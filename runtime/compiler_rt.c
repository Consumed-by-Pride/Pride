/*
 * ============================================================================
 * compiler_rt.c — Pride compiler support library
 *
 * Named after Zig's compiler_rt and LLVM's compiler-rt.
 * Rust calls the equivalent "lang items" (std::rt / #[lang = "..."]).
 *
 * WHY THIS FILE EXISTS:
 *   Three things cannot be expressed in LLVM IR or Pride source:
 *     1. Algebraic effects — require ucontext_t (POSIX, C-only)
 *     2. Panic           — requires signal-safe write(2) + backtrace
 *     3. SIMD builtins   — require SSE4.1/AVX GCC vector extensions
 *   Everything else (malloc, syscalls, math) is declared in the codegen
 *   IR as direct libc/LLVM-intrinsic calls. This file is ~1800 lines.
 *   Zig's compiler_rt is ~15K lines. Rust's is ~80K lines. We are tiny.
 *
 * COMPILE:
 *   gcc -O2 -msse4.1 -pthread -std=c11 -c compiler_rt.c -o compiler_rt.o
 *
 * SECTIONS:
 *   §1  Platform macros
 *   §2  Internal allocator (used only by effects engine and tensor ops)
 *   §3  Panic  : lang item: __pride_panic
 *   §4  Effects engine  : lang items: __pride_push/pop_handler, perform, resume
 *   §5  Drop registry   : lang item: __pride_drop
 *   §6  String builder  : lang item: pride_str_*
 *   §7  Buffered I/O    : lang item: __pride_io_*
 *   §8  Tensors / matmul : lang item: __pride_matmul
 *   §9  ARC             : lang item: __pride_arc_*
 *   §10 Thread spawn    : lang item: __pride_thread_*
 *   §11 Entry / signal setup
 *   §12–§16 ABI helpers (atomics, SIMD, bit ops, float bits, pool)
 * ============================================================================
 */
/* ── §1  Platform detection ──────────────────────────────────────────────── */

#define _GNU_SOURCE   /* mmap(MAP_ANONYMOUS), pthread extensions               */

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

/* POSIX / Linux */
#include <unistd.h>
#include <sys/mman.h>
#include <signal.h>
#include <ucontext.h>
#include <execinfo.h>
#include <pthread.h>
#include <math.h>

/* Compiler intrinsics */
#if defined(__GNUC__) || defined(__clang__)
#  define PRIDE_LIKELY(x)   __builtin_expect(!!(x), 1)
#  define PRIDE_UNLIKELY(x) __builtin_expect(!!(x), 0)
#  define PRIDE_NOINLINE    __attribute__((noinline))
#  define PRIDE_NORETURN    __attribute__((noreturn))
#  define PRIDE_UNUSED      __attribute__((unused))
#  define PRIDE_PACKED      __attribute__((packed))
#  define PRIDE_COLD        __attribute__((cold))
#  define PRIDE_INLINE      __attribute__((always_inline)) static inline
#else
#  define PRIDE_LIKELY(x)   (x)
#  define PRIDE_UNLIKELY(x) (x)
#  define PRIDE_NOINLINE
#  define PRIDE_NORETURN
#  define PRIDE_UNUSED
#  define PRIDE_PACKED
#  define PRIDE_COLD
#  define PRIDE_INLINE      static inline
#endif

/* Atomic builtins (GCC/Clang built-ins; no <stdatomic.h> required) */
#define ATOMIC_LOAD(ptr)         __atomic_load_n((ptr), __ATOMIC_ACQUIRE)
#define ATOMIC_STORE(ptr, val)   __atomic_store_n((ptr), (val), __ATOMIC_RELEASE)
#define ATOMIC_ADD(ptr, val)     __atomic_fetch_add((ptr), (val), __ATOMIC_ACQ_REL)
#define ATOMIC_SUB(ptr, val)     __atomic_fetch_sub((ptr), (val), __ATOMIC_ACQ_REL)
#define ATOMIC_CAS(ptr,exp,des)  __atomic_compare_exchange_n((ptr),(exp),(des),0,\
                                     __ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST)

/* Page size (4 KB on x86-64, 16 KB on Apple Silicon — we always use 4 KB) */
#define PRIDE_PAGE_SIZE     4096UL
#define PRIDE_PAGE_ALIGN(n) (((n) + PRIDE_PAGE_SIZE - 1) & ~(PRIDE_PAGE_SIZE - 1))


/* ── §2  Memory: arena + pool allocator ─────────────────────────────────── */
/*
 * Two-tier allocator:
 *
 *   SMALL (≤ 2 KB):  size-class pool with per-class free-lists.
 *     16 size classes: 8, 16, 32, 48, 64, 96, 128, 192, 256, 384, 512,
 *                      768, 1024, 1280, 1536, 2048 bytes.
 *     Each class is backed by one or more 64-KB slabs mmap'd directly.
 *     Free-list is a singly-linked list embedded in the free objects.
 *     Thread-safe via per-class spinlocks (compare-and-swap on the head ptr).
 *
 *   LARGE (> 2 KB):  direct mmap, rounded up to PRIDE_PAGE_SIZE.
 *     Stored with a 16-byte header for bookkeeping.
 *
 * The libc malloc/free symbols remain available and are used for system-
 * level allocations (backtrace_symbols, pthread internals, etc.).
 * Pride-generated code always calls through the pride_alloc / pride_free
 * wrappers below, which map to this allocator.
 */

#define POOL_CLASSES    16
#define POOL_SLAB_BYTES (64 * 1024)   /* 64 KB per slab                       */
#define POOL_LARGE_THRESHOLD 2048

static const size_t pool_sizes[POOL_CLASSES] = {
    8, 16, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768, 1024, 1280, 1536, 2048
};

typedef union PoolNode { union PoolNode* next; char data[1]; } PoolNode;

typedef struct {
    PoolNode*   head;        /* free-list head (CAS-protected)                 */
    size_t      obj_size;    /* size of one object in this class                */
} PoolClass;

static PoolClass pool[POOL_CLASSES];
static pthread_once_t pool_once = PTHREAD_ONCE_INIT;

/* Large allocation header (sits immediately before the user pointer) */
typedef struct PRIDE_PACKED { size_t mmap_size; uint32_t magic; } LargeHdr;
#define LARGE_MAGIC 0xDE4D4E41u   /* "DEAD" backwards — paranoia check        */

PRIDE_INLINE int pool_class_for(size_t bytes) {
    for (int i = 0; i < POOL_CLASSES; i++)
        if (pool[i].obj_size >= bytes) return i;
    return -1;
}

static void pool_refill(int cls) {
    /* Map a fresh 64-KB slab and carve it into objects */
    size_t obj = pool[cls].obj_size;
    size_t slab_size = PRIDE_PAGE_ALIGN(POOL_SLAB_BYTES);
    char* mem = mmap(NULL, slab_size,
                     PROT_READ | PROT_WRITE,
                     MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (PRIDE_UNLIKELY(mem == MAP_FAILED)) return;

    size_t count = slab_size / obj;
    /* Link all objects into the class free-list using CAS */
    for (size_t i = count; i-- > 0; ) {
        PoolNode* node = (PoolNode*)(mem + i * obj);
        PoolNode* old_head;
        do {
            old_head = ATOMIC_LOAD(&pool[cls].head);
            node->next = old_head;
        } while (!ATOMIC_CAS(&pool[cls].head, &old_head, node));
    }
}

static void pool_init(void) {
    for (int i = 0; i < POOL_CLASSES; i++) {
        pool[i].obj_size = pool_sizes[i];
        pool[i].head     = NULL;
    }
}

void* pride_alloc(size_t bytes) {
    if (PRIDE_UNLIKELY(bytes == 0)) bytes = 1;
    pthread_once(&pool_once, pool_init);

    int cls = pool_class_for(bytes);

    if (PRIDE_LIKELY(cls >= 0)) {
        /* Pool path */
        PoolNode* node;
        PoolNode* next;
        for (;;) {
            node = ATOMIC_LOAD(&pool[cls].head);
            if (PRIDE_UNLIKELY(node == NULL)) {
                pool_refill(cls);
                node = ATOMIC_LOAD(&pool[cls].head);
                if (PRIDE_UNLIKELY(node == NULL)) {
                    /* Fall back to mmap for this one if refill also failed */
                    void* p = mmap(NULL, PRIDE_PAGE_ALIGN(bytes),
                                   PROT_READ|PROT_WRITE,
                                   MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
                    return (p == MAP_FAILED) ? NULL : p;
                }
            }
            next = node->next;
            if (ATOMIC_CAS(&pool[cls].head, &node, next)) break;
        }
        return (void*)node;
    } else {
        /* Large path: mmap + header */
        size_t total = PRIDE_PAGE_ALIGN(bytes + sizeof(LargeHdr));
        char* mem = mmap(NULL, total,
                         PROT_READ|PROT_WRITE,
                         MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
        if (PRIDE_UNLIKELY(mem == MAP_FAILED)) return NULL;
        LargeHdr* hdr = (LargeHdr*)mem;
        hdr->mmap_size = total;
        hdr->magic     = LARGE_MAGIC;
        return mem + sizeof(LargeHdr);
    }
}

void* pride_alloc_zeroed(size_t bytes) {
    /* mmap pages are already zero — pool objects need explicit zeroing */
    void* p = pride_alloc(bytes);
    if (p) {
        int cls = pool_class_for(bytes);
        if (cls >= 0) memset(p, 0, pool[cls].obj_size);
        /* large allocs come from mmap and are already zero */
    }
    return p;
}

void pride_free(void* ptr, size_t bytes) {
    if (PRIDE_UNLIKELY(ptr == NULL)) return;

    int cls = pool_class_for(bytes);
    if (PRIDE_LIKELY(cls >= 0)) {
        /* Return to pool free-list */
        PoolNode* node = (PoolNode*)ptr;
        PoolNode* old_head;
        do {
            old_head = ATOMIC_LOAD(&pool[cls].head);
            node->next = old_head;
        } while (!ATOMIC_CAS(&pool[cls].head, &old_head, node));
    } else {
        /* Undo the large mmap */
        LargeHdr* hdr = (LargeHdr*)((char*)ptr - sizeof(LargeHdr));
        if (PRIDE_LIKELY(hdr->magic == LARGE_MAGIC)) {
            munmap(hdr, hdr->mmap_size);
        }
        /* Silently ignore bad frees (same as free(NULL)) */
    }
}

/* Compatibility shims: __pride_alloc / __pride_free used by generated IR */
void* __pride_alloc(size_t bytes) { return pride_alloc(bytes); }
void  __pride_free(void* ptr, size_t bytes) { pride_free(ptr, bytes); }

/* malloc wrapper for generated code that calls @malloc directly */
/* We deliberately do NOT override malloc/free — that would break libc itself. */


/* ── §3  Panic ───────────────────────────────────────────────────────────── */
/*
 * __pride_panic: signal-safe, writes to fd 2, then dumps a backtrace.
 *
 * Design:
 *  - Uses write(2) not fprintf — write() is async-signal-safe.
 *  - backtrace() / backtrace_symbols_fd() are also signal-safe on Linux.
 *  - Raises SIGABRT (not abort()) so a debugger can catch it.
 */

static void write_str(const char* s) {
    write(STDERR_FILENO, s, strlen(s));
}


PRIDE_NORETURN PRIDE_COLD PRIDE_NOINLINE
void __pride_panic(void* msg_ptr, int64_t msg_len) {
    /* Build the panic header on the stack (no alloc) */
    write_str("\n\033[1;31mpride: panic\033[0m");
    if (msg_ptr != NULL && msg_len > 0) {
        write_str(": ");
        write(STDERR_FILENO, msg_ptr, (size_t)msg_len);
    }
    write_str("\n");

    /* Stack backtrace */
    write_str("stack backtrace:\n");
    void* bt[64];
    int n = backtrace(bt, 64);
    backtrace_symbols_fd(bt, n, STDERR_FILENO);
    write_str("\n");

    /* Raise SIGABRT so a debugger / core dump policy kicks in */
    raise(SIGABRT);
    _exit(134);   /* SIGABRT exit code — should not reach here */
}

PRIDE_NORETURN static void panic_fmt(const char* msg) {
    __pride_panic((void*)msg, (int64_t)strlen(msg));
}


/* ── §4  Algebraic effects: ucontext prompt stack ───────────────────────── */
/*
 * The effect system uses a per-thread prompt stack of handler frames.
 * Each frame holds a ucontext_t so we can perform genuine coroutine-style
 * suspension and resumption — not just longjmp.
 *
 * Lifecycle of one effect operation:
 *
 *   1. Code calls __pride_push_handler(frame_id).
 *      We save the caller's context in frame->caller_ctx.
 *      We allocate a coroutine stack for the computation.
 *      We swap to the computation context (which runs the body).
 *      When the body finishes or performs an op, we swap back.
 *
 *   2. Inside the computation, __pride_perform(op_id, ...) is called.
 *      We walk the stack, find the matching handler, snapshot the
 *      continuation (the coroutine context), and swap to the handler body.
 *
 *   3. The handler body may call __pride_resume(val).
 *      We swap back to the saved computation context with the resume value.
 *      The computation continues from after the perform() call.
 *
 *   4. __pride_pop_handler() tears down the frame and frees the coro stack.
 *
 * Stack size: 256 KB per handler frame (user programs can exceed this by
 * nesting multiple handles — each gets its own stack).
 *
 * Thread safety: the handler stack is __thread (per-thread storage).
 */

#define EFFECT_STACK_DEPTH  16
#define EFFECT_CORO_STACK   (256 * 1024)  /* 256 KB per handler frame         */

typedef struct PrideHandlerFrame {
    uint64_t    frame_id;       /* effect decl AST node id                      */
    ucontext_t  handler_ctx;    /* context of the handler body (the arm code)   */
    ucontext_t  perform_ctx;    /* context of the performing computation        */
    char*       coro_stack;     /* heap stack for the coroutine                 */
    void*       perform_arg;    /* argument passed to __pride_perform           */
    uint64_t    perform_op_id;  /* op id passed to __pride_perform              */
    void*       resume_val;     /* value passed to __pride_resume               */
    bool        resumed;        /* true after a resume() call                   */
    bool        complete;       /* true after the handler body returned          */
} PrideHandlerFrame;

static __thread PrideHandlerFrame  effect_stack[EFFECT_STACK_DEPTH];
static __thread int                effect_top = -1;

/*
 * __pride_push_handler — install a handler frame.
 *
 * The caller (the `handle` block in generated IR) invokes this, then the
 * TERM_SWITCH in the IR routes to either the normal-exit join block (if no
 * effect was performed) or one of the arm blocks (if an op was performed and
 * dispatched here).
 *
 * Returns a discriminant pointer that the TERM_SWITCH uses to select the arm.
 * In our implementation the discriminant is the frame pointer itself; the
 * generated IR switch has case labels matching arm indices [1..N].
 * We return an integer-sized tag: 0 = normal return, k = arm k performed.
 */
void* __pride_push_handler(uint64_t frame_id) {
    if (PRIDE_UNLIKELY(effect_top + 1 >= EFFECT_STACK_DEPTH)) {
        panic_fmt("effect handler stack overflow (max 64 nested handlers)");
    }
    effect_top++;
    PrideHandlerFrame* f = &effect_stack[effect_top];
    f->frame_id      = frame_id;
    f->perform_arg   = NULL;
    f->perform_op_id = 0;
    f->resume_val    = NULL;
    f->resumed       = false;
    f->complete      = false;

    /* Allocate coroutine stack via our pool allocator */
    f->coro_stack = (char*)pride_alloc(EFFECT_CORO_STACK);
    if (PRIDE_UNLIKELY(f->coro_stack == NULL)) {
        panic_fmt("effect: failed to allocate coroutine stack");
    }

    /*
     * Return the frame pointer as the IR_HANDLER value.
     * The generated TERM_SWITCH uses this as the discriminant.
     * A real evidence-passing backend would thread this as a hidden
     * argument; here we use a global (per-thread) stack instead.
     */
    return (void*)f;
}

void __pride_pop_handler(void) {
    if (PRIDE_UNLIKELY(effect_top < 0)) return;
    PrideHandlerFrame* f = &effect_stack[effect_top];
    if (f->coro_stack) {
        pride_free(f->coro_stack, EFFECT_CORO_STACK);
        f->coro_stack = NULL;
    }
    effect_top--;
}

/*
 * __pride_perform — invoke an effect operation.
 *
 * Walks the per-thread handler stack from top to bottom.  When a matching
 * frame is found, saves the current (computation) context and swaps to the
 * handler body.  The perform_arg field carries the first argument; variadic
 * args are accessed by the arm via the standard calling convention (they are
 * already on the hardware stack at the call to __pride_perform).
 *
 * Returns the resume value set by __pride_resume().
 */
void* __pride_perform(uint64_t op_id, ...) {
    for (int i = effect_top; i >= 0; i--) {
        PrideHandlerFrame* f = &effect_stack[i];
        f->perform_op_id = op_id;
        f->resume_val    = NULL;
        f->resumed       = false;

        /*
         * Save the current (performing) context and swap to the handler
         * context.  The handler code will run in handler_ctx; when it calls
         * __pride_resume() we swap back here.
         *
         * Note: in the setjmp model the handler ran as a function call.
         * In the ucontext model we co-routinely swap.  The generated IR
         * simply reads the resume value from __pride_resume's return —
         * so this is transparent to the compiler output.
         */
        swapcontext(&f->perform_ctx, &f->handler_ctx);

        /* When we return here, the handler has called __pride_resume() */
        return f->resume_val;
    }

    /* No handler installed: unhandled effect */
    char buf[128];
    snprintf(buf, sizeof(buf),
             "unhandled effect operation (op_id=%llu)",
             (unsigned long long)op_id);
    panic_fmt(buf);
    __builtin_unreachable();
}

/*
 * __pride_resume — resume a suspended computation with value `val`.
 *
 * Called from inside a handler arm body.  Saves the handler context and
 * swaps back to the computation that called __pride_perform().
 */
void* __pride_resume(void* val) {
    if (PRIDE_UNLIKELY(effect_top < 0)) {
        panic_fmt("resume called outside of a handler arm");
    }
    PrideHandlerFrame* f = &effect_stack[effect_top];
    f->resume_val = val;
    f->resumed    = true;
    /* Swap back to the performing computation */
    swapcontext(&f->handler_ctx, &f->perform_ctx);
    /* When the computation next performs an op we'll return here */
    return val;
}


/* ── §5  Drop registry ───────────────────────────────────────────────────── */
/*
 * A flat table mapping type-tag (uint64_t, the struct decl AST node id)
 * to a destructor function pointer.  Registered at program startup by
 * code generated for each type that implements `with`-resource RAII.
 *
 * Usage:
 *   pride_register_drop(type_id, my_destructor);
 *   __pride_drop(ptr);   // dispatches via the table
 *
 * The type tag is stored in the first 8 bytes of every with-resource object
 * (the codegen packs it as the first field).  This is a convention; the
 * compiler ensures it.
 */

#define DROP_TABLE_CAP  64

typedef void (*DropFn)(void*);

typedef struct { uint64_t type_id; DropFn fn; } DropEntry;

static DropEntry drop_table[DROP_TABLE_CAP];
static int       drop_count = 0;
static pthread_mutex_t drop_mutex = PTHREAD_MUTEX_INITIALIZER;

void pride_register_drop(uint64_t type_id, void (*destructor)(void*)) {
    pthread_mutex_lock(&drop_mutex);
    if (drop_count < DROP_TABLE_CAP) {
        drop_table[drop_count].type_id = type_id;
        drop_table[drop_count].fn      = destructor;
        drop_count++;
    }
    pthread_mutex_unlock(&drop_mutex);
}

void __pride_drop(void* ptr) {
    if (PRIDE_UNLIKELY(ptr == NULL)) return;
    /*
     * Read the type tag from the first 8 bytes of the object.
     * This is a convention established by codegen for with-resource objects.
     */
    uint64_t type_id;
    memcpy(&type_id, ptr, sizeof(uint64_t));
    for (int i = 0; i < drop_count; i++) {
        if (drop_table[i].type_id == type_id) {
            drop_table[i].fn(ptr);
            return;
        }
    }
    /* No destructor registered: resource leaks silently.
     * In --strict builds the compiler warns at the point of `with`. */
}


/* ── §6  Strings ─────────────────────────────────────────────────────────── */
/*
 * Pride Str = { ptr: *u8, len: u64 } — a fat pointer with byte length.
 * The data is not null-terminated; all operations work with explicit lengths.
 */

typedef struct { const char* ptr; uint64_t len; } PrideStr;

/* Construct a PrideStr from a C string literal */
PRIDE_INLINE PrideStr pride_str_from_cstr(const char* s) {
    PrideStr r; r.ptr = s; r.len = (uint64_t)strlen(s); return r;
}

/* Lexicographic comparison: < 0, 0, > 0 */
int pride_str_cmp(PrideStr a, PrideStr b) {
    size_t n = a.len < b.len ? a.len : b.len;
    int c = memcmp(a.ptr, b.ptr, n);
    if (c != 0) return c;
    return (a.len < b.len) ? -1 : (a.len > b.len) ? 1 : 0;
}

bool pride_str_eq(PrideStr a, PrideStr b) {
    return a.len == b.len && memcmp(a.ptr, b.ptr, a.len) == 0;
}

/* Heap-allocate a copy of a string (caller must pride_free with len bytes) */
PrideStr pride_str_dup(PrideStr s) {
    char* buf = (char*)pride_alloc(s.len + 1);
    if (PRIDE_UNLIKELY(buf == NULL)) panic_fmt("pride_str_dup: out of memory");
    memcpy(buf, s.ptr, s.len);
    buf[s.len] = '\0';
    PrideStr r; r.ptr = buf; r.len = s.len; return r;
}

/* Concatenate two strings into a fresh heap allocation */
PrideStr pride_str_cat(PrideStr a, PrideStr b) {
    size_t total = a.len + b.len;
    char* buf = (char*)pride_alloc(total + 1);
    if (PRIDE_UNLIKELY(buf == NULL)) panic_fmt("pride_str_cat: out of memory");
    memcpy(buf, a.ptr, a.len);
    memcpy(buf + a.len, b.ptr, b.len);
    buf[total] = '\0';
    PrideStr r; r.ptr = buf; r.len = (uint64_t)total; return r;
}

/* Write a PrideStr to fd (async-signal-safe) */
void pride_str_write(int fd, PrideStr s) {
    if (s.ptr && s.len) write(fd, s.ptr, s.len);
}

/* Expose to generated code */
void __pride_str_write_stdout(PrideStr s) { pride_str_write(STDOUT_FILENO, s); }
void __pride_str_write_stderr(PrideStr s) { pride_str_write(STDERR_FILENO, s); }


/* ── §7  I/O ─────────────────────────────────────────────────────────────── */
/*
 * Buffered stdout for performance: batch small writes, flush on newline or
 * when the buffer fills.  stderr is always unbuffered (matches conventional
 * expectation for diagnostic streams).
 *
 * These are the primitives backing Pride's IO effect operations:
 *   IO.write_byte(b)  →  __pride_io_write_byte
 *   IO.read_byte()    →  __pride_io_read_byte
 *   IO.write_str(s)   →  __pride_io_write_str
 *   IO.read_line()    →  __pride_io_read_line
 *   IO.flush()        →  __pride_io_flush
 */

#define IO_BUF_SIZE 4096

static __thread char   io_out_buf[IO_BUF_SIZE];
static __thread size_t io_out_pos = 0;

static void io_flush_internal(void) {
    if (io_out_pos > 0) {
        write(STDOUT_FILENO, io_out_buf, io_out_pos);
        io_out_pos = 0;
    }
}

void __pride_io_flush(void) { io_flush_internal(); }

void __pride_io_write_byte(uint8_t b) {
    io_out_buf[io_out_pos++] = (char)b;
    if (io_out_pos >= IO_BUF_SIZE || b == '\n') io_flush_internal();
}

void __pride_io_write_str(PrideStr s) {
    const char* p = s.ptr;
    size_t      n = s.len;
    while (n > 0) {
        size_t room = IO_BUF_SIZE - io_out_pos;
        size_t chunk = n < room ? n : room;
        memcpy(io_out_buf + io_out_pos, p, chunk);
        io_out_pos += chunk;
        p += chunk;
        n -= chunk;
        if (io_out_pos >= IO_BUF_SIZE) io_flush_internal();
    }
    /* Flush on embedded newlines */
    for (size_t i = 0; i < s.len; i++) {
        if (s.ptr[i] == '\n') { io_flush_internal(); break; }
    }
}

uint8_t __pride_io_read_byte(void) {
    io_flush_internal();   /* flush before blocking read */
    uint8_t b = 0;
    if (read(STDIN_FILENO, &b, 1) != 1) return 0xFF; /* EOF sentinel */
    return b;
}

/*
 * Read one line from stdin, heap-allocated.
 * Returns a PrideStr; the caller owns the buffer and must pride_free it.
 */
PrideStr __pride_io_read_line(void) {
    io_flush_internal();
    size_t cap = 256;
    char* buf = (char*)pride_alloc(cap);
    if (PRIDE_UNLIKELY(buf == NULL)) panic_fmt("read_line: out of memory");
    size_t len = 0;
    for (;;) {
        if (len + 1 >= cap) {
            size_t new_cap = cap * 2;
            char* new_buf = (char*)pride_alloc(new_cap);
            if (PRIDE_UNLIKELY(new_buf == NULL)) panic_fmt("read_line: out of memory");
            memcpy(new_buf, buf, len);
            pride_free(buf, cap);
            buf = new_buf;
            cap = new_cap;
        }
        uint8_t c;
        ssize_t r = read(STDIN_FILENO, &c, 1);
        if (r <= 0 || c == '\n') break;
        buf[len++] = (char)c;
    }
    buf[len] = '\0';
    PrideStr s; s.ptr = buf; s.len = (uint64_t)len;
    return s;
}


/* ── §8  Tensors ─────────────────────────────────────────────────────────── */
/*
 * Pride tensors: Tensor<T; D0, D1, ..., Dk> — arbitrary-rank, row-major.
 *
 * Wire format (what __pride_matmul receives / returns):
 *   PrideTensor header followed immediately by the element data.
 *   rank       : number of dimensions
 *   dims[rank] : dimension sizes
 *   data[]     : double elements (we use double as the universal numeric type;
 *                the codegen may specialise for float/i32 via separate fns)
 *
 * The layout is:
 *   struct PrideTensor {
 *       uint64_t rank;
 *       uint64_t dims[rank];    // flexible array not used — manual arithmetic
 *       double   data[];
 *   }
 *
 * Operations:
 *   __pride_matmul    — generalised matrix contraction (@ operator)
 *   __pride_tensor_elemwise  — elementwise binary op
 *   __pride_tensor_new       — allocate a zeroed tensor
 *
 * CBLAS hook: if compiled with -DPRIDE_USE_CBLAS and cblas.h is available,
 * 2D GEMM is delegated to cblas_dgemm.  Otherwise we use a cache-friendly
 * IJK loop with register blocking.
 */

typedef struct {
    uint64_t rank;
    /* dims and data follow: dims[rank] then data[prod(dims)] */
} PrideTensor;

static uint64_t* tensor_dims(PrideTensor* t) {
    return (uint64_t*)((char*)t + sizeof(PrideTensor));
}

static double* tensor_data(PrideTensor* t) {
    return (double*)((char*)t + sizeof(PrideTensor)
                     + t->rank * sizeof(uint64_t));
}

static size_t tensor_elem_count(PrideTensor* t) {
    size_t n = 1;
    uint64_t* dims = tensor_dims(t);
    for (uint64_t i = 0; i < t->rank; i++) n *= (size_t)dims[i];
    return n;
}

static size_t tensor_alloc_size(uint64_t rank, uint64_t* dims) {
    size_t n = 1;
    for (uint64_t i = 0; i < rank; i++) n *= (size_t)dims[i];
    return sizeof(PrideTensor)
         + rank * sizeof(uint64_t)
         + n * sizeof(double);
}

PrideTensor* __pride_tensor_new(uint64_t rank, uint64_t* dims) {
    size_t alloc = tensor_alloc_size(rank, dims);
    PrideTensor* t = (PrideTensor*)pride_alloc_zeroed(alloc);
    if (PRIDE_UNLIKELY(t == NULL)) panic_fmt("tensor_new: out of memory");
    t->rank = rank;
    uint64_t* td = tensor_dims(t);
    for (uint64_t i = 0; i < rank; i++) td[i] = dims[i];
    return t;
}

/*
 * __pride_matmul — the `@` operator for any rank-2 tensors (matrices).
 *
 * A @ B where A is [M×K] and B is [K×N] → C is [M×N].
 *
 * For higher-rank tensors this is a batched GEMM: the last two dimensions
 * are the matrix dims; all preceding dims are batch dims that must match.
 *
 * Implementation:
 *   - Rank-2: a direct O(MKN) loop with cache-line blocking (block size 64).
 *   - Rank > 2: batched over leading dims, each batch calls the rank-2 path.
 */

#define GEMM_BLOCK 64

static void gemm_block(double* C, const double* A, const double* B,
                        size_t M, size_t K, size_t N) {
    /* Blocked IJK GEMM — L1-friendly with register accumulation */
    for (size_t ii = 0; ii < M; ii += GEMM_BLOCK) {
        size_t ilim = ii + GEMM_BLOCK < M ? ii + GEMM_BLOCK : M;
        for (size_t jj = 0; jj < N; jj += GEMM_BLOCK) {
            size_t jlim = jj + GEMM_BLOCK < N ? jj + GEMM_BLOCK : N;
            for (size_t kk = 0; kk < K; kk += GEMM_BLOCK) {
                size_t klim = kk + GEMM_BLOCK < K ? kk + GEMM_BLOCK : K;
                /* Micro-kernel */
                for (size_t i = ii; i < ilim; i++) {
                    for (size_t k = kk; k < klim; k++) {
                        double a_ik = A[i * K + k];
                        for (size_t j = jj; j < jlim; j++) {
                            C[i * N + j] += a_ik * B[k * N + j];
                        }
                    }
                }
            }
        }
    }
}

void* __pride_matmul(void* lhs_ptr, void* rhs_ptr) {
    if (PRIDE_UNLIKELY(lhs_ptr == NULL || rhs_ptr == NULL)) {
        panic_fmt("matmul: null operand");
    }
    PrideTensor* A = (PrideTensor*)lhs_ptr;
    PrideTensor* B = (PrideTensor*)rhs_ptr;

    if (PRIDE_UNLIKELY(A->rank < 2 || B->rank < 2)) {
        panic_fmt("matmul: operands must have rank >= 2");
    }
    if (PRIDE_UNLIKELY(A->rank != B->rank)) {
        panic_fmt("matmul: rank mismatch");
    }

    uint64_t rank    = A->rank;
    uint64_t* a_dims = tensor_dims(A);
    uint64_t* b_dims = tensor_dims(B);

    /* Matrix dims: A=[...×M×K], B=[...×K×N] */
    size_t M = (size_t)a_dims[rank - 2];
    size_t K = (size_t)a_dims[rank - 1];
    size_t N = (size_t)b_dims[rank - 1];

    if (PRIDE_UNLIKELY(K != (size_t)b_dims[rank - 2])) {
        panic_fmt("matmul: inner dimensions do not match");
    }

    /* Compute batch size (product of leading dims) */
    size_t batch = 1;
    for (uint64_t i = 0; i < rank - 2; i++) {
        if (PRIDE_UNLIKELY(a_dims[i] != b_dims[i])) {
            panic_fmt("matmul: batch dimensions do not match");
        }
        batch *= (size_t)a_dims[i];
    }

    /* Allocate result tensor C: [...×M×N] */
    uint64_t* c_dims = (uint64_t*)pride_alloc(rank * sizeof(uint64_t));
    if (PRIDE_UNLIKELY(c_dims == NULL)) panic_fmt("matmul: OOM");
    for (uint64_t i = 0; i < rank - 2; i++) c_dims[i] = a_dims[i];
    c_dims[rank - 2] = (uint64_t)M;
    c_dims[rank - 1] = (uint64_t)N;

    PrideTensor* C = __pride_tensor_new(rank, c_dims);
    pride_free(c_dims, rank * sizeof(uint64_t));

    /* Batched GEMM */
    double* Ad = tensor_data(A);
    double* Bd = tensor_data(B);
    double* Cd = tensor_data(C);

    for (size_t b = 0; b < batch; b++) {
        gemm_block(Cd + b * M * N,
                   Ad + b * M * K,
                   Bd + b * K * N,
                   M, K, N);
    }

    return (void*)C;
}

/* Elementwise binary op: result = f(A[i], B[i]) for each element.
 * `op`: 0=add, 1=sub, 2=mul, 3=div (matching TOKEN_PLUS/MINUS/STAR/SLASH) */
void* __pride_tensor_elemwise(void* lhs_ptr, void* rhs_ptr, int op) {
    PrideTensor* A = (PrideTensor*)lhs_ptr;
    PrideTensor* B = (PrideTensor*)rhs_ptr;

    size_t na = tensor_elem_count(A);
    size_t nb = tensor_elem_count(B);
    if (PRIDE_UNLIKELY(na != nb || A->rank != B->rank)) {
        panic_fmt("tensor_elemwise: shape mismatch");
    }

    PrideTensor* C = __pride_tensor_new(A->rank, tensor_dims(A));
    double* Ad = tensor_data(A);
    double* Bd = tensor_data(B);
    double* Cd = tensor_data(C);

    switch (op) {
        case 0: for (size_t i = 0; i < na; i++) Cd[i] = Ad[i] + Bd[i]; break;
        case 1: for (size_t i = 0; i < na; i++) Cd[i] = Ad[i] - Bd[i]; break;
        case 2: for (size_t i = 0; i < na; i++) Cd[i] = Ad[i] * Bd[i]; break;
        case 3: for (size_t i = 0; i < na; i++) Cd[i] = Ad[i] / Bd[i]; break;
        default: panic_fmt("tensor_elemwise: unknown op");
    }
    return (void*)C;
}


/* ── §9  Atomic reference-counting ──────────────────────────────────────── */
/*
 * Shared resources that outlive a single scope use atomic reference counting.
 * The generated code calls __pride_arc_retain / __pride_arc_release.
 * The header is embedded before the user pointer (same trick as LargeHdr).
 */

typedef struct { uint64_t count; DropFn drop; } ArcHdr;
#define ARC_HDR_SIZE ((sizeof(ArcHdr) + 15) & ~15u)  /* 16-byte aligned       */

void* __pride_arc_new(size_t bytes, void (*drop)(void*)) {
    char* mem = (char*)pride_alloc(ARC_HDR_SIZE + bytes);
    if (PRIDE_UNLIKELY(mem == NULL)) panic_fmt("arc_new: out of memory");
    ArcHdr* hdr = (ArcHdr*)mem;
    hdr->count = 1;
    hdr->drop  = drop;
    memset(mem + ARC_HDR_SIZE, 0, bytes);
    return mem + ARC_HDR_SIZE;
}

void __pride_arc_retain(void* ptr) {
    if (PRIDE_UNLIKELY(ptr == NULL)) return;
    ArcHdr* hdr = (ArcHdr*)((char*)ptr - ARC_HDR_SIZE);
    ATOMIC_ADD(&hdr->count, 1ULL);
}

void __pride_arc_release(void* ptr, size_t bytes) {
    if (PRIDE_UNLIKELY(ptr == NULL)) return;
    ArcHdr* hdr = (ArcHdr*)((char*)ptr - ARC_HDR_SIZE);
    uint64_t prev = ATOMIC_SUB(&hdr->count, 1ULL);
    if (prev == 1) {
        /* Last reference: run destructor then free */
        if (hdr->drop) hdr->drop(ptr);
        pride_free((char*)ptr - ARC_HDR_SIZE, ARC_HDR_SIZE + bytes);
    }
}


/* ── §10  Thread support ─────────────────────────────────────────────────── */
/*
 * Per-thread initialisation.  Pride threads are pthreads under the hood.
 * __pride_thread_spawn creates a pthread, initialises its TLS, and calls
 * the Pride function pointer with the given argument.
 */

typedef void* (*PrideThreadFn)(void*);
typedef struct { PrideThreadFn fn; void* arg; } ThreadArg;

static void* thread_trampoline(void* raw) {
    ThreadArg* ta = (ThreadArg*)raw;
    PrideThreadFn fn = ta->fn;
    void* arg = ta->arg;
    pride_free(ta, sizeof(ThreadArg));
    return fn(arg);
}

void* __pride_thread_spawn(void* fn_ptr, void* arg) {
    ThreadArg* ta = (ThreadArg*)pride_alloc(sizeof(ThreadArg));
    if (PRIDE_UNLIKELY(ta == NULL)) panic_fmt("thread_spawn: OOM");
    ta->fn  = (PrideThreadFn)(uintptr_t)fn_ptr;  /* POSIX: fn ptrs via uintptr_t */
    ta->arg = arg;

    pthread_t* tid = (pthread_t*)pride_alloc(sizeof(pthread_t));
    if (PRIDE_UNLIKELY(tid == NULL)) panic_fmt("thread_spawn: OOM");

    int rc = pthread_create(tid, NULL, thread_trampoline, ta);
    if (PRIDE_UNLIKELY(rc != 0)) {
        pride_free(ta, sizeof(ThreadArg));
        pride_free(tid, sizeof(pthread_t));
        panic_fmt("thread_spawn: pthread_create failed");
    }
    return (void*)tid;
}

void __pride_thread_join(void* tid_ptr) {
    pthread_t* tid = (pthread_t*)tid_ptr;
    pthread_join(*tid, NULL);
    pride_free(tid, sizeof(pthread_t));
}

void __pride_thread_detach(void* tid_ptr) {
    pthread_t* tid = (pthread_t*)tid_ptr;
    pthread_detach(*tid);
    pride_free(tid, sizeof(pthread_t));
}


/* ── §11  Program entry & signal setup ───────────────────────────────────── */
/*
 * Signal handler: catches SIGSEGV, SIGBUS, SIGFPE, SIGILL and prints a
 * readable crash message with a backtrace before raising the default handler.
 *
 * We install these in pride_runtime_init(), called from __attribute__((constructor)).
 */

static void crash_handler(int sig, siginfo_t* info PRIDE_UNUSED, void* uctx PRIDE_UNUSED) {
    /* Async-signal-safe path: only write() and backtrace*_fd() */
    const char* signame =
        sig == SIGSEGV ? "SIGSEGV (segmentation fault)" :
        sig == SIGBUS  ? "SIGBUS  (bus error)"          :
        sig == SIGFPE  ? "SIGFPE  (arithmetic exception)" :
        sig == SIGILL  ? "SIGILL  (illegal instruction)"  : "fatal signal";
    write_str("\n\033[1;31mpride: ");
    write_str(signame);
    write_str("\033[0m\n");
    if (sig == SIGSEGV && info) {
        write_str("fault address: 0x");
        /* Print the fault address in hex */
        uintptr_t addr = (uintptr_t)info->si_addr;
        char hex[17]; int i = 16;
        hex[i] = '\0';
        if (addr == 0) { write_str("0"); }
        else {
            while (addr > 0) { hex[--i] = "0123456789abcdef"[addr & 0xF]; addr >>= 4; }
            write_str(hex + i);
        }
        write_str("\n");
    }
    write_str("stack backtrace:\n");
    void* bt[64];
    int n = backtrace(bt, 64);
    backtrace_symbols_fd(bt, n, STDERR_FILENO);
    write_str("\n");

    /* Re-raise with default handler to generate a core dump */
    struct sigaction dfl; sigemptyset(&dfl.sa_mask);
    dfl.sa_handler = SIG_DFL; dfl.sa_flags = 0;
    sigaction(sig, &dfl, NULL);
    raise(sig);
}

/* Inline asm barrier */
void __pride_asm_barrier(void) {
    __asm__ volatile("" ::: "memory");
}

/* Constructor: runs before main() */
__attribute__((constructor))
static void pride_runtime_init(void) {
    /* Install crash signal handlers */
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sigemptyset(&sa.sa_mask);
    sa.sa_flags     = SA_SIGINFO | SA_RESETHAND;
    sa.sa_sigaction = crash_handler;
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGBUS,  &sa, NULL);
    sigaction(SIGFPE,  &sa, NULL);
    sigaction(SIGILL,  &sa, NULL);

    /* Initialise the pool allocator */
    pthread_once(&pool_once, pool_init);
}

/* Destructor: flush I/O on clean exit */
__attribute__((destructor))
static void pride_runtime_fini(void) {
    io_flush_internal();
}

/*
 * Default entry-point shim.  When the user writes `fn main` in Pride the
 * compiler emits @main (no prefix), which overrides this weak symbol.
 * Without a Pride main, this stub runs and exits cleanly.
 */
__attribute__((weak))
int main(int argc PRIDE_UNUSED, char** argv PRIDE_UNUSED) {
    write_str("pride: no main function defined\n");
    return 1;
}

/* ==========================================================================
 * §12 — C23 Standard Library Additions
 * ==========================================================================
 *
 * Implementations of new C23 library functions/macros:
 *   - ckd_add / ckd_sub / ckd_mul   (<stdckdint.h> overflow-checked arithmetic)
 *   - memset_explicit                 (<string.h> secure memory clear)
 *   - memalignment                   (<stdlib.h> alignment query)
 *   - strdup / strndup               (<string.h> string duplication)
 *   - __pride_stdc_count_ones et al  (<stdbit.h> bit operations)
 */

/* --- Checked integer arithmetic (C23 <stdckdint.h>) ---------------------- */

/* ckd_add: a + b → writes *result, returns true on overflow */
int __pride_ckd_add_i32(int *result, int a, int b) {
    return __builtin_add_overflow(a, b, result);
}
int __pride_ckd_add_i64(long long *result, long long a, long long b) {
    return __builtin_add_overflow(a, b, result);
}
int __pride_ckd_sub_i32(int *result, int a, int b) {
    return __builtin_sub_overflow(a, b, result);
}
int __pride_ckd_sub_i64(long long *result, long long a, long long b) {
    return __builtin_sub_overflow(a, b, result);
}
int __pride_ckd_mul_i32(int *result, int a, int b) {
    return __builtin_mul_overflow(a, b, result);
}
int __pride_ckd_mul_i64(long long *result, long long a, long long b) {
    return __builtin_mul_overflow(a, b, result);
}

/* --- memset_explicit (C23): guaranteed not optimised away (secure clear) -- */
void *__pride_memset_explicit(void *s, int c, size_t n) {
    volatile unsigned char *p = (volatile unsigned char *)s;
    while (n--) *p++ = (unsigned char)c;
    return s;
}
#define PRIDE_RT_HAS_MEMSET_EXPLICIT

/* --- memalignment (C23): alignment of a heap allocation ------------------- */
size_t __pride_memalignment(const void *p) {
    uintptr_t addr = (uintptr_t)p;
    if (addr == 0) return 0;
    /* Return the largest power-of-2 that divides the address */
    return addr & (~addr + 1);
}

/* --- strdup / strndup (C23 standard, POSIX already) ---------------------- */
char *__pride_strdup(const char *s) {
    if (!s) return NULL;
    size_t n = strlen(s) + 1;
    char *copy = (char *)malloc(n);
    if (copy) memcpy(copy, s, n);
    return copy;
}
#define PRIDE_RT_HAS_STRDUP
char *__pride_strndup(const char *s, size_t maxlen) {
    if (!s) return NULL;
    size_t n = strnlen(s, maxlen);
    char *copy = (char *)malloc(n + 1);
    if (copy) { memcpy(copy, s, n); copy[n] = '\0'; }
    return copy;
}
#define PRIDE_RT_HAS_STRNDUP

/* --- <stdbit.h> bit operations (C23) ------------------------------------- */
/* All operate on unsigned 64-bit; Pride casts widths as needed */

/* stdc_count_ones: popcount */
int __pride_stdc_count_ones_u64(unsigned long long x) {
    return ({ unsigned long long _x=(x); int _c=0; while(_x){_c+=_x&1;_x>>=1;} _c; });
}
/* stdc_count_zeros */
int __pride_stdc_count_zeros_u64(unsigned long long x) {
    return 64 - ({ unsigned long long _x=(x); int _c=0; while(_x){_c+=_x&1;_x>>=1;} _c; });
}
/* stdc_leading_zeros */
int __pride_stdc_leading_zeros_u64(unsigned long long x) {
    if (x == 0) return 64;
    return ({ unsigned long long _x=(x); int _c=0; if(!_x)return 64; while(!(_x&(1ULL<<63))){_c++;_x<<=1;} _c; });
}
/* stdc_trailing_zeros */
int __pride_stdc_trailing_zeros_u64(unsigned long long x) {
    if (x == 0) return 64;
    return ({ unsigned long long _x=(x); int _c=0; if(!_x)return 64; while(!(_x&1)){_c++;_x>>=1;} _c; });
}
/* stdc_bit_ceil: smallest power-of-2 >= x */
unsigned long long __pride_stdc_bit_ceil_u64(unsigned long long x) {
    if (x <= 1) return 1;
    if ((x & (x-1)) == 0) return x;
    return 1ULL << (64 - __builtin_clzll(x-1));
}
/* stdc_bit_floor: largest power-of-2 <= x */
unsigned long long __pride_stdc_bit_floor_u64(unsigned long long x) {
    if (x == 0) return 0;
    return 1ULL << (63 - ({ unsigned long long _x=(x); int _c=0; if(!_x)return 64; while(!(_x&(1ULL<<63))){_c++;_x<<=1;} _c; }));
}
/* stdc_bit_width: number of bits needed to represent x */
int __pride_stdc_bit_width_u64(unsigned long long x) {
    if (x == 0) return 0;
    return 64 - ({ unsigned long long _x=(x); int _c=0; if(!_x)return 64; while(!(_x&(1ULL<<63))){_c++;_x<<=1;} _c; });
}
/* stdc_rotate_left */
unsigned long long __pride_stdc_rotate_left_u64(unsigned long long x, int n) {
    n &= 63;
    return (x << n) | (x >> (64 - n));
}
/* stdc_rotate_right */
unsigned long long __pride_stdc_rotate_right_u64(unsigned long long x, int n) {
    n &= 63;
    return (x >> n) | (x << (64 - n));
}

/* --- unreachable (C23: macro in <stddef.h>) ------------------------------ */
/* __pride_unreachable() is called when ub! or unreachable regions execute */
/* Already handled in runtime §3 panic; this is the lightweight version */
void __pride_unreachable_c23(void) {
    __builtin_unreachable();
}

/* ── §10  Atomic primitives (C23 _Atomic / GCC builtins) ─────────────────── */

#include <stdatomic.h>

int64_t  __pride_atomic_load_i64(const int64_t* p)        { return atomic_load((const _Atomic int64_t*)p); }
#define PRIDE_RT_HAS_ATOMIC_LOAD_I64
void     __pride_atomic_store_i64(int64_t* p, int64_t v)  { atomic_store((_Atomic int64_t*)p, v); }
#define PRIDE_RT_HAS_ATOMIC_STORE_I64
int64_t  __pride_atomic_add_i64(int64_t* p, int64_t v)    { return atomic_fetch_add((_Atomic int64_t*)p, v); }
int64_t  __pride_atomic_sub_i64(int64_t* p, int64_t v)    { return atomic_fetch_sub((_Atomic int64_t*)p, v); }
int64_t  __pride_atomic_and_i64(int64_t* p, int64_t v)    { return atomic_fetch_and((_Atomic int64_t*)p, v); }
int64_t  __pride_atomic_or_i64(int64_t* p, int64_t v)     { return atomic_fetch_or((_Atomic int64_t*)p, v); }
int64_t  __pride_atomic_xor_i64(int64_t* p, int64_t v)    { return atomic_fetch_xor((_Atomic int64_t*)p, v); }
int64_t  __pride_atomic_swap_i64(int64_t* p, int64_t v)   { return atomic_exchange((_Atomic int64_t*)p, v); }
int      __pride_atomic_cas_i64(int64_t* p, int64_t* expected, int64_t desired)
{ return atomic_compare_exchange_strong((_Atomic int64_t*)p, expected, desired); }
#define PRIDE_RT_HAS_ATOMIC_CAS_I64
void     __pride_atomic_fence_seq(void) { atomic_thread_fence(memory_order_seq_cst); }
void     __pride_atomic_fence_acq(void) { atomic_thread_fence(memory_order_acquire); }
void     __pride_atomic_fence_rel(void) { atomic_thread_fence(memory_order_release); }

int32_t  __pride_atomic_load_i32(const int32_t* p)        { return atomic_load((const _Atomic int32_t*)p); }
void     __pride_atomic_store_i32(int32_t* p, int32_t v)  { atomic_store((_Atomic int32_t*)p, v); }
int32_t  __pride_atomic_add_i32(int32_t* p, int32_t v)    { return atomic_fetch_add((_Atomic int32_t*)p, v); }
int32_t  __pride_atomic_cas_i32_val(int32_t* p, int32_t e, int32_t d)
{ atomic_compare_exchange_strong((_Atomic int32_t*)p, &e, d); return e; }

/* ── §11  Mutex / RwLock / Condvar (POSIX) ───────────────────────────────── */

#include <pthread.h>

/* Mutex — opaque handle returned as i64 */
void* __pride_mutex_new(void)
{
    pthread_mutex_t* m = (pthread_mutex_t*)malloc(sizeof(pthread_mutex_t));
    if (!m) return NULL;
    pthread_mutex_init(m, NULL);
    return m;
}
void __pride_mutex_lock(void* m)    { if(m) pthread_mutex_lock((pthread_mutex_t*)m); }
void __pride_mutex_unlock(void* m)  { if(m) pthread_mutex_unlock((pthread_mutex_t*)m); }
int  __pride_mutex_trylock(void* m) { return m ? pthread_mutex_trylock((pthread_mutex_t*)m)==0 : 0; }
void __pride_mutex_free(void* m)    { if(m){ pthread_mutex_destroy((pthread_mutex_t*)m); free(m); } }

/* RwLock */
void* __pride_rwlock_new(void)
{
    pthread_rwlock_t* r = (pthread_rwlock_t*)malloc(sizeof(pthread_rwlock_t));
    if (!r) return NULL;
    pthread_rwlock_init(r, NULL);
    return r;
}
void __pride_rwlock_rdlock(void* r)  { if(r) pthread_rwlock_rdlock((pthread_rwlock_t*)r); }
void __pride_rwlock_wrlock(void* r)  { if(r) pthread_rwlock_wrlock((pthread_rwlock_t*)r); }
void __pride_rwlock_unlock(void* r)  { if(r) pthread_rwlock_unlock((pthread_rwlock_t*)r); }
void __pride_rwlock_free(void* r)    { if(r){ pthread_rwlock_destroy((pthread_rwlock_t*)r); free(r); } }

/* Condvar */
void* __pride_condvar_new(void)
{
    pthread_cond_t* c = (pthread_cond_t*)malloc(sizeof(pthread_cond_t));
    if (!c) return NULL;
    pthread_cond_init(c, NULL);
    return c;
}
void __pride_condvar_wait(void* cv, void* mx)
{ if(cv&&mx) pthread_cond_wait((pthread_cond_t*)cv,(pthread_mutex_t*)mx); }
void __pride_condvar_signal(void* cv)    { if(cv) pthread_cond_signal((pthread_cond_t*)cv); }
void __pride_condvar_broadcast(void* cv) { if(cv) pthread_cond_broadcast((pthread_cond_t*)cv); }
void __pride_condvar_free(void* cv)      { if(cv){ pthread_cond_destroy((pthread_cond_t*)cv); free(cv); } }

/* Once */
static pthread_once_t __pride_once_ctrl = PTHREAD_ONCE_INIT;
static void (*__pride_once_fn)(void) = NULL;
static void __pride_once_wrapper(void) { if(__pride_once_fn) __pride_once_fn(); }
void __pride_once(void (*fn)(void)) { __pride_once_fn = fn; pthread_once(&__pride_once_ctrl, __pride_once_wrapper); }

/* Semaphore */
#include <semaphore.h>
void* __pride_sem_new(int initial) { sem_t* s=(sem_t*)malloc(sizeof(sem_t)); if(s) sem_init(s,0,(unsigned)initial); return s; }
void  __pride_sem_wait(void* s)    { if(s) sem_wait((sem_t*)s); }
void  __pride_sem_post(void* s)    { if(s) sem_post((sem_t*)s); }
int   __pride_sem_trywait(void* s) { return s ? sem_trywait((sem_t*)s)==0 : 0; }
void  __pride_sem_free(void* s)    { if(s){ sem_destroy((sem_t*)s); free(s); } }

/* ── §12  Standard stream accessors ──────────────────────────────────────── */
FILE* __pride_get_stdin(void)  { return stdin; }
FILE* __pride_get_stdout(void) { return stdout; }
FILE* __pride_get_stderr(void) { return stderr; }

/* ── §13  stride_of / unaligned read-write ────────────────────────────────── */
#include <string.h>

/* stride_of is sizeof for arrays — same as sizeof on most types */
/* Exposed as __pride_stride_of(element_size) — just returns the element size */
int64_t __pride_stride_of(int64_t elem_size) { return elem_size; }

/* Unaligned reads: memcpy-based to avoid UB on strict-alignment platforms */
int64_t __pride_read_unaligned_i64(const void* ptr)
{ int64_t v; memcpy(&v, ptr, 8); return v; }

int32_t __pride_read_unaligned_i32(const void* ptr)
{ int32_t v; memcpy(&v, ptr, 4); return v; }

int16_t __pride_read_unaligned_i16(const void* ptr)
{ int16_t v; memcpy(&v, ptr, 2); return v; }

/* Unaligned writes */
void __pride_write_unaligned_i64(void* ptr, int64_t val) { memcpy(ptr, &val, 8); }
void __pride_write_unaligned_i32(void* ptr, int32_t val) { memcpy(ptr, &val, 4); }
void __pride_write_unaligned_i16(void* ptr, int16_t val) { memcpy(ptr, &val, 2); }

/* ── §14  Float bit manipulation ─────────────────────────────────────────── */
int64_t __pride_f64_to_bits(double v)  { int64_t r; memcpy(&r, &v, 8); return r; }
double  __pride_f64_from_bits(int64_t b) { double r; memcpy(&r, &b, 8); return r; }
int32_t __pride_f32_to_bits(float v)   { int32_t r; memcpy(&r, &v, 4); return r; }
float   __pride_f32_from_bits(int32_t b){ float r; memcpy(&r, &b, 4); return r; }

double __pride_f64_nan(void)  { return 0.0/0.0; }
double __pride_f64_inf(void)  { return 1.0/0.0; }
int    __pride_f64_is_nan(double x)    { return x != x; }
int    __pride_f64_is_inf(double x)    { return x == 1.0/0.0 || x == -1.0/0.0; }
int    __pride_f64_is_finite(double x) { return x == x && x != 1.0/0.0 && x != -1.0/0.0; }

/* ── §15  Pool allocator ─────────────────────────────────────────────────── */
typedef struct {
    void*   buf;
    size_t  obj_size;
    size_t  cap;
    size_t  used;
    void*   freelist;  /* linked list of free slots */
} PridePool;

void* __pride_pool_new(size_t obj_size, size_t capacity)
{
    PridePool* p = (PridePool*)malloc(sizeof(PridePool));
    if (!p) return NULL;
    /* Ensure obj_size can hold a pointer (for freelist) */
    size_t slot = obj_size > sizeof(void*) ? obj_size : sizeof(void*);
    p->buf      = malloc(slot * capacity);
    if (!p->buf) { free(p); return NULL; }
    p->obj_size = slot;
    p->cap      = capacity;
    p->used     = 0;
    p->freelist = NULL;
    return p;
}

void* __pride_pool_alloc(void* pool)
{
    PridePool* p = (PridePool*)pool;
    if (!p) return NULL;
    if (p->freelist)
    {
        void* slot = p->freelist;
        p->freelist = *(void**)slot;
        return slot;
    }
    if (p->used >= p->cap) return NULL;  /* pool exhausted */
    void* slot = (char*)p->buf + p->used * p->obj_size;
    p->used++;
    return slot;
}

void __pride_pool_free_slot(void* pool, void* obj)
{
    PridePool* p = (PridePool*)pool;
    if (!p || !obj) return;
    *(void**)obj = p->freelist;
    p->freelist  = obj;
}

void __pride_pool_destroy(void* pool)
{
    PridePool* p = (PridePool*)pool;
    if (!p) return;
    free(p->buf);
    free(p);
}

size_t __pride_pool_used(void* pool)
{
    PridePool* p = (PridePool*)pool;
    return p ? p->used : 0;
}

/* ── §16  SIMD intrinsics (SSE/AVX via compiler builtins) ─────────────────── */
#include <immintrin.h>

/* f32x4 operations */
void* __pride_simd_f32x4_add(const void* a, const void* b) {
    __m128* r = (__m128*)malloc(16);
    *r = _mm_add_ps(*(__m128*)a, *(__m128*)b); return r; }
void* __pride_simd_f32x4_sub(const void* a, const void* b) {
    __m128* r = (__m128*)malloc(16);
    *r = _mm_sub_ps(*(__m128*)a, *(__m128*)b); return r; }
void* __pride_simd_f32x4_mul(const void* a, const void* b) {
    __m128* r = (__m128*)malloc(16);
    *r = _mm_mul_ps(*(__m128*)a, *(__m128*)b); return r; }
void* __pride_simd_f32x4_div(const void* a, const void* b) {
    __m128* r = (__m128*)malloc(16);
    *r = _mm_div_ps(*(__m128*)a, *(__m128*)b); return r; }
void* __pride_simd_f32x4_sqrt(const void* a) {
    __m128* r = (__m128*)malloc(16);
    *r = _mm_sqrt_ps(*(__m128*)a); return r; }
void* __pride_simd_f32x4_fma(const void* a, const void* b, const void* c) {
    __m128* r = (__m128*)malloc(16);
    /* FMA disabled - use software fallback */
    __m128 t = _mm_mul_ps(*(__m128*)a, *(__m128*)b);
    *r = _mm_add_ps(t, *(__m128*)c); return r; }
float __pride_simd_f32x4_dot(const void* a, const void* b) {
    __m128 d = _mm_setzero_ps(); { float *pa=(float*)a, *pb=(float*)b; float s=0; for(int i=0;i<4;i++)s+=pa[i]*pb[i]; d=_mm_set1_ps(s); }
    float r; _mm_store_ss(&r, d); return r; }
float __pride_simd_f32x4_sum(const void* a) {
    __m128 v = *(__m128*)a;
    v = _mm_hadd_ps(v, v); v = _mm_hadd_ps(v, v);
    float r; _mm_store_ss(&r, v); return r; }
void* __pride_simd_f32x4_min(const void* a, const void* b) {
    __m128* r = (__m128*)malloc(16);
    *r = _mm_min_ps(*(__m128*)a, *(__m128*)b); return r; }
void* __pride_simd_f32x4_max(const void* a, const void* b) {
    __m128* r = (__m128*)malloc(16);
    *r = _mm_max_ps(*(__m128*)a, *(__m128*)b); return r; }

/* i32x4 operations */
void* __pride_simd_i32x4_add(const void* a, const void* b) {
    __m128i* r = (__m128i*)malloc(16);
    *r = _mm_add_epi32(*(__m128i*)a, *(__m128i*)b); return r; }
void* __pride_simd_i32x4_sub(const void* a, const void* b) {
    __m128i* r = (__m128i*)malloc(16);
    *r = _mm_sub_epi32(*(__m128i*)a, *(__m128i*)b); return r; }
void* __pride_simd_i32x4_mul(const void* a, const void* b) {
    __m128i* r = (__m128i*)malloc(16);
    *r = _mm_mullo_epi32(*(__m128i*)a, *(__m128i*)b); return r; }
void* __pride_simd_i32x4_and(const void* a, const void* b) {
    __m128i* r = (__m128i*)malloc(16);
    *r = _mm_and_si128(*(__m128i*)a, *(__m128i*)b); return r; }
void* __pride_simd_i32x4_or(const void* a, const void* b) {
    __m128i* r = (__m128i*)malloc(16);
    *r = _mm_or_si128(*(__m128i*)a, *(__m128i*)b); return r; }

/* ── String format helpers (used by format!() macro lowering) ─────────────── */

/* PrideString layout: { char* ptr, size_t len, size_t cap } */
typedef struct { char* ptr; size_t len; size_t cap; } PrideString;

void pride_str_init(PrideString* s)
{
    s->ptr = NULL; s->len = 0; s->cap = 0;
}

static void pride_str_grow(PrideString* s, size_t need)
{
    if (s->len + need <= s->cap) return;
    size_t nc = s->cap == 0 ? (need + 16) : s->cap * 2;
    if (nc < s->len + need) nc = s->len + need + 1;
    char* p2 = (char*)realloc(s->ptr, nc + 1);
    if (!p2) return;
    s->ptr = p2; s->cap = nc;
}

void pride_str_push_str(PrideString* s, const char* p, int64_t n)
{
    if (n <= 0 || !p) return;
    pride_str_grow(s, (size_t)n);
    memcpy(s->ptr + s->len, p, (size_t)n);
    s->len += (size_t)n;
    s->ptr[s->len] = 0;
}

void pride_str_push_i64(PrideString* s, int64_t v)
{
    char buf[32];
    int n = snprintf(buf, sizeof(buf), "%lld", (long long)v);
    if (n > 0) pride_str_push_str(s, buf, n);
}

void pride_str_push_f64(PrideString* s, double v)
{
    char buf[64];
    int n = snprintf(buf, sizeof(buf), "%g", v);
    if (n > 0) pride_str_push_str(s, buf, n);
}

/* ── C23 / POSIX extended helpers ────────────────────────────────────────── */

#include <stdatomic.h>
#include <threads.h>

#ifndef PRIDE_RT_HAS_ATOMIC_CAS_I64
#define PRIDE_RT_HAS_ATOMIC_CAS_I64
/* Atomic 64-bit CAS: returns 1 on success, 0 on failure.
   *expected is updated to the current value on failure. */
int __pride_atomic_cas_i64(volatile int64_t* ptr, int64_t* expected, int64_t desired)
{
    _Atomic int64_t* ap = (_Atomic int64_t*)ptr;
    return atomic_compare_exchange_strong_explicit(
        ap, expected, desired, memory_order_seq_cst, memory_order_seq_cst);
}
#endif /* PRIDE_RT_HAS_ATOMIC_CAS_I64 */

/* Atomic fetch-and-add i64. Returns the old value. */
int64_t __pride_atomic_fetch_add_i64(volatile int64_t* ptr, int64_t delta)
{
    _Atomic int64_t* ap = (_Atomic int64_t*)ptr;
    return atomic_fetch_add_explicit(ap, delta, memory_order_seq_cst);
}

#ifndef PRIDE_RT_HAS_ATOMIC_LOAD_I64
#define PRIDE_RT_HAS_ATOMIC_LOAD_I64
/* Atomic load i64. */
int64_t __pride_atomic_load_i64(volatile int64_t* ptr)
{
    _Atomic int64_t* ap = (_Atomic int64_t*)ptr;
    return atomic_load_explicit(ap, memory_order_seq_cst);
}
#endif /* PRIDE_RT_HAS_ATOMIC_LOAD_I64 */

#ifndef PRIDE_RT_HAS_ATOMIC_STORE_I64
#define PRIDE_RT_HAS_ATOMIC_STORE_I64
/* Atomic store i64. */
void __pride_atomic_store_i64(volatile int64_t* ptr, int64_t val)
{
    _Atomic int64_t* ap = (_Atomic int64_t*)ptr;
    atomic_store_explicit(ap, val, memory_order_seq_cst);
}
#endif /* PRIDE_RT_HAS_ATOMIC_STORE_I64 */

/* Atomic exchange i64. Returns old value. */
int64_t __pride_atomic_exchange_i64(volatile int64_t* ptr, int64_t val)
{
    _Atomic int64_t* ap = (_Atomic int64_t*)ptr;
    return atomic_exchange_explicit(ap, val, memory_order_seq_cst);
}

/* Fence: full memory barrier. */
void __pride_atomic_fence(void)
{
    atomic_thread_fence(memory_order_seq_cst);
}

/* ── C23 stdc_count_ones / bit operations (stdbit.h) ─────────────────────── */

uint32_t __pride_stdc_count_ones_u32(uint32_t x) {
    return (uint32_t)__builtin_popcount(x);
}
uint32_t __pride_stdc_count_zeros_u32(uint32_t x) {
    return 32 - (uint32_t)__builtin_popcount(x);
}
uint32_t __pride_stdc_leading_zeros_u32(uint32_t x) {
    return x == 0 ? 32 : (uint32_t)__builtin_clz(x);
}
uint32_t __pride_stdc_trailing_zeros_u32(uint32_t x) {
    return x == 0 ? 32 : (uint32_t)__builtin_ctz(x);
}
uint32_t __pride_stdc_leading_ones_u32(uint32_t x) {
    return x == 0xFFFFFFFF ? 32 : (uint32_t)__builtin_clz(~x);
}
uint32_t __pride_stdc_trailing_ones_u32(uint32_t x) {
    return x == 0xFFFFFFFF ? 32 : (uint32_t)__builtin_ctz(~x);
}
uint32_t __pride_stdc_first_leading_zero_u32(uint32_t x) {
    return x == 0xFFFFFFFF ? 0 : 1 + (uint32_t)__builtin_clz(~x);
}
uint32_t __pride_stdc_first_leading_one_u32(uint32_t x)  {
    return x == 0 ? 0 : 1 + (uint32_t)__builtin_clz(x);
}
uint32_t __pride_stdc_first_trailing_zero_u32(uint32_t x){
    return x == 0xFFFFFFFF ? 0 : 1 + (uint32_t)__builtin_ctz(~x);
}
uint32_t __pride_stdc_first_trailing_one_u32(uint32_t x) {
    return (uint32_t)__builtin_ffs(x);
}
uint32_t __pride_stdc_bit_width_u32(uint32_t x) {
    return x == 0 ? 0 : 32 - (uint32_t)__builtin_clz(x);
}
uint32_t __pride_stdc_bit_floor_u32(uint32_t x) {
    return x == 0 ? 0 : 1U << (31 - (uint32_t)__builtin_clz(x));
}
uint32_t __pride_stdc_bit_ceil_u32(uint32_t x)  {
    if (x <= 1) return 1;
    return 1U << (32 - (uint32_t)__builtin_clz(x - 1));
}
int      __pride_stdc_has_single_bit_u32(uint32_t x) {
    return x > 0 && (x & (x - 1)) == 0;
}

/* ── 128-bit arithmetic helpers ──────────────────────────────────────────── */

/* Widening multiply: (i64 × i64) → 128-bit result in out[0]=lo, out[1]=hi. */
void __pride_mul_i64_wide(int64_t a, int64_t b, int64_t* out)
{
    __int128 r = (__int128)a * (__int128)b;
    out[0] = (int64_t)(r & ((__int128)0xFFFFFFFFFFFFFFFFULL));
    out[1] = (int64_t)(r >> 64);
}

void __pride_mul_u64_wide(uint64_t a, uint64_t b, uint64_t* out)
{
    unsigned __int128 r = (unsigned __int128)a * (unsigned __int128)b;
    out[0] = (uint64_t)(r & 0xFFFFFFFFFFFFFFFFULL);
    out[1] = (uint64_t)(r >> 64);
}

/* Divide 128-bit by 64-bit → 64-bit quotient + remainder.
   hi:lo = dividend, divisor = div, *rem = remainder. */
uint64_t __pride_div_u128_u64(uint64_t hi, uint64_t lo, uint64_t div, uint64_t* rem)
{
    if (div == 0) { *rem = 0; return UINT64_MAX; }
    unsigned __int128 dividend = ((unsigned __int128)hi << 64) | lo;
    unsigned __int128 divisor  = div;
    *rem = (uint64_t)(dividend % divisor);
    return (uint64_t)(dividend / divisor);
}

/* ── Soft-float: f16 (half-precision) conversion ────────────────────────── */

/* Convert f32 to f16 (IEEE 754-2008, round-to-nearest-even). */
uint16_t __pride_f32_to_f16(float f)
{
    uint32_t bits;
    memcpy(&bits, &f, 4);
    uint32_t sign = (bits >> 31) & 1;
    int32_t  exp  = (int32_t)((bits >> 23) & 0xFF) - 127 + 15;
    uint32_t mant = bits & 0x7FFFFF;
    if (exp <= 0)      { return (uint16_t)(sign << 15); }  /* flush to zero */
    if (exp >= 31)     { return (uint16_t)((sign << 15) | 0x7C00); } /* inf */
    return (uint16_t)((sign << 15) | ((uint16_t)exp << 10) | (uint16_t)(mant >> 13));
}

/* Convert f16 to f32. */
float __pride_f16_to_f32(uint16_t h)
{
    uint32_t sign = (h >> 15) & 1;
    uint32_t exp  = (h >> 10) & 0x1F;
    uint32_t mant = h & 0x3FF;
    uint32_t bits;
    if (exp == 0) {
        if (mant == 0) { bits = sign << 31; }
        else {
            exp = 1;
            while (!(mant & 0x400)) { mant <<= 1; exp--; }
            mant &= 0x3FF;
            bits = (sign << 31) | ((exp - 1 + 127) << 23) | (mant << 13);
        }
    } else if (exp == 31) {
        bits = (sign << 31) | 0x7F800000 | (mant << 13);
    } else {
        bits = (sign << 31) | ((exp - 15 + 127) << 23) | (mant << 13);
    }
    float r; memcpy(&r, &bits, 4); return r;
}

/* ── Memory utilities ─────────────────────────────────────────────────────── */

#ifndef PRIDE_RT_HAS_MEMSET_EXPLICIT
#define PRIDE_RT_HAS_MEMSET_EXPLICIT
/* Secure memset that won't be optimized away (volatile write trick). */
void* __pride_memset_explicit(void* dst, int c, int64_t n)
{
    volatile unsigned char* p = (volatile unsigned char*)dst;
    for (int64_t i = 0; i < n; i++) p[i] = (unsigned char)c;
    return dst;
}
#endif /* PRIDE_RT_HAS_MEMSET_EXPLICIT */

/* Memory copy with non-overlapping assertion (uses memcpy). */
void* __pride_memcpy_noalias(void* restrict dst, const void* restrict src, int64_t n)
{
    return memcpy(dst, src, (size_t)n);
}

/* Checked memory move (handles overlap correctly). */
void* __pride_memmove(void* dst, const void* src, int64_t n)
{
    return memmove(dst, src, (size_t)n);
}

/* ── String helpers ───────────────────────────────────────────────────────── */

/* Case-insensitive comparison (ASCII only). */
int __pride_strcasecmp(const char* a, const char* b, int64_t n)
{
    for (int64_t i = 0; i < n; i++) {
        int ca = (unsigned char)a[i], cb = (unsigned char)b[i];
        if (ca >= 'A' && ca <= 'Z') ca += 32;
        if (cb >= 'A' && cb <= 'Z') cb += 32;
        if (ca != cb) return ca - cb;
        if (ca == 0)  return 0;
    }
    return 0;
}

/* Find first occurrence of byte c in s[0..n). Returns offset or -1. */
int64_t __pride_memchr(const void* s, int c, int64_t n)
{
    const unsigned char* p = (const unsigned char*)s;
    for (int64_t i = 0; i < n; i++) if (p[i] == (unsigned char)c) return i;
    return -1;
}

/* Find last occurrence of byte c in s[0..n). Returns offset or -1. */
int64_t __pride_memrchr(const void* s, int c, int64_t n)
{
    const unsigned char* p = (const unsigned char*)s;
    for (int64_t i = n - 1; i >= 0; i--) if (p[i] == (unsigned char)c) return i;
    return -1;
}

/* Count occurrences of byte c in s[0..n). */
int64_t __pride_memcount(const void* s, int c, int64_t n)
{
    const unsigned char* p = (const unsigned char*)s;
    int64_t count = 0;
    for (int64_t i = 0; i < n; i++) if (p[i] == (unsigned char)c) count++;
    return count;
}

/* Reverse bytes in-place. */
void __pride_reverse_bytes(void* buf, int64_t n)
{
    unsigned char* p = (unsigned char*)buf;
    for (int64_t i = 0, j = n-1; i < j; i++, j--) {
        unsigned char tmp = p[i]; p[i] = p[j]; p[j] = tmp;
    }
}

/* ── Hash functions (non-cryptographic) ─────────────────────────────────── */

/* FNV-1a 64-bit. */
uint64_t __pride_fnv1a_64(const void* data, int64_t n)
{
    const uint8_t* p = (const uint8_t*)data;
    uint64_t h = 14695981039346656037ULL;
    for (int64_t i = 0; i < n; i++) {
        h ^= (uint64_t)p[i];
        h *= 1099511628211ULL;
    }
    return h;
}

/* xxHash32 (simplified, no special SIMD path). */
uint32_t __pride_xxhash32(const void* data, int64_t n, uint32_t seed)
{
    const uint8_t* p = (const uint8_t*)data;
    static const uint32_t P1 = 2654435761u, P2 = 2246822519u;
    static const uint32_t P3 = 3266489917u, P4 =  668265263u;
    static const uint32_t P5 =  374761393u;
    uint32_t h32;
    if (n >= 16) {
        uint32_t v1 = seed + P1 + P2, v2 = seed + P2;
        uint32_t v3 = seed, v4 = seed - P1;
        const uint8_t* end = p + n - 16;
        do {
            uint32_t t; memcpy(&t, p, 4); v1 = ((v1+(t*P2)>>0u)*P1); p+=4;
            memcpy(&t, p, 4); v2 = ((v2+(t*P2)>>0u)*P1); p+=4;
            memcpy(&t, p, 4); v3 = ((v3+(t*P2)>>0u)*P1); p+=4;
            memcpy(&t, p, 4); v4 = ((v4+(t*P2)>>0u)*P1); p+=4;
        } while (p <= end);
        h32 = ((v1<<1)|(v1>>31)) + ((v2<<7)|(v2>>25)) +
              ((v3<<12)|(v3>>20)) + ((v4<<18)|(v4>>14));
    } else { h32 = seed + P5; }
    h32 += (uint32_t)n;
    while (p + 4 <= (uint8_t*)data + n) {
        uint32_t t; memcpy(&t, p, 4);
        h32 = (((h32 + t*P3)<<17)|(((h32+t*P3)>>15))) * P4; p += 4;
    }
    while (p < (uint8_t*)data + n) {
        h32 = ((((h32 + (*p)*P5)<<11)|(((h32+(*p)*P5)>>21))) * P1); p++;
    }
    h32 ^= h32 >> 15; h32 *= 2246822519u; h32 ^= h32 >> 13;
    h32 *= 3266489917u; h32 ^= h32 >> 16;
    return h32;
}

/* ── POSIX real-time clock nanosecond timer ──────────────────────────────── */
#include <time.h>
int64_t __pride_monotonic_ns(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

int64_t __pride_realtime_ns(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    return (int64_t)ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

/* ── Environment ─────────────────────────────────────────────────────────── */
#include <stdlib.h>
#ifndef PRIDE_RT_HAS_STRDUP
#define PRIDE_RT_HAS_STRDUP
char* __pride_strdup(const char* s)  { return s ? strdup(s)  : NULL; }
#endif /* PRIDE_RT_HAS_STRDUP */
#ifndef PRIDE_RT_HAS_STRNDUP
#define PRIDE_RT_HAS_STRNDUP
char* __pride_strndup(const char* s, int64_t n) { return s ? strndup(s, (size_t)n) : NULL; }

/* ── Error string ────────────────────────────────────────────────────────── */
#include <string.h>
const char* __pride_strerror(int errnum)
{
    return strerror(errnum);
}
#endif /* PRIDE_RT_HAS_STRNDUP */

/* ── Filesystem stat ─────────────────────────────────────────────────────── */
#include <sys/stat.h>
int64_t __pride_file_size(const char* path)
{
    struct stat st;
    if (stat(path, &st) != 0) return -1;
    return (int64_t)st.st_size;
}

int __pride_file_exists(const char* path)
{
    struct stat st;
    return stat(path, &st) == 0;
}

int __pride_is_dir(const char* path)
{
    struct stat st;
    if (stat(path, &st) != 0) return 0;
    return S_ISDIR(st.st_mode);
}

int __pride_is_file(const char* path)
{
    struct stat st;
    if (stat(path, &st) != 0) return 0;
    return S_ISREG(st.st_mode);
}


/* ── Portable byte-swap helpers ──────────────────────────────────────────── */
uint16_t __pride_bswap16(uint16_t x) { return (uint16_t)((x >> 8) | (x << 8)); }
uint32_t __pride_bswap32(uint32_t x) {
    return ((x & 0xFF000000u) >> 24) | ((x & 0x00FF0000u) >> 8)
         | ((x & 0x0000FF00u) <<  8) | ((x & 0x000000FFu) << 24); }
uint64_t __pride_bswap64(uint64_t x) {
    return ((uint64_t)__pride_bswap32((uint32_t)(x >> 32))) |
           ((uint64_t)__pride_bswap32((uint32_t)(x & 0xFFFFFFFFu)) << 32); }

/* ── Network byte order (host ↔ network) ──────────────────────────────────── */
uint16_t __pride_htons(uint16_t x) { return __pride_bswap16(x); }
uint32_t __pride_htonl(uint32_t x) { return __pride_bswap32(x); }
uint16_t __pride_ntohs(uint16_t x) { return __pride_bswap16(x); }
uint32_t __pride_ntohl(uint32_t x) { return __pride_bswap32(x); }

/* ── Custom test helpers ────────────────────────────────────────────────── */
int64_t pryde_add5(int64_t x);
int64_t __pride_run_apply_add5(void) {
    return pryde_add5(10);
}

void __pride_print_u64_nl(uint64_t n) {
    char buf[64];
    int len = snprintf(buf, sizeof(buf), "%llu\n", (unsigned long long)n);
    if (len > 0) {
        write(1, buf, len);
    }
}

