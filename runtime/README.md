# Pride Runtime — production

"The over-engineered C."

This is compiler_rt that every Pride-compiled binary links against.
It is self-contained, has no external dependencies beyond POSIX and libc,
and every subsystem is replaceable independently without touching the frontend.

## Building

```sh
# Step 1: Compile the Pride compiler_rt (gcc for the C runtime only).
# Both TUs are required: compiler_rt.c has the language-level runtime
# (effects, strings, allocator, ...); compiler_rt_arch.c supplies the
# architecture/ABI intrinsics the LLVM-generated code calls directly
# (e.g. 128-bit division for i128/u128 arithmetic) — a binary missing it
# will fail to link with undefined-symbol errors for any program touching
# those features.
gcc -O2 -std=c11 -pthread -Wall -Wextra -fno-strict-aliasing \
    -msse4.1 -fPIC -c runtime/compiler_rt.c -o runtime/compiler_rt.o
gcc -O2 -std=c11 -pthread -Wall -Wextra -fno-strict-aliasing \
    -msse4.1 -fPIC -c runtime/compiler_rt_arch.c -o runtime/compiler_rt_arch.o
# Or: make runtime

# Step 2: Emit LLVM 22 IR from a Pride source file
./pride --emit-llvm output.ll source.pie

# Step 3: Assemble → optimise → compile (pure LLVM 22, no Clang)
llvm-as-22 output.ll -o output.bc
opt-22 -O2 output.bc -o output.opt.bc
llc-22 -filetype=obj -relocation-model=pic output.opt.bc -o output.o

# Step 4: Link with lld-22 (no gcc/Clang in the link step).
# -lgcc/-lgcc_s supply compiler-generated intrinsic calls (128-bit division,
# some popcount/clz paths, etc.) that aren't natively covered by hardware
# instructions on x86-64 — link them even though the link step otherwise
# avoids gcc/Clang, matching tests/run_exec.sh's proven-working recipe.
ld.lld-22 \
  /usr/lib/x86_64-linux-gnu/crt1.o \
  /usr/lib/x86_64-linux-gnu/crti.o \
  output.o runtime/compiler_rt.o runtime/compiler_rt_arch.o \
  /usr/lib/x86_64-linux-gnu/crtn.o \
  -L/usr/lib/x86_64-linux-gnu -L/lib/x86_64-linux-gnu \
  -L/usr/lib/gcc/x86_64-linux-gnu/14 \
  -lc -lpthread -lm -lgcc -lgcc_s \
  --dynamic-linker /lib64/ld-linux-x86-64.so.2 \
  -o program

# Or use the Makefile shortcut:
make compile SRC=source.pie OUT=program
```

## Subsystems

### §1 — Platform macros
Compiler intrinsics (`LIKELY`, `NOINLINE`, `NORETURN`, `COLD`),
`__atomic` builtins, `__thread` TLS. No external headers beyond POSIX.

---

### §2 — Memory: mmap-backed slab pool + large-object allocator

| Object size | Mechanism |
|---|---|
| ≤ 2 KB | 16 size-class pool (8, 16, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768, 1024, 1280, 1536, 2048 bytes). Each class backed by 64 KB slabs via `mmap(MAP_ANONYMOUS)`. Lock-free free-lists using `__atomic_compare_exchange`. |
| > 2 KB | Direct `mmap` with a 16-byte header. `pride_free` calls `munmap` exactly. |

**Thread-safety:** the pool free-lists are CAS-protected; no mutex.
**No sbrk/brk** — all memory comes from `mmap`, so the heap never grows
contiguously and ASLR applies per-slab.

API used by generated code:
```c
void* pride_alloc(size_t bytes);
void* pride_alloc_zeroed(size_t bytes);
void  pride_free(void* ptr, size_t bytes);
```
The standard `@malloc` / `@free` symbols declared in the LLVM IR are libc's
— used only by system libraries (pthread internals, backtrace_symbols, etc.).

---

### §3 — Panic: signal-safe, backtrace-annotated

`__pride_panic(msg_ptr, msg_len)` is the target of `assert`, `unreachable`,
`trap`, and `ub!`. It:

1. Writes the panic message using `write(2)` (async-signal-safe — no stdio).
2. Calls `backtrace()` + `backtrace_symbols_fd()` to dump the stack.
3. Raises `SIGABRT` (not `abort()`) so a debugger or core-dump policy triggers.

Crash signals (`SIGSEGV`, `SIGBUS`, `SIGFPE`, `SIGILL`) are intercepted by a
`SA_SIGINFO` handler installed at startup via `__attribute__((constructor))`.
The handler prints the signal name, fault address (for SIGSEGV), and a full
backtrace before re-raising with the default handler.

---

### §4 — Algebraic effects: ucontext prompt stack

**Not setjmp/longjmp.** We use `ucontext_t` for genuine coroutine-style
suspension and resumption — the computation literally yields to the handler
and resumes where it left off.

```
handle computation { | Op(arg) k → body }
  ↓
__pride_push_handler(frame_id)
  → allocates a 256 KB coroutine stack via pride_alloc
  → saves frame on per-thread __thread stack (max 64 deep)
  → returns the frame pointer as the IR_HANDLER discriminant

Inside the computation:
__pride_perform(op_id, ...)
  → finds matching handler frame (by frame_id)
  → swapcontext(perform_ctx → handler_ctx)  [saves computation, resumes handler]
  → returns the value set by __pride_resume()

Inside the handler arm:
__pride_resume(val)
  → stores val in frame->resume_val
  → swapcontext(handler_ctx → perform_ctx)  [resumes computation]
  → returns val

__pride_pop_handler()
  → frees the 256 KB coroutine stack
  → pops the frame from the per-thread stack
```

**Thread-safety:** the handler stack is `__thread` — one per OS thread.
No locking needed.

#### Upgrading the effects ABI

Replace just the four `__pride_{push_handler,pop_handler,perform,resume}` functions:

| ABI | Speed | Allocation | Notes |
|---|---|---|---|
| **ucontext (current)** | Good | 256 KB/frame | Correct, portable |
| **Evidence passing (Koka)** | Excellent | Zero | Hidden arg per call; no stack switch |
| **Multicore (OCaml 5)** | Excellent | Per-perform | Heap-allocate continuation on perform |
| **setjmp/longjmp** | Good | ~200 B/frame | Cannot resume after longjmp |

No changes to the frontend or `codegen.c3` required for any of these.

---

### §5 — Drop registry: RAII dispatch table

`pride_register_drop(type_id, destructor)` registers a destructor for a type.
`__pride_drop(ptr)` reads the type tag from the first 8 bytes of the object
and dispatches to the registered destructor.

The codegen emits a `__pride_drop` call for every `with r = resource { body }`
block. Types without a registered destructor leak silently (the same as C).

To add RAII: call `pride_register_drop` for your type at startup, and ensure
the codegen packs the type tag as the first field.

---

### §6 — Strings: `PrideStr = { ptr, len }`

Pride's `Str` is a fat pointer — **not** null-terminated.

```c
typedef struct { const char* ptr; uint64_t len; } PrideStr;
```

Provided operations: `pride_str_cmp`, `pride_str_eq`, `pride_str_dup`,
`pride_str_cat`, `pride_str_write`.

IO effect operations map to:
- `IO.write_str(s)` → `__pride_io_write_str`
- `IO.read_line()`  → `__pride_io_read_line` (returns heap-allocated `PrideStr`)
- `IO.write_byte(b)` → `__pride_io_write_byte`
- `IO.read_byte()`   → `__pride_io_read_byte`
- `IO.flush()`      → `__pride_io_flush`

---

### §7 — I/O: buffered stdout

stdout is **8 KB buffered per-thread**. Flushes on newline or buffer full.
stderr is always unbuffered (written directly via `write(2)`).
The flush happens before any blocking read and at program exit via
`__attribute__((destructor))`.

---

### §8 — Tensors: dense row-major + blocked GEMM

Pride's `Tensor<T; D0, D1, ..., Dk>` maps to:

```
PrideTensor header:
  uint64_t rank
  uint64_t dims[rank]
  double   data[prod(dims)]    ← row-major, double precision
```

Operations:
- `__pride_matmul(A, B)` — generalised `@` operator. Rank-2: blocked IJK GEMM
  with 64-element cache tiles. Rank > 2: batched over leading dimensions.
- `__pride_tensor_elemwise(A, B, op)` — elementwise +/-/*/÷.
- `__pride_tensor_new(rank, dims)` — allocate a zeroed tensor.

The GEMM uses 64-element cache blocking (L1-friendly) and register accumulation.
To use CBLAS: compile with `-DPRIDE_USE_CBLAS -lcblas` and add a `#ifdef` block
routing the rank-2 path to `cblas_dgemm`.

---

### §9 — Atomic reference-counting

Shared resources use `__pride_arc_new` / `__pride_arc_retain` / `__pride_arc_release`.
The reference count is stored in a 16-byte-aligned header immediately before the
user pointer. Release at count=1 runs the registered destructor, then frees the header+object.

---

### §10 — Thread support

```c
void* __pride_thread_spawn(void* fn_ptr, void* arg)  // → opaque tid
void  __pride_thread_join(void* tid)
void  __pride_thread_detach(void* tid)
```

Each thread gets its own effect handler stack (TLS), its own I/O buffer,
and its own pool slab (CAS-based sharing happens at the pool class level).

---

### §11 — Startup / shutdown

`__attribute__((constructor))` `pride_runtime_init`:
- Installs signal handlers (SIGSEGV, SIGBUS, SIGFPE, SIGILL)
- Initialises the pool allocator (pthread_once)

`__attribute__((destructor))` `pride_runtime_fini`:
- Flushes the stdout buffer

`main()` is `__attribute__((weak))` — overridden by any Pride `fn main`.

## Symbol table

| Symbol | Called from |
|---|---|
| `__pride_panic(msg, len)` | `assert`, `trap`, `unreachable`, `ub!` |
| `__pride_push_handler(id)` | `handle` block prologue |
| `__pride_pop_handler()` | handler arm epilogue |
| `__pride_perform(op_id, ...)` | `Effect.op(args)` |
| `__pride_resume(val)` | `resume(v)` inside handler arm |
| `__pride_drop(ptr)` | `with r = resource { body }` cleanup |
| `__pride_asm_barrier()` | inline `asm` |
| `__pride_matmul(A, B)` | `a @ b` tensor contraction |
| `__pride_tensor_new(rank, dims)` | `[| ... |]` literal |
| `__pride_tensor_elemwise(A, B, op)` | tensor binary ops |
| `__pride_alloc(bytes)` | `alloc T` |
| `__pride_free(ptr, bytes)` | `free p` |
| `__pride_arc_new(bytes, drop)` | shared resource creation |
| `__pride_arc_retain(ptr)` | shared resource clone |
| `__pride_arc_release(ptr, bytes)` | shared resource drop |
| `__pride_io_write_byte(b)` | `IO.write_byte` |
| `__pride_io_write_str(s)` | `IO.write_str` |
| `__pride_io_read_byte()` | `IO.read_byte` |
| `__pride_io_read_line()` | `IO.read_line` |
| `__pride_io_flush()` | `IO.flush` |
| `__pride_thread_spawn(fn, arg)` | thread spawn |
| `__pride_thread_join(tid)` | thread join |
| `__pride_thread_detach(tid)` | thread detach |
