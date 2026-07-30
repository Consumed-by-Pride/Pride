# Pride Runtime — production

"The over-engineered C."

This is compiler_rt that every Pride-compiled binary links against.
It is self-contained, has no external dependencies beyond POSIX and libc,
and every subsystem is replaceable independently without touching the frontend.

## Building

```sh
# Step 1: Compile the Pride compiler_rt ($CC for the C runtime only).
# The C standard flag is auto-detected — newest supported wins:
# c23 → c2x → gnu18 → c18 → c17 → c11 (see scripts/detect_c_std.sh;
# override with CC=... or PRIDE_C_STD=-std=xxx).
make runtime
# Or manually:
$CC -O2 "$(bash scripts/detect_c_std.sh)" -pthread -Wall -Wextra \
    -fno-strict-aliasing -fPIC -c runtime/compiler_rt.c -o runtime/compiler_rt.o

# Step 2: Emit LLVM 22 IR from a Pride source file
./pride --emit-llvm output.ll source.pie

# Step 3: Assemble → optimise → compile (pure LLVM 22, no Clang)
llvm-as-22 output.ll -o output.bc
opt-22 -O2 output.bc -o output.opt.bc
llc-22 -filetype=obj -relocation-model=pic output.opt.bc -o output.o

# Step 4: Link with lld-22 (no gcc/Clang in the link step)
ld.lld-22 \
  /usr/lib/x86_64-linux-gnu/crt1.o \
  /usr/lib/x86_64-linux-gnu/crti.o \
  output.o runtime/compiler_rt.o \
  /usr/lib/x86_64-linux-gnu/crtn.o \
  -L/usr/lib/x86_64-linux-gnu -L/lib/x86_64-linux-gnu \
  -lc -lpthread -lm \
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

### §4 — Algebraic effects: snapshot-based delimited continuations

**Not setjmp/longjmp — and not pure swapcontext either.** We use `ucontext_t`
trampolines *plus stack snapshots*: the classic snapshot implementation of
delimited control ("shift/reset for C"), adapted to Pride's inline handle
blocks. Everything runs on **one linear C stack**; the suspended region is
memcpy'd to the heap at each `perform` and restored at `resume`.

Why snapshots? Codegen emits `handle` **inline**: the dispatch block, the
computation block, and every arm block are basic blocks of one LLVM function
sharing one stack. When the computation performs an op, the arm must run at
the handle's dispatch point — its frames would overwrite the suspended
computation's frames below it on the same stack. So `__pride_perform`
copies every byte of the suspended region (from its own SP up to the
high-water mark captured at push, clamped against the live stack VMA read
from `/proc/self/maps`) into a heap buffer before yielding, and
`__pride_resume` memcpies it back through a restore trampoline before
re-entering the computation.

**Semantics — TAIL-RESUMPTIVE, ONE-SHOT (Koka-style):** `resume()` never
returns; the resumed computation runs to completion and the arm does not
continue after it. A computation may perform any number of ops in sequence
(each perform re-snapshots). An arm that finishes *without* resuming unwinds
to the dispatched frame (`__pride_pop_handler`).

```
handle computation { | Op(arg) → resume(v) }
  ↓
__pride_push_handler(frame_id, nops, op_id+1, ...)
  → pushes a frame on the per-thread __thread stack (depth 16)
  → records the op list (for correct multi-handler dispatch)
  → takes a mini frame-repair snapshot of the return path
  → allocates a 256 KB scratch stack for the dispatch/restore trampolines
  → returns the DISPATCH TOKEN: 0 = run the computation

Inside the computation:
__pride_perform(op_id, nargs, args...)
  → finds the NEWEST frame listing op_id (inner handlers that don't
    handle the op are transparently bypassed, like multi-prompt bypass)
  → snapshots [SP, frame_top) to the heap
  → dispatch trampoline (on the scratch stack) repairs the push frame and
    setcontext()s to push's continuation ⇒ push_handler "returns again",
    this time yielding token op_id+1 ⇒ the switch selects the op's arm

Inside the handler arm:
__pride_resume(val)
  → stores val; the restore trampoline writes the big snapshot back over
    the live stack and setcontext()s into the computation, which then sees
    __pride_perform RETURN val  (never returns to the arm)

__pride_complete()   ← computation finished normally: pop the frame
__pride_pop_handler()← arm finished WITHOUT resuming: unwind to the prompt
__pride_get_arm_arg(i) → arm_args[i] of the currently dispatched frame
```

**Dispatch is a stack, not a slot.** An arm body may itself `perform` an
operation — routed to some (typically outer) frame. `__pride_perform`
saves the current dispatch identity in the handler frame struct
(`prev_dispatched`, TLS — never on the machine stack, because perform's
own activation lives inside the snapshotted region and a local copy would
be clobbered by the restore memcpy) and reinstates it when the nested
perform is resumed. Performs therefore strictly nest (LIFO), and an inner
arm's own `resume()` always targets its own frame.

**Deep-handler re-perform rule.** While a handler's arm is in flight, that
handler's prompt is dissolved: the dispatch search skips every frame in the
in-flight arm chain (`effect_dispatched` + its `prev_dispatched` links).
An arm that re-performs one of its own ops escapes to a strictly outer
handler — or, with none, panics as *unhandled effect operation* — instead
of re-entering its own dispatch context (which would free the still-needed
snapshot and loop forever).

**Dispatch-token ABI (with `ssi_ir.c3 lower_handle` / `codegen.c3`):**
the token returned by push_handler drives the LLVM `switch`: default (0) is
the computation edge, a case `op_id+1` is that op's arm edge. The handle
expression's value is the join-block φ over the computation edge and each
arm edge, typed by the *computation's* type (or the arm's type if the arm
never resumes).

**Thread-safety:** the handler stack is `__thread` — one per OS thread.
No locking needed.

#### Upgrading the effects ABI

Replace just the four `__pride_{push_handler,pop_handler,perform,resume}` functions:

| ABI | Speed | Allocation | Notes |
|---|---|---|---|
| **ucontext + snapshots (current)** | Good | 256 KB/frame + live-region snapshot per perform | Correct, portable; one-shot tail resumption |
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
