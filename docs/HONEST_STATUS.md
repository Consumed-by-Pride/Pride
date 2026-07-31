# Pride — Honest Capability Assessment

**As of 2026-07-31. Compiler: 47,135 LoC C3 across 23 modules.**  
**Verified against: c3c v0.8.2, LLVM 19.1.7, Debian trixie x86-64.**

---

## What Pride Actually Is Right Now

Pride is a **working AOT-compiled systems language** with a functioning
frontend pipeline, a complete LLVM backend, and a real algebraic effect
runtime.  It is pre-alpha.  Many things are implemented but not integrated;
many things that look implemented are actually stubs.

The test numbers are honest:
- **261/262 conformance cases pass** (1 failure: case 258 uses unimplemented
  `op name`/`perform`/`resume` surface syntax)
- **44/47 exec tests pass** (3 failures: 44/45/46 use unimplemented `mod`/`use`
  import syntax — pre-existing, require multi-file compiler support)

---

## ✅ What Pride Can Do (Exec-Verified)

### Core language
- Integer, float, bool, string, pointer arithmetic
- Structs, enums with payloads, tuples, arrays (fixed and heap)
- `let` / `let mut` bindings, pattern matching, guards
- `if`/`else`, `while`, `for`-range, `break`/`continue` with labels
- Functions, closures (multi-arm with environment capture)
- Generics (monomorphized at compile time)
- Newtypes, type aliases
- C-union layout structs
- `unsafe` / `unchecked` blocks
- Inline assembly via `syscall(...)` (Linux ABI)

### Type system
- Hindley-Milner-style inference with explicit annotations
- Effect rows `! [E1, E2, ..r]` — effect-polymorphic functions work
- Subtyping for effect rows
- Struct/enum/newtype/array types all resolved correctly
- Integer promotion and signedness-aware implicit coercions

### Algebraic effects
- `effect E { op : T -> U }` declarations
- `handle comp | E.op args k -> body` — resumable handlers
- Effect-polymorphic functions with open rows `[..r]`
- Effect forwarding through generics
- Multiple operations per handler

### Codegen / pipeline
- LLVM 19 IR emission (clean, `llvm-as` verified)
- `comptime <expr>` — stage-0 constant folding
- Mutable module globals (`let mut` with `@pride.gmut.k` LLVM globals)
- All LLVM arithmetic/comparison/bitwise/shift operations
- Saturating arithmetic (`sat_add`, `sat_sub`, `sat_mul`)
- Wrapping arithmetic (`wrap_add`, etc.)
- Float-to-int and int-to-float casts
- `alloc`/`free` (backed by `__pride_alloc`)
- Pointer arithmetic (scales by element size)
- Struct field read/write through pointers
- Array element read/write
- **`&arr[0] as *T` — address-of array element (ptr-to-ptr dedup fixed)**
- Slice types `[T]` as `{ ptr, i64 }` fat pointers
- Tensor/matrix operations (`@` matmul operator)
- SIMD operations on fixed-size vectors

### HOSE runtime (callable via `stdlib/pride/effects.pie`)
- Prompt install/unwind/is_in_scope
- Dynamic winding (push/enter/exit/pop)
- Local environment binding (reader monad via key_id)
- Fiber spawn/resume/yield (ucontext, real stack switching)

### Optimizer passes (`sasi_opt.c3`)
- Constant arithmetic folding
- Algebraic identity folding (x*1→x, x^0→x, x&0→0, etc.)
- Redundant comparison elimination (SASI-driven)
- Branch folding on constant conditions
- Unreachable block pruning
- Dead instruction elimination (pure + no users)

### Lints
- Undefined name / scope errors
- Duplicate pattern bindings
- Arity mismatches
- Type mismatches
- Effect handler arm assigns outer local (catches a common mistake)
- Unreachable match arm after catch-all
- Unused binding
- **Self-assignment `x = x`** (new)
- **Constant condition `if true`/`if false`** (new, skips `while true`)

---

## 🔶 What Exists But Has Edge Cases

### Handler arm mutation
Handler arms cannot write to variables declared in the enclosing scope.  The
snapshot runtime drops such writes silently.  This is a semantic limitation,
not a bug — the correct pattern is to accumulate state through resume values.

### O2 optimization interaction
With `opt -O2`, functions that call pointer-mutating helpers (e.g. `hm_insert`
modifying a struct through a `*HMap` pointer) inside while loops may
miscompile.  Root cause: LLVM's interprocedural alias analysis can infer
incorrect aliasing properties for deeply inlined call chains.  `opt -O1` is
safe and recommended for code with this pattern.

### Struct literals with multi-line indented fields
```pie
-- FAILS:
let s = Foo {
    field1: val1,
    field2: val2,
}

-- WORKS:
let s = Foo { field1: val1, field2: val2 }
```

### Tuple values from function calls as effect resume args
`k (fn_returning_tuple())` where `fn_returning_tuple` returns `(bool, i64)`
produces invalid IR.  Literal tuples `k (true, 42)` work.  Workaround: use
a `let` binding then pass: but that has the ptr-alloca issue.  Encode tuples
as single `i64` values (e.g. negative = empty, non-negative = value).

### Inline multi-arm `match`
```pie
-- FAILS (| is parsed as bitwise OR):
let r = match x | A(v) -> v | B -> 0

-- WORKS:
let r = match x
  | A(v) -> v
  | B    -> 0
```

---

## ❌ What Pride Cannot Do Yet

### Module system
- `use module.submodule` does not load and compile the referenced file.
  The directive is parsed and partially resolved (for intra-file module
  qualified names) but no cross-file linking happens.
- `mod foo.bar.baz` multi-segment module names are parsed only as single-segment.
  Only `mod name` (one identifier) works.

### Full MSP surface language
- `quote` / `splice` / `unquote` keywords are parsed but not codegen-lowered.
- `box[Γ] expr at Stage L` syntax is in `parse_modal.c3` but not wired into
  the main parser.
- Stage-polymorphic functions (`∀L. T[L]`) are not implemented.
- Cross-stage escape checking (`msp_verify_no_escape`) is built but not called.

### Async / structured concurrency
- The `effect_async/` stdlib exists but requires an event loop integration
  that is not built.
- `fiber_spawn`/`fiber_resume`/`fiber_yield` work in isolation (the ucontext
  implementation is real) but no exec test drives them through the full stack.

### Trait objects / dynamic dispatch at language level
- `dyn Interface` is not a language construct — only a library pattern
  (`stdlib/dyn.pie` provides `DynPtr { data, vtable }` manually).
- No implicit vtable generation.

### Error handling at language level
- No `?` propagation operator.
- No `try`/`catch` at the language level (effects can model this, but there's
  no sugar).

### Async/await surface syntax
- No `async fn`, `await`, `.then()`.
- The HOSE fiber engine can implement cooperative multitasking manually but
  there's no language-level abstraction.

### Operator overloading
- Interfaces for `Add`/`Sub`/`Mul` etc. exist in `stdlib/dyn.pie` but the
  compiler does not map `a + b` to an `Add.add(a, b)` call for user types.

### Integer/float formatting
- No `format!()` macro in the compiler sense.  String interpolation exists
  (`format!` → `IR_FORMAT`) but its output path is not fully wired.
- `print_i64_nl` must be written by hand in each exec test (see any exec test
  for the boilerplate).

### DWARF debug info
- `--debug` / `-g` flag exists in the CLI but debug info emission is not
  implemented.

### Windows / macOS targets
- Pride emits Linux x86-64 ELF.  No PE/COFF or Mach-O support.  No Windows
  ABI (MSVC or MinGW).  macOS is theoretically possible (same LLVM backend)
  but untested.

### Cross-compilation
- No target triple in the emit path.  Always targets the host.

### Incremental compilation
- Every `pride` invocation is a full compile of the single input file.

### Package manager / build system integration
- `Makefile` and `build.sh` exist for the compiler itself.  No package
  registry, no `pride.toml` dependency resolution.

### Garbage collection / reference counting
- All memory is manual (`alloc`/`free`).  The runtime has ARC infrastructure
  (`__pride_rc_retain`/`__pride_rc_release`) but the compiler does not emit
  retain/release calls.  ARC is opt-in (not implemented yet).

### Concurrency primitives at language level
- Threads, mutexes, channels are in `stdlib/sync/` as library code that
  wraps pthreads.  No language-level `spawn`, no `Send`/`Sync` type classes.

---

## Known Codegen Bugs (Remaining)

| Bug | Trigger | Workaround |
|---|---|---|
| O2 LICM with inlined struct-mutating fns | `opt -O2` inlines `fn(ptr_to_struct)` into caller loop | Use `opt -O1` for affected code |
| Tuple resume from function call | `k (fn_returning_tuple())` | Use `i64` encoding or literal tuples |
| Stack-array indexed via `*[T;N]` parameter | `fn f(a: *[i64;8], i: i64)` then `a[i]` | Use raw `(a as i64 + i*8) as *i64` arithmetic |

### Fixed This Session

| Bug | Root cause | Fix |
|---|---|---|
| `&arr[0] as *T` double-indirection | `IR_UN '&'` handler always emitted `alloca ptr; store ptr v; gep ptr alloca 0` even when operand was already a `ptr`, producing a `ptr*` instead of `ptr` | Skip the alloca+store when operand type is `"ptr"`: emit identity `gep i8, ptr arg, 0` instead |
| Test 40 (sort/search/reverse): wrong array pointer passed to fn, wrong array reads | Same double-indirection bug: `sort_array(&arr[0] as *i64, 5)` passed the alloca address instead of arr[0] address | Same fix above |

---

## Build Numbers (2026-07-31)

| Metric | Value |
|---|---|
| Compiler source | 47,135 LoC C3 (23 modules) |
| Runtime C source | 3,081 LoC (compiler_rt.c + compiler_rt_arch.c) |
| Stdlib | 257 `.pie` files |
| Conformance tests | **261/262 pass** |
| Execution tests | **44/47 pass** (up from 43, fixed test 40) |
| Example files | 5 (all PASS at `opt -O1`) |
| LLVM target | LLVM 19.1.7, x86-64 Linux ELF |
| Host compiler | c3c v0.8.2 |
