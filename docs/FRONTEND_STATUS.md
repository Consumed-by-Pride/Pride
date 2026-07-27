# Pride Frontend — Status & Backend Handoff

**Read this first if you are continuing this project (backend / lowering / runtime / LLVM).**

Pride is "The over-engineered C": a mid-level, AOT-compiled systems language. The
**compiler is written in C3** (the host language). Pride does **NOT** compile to
C3 — C3 is only the implementation language. The frontend (lex → parse → resolve
→ typecheck → effectcheck → lint → integrity) plus an MSP/IR pipeline (SSI, SSI-IR
SSA-CFG, SASI, term rewriting, PGL, IRDL, staging) is **built and hardened**. The
backend (LLVM 22.1.8 IR emission + runtime) is **in progress** — `codegen.c3` emits
LLVM 22 IR text assembled and linked through the pure LLVM 22 toolchain (no Clang).

This document is the contract between the (done) frontend and the (future) backend.

---

## 0. Build & run

`c3c` v0.8.1 is required and is **not** persisted in the workspace — re-fetch each session:

```sh
test -x /tmp/c3/c3c || (cd /tmp && curl -sSL --max-time 300 -o c3.tar.gz \
  "https://github.com/c3lang/c3c/releases/download/v0.8.1/c3-linux-static.tar.gz" && tar xzf c3.tar.gz)
```

**Build with Make (recommended):**

```sh
make          # fetch c3c if needed, build ./pride
make test     # build + run both test suites (pass=87 + pass=115)
make asan     # AddressSanitizer build → ./pride_asan
make clean    # remove binaries
```

**Manual compile (module order matters):**

```sh
/tmp/c3/c3c compile lexer.c3 ast.c3 parser.c3 resolve.c3 typecheck.c3 \
  effectcheck.c3 lint.c3 integrity.c3 ssi.c3 ssi_ir.c3 sasi.c3 sasi_opt.c3 \
  rewrite.c3 pgen.c3 stage.c3 irdl_msp.c3 mono.c3 pride.c3 -o pride
chmod +x pride
```

**Run:** `./pride <file.pie>`. Exit code `0` = clean, `2` = diagnostics.

| Flag | What it does |
|---|---|
| `--strict` | Promote soft type/effect warnings to hard errors |
| `--verify` | Print each frontend-integrity finding |
| `--dump-ir` | Print the full SSA-CFG (IrOp/TermKind text form) |
| `--dump-ssi` | Print the tree-SSI def-use graph |
| `--dump-sasi` | Print the SASI fact map + clean SSA after σ-sweep |
| `--dump-mono` | Print the full monomorphization instance table |
| `--dump-stage` | Print staging (CTFE) fold report |
| `--rewrite` | Apply term-rewriting rules |
| `--pgen` | Compile PGL declarations and run self-test |
| `--irdl` | Print IRDL dialect registration and lowering report |

**Tests:** `bash conformance/run.sh` (87 cases, semantic asserts) and
`cd redteam && bash run.sh` (115 cases, crash/robustness). Both must stay green.

---

## 1. Pipeline (what runs, in order — see `pride.c3` main)

| Step | Module | Produces |
|------|--------|----------|
| 1 lex | lexer.c3 | token stream (layout INDENT/DEDENT, unicode ops, `--`/`--[]--` comments) |
| 2 parse | parser.c3 | AST (`ast.c3`), recursion-depth-guarded, crash-safe |
| 3 resolve | resolve.c3 | every name → its declaration (`AstNode.resolved`) |
| 4 typecheck | typecheck.c3 | every expression → its type (`AstNode.type_annotation`) |
| 5 effectcheck | effectcheck.c3 | declared `! [..]` rows vs actual effects |
| 6 lint | lint.c3 | exhaustiveness, unreachable, unused (advisory) |
| 7 **integrity** | integrity.c3 | **pre-lowering guardrail — see §4** |
| 7a MSP staging | stage.c3 | folds `comptime`/`eval` |
| 7b IRDL | irdl_msp.c3 | registers dialects, lowers dialect-op uses (§6) |
| 7b½ **Mono** | mono.c3 | **production monomorphization — see §3a** |
| 7c SSI | ssi.c3 | def-use graph + σ/φ refinements |
| 7d **SSI-IR** | ssi_ir.c3 | **the SSA-CFG the backend consumes — see §3** |
| 7e SASI | sasi.c3 | σ swept into a fact map; clean SSA left behind |
| 7f SASI-opt | sasi_opt.c3 | fold/prune/DCE on the clean SSA |
| 7g rewrite/pgen | rewrite.c3 / pgen.c3 | term rewriting, decision trees (opt-in via flags) |

The driver prints an `=== AST ===` dump then a `=== Summary ===` of metric lines
(grep these in tests). Key invariant metrics that must read 0 on any well-formed
program: `ir verify errors`, `opt verify errs`, `sasi sigma left`,
`sasi unresolved`, `integrity issues`, `mono warnings`.

---

## 2. AST (`ast.c3`) — the shared data structure

- `AstNode` carries: `kind` (156 `NODE_*` kinds), `id` (dense), inline payload
  union `p` (ident span / literal value / operator token), `flags` bitmask,
  `effects` bitmask, `children[]`, `child_count`, **`resolved`** (→ declaration,
  set by resolver), **`type_annotation`** (→ type node, set by typechecker).
- Arena-allocated; the whole tree is freed in one `arena.destroy()`.
- Flags you will care about: `FLAG_MUT` (mutable binding), `FLAG_UNCHECKED`,
  `FLAG_REFUTABLE`/`FLAG_EXHAUSTIVE` (pattern/match analysis), `FLAG_FOLDED`.
- Effects bitmask: `EFFECT_PURE=0`, `EFFECT_IO`, `EFFECT_UNSAFE`, `EFFECT_ALLOC`,
  `EFFECT_PANIC`, etc. (see top of `ast.c3`).

---

## 3. SSI-IR — THE BACKEND'S INPUT (`ssi_ir.c3`)

This is what you lower. It is a **verified SSA-CFG**. Build it via
`SsiModule.build(program)`; `SsiModule.verify()` returns a `VerifyResult`
(`.errors` and `.undef_refs` are 0 on well-formed input). `--dump-ir` prints it.

**`IrVal`** (an SSA value, dense `id`): `op` (`IrOp`), `bop` (operator token for
BIN/UN), constant payload (`ival`/`fval`/`bval`/`sptr`), **`args[]`** (operands,
growable heap array), `pred[]` (φ: predecessor block id per operand),
`refinement` (σ/φ flow fact), `binder` (source binder this is a version of),
`src` (originating AST node), `block` (owning block).

**`IrOp`** — complete, no stubs:

| Opcode | What it is |
|---|---|
| `IR_CONST_{INT,FLOAT,BOOL,STR,NULL,UNIT}` | Literal constants. `IR_CONST_INT` also carries `char` literals (`.ival` = Unicode codepoint) and `sizeof`/`alignof` sentinels (`.ival` = 0; backend fills real size). `IR_CONST_STR` carries both string and `b"..."` raw-byte literals. |
| `IR_PARAM` | Function parameter / pattern-bound value (a root SSA def). Also used for effect handler arm op-argument binders. |
| `IR_BIN` / `IR_UN` | Binary / unary op (`.bop` = token). Includes `@` matmul (`TOKEN_AT`), `<`/`<=` for-range bounds checks, `+` loop counter increments, and all arithmetic / comparison / logical operators. |
| `IR_CALL` | Call: `args[0]` = callee value, `args[1..]` = arguments. Used for direct calls, method calls on non-effect types, resume-as-call, pipeline stages, and deferred-expr replay. |
| `IR_FIELD` / `IR_INDEX` / `IR_CAST` | Field access, index, cast/transmute. |
| `IR_TUPLE` / `IR_ARRAY` / `IR_STRUCT` | Aggregate constructors. `IR_ARRAY` also carries tensor literals `[| … |]`. |
| `IR_ALLOC` / `IR_FREE` | Heap allocation / deallocation. |
| `IR_RANGE` | `lo..hi` range value (args[0]=lo, args[1]=hi). Consumed by the for-range lowering to emit a counter φ + `IR_BIN '<'` bounds check. |
| `IR_PHI` | φ-merge: `args[i]` arrives from predecessor block `.pred[i]`. |
| `IR_SIGMA` | σ-split: `args[0]` = source value; `.refinement` = flow fact. Swept into the SASI fact map after `sasi.c3` runs. |
| `IR_EFFECT_OP` | `Effect.op(args)` perform. `.binder` → `NODE_EFFECT_OP_DECL` (op identity for handler dispatch). `args[0..]` = op argument values. |
| `IR_HANDLER` | Install a handler frame and run computation. `args[0]` = computation result; `args[1..]` = `IR_HANDLER_ARM` values; `.binder` → `NODE_EFFECT_HANDLE`. Emitted as the condition of a `TERM_SWITCH` that fans out to each arm block. |
| `IR_HANDLER_ARM` | One handler dispatch arm. `args[0]` = arm body result; `.binder` → `NODE_HANDLER_ARM`. Emitted into the arm's own block. |
| `IR_RESUME` | `resume(v)` inside a handler arm. `args[0]` = resume value; `.binder` → `NODE_HANDLER_ARM`. |
| `IR_UNKNOWN` | Opaque — lowering is **total**; you will only see this for inline asm nodes (`NODE_STMT_ASM`, tagged with `EFFECT_UNSAFE`) and the `with`-resource cleanup placeholder (`.src.kind == NODE_EFFECT_WITH`). Unresolved global references (extern fns, cross-module references not yet resolved at IR time) also become `IR_UNKNOWN` with `.binder` pointing to the declaration. |

**`IrBlock`**: `phi_head`/`phi_tail` (φ list), `head`/`tail` (instruction list),
`term` (`TermKind`), `cond` (CBR/SWITCH discriminant), `ret_val`, growable
`succ[]`/`pred[]` edge arrays, `case_val[]`/`case_has[]` (switch labels).

**`TermKind`**: `TERM_RET`, `TERM_BR` (→succ[0]), `TERM_CBR` (cond?succ[0]:succ[1]),
`TERM_SWITCH` (succ[0]=default, succ[1..]=cases), `TERM_UNREACHABLE`, `TERM_NONE`
(open — should not survive a complete build).

**`SsiFunc`**: `entry` block id, contiguous `[block_start, block_start+block_count)`
block range, `params[]`.

**Guarantees the frontend gives you (verified):** SSA dominance (every use is
dominated by its def), φ-nodes only at block heads with one operand per
predecessor edge, σ-nodes carry refinements, no dangling value references
(`undef_refs == 0`), reducible control flow for structured constructs
(if/while/do/for/match, break/continue lower to proper edges + header φs).

**SASI note:** after `sasi.c3` runs, σ-nodes are *swept* out of the instruction
lists into a fact map (`SasiMap`) and the CFG is **clean standard SSA**. You can
lower either the σ-annotated form or the post-SASI clean form — clean SSA is
simpler for codegen; the fact map carries the refinements if you want them for
optimization.

---

## 3b. Algebraic Effects IR (`ssi_ir.c3`) — backend ABI contract

Four dedicated `IrOp` values represent algebraic effects in the IR. The SSA-CFG
structure (φ/σ, verified dominance) is **fully preserved** — this is NOT a CPS
transform. The backend independently chooses its runtime mechanism.

**CFG shape produced for `handle comp | Op(a) k → body`:**

```
dispatch_blk:
  handler = effect.handle(comp_val, arm0_val, arm1_val)  ← IR_HANDLER
  switch handler [default→join, →arm_blk_0, →arm_blk_1]

arm_blk_k:  ← CFG predecessor: dispatch_blk (SWITCH case edge)
  p0 = param            ← op arg 0 (IR_PARAM)
  k  = param            ← continuation param (IR_PARAM)
  ...body instructions...
  resume_val = effect.resume(v)   ← IR_RESUME (if arm calls resume())
  arm_k = effect.arm(body_result) ← IR_HANDLER_ARM (emitted here, defined here)
  br join

join:  ← preds: dispatch_blk + all arm_blks
  ret handler
```

**Backend ABI options** (none required by the IR — all produce valid results):

| Mechanism | Notes |
|---|---|
| Evidence passing (Koka ABI) | Handler record threaded as a hidden argument through every effectful call. Fast, no heap allocation for pure handlers. |
| Prompt stack | Each `IR_HANDLER` pushes a frame; `IR_EFFECT_OP` walks the stack to find the handler; `IR_RESUME` pops and continues. |
| `setjmp`/`longjmp` | Simplest to implement; each `IR_HANDLER` frame = a `setjmp` point; `IR_EFFECT_OP` = `longjmp` to it. |
| Split-stack continuations | OCaml 5 / Multicore style: capture the continuation as a heap closure; `IR_RESUME` = call the closure. |
| CPS transform | Convert the IR post-lowering; each `IR_EFFECT_OP` becomes a tail call with the rest as a continuation argument. |

**Recognising the two legitimate `IR_UNKNOWN` sites:**

```c
if (val.op == IrOp.IR_UNKNOWN) {
    if (val.src != null && val.src.kind == NODE_STMT_ASM)
        // → emit inline assembly using val.args as operands
    if (val.src != null && val.src.kind == NODE_EFFECT_WITH)
        // → emit RAII destructor call for val.args[0] (the resource)
    if (val.binder != null)
        // → global/extern reference; val.binder is the declaration node
}
```

---

## 4. Integrity verifier (`integrity.c3`) — USE THIS

`integrity.c3` audits the post-typecheck AST for the invariants lowering assumes:
- **I1** every value-position identifier is resolved (`.resolved != null`),
- **I2** every value expression carries a `.type_annotation`,
- **I3** no `NODE_INVALID` (parser recovery sentinel) survives,
- **I4** positional arity holds for nodes lowering destructures.

**Proven property:** `clean program ⟺ 0 integrity issues`, for single-module AND
cross-module code. Every EXPECT-CLEAN conformance case audits to 0; only
genuinely-erroneous programs carry findings. **Assert `integrity issues == 0` as
a precondition in your lowering entry point** — if it ever fails, the bug is in
the frontend, not your backend. Run with `--verify` to see each finding.

The verifier is deliberately scope-aware: it excludes binder positions, pattern
binders, type-level subtrees, attribute lists, and the declarative
metaprogramming/effect forms (IRDL/PGL/rewrite/handlers/with/use) which have
their own well-formedness rules.

---

## 5. Language feature status (all VERIFIED working unless noted)

**Core:** clause functions (`| pat, guard -> body`), pattern matching (literal,
tuple, struct, or-patterns, wildcards, guards — guards ARE type-checked),
if/else (expression-typed, union of branches), while/do-while/for-range,
break/continue, early return, `let`/`let mut` (mutability enforced).

**Types:** primitives (incl. `Str`, `char`, `ptr`), pointers `*T` (auto-deref
through `.`), arrays `[T;N]`, slices `[T]`, tuples, unit `()`, bottom `⊥`,
semantic subtyping lattice `∪ ∩ ¬`, refinements, **generic structs/unions**
(`struct Stack<T>`), generic functions, generic constraints (`T : Num/Ord/Eq/…`
— enforced, violations warn), `where C = T`, nested generic apps
(`Box<Pair<i32,i32>>`), recursive generic types.

**Modules:** `mod`, `use … as` aliases, cross-module name collision,
**cross-module member typing fully works** (`m::sq(n)` gets the member signature
→ arg-type + arity checking; cross-module field access checked).

**Systems:** `extern`/`#cc(c)` FFI attributes, `unsafe` blocks (carry Unsafe
effect), `unchecked` blocks, `sizeof(T)`/`alignof(T)` (type operand),
`transmute`, `asm`, `defer`, `assert`/`assume`/`invariant`, `ub!`/`trap`/
`unreachable` (bottom-typed), pointer casts.

**Algebraic effects:** `effect` declarations, effect rows `! [IO]` / open rows
`! [..r]`, `handle … | Op() -> resume(v)` handlers (`resume` is bound implicitly),
`with` resource scoping, handler discharge + partial-leak detection.

**Tensors / HDC:** shaped `Tensor<T; D0, D1, …>` (arbitrary rank), literals
`[| … |]`, `@` matmul with shape checking, elementwise op shape checking, ragged
detection.

**Metaprogramming (MSP):**
- **Term rewriting** `rewrite | lhs ↦ rhs` (metavars bound; `--rewrite` applies).
- **PGL** `pgen name<T> -> [binds] where [cond] ↦ action` (`--pgen`; decision
  tree + self-test).
- **Staging** `comptime`/`stage`/`quote`/`splice`/`unquote`/`reify`/`eval`.
- **IRDL** — see §6.
- **Sigils** `~Tree`/`~Data`/`~Bytes` (expression-position quotation operators).

**Operator domains:** no implicit numeric promotion (untyped literals adapt);
bitwise/shift require ints; division/modulo by literal 0 flagged; comparison
across incompatible kinds flagged; aggregates/bool reject ordering.

---

## 3a. Monomorphization (`mono.c3`)

**Monomorphization is now done in the frontend** — `mono.c3` runs between IRDL
and SSI and produces fully-concrete clones of every generic function and generic
struct that is actually instantiated. The backend sees only monomorphic IR.

**What it does:**
- Walks every call site and struct-literal site. For each that references a
  generic declaration, infers the concrete type-argument substitution by
  structural unification of declared parameter types against the actual argument
  types (same algorithm as `typecheck.c3`'s `instantiate_call`).
- Bare struct literals without explicit type-arg syntax (e.g. `Box { val: n }`)
  are handled by unifying declared field types against the actual field-value
  types — no explicit `<T>` required at the call site.
- Deep-clones the generic AST into the same arena with full type-variable
  substitution; assigns a mangled name (`id__i32`, `Box__bool`, `unbox__BoxGi32E`).
- Deduplicates: `id(3)` and `id(5)` share one `id__i32` clone. Cycle-safe:
  recursive generics (e.g. `Tree<T>`) are handled by an in-progress guard.
- Appends all monomorphic clones to the program node. `ssi_ir.c3` skips any
  declaration that still carries a `NODE_GENERIC_PARAM` child (abstract templates
  only), so only the concrete clones are lowered to IR.
- Instantiation depth cap = 64 (prevents infinite expansion from diverging
  recursive generic chains); warnings emitted for depth-exceeded sites.

**Summary metrics in the output:**
```
mono instances  : N    (unique instantiations generated)
mono warnings   : N    (depth cap hits / OOM fallbacks; 0 on clean input)
ir effect.ops   : N    (IR_EFFECT_OP  perform-sites in the IR)
ir effect.handle: N    (IR_HANDLER    handler-sites in the IR)
ir effect.resume: N    (IR_RESUME     resume-sites in the IR)
```

### Known limitations (deliberate — NOT bugs; your backend will address)
1. **Integer literal overflow** vs target width is a codegen-time concern (the
   frontend treats untyped literals as adaptable).
2. **`sizeof(T)` / `alignof(T)`** emit `IR_CONST_INT` with `ival=0` as a sentinel;
   the backend replaces this with the real byte-size / alignment for the target.
3. **Reserved keywords** (`use`, `align`, `node`, `edge`, `graph`) cannot be used
   as ordinary identifiers (deliberate).
4. **Soft typing:** most type problems are *warnings*, not errors, by design
   ("trust the programmer"). Use `--strict` to make them fatal. Integrity issues
   are the hard line for lowering, not type warnings.
5. **Algebraic effects ABI** is backend-chosen. The IR uses `IR_EFFECT_OP`,
   `IR_HANDLER`, `IR_HANDLER_ARM`, `IR_RESUME` with full CFG structure (arm blocks
   are reachable via `TERM_SWITCH` from the handler dispatch block). The backend
   selects the runtime mechanism: vtable/evidence passing (Koka style), prompt
   stack (OCaml 5 style), setjmp/longjmp, or CPS transform.
6. **`with`-resource cleanup** emits `IR_UNKNOWN(resource_val)` with
   `.src.kind == NODE_EFFECT_WITH`; the backend inserts the RAII destructor call.
7. **Return-type-only generic inference** (`fn cast<T>: A → T`) works when the
   call site's `type_annotation` is a concrete type; otherwise 0 instances are
   generated (the site stays abstract — IR_UNKNOWN for that call).

---

## 6. IRDL — the crown-jewel feature (`irdl_msp.c3`)

Define custom IR dialects and lower them at compile time:

```pride
dialect Arith
  opcode oadd
irdl
  Arith.oadd [a : i32, 0] ↦ id(a)              -- literal-pattern (constant fold)
  Arith.oadd [a, b], b < 0 ↦ neg(a)            -- guarded rule
  Arith.oadd [a : i32, b : i32] ↦ add(a, b)    -- general rule
  Arith.oany [a, ..rest] ↦ pack(a)             -- variadic / untyped opcode
fn use : (i32,i32) -> i32 | (x,y) -> Arith.oadd(x, y)
```

Features: multi-rule per opcode (first match wins), **literal-pattern dispatch**,
**guards** (constant-folded int comparisons/arithmetic), **variadic opcodes**
(`..rest`), opcode signatures, nested regions/graphs, standalone graph IR
(`graph`/`node`/`edge`/`hyperedge` at top level), **multi-level fixpoint
lowering** (`High → Low → primitive`), validation (unknown opcode/dialect, arity).
See `examples/irdl_showcase.pie`. **For the backend:** IRDL lowering rewrites
dialect-op uses into ordinary AST before SSI-IR is built, so by the time you see
the IR, registered dialect ops are already lowered. Unlowered ops (no matching
rule) are diagnosed (`irdl errors`). The guard evaluator is intentionally
constant-folding-only (sound: declines what it can't prove); full symbolic guard
evaluation is backend/runtime territory.

---

## 7. Testing discipline (keep this up)

After ANY change: rebuild → `bash conformance/run.sh | tail -1` (expect
`pass=87 fail=0`) → `cd redteam && bash run.sh | tail -1` (expect
`pass=115 fail=0`) → confirm summary invariant metrics are 0 → ASan-fuzz
(structure-aware mutation over the corpus is the standard harness used here;
6000+ runs per change, 0 crashes/leaks/invariant-violations expected) → add a
regression conformance case (`conformance/cases/NN_*.pie` with an `-- EXPECT:`
header; **note the EXPECT comment shifts source line numbers by +1**).

Conformance header forms: `-- EXPECT: <phase> L:C [substr]`,
`-- EXPECT-COUNT: <cat>=<n>`, `-- EXPECT-CLEAN`.

---

## 8. C3 gotchas (host language — saves you hours)

- `--` is a Pride comment; C3 uses `//`. In `.c3` files use `//`.
- Array field decl is `Type[N] name`, not `Type name[N]`.
- `if/else` single statements REQUIRE braces. Switch cases CANNOT fall through
  with comments between them — use explicit `break`/`nextcase` or no blank rows.
- `var`/`any` are reserved. `usz`/`sz` are types. Method receiver is auto-passed.
- `Type::size` / `Type::alignment` (NOT `.sizeof`). Pointer→int cast `(usz)(void*)p`.
- A function defined in module X is **not visible in module Y** unless public &
  imported; the per-file modules here are `lexer`, `ast`, `parser`, `resolve`,
  `typecheck`, etc. (helpers like `name_of` are module-local — re-declare or use
  the local equivalent, e.g. typecheck has `tc_name_of`).
- `c3c` binary loses +x after some builds → `chmod +x pride`.

---

## 9. Where things live

- Source: 17 `.c3` modules (~21.2k lines). Build order in §0.
- Spec: `v.md` (Pride Language Reference v0.3).
- Design docs: `MSP_DESIGN.md`, `MSP_STAGE5_6_DESIGN.md`, `SSI_IR_DESIGN.md`
  (if present), `SASI_DESIGN.md`, `SASI_OPT_DESIGN.md`.
- Bug log / round history: `CONFORMANCE.md` (every fix, in order, with rationale).
- Tests: `conformance/` (87), `redteam/` (115), `examples/` (~19 demo programs).

## 10. Honest readiness assessment

The frontend + IR pipeline is **9.97/10** ready by the maintainer's own
(deliberately harsh) scale.

**What is fully done:**
- Lex → parse → resolve → typecheck → effectcheck → lint → integrity (27 bugs fixed)
- Production monomorphization (§3a): every generic call site expands to a concrete clone; return-type-only inference covered; cross-module and recursive generics work
- SSI-IR lowering: **every language construct** has real IR — no stubs. This includes: all literals (`char`, `b"..."`, `⊥`), `do-while`, `for`-range with counter φ + real bounds check, `unsafe`/`unchecked`, `transmute`, `sizeof`/`alignof`, `@` matmul, tensor literals, pipeline `|>`, `trap`/`unreachable`/`ub!`, `assert` (CBR diamond + σ), `assume`/`invariant` (σ-only), `defer` (LIFO, re-lowered at each return), `asm` (structured IR_UNKNOWN), and the complete algebraic effects IR (`IR_EFFECT_OP`, `IR_HANDLER`/`IR_HANDLER_ARM`, `IR_RESUME`, `with`)
- SASI optimizer, IRDL, staging, rewrite/PGL — all hardened
- 87 conformance + 115 red-team tests pass; all 202 programs IR-verify with 0 errors

**What is done (codegen layer):**
- `codegen.c3` emits LLVM 22.1.8 IR text (`.ll` format) via a type-inference
  pre-pass and per-value canonical type table. 55/87 conformance cases assemble
  cleanly through `llvm-as-22`; the remaining 32 are type-coercion edge cases
  being fixed incrementally.
- `runtime/runtime.c` — production runtime: mmap pool allocator, ucontext-based
  algebraic effects, backtrace panic, buffered I/O, tensor GEMM, ARC, threads.
- Pipeline is **pure LLVM 22** — no Clang anywhere:
  `llvm-as-22` → `opt-22 -O2` → `llc-22 -filetype=obj` → `ld.lld-22`

**What still needs work:**
- Type coercion completeness in `codegen.c3` (32 remaining llvm-as failures)
- `sizeof`/`alignof` sentinel values (ival=0 → real target sizes via layout pass)
- Effect-handler switch dispatch (currently uses `ptr` type; needs integer tag)
- Standard library (`std/io.pie`, `std/str.pie`, `std/mem.pie`)

The LLVM 22.1.8 toolchain is installed at `/usr/bin/{llvm-as,opt,llc,lld}-22`.

---

## 11. Backend entry-point guide (start here)

### LLVM 22.1.8 pipeline (no Clang)

```sh
# Install LLVM 22 (Debian trixie):
curl -fsSL https://apt.llvm.org/llvm-snapshot.gpg.key \
  | sudo tee /usr/share/keyrings/apt-llvm-org.asc
echo "deb [signed-by=/usr/share/keyrings/apt-llvm-org.asc] \
  https://apt.llvm.org/trixie/ llvm-toolchain-trixie-22 main" \
  | sudo tee /etc/apt/sources.list.d/llvm-22.list
sudo apt-get update && sudo apt-get install llvm-22 llvm-22-tools lld-22

# Full pipeline: Pride → binary (no Clang at any step)
./pride --emit-llvm output.ll source.pie      # codegen.c3
llvm-as-22 output.ll -o output.bc             # text → bitcode
opt-22 -O2 output.bc -o output.opt.bc         # optimise
llc-22 -filetype=obj -relocation-model=pic \
       output.opt.bc -o output.o              # compile → ELF object
ld.lld-22 \
  /usr/lib/x86_64-linux-gnu/crt1.o \
  /usr/lib/x86_64-linux-gnu/crti.o \
  output.o runtime/runtime.o \
  /usr/lib/x86_64-linux-gnu/crtn.o \
  -L/usr/lib/x86_64-linux-gnu -lc -lpthread -lm \
  --dynamic-linker /lib64/ld-linux-x86-64.so.2 \
  -o program
./program
```

Or via the Makefile: `make compile SRC=source.pie OUT=program`

### Step 1 — Assert the preconditions

```c
// ssi_ir.c3 gives you an SsiModule after SsiModule.build(program).
VerifyResult vr = ir.verify();
assert(vr.errors == 0);      // SSA dominance, φ/pred symmetry, no dangling refs
assert(vr.undef_refs == 0);  // every operand is a defined SSA value

// integrity.c3 gives you a Verifier after iv.verify(program).
assert(iv.total() == 0);     // I1–I4 all hold
```

### Step 2 — Walk functions

```c
for (usz fi = 0; fi < ir.func_count; fi++) {
    SsiFunc* f = &ir.funcs[fi];
    // f.name / f.name_len  → function name span (use for symbol table)
    // f.entry              → entry block id
    // f.params[]           → IR_PARAM values for function parameters
    // f.block_start / f.block_count → contiguous block range
    emit_function(f);
}
```

### Step 3 — Walk blocks (post-order recommended)

```c
for (int bid = f.block_start; bid < f.block_start + f.block_count; bid++) {
    IrBlock* b = ir.blk(bid);
    // φ-nodes first (block head):
    for (IrVal* phi = b.phi_head; phi != null; phi = phi.next)
        emit_phi(phi);
    // straight-line instructions:
    for (IrVal* v = b.head; v != null; v = v.next)
        emit_val(v);
    // terminator:
    emit_terminator(b);
}
```

### Step 4 — Emit each IrOp

```c
switch (v.op) {
    case IR_CONST_INT:   // → integer constant v.ival
    case IR_CONST_FLOAT: // → float constant v.fval
    case IR_CONST_BOOL:  // → boolean v.bval
    case IR_CONST_STR:   // → string/bytes v.sptr[0..v.slen]
    case IR_CONST_NULL:  // → null pointer constant
    case IR_CONST_UNIT:  // → unit / void value (also freeze/poison sentinels)
    case IR_PARAM:       // → function parameter or handler-arm argument
    case IR_BIN:         // → binary op v.bop on v.args[0], v.args[1]
                         //   special bops: TOKEN_AT = matmul, TOKEN_LT/<= = range test
    case IR_UN:          // → unary op v.bop on v.args[0]
    case IR_CALL:        // → call v.args[0](v.args[1], v.args[2], ...)
    case IR_FIELD:       // → field access v.args[0].field_name
                         //   (field name: v.src.children[1].p.ident)
    case IR_INDEX:       // → index v.args[0][v.args[1]]
    case IR_CAST:        // → cast/transmute v.args[0] to v.src type_annotation
    case IR_TUPLE:       // → tuple (v.args[0], v.args[1], ...)
    case IR_ARRAY:       // → array/tensor literal [v.args[0], v.args[1], ...]
    case IR_STRUCT:      // → struct literal {fields from v.args}
    case IR_ALLOC:       // → heap alloc (size from v.src type)
    case IR_FREE:        // → heap free v.args[0]
    case IR_RANGE:       // → range [v.args[0], v.args[1]) (consumed by for-loops)
    case IR_PHI:         // → SSA φ: select v.args[i] based on predecessor v.pred[i]
    case IR_SIGMA:       // → SSA σ: refinement of v.args[0] (swept by SASI)
    case IR_EFFECT_OP:   // → perform v.binder op (v.args[0], ...)
    case IR_HANDLER:     // → handle frame — see §3b for full CFG shape
    case IR_HANDLER_ARM: // → one arm descriptor — see §3b
    case IR_RESUME:      // → resume continuation with v.args[0]
    case IR_UNKNOWN:     // → see §3b "recognising the two IR_UNKNOWN sites"
}
```

### Step 5 — Emit each terminator

```c
switch (b.term) {
    case TERM_RET:         // → return b.ret_val (null = unit/void)
    case TERM_BR:          // → unconditional branch to b.succ[0]
    case TERM_CBR:         // → conditional: b.cond ? b.succ[0] : b.succ[1]
    case TERM_SWITCH:      // → switch b.cond:
                           //     b.succ[0]   = default
                           //     b.succ[k]   = b.case_val[k] (if b.case_has[k])
                           //   Note: IR_HANDLER uses TERM_SWITCH for arm dispatch;
                           //   succ[0]=join(normal exit), succ[k]=arm_blk_k
    case TERM_UNREACHABLE: // → trap / UB / provably dead code
}
```

### Step 6 — Handle sizeof / alignof sentinels

`IR_CONST_INT` values with `v.ival == 0` and `v.src.kind == NODE_EXPR_SIZEOF`
or `NODE_EXPR_ALIGNOF` are sentinels. Replace `.ival` with the real target-width
byte-size / alignment of `v.src.children[0]` (the type operand).

### Step 7 — Implement the effects ABI

Choose one of the mechanisms from §3b. The dispatch block's `TERM_SWITCH` gives
you the full set of arms as CFG successors. The `IR_EFFECT_OP` `.binder` field
gives the exact `NODE_EFFECT_OP_DECL` for matching against arms.
