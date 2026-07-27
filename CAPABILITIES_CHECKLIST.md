# Pride Capability Checklist

Updated: 2026-07-27
**Compiler**: ~37,000 LoC C3 (root `*.c3`)
**Runtime**: `compiler_rt.c` 1,900 LoC + `compiler_rt_arch.c` ~190 LoC
**Exec tests**: 18/18 PASS · Conformance: 242/242 PASS (both pending a fresh
build/run — the c3c/LLVM toolchain was unavailable in the review sandbox;
all fixes below were instead verified either via an independently-assembled
LLVM 22 toolchain compiling and running real code, or via careful static
cross-referencing — see `finds.md` §7 and `.review_notes/` for the full
methodology and per-finding verification detail)

> ⚠️ **Repo layout note**: The `compiler/` directory contains an older
> "Pryde"-branded snapshot that predates the current codebase. It is NOT
> built by `build.sh` or `Makefile`. The active source is the 19 `*.c3`
> files in the repository root. The `compiler/` directory will be removed
> in a future cleanup commit.

---

## Legend

| Mark | Meaning |
|------|---------|
| ✅ | parse + resolve + IR + llvm-as + exec verified |
| 🔶 | IR ok, edge case in codegen / partial |
| 🔷 | parse ok, IR/codegen incomplete |
| ❌ | not implemented |

---

## §3 Lexical

| Feature | Status | Notes |
|---------|--------|-------|
| Line comments `--` | ✅ | |
| Nested block comments `--[...]` | ✅ | |
| Hex `0xFF`, bin `0b`, oct `0o`, underscore `1_000` | ✅ | |
| Float literals `3.14`, `1.5e-3`, `f32`/`f64` suffix | ✅ | `strtod`-based parsing |
| Integer suffixes `i8` `u8` `i32` `u32` `i64` `u64` etc. | ✅ | Correct tymap type |
| Bool `true`/`false`, `null` | ✅ | |
| Char literal, string literal, raw bytes `b"..."` | ✅ Fixed this session | The parser previously hardcoded EVERY char literal's decoded value to `0` regardless of content (`node_char(self.arena, 0, ...)` at both call sites) — every `'x'` silently became NUL. Also fixed a lexer ambiguity where a single-letter/underscore char literal (`'a'`, `'_'`) was always mislexed as the start of a `'label` reference instead. String/raw-bytes literals were unaffected. |
| `'label` reference lexing | ✅ | |
| Unicode operators `→ ↦ ∩ ∪ ⊥ ≥ ≤ ≠` etc. | ✅ | |

## §4 Primitive Types

`i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 bool chr ptr isize usize () (A,B) *T i128 u128` — all ✅

`i128`/`u128` arithmetic specifically: division and modulo were **silently
wrong** for any value not fitting in 64 bits until this session — the
runtime's `__udivti3`/`__divti3`/`__umodti3`/`__modti3` compiler-rt
intrinsics (which real LLVM `i128`/`u128` codegen calls directly) were
declared with 64-bit parameter/return types, truncating every 128-bit
operand before dividing. Verified and fixed against a real LLVM 22
toolchain — see `finds.md` §7 and `.review_notes/i128_division_critical_bug.md`.

## §5 Bindings

| Feature | Status |
|---------|--------|
| `let x : T = v` / `let x = v` / `let mut z` | ✅ |
| Compound assign `+= -= *= /= %= &= \|= ^= <<= >>=` | ✅ Fixed this session |
| Tuple destructure / `let _` wildcard | ✅ |

## §6 Functions

| Feature | Status | Notes |
|---------|--------|-------|
| Multi-clause `fn` with literal + tuple + guard patterns | ✅ | |
| Function pointer params `fn f : (i64 -> i64, i64) -> i64` | ✅ | |
| Higher-order: `apply(add5, 10)` → `15` | ✅ Exec verified | |
| Zero-capture closure | ✅ | |
| Capturing closure (multi-var) | 🔶 | Basic capture works; complex env chains untested |
| `#[inline] #[cold] #[pure] #[hot]` attributes | ✅ | |
| `extern fn` / `#[extern("name")]` | ✅ | |

## §7 Control Flow

| Feature | Status |
|---------|--------|
| `if`/`else if`/`else` (inline + block) | ✅ |
| `while` / `do`-`while` | ✅ |
| `for i in lo..hi` / `lo..=hi by step` | ✅ |
| `break` (bare + with value) / `continue` | ✅ |
| `break 'label` / `continue 'label` | ✅ |
| `defer` with correct scoping | ✅ |
| `match` multi-arm + wildcard + guard | ✅ Exec verified |

## §8 Pattern Matching

Multi-clause literal patterns compiled to decision trees (Maranget's algorithm in `pgen.c3`) — ✅ exec verified

## §9 Structs

| Feature | Status | Notes |
|---------|--------|-------|
| Field read/write, construction | ✅ | |
| Struct return + field access | ✅ Exec verified | `dot(Vec2, Vec2)` = 11 |
| All field GEP indices correct | ✅ Fixed | Was off-by-one for 2nd+ fields |
| `struct update { base \| field: val }` | ✅ | |
| `#align` / `#packed` | ✅ | |
| **Union type `∪` (tagged union)** | 🔷 | Parses to `NODE_TYPE_UNION`. **Not lowered in `ssi_ir.c3` or `codegen.c3`**. Conformance tests pass because they only test parse+resolve, not codegen. Runtime behavior undefined. |
| **Intersection type `∩`** | 🔷 | Parses to `NODE_TYPE_INTERSECT`. **Not lowered in `ssi_ir.c3` or `codegen.c3`**. Same status as union. |

> **Honest status on ∪/∩:** The conformance tests 29, 30, 31 pass because they
> test parse/resolve/type-check only. Codegen for union/intersection types falls
> through to the generic `ptr`/`i64` fallback. This means subtyping coercions
> are not enforced at runtime — they are type-system annotations only.
> A real codegen implementation requires a tagged-union representation and
> discriminant-based dispatch, which is on the roadmap.

## §10 Algebraic Effects

| Feature | Status | Notes |
|---------|--------|-------|
| Effect declaration + perform | ✅ Exec verified | |
| Effect row `! [IO, Alloc, Log]` tracking | ✅ | |
| Effect propagation through call chains | ✅ Exec verified | |
| `ub!` explicit UB effect | ✅ Exec verified | pattern-guards prevent runtime UB |
| Single-arm `handle` + `resume` | 🔶 | Works end-to-end via `getcontext`/`setcontext` |
| Multi-arm effect dispatch | 🔶 | Dispatch always routes to arm 1; op_id→arm_index map is TODO. Multi-arm handlers with different ops will always fire arm 1. |
| Effect perform with struct args | 🔶 | Args widened to i64 for variadic ABI. Struct args not supported. |

## §11 Wrapping / Saturating / Checked Arithmetic

| Op | Status | Notes |
|----|--------|-------|
| `+%` `-% `*%` wrapping (two's complement) | ✅ Exec verified | |
| `+\|` `-\|` `*\|` saturating | ✅ | Emits `llvm.sadd.sat` etc. Fixed from `add nsw` stub. |
| `+?` `-?` `*?` checked (returns `{T, bool}`) | ✅ Fixed this session | Was previously ❌: the lexer never fused `+?`/`-?`/`*?` into single tokens at all (only `+%`/`+\|` had the required 2-char lookahead in `lex_punct`), so despite real parser/codegen support existing (`llvm.sadd.with.overflow` etc.), the feature was completely unreachable — `1 +? 2` parsed as `+` followed by a stray `?`. Fixed by adding the missing lookahead branches. |

## §12 Generics

Monomorphization via `mono.c3` (Cooper/Harvey/Kennedy idom, BFS body). Generic fns + structs — ✅

## §13 Type System

| Feature | Status |
|---------|--------|
| Bottom type `⊥` | ✅ |
| `∪` union type annotation | 🔷 parse/typecheck only, no codegen |
| `∩` intersection type annotation | 🔷 parse/typecheck only, no codegen |
| Refinement types (SASI σ-nodes) | ✅ |

## §14 Explicit UB

`ub!` / `assume` / `trap` / `unreachable` / `poison` + `freeze` — ✅ exec verified

## §15 Memory

`alloc` scalar + arrays, `free`, `*p` deref, `&x`, `p+i`, `p[i]`, casts, `sizeof`, `alignof`, `offset_of` — ✅

## §16–19 Research Features

| Feature | Status | Notes |
|---------|--------|-------|
| Term rewriting `rewrite { \| lhs ↦ rhs }` | ✅ | Discrimination tree, hash-consing, worklist. `MAX_REWRITE_DEPTH=800` fuel limit (silent bail on overflow — known issue). |
| Pattern generation `pgen` | ✅ | Maranget decision tree compilation |
| IRDL dialect + lowering | ✅ Exec verified | Multi-rule, literal-pattern, variadic. |
| MSP staging `comptime` + `eval` | ✅ | AST-level interpreter in `stage.c3` |
| `\|>` pipeline operator | ✅ | |

## §20 Self-Hosting Progress

| Milestone | Status |
|-----------|--------|
| `lexer.pie` compiles to LLVM IR (llvm-as clean) | ✅ |
| `lexer.pie` binary boots and tokenises Pride source | ✅ Verified |
| `ast.pie` | ❌ Not written |
| `parser.pie` | ❌ Not written |

## Stdlib

**20 modules, ~2,300 LoC** in `compiler/stdlib/` (`.pie` format, experimental).  
Not yet integrated into the compiler pipeline. These are prototype implementations.

The claimed "49 modules, 11,882 LoC" in a previous checklist version was wrong —
there were 20 `.pie` + 20 `.pry` (old Pryde format) = 40 files, ~4,500 LoC total.
The `.pry` files use the old Pryde syntax and are not valid Pride source.

## Known Bugs / TODOs

1. **Union/intersection codegen**: `∪` and `∩` parse and typecheck but emit no IR. Runtime behavior unspecified.
2. **Multi-arm effect dispatch**: `perform()` always returns arm index 1. The op_id→arm_index mapping needs to be stored in the handler frame and populated from the generated TERM_SWITCH case table.
3. **Effect `resume` with struct values**: Currently only primitive (i64/ptr) resume values work. Struct resume requires aggregate-by-value handling.
4. **Rewrite fuel overflow**: `MAX_REWRITE_DEPTH=800` silently bails — should be a diagnostic.
5. **Float literal suffix `f32`**: Parser extracts bits=32 correctly but `node_float` doesn't truncate the `double` value, so `f32` literals may have excess precision in IR.
6. **`compiler/` dead directory**: Contains old "Pryde" snapshot. Not used in build. To be removed.

---

## Test Results (2026-07-26)

```
conformance: 242/242 PASS
exec tests:   18/18 PASS (hello, fibonacci, primes, dynamic alloc,
              mutual recursion, wrapping ops, bitops, pattern match,
              higher-order fns, FNV-1a, step ranges, struct ops,
              IRDL lowering, effects, explicit UB, semantic subtyping,
              pgen decision tree, SASI refinement)
```
