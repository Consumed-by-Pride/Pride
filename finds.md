# Pride: Promises vs Reality Findings

This document tracks inconsistencies and bugs between the stated promises of the Pride language (in `CAPABILITIES_CHECKLIST.md` and documentation) and the actual implementation.

## 1. Semantic Subtyping Hallucination (Intersections & Unions)
**Promise**: True structural semantic subtyping with Unions (`|`) and Intersections (`&`). The checklist explicitly states: `🔷 ∩ intersection type (parse ok, codegen partial)` and `❌ union type (∪ parse gap; ASCII | accepted but codegen incomplete)`.
**Reality**: 
- `NODE_TYPE_UNION` and `NODE_TYPE_INTERSECT` are successfully parsed and represented in the `typecheck.c3` subtyping lattice.
- However, `ssi_ir.c3` and `codegen.c3` completely drop these nodes on the floor. Neither file handles them. If a union or intersection type makes it out of the type checker, the compiler will panic or ignore it during IR lowering and code generation.

## 2. Multi-Stage Programming (MSP) Leaks
**Promise**: Compile-time staging, `comptime`, and evaluation interleaving smoothly with compilation.
**Reality**:
- `stage.c3` correctly evaluates `NODE_STAGE` and `NODE_EXPR_COMPTIME` nodes.
- **Inconsistency**: If an unresolved `NODE_STAGE` block (e.g. dependent on generic parameters or untracked state) escapes `stage.c3` and reaches LLVM generation, there is no code path in `ssi_ir.c3` or `codegen.c3` to catch or gracefully reject it. The backend will crash.

## 3. Algebraic Effects: Hardcoded Variadic ABI
**Promise**: Native, strongly-typed effect tracking and perform/resume mechanics.
**Reality**:
- The frontend tracking and `IR_EFFECT_OP` IR translation are quite impressive.
- **Inconsistency**: In `codegen.c3` (lines ~4050-4080), the code generator blindly widens sub-i64 integer arguments to make them fit a hardcoded variadic ABI call to `__pride_perform` (`call @__pride_perform(op_id, ...)`). This is a brittle hack that circumvents the type-map and will likely corrupt complex struct arguments or vectors.

## 4. Term Rewriting `MAX_REWRITE_DEPTH` Hack
**Promise**: Turing-complete, first-class AST term rewriting.
**Reality**:
- The engine implements `strat_innermost`, `strat_outermost`, and confluence checking.
- **Inconsistency**: To prevent infinite recursion, `rewrite.c3` forces `MAX_REWRITE_DEPTH = 800`. If a rewrite sequence reaches 800 steps, it silently aborts and returns the partially rewritten AST (`rw.too_deep = true; return t;`). No warning or error is surfaced to the user; the compiler simply proceeds with malformed code.

## 5. The "Split-Brain" Directory Issue
**Major Architectural Bug**: The codebase has two divergent sources of truth for the compiler frontend.
- There is a `compiler/` directory full of `.c3` files (`compiler/codegen.c3`, `compiler/ssi_ir.c3`, etc.).
- There are duplicate `.c3` files directly in the root directory.
- `build.sh` and `Makefile` use the root files. The files in `compiler/` seem to be a ghost version (e.g., `compiler/codegen.c3` is 211KB and references "Pryde", whereas `./codegen.c3` is 296KB and references "Pride").
- Any changes made to the `compiler/` directory are ignored by the build system.

## 6. Operator Overloading IR Generation Bug
**Promise**: Operator overloading via interface dispatch.
**Reality**:
- `ssi_ir.c3` accurately detects operator overload calls and attempts to generate an `IR_CALL`.
- **Inconsistency**: The callee is injected as `IR_UNKNOWN` with its binder pointing to the AST `NODE_DECL_FN`. While `codegen.c3` tries to catch this with `known_fn_ref` logic, the indirection is extremely brittle and bypasses standard function pointer resolution if the impl method isn't monomorphized correctly.

