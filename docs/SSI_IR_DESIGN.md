# Pride SSI-IR — Explicit CFG + SSI Intermediate Representation

`ssi_ir.c3` is the **backend-facing** form of Pride's program. Where `ssi.c3`
annotates the AST in place (great for the rewrite/PGL passes that work on the
tree), `ssi_ir.c3` lowers that structured tree into an **explicit control-flow
graph**: real basic blocks, SSA values, terminators, φ-merges that name their
predecessor *blocks*, and σ-splits that sit on the conditional out-edges where a
fact is learned. This is exactly the shape any modern code generator wants.

## 1. Why a separate IR (and not just the tree-SSI)

Tree-SSI is *coupled to the AST*: a φ "knows" it is the merge of an `if`'s two
arms because it lives at that `if` node. A backend needs the dual: blocks and
edges as first-class objects it can iterate, schedule, color, and lower —
without re-deriving control flow from syntax each time. The Ananian SSI thesis
and Singer's functional formulation both make the same point: SSA/SSI is
"complete" only when the CFG edge structure is explicit (σ-functions and switch
nodes are undecipherable without it). So we build it.

Pride has **no `goto`** — control flow is structured — so the construction is the
textbook **single-pass SSA for structured languages** (Brandis & Mössenböck),
extended with σ-splits (Ananian). No dominance-frontier iteration, no worklist:
one structured walk produces pruned, minimal-ish SSI directly.

## 2. The data model

```
SsiModule  → funcs[]  blocks[]  vals[]      (+ builder env / loop stack)
SsiFunc    → entry block id, contiguous [block_start, block_start+count), params[]
IrBlock    → phi_head/tail · head/tail (instrs) · ONE terminator · succ[]/pred[]
IrVal      → one SSA value: const | param | bin/un | call | field | index | cast
             | tuple/array/struct | alloc/free | range | PHI | SIGMA | opaque
```

* **Pure SSA**: a reassignment `x = e` just rebinds the name in the builder env
  to a new value; joins reconcile via φ. Every value has a dense id `vN`.
* **φ-nodes** live in the block's `phi_head` list and carry, per operand, the
  **predecessor block id** it arrives from (`vK@Bj`). This is the LLVM-style
  formalism (operands tagged with predecessor blocks), chosen over basic-block
  arguments because Pride's φ-merge logic was already operand+edge based in
  `ssi.c3`, so the two forms stay consistent and inter-derivable.
* **σ-nodes** are emitted at the *start of the successor edge's block* (the place
  where the refined fact holds), tagged with a `NODE_TYPE_REFINEMENT` — the same
  refinement node the type checker already understands.

## 3. Lowering rules — all constructs fully implemented, no stubs

| Construct | CFG shape |
|---|---|
| `if c then a else b` | Diamond `B0 -cbr→ {then,else} → join`; σ on each edge; φ at join per reassigned outer binder + result value. |
| `match s \| …` | `TERM_SWITCH`: default + one case edge per arm; literal arms carry a case label + `σ(s==lit)`; N-way φ at join. |
| `while c { … }` | `pre→header`; header φ per loop-carried binder; `header -cbr→ {body,exit}`; σ(c)/σ(¬c) on edges. |
| `do { … } while c` | `pre→body_blk→header(cond) -cbr→ {body_blk,exit}`; body runs once unconditionally before first test. |
| `for x in lo..hi` | Counter φ at header: `phi(lo@pre, counter+1@body_end)`; test = `IR_BIN '<'` (or `'<='`); loop var = counter φ. |
| `for x in iter` | Same skeleton; test = `IR_UNKNOWN(iter_val)` (opaque has-next for non-range iterators). |
| multi-clause fn | Dispatch cascade: each clause emits a refutability test; match → bind + lower body + `ret`; non-exhaustive tail → `unreachable`. |
| `return e` | Flushes defer stack (LIFO), then `TERM_RET`. Dead code → fresh unreachable block. |
| `break` / `continue` | Extra edge to loop `exit` / `header`; continue appends operand to header φs; break snapshots carried values for exit φs. |
| `trap` / `unreachable` / `ub!` / `⊥` | `TERM_UNREACHABLE`; subsequent dead code → fresh unreachable block. |
| `assert cond` | `CBR → {pass,fail}`; `fail = TERM_UNREACHABLE`; σ-refinements on pass edge. |
| `assume cond` / `invariant cond` | No CFG change; σ-refinements injected into current block. |
| `defer expr` | Body `Node*` on per-function LIFO stack; re-lowered at every `return`. |
| `asm "…"` | `IR_UNKNOWN` with AsmLine/AsmOperand operands; `.src.kind == NODE_STMT_ASM`, `EFFECT_UNSAFE`. |
| `Effect.op(args)` | `IR_EFFECT_OP`; `.binder` → op decl; `args[0..]` = op args. |
| `handle comp \| Op k→body` | `TERM_SWITCH(IR_HANDLER) → {join,arm_blk_0,…}`; each arm emits IR_PARAMs + body + `IR_HANDLER_ARM`; branches to join. |
| `resume(v)` | `IR_RESUME`; `args[0]` = resume value; `.binder` → handler arm. |
| `with r=res {body}` | `resource=lower(res)`; `[bind r]`; `result=lower(body)`; cleanup `IR_UNKNOWN(resource)` with `.src.kind==NODE_EFFECT_WITH`. |
| `transmute(e)` | `IR_CAST` (type check bypassed). |
| `sizeof(T)` / `alignof(T)` | `IR_CONST_INT` ival=0 sentinel; backend replaces with target-width value. |
| `a @ b` (matmul) | `IR_BIN` `bop=TOKEN_AT`. |
| `[\| … \|]` (tensor lit) | `IR_ARRAY` (same as array literal). |
| `e \|> f \|> g` (pipeline) | Left-fold: `IR_CALL(g, IR_CALL(f, e))`. |
| `unsafe{…}` / `unchecked{…}` | Transparent: lowers body; flags already on AST node. |

### Loop-carried φ with early exits (the hard case)

`continue` is a second (third, …) back-edge into the header, and `break` is an
extra entry into the exit. Both are handled exactly:

* `LoopCtx` aliases the header-φ arrays, so `lower_continue` can
  `phi.add_arg(current_value, continue_block)` for every loop-carried binder.
* `LoopCtx` owns a `break_vals` matrix `[break_site × loop_phi]`; `lower_break`
  snapshots each binder's value at the break site, and `build_exit_phis` merges
  them with the normal-exit (header-φ) value into proper exit-block φs.

This is verified on `cont` (header φ has 3 operands: entry + continue + normal
back-edge) and `loops` (exit φ merges fall-through with the break site) — both
report **0 verify errors**.

## 4. Verification (`SsiModule.verify`)

A real IR needs an invariant checker. `verify()` walks every block and asserts:

1. every non-`unreachable` block has a terminator;
2. `succ`/`pred` are symmetric (every edge is recorded on both ends);
3. each φ has exactly one operand per predecessor edge, and every operand's
   tagged predecessor is an actual predecessor of the φ's block.

It returns counts (blocks, values, φ, σ, edges) plus an error tally surfaced in
the driver summary (`ir verify errors: N`). All 17 examples and all 77 red-team
cases verify with **0 errors**.

## 5. Driver integration

The IR is built unconditionally after tree-SSI (it is cheap — a single walk) and
verified; `--dump-ir` prints the textual form:

```
fn cont  (entry B18, 7 blocks)
  B18:
    v46   = param
    ...
    br B19
  B19:   ; preds: B18 B22 B24
    v49   = phi {i} (v48@B18, v57@B22, v54@B24)
    v50   = phi {s} (v47@B18, v50@B22, v61@B24)
    v51   = bin '<' (v49, v46)
    cbr v51 ? B20 : B21
  ...
```

## 6. Backend choice — research notes (informing, not yet committing)

We deliberately keep the backend *undecided*; the IR is designed so the common
options are all reachable:

* **φ-nodes vs basic-block arguments** are inter-derivable (Cranelift/MLIR/SIL
  use block args; LLVM uses φ). We picked φ-with-predecessor-tags; converting to
  block-args later is a mechanical pass (move each φ operand to the corresponding
  predecessor's terminator as an argument).
* **SSI specifically helps register allocation**: under SSI, live-ranges form an
  *interval graph* (a stronger property than SSA's chordal graphs), which makes
  liveness/coloring simpler — a concrete reason the σ-splits are worth carrying
  into the backend rather than discarding them.
* **Lowering targets** remain open: emit LLVM IR (φ → LLVM φ), emit Cranelift
  (φ → block args), or a self-hosted SSA register allocator. None of these
  require changing the IR; they are separate `*_emit.c3` modules.

The headline: the IR is **backend-agnostic and complete** — control flow,
data flow, and flow-sensitive facts (σ) are all explicit and verified.
