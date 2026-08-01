# SSI-IR Design — The Backend's Input Contract

This is the SSA-CFG that the **backend lowers to LLVM**. It is produced by
`ssi_ir.c3` (`SsiModule.build(program)`), verified by `SsiModule.verify()`, and
printed by `./pride --dump-ir <file>`. Read [`../status/FRONTEND_STATUS.md`](../status/FRONTEND_STATUS.md) §3 first; this
doc is the detailed reference + worked examples.

## Why "SSI" and not plain SSA

Pride's IR is **Static Single Information** form: standard SSA (single
assignment, φ-merges at joins) PLUS **σ-nodes** ("sigma") on the out-edges of
conditional branches. A σ-node rebinds a value on a specific branch and carries a
**refinement** (the fact learned by taking that edge). Example: after
`if a > b`, on the true edge `a` is rebound to a σ-node `refined:(>)`; on the
false edge `refined:(<=)`. This gives every later use strictly-more information,
which the SASI pass and any backend optimizer can exploit.

**The backend does not have to care about σ if it doesn't want to.** After the
SASI pass (`sasi.c3`) runs, σ-nodes are swept out of the instruction stream into
a side fact-map and the CFG becomes **clean standard SSA**. Lower the clean form
for simplicity; consult the fact-map only for optimization.

## Data structures (`ssi_ir.c3`)

### IrVal — an SSA value
```
id          dense value id (v0, v1, …)
op          IrOp (see below)
bop         operator token, for IR_BIN / IR_UN
ival/fval/bval/sptr+slen   constant payloads
args[]      operands (growable heap array); IR_CALL: args[0]=callee, args[1..]=args
pred[]      IR_PHI only: predecessor block id for each operand (args[i] from pred[i])
refinement  IR_SIGMA/IR_PHI: the flow fact node (or null)
binder      the source binder this value is a version of (for φ/σ naming)
src         originating AST node (keep for diagnostics / debug info)
block       owning block id
```

### IrOp
```
IR_CONST_INT, IR_CONST_FLOAT, IR_CONST_BOOL, IR_CONST_STR, IR_CONST_NULL, IR_CONST_UNIT
IR_PARAM     a root SSA def (function parameter / pattern-bound value)
IR_BIN       binary op (.bop is the operator)
IR_UN        unary op (.bop)
IR_CALL      args[0] = callee value, args[1..] = argument values
IR_FIELD     a.field          (args[0] = base; field name via .src)
IR_INDEX     a[i]             (args[0] = base, args[1] = index)
IR_CAST      a as T           (target type via .src / .type_annotation)
IR_TUPLE     (a, b, …)
IR_ARRAY     [a, b, …]
IR_STRUCT    S { … }
IR_ALLOC     heap allocation  (carries EFFECT_ALLOC)
IR_FREE      free
IR_RANGE     a..b
IR_PHI       φ-merge: args[i] arrives from predecessor block pred[i]
IR_SIGMA     σ-split: args[0] = source value, .refinement = learned fact
IR_UNKNOWN   opaque expression — kept so lowering is ALWAYS total
```
**IR_UNKNOWN matters:** the frontend never drops a construct. Anything it cannot
reduce to a concrete op becomes `IR_UNKNOWN` (operands preserved in args). Your
backend must handle it — emit a trap, or treat it as an opaque black-box value
with the right type. This guarantees you can bring codegen up incrementally:
implement ops one at a time; everything else is a well-formed `IR_UNKNOWN`.

### IrBlock — a basic block
```
id
phi_head/phi_tail   φ-node list (block head; φs always precede instructions)
head/tail           straight-line instruction list
term                TermKind
cond                CBR/SWITCH discriminant value
ret_val             RET value (may be null = unit)
succ[]/pred[]       edges (growable)
case_val[]/case_has[]   SWITCH: integer label per succ[i] (i>=1; succ[0]=default)
```

### TermKind
```
TERM_RET          return ret_val (null ⇒ unit)
TERM_BR           unconditional → succ[0]
TERM_CBR          cond ? succ[0] (true) : succ[1] (false)
TERM_SWITCH       switch cond: succ[0]=default, succ[1..]=labelled cases
TERM_UNREACHABLE  provably dead (after a diverging branch: return/ub!/trap)
TERM_NONE         open block — should NOT survive a complete build
```

### SsiFunc
```
decl              source fn decl
name/name_len
entry             entry block id
block_start       first block id owned by this fn
block_count       contiguous count → blocks [block_start, block_start+block_count)
params[]          parameter IrVals (these are IR_PARAM roots)
```

## Verified invariants (you may assume these)

1. **SSA dominance:** every use is dominated by its definition.
2. **φ placement:** φ-nodes only at block heads; each φ has exactly one operand
   per incoming predecessor edge, in `pred[]` order.
3. **No dangling refs:** `VerifyResult.undef_refs == 0` (every operand is a
   defined value or param).
4. **Reducible CFG** for all structured control flow (if/while/do/for/match,
   break/continue). Loops have a header block with φs; `continue` adds a back-edge
   operand to each header φ; `break` routes to the loop exit (exit φs merge the
   normal-exit value with each break-site value).
5. **Termination:** every block has a real `term` (never `TERM_NONE`) in a
   completed build.

Assert `verify().errors == 0 && verify().undef_refs == 0` before lowering.

## Worked example

Source:
```pride
fn max : (i64, i64) -> i64
  | (a, b) -> if a > b then a else b
```
`./pride --dump-ir`:
```
fn max  (entry B0, 4 blocks)
  B0:
    v0    = param
    v1    = param
    v2    = bin '>' (v0, v1)
    cbr v2 ? B1 : B2
  B1:   ; preds: B0
    v3    = sigma {a} (v0)  refined:(>)     ; a, knowing a > b
    br B3
  B2:   ; preds: B0
    v4    = sigma {a} (v0)  refined:(<=)    ; a, knowing a <= b
    br B3
  B3:   ; preds: B1 B2
    v5    = phi (v3@B1, v1@B2)              ; then→a(=v3), else→b(=v1)
    ret v5
```
LLVM sketch (clean-SSA view, σ collapses to its source):
```
define i64 @max(i64 %a, i64 %b) {
entry:  %c = icmp sgt i64 %a, %b
        br i1 %c, label %t, label %f
t:      br label %j
f:      br label %j
j:      %r = phi i64 [ %a, %t ], [ %b, %f ]
        ret i64 %r
}
```

## Loops (break/continue) — what to expect

`while c { … continue … break … }` lowers to: a header block (φs for every
binder mutated in the loop), a body block, and an exit block. Each `continue`
contributes an extra operand to every header φ (its back-edge value); each
`break` records its site so the exit block can φ-merge break values with the
normal fall-through. This is already built and verified — you just emit the
blocks/φs as given.

## Practical lowering order (recommended)

1. Build `SsiModule`, assert integrity + IR verify == 0.
2. For each `SsiFunc`: declare the LLVM function, map `IR_PARAM`s to LLVM params.
3. Pre-create one LLVM basic block per IrBlock id (so edges can reference them).
4. Walk blocks in id order; for each: emit φs (LLVM `phi`), then instructions
   (one `switch` over `IrOp`), then the terminator (one `switch` over `TermKind`).
5. Map types from `IrVal.src.type_annotation` / the fn signature. Generics arrive
   abstract — **monomorphize at this layer** (the frontend deliberately does not).
6. `IR_UNKNOWN` / `IR_ALLOC` / `IR_FREE` / `IR_CALL` to runtime: bind to the
   thin runtime (crt0 + allocator) as it comes up incrementally.

---

# Appendix — Structural Overview (previously SSI_IR_DESIGN.md)

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
