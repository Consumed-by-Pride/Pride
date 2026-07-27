# SSI-IR Design — The Backend's Input Contract

This is the SSA-CFG that the **backend lowers to LLVM**. It is produced by
`ssi_ir.c3` (`SsiModule.build(program)`), verified by `SsiModule.verify()`, and
printed by `./pryde --dump-ir <file>`. Read `FRONTEND_STATUS.md` §3 first; this
doc is the detailed reference + worked examples.

## Why "SSI" and not plain SSA

Pryde's IR is **Static Single Information** form: standard SSA (single
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
```pryde
fn max : (i64, i64) -> i64
  | (a, b) -> if a > b then a else b
```
`./pryde --dump-ir`:
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
