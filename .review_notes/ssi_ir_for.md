# ssi_ir.c3 — SsiModule.lower_for(): step-ranges ("by") are structurally unsupported

Confirmed via static reading of ssi_ir.c3:3927-4095 (`SsiModule.lower_for`):

1. `bool is_range = (iter != null && iter.kind == Nk.NODE_EXPR_RANGE);`
   (line ~3936) — this test only recognizes plain `NODE_EXPR_RANGE`. A step
   range produced by the parser's `by` clause is a DIFFERENT node kind,
   `NODE_EXPR_RANGE_STEP` (see ast.c3, parser.c3 parse_range ~2785-2789). So
   `for i in lo..hi by step` always takes the `is_range = false` branch,
   which:
     - builds `test` as an opaque `IR_UNKNOWN` wrapping the (already-opaque,
       since NODE_EXPR_RANGE_STEP also has no lower_expr_body case — see
       below) iterator value, used directly as a boolean loop condition —
       this is nonsensical for a range value (an IR_RANGE-shaped or
       IR_UNKNOWN-shaped SSA value being truth-tested does not implement
       "has next"),
     - binds the loop variable `binder` to a **fresh, unconstrained
       `IR_PARAM`** (ssi_ir.c3 ~4045) rather than any actual iteration value
       — i.e. inside the loop body, the loop variable is bound to an
       arbitrary/undefined SSA value with no defining computation, since
       nothing ever assigns to that IR_PARAM.
   This is a correctness bug independent of the "by" feature: ANY iterable
   that isn't literally `lo..hi`/`lo..=hi` (so, definitely `NODE_EXPR_RANGE_STEP`,
   but potentially any future/other iterable expression) silently produces a
   loop whose induction variable is uninitialized garbage in the IR — no
   diagnostic, no crash, just wrong/undefined codegen.

2. Even setting aside the node-kind mismatch: the back-edge increment is
   HARDCODED to `+1` regardless of any step:
   ```
   IrVal* one = m.new_val(IrOp.IR_CONST_INT, n);
   if (one != null) { one.ival = 1; m.emit(one); }
   back_counter = ...counter_phi + one...
   ```
   (ssi_ir.c3 ~4064-4073). There is no code path anywhere in `lower_for` that
   reads a step value from a `NODE_EXPR_RANGE_STEP`'s third child (the step
   expression) and uses it instead of the constant 1. So even if (1) were
   fixed to recognize `NODE_EXPR_RANGE_STEP` as a range, step ranges would
   still increment by 1 every time, silently ignoring the user's requested
   step and producing a semantically wrong number of iterations (e.g.
   `for i in 0..10 by 2` would iterate i=0,1,2,...,9 instead of 0,2,4,6,8).

Net effect: the parsed, dedicated step-range AST shape
(`RangeStepData{inclusive, has_step}` + 3 children start/end/step, ast.c3
~1023-1035) is completely unconsumed by the only lowering pass that would
need it (`ssi_ir.c3`) — matching the project's confirmed pattern from
finds.md (features that parse+typecheck but silently do nothing/wrong thing
at codegen). `grep -rn RANGE_STEP *.c3` outside ast.c3 returns zero hits,
confirming no pass past parsing ever looks at this node kind — not
resolve.c3 (falls through to the generic default recursion, which is at
least safe), not typecheck.c3 (same — no dedicated type rule, so `x..y by z`
presumably gets an implicit/absent type rather than the range's element
type — worth flagging but lower severity), and definitely not ssi_ir.c3.

Also relevant: even a maximally-simple `let r = 0..10 by 2` (no `for`, just
building the step-range value) has no lower_expr_body case for
NODE_EXPR_RANGE_STEP either (confirmed: `awk` scan of the full switch in
lower_expr_body lists NODE_EXPR_RANGE at line ~301 relative offset but no
RANGE_STEP entry) — so it falls to the generic `default:` arm, which lowers
it as an opaque `IR_UNKNOWN` node whose args are the lowered children
(start, end, step lowered independently, but the IR_UNKNOWN carries no
semantic meaning "this is a stepped range" for any later consumer, including
codegen.c3, to act on).

Recommendation: either (a) implement full step-range lowering (extend
`is_range` detection to also match `NODE_EXPR_RANGE_STEP`, extract lo/hi/step,
and use the step value instead of hardcoded 1 in the back-edge), or (b) if
not ready, have typecheck/integrity reject `by`-step for-loops with a clear
"not yet implemented" diagnostic rather than silently emitting wrong/garbage
IR — consistent with how the project handles other known-gaps (though even
those, per finds.md, aren't diagnosed either; this is the same anti-pattern
repeating).
