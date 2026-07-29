# Step 4 — SASI-driven optimization (`sasi_opt.c3`)

The active-vision goal: use the SASI fact map (step 2) to **delete redundant
instructions** on the clean SSA CFG (step 3 output), then re-verify.

## What it does (four passes, fixpointed)

1. **Redundant-comparison folding.** A comparison value `v = a <cmp> k` whose
   truth is already implied by a SASI fact on `a` (crawling the dominating-σ
   chain via `parent`) is replaced by a constant bool. E.g. inside
   `if n>10 { if n>5 ... }` the inner `n>5` is statically true.

2. **Branch folding.** A `cbr cond` whose `cond` is now a constant bool becomes
   an unconditional `br` to the taken successor; the untaken edge is removed
   (predecessor lists + φ operands fixed up via `detach_edge`).

3. **Unreachable pruning.** Blocks that lose all predecessors (and aren't a
   function entry) become `TERM_UNREACHABLE`; their out-edges are removed and
   successors' φ operands dropped — iterated to a fixpoint.

4. **Dead-code elimination.** A mark-sweep over value uses: pure instructions and
   φ with no remaining users are removed from their block lists, recomputed to a
   fixpoint. Impure ops (call/alloc/free/struct/param/unknown) are always kept.

## The reasoning core — a sound integer-implication checker

`implies(fc, fk, qc, qk)` decides whether a known fact `a <fc> fk` (true) forces
a query `a <qc> qk` to be **D_TRUE**, **D_FALSE**, or **D_UNKNOWN**. It models the
fact as an inclusive integer interval `[lo, hi]` (with ±∞ sentinels and overflow
guards) and asks whether the query holds for *every* point in that interval
(→TRUE) or *no* point (→FALSE):

```
fact n>10  → interval [11, +∞)
query n>5  → true for all x≥11        ⟹ D_TRUE      → fold to `true`
query n<0  → false for all x≥11       ⟹ D_FALSE     → fold to `false`
query n>100→ mixed over [11,+∞)       ⟹ D_UNKNOWN   → leave untouched
```

`!=` facts are handled specially (only same-point queries are decidable).
Equality facts (`n==5`) pin the interval to a point, so `n==5 ⟹ n>0` folds.
Everything not decidable is left exactly as-is — the pass is **conservative and
never changes program meaning**.

The query value's operand `a` is the σ-handle the comparison reads (SASI kept σ
values as abstract handles), so `fact_of(a)` finds the immediate fact and
`.parent` walks the dominating chain — so `if a { if b { if c ... } }` decides a
query against the conjunction `a ∧ b ∧ c` by trying each fact in turn.

## CFG-edit safety

Every edit preserves the SSA-CFG invariants `ssi_ir::verify()` checks:
- `detach_edge(from,to)` removes one succ occurrence, one pred occurrence, and
  the matching φ operand (the one tagged with predecessor `from`).
- pruning rebuilds out-edges before marking a block unreachable.
- DCE only removes values with zero live users.

The driver re-runs `ir.verify()` after optimization and reports `opt verify errs`
(must be 0).

## Worked example

`if n>0 { if n>0 {r=1} else {r=2} }`:
```
SASI:  v4{n}:=n>0 [B1]   v7{n}:=n>0 [B4, parent v4]   (inner is redundant)
opt:   redundant compares folded : 1   (inner n>0 → true)
       branches folded (cbr→br)  : 1   (B1: cbr → br B4)
       blocks pruned             : 1   (B5 = else, now unreachable)
       dead instructions removed : 4
result: B1 → br B4 unconditionally; B5 unreachable; φ collapsed to one operand
```

## Driver
`--dump-sasi` prints the fact map, the σ-stripped CFG, the optimization report,
and the optimized CFG. Summary counters: `opt compares`, `opt branches`,
`opt blocks pruned`, `opt dead removed`, `opt verify errs` (must be 0).

## Test status
- **Red-team**: 105/105 (cases 101–105: redundant-true, redundant-false,
  undecided-no-fold, equality-chain, deep 4-level nest folding 3 compares).
- **Examples**: all 17 verify clean post-opt (0 errors; no spurious folds).
- **ASan**: 0 failures across 488 runs (files × 4 flags).
- **Mutation fuzz**: 4000 runs — 0 crashes, **0 `opt verify errs` violations,
  0 leftover-σ violations**. The optimizer provably never builds an invalid CFG.

## Pipeline status
```
1. SSI Tree ........................ done (ssi.c3, polished)
2. SASI Fact Map ................... done (sasi.c3)
3. Clean SSA CFG ................... done (falls out of step-2 σ-strip)
4. SASI-driven optimization ....... done (sasi_opt.c3)  ← active vision reached
5. Backend / teardown ............. open (decide after 4)
```

## Hardening round (full-blown upgrade pass)

A dedicated correctness/robustness pass found and fixed multiple latent bugs:

### IR correctness
- **Dangling SSA references**: else-less `if`, global/fn-ref idents, null-rhs
  assignments, and pattern-ident fallbacks created `IR_*` values that were never
  emitted into any block → dangling φ/instruction operands. Now every value-
  producing path emits its result (`mk_unit` for units). The IR verifier was
  upgraded to **check operand definedness** (`undef_refs`), which surfaced these
  across 9 example files; all now report 0.
- **Wide control flow**: φ-operand and block-edge arrays were fixed-size
  (`MAX_OPERANDS=16`, `MAX_EDGES=32`), so matches/switches with >16 arms
  silently produced invalid IR. These are now **growable heap arrays** (doubling,
  freed in `destroy`). A 3001-arm match lowers cleanly (3003 blocks, 0 errors).
  Match-arm bookkeeping is heap-sized to the arm count (no `MAX_ARMS` cap).
- **Null-source σ**: a σ whose refined value wasn't in scope produced an
  unresolvable SASI fact. `emit_sigmas` now skips σ with no source; `add_fact`
  defensively skips them too. Result: 0 unresolved facts on all fuzzed inputs.

### Stack-overflow guards (found by ASan fuzzing)
Depth guards added to every recursive AST/IR walker that lacked one:
`ssi.walk`, `ssi_ir.lower_expr`/`lower_program`, `effectcheck.gather`,
`lint.walk`/`collect_binders`/`mark_used`, `typecheck.walk`, and the driver
collectors (`collect_rules`, `apply_at_pipelines`, `collect_pgen_nodes`) plus the
printers (`print_node`, `print_type_brief`, `print_expr`). resolve/typecheck-synth
already had guards.

### Rewrite engine
- **Float/char/string hash-cons + matching** were value-blind (`term_eq`/
  `term_hash`/`match_term` ignored float/char/string payloads), so distinct
  literals could be wrongly unified. Now compared bit-exactly (`bitcast` for
  floats) — a real hash-cons soundness fix.

### Optimizer reach
- **Boolean condition folding**: `if flag { if flag }` now folds the inner
  branch via the bool σ-fact (`decide_value` crawls the chain for `flag==bool`).
- **Constant arithmetic folding**: `fold_const_arith` folds `IR_BIN` with two
  constant-int operands (signedness-correct), catching arithmetic exposed after
  SASI folding + DCE.

### Validation after hardening
- Red-team: 108/108 (added 106 wide-match-φ, 107 else-less-if-value,
  108 deep-type-union regression cases).
- All 122 corpus files: 0 ir-verify / 0 opt-verify / 0 leftover-σ / 0 unresolved.
- Mutation fuzz: ~19,000 cumulative runs across the round, ending at
  **0 crashes, 0 invariant violations**; ASan-clean (no leaks).

## Hardening round 2 — structure-aware fuzzing

Random byte-mutation mostly produces parse errors; to exercise the *semantic*
pipeline deeply I added a structure-aware fuzzer that emits VALID nested Pride
programs (if/while/for/match/break/continue/return over mutable vars). It found
two real **post-optimization CFG corruption** bugs that byte-fuzzing missed:

1. **Pruned RET block kept its `ret_val`** — `prune_unreachable` blanked a
   block's instructions but left `ret_val` pointing at a now-undefined φ. Fixed:
   clear `ret_val` (and `cond`) when pruning.

2. **Unreachable strongly-connected components** — the old pred-count pruning
   could not remove an isolated infinite loop after a diverging loop (each block
   in the cycle has a predecessor *within* the cycle), leaving dangling operand
   references. Replaced with **true reachability pruning**: a worklist DFS from
   every function entry marks reachable blocks; everything unmarked is pruned.
   This is the principled, dominance-correct fix.

Regression cases 109 (infinite-loop prune) and 110 (unreachable SCC) added.

### Cumulative fuzz (this round)
~24,000 runs across three channels — byte-mutation (5954), structure-aware
(4000), structure-aware-with-control-flow (4000), plus earlier sets — ending at
**0 crashes, 0 invariant violations, 0 leaks** (LeakSanitizer clean). The four
machine-checked invariants hold on every input: `ir verify errors = 0`,
`opt verify errs = 0`, `sasi sigma left = 0`, `sasi unresolved = 0`.
