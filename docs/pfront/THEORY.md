# `pfront/theory` — the analysis layer

**Verified 2026-07-31** · c3c 0.8.1 · LLVM 22.1.8 · Debian 13 trixie x86-64

**16,066 LoC across 21 modules.** Every one is wired into the pipeline, runs
on real input, and is covered by the regression suite. Nothing here is
unreachable.

---

## 0. What this layer is FOR

Read this before adding a pass.

**Pride is untyped. No analysis in this directory may reject a program.**

That is not a style preference — it changes what an analysis is *for*. A
conventional compiler computes facts in order to refuse bad programs. Pride
computes the same facts in order to **optimize good ones**:

| Fact an analysis proves | Conventional compiler | Pride |
|---|---|---|
| index out of bounds on every path | error, build fails | mark path unreachable → **delete it** |
| condition always false | warning | **fold the branch away** |
| index provably in range | nothing | **elide the bounds check** |
| pointer provably non-null | nothing | **elide the null check** |
| variable never live across an edge | nothing | **no φ needed** (semi-pruned) |
| type mismatch | error | advisory under `--lint`, nothing by default |

The enforcement point is a single function pair in `pfront_core.c3` —
`DiagBag.advisory` / `advisory_hint`. Advisories are off unless `--lint` is
passed, and are always warnings. To add a type-policing *error* you would have
to call `.error()` directly, which is visible in review.

**There is no borrow checker, no lifetime checker, and no ownership analysis.
None is planned.** One was on an early roadmap; it was never written and the
item is withdrawn.

---

## 1. Module list

| Module | LoC | Contents |
|---|---:|---|
| `theory_opt.c3` | 1,663 | **The optimizer.** Const folding, algebraic identities, branch folding, 3-way DCE, copy propagation, CSE, block flattening |
| `theory_live.c3` | 1,029 | **CFG + liveness + semi-pruned classification.** The `SP` of SP-ERM-e-SSI |
| `theory_poly.c3` | 804 | **Polymorphism: constraint solving + real instantiation.** Unifies declared parameter types against call arguments to produce a substitution θ, checks bounds, applies θ to build a monomorphic signature per instance |
| `theory_absint.c3` | 979 | Abstract interpretation: sign, interval (widen/narrow), nullness; fixpoint over loops |
| `theory_check.c3` | 907 | Pipeline driver, gradual sort checking, per-pass timing |
| `theory_rowinfer.c3` | 834 | Principal-type effect-row inference |
| `theory_pglcert.c3` | 791 | PGL certificates: exhaustiveness with a named counter-example |
| `theory_stage.c3` | 783 | Staged partial evaluation, binding-time analysis, loop unrolling |
| `theory_modal.c3` | 764 | Scoped effects, continuation trees, UB tracking |
| `theory_bidi.c3` | 748 | Bidirectional CMTT: box types become inferrable |
| `theory_egraph.c3` | 740 | E-graphs: union-find + congruence closure, equality saturation, cost extraction |
| `theory_subtype.c3` | 726 | Set-theoretic subtyping by reduction to DNF emptiness |
| `theory_irdlverify.c3` | 725 | IRDL verification traits: SSA form, dominance, purity, termination |
| `theory_effects.c3` | 722 | Handler coverage, linearity, effect rows |
| `theory_irdl.c3` | 688 | Dialect/opcode registry and lowering |
| `theory_cmtt.c3` | 616 | Modal judgment `Γ ⊢^E e : □_{Γ'}^{L'} τ at L` |
| `theory_msp.c3` | 602 | Stage lattice, cross-stage escape, quote hash-consing |
| `theory_trs.c3` | 543 | Term rewriting: discrimination tree, critical pairs, fuel |
| `theory_bridge.c3` | 525 | Parser↔theory bridge, feature scan, convention audit |
| `theory_verify.c3` | 461 | AST integrity: 8 invariants, transform snapshot diff |
| `theory_term.c3` | 387 | Structural hashing, hash-consing, substitution |

---

## 2. Why each component earns its place

**E-graphs (`theory_egraph`).** The destructive rewriter throws away `a + 0`
when it applies `a + 0 ↦ a`, so results depend on rule order. Given
`x*2 ↦ x<<1`, `x*1 ↦ x`, `(a*b)/b ↦ a`, the term `(a*2)/2` reaches `a` **only
if the shift rule fires last**. An e-graph keeps both forms, so extraction finds
`a` regardless of order. Congruence closure is maintained incrementally with a
dirty worklist; extraction is a fixpoint over a pluggable cost model where a
shift costs 2 and a multiply costs 5.

**Partial evaluation (`theory_stage`).** Staging is only useful if stage-0 code
actually runs. Binding-time analysis classifies each expression static or
dynamic — conservatively, since refusing to evaluate is always safe and the
reverse is not. Specialising `power(n,x)` at `n=3` unrolls to `x*(x*(x*1))`.
The interpreter is fuel-bounded, so a divergent stage-0 program is a diagnostic
rather than a hung compiler.

**Row inference (`theory_rowinfer`).** Effect signatures need not be written.
The (HANDLE) rule is what makes the system worth having: handling an effect
*removes* it from the row, so `main` can be pure though its callees perform
State and IO. Generalisation uses levels — quantifying a variable shared with
an enclosing scope is the classic unsoundness this prevents.

**Bidirectional CMTT (`theory_bidi`).** A quotation's type cannot be
synthesised in general: `<x + y>` could be `□(i64)` or `□(f64)`. Checking mode
pushes the expectation inward. (SUB) is the only non-syntax-directed rule,
which keeps everything else deterministic.

**IRDL traits (`theory_irdlverify`).** A dialect author writes
`opcode gadd : Pure, Commutative` and gets verification plus canonicalisation
opportunities. Dominance uses Cooper-Harvey-Kennedy over the region's block
graph — a use not dominated by its definition reads uninitialised memory on
some path.

**PGL certificates (`theory_pglcert`).** "Not exhaustive" sends the reader
hunting; "does not handle `Some(None)`" does not. The witness search is a
constructive reading of Maranget's usefulness algorithm. Proving a match
*is* exhaustive is recorded too, so the backend can omit the fallback branch.

**Semantic subtyping (`theory_subtype`).** `A <: B` iff `⟦A ∩ ¬B⟧ = ∅`, decided
on a DNF. That reduction makes distributivity, De Morgan, and `A ∩ ¬A <: ⊥`
fall out automatically instead of being special-cased. Arrows are handled
conservatively — a false negative rejects a valid program with a clear message,
a false positive miscompiles.

---

## 3. Verified behaviour

```
$ bash pfront_tests/run.sh
pfront regression: pass=37 fail=0
stdlib self-clean: 119 / 253   (baseline before rewrite: 4)
```

| Test | Asserts |
|---|---|
| `26_effects_perform` | effect decl + `perform E.op()` registers 2 ops |
| `27_ub_outside_unsafe` | `ub!` outside `unsafe` → E3230 |
| `28_stage_escape` | cross-stage reference → E3202 |
| `29_splice_stage0` | splice with no quotation → E3201 |
| `30_gradual_sort` | calling a non-function → W4060 |
| `31_trs_rule` | rewrite block collects and fires |
| `32_irdl_dialect` | dialect + opcode registers |
| `33_comptime_let` | `let x = comptime 3*4` evaluates *(found a real parser bug)* |
| `34_exhaustive_witness` | missing variant → warning naming the witness |
| `35_egraph_rewrite` | e-graph builds classes and saturates |

**A real parser bug fell out of this work.** `let x = comptime 3i64 * 4i64`
reported "not computable at compile time" while the same expression inline
succeeded. The cause was `parse_block_or_expr`'s virtual-block heuristic
absorbing the *following statement* into the comptime body. Inline `comptime`
now parses a single expression. Test 33 locks it in.

---
---


---

## 4. Pipeline order

24 passes. Order is load-bearing; the comments in `theory_check.c3` say why
each pass sits where it does. The shape:

```
 0  feature scan + convention audit     what constructs are even present
 1  register dialects / effects         must exist before any use is checked
 2  staging soundness                   BEFORE rewriting moves terms around
 2b CMTT judgment                       contexts, kinds, levels
 2c handler coverage + effect rows
 2d monomorphisation census
 2e bidirectional modal typing
 2f row inference
    ── snapshot taken here ──
 3  term rewriting to normal form
 3b comptime forcing + partial evaluation
 3c equality saturation                 order-independent, unlike 3
 4  dialect validation + lowering
 5  continuation-tree normalisation
 6  UB accounting
 7  gradual sort checking
 7b IRDL verification traits
 7c PGL certificates
 7d semantic subtyping / match refinement
 7e abstract interpretation             intervals, signs, nullness
 7e′ LIVENESS + semi-pruned split       ← builds the CFG
 7f THE OPTIMIZER                       ← consumes everything above
 8  handler-arm linearity
 9  verify + snapshot diff              catches a bad rewrite at its source
```

Passes whose constructs are absent are skipped, so the report has no rows of
zeroes.

---
## 5. Parser integration

| Syntax | Node | Consumer |
|---|---|---|
| `quote e` / `~Tree e` | `N_EXPR_QUOTE` | msp, cmtt, bidi |
| `box[Γ] e at Stage L` | `N_EXPR_QUOTE` + env child + `p.aux` | cmtt, bidi |
| `splice e` | `N_EXPR_SPLICE` | msp, cmtt |
| `stage N { … }` | `N_EXPR_QUOTE` with level | msp, stage |
| `comptime e` | `N_EXPR_COMPTIME` | stage |
| `perform E.op(a)` | `N_EXPR_PERFORM` | modal, rowinfer |
| `resume(v)` | `N_EXPR_RESUME` | modal linearity |
| `rewrite name \| lhs -> rhs` | `N_DECL_FN` + clauses | trs, egraph |
| `pgen name where [p] ↦ a` | `N_DECL_FN` (`aux=2`) | irdl/PGL, pglcert |
| `dialect D / opcode o` | `N_DECL_INTERFACE` | irdl, irdlverify |
| `irdl D.op [a,b] ↦ act` | `N_DECL_INTERFACE` (`aux=3`) | irdl |
| `ub! "reason"` | `N_EXPR_UB` | modal UB |
| `A ∪ B`, `A ∩ B`, `¬A` | `N_TY_UNION/INTERSECT/NEGATION` | subtype |
| `! [IO, ..r]` | `N_TY_EFFECT_ROW` | rowinfer |

`perform` and `resume` are recognised **contextually**, so programs using
either as a variable still compile. Payload conventions (`p.aux` overloading)
are documented and enforced in `theory_bridge.c3`.

---

## 6. Honest limits

- **Arrow subtyping is conservative.** The full set-theoretic decomposition is
  more involved; unproven cases answer "not a subtype", which rejects rather
  than miscompiles.
- **E-matching binds class representatives**, not full class enumeration. Some
  matches inside large classes are missed — sound, not complete.
- **Partial evaluation models no heap, pointers, or I/O.** Anything it cannot
  model stays dynamic.
- **Monomorphisation is a census**, not an instantiation: it records what the
  middle end will need without duplicating bodies.
- **Row inference does not yet feed the HM type inferencer**; the two run
  side by side rather than as one solver.
- **Liveness is intra-procedural.** A store to a variable captured by a
  closure, or reachable through a pointer, is conservatively kept.
- **CSE reports redundancy, it does not rewrite.** Introducing a temporary
  needs a scope to hold it; that is the middle end's job. The count is what
  the SSI builder will consume.
- **Block flattening never fires on the stdlib** (0 sites). It needs a folded
  branch to expose a spliceable block, and stdlib code has none. It fires on
  the regression cases, so it is tested, but its real-world value is unproven.
- **The optimizer removes ~0.3% of stdlib nodes.** Most stdlib code is
  declarations, and partial evaluation already folds static arithmetic before
  the optimizer sees it. On dynamic-value code the reduction is 50–96%.

---

## 7. Untyped-language policy — every demoted diagnostic

Section 0 states the rule. This is the complete list of what changed, so a
reviewer can check nothing was missed:

| Situation                                | Old behaviour        | Now                        |
|------------------------------------------|----------------------|----------------------------|
| assignment to a non-`mut` binding         | `E3330` hard error   | accepted; advisory only    |
| write through a non-`mut` pointer         | `E3332` hard error   | accepted; advisory only    |
| type mismatch                             | `E3100` under strict | advisory only              |
| wrong argument count                      | `E3102` under strict | advisory only              |
| unknown field                             | `E3104`/`E3353`      | advisory only              |
| index out of bounds on every path         | `E3360` hard error   | advisory + optimizer fact  |
| ambiguous overload / method               | `E3340`/`E3341`      | advisory; first match used |
| duplicate impl / missing interface method | `E3320`/`E3321`      | advisory only              |

Advisories are **off by default** and surface only under `--lint`, always as
warnings, never as errors. They route through a single chokepoint —
`DiagBag.advisory` / `DiagBag.advisory_hint` in `pfront_core.c3` — so it is
impossible to add a type-policing error by accident: you would have to call
`.error()` directly and the reviewer would see it.

**There is no borrow checker, no lifetime checker and no ownership analysis,
and none will be added.** A borrow/lifetime checker was on an earlier plan; it
was never written and the plan item has been withdrawn.

### So what are the analyses *for*?

Optimization. Every fact that used to justify a rejection now justifies a
transformation instead:

* interval analysis proves an index in range  → **bounds check elided**
* interval analysis proves it out of range    → **path marked unreachable**
* nullness proves a pointer non-null          → **null check elided**
* a decided condition                         → **branch folded away**

This is the same information with the opposite posture: the developer keeps
their program and the optimizer gets the benefit.

---

## 8. `theory_opt.c3` — the optimizer (1,663 LoC)

Runs as pass 7f, after every analysis (so it consumes their facts) and before
the verifier (so a bad rewrite is caught by the snapshot diff).

**Passes, each iterated to a fixpoint (max 8 rounds):**

1. **Constant folding** — integer/float arithmetic, comparison, logical,
   bitwise, and casts *with correct truncation* (`300 as u8` → `44`).
   Declines to fold `x/0` and `INT64_MIN / -1` rather than bake in a wrong
   value.
2. **Algebraic simplification** — `x+0`, `x*1`, `x*0`, `x-x`, `x^x`, `x&x`,
   `x|x`, `x&-1`, `x<<0`, `!!x`, `--x`, plus the comparison forms
   (`x==x` → `true`). Needs no constants, so it fires on dynamic values.
3. **Branch folding** — `if true`/`if false` collapse to the taken arm;
   `while false` is deleted entirely.
4. **Dead code elimination**, three distinct notions:
   * *unreachable* — statements after `return`/`break`/`ub!`/`trap`
   * *useless* — a pure expression in non-tail position whose value is dropped
   * *dead store* — a `let` nobody reads, **only if its initializer is pure**
5. **Copy propagation** — `let a = b` rewrites later `a` to `b`, killed
   correctly on any assignment to either side.
6. **CSE** — structural value numbering per block; reports redundancy for the
   SSI builder to consume.

### The purity interlock

`is_pure` answers *"definitely no side effects"* and is deliberately
conservative — calls, assignments, `perform`, asm, syscall, atomics, volatile,
alloc/free and deref all answer **false** and are never removed. Getting this
backwards would delete the user's I/O, which is the one unforgivable optimizer
bug.

Locked by test `44_opt_purity`, which asserts **exactly one** of two dead
stores is removed: the pure one goes, the one initialized by a function call
stays.

### Pass composition

Passes exist to feed each other; that is why the pipeline iterates to a
fixpoint (max 8 rounds). Test `48_opt_cascade` asserts the full chain:

```pride
fn f : i64 -> i64
  | n ->
      if 1i64 > 0i64      -- 1. condition folds to `true`
        return n          -- 2. branch folds to the then-arm
      let after = n * 2i64--    ...whose block is then FLATTENED into the parent
      after               -- 3. the spliced `return` makes these unreachable
```

Result: `(fn f (clause (pat-ident n) (block (return (ident n)))))` — 16 nodes
down to 7, **56%**, in three rounds. Asserting only the final node count would
pass even if one link in the chain broke, so the test checks each stage
individually.

### Measured on the real stdlib (253 files)

```
useless exprs   : 115      dead stores : 44
algebraic       :   9      const-fold  :  1 arith
branches folded :   1      unreachable :  0
blocks flattened:   0      files changed: 35 / 253
```

Total ≈170 transformations, 442 nodes removed of 125,481 (**0.3%**). That
number is unflattering and it is the honest one: most stdlib code is
declarations, and partial evaluation already folds static arithmetic before
this pass runs. On code with dynamic values the reduction is large — the
regression cases hit **50%**, **56%**, **61%**, and a 12,000-binding generated
file hits **96%**.

---

## 9. `theory_live.c3` — CFG, liveness, semi-pruned (1,029 LoC)

This is the **SP** of SP-ERM-e-SSI, and it is what makes the DCE above more
than a syntactic tidy-up.

### Why semi-pruned

Three classical φ-placement strategies:

| Strategy | φ count | Analysis cost |
|---|---|---|
| **Minimal** | φ at every iterated dominance frontier of every def | cheap, wasteful — most φs are for variables dead at the join |
| **Pruned** | φ only where the variable is live-in | minimal φs, but needs full liveness for every variable first |
| **Semi-pruned** | φ only for variables live **across a block boundary** | most of pruned's benefit, a fraction of the cost |

Briggs, Cooper, Harvey & Simpson (*Practical Improvements to the Construction
and Destruction of Static Single Assignment Form*, SP&E 1998) measured
semi-pruned as capturing most of the benefit for much less analysis. That is
the right trade for Pride: the front end runs on every keystroke in an editor;
the back end does not.

A variable used and killed inside one block can never need a φ, and
semi-pruned excludes it **without ever running full liveness**.

### What it computes

1. A **CFG** per function. Pride has no `goto`, so block structure is derived
   syntactically: `if` forks and rejoins, `while` gets a real back edge,
   `return`/`break`/`ub!`/`trap` terminate, `match` arms fan out to a join.
2. Per-block **GEN** (used before defined) and **KILL** (defined here) sets.
3. **LIVE-IN / LIVE-OUT** by backward iterative dataflow to a fixpoint:
   ```
   live_out[b] = ⋃ live_in[s]  for s ∈ succ(b)
   live_in[b]  = gen[b] ∪ (live_out[b] \ kill[b])
   ```
   Blocks are visited in reverse creation order — an approximation of reverse
   postorder, which converges in far fewer passes for a backward problem.
4. The **non-local set**: variables live across at least one edge. This is
   exactly the semi-pruned φ-placement set.
5. **Dead definitions**, fed to the optimizer.

Everything is a fixed-width bitset over a dense variable numbering, so the
dataflow inner loop is a word-at-a-time OR. `bs_count` uses Kernighan's
popcount (loops once per *set* bit).

### Correctness details that took care

- **Address-taken variables are conservatively non-local.** `&x` means the
  value can be read or written through the pointer anywhere, so it is
  recorded as both a use and a def.
- **`let x = <init>` records the init's uses BEFORE the binding exists.**
  Otherwise `let x = x` looks like a self-reference rather than a use of an
  outer `x`.
- **Compound assignment (`x += 1`) is a use *and* a def.**
- **`a.f = v` reads `a`** to find the location; only a bare identifier LHS is
  a pure def.

### Measured

On the real 253-module stdlib:

```
3,788 functions · 13,804 blocks
7,059 non-local (need φ) · 6,497 block-local
→ 47% of all variables need NO φ
0 capacity overflows
```

Contrast asserted by tests 46/47:

| Input | non-local | block-local | dataflow iters |
|---|---:|---:|---:|
| loop with carried `acc`, `i` | 3 | 1 | 3 |
| straight-line `a→b→c` | 0 | 4 | 1 |

`--dump-cfg` prints the graph:

```
b0 entry succ=[b1]      live_in=0 live_out=0
b1 block succ=[b2]      live_in=0 live_out=3
b2 loop  succ=[b3,b4]   live_in=3 live_out=3
b3 body  succ=[b2]      live_in=3 live_out=3   ← back edge
b4 join  succ=[]        live_in=2 live_out=0
```

### How the optimizer uses it

A store can be dead for two independent reasons. The **syntactic** one (no
identifier refers to the binder) is always available. The **liveness** one is
strictly stronger: a variable can be referenced textually and still be dead,
because every such reference is itself in dead code.

The optimizer only trusts liveness for variables classified **block-local** —
proving a non-local variable dead needs the interprocedural picture this pass
does not have. Liveness-driven removals are counted separately in the report.

---

## 10. `pfront_dump.c3` — final AST emitter (332 LoC)

`--dump-ast` shows the parse tree. `--emit-ast` / `--emit-sexp` show the
**final** tree, after rewriting, partial evaluation, e-graph extraction and
the optimizer — i.e. what the middle end will actually consume.

Annotations: resolution targets with node ids, effect rows, operator spelling,
literal values after folding, and a **`SYN` marker** distinguishing
compiler-synthesised nodes from source text.

`--emit-sexp` prints one S-expression per top-level declaration — stable and
diffable, which is what makes it usable as an optimization regression
baseline.
