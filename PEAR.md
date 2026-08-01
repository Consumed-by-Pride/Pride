# PEAR — Prideful Engine for Abstractive Representations

**Status:** design, not yet implemented
**Date:** 2026-07-31
**Target:** LLVM 22.1.8 · c3c 0.8.1 · x86-64 Linux

---

## 0. What PEAR is

PEAR is Pride's middle and back end. It takes the AST that `pfront` produces
and carries it, through five deliberately-chosen intermediate forms, to
executable output.

```
pfront ──PNode──▶ a1 ──AIR──▶ a2 ──AIR′──▶ a3 ──CPS──▶ a4 ──PON──▶ a5 ──▶ X
                 build      analyse+DCE   DB/delim    defunc      λ̄μμ̃
                                          CPS         + layout    + emit
```

| Stage | Directory | Input | Output | Job |
|---|---|---|---|---|
| **a1** | `pear/a1/` | `pfront_core::PNode` | **AIR** | Build SP-ERM-e-SSI |
| **a2** | `pear/a2/` | AIR | AIR′ | Analyses, optimisation, DCE |
| **a3** | `pear/a3/` | AIR′ | **CPS** | Double-barrelled + delimited CPS; continuation DCE |
| **a4** | `pear/a4/` | CPS | **PON** | Defunctionalisation, closure conversion, explicit layout |
| **a5** | `pear/a5/` | PON | **X** | λ̄μμ̃ symmetric form, global dual DCE, emission |

`a1` reads the **AST**, never Pride source. There is no second Pride
lexer or parser: `pfront` owns the grammar, and PEAR owns everything after it.

### The IR name

**SP-ERM-e-SSI** — Semi-Pruned, Exceptional, Range-bounded, Memory-aware,
extended Static Single Information.

`FG` (Future-Gated) was **dropped**. FGSA's own abstract states it *"produces
pruned single assignment form, rendering a separate pruning step
unnecessary"* — so FG and SP are mutually redundant by construction, and
adopting FG would mean replacing dominance-frontier placement with T1/T2/TR
interval analysis and inverting the def-before-use invariant that every
existing pass depends on, for a measured 7.7% average gain.

**Infinitary CPS** was **dropped** for a related reason: its premise is that
untyped languages encode recursion with fixed-point combinators. Pride does
not. Pride has named recursive functions, and `pfront_flow.c3` already
computes recursion with Tarjan SCC over a real call graph. The problem
Infinitary solves does not exist here. Structural bisimulation remains
interesting as *function deduplication* and may return later as a flag-gated
`a3` pass, scoped honestly as the largest single component in the project.

---

## 1. Why this specific chain

Each conversion exists because it makes a class of elimination **visible** to
the next stage. That is the whole argument, and it is the reason the order
cannot be permuted.

| Step | What becomes visible | Elimination it unlocks |
|---|---|---|
| AST → **e-SSI** | one name per live range; branch-derived facts | range/bounds/null-check elision |
| e-SSI → **CPS** | control flow as ordinary data; both barrels | dead *continuations* — invisible in SSA |
| CPS → **PON** | closure envs, handler frames as explicit records | dead environment fields |
| PON → **λ̄μμ̃** | producers paired with consumers | unmatched producer / unactivated consumer |
| λ̄μμ̃ → **X** | — | final emission |

**Why PON before λ̄μμ̃.** A DCE pass can only delete what has been made
explicit to it. If closures and environment records are still implicit when
the symmetric pass runs, that pass cannot see inside them. Defunctionalising
first turns every captured variable into an ordinary producer, so an
unconsumed capture becomes an unmatched producer and dies like anything else.
This mirrors why LLVM runs `argpromotion`/`globalopt` before heavy IPO.

**Why CPS before PON.** Closure conversion needs to know what is actually
captured. In direct style that requires a separate free-variable analysis
over a control-flow graph; in CPS the continuation *is* the environment, so
capture sets fall out of the representation.

---

## 2. Cross-cutting decisions

These apply to every stage and are the parts most likely to be got wrong if
left implicit. They are decided here, up front.

### D1 — Origin threading (the fact-survival mechanism)

**Problem.** `R` (ranges) and `M` (memory) are computed in `a2`. They only
pay off at `a5`, as `range(lo,hi)`, `!nonnull`, `!alias.scope`. They must
survive **four** conversions. The default outcome — the one that happens if
nothing is designed against it — is that `a2` computes excellent facts and
`a5` emits none of them, leaving `ERM` decorative.

**Decision.** Every construct in every IR carries:

```c3
uint origin;    // the AIR value id this descends from; 0 = synthesised
```

Facts live in **one side table keyed by origin**, never inline in the term:

```c3
struct FactTable
{
    // keyed by AIR value id
    Interval[]  ranges;       // R: [lo,hi] per value
    Nullness[]  nullness;     // R: never/maybe/always null
    uint[]      mem_def;      // M: reaching MemoryDef
    uint[]      alias_scope;  // M: !alias.scope id
    bool[]      no_alias;
}
```

Rules, enforced by `pear_verify`:

1. A conversion **copies** origin; it never invents or reuses one.
2. A genuinely new construct gets `origin = 0` and is documented as such.
3. A pass that merges two constructs keeps the origin of the **dominating**
   one and records the merge in a log.

**Measurement.** `--verify-facts` reports how many `a2` facts reached
emission. That number is the honest measure of whether `ERM` works, and it is
reported in the build output whether it is flattering or not.

### D2 — No sentinel overloading

`ssi_ir.c3` stores six distinct meanings in one `ival` field — `-1`, `-2`,
`-3`, `0`, `1`, and the magic number `55555` — covering address-of-field
mode, array-element update, atomic ordering, field index, and sizeof
sentinels. Reading that code requires knowing which meaning is live at each
site, and the `r43`–`r46` fix markers cluster exactly there.

**Decision.** Named fields or a tagged payload union. No integer sentinels
with site-dependent meaning. Any field whose interpretation depends on the
opcode is documented in the opcode's own comment block.

### D3 — Every IR is printable and re-readable

Each of AIR, CPS, PON and λ̄μμ̃ has a **textual form** with a printer and a
parser. Cost: roughly 200–400 lines per stage. Buys:

- every stage testable in isolation, without running the ones before it
- every optimisation diffable — a regression is a text diff, not a
  behavioural mystery
- hand-written test inputs for `a3`/`a4`/`a5` before `a1` is finished
- round-trip property tests: `parse(print(x)) == x`

This is the single highest-leverage decision in the document. `ssi_ir.c3` has
a dump but no reader, so every backend test must run the whole front end
first.

### D4 — Call-by-value orientation is fixed and enforced

λ̄μμ̃ is **not confluent**. The command `⟨μα.c₁ ∥ μ̃x.c₂⟩` reduces two ways
and the results differ: μ-first is call-by-name, μ̃-first is call-by-value.

Pride is strict. **`a5` fixes μ̃ priority (call-by-value)**, and the verifier
rejects any rewrite that resolves the critical pair the other way. Getting
this wrong does not crash — it silently reorders effects, which is the worst
possible failure mode.

### D5 — Stage isolation

`a_{n+1}` may not reach back into `a_n`'s data structures, and **no stage may
read a `PNode` except `a1`**.

This is not stylistic. `codegen.c3` has 285 references to `ssi_ir::` but also
**34 direct `ast::` references** — it reaches past the IR into AST nodes for
struct layout, global types and effect metadata. That coupling is why it
cannot be reused by swapping the IR underneath. A CI grep enforces the rule:

```sh
grep -l "pfront_core::PNode" pear/a[2-5]/*.c3   # must be empty
```

Anything a later stage needs must travel *in the IR*. If something is missing,
the fix is to add it to the IR, never to peek backwards.

### D6 — Growable storage, no silent truncation

`ssi_ir.c3` caps at `MAX_OPERANDS 16`, `MAX_EDGES 32`, `MAX_IR_VALS 65536`.
A wide switch or a large function silently overflows.

**Decision.** Arena-backed growable arrays. Where a hard cap is unavoidable,
exceeding it sets an `overflowed` flag that is **reported**, and the affected
analysis degrades to "unknown" rather than to "wrong".

---

## 3. `pear/a1/` — AST to AIR

**Input** `pfront_core::PNode` · **Output** AIR · **Est.** ~3,500 LoC

### Contents

| File | Purpose |
|---|---|
| `air.c3` | The AIR datatype: `AirValue`, `AirBlock`, `AirFunc`, `AirModule` |
| `air_print.c3` | Textual writer |
| `air_parse.c3` | Textual reader (D3) |
| `build_cfg.c3` | `PNode` → basic blocks |
| `build_ssa.c3` | φ placement, renaming |
| `split_sigma.c3` | σ placement: the `e` and `E` of the acronym |
| `verify.c3` | The four strong-SSI properties |

### The four properties `verify.c3` checks

From Boissinot et al., as restated in Tavares et al. 2012:

1. **pseudo-definition** — every variable has a definition at CFG entry
2. **single reaching-definition** — each program point is reached by at most
   one definition of each variable
3. **pseudo-use** — every variable has a use at CFG exit
4. **single upward-exposed-use** — from each point at most one use is
   reachable without passing a previous use

Plus structural checks inherited from `ssi_ir.c3`'s `verify()`, which are
sound and worth keeping: every live block has a terminator; succ/pred are
symmetric; each φ has exactly one operand per predecessor; no dangling
value references.

### σ placement — where the `e` and `E` come from

`e-SSA` (Bodík et al.) splits at **conditionals**. `E` (Exceptional) splits at
**potentially-diverging operations**. Pride has no try/catch, so the ESSI
"success twin / crash twin" idea maps onto Pride's actual constructs:

| Site | Split | Why |
|---|---|---|
| `if c` | σ on every binder in `c` | e-SSA; gives `R` its facts |
| `match` arm | σ per arm | pattern narrowing |
| `perform E.op(…)` | σ across the operation | control may not return, or may resume with a different value |
| `ub!` / `trap` / `unreachable` | terminator, ⊥-typed | divergent |
| `/`, `%`, `[]`, unary `*` | σ on the operand | the fault twin |
| `alloc` | σ on the result | may fail |

`resume` is the interesting case and the one with no exception-language
analogue: it is a **re-entry** edge, closer to a coroutine yield. It gets a
dedicated AIR construct rather than being modelled as a call.

### SP — semi-pruned, done as on-demand conversion

The papers this design follows are explicit that full SSI is rarely wanted.
Tavares et al. 2010 measured ABCD and CCP requesting **15× and 24× faster**
conversion than full SSI, generating **6.5× and 10× fewer** σ/φ instructions.

So **SP means client-driven partial conversion**: a pass declares which
variables it needs in SSI form, and only those are split. Requests are logged
so two clients asking for the same variable do not duplicate work.

The **default client filter** is semi-pruned liveness, which
`theory_live.c3` already computes: a variable is split only if it is live
across a block boundary. Measured on the real stdlib — 3,788 functions,
13,804 blocks — **47% of variables never cross an edge** and need no φ at
all.

### Reused from `pfront`

- `theory_live.c3` — CFG construction, backward liveness, non-local set
- `theory_absint.c3` — interval/sign/nullness lattices, seeding `R`
- `pfront_core::Arena` — slab allocator

---

## 4. `pear/a2/` — analysis and optimisation on AIR

**Input** AIR · **Output** AIR′ (same form) · **Est.** ~4,000 LoC

| File | Purpose |
|---|---|
| `range.c3` | `R`: non-iterative range analysis over σ-refinements |
| `memssa.c3` | `M`: MemoryDef / MemoryUse / MemoryPhi |
| `sccp.c3` | Sparse conditional constant propagation |
| `dce.c3` | Aggressive DCE over the SSI graph |
| `abcd.c3` | Bounds-check elimination |
| `facts.c3` | The `FactTable` of D1 |

`R` follows Rodrigues/Quintão Pereira's non-iterative range analysis:
build a constraint graph from σ-refinements, find SCCs, solve each in
topological order with widening then narrowing. Non-iterative because the
σ-nodes already encode the branch conditions.

`M` is MemorySSA in the LLVM sense — `MemoryDef` for each store,
`MemoryUse` for each load, `MemoryPhi` at joins — and it feeds `!alias.scope`
and `!noalias` at `a5`.

**What `a2` DCE catches:** unreachable blocks, values with no consumers,
stores to locations never loaded, branch arms σ-proven impossible.

**What it cannot catch:** dead *continuations*. That is `a3`'s job, and it is
the reason `a3` exists.

---

## 5. `pear/a3/` — double-barrelled delimited CPS

**Input** AIR′ · **Output** CPS · **Est.** ~4,500 LoC

| File | Purpose |
|---|---|
| `cps.c3` | The CPS term datatype |
| `cps_print.c3` / `cps_parse.c3` | Textual form (D3) |
| `to_cps.c3` | AIR′ → CPS; the SSA→CPS correspondence |
| `delimit.c3` | `handle`/`perform`/`resume` → `reset`/`shift`/invoke |
| `cont_dce.c3` | Dead-continuation elimination |
| `contract.c3` | β-contraction, η-reduction, inlining |

### Double-barrelled

Every function takes **two** continuations:

```
f(x, k_ok, k_err)
```

Pride has no exceptions, which makes this a *better* fit than the usual
argument suggests. The error barrel carries `ub!`, `trap`, `unreachable`,
`assert` failure and allocation failure. Once divergence is an ordinary value
flow, a DCE pass can prove an entire failure path unreachable and delete it
along with everything it holds live — which is exactly what `E` is for, and
gives the `E` work in `a2` a real lowering target instead of a dead end.

### Delimited — already native to Pride

The spec (`docs/reference/v.md`, line 593) says of handlers:
*"k is the continuation; calling k(v) resumes the computation with value v."*
Pride's effect system **is** a delimited-continuation construct:

| Pride | Delimited CPS |
|---|---|
| `handle comp \| arms` | `reset` — the prompt |
| `perform E.op(args)` | `shift` — capture up to the prompt |
| `resume v` | invoke the captured slice |

Today `codegen.c3` lowers this to a setjmp/longjmp prompt stack that its own
header calls *"the simplest correct ABI"*. Delimited CPS replaces a hack with
the construct the language already means.

### Dead-continuation elimination

The elimination SSA structurally cannot express. A continuation is dead when:

- it is never invoked on any path (unreachable handler arm)
- its result is discarded outside its own prompt — with `reset` marking the
  boundary, the whole control sub-tree goes
- both barrels of a call lead to the same continuation, so the split was
  pointless and collapses

The third case is the common one after `a2` has proven a fault impossible.

### Preserving `R` and `M` (D1 applied)

CPS is a *tree*; AIR is a *graph*. The conversion is sound (Kelsey, *A
Correspondence between CPS and SSA*) but it is exactly where facts get
dropped. Every CPS term carries its `origin`, the `FactTable` is passed
through untouched, and `--verify-facts` reports survival.

---

## 6. `pear/a4/` — CPS to PON

**Input** CPS · **Output** PON · **Est.** ~3,000 LoC

| File | Purpose |
|---|---|
| `pon.c3` | The PON datatype: records, layouts, dispatch tables |
| `pon_print.c3` / `pon_parse.c3` | Textual form (D3) |
| `defunc.c3` | Defunctionalisation |
| `closconv.c3` | Closure conversion: env → explicit record |
| `layout.c3` | Field offsets, alignment, padding |

### Naming

**PON here means the post-defunctionalisation layout form, not the
front-end's AST notation.** `docs/README.md` currently uses "PON" for the
parse output. That collision is confusing and one of them must be renamed;
this document reserves PON for the layout form and the front-end usage should
become "the AST".

### Scope — narrower than it first appears

Pride has **no dynamic dispatch**: no `dyn`, no trait objects, no virtual
methods, and generics are monomorphised before PEAR sees anything. So the
C++-style vtable framing does not apply. What actually needs laying out:

1. **Closure environments** — the spec confirms *"closures (multi-arm with
   environment capture)"*. Each becomes a record of captured values.
2. **Handler frames** — `handle`/`resume` capture a continuation slice, which
   must become a concrete record with a resume point.
3. **Effect operation dispatch** — the one genuinely table-shaped construct:
   `perform E.op` selects an arm at runtime.

This is a smaller, sharper job than "objects", and scoping it honestly now
avoids discovering it at implementation time.

After this stage the program is **first-order**: no closures, no dynamic
dispatch, everything monomorphised. That is what makes `a5`'s analysis sound
and terminating.

---

## 7. `pear/a5/` — λ̄μμ̃ and emission

**Input** PON · **Output** X · **Est.** ~4,000 LoC

| File | Purpose |
|---|---|
| `lmm.c3` | λ̄μμ̃ terms: producer, consumer, command |
| `lmm_print.c3` / `lmm_parse.c3` | Textual form (D3) |
| `to_lmm.c3` | PON → λ̄μμ̃ |
| `dual_dce.c3` | The global dual-filtering DCE |
| `emit.c3` | λ̄μμ̃ → X |

### Why λ̄μμ̃ follows naturally from DB-CPS

Not merely aesthetic symmetry. **λ̄μμ̃ has exactly two binders**: `μ` binds a
continuation variable, `μ̃` binds a term variable. Double-barrelled CPS has
exactly two continuations. λ̄μμ̃ is the calculus DB-CPS lands in — steps 3 and
5 are the same idea at different degrees of explicitness, which is why the
chain coheres rather than being five arbitrary hops.

A command is `⟨producer ∥ consumer⟩`. DCE becomes dual filtering:

- a producer with no matching consumer is dead
- a consumer never activated is dead
- both sides of an unmatched pair go at once

Because `a4` made environments and dispatch explicit, this reaches *inside*
records: an unconsumed struct field is an unmatched producer and is deleted
before anything reaches the target.

### Honest framing

After `a4` the program is first-order, so a plain field-level reachability
analysis would find much of the same dead code. λ̄μμ̃'s advantages are that it
handles producers and consumers **uniformly** (one pass instead of separate
field-DCE, arg-DCE and return-DCE), and that CBV orientation (D4) makes the
result predictable.

**Therefore `dual_dce.c3` ships with a reachability baseline behind
`--dce-baseline`, and the report prints both counts.** If λ̄μμ̃ does not beat
the baseline it stays as a research result and the baseline does the work —
and either way the number is reported rather than assumed.

### D4 restated, because it is the sharpest edge here

Fix **μ̃ priority — call-by-value**. Pride is strict. The verifier rejects any
rewrite resolving the critical pair the other way.

### X

Undecided; the user will specify. The stage is structured so this is a
localised choice:

- **`.bc` via the LLVM C API** — `poc/llvm_bc_ffi.c3` already proves C3 →
  libLLVM-22 → real `.bc` (disassembles, runs, exits 42), and
  `poc/range_attr_proof.ll` proves `range(i64 0, 100)` makes `opt -O2` delete
  a whole branch. This is the channel `R` pays off through.
- **`.ll` text** — what `codegen.c3` does today across 9,718 lines. Emitted
  additionally for debugging via one extra call, never as the primary path.
- **something else** — λ̄μμ̃ commands may map directly, in which case the
  `getelementptr`/`load`/`store` framing does not apply.

Only `emit.c3` changes with X. Everything above it is unaffected.

---

## 8. Lessons taken from `ssi_ir.c3`

`ssi_ir.c3` is 7,290 working lines and its `r15`–`r56d` comment markers are a
record of bugs that cost real debugging. PEAR is designed so those classes
cannot recur.

| Marker | The bug | PEAR's structural answer |
|---|---|---|
| `r43`–`r46` | Field/index writes: address-of vs load mode, encoded in `.ival` as `1`, `-2`, `-3` | Distinct opcodes. Never a mode flag. (D2) |
| `r44` | φ slots reused across sibling loops; a stale counter corrupted the next loop | Loop context is a fresh arena allocation per loop; nothing is reused |
| `r54`–`r56` | Enum-variant and array→slice decay handled ad hoc at many sites | One explicit coercion node, inserted in `a1`, visible in the dump |
| `r56d` | Mutable module globals bolted on late, adding `IR_GLOAD`/`IR_GSTORE` | Globals are `M`-tracked memory from the start |
| — | 34 direct `ast::` references in `codegen.c3` | D5, enforced by CI grep |
| — | `.ival = 55555` magic sentinel | D2 |
| — | Dump exists, no reader | D3 |

**Kept, because they are right:** the structured single-pass CFG walk
(Brandis–Mössenböck, no dominance-frontier iteration needed since Pride has
no goto); the `verify()` invariant set; effect opcodes that stay
backend-agnostic so the runtime ABI is a late choice.

---

## 9. Build order

Not stage order. This sequence keeps something testable at every point.

1. **`a1/air.c3` + print + parse** — the datatype and its text form. Round-trip
   tests pass with no compiler attached.
2. **`a1/verify.c3`** — the four SSI properties, tested against hand-written
   `.air` files. Verification exists before anything can produce bad IR.
3. **`a1` build path** — `PNode` → AIR for a small language subset; grow by
   construct with a regression test each.
4. **`a2` facts + range** — `R` working, measured, `--verify-facts` reporting.
5. **`a2` memssa** — `M`.
6. **`a2` dce/sccp** — with before/after node counts.
7. **`a3` CPS** — datatype, text form, conversion, then dead-continuation DCE.
8. **`a4` PON** — defunctionalisation and layout.
9. **`a5` λ̄μμ̃** — plus the reachability baseline for honest comparison.
10. **`a5` emit** — once X is known.

Steps 1–2 are unblocked now and do not depend on X.

---

## 10. Testing

Mirrors `pfront_tests/run.sh`, which is at 61/61 and asserts behaviour rather
than counting lines.

| Kind | What it asserts |
|---|---|
| **Round-trip** | `parse(print(x)) == x` for AIR, CPS, PON, λ̄μμ̃ |
| **Verify** | every stage's output satisfies its own invariants |
| **Property** | e.g. σ count, φ count, semi-pruned split ratio |
| **Fact survival** | `a2` facts reaching emission — the `ERM` metric |
| **Optimisation** | minimum counts per pass, so a pass that silently stops firing fails |
| **Differential** | PEAR output vs legacy `codegen.c3` output, same program, same result |
| **Purity** | no pass ever deletes an effectful construct |

The last one is non-negotiable. `pfront`'s `44_opt_purity` asserts that
exactly one of two dead stores is removed — the pure one goes, the one
initialised by a call stays. PEAR needs the equivalent at every stage: an
optimiser that deletes I/O is the one unforgivable bug.

---

## 11. Honest risk assessment

1. **Fact survival across four conversions is the central risk.** D1 is the
   mitigation and `--verify-facts` is the measurement. If the number comes
   out low, `ERM` is decorative and the document should say so.
2. **λ̄μμ̃ may not beat plain reachability** on a first-order program. The
   baseline is built in so this is measurable, not assumed.
3. **Five IRs is a lot of surface.** Each boundary is a place facts drop and
   bugs hide. D3 (text at every stage) is what makes each boundary
   independently testable.
4. **`a4`'s scope depends on how much closure use real Pride code has.**
   Unmeasured so far. Worth counting before writing `closconv.c3`.
5. **X is unspecified**, which blocks only `a5/emit.c3`. Everything else
   proceeds.
6. **The legacy pipeline must stay green throughout** — conformance 261/262,
   exec 44/47. PEAR is additive until it can pass the same suite.

---

## 12. Decisions log

| # | Decision | Rationale |
|---|---|---|
| 1 | Drop **FG** | Redundant with SP by FGSA's own abstract; 7.7% average gain for an architectural rewrite |
| 2 | Drop **Infinitary** | Premise (Y-combinator recursion) false for Pride; SCC already handles loops |
| 3 | `a1` reads AST, not source | One grammar, one lexer; no divergence |
| 4 | **D1** origin threading | Without it `ERM` cannot survive to emission |
| 5 | **D2** no sentinel overloading | `r43`–`r46` cluster on exactly this in `ssi_ir.c3` |
| 6 | **D3** text form per stage | Independent testing; diffable optimisation |
| 7 | **D4** CBV / μ̃ priority | λ̄μμ̃ is non-confluent; wrong choice silently reorders effects |
| 8 | **D5** stage isolation | `codegen.c3`'s 34 `ast::` refs are why it cannot be reused |
| 9 | **D6** growable storage | Fixed caps truncate silently |
| 10 | SP = on-demand conversion | What the cited papers actually advocate; 15–24× measured |
| 11 | λ̄μμ̃ ships with a DCE baseline | So its value is measured, not assumed |
| 12 | PON = layout form, not AST | Resolve the name collision in `docs/README.md` |
| 13 | **IRDL splits across the boundary** | See below |

### Decision 13 — IRDL is split, not moved

IRDL currently lives entirely in `pfront/theory/theory_irdl.c3` (declaration +
lowering) and `theory_irdlverify.c3` (verification traits). It splits:

**Stays in `pfront` — the high-level half.** Dialect and opcode declarations,
registration, arity and sort checking, name resolution of dialect members.
These are grammar-and-scope concerns; they need the interner and the module
system, and they must report errors with source positions.

**Moves to `pear/a2/` — the low-level half.** The actual lowering of dialect
operations, plus the verification traits.

The reason is that `theory_irdlverify.c3` claims to check *"SSA form,
dominance, purity, termination"* — properties that only genuinely **exist**
once the program is in SSA with a real CFG. On the AST it can only
approximate them. In `a2` they are decidable, and a lowering rule can consult
range facts, alias information and reachability before choosing a form.

The same argument applies to two more `pfront` passes, and they should follow
IRDL once it works:

* **e-graph saturation** (`theory_egraph.c3`) — cost-based extraction is
  strictly better informed with dataflow facts available.
* **TRS rewriting** (`theory_trs.c3`) — a rewrite guarded on "this value is
  non-null" or "this index is in range" cannot be expressed on the AST.

Neither moves until IRDL has proven the pattern.

---

## 13. References

- Ananian, *The Static Single Information Form*, MIT 1999
- Boissinot et al., *Revisiting Out-of-SSA Translation*, CGO 2009 — strong vs weak SSI
- Tavares, Pereira, Bigonha, Bigonha, *Efficient SSI Conversion*, SBLP 2010 — on-demand conversion, the SP argument
- Tavares, Bigonha, Bigonha, Boissinot, Pereira, Rastello, *SSI Revisited*, 2012 — the parametrised framework subsuming SSA/SSI/e-SSA
- Bodík, Gupta, Sarkar, *ABCD: Eliminating Array Bounds Checks on Demand*, PLDI 2000 — e-SSA
- Choi, Cytron, Ferrante, *Effective Representation of Aliasing and Exceptions in SSA Form* — the `E`
- Rodrigues, Campos, Pereira, *A Fast and Low-Overhead Technique to Secure Programs Against Integer Overflows* / SBLP 2011 non-iterative range analysis — the `R`
- Briggs, Cooper, Harvey, Simpson, *Practical Improvements to the Construction and Destruction of SSA Form*, SP&E 1998 — semi-pruned
- Kelsey, *A Correspondence between Continuation Passing Style and Static Single Assignment Form*, 1995
- Curien, Herbelin, *The Duality of Computation*, ICFP 2000 — λ̄μμ̃
- Danvy, Filinski, *Abstracting Control*, LFP 1990 — shift/reset
- Ding, Earnest, Önder, *Future Gated Single Assignment Form*, CGO 2014 — **evaluated and rejected**, see decision 1
