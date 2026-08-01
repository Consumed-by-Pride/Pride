# SASI — Sparsely-Annotated Single Information (pipeline steps 1–2)

The vision (your 5-step pipeline):

```
[Frontend] → 1. SSI Tree (structural, nested scopes)
                 │  (SASI Extraction Pass)
                 ▼
             2. Populate SASI Fact Map with Path Info
                 │  (Flattening Pass)
                 ▼
             3. Strip tree → emit standard SSA CFG basic blocks
                 │  (Optimization Pass)
                 ▼
             4. Use SASI Map to delete redundant instructions
                 │  (Tear-down)
                 ▼
[Backend] →  5. Pure optimized SSA CFG → machine code
```

This document covers **steps 1–2** (done) and how step 3 falls out of step 2.

---

## Step 1 — clean & complete SSI tree (`ssi.c3`)

The SSI tree is a def-use graph over the AST with σ-refinements at branch edges
and φ-merges at joins. Step-1 hardening made the flow facts COMPLETE:

- **comparisons**: `if x < 0` → σ(`x<0`) true edge, σ(`x≥0`) false edge.
- **boolean variables**: `if flag` → σ(`flag==true`) / σ(`flag==false`).
- **negation**: `if !flag` / `¬flag` / `not flag` → polarity flipped.
- **conjunction**: `if a<10 && flag` → **both** facts on the true edge; nothing
  precise on the false edge (sound).
- **disjunction**: `if a||b` → both negations on the false edge (De Morgan);
  nothing precise on the true edge.
- **loop guards**: `while i<n` refines `i<n` inside the body.

A single shared analyzer, `collect_facts_pure(arena, cond, polarity, FactSet*)`,
produces the per-edge fact list. The SSI-tree builder and the CFG flattener both
call it, so they always agree. Each σ's `parent` points at the binder's prior
version → the dominating-σ chain.

## Steps 2+3 — SASI extraction = flatten-first, then sweep (`sasi.c3`)

Per the chosen design (flatten-first, e-SSA-style sparse map):

1. **Flatten with σ in-band** (`ssi_ir.c3`, already built): the SSI tree is
   lowered into an SSI-CFG. Every learned fact becomes a physical σ value,
   `%n.1 = σ(%n.0)  refined:(>0)`, emitted at the head of the edge-block. The
   flattener knows nothing about SASI — it just lowers structure.

2. **Sweep** (`SasiMap.extract`, three linear passes):
   - **harvest** — record every σ value into a `SasiFact`, indexed by SSA
     value-id (`by_value[id] → fact`). This is the sparse map: only σ values
     populate it.
   - **link_chains** — if a σ's source is itself a σ (has a fact), link it as the
     `parent` (the dominating refinement on the same binder); compute the
     ultimate non-σ `root`.
   - **strip** — rebuild each block's instruction list dropping σ. The σ IrVals
     stay alive in the module pool (downstream instructions still reference them
     as *abstract* handles), but no longer appear as physical block
     instructions. **Zero use-rewriting** — facts attach exactly where they hold.

After the sweep the block instruction lists are **σ-free** (φ + ordinary ops =
clean LLVM-shaped SSA), so **step 3 is achieved by the same pass** — there is no
separate flattening pass; the strip *is* the flattening to clean SSA.

### The fact

```
struct SasiFact {
    value;        // the σ value version (the map key)
    source;       // the σ's immediate operand (σ.args[0])
    root;         // ultimate non-σ root of the σ chain
    refinement;   // NODE_TYPE_REFINEMENT: op + bound (the predicate)
    parent;       // dominating fact on the SAME binder (or null) — the chain
    binder;       // source binder this version refines
    block;        // block the fact holds in
}
```

Path info is **minimal**: each fact stores its immediate predicate + a `parent`
pointer. A consumer crawls `parent` on demand to recover the conjunction of
dominating facts (e.g. `n>10 → n>0`), with no eager conjunction matrix.

### Queries (for step 4)
- `fact_of(v)` → the fact annotating `v`, or null (O(1) via `by_value`).
- `resolve(v)` → collapse a σ handle to its non-σ root (a SASI-unaware backend
  uses this to "see through" σ during teardown).

### Verification & sparseness invariant
`SasiMap.verify()` asserts the post-strip CFG holds **0 leftover σ** in any
block and **0 unresolved facts** (every fact resolves to a non-σ root). This is
checked on every compile and is the headline correctness property.

## Worked examples

`if n > 0 && flag` (multi-fact):
```
SASI: v6 {n}    := n > 0      [from v0, root v0, B1]
      v7 {flag} := flag==true [from v1, root v1, B1]
clean B1: v8 = const.int 1    (both σ gone)
```

Nested `if n>0 { if n>10 ... }` (dominating-σ chain):
```
v4 {n} := n > 0    [root v0, B1]
v7 {n} := n > 10   [from v4, root v0, B4]   parent v4   ← crawl v7→v4 for n>10 ∧ n>0
v9 {n} := n <= 10  [from v4, root v0, B5]   parent v4
```

## Driver
`--dump-sasi` prints the fact map + the cleaned (σ-free) CFG. Summary counters:
`sasi facts`, `sasi sigma swept`, `sasi sigma left` (must be 0),
`sasi unresolved` (must be 0). The pass runs unconditionally after IR
construction (`ir.verify()` runs first, while σ is still in-band, so the IR
verifier sees a well-formed SSI-CFG; SASI then strips to clean SSA).

## Test status
- **Red-team**: 100/100 (cases 95–100 added for SASI: multifact, chain, loop
  guard, bool/negation, disjunction, match).
- **Examples**: all 17 strip cleanly (0 leftover σ, 0 unresolved).
- **ASan**: 0 failures across 585 runs (files × 5 flags).
- **Mutation fuzz**: 3500 runs — 0 crashes, **0 sparseness-invariant violations**
  (leftover σ always 0).

## Next (step 4 — `sasi_opt.c3`)
Query `fact_of`/`parent` to fold redundant comparisons & branches and delete
dead instructions on the clean CFG, reporting deletions — the active goal.
