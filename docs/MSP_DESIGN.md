# Pryde MSP Stage — Architecture & Design

> The MSP (Meta-Staging / Program) stage is where Pryde stops being "a checked
> language" and becomes "a programmable compiler." It runs **after** the typed
> frontend (resolve → typecheck → effectcheck → lint) and **before** codegen.
>
> **MSP is untyped and unrestricted by design.** It rewrites the AST in place.
> The frontend already proved the program is well-formed; MSP is the foot-gun
> aisle — operated with mathematical precision.

This document breaks down every moving part so implementation is mechanical:

1. Pipeline position & the MSP driver
2. SSI — Static Single Information (the better-than-SSA form)
3. The term-rewriting engine (the highly-engineered, low-overhead core)
4. Pattern Generation Language (PGL) → decision trees
5. IRDL — dialect registration & lowering
6. Undefined Behavior in MSP
7. Staging: quote / splice / eval / comptime
8. Module & data-structure plan
9. Build order & test plan

Everything references the **real AST** (`ast.c3`): an `AstNode` has
`kind, id, line, col, type_annotation, effects, flags, child_count, children,
resolved, payload`, bump-allocated in a 64 MB `AstArena`.

---

## 1. Pipeline Position & the MSP Driver

```
... → Lint  →  ┌──────────────── MSP STAGE ───────────────┐  → ClangIR/LLVM
               │ 1. build SSI (sigma/phi → real def-use)   │
               │ 2. collect rules/pgen/irdl (declarations) │
               │ 3. run rewrite fixpoint over the AST      │
               │ 4. evaluate comptime / stage / eval       │
               │ 5. lower IRDL dialect ops to target ops   │
               │ 6. strip MSP-only nodes, verify, hand off │
               └───────────────────────────────────────────┘
```

### 1.1 New module: `msp.c3`

```
module msp;
import lexer; import ast;

struct MspContext {
    ast::AstArena* arena;       // same arena — rewrites allocate fresh nodes here
    RuleSet        rules;       // all rewrite rules collected from the program
    PgenSet        pgens;       // compiled PGL matchers
    DialectTable   dialects;    // IRDL dialects + lowering rules
    SsiGraph       ssi;         // def-use + refinements (built in step 1)
    Worklist       dirty;       // nodes needing (re)examination
    MspDiag[1024]  diags;       // MSP is untyped, but still reports failures
    int            diag_count;
    int            steps;       // global rewrite-step budget (fuel)
    bool           changed;     // fixpoint flag
}

fn void MspContext.run(MspContext* self, ast::AstNode* program);
```

### 1.2 Driver ordering (why this order)

- **SSI first** so rewrite rules can ask "what do we know about this value here?"
  (refinements/guards depend on flow facts).
- **Collect declarations** (`rewrite`, `rule`, `pgen`, `irdl`, `dialect`) before
  firing anything, so forward references work and rule sets compose.
- **Rewrite fixpoint** before comptime, so `comptime` blocks see simplified
  terms (e.g. `~Tree (1+2) |> arith*` folds before evaluation).
- **IRDL lowering last** among transforms — it produces target-specific nodes
  that should not be re-simplified by source-level rules.

### 1.3 Fuel & termination

MSP transformations can diverge (rewrite rules are Turing-complete). Every run
carries **fuel** (`steps`, default e.g. 2_000_000). Each rule application decrements
fuel; exhaustion is a hard MSP diagnostic ("rewrite did not reach a fixpoint —
possible non-terminating rule set"), never a crash. This is the MSP analogue of
the parser's recursion-depth guard.

---

## 2. SSI — Static Single Information

SSA (Static Single Assignment) gives each variable **one definition**. **SSI**
(Ananian's *Static Single Information* form) additionally splits a variable at
every point where the program *learns something new about it* — i.e. at branch
conditions. That is strictly more information than SSA, hence "the better
version of SSA."

### 2.1 The two node kinds (already emitted by the parser)

- **`NODE_PHI`** — a *merge*. At a control-flow join, `φ(x₁, x₂, …)` selects the
  value of `x` coming from whichever predecessor was taken. (Same as SSA.)
- **`NODE_SIGMA`** — a *split*. At a branch on a condition involving `x`, σ
  produces *distinct* names for `x` on each outgoing edge, each carrying the
  refinement that edge implies.

```
if x < 0.0            -- parser already inserts σ(x<0.0) here
  ub! "neg"           -- on the TRUE edge:  x : f64 ∩ (< 0.0)
sqrt(x)               -- on the FALSE edge: x : f64 ∩ (≥ 0.0)  ← φ merges back
```

### 2.2 What MSP builds from σ/φ

The parser plants σ/φ *markers*; MSP turns them into a real **def-use graph with
refinements**:

```
struct SsiVar {
    ast::AstNode* def;        // the defining node (let, param, σ, φ)
    ast::AstNode* refinement; // a type node: the extra fact on this version
    SsiVar*       parent;     // version this was split/merged from
    Use*          uses;       // linked list of use sites
}

struct SsiGraph {
    SsiVar*[]  vars;          // one per value-version
    // index: AstNode (an Ident use) -> SsiVar (which version it reads)
}
```

Build algorithm (single pass, dominator-light because Pryde blocks are already
tree-structured — no `goto`):

1. Walk the AST in source order maintaining a **scope→current-version** map.
2. At a `let`/param: create version v0.
3. At an assignment `x = e`: create version vₙ₊₁ (SSA renaming).
4. At a `σ(cond)` on edge E: create a refined version whose `refinement` is the
   type-predicate `cond` implies for that edge (`x<0` ⇒ `∩(<0)`, the negation on
   the other edge).
5. At a `φ` join: create a merge version; `refinement` = union of incoming
   refinements (the join in the subtyping lattice the typechecker already has).

Because Pryde has no arbitrary `goto`, the CFG is reducible and tree-shaped, so
SSI construction is **O(n)** with no iterative dominance-frontier computation.

### 2.3 Why MSP needs it

- **Rewrite guards** (`x / b, b ≠ 0 ↦ …`) consult SSI refinements to decide if
  `b ≠ 0` is *statically known* on this edge — enabling safe simplifications.
- **UB exploitation/preservation** (§6): `assume`/`ub!` install refinements; MSP
  may use them but must never invent UB beyond what they declare.
- **PGL conditions** (`where [i < len]`) are discharged against SSI facts.

SSI is consumed by MSP, then **lowered away** (σ/φ collapse to plain values plus
selects) before codegen.

### 2.4 Explicit CFG + SSI IR (`ssi_ir.c3`) — the backend-facing form

The tree-SSI above is coupled to the AST (a φ "knows" it is an `if`'s merge
because it lives at that node). A backend needs the dual: **basic blocks and
edges as first-class objects**. `ssi_ir.c3` lowers the structured AST into an
explicit CFG — `IrBlock`s with one terminator each (`ret`/`br`/`cbr`/`switch`/
`unreachable`), `IrVal` SSA values, φ-nodes tagged with predecessor *block ids*,
and σ-nodes emitted at the head of the edge-block where the fact holds.

Because Pryde has no `goto`, this is single-pass structured SSA construction
(Brandis & Mössenböck) + σ-splits (Ananian): one walk, no dominance frontiers.
It handles the hard cases for real — multi-clause functions become dispatch
cascades; `break`/`continue` add extra exit/header edges and the loop-φ /
exit-φ machinery reconciles them; early `return` routes dead code into
`unreachable` blocks. A built-in `verify()` checks terminator presence,
succ/pred symmetry, and φ-operand/predecessor agreement. See `SSI_IR_DESIGN.md`
for the full treatment. Status: **done, verified (0 errors on all examples +
red-team), ASan-clean, fuzzed.**

---

## 3. The Term-Rewriting Engine (low-overhead core)

This is the part the brief calls out: *"a highly engineered Term Rewriting system
for avoiding the typical overhead of Term Rewriting."* Naive rewriting is slow
for four reasons; we engineer each away.

| Naive overhead | Our technique |
|---|---|
| Re-traverses the **whole tree** every pass | **Worklist of dirty nodes** — only changed subterms + their parents are re-examined |
| Tries **every rule** at every node | **Discrimination-tree term index** — O(depth) lookup of *candidate* rules by top symbol |
| Rebuilds identical subterms repeatedly | **Hash-consing / interning** — structurally-equal terms share one node; rewrites are **memoized** |
| Re-matches a pattern from scratch | Rules are **pre-compiled to match programs** (instruction lists), left-linear fast path |

### 3.1 Rule representation

A `rewrite` block / `rule` compiles each `LHS ↦ RHS (, guard)?` into:

```
struct Rule {
    MatchProgram lhs;     // compiled matcher (see 3.3)
    ast::AstNode* rhs;    // template AST with pattern vars as holes
    ast::AstNode* guard;  // optional; evaluated against bindings + SSI
    int           top;    // top symbol key for the discrimination tree
    EffectMask    effects;// what RHS may introduce (for UB/effect safety)
    uint          prio;   // composition order (++ chains, source order)
}

struct RuleSet { Rule[] rules; DiscTree index; }
```

### 3.2 Discrimination tree (term indexing)

Instead of scanning all rules, we index them by the **shape of their LHS top**.
A discrimination tree is a trie keyed on a pre-order flattening of the pattern
(operators + arities; `*` for pattern variables). Lookup walks the subject term
once and yields only rules whose LHS *could* match — typically 1–3 candidates
instead of all N.

```
key("x + 0")   = [BINARY(+), VAR, LIT_INT(0)]
key("x * 2")   = [BINARY(*), VAR, LIT_INT(2)]
key("a / b")   = [BINARY(/), VAR, VAR]
```

Subject `n*2` → descend `[BINARY(*) → VAR → LIT_INT(2)]` → returns only the
strength-reduction rule. This is the single biggest constant-factor win.

### 3.3 Pattern matching = a compiled program

Each LHS becomes a small list of match instructions executed against a subject:

```
CHECK_KIND BINARY(*)        -- subject must be a multiply
BIND       v0   (child 0)   -- capture x
CHECK_LIT  child1 == 2      -- literal 2
COMMIT                      -- success; v0 bound
```

- **Left-linear** patterns (each var appears once) need no equality checks — the
  common, fast case.
- **Non-linear** patterns (`x - x ↦ 0`) emit a `CHECK_EQUAL v0 == v_other`,
  which uses hash-cons identity (pointer equality) — O(1).

### 3.4 Hash-consing + memoized rewriting

The AST arena gains an **intern table** (re-introducing the dedup the original
`asmh` had, but as an optional MSP-side index, not the whole IR model):

```
hashcons(node) -> canonical node   // structurally-equal subterms share identity
rewrite_memo : map<node, node>     // node -> its normal form
```

`normalize(t)`:
```
if t in rewrite_memo: return rewrite_memo[t]      -- already solved
t' = rewrite children first (bottom-up), hash-cons
loop:
    cand = index.lookup(t')                        -- candidate rules only
    fired = false
    for rule in cand (by prio):
        if rule.lhs.match(t', binds) and guard_ok(rule, binds, ssi):
            t' = instantiate(rule.rhs, binds)       -- build RHS, hash-consed
            spend_fuel(); fired = true; break
    if not fired: break
rewrite_memo[t] = t'
return t'
```

Because children are normalized first and memoized, and equal subterms are
shared, each distinct subterm is normalized **once**. Combined with the dirty
worklist, a second `|>` pass over an already-normal tree is nearly free.

### 3.5 Fixpoint (`expr |> rules*`) without re-traversal

`expr |> rules` = one normalization pass. `expr |> rules*` = run to fixpoint, but
fixpoint is reached when the **worklist drains**, not by comparing whole trees:

- A successful rewrite at node `t` marks `t`'s parent dirty (its child changed).
- Only dirty nodes are re-`normalize`d.
- Memo + hash-cons mean unchanged siblings are skipped instantly.

This turns the classic "rewrite until nothing changes = N full passes" into
"process a worklist," which is the engineered overhead win.

### 3.6 Composition (`++`) and rule algebra

`a ++ b` concatenates rule sets (priority preserved: `a`'s rules first). Because
rules are values, `++` is just `RuleSet` concatenation + a merged discrimination
tree. Confluence is **not** required (Pryde trusts you); determinism comes from
priority order. Optional `--check-confluence` can warn on overlapping LHSs.

### 3.7 Safety rails (untyped, but not reckless)

MSP is untyped, yet two invariants are preserved so rewriting can't silently
break the verified program:

- **Effect monotonicity**: a rule's RHS may not *introduce* an effect the LHS
  didn't have unless the rule is explicitly tagged `#unsafe_rewrite`. (Keeps the
  effect rows the frontend verified honest.)
- **UB conservation** (§6): rules may *remove* UB (optimize) but never *add* it.

---

## 4. PGL → Decision Trees

`pgen name<C> → [binds : Types] where [conds] ↦ action` generates a **matcher**,
not a single rule. Where rewriting transforms terms, PGL builds the matching
*infrastructure* — compiled to a **decision tree** (the standard maximal-sharing
pattern-match compilation, à la Maranget).

```
struct Pgen {
    Binding[]     binds;     // [x : T, n : Int] — typed holes
    ast::AstNode* pattern;   // the [ ... ] match shape (may be OR of shapes)
    ast::AstNode* where;     // conditions, discharged vs SSI facts
    ast::AstNode* action;    // RHS / emit_asm(...) / replacement term
}
```

Compilation:

1. Collect all PGL clauses sharing a domain into a **pattern matrix**.
2. Compile to a decision tree by repeatedly choosing the most-discriminating
   column (Maranget's heuristic) → minimal tests, maximal sharing.
3. Conditions (`where [i < len]`) become guard nodes consulting SSI.
4. The tree is emitted as ordinary AST (nested `match`/`if`) **or**, in backend
   PGL (`select_*`), as IRDL lowering actions.

This is how PGL does instruction selection: the decision tree picks the cheapest
target op for a given source pattern, sharing tests across opcodes.

---

## 5. IRDL — Dialect Registration & Lowering

```
struct Opcode  { name; arg_kinds[]; result_kind; }
struct Dialect { name; Opcode[] opcodes; Region[] regions; }
struct LowerRule { ast::AstNode* lhs_pattern; ast::AstNode* action; }
struct DialectTable { Dialect[] dialects; LowerRule[] lowerings; }
```

- `dialect D` blocks **register** opcodes/regions into `DialectTable`.
- `irdl` blocks register **lowering rules** (`D.op [binds] ↦ emit_asm(...)`),
  which are just rewrite rules whose LHS top symbol is a dialect opcode — so
  they ride the *same* discrimination-tree engine from §3, no separate matcher.
- Lowering runs as the **final** rewrite phase (its own priority band) so
  high-level simplification finishes before target-specific expansion.
- Validation: an opcode use must match its registered arity/kinds (MSP diag if
  not). Dialects compose; `node/edge/hyperedge/graph` declare the graph-IR
  shapes a dialect introduces.

**Status: DONE** (`irdl_msp.c3`). The `DialectTable` registers `dialect`
opcodes/regions and `irdl` lowering rules, validates every dialect-op USE
(unknown dialect/opcode and arity mismatches become MSP diagnostics), and lowers
uses by substituting the call's arguments into the matching rule's action — to a
fixpoint, so chained dialects (`Hi.hadd ↦ Lo.ladd ↦ +`) collapse in one pass.
Depth/fuel-guarded; red-teamed (cases 83–86) and ASan-fuzzed.

The payoff: IRDL, PGL backend selection, and term rewriting are **one engine**
with three front-doors, not three engines.

---

## 6. Undefined Behavior in MSP

UB is a first-class, *tracked* fact (the `EFFECT_UB` bit + `ub!`/`assume`/
`poison`/`freeze`/`unchecked` nodes the frontend already produces). MSP's job is
to **exploit declared UB for optimization without inventing new UB**.

- **`assume p`** installs an SSI refinement (`p` holds downstream). Rewrite
  guards may rely on it. If `p` is false at runtime → declared UB (your problem).
- **`ub! "msg"`** is typed `⊥`; any code dominated by it is dead. MSP may delete
  the dead path (it's unreachable) but must keep the `ub!` itself (it's a
  declaration, not an optimization artifact).
- **`unchecked e`** lets MSP drop bounds/overflow guard nodes *inside* `e` only.
- **`poison`** propagates: a rule producing poison taints uses; **`freeze`**
  stops propagation. These become LLVM `poison`/`freeze` at codegen.
- **Conservation invariant** (the rail from §3.7): for every rule,
  `effects(RHS) ⊆ effects(LHS) ∪ declared`. So a rewrite can simplify
  `x / 1 ↦ x` (removes nothing dangerous) but cannot rewrite a checked op into
  an unchecked one unless the source already declared `unchecked`/`UB`.

This is the "no hidden behavior" tenet enforced *through* the optimizer, not just
at the source.

---

## 7. Staging: quote / splice / eval / comptime

Modeled on MetaOCaml's three operators (the mental model you already have):

| MetaOCaml | Pryde | AST node | MSP action |
|---|---|---|---|
| bracket `.<e>.` | `~Tree e` / `quote e` | `NODE_SIGIL_TREE` / `NODE_QUOTE` | freeze `e` as data: stop normalizing inside |
| escape `.~e` | `splice e` / `unquote e` | `NODE_SPLICE`/`NODE_UNQUOTE` | run `e` now, graft its result into the surrounding quote |
| run `.!e` | `eval e` / `comptime` | `NODE_EVAL`/`NODE_COMPTIME` | evaluate the quoted AST at compile time |

- A **quotation level** counter tracks nesting. `splice` is only legal at level
  ≥ 1 and decrements it; an escape with no enclosing bracket is an MSP diag.
- `comptime` blocks are evaluated by a small **AST interpreter** (untyped: it
  walks literals/arith/calls to other comptime fns, folds, and returns a value
  node). Result replaces the block.
- `~Tree (1+2+3) |> arith*` works because the quote holds the *tree*, the
  pipeline applies §3's engine, and the result is spliced back.
- `reify` lifts a compile-time value to a runtime constant node; `runtime`
  forces a value out of comptime.

The interpreter is deliberately small and **untyped** — it can call arbitrary
comptime functions, exactly the "runs arbitrary commands as it wants" freedom.

**Status: DONE** (`stage.c3`). NB: this is COMPILE-TIME function evaluation
(CTFE), not a runtime interpreter — it runs *inside the compiler* and bakes
results back into the AST as literal nodes (exactly like C++ `constexpr`, Zig
`comptime`, Rust `const fn`). It does two things: (1) a quotation-LEVEL CHECK
(quote/~Tree/~Data/~Bytes/stage raise the level, splice/unquote lower it; an
escape at level 0 is a staging error), and (2) the CTFE evaluator — literals,
arithmetic, comparisons, short-circuit boolean, `if`, `let`, blocks, and calls
to single-clause comptime functions (with **lexical** scoping via a frame_base,
not dynamic). `comptime`/`eval` blocks are replaced by their value; `splice`s
inside a quote/stage are evaluated and grafted in. Recursion terminates via a
fuel + depth guard. Verified: `comptime fib(10) == 55`, lexical isolation
(`outer(5)` with a free var in the callee correctly does NOT fold). Red-teamed
(cases 78–82) and ASan-fuzzed.

---

## 8. Module & Data-Structure Plan

New files (mirrors the one-concern-per-module style):

```
ssi.c3        — SsiGraph, build_ssi(), refinement lattice (reuses typecheck subtyping)
rewrite.c3    — Rule, RuleSet, DiscTree, MatchProgram, hash-cons, normalize(), fixpoint
pgen.c3       — Pgen, decision-tree compiler (Maranget)
irdl_msp.c3   — DialectTable, opcode validation, lowering = rewrite rules
stage.c3      — quotation-level checker + comptime AST interpreter
msp.c3        — MspContext driver: orchestrates the above in the §1.2 order
```

AST additions (small, additive):
```
ast.c3:  + intern table on AstArena (hash-cons; opt-in, MSP only)
         + FLAG_QUOTED, FLAG_NORMAL (memo marker), FLAG_DIRTY (worklist)
         + node_intern(), node_equal() (structural)
```

Driver wiring in `pryde.c3`: after lint, `if (!strict_errors) msp.run(program)`,
then a final `--dump-msp` to print the rewritten tree.

---

## 9. Build Order & Test Plan (one piece at a time, red-teamed each)

1. **SSI** (`ssi.c3`) — build def-use + refinements; dump and verify on the
   `safe_sqrt` example; fuzz for cycles.
2. **Hash-cons + rewrite core** (`rewrite.c3`) — `arith`/`strength` rules,
   `|>` and `|>*`; verify `(n*8) |> strength` → `n<<3`; fuel/termination tests.
3. **Discrimination tree + worklist** — perf: confirm a no-op `|>*` pass is
   O(dirty), not O(n); benchmark vs a naive baseline.
4. **PGL** (`pgen.c3`) — decision-tree compilation; `elim_add_zero`,
   `mul_to_shift`; exhaustiveness of generated trees.
5. **IRDL** (`irdl_msp.c3`) — register a tiny `x86` dialect; lower
   `add_i32 ↦ emit_asm`; opcode-arity validation.
6. **Staging** (`stage.c3`) — quotation-level checker; comptime interpreter on
   `~Tree (1+2+3) |> arith*` → `6`.
7. **UB conservation** — property test: no rule run ever increases the effect
   mask of a node beyond declared.
8. **MSP driver** (`msp.c3`) + full red-team & ASan fuzz, same bar as the
   frontend (0 crashes, 0 memory errors).

Each step ships compiling, tested, and fuzzed before the next — no MVP, no
placeholders, consistent with how the frontend was built.
