# MSP Steps 5 & 6 — IRDL Lowering and Staging (CTFE)

This document covers the two modules that complete the MSP stage:
`irdl_msp.c3` (IRDL dialect registration + lowering) and `stage.c3` (staging:
quote / splice / eval / comptime, implemented as compile-time function
evaluation). Both are real, compiling, tested, red-teamed and ASan-fuzzed.

---

## A note on "staging interpreter" in a compiled language

Pride is AOT-compiled. The staging module does **not** interpret your program at
runtime. It is **CTFE — compile-time function evaluation**: a small evaluator
that runs *inside the compiler* during the MSP stage, reduces `comptime`/`eval`
expressions to values, and **bakes the result back into the AST as literal
nodes**. The compiled binary contains the *result* (`55`), never the evaluator.

This is exactly what every modern compiled language does:

| Language | Mechanism | Compile-time evaluator? |
|----------|-----------|--------------------------|
| C++      | `constexpr` / `consteval` | yes (the constant evaluator) |
| Zig      | `comptime` | yes |
| Rust     | `const fn` / `const` | yes (Miri-style const-eval) |
| **Pride**| `comptime` / `eval` / `quote` / `splice` | yes (`stage.c3`) |

So "a tiny interpreter in the compiler" is not a contradiction with "compiled
language" — it is the standard way compile-time metaprogramming is implemented.

---

## 1. IRDL — `irdl_msp.c3`

### 1.1 What it does
```
dialect GpuD                          -- REGISTER opcodes + regions
  opcode gadd : (i32, i32) -> i32     -- opcodes can carry a SIGNATURE
  opcode gmul : (i32, i32) -> i32
  region body                         -- regions can have NESTED bodies
    opcode binner : i32 -> i32        --   with their own opcodes

irdl                                  -- REGISTER lowering rules
  GpuD.gadd [a, b] ↦ a + b
  GpuD.gmul [a, b] ↦ a * b

fn f : (i32,i32) -> i32
  | (x, y) -> GpuD.gadd(GpuD.gmul(x, y), y)   -- a USE → lowered to (x*y)+y
```

### 1.2 Pipeline (three phases)
1. **register** — `scan_dialects` walks the program; `register_members`
   records every `dialect`'s `opcode`/`region`/`block`/`graph` into the
   `DialectTable`, **recursing into region/block/graph bodies** so nested
   opcodes register too. An opcode's `: (T0,T1) -> R` SIGNATURE is captured as
   per-parameter kinds + a result kind. `scan_lowerings` records every `irdl`
   rule (head path `Dialect.op`, binding list `[a,b]`, action template). A rule
   whose binding count disagrees with the opcode's signature arity is diagnosed.
   Duplicate opcodes / duplicate rules / unknown dialects / unknown opcodes too.
2. **validate** — `validate_uses` walks the program and, for every dialect-op
   USE (a `MethodCall` `D.op(args)` or `Call Field(D,op)(args)`), checks the
   dialect/opcode exist, the argument count matches the **signature** arity (or
   the rule's, if no signature), and — where an argument's kind is statically
   known (type annotation / bool / string literal) — that it matches the
   declared parameter kind (`check_arg_kinds`).
3. **lower** — `lower_node` post-order rewrites every use by `substitute`-ing the
   call arguments into the rule's action template, then re-lowers the result so
   **chained dialects collapse** (`Hi.hadd ↦ Lo.ladd ↦ +` in one pass).

### 1.3 Discrimination
A node is a dialect-op use only if its callee is a `Dialect.opcode` path whose
head is a `NODE_TYPEVAR` (dialect names are TypeVars). So ordinary method calls
(`x.abs()`) are never mistaken for dialect ops.

### 1.4 Safety
- `LOWER_FUEL` (100k) bounds total lowerings; `LOWER_MAX_DEPTH` (600) bounds the
  dialect chain; `WALK_MAX_DEPTH` (2000) guards all tree walks against deeply
  nested input. Overflow sets `too_deep`/`out_of_fuel`, never crashes.

---

## 2. Staging / CTFE — `stage.c3`

### 2.1 The operator trio (MetaOCaml model)
| role | Pride surface | AST node |
|------|---------------|----------|
| bracket (freeze code) | `~Tree e` / `quote e` / `~Data` / `~Bytes` | `NODE_SIGIL_*` / `NODE_QUOTE` |
| escape (inject value) | `splice e` / `unquote e` | `NODE_SPLICE` / `NODE_UNQUOTE` |
| run (evaluate now)    | `comptime …` / `eval e` | `NODE_COMPTIME` / `NODE_EVAL` |

A `stage` block is also a quotation context (it produces next-stage code), so
splices inside it are well-staged.

### 2.2 Phase A — level check (well-stagedness)
A quotation-level counter rises on quote/`~`-sigils/`stage` and falls on
splice/unquote. A splice/unquote at level 0 (no enclosing bracket) is a staging
**error**. This is the classic well-stagedness check.

### 2.3 Phase B — the CTFE evaluator
`eval` reduces a node to a value when possible, else returns the most-reduced
form (partial evaluation — it never hard-fails the build). It handles:
- literals; identifiers (looked up in the CTFE env);
- binary/unary arithmetic & comparison (via the AST constant folder, now
  **signedness-correct** — signed division/modulo/shift/comparison when either
  operand is signed), with **short-circuit** `&&`/`||`;
- `if` (evaluates the taken branch when the condition is statically known);
- `match` (selects the first arm whose pattern + guard match a known scrutinee);
- **mutable state**: `let mut` + assignment update bindings in place (`env_set`);
- **`while` and `for` loops** — iterated at compile time, bounded by a per-loop
  iteration cap and the global fuel; integer ranges (`for i in lo..hi`) drive
  for-loops, with inclusive `..=` honored;
- **control flow**: `return`/`break`/`continue` via a `flow` signal the loop and
  function-call handlers unwind on;
- **multi-clause comptime functions** — Prolog-style clause dispatch: the first
  clause whose parameter pattern (literal / ident / wildcard / or-pattern) and
  optional guard match the reduced arguments is selected and evaluated.

A `stuck` flag is raised whenever CTFE hits something it cannot decide (unknown
`if` condition, non-integer loop range, field/index store, non-exhaustive match,
fuel/iteration exhaustion). The wrapper `ctfe_eval` resets transient state per
evaluation and **accepts the result only if the fold was clean and produced a
value** — so a partially-reducible body is left as source, never mis-folded.

`comptime`/`eval` nodes are replaced by their computed value; `splice`s inside a
quote/stage are evaluated and grafted into the surrounding (still-quoted) code.

Worked examples (all verified): `fact(6)==720`, `classify(-3)==2` (wildcard arm
after the signedness fix), `sumto(100)==5050` (while), `forsum(10)==45` (for),
`early(10)==6` (return inside a for-loop), `sumdbl(5)==20` (loop calling another
comptime fn). A base-case-less `while` correctly hits `[OUT OF FUEL]` and is left
unfolded rather than hanging.

### 2.4 Lexical scoping (audited correctness fix)
A callee must see **only its own parameters**, never the caller's locals. This is
enforced with a `frame_base` index: on a call we raise `frame_base` above the
caller's bindings so `env_lookup` cannot reach them, then restore it on return.
Without this, CTFE had dynamic scoping (a bug): `inner` referencing a free `b`
would wrongly capture the caller's `b`. Now `outer(5)` with such a free variable
correctly does **not** fold, while `fib(10)` (whose recursion only uses its own
parameter) still folds to `55`.

### 2.5 Safety
- `EVAL_FUEL` (200k) bounds total reduction steps; `EVAL_MAX_DEPTH` (600) bounds
  eval recursion (so a non-terminating `comptime` like a base-case-less recursion
  stops cleanly with `[EVAL TOO DEEP]`); `WALK_MAX_DEPTH` (2000) guards the
  level-check / transform walks against deeply nested input.

---

## 3. Driver integration & ordering

In `pride.c3`, after the frontend (lint), the MSP stage runs in this order:

```
7a.  Staging (CTFE)      — fold comptime/eval, graft splices, level-check
7a'. IRDL lowering       — register, validate, lower dialect ops (final transform)
7b.  SSI (tree)          — built on the lowered/folded program
7b'. SSI-IR (CFG)        — explicit basic blocks + φ/σ
7c.  Rewrite (--rewrite)
7d.  PGL (--pgen)
```

Staging runs first so comptime results are baked in before analysis; IRDL
lowering is the last *transform* (per the design) so high-level code is settled
before target-ish expansion; SSI/IR are then built on the final tree.

Flags: `--stage` prints the CTFE report; `--irdl` prints the dialect report.
Both passes run unconditionally (they are real pipeline transforms); the flags
only control verbose output. Summary counters: `stage folded/errors`,
`irdl dialects/lowerings/errors`.

---

## 4. Test status
- **Examples**: all 17 clean (`stage errors = 0`, `irdl errors = 0`).
- **Red-team**: 94/94 pass; cases 78–82 (staging), 83–86 (IRDL basics),
  87–90 (deep CTFE: multi-clause / while / for+return / infinite-guard),
  91–94 (IRDL signatures: nested regions / arity / kind / rule-sig disagreement).
- **ASan**: 0 failures across 888 runs (all files × 8 flags).
- **Mutation fuzz**: 3500 runs across `--stage`/`--irdl`/`--dump-ir`, 0 crashes.
- **Correctness spot-checks**: `comptime fib(10)==55`, `fact(6)==720`,
  `classify(-3)==2`, `sumto(100)==5050`, `forsum(10)==45`, `early(10)==6`,
  `sumdbl(5)==20`; lexical isolation holds through nested calls/loops; chained
  dialect lowering collapses; signature arity + argument-kind + rule/signature
  disagreement diagnostics all fire; splice-outside-quote diagnosed.

## 5. Deepening done in this round (b & c)
- **(b) CTFE**: multi-clause dispatch (pattern + guard), `match`, `while`/`for`
  loops, `return`/`break`/`continue`, mutable `let mut` + assignment, plus a
  signedness fix to the shared AST folder (`ast::fold_binary`) so signed
  comparison/division/shift fold correctly (was a latent bug affecting the
  parser's folding too).
- **(c) IRDL**: opcode signatures `: (T..) -> R` with per-parameter kind capture,
  arity + argument-kind + rule/signature-disagreement validation, and
  region/block/graph bodies that nest further opcodes (registered recursively).
