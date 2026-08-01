# `pfront` — the Pride front end

A from-scratch front end for Pride, written in C3. **32,430 lines** across 34
modules: 17,197 in the core pipeline, 15,233 in the analysis layer.

---

## Why it exists

The legacy front end had **no module system**. `use` was lexed, parsed and
hoisted into the AST, but the compiler never opened a second file — it exited
0 and said nothing. The consequence: of a 257-module standard library,
**4 modules compiled, and all four were empty shells**.

Everything else followed from that. Showcase examples with `use pride.msp`
had parse errors hidden behind soft-warning exits. `parse_modal.c3` existed
but was never wired to the parser, so CMTT boxes could not be written in a
`.pie` file at all.

`pfront` fixes the root cause: a real loader with a load-once module cache,
exports collected before any resolution (so import order is irrelevant), and
identifiers interned at parse time so cross-module lookup is a `uint`
comparison rather than a `memcmp`.

**Result: 258 / 258 stdlib modules self-clean, from a baseline of 4** — and all
258 load into a single compilation unit with 0 errors in 164 ms.

---

## Build and test

```sh
/tmp/c3/c3c compile pfront/*.c3 pfront/theory/*.c3 -o pfrontc
chmod +x pfrontc                # snapshots drop the exec bit
bash pfront_tests/run.sh        # 100 pass / 0 fail
```

---

## Pipeline

```
source
  │
  ├─ pfront_lex      tokens, layout (INDENT/DEDENT), UTF-8 columns
  ├─ pfront_parse    PON AST; names interned here
  ├─ pfront_resolve  module loader + scope chain; fills .resolved
  │
  ├─ pfront_sema     visibility, patterns, const-eval, type cycles
  ├─ pfront_types    the type universe
  ├─ pfront_infer    unification, effect rows
  ├─ pfront_narrow   flow-sensitive facts (join = intersection)
  ├─ pfront_check    traits, coercions, overloads, access
  ├─ pfront_flow     call graph, recursion, reachability
  │
  ├─ theory/         ~24 analysis passes  → see THEORY.md
  │    …
  │    theory_live   CFG + liveness + semi-pruned classification
  │    theory_opt    THE OPTIMIZER: folding, algebraic, DCE, CSE
  │
  └─ pfront_dump     final AST (--emit-ast / --emit-sexp)
```

### Core modules

| Module | LoC | Responsibility |
|---|---:|---|
| `pfront_parse.c3` | 3,744 | recursive descent over the layout-sensitive grammar |
| `pfront_lex.c3` | 2,275 | tokens, indentation stack, contextual keywords |
| `pfront_resolve.c3` | 1,641 | module loader, scope chain, cross-module binding |
| `pfront_sema.c3` | 1,559 | visibility, pattern usefulness, const-eval, cycles |
| `pfront_check.c3` | 1,133 | traits, coercions, overload specificity, field access |
| `pfront_core.c3` | 1,034 | AST substrate, arena, interner, diagnostics |
| `pfront_ext.c3` | 978 | effects, lints, exhaustiveness, suggestions |
| `pfront_infer.c3` | 974 | Hindley–Milner-style unification |
| `pfront_narrow.c3` | 801 | flow-sensitive narrowing |
| `pfront_flow.c3` | 769 | call graph, recursion, intra-procedural flow |
| `pfront_types.c3` | 743 | the type universe |
| `pfront_main.c3` | 663 | driver, flags, pass sequencing |
| `pfront_source.c3` | 551 | source map, snippet rendering, carets |
| `pfront_dump.c3` | 332 | final-AST emitter |

---

## Driver flags

```
-I <dir>          add a module search root
--lint            surface type/mutability advice (OFF by default)
--strict-vis      enforce visibility
--dead-code       report unreachable functions

-O0 / --no-opt    disable the optimizer
-O1               constant folding + algebraic identities
-O2               + dead code elimination        [default]
-O3               + copy propagation + CSE

--emit-ast        print the FINAL (optimized) tree, annotated
--emit-sexp       same, as one S-expression per declaration (diffable)
--dump-ast        print the PARSE tree (pre-optimization)
--dump-cfg        print the last function's control-flow graph
--dump-mods       module load report
--time-passes     per-pass wall clock

--no-theory       skip the analysis layer
--no-verify       skip AST integrity checking
--context <n>     lines of source context in diagnostics
--plain           no colour
--quiet           one summary line only
```

Exit codes: `0` clean · `1` warnings · `2` errors.

---

## Design decisions that matter

**Pride is untyped.** No analysis may reject a program over types, arity,
mutability or bounds. Advice routes through `DiagBag.advisory`, is off by
default, and is never an error. See `THEORY.md` for the enforced policy.

**Interning at parse time.** Identifiers become `uint` in the lexer, so
resolution compares integers. This is what makes a 253-module sweep cheap.

**Chained arena slabs, never realloc'd.** 4 MB slabs, chained. Pointers into
the arena stay valid for the whole compilation; one `destroy` frees everything.

**64 KB stack-object limit.** C3 enforces this. `TypeTable`, `SccGraph`,
`CallGraph`, `AbstractState`, `Cfg`, `VarNumbering`, `UseMap` and `ValueTable`
are all heap-allocated for this reason.

**Permissive by default, strict opt-in.** Measured, not assumed: the stdlib
has 1,053 non-`pub` cross-module references. Hard-gating visibility would emit
thousands of false positives on real code.

**`tok_is_member_name()` centralises contextual keywords.** Six separate bug
classes (`os.linux.free(p)`, `fn free`, `JitMemory { region: … }`,
`meta.Metadata`, …) collapsed into one rule.

---

## Scale

Everything hot is an open-addressed hash table, not a linear scan. Two
O(n²) bottlenecks were found by instrumentation (`--time-passes`) and fixed:

| Site | Before | After |
|---|---:|---:|
| `Verifier.mark_seen` — visited set | 5,080 ms | **11 ms** |
| `UseMap` / `CopyMap` / `ValueTable` | linear | hashed |
| `AbstractState.find` | linear | direct-mapped cache |

Measured on a 60,604-node tree. Total front-end time on that input went
6,099 ms → 1,038 ms.

Current per-pass profile at 12,000 bindings (`--time-passes`):

```
absint 344ms (33%) · irdlverify 202ms · cmtt 180ms · bidi 179ms
stages 102ms · verifier 11ms · TOTAL 1,038ms
```

---

## Test suite

`pfront_tests/run.sh` — **84 assertions**, four kinds:

1. **`EXPECT`** — exact diagnostic count in the file's own source.
2. **`ADVISORY`** — asserts *both* halves of the untyped policy: zero errors
   even with every strict switch on, **and** ≥N warnings under `--lint`.
3. **`OPT_FIELD` / `OPT_MIN`** — a minimum for each optimizer statistic, so a
   pass that silently stops firing fails the suite. Node counts alone would
   not catch it, because another pass could mask the regression.
4. **Property assertions** — the purity interlock (exactly one of two dead
   stores removed), the CFG back edge, the semi-pruned split, and the full
   fold→flatten→unreachable cascade.

Then a **258-module stdlib sweep** reporting self-clean count, plus a
**megaload** assertion that loads every stdlib module into one compilation
unit — the configuration that exposes alias/module and local/module collisions
that are invisible file-by-file.
