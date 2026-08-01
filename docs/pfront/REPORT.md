# `pfront` — measured results

**Verified 2026-08-01** · c3c 0.8.1 · LLVM 22.1.8 · Debian 13 trixie x86-64

Every number here was produced by running the compiler. Nothing is estimated.

---

## Headline

| Metric | Value | Baseline |
|---|---:|---:|
| `pfront` regression suite | **100 / 100** | 43 at session start |
| stdlib self-clean | **258 / 258** | **4** before the rewrite |
| megaload (all 258 modules, one unit) | **0 errors**, 164 ms | 432 errors |
| identifiers accounted for | **33,508 / 33,508 (100%)** | — |
| AST invariant violations | **0** across 258 files | — |
| legacy conformance | **261 / 262** | unchanged (frozen) |
| legacy exec tests | **44 / 47** | unchanged (frozen) |
| front-end LoC | 34,423 across 35 modules | — |
| stale code deleted | **34,020 lines** | — |

The megaload number is the one that matters. Several bugs were invisible
per-file and appeared only when every module was loaded into a single
compilation unit — a file that is clean alone but breaks in a large graph is
the hardest kind to place, so that configuration is now a permanent
regression assertion rather than an occasional manual check.

---

## The flattering and the unflattering, side by side

**Flattering:** the optimizer removes **96%** of nodes from a 12,000-binding
generated file, and **50–61%** from the regression cases.

**Unflattering:** it removes **0.3%** from the real standard library —
442 nodes of 125,481, touching only 35 of 253 files.

Both are true. The reason for the gap is that stdlib code is mostly
declarations, and the partial evaluator already folds static arithmetic before
the optimizer runs. The optimizer earns its place on code with *dynamic*
values, which is what a real program body is, and what the stdlib's
declaration-heavy modules are not.

---

## Optimizer, on the real stdlib (258 files)

```
useless exprs    :   5        dead stores      :  28
algebraic        :   8        branches folded  :   1
unreachable      :   0        loops removed    :   0
blocks flattened :   0        files changed    :  18 / 258
nodes 127,268 -> 127,070      (198 removed, 0.16%)
```

Note this is *lower* than the 442 nodes (0.3%) reported previously, over
*more* files. Nothing regressed: the earlier sweep ran before several parser
fixes, and code that had been silently mis-parsed (whole functions reparented
into their predecessors — see the hanging-indent bug) is now shaped correctly,
which leaves the optimizer less accidental debris to remove. A smaller number
here is the honest consequence of a more correct parse.

`blocks flattened : 0` is honest: that pass needs a folded branch to expose a
spliceable block, and stdlib code has none. It is exercised by the regression
suite, so it is tested, but its real-world value is **unproven**.

## Optimizer, on code with dynamic values

| Case | Before | After | Removed |
|---|---:|---:|---:|
| `42_opt_algebraic` — `n*1`, `+0`, `b-b`, `n*0` | 28 | 14 | **50%** |
| `48_opt_cascade` — fold → flatten → unreachable | 16 | 7 | **56%** |
| `43_opt_dce` — statements after `return` | 18 | 7 | **61%** |
| 12,000 generated bindings | 60,598 | 2,078 | **96%** |

---

## Semi-pruned liveness, on the real stdlib

```
14,340 basic blocks analysed · 0 capacity overflows
 5,967 variables non-local (need a φ)
 6,714 variables block-local (need none)
→ 53% of all variables need NO φ
```

That 53% is the semi-pruned payoff, measured rather than cited.

The classification is asserted in both directions, because a pass that put
everything in one bucket would still "run":

| Input | non-local | block-local | dataflow iterations |
|---|---:|---:|---:|
| loop carrying `acc`, `i` | 3 | 1 | 3 |
| straight-line `a → b → c` | 0 | 4 | 1 |

---

## Scale: two O(n²) bugs found and fixed

Found with `--time-passes`, not by guessing. The first attempt at fixing the
optimizer's hash maps produced **no measurable improvement** — instrumenting
showed the real cost was somewhere else entirely.

| Site | Before | After | Speedup |
|---|---:|---:|---:|
| `Verifier.mark_seen` visited set | 5,080 ms | **11 ms** | **462×** |
| total front end, 60k-node tree | 6,099 ms | 1,038 ms | 5.9× |

Also converted to hash tables: `UseMap`, `CopyMap`, `ValueTable`,
`VarNumbering`. `AbstractState.find` got a direct-mapped cache instead — a
full table would have made the by-value state copy at every CFG join more
expensive than the scan it replaced.

Per-pass profile at 12,000 bindings after the fix:

```
absint 344ms (33%) · irdlverify 202ms · cmtt 180ms · bidi 179ms
stages 102ms · verifier 11ms · TOTAL 1,038ms
```

`absint` is now the top cost. It is a fixpoint with widening over three
domains, so it is *expected* to be the most expensive pass; it has not been
optimized further.

---

## Correctness bugs found and fixed this session

### 1. Parent links broken by every rewriting pass

Six sites across four modules did `n.children[i] = replacement` directly,
leaving `replacement.parent` pointing at the old location or at null. On a
12,000-binding file the verifier reported **12,000 broken parent links**.

Fixed at the root with `PNode.set_child`, which every in-place replacement now
funnels through. Result: **"all 8 invariants hold"**.

### 2. Thirteen spurious "declaration set changed" warnings

The transform verifier treated *any* drop in declaration count as suspicious.
That predates the optimizer — dead-store elimination removes `let`
declarations by design.

Fixed precisely rather than by relaxing the check: the optimizer now reports
how many declarations it deleted, and the verifier flags only an *unexplained*
loss. Losing a **function** is still always an error.

```
before: WARNING : a theory pass changed the declaration set
after : decl removals : 2, all accounted for by dead-code elimination
```

### 3. `build.sh` silently building a broken compiler

The legacy build piped `c3c` output through `grep … || true`, so a compile
failure exited 0 and printed `Built:` over a stale binary. Three modules
(`modal.c3`, `msp.c3`, `parse_modal.c3`) had been missing from the source list
and nothing noticed.

Fixed: the build now checks for errors and fails loudly. It compiles clean.

---

## The purity interlock

The single most important correctness property of the DCE pass, and the one
worth reviewing.

`is_pure` answers *"definitely no side effects"*. Calls, assignments,
`perform`, asm, syscall, atomics, volatile, alloc/free and deref all answer
**false** and are never removed. Getting this backwards would delete the
user's I/O.

Asserted by `44_opt_purity`, which requires **exactly one** of two dead stores
to be removed:

```pride
let dead_but_impure = sink(n)   -- KEPT: sink() may do anything
let dead_and_pure   = n + 1i64  -- REMOVED
```

A second test writes six assignments and two array stores and asserts **zero**
deletions.

---

## What is not done

1. **Downstream migration not started.** `ssi_ir.c3`, `typecheck.c3` and
   `codegen.c3` still consume the legacy `ast::AstNode`, not
   `pfront_core::PNode`. This is the next major piece of work.

2. **~~119 / 253 stdlib modules~~ — now 258 / 258.** The wrapped-condition
   layout case referred to here is fixed, as is the deeper defect behind it:
   the lexer's hanging-indent realign *overwrote* an enclosing indent level
   instead of pushing a new one, destroying live blocks so their closing
   DEDENT was never emitted. Two wrapped `else if` links were enough to walk
   the indent stack down to index 0 and clobber the file level, after which
   the next top-level function was parsed **inside** its predecessor with
   **zero diagnostics**. That silence is why an error-count test could not
   catch it, and why the regression assertions here are structural (AST depth,
   top-level declaration counts, binder identity) rather than count-based.

3. **Liveness is intra-procedural.** A store to a variable captured by a
   closure or reachable through a pointer is conservatively kept.

4. **CSE reports, it does not rewrite.** Introducing a temporary needs a scope
   to hold it — that is the middle end's job.

5. **`--strict-types` is now nearly inert.** Since Pride is untyped, almost
   everything it used to gate is an advisory. It should probably be removed or
   made an alias for `--lint`.

---

## Reproducing

```sh
/tmp/c3/c3c compile pfront/*.c3 pfront/theory/*.c3 -o pfrontc
chmod +x pfrontc                  # workspace snapshots drop the exec bit
bash pfront_tests/run.sh          # 100/100, then the 258-module sweep
bash experiments/run.sh           # 14/14

# legacy, must stay green
export PATH=/usr/lib/llvm-22/bin:$PATH
bash build.sh
bash conformance/run.sh           # 261/262
bash tests/run_exec.sh            # 44/47
```

`pfront_tests/run.sh` builds the megaload file itself, so the whole-graph
check runs on every invocation — it is not a separate manual step.
