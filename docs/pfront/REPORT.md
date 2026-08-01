# `pfront` — measured results

**Verified 2026-07-31** · c3c 0.8.1 · LLVM 22.1.8 · Debian 13 trixie x86-64

Every number here was produced by running the compiler. Nothing is estimated.

---

## Headline

| Metric | Value | Baseline |
|---|---:|---:|
| `pfront` regression suite | **61 / 61** | 43 at session start |
| stdlib self-clean | **119 / 253** | **4** before the rewrite |
| legacy conformance | **261 / 262** | unchanged (frozen) |
| front-end LoC | 32,440 across 34 modules | — |
| stale code deleted | **34,020 lines** | — |

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

## Optimizer, on the real stdlib (253 files)

```
useless exprs    : 115        dead stores      :  44
algebraic        :   9        const-fold arith :   1
branches folded  :   1        unreachable      :   0
blocks flattened :   0        files changed    :  35 / 253
nodes 125,481 -> 125,039      (442 removed, 0.3%)
```

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
3,788 functions analysed · 13,804 basic blocks · 0 capacity overflows
7,059 variables non-local (need a φ)
6,497 variables block-local (need none)
→ 47% of all variables need NO φ
```

That 47% is the semi-pruned payoff, measured rather than cited.

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

2. **119 / 253 stdlib modules, not 253.** The remaining 134 have real parse
   failures. One known layout case is documented and reproducible: a wrapped
   condition whose continuation line is indented to the same column as the
   body —

   ```pride
   if (a) ||
      (b)
     body
   ```

   The lexer realigns its indent stack so no INDENT is emitted for `body`.
   Four fixes were attempted and all reverted. Affects ~39 stdlib sites.

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
chmod +x pfrontc
bash pfront_tests/run.sh          # 61/61, then the 253-module sweep

# legacy, must stay green
bash build.sh
export PATH=/usr/lib/llvm-22/bin:$PATH
bash conformance/run.sh           # 261/262
```
