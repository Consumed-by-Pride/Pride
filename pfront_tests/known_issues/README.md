# Known issues — reproducers kept OUT of the pass/fail suites

These files are real defects that are **not fixed**. They live here, not
in `fuzz/`, because the fuzz corpus asserts "nothing crashes" and these
do crash — putting them there would either turn the suite permanently red
or force the assertion to be weakened, and a weakened assertion is worse
than an acknowledged gap.

Each one must be removed from this directory the day it is fixed.

## `pgen_memory.pie` / `pgen_memory_min.pie`

A `pgen` block containing a wildcard pattern allocates far more memory
than the input justifies:

| input | peak RSS |
|---|---|
| trivial file, theory ON | 2.8 MB |
| all of `stdlib/io.pie` | 24 MB |
| `pgen_memory_min.pie` (4 lines) | 77 MB |
| `pgen_memory.pie` (2 KB, fuzzed) | ~1.4 GB, then OOM-killed |

**Investigated and ruled out**, so the next attempt does not repeat it:

* not the AST arena — instrumented, exactly **1 slab** in every case,
  including the 1.4 GB one;
* not `PgMatrix` — 70 KB each and freed on every path, including the
  error paths;
* not recursion in `PgenCompiler.compile` — instrumented, exactly **one**
  call, at depth 0, with 4 rows, and the memory goes before it returns;
* not the theory pipeline's fixed structures — 23 MB in total
  (`PgenCompiler` 13.1 MB, `HashCons` 6.5 MB), allocated for every
  compile including the 2.8 MB trivial one.

The allocation happens between entering the all-wildcards branch of
`compile` and leaving it. That is as far as it was narrowed.

It is a denial-of-service on hostile input, not a miscompile: no real
module is affected, and `pfront_tests/run.sh` pins the ceiling with
`resource_ceiling` so a regression on REAL code is caught.
