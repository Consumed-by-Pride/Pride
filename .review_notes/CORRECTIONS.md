# Major correction to earlier review pass

## conformance/run.sh referenced a nonexistent binary — ALL "38 failing tests" from
## the initial review were a harness bug, not compiler bugs

`conformance/run.sh` had `BIN=../pride` hardcoded, but the actual built
compiler binary in this repository is `pryde` (`./pryde`, not `./pride` —
this is the same Pryde/Pride rename residue seen elsewhere, e.g. the
`name_is_runtime_decl` "pryd" byte-check bug in codegen.c3). Running the
suite as shipped therefore executed `../pride` (a file that does not exist),
so `$out` was always empty/an error message for every single case, and the
harness's own EXPECT-matching logic just happened to occasionally match
"empty output contains 0 diagnostics" as correct for EXPECT-CLEAN cases
(hence 204/242 "passed") while failing every case that expected an actual
diagnostic string in the output. This was NOT a compiler defect — it fully
explains the discrepancy between the checklist's claimed "242/242 PASS" and
my initial "204/242" measurement.

**FIX APPLIED**: `conformance/run.sh` line `BIN=../pride` → `BIN=../pryde`.

After the fix, re-running against the (stale, pre-existing) `./pryde` binary:
`conformance pass=241 fail=1`. The one remaining failure
(`47_class_guidance.pie`) expects the parser's guidance message to say
"Pride has no `class`" but the STALE BINARY still emits the pre-rename text
"Pryde has no `class`" — and I confirmmed via reading `parser.c3` that the
CURRENT SOURCE already says "Pride" (line ~460), so this failure is fully
explained by binary staleness too, not a live source bug. Once the project
is rebuilt with a working `c3c` toolchain (unavailable in this sandbox — see
toolchain note in lexer.md), conformance should read 242/242 exactly as
claimed.

This correction supersedes the "conformance 204/242" figure from the initial
review response and confirms the checklist's "242/242 PASS" claim is (very
likely) accurate for current source, once rebuilt.
