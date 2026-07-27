# Silent CTFE/IRDL table-overflow gap (stage.c3 + irdl_msp.c3)

## Symptom
Both the compile-time evaluator (`stage.c3`'s `Stager`) and the IR-dialect
lowering table (`irdl_msp.c3`'s `DialectTable`) track a capacity-overflow
condition:

- `Stager.overflow` — set when the 4096-entry CTFE environment stack
  (`env_push`) or the 4096-entry compile-time-function table overflows.
- `DialectTable.overflow` — set when the dialect/opcode/region tables
  overflow (`register_lowering`, opcode registration, region registration).

Both flags were correctly *set* in every overflow path, but neither was ever
*read* anywhere else in the codebase. `pride.c3`'s `--dump-stage` and
`--dump-irdl` opt-in diagnostic dumps (`dump_stage_report` /
`dump_irdl_report`) already report the sibling conditions `out_of_fuel` and
`too_deep`, but silently omitted `overflow` — so a program that tripped
either table cap would have some of its compile-time bindings, compile-time
functions, dialects, opcodes, or lowering regions silently dropped with
*zero* diagnostic output, even under the most verbose opt-in reporting flags.

## Why this matters
Both `stage.c3` and `irdl_msp.c3` are explicitly designed as "soft: partial
evaluation, not a hard error" subsystems (per their own header comments) —
correctly degrading to "leave as source" / "leave lowering unresolved"
rather than crashing or miscompiling when they get stuck or run out of
capacity. That soft-degradation design is sound. But a design that
*silently* drops data with no way to observe it even in verbose/debug mode
undermines the project's broader "no hidden behavior" philosophy (the same
principle motivating the effect-checker's exhaustive effect tracking, and
the lint pass's unreachable-code detection). A user hitting one of these
caps deserves at least an opt-in visible signal, the same as `out_of_fuel`
and `too_deep` already provide.

## Fix
Added the missing report lines to both diagnostic dumps in `pride.c3`,
mirroring the exact style of the adjacent `out_of_fuel`/`too_deep` lines:

```c3
// dump_stage_report()
if (st.overflow) printf("  [CTFE ENV/FN TABLE OVERFLOW — some bindings or comptime fns were dropped]\n");

// dump_irdl_report()
if (dt.overflow) printf("  [IRDL TABLE OVERFLOW — some dialects/opcodes/regions were dropped]\n");
```

## Verification
- Confirmed `bool overflow;` is a real field on both `stage::Stager`
  (`stage.c3:98`) and `irdl_msp::DialectTable` (`irdl_msp.c3:127`), and that
  `dump_stage_report(stage::Stager* st)` / `dump_irdl_report(irdl_msp::DialectTable* dt)`
  use the matching parameter names (`st.overflow` / `dt.overflow`) — no
  naming mismatch.
- Confirmed via `git show HEAD:<file> | grep -o '{' | wc -l` vs. the same for
  `}` that the brace-balance delta introduced by this change is 0/0 (single
  `if (...) printf(...);` statements, no new blocks) for both `pride.c3`
  edits, alongside the identical check for every other file touched this
  session (all deltas matched exactly — see `git diff --stat` for the full
  file list).
- Not independently compile-verified (the `c3c` compiler itself remains
  unbuildable in this sandbox — see `finds.md` §7 and `CORRECTIONS.md` for
  the full explanation of that limitation), but the change is a single
  conditional `printf` statement using pre-existing, already-referenced
  struct fields and an already-established code pattern, so the risk
  profile is minimal.
