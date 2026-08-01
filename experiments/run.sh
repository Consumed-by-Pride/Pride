#!/usr/bin/env bash
# experiments/run.sh — compile every experiment and stdlib demo through pfront.
#
# These are not pass/fail regression tests. They are STRESS INPUTS: each one
# deliberately drives a subsystem into a corner and prints what that subsystem
# reported, so a capability change shows up as a diff in the numbers.
#
# Two files END IN ERRORS ON PURPOSE and are marked below. Everything else must
# compile clean.
set -u
cd "$(dirname "$0")/.." || exit 1
BIN=./pfrontc
[ -x "$BIN" ] || { echo "build ./pfrontc first"; exit 2; }

# Files whose whole point is to trigger a diagnostic.
declare -A EXPECT_ERRORS=(
  [test_scoped_effects]=1   # E3220: bracket resumed twice (linearity)
  # Was 9. Those 9 were E3202 on `~Tree (x + 1)` over outer locals — which
  # spec §18 documents as the NORMAL use of the sigil ("let node = ~Tree
  # (x + y * z)"). The reification sigils share the N_EXPR_QUOTE node kind
  # with `quote`/`stage` but do not defer evaluation, so treating them as a
  # stage bump was a false positive. Fixed in theory_msp.c3 and
  # theory_cmtt.c3; genuine escapes through `stage`/`quote` still fire, and
  # pfront_tests asserts that separately (stage_escape_kept).
  [test_msp_cmtt]=0
  [test_irdl_trs]=0
)

fail=0

echo "══ experiments ══════════════════════════════════════════════════════"
for f in experiments/*.pie; do
  name=$(basename "$f" .pie)
  got=$("$BIN" "$f" -I stdlib -I . --plain 2>&1 | grep -c "^  $f:.*error")
  want=${EXPECT_ERRORS[$name]:-0}
  if [ "$got" = "$want" ]; then
    if [ "$want" = "0" ]; then
      printf '  ok    %-28s clean\n' "$name"
    else
      printf '  ok    %-28s %s expected diagnostic(s)\n' "$name" "$got"
    fi
  else
    printf '  FAIL  %-28s expected %s errors, got %s\n' "$name" "$want" "$got"
    fail=$((fail+1))
  fi
done

echo
echo "══ stdlib demos ═════════════════════════════════════════════════════"
for f in experiments/stdlib_demos/*.pie; do
  name=$(basename "$f" .pie)
  got=$("$BIN" "$f" -I stdlib -I . --plain 2>&1 | grep -c "^  $f:.*error")
  mods=$("$BIN" "$f" -I stdlib -I . --quiet 2>&1 | grep -oE 'modules=[0-9]+' | grep -oE '[0-9]+')
  if [ "$got" = "0" ]; then
    printf '  ok    %-28s clean (%s modules loaded)\n' "$name" "${mods:-?}"
  else
    printf '  FAIL  %-28s %s errors\n' "$name" "$got"
    fail=$((fail+1))
  fi
done

echo
echo "══ stdlib coverage ══════════════════════════════════════════════════"
# The demos exist to prove the stdlib is USABLE from Pride, which is the
# metric the whole pfront rewrite was justified by (4/257 -> 224/257).
# Module-load depth is the honest proxy: a demo that loads 58 modules has
# exercised a real dependency graph, not a leaf.
total_mods=0
for f in experiments/stdlib_demos/*.pie; do
  m=$("$BIN" "$f" -I stdlib -I . --quiet 2>&1 | grep -oE 'modules=[0-9]+' | grep -oE '[0-9]+')
  total_mods=$((total_mods + ${m:-0}))
done
printf '  %-28s %s module-loads across %s demos\n' "total" "$total_mods" \
       "$(ls experiments/stdlib_demos/*.pie | wc -l)"

echo
echo "══ what each experiment exercised ═══════════════════════════════════"
probe() {  # probe <file> <grep-pattern> <label>
  local line
  line=$("$BIN" "experiments/$1.pie" -I stdlib -I . --plain 2>&1 | grep -m1 "$2")
  [ -n "$line" ] && printf '  %-22s %s\n' "$3" "$(echo "$line" | sed 's/^ *//')"
}
probe test_semantic_subtyping "type algebra"     "subtyping"
probe test_semantic_subtyping "dnf  "            ""
probe test_scoped_effects     "handlers  "       "effects"
probe test_scoped_effects     "effect misuse"    ""
probe test_msp_cmtt           "cmtt judgments"   "staging"
probe test_msp_cmtt           "stage soundness"  ""
probe test_explicit_ub        "explicit UB"      "UB"
probe test_explicit_ub        "dead code"        ""
probe test_irdl_trs           "rewrite rules"    "TRS"
probe test_irdl_trs           "fuel  "           ""

echo
echo "---"
if [ "$fail" -eq 0 ]; then
  echo "experiments: all $(ls experiments/*.pie experiments/stdlib_demos/*.pie | wc -l) files behaved as expected"
else
  echo "experiments: $fail file(s) deviated"
  exit 1
fi
