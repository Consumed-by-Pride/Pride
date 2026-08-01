#!/usr/bin/env bash
# PEAR regression suite.
#
# Mirrors pfront_tests/run.sh: assert BEHAVIOUR, never line counts. Every
# assertion here was checked against a deliberately broken build to confirm
# it actually fails — an assertion that cannot fail is worse than no
# assertion, because it reads like coverage.
#
# Stages are added to this file as they are built. Today: a1.
set -u
cd "$(dirname "$0")/.." || exit 1

C3=${C3:-/tmp/c3/c3c}
BIN=./pear_a1_test

pass=0
fail=0

note() { printf '  %-6s %-34s %s\n' "$1" "$2" "$3"; }

# ── build ───────────────────────────────────────────────────────────────
if [ ! -x "$C3" ]; then
  echo "c3c not found at $C3 (set C3=/path/to/c3c)"
  exit 2
fi

if ! "$C3" compile pear/a1/*.c3 pfront/pfront_core.c3 -o "$BIN" >/tmp/pear_build.log 2>&1; then
  echo "BUILD FAILED"
  tail -20 /tmp/pear_build.log
  exit 2
fi
chmod +x "$BIN"   # workspace snapshots drop the exec bit

# ── a1 self-test: round-trip, verify, and the negative cases ────────────
#
# The self-test prints one PASS/FAIL line per assertion and exits non-zero
# on any failure. Parse its output rather than trusting the exit code alone,
# so a binary that dies early cannot look like a pass.
out=$("$BIN" 2>&1)
st_pass=$(echo "$out" | grep -c '^  PASS')
st_fail=$(echo "$out" | grep -c '^  FAIL')

if [ "$st_fail" = "0" ] && [ "$st_pass" -ge 20 ]; then
  pass=$((pass+1)); note PASS "a1_selftest" "($st_pass assertions, 0 failures)"
else
  fail=$((fail+1)); note FAIL "a1_selftest" "($st_pass pass, $st_fail fail)"
  echo "$out" | grep '^  FAIL' | sed 's/^/      /'
fi

# The self-test must actually be RUNNING the round-trip and the negative
# cases, not just printing passes. Assert both families are present.
rt=$(echo "$out" | grep -c 'round-trip')
neg=$(echo "$out" | grep -c 'reject:')
if [ "$rt" -ge 5 ] && [ "$neg" -ge 7 ]; then
  pass=$((pass+1)); note PASS "a1_coverage" "($rt round-trips, $neg rejection cases)"
else
  fail=$((fail+1)); note FAIL "a1_coverage" "round-trips=$rt (want>=5) rejections=$neg (want>=7)"
fi

# ── hand-written .air fixtures ──────────────────────────────────────────
#
# These are the reason D3 has a READER and not just a dumper: a stage can be
# tested against IR nobody's compiler produced. ok_* must verify clean,
# bad_* must be rejected.
for f in pear/a1/tests/ok_*.air; do
  [ -e "$f" ] || continue
  name=$(basename "$f" .air)
  if "$BIN" "$f" >/tmp/pear_fx.log 2>&1; then
    errs=$(grep 'errors / warnings' /tmp/pear_fx.log | grep -oE '[0-9]+ / [0-9]+' | cut -d' ' -f1)
    pass=$((pass+1)); note PASS "fixture_$name" "(parsed and verified, ${errs:-0} errors)"
  else
    fail=$((fail+1)); note FAIL "fixture_$name" "(should verify clean)"
    grep -E 'error|    - ' /tmp/pear_fx.log | sed 's/^/      /' | head -5
  fi
done

for f in pear/a1/tests/bad_*.air; do
  [ -e "$f" ] || continue
  name=$(basename "$f" .air)
  if "$BIN" "$f" >/tmp/pear_fx.log 2>&1; then
    fail=$((fail+1)); note FAIL "fixture_$name" "(malformed IR was ACCEPTED)"
  else
    why=$(grep '    - ' /tmp/pear_fx.log | head -1 | sed 's/^ *- //')
    pass=$((pass+1)); note PASS "fixture_$name" "(rejected: $why)"
  fi
done

# ── D3 property: the text form is CANONICAL ─────────────────────────────
#
# Printed ids are assigned in traversal order, not construction order, so
# print(parse(print(x))) is byte-identical to print(x). Without this, a loop
# header's phi and the body value it forward-references swap numbers on
# every reparse, and every optimiser diff is buried in renumbering noise.
# The self-test's loop fixture is the case that exercises it.
if echo "$out" | grep -q 'PASS  loop (round-trip'; then
  pass=$((pass+1)); note PASS "d3_canonical" "(loop with a forward reference round-trips)"
else
  fail=$((fail+1)); note FAIL "d3_canonical" "(forward-reference round-trip broken)"
fi

# ── D5 property: stage isolation, enforced by grep ──────────────────────
#
# PEAR.md D5: no stage after a1 may read a PNode. codegen.c3 has 285
# ssi_ir:: references AND 34 direct ast:: ones, and that coupling is exactly
# why it cannot be reused by swapping the IR underneath. Catch the first
# violation on the day it appears, not after four stages depend on it.
leak=""
for d in pear/a2 pear/a3 pear/a4 pear/a5; do
  [ -d "$d" ] || continue
  found=$(grep -l "pfront_core::PNode\|pfront_parse\|pfront_lex" "$d"/*.c3 2>/dev/null || true)
  [ -n "$found" ] && leak="$leak $found"
done
if [ -z "$leak" ]; then
  pass=$((pass+1)); note PASS "d5_isolation" "(no stage past a1 reads the AST)"
else
  fail=$((fail+1)); note FAIL "d5_isolation" "AST leaked into:$leak"
fi

# a1 itself is ALLOWED to read PNode — that is its job. But nothing in a1
# may read Pride SOURCE: there is one grammar and pfront owns it.
srcleak=$(grep -l "pfront_lex::Lexer" pear/a1/*.c3 2>/dev/null || true)
if [ -z "$srcleak" ]; then
  pass=$((pass+1)); note PASS "a1_no_lexer" "(a1 reads the AST, never source)"
else
  fail=$((fail+1)); note FAIL "a1_no_lexer" "a1 opened a lexer: $srcleak"
fi

echo "---"
echo "pear regression: pass=$pass fail=$fail"
[ "$fail" = "0" ] || exit 1
