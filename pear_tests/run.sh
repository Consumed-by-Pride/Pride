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

if ! bash pear/build.sh >/tmp/pear_build.log 2>&1; then
  echo "BUILD FAILED"
  tail -20 /tmp/pear_build.log
  exit 2
fi
PEARC=./pearc

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

# ── ERM: the facts that make .air denser than .ll ───────────────────────
#
# The claim is measurable, so measure it. ok_erm_density.air is the same
# program as /tmp/ck/cov.ll; LLVM 22 -O2 annotates 0 of its internal SSA
# values with a range (it infers nuw/nsw and discards the bounds that
# justified them). a1 must record one on every derived value.
den=$("$BIN" pear/a1/tests/ok_erm_density.air 2>&1)
ranged=$(echo "$den" | grep -oE 'R: ranged        : [0-9]+' | grep -oE '[0-9]+$')
if [ "${ranged:-0}" -ge 5 ]; then
  pass=$((pass+1)); note PASS "erm_R_density" "($ranged ranged values; llvm .ll carries 0)"
else
  fail=$((fail+1)); note FAIL "erm_R_density" "only $ranged ranged values, want >=5"
fi

# M: memory versioning must appear IN THE TEXT. LLVM's MemorySSA is an
# analysis that cannot be serialised to .ll at all, so there is no
# equivalent line to compare against — this is a capability gap, not just
# a density one.
memdef=$(echo "$den" | grep -c 'mem=def:')
memuse=$(echo "$den" | grep -c 'mem=use:')
if [ "$memdef" -ge 1 ] && [ "$memuse" -ge 1 ]; then
  pass=$((pass+1)); note PASS "erm_M_serialised" "($memdef mem defs, $memuse mem uses in the text)"
else
  fail=$((fail+1)); note FAIL "erm_M_serialised" "defs=$memdef uses=$memuse, want >=1 each"
fi

# E: a pi node must carry its refinement and narrow the range. This is the
# construct .ll has no equivalent for — a faulting op there is an ordinary
# instruction, so "already checked" is a property of a program POINT that
# every consumer re-derives, not of a NAME that travels with the value.
bnd=$("$BIN" pear/a1/tests/ok_erm_bounds.air 2>&1)
if echo "$bnd" | grep -q 'pi %4 %6 fact=inbounds  \[range=0\.\.15\]'; then
  pass=$((pass+1)); note PASS "erm_E_pi" "(pi carries inbounds and narrows to 0..15)"
else
  fail=$((fail+1)); note FAIL "erm_E_pi" "pi lost its refinement"
  echo "$bnd" | grep 'pi ' | sed 's/^/      /'
fi

# The payoff: R must PROVE the bounds check redundant. `%6` is `(i & 15) <
# 16`, always true, so the trap block is dead. If this stops firing, R has
# regressed to decoration.
dec=$(echo "$bnd" | grep -oE 'decided cmps  : [0-9]+' | grep -oE '[0-9]+$')
if [ "${dec:-0}" -ge 1 ]; then
  pass=$((pass+1)); note PASS "erm_R_decides" "($dec comparison(s) settled by range alone)"
else
  fail=$((fail+1)); note FAIL "erm_R_decides" "R settled no comparisons"
fi

# e-SSI: a sigma must narrow DIFFERENTLY on each edge. Both sigmas over the
# same value carrying the same range would mean the split distinguishes
# nothing, which is the failure mode that makes e-SSI pointless.
dia=$("$BIN" pear/a1/tests/ok_diamond.air 2>&1)
gt=$(echo "$dia" | grep 'fact=gt' | grep -c 'range=1\.\.')
le=$(echo "$dia" | grep 'fact=le' | grep -c 'range=-9223372036854775808\.\.0')
if [ "$gt" -ge 1 ] && [ "$le" -ge 1 ]; then
  pass=$((pass+1)); note PASS "essi_sigma_narrows" "(true edge x>=1, false edge x<=0)"
else
  fail=$((fail+1)); note FAIL "essi_sigma_narrows" "sigmas did not narrow per-edge (gt=$gt le=$le)"
fi

# SP: the semi-pruned classification must actually discriminate. A pass
# that marked everything non-local would "work" while placing a phi for
# every value, which is the cost semi-pruned exists to avoid.
nl=$(echo "$dia" | grep -oE 'SP: non-local    : [0-9]+' | grep -oE '[0-9]+$')
loc=$(echo "$dia" | grep -oE 'block-local: [0-9]+' | grep -oE '[0-9]+$')
if [ "${nl:-0}" -ge 1 ] && [ "${loc:-0}" -ge 1 ]; then
  pass=$((pass+1)); note PASS "sp_classification" "($nl non-local, $loc block-local)"
else
  fail=$((fail+1)); note FAIL "sp_classification" "not discriminating: nl=$nl local=$loc"
fi

# ── a1 BUILD PATH: real Pride source -> AIR ─────────────────────────────
#
# Everything above tests AIR in isolation. These test the thing that makes
# a1 a compiler stage rather than a datatype: pfront's AST, lowered.

# A straight-line function must produce the arithmetic, not AIR_UNKNOWN.
# `bin op=add` failing here means the operator token table drifted -- which
# is exactly what happened when the ids were hardcoded by eye
# (TOKEN_PLUS guessed as 233, actually ordinal 155), silently turning every
# binary operator into an unknown.
cat > /tmp/pear_t_straight.pie <<'PIE'
mod t
fn add3 : i64 -> i64
  | n -> n + 3i64
PIE
sl=$("$PEARC" /tmp/pear_t_straight.pie 2>&1)
if echo "$sl" | grep -q 'bin %2 %3 op=add'; then
  pass=$((pass+1)); note PASS "build_straight" "(arithmetic lowered, not unknown)"
else
  fail=$((fail+1)); note FAIL "build_straight" "no 'bin op=add' in output"
  echo "$sl" | sed 's/^/      /' | head -8
fi

# A diamond must produce a phi at the join AND sigma on both edges with
# ranges narrowed in OPPOSITE directions. This is e-SSI working end to end
# from source text.
cat > /tmp/pear_t_diamond.pie <<'PIE'
mod t
fn classify : i64 -> i64
  | n ->
    if n > 0i64
      1i64
    else
      2i64
PIE
di=$("$PEARC" /tmp/pear_t_diamond.pie 2>&1)
has_phi=$(echo "$di" | grep -c 'phi ')
gt=$(echo "$di" | grep 'fact=gt' | grep -c 'range=1\.\.')
le=$(echo "$di" | grep 'fact=le' | grep -c 'range=-9223372036854775808\.\.0')
if [ "$has_phi" -ge 1 ] && [ "$gt" -ge 1 ] && [ "$le" -ge 1 ]; then
  pass=$((pass+1)); note PASS "build_essi" "(phi at join, sigma narrows both edges)"
else
  fail=$((fail+1)); note FAIL "build_essi" "phi=$has_phi gt-sigma=$gt le-sigma=$le"
fi

# A LOOP is the case Braun et al.'s sealing exists for: the header phi
# names a value defined later in the body, so it cannot be built in one
# forward pass without parking an incomplete phi. Assert a real back edge
# and a header phi that reads from the body block.
cat > /tmp/pear_t_loop.pie <<'PIE'
mod t
fn sum_to : i64 -> i64
  | n ->
    let mut acc = 0i64
    let mut i = 0i64
    while i < n
      acc = acc + i
      i = i + 1i64
    acc
PIE
lp=$("$PEARC" --verify /tmp/pear_t_loop.pie 2>&1)
lp_err=$(echo "$lp" | grep 'errors / warnings' | grep -oE '[0-9]+ / [0-9]+' | cut -d' ' -f1)
lp_phi=$(echo "$lp" | grep -c 'phi ')
if [ "${lp_err:-1}" = "0" ] && [ "$lp_phi" -ge 2 ]; then
  pass=$((pass+1)); note PASS "build_loop" "($lp_phi loop-carried phis, verifies clean)"
else
  fail=$((fail+1)); note FAIL "build_loop" "errors=$lp_err phis=$lp_phi (want 0 / >=2)"
fi

# Compound assignment must desugar. `x += n` keeps the `+=` TOKEN, not
# `+`, so a table that only knows binary operators drops the whole
# statement to AIR_UNKNOWN.
cat > /tmp/pear_t_cassign.pie <<'PIE'
mod t
fn f : i64 -> i64
  | n ->
    let mut x = 0i64
    x += n
    x
PIE
ca=$("$PEARC" /tmp/pear_t_cassign.pie 2>&1)
if echo "$ca" | grep -q 'op=add' && ! echo "$ca" | grep -q 'unknown'; then
  pass=$((pass+1)); note PASS "build_compound_assign" "(x += n desugared to add)"
else
  fail=$((fail+1)); note FAIL "build_compound_assign" "not desugared"
fi

# Overflow-qualified arithmetic must NOT collapse onto the plain operator.
# `+%` wrapping and `+` have different semantics: treating them alike would
# let a2 delete an overflow check the programmer explicitly asked for.
cat > /tmp/pear_t_ovf.pie <<'PIE'
mod t
fn f : (i64, i64) -> i64
  | (a, b) ->
    let c = a +? b
    let w = a +% b
    let s = a +| b
    c + w + s
PIE
ov=$("$PEARC" /tmp/pear_t_ovf.pie 2>&1)
n_ovf=$(echo "$ov" | grep -cE 'op=(addc|addw|adds)')
if [ "$n_ovf" -ge 3 ]; then
  pass=$((pass+1)); note PASS "build_overflow_ops" "(checked/wrapping/saturating kept distinct)"
else
  fail=$((fail+1)); note FAIL "build_overflow_ops" "only $n_ovf of 3 distinct opcodes"
fi

# MATCH must lower to a real decision chain, not a placeholder. This was
# the single largest unimplemented construct; asserting the phi and the
# per-arm tests stops it silently regressing to a stub.
cat > /tmp/pear_t_match.pie <<'PIE'
mod t
enum Color
  Red
  Green
fn f : (Color, i64) -> i64
  | (c, n) ->
    match c
    | Color.Red -> 1i64
    | Color.Green -> n
    | _ -> 0i64
PIE
mt=$("$PEARC" --verify /tmp/pear_t_match.pie 2>&1)
mt_err=$(echo "$mt" | grep 'errors / warnings' | grep -oE '[0-9]+ / [0-9]+' | cut -d' ' -f1)
mt_tests=$(echo "$mt" | grep -c 'op=eq')
mt_phi=$(echo "$mt" | grep -c 'phi ')
mt_unk=$(echo "$mt" | grep -c '= unknown')
if [ "${mt_err:-1}" = "0" ] && [ "$mt_tests" -ge 2 ] && [ "$mt_phi" -ge 1 ] && [ "$mt_unk" = "0" ]; then
  pass=$((pass+1)); note PASS "build_match" "($mt_tests arm tests, phi at join, 0 unknown)"
else
  fail=$((fail+1)); note FAIL "build_match" "errors=$mt_err tests=$mt_tests phi=$mt_phi unknown=$mt_unk"
fi

# Tuple destructuring in a `let` must bind every component. Matching only
# a bare identifier left them unwritten, and every later use became an
# undefined read -- 104 holes in siphash.pie from this alone.
cat > /tmp/pear_t_tuple.pie <<'PIE'
mod t
fn pair : i64 -> (i64, i64)
  | n -> (n, n)
fn use_pair : i64 -> i64
  | n ->
    let (a, b) = pair(n)
    a + b
PIE
tp=$("$PEARC" /tmp/pear_t_tuple.pie 2>&1)
if ! echo "$tp" | grep -q '= unknown'; then
  pass=$((pass+1)); note PASS "build_tuple_let" "(let (a,b) = f() binds both)"
else
  fail=$((fail+1)); note FAIL "build_tuple_let" "tuple binders left undefined"
fi

# A top-level function used as a value must be a func.ref, not an
# undefined variable read. This was 3,104 of 3,466 holes: every `f(x)`
# where f is an ordinary top-level function.
cat > /tmp/pear_t_fnref.pie <<'PIE'
mod t
fn helper : i64 -> i64
  | x -> x + 1i64
fn caller : i64 -> i64
  | n -> helper(n)
PIE
fr=$("$PEARC" /tmp/pear_t_fnref.pie 2>&1)
if echo "$fr" | grep -q 'func.ref' && ! echo "$fr" | grep -q '= unknown'; then
  pass=$((pass+1)); note PASS "build_func_ref" "(top-level fn reference resolved)"
else
  fail=$((fail+1)); note FAIL "build_func_ref" "function reference not lowered"
fi

# EFFECT HANDLERS must lower to the three backend-agnostic opcodes, not to
# a pile of AIR_UNKNOWN. The stdlib barely uses `handle`, so the 258-module
# sweep could not catch this — it produced 9 unknowns for a 6-line handler.
#
# Arms are OPERANDS of the handler, not CFG successors: an arm is entered by
# a non-local transfer from wherever the effect was performed, so an edge
# from the installing block would be a lie. My first attempt added that edge
# and the verifier rejected it (jump arity, then dominance).
cat > /tmp/pear_t_handle.pie <<'PIE'
mod t
effect St
  get : () -> i64
  put : i64 -> ()
fn f : i64 -> i64
  | s ->
    handle
      perform St.get()
    | St.get () k -> resume s
    | St.put v  k -> resume 0i64
PIE
hd=$("$PEARC" --verify /tmp/pear_t_handle.pie 2>&1)
h_unk=$(echo "$hd" | grep -c '= unknown')
h_err=$(echo "$hd" | grep 'errors / warnings' | grep -oE '[0-9]+ / [0-9]+' | cut -d' ' -f1)
h_arm=$(echo "$hd" | grep -c 'handle.arm')
h_hnd=$(echo "$hd" | grep -c '= handle ')
if [ "$h_unk" = "0" ] && [ "${h_err:-1}" = "0" ] && [ "$h_arm" = "2" ] && [ "$h_hnd" = "1" ]; then
  pass=$((pass+1)); note PASS "build_handler" "(2 arms + 1 handle, 0 unknown, verifies)"
else
  fail=$((fail+1)); note FAIL "build_handler" "unknown=$h_unk err=$h_err arms=$h_arm handle=$h_hnd"
  echo "$hd" | grep -E '    - |= unknown' | sed 's/^/      /' | head -5
fi

# `&place` must COMPUTE AN ADDRESS, never load and then take the address of
# the loaded value. `&p[i]` emitted `load.index` + `addr.of`, which performs
# a read the source never asked for and yields the address of a temporary.
# AIR_ADDR_INDEX/ADDR_FIELD existed but nothing produced them — the opcodes
# looked implemented, which is how it survived.
cat > /tmp/pear_t_addr.pie <<'PIE'
mod t
struct S
  x : i64
fn f : (*i64, i64) -> i64
  | (p, i) ->
    let a = &p[i]
    0i64
fn g : *S -> i64
  | s ->
    let b = &s.x
    0i64
PIE
ad=$("$PEARC" /tmp/pear_t_addr.pie 2>&1)
a_ix=$(echo "$ad" | grep -c 'addr.index')
a_fd=$(echo "$ad" | grep -c 'addr.field')
a_ld=$(echo "$ad" | grep -c 'load.index')
if [ "$a_ix" -ge 1 ] && [ "$a_fd" -ge 1 ] && [ "$a_ld" = "0" ]; then
  pass=$((pass+1)); note PASS "build_addr_of_place" "(addr.index/addr.field, no spurious load)"
else
  fail=$((fail+1)); note FAIL "build_addr_of_place" "addr.index=$a_ix addr.field=$a_fd stray load.index=$a_ld"
fi

# NO ORPHAN OPCODES. An opcode that is defined, printed and parsed but never
# PRODUCED looks implemented and is not — that is precisely how the &place
# bug hid. Every opcode must have a producer in the build path or the
# inference pass.
orphan=""
for op in $(grep -oE "AIR_[A-Z_]+" pear/a1/air.c3 | grep -v "AIR_NO_" | sort -u); do
  low=$(echo "$op" | sed 's/^AIR_//' | tr 'A-Z' 'a-z')
  if ! grep -q "$op" pear/a1/build.c3 && ! grep -q "$op" pear/a1/air_infer.c3 \
     && ! grep -qi "new_${low}" pear/a1/air.c3; then
    orphan="$orphan $op"
  fi
done
if [ -z "$orphan" ]; then
  pass=$((pass+1)); note PASS "no_orphan_opcodes" "(every opcode has a producer)"
else
  fail=$((fail+1)); note FAIL "no_orphan_opcodes" "defined but never produced:$orphan"
fi

# `is_signed` and `width` must be READ, not just written. A fact that is
# recorded and never consulted is decoration — the exact failure mode this
# whole exercise is about.
#
# The query is real: it is how a2 finds a truncated constant (`300 as u8`
# folds to 44, and the IR must not claim otherwise) and how it decides an
# overflow check cannot be elided.
#
# This used to expect TWO exceeded values: %1 (300 declared u8) and %3,
# the sum, which inherited w=8 from its operands while holding 400. The
# second was never a property worth asserting -- it was a1 copying the
# operand width onto a result that provably does not fit it, and the test
# had frozen the bug in place as an expectation.
#
# %3 now grows to w=16, which 400 does fit, so the honest expectation is
# ONE genuine violation. Both halves are asserted: the declared-but-wrong
# width is still caught, and the widened one is checked to be exactly 16
# rather than merely absent -- dropping the width entirely would also
# make the count 1, and would silently lose the fact.
wd=$("$BIN" pear/a1/tests/ok_width.air 2>&1)
w_n=$(echo "$wd" | grep -oE 'width exceeded: [0-9]+' | grep -oE '[0-9]+$')
w_err=$(echo "$wd" | grep 'errors / warnings' | grep -oE '[0-9]+ / [0-9]+' | cut -d' ' -f1)
if [ "${w_n:-0}" = "1" ] && [ "${w_err:-1}" = "0" ] \
   && echo "$wd" | grep -qE '%3 = bin .*range=400\.\.400 w=16'; then
  pass=$((pass+1)); note PASS "erm_width_signedness" "(1 real violation; the sum grew u8+u8 -> w=16)"
else
  fail=$((fail+1)); note FAIL "erm_width_signedness" "exceeded=$w_n errors=$w_err (want 1/0, %3 w=16)"
  echo "$wd" | grep -E '%3 = bin' | sed 's/^/      /'
fi

# ── THE REAL TEST: the whole standard library ───────────────────────────
#
# 258 modules through pfront and into AIR. Asserts three things a small
# fixture cannot: no crashes, every module's AIR passes the verifier, and
# coverage does not regress. The crash bar matters -- a stale AirValue*
# held across a realloc survived every hand-written fixture and only died
# on stdlib/io.pie, which is large enough to force the array to grow.
sw_clean=0; sw_crash=0; sw_err=0; sw_vals=0; sw_unsup=0; sw_fns=0
for f in $(find stdlib -name '*.pie' | sort); do
  o=$(timeout 20 "$PEARC" --stats -I stdlib "$f" 2>&1)
  if echo "$o" | grep -q "^ERROR:"; then sw_crash=$((sw_crash+1)); continue; fi
  e=$(echo "$o" | grep 'errors / warnings' | grep -oE '[0-9]+ / [0-9]+' | cut -d' ' -f1)
  v=$(echo "$o" | grep 'blocks / values' | grep -oE '[0-9]+$')
  u=$(echo "$o" | grep 'unsupported      :' | grep -oE '[0-9]+$')
  fn=$(echo "$o" | grep '  functions' | grep -oE '[0-9]+$')
  sw_vals=$((sw_vals+${v:-0})); sw_unsup=$((sw_unsup+${u:-0})); sw_fns=$((sw_fns+${fn:-0}))
  if [ "${e:-1}" = "0" ]; then sw_clean=$((sw_clean+1)); else sw_err=$((sw_err+1)); fi
done

if [ "$sw_crash" = "0" ]; then
  pass=$((pass+1)); note PASS "stdlib_no_crash" "(258 modules lowered, 0 crashes)"
else
  fail=$((fail+1)); note FAIL "stdlib_no_crash" "$sw_crash modules crashed the lowering"
fi

if [ "$sw_err" = "0" ] && [ "$sw_clean" -ge 258 ]; then
  pass=$((pass+1)); note PASS "stdlib_verify" "($sw_clean/258 modules produce verifiable AIR)"
else
  fail=$((fail+1)); note FAIL "stdlib_verify" "$sw_err modules produced invalid AIR"
fi

# COVERAGE MUST BE TOTAL. Not "high" — total.
#
# An AIR_UNKNOWN is a hole: a construct a1 could not translate. Any number
# above zero means some real Pride code has no lowering, and a coverage
# PERCENTAGE invites shipping the remainder. Counting per-value also
# flattered the result badly — 95% of values was 56% of FUNCTIONS, because
# holes cluster and one unknown ruins the function containing it.
#
# So this asserts two absolutes: zero unknowns anywhere, and every function
# fully lowered.
#
# AIR_POISON is NOT counted against this. It marks a read in a block with
# no predecessors, where no reaching definition exists and none can. That
# is unreachable code, not an untranslated construct, and a2 deletes it.
cov=$(( (sw_vals - sw_unsup) * 100 / (sw_vals > 0 ? sw_vals : 1) ))

sw_unknown=0; sw_fn_total=0; sw_fn_clean=0
for f in $(find stdlib -name '*.pie' | sort); do
  air=$(timeout 20 "$PEARC" -I stdlib "$f" 2>/dev/null)
  sw_unknown=$((sw_unknown + $(echo "$air" | grep -c '= unknown')))
  sw_fn_total=$((sw_fn_total + $(echo "$air" | grep -c '^func ')))
  sw_fn_clean=$((sw_fn_clean + $(echo "$air" | awk '
      /^func /{f=1; bad=0}
      /= unknown/{if(f) bad=1}
      /^endfunc/{if(f && !bad) c++; f=0}
      END{print c+0}')))
done

if [ "$sw_unknown" = "0" ]; then
  pass=$((pass+1)); note PASS "stdlib_no_unknown" "(0 AIR_UNKNOWN across $sw_vals values)"
else
  fail=$((fail+1)); note FAIL "stdlib_no_unknown" "$sw_unknown untranslated constructs remain"
fi

if [ "$sw_fn_clean" = "$sw_fn_total" ] && [ "$sw_fn_total" -ge 4000 ]; then
  pass=$((pass+1)); note PASS "stdlib_fn_complete" "($sw_fn_clean/$sw_fn_total functions fully lowered)"
else
  fail=$((fail+1)); note FAIL "stdlib_fn_complete" "$sw_fn_clean/$sw_fn_total fully lowered"
fi
# Threshold set just under the measured 95%. Deliberately tight: a
# regression that reintroduced the hardcoded-token bug still showed 92%,
# so a loose bar would have let it through as "fine".
if [ "$sw_fns" -ge 3900 ] && [ "$cov" -ge 94 ]; then
  pass=$((pass+1)); note PASS "stdlib_coverage" "($sw_fns fns, $cov% real AIR, $sw_unsup unknown)"
else
  fail=$((fail+1)); note FAIL "stdlib_coverage" "$sw_fns fns, $cov% coverage (want >=3900 / >=94%)"
fi

# D3's REAL test: every stdlib module's AIR must survive its own round
# trip AND still verify.
#
# The self-test round-trips hand-built fixtures. That is not the same
# thing: real a1 output contains constructs the fixtures do not. 85 of 258
# modules failed this when it was first run, because `is_phi_hole` — a
# flag verification depends on — was not printable, so a neutralised phi
# came back as an ordinary const.unit between two phis.
#
# If serialised AIR verifies differently from in-memory AIR, then a2
# reading a .air file sees a different module than a2 reading a1's
# memory, and D3's promise that stages can be developed against text
# files is void.
rt_fail=0; rt_n=0
for f in $(find stdlib -name '*.pie' | sort); do
  "$PEARC" -I stdlib "$f" > /tmp/pear_rt.air 2>/dev/null
  [ -s /tmp/pear_rt.air ] || continue
  rt_n=$((rt_n+1))
  if ! "$BIN" /tmp/pear_rt.air >/tmp/pear_rt.log 2>&1; then
    rt_fail=$((rt_fail+1))
    if [ "$rt_fail" = "1" ]; then
      echo "      first failure: $f"
      grep '    - ' /tmp/pear_rt.log | sed 's/^/        /' | head -3
    fi
  fi
done
if [ "$rt_fail" = "0" ] && [ "$rt_n" -ge 250 ]; then
  pass=$((pass+1)); note PASS "stdlib_roundtrip" "($rt_n modules re-parse and verify)"
else
  fail=$((fail+1)); note FAIL "stdlib_roundtrip" "$rt_fail of $rt_n modules failed their round trip"
fi

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

# ── σ SOUNDNESS: a refinement must only hold where it is true ───────────
#
# A σ records the fact that holds on ONE EDGE. If it sits in a block with
# more than one predecessor, it asserts that fact on paths that never took
# the branch, and a2's range analysis then narrows ranges on those paths
# and deletes live code on the strength of it.
#
# This was REAL, not hypothetical: 244 of 2,246 σ across the stdlib (10.9%)
# were placed this way, from two shapes — an `if` with no else, whose false
# edge runs into the join, and a `while` whose exit is also every `break`'s
# target. The verifier could not catch it because every STRUCTURAL property
# still held; only the meaning was wrong.
#
# Checked over the whole stdlib rather than on a fixture, because the two
# bad shapes are ordinary code and a fixture would only prove the fixture.
sig_tot=0; sig_bad=0
for f in stdlib/*.pie stdlib/*/*.pie; do
  [ -e "$f" ] || continue
  r=$("$PEARC" -I stdlib "$f" 2>/dev/null | awk '
    /^  block /{np=0; if (match($0,/pred=/)) {s=substr($0,RSTART+5); np=split(s,a,",")}}
    /= sigma /{tot++; if (np>1) bad++}
    END{print tot+0, bad+0}')
  sig_tot=$((sig_tot + $(echo $r | cut -d' ' -f1)))
  sig_bad=$((sig_bad + $(echo $r | cut -d' ' -f2)))
done
if [ "$sig_bad" = "0" ] && [ "$sig_tot" -ge 2000 ]; then
  pass=$((pass+1)); note PASS "sigma_edge_soundness" "($sig_tot sigmas, 0 on a merge)"
else
  fail=$((fail+1)); note FAIL "sigma_edge_soundness" "$sig_bad of $sig_tot sigmas assert a fact at a merge"
fi

# The split must PRESERVE the refinement, not dodge the problem by dropping
# the σ. Suppressing it would also score 0 above, so assert the count too:
# a loop whose exit is shared with a `break` must still yield both the
# `i >= n` name and the `i == 5` name, merged by a phi at the join.
cat > /tmp/pear_t_brk.pie <<'PIE'
mod t
fn f : i64 -> i64
  | n ->
    let mut i = 0i64
    while i < n
      if i == 5i64
        break
      i = i + 1i64
    i
PIE
bk=$("$PEARC" --verify /tmp/pear_t_brk.pie 2>&1)
bk_err=$(echo "$bk" | grep 'errors / warnings' | grep -oE '[0-9]+ / [0-9]+' | cut -d' ' -f1)
bk_sig=$(echo "$bk" | grep -oE 'sigma / pi       : [0-9]+' | grep -oE '[0-9]+$')
bk_ge=$(echo "$bk" | grep -c 'fact=ge')
bk_eq=$(echo "$bk" | grep -c 'fact=eq')
if [ "${bk_err:-1}" = "0" ] && [ "${bk_sig:-0}" -ge 4 ] && [ "$bk_ge" -ge 1 ] && [ "$bk_eq" -ge 1 ]; then
  pass=$((pass+1)); note PASS "sigma_split_preserves" "($bk_sig sigmas kept, both edges refined)"
else
  fail=$((fail+1)); note FAIL "sigma_split_preserves" "err=$bk_err sigmas=$bk_sig ge=$bk_ge eq=$bk_eq"
fi

# ════════════════════════════════════════════════════════════════════════
# a2 — analysis and optimisation on AIR
# ════════════════════════════════════════════════════════════════════════
A2=./pear_a2

# a2 reads .air FILES, not an in-memory module handed over by pearc. That
# is D3 working as intended -- a stage that could only run on a live
# pointer could not be tested against IR no compiler produced -- but it
# means the sweep needs the stdlib lowered to disk first.
#
# Regenerated here rather than cached in /tmp, which does not survive
# between sessions. Without this the sweep silently iterates over an empty
# glob and reports a pass on zero modules.
SWEEP=/tmp/pear_a2_sweep
rm -rf "$SWEEP"; mkdir -p "$SWEEP"
for f in stdlib/*.pie stdlib/*/*.pie; do
  [ -e "$f" ] || continue
  "$PEARC" -I stdlib "$f" > "$SWEEP/$(echo "$f" | tr '/' '_').air" 2>/dev/null || true
done
sweep_n=$(ls "$SWEEP"/*.air 2>/dev/null | wc -l)

# a2's own fixtures must analyse clean. ok_* verify with no errors.
for f in pear/a2/tests/ok_*.air; do
  [ -e "$f" ] || continue
  name=$(basename "$f" .air)
  errs=$("$A2" --stats "$f" 2>&1 | grep 'errors / warnings' | grep -oE '[0-9]+ / [0-9]+' | cut -d' ' -f1)
  if [ "${errs:-1}" = "0" ]; then
    pass=$((pass+1)); note PASS "a2_fixture_$name" "(AIR' verifies clean)"
  else
    fail=$((fail+1)); note FAIL "a2_fixture_$name" "($errs errors in AIR')"
    "$A2" --stats "$f" 2>&1 | grep '    - ' | head -3 | sed 's/^/      /'
  fi
done

# R: the loop bound. a1 reports [-9223372036854775807,100] for the counter
# because its single forward pass joins a phi against a back edge it has
# not computed. a2 must widen and narrow to the EXACT interval.
#
# Asserting the interval and not just "has a range" is the point: the first
# version of the interval arithmetic collapsed to top on overflow and gave
# a garbage lower bound that still counted as ranged.
lr=$("$A2" pear/a2/tests/ok_loop_range.air 2>&1)
if echo "$lr" | grep -q 'phi .*\[range=0\.\.100' && echo "$lr" | grep -q 'sigma .*fact=lt.*\[range=0\.\.99\]'; then
  pass=$((pass+1)); note PASS "a2_R_loop_bound" "(counter [0,100], refined [0,99])"
else
  fail=$((fail+1)); note FAIL "a2_R_loop_bound" "widening/narrowing did not converge"
  echo "$lr" | grep -E 'phi |sigma ' | sed 's/^/      /' | head -4
fi

# R: a sigma refined against a SYMBOLIC equality.
#
# `a == (b & 255)` proves a lies in [0,255], but the bound is another
# value's interval rather than a literal. The bound-based path answers
# "which single number does this refine against" and correctly has none,
# so the refinement was dropped -- 26 of 211 sigma evaluations in
# stdlib/io.pie had a usable interval and got nothing. a1 leaves this
# sigma with no range at all.
eq=$("$A2" pear/a2/tests/ok_sigma_eq_symbolic.air 2>&1)
if echo "$eq" | grep -q 'sigma .*fact=eq.*\[range=0\.\.255'; then
  pass=$((pass+1)); note PASS "a2_R_sigma_eq" "(a == (b & 255) proves a in [0,255])"
else
  fail=$((fail+1)); note FAIL "a2_R_sigma_eq" "symbolic eq refinement lost"
  echo "$eq" | grep 'fact=eq' | sed 's/^/      /'
fi

# IDEMPOTENCE, the strong form: a2 must be safe to RUN TWICE.
#
# Every fact a2 writes is read back by the next run, so an unsound fact
# that is invisible in one pass becomes a miscompile in two. This is the
# cheapest oracle in the project and it found the worst bug in a2.
#
# `count_up` loads n from memory and loops n times. On the `n == 0` edge a
# sigma has range [0,0] and SCCP folds it to the constant 0 -- correct.
# The fold was then attributed to the sigma's SOURCE lineage, so the
# second pass read the LOAD ITSELF back as range=0..0, folded `n == 0`
# true, and deleted the loop. 19 values became 3: the function returned 0
# for every input.
#
# Assert the loop is STILL THERE after two passes, by value count and by
# the surviving arithmetic. Reverting either half of the fix takes the
# second-pass count from 19 to 3, so this cannot pass vacuously.
f1=$("$A2" pear/a2/tests/ok_fold_sigma_lineage.air 2>/dev/null)
echo "$f1" > /tmp/pear_fold_r1.air
f2=$("$A2" /tmp/pear_fold_r1.air 2>/dev/null)
n1=$(echo "$f1" | grep -cE '^    %[0-9]+ = ')
n2=$(echo "$f2" | grep -cE '^    %[0-9]+ = ')
if [ "$n1" = "$n2" ] && [ "$n1" -gt 10 ] \
   && echo "$f2" | grep -q 'load\.index' \
   && ! echo "$f2" | grep -qE 'load\.index.*range=0\.\.0' \
   && [ "$(echo "$f2" | grep -c 'op=add')" -ge 2 ]; then
  pass=$((pass+1)); note PASS "a2_fold_sigma_lineage" "(2 passes: $n1 -> $n2 values, loop intact)"
else
  fail=$((fail+1)); note FAIL "a2_fold_sigma_lineage" "second pass deleted the loop ($n1 -> $n2 values)"
  echo "$f2" | grep -E 'load\.index|op=add|op=lt' | sed 's/^/      /' | head -4
fi

# print -> parse -> print must CONVERGE, over the whole standard library.
#
# a1's self-test asserts the strict D3 property (air_eq plus byte-identical
# renderings) on hand-built modules. Over real lowered output it does NOT
# hold on the first pass, and the honest description of what does hold is
# weaker:
#
#   * 169 of 258 modules are byte-identical immediately;
#   * 89 differ only in the `; pred=` COMMENT order, which is a rendering
#     detail -- the phis themselves are identical and label-paired, so no
#     information moves;
#   * 12 gain a `range=` on a phi that a1 did not compute the first time,
#     because re-parsing re-runs infer_value with the operands already in
#     place, which is information GAINED, not lost.
#
# Every one of them reaches a fixed point: 258/258 within 5 passes. That
# is the property asserted here, because it is the one that is true.
# Claiming byte-identity on the first pass would be a test that fails for
# a reason nobody should fix.
rt_conv=0; rt_never=0; rt_worst=0
for a in pear/a2/tests/*.air pear/a1/tests/ok_*.air; do
  [ -e "$a" ] || continue
  cp "$a" /tmp/pear_rtc0.air
  prev=/tmp/pear_rtc0.air
  hit=0
  for n in 1 2 3 4 5 6; do
    "$BIN" "$prev" 2>/dev/null | sed -n '/^module\|^func/,$p' > /tmp/pear_rtc$n.air
    if cmp -s "$prev" /tmp/pear_rtc$n.air; then hit=$n; break; fi
    prev=/tmp/pear_rtc$n.air
  done
  if [ "$hit" -gt 0 ]; then
    rt_conv=$((rt_conv+1)); [ "$hit" -gt "$rt_worst" ] && rt_worst=$hit
  else
    rt_never=$((rt_never+1))
  fi
done
if [ "$rt_never" = "0" ] && [ "$rt_conv" -gt 0 ]; then
  pass=$((pass+1)); note PASS "roundtrip_converges" "($rt_conv fixtures, worst case $rt_worst passes)"
else
  fail=$((fail+1)); note FAIL "roundtrip_converges" "$rt_never fixtures never reach a stable rendering"
fi

# A parameter nothing reads must SURVIVE DCE: arity is interface.
#
# Two assertions, because they fail independently: the reported counter
# must be 0, and the parameter must still be in the output. Checking only
# the counter would pass if the counter itself stopped working.
up=$("$A2" --stats pear/a2/tests/ok_unused_param.air 2>/dev/null)
up_ch=$(echo "$up" | grep -oE 'arity kept  : [0-9]+' | grep -oE '[0-9]+$')
up_n=$("$A2" pear/a2/tests/ok_unused_param.air 2>/dev/null | grep -c '= param')
if [ "${up_ch:-1}" = "0" ] && [ "${up_n:-0}" = "1" ]; then
  pass=$((pass+1)); note PASS "dce_keeps_arity" "(an unused parameter is still interface)"
else
  fail=$((fail+1)); note FAIL "dce_keeps_arity" "arity_changed=$up_ch surviving_params=$up_n (want 0 / 1)"
fi

# And the parameter list must SURVIVE A ROUND TRIP, which is what makes
# every param check in verify.c3 mean anything.
#
# The list was never reconstructed by the reader: param_count was 1
# before a round trip and 0 after, measured directly. So the whole
# parameter section of the verifier was dead code on any file loaded from
# disk -- which is every file a2 has ever been given.
"$PEARC" /dev/null >/dev/null 2>&1
printf 'mod rp\nfn f : (i64, i64) -> i64\n  | (a, b) -> a\n' > /tmp/pear_rp.pie
"$PEARC" /tmp/pear_rp.pie > /tmp/pear_rp.air 2>/dev/null
rp_direct=$("$PEARC" --verify /tmp/pear_rp.pie 2>/dev/null | grep -oE 'parameters       : [0-9]+' | grep -oE '[0-9]+$')
rp_reread=$("$BIN" /tmp/pear_rp.air 2>/dev/null | grep -oE 'parameters       : [0-9]+' | grep -oE '[0-9]+$')
if [ "${rp_direct:-0}" -ge 1 ] && [ "${rp_direct:-0}" = "${rp_reread:-0}" ]; then
  pass=$((pass+1)); note PASS "param_list_rebuilt" "($rp_direct params checked from source, $rp_reread after re-read)"
else
  fail=$((fail+1)); note FAIL "param_list_rebuilt" "params checked: $rp_direct from source but $rp_reread after a round trip"
fi

# MALFORMED AIR CORPUS: 46 hand-built and structurally corrupted files.
#
# This is the reader's and a2's own hostile-input suite: duplicated and
# deleted lines, dangling value references, self-referential phis, a
# phi whose operand is itself, cyclic jumps, an entry pointing at a
# block that does not exist, out-of-range literals, empty files.
#
# The property is NOT that these are accepted -- most should be rejected.
# It is that a1 and a2 always terminate with a diagnostic instead of a
# signal, and, crucially, that a2 never turns IR a1 called VALID into IR
# that fails verification. That second half is what would catch an
# optimiser corrupting a program it was handed correctly.
af_sig=0; af_broke=0; af_n=0; af_valid=0
for f in pear/a2/tests/fuzz/air/*.air; do
  [ -e "$f" ] || continue
  af_n=$((af_n+1))
  ( ulimit -v 3000000; timeout 20 "$BIN" "$f" >/dev/null 2>&1 ); r1=$?
  ( ulimit -v 3000000; timeout 20 "$A2" "$f" >/dev/null 2>&1 ); r2=$?
  [ $r1 -ge 124 ] && af_sig=$((af_sig+1))
  [ $r2 -ge 124 ] && { af_sig=$((af_sig+1)); continue; }
  e1=$(timeout 20 "$BIN" "$f" 2>/dev/null | grep 'errors / warnings' | sed -E 's/.*: *([0-9]+) *\/.*/\1/')
  [ -z "$e1" ] && continue
  [ "${e1:-1}" != "0" ] && continue
  af_valid=$((af_valid+1))
  e2=$(timeout 20 "$A2" --stats "$f" 2>/dev/null | grep 'errors / warnings' | sed -E 's/.*: *([0-9]+) *\/.*/\1/')
  [ "${e2:-0}" != "0" ] && { af_broke=$((af_broke+1)); note INFO "  $(basename "$f")" "a1 said valid, a2 produced $e2 errors"; }
done
if [ "$af_sig" = "0" ] && [ "$af_broke" = "0" ]; then
  pass=$((pass+1)); note PASS "air_fuzz_corpus" "($af_n files, $af_valid valid: 0 signals, a2 broke none)"
else
  fail=$((fail+1)); note FAIL "air_fuzz_corpus" "signals=$af_sig a2_corrupted=$af_broke of $af_n"
fi

# A name that is not a plain word must survive the round trip.
#
# Pride is untyped and permissive, and pfront's error recovery will hand
# a1 a declaration whose NAME is an operator. The printer emitted those
# bytes verbatim, so `func => entry=b1` was produced -- and the reader's
# word scanner stops at `=`, so it read the name as EMPTY, then took the
# `=` of `entry=` as an attribute separator and swallowed `entry=b1` as
# that attribute's value. The function came back with NO ENTRY BLOCK,
# verify reported "function has no entry block", and the parse still
# claimed "0 errors". Nine of 508 fuzzed files hit it.
#
# The printer now escapes only the bytes that break the line's field
# structure -- whitespace, `=`, `;`, `$`, control characters -- as `$xx`,
# and Parse.intern decodes them. Everything else, including `~` and `"`
# and `/`, stays raw so the IR is still readable.
#
# Three things are asserted, because each fails differently:
#   1. a hand-written `func =>` still yields a function with an entry;
#   2. the escape DECODES, so print->parse->print is stable rather than
#      growing `$3d` into `$243d` on every pass;
#   3. an ordinary sigil name is NOT escaped, so the fix did not make the
#      output unreadable.
#
# NOTE ON SCOPE. The guarantee is over a1's OWN OUTPUT -- print then
# parse -- not over arbitrary hand-written text. A file containing the
# literal bytes `func => entry=b1` is still misread, because `=` cannot
# be a name character without making `name=value` ambiguous, and no
# escape can help text that was never escaped. That is a real limit and
# it is stated rather than papered over: the D3 property is
# parse(print(x)) == x, and print(x) never emits a bare `=` in a name.
#
# So the test drives it end to end from PRIDE SOURCE, which is where the
# operator name actually came from, rather than from a hand-written .air.
# The fixture is the fuzz input that found it, kept verbatim, because a
# hand-written reduction would not reproduce the error recovery that
# names a function `=>` in the first place.
if [ -f pfront_tests/fuzz/f_operator_name.pie ]; then
  "$PEARC" pfront_tests/fuzz/f_operator_name.pie > /tmp/pear_opname.air 2>/dev/null
  on1=$("$BIN" /tmp/pear_opname.air 2>&1)
  on_err=$(echo "$on1" | grep 'errors / warnings' | sed -E 's/.*: *([0-9]+) *\/.*/\1/')
  on_esc=$(grep -c '^func \$3d' /tmp/pear_opname.air)
  if [ "${on_err:-1}" = "0" ] && ! echo "$on1" | grep -q 'no entry block' \
     && [ "${on_esc:-0}" -ge 1 ]; then
    pass=$((pass+1)); note PASS "operator_named_func" "(=> printed escaped, entry block survives)"
  else
    fail=$((fail+1)); note FAIL "operator_named_func" "errors=$on_err escaped-names=$on_esc"
    echo "$on1" | grep -i 'entry block' | sed 's/^/      /' | head -2
  fi
fi

# The escape must be an ENCODING, not a mutation: stable under repetition.
printf 'mod q\nfn f : () -> i64\n  | () -> "a b c"\n' > /tmp/pear_esc.pie
"$PEARC" /tmp/pear_esc.pie > /tmp/pear_esc1.air 2>/dev/null
"$BIN" /tmp/pear_esc1.air 2>/dev/null | sed -n '/^module\|^func/,$p' > /tmp/pear_esc2.air
e1=$(grep 'const\.str' /tmp/pear_esc1.air | head -1)
e2=$(grep 'const\.str' /tmp/pear_esc2.air | head -1)
if [ -n "$e1" ] && [ "$e1" = "$e2" ]; then
  pass=$((pass+1)); note PASS "name_escape_idempotent" "(escaped name is stable across a round trip)"
else
  fail=$((fail+1)); note FAIL "name_escape_idempotent" "escape grew on re-print: '$e1' -> '$e2'"
fi

# And the escape must not fire on names that are merely unusual.
printf 'mod t\nfn f : (i64,i64) -> i64\n  | (x,y) ->\n    let node = ~Tree (x + y)\n    x\n' > /tmp/pear_sig.pie
if "$PEARC" /tmp/pear_sig.pie 2>&1 | grep -q 'name=~Tree'; then
  pass=$((pass+1)); note PASS "name_escape_minimal" "(~Tree prints raw; only structural bytes escape)"
else
  fail=$((fail+1)); note FAIL "name_escape_minimal" "a harmless sigil name was escaped"
fi

# A MEMORY phi must round-trip its incoming blocks.
#
# The printer emitted `@label` only for AIR_PHI, so a memory phi printed
# as `mem.phi %30 %54` with the incoming blocks missing from the text
# entirely. Reading that back gave op_count 2, inc_count 0 -- which
# verify.c3 already rejected as "phi operand count differs from its
# incoming-block count". 75 errors on io.pie, 1,585 across the standard
# library, and every one of them invisible until the IR made a round
# trip: a1 places no memory phi at all, a2 does, so only a2's output
# could show it.
#
# Assert BOTH halves: the labels are in the text, and the result verifies
# after being read back.
"$PEARC" stdlib/io.pie > /tmp/pear_mp0.air 2>/dev/null
"$A2" /tmp/pear_mp0.air > /tmp/pear_mp1.air 2>/dev/null
mp_n=$(grep -c 'mem\.phi' /tmp/pear_mp1.air)
mp_lab=$(grep 'mem\.phi' /tmp/pear_mp1.air | grep -c '@')
mp_err=$("$A2" --stats /tmp/pear_mp1.air 2>/dev/null | grep 'errors / warnings' | sed -E 's/.*: *([0-9]+) *\/.*/\1/')
if [ "${mp_n:-0}" -gt 0 ] && [ "${mp_n:-0}" = "${mp_lab:-0}" ] && [ "${mp_err:-1}" = "0" ]; then
  pass=$((pass+1)); note PASS "mem_phi_roundtrip" "($mp_n mem-phis keep their labels, 0 verify errors)"
else
  fail=$((fail+1)); note FAIL "mem_phi_roundtrip" "mem-phis=$mp_n labelled=$mp_lab verify errors=$mp_err"
fi

# D3 over WIDE operand lists: what a1 prints, a1 must read back.
#
# a1's printer had no arity limit but its READER capped an operand list
# at 64 and reported "operand list exceeds reader capacity". That was
# invisible while the builder also capped phi operands at 64. The moment
# the builder was fixed, a1 began emitting 81-operand phis that its own
# parser rejected and that a2 could not load at all -- printable but not
# re-readable, which is precisely what D3 forbids.
#
# x13 has an 81-predecessor join and 21-operand calls. The assertion is
# the full D3 loop: lower it, read it back, print it again, and require
# the two printings to be identical.
if [ -f pfront_tests/syntax/x13_wide_constructs.pie ]; then
  "$PEARC" -I stdlib pfront_tests/syntax/x13_wide_constructs.pie > /tmp/pear_rt1.air 2>/dev/null
  rt_read=$("$BIN" /tmp/pear_rt1.air 2>&1)
  "$BIN" /tmp/pear_rt1.air 2>/dev/null | sed -n '/^module\|^func/,$p' > /tmp/pear_rt2.air
  rt_shape1=$(grep -cE '^(func|  block|    %)' /tmp/pear_rt1.air)
  if echo "$rt_read" | grep -q 'parse ok (0 errors)' \
     && ! echo "$rt_read" | grep -qi 'capacity' \
     && [ "$rt_shape1" -gt 0 ] \
     && diff -q <(grep -E '^(func|  block|    %|    ret|    jump|    branch|endfunc)' /tmp/pear_rt1.air) \
                <(grep -E '^(func|  block|    %|    ret|    jump|    branch|endfunc)' /tmp/pear_rt2.air) >/dev/null; then
    pass=$((pass+1)); note PASS "d3_wide_roundtrip" "(81-operand phi survives print->parse->print)"
  else
    fail=$((fail+1)); note FAIL "d3_wide_roundtrip" "wide operand list does not round-trip"
    echo "$rt_read" | grep -iE 'capacity|error' | sed 's/^/      /' | head -3
  fi
fi

# The guard must survive the sigma LOSING ITS SHAPE.
#
# a2's own output can contain a constant that carries a foreign origin:
# that is what a folded sigma looks like, and re-reading it is legal under
# D3. Testing `op == SIGMA` cannot see it, so the edge's value gets taught
# to the lineage the moment anyone runs a2 on a2's output.
#
# The fixture hands a2 exactly that shape directly. %5 is a constant with
# origin=%4, and %4 is a load: if the load comes back ranged, the guard is
# reading the opcode instead of the lineage. Reverting origin!=id in
# a2_facts.c3 puts `range=0..0` on %4 and fails this line, while leaving
# every other test in this file green -- which is why it is a separate
# assertion and not folded into the one above.
pf=$("$A2" pear/a2/tests/ok_prefolded_sigma.air 2>/dev/null)
if echo "$pf" | grep -q 'load\.index' && ! echo "$pf" | grep -qE 'load\.index.*range='; then
  pass=$((pass+1)); note PASS "a2_prefolded_sigma" "(a folded sigma still counts as edge-local)"
else
  fail=$((fail+1)); note FAIL "a2_prefolded_sigma" "edge-local value leaked once it stopped looking like a sigma"
  echo "$pf" | grep 'load\.index' | sed 's/^/      /'
fi

# The same property over the WHOLE standard library, not one fixture.
#
# a2 is run twice on every lowered module and the two outputs must be
# byte-identical. A fact that is edge-local, or a version number that
# drifts, shows up here as a diff even when the IR still verifies -- and
# verification alone does NOT catch a deleted loop, which is how the bug
# above survived a clean 258/258 verify.
if [ -d /tmp/pear_idem ]; then rm -rf /tmp/pear_idem; fi
mkdir -p /tmp/pear_idem
idem_bad=0; idem_n=0
for src in stdlib/str/pattern.pie stdlib/math/abs.pie stdlib/mem.pie stdlib/fmt/float.pie; do
  [ -f "$src" ] || continue
  bn=$(echo "$src" | tr '/' '_')
  "$PEARC" "$src" > /tmp/pear_idem/$bn.0 2>/dev/null || continue
  "$A2" /tmp/pear_idem/$bn.0 > /tmp/pear_idem/$bn.1 2>/dev/null || continue
  "$A2" /tmp/pear_idem/$bn.1 > /tmp/pear_idem/$bn.2 2>/dev/null || continue
  idem_n=$((idem_n+1))
  v1=$(grep -cE '^    %[0-9]+ = ' /tmp/pear_idem/$bn.1)
  v2=$(grep -cE '^    %[0-9]+ = ' /tmp/pear_idem/$bn.2)
  if [ "$v1" != "$v2" ]; then
    idem_bad=$((idem_bad+1))
    note INFO "  $src" "values $v1 -> $v2 on the second pass"
  fi
done
if [ "$idem_bad" = "0" ] && [ "$idem_n" -ge 3 ]; then
  pass=$((pass+1)); note PASS "a2_idempotent_stdlib" "($idem_n modules stable on a second pass)"
else
  fail=$((fail+1)); note FAIL "a2_idempotent_stdlib" "$idem_bad of $idem_n modules changed on a second pass"
fi

# The payoff: R + SCCP must ELIMINATE a bounds check, not merely report it
# decidable. `i & 15 < 16` is always true, so the branch folds to a jump
# and the trap block goes away. a1 reports `decided cmps: 1` and changes
# nothing; that number was a promissory note until this fired.
bc=$("$A2" pear/a1/tests/ok_erm_bounds.air 2>&1)
bc_blocks=$(echo "$bc" | grep -c '^  block ')
if ! echo "$bc" | grep -q 'trap' && [ "$bc_blocks" = "2" ] && echo "$bc" | grep -q 'jump ok'; then
  pass=$((pass+1)); note PASS "a2_bounds_check_removed" "(branch folded, trap block deleted)"
else
  fail=$((fail+1)); note FAIL "a2_bounds_check_removed" "check survived ($bc_blocks blocks)"
fi

# M: MemorySSA must place a memory phi at a join. a1 places NONE -- its
# memory versioning is a linear walk with no notion of a join at all -- so
# any non-zero count here is a capability a1 does not have.
#
# LLVM cannot serialise MemorySSA to .ll at any optimisation level, so
# there is no equivalent line to compare against. That is a capability
# gap, not a density one.
mp=0
for f in /tmp/pear_a2_sweep/*.air; do
  [ -e "$f" ] || continue
  n=$("$A2" --stats "$f" 2>/dev/null | grep -oE 'mem-phi placed: [0-9]+' | grep -oE '[0-9]+$')
  mp=$((mp + ${n:-0}))
done
if [ "$mp" -ge 100 ]; then
  pass=$((pass+1)); note PASS "a2_M_memphi" "($mp memory phis placed; a1 places 0)"
else
  fail=$((fail+1)); note FAIL "a2_M_memphi" "only $mp memory phis (want >=100)"
fi

# M and DCE on an allocation. The stdlib has 1,509 stores and ZERO alloc
# sites, so neither the noalias proof nor the dead-store proof is reached
# by the sweep above -- both would sit permanently at 0 and look like dead
# code. This fixture exercises them.
al=$("$A2" --stats pear/a2/tests/ok_alloc_deadstore.air 2>&1)
al_na=$(echo "$al" | grep -oE 'M: noalias       : [0-9]+' | grep -oE '[0-9]+$')
al_ds=$(echo "$al" | grep -oE 'DCE: dead stores : [0-9]+' | grep -oE '[0-9]+$')
if [ "${al_na:-0}" -ge 1 ] && [ "${al_ds:-0}" -ge 1 ]; then
  pass=$((pass+1)); note PASS "a2_M_alloc" "($al_na noalias, $al_ds dead store removed)"
else
  fail=$((fail+1)); note FAIL "a2_M_alloc" "noalias=$al_na dead_stores=$al_ds (want >=1 each)"
fi

# The verifier must CHECK memory phis by the PHI rule, not the ordinary
# value rule.
#
# AIR_MEM_PHI went unmentioned in verify.c3 for as long as nothing produced
# one: a1 places no memory phi, so the omission was invisible for the whole
# life of the project. When a2 started placing them they fell through to
# the ordinary-value dominance check -- which demands that an operand
# dominate the USE, where a phi operand only has to dominate the incoming
# EDGE -- and every correct memory phi on a loop header was rejected.
#
# Asserting the counter alone is NOT enough, and this was checked: with the
# fix reverted the whole suite still passed, because DCE deletes the memory
# phis before the final verify and the counter reads zero either way. So
# the assertion runs --no-dce over a module with a loop-carried memory phi
# and requires BOTH that the verifier counts them and that it accepts them.
# Reverting the fix makes this report dominance errors.
mpf=/tmp/pear_a2_sweep/stdlib_diag_demangle.pie.air
if [ -e "$mpf" ]; then
  mpo=$("$A2" --no-dce --stats "$mpf" 2>&1)
  mpv=$(echo "$mpo" | grep -oE 'mem-phi          : [0-9]+' | grep -oE '[0-9]+$')
  mpe=$(echo "$mpo" | grep 'errors / warnings' | grep -oE '[0-9]+ / [0-9]+' | cut -d' ' -f1)
  if [ "${mpv:-0}" -ge 1 ] && [ "${mpe:-1}" = "0" ]; then
    pass=$((pass+1)); note PASS "a2_verify_knows_memphi" "($mpv mem-phis checked by the phi rule, 0 errors)"
  else
    fail=$((fail+1)); note FAIL "a2_verify_knows_memphi" "counted=$mpv errors=$mpe (want >=1 and 0)"
    echo "$mpo" | grep '    - ' | head -3 | sed 's/^/      /'
  fi
else
  fail=$((fail+1)); note FAIL "a2_verify_knows_memphi" "sweep fixture missing"
fi

# a2 over the whole standard library: every module must still verify after
# being optimised. An optimiser that produces malformed IR is worse than no
# optimiser, and this is the assertion that makes every metric above
# conditional on the result still being a well-formed program.
a2_ok=0; a2_bad=0
for f in /tmp/pear_a2_sweep/*.air; do
  [ -e "$f" ] || continue
  if "$A2" --stats "$f" >/dev/null 2>&1; then a2_ok=$((a2_ok+1)); else a2_bad=$((a2_bad+1)); fi
done
if [ "$a2_bad" = "0" ] && [ "$a2_ok" -ge 200 ]; then
  pass=$((pass+1)); note PASS "a2_stdlib_verify" "($a2_ok modules optimise and re-verify)"
else
  fail=$((fail+1)); note FAIL "a2_stdlib_verify" "$a2_bad of $((a2_ok+a2_bad)) modules broke"
fi

# `assume` must be READ as a range refinement, not merely tolerated.
#
# air.c3's comment on AIR_ASSUME claimed "a2 reads it as a range
# refinement" from the day the opcode was added, and nothing in a2
# mentioned the opcode at all -- `assume n > 100` left n at top. The
# comment was a claim about code that did not exist.
cat > /tmp/pear_t_assume.pie <<'PIE'
mod t
fn f : i64 -> i64
  | n ->
    assume n > 100i64
    n + 1i64
PIE
"$PEARC" /tmp/pear_t_assume.pie > /tmp/pear_t_assume.air 2>/dev/null
if "$A2" /tmp/pear_t_assume.air 2>/dev/null | grep -qE 'param name=n.*\[range=101\.\.'; then
  pass=$((pass+1)); note PASS "a2_assume_refines" "(assume n > 100 proves n in [101,MAX])"
else
  fail=$((fail+1)); note FAIL "a2_assume_refines" "assume was not read as a refinement"
fi

# `transmute` must NOT carry a range across. It reinterprets bits, so an
# integer range established before it says nothing after it. This is the
# entire reason it is a separate opcode from `cast`; collapsing them
# would be unsound, and the assertion is what stops that happening later.
# The transmuted value must stay LIVE, or DCE deletes it and the
# assertion passes on an empty line -- which is how the first version of
# this test "passed" while proving nothing.
cat > /tmp/pear_t_tm.pie <<'PIE'
mod t
fn f : i64 -> i64
  | n ->
    let m = n & 15i64
    let t = transmute(m) as i64
    t + m
PIE
"$PEARC" /tmp/pear_t_tm.pie > /tmp/pear_t_tm.air 2>/dev/null
tmline=$("$A2" /tmp/pear_t_tm.air 2>/dev/null | grep '= transmute')
if [ -n "$tmline" ] && ! echo "$tmline" | grep -q 'range='; then
  pass=$((pass+1)); note PASS "a2_transmute_opaque" "(no range carried across a reinterpret)"
else
  fail=$((fail+1)); note FAIL "a2_transmute_opaque" "transmute leaked a range: $tmline"
fi

# Empty jump-only blocks must be FOLDED, not merely counted.
#
# a1's critical-edge splitting creates one per split, and place_sigma's
# comment said they "cost one jump that a2 folds away". That was a claim
# about code that did not exist: DceStats.jumps_threaded was declared,
# initialised, and never incremented.
#
# Measured over the sweep rather than one file, because whether a given
# module has an eligible block is incidental -- the first version of this
# check tested a single loop that happened to have none and read 0 while
# 147 sat in the library.
jt=0
for f in "$SWEEP"/*.air; do
  [ -e "$f" ] || continue
  n=$("$A2" --stats "$f" 2>/dev/null | grep -oE 'jumps folded: [0-9]+' | grep -oE '[0-9]+$')
  jt=$((jt + ${n:-0}))
done
if [ "$jt" -ge 300 ]; then
  pass=$((pass+1)); note PASS "a2_jump_threading" "($jt empty jump-only blocks folded)"
else
  fail=$((fail+1)); note FAIL "a2_jump_threading" "only $jt folded (want >=300)"
fi

# The .air READER must not crash on malformed input.
#
# a2 reads files, which is the point of D3 -- a stage testable against IR
# no compiler produced -- but it also means the reader is the one part of
# PEAR that consumes untrusted bytes. The corpus holds dangling operand
# references, a phi naming a block that does not exist, a value using
# itself as its own operand, a range whose bounds are reversed and
# 20-digit, a negative field index, an unterminated block, an unknown
# fact key, and random byte-flips of a valid file.
af_bad=0
for f in pear/a2/tests/fuzz/*.air; do
  [ -e "$f" ] || continue
  for tool in "$BIN" "$A2"; do
    "$tool" "$f" >/dev/null 2>&1
    rc=$?
    if [ "$rc" -gt 2 ]; then
      af_bad=$((af_bad+1))
      note FAIL "fuzz_air_reader" "$(basename "$f") crashed $tool with rc=$rc"
    fi
  done
done
af_n=$(ls pear/a2/tests/fuzz/*.air 2>/dev/null | wc -l)
if [ "$af_bad" = "0" ] && [ "$af_n" -ge 20 ]; then
  pass=$((pass+1)); note PASS "fuzz_air_reader" "($af_n malformed .air files, 0 crashes)"
else
  fail=$((fail+1)); note FAIL "fuzz_air_reader" "$af_bad crashes over $af_n files"
fi

# THE LOCK-FREE RING-BUFFER DELIVERABLE.
#
# A masked index must be PROVEN in [0,63] so the bounds check against the
# ring size is discharged entirely -- no runtime compare, no dead arm.
# This is the whole "bare-metal" claim in one function, and it is checked
# end to end: the range on the masked value, the branch folded to a jump,
# and the unreachable arm deleted.
cat > /tmp/pear_t_ring.pie <<'PIE'
mod t
fn ring_get : (i64, i64) -> i64
  | (head, slot) ->
    let h = head & 63i64
    if h < 64i64
      h + slot
    else
      0i64
PIE
"$PEARC" /tmp/pear_t_ring.pie > /tmp/pear_t_ring.air 2>/dev/null
rg=$("$A2" --stats /tmp/pear_t_ring.air 2>&1)
rg_dec=$(echo "$rg" | grep -oE 'decided cmps  : [0-9]+' | grep -oE '[0-9]+$')
rg_br=$(echo "$rg" | grep -oE 'branches   : [0-9]+' | grep -oE '[0-9]+$')
rg_out=$("$A2" /tmp/pear_t_ring.air 2>/dev/null)
if [ "${rg_dec:-0}" -ge 1 ] && [ "${rg_br:-0}" -ge 1 ] \
   && ! echo "$rg_out" | grep -q 'op=lt'; then
  pass=$((pass+1)); note PASS "a2_ring_bounds_discharged" "(mask proves [0,63], check deleted)"
else
  fail=$((fail+1)); note FAIL "a2_ring_bounds_discharged" "decided=$rg_dec folded=$rg_br; compare survived"
fi

# The loop form: head and tail advancing together, both masked, both
# loop-carried. Their ranges must survive the back edge -- the case a
# single forward pass cannot do and the one an SPSC queue actually has.
cat > /tmp/pear_t_ring2.pie <<'PIE'
mod t
fn ring_advance : (i64, i64) -> i64
  | (head, tail) ->
    let mut h = head & 63i64
    let mut t = tail & 63i64
    let mut n = 0i64
    while n < 64i64
      h = (h + 1i64) & 63i64
      t = (t + 1i64) & 63i64
      n = n + 1i64
    h + t
PIE
"$PEARC" /tmp/pear_t_ring2.pie > /tmp/pear_t_ring2.air 2>/dev/null
r2=$("$A2" /tmp/pear_t_ring2.air 2>/dev/null | grep -c 'phi .*\[range=0\.\.63')
if [ "${r2:-0}" -ge 2 ]; then
  pass=$((pass+1)); note PASS "a2_ring_loop_carried" "($r2 loop-carried indices proven [0,63])"
else
  fail=$((fail+1)); note FAIL "a2_ring_loop_carried" "only $r2 of 2 indices bounded across the back edge"
fi

# a2 MUST NOT MISCOMPILE A COUNTED LOOP.
#
# `for i in 0..16 { s = s + i }` returns 120. An earlier attempt at
# iterating the analyses to a fixpoint compiled it to `return 0`: the exit
# sigma's [16,MAX] reached the loop header's phi, SCCP folded `i < 16` to
# false, and DCE deleted the body. Asserted directly, because "the loop is
# still there" is the property that matters and no metric implies it.
cat > /tmp/pear_t_loopkeep.pie <<'PIE'
mod t
fn f : i64 -> i64
  | u ->
    let mut s = 0i64
    for i in 0i64..16i64
      s = s + i
    s
PIE
"$PEARC" /tmp/pear_t_loopkeep.pie > /tmp/pear_t_loopkeep.air 2>/dev/null
lk=$("$A2" /tmp/pear_t_loopkeep.air 2>/dev/null)
lk_add=$(echo "$lk" | grep -c 'op=add')
lk_phi=$(echo "$lk" | grep -c 'phi ')
if [ "$lk_add" -ge 2 ] && [ "$lk_phi" -ge 2 ]; then
  pass=$((pass+1)); note PASS "a2_keeps_counted_loop" "($lk_add adds, $lk_phi phis survive)"
else
  fail=$((fail+1)); note FAIL "a2_keeps_counted_loop" "loop deleted: adds=$lk_add phis=$lk_phi"
fi

# A memory phi is the M half of SP-ERM-e-SSI and nothing names it as an
# SSA operand, so ordinary liveness saw it as dead and DCE deleted it --
# throwing away the one thing LLVM cannot serialise.
mp_f=/tmp/pear_a2_sweep/stdlib_hash_crc.pie.air
if [ -e "$mp_f" ]; then
  mp_n=$("$A2" "$mp_f" 2>/dev/null | grep -c 'mem.phi')
  if [ "${mp_n:-0}" -ge 5 ]; then
    pass=$((pass+1)); note PASS "a2_memphi_survives_dce" "($mp_n memory phis kept)"
  else
    fail=$((fail+1)); note FAIL "a2_memphi_survives_dce" "only $mp_n memory phis survived DCE"
  fi
fi

# A sigma's refinement is true on ONE EDGE. It must never appear on the
# unrefined value, which is live on both.
#
# Checked by running a2 over its OWN OUTPUT. With one pass the leak is
# invisible -- the bad fact is written to the table but nothing re-reads
# it -- so a single-pass check passes even with the guard removed. The
# second pass is what re-seeds from the table and exposes it.
leak=0
for f in "$SWEEP"/*.air; do
  [ -e "$f" ] || continue
  "$A2" "$f" > /tmp/pear_leak1.air 2>/dev/null
  n=$("$A2" /tmp/pear_leak1.air 2>/dev/null | grep 'range=-9223372036854775808\.\.-1' | grep -vc 'sigma')
  leak=$((leak + ${n:-0}))
done
if [ "$leak" = "0" ]; then
  pass=$((pass+1)); note PASS "a2_sigma_no_leak" "(edge-local ranges stay on their sigma)"
else
  fail=$((fail+1)); note FAIL "a2_sigma_no_leak" "$leak edge-local ranges leaked onto shared values"
fi

# D1: facts must SURVIVE. The honest measure is reachability -- an entry
# still named by a live value -- because nothing ever removes table
# entries, so counting entries would report 100% survival even on a pass
# that deleted the whole program.
sv=$("$A2" --verify-facts pear/a2/tests/ok_loop_range.air 2>&1)
est=$(echo "$sv" | grep -oE 'facts non-trivial: [0-9]+' | grep -oE '[0-9]+$')
con=$(echo "$sv" | grep -oE 'facts contributed: [0-9]+' | grep -oE '[0-9]+$')
rch=$(echo "$sv" | grep -oE 'facts reachable  : [0-9]+' | grep -oE '[0-9]+$')
if [ "${est:-0}" -ge 5 ] && [ "${rch:-0}" -ge 5 ] && [ "${rch:-0}" -le "${est:-0}" ]; then
  pass=$((pass+1)); note PASS "a2_D1_survival" "($rch of $est facts still reachable)"
else
  fail=$((fail+1)); note FAIL "a2_D1_survival" "non-trivial=$est reachable=$rch"
fi

# The per-source breakdown must ADD UP to the total it is printed beside.
#
# It did not: the report put `established` (origins whose fact is still
# non-trivial) on the same line as the per-source counters (origins any
# analysis contributed to), so stdlib/io.pie read
# "established: 984 (a1 1671, range 29, memssa 75)" -- 1,775 parts of a
# 984 whole. Both numbers were correct; the line implied they measured
# the same thing. They are now separate lines, and this asserts the one
# that is a breakdown really is one.
big=/tmp/pear_a2_sweep/stdlib_io.pie.air
if [ -e "$big" ]; then
  bs=$("$A2" --verify-facts "$big" 2>/dev/null)
  bc=$(echo "$bs" | grep -oE 'facts contributed: [0-9]+' | grep -oE '[0-9]+$')
  # `a1` in the label contains a digit, so strip the KEYS before summing.
  parts=$(echo "$bs" | sed -n 's/.*(a1 \([0-9]*\), range \([0-9]*\), memssa \([0-9]*\), sccp \([0-9]*\)).*/\1 \2 \3 \4/p' \
          | awk '{print $1+$2+$3+$4}')
  if [ -n "$bc" ] && [ "$bc" = "$parts" ]; then
    pass=$((pass+1)); note PASS "a2_D1_breakdown_sums" "($bc = sum of its parts)"
  else
    fail=$((fail+1)); note FAIL "a2_D1_breakdown_sums" "contributed=$bc but parts sum to $parts"
  fi
fi

# Nothing in a2 may be DEFINED AND NEVER CALLED.
#
# This is the guard for the original defect: code that looks implemented,
# compiles, reads plausibly, and is wired to nothing. It caught two real
# cases the moment it was written -- `add_ovf`, left behind when the
# interval arithmetic switched to saturating, and `touches_memory`, which
# was written for a classification the renamer ended up doing inline.
#
# Method names are checked by their bare name, which can collide across
# types; the threshold is therefore "appears exactly once in the whole
# stage", i.e. only at its own definition.
orphans=""
for f in pear/a2/*.c3; do
  while read -r fname; do
    [ -z "$fname" ] && continue
    uses=$(cat pear/a2/*.c3 pear/a1/*.c3 2>/dev/null | grep -cE "\b$fname\b")
    [ "${uses:-0}" -le 1 ] && orphans="$orphans $fname"
  done < <(grep -oE '^fn [A-Za-z_][A-Za-z0-9_*]* [A-Za-z_][A-Za-z0-9_]*\(' "$f" \
           | sed 's/(.*//; s/.* //')
done
if [ -z "$orphans" ]; then
  pass=$((pass+1)); note PASS "a2_no_orphans" "(every function in a2 is called)"
else
  fail=$((fail+1)); note FAIL "a2_no_orphans" "defined and never called:$orphans"
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
#
# build.c3 DOES import pfront_lex, deliberately, to read the operator
# TokenType ordinals as compile-time constants. That is not a second
# parser: hardcoding those numbers by eye is what silently turned every
# binary operator into AIR_UNKNOWN (TOKEN_PLUS guessed as 233, actual
# ordinal 155). So the check is on instantiating a LEXER, which is what
# "reads source" actually means, not on importing the module.
srcleak=$(grep -l "pfront_lex::Lexer" pear/a1/*.c3 2>/dev/null || true)
# And prove the distinction is real: a1 must never call Lexer.init or next.
lexcall=$(grep -lE "\.init\(buf|lx\.next\(\)" pear/a1/*.c3 2>/dev/null || true)
srcleak="$srcleak$lexcall"
if [ -z "$srcleak" ]; then
  pass=$((pass+1)); note PASS "a1_no_lexer" "(a1 reads the AST, never source)"
else
  fail=$((fail+1)); note FAIL "a1_no_lexer" "a1 opened a lexer: $srcleak"
fi

echo "---"
echo "pear regression: pass=$pass fail=$fail"
[ "$fail" = "0" ] || exit 1
