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
wd=$("$BIN" pear/a1/tests/ok_width.air 2>&1)
w_n=$(echo "$wd" | grep -oE 'width exceeded: [0-9]+' | grep -oE '[0-9]+$')
w_err=$(echo "$wd" | grep 'errors / warnings' | grep -oE '[0-9]+ / [0-9]+' | cut -d' ' -f1)
# %1 (300 in 8 bits) and %3 (400 in 8 bits) exceed; %2 (100) fits.
if [ "${w_n:-0}" = "2" ] && [ "${w_err:-1}" = "0" ]; then
  pass=$((pass+1)); note PASS "erm_width_signedness" "(2 of 3 values exceed their declared width)"
else
  fail=$((fail+1)); note FAIL "erm_width_signedness" "exceeded=$w_n errors=$w_err (want 2/0)"
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
