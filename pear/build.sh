#!/usr/bin/env bash
# Build the PEAR binaries.
#
# Two executables share pear/a1/, so neither can be built with a plain
# glob: each has its own `main`.
#
#   pear_a1_test  self-test + .air fixture runner. Links only the a1
#                 modules and pfront_core -- no lexer, no parser. That is
#                 deliberate: the round-trip and verifier tests must be
#                 runnable with no compiler attached (PEAR.md D3).
#
#   pearc         the real driver: Pride source -> AST -> AIR. Links the
#                 whole pfront front end (minus its own main).
set -u
cd "$(dirname "$0")/.." || exit 1
C3=${C3:-/tmp/c3/c3c}
[ -x "$C3" ] || { echo "c3c not found at $C3"; exit 2; }

A1_CORE="pear/a1/air.c3 pear/a1/air_erm.c3 pear/a1/air_infer.c3 \
         pear/a1/air_print.c3 pear/a1/air_parse.c3 pear/a1/verify.c3"

# The self-test does NOT link build.c3 or pearc.c3: it must keep working
# without the front end, which is what makes a3/a4/a5 testable before a1's
# build path is finished.
"$C3" compile $A1_CORE pear/a1/air_selftest.c3 pfront/pfront_core.c3 \
      -o pear_a1_test 2>&1 | grep -v "^Program linked" || true
[ -f pear_a1_test ] || { echo "FAILED: pear_a1_test"; exit 2; }
chmod +x pear_a1_test

PFRONT=$(ls pfront/*.c3 | grep -v pfront_main.c3)
"$C3" compile $A1_CORE pear/a1/build.c3 pear/a1/pearc.c3 \
      $PFRONT pfront/theory/*.c3 \
      -o pearc 2>&1 | grep -v "^Program linked" || true
[ -f pearc ] || { echo "FAILED: pearc"; exit 2; }
chmod +x pearc

# pear_a2 reads and writes .air. It links the a1 CORE (the datatype, the
# reader, the writer, the verifier) but NOT build.c3 -- a2 must not be able
# to reach a PNode even by accident, which is D5 enforced by the link line
# rather than by convention. pear_tests/run.sh greps for the same property.
A2="pear/a2/a2_cfg.c3 pear/a2/a2_facts.c3 pear/a2/a2_range.c3 \
    pear/a2/a2_memssa.c3 pear/a2/a2_sccp.c3 pear/a2/a2_dce.c3"
"$C3" compile $A1_CORE $A2 pear/a2/a2_main.c3 pfront/pfront_core.c3 \
      -o pear_a2 2>&1 | grep -v "^Program linked" || true
[ -f pear_a2 ] || { echo "FAILED: pear_a2"; exit 2; }
chmod +x pear_a2

echo "built: pear_a1_test pearc pear_a2"
