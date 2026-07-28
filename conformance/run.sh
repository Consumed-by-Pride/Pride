#!/bin/bash
# Semantic conformance harness.
#
# Each case file begins with EXPECT lines of the form:
#   -- EXPECT: <phase>-<kind> <line>:<col> [substring]
#   -- EXPECT-COUNT: <category>=<n>
#   -- EXPECT-CLEAN            (no errors/warnings of any kind)
# where <phase>-<kind> is one of:
#   resolve, type-err, type-warn, effect-err, effect-warn, lint-warn
# A test PASSES iff every EXPECT is satisfied AND (in strict-expectation mode)
# no unexpected diagnostics of the asserted phases appear.
#
# Usage: bash conformance/run.sh
BIN=../pride
cd "$(dirname "$0")"
pass=0; fail=0
for f in cases/*.pie; do
  exp=$(grep -E '^-- EXPECT' "$f")
  # actual run
  out=$("$BIN" "$f" 2>&1)
  ok=1
  reasons=""
  # COUNT assertions
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    spec="${line#*EXPECT}"
    case "$spec" in
      -COUNT:*)
        kv="${spec#-COUNT:}"; kv="$(echo "$kv"|xargs)"
        cat="${kv%%=*}"; want="${kv##*=}"
        case "$cat" in
          resolve)    got=$(echo "$out"|grep -cE '^\s+\[resolve ');;
          type-err)   got=$(echo "$out"|grep -cE '^\s+\[type-err ');;
          type-warn)  got=$(echo "$out"|grep -cE '^\s+\[type-warn ');;
          effect-err) got=$(echo "$out"|grep -cE '^\s+\[effect-err ');;
          effect-warn)got=$(echo "$out"|grep -cE '^\s+\[effect-warn ');;
          lint-warn)  got=$(echo "$out"|grep -cE '^\s+\[lint');;
          parse)      got=$(echo "$out"|grep -E 'parse errors'|grep -oE '[0-9]+$');;
        esac
        if [ "$got" != "$want" ]; then ok=0; reasons="$reasons; count $cat want=$want got=$got"; fi
        ;;
      :*)
        body="${spec#:}"; body="$(echo "$body"|xargs)"
        # body = "<tag> <line>:<col> [substr]"
        tag=$(echo "$body"|awk '{print $1}')
        loc=$(echo "$body"|awk '{print $2}')
        sub=$(echo "$body"|cut -d' ' -f3-)
        # map tag to bracket label
        case "$tag" in
          resolve)    lbl="resolve";;
          type-err)   lbl="type-err";;
          type-warn)  lbl="type-warn";;
          effect-err) lbl="effect-err";;
          effect-warn)lbl="effect-warn";;
          lint-warn)  lbl="lint-warn";;
          *)          lbl="$tag";;
        esac
        # match a diagnostic line: [<lbl> L:C] ... <substr>
        if ! echo "$out" | grep -qE "\[$lbl $loc\]" ; then
          ok=0; reasons="$reasons; missing $tag at $loc"
        elif [ -n "$sub" ] && ! echo "$out" | grep -E "\[$lbl $loc\]" | grep -qF "$sub"; then
          ok=0; reasons="$reasons; $tag@$loc text!~'$sub'"
        fi
        ;;
      -CLEAN*)
        n=$(echo "$out"|grep -cE '^\s+\[(resolve|type-err|type-warn|effect-err|effect-warn|lint)')
        if [ "$n" != "0" ]; then ok=0; reasons="$reasons; expected CLEAN but got $n diagnostics"; fi
        ;;
    esac
  done <<< "$exp"
  if [ "$ok" = 1 ]; then pass=$((pass+1)); else echo "FAIL $f$reasons"; fail=$((fail+1)); fi
done
echo "----"
echo "conformance pass=$pass fail=$fail"
