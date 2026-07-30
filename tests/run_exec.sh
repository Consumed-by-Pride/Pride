#!/bin/bash
# Pride execution test suite.
# Each test: compiles .pie → runs binary → checks stdout against EXPECT.
# Usage: bash tests/run_exec.sh

set -o pipefail
PRIDE="./pride"
CRT_LANG="runtime/compiler_rt.o"
CRT_ARCH="runtime/compiler_rt_arch.o"
CRT=/usr/lib/x86_64-linux-gnu
GCC=/usr/lib/gcc/x86_64-linux-gnu/14

pass=0; fail=0; skip=0

# Adaptive C standard detection for the runtime objects — probes $CC for the
# newest supported standard (c23 → c2x → gnu18 → c18 → c17 → c11).
# Override with CC=... or PRIDE_C_STD=-std=xxx.
# shellcheck source=../scripts/detect_c_std.sh
source "$(dirname "$0")/../scripts/detect_c_std.sh"
CC="$(pride_resolve_cc)"
CSTD="$(pride_detect_c_std "$CC")"
echo "C runtime toolchain: $CC $CSTD (adaptive)"

# Recompile CRTs if needed
if [ ! -f "$CRT_LANG" ] || [ runtime/compiler_rt.c -nt "$CRT_LANG" ]; then
    $CC -O2 $CSTD -pthread -fPIC -msse4.1 -ffunction-sections -fdata-sections \
        -Wno-unused-parameter -Wno-unused-function -Wno-builtin-declaration-mismatch \
        -c runtime/compiler_rt.c -o "$CRT_LANG" 2>/dev/null
fi
if [ ! -f "$CRT_ARCH" ] || [ runtime/compiler_rt_arch.c -nt "$CRT_ARCH" ]; then
    $CC -O2 $CSTD -pthread -fPIC -ffunction-sections -fdata-sections \
        -Wno-unused-parameter -Wno-unused-function -Wno-builtin-declaration-mismatch \
        -c runtime/compiler_rt_arch.c -o "$CRT_ARCH" 2>/dev/null
fi

compile_and_run() {
    local src="$1" name="$2" expect="$3"
    local ll="${src%.pie}.ll" bc="/tmp/pt_${name}.bc" obj="/tmp/pt_${name}.o" bin="/tmp/pt_${name}"

    # Emit LLVM IR
    "$PRIDE" "$src" --emit-llvm >/dev/null 2>&1 || { echo "FAIL [emit] $name"; fail=$((fail+1)); return; }
    [ -f "$ll" ] || { echo "FAIL [no-ll] $name"; fail=$((fail+1)); return; }

    # Assemble → optimise → codegen → link
    llvm-as "$ll" -o "$bc" 2>/dev/null || { echo "FAIL [llvm-as] $name"; fail=$((fail+1)); return; }
    opt -O2 "$bc" -o "${bc%.bc}.opt.bc" 2>/dev/null || { echo "FAIL [opt] $name"; fail=$((fail+1)); return; }
    llc -filetype=obj -relocation-model=pic "${bc%.bc}.opt.bc" -o "$obj" 2>/dev/null \
        || { echo "FAIL [llc] $name"; fail=$((fail+1)); return; }
    ld.lld --gc-sections "$obj" "$CRT_LANG" "$CRT_ARCH" \
        $CRT/crt1.o $CRT/crti.o $CRT/crtn.o \
        -dynamic-linker /lib64/ld-linux-x86-64.so.2 \
        -L$CRT -L$GCC -lc -lm -lgcc -lgcc_s \
        -o "$bin" 2>/dev/null || { echo "FAIL [link] $name"; fail=$((fail+1)); return; }

    # Run with 5s timeout
    local got; got=$(timeout 5 "$bin" 2>/dev/null); local rc=$?
    if [ $rc -eq 124 ]; then echo "FAIL [timeout] $name"; fail=$((fail+1)); return; fi
    if [ $rc -ne 0 ] && [ $rc -ne 1 ]; then echo "FAIL [crash:$rc] $name"; fail=$((fail+1)); return; fi

    if [ "$got" = "$expect" ]; then
        echo "PASS $name"
        pass=$((pass+1))
    else
        echo "FAIL [output] $name"
        echo "  expected: $(echo "$expect" | head -3)"
        echo "  got:      $(echo "$got" | head -3)"
        fail=$((fail+1))
    fi
}

for f in tests/exec/*.pie; do
    name=$(basename "$f" .pie)
    expect=$(grep '^-- EXPECT:' "$f" | sed 's/^-- EXPECT: //' | sed 's/\\n/\n/g' | tr -d '\r')
    compile_and_run "$f" "$name" "$expect"
done

echo ""
echo "=== Execution tests: pass=$pass fail=$fail skip=$skip ==="
