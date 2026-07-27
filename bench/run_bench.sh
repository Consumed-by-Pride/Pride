#!/usr/bin/env bash
# bench/run_bench.sh — Pride vs C performance benchmarks
# Usage: bash bench/run_bench.sh
set -e
cd "$(dirname "$0")/.."
export PATH="/usr/bin:$PATH"

PRIDEC="./prydc"
GCC="gcc"
LLVM_OPT="opt-22"

RED='\033[0;31m'; GRN='\033[0;32m'; YEL='\033[1;33m'; BLU='\033[0;34m'; NC='\033[0m'; BOLD='\033[1m'

run_bench() {
    local name="$1" pry_src="$2" c_src="$3"
    echo -e "\n${BLU}══════════════════════════════════════════════${NC}"
    echo -e "${BOLD}  $name${NC}"
    echo -e "${BLU}══════════════════════════════════════════════${NC}"

    local pry_bin="/tmp/bench_${name// /_}_pride"
    local c_bin="/tmp/bench_${name// /_}_c"

    # Build Pride (--maxout)
    "$PRIDEC" --maxout "$pry_src" -o "$pry_bin" 2>&1 | grep -E "error|Built" || true

    # Build C (O3 + lto)
    "$GCC" -O3 -march=native -flto "$c_src" -o "$c_bin" -lm 2>&1

    # Run both 3 times, take median
    local pry_times=() c_times=()
    for _ in 1 2 3; do
        pry_times+=( $("$pry_bin") )
        c_times+=( $("$c_bin") )
    done

    # Sort and pick median
    pry_median=$(printf '%s\n' "${pry_times[@]}" | sort -n | sed -n '2p')
    c_median=$(printf '%s\n' "${c_times[@]}" | sort -n | sed -n '2p')

    local ratio=$(awk "BEGIN{printf \"%.2f\", $pry_median/$c_median}")
    local pct=$(awk "BEGIN{printf \"%.1f\", ($pry_median-$c_median)/$c_median*100}")

    echo -e "  Pride:  ${BOLD}${pry_median} ns${NC}"
    echo -e "  C(gcc): ${BOLD}${c_median} ns${NC}"
    if awk "BEGIN{exit !($ratio <= 1.05)}"; then
        echo -e "  Ratio:  ${GRN}${ratio}x${NC}  (${pct}%)  ✓ C-competitive"
    elif awk "BEGIN{exit !($ratio <= 1.20)}"; then
        echo -e "  Ratio:  ${YEL}${ratio}x${NC}  (${pct}%)  ~ within 20%"
    else
        echo -e "  Ratio:  ${RED}${ratio}x${NC}  (${pct}%)  ✗ slower"
    fi
}

echo -e "${BOLD}Pride vs C — Performance Suite${NC}"
echo -e "  Pride:   --maxout (O3+WPD+GVN+ICF+ThinLTO)"
echo -e "  C:       gcc -O3 -march=native -flto"

run_bench "stack_vm"   bench/stack_vm.pie   bench/stack_vm.c
run_bench "sum_array"  bench/sum_array.pie  bench/sum_array.c
run_bench "fib"        bench/fib.pie        bench/fib.c
run_bench "sieve"      bench/sieve.pie      bench/sieve.c
run_bench "matmul"     bench/matmul.pie     bench/matmul.c

echo ""
