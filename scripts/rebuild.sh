#!/bin/bash
# scripts/rebuild.sh — full rebuild of the Pride compiler + runtime objects.
#
# Environment knobs (all optional):
#   C3C=/path/to/c3c      C3 compiler binary      (default: /home/user/c3/c3c)
#   CC=cc                 C compiler for runtime  (default: first of cc/gcc/clang)
#   PRIDE_C_STD=-std=xxx  Force the C standard flag for the runtime, skipping
#                         adaptive detection (default: probe newest supported:
#                         c23 → c2x → gnu18 → c18 → c17 → c11)
#
# Toolchain policy: the verified pipeline is LLVM 22.1.x. This script installs
# the -22 toolchain via apt.llvm.org when missing and no unversioned LLVM is
# present; on hosts without sudo/network it simply uses what is on PATH
# (the compiler binary itself adapts: it prefers 22-pinned tool names and
# falls back to unversioned ones — see resolve_toolchain() in pride.c3).
set -e
cd "$(dirname "$0")/.."
PRIDE_DIR="$(pwd)"

C3C="${C3C:-/home/user/c3/c3c}"

# Adaptive C toolchain resolution for the runtime objects (shared library:
# honours $CC, falls back cc → gcc → clang, probes the newest -std= flag).
# shellcheck source=detect_c_std.sh
source "$PRIDE_DIR/scripts/detect_c_std.sh"
CC="$(pride_resolve_cc)"

echo "=== Toolchain check ==="
if ! command -v llvm-as-22 >/dev/null 2>&1 && ! command -v llvm-as >/dev/null 2>&1; then
    echo "No LLVM found — attempting apt.llvm.org install of LLVM 22..."
    if command -v sudo >/dev/null 2>&1; then
        wget -qO- https://apt.llvm.org/llvm-snapshot.gpg.key \
            | sudo tee /etc/apt/trusted.gpg.d/apt.llvm.org.asc >/dev/null
        . /etc/os-release
        echo "deb http://apt.llvm.org/${VERSION_CODENAME}/ llvm-toolchain-${VERSION_CODENAME}-22 main" \
            | sudo tee /etc/apt/sources.list.d/llvm-22.list >/dev/null
        sudo apt-get update -qq && sudo apt-get install -y -qq llvm-22 clang-22 lld-22
    else
        echo "ERROR: no LLVM and no sudo to install it. Install LLVM (22 preferred) on PATH." >&2
        exit 1
    fi
fi
# Unversioned aliases: the compiler and test harnesses probe 22-pinned names
# first, so only provide aliases when the pinned ones are absent.
if ! command -v llvm-as-22 >/dev/null 2>&1; then
    for t in llvm-as opt llc ld.lld clang; do
        command -v "$t" >/dev/null 2>&1 || { echo "ERROR: $t missing from PATH" >&2; exit 1; }
    done
fi
"$C3C" --version 2>&1 | head -1

echo "=== Building compiler (-O3) ==="
BUILD_DIR="$(mktemp -d /tmp/pride_build_XXXX)"
trap 'rm -rf "$BUILD_DIR"' EXIT
cp "$PRIDE_DIR"/*.c3 "$BUILD_DIR/"
cd "$BUILD_DIR"
"$C3C" compile -O3 \
    lexer.c3 ast.c3 parser.c3 resolve.c3 typecheck.c3 effectcheck.c3 \
    lint.c3 integrity.c3 ssi.c3 ssi_ir.c3 sasi.c3 sasi_opt.c3 \
    rewrite.c3 pgen.c3 stage.c3 irdl_msp.c3 mono.c3 codegen.c3 pride.c3 \
    -o "$PRIDE_DIR/pride" 2>&1 | grep -iE "error|linked" || true
chmod +x "$PRIDE_DIR/pride"
cd "$PRIDE_DIR"
./pride --version

echo "=== Building runtime objects ==="
CSTD="$(pride_detect_c_std "$CC")"
echo "C runtime toolchain: $CC $CSTD (adaptive)"
CFLAGS="-O2 $CSTD -pthread -fPIC -fno-strict-aliasing -msse4.1 \
 -ffunction-sections -fdata-sections -Wno-unused-parameter -Wno-unused-function"
$CC $CFLAGS -c runtime/compiler_rt.c      -o runtime/compiler_rt.o
$CC $CFLAGS -c runtime/compiler_rt_arch.c -o runtime/compiler_rt_arch.o

echo "=== Done. Gates: ==="
echo "  bash conformance/run.sh      # expect: pass=242 fail=0"
echo "  bash tests/run_exec.sh       # expect: pass=19 fail=0"
