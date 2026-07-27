#!/bin/bash
# scripts/rebuild.sh — full rebuild from scratch each session
# Downloads c3c from the pinned GitHub Release, rebuilds compiler + CRTs
set -e
PRYDE=/home/user/unzipped_content/pryde
C3C_RELEASE="https://github.com/Father-of-Pride/Pride/releases/download/toolchain-c3c-0.8.2/c3c-0.8.2-linux-x86_64-pride-workspace.tar.gz"

echo "=== Installing LLVM 19 ==="
sudo apt-get install -y llvm-19 lld-19 2>/dev/null | tail -2
ln -sf /usr/lib/llvm-19/bin/llvm-as  /usr/local/bin/llvm-as  2>/dev/null || true
ln -sf /usr/lib/llvm-19/bin/llc      /usr/local/bin/llc      2>/dev/null || true
ln -sf /usr/lib/llvm-19/bin/opt      /usr/local/bin/opt      2>/dev/null || true
ln -sf /usr/lib/llvm-19/bin/ld.lld   /usr/local/bin/ld.lld   2>/dev/null || true
ln -sf /usr/lib/llvm-19/bin/llvm-dis /usr/local/bin/llvm-dis 2>/dev/null || true

echo "=== Fetching c3c 0.8.2 from Pride release ==="
mkdir -p /tmp/c3toolchain
cd /tmp/c3toolchain
curl -sL "$C3C_RELEASE" -o c3.tar.gz
tar xf c3.tar.gz
C3C=/tmp/c3toolchain/c3/c3c
$C3C --version 2>&1 | head -1

echo "=== Building compiler ==="
mkdir -p /tmp/pb
cp $PRYDE/*.c3 /tmp/pb/
cd /tmp/pb
$C3C compile --use-stdlib=no \
    lexer.c3 ast.c3 parser.c3 resolve.c3 typecheck.c3 effectcheck.c3 \
    lint.c3 integrity.c3 ssi.c3 ssi_ir.c3 sasi.c3 sasi_opt.c3 \
    rewrite.c3 pgen.c3 stage.c3 irdl_msp.c3 mono.c3 codegen.c3 pride.c3 \
    -o $PRYDE/pride 2>&1 | grep -v "@private" | grep -E "Error|error|linked"
chmod +x $PRYDE/pride

echo "=== Building compiler_rt.o ==="
gcc -O2 -std=c11 -pthread -fPIC -msse4.1 -ffunction-sections -fdata-sections \
    -Wno-unused-parameter -Wno-unused-function -Wno-builtin-declaration-mismatch \
    -c $PRYDE/runtime/compiler_rt.c -o $PRYDE/runtime/compiler_rt.o

echo "=== Building compiler_rt_arch.o ==="
gcc -O2 -std=c11 -pthread -fPIC -ffunction-sections -fdata-sections \
    -Wno-unused-parameter -Wno-unused-function -Wno-builtin-declaration-mismatch \
    -c $PRYDE/runtime/compiler_rt_arch.c -o $PRYDE/runtime/compiler_rt_arch.o

echo "=== Done. Run tests: ==="
echo "  cd $PRYDE && bash conformance/run.sh"
echo "  cd $PRYDE && bash tests/run_exec.sh"
