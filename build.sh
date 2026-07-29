#!/bin/bash
# Pride compiler build script — busts c3c's path-based object cache
set -e
SRCDIR="$(cd "$(dirname "$0")" && pwd)"
TMPDIR="$(mktemp -d /tmp/pride_build_XXXXXX)"
trap "rm -rf $TMPDIR" EXIT
cp "$SRCDIR"/*.c3 "$TMPDIR/"
cd "$TMPDIR"
/tmp/c3/c3c compile --use-stdlib=no \
    lexer.c3 ast.c3 parser.c3 resolve.c3 typecheck.c3 effectcheck.c3 \
    lint.c3 integrity.c3 ssi.c3 ssi_ir.c3 sasi.c3 sasi_opt.c3 \
    rewrite.c3 pgen.c3 stage.c3 irdl_msp.c3 mono.c3 codegen.c3 pride.c3 \
    -o "$SRCDIR/pride" 2>&1 | grep -E "^.*[Ee]rror" | grep -v "@private|Warning" || true
chmod +x "$SRCDIR/pride"
echo "Built: $(md5sum $SRCDIR/pride | cut -c1-8)..."
