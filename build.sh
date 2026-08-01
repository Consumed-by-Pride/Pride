#!/bin/bash
# Pride compiler build script — busts c3c's path-based object cache
set -e
SRCDIR="$(cd "$(dirname "$0")" && pwd)"
TMPDIR="$(mktemp -d /tmp/pride_build_XXXXXX)"
trap "rm -rf $TMPDIR" EXIT
cp "$SRCDIR"/*.c3 "$TMPDIR/"
cd "$TMPDIR"
/tmp/c3/c3c compile --use-stdlib=no \
    lexer.c3 ast.c3 parser.c3 cstats.c3 resolve.c3 typecheck.c3 effectcheck.c3 \
    lint.c3 integrity.c3 ssi.c3 ssi_ir.c3 sasi.c3 sasi_opt.c3 \
    rewrite.c3 pgen.c3 stage.c3 irdl_msp.c3 mono.c3 codegen.c3 \
    modal.c3 msp.c3 parse_modal.c3 pride.c3 \
    -o "$SRCDIR/pride" 2>&1 | tee "$TMPDIR/build.log" | grep -E "[Ee]rror" || true

# The build used to pipe c3c's output through grep and then `|| true`, so a
# compile failure exited 0 and printed "Built:" over a stale binary. Three
# modules (modal, msp, parse_modal) had been missing from the source list for
# an unknown length of time and nothing noticed. Check for real now.
if grep -qE "[Ee]rror:" "$TMPDIR/build.log"; then
    echo "BUILD FAILED - see errors above" >&2
    exit 1
fi
[ -f "$SRCDIR/pride" ] || { echo "BUILD FAILED - no output binary" >&2; exit 1; }
chmod +x "$SRCDIR/pride"
echo "Built: $(md5sum $SRCDIR/pride | cut -c1-8)..."
