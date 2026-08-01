#!/bin/bash
# scripts/detect_c_std.sh — adaptive C standard detection for the Pride C runtime
# (runtime/compiler_rt.c, runtime/compiler_rt_arch.c).
#
# Probes the host C compiler ($CC) for the newest usable ISO C standard and
# prints the matching -std= flag on stdout. Priority order (newest first):
#
#   1. C23      : -std=c23, then -std=c2x          (GCC 15+ / Clang 19+)
#   2. C18 / C17: -std=gnu18, -std=c18, -std=c17   (GCC 8–14 / Clang 8–18)
#   3. C11      : -std=c11                         (minimal baseline)
#
# A candidate is accepted only if the compiler (a) recognises the flag and
# (b) reports a matching __STDC_VERSION__ for the *final* standard. This is
# what keeps e.g. GCC 12–14 on -std=gnu18 instead of their draft -std=c2x
# mode (which reports 202000L, not the final 202311L), matching the
# compiler-generation mapping above.
#
# Direct mode (prints to stdout, diagnostics to stderr):
#   bash scripts/detect_c_std.sh          # selected flag,  e.g. "-std=gnu18"
#   bash scripts/detect_c_std.sh --cc     # resolved C compiler, e.g. "cc"
#   bash scripts/detect_c_std.sh --table  # "compiler flag" pair
#
# Library mode (no side effects when sourced):
#   source scripts/detect_c_std.sh
#   CC_BIN="$(pride_resolve_cc)"
#   CSTD="$(pride_detect_c_std "$CC_BIN")"   # or omit arg to resolve internally
#
# Environment knobs:
#   CC            C compiler to probe; first word must exist on PATH
#                 (default: first of cc, gcc, clang found on PATH)
#   PRIDE_C_STD   Force this -std= flag and skip probing entirely
#   CSTD_VERBOSE  Non-empty → log probe decisions to stderr
#
# Notes:
#   * Probe programs are fed to the compiler via stdin (`-x c -fsyntax-only`),
#     so no temp files, no traps, no code generation — safe to source from
#     `set -e` / `set -o pipefail` scripts; all probes run inside conditions.
#   * `$CC` may be multi-word (e.g. "ccache gcc"), autoconf-style.

# ── Internals ────────────────────────────────────────────────────────────────

_pride_cstd_log() {
    # shellcheck disable=SC2086
    { [ -n "${CSTD_VERBOSE:-}" ] && printf '%s\n' "$*" >&2; } || :
}

# Usage: _pride_cstd_probe <cc> <flag> <min __STDC_VERSION__ (e.g. 202311L)>
# Succeeds iff <cc> accepts <flag> AND the translation unit compiled under it
# reports __STDC_VERSION__ >= the given final-standard value.
_pride_cstd_probe() {
    # Deliberately unquoted $1: CC may be multi-word ("ccache gcc").
    # shellcheck disable=SC2086
    printf '#if !defined(__STDC_VERSION__) || __STDC_VERSION__ < %s\n#error "compiler does not provide this standard in final form"\n#endif\nint main(void){return 0;}\n' "$3" \
        | $1 "$2" -x c -fsyntax-only - >/dev/null 2>&1
}

# ── Public API ───────────────────────────────────────────────────────────────

# Resolve the C compiler: $CC if usable, else first of cc/gcc/clang on PATH.
pride_resolve_cc() {
    if [ -n "${CC:-}" ]; then
        # shellcheck disable=SC2086
        if command -v ${CC%% *} >/dev/null 2>&1; then
            printf '%s\n' "$CC"
            return 0
        fi
        _pride_cstd_log "c-std: CC='$CC' not found on PATH — falling back"
    fi
    local c
    for c in cc gcc clang; do
        if command -v "$c" >/dev/null 2>&1; then
            printf '%s\n' "$c"
            return 0
        fi
    done
    printf '%s\n' "cc"   # nothing found; let the build fail with its own error
}

# Print the newest -std= flag supported by the given compiler (or $CC /
# auto-resolved when no argument is passed).
pride_detect_c_std() {
    if [ -n "${PRIDE_C_STD:-}" ]; then
        _pride_cstd_log "c-std: PRIDE_C_STD override → $PRIDE_C_STD"
        printf '%s\n' "$PRIDE_C_STD"
        return 0
    fi

    local cc="${1:-}"
    [ -n "$cc" ] || cc="$(pride_resolve_cc)"
    local flag

    # Tier 1 — C23 (final): GCC 15+ / Clang 19+.
    for flag in -std=c23 -std=c2x; do
        if _pride_cstd_probe "$cc" "$flag" 202311L; then
            _pride_cstd_log "c-std: $cc accepts $flag (__STDC_VERSION__ >= 202311L) — C23"
            printf '%s\n' "$flag"
            return 0
        fi
        _pride_cstd_log "c-std: $cc does not provide final C23 via $flag"
    done

    # Tier 2 — C18 / C17: GCC 8–14 / Clang 8–18.
    for flag in -std=gnu18 -std=c18 -std=c17; do
        if _pride_cstd_probe "$cc" "$flag" 201710L; then
            _pride_cstd_log "c-std: $cc accepts $flag (__STDC_VERSION__ >= 201710L) — C18/C17"
            printf '%s\n' "$flag"
            return 0
        fi
        _pride_cstd_log "c-std: $cc rejects $flag"
    done

    # Tier 3 — C11 baseline (returned unconditionally).
    _pride_cstd_log "c-std: falling back to -std=c11 (minimal baseline)"
    if ! _pride_cstd_probe "$cc" -std=c11 201112L; then
        _pride_cstd_log "c-std: WARNING: $cc does not appear to accept even -std=c11"
    fi
    printf '%s\n' "-std=c11"
}

# ── Direct mode ──────────────────────────────────────────────────────────────

if [ "${BASH_SOURCE[0]:-$0}" = "$0" ]; then
    case "${1:-}" in
        "")
            pride_detect_c_std
            ;;
        --cc)
            pride_resolve_cc
            ;;
        --table)
            _cc="$(pride_resolve_cc)"
            printf '%s %s\n' "$_cc" "$(pride_detect_c_std "$_cc")"
            ;;
        -h|--help)
            sed -n '2,40p' "$0" | sed 's/^# \{0,1\}//'
            ;;
        *)
            echo "usage: bash $0 [--cc|--table]" >&2
            exit 2
            ;;
    esac
fi
