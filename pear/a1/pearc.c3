/*
 pearc — the a1 driver. Pride source → AST → AIR.

 Runs pfront's real front end (loader, parser, resolver), then hands the
 resolved AST to pear_build. This is the ONLY place the two halves meet:
 pfront owns the grammar, PEAR owns everything after it (PEAR.md D5).

 Usage:
   pearc [-I dir]... <file.pie>          print the AIR
   pearc --stats <file.pie>              build stats and ERM metrics only
   pearc --verify <file.pie>             run the AIR verifier, exit non-zero on error
   pearc --no-erm <file.pie>             skip ERM inference (for isolating it)

 Exit: 0 clean · 1 AIR verification errors · 2 could not read the input.
*/

module pearc;

import pear_air;
import pear_air_print;
import pear_build;
import pear_erm;
import pear_infer;
import pear_verify;
import pfront_core;
import pfront_resolve;
import pfront_source;

extern fn int   printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn void  free(void* p);

fn bool arg_is(String a, String want)
{
    if (a.len != want.len) { return false; }
    for (usz i = 0; i < a.len; i++) { if (a[i] != want[i]) { return false; } }
    return true;
}

fn int main(String[] args)
{
    char* path = null;
    char*[16] roots;
    usz root_count = 0;
    bool stats_only = false;
    bool want_verify = false;
    bool run_erm = true;
    bool show_miss = false;

    for (usz i = 1; i < args.len; i++)
    {
        String a = args[i];
        if (arg_is(a, "-I") && i + 1 < args.len)
        {
            i = i + 1;
            if (root_count < 16) { roots[root_count] = (char*)args[i].ptr; root_count++; }
            continue;
        }
        if (arg_is(a, "--stats"))  { stats_only = true; continue; }
        if (arg_is(a, "--verify")) { want_verify = true; continue; }
        if (arg_is(a, "--no-erm")) { run_erm = false; continue; }
        if (arg_is(a, "--miss"))   { show_miss = true; continue; }
        path = (char*)a.ptr;
    }

    if (path == null)
    {
        printf("usage: pearc [-I dir]... [--stats] [--verify] [--no-erm] [--miss] <file.pie>\n");
        return 2;
    }

    // ── pfront front end ────────────────────────────────────────────────
    // Everything is heap-allocated: C3 caps a stack object at 64 KB and
    // Interner alone is ~1.4 MB.
    pfront_core::Arena* arena = (pfront_core::Arena*)malloc(pfront_core::Arena::size);
    if (arena == null || !arena.init()) { printf("oom\n"); return 2; }

    pfront_core::Interner* it =
        (pfront_core::Interner*)malloc(pfront_core::Interner::size);
    if (it == null) { printf("oom\n"); return 2; }
    it.init(arena);

    pfront_core::DiagBag* diags =
        (pfront_core::DiagBag*)malloc(pfront_core::DiagBag::size);
    if (diags == null) { printf("oom\n"); return 2; }
    diags.init();
    diags.advisories = false;      // Pride is untyped; advice is opt-in.

    pfront_resolve::Loader* ld =
        (pfront_resolve::Loader*)malloc(pfront_resolve::Loader::size);
    if (ld == null) { printf("oom\n"); return 2; }
    ld.init(arena, it, diags);
    for (usz i = 0; i < root_count; i++) { ld.add_root(roots[i]); }

    pfront_core::Module* entry = ld.load_entry(path);
    if (entry == null || entry.ast == null)
    {
        printf("pearc: could not load %s\n", path);
        return 2;
    }

    pfront_resolve::Resolver* rs =
        (pfront_resolve::Resolver*)malloc(pfront_resolve::Resolver::size);
    if (rs != null)
    {
        rs.init(arena, it, diags, ld);
        rs.resolve_all();
    }

    /*
     Front-end diagnostics are REPORTED but do not stop the lowering.
     Pride is untyped and the compiler must never reject on types; an
     unresolved name becomes an explicit AIR_UNKNOWN rather than a failure,
     which is what lets a1 be run over the whole stdlib to measure coverage
     instead of stopping at the first gap.
    */
    if (diags.error_count > 0)
    {
        printf("; note: %d front-end errors; lowering anyway\n", (int)diags.error_count);
    }

    // ── a1: AST -> AIR ──────────────────────────────────────────────────
    pear_air::AirModule* m =
        (pear_air::AirModule*)malloc(pear_air::AirModule::size);
    if (m == null) { printf("oom\n"); return 2; }
    m.init(arena, it, entry.name_id);

    pear_build::BuildStats bs;
    pear_build::build_module(m, entry.ast, it, &bs);

    pear_infer::ErmStats es;
    if (run_erm) { pear_infer::run(m, &es); } else { es.init(); }

    int rc = 0;
    if (want_verify || stats_only)
    {
        pear_verify::Report rep;
        pear_verify::verify(m, &rep);
        printf("=== a1 build (%s) ===\n", path);
        pear_build::print_build_stats(&bs);
        if (show_miss) { pear_build::print_miss_histogram(&bs); }
        printf("=== AIR verify ===\n");
        pear_verify::print_report(&rep);
        if (run_erm)
        {
            printf("=== ERM ===\n");
            pear_infer::print_stats(&es);
        }
        if (rep.errors > 0) { rc = 1; }
    }

    if (!stats_only) { pear_air_print::dump(m, true); }

    m.destroy();
    free((void*)m);
    return rc;
}
