/*
 pear_a2 — the a2 driver: AIR in, AIR′ out.

 Reads a `.air` file, runs the a2 analyses, and writes the result back out
 as `.air`. Input and output are the same form, which is what PEAR.md means
 by AIR → AIR′: a2 refines, it does not change representation.

 Reading a FILE rather than being handed an in-memory module from pearc is
 deliberate and is D3 working as intended. It means a2 can be run against
 IR that no compiler produced — a hand-written fixture, a reduced test case
 — and it proves the serialised form really is complete enough to carry a
 program between stages. A stage that could only run on a live pointer
 would make that claim untestable.

 Usage:
   pear_a2 <file.air>              analyse, print AIR'
   pear_a2 --stats <file.air>      analyse, print metrics only
   pear_a2 --verify-facts <f.air>  report D1 fact survival
   pear_a2 --no-range <file.air>   skip R (to isolate a pass)
   pear_a2 --no-mem <file.air>     skip M
   pear_a2 --no-dce <file.air>     skip DCE
   pear_a2 --time <file.air>       per-pass wall time

 Exit: 0 clean · 1 the result failed verification · 2 could not read input.
*/

module pear_a2;

import pear_air;
import pear_air_print;
import pear_air_parse;
import pear_erm;
import pear_verify;
import pear_a2_facts;
import pear_a2_range;
import pear_a2_memssa;
import pear_a2_sccp;
import pear_a2_dce;
import pfront_core;

extern fn int   printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn void  free(void* p);
extern fn void* fopen(char* path, char* mode);
extern fn usz   fread(void* p, usz esize, usz count, void* f);
extern fn int   fclose(void* f);
extern fn int   fseek(void* f, long off, int whence);
extern fn long  ftell(void* f);

fn bool arg_is(String a, String want)
{
    if (a.len != want.len) { return false; }
    for (usz i = 0; i < a.len; i++) { if (a[i] != want[i]) { return false; } }
    return true;
}

fn char* read_all(char* path, usz* out_len)
{
    void* f = fopen(path, "rb");
    if (f == null) { return null; }
    fseek(f, 0, 2);
    long total = ftell(f);
    fseek(f, 0, 0);
    if (total < 0) { fclose(f); return null; }
    char* buf = (char*)malloc((usz)total + 1);
    if (buf == null) { fclose(f); return null; }
    usz got = fread((void*)buf, 1, (usz)total, f);
    buf[got] = (char)0;
    *out_len = got;
    fclose(f);
    return buf;
}

fn int main(String[] args)
{
    char* path = null;
    bool stats_only = false;
    bool want_facts = false;
    bool do_range = true;
    bool do_mem = true;
    bool do_dce = true;
    bool do_sccp = true;

    for (usz i = 1; i < args.len; i++)
    {
        String a = args[i];
        if (arg_is(a, "--stats"))        { stats_only = true; continue; }
        if (arg_is(a, "--verify-facts")) { want_facts = true; stats_only = true; continue; }
        if (arg_is(a, "--no-range"))     { do_range = false; continue; }
        if (arg_is(a, "--no-mem"))       { do_mem = false; continue; }
        if (arg_is(a, "--no-dce"))       { do_dce = false; continue; }
        if (arg_is(a, "--no-sccp"))      { do_sccp = false; continue; }
        path = (char*)a.ptr;
    }

    if (path == null)
    {
        printf("usage: pear_a2 [--stats] [--verify-facts] [--no-range] [--no-mem] [--no-sccp] [--no-dce] <file.air>\n");
        return 2;
    }

    usz len = 0;
    char* src = read_all(path, &len);
    if (src == null) { printf("pear_a2: cannot read %s\n", path); return 2; }

    // Everything heap-allocated: Interner alone is ~1.4 MB and C3 caps a
    // stack object at 64 KB.
    pfront_core::Arena* arena = (pfront_core::Arena*)malloc(pfront_core::Arena::size);
    if (arena == null || !arena.init()) { printf("oom\n"); return 2; }
    pfront_core::Interner* it =
        (pfront_core::Interner*)malloc(pfront_core::Interner::size);
    if (it == null) { printf("oom\n"); return 2; }
    it.init(arena);

    pear_air::AirModule* m =
        (pear_air::AirModule*)malloc(pear_air::AirModule::size);
    if (m == null) { printf("oom\n"); return 2; }
    m.init(arena, it, 0);

    usz perrs = 0;
    if (!pear_air_parse::parse_into(m, src, len, &perrs))
    {
        printf("pear_a2: %s: could not parse (%d errors)\n", path, (int)perrs);
        return 2;
    }

    pear_a2_facts::Facts2 facts;
    if (!facts.init(m.value_count + 16)) { printf("oom\n"); return 2; }
    pear_a2_facts::seed_from_module(m, &facts);

    pear_a2_range::RangeStats rs;
    rs.init();
    if (do_range) { pear_a2_range::run(m, &facts, &rs); }

    pear_a2_memssa::MemStats ms;
    ms.init();
    if (do_mem) { pear_a2_memssa::run(m, &facts, &ms); }

    pear_a2_sccp::SccpStats cs;
    cs.init();
    if (do_sccp) { pear_a2_sccp::run(m, &facts, &cs); }

    pear_a2_dce::DceStats ds;
    ds.init();
    if (do_dce) { pear_a2_dce::run(m, &ds); }

    // D1: the table is the durable record, but the PRINTER reads the
    // inline copy, so what is not written back does not reach a3.
    pear_a2_facts::writeback(m, &facts);

    int rc = 0;
    if (stats_only)
    {
        printf("=== a2 (%s) ===\n", path);
        if (do_range) { pear_a2_range::print_stats(&rs); }
        if (do_mem)   { pear_a2_memssa::print_stats(&ms); }
        if (do_sccp)  { pear_a2_sccp::print_stats(&cs); }
        if (do_dce)   { pear_a2_dce::print_stats(&ds); }

        if (want_facts)
        {
            pear_a2_facts::Survival sv;
            pear_a2_facts::measure(m, &facts, &sv);
            printf("=== D1 fact survival ===\n");
            pear_a2_facts::print_survival(&facts, &sv);
        }

        /*
         a2 must not be able to report a clean run while having produced
         broken IR. Verifying the OUTPUT here, in the same invocation, is
         what makes every metric above conditional on the result still
         being a well-formed program.
        */
        pear_verify::Report rep;
        pear_verify::verify(m, &rep);
        printf("=== AIR' verify ===\n");
        pear_verify::print_report(&rep);
        if (rep.errors > 0) { rc = 1; }
    }
    else
    {
        pear_air_print::dump(m, true);
    }

    facts.destroy();
    m.destroy();
    free((void*)m);
    free((void*)src);
    return rc;
}
