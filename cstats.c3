// cstats.c3 — Compiler pass instrumentation: per-pass CPU-time accounting
// Implementation language: C3 (host).
//
// Pride's pipeline (lexer → parser → resolve → typecheck → effectcheck →
// lint → integrity → stage → irdl → mono → ssi → ssi_ir → sasi → sasi_opt →
// codegen) is driven straight-line from pride.c3. This module provides the
// tiny, dependency-free registry that lets the driver answer the question
// "where does compile time go?" without pulling in a profiler:
//
//   long t0 = cstats::now();
//   <run one pass>
//   cstats::record_pass((char*)"resolve", t0);
//   ...
//   if (time_passes) cstats::print_report();
//
// Design constraints (matching the rest of the compiler):
//   * Zero allocations, zero syscalls on the hot path — one clock() call at
//     pass begin and one at pass end, O(#passes) table lookup at record time.
//   * Fixed-capacity registry (one row per pipeline pass, 64 is plenty;
//     extras fold into a spill row instead of being silently dropped).
//   * Pass names are string literals with static storage duration; only the
//     pointer is kept, nothing is copied.
//   * CPU time (clock(3)), so I/O waits outside the compiler process don't
//     pollute the numbers. On Linux/glibc CLOCKS_PER_SEC is 1e6 (one tick ==
//     one microsecond): raw tick deltas are stored directly as microseconds.
//
// Aggregation semantics: recording the same name twice ACCUMULATES into one
// row (a pass run per-function still gets one line). The report prints rows
// in pipeline (registration) order — the order in which passes run — rather
// than sorted by cost, because the primary use is eyeballing the pipeline.

module cstats;

extern fn long clock();                       // libc clock(3): CPU time
extern fn int  printf(char* fmt, ...);

// linux/glibc: CLOCKS_PER_SEC == 1e6, so one clock() tick == one microsecond
// and deltas can be stored/printed as µs without conversion.
const long TICKS_PER_SEC  = 1000000;
const usz  CSTATS_MAX_PASSES = 64;            // one row per pipeline pass
const usz  CSTATS_SPILL      = CSTATS_MAX_PASSES - 1;  // overflow bucket row

// ── Registry state (zero-initialised globals; name pointers are literals) ──

char*[CSTATS_MAX_PASSES] g_pass_name;         // name pointer (static storage)
usz[CSTATS_MAX_PASSES]   g_pass_nlen;         // cached name length (no NUL)
ulong[CSTATS_MAX_PASSES] g_pass_micros;       // accumulated CPU microseconds
usz[CSTATS_MAX_PASSES]   g_pass_calls;        // how many records merged here
usz                        g_count;           // rows in use (<= MAX)
bool                       g_spilled;         // true once the spill row fired

// Current CPU time in clock ticks. Cheap: a single VDSO/libc call.
fn long now()
{
    return clock();
}

// Ticks elapsed since `start`, clamped at zero (clock is per-process CPU time
// and can regress by a tick across threads on exotic hosts; never propagate a
// negative duration into the accumulators).
fn long ticks_since(long start)
{
    long end = clock();
    long d = end - start;
    return d > 0 ? d : 0;
}

// Small strlen for the tag names (kept local: this module must not depend on
// the driver's helpers).
fn usz lit_len(char* s)
{
    usz n = 0;
    if (s == null) return 0;
    while (s[n] != 0) n++;
    return n;
}

// Record one completed pass run: `name` began at `start` (a value from now())
// and just finished. Accumulates into the pass's row (creating it on first
// use). When the table is full, further distinct names fold into a shared
// spill row labelled "<other>" so timing totals stay exact.
fn void record_pass(char* name, long start)
{
    ulong micros = (ulong)ticks_since(start);
    usz nlen = lit_len(name);

    // Find the existing row for this pass name (pointer + length identity;
    // names are literals so pointer equality is the common fast path).
    for (usz i = 0; i < g_count; i++)
    {
        if (g_pass_name[i] == name)
        {
            g_pass_micros[i] += micros;
            g_pass_calls[i]  += 1;
            return;
        }
        if (g_pass_nlen[i] == nlen && name != null && g_pass_name[i] != null)
        {
            bool eq = true;
            for (usz j = 0; j < nlen; j++)
            {
                if (g_pass_name[i][j] != name[j]) { eq = false; break; }
            }
            if (eq)
            {
                g_pass_micros[i] += micros;
                g_pass_calls[i]  += 1;
                return;
            }
        }
    }

    // Register a new row, or fold into the spill bucket when full.
    usz slot = g_count;
    if (slot >= CSTATS_SPILL)
    {
        slot = CSTATS_SPILL;
        if (g_pass_name[slot] == null)
        {
            g_pass_name[slot] = (char*)"<other>";
            g_pass_nlen[slot] = 7;
            g_pass_micros[slot] = 0;
            g_pass_calls[slot] = 0;
        }
        // Ensure table printers (loop bound g_count) include the spill row.
        if (g_count <= slot) g_count = slot + 1;
        g_spilled = true;
        g_pass_micros[slot] += micros;
        g_pass_calls[slot]  += 1;
        return;
    }
    g_pass_name[slot]   = name;
    g_pass_nlen[slot]   = nlen;
    g_pass_micros[slot] = micros;
    g_pass_calls[slot]  = 1;
    g_count++;
}

// Reset the whole registry (single-shot CLI process today; provided so the
// in-process driver used by tooling can time multiple compilations sanely).
fn void reset()
{
    for (usz i = 0; i < g_count; i++)
    {
        g_pass_name[i] = null;
        g_pass_nlen[i] = 0;
        g_pass_micros[i] = 0;
        g_pass_calls[i] = 0;
    }
    g_count = 0;
    g_spilled = false;
}

// Total CPU microseconds across all recorded passes.
fn ulong total_micros()
{
    ulong t = 0;
    for (usz i = 0; i < g_count; i++) t += g_pass_micros[i];
    return t;
}

// Print the pass table between `start` (pipeline begin) and the call moment:
// one row per pass in pipeline order, then the accounted total and the wall
// span. Percentages are hundredths-of-a-percent computed with integer math —
// no float formatting through varargs, and no div-by-zero when total == 0.
fn void print_report(long pipeline_start)
{
    ulong total = total_micros();
    ulong span  = (ulong)ticks_since(pipeline_start);

    printf("\n=== Pass timing (CPU) ===\n");
    printf("  %-16s %12s %10s %8s\n", "pass", "microsec", "millisec", "%");
    for (usz i = 0; i < g_count; i++)
    {
        // ms10 = round(us * 100 / 1000) = hundredths of a millisecond.
        ulong us  = g_pass_micros[i];
        ulong ms10 = (us + 5) / 10;
        ulong pct100 = total > 0 ? (us * 10000 + total / 2) / total : 0;
        printf("  %-16s %12llu %7llu.%02llu %6llu.%02llu%%\n",
               g_pass_name[i] != null ? g_pass_name[i] : (char*)"?",
               us, ms10 / 100, ms10 % 100, pct100 / 100, pct100 % 100);
    }
    if (g_spilled)
    {
        printf("  (over %d distinct passes recorded; the tail is folded into <other>)\n",
               (int)CSTATS_SPILL);
    }
    // Accounted = sum of rows. Span = pipeline begin → now. The gap is
    // per-pass driver glue (AST printing, arg parsing, teardown).
    ulong total_ms10 = (total + 5) / 10;
    ulong span_ms10  = (span + 5) / 10;
    printf("  %-16s %12llu %7llu.%02llu\n", "accounted", total,
           total_ms10 / 100, total_ms10 % 100);
    printf("  %-16s %12llu %7llu.%02llu\n", "span", span,
           span_ms10 / 100, span_ms10 % 100);
    if (span > total)
    {
        ulong gap = span - total;
        printf("  driver glue  : %llu µs (%.2llu%% of span outside recorded passes)\n",
               gap, span > 0 ? (gap * 100 + span / 2) / span : 0);
    }
}

// One-line compact form for the normal summary ("passes: resolve 120µs, ...")
// Used when the full table would be noise but a breadcrumb is still wanted.
fn void print_compact()
{
    printf("pass timing     :");
    for (usz i = 0; i < g_count; i++)
    {
        printf(" %s=%lluµs",
               g_pass_name[i] != null ? g_pass_name[i] : (char*)"?",
               g_pass_micros[i]);
    }
    if (g_count == 0) printf(" (none recorded)");
    printf("\n");
}
