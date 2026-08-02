/*
 a2 — the fact table of PEAR.md D1, and the survival accounting that makes
 `ERM` a measurement rather than a claim.

 ── Why a side table at all ─────────────────────────────────────────────

 a1 carries facts INLINE, on the value. That is right for a1: it builds
 each value once and never rewrites it, so an inline fact cannot go stale.

 From a2 onward terms are rewritten constantly — a σ is folded away, a φ
 collapses, a value is replaced by a constant — and every rewrite is a
 chance for the fact to be dropped on the floor. D1's answer is that facts
 live in ONE table keyed by ORIGIN, and origin is the thing conversions
 copy. When a2 folds `%7` into a constant, whatever was learned about
 `%7`'s lineage is still in the table under the same key, and a5 can still
 find it.

 ── What "survival" means here, precisely ───────────────────────────────

 It would be easy, and dishonest, to report survival as "entries still in
 the table", which is 100% by construction: nothing removes entries. That
 number would be pure decoration.

 So survival is measured against REACHABILITY instead: an entry survives
 only if some value still present in the module names that origin. A fact
 about a lineage that no live value descends from is DEAD, and it is
 counted as dead however good the fact was. That is the number that says
 whether ERM works, and it is reported whether it flatters or not.
*/

module pear_a2_facts;

import pear_air;
import pear_erm;
import pfront_core;

alias Air  = pear_air::AirModule;
alias Val  = pear_air::AirValue;
alias Blk  = pear_air::AirBlock;
alias Fn   = pear_air::AirFunc;
alias Op   = pear_air::AirOp;

extern fn int   printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn void* realloc(void* p, usz size);
extern fn void  free(void* p);

// ════════════════════════════════════════════════════════════════════════
// THE TABLE
// ════════════════════════════════════════════════════════════════════════

/*
 pear_erm::FactTable already implements the storage D1 asks for — keyed by
 origin, with meet-based refinement. This wraps it with the accounting a2
 needs and does not duplicate it.

 `established_by` records WHICH analysis put each entry in, so a survival
 report can say "range analysis contributed 900 facts and 890 of them are
 still reachable" rather than one opaque total. Without it, a pass that
 contributes nothing is indistinguishable from one that contributes
 everything.
*/
enum FactSource : int (String mnemonic)
{
    FS_NONE   { "-" },
    FS_A1     { "a1" },        // seeded during lowering
    FS_RANGE  { "range" },     // a2 range analysis
    FS_MEMSSA { "memssa" },    // a2 memory SSA
    FS_SCCP   { "sccp" }       // a2 conditional constant propagation
}

struct Facts2
{
    pear_erm::FactTable t;
    FactSource* source;        // parallel to t, one per origin
    usz         source_cap;

    // Absolute counts, per PEAR.md's rule that a percentage invites
    // shipping the remainder.
    usz  from_a1;
    usz  from_range;
    usz  from_memssa;
    usz  from_sccp;
}

fn bool Facts2.init(Facts2* f, usz n)
{
    if (!f.t.init(n)) { return false; }
    f.source_cap = n == 0 ? 64 : n;
    f.source = (FactSource*)malloc(f.source_cap * FactSource::size);
    if (f.source == null) { f.source_cap = 0; return false; }
    for (usz i = 0; i < f.source_cap; i++) { f.source[i] = FactSource.FS_NONE; }
    f.from_a1 = 0; f.from_range = 0; f.from_memssa = 0; f.from_sccp = 0;
    return true;
}

fn void Facts2.destroy(Facts2* f)
{
    f.t.destroy();
    if (f.source != null) { free((void*)f.source); f.source = null; }
    f.source_cap = 0;
}

fn bool Facts2.ensure_source(Facts2* f, usz idx)
{
    if (idx < f.source_cap) { return true; }
    usz nc = f.source_cap == 0 ? 64 : f.source_cap;
    while (nc <= idx) { nc = nc * 2; }
    FactSource* p = (FactSource*)realloc((void*)f.source, nc * FactSource::size);
    if (p == null) { return false; }
    for (usz i = f.source_cap; i < nc; i++) { p[i] = FactSource.FS_NONE; }
    f.source = p;
    f.source_cap = nc;
    return true;
}

fn void Facts2.count_source(Facts2* f, FactSource s)
{
    switch (s)
    {
        case FS_A1:     f.from_a1 = f.from_a1 + 1;
        case FS_RANGE:  f.from_range = f.from_range + 1;
        case FS_MEMSSA: f.from_memssa = f.from_memssa + 1;
        case FS_SCCP:   f.from_sccp = f.from_sccp + 1;
        default: break;
    }
}

/*
 Record a fact about an origin, attributed to the analysis that found it.

 MEET, not overwrite: two analyses that both learn something about the
 same lineage are both right, so the intersection is the sound merge.
 pear_erm::FactTable.refine already does this correctly, including the
 detail that nullness only tightens from unknown.
*/
/*
 Is this value's knowledge EDGE-LOCAL rather than true of its lineage?

 A σ names the value on one outgoing edge of a branch and a π names it on
 the non-faulting path of an operation. Both deliberately INHERIT their
 source's origin (D1), so that a fact learned about the refined name can
 still be attributed to the lineage. That is right for attribution and
 wrong for the fact itself: `x` on the `x < 0` edge is in [MIN,-1], and
 `x` before the branch is not.

 Recorded here rather than filtered at each of the four learn() call
 sites, because a fact that leaks from one of them is not recoverable
 later -- the table has no record of which edge it came from.
*/
fn bool origin_local_only(Air* m, uint vid)
{
    Val* v = m.val(vid);
    if (v == null) { return false; }
    return v.op == pear_air::AirOp.AIR_SIGMA || v.op == pear_air::AirOp.AIR_PI;
}

fn void Facts2.learn(Facts2* f, uint origin, pear_erm::Facts fact, FactSource src)
{
    if (origin == pear_air::AIR_NO_ORIGIN) { return; }
    if (!pear_erm::facts_known(&fact)) { return; }
    if (!f.ensure_source((usz)origin)) { return; }

    /*
     Attribute the LINEAGE to the first analysis that learned anything
     about it. A later refinement of the same origin is not a new fact.

     The per-source counters and `established` therefore count the same
     thing -- ORIGINS, not values -- and must agree. They did not: the
     counters were incremented once per learn() call while `established`
     counted distinct origins, so on stdlib/io.pie the breakdown read
     "established: 984 (a1 1671, range 29, memssa 75)". 1,775 parts of a
     984 whole, because sigma and pi INHERIT their source's origin (D1),
     so many values legitimately share one lineage and each of them
     called learn().

     The guard below already existed for `source`; the counter increment
     just sat outside it.
    */
    if (f.source[origin] == FactSource.FS_NONE)
    {
        f.source[origin] = src;
        f.count_source(src);
    }
    f.t.refine(origin, fact);
}

fn pear_erm::Facts Facts2.get(Facts2* f, uint origin)
{
    return f.t.get(origin);
}

// ════════════════════════════════════════════════════════════════════════
// SEEDING FROM a1
// ════════════════════════════════════════════════════════════════════════

/*
 Lift a1's inline per-value facts into the origin-keyed table.

 This is where the two representations meet, and it is the only place that
 reads a1's inline form. Everything after this point in a2 reads the table.
*/
fn void seed_from_module(Air* m, Facts2* f)
{
    for (usz i = 1; i < m.value_count; i++)
    {
        Val* v = &m.values[i];
        if (v.block == pear_air::AIR_NO_BLOCK) { continue; }
        if (v.is_phi_hole) { continue; }
        /*
         A σ/π refinement is true on ONE EDGE. Feeding it into the
         origin-keyed table, which σ and π share with their source by
         construction, made writeback() meet an edge-local range into the
         unrefined value that is live on both edges.

         Caught by running a2 twice: the second pass gave a call result
         `range=MIN..-1` inherited from the `< 0` edge of a branch below
         it, and then folded a branch on the strength of it. a2 was not
         idempotent, which is the observable symptom of an unsound fact.
        */
        if (origin_local_only(m, (uint)i)) { continue; }
        f.learn(v.origin, v.facts, FactSource.FS_A1);
    }
}

/*
 Write the table's knowledge back onto the values.

 Needed because the PRINTER reads the inline form, so a fact that only
 exists in the table would not appear in the serialised `.air` and would
 not survive to a3 — which is precisely the failure D1 exists to prevent.
 The table is the durable record across rewrites; the inline copy is how
 it reaches the file.

 A value's own facts are MET with its lineage's, never replaced: the value
 may know something more specific than the lineage as a whole (a σ knows
 its edge's refinement), and overwriting would discard it.
*/
fn void writeback(Air* m, Facts2* f)
{
    for (usz i = 1; i < m.value_count; i++)
    {
        Val* v = &m.values[i];
        if (v.block == pear_air::AIR_NO_BLOCK) { continue; }
        if (v.is_phi_hole) { continue; }

        /*
         A σ/π must not RECEIVE its lineage's facts either.

         Blocking the write side alone was not enough. σ and π share their
         source's origin by construction (D1), so a refinement placed on
         one edge and the unrefined value on another are the same key. The
         write guard stops the edge-local fact entering the table; this
         guard stops the table's accumulated fact being met INTO an
         edge-local name, which is the same unsoundness read backwards.

         The two together are what make the meet below safe. Without this
         half, `for i in 0..16` was miscompiled: the exit σ's
         `[16,MAX]` reached the loop header's φ, SCCP folded `i < 16` to
         false, and DCE deleted the entire loop body -- the function
         returned 0 instead of 120. It only surfaced once a2 iterated to
         a fixpoint, because a single pass never fed the fact back round.
        */
        if (origin_local_only(m, (uint)i)) { continue; }

        pear_erm::Facts lineage = f.get(v.origin);
        if (!pear_erm::facts_known(&lineage)) { continue; }

        /*
         Range: meet. Both are true of this value, so the intersection is
         sound and strictly better than either.

         A contradiction — an empty intersection — is NOT written back as
         bottom. It means one of the two is wrong, and marking the value
         unreachable on the strength of a disagreement would turn an
         analysis bug into deleted code. Keep the value's own range, which
         is the more specific of the two, and leave the value alone.
        */
        pear_erm::Range met = pear_erm::r_meet(v.facts.range, lineage.range);
        if (!met.is_bottom || v.facts.range.is_bottom) { v.facts.range = met; }

        v.facts.bits.zeros = v.facts.bits.zeros | lineage.bits.zeros;
        v.facts.bits.ones  = v.facts.bits.ones  | lineage.bits.ones;
        // Contradictory bits mean the same disagreement; drop the merge
        // rather than claim an impossible value.
        if (pear_erm::kb_conflicts(&v.facts.bits))
        {
            v.facts.bits = pear_erm::kb_unknown();
        }

        if (v.facts.nullness == pear_erm::Nullness.NULL_UNKNOWN)
        {
            v.facts.nullness = lineage.nullness;
        }
        if (v.facts.width == 0) { v.facts.width = lineage.width; }
    }
}

// ════════════════════════════════════════════════════════════════════════
// SURVIVAL — the honest ERM metric
// ════════════════════════════════════════════════════════════════════════

/*
 How many established facts are still attached to something live.

 An origin is REACHED if some value still in the module names it. That is
 the only definition that cannot be gamed: entries never leave the table,
 so counting entries would report 100% survival on a pass that deleted
 every value in the program.
*/
/*
 Three DIFFERENT quantities, which an earlier version of this report
 conflated into one line:

   contributed  origins an analysis ever put a fact into. This is what
                the per-source counters add up to.
   established  origins whose fact is STILL non-trivial when the report
                runs. Strictly smaller: a2 rewrites values, and a fact
                that was interesting about `%7` before constant folding
                may be `range=3..3` on a literal afterwards, which
                facts_known correctly calls trivial.
   reached      established origins still named by a live value.

 The report used to print `established` next to the per-source breakdown,
 so stdlib/io.pie read "established: 984 (a1 1671, range 29, memssa 75)"
 -- 1,775 parts of a 984 whole. Both numbers were right; putting them on
 one line implied they measured the same thing.
*/
struct Survival
{
    usz contributed;     // origins any analysis put a fact into
    usz established;     // ...whose fact is still non-trivial now
    usz reached;         // ...still named by a live value
    usz orphaned;        // ...named by nothing: the fact is unusable
    usz values;          // live values
    usz values_with;     // live values whose lineage carries a fact
    usz values_without;  // live values with nothing known -- reported too
}

fn void measure(Air* m, Facts2* f, Survival* s)
{
    s.contributed = 0; s.established = 0; s.reached = 0; s.orphaned = 0;
    s.values = 0; s.values_with = 0; s.values_without = 0;

    usz n = f.t.cap;
    bool* named = (bool*)malloc(n == 0 ? 1 : n);
    if (named == null) { return; }
    for (usz i = 0; i < n; i++) { named[i] = false; }

    for (usz i = 1; i < m.value_count; i++)
    {
        Val* v = &m.values[i];
        if (v.block == pear_air::AIR_NO_BLOCK) { continue; }
        if (v.is_phi_hole) { continue; }
        s.values = s.values + 1;
        if ((usz)v.origin < n) { named[v.origin] = true; }

        pear_erm::Facts lf = f.get(v.origin);
        if (pear_erm::facts_known(&lf)) { s.values_with = s.values_with + 1; }
        else { s.values_without = s.values_without + 1; }
    }

    for (usz i = 0; i < n; i++)
    {
        if (!f.t.present[i]) { continue; }
        s.contributed = s.contributed + 1;
        pear_erm::Facts ff = f.t.by_origin[i];
        if (!pear_erm::facts_known(&ff)) { continue; }
        s.established = s.established + 1;
        if (named[i]) { s.reached = s.reached + 1; }
        else { s.orphaned = s.orphaned + 1; }
    }
    free((void*)named);
}

fn void print_survival(Facts2* f, Survival* s)
{
    printf("  facts contributed: %d   (a1 %d, range %d, memssa %d, sccp %d)\n",
           (int)s.contributed, (int)f.from_a1, (int)f.from_range,
           (int)f.from_memssa, (int)f.from_sccp);
    printf("  facts non-trivial: %d   (still say something after a2 rewrote)\n",
           (int)s.established);
    printf("  facts reachable  : %d\n", (int)s.reached);
    printf("  facts orphaned   : %d   (lineage no live value descends from)\n",
           (int)s.orphaned);
    printf("  values with facts: %d of %d   (%d know nothing)\n",
           (int)s.values_with, (int)s.values, (int)s.values_without);
}
