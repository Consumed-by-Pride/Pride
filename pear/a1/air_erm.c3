/*
 ERM — the Exceptional, Range-bounded, Memory-aware layer of SP-ERM-e-SSI.

 This is the part that is supposed to make `.air` denser than `.ll`, so it
 is worth being precise about what LLVM actually does and where the gap is.

 ── R: range and bit facts ──────────────────────────────────────────────
   .ll   `!range !0` metadata on a load, or `range(i64 0, 100)` on a call
         return / parameter. OPTIONAL, sparse, attached to a handful of
         instruction kinds, and dropped by any pass that does not know to
         preserve it. Known-bits and sign information are not in the text
         at all — they are recomputed by ValueTracking on demand, every
         time, from scratch.
   .air  every version carries lo/hi, a known-zero/known-one bit pair, a
         nullness lattice point and a declared bit width. They are part of
         the value, printed in the text, and round-tripped.

 ── M: memory ───────────────────────────────────────────────────────────
   .ll   MemorySSA is an ANALYSIS. It is constructed, used and thrown away;
         it never appears in a .ll file. Every consumer that wants it pays
         to rebuild it, and nothing downstream of serialisation can see it.
   .air  memory is versioned in the IR itself: every store defines a memory
         version, every load names the version it reads, and a control-flow
         join gets a memory φ. Alias scopes and a no-alias flag ride along.

 ── E: exceptional ──────────────────────────────────────────────────────
   .ll   nothing. A potentially-faulting operation is an ordinary
         instruction; there is no name for "the value on the path where it
         did not fault", so a bounds check that has already been proven
         cannot be expressed as a renaming.
   .air  a π-node. `AIR_PI` names the value on the non-faulting edge of a
         diverging operation, so "this index was in range past here" is a
         fact about a NAME rather than a fact about a program point.

 ── SP: semi-pruned ─────────────────────────────────────────────────────
   Not a data structure but a placement filter: only variables live across
   a block boundary get a φ. Recorded per value as `crosses_block` so the
   decision is auditable rather than implicit.

 Nothing here is inferred yet — a1 SEEDS these from the AST and from σ/π
 facts, and a2 refines them. What matters at this stage is that the slots
 exist, are printed, and survive a round trip, because D1's whole argument
 is that facts computed in a2 have to survive four conversions to reach
 emission.
*/

module pear_erm;

import pfront_core;

extern fn int printf(char* fmt, ...);

// ════════════════════════════════════════════════════════════════════════
// R — RANGES
// ════════════════════════════════════════════════════════════════════════

/*
 A closed integer interval [lo, hi] with explicit top/bottom.

 `bottom` means unreachable / no value can arrive here — it is the identity
 for join and it is how a proven-dead branch is represented. `top` means
 nothing is known. Both are flags rather than sentinel lo/hi values,
 because INT64_MIN and INT64_MAX are legitimate bounds for an i64 and
 overloading them would be exactly the D2 mistake.
*/
struct Range
{
    long lo;
    long hi;
    bool is_top;      // nothing known
    bool is_bottom;   // unreachable
}

fn Range r_top()    { Range r; r.lo = 0; r.hi = 0; r.is_top = true;  r.is_bottom = false; return r; }
fn Range r_bottom() { Range r; r.lo = 0; r.hi = 0; r.is_top = false; r.is_bottom = true;  return r; }

fn Range r_const(long v)
{
    Range r; r.lo = v; r.hi = v; r.is_top = false; r.is_bottom = false; return r;
}

fn Range r_range(long lo, long hi)
{
    if (lo > hi) { return r_bottom(); }
    Range r; r.lo = lo; r.hi = hi; r.is_top = false; r.is_bottom = false; return r;
}

fn bool r_is_const(Range* r)
{
    return !r.is_top && !r.is_bottom && r.lo == r.hi;
}

fn bool r_eq(Range a, Range b)
{
    if (a.is_top != b.is_top || a.is_bottom != b.is_bottom) { return false; }
    if (a.is_top || a.is_bottom) { return true; }
    return a.lo == b.lo && a.hi == b.hi;
}

// Join, for a φ: the value could be either, so widen to cover both.
fn Range r_join(Range a, Range b)
{
    if (a.is_bottom) { return b; }
    if (b.is_bottom) { return a; }
    if (a.is_top || b.is_top) { return r_top(); }
    long lo = a.lo < b.lo ? a.lo : b.lo;
    long hi = a.hi > b.hi ? a.hi : b.hi;
    return r_range(lo, hi);
}

// Meet, for a σ: both facts hold on this edge, so narrow to the overlap.
fn Range r_meet(Range a, Range b)
{
    if (a.is_bottom || b.is_bottom) { return r_bottom(); }
    if (a.is_top) { return b; }
    if (b.is_top) { return a; }
    long lo = a.lo > b.lo ? a.lo : b.lo;
    long hi = a.hi < b.hi ? a.hi : b.hi;
    if (lo > hi) { return r_bottom(); }     // contradictory: dead edge
    return r_range(lo, hi);
}

/*
 Does this range fit in `bits` of the given signedness?

 This is the query the whole `R` exists to answer: it is what lets a2
 delete an overflow check, narrow a 64-bit operation to 32, or drop a
 bounds check entirely.
*/
fn bool r_fits(Range* r, int bits, bool is_signed)
{
    if (r.is_bottom) { return true; }
    if (r.is_top) { return false; }
    if (bits <= 0 || bits > 64) { return false; }
    if (is_signed)
    {
        if (bits == 64) { return true; }
        long max = ((long)1 << (bits - 1)) - 1;
        long min = -((long)1 << (bits - 1));
        return r.lo >= min && r.hi <= max;
    }
    /*
     A NEGATIVE lower bound in an unsigned range is not necessarily a
     value out of range: at 64 bits the interval is stored in a signed
     long, so `0xFFFFFFFFFFFFFFFF` is held as -1. Rejecting on the sign
     alone reported 1,111 spurious `width exceeded` warnings on the
     standard library -- every `u64` constant with the top bit set,
     including plain `-1 as u64` masks.

     At 64 bits every bit pattern is a valid u64 whichever way the long
     is read, so the honest answer is true. Below 64 a negative bound
     genuinely cannot be represented and is still rejected.
    */
    if (bits == 64) { return true; }
    if (r.lo < 0) { return false; }
    long umax = (long)(((ulong)1 << (ulong)bits) - 1);
    return r.hi <= umax;
}

// ════════════════════════════════════════════════════════════════════════
// R — KNOWN BITS
// ════════════════════════════════════════════════════════════════════════

/*
 Per-bit tri-state: known-zero, known-one, unknown.

 Invariant: `zeros & ones == 0`. A bit claimed both zero and one means the
 value is unreachable, which callers should represent as a bottom Range
 rather than as contradictory bits.

 LLVM computes this in ValueTracking and discards it. Keeping it in the IR
 means an alignment fact established once (`ptr & 7 == 0`) is still
 available at emission, where it becomes an `align` attribute, instead of
 being rediscovered or lost.
*/
struct KnownBits
{
    ulong zeros;   // bit set => that bit is definitely 0
    ulong ones;    // bit set => that bit is definitely 1
}

fn KnownBits kb_unknown() { KnownBits k; k.zeros = 0; k.ones = 0; return k; }

fn KnownBits kb_const(long v)
{
    KnownBits k;
    k.ones  = (ulong)v;
    k.zeros = ~(ulong)v;
    return k;
}

fn bool kb_is_unknown(KnownBits* k) { return k.zeros == 0 && k.ones == 0; }

fn bool kb_conflicts(KnownBits* k) { return (k.zeros & k.ones) != 0; }

// Meet over a φ: only bits both sides agree on survive.
fn KnownBits kb_join(KnownBits a, KnownBits b)
{
    KnownBits k;
    k.zeros = a.zeros & b.zeros;
    k.ones  = a.ones  & b.ones;
    return k;
}

/*
 Trailing zero count, which is the alignment this value is known to have.
 Returns 64 for a value known to be entirely zero.
*/
fn int kb_trailing_zeros(KnownBits* k)
{
    for (int i = 0; i < 64; i++)
    {
        if ((k.zeros & ((ulong)1 << (ulong)i)) == 0) { return i; }
    }
    return 64;
}

// ════════════════════════════════════════════════════════════════════════
// R — NULLNESS
// ════════════════════════════════════════════════════════════════════════

/*
 A three-point lattice, separate from Range because a pointer's null-ness
 is not usefully expressed as an integer bound: "definitely not null" is a
 fact about a pointer that has nothing to say about its numeric value.

 This is what `!nonnull` becomes at emission, and what lets a2 delete a
 redundant null check after a π on a dereference.
*/
enum Nullness : int (String mnemonic)
{
    NULL_UNKNOWN { "maybe" },
    NULL_NEVER   { "nonnull" },
    NULL_ALWAYS  { "null" }
}

fn Nullness null_join(Nullness a, Nullness b)
{
    if (a == b) { return a; }
    return Nullness.NULL_UNKNOWN;
}

// ════════════════════════════════════════════════════════════════════════
// M — MEMORY VERSIONS
// ════════════════════════════════════════════════════════════════════════

/*
 MemorySSA, but IN the IR rather than beside it.

 Memory is a single versioned resource. Every operation that writes defines
 a new version; every operation that reads names the version it observes; a
 control-flow join needs a memory φ exactly as a scalar join does.

   MEM_LIVE_ON_ENTRY   version 0, the state at function entry
   MEM_DEF             a store: consumes one version, produces the next
   MEM_USE             a load: observes a version, produces none
   MEM_PHI             a join of versions from each predecessor

 Because this is serialised, a consumer four stages downstream can still
 ask "what wrote the memory this load reads?" without rebuilding anything.
 That is the concrete difference from LLVM, where MemorySSA cannot survive
 a trip through a .ll file.
*/
enum MemKind : int (String mnemonic)
{
    MEM_NONE           { "-" },        // this value does not touch memory
    MEM_LIVE_ON_ENTRY  { "entry" },
    MEM_DEF            { "def" },
    MEM_USE            { "use" },
    MEM_PHI            { "memphi" }
}

/*
 An alias scope id. Two accesses with DIFFERENT non-zero scope ids provably
 do not alias; scope 0 means unknown and forces the conservative answer.

 Deliberately an opaque id rather than a type name: alias reasoning in a2
 wants disjointness, not the type system, and coupling them would drag
 pfront's type universe across the D5 boundary.
*/
alias AliasScope = uint;
const AliasScope ALIAS_UNKNOWN = 0;

struct MemFact
{
    MemKind    kind;
    uint       version;      // the memory version defined, or 0
    uint       reaching;     // MEM_USE / MEM_DEF: the version observed
    AliasScope scope;
    bool       no_alias;     // provably disjoint from every other scope
    bool       volatile_;    // must not be reordered or elided, ever
}

fn MemFact mem_none()
{
    MemFact m;
    m.kind = MemKind.MEM_NONE;
    m.version = 0; m.reaching = 0;
    m.scope = ALIAS_UNKNOWN;
    m.no_alias = false; m.volatile_ = false;
    return m;
}

// ════════════════════════════════════════════════════════════════════════
// THE FACT RECORD — one per value
// ════════════════════════════════════════════════════════════════════════

/*
 PEAR.md D1 specifies facts living in a side table keyed by origin, never
 inline in the term. That is right for a2/a3/a4/a5, where a term is
 rewritten and re-created constantly and an inline fact would be copied,
 stale or lost at every step.

 In a1 the facts are attached per value, and the side table (FactTable
 below) is keyed by origin over the top. Both exist because they answer
 different questions: the per-value record is "what does THIS version
 know", the origin-keyed table is "what has ever been learned about this
 lineage". A σ splits the first and shares the second, which is exactly why
 σ inherits origin.

 SP lives here too: `crosses_block` is the semi-pruned classification, and
 recording it per value makes the φ-placement decision auditable rather
 than implicit in whichever pass happened to run.
*/
struct Facts
{
    Range     range;
    KnownBits bits;
    Nullness  nullness;
    int       width;          // declared bit width; 0 = unknown/not integral
    bool      is_signed;
    MemFact   mem;
    bool      crosses_block;  // SP: needs a φ
    bool      may_fault;      // E: this operation can diverge
}

fn Facts facts_unknown()
{
    Facts f;
    f.range = r_top();
    f.bits = kb_unknown();
    f.nullness = Nullness.NULL_UNKNOWN;
    f.width = 0;
    f.is_signed = true;
    f.mem = mem_none();
    f.crosses_block = false;
    f.may_fault = false;
    return f;
}

/*
 Is this fact record worth printing? A value about which nothing is known
 should not emit a fact comment on every line — the text form has to stay
 readable, and a wall of `[range=top bits=unknown null=maybe]` would make
 the diff property useless.
*/
fn bool facts_known(Facts* f)
{
    if (!f.range.is_top) { return true; }
    if (!kb_is_unknown(&f.bits)) { return true; }
    if (f.nullness != Nullness.NULL_UNKNOWN) { return true; }
    if (f.width != 0) { return true; }
    if (f.mem.kind != MemKind.MEM_NONE) { return true; }
    if (f.crosses_block) { return true; }
    if (f.may_fault) { return true; }
    return false;
}

/*
 Join two fact records, for a φ. Every component joins independently.

 Memory does NOT join here: a memory φ is a real MEM_PHI node with its own
 version, not a merged fact, because the identity of the reaching version
 is what downstream queries need.
*/
fn Facts facts_join(Facts a, Facts b)
{
    Facts f = facts_unknown();
    f.range = r_join(a.range, b.range);
    f.bits = kb_join(a.bits, b.bits);
    f.nullness = null_join(a.nullness, b.nullness);
    f.width = a.width == b.width ? a.width : 0;
    f.is_signed = a.is_signed && b.is_signed;
    f.crosses_block = a.crosses_block || b.crosses_block;
    f.may_fault = a.may_fault || b.may_fault;
    return f;
}

// ════════════════════════════════════════════════════════════════════════
// APPLYING A REFINEMENT — where σ and π earn their keep
// ════════════════════════════════════════════════════════════════════════

/*
 Narrow a range given that `cmp bound` holds.

 This is the concrete content of e-SSA: on the true edge of `if x < 10`,
 the σ-renamed x has range [top.lo, 9]. LLVM cannot express this as a
 renaming at all — it recovers the same information with a predicate-aware
 analysis that must re-derive it at every use site.
*/
fn Range r_refine_lt(Range r, long bound)
{
    if (bound == (long)0x8000000000000000) { return r_bottom(); }  // x < INT64_MIN
    return r_meet(r, r_range((long)0x8000000000000000, bound - 1));
}

fn Range r_refine_le(Range r, long bound)
{
    return r_meet(r, r_range((long)0x8000000000000000, bound));
}

fn Range r_refine_gt(Range r, long bound)
{
    if (bound == (long)0x7FFFFFFFFFFFFFFF) { return r_bottom(); }  // x > INT64_MAX
    return r_meet(r, r_range(bound + 1, (long)0x7FFFFFFFFFFFFFFF));
}

fn Range r_refine_ge(Range r, long bound)
{
    return r_meet(r, r_range(bound, (long)0x7FFFFFFFFFFFFFFF));
}

fn Range r_refine_eq(Range r, long v) { return r_meet(r, r_const(v)); }

/*
 `x != v` only narrows when v sits at an endpoint — an interval domain
 cannot represent a hole. Returning the input unchanged otherwise is the
 sound answer, and saying so here is better than silently producing a
 wrong-but-tighter range.
*/
fn Range r_refine_ne(Range r, long v)
{
    if (r.is_top || r.is_bottom) { return r; }
    if (r.lo == v && r.hi == v) { return r_bottom(); }
    if (r.lo == v) { return r_range(r.lo + 1, r.hi); }
    if (r.hi == v) { return r_range(r.lo, r.hi - 1); }
    return r;
}

// ════════════════════════════════════════════════════════════════════════
// FACT TABLE — D1's side table, keyed by origin
// ════════════════════════════════════════════════════════════════════════

/*
 PEAR.md D1, implemented as specified: facts keyed by the AIR value id a
 construct descends from, so that after four conversions a5 can still ask
 "what was learned about this lineage" even though the term holding it has
 been rebuilt three times.

 `--verify-facts` reports how many entries were established and how many
 were still reachable at the end. That number is the honest measure of
 whether ERM works, and reporting it whether flattering or not is the whole
 point of having it.
*/
struct FactTable
{
    Facts* by_origin;
    bool*  present;
    usz    cap;
    usz    established;   // how many origins ever got a non-trivial fact
}

extern fn void* malloc(usz size);
extern fn void* realloc(void* p, usz size);
extern fn void  free(void* p);

fn bool FactTable.init(FactTable* t, usz n)
{
    if (n == 0) { n = 64; }
    t.by_origin = (Facts*)malloc(n * Facts::size);
    t.present = (bool*)malloc(n);
    t.cap = n;
    t.established = 0;
    if (t.by_origin == null || t.present == null) { t.cap = 0; return false; }
    for (usz i = 0; i < n; i++) { t.by_origin[i] = facts_unknown(); t.present[i] = false; }
    return true;
}

fn void FactTable.destroy(FactTable* t)
{
    if (t.by_origin != null) { free((void*)t.by_origin); t.by_origin = null; }
    if (t.present != null) { free((void*)t.present); t.present = null; }
    t.cap = 0;
}

fn bool FactTable.ensure(FactTable* t, usz idx)
{
    if (idx < t.cap) { return true; }
    usz nc = t.cap == 0 ? 64 : t.cap;
    while (nc <= idx) { nc = nc * 2; }
    Facts* nf = (Facts*)realloc((void*)t.by_origin, nc * Facts::size);
    if (nf == null) { return false; }
    t.by_origin = nf;
    bool* np = (bool*)realloc((void*)t.present, nc);
    if (np == null) { return false; }
    t.present = np;
    for (usz i = t.cap; i < nc; i++) { t.by_origin[i] = facts_unknown(); t.present[i] = false; }
    t.cap = nc;
    return true;
}

fn void FactTable.put(FactTable* t, uint origin, Facts f)
{
    if (!t.ensure((usz)origin)) { return; }
    if (!t.present[origin] && facts_known(&f)) { t.established = t.established + 1; }
    t.by_origin[origin] = f;
    t.present[origin] = true;
}

fn Facts FactTable.get(FactTable* t, uint origin)
{
    if ((usz)origin >= t.cap || !t.present[origin]) { return facts_unknown(); }
    return t.by_origin[origin];
}

/*
 Merge a newly-learned fact into an origin's accumulated knowledge.

 MEET, not join: two facts about the same lineage established on different
 paths are both true of that lineage, so the intersection is sound. Using
 join here would throw away every refinement a σ produced, which is the
 single most likely way for ERM to end up decorative.
*/
fn void FactTable.refine(FactTable* t, uint origin, Facts f)
{
    Facts cur = t.get(origin);
    Facts merged = cur;
    merged.range = r_meet(cur.range, f.range);
    merged.bits.zeros = cur.bits.zeros | f.bits.zeros;
    merged.bits.ones  = cur.bits.ones  | f.bits.ones;
    if (cur.nullness == Nullness.NULL_UNKNOWN) { merged.nullness = f.nullness; }
    if (merged.width == 0) { merged.width = f.width; }
    merged.crosses_block = cur.crosses_block || f.crosses_block;
    merged.may_fault = cur.may_fault || f.may_fault;
    t.put(origin, merged);
}
