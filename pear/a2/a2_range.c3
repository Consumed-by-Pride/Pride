/*
 a2 — `R`, the range analysis.

 a1 seeds ranges in ONE FORWARD PASS with no iteration, which is correct
 but weak in exactly two places, and both are the interesting ones:

   a loop-carried φ sees `top` for the operand arriving on the back edge,
   because that value does not exist yet when the φ is built; and

   a σ split on a SYMBOLIC bound (`if i < n`) records the comparison but
   cannot narrow, because `n` is not a literal.

 This pass fixes both. It follows Rodrigues, Campos and Quintão Pereira's
 non-iterative range analysis (CGO 2013): build a constraint graph, find
 its strongly-connected components, and solve them in topological order.
 Inside an SCC — that is, inside a loop — apply widening to reach a fixed
 point in bounded time, then narrowing to recover the precision widening
 threw away.

 "Non-iterative" refers to the graph as a whole: components are solved once
 each, in dependency order, rather than the whole function being re-swept
 until nothing changes. Within one SCC iteration is unavoidable, which is
 what widening is for.

 ── Why widening is not optional ────────────────────────────────────────

     let mut i = 0
     while i < n
       i = i + 1

 The φ for `i` joins `0` and `i+1`. Plain fixpoint iteration gives [0,0],
 then [0,1], then [0,2] — it climbs one step per pass and only terminates
 after as many passes as the loop has iterations, which is unbounded and
 may be unknown. Widening jumps straight to [0, +∞] on seeing the bound
 grow, terminating in two passes. Narrowing then re-reads the σ from
 `i < n` and pulls the upper bound back to `n - 1` when `n` is itself
 bounded.

 The result is that `i` is provably non-negative and bounded by the loop
 condition — which is what makes a bounds check on `a[i]` removable, and
 that is the payoff this whole file exists for. It is reported as an
 absolute count of comparisons decided, not a percentage.
*/

module pear_a2_range;

import pear_air;
import pear_erm;
import pear_a2_cfg;
import pear_a2_facts;
import pfront_core;

alias Air   = pear_air::AirModule;
alias Val   = pear_air::AirValue;
alias Blk   = pear_air::AirBlock;
alias Fn    = pear_air::AirFunc;
alias Op    = pear_air::AirOp;
alias Term  = pear_air::AirTerm;
alias BOp   = pear_air::AirBinOp;
alias Fact  = pear_air::AirFact;
alias Range = pear_erm::Range;

extern fn int   printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn void  free(void* p);

const long LONG_MIN = (long)0x8000000000000000;
const long LONG_MAX = (long)0x7FFFFFFFFFFFFFFF;

// ════════════════════════════════════════════════════════════════════════
// INTERVAL ARITHMETIC
// ════════════════════════════════════════════════════════════════════════

/*
 These duplicate a1's air_infer transfer functions deliberately rather than
 sharing them, for one reason: a1's must be single-pass and monotone-free,
 while these run inside a widening loop and have to be MONOTONE for the
 fixpoint to terminate. Sharing would force one of the two to compromise,
 and a non-monotone transfer function inside a widening loop does not
 converge — it oscillates.
*/
fn bool mul_ovf(long a, long b)
{
    if (a == 0 || b == 0) { return false; }
    long r = a * b;
    return r / b != a;
}

/*
 SATURATE, do not collapse.

 An endpoint that overflows becomes the extreme rather than sending the
 whole interval to top. This is sound for these opcodes — AIR_BIN's plain
 `add`/`sub`/`mul` have undefined overflow, so an execution that overflows
 is one the analysis is entitled to exclude, and `addc`/`adds` either trap
 or clamp. Wrapping (`addw`) never reaches here; it returns top at the
 call site, which is the whole reason those are distinct opcodes.

 Collapsing to top instead was a real precision bug, and an instructive
 one. On `while i < 100 { i = i + 1 }` widening had correctly kept the
 lower bound and pushed only the upper to +inf, giving `i` as [0, MAX].
 The very next step, `i + 1`, overflowed at the top end and returned top —
 throwing away the lower bound that widening had gone to the trouble of
 preserving. Narrowing then rebuilt it from `refine_lt(top, 100)`, whose
 lower bound is MIN, and `i` came out as [-9223372036854775807, 100]
 instead of [0, 100].

 The failure is invisible in the metrics: the value still counts as
 "ranged", the pass still reports a tightening, and the number is simply
 wrong. It is only visible by reading the output on a loop, which is why
 the regression test asserts the exact interval and not merely that one
 exists.
*/
fn long sat_add(long a, long b)
{
    if (b > 0 && a > LONG_MAX - b) { return LONG_MAX; }
    if (b < 0 && a < LONG_MIN - b) { return LONG_MIN; }
    return a + b;
}

fn Range radd(Range a, Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    if (a.is_top || b.is_top) { return pear_erm::r_top(); }
    return pear_erm::r_range(sat_add(a.lo, b.lo), sat_add(a.hi, b.hi));
}

fn Range rsub(Range a, Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    if (a.is_top || b.is_top) { return pear_erm::r_top(); }
    // -LONG_MIN is not representable, so negate through the saturating
    // helper rather than writing `-b.hi` and hoping.
    long nlo = b.hi == LONG_MIN ? LONG_MAX : -b.hi;
    long nhi = b.lo == LONG_MIN ? LONG_MAX : -b.lo;
    return pear_erm::r_range(sat_add(a.lo, nlo), sat_add(a.hi, nhi));
}

fn long sat_mul(long a, long b)
{
    if (a == 0 || b == 0) { return 0; }
    if (!mul_ovf(a, b)) { return a * b; }
    bool neg = (a < 0) != (b < 0);
    return neg ? LONG_MIN : LONG_MAX;
}

fn Range rmul(Range a, Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    if (a.is_top || b.is_top) { return pear_erm::r_top(); }
    // All four corners: a negative operand swaps which endpoint is which.
    long p1 = sat_mul(a.lo, b.lo); long p2 = sat_mul(a.lo, b.hi);
    long p3 = sat_mul(a.hi, b.lo); long p4 = sat_mul(a.hi, b.hi);
    long lo = p1; long hi = p1;
    if (p2 < lo) { lo = p2; } if (p2 > hi) { hi = p2; }
    if (p3 < lo) { lo = p3; } if (p3 > hi) { hi = p3; }
    if (p4 < lo) { lo = p4; } if (p4 > hi) { hi = p4; }
    return pear_erm::r_range(lo, hi);
}

fn Range rdiv(Range a, Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    if (a.is_top || b.is_top) { return pear_erm::r_top(); }
    // A divisor interval containing zero says nothing; division by zero
    // faults, and the surviving path is described by a pi, not by this.
    if (b.lo <= 0 && b.hi >= 0) { return pear_erm::r_top(); }
    if (b.lo == -1 || b.hi == -1) { return pear_erm::r_top(); }   // LONG_MIN / -1
    long p1 = a.lo / b.lo; long p2 = a.lo / b.hi;
    long p3 = a.hi / b.lo; long p4 = a.hi / b.hi;
    long lo = p1; long hi = p1;
    if (p2 < lo) { lo = p2; } if (p2 > hi) { hi = p2; }
    if (p3 < lo) { lo = p3; } if (p3 > hi) { hi = p3; }
    if (p4 < lo) { lo = p4; } if (p4 > hi) { hi = p4; }
    return pear_erm::r_range(lo, hi);
}

/*
 `a % b`: the result has the sign of `a` and magnitude below |b|.

 This is the C/LLVM truncated-remainder rule, which Pride follows. Getting
 the sign wrong here would claim `x % 8` is non-negative for negative `x`,
 and a mask-based bounds check would then be deleted incorrectly.
*/
fn Range rmod(Range a, Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    if (b.is_top) { return pear_erm::r_top(); }
    if (b.lo <= 0 && b.hi >= 0) { return pear_erm::r_top(); }

    long mag = b.hi > 0 ? b.hi : -b.lo;
    if (mag == LONG_MIN) { return pear_erm::r_top(); }
    if (mag < 0) { mag = -mag; }
    long bound = mag - 1;

    if (a.is_top) { return pear_erm::r_range(-bound, bound); }
    bool a_nonneg = a.lo >= 0;
    bool a_nonpos = a.hi <= 0;
    if (a_nonneg) { return pear_erm::r_range(0, bound); }
    if (a_nonpos) { return pear_erm::r_range(-bound, 0); }
    return pear_erm::r_range(-bound, bound);
}

/*
 Bitwise AND with a non-negative mask bounds the result by the mask. This
 is the single most valuable bit-level fact in real code: `i & 15` is
 exactly how a bounds-checked ring buffer index is written, and it is what
 makes the check provably redundant.
*/
fn Range rand(Range a, Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    bool a_mask = !a.is_top && a.lo >= 0;
    bool b_mask = !b.is_top && b.lo >= 0;
    if (a_mask && b_mask)
    {
        long m = a.hi < b.hi ? a.hi : b.hi;
        return pear_erm::r_range(0, m);
    }
    if (a_mask) { return pear_erm::r_range(0, a.hi); }
    if (b_mask) { return pear_erm::r_range(0, b.hi); }
    return pear_erm::r_top();
}

fn Range ror(Range a, Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    if (a.is_top || b.is_top) { return pear_erm::r_top(); }
    if (a.lo < 0 || b.lo < 0) { return pear_erm::r_top(); }
    /*
     For non-negative operands, `a | b <= next_pow2(max)-1`. Derived by
     rounding the larger bound up to an all-ones mask, which is the
     tightest bound expressible without tracking bits individually.
    */
    long m = a.hi > b.hi ? a.hi : b.hi;
    long fill = m;
    fill |= fill >> 1;  fill |= fill >> 2;  fill |= fill >> 4;
    fill |= fill >> 8;  fill |= fill >> 16; fill |= fill >> 32;
    if (fill < 0) { return pear_erm::r_range(0, LONG_MAX); }
    return pear_erm::r_range(0, fill);
}

fn Range rshl(Range a, Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    if (a.is_top || b.is_top) { return pear_erm::r_top(); }
    if (b.lo < 0 || b.hi > 62 || a.lo < 0) { return pear_erm::r_top(); }
    if (mul_ovf(a.hi, (long)1 << (ulong)b.hi)) { return pear_erm::r_top(); }
    return pear_erm::r_range(a.lo << (ulong)b.lo, a.hi << (ulong)b.hi);
}

// Arithmetic shift right: monotone in both operands for non-negative shift.
fn Range rshr(Range a, Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    if (a.is_top || b.is_top) { return pear_erm::r_top(); }
    if (b.lo < 0 || b.hi > 63) { return pear_erm::r_top(); }
    long lo = a.lo >= 0 ? a.lo >> (ulong)b.hi : a.lo >> (ulong)b.lo;
    long hi = a.hi >= 0 ? a.hi >> (ulong)b.lo : a.hi >> (ulong)b.hi;
    if (lo > hi) { return pear_erm::r_top(); }
    return pear_erm::r_range(lo, hi);
}

// ════════════════════════════════════════════════════════════════════════
// WIDENING AND NARROWING
// ════════════════════════════════════════════════════════════════════════

/*
 Widen `old` towards `wide`.

 An endpoint that MOVED goes straight to infinity; an endpoint that held
 still is kept. This is the standard interval widening operator, and the
 asymmetry is the point: the lower bound of `i = 0; i++` never moves, so
 `i >= 0` survives widening while the useless upper bound is discarded
 immediately instead of being climbed one unit at a time.
*/
fn Range widen(Range old, Range wide)
{
    if (old.is_bottom) { return wide; }
    if (wide.is_bottom) { return old; }
    if (old.is_top || wide.is_top) { return pear_erm::r_top(); }
    long lo = wide.lo < old.lo ? LONG_MIN : old.lo;
    long hi = wide.hi > old.hi ? LONG_MAX : old.hi;
    if (lo == LONG_MIN && hi == LONG_MAX) { return pear_erm::r_top(); }
    return pear_erm::r_range(lo, hi);
}

/*
 Narrow: recover precision widening gave away.

 Only an endpoint that widening pushed to infinity may be pulled back, and
 only to a value the transfer functions actually justify. An endpoint that
 was never widened is left alone — narrowing a real bound would be
 unsound, and this restriction is what makes narrowing safe to iterate.
*/
fn Range narrow(Range wide, Range tight)
{
    if (wide.is_bottom || tight.is_bottom) { return wide; }
    if (tight.is_top) { return wide; }
    if (wide.is_top) { return tight; }
    long lo = wide.lo == LONG_MIN && tight.lo != LONG_MIN ? tight.lo : wide.lo;
    long hi = wide.hi == LONG_MAX && tight.hi != LONG_MAX ? tight.hi : wide.hi;
    if (lo > hi) { return wide; }
    return pear_erm::r_range(lo, hi);
}

// ════════════════════════════════════════════════════════════════════════
// THE SOLVER
// ════════════════════════════════════════════════════════════════════════

/*
 Ranges are held in a dense array indexed by value id, not on the values
 themselves, so that iteration never disturbs a1's seeds until the solution
 has converged. Writing through to the values mid-solve would make the
 result depend on visit order.
*/
struct Solver
{
    Air*    m;
    Range*  r;            // current range per value id
    bool*   in_scc;       // scratch: membership of the component being solved
    usz     n;

    // SCC discovery (Tarjan, iterative).
    int*    index;
    int*    lowlink;
    bool*   on_stack;
    int*    stack;
    usz     sp;
    int     next_index;
    int*    comp;         // value id -> component number
    int     ncomp;

    usz     widened;      // how many values needed widening: loop count proxy
    bool    ok;
}

fn bool Solver.init(Solver* s, Air* m)
{
    s.m = m;
    s.n = m.value_count;
    s.widened = 0;
    s.ok = false;
    usz n = s.n == 0 ? 1 : s.n;
    s.r        = (Range*)malloc(n * Range::size);
    s.in_scc   = (bool*)malloc(n);
    s.index    = (int*)malloc(n * int::size);
    s.lowlink  = (int*)malloc(n * int::size);
    s.on_stack = (bool*)malloc(n);
    s.stack    = (int*)malloc(n * int::size);
    s.comp     = (int*)malloc(n * int::size);
    if (s.r == null || s.in_scc == null || s.index == null || s.lowlink == null
        || s.on_stack == null || s.stack == null || s.comp == null)
    {
        return false;
    }
    for (usz i = 0; i < n; i++)
    {
        s.r[i] = pear_erm::r_top();
        s.in_scc[i] = false;
        s.index[i] = -1;
        s.lowlink[i] = 0;
        s.on_stack[i] = false;
        s.comp[i] = -1;
    }
    s.sp = 0;
    s.next_index = 0;
    s.ncomp = 0;
    s.ok = true;
    return true;
}

fn void Solver.destroy(Solver* s)
{
    if (s.r != null)        { free((void*)s.r); s.r = null; }
    if (s.in_scc != null)   { free((void*)s.in_scc); s.in_scc = null; }
    if (s.index != null)    { free((void*)s.index); s.index = null; }
    if (s.lowlink != null)  { free((void*)s.lowlink); s.lowlink = null; }
    if (s.on_stack != null) { free((void*)s.on_stack); s.on_stack = null; }
    if (s.stack != null)    { free((void*)s.stack); s.stack = null; }
    if (s.comp != null)     { free((void*)s.comp); s.comp = null; }
}

/*
 The constraint graph's edges: which values does `v` READ?

 σ and π read their source. φ reads every incoming operand. Arithmetic
 reads its operands. Everything else reads nothing that constrains its
 range, and is left at whatever it was seeded with.
*/
fn usz Solver.dep_count(Solver* s, uint v)
{
    Val* vv = s.m.val(v);
    if (vv == null) { return 0; }
    switch (vv.op)
    {
        case AIR_PHI:
        case AIR_SIGMA:
        case AIR_PI:
        case AIR_BIN:
        case AIR_UN:
        case AIR_CAST:
            return vv.op_count;
        default:
            return 0;
    }
}

fn uint Solver.dep(Solver* s, uint v, usz i)
{
    Val* vv = s.m.val(v);
    if (vv == null || i >= vv.op_count) { return pear_air::AIR_NO_VALUE; }
    return s.m.operands[vv.op_off + i];
}

/*
 Tarjan's SCC algorithm, iteratively.

 Recursion is not an option: the 64 KB C3 stack limit is reached well
 before the ~2,400-value functions this runs on. The explicit frame keeps
 the child index so the walk can resume where it left off.
*/
fn void Solver.tarjan(Solver* s)
{
    usz n = s.n;
    int* frame_v = (int*)malloc(n * int::size);
    usz* frame_i = (usz*)malloc(n * usz::size);
    if (frame_v == null || frame_i == null)
    {
        if (frame_v != null) { free((void*)frame_v); }
        if (frame_i != null) { free((void*)frame_i); }
        return;
    }

    for (usz root = 1; root < n; root++)
    {
        if (s.index[root] != -1) { continue; }
        Val* rv = s.m.val((uint)root);
        if (rv == null || rv.block == pear_air::AIR_NO_BLOCK) { continue; }

        usz fp = 0;
        frame_v[fp] = (int)root;
        frame_i[fp] = 0;
        s.index[root] = s.next_index;
        s.lowlink[root] = s.next_index;
        s.next_index = s.next_index + 1;
        s.stack[s.sp] = (int)root; s.sp = s.sp + 1;
        s.on_stack[root] = true;

        while (true)
        {
            int v = frame_v[fp];
            usz di = frame_i[fp];
            usz nd = s.dep_count((uint)v);

            if (di < nd)
            {
                frame_i[fp] = di + 1;
                uint w = s.dep((uint)v, di);
                if (w == pear_air::AIR_NO_VALUE || (usz)w >= n) { continue; }
                if (s.index[w] == -1)
                {
                    s.index[w] = s.next_index;
                    s.lowlink[w] = s.next_index;
                    s.next_index = s.next_index + 1;
                    if (s.sp < n) { s.stack[s.sp] = (int)w; s.sp = s.sp + 1; }
                    s.on_stack[w] = true;
                    if (fp + 1 < n) { fp = fp + 1; frame_v[fp] = (int)w; frame_i[fp] = 0; }
                }
                else if (s.on_stack[w])
                {
                    if (s.index[w] < s.lowlink[v]) { s.lowlink[v] = s.index[w]; }
                }
                continue;
            }

            // v is finished. Close its component if it is a root.
            if (s.lowlink[v] == s.index[v])
            {
                while (s.sp > 0)
                {
                    s.sp = s.sp - 1;
                    int w = s.stack[s.sp];
                    s.on_stack[w] = false;
                    s.comp[w] = s.ncomp;
                    if (w == v) { break; }
                }
                s.ncomp = s.ncomp + 1;
            }

            if (fp == 0) { break; }
            fp = fp - 1;
            int parent = frame_v[fp];
            if (s.lowlink[v] < s.lowlink[parent]) { s.lowlink[parent] = s.lowlink[v]; }
        }
    }
    free((void*)frame_v);
    free((void*)frame_i);
}

/*
 The transfer function: recompute one value's range from its inputs.

 `use_sigma_bound` controls whether a σ over a SYMBOLIC bound is allowed to
 consult the current range of that bound. During widening it must not —
 a symbolic bound that is itself still climbing would make this function
 non-monotone and the fixpoint would never settle. During narrowing it is
 exactly the point: that is how `i < n` finally bounds `i` by `n - 1`.
*/
fn Range Solver.transfer(Solver* s, uint vid, bool use_sigma_bound)
{
    Val* v = s.m.val(vid);
    if (v == null) { return pear_erm::r_top(); }

    switch (v.op)
    {
        case AIR_CONST_INT:
            return pear_erm::r_const(v.p.ival);

        case AIR_CONST_BOOL:
            return pear_erm::r_range(0, 1);

        case AIR_PHI:
        {
            // Join over incoming operands. A hole contributes nothing.
            Range acc = pear_erm::r_bottom();
            for (usz i = 0; i < v.op_count; i++)
            {
                uint o = s.m.operands[v.op_off + i];
                if ((usz)o >= s.n) { return pear_erm::r_top(); }
                acc = pear_erm::r_join(acc, s.r[o]);
            }
            return acc;
        }

        case AIR_SIGMA:
        {
            if (v.op_count < 1) { return pear_erm::r_top(); }
            uint src = s.m.operands[v.op_off];
            if ((usz)src >= s.n) { return pear_erm::r_top(); }
            Range base = s.r[src];

            long bound;
            if (!s.sigma_bound(vid, &bound, use_sigma_bound))
            {
                /*
                 No single-number bound. An EQ or NE against a symbolic
                 value is still a refinement -- `x == n` means x lies in
                 n's interval -- and it is only expressible as a meet, so
                 it takes the interval path rather than being dropped.
                */
                Range mr;
                if (use_sigma_bound && s.sigma_meet(vid, &mr))
                {
                    if (v.p.fact == Fact.FACT_EQ) { return pear_erm::r_meet(base, mr); }
                    return pear_erm::r_refine_ne(base, mr.lo);
                }
                return base;
            }
            switch (v.p.fact)
            {
                case FACT_LT: return pear_erm::r_refine_lt(base, bound);
                case FACT_LE: return pear_erm::r_refine_le(base, bound);
                case FACT_GT: return pear_erm::r_refine_gt(base, bound);
                case FACT_GE: return pear_erm::r_refine_ge(base, bound);
                case FACT_EQ: return pear_erm::r_refine_eq(base, bound);
                case FACT_NE: return pear_erm::r_refine_ne(base, bound);
                default:      return base;
            }
        }

        case AIR_PI:
        {
            if (v.op_count < 1) { return pear_erm::r_top(); }
            uint g = s.m.operands[v.op_off];
            if ((usz)g >= s.n) { return pear_erm::r_top(); }
            Range base = s.r[g];
            switch (v.p.fact)
            {
                case FACT_NONZERO:  return pear_erm::r_refine_ne(base, 0);
                case FACT_INBOUNDS: return pear_erm::r_refine_ge(base, 0);
                default:            return base;
            }
        }

        case AIR_BIN:
        {
            if (v.op_count < 2) { return pear_erm::r_top(); }
            uint a = s.m.operands[v.op_off];
            uint b = s.m.operands[v.op_off + 1];
            if ((usz)a >= s.n || (usz)b >= s.n) { return pear_erm::r_top(); }
            Range ra = s.r[a];
            Range rb = s.r[b];
            switch (v.p.op)
            {
                case ABO_ADD:  return radd(ra, rb);
                case ABO_SUB:  return rsub(ra, rb);
                case ABO_MUL:  return rmul(ra, rb);
                case ABO_DIV:  return rdiv(ra, rb);
                case ABO_MOD:  return rmod(ra, rb);
                case ABO_AND:  return rand(ra, rb);
                case ABO_OR:   return ror(ra, rb);
                case ABO_SHL:  return rshl(ra, rb);
                case ABO_SHR:  return rshr(ra, rb);
                case ABO_XOR:
                {
                    // Non-negative operands keep the sign; the magnitude
                    // bound follows the same all-ones fill as OR.
                    if (ra.is_top || rb.is_top || ra.lo < 0 || rb.lo < 0)
                    {
                        return pear_erm::r_top();
                    }
                    return ror(ra, rb);
                }
                /*
                 Comparisons yield 0 or 1 — and when the answer is already
                 decided by the operand ranges, the exact constant. That
                 constant is what sccp folds and what makes a bounds check
                 disappear.
                */
                case ABO_EQ:
                case ABO_NE:
                case ABO_LT:
                case ABO_LE:
                case ABO_GT:
                case ABO_GE:
                {
                    int d = decide(v.p.op, ra, rb);
                    if (d == 1) { return pear_erm::r_const(1); }
                    if (d == 0) { return pear_erm::r_const(0); }
                    return pear_erm::r_range(0, 1);
                }
                case ABO_LAND:
                case ABO_LOR:
                    return pear_erm::r_range(0, 1);
                /*
                 Checked arithmetic traps on overflow, so the value that
                 flows on is within the ordinary bound. Saturating clamps,
                 which the plain transfer function also models correctly
                 once overflow is excluded. WRAPPING must go to top: the
                 programmer explicitly opted out of the bound, and claiming
                 one would let a check they asked for be deleted.
                */
                case ABO_ADDC:
                case ABO_ADDS: return radd(ra, rb);
                case ABO_SUBC:
                case ABO_SUBS: return rsub(ra, rb);
                case ABO_MULC:
                case ABO_MULS: return rmul(ra, rb);
                default:       return pear_erm::r_top();
            }
        }

        case AIR_UN:
        {
            if (v.op_count < 1) { return pear_erm::r_top(); }
            uint a = s.m.operands[v.op_off];
            if ((usz)a >= s.n) { return pear_erm::r_top(); }
            Range ra = s.r[a];
            switch (v.p.uop)
            {
                case AUO_NEG:
                {
                    if (ra.is_top || ra.is_bottom) { return ra; }
                    if (ra.lo == LONG_MIN) { return pear_erm::r_top(); }
                    return pear_erm::r_range(-ra.hi, -ra.lo);
                }
                case AUO_NOT:  return pear_erm::r_range(0, 1);
                default:       return pear_erm::r_top();
            }
        }

        case AIR_CAST:
            // A cast's target width is a name, not a parsed width, so the
            // value cannot be narrowed here without re-deriving pfront's
            // type table. Pass the operand's range through unchanged: it is
            // sound for a widening cast and top-ward for a narrowing one.
            if (v.op_count >= 1)
            {
                uint a = s.m.operands[v.op_off];
                if ((usz)a < s.n) { return s.r[a]; }
            }
            return pear_erm::r_top();

        default:
            // Not computed by this analysis: keep whatever a1 seeded.
            return v.facts.range;
    }
}

/*
 Find the bound a σ was split on.

 The σ names the value being refined, not the comparison, so the
 comparison has to be recovered. It is the scrutinee of the terminator of
 the σ's block's single predecessor, and it has the σ's source as one
 operand; the OTHER operand is the bound.

 With `allow_symbolic`, a non-constant bound contributes the appropriate
 endpoint of its own current range — which is how `i < n` bounds `i` by
 `n`'s maximum. Without it, only literal bounds are used.
*/
/*
 The OTHER operand of the comparison a σ was split on -- the thing the
 σ's source is being compared against.

 The σ names the value being refined, not the comparison, so the
 comparison has to be recovered: it is the scrutinee of the terminator of
 the branching block, and it has the σ's source as one operand.

 Shared by sigma_bound (which wants one endpoint of it) and sigma_meet
 (which wants the whole interval), so the recovery walk exists once.
*/
fn bool Solver.sigma_other(Solver* s, uint sid, uint* out)
{
    Val* sv = s.m.val(sid);
    if (sv == null || sv.op_count < 1) { return false; }
    uint src = s.m.operands[sv.op_off];

    Blk* b = s.m.blk(sv.block);
    if (b == null) { return false; }

    // Walk back through the jump-only blocks a critical-edge split leaves
    // behind, to the block that actually branched.
    uint pb = sv.block;
    usz guard = 0;
    while (guard < 8)
    {
        guard = guard + 1;
        Blk* cur = s.m.blk(pb);
        if (cur == null || cur.pred_count != 1) { break; }
        pb = cur.pred[0];
        Blk* pbb = s.m.blk(pb);
        if (pbb == null) { break; }
        if (pbb.term == Term.TERM_BRANCH) { break; }
    }
    Blk* pbb = s.m.blk(pb);
    if (pbb == null || pbb.term != Term.TERM_BRANCH) { return false; }

    Val* cmp = s.m.val(pbb.term_value);
    if (cmp == null || cmp.op != Op.AIR_BIN || cmp.op_count < 2) { return false; }

    uint lhs = s.m.operands[cmp.op_off];
    uint rhs = s.m.operands[cmp.op_off + 1];
    if (lhs == src)      { *out = rhs; return true; }
    if (rhs == src)      { *out = lhs; return true; }
    return false;
}

/*
 Find the single number a σ refines against.

 With `allow_symbolic`, a non-constant bound contributes the appropriate
 endpoint of its own current range -- which is how `i < n` bounds `i` by
 `n`'s maximum. Without it, only literal bounds are used, because during
 widening a symbolic bound that is itself still climbing would make the
 transfer function non-monotone and the fixpoint would not settle.
*/
fn bool Solver.sigma_bound(Solver* s, uint sid, long* out, bool allow_symbolic)
{
    Val* sv = s.m.val(sid);
    if (sv == null) { return false; }

    uint other;
    if (!s.sigma_other(sid, &other)) { return false; }
    if ((usz)other >= s.n) { return false; }
    Range ro = s.r[other];
    if (pear_erm::r_is_const(&ro)) { *out = ro.lo; return true; }
    if (!allow_symbolic || ro.is_top || ro.is_bottom) { return false; }

    /*
     Symbolic bound. Which endpoint is sound depends on the direction of
     the refinement: `x < n` with n in [a,b] gives `x <= b-1`, so the
     UPPER endpoint is the one to use; `x > n` gives `x >= a+1`, the lower.
     Taking the wrong endpoint here is unsound, not merely imprecise.
    */
    switch (sv.p.fact)
    {
        case FACT_LT:
        case FACT_LE:
            *out = ro.hi;
            return true;
        case FACT_GT:
        case FACT_GE:
            *out = ro.lo;
            return true;
        default:
            /*
             EQ and NE cannot be expressed as a single bound against an
             interval, so they are handled by the caller through
             `sigma_meet` instead of here. Returning false is the honest
             answer to "what one number does this refine against"; it is
             not a statement that nothing is known.
            */
            return false;
    }
}

/*
 The refinement a σ imposes when its bound is an INTERVAL rather than a
 single number.

 `x == n` with n in [a,b] gives x in [a,b] — an intersection, not a
 comparison against one endpoint, so it does not fit the bound-based path
 above and was dropped on the floor entirely.

 Measured on stdlib/io.pie by counting the fact on every σ that reached
 this path: 73 lt, 39 ge, 13 gt, 1 le — all handled by sigma_bound — and
 8 eq plus 9 ne, which were not. So this recovers 8 refinements in that
 module, not the 26 an earlier version of this comment claimed: 26 was
 the count of σ evaluations rejected with a usable interval in hand, and
 most of those were rejected for the correct reason (a moving symbolic
 bound during widening), not for being EQ.

 Across the whole 233-module sweep the aggregate ranged-value count does
 not move at all. The fixture pear/a2/tests/ok_sigma_eq_symbolic.air is
 what proves the path works, because the standard library barely uses it.

 NE is included and deliberately does almost nothing: an interval domain
 cannot represent a hole, so `x != n` only narrows when n is a single
 point sitting on an endpoint of x's range. r_refine_ne already
 implements exactly that, and saying so is better than pretending the
 domain is more precise than it is.
*/
fn bool Solver.sigma_meet(Solver* s, uint sid, Range* out)
{
    Val* sv = s.m.val(sid);
    if (sv == null || sv.op_count < 1) { return false; }
    if (sv.p.fact != Fact.FACT_EQ && sv.p.fact != Fact.FACT_NE) { return false; }

    uint other;
    if (!s.sigma_other(sid, &other)) { return false; }
    if ((usz)other >= s.n) { return false; }
    Range ro = s.r[other];
    if (ro.is_top || ro.is_bottom) { return false; }

    if (sv.p.fact == Fact.FACT_EQ) { *out = ro; return true; }

    // NE: only a point bound can carve anything out of an interval.
    if (!pear_erm::r_is_const(&ro)) { return false; }
    *out = ro;
    return true;
}

/*
 Is this comparison already decided by the operand ranges?
 Returns 1 for always-true, 0 for always-false, -1 for unknown.
*/
fn int decide(BOp op, Range a, Range b)
{
    if (a.is_top || b.is_top || a.is_bottom || b.is_bottom) { return -1; }
    switch (op)
    {
        case ABO_LT:
            if (a.hi < b.lo) { return 1; }
            if (a.lo >= b.hi) { return 0; }
            return -1;
        case ABO_LE:
            if (a.hi <= b.lo) { return 1; }
            if (a.lo > b.hi) { return 0; }
            return -1;
        case ABO_GT:
            if (a.lo > b.hi) { return 1; }
            if (a.hi <= b.lo) { return 0; }
            return -1;
        case ABO_GE:
            if (a.lo >= b.hi) { return 1; }
            if (a.hi < b.lo) { return 0; }
            return -1;
        case ABO_EQ:
            if (a.hi < b.lo || b.hi < a.lo) { return 0; }
            if (a.lo == a.hi && b.lo == b.hi && a.lo == b.lo) { return 1; }
            return -1;
        case ABO_NE:
            if (a.hi < b.lo || b.hi < a.lo) { return 1; }
            if (a.lo == a.hi && b.lo == b.hi && a.lo == b.lo) { return 0; }
            return -1;
        default:
            return -1;
    }
}

/*
 Solve one strongly-connected component.

 A single-value component with no self-reference is just an evaluation. A
 real component is a loop, and gets the three-phase treatment: evaluate to
 a first approximation, widen to a fixed point, then narrow to recover.
*/
fn void Solver.solve_comp(Solver* s, int* members, usz count)
{
    if (count == 0) { return; }

    // Fast path: a single value that does not depend on itself.
    if (count == 1)
    {
        uint v = (uint)members[0];
        bool self = false;
        usz nd = s.dep_count(v);
        for (usz i = 0; i < nd; i++) { if (s.dep(v, i) == v) { self = true; } }
        if (!self)
        {
            s.r[v] = s.transfer(v, true);
            return;
        }
    }

    for (usz i = 0; i < count; i++) { s.in_scc[members[i]] = true; }

    /*
     Phase 1 — iterate, and only widen once plain iteration has had a fair
     chance to converge on its own.

     DELAYED WIDENING, and the delay is the whole point. Widening is a
     blunt instrument: it exists to guarantee termination, and it pays for
     that by throwing away any endpoint that moved. Applying it from the
     first iteration therefore destroys precision on every cycle that
     would have converged by itself — and many do, because a cycle whose
     transfer functions are contracting reaches its fixed point in two or
     three steps.

     WIDEN_AFTER is the number of plain passes granted first. Termination
     is unaffected: after the delay the operator is applied on every
     subsequent pass exactly as before, so the ascending chain is still
     finite. The delay only changes which fixed point is reached, never
     whether one is.

     ── What this is worth, measured rather than argued ─────────────────

     Almost nothing on this standard library, and the honest number is
     here so nobody re-derives it. Total ranged values across 233 modules:

         WIDEN_AFTER = 0   18,766      (widen from the first pass)
         WIDEN_AFTER = 1   18,724
         WIDEN_AFTER = 3   18,766      (the setting in use)
         WIDEN_AFTER = 8   18,779

     A 55-value spread over the whole library, and 0 above always-on
     widening. The reason is visible in the SCC distribution: on
     stdlib/io.pie the constraint graph has 2,159 components of which 27
     hold more than one value, and the largest holds 9. Delayed widening
     can only matter inside a multi-value component, and there are almost
     none — Pride's loops mostly carry their induction variable through a
     σ whose bound is already a literal, which the ordinary path handles.

     The delay is KEPT because it costs nothing (the same fixed point is
     reached, just occasionally more precisely) and because a language
     with more cyclic dataflow would benefit. It is not kept because it
     was measured to help here. It was not.
    */
    const usz WIDEN_AFTER = 3;

    usz cap = count * 4 + 16;
    usz iter = 0;
    bool changed = true;
    while (changed && iter < cap)
    {
        changed = false;
        bool do_widen = iter >= WIDEN_AFTER;
        iter = iter + 1;
        for (usz i = 0; i < count; i++)
        {
            uint v = (uint)members[i];
            Range nv = s.transfer(v, false);
            Range w = do_widen ? widen(s.r[v], nv) : nv;
            if (!pear_erm::r_eq(w, s.r[v]))
            {
                if (w.is_top && !s.r[v].is_top) { s.widened = s.widened + 1; }
                s.r[v] = w;
                changed = true;
            }
        }
    }

    /*
     Phase 2 — narrow.

     Now that every value in the component has a stable (if coarse) range,
     symbolic σ bounds can be consulted: the bound's own range no longer
     moves, so using it cannot break monotonicity. This is where `i < n`
     turns into a real upper bound on `i`.
    */
    iter = 0;
    changed = true;
    while (changed && iter < cap)
    {
        changed = false;
        iter = iter + 1;
        for (usz i = 0; i < count; i++)
        {
            uint v = (uint)members[i];
            Range nv = s.transfer(v, true);
            Range nr = narrow(s.r[v], nv);
            if (!pear_erm::r_eq(nr, s.r[v]))
            {
                s.r[v] = nr;
                changed = true;
            }
        }
    }

    for (usz i = 0; i < count; i++) { s.in_scc[members[i]] = false; }
}

/*
 Solve every component in topological order.

 Tarjan emits components in REVERSE topological order of the condensation,
 so a component's dependencies always have a LOWER component number. Going
 0..ncomp-1 therefore visits each component only after everything it reads
 is final, which is what makes one pass per component enough.
*/
/*
 Does `transfer` derive this value's range from its operands?

 The distinction decides how the value is SEEDED, and getting it wrong is
 what made the first version of this pass produce a garbage loop bound.

 A value the solver computes must start at BOTTOM so the fixpoint climbs to
 it from below. Seeding it with a1's answer instead poisons the widening
 operator: widening compares the old range against the new one, so if the
 old range is already an over-approximation the comparison sees no movement
 and the wrong bound is simply preserved. On `while i < 100` that left `i`
 at [-9223372036854775807, 100] — a1's single forward pass had joined the
 φ against a back edge it had not yet computed, and the solver dutifully
 kept it.

 A value the solver does NOT compute — a parameter, a load, a call result —
 keeps a1's seed, because a1 may know something from the source that the
 constraint graph cannot express.
*/
fn bool is_computed(Op op)
{
    switch (op)
    {
        case AIR_CONST_INT:
        case AIR_CONST_BOOL:
        case AIR_PHI:
        case AIR_SIGMA:
        case AIR_PI:
        case AIR_BIN:
        case AIR_UN:
        case AIR_CAST:
            return true;
        default:
            return false;
    }
}

fn void Solver.solve(Solver* s)
{
    /*
     Seed. Computed values start at bottom and climb; everything else keeps
     whatever a1 established.
    */
    for (usz i = 1; i < s.n; i++)
    {
        Val* v = &s.m.values[i];
        if (v.block == pear_air::AIR_NO_BLOCK) { continue; }
        s.r[i] = is_computed(v.op) ? pear_erm::r_bottom() : v.facts.range;
    }

    s.tarjan();

    // Bucket values by component.
    int* order = (int*)malloc((s.n == 0 ? 1 : s.n) * int::size);
    usz* start = (usz*)malloc(((usz)s.ncomp + 1) * usz::size);
    usz* fill  = (usz*)malloc(((usz)s.ncomp + 1) * usz::size);
    if (order == null || start == null || fill == null)
    {
        if (order != null) { free((void*)order); }
        if (start != null) { free((void*)start); }
        if (fill != null)  { free((void*)fill); }
        return;
    }
    for (usz i = 0; i <= (usz)s.ncomp; i++) { start[i] = 0; fill[i] = 0; }
    for (usz i = 1; i < s.n; i++)
    {
        if (s.comp[i] >= 0) { start[s.comp[i]] = start[s.comp[i]] + 1; }
    }
    usz run = 0;
    for (usz c = 0; c < (usz)s.ncomp; c++)
    {
        usz cnt = start[c];
        start[c] = run;
        run = run + cnt;
    }
    start[(usz)s.ncomp] = run;
    for (usz i = 1; i < s.n; i++)
    {
        int c = s.comp[i];
        if (c < 0) { continue; }
        order[start[c] + fill[c]] = (int)i;
        fill[c] = fill[c] + 1;
    }

    for (usz c = 0; c < (usz)s.ncomp; c++)
    {
        s.solve_comp(&order[start[c]], fill[c]);
    }

    free((void*)order); free((void*)start); free((void*)fill);
}

// ════════════════════════════════════════════════════════════════════════
// ENTRY POINT
// ════════════════════════════════════════════════════════════════════════

struct RangeStats
{
    usz values;
    usz ranged_before;
    usz ranged_after;
    usz improved;        // strictly tighter than a1's answer
    usz widened;         // needed widening: a loop-carried value
    usz decided_cmps;    // comparisons R now settles -- the payoff
    usz nonneg;          // values proven >= 0: what kills a bounds check
}

fn void RangeStats.init(RangeStats* st)
{
    st.values = 0; st.ranged_before = 0; st.ranged_after = 0;
    st.improved = 0; st.widened = 0; st.decided_cmps = 0; st.nonneg = 0;
}

/*
 Run the range analysis over a module and write the result back.

 The facts also go into the origin-keyed table, because that is the copy
 that survives to a3 (D1). Writing only to the values would mean every
 fact established here is lost at the first rewrite in a later stage.
*/
fn void run(Air* m, pear_a2_facts::Facts2* f, RangeStats* st)
{
    st.init();

    Solver s;
    if (!s.init(m)) { s.destroy(); return; }

    for (usz i = 1; i < m.value_count; i++)
    {
        Val* v = &m.values[i];
        if (v.block == pear_air::AIR_NO_BLOCK || v.is_phi_hole) { continue; }
        st.values = st.values + 1;
        if (!v.facts.range.is_top) { st.ranged_before = st.ranged_before + 1; }
    }

    s.solve();

    for (usz i = 1; i < m.value_count; i++)
    {
        Val* v = &m.values[i];
        if (v.block == pear_air::AIR_NO_BLOCK || v.is_phi_hole) { continue; }

        Range before = v.facts.range;
        Range after = s.r[i];

        /*
         Only ever TIGHTEN. If the solver came back with something looser
         than a1 had, keep a1's: the solver's answer is sound but a1 may
         have had a source-level fact (a literal's exact value, a declared
         width) that the constraint graph does not model.
        */
        Range best = pear_erm::r_meet(before, after);
        if (best.is_bottom && !before.is_bottom && !after.is_bottom)
        {
            // Disagreement, not a proof of unreachability. Keep the seed.
            best = before;
        }
        v.facts.range = best;

        if (!best.is_top) { st.ranged_after = st.ranged_after + 1; }
        if (!pear_erm::r_eq(best, before) && !before.is_top) { st.improved = st.improved + 1; }
        if (before.is_top && !best.is_top) { st.improved = st.improved + 1; }
        if (!best.is_top && !best.is_bottom && best.lo >= 0) { st.nonneg = st.nonneg + 1; }

        f.learn(v.origin, v.facts, pear_a2_facts::FactSource.FS_RANGE);
    }

    st.widened = s.widened;

    // The payoff, counted after the solve rather than claimed before it.
    for (usz i = 1; i < m.value_count; i++)
    {
        Val* v = &m.values[i];
        if (v.block == pear_air::AIR_NO_BLOCK || v.is_phi_hole) { continue; }
        if (v.op != Op.AIR_BIN || v.op_count < 2) { continue; }
        uint a = m.operands[v.op_off];
        uint b = m.operands[v.op_off + 1];
        Val* av = m.val(a);
        Val* bv = m.val(b);
        if (av == null || bv == null) { continue; }
        if (decide(v.p.op, av.facts.range, bv.facts.range) >= 0)
        {
            st.decided_cmps = st.decided_cmps + 1;
        }
    }

    s.destroy();
}

fn void print_stats(RangeStats* st)
{
    printf("  R: values        : %d\n", (int)st.values);
    printf("  R: ranged        : %d -> %d   (+%d)\n",
           (int)st.ranged_before, (int)st.ranged_after,
           (int)(st.ranged_after - st.ranged_before));
    printf("  R: tightened     : %d\n", (int)st.improved);
    printf("  R: widened       : %d   (loop-carried)\n", (int)st.widened);
    printf("  R: proven >= 0   : %d\n", (int)st.nonneg);
    printf("  >> decided cmps  : %d   (branches R settles outright)\n",
           (int)st.decided_cmps);
}
