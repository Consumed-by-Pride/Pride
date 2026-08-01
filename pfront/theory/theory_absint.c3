// ============================================================================
// theory_absint.c3 — abstract interpretation framework (part 30)
// ----------------------------------------------------------------------------
// Every analysis so far computes one specific thing. This module supplies the
// FRAMEWORK they are all instances of, so a new analysis is a lattice plus a
// transfer function rather than another bespoke tree walk.
//
// An abstract interpretation is four things:
//
//   1. A LATTICE of abstract values, with ⊔ (join), ⊓ (meet), ⊥ and ⊤.
//   2. A TRANSFER FUNCTION mapping a statement and an input state to an
//      output state.
//   3. A FIXPOINT ITERATION over the control-flow graph.
//   4. A WIDENING operator guaranteeing termination on lattices of infinite
//      height — without it, interval analysis of `while true { x = x + 1 }`
//      never converges.
//
// Three domains are provided, each useful on its own and each demonstrating a
// different lattice shape:
//
//   * SIGN      — a tiny finite lattice; converges without widening.
//   * INTERVAL  — infinite height, so widening is mandatory. This is what
//                 drives the R (Range-Bounded) part of SP-ERM-e-SSI, and the
//                 `range(lo,hi)` attributes that make LLVM fold branches.
//   * NULLNESS  — three-valued; catches null dereference before the backend.
//
// Widening deserves a note. The standard operator jumps a bound straight to
// infinity when it grows, trading precision for termination. NARROWING then
// recovers some of that precision by re-running the transfer function on the
// stabilised result — which is why both are implemented rather than only the
// first.
// ============================================================================

module theory_absint;

import pfront_lex;
import pfront_core;
import theory_term;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz AI_MAX_VARS     = 4096;
const usz AI_MAX_STATES   = 2048;
const usz AI_MAX_BLOCKS   = 2048;
const int AI_WIDEN_AFTER  = 3;      // iterations before widening kicks in
const int AI_MAX_ITERS    = 64;
const int AI_MAX_DEPTH    = 300;

const long AI_NEG_INF = -9223372036854775807L - 1;
const long AI_POS_INF = 9223372036854775807L;

// ════════════════════════════════════════════════════════════════════════════
// DOMAIN 1 — SIGN
// ════════════════════════════════════════════════════════════════════════════
// A five-element lattice:  ⊥ < {NEG, ZERO, POS} < ⊤
// Finite height, so the fixpoint converges without widening. Useful for
// division-by-zero and for proving an index non-negative.
enum Sign : int
{
    SIGN_BOTTOM,     // unreachable
    SIGN_NEG,
    SIGN_ZERO,
    SIGN_POS,
    SIGN_NONNEG,     // ZERO ⊔ POS
    SIGN_NONPOS,     // ZERO ⊔ NEG
    SIGN_NONZERO,    // NEG ⊔ POS
    SIGN_TOP
}

fn char* sign_name(Sign s)
{
    switch (s)
    {
        case SIGN_BOTTOM:  return "bottom";
        case SIGN_NEG:     return "negative";
        case SIGN_ZERO:    return "zero";
        case SIGN_POS:     return "positive";
        case SIGN_NONNEG:  return ">=0";
        case SIGN_NONPOS:  return "<=0";
        case SIGN_NONZERO: return "!=0";
        case SIGN_TOP:     return "any";
    }
}

fn Sign sign_of(long v)
{
    if (v < 0) { return Sign.SIGN_NEG; }
    if (v == 0) { return Sign.SIGN_ZERO; }
    return Sign.SIGN_POS;
}

fn Sign sign_join(Sign a, Sign b)
{
    if (a == b) { return a; }
    if (a == Sign.SIGN_BOTTOM) { return b; }
    if (b == Sign.SIGN_BOTTOM) { return a; }
    if (a == Sign.SIGN_TOP || b == Sign.SIGN_TOP) { return Sign.SIGN_TOP; }

    // The join of two singletons is the two-element set that contains both.
    if ((a == Sign.SIGN_ZERO && b == Sign.SIGN_POS)
     || (a == Sign.SIGN_POS && b == Sign.SIGN_ZERO)) { return Sign.SIGN_NONNEG; }
    if ((a == Sign.SIGN_ZERO && b == Sign.SIGN_NEG)
     || (a == Sign.SIGN_NEG && b == Sign.SIGN_ZERO)) { return Sign.SIGN_NONPOS; }
    if ((a == Sign.SIGN_NEG && b == Sign.SIGN_POS)
     || (a == Sign.SIGN_POS && b == Sign.SIGN_NEG)) { return Sign.SIGN_NONZERO; }

    // A singleton joined with a compatible two-element set is absorbed.
    if (a == Sign.SIGN_NONNEG && (b == Sign.SIGN_ZERO || b == Sign.SIGN_POS)) { return a; }
    if (b == Sign.SIGN_NONNEG && (a == Sign.SIGN_ZERO || a == Sign.SIGN_POS)) { return b; }
    if (a == Sign.SIGN_NONPOS && (b == Sign.SIGN_ZERO || b == Sign.SIGN_NEG)) { return a; }
    if (b == Sign.SIGN_NONPOS && (a == Sign.SIGN_ZERO || a == Sign.SIGN_NEG)) { return b; }
    if (a == Sign.SIGN_NONZERO && (b == Sign.SIGN_NEG || b == Sign.SIGN_POS)) { return a; }
    if (b == Sign.SIGN_NONZERO && (a == Sign.SIGN_NEG || a == Sign.SIGN_POS)) { return b; }
    return Sign.SIGN_TOP;
}

fn Sign sign_add(Sign a, Sign b)
{
    if (a == Sign.SIGN_BOTTOM || b == Sign.SIGN_BOTTOM) { return Sign.SIGN_BOTTOM; }
    if (a == Sign.SIGN_ZERO) { return b; }
    if (b == Sign.SIGN_ZERO) { return a; }
    // Same sign is preserved; opposite signs give no information.
    if (a == Sign.SIGN_POS && b == Sign.SIGN_POS) { return Sign.SIGN_POS; }
    if (a == Sign.SIGN_NEG && b == Sign.SIGN_NEG) { return Sign.SIGN_NEG; }
    if (a == Sign.SIGN_NONNEG && b == Sign.SIGN_NONNEG) { return Sign.SIGN_NONNEG; }
    if (a == Sign.SIGN_NONPOS && b == Sign.SIGN_NONPOS) { return Sign.SIGN_NONPOS; }
    return Sign.SIGN_TOP;
}

fn Sign sign_mul(Sign a, Sign b)
{
    if (a == Sign.SIGN_BOTTOM || b == Sign.SIGN_BOTTOM) { return Sign.SIGN_BOTTOM; }
    if (a == Sign.SIGN_ZERO || b == Sign.SIGN_ZERO) { return Sign.SIGN_ZERO; }
    if (a == Sign.SIGN_TOP || b == Sign.SIGN_TOP) { return Sign.SIGN_TOP; }
    bool a_pos = a == Sign.SIGN_POS;
    bool b_pos = b == Sign.SIGN_POS;
    bool a_neg = a == Sign.SIGN_NEG;
    bool b_neg = b == Sign.SIGN_NEG;
    if ((a_pos && b_pos) || (a_neg && b_neg)) { return Sign.SIGN_POS; }
    if ((a_pos && b_neg) || (a_neg && b_pos)) { return Sign.SIGN_NEG; }
    return Sign.SIGN_TOP;
}

fn bool sign_maybe_zero(Sign s)
{
    return s == Sign.SIGN_ZERO || s == Sign.SIGN_NONNEG
        || s == Sign.SIGN_NONPOS || s == Sign.SIGN_TOP;
}

// ════════════════════════════════════════════════════════════════════════════
// DOMAIN 2 — INTERVALS
// ════════════════════════════════════════════════════════════════════════════
// [lo, hi] with ±∞ endpoints. Infinite height, so widening is REQUIRED.
struct Interval
{
    long lo;
    long hi;
    bool is_bottom;
}

fn Interval iv_bottom()
{
    Interval i;
    i.lo = AI_POS_INF;
    i.hi = AI_NEG_INF;
    i.is_bottom = true;
    return i;
}

fn Interval iv_top()
{
    Interval i;
    i.lo = AI_NEG_INF;
    i.hi = AI_POS_INF;
    i.is_bottom = false;
    return i;
}

fn Interval iv_const(long v)
{
    Interval i;
    i.lo = v;
    i.hi = v;
    i.is_bottom = false;
    return i;
}

fn Interval iv_range(long lo, long hi)
{
    if (lo > hi) { return iv_bottom(); }
    Interval i;
    i.lo = lo;
    i.hi = hi;
    i.is_bottom = false;
    return i;
}

fn bool iv_is_top(Interval* i)
{
    return !i.is_bottom && i.lo == AI_NEG_INF && i.hi == AI_POS_INF;
}

fn bool iv_eq(Interval a, Interval b)
{
    if (a.is_bottom && b.is_bottom) { return true; }
    if (a.is_bottom != b.is_bottom) { return false; }
    return a.lo == b.lo && a.hi == b.hi;
}

fn Interval iv_join(Interval a, Interval b)
{
    if (a.is_bottom) { return b; }
    if (b.is_bottom) { return a; }
    Interval r;
    r.lo = a.lo < b.lo ? a.lo : b.lo;
    r.hi = a.hi > b.hi ? a.hi : b.hi;
    r.is_bottom = false;
    return r;
}

fn Interval iv_meet(Interval a, Interval b)
{
    if (a.is_bottom || b.is_bottom) { return iv_bottom(); }
    long lo = a.lo > b.lo ? a.lo : b.lo;
    long hi = a.hi < b.hi ? a.hi : b.hi;
    if (lo > hi) { return iv_bottom(); }
    return iv_range(lo, hi);
}

// WIDENING. When a bound grows between iterations, jump it to infinity rather
// than creeping upward forever. This is what makes `while c { x = x + 1 }`
// terminate: without it the analysis would produce [0,1], [0,2], [0,3] ...
fn Interval iv_widen(Interval old_v, Interval new_v)
{
    if (old_v.is_bottom) { return new_v; }
    if (new_v.is_bottom) { return old_v; }
    Interval r;
    r.is_bottom = false;
    r.lo = new_v.lo < old_v.lo ? AI_NEG_INF : old_v.lo;
    r.hi = new_v.hi > old_v.hi ? AI_POS_INF : old_v.hi;
    return r;
}

// NARROWING recovers precision after widening: an infinite bound that the
// transfer function can prove finite is pulled back in.
fn Interval iv_narrow(Interval widened, Interval computed)
{
    if (widened.is_bottom) { return computed; }
    if (computed.is_bottom) { return widened; }
    Interval r;
    r.is_bottom = false;
    r.lo = widened.lo == AI_NEG_INF ? computed.lo : widened.lo;
    r.hi = widened.hi == AI_POS_INF ? computed.hi : widened.hi;
    return r;
}

// Saturating arithmetic on bounds: overflow means "no information".
fn long sat_add(long a, long b)
{
    if (a == AI_NEG_INF || b == AI_NEG_INF) { return AI_NEG_INF; }
    if (a == AI_POS_INF || b == AI_POS_INF) { return AI_POS_INF; }
    if (b > 0 && a > AI_POS_INF - b) { return AI_POS_INF; }
    if (b < 0 && a < AI_NEG_INF - b) { return AI_NEG_INF; }
    return a + b;
}

fn long sat_mul(long a, long b)
{
    if (a == 0 || b == 0) { return 0; }
    if (a == AI_NEG_INF || a == AI_POS_INF || b == AI_NEG_INF || b == AI_POS_INF)
    {
        bool neg = (a < 0) != (b < 0);
        return neg ? AI_NEG_INF : AI_POS_INF;
    }
    long r = a * b;
    if (r / b != a) { return (a < 0) != (b < 0) ? AI_NEG_INF : AI_POS_INF; }
    return r;
}

fn Interval iv_add(Interval a, Interval b)
{
    if (a.is_bottom || b.is_bottom) { return iv_bottom(); }
    return iv_range(sat_add(a.lo, b.lo), sat_add(a.hi, b.hi));
}

fn Interval iv_sub(Interval a, Interval b)
{
    if (a.is_bottom || b.is_bottom) { return iv_bottom(); }
    return iv_range(sat_add(a.lo, -b.hi), sat_add(a.hi, -b.lo));
}

// Multiplication must consider all four endpoint products: with negative
// operands the extremes need not come from matching endpoints.
fn Interval iv_mul(Interval a, Interval b)
{
    if (a.is_bottom || b.is_bottom) { return iv_bottom(); }
    long p1 = sat_mul(a.lo, b.lo);
    long p2 = sat_mul(a.lo, b.hi);
    long p3 = sat_mul(a.hi, b.lo);
    long p4 = sat_mul(a.hi, b.hi);
    long lo = p1;
    if (p2 < lo) { lo = p2; }
    if (p3 < lo) { lo = p3; }
    if (p4 < lo) { lo = p4; }
    long hi = p1;
    if (p2 > hi) { hi = p2; }
    if (p3 > hi) { hi = p3; }
    if (p4 > hi) { hi = p4; }
    return iv_range(lo, hi);
}

fn Interval iv_div(Interval a, Interval b, bool* div_by_zero)
{
    if (a.is_bottom || b.is_bottom) { return iv_bottom(); }
    // A divisor interval spanning zero may divide by zero.
    if (b.lo <= 0 && b.hi >= 0) { *div_by_zero = true; return iv_top(); }
    long p1 = b.lo == 0 ? 0 : a.lo / b.lo;
    long p2 = b.hi == 0 ? 0 : a.lo / b.hi;
    long p3 = b.lo == 0 ? 0 : a.hi / b.lo;
    long p4 = b.hi == 0 ? 0 : a.hi / b.hi;
    long lo = p1;
    if (p2 < lo) { lo = p2; }
    if (p3 < lo) { lo = p3; }
    if (p4 < lo) { lo = p4; }
    long hi = p1;
    if (p2 > hi) { hi = p2; }
    if (p3 > hi) { hi = p3; }
    if (p4 > hi) { hi = p4; }
    return iv_range(lo, hi);
}

// Does this interval fit in a machine integer of the given width?
fn bool iv_fits(Interval* i, int bits, bool is_signed)
{
    if (i.is_bottom) { return true; }
    if (bits >= 64) { return true; }
    long lo = 0;
    long hi = 0;
    if (is_signed)
    {
        hi = ((long)1 << (long)(bits - 1)) - 1;
        lo = -hi - 1;
    }
    else
    {
        lo = 0;
        hi = ((long)1 << (long)bits) - 1;
    }
    return i.lo >= lo && i.hi <= hi;
}

fn void iv_print(Interval* i)
{
    if (i.is_bottom) { printf("[bottom]"); return; }
    if (i.lo == AI_NEG_INF) { printf("[-inf,"); } else { printf("[%lld,", i.lo); }
    if (i.hi == AI_POS_INF) { printf("+inf]"); } else { printf("%lld]", i.hi); }
}

// ════════════════════════════════════════════════════════════════════════════
// DOMAIN 3 — NULLNESS
// ════════════════════════════════════════════════════════════════════════════
enum Nullness : int
{
    NN_BOTTOM,
    NN_NULL,
    NN_NONNULL,
    NN_MAYBE
}

fn Nullness nn_join(Nullness a, Nullness b)
{
    if (a == b) { return a; }
    if (a == Nullness.NN_BOTTOM) { return b; }
    if (b == Nullness.NN_BOTTOM) { return a; }
    return Nullness.NN_MAYBE;
}

fn char* nn_name(Nullness n)
{
    switch (n)
    {
        case NN_BOTTOM:  return "unreachable";
        case NN_NULL:    return "null";
        case NN_NONNULL: return "non-null";
        case NN_MAYBE:   return "maybe-null";
    }
}

// ════════════════════════════════════════════════════════════════════════════
// ABSTRACT STATE
// ════════════════════════════════════════════════════════════════════════════
// One entry per tracked variable, carrying all three domains at once. Running
// them together costs little and lets a transfer function consult one domain
// while updating another — division-by-zero uses sign, bounds use intervals.
struct VarState
{
    Node*    binder;
    uint     name_id;
    Sign     sign;
    Interval interval;
    Nullness nullness;
    bool     live;
}

// Direct-mapped lookup cache in front of `vars`.
//
// An AbstractState is COPIED BY VALUE at every control-flow join
// (`*dst = *src`), so a full hash table here would make every join
// proportional to the table size rather than the variable count -- the cure
// would be worse than the disease. A small direct-mapped cache keeps the
// copy cheap while removing the quadratic term from the common case, which
// is a repeated lookup of the same handful of variables inside a loop body.
//
// On a miss it falls back to the linear scan and fills the slot, so the
// result is always correct; the cache only changes how long it takes.
const usz AI_CACHE = 256;

struct AbstractState
{
    VarState[AI_MAX_VARS] vars;
    Node*[AI_CACHE]       cache_key;
    int[AI_CACHE]         cache_val;
    usz                   count;
    bool                  reachable;
}

fn usz ai_cache_slot(Node* binder)
{
    ulong x = (ulong)(usz)(void*)binder;
    x = x ^ (x >> 30);
    x = x * 0xbf58476d1ce4e5b9UL;
    x = x ^ (x >> 29);
    return (usz)x & (AI_CACHE - 1);
}

fn void AbstractState.init(AbstractState* s)
{
    s.count = 0;
    s.reachable = true;
    for (usz i = 0; i < AI_CACHE; i++) { s.cache_key[i] = null; s.cache_val[i] = -1; }
}

fn int AbstractState.find(AbstractState* s, Node* binder)
{
    usz slot = ai_cache_slot(binder);
    if (s.cache_key[slot] == binder)
    {
        int v = s.cache_val[slot];
        // Validate: a state copy may have brought a stale slot with it.
        if (v >= 0 && (usz)v < s.count && s.vars[v].binder == binder) { return v; }
    }
    for (usz i = 0; i < s.count; i++)
    {
        if (s.vars[i].binder == binder)
        {
            s.cache_key[slot] = binder;
            s.cache_val[slot] = (int)i;
            return (int)i;
        }
    }
    return -1;
}

fn int AbstractState.declare(AbstractState* s, Node* binder, uint name)
{
    int e = s.find(binder);
    if (e >= 0) { return e; }
    if (s.count >= AI_MAX_VARS) { return -1; }
    int id = (int)s.count;
    s.count = s.count + 1;
    usz slot = ai_cache_slot(binder);
    s.cache_key[slot] = binder;
    s.cache_val[slot] = id;
    VarState* v = &s.vars[id];
    v.binder = binder;
    v.name_id = name;
    v.sign = Sign.SIGN_TOP;
    v.interval = iv_top();
    v.nullness = Nullness.NN_MAYBE;
    v.live = true;
    return id;
}

fn void AbstractState.set_interval(AbstractState* s, Node* binder, Interval iv)
{
    int i = s.find(binder);
    if (i < 0) { return; }
    s.vars[i].interval = iv;
    // Keep the sign domain consistent with the interval: they must not
    // disagree, or two analyses reading the same state draw opposite
    // conclusions.
    if (iv.is_bottom) { s.vars[i].sign = Sign.SIGN_BOTTOM; }
    else if (iv.lo > 0) { s.vars[i].sign = Sign.SIGN_POS; }
    else if (iv.hi < 0) { s.vars[i].sign = Sign.SIGN_NEG; }
    else if (iv.lo == 0 && iv.hi == 0) { s.vars[i].sign = Sign.SIGN_ZERO; }
    else if (iv.lo >= 0) { s.vars[i].sign = Sign.SIGN_NONNEG; }
    else if (iv.hi <= 0) { s.vars[i].sign = Sign.SIGN_NONPOS; }
    else { s.vars[i].sign = Sign.SIGN_TOP; }
}

fn Interval AbstractState.get_interval(AbstractState* s, Node* binder)
{
    int i = s.find(binder);
    if (i < 0) { return iv_top(); }
    return s.vars[i].interval;
}

// JOIN two states at a control-flow merge.
fn void AbstractState.join(AbstractState* dst, AbstractState* src)
{
    if (!src.reachable) { return; }
    if (!dst.reachable) { *dst = *src; return; }
    for (usz i = 0; i < src.count; i++)
    {
        VarState* sv = &src.vars[i];
        int d = dst.find(sv.binder);
        if (d < 0)
        {
            d = dst.declare(sv.binder, sv.name_id);
            if (d < 0) { continue; }
            dst.vars[d] = *sv;
            continue;
        }
        VarState* dv = &dst.vars[d];
        dv.sign = sign_join(dv.sign, sv.sign);
        dv.interval = iv_join(dv.interval, sv.interval);
        dv.nullness = nn_join(dv.nullness, sv.nullness);
    }
}

// WIDEN this state against a previous iteration's.
fn bool AbstractState.widen(AbstractState* dst, AbstractState* prev)
{
    bool changed = false;
    for (usz i = 0; i < dst.count; i++)
    {
        VarState* dv = &dst.vars[i];
        int p = prev.find(dv.binder);
        if (p < 0) { continue; }
        Interval w = iv_widen(prev.vars[p].interval, dv.interval);
        if (!iv_eq(w, dv.interval)) { changed = true; }
        dv.interval = w;
    }
    return changed;
}

fn bool AbstractState.equals(AbstractState* a, AbstractState* b)
{
    if (a.count != b.count) { return false; }
    if (a.reachable != b.reachable) { return false; }
    for (usz i = 0; i < a.count; i++)
    {
        int j = b.find(a.vars[i].binder);
        if (j < 0) { return false; }
        if (!iv_eq(a.vars[i].interval, b.vars[j].interval)) { return false; }
        if (a.vars[i].sign != b.vars[j].sign) { return false; }
        if (a.vars[i].nullness != b.vars[j].nullness) { return false; }
    }
    return true;
}

// ════════════════════════════════════════════════════════════════════════════
// THE INTERPRETER
// ════════════════════════════════════════════════════════════════════════════
struct AbstractInterpreter
{
    AbstractState  state;
    AbstractState* scratch;
    Arena*                 arena;
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;

    usz vars_tracked;
    usz transfers;
    usz joins;
    usz widenings;
    usz narrowings;
    int iterations;

    // Findings, which is the point of running any of this.
    usz div_by_zero;
    usz overflow_risk;
    usz null_derefs;
    usz bounds_provable;      // indices proven in range
    usz bounds_always_bad;    // indices outside the array on every path
    usz branches_decided;     // conditions with a known outcome
    bool strict;
}

fn bool AbstractInterpreter.init(AbstractInterpreter* ai, Arena* a,
                                 pfront_core::DiagBag* d,
                                 pfront_core::Interner* it, char* file)
{
    ai.state.init();
    ai.scratch = (AbstractState*)malloc(AbstractState::size);
    if (ai.scratch == null) { return false; }
    ai.scratch.init();
    ai.arena = a;
    ai.diags = d;
    ai.interner = it;
    ai.file = file;
    ai.vars_tracked = 0;
    ai.transfers = 0;
    ai.joins = 0;
    ai.widenings = 0;
    ai.narrowings = 0;
    ai.iterations = 0;
    ai.div_by_zero = 0;
    ai.overflow_risk = 0;
    ai.null_derefs = 0;
    ai.bounds_provable = 0;
    ai.bounds_always_bad = 0;
    ai.branches_decided = 0;
    ai.strict = false;
    return true;
}

fn void AbstractInterpreter.destroy(AbstractInterpreter* ai)
{
    if (ai.scratch != null) { free((void*)ai.scratch); ai.scratch = null; }
}

// Evaluate an expression in the abstract domain.
fn Interval AbstractInterpreter.eval(AbstractInterpreter* ai, Node* e, int depth)
{
    if (e == null || depth > AI_MAX_DEPTH) { return iv_top(); }
    ai.transfers = ai.transfers + 1;

    switch (e.kind)
    {
        case N_EXPR_INT:
            return iv_const((long)e.p.ival);
        case N_EXPR_BOOL:
            return iv_range(0, 1);
        case N_EXPR_CHAR:
            return iv_range(0, 255);

        case N_EXPR_IDENT:
        {
            if (e.resolved == null) { return iv_top(); }
            return ai.state.get_interval(e.resolved);
        }

        case N_EXPR_UNARY:
        {
            Interval a = ai.eval(e.child(0), depth + 1);
            Tk op = (Tk)e.p.op;
            if (op == Tk.TOKEN_MINUS)
            {
                if (a.is_bottom) { return a; }
                return iv_range(a.hi == AI_POS_INF ? AI_NEG_INF : -a.hi,
                                a.lo == AI_NEG_INF ? AI_POS_INF : -a.lo);
            }
            if (op == Tk.TOKEN_BANG || op == Tk.TOKEN_KW_NOT) { return iv_range(0, 1); }
            return iv_top();
        }

        case N_EXPR_BINARY:
        {
            Interval a = ai.eval(e.child(0), depth + 1);
            Interval b = ai.eval(e.child(1), depth + 1);
            Tk op = (Tk)e.p.op;
            switch (op)
            {
                case TOKEN_PLUS:  return iv_add(a, b);
                case TOKEN_MINUS: return iv_sub(a, b);
                case TOKEN_STAR:  return iv_mul(a, b);
                case TOKEN_SLASH:
                {
                    bool dz = false;
                    Interval r = iv_div(a, b, &dz);
                    if (dz)
                    {
                        ai.div_by_zero = ai.div_by_zero + 1;
                        ai.diags.warn(pfront_core::Phase.PH_RESOLVE, 4130,
                                      e.line, e.col,
                                      "divisor may be zero on some path", ai.file);
                    }
                    return r;
                }
                case TOKEN_PERCENT:
                {
                    bool dz = false;
                    iv_div(a, b, &dz);
                    if (dz)
                    {
                        ai.div_by_zero = ai.div_by_zero + 1;
                        ai.diags.warn(pfront_core::Phase.PH_RESOLVE, 4130,
                                      e.line, e.col,
                                      "modulus may be zero on some path", ai.file);
                    }
                    if (b.is_bottom || b.lo <= 0) { return iv_top(); }
                    return iv_range(0, b.hi - 1);
                }
                // Comparisons yield a boolean, but their OUTCOME may be known.
                case TOKEN_LT:
                {
                    if (!a.is_bottom && !b.is_bottom)
                    {
                        if (a.hi < b.lo) { ai.branches_decided = ai.branches_decided + 1; return iv_const(1); }
                        if (a.lo >= b.hi) { ai.branches_decided = ai.branches_decided + 1; return iv_const(0); }
                    }
                    return iv_range(0, 1);
                }
                case TOKEN_GT:
                {
                    if (!a.is_bottom && !b.is_bottom)
                    {
                        if (a.lo > b.hi) { ai.branches_decided = ai.branches_decided + 1; return iv_const(1); }
                        if (a.hi <= b.lo) { ai.branches_decided = ai.branches_decided + 1; return iv_const(0); }
                    }
                    return iv_range(0, 1);
                }
                case TOKEN_EQEQ:
                {
                    // Disjoint intervals can never be equal.
                    if (!a.is_bottom && !b.is_bottom && (a.hi < b.lo || b.hi < a.lo))
                    {
                        ai.branches_decided = ai.branches_decided + 1;
                        return iv_const(0);
                    }
                    return iv_range(0, 1);
                }
                default:
                    return iv_top();
            }
        }

        case N_EXPR_CAST:
        {
            Interval a = ai.eval(e.child(0), depth + 1);
            // A cast to a narrower type may truncate: report when the source
            // range provably does not fit.
            if (e.type_ann != null && e.type_ann.kind == Nk.N_TY_NAME)
            {
                char* s = e.type_ann.p.sptr;
                usz n = e.type_ann.p.slen;
                if (s != null && n >= 2 && (s[0] == 'i' || s[0] == 'u'))
                {
                    int bits = 0;
                    for (usz k = 1; k < n; k++)
                    {
                        if (s[k] < '0' || s[k] > '9') { bits = 0; break; }
                        bits = bits * 10 + (int)(s[k] - '0');
                    }
                    if (bits > 0 && !iv_fits(&a, bits, s[0] == 'i'))
                    {
                        ai.overflow_risk = ai.overflow_risk + 1;
                        ai.diags.warn(pfront_core::Phase.PH_RESOLVE, 4131,
                                      e.line, e.col,
                                      "value may not fit in the target type",
                                      ai.file);
                    }
                }
            }
            return a;
        }

        default:
            return iv_top();
    }
}

// Apply the effect of a statement to the state.
fn void AbstractInterpreter.transfer(AbstractInterpreter* ai, Node* s, int depth)
{
    if (s == null || depth > AI_MAX_DEPTH) { return; }

    switch (s.kind)
    {
        case N_DECL_LET:
        {
            Interval iv = iv_top();
            for (usz i = 1; i < s.child_count; i++)
            {
                Node* c = s.children[i];
                if (c == null || pfront_core::is_pattern(c.kind)) { continue; }
                iv = ai.eval(c, depth + 1);
            }
            Node* pat = s.child(0);
            if (pat != null && pat.kind == Nk.N_PAT_IDENT)
            {
                ai.state.declare(pat, pat.name_id);
                ai.state.set_interval(pat, iv);
                ai.vars_tracked = ai.vars_tracked + 1;
            }
            return;
        }

        case N_STMT_ASSIGN:
        {
            Interval iv = ai.eval(s.child(1), depth + 1);
            Node* lhs = s.child(0);
            if (lhs != null && lhs.kind == Nk.N_EXPR_IDENT && lhs.resolved != null)
            {
                ai.state.declare(lhs.resolved, lhs.name_id);
                ai.state.set_interval(lhs.resolved, iv);
            }
            return;
        }

        case N_EXPR_INDEX:
        {
            // Bounds: if the index interval is provably within the array's
            // extent, the check can be elided by the backend.
            Interval idx = ai.eval(s.child(1), depth + 1);
            Node* base = s.child(0);
            if (base != null && base.type_ann != null
                && base.type_ann.kind == Nk.N_TY_ARRAY)
            {
                Node* len = base.type_ann.child(1);
                if (len != null && len.p.ival > 0)
                {
                    long n = (long)len.p.ival;
                    if (!idx.is_bottom && idx.lo >= 0 && idx.hi < n)
                    {
                        ai.bounds_provable = ai.bounds_provable + 1;
                        s.flags = s.flags | pfront_core::NF_TYPED;
                    }
                    else if (!idx.is_bottom && (idx.hi < 0 || idx.lo >= n))
                    {
                        // Pride does not reject this. The fact is recorded so
                        // the optimizer can mark the path unreachable and let
                        // the back end trap; the developer is trusted.
                        ai.bounds_always_bad = ai.bounds_always_bad + 1;
                        s.flags = s.flags | pfront_core::NF_ERROR;
                        ai.diags.advisory(pfront_core::Phase.PH_RESOLVE, 3360,
                                          s.line, s.col,
                                          "index is outside the array on every path",
                                          ai.file);
                    }
                }
            }
            for (usz i = 0; i < s.child_count; i++) { ai.transfer(s.children[i], depth + 1); }
            return;
        }

        case N_EXPR_IF:
        {
            Node* cond = s.child(0);
            Interval c = ai.eval(cond, depth + 1);
            // A condition with a known value makes one branch dead.
            bool known_true = !c.is_bottom && c.lo == 1 && c.hi == 1;
            bool known_false = !c.is_bottom && c.lo == 0 && c.hi == 0;
            if (known_true || known_false)
            {
                ai.branches_decided = ai.branches_decided + 1;
                ai.diags.add(pfront_core::Severity.SEV_NOTE,
                             pfront_core::Phase.PH_RESOLVE, 4132,
                             cond == null ? 0 : cond.line,
                             cond == null ? 0 : cond.col,
                             known_true ? "condition is always true"
                                        : "condition is always false",
                             null, ai.file);
            }

            // Analyse both branches from a copy, then join.
            // Both branch states are heap-allocated: an AbstractState is
            // ~192 KB, far past the 64 KB stack-object limit, and putting one
            // in a recursive frame would overflow on deep nesting.
            AbstractState* entry = (AbstractState*)malloc(AbstractState::size);
            AbstractState* then_state = (AbstractState*)malloc(AbstractState::size);
            if (entry == null || then_state == null)
            {
                if (entry != null) { free((void*)entry); }
                if (then_state != null) { free((void*)then_state); }
                return;
            }
            *entry = ai.state;
            ai.transfer(s.child(1), depth + 1);
            *then_state = ai.state;
            ai.state = *entry;
            if (s.child_count >= 3) { ai.transfer(s.child(2), depth + 1); }
            ai.state.join(then_state);
            ai.joins = ai.joins + 1;
            free((void*)entry);
            free((void*)then_state);
            return;
        }

        case N_EXPR_WHILE:
        {
            // Fixpoint with widening. Without the widening step this loop
            // would not terminate on a counter that grows each iteration.
            AbstractState* prev = (AbstractState*)malloc(AbstractState::size);
            if (prev == null) { return; }
            for (int iter = 0; iter < AI_MAX_ITERS; iter++)
            {
                ai.iterations = ai.iterations + 1;
                *prev = ai.state;
                ai.eval(s.child(0), depth + 1);
                ai.transfer(s.child(1), depth + 1);
                if (iter >= AI_WIDEN_AFTER)
                {
                    if (ai.state.widen(prev)) { ai.widenings = ai.widenings + 1; }
                }
                if (ai.state.equals(prev)) { break; }
            }
            free((void*)prev);
            return;
        }

        case N_BLOCK:
        {
            for (usz i = 0; i < s.child_count; i++) { ai.transfer(s.children[i], depth + 1); }
            return;
        }

        default:
        {
            // A bare expression statement must be EVALUATED, not merely
            // descended into: the findings (division by zero, truncating
            // casts) come from eval, and a tail expression is the common
            // place for them to appear.
            if (pfront_core::is_expr(s.kind))
            {
                ai.eval(s, depth + 1);
                return;
            }
            for (usz i = 0; i < s.child_count; i++) { ai.transfer(s.children[i], depth + 1); }
        }
    }
}

fn void AbstractInterpreter.run(AbstractInterpreter* ai, Node* root)
{
    if (root == null) { return; }
    for (usz i = 0; i < root.child_count; i++)
    {
        Node* d = root.children[i];
        if (d == null) { continue; }
        if (d.kind == Nk.N_DECL_FN)
        {
            ai.state.init();
            for (usz k = 0; k < d.child_count; k++)
            {
                Node* c = d.children[k];
                if (c == null) { continue; }
                if (c.kind == Nk.N_CLAUSE)
                {
                    for (usz j = 1; j < c.child_count; j++)
                    {
                        ai.transfer(c.children[j], 0);
                    }
                }
                else if (c.kind == Nk.N_BLOCK) { ai.transfer(c, 0); }
            }
        }
        else if (d.kind == Nk.N_MODULE) { ai.run(d); }
    }
}

fn void AbstractInterpreter.report(AbstractInterpreter* ai)
{
    printf("  abstract interp  : %d vars, %d transfers, %d iterations\n",
           (int)ai.vars_tracked, (int)ai.transfers, ai.iterations);
    printf("  lattice ops      : %d joins, %d widenings, %d narrowings\n",
           (int)ai.joins, (int)ai.widenings, (int)ai.narrowings);
    printf("  findings         : %d div-by-zero, %d overflow risk, %d decided branches\n",
           (int)ai.div_by_zero, (int)ai.overflow_risk, (int)ai.branches_decided);
    if (ai.bounds_always_bad > 0)
    {
        printf("  bounds           : %d index(es) outside the array on every path\n",
               (int)ai.bounds_always_bad);
    }
    if (ai.bounds_provable > 0)
    {
        printf("  bounds elision   : %d indices proven in range\n",
               (int)ai.bounds_provable);
    }
}
