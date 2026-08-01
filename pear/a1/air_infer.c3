/*
 ERM inference over AIR — the SP classification and the R transfer
 functions.

 a1's job is to SEED the facts; a2 refines them to a fixpoint with widening.
 The split matters: a1 runs once, in one forward pass, and must not iterate
 — a construction pass that loops to a fixpoint is a1 doing a2's job, and
 that is how build passes become unmaintainable.

 What is here:
   SP   classify every value by whether it is live across a block boundary,
        which is the semi-pruned filter that decides where a φ is needed
   R    transfer functions for the arithmetic opcodes, so a range derived
        from constants propagates through the expression tree in one pass
   M    a linear memory-versioning walk, so every load names the store it
        reads before a2 ever runs

 The measured payoff is reported by `--erm-stats`, flattering or not: how
 many values ended with a non-trivial range, how many pointers are provably
 nonnull, how many memory versions exist. Those numbers are the honest test
 of whether ERM is real or decorative.
*/

module pear_infer;

import pear_air;
import pear_erm;
import pfront_core;

alias Air  = pear_air::AirModule;
alias Val  = pear_air::AirValue;
alias Blk  = pear_air::AirBlock;
alias Fn   = pear_air::AirFunc;
alias Op   = pear_air::AirOp;
alias Term = pear_air::AirTerm;

extern fn int   printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn void  free(void* p);

// ════════════════════════════════════════════════════════════════════════
// SP — SEMI-PRUNED CLASSIFICATION
// ════════════════════════════════════════════════════════════════════════

/*
 A value is NON-LOCAL if it is used in a block other than the one that
 defines it. Only non-local values can need a φ.

 Briggs/Cooper/Harvey/Simpson's semi-pruned form: cheaper than pruned
 (which needs full liveness) and far cheaper than minimal-with-dead-φ.
 theory_live.c3 measured 53% of stdlib variables never crossing a block
 boundary, so this filter roughly halves the φ count before any φ is placed.

 Recording it per value rather than in a side set makes the placement
 decision auditable: the .air text says which values were considered
 non-local, so a wrong φ count can be traced to a wrong classification
 rather than to the placement algorithm.
*/
fn void classify_sp(Air* m, Fn* f, usz* out_nonlocal, usz* out_local)
{
    usz nonlocal = 0;
    usz local = 0;

    for (usz bi = 0; bi < f.block_count; bi++)
    {
        Blk* b = m.blk(f.blocks[bi]);
        if (b == null) { continue; }

        for (usz vi = 0; vi < b.value_count; vi++)
        {
            uint vid = b.values[vi];
            Val* v = m.val(vid);
            if (v == null) { continue; }

            bool crosses = false;

            // Used by a value in another block?
            for (usz obi = 0; obi < f.block_count && !crosses; obi++)
            {
                uint other = f.blocks[obi];
                if (other == b.id) { continue; }
                Blk* ob = m.blk(other);
                if (ob == null) { continue; }
                for (usz ovi = 0; ovi < ob.value_count && !crosses; ovi++)
                {
                    Val* ov = m.val(ob.values[ovi]);
                    if (ov == null) { continue; }
                    for (usz oi = 0; oi < ov.op_count; oi++)
                    {
                        if (m.operands[ov.op_off + oi] == vid) { crosses = true; break; }
                    }
                }
                // Or by another block's terminator.
                if (!crosses && ob.term_value == vid) { crosses = true; }
            }

            /*
             A φ operand is evaluated on the EDGE, so a value feeding a φ
             is live out of its own block by definition — even when the φ
             is in the immediately following block.
            */
            if (v.op == Op.AIR_PHI || v.op == Op.AIR_MEM_PHI) { crosses = true; }

            v.facts.crosses_block = crosses;
            if (crosses) { nonlocal = nonlocal + 1; } else { local = local + 1; }
        }
    }

    if (out_nonlocal != null) { *out_nonlocal = nonlocal; }
    if (out_local != null) { *out_local = local; }
}

// ════════════════════════════════════════════════════════════════════════
// R — TRANSFER FUNCTIONS
// ════════════════════════════════════════════════════════════════════════

/*
 Interval arithmetic with explicit overflow bail-out.

 Every operation that could overflow 64 bits returns top instead of
 wrapping. A wrapped bound is not conservative — it is WRONG, and a wrong
 range is far worse than no range, because a2 will delete a check on the
 strength of it. This is the one place in the ERM layer where being
 imprecise is mandatory and being clever is a correctness bug.
*/
fn bool add_overflows(long a, long b)
{
    if (b > 0 && a > (long)0x7FFFFFFFFFFFFFFF - b) { return true; }
    if (b < 0 && a < (long)0x8000000000000000 - b) { return true; }
    return false;
}

fn bool mul_overflows(long a, long b)
{
    if (a == 0 || b == 0) { return false; }
    long r = a * b;
    return r / b != a;
}

fn pear_erm::Range range_add(pear_erm::Range a, pear_erm::Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    if (a.is_top || b.is_top) { return pear_erm::r_top(); }
    if (add_overflows(a.lo, b.lo) || add_overflows(a.hi, b.hi))
    {
        return pear_erm::r_top();
    }
    return pear_erm::r_range(a.lo + b.lo, a.hi + b.hi);
}

fn pear_erm::Range range_sub(pear_erm::Range a, pear_erm::Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    if (a.is_top || b.is_top) { return pear_erm::r_top(); }
    if (add_overflows(a.lo, -b.hi) || add_overflows(a.hi, -b.lo))
    {
        return pear_erm::r_top();
    }
    return pear_erm::r_range(a.lo - b.hi, a.hi - b.lo);
}

/*
 Multiplication needs all four corner products, because a negative operand
 flips the ordering. Taking lo*lo and hi*hi alone is a classic and silent
 error: [-2,3] * [-2,3] would give [4,9] instead of [-6,9].
*/
fn pear_erm::Range range_mul(pear_erm::Range a, pear_erm::Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    if (a.is_top || b.is_top) { return pear_erm::r_top(); }
    if (mul_overflows(a.lo, b.lo) || mul_overflows(a.lo, b.hi)
     || mul_overflows(a.hi, b.lo) || mul_overflows(a.hi, b.hi))
    {
        return pear_erm::r_top();
    }
    long p1 = a.lo * b.lo;
    long p2 = a.lo * b.hi;
    long p3 = a.hi * b.lo;
    long p4 = a.hi * b.hi;
    long lo = p1;
    long hi = p1;
    if (p2 < lo) { lo = p2; }  if (p2 > hi) { hi = p2; }
    if (p3 < lo) { lo = p3; }  if (p3 > hi) { hi = p3; }
    if (p4 < lo) { lo = p4; }  if (p4 > hi) { hi = p4; }
    return pear_erm::r_range(lo, hi);
}

/*
 Division. A divisor interval that straddles zero yields top rather than a
 fabricated bound, and INT64_MIN / -1 is excluded because it overflows.
*/
fn pear_erm::Range range_div(pear_erm::Range a, pear_erm::Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    if (a.is_top || b.is_top) { return pear_erm::r_top(); }
    if (b.lo <= 0 && b.hi >= 0) { return pear_erm::r_top(); }   // may divide by zero
    if (a.lo == (long)0x8000000000000000 && b.lo <= -1 && b.hi >= -1)
    {
        return pear_erm::r_top();
    }
    long q1 = a.lo / b.lo;
    long q2 = a.lo / b.hi;
    long q3 = a.hi / b.lo;
    long q4 = a.hi / b.hi;
    long lo = q1; long hi = q1;
    if (q2 < lo) { lo = q2; }  if (q2 > hi) { hi = q2; }
    if (q3 < lo) { lo = q3; }  if (q3 > hi) { hi = q3; }
    if (q4 < lo) { lo = q4; }  if (q4 > hi) { hi = q4; }
    return pear_erm::r_range(lo, hi);
}

// Bitwise AND with a constant mask bounds the result by the mask.
fn pear_erm::Range range_and(pear_erm::Range a, pear_erm::Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    // x & m, with m a non-negative constant, gives [0, m].
    if (!b.is_top && b.lo == b.hi && b.lo >= 0) { return pear_erm::r_range(0, b.lo); }
    if (!a.is_top && a.lo == a.hi && a.lo >= 0) { return pear_erm::r_range(0, a.lo); }
    return pear_erm::r_top();
}

// x % m, with m a positive constant, gives [0, m-1] for non-negative x.
fn pear_erm::Range range_mod(pear_erm::Range a, pear_erm::Range b)
{
    if (a.is_bottom || b.is_bottom) { return pear_erm::r_bottom(); }
    if (b.is_top || b.lo != b.hi || b.lo <= 0) { return pear_erm::r_top(); }
    if (!a.is_top && a.lo >= 0) { return pear_erm::r_range(0, b.lo - 1); }
    return pear_erm::r_range(-(b.lo - 1), b.lo - 1);
}

/*
 Apply the transfer function for one value, from its operands' facts.

 One forward pass, no iteration. A φ joins whatever its operands already
 have — on a back edge that operand may still be top, and a1 accepts the
 weaker answer rather than looping. a2 is where the fixpoint happens.
*/
fn void infer_value(Air* m, uint vid)
{
    Val* v = m.val(vid);
    if (v == null) { return; }

    switch (v.op)
    {
        case AIR_CONST_INT:
            // Already seeded by set_const_int; re-derive so a hand-written
            // .air file that only gave ival still gets a range.
            if (v.facts.range.is_top)
            {
                v.facts.range = pear_erm::r_const(v.p.ival);
                v.facts.bits = pear_erm::kb_const(v.p.ival);
            }

        case AIR_CONST_BOOL:
            v.facts.range = pear_erm::r_range(0, 1);
            v.facts.width = 1;

        case AIR_CONST_NULL:
            v.facts.nullness = pear_erm::Nullness.NULL_ALWAYS;

        case AIR_BIN:
        {
            if (v.op_count < 2) { break; }
            Val* a = m.val(m.operands[v.op_off]);
            Val* b = m.val(m.operands[v.op_off + 1]);
            if (a == null || b == null) { break; }
            pear_erm::Range ra = a.facts.range;
            pear_erm::Range rb = b.facts.range;
            switch (v.p.op)
            {
                case ABO_ADD: v.facts.range = range_add(ra, rb);
                case ABO_SUB: v.facts.range = range_sub(ra, rb);
                case ABO_MUL: v.facts.range = range_mul(ra, rb);
                case ABO_DIV: v.facts.range = range_div(ra, rb);
                case ABO_MOD: v.facts.range = range_mod(ra, rb);
                case ABO_AND: v.facts.range = range_and(ra, rb);
                /*
                 WRAPPING arithmetic: the result is defined but can be any
                 value of the type, so the range MUST go to top. Reusing
                 the plain transfer function here would claim a bound the
                 programmer explicitly opted out of, and a2 would then
                 delete a check on the strength of it.
                */
                case ABO_ADDW:
                case ABO_SUBW:
                case ABO_MULW:
                    v.facts.range = pear_erm::r_top();

                /*
                 CHECKED arithmetic traps or reports on overflow, so the
                 non-trapping result IS within the ordinary bound — the
                 same transfer function as the plain operator, plus a
                 may-fault marker for E.
                */
                case ABO_ADDC:
                    v.facts.range = range_add(ra, rb);
                    v.facts.may_fault = true;
                case ABO_SUBC:
                    v.facts.range = range_sub(ra, rb);
                    v.facts.may_fault = true;
                case ABO_MULC:
                    v.facts.range = range_mul(ra, rb);
                    v.facts.may_fault = true;

                /*
                 SATURATING arithmetic clamps at the type bound, so the
                 result is bounded even when the inputs are not. Without a
                 declared width the clamp point is unknown, so this stays
                 top rather than guessing 64-bit.
                */
                case ABO_ADDS:
                case ABO_SUBS:
                case ABO_MULS:
                    v.facts.range = pear_erm::r_top();

                case ABO_EQ:
                case ABO_NE:
                case ABO_LT:
                case ABO_LE:
                case ABO_GT:
                case ABO_GE:
                case ABO_LAND:
                case ABO_LOR:
                    v.facts.range = pear_erm::r_range(0, 1);
                    v.facts.width = 1;
                default:
                    break;
            }
        }

        case AIR_PHI:
        {
            /*
             Join every operand. This is where R pays for itself on a loop:
             a counter initialised to 0 and incremented by 1 gets [0, top]
             on the first pass, and a2's widening then bounds it by the
             loop guard.
            */
            if (v.op_count == 0) { break; }
            pear_erm::Facts acc = pear_erm::facts_unknown();
            bool first = true;
            for (usz i = 0; i < v.op_count; i++)
            {
                Val* o = m.val(m.operands[v.op_off + i]);
                if (o == null) { continue; }
                if (first) { acc = o.facts; first = false; }
                else       { acc = pear_erm::facts_join(acc, o.facts); }
            }
            if (!first)
            {
                // Keep the memory and SP fields the φ already has; only the
                // value lattice is joined.
                pear_erm::MemFact keep_mem = v.facts.mem;
                bool keep_sp = v.facts.crosses_block;
                v.facts = acc;
                v.facts.mem = keep_mem;
                v.facts.crosses_block = keep_sp;
            }
        }

        case AIR_SIGMA:
        {
            /*
             A σ inherits the source's facts, then narrows them using the
             bound it was split on.

             Finding that bound is the whole trick. The σ names the value
             being split, not the comparison, so scan this block for the
             comparison that (a) is the terminator's scrutinee and (b) has
             our source as an operand. Its other operand is the bound.

             This is the concrete payoff of e-SSA: on the true edge of
             `if x > 0` the σ-renamed x has range [1, MAX], and every
             downstream use sees that WITHOUT re-deriving it. LLVM has no
             name for this value, so a consumer must ask a predicate-aware
             analysis at each use site.
            */
            if (v.op_count < 1) { break; }
            uint src_id = m.operands[v.op_off];
            Val* src = m.val(src_id);
            if (src == null) { break; }
            if (v.facts.range.is_top) { v.facts.range = src.facts.range; }

            Blk* b = m.blk(v.block);
            if (b == null) { break; }
            if (b.term != Term.TERM_BRANCH) { break; }
            Val* cmp = m.val(b.term_value);
            if (cmp == null || cmp.op != Op.AIR_BIN || cmp.op_count < 2) { break; }

            uint lhs = m.operands[cmp.op_off];
            uint rhs = m.operands[cmp.op_off + 1];
            uint bound_id = 0;
            bool src_on_left = false;
            if (lhs == src_id)      { bound_id = rhs; src_on_left = true; }
            else if (rhs == src_id) { bound_id = lhs; src_on_left = false; }
            else { break; }

            Val* bv = m.val(bound_id);
            if (bv == null) { break; }
            if (!pear_erm::r_is_const(&bv.facts.range)) { break; }
            long bound = bv.facts.range.lo;

            /*
             The σ's own fact says which EDGE it guards, and that already
             accounts for the comparison's direction and for the negation
             on the false edge. Applying it directly is right when the
             source is on the left of the comparison; when it is on the
             right the relation flips (`0 < x` constrains x the way
             `x > 0` does).
            */
            pear_air::AirFact eff = v.p.fact;
            if (!src_on_left)
            {
                switch (eff)
                {
                    case FACT_LT: eff = pear_air::AirFact.FACT_GT;
                    case FACT_LE: eff = pear_air::AirFact.FACT_GE;
                    case FACT_GT: eff = pear_air::AirFact.FACT_LT;
                    case FACT_GE: eff = pear_air::AirFact.FACT_LE;
                    default: break;
                }
            }
            switch (eff)
            {
                case FACT_LT: v.facts.range = pear_erm::r_refine_lt(v.facts.range, bound);
                case FACT_LE: v.facts.range = pear_erm::r_refine_le(v.facts.range, bound);
                case FACT_GT: v.facts.range = pear_erm::r_refine_gt(v.facts.range, bound);
                case FACT_GE: v.facts.range = pear_erm::r_refine_ge(v.facts.range, bound);
                case FACT_EQ: v.facts.range = pear_erm::r_refine_eq(v.facts.range, bound);
                case FACT_NE: v.facts.range = pear_erm::r_refine_ne(v.facts.range, bound);
                case FACT_NONNULL: v.facts.nullness = pear_erm::Nullness.NULL_NEVER;
                case FACT_NULL:    v.facts.nullness = pear_erm::Nullness.NULL_ALWAYS;
                default: break;
            }
        }

        case AIR_PI:
        {
            /*
             E feeding R. Surviving the guarded operation PROVES something:
             a dereference that did not fault proves nonnull, a division
             that did not fault proves the divisor nonzero, a checked index
             proves inbounds.

             Applied here as well as in new_pi because a π read from a text
             file never went through new_pi. Both paths must agree, or a
             hand-written .air would carry weaker facts than a built one.
            */
            if (v.op_count < 1) { break; }
            Val* g = m.val(m.operands[v.op_off]);
            if (g == null) { break; }
            if (v.facts.range.is_top) { v.facts.range = g.facts.range; }
            if (v.facts.nullness == pear_erm::Nullness.NULL_UNKNOWN)
            {
                v.facts.nullness = g.facts.nullness;
            }
            switch (v.p.fact)
            {
                case FACT_NONNULL:
                    v.facts.nullness = pear_erm::Nullness.NULL_NEVER;
                case FACT_NONZERO:
                    v.facts.range = pear_erm::r_refine_ne(v.facts.range, 0);
                case FACT_INBOUNDS:
                    v.facts.range = pear_erm::r_refine_ge(v.facts.range, 0);
                default:
                    break;
            }
        }

        case AIR_CAST:
        {
            /*
             A cast to a narrower type TRUNCATES, so the range must be
             recomputed rather than carried through. Carrying it through is
             the bug that makes `300 as u8` claim to still be 300 — pfront's
             constant folder gets this right (it folds to 44) and the IR
             must not contradict it.
            */
            v.facts.range = pear_erm::r_top();
            v.facts.bits = pear_erm::kb_unknown();
        }

        default:
            break;
    }
}

/*
 Seed and propagate over one function, in block order.

 Block order is not dominance order, so a value defined in a later block
 and used in an earlier one (only possible through a back edge, i.e. a φ)
 sees top. That is correct and intentional for a single pass.
*/
fn void infer_function(Air* m, Fn* f)
{
    for (usz bi = 0; bi < f.block_count; bi++)
    {
        Blk* b = m.blk(f.blocks[bi]);
        if (b == null) { continue; }
        for (usz vi = 0; vi < b.value_count; vi++)
        {
            infer_value(m, b.values[vi]);
        }
    }
}

// ════════════════════════════════════════════════════════════════════════
// M — MEMORY VERSIONING
// ════════════════════════════════════════════════════════════════════════

/*
 Assign memory versions in block order: every store gets a fresh version
 and records the one it supersedes, every load records the version it
 reads.

 This is a LINEAR walk, not a dominance-correct MemorySSA. It is right for
 straight-line code and approximate across joins, and a2 inserts the real
 memory φs. Saying so is better than implying a1 computes full MemorySSA:
 the value here is that the versions EXIST in the serialised IR at all,
 which is the thing LLVM cannot do.
*/
fn void version_memory(Air* m, Fn* f, usz* out_versions)
{
    uint cur = 0;          // version 0 = live-on-entry
    uint next = 1;

    for (usz bi = 0; bi < f.block_count; bi++)
    {
        Blk* b = m.blk(f.blocks[bi]);
        if (b == null) { continue; }
        for (usz vi = 0; vi < b.value_count; vi++)
        {
            uint vid = b.values[vi];
            Val* v = m.val(vid);
            if (v == null) { continue; }

            switch (v.op)
            {
                case AIR_STORE_PTR:
                case AIR_STORE_FIELD:
                case AIR_STORE_INDEX:
                    v.facts.mem.kind = pear_erm::MemKind.MEM_DEF;
                    v.facts.mem.reaching = cur;
                    v.facts.mem.version = next;
                    cur = next;
                    next = next + 1;

                case AIR_LOAD_PTR:
                case AIR_LOAD_FIELD:
                case AIR_LOAD_INDEX:
                    v.facts.mem.kind = pear_erm::MemKind.MEM_USE;
                    v.facts.mem.reaching = cur;

                case AIR_CALL:
                case AIR_CALL_DIRECT:
                    /*
                     A call may write anything not proven otherwise, so it
                     clobbers the memory version. Treating a call as
                     transparent is the classic way to produce a
                     miscompile, so the conservative answer is the only
                     acceptable one until a2 has interprocedural facts.
                    */
                    v.facts.mem.kind = pear_erm::MemKind.MEM_DEF;
                    v.facts.mem.reaching = cur;
                    v.facts.mem.version = next;
                    cur = next;
                    next = next + 1;

                case AIR_ALLOC:
                    /*
                     A fresh allocation cannot alias anything that already
                     exists, which is the strongest alias fact in the whole
                     system and the one that makes escape analysis possible.
                    */
                    v.facts.mem.kind = pear_erm::MemKind.MEM_DEF;
                    v.facts.mem.reaching = cur;
                    v.facts.mem.version = next;
                    v.facts.mem.no_alias = true;
                    v.facts.mem.scope = next;
                    v.facts.nullness = pear_erm::Nullness.NULL_NEVER;
                    cur = next;
                    next = next + 1;

                default:
                    break;
            }
        }
    }
    if (out_versions != null) { *out_versions = (usz)next; }
}

// ════════════════════════════════════════════════════════════════════════
// DRIVER + MEASUREMENT
// ════════════════════════════════════════════════════════════════════════

/*
 What ERM actually achieved, reported whether flattering or not.

 A format that claims to be denser than .ll has to show the density. If
 `ranged` comes out near zero on real input then R is decorative and this
 report is what says so.
*/
struct ErmStats
{
    usz values;
    usz ranged;        // non-top range
    usz const_valued;  // range is a single point
    usz nonnull;
    usz known_bits;
    usz mem_defs;
    usz mem_uses;
    usz mem_versions;
    usz sp_nonlocal;
    usz sp_local;
    usz may_fault;
    usz decided_cmps;   // comparisons R already settles -- the payoff metric
    usz entry_loads;    // loads provably unaffected by this function
}

fn void ErmStats.init(ErmStats* s)
{
    s.values = 0; s.ranged = 0; s.const_valued = 0; s.nonnull = 0;
    s.known_bits = 0; s.mem_defs = 0; s.mem_uses = 0; s.mem_versions = 0;
    s.sp_nonlocal = 0; s.sp_local = 0; s.may_fault = 0;
    s.decided_cmps = 0; s.entry_loads = 0;
}

fn void run(Air* m, ErmStats* st)
{
    st.init();

    for (usz fi = 1; fi < m.func_count; fi++)
    {
        Fn* f = m.fun((uint)fi);
        if (f == null) { continue; }

        usz nl = 0; usz lo = 0;
        classify_sp(m, f, &nl, &lo);
        st.sp_nonlocal = st.sp_nonlocal + nl;
        st.sp_local = st.sp_local + lo;

        infer_function(m, f);

        usz vers = 0;
        version_memory(m, f, &vers);
        if (vers > st.mem_versions) { st.mem_versions = vers; }
    }

    for (usz i = 1; i < m.value_count; i++)
    {
        Val* v = &m.values[i];
        if (v.block == pear_air::AIR_NO_BLOCK) { continue; }
        st.values = st.values + 1;
        if (!v.facts.range.is_top) { st.ranged = st.ranged + 1; }
        if (pear_erm::r_is_const(&v.facts.range)) { st.const_valued = st.const_valued + 1; }
        if (v.facts.nullness == pear_erm::Nullness.NULL_NEVER) { st.nonnull = st.nonnull + 1; }
        if (!pear_erm::kb_is_unknown(&v.facts.bits)) { st.known_bits = st.known_bits + 1; }
        if (v.facts.mem.kind == pear_erm::MemKind.MEM_DEF) { st.mem_defs = st.mem_defs + 1; }
        if (v.facts.mem.kind == pear_erm::MemKind.MEM_USE) { st.mem_uses = st.mem_uses + 1; }
        if (v.facts.may_fault) { st.may_fault = st.may_fault + 1; }
    }

    st.decided_cmps = count_decided_comparisons(m);
    st.entry_loads = count_entry_loads(m);
}

/*
 THE PAYOFF QUERY. Which comparisons are already decided by R?

 This is the concrete claim behind "extreme optimisation potential": a
 bounds check whose operand ranges do not overlap is DECIDABLE from the IR
 text alone, with no analysis pass, because every version carries its
 range. a2 turns each of these into a folded branch and a deleted block.

 Reported as a count so the claim is measured rather than asserted. If it
 comes out zero on real input, R is decorative and this number says so.
*/
fn usz count_decided_comparisons(Air* m)
{
    usz decided = 0;
    for (usz i = 1; i < m.value_count; i++)
    {
        Val* v = &m.values[i];
        if (v.block == pear_air::AIR_NO_BLOCK) { continue; }
        if (v.op != Op.AIR_BIN || v.op_count < 2) { continue; }

        Val* a = m.val(m.operands[v.op_off]);
        Val* b = m.val(m.operands[v.op_off + 1]);
        if (a == null || b == null) { continue; }
        pear_erm::Range ra = a.facts.range;
        pear_erm::Range rb = b.facts.range;
        if (ra.is_top || rb.is_top || ra.is_bottom || rb.is_bottom) { continue; }

        bool always_true = false;
        bool always_false = false;
        switch (v.p.op)
        {
            case ABO_LT:
                always_true  = ra.hi <  rb.lo;
                always_false = ra.lo >= rb.hi;
            case ABO_LE:
                always_true  = ra.hi <= rb.lo;
                always_false = ra.lo >  rb.hi;
            case ABO_GT:
                always_true  = ra.lo >  rb.hi;
                always_false = ra.hi <= rb.lo;
            case ABO_GE:
                always_true  = ra.lo >= rb.hi;
                always_false = ra.hi <  rb.lo;
            case ABO_EQ:
                always_true  = ra.lo == ra.hi && rb.lo == rb.hi && ra.lo == rb.lo;
                always_false = ra.hi < rb.lo || rb.hi < ra.lo;
            case ABO_NE:
                always_false = ra.lo == ra.hi && rb.lo == rb.hi && ra.lo == rb.lo;
                always_true  = ra.hi < rb.lo || rb.hi < ra.lo;
            default:
                break;
        }
        if (always_true || always_false)
        {
            decided = decided + 1;
            // Record the constant so a2 does not have to redo the work,
            // and so the .air text SHOWS the branch is already decided.
            v.facts.range = always_true ? pear_erm::r_const(1) : pear_erm::r_const(0);
        }
    }
    return decided;
}

/*
 Which loads read a memory version no store ever wrote? Those read
 live-on-entry, so they cannot be affected by anything in this function —
 the fact that makes hoisting out of a loop legal. Answering this needs
 only the serialised IR; LLVM would rebuild MemorySSA to ask it.
*/
fn usz count_entry_loads(Air* m)
{
    usz n = 0;
    for (usz i = 1; i < m.value_count; i++)
    {
        Val* v = &m.values[i];
        if (v.facts.mem.kind != pear_erm::MemKind.MEM_USE) { continue; }
        if (v.facts.mem.reaching == 0) { n = n + 1; }
    }
    return n;
}

fn void print_stats(ErmStats* s)
{
    printf("  values           : %d\n", (int)s.values);
    printf("  R: ranged        : %d (%d constant)\n", (int)s.ranged, (int)s.const_valued);
    printf("  R: known bits    : %d\n", (int)s.known_bits);
    printf("  R: nonnull       : %d\n", (int)s.nonnull);
    printf("  M: versions      : %d (%d defs, %d uses)\n",
           (int)s.mem_versions, (int)s.mem_defs, (int)s.mem_uses);
    printf("  E: may-fault     : %d\n", (int)s.may_fault);
    printf("  >> decided cmps  : %d   (branches R already settles)\n", (int)s.decided_cmps);
    printf("  >> entry loads   : %d   (provably unaffected by this fn)\n", (int)s.entry_loads);
    printf("  SP: non-local    : %d  block-local: %d\n",
           (int)s.sp_nonlocal, (int)s.sp_local);
    if (s.sp_nonlocal + s.sp_local > 0)
    {
        int pct = (int)((s.sp_local * 100) / (s.sp_nonlocal + s.sp_local));
        printf("  SP: no phi needed: %d%%\n", pct);
    }
}
