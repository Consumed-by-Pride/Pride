/*
 a2 — SCCP, sparse conditional constant propagation (Wegman & Zadeck).

 Two lattices at once, which is the whole reason SCCP beats running
 constant folding and unreachable-block removal separately:

   values  ⊥ (not yet reached) → constant → ⊤ (not constant)
   blocks  unreachable → reachable

 They feed each other. A branch on a value that is constant marks only ONE
 successor reachable, so the other arm never contributes to any φ, so more
 values turn out constant, so more branches resolve. Running the two passes
 in sequence, however many times, cannot reach the same answer: constant
 folding alone must assume both arms of every branch are live.

 ── What this does that a1's range analysis does not ────────────────────

 a1 marks a comparison decided; that is a FACT about the value. SCCP acts
 on it: the comparison is replaced by the constant, the branch becomes a
 jump, and the dead arm stops being reachable. That is the difference
 between reporting an optimisation and performing one, and it is the reason
 `decided cmps` in a1's output was only ever a promissory note.

 ── Range facts are an INPUT here ───────────────────────────────────────

 The interesting case is a comparison whose operands are not constants but
 whose RANGES do not overlap: `i & 15 < 16` is true for every i, and no
 amount of constant propagation shows it. a2_range has already proven it,
 so SCCP consults the range lattice as a source of constants. That is `R`
 paying for itself, and it is counted separately (`from_range`) so the
 claim can be checked rather than assumed.
*/

module pear_a2_sccp;

import pear_air;
import pear_erm;
import pear_a2_cfg;
import pear_a2_facts;
import pear_a2_range;
import pfront_core;

alias Air  = pear_air::AirModule;
alias Val  = pear_air::AirValue;
alias Blk  = pear_air::AirBlock;
alias Fn   = pear_air::AirFunc;
alias Op   = pear_air::AirOp;
alias Term = pear_air::AirTerm;
alias BOp  = pear_air::AirBinOp;

extern fn int   printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn void  free(void* p);

// ════════════════════════════════════════════════════════════════════════
// THE VALUE LATTICE
// ════════════════════════════════════════════════════════════════════════

/*
 Three points. `LAT_BOTTOM` means no reachable definition has been seen
 yet, which is NOT the same as "unknown" — a φ whose only reachable
 operand is bottom stays bottom, and that is what lets an unreachable arm
 contribute nothing instead of forcing the result to top.
*/
enum Lat : int (String mnemonic)
{
    LAT_BOTTOM { "bottom" },     // unreached
    LAT_CONST  { "const" },
    LAT_TOP    { "top" }         // not a constant
}

struct Cell
{
    Lat  lat;
    long val;
}

fn Cell cell_bottom() { Cell c; c.lat = Lat.LAT_BOTTOM; c.val = 0; return c; }
fn Cell cell_top()    { Cell c; c.lat = Lat.LAT_TOP; c.val = 0; return c; }
fn Cell cell_const(long v) { Cell c; c.lat = Lat.LAT_CONST; c.val = v; return c; }

/*
 Lattice meet. Two different constants join to top; bottom is the identity.
 Monotone by construction, which is what guarantees termination: a cell can
 only move bottom → const → top, so at most twice.
*/
fn Cell cell_meet(Cell a, Cell b)
{
    if (a.lat == Lat.LAT_BOTTOM) { return b; }
    if (b.lat == Lat.LAT_BOTTOM) { return a; }
    if (a.lat == Lat.LAT_TOP || b.lat == Lat.LAT_TOP) { return cell_top(); }
    if (a.val != b.val) { return cell_top(); }
    return a;
}

fn bool cell_eq(Cell a, Cell b)
{
    if (a.lat != b.lat) { return false; }
    return a.lat != Lat.LAT_CONST || a.val == b.val;
}

// ════════════════════════════════════════════════════════════════════════
// THE SOLVER
// ════════════════════════════════════════════════════════════════════════

struct Sccp
{
    Air*   m;
    Fn*    f;
    Cell*  cells;          // per value id
    bool*  block_exec;     // per GLOBAL block id
    usz    nv;
    usz    nb;

    uint*  vwork;          // value worklist
    usz    vw_count;
    usz    vw_cap;
    uint*  bwork;          // block worklist
    usz    bw_count;
    usz    bw_cap;
    bool   ok;
}

fn bool Sccp.init(Sccp* s, Air* m, Fn* f)
{
    s.m = m; s.f = f;
    s.nv = m.value_count;
    s.nb = m.block_count;
    s.ok = false;
    usz nv = s.nv == 0 ? 1 : s.nv;
    usz nb = s.nb == 0 ? 1 : s.nb;
    s.cells      = (Cell*)malloc(nv * Cell::size);
    s.block_exec = (bool*)malloc(nb);
    s.vwork      = (uint*)malloc(nv * uint::size);
    s.bwork      = (uint*)malloc(nb * uint::size);
    if (s.cells == null || s.block_exec == null || s.vwork == null || s.bwork == null)
    {
        return false;
    }
    for (usz i = 0; i < nv; i++) { s.cells[i] = cell_bottom(); }
    for (usz i = 0; i < nb; i++) { s.block_exec[i] = false; }
    s.vw_count = 0; s.vw_cap = nv;
    s.bw_count = 0; s.bw_cap = nb;
    s.ok = true;
    return true;
}

fn void Sccp.destroy(Sccp* s)
{
    if (s.cells != null)      { free((void*)s.cells); s.cells = null; }
    if (s.block_exec != null) { free((void*)s.block_exec); s.block_exec = null; }
    if (s.vwork != null)      { free((void*)s.vwork); s.vwork = null; }
    if (s.bwork != null)      { free((void*)s.bwork); s.bwork = null; }
}

fn void Sccp.push_value(Sccp* s, uint v)
{
    if (s.vw_count < s.vw_cap) { s.vwork[s.vw_count] = v; s.vw_count = s.vw_count + 1; }
}

fn void Sccp.push_block(Sccp* s, uint b)
{
    if (s.block_exec[b]) { return; }
    s.block_exec[b] = true;
    if (s.bw_count < s.bw_cap) { s.bwork[s.bw_count] = b; s.bw_count = s.bw_count + 1; }
}

/*
 The cell for an operand, consulting the RANGE lattice as a fallback.

 A value a2_range proved to be a single point is a constant for SCCP's
 purposes even though no constant-propagation step produced it. This is the
 join between the two analyses and the reason `i & 15 < 16` folds.
*/
fn Cell Sccp.operand_cell(Sccp* s, uint v)
{
    if ((usz)v >= s.nv) { return cell_top(); }
    Cell c = s.cells[v];
    if (c.lat != Lat.LAT_TOP) { return c; }
    Val* vv = s.m.val(v);
    if (vv != null && pear_erm::r_is_const(&vv.facts.range))
    {
        return cell_const(vv.facts.range.lo);
    }
    return c;
}

/*
 Evaluate one value from its operands' cells.

 Only pure, total operations fold. A division is folded only when the
 divisor is a non-zero constant — folding `x / 0` to anything would replace
 a trap with a wrong answer.
*/
fn Cell Sccp.evaluate(Sccp* s, uint vid)
{
    Val* v = s.m.val(vid);
    if (v == null) { return cell_top(); }

    switch (v.op)
    {
        case AIR_CONST_INT:
        case AIR_CONST_BOOL:
            return cell_const(v.p.ival);

        case AIR_PHI:
        {
            /*
             Meet over operands arriving on EXECUTABLE edges only. This is
             the sparse-conditional part: an operand from a block SCCP has
             not proven reachable contributes nothing, so a φ whose live
             arm is constant stays constant.
            */
            Cell acc = cell_bottom();
            for (usz i = 0; i < v.op_count && i < v.inc_count; i++)
            {
                uint from = s.m.phi_blocks[v.inc_off + i];
                if ((usz)from < s.nb && !s.block_exec[from]) { continue; }
                acc = cell_meet(acc, s.operand_cell(s.m.operands[v.op_off + i]));
                if (acc.lat == Lat.LAT_TOP) { break; }
            }
            return acc;
        }

        case AIR_SIGMA:
        case AIR_PI:
        {
            // A rename: the same value, with a narrower range. If the
            // range analysis pinned it to a point, that IS its value.
            if (v.op_count < 1) { return cell_top(); }
            if (pear_erm::r_is_const(&v.facts.range))
            {
                return cell_const(v.facts.range.lo);
            }
            return s.operand_cell(s.m.operands[v.op_off]);
        }

        case AIR_BIN:
        {
            if (v.op_count < 2) { return cell_top(); }
            Cell a = s.operand_cell(s.m.operands[v.op_off]);
            Cell b = s.operand_cell(s.m.operands[v.op_off + 1]);

            /*
             Range-decided comparison. Checked BEFORE requiring constant
             operands, because this is the case that constants alone
             cannot reach and the whole reason R runs first.
            */
            if (is_cmp(v.p.op))
            {
                Val* av = s.m.val(s.m.operands[v.op_off]);
                Val* bv = s.m.val(s.m.operands[v.op_off + 1]);
                if (av != null && bv != null)
                {
                    int d = pear_a2_range::decide(v.p.op, av.facts.range, bv.facts.range);
                    if (d >= 0) { return cell_const((long)d); }
                }
            }

            if (a.lat == Lat.LAT_BOTTOM || b.lat == Lat.LAT_BOTTOM)
            {
                return cell_bottom();
            }
            if (a.lat != Lat.LAT_CONST || b.lat != Lat.LAT_CONST)
            {
                return cell_top();
            }
            return fold_bin(v.p.op, a.val, b.val);
        }

        case AIR_UN:
        {
            if (v.op_count < 1) { return cell_top(); }
            Cell a = s.operand_cell(s.m.operands[v.op_off]);
            if (a.lat != Lat.LAT_CONST) { return a; }
            switch (v.p.uop)
            {
                case AUO_NEG:
                    if (a.val == (long)0x8000000000000000) { return cell_top(); }
                    return cell_const(-a.val);
                case AUO_NOT:  return cell_const(a.val == 0 ? 1 : 0);
                case AUO_BNOT: return cell_const(~a.val);
                default:       return cell_top();
            }
        }

        default:
            /*
             Not foldable. A load, a call, a parameter — anything whose
             value is not a function of its operands' constants. Top rather
             than bottom: it has a value, we just do not know it.
            */
            return cell_top();
    }
}

fn bool is_cmp(BOp op)
{
    switch (op)
    {
        case ABO_EQ: case ABO_NE: case ABO_LT:
        case ABO_LE: case ABO_GT: case ABO_GE:
            return true;
        default:
            return false;
    }
}

/*
 Constant-fold one binary operation.

 Every case that can trap or is undefined returns top instead of a value:
 division by zero, shift past the width, and the one signed-overflow case
 that is not representable. Folding those would turn a runtime fault into a
 silently wrong answer, which is strictly worse than not folding.
*/
fn Cell fold_bin(BOp op, long a, long b)
{
    const long L_MIN = (long)0x8000000000000000;
    switch (op)
    {
        case ABO_ADD:
        case ABO_ADDC:
        case ABO_ADDS:
        {
            if (b > 0 && a > (long)0x7FFFFFFFFFFFFFFF - b) { return cell_top(); }
            if (b < 0 && a < L_MIN - b) { return cell_top(); }
            return cell_const(a + b);
        }
        case ABO_SUB:
        case ABO_SUBC:
        case ABO_SUBS:
        {
            if (b == L_MIN) { return cell_top(); }
            if (b < 0 && a > (long)0x7FFFFFFFFFFFFFFF + b) { return cell_top(); }
            if (b > 0 && a < L_MIN + b) { return cell_top(); }
            return cell_const(a - b);
        }
        case ABO_MUL:
        case ABO_MULC:
        case ABO_MULS:
        {
            if (a == 0 || b == 0) { return cell_const(0); }
            long r = a * b;
            if (r / b != a) { return cell_top(); }
            return cell_const(r);
        }
        // Wrapping is DEFINED to wrap, so folding it is exact.
        case ABO_ADDW: return cell_const((long)((ulong)a + (ulong)b));
        case ABO_SUBW: return cell_const((long)((ulong)a - (ulong)b));
        case ABO_MULW: return cell_const((long)((ulong)a * (ulong)b));

        case ABO_DIV:
            if (b == 0) { return cell_top(); }
            if (a == L_MIN && b == -1) { return cell_top(); }
            return cell_const(a / b);
        case ABO_MOD:
            if (b == 0) { return cell_top(); }
            if (a == L_MIN && b == -1) { return cell_top(); }
            return cell_const(a % b);

        case ABO_AND: return cell_const(a & b);
        case ABO_OR:  return cell_const(a | b);
        case ABO_XOR: return cell_const(a ^ b);
        case ABO_SHL:
            if (b < 0 || b > 63) { return cell_top(); }
            return cell_const((long)((ulong)a << (ulong)b));
        case ABO_SHR:
            if (b < 0 || b > 63) { return cell_top(); }
            return cell_const(a >> (ulong)b);

        case ABO_EQ: return cell_const(a == b ? 1 : 0);
        case ABO_NE: return cell_const(a != b ? 1 : 0);
        case ABO_LT: return cell_const(a < b ? 1 : 0);
        case ABO_LE: return cell_const(a <= b ? 1 : 0);
        case ABO_GT: return cell_const(a > b ? 1 : 0);
        case ABO_GE: return cell_const(a >= b ? 1 : 0);
        case ABO_LAND: return cell_const((a != 0 && b != 0) ? 1 : 0);
        case ABO_LOR:  return cell_const((a != 0 || b != 0) ? 1 : 0);
        default: return cell_top();
    }
}

/*
 Mark the successors a block's terminator can actually reach.

 A branch on a constant reaches ONE arm. This is the step that makes the
 whole thing conditional, and it is what a separate constant folder cannot
 do, because it has no way to stop believing in the other arm.
*/
fn void Sccp.visit_terminator(Sccp* s, uint bid)
{
    Blk* b = s.m.blk(bid);
    if (b == null) { return; }

    switch (b.term)
    {
        case TERM_BRANCH:
        {
            if (b.succ_count < 2) { return; }
            Cell c = s.operand_cell(b.term_value);
            if (c.lat == Lat.LAT_CONST)
            {
                s.push_block(c.val != 0 ? b.succ[0] : b.succ[1]);
                return;
            }
            if (c.lat == Lat.LAT_BOTTOM) { return; }   // not yet known
            s.push_block(b.succ[0]);
            s.push_block(b.succ[1]);
        }
        case TERM_SWITCH:
        {
            Cell c = s.operand_cell(b.term_value);
            if (c.lat == Lat.LAT_CONST)
            {
                for (usz i = 0; i < b.case_count && i < b.succ_count; i++)
                {
                    if (b.case_vals[i] == c.val) { s.push_block(b.succ[i]); return; }
                }
                // No case matched: only the default arm runs.
                if (b.has_default && b.succ_count > 0)
                {
                    s.push_block(b.succ[b.succ_count - 1]);
                }
                return;
            }
            if (c.lat == Lat.LAT_BOTTOM) { return; }
            for (usz i = 0; i < b.succ_count; i++) { s.push_block(b.succ[i]); }
        }
        default:
            for (usz i = 0; i < b.succ_count; i++) { s.push_block(b.succ[i]); }
    }
}

fn void Sccp.solve(Sccp* s)
{
    s.push_block(s.f.entry);

    usz guard = 0;
    usz cap = (s.nv + s.nb) * 8 + 1024;
    while ((s.bw_count > 0 || s.vw_count > 0) && guard < cap)
    {
        guard = guard + 1;

        if (s.bw_count > 0)
        {
            s.bw_count = s.bw_count - 1;
            uint bid = s.bwork[s.bw_count];
            Blk* b = s.m.blk(bid);
            if (b == null) { continue; }
            for (usz i = 0; i < b.value_count; i++)
            {
                uint vid = b.values[i];
                Val* v = s.m.val(vid);
                if (v == null || v.is_phi_hole) { continue; }
                Cell nc = s.evaluate(vid);
                if (!cell_eq(nc, s.cells[vid]))
                {
                    s.cells[vid] = nc;
                    s.push_value(vid);
                }
            }
            s.visit_terminator(bid);
            continue;
        }

        s.vw_count = s.vw_count - 1;
        uint vid = s.vwork[s.vw_count];

        /*
         Re-evaluate every USER of this value. The scan is over the whole
         module rather than a use list, which is O(n) per pop; building a
         use list first would be faster but is a second structure to keep
         in step with every rewrite. Functions here are small enough that
         the simpler invariant is worth more than the constant factor.
        */
        for (usz i = 1; i < s.nv; i++)
        {
            Val* u = &s.m.values[i];
            if (u.block == pear_air::AIR_NO_BLOCK || u.is_phi_hole) { continue; }
            if ((usz)u.block < s.nb && !s.block_exec[u.block]) { continue; }
            bool uses = false;
            for (usz k = 0; k < u.op_count; k++)
            {
                if (s.m.operands[u.op_off + k] == vid) { uses = true; break; }
            }
            if (!uses) { continue; }
            Cell nc = s.evaluate((uint)i);
            if (!cell_eq(nc, s.cells[i]))
            {
                s.cells[i] = nc;
                s.push_value((uint)i);
            }
        }
        // A terminator reading this value may now resolve.
        for (usz i = 1; i < s.nb; i++)
        {
            if (!s.block_exec[i]) { continue; }
            if (s.m.blocks[i].term_value == vid) { s.visit_terminator((uint)i); }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════
// REWRITING — where the analysis becomes an optimisation
// ════════════════════════════════════════════════════════════════════════

struct SccpStats
{
    usz values;
    usz folded;            // values replaced by a constant
    usz branches_folded;   // conditional branches that became jumps
    usz blocks_dead;       // blocks SCCP proved unreachable
    usz edges_cut;
}

fn void SccpStats.init(SccpStats* s)
{
    s.values = 0; s.folded = 0; s.branches_folded = 0;
    s.blocks_dead = 0; s.edges_cut = 0;
}

/*
 Remove the edge `from -> to`, keeping φ operands in step.

 A φ in `to` has one operand per predecessor. Dropping a predecessor
 without dropping the matching operand leaves a φ whose arity disagrees
 with its block, which the verifier rejects — and rightly, since it would
 mean an operand arriving on an edge that no longer exists.
*/
fn void cut_edge(Air* m, uint from, uint to)
{
    Blk* fb = m.blk(from);
    Blk* tb = m.blk(to);
    if (fb == null || tb == null) { return; }

    usz removed = 0;
    for (usz i = 0; i < fb.succ_count; )
    {
        if (fb.succ[i] == to)
        {
            for (usz j = i; j + 1 < fb.succ_count; j++) { fb.succ[j] = fb.succ[j + 1]; }
            fb.succ_count = fb.succ_count - 1;
            removed = removed + 1;
        }
        else { i = i + 1; }
    }
    if (removed == 0) { return; }

    for (usz r = 0; r < removed; r++)
    {
        for (usz i = 0; i < tb.pred_count; i++)
        {
            if (tb.pred[i] == from)
            {
                for (usz j = i; j + 1 < tb.pred_count; j++) { tb.pred[j] = tb.pred[j + 1]; }
                tb.pred_count = tb.pred_count - 1;
                break;
            }
        }
        // Drop the matching operand from every phi in the target.
        for (usz i = 0; i < tb.value_count; i++)
        {
            Val* v = m.val(tb.values[i]);
            if (v == null) { continue; }
            if (v.op != Op.AIR_PHI && v.op != Op.AIR_MEM_PHI) { continue; }
            for (usz k = 0; k < v.inc_count; k++)
            {
                if (m.phi_blocks[v.inc_off + k] != from) { continue; }
                for (usz j = k; j + 1 < v.inc_count; j++)
                {
                    m.phi_blocks[v.inc_off + j] = m.phi_blocks[v.inc_off + j + 1];
                    m.operands[v.op_off + j] = m.operands[v.op_off + j + 1];
                }
                v.inc_count = v.inc_count - 1;
                v.op_count = v.op_count - 1;
                break;
            }
        }
    }
}

/*
 Move a value out of the φ prefix, to the first position after it.

 Used when SCCP folds a φ into a constant: the value stays in the same
 block (so nothing about dominance changes) but stops occupying a slot the
 φ invariant reserves.
*/
fn void move_after_phis(Air* m, Blk* b, uint vid)
{
    usz at = b.value_count;
    for (usz i = 0; i < b.value_count; i++)
    {
        if (b.values[i] == vid) { at = i; break; }
    }
    if (at == b.value_count) { return; }

    /*
     Find the LAST φ in the block and land just after it.

     Scanning forward for the first non-φ does not work here: the value
     being moved is itself that first non-φ (it was a φ a moment ago and
     still occupies its old slot), so the scan stops at position 0 and the
     move is a no-op. That is exactly the bug this function was written to
     fix, reintroduced one level down — the folded constant stayed at the
     head of the block with four live φ behind it.

     Scanning for the last φ instead is immune to where the moved value
     currently sits.
    */
    usz last_phi = b.value_count;      // sentinel: no φ at all
    for (usz i = 0; i < b.value_count; i++)
    {
        if (b.values[i] == vid) { continue; }
        Val* v = m.val(b.values[i]);
        if (v == null) { continue; }
        if (v.op == Op.AIR_PHI || v.op == Op.AIR_MEM_PHI) { last_phi = i; }
    }
    if (last_phi == b.value_count) { return; }   // nothing to get behind
    if (at > last_phi) { return; }               // already after every φ

    // Shift the φ between `at` and `last_phi` down one, and drop the
    // folded value into the vacated slot.
    for (usz i = at; i < last_phi; i++) { b.values[i] = b.values[i + 1]; }
    b.values[last_phi] = vid;
}

fn void run_function(Air* m, Fn* f, pear_a2_facts::Facts2* facts, SccpStats* st)
{
    Sccp s;
    if (!s.init(m, f)) { s.destroy(); return; }
    s.solve();

    /*
     Rewrite constants in place.

     The value KEEPS its id and its origin — this is D1 working: the value
     is now a constant, but everything learned about its lineage is still
     reachable under the same key. Replacing it with a NEW value would
     start a fresh lineage and orphan every fact about it.
    */
    for (usz bi = 0; bi < f.block_count; bi++)
    {
        Blk* b = m.blk(f.blocks[bi]);
        if (b == null) { continue; }
        bool live = s.block_exec[b.id];
        if (!live) { st.blocks_dead = st.blocks_dead + 1; continue; }

        for (usz i = 0; i < b.value_count; i++)
        {
            uint vid = b.values[i];
            Val* v = m.val(vid);
            if (v == null || v.is_phi_hole) { continue; }
            st.values = st.values + 1;

            Cell c = s.cells[vid];
            if (c.lat != Lat.LAT_CONST) { continue; }
            if (v.op == Op.AIR_CONST_INT || v.op == Op.AIR_CONST_BOOL) { continue; }
            // Only fold things that are pure: a call returning a constant
            // still has to be called.
            if (pear_air::op_has_effect(v.op)) { continue; }
            if (v.op == Op.AIR_MEM_PHI || v.op == Op.AIR_MEM_ENTRY) { continue; }

            bool was_phi = v.op == Op.AIR_PHI;

            int w = v.facts.width;
            bool sg = v.facts.is_signed;
            v.op = Op.AIR_CONST_INT;
            v.op_count = 0;
            v.inc_count = 0;
            v.p.clear();
            m.set_const_int(vid, c.val, w, sg);
            st.folded = st.folded + 1;
            facts.learn(v.origin, v.facts, pear_a2_facts::FactSource.FS_SCCP);

            /*
             Folding a φ breaks the all-φ-come-first invariant.

             A φ lives in the block's φ prefix. Rewriting it in place makes
             it an ordinary constant SITTING IN that prefix, so every φ
             after it now "appears after a non-φ value" and the verifier
             rejects the block. Four functions in the standard library hit
             this, and the folded IR was genuinely malformed rather than
             merely ugly: a φ is a parallel copy on the incoming edges and
             a real instruction before it has no defined position.

             Moving it to just after the prefix keeps both properties: the
             constant is still dominated by everything it needs (it needs
             nothing) and the remaining φ are still contiguous at the top.
            */
            if (was_phi) { move_after_phis(m, b, vid); i = 0; }
        }
    }

    /*
     Fold branches whose condition is now constant, and cut the edge to the
     arm that cannot be taken. Done AFTER value rewriting so the condition
     is already a constant in the IR, not just in the lattice.
    */
    for (usz bi = 0; bi < f.block_count; bi++)
    {
        uint bid = f.blocks[bi];
        Blk* b = m.blk(bid);
        if (b == null || !s.block_exec[bid]) { continue; }
        if (b.term != Term.TERM_BRANCH || b.succ_count != 2) { continue; }

        Cell c = s.operand_cell(b.term_value);
        if (c.lat != Lat.LAT_CONST) { continue; }

        uint taken = c.val != 0 ? b.succ[0] : b.succ[1];
        uint gone  = c.val != 0 ? b.succ[1] : b.succ[0];
        if (taken == gone) { continue; }      // both arms the same block

        cut_edge(m, bid, gone);
        m.set_term(bid, Term.TERM_JUMP, pear_air::AIR_NO_VALUE);
        st.branches_folded = st.branches_folded + 1;
        st.edges_cut = st.edges_cut + 1;
    }

    s.destroy();
}

fn void run(Air* m, pear_a2_facts::Facts2* facts, SccpStats* st)
{
    st.init();
    for (usz i = 1; i < m.func_count; i++)
    {
        Fn* f = m.fun((uint)i);
        if (f == null) { continue; }
        run_function(m, f, facts, st);
    }
}

fn void print_stats(SccpStats* s)
{
    printf("  SCCP: folded     : %d values\n", (int)s.folded);
    printf("  SCCP: branches   : %d became jumps\n", (int)s.branches_folded);
    printf("  SCCP: dead blocks: %d   (proven unreachable)\n", (int)s.blocks_dead);
}
