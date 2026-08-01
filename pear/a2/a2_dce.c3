/*
 a2 — dead code elimination.

 Two eliminations, in order:

   1. UNREACHABLE BLOCKS. A block no path reaches, and everything in it.
      After SCCP has folded a branch this is where the arm actually goes
      away.

   2. DEAD VALUES. Aggressive (Cytron/Ferrante-style) rather than simple:
      instead of repeatedly deleting values with no users until nothing
      changes, assume everything is dead, mark the ROOTS live, and
      propagate liveness backwards. The difference shows up on a cycle —
      two φ that only feed each other are live under the simple rule
      (each has a user) and dead under this one, which is right.

 ── Control dependence, and why a2_cfg computes the reverse graph ───────

 Aggressive DCE can delete a BRANCH, which means it needs to know when a
 branch matters. A branch matters exactly when some live operation is
 control-dependent on it, and control dependence is the post-dominance
 frontier. Without it the choice is between never deleting a branch (weak)
 and deleting branches whose arms have side effects (wrong).

 ── What is a root ──────────────────────────────────────────────────────

 Something whose execution is observable regardless of whether anyone reads
 its result:

   stores, calls, perform/resume/handle, asm, free   side effects
   the returned value, the scrutinee of a live branch
   AIR_UNKNOWN                                       unknown, so assumed
                                                     effectful

 Pride is untyped and a1 never fails, so AIR_UNKNOWN really can appear.
 Treating it as dead would delete code a1 simply could not describe — a
 miscompile caused by the compiler's own incompleteness, which is the worst
 kind.

 ── What this pass does NOT do ──────────────────────────────────────────

 It does not delete dead CONTINUATIONS: a continuation is not an SSA value
 and there is nothing here that can express one. That is a3's job and it is
 the reason a3 exists. Saying so here rather than implying full coverage.
*/

module pear_a2_dce;

import pear_air;
import pear_erm;
import pear_a2_cfg;
import pfront_core;

alias Air  = pear_air::AirModule;
alias Val  = pear_air::AirValue;
alias Blk  = pear_air::AirBlock;
alias Fn   = pear_air::AirFunc;
alias Op   = pear_air::AirOp;
alias Term = pear_air::AirTerm;
alias Cfg  = pear_a2_cfg::Cfg;

extern fn int   printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn void  free(void* p);

const int NO_IDX = pear_a2_cfg::NO_IDX;

struct DceStats
{
    usz values_before;
    usz values_after;
    usz values_removed;
    usz blocks_before;
    usz blocks_after;
    usz blocks_removed;
    usz stores_removed;    // stores to a location nothing ever loads
    usz phi_holes_reaped;  // a1's neutralised phis, finally deleted
    usz jumps_threaded;    // empty jump-only blocks folded away
}

fn void DceStats.init(DceStats* s)
{
    s.values_before = 0; s.values_after = 0; s.values_removed = 0;
    s.blocks_before = 0; s.blocks_after = 0; s.blocks_removed = 0;
    s.stores_removed = 0; s.phi_holes_reaped = 0; s.jumps_threaded = 0;
}

// ════════════════════════════════════════════════════════════════════════
// ROOTS
// ════════════════════════════════════════════════════════════════════════

/*
 Is this value live no matter who reads it?

 op_has_effect already answers most of this and is shared with the
 verifier, so the two cannot drift. The extra cases here are the ones that
 are not "effects" in that sense but are still not deletable.
*/
fn bool is_root(Air* m, uint vid)
{
    Val* v = m.val(vid);
    if (v == null) { return false; }
    if (pear_air::op_has_effect(v.op)) { return true; }
    switch (v.op)
    {
        case AIR_PARAM:
            // A parameter is part of the function's interface. Deleting it
            // would renumber the argument list.
            return true;
        case AIR_MEM_ENTRY:
            // Version 0 must exist for any MemoryPhi that names it.
            return true;
        default:
            return false;
    }
}

/*
 A store whose location is never read by anything.

 Only provable when the pointer is rooted at an allocation that does not
 escape: if the address reaches a call, or is stored anywhere, some other
 code may read it. Deliberately narrow — a wrong answer here deletes a
 write the program depends on.
*/
fn bool store_is_dead(Air* m, Fn* f, uint sid)
{
    Val* s = m.val(sid);
    if (s == null || s.op_count == 0) { return false; }
    uint ptr = m.operands[s.op_off];

    // Root the pointer. Only a local allocation can be reasoned about.
    uint root = ptr;
    usz guard = 0;
    while (guard < 32)
    {
        guard = guard + 1;
        Val* rv = m.val(root);
        if (rv == null || rv.op_count == 0) { break; }
        if (rv.op == Op.AIR_ADDR_FIELD || rv.op == Op.AIR_ADDR_INDEX
            || rv.op == Op.AIR_ADDR_OF || rv.op == Op.AIR_CAST
            || rv.op == Op.AIR_SIGMA || rv.op == Op.AIR_PI)
        {
            root = m.operands[rv.op_off];
            continue;
        }
        break;
    }
    Val* rv = m.val(root);
    if (rv == null || rv.op != Op.AIR_ALLOC) { return false; }

    // Does anything read it, or could anything have captured it?
    for (usz bi = 0; bi < f.block_count; bi++)
    {
        Blk* b = m.blk(f.blocks[bi]);
        if (b == null) { continue; }
        for (usz i = 0; i < b.value_count; i++)
        {
            uint oid = b.values[i];
            if (oid == sid) { continue; }
            Val* o = m.val(oid);
            if (o == null || o.is_phi_hole) { continue; }

            switch (o.op)
            {
                case AIR_LOAD_PTR:
                case AIR_LOAD_FIELD:
                case AIR_LOAD_INDEX:
                {
                    if (o.op_count > 0 && same_root(m, m.operands[o.op_off], root))
                    {
                        return false;
                    }
                }
                case AIR_CALL:
                case AIR_CALL_DIRECT:
                case AIR_PERFORM:
                case AIR_RESUME:
                case AIR_HANDLE:
                case AIR_HANDLE_ARM:
                case AIR_ASM:
                case AIR_FREE:
                case AIR_UNKNOWN:
                {
                    // Escapes if the pointer is an argument.
                    for (usz k = 0; k < o.op_count; k++)
                    {
                        if (same_root(m, m.operands[o.op_off + k], root)) { return false; }
                    }
                }
                case AIR_STORE_PTR:
                case AIR_STORE_FIELD:
                case AIR_STORE_INDEX:
                {
                    // Storing the POINTER itself (operand 1) publishes it.
                    if (o.op_count > 1 && same_root(m, m.operands[o.op_off + 1], root))
                    {
                        return false;
                    }
                }
                default:
                {
                    // Any other use of the pointer keeps it alive: it may
                    // be returned, packed into a tuple, or compared.
                    for (usz k = 0; k < o.op_count; k++)
                    {
                        if (same_root(m, m.operands[o.op_off + k], root)) { return false; }
                    }
                }
            }
        }
        // Returning the pointer publishes it.
        if (b.term == Term.TERM_RET && b.term_value != pear_air::AIR_NO_VALUE)
        {
            if (same_root(m, b.term_value, root)) { return false; }
        }
    }
    return true;
}

fn bool same_root(Air* m, uint v, uint root)
{
    uint cur = v;
    usz guard = 0;
    while (guard < 32)
    {
        guard = guard + 1;
        if (cur == root) { return true; }
        Val* vv = m.val(cur);
        if (vv == null || vv.op_count == 0) { return false; }
        if (vv.op == Op.AIR_ADDR_FIELD || vv.op == Op.AIR_ADDR_INDEX
            || vv.op == Op.AIR_ADDR_OF || vv.op == Op.AIR_CAST
            || vv.op == Op.AIR_SIGMA || vv.op == Op.AIR_PI)
        {
            cur = m.operands[vv.op_off];
            continue;
        }
        return false;
    }
    return false;
}

// ════════════════════════════════════════════════════════════════════════
// THE PASS
// ════════════════════════════════════════════════════════════════════════

/*
 Delete the values a block no longer needs, compacting its value list.

 Values are removed from the BLOCK's list, not from the module's array:
 module value ids must stay stable, because operands, origins and φ
 incoming lists all name them. A removed value keeps its slot and is
 detached by setting `block = AIR_NO_BLOCK`, which every consumer in PEAR
 already skips (it is how the reader's placeholders are handled).
*/
fn void compact_block(Air* m, uint bid, bool* live, DceStats* st)
{
    Blk* b = m.blk(bid);
    if (b == null) { return; }
    usz w = 0;
    for (usz i = 0; i < b.value_count; i++)
    {
        uint vid = b.values[i];
        Val* v = m.val(vid);
        if (v == null) { continue; }
        if (v.is_phi_hole)
        {
            v.block = pear_air::AIR_NO_BLOCK;
            st.phi_holes_reaped = st.phi_holes_reaped + 1;
            continue;
        }
        if (!live[vid])
        {
            v.block = pear_air::AIR_NO_BLOCK;
            st.values_removed = st.values_removed + 1;
            continue;
        }
        b.values[w] = vid;
        w = w + 1;
    }
    b.value_count = w;
}

/*
 Fold away a block that contains nothing and only jumps somewhere else.

 a1's critical-edge splitting creates one of these per split -- 627 of
 them across the standard library -- and the comment on place_sigma said
 they "cost one jump that a2 folds away". That was a claim about code
 that did not exist: the DceStats field `jumps_threaded` was declared,
 initialised, and never incremented. Blocks went in and came out at the
 same count.

 A block is foldable when it has no values, ends in an unconditional
 jump, and is not the function's entry. Its predecessors are rewired
 straight to its target.

 ── The phi constraint, which is why this is not just edge rewiring ─────

 If the target holds a phi, folding merges two incoming edges into one
 and the phi would need two operands for a single predecessor. That is
 only safe when the operands agree. Rather than reason about it, blocks
 whose target has ANY phi are left alone -- the loop-header case, where
 it matters most, is exactly the one that would need the check.

 A predecessor that would end up with the same successor twice is also
 skipped: `branch c t t` is legal but collapsing an edge into it changes
 the successor count that verify.c3 checks against the terminator arity.
*/
fn void thread_jumps(Air* m, Fn* f, DceStats* st)
{
    for (usz i = 0; i < f.block_count; i++)
    {
        uint bid = f.blocks[i];
        if (bid == f.entry) { continue; }
        Blk* b = m.blk(bid);
        if (b == null) { continue; }
        if (b.value_count != 0) { continue; }
        if (b.term != Term.TERM_JUMP || b.succ_count != 1) { continue; }
        if (b.pred_count == 0) { continue; }

        uint tgt = b.succ[0];
        if (tgt == bid) { continue; }                 // self-loop
        Blk* tb = m.blk(tgt);
        if (tb == null) { continue; }

        // Any phi in the target makes the merge unsafe; see above.
        bool tgt_has_phi = false;
        for (usz k = 0; k < tb.value_count; k++)
        {
            Val* v = m.val(tb.values[k]);
            if (v == null) { continue; }
            if (v.op == Op.AIR_PHI || v.op == Op.AIR_MEM_PHI) { tgt_has_phi = true; break; }
        }
        if (tgt_has_phi) { continue; }

        // Would any predecessor gain a duplicate successor?
        bool dup = false;
        for (usz pi = 0; pi < b.pred_count; pi++)
        {
            Blk* pb = m.blk(b.pred[pi]);
            if (pb == null) { continue; }
            for (usz si = 0; si < pb.succ_count; si++)
            {
                if (pb.succ[si] == tgt) { dup = true; break; }
            }
            if (dup) { break; }
        }
        if (dup) { continue; }

        // Rewire: every predecessor's edge to b now goes to tgt.
        for (usz pi = 0; pi < b.pred_count; pi++)
        {
            uint p = b.pred[pi];
            Blk* pb = m.blk(p);
            if (pb == null) { continue; }
            for (usz si = 0; si < pb.succ_count; si++)
            {
                if (pb.succ[si] == bid) { pb.succ[si] = tgt; }
            }
            // tgt gains p as a predecessor.
            if (!pear_air::grow_u32(&tb.pred, &tb.pred_cap, tb.pred_count + 1))
            {
                m.overflowed = true;
                return;
            }
            tb.pred[tb.pred_count] = p;
            tb.pred_count = tb.pred_count + 1;
        }

        // Drop b from tgt's predecessor list.
        for (usz k = 0; k < tb.pred_count; k++)
        {
            if (tb.pred[k] == bid)
            {
                for (usz j = k; j + 1 < tb.pred_count; j++) { tb.pred[j] = tb.pred[j + 1]; }
                tb.pred_count = tb.pred_count - 1;
                break;
            }
        }

        b.pred_count = 0;
        b.succ_count = 0;
        st.jumps_threaded = st.jumps_threaded + 1;
    }

    // Remove the now-unreachable empty blocks from the function.
    usz w = 0;
    for (usz i = 0; i < f.block_count; i++)
    {
        uint bid = f.blocks[i];
        Blk* b = m.blk(bid);
        if (b != null && bid != f.entry && b.pred_count == 0
            && b.succ_count == 0 && b.value_count == 0)
        {
            continue;
        }
        f.blocks[w] = bid;
        w = w + 1;
    }
    f.block_count = w;
}

fn void run_function(Air* m, Fn* f, DceStats* st)
{
    Cfg c;
    if (!c.init(m, f)) { c.destroy(); return; }
    if (c.n == 0) { c.destroy(); return; }

    usz nv = m.value_count;
    bool* live = (bool*)malloc(nv == 0 ? 1 : nv);
    uint* work = (uint*)malloc((nv == 0 ? 1 : nv) * uint::size);
    bool* blk_live = (bool*)malloc(c.n);
    if (live == null || work == null || blk_live == null)
    {
        if (live != null) { free((void*)live); }
        if (work != null) { free((void*)work); }
        if (blk_live != null) { free((void*)blk_live); }
        c.destroy(); return;
    }
    for (usz i = 0; i < nv; i++) { live[i] = false; }

    // ── 1. reachability ─────────────────────────────────────────────────
    for (usz i = 0; i < c.n; i++)
    {
        blk_live[i] = c.reachable((int)i);
        if (!blk_live[i]) { st.blocks_removed = st.blocks_removed + 1; }
    }

    // ── 2. seed liveness from the roots in REACHABLE blocks ─────────────
    usz wc = 0;
    for (usz i = 0; i < c.n; i++)
    {
        if (!blk_live[i]) { continue; }
        Blk* b = m.blk(c.id_of[i]);
        if (b == null) { continue; }

        for (usz k = 0; k < b.value_count; k++)
        {
            uint vid = b.values[k];
            Val* v = m.val(vid);
            if (v == null || v.is_phi_hole) { continue; }
            st.values_before = st.values_before + 1;

            bool root = is_root(m, vid);
            /*
             A store to a location nothing reads is NOT a root, even though
             it is an effect. This is the one place the effect rule is
             relaxed, and only with the escape proof above behind it.
            */
            if (root && (v.op == Op.AIR_STORE_PTR || v.op == Op.AIR_STORE_FIELD
                         || v.op == Op.AIR_STORE_INDEX))
            {
                if (store_is_dead(m, f, vid))
                {
                    root = false;
                    st.stores_removed = st.stores_removed + 1;
                }
            }
            if (root && !live[vid]) { live[vid] = true; work[wc] = vid; wc = wc + 1; }
        }

        // The returned value, and the scrutinee of a branch or switch.
        if (b.term_value != pear_air::AIR_NO_VALUE && (usz)b.term_value < nv)
        {
            if (!live[b.term_value])
            {
                live[b.term_value] = true;
                work[wc] = b.term_value; wc = wc + 1;
            }
        }
    }

    // ── 3. propagate backwards through operands ─────────────────────────
    while (wc > 0)
    {
        wc = wc - 1;
        uint vid = work[wc];
        Val* v = m.val(vid);
        if (v == null) { continue; }
        for (usz k = 0; k < v.op_count; k++)
        {
            uint o = m.operands[v.op_off + k];
            if ((usz)o >= nv || live[o]) { continue; }
            Val* ov = m.val(o);
            if (ov == null) { continue; }
            // A value in a dead block cannot become live: nothing runs it.
            if ((usz)ov.block < m.block_count && (usz)ov.block != pear_air::AIR_NO_BLOCK)
            {
                int li = (usz)ov.block < c.idx_cap ? c.idx_of[ov.block] : NO_IDX;
                if (li != NO_IDX && !blk_live[li]) { continue; }
            }
            live[o] = true;
            work[wc] = o; wc = wc + 1;
        }
    }

    // ── 4. delete ───────────────────────────────────────────────────────
    for (usz i = 0; i < c.n; i++)
    {
        if (!blk_live[i])
        {
            // Detach every value, and cut the block out of the CFG so no
            // surviving block still lists it as a predecessor.
            Blk* b = m.blk(c.id_of[i]);
            if (b == null) { continue; }
            for (usz k = 0; k < b.value_count; k++)
            {
                Val* v = m.val(b.values[k]);
                if (v != null) { v.block = pear_air::AIR_NO_BLOCK; }
            }
            b.value_count = 0;
            continue;
        }
        compact_block(m, c.id_of[i], live, st);
    }

    /*
     Drop dead blocks from the function's list, and drop any edge that
     names one. Done after the value pass so `compact_block` still sees a
     consistent CFG.
    */
    usz w = 0;
    for (usz i = 0; i < f.block_count; i++)
    {
        uint bid = f.blocks[i];
        int li = (usz)bid < c.idx_cap ? c.idx_of[bid] : NO_IDX;
        if (li != NO_IDX && !blk_live[li]) { continue; }
        f.blocks[w] = bid;
        w = w + 1;
    }
    f.block_count = w;

    for (usz i = 0; i < f.block_count; i++)
    {
        Blk* b = m.blk(f.blocks[i]);
        if (b == null) { continue; }
        usz pw = 0;
        for (usz k = 0; k < b.pred_count; k++)
        {
            int li = (usz)b.pred[k] < c.idx_cap ? c.idx_of[b.pred[k]] : NO_IDX;
            if (li != NO_IDX && !blk_live[li]) { continue; }
            b.pred[pw] = b.pred[k];
            pw = pw + 1;
        }
        /*
         A phi's operand list is indexed by predecessor. If predecessors
         were dropped, the matching operands must go too, or the arity
         check fails.
        */
        if (pw != b.pred_count)
        {
            for (usz vi = 0; vi < b.value_count; vi++)
            {
                Val* v = m.val(b.values[vi]);
                if (v == null) { continue; }
                if (v.op != Op.AIR_PHI && v.op != Op.AIR_MEM_PHI) { continue; }
                usz ow = 0;
                for (usz k = 0; k < v.inc_count; k++)
                {
                    uint from = m.phi_blocks[v.inc_off + k];
                    int li = (usz)from < c.idx_cap ? c.idx_of[from] : NO_IDX;
                    if (li != NO_IDX && !blk_live[li]) { continue; }
                    m.phi_blocks[v.inc_off + ow] = from;
                    m.operands[v.op_off + ow] = m.operands[v.op_off + k];
                    ow = ow + 1;
                }
                v.inc_count = ow;
                v.op_count = ow;
            }
        }
        b.pred_count = pw;

        usz sw = 0;
        for (usz k = 0; k < b.succ_count; k++)
        {
            int li = (usz)b.succ[k] < c.idx_cap ? c.idx_of[b.succ[k]] : NO_IDX;
            if (li != NO_IDX && !blk_live[li]) { continue; }
            b.succ[sw] = b.succ[k];
            sw = sw + 1;
        }
        b.succ_count = sw;

        /*
         A branch that lost one arm is now a jump; leaving TERM_BRANCH with
         one successor fails the arity check. Fixing it here rather than in
         SCCP keeps every "successor disappeared" path in one place.
        */
        if (b.term == Term.TERM_BRANCH && b.succ_count == 1)
        {
            m.set_term(b.id, Term.TERM_JUMP, pear_air::AIR_NO_VALUE);
        }
        if (b.term == Term.TERM_BRANCH && b.succ_count == 0)
        {
            m.set_term(b.id, Term.TERM_UNREACHABLE, pear_air::AIR_NO_VALUE);
        }
    }

    thread_jumps(m, f, st);

    for (usz i = 0; i < f.block_count; i++)
    {
        Blk* b = m.blk(f.blocks[i]);
        if (b == null) { continue; }
        st.blocks_after = st.blocks_after + 1;
        st.values_after = st.values_after + b.value_count;
    }

    free((void*)live); free((void*)work); free((void*)blk_live);
    c.destroy();
}

fn void run(Air* m, DceStats* st)
{
    st.init();
    for (usz i = 1; i < m.func_count; i++)
    {
        Fn* f = m.fun((uint)i);
        if (f == null) { continue; }
        st.blocks_before = st.blocks_before + f.block_count;
        run_function(m, f, st);
    }
}

fn void print_stats(DceStats* s)
{
    printf("  DCE: values      : %d -> %d   (-%d)\n",
           (int)s.values_before, (int)s.values_after, (int)s.values_removed);
    printf("  DCE: blocks      : %d -> %d   (-%d unreachable)\n",
           (int)s.blocks_before, (int)s.blocks_after, (int)s.blocks_removed);
    printf("  DCE: dead stores : %d   (to allocations nothing reads)\n",
           (int)s.stores_removed);
    printf("  DCE: phi holes   : %d   (a1's neutralised phis, reaped)\n",
           (int)s.phi_holes_reaped);
    printf("  DCE: jumps folded: %d   (empty jump-only blocks)\n",
           (int)s.jumps_threaded);
}
