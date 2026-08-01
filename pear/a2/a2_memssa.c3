/*
 a2 — `M`, MemorySSA.

 a1 versions memory with a LINEAR walk in block order: every store takes
 the next version, every load reads whatever the last store was. Its own
 comment says so. That is correct for straight-line code and simply wrong
 across a join, because block order is not dominance order and there is no
 φ for memory at all — a load after an `if` whose two arms both store reads
 whichever arm happened to be laid out last.

 This pass replaces it with real MemorySSA, in the LLVM sense:

   MemoryDef        a store. Consumes one version, produces the next.
   MemoryUse        a load. Observes a version, produces none.
   MemoryPhi        a join of the versions arriving on each edge.

 Placement is Cytron's: MemoryPhi goes on the iterated dominance frontier
 of the set of blocks containing stores. Renaming is a pre-order walk of
 the dominator tree carrying a current version, which is why a2_cfg
 computes the dominator TREE and not just a dominance bitset.

 ── The difference from LLVM that actually matters ──────────────────────

 In LLVM, MemorySSA is an analysis: built on demand, consulted, discarded.
 It has no representation in a `.ll` file, so every consumer that wants it
 pays to rebuild it, and nothing downstream of serialisation can see it at
 all.

 Here the versions are IN the IR. `AIR_MEM_PHI` is a real value in a real
 block, and `mem=use:0<-3` on a load is part of the text. It round-trips.
 That is a capability difference, not a density one: after a5 writes a
 file, an LLVM consumer CANNOT ask "what wrote the memory this load reads"
 without recomputing, and a PEAR consumer can just read it.

 ── Aliasing: what is and is not claimed ────────────────────────────────

 The alias analysis here is deliberately shallow, and saying so is better
 than implying more. Two accesses are proven disjoint when they are
 rooted at DIFFERENT allocations, or at different fields of the same base.
 Anything else is assumed to alias. In particular there is no
 inter-procedural alias analysis, no escape analysis, and no attempt to
 disambiguate two index expressions into the same array.

 That is enough for the fact a5 wants to emit (`!noalias` on a fresh
 allocation) and enough for DCE to delete a store to a location never
 loaded, and it is honest about the rest.
*/

module pear_a2_memssa;

import pear_air;
import pear_erm;
import pear_a2_cfg;
import pear_a2_facts;
import pfront_core;

alias Air  = pear_air::AirModule;
alias Val  = pear_air::AirValue;
alias Blk  = pear_air::AirBlock;
alias Fn   = pear_air::AirFunc;
alias Op   = pear_air::AirOp;
alias Cfg  = pear_a2_cfg::Cfg;

extern fn int   printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn void  free(void* p);

const int NO_IDX = pear_a2_cfg::NO_IDX;

// ════════════════════════════════════════════════════════════════════════
// CLASSIFYING MEMORY OPERATIONS
// ════════════════════════════════════════════════════════════════════════

fn bool is_store(Op op)
{
    switch (op)
    {
        case AIR_STORE_PTR:
        case AIR_STORE_FIELD:
        case AIR_STORE_INDEX:
            return true;
        default:
            return false;
    }
}

fn bool is_load(Op op)
{
    switch (op)
    {
        case AIR_LOAD_PTR:
        case AIR_LOAD_FIELD:
        case AIR_LOAD_INDEX:
            return true;
        default:
            return false;
    }
}

/*
 Does this operation CLOBBER memory in a way no alias reasoning can bound?

 A call can write anything it can reach. `perform` transfers control to a
 handler that can do the same. Inline asm is opaque by construction.
 AIR_UNKNOWN is treated as clobbering precisely because it is unknown —
 the whole point of keeping it distinct from `poison` is that it makes no
 promises.

 Treating these as ordinary defs rather than clobbers would be the
 miscompile: a load after a call would be told it still reads the version
 from before the call.
*/
fn bool is_clobber(Op op)
{
    switch (op)
    {
        case AIR_CALL:
        case AIR_CALL_DIRECT:
        case AIR_PERFORM:
        case AIR_RESUME:
        case AIR_HANDLE:
        case AIR_HANDLE_ARM:
        case AIR_ASM:
        case AIR_ALLOC:
        case AIR_FREE:
        case AIR_UNKNOWN:
            return true;
        default:
            return false;
    }
}

/*
 Follow a pointer back to the object it is rooted at.

 Field and index addressing, σ, π and casts are all transparent: they
 rename or offset a pointer without changing which allocation it refers
 to. The walk stops at whatever is left, which is an alloc, a global, a
 parameter or a load — the things that can actually be distinct objects.

 The guard is a real bound, not decoration: σ and π chains in a loop can
 be long, and this is called once per memory operation.
*/
fn uint root_of(Air* m, uint v)
{
    uint cur = v;
    usz guard = 0;
    while (guard < 32)
    {
        guard = guard + 1;
        Val* vv = m.val(cur);
        if (vv == null || vv.op_count == 0) { return cur; }
        switch (vv.op)
        {
            case AIR_ADDR_FIELD:
            case AIR_ADDR_INDEX:
            case AIR_ADDR_OF:
            case AIR_SIGMA:
            case AIR_PI:
            case AIR_CAST:
                cur = m.operands[vv.op_off];
            default:
                return cur;
        }
    }
    return cur;
}

/*
 Can these two accesses refer to the same location?

 Conservative by default. Only two things are proven here, and both are
 sound without any type information — which matters because Pride is
 untyped and a type-based rule would be unavailable.

   1. Different ALLOCATIONS never alias. A fresh `alloc` is a new object,
      so it is disjoint from every pointer that existed before it.
   2. Different FIELDS of the same base never alias. `p.x` and `p.y` are
      distinct slots by construction.

 Everything else — two indices into the same array, two globals, anything
 through a parameter — is assumed to alias.
*/
fn bool may_alias(Air* m, uint a, uint b)
{
    if (a == b) { return true; }
    uint ra = root_of(m, a);
    uint rb = root_of(m, b);
    if (ra == rb)
    {
        // Same root: distinguish only by static field index.
        Val* va = m.val(a);
        Val* vb = m.val(b);
        if (va != null && vb != null
            && (va.op == Op.AIR_ADDR_FIELD || va.op == Op.AIR_LOAD_FIELD
                || va.op == Op.AIR_STORE_FIELD)
            && (vb.op == Op.AIR_ADDR_FIELD || vb.op == Op.AIR_LOAD_FIELD
                || vb.op == Op.AIR_STORE_FIELD))
        {
            return va.p.index == vb.p.index;
        }
        return true;
    }

    Val* va = m.val(ra);
    Val* vb = m.val(rb);
    if (va == null || vb == null) { return true; }

    // A fresh allocation is a distinct object from anything else rooted
    // somewhere else. This is the fact `!noalias` is made of.
    if (va.op == Op.AIR_ALLOC || vb.op == Op.AIR_ALLOC) { return false; }

    // Two DIFFERENT named globals are different objects.
    if (va.op == Op.AIR_GLOBAL_ADDR && vb.op == Op.AIR_GLOBAL_ADDR)
    {
        return va.p.name == vb.p.name;
    }
    return true;
}

/*
 The pointer operand of a memory operation.

 Layout differs per opcode (D2: three store opcodes rather than one with a
 mode flag), so this is the one place that knows which slot holds the
 address.
*/
fn uint mem_pointer(Air* m, uint vid)
{
    Val* v = m.val(vid);
    if (v == null || v.op_count == 0) { return pear_air::AIR_NO_VALUE; }
    return m.operands[v.op_off];      // operand 0 for every load and store
}

// ════════════════════════════════════════════════════════════════════════
// THE PASS
// ════════════════════════════════════════════════════════════════════════

struct MemStats
{
    usz defs;
    usz uses;
    usz phis_placed;
    usz clobbers;
    usz entry_loads;      // loads no store reaches: read state from the caller
    usz noalias_marked;   // accesses proven disjoint from everything else
    usz versions;
    usz repaired;         // a1 versions this pass had to correct
}

fn void MemStats.init(MemStats* s)
{
    s.defs = 0; s.uses = 0; s.phis_placed = 0; s.clobbers = 0;
    s.entry_loads = 0; s.noalias_marked = 0; s.versions = 0; s.repaired = 0;
}

struct MemBuild
{
    Air*   m;
    Cfg*   c;
    uint   next_version;
    uint   entry_tok;      // the AIR_MEM_ENTRY standing for version 0

    // Per local block index: the memory version live on entry / on exit.
    uint*  in_ver;
    uint*  out_ver;
    bool*  has_def;        // this block contains a def or clobber
    bool*  needs_phi;
    uint*  phi_value;      // the AIR_MEM_PHI placed in this block, or 0
    uint*  def_value;      // the VALUE that last defined memory in the block
}

fn void MemBuild.destroy(MemBuild* mb)
{
    if (mb.in_ver != null)    { free((void*)mb.in_ver); mb.in_ver = null; }
    if (mb.out_ver != null)   { free((void*)mb.out_ver); mb.out_ver = null; }
    if (mb.has_def != null)   { free((void*)mb.has_def); mb.has_def = null; }
    if (mb.needs_phi != null) { free((void*)mb.needs_phi); mb.needs_phi = null; }
    if (mb.phi_value != null) { free((void*)mb.phi_value); mb.phi_value = null; }
    if (mb.def_value != null) { free((void*)mb.def_value); mb.def_value = null; }
}

/*
 The value that last defined memory in each block — the operand a
 successor's MemoryPhi needs on the edge from that block.

 A block with no def of its own passes through whatever REACHED it, and
 the value that reaches it is its immediate dominator's exit value.

 Walking the dominator chain is what makes this correct, and the reason is
 worth stating because the obvious alternative is wrong in a way the
 verifier catches immediately. Taking the value from a PREDECESSOR would
 let a φ operand name a definition that only exists on one side of a
 branch, so on the other path the operand is undefined. The dominator's
 value, by construction, is live on every path that reaches the block.

 The propagation must run in REVERSE POSTORDER and must be a single
 forward sweep. Iterating it twice, as the first version did, is not
 merely wasteful: on a loop it lets a definition from inside the body
 propagate back to a block the body does not dominate, which is exactly
 the "operand's definition does not dominate its use" the verifier
 reported on four stdlib modules. RPO guarantees a block's dominator is
 finalised before the block is read, so one pass is both sufficient and
 the only sound number.
*/
fn void MemBuild.collect_def_values(MemBuild* mb)
{
    usz n = mb.c.n;
    for (usz i = 0; i < n; i++)
    {
        uint last = pear_air::AIR_NO_VALUE;
        Blk* b = mb.m.blk(mb.c.id_of[i]);
        if (b != null)
        {
            for (usz k = 0; k < b.value_count; k++)
            {
                Val* v = mb.m.val(b.values[k]);
                if (v == null || v.is_phi_hole) { continue; }
                if (v.facts.mem.kind == pear_erm::MemKind.MEM_DEF
                    || v.facts.mem.kind == pear_erm::MemKind.MEM_PHI)
                {
                    last = v.id;
                }
            }
        }
        mb.def_value[i] = last;
    }

    for (usz r = 0; r < mb.c.rpo_count; r++)
    {
        int b = mb.c.rpo[r];
        if (mb.def_value[b] != pear_air::AIR_NO_VALUE) { continue; }
        int d = mb.c.idom[b];
        if (d != NO_IDX && d != b) { mb.def_value[b] = mb.def_value[d]; }
    }

    /*
     A definition may only be inherited across a block it actually
     dominates.

     The dominator chain is the right structure to inherit along, but the
     inheritance has to be CHECKED, because a block's recorded def may have
     come from a sibling region rather than from an ancestor. That happens
     whenever a join has an unreachable predecessor: dominance treats the
     dead edge as if it does not exist, so the join's idom is an ordinary
     ancestor and nothing marks the join as needing a phi — but the join is
     still printed with two predecessors, and a phi built for it names an
     operand from a block that does not dominate the live one.

     This is not hypothetical. In stdlib/diag/demangle.pie, `b9` has
     predecessors `b7` and `b15`, and `b15` has no predecessors at all: it
     is dead code a1 left behind. The memory phi in `b11` then took its
     operand for predecessor `b12` from `b7`, which does not dominate
     `b12`, and the verifier rejected it — correctly.

     Rather than trusting the chain, verify it. An inherited value whose
     defining block does not dominate the inheriting block is dropped back
     to live-on-entry, which is always sound: version 0 is the weakest
     answer, never a wrong one.
    */
    for (usz i = 0; i < n; i++)
    {
        uint dv = mb.def_value[i];
        if (dv == pear_air::AIR_NO_VALUE) { continue; }
        Val* v = mb.m.val(dv);
        if (v == null) { mb.def_value[i] = pear_air::AIR_NO_VALUE; continue; }
        if ((usz)v.block >= mb.c.idx_cap) { continue; }
        int db = mb.c.idx_of[v.block];
        if (db == NO_IDX) { continue; }
        if (!mb.c.dominates(db, (int)i))
        {
            mb.def_value[i] = pear_air::AIR_NO_VALUE;
        }
    }
}

/*
 Re-fill MemoryPhi operands once every block's def value is final.

 During renaming a back edge's predecessor has not been walked yet, so its
 operand was the entry token. That is sound but imprecise, and leaving it
 would mean a loop-carried store is invisible to anything reading the phi.
 The operand SLICE is already the right length, so this rewrites in place
 and cannot change the phi's arity.
*/
fn void MemBuild.refill_phis(MemBuild* mb)
{
    uint entry_tok = mb.entry_token();
    for (usz i = 0; i < mb.c.n; i++)
    {
        uint pv = mb.phi_value[i];
        if (pv == pear_air::AIR_NO_VALUE) { continue; }
        Val* v = mb.m.val(pv);
        if (v == null) { continue; }
        for (usz k = 0; k < v.op_count && k < v.inc_count; k++)
        {
            uint from_g = mb.m.phi_blocks[v.inc_off + k];
            if ((usz)from_g >= mb.c.idx_cap) { continue; }
            int p = mb.c.idx_of[from_g];
            if (p == NO_IDX) { continue; }
            uint dv = mb.def_value[p];
            /*
             A phi must not name ITSELF as its own incoming value: that is
             what def_value says for the block the phi is in when the loop
             body defines nothing. Keep the entry token in that case.
            */
            if (dv == pv) { dv = pear_air::AIR_NO_VALUE; }
            mb.m.operands[v.op_off + k] =
                dv != pear_air::AIR_NO_VALUE ? dv : entry_tok;
        }
    }
}

/*
 Place MemoryPhi on the iterated dominance frontier of the store blocks.

 A φ is only placed in a block with more than one predecessor: a single-
 predecessor block has nothing to merge. IDF can name such a block when the
 CFG has an unreachable predecessor, and placing a one-operand φ there
 would fail the verifier's "one operand per predecessor" check.
*/
fn void MemBuild.place_phis(MemBuild* mb, MemStats* st)
{
    usz n = mb.c.n;
    if (n == 0) { return; }

    bool* defs = (bool*)malloc(n);
    bool* idf  = (bool*)malloc(n);
    if (defs == null || idf == null)
    {
        if (defs != null) { free((void*)defs); }
        if (idf != null) { free((void*)idf); }
        return;
    }
    for (usz i = 0; i < n; i++) { defs[i] = mb.has_def[i]; }

    mb.c.idf(defs, idf);

    for (usz i = 0; i < n; i++)
    {
        if (!idf[i]) { continue; }
        if (!mb.c.reachable((int)i)) { continue; }
        usz pc = mb.c.pred_count((int)i);
        if (pc < 2) { continue; }
        mb.needs_phi[i] = true;
    }
    free((void*)defs); free((void*)idf);

    /*
     A join with an UNREACHABLE predecessor still needs a phi.

     Dominance frontiers are computed over reachable blocks only, which is
     right: a dead edge carries no values and must not influence where a
     phi is required. But the block is still PRINTED with that predecessor,
     because a1 leaves dead blocks for DCE to remove and the pred list is
     the printed one. A phi in such a block therefore needs one operand per
     LISTED predecessor, and the block never appears in any frontier, so
     nothing here would have placed one.

     What happened instead was worse than a missing phi. With no phi at the
     join, `collect_def_values` inherited the definition from the block's
     immediate dominator and handed it to the phi in a LATER block, where
     it was an operand for a predecessor the definition does not reach.
     stdlib/diag/demangle.pie hit exactly this: `b9` joins `b7` and the
     dead `b15`, and `%31` from `b7` ended up as `b11`'s operand for
     predecessor `b12`.

     Placing the phi here is the fix, and it is also the honest shape: the
     block genuinely has two incoming edges as far as the serialised IR is
     concerned. When DCE removes the dead predecessor it drops the matching
     operand with it, and the phi collapses on its own.
    */
    for (usz i = 0; i < n; i++)
    {
        if (mb.needs_phi[i]) { continue; }
        if (!mb.c.reachable((int)i)) { continue; }
        Blk* b = mb.m.blk(mb.c.id_of[i]);
        if (b == null || b.pred_count < 2) { continue; }

        bool has_dead_pred = false;
        for (usz k = 0; k < b.pred_count; k++)
        {
            if ((usz)b.pred[k] >= mb.c.idx_cap) { continue; }
            int p = mb.c.idx_of[b.pred[k]];
            if (p == NO_IDX || !mb.c.reachable(p)) { has_dead_pred = true; break; }
        }
        if (has_dead_pred) { mb.needs_phi[i] = true; }
    }
}

/*
 Rename: walk the dominator tree in pre-order, carrying the current
 version.

 Pre-order is required, not merely convenient. A block's incoming version
 is the one live at its immediate dominator's exit, and that is only known
 after the dominator has been processed. Visiting in block order instead
 is exactly a1's bug.

 The walk is an explicit stack for the usual 64 KB reason.
*/
fn void MemBuild.rename(MemBuild* mb, MemStats* st)
{
    usz n = mb.c.n;
    if (n == 0) { return; }
    if (mb.c.rpo_count == 0) { return; }

    int* stack = (int*)malloc(n * int::size);
    if (stack == null) { return; }
    pear_a2_cfg::IntList kids;
    kids.init();

    usz sp = 0;
    stack[sp] = mb.c.rpo[0]; sp = sp + 1;

    while (sp > 0)
    {
        sp = sp - 1;
        int b = stack[sp];

        // Incoming version: the immediate dominator's exit version, or 0
        // (live-on-entry) at the root.
        uint cur;
        if (mb.c.idom[b] == b || mb.c.idom[b] == NO_IDX) { cur = 0; }
        else { cur = mb.out_ver[mb.c.idom[b]]; }

        // A MemoryPhi defines a fresh version at the top of the block.
        if (mb.needs_phi[b])
        {
            uint pv = mb.emit_phi(b, st);
            if (pv != pear_air::AIR_NO_VALUE)
            {
                cur = mb.m.val(pv).facts.mem.version;
            }
        }
        mb.in_ver[b] = cur;

        Blk* bb = mb.m.blk(mb.c.id_of[b]);
        if (bb != null)
        {
            for (usz i = 0; i < bb.value_count; i++)
            {
                uint vid = bb.values[i];
                Val* v = mb.m.val(vid);
                if (v == null || v.is_phi_hole) { continue; }
                if (v.op == Op.AIR_MEM_PHI) { continue; }   // handled above

                if (is_load(v.op))
                {
                    uint before = v.facts.mem.reaching;
                    v.facts.mem.kind = pear_erm::MemKind.MEM_USE;
                    v.facts.mem.reaching = cur;
                    v.facts.mem.version = 0;
                    st.uses = st.uses + 1;
                    if (cur == 0) { st.entry_loads = st.entry_loads + 1; }
                    if (before != cur) { st.repaired = st.repaired + 1; }
                    mb.mark_noalias(vid, st);
                }
                else if (is_store(v.op) || is_clobber(v.op))
                {
                    uint before = v.facts.mem.version;
                    uint nv = mb.next_version;
                    mb.next_version = mb.next_version + 1;
                    v.facts.mem.kind = pear_erm::MemKind.MEM_DEF;
                    v.facts.mem.reaching = cur;
                    v.facts.mem.version = nv;
                    cur = nv;
                    if (is_clobber(v.op)) { st.clobbers = st.clobbers + 1; }
                    else { st.defs = st.defs + 1; mb.mark_noalias(vid, st); }
                    if (before != nv) { st.repaired = st.repaired + 1; }
                }
            }
        }
        mb.out_ver[b] = cur;

        mb.c.dom_children(b, &kids);
        for (usz i = 0; i < kids.count; i++)
        {
            if (sp < n) { stack[sp] = kids.v[i]; sp = sp + 1; }
        }
    }

    kids.destroy();
    free((void*)stack);
}

/*
 Create the AIR_MEM_PHI for a block.

 Its operands are the memory-defining values reaching from each
 predecessor. A predecessor not yet renamed contributes version 0, which
 is sound (live-on-entry is the weakest answer) and is unavoidable on a
 back edge, where the loop's own defs are not known yet.

 The φ names VERSIONS, and the operand list holds the VALUES that defined
 them, so a consumer can go straight from the φ to the store.
*/
fn uint MemBuild.emit_phi(MemBuild* mb, int b, MemStats* st)
{
    if (mb.phi_value[b] != pear_air::AIR_NO_VALUE) { return mb.phi_value[b]; }

    usz pc = mb.c.pred_count(b);
    if (pc == 0) { return pear_air::AIR_NO_VALUE; }

    uint* ops  = (uint*)malloc(pc * uint::size);
    uint* incs = (uint*)malloc(pc * uint::size);
    if (ops == null || incs == null)
    {
        if (ops != null) { free((void*)ops); }
        if (incs != null) { free((void*)incs); }
        return pear_air::AIR_NO_VALUE;
    }

    /*
     Operands must be real value ids: the verifier rejects AIR_NO_VALUE in
     an operand slot. The memory-entry token is the value that stands for
     version 0, so a predecessor with no reaching def points at it.
    */
    uint entry_tok = mb.entry_token();
    usz k = 0;
    for (usz i = 0; i < pc; i++)
    {
        int p = mb.c.pred(b, i);
        if (p == NO_IDX) { continue; }
        uint defv = mb.def_value[p];
        ops[k] = defv != pear_air::AIR_NO_VALUE ? defv : entry_tok;
        incs[k] = mb.c.id_of[p];
        k = k + 1;
    }
    if (k == 0)
    {
        free((void*)ops); free((void*)incs);
        return pear_air::AIR_NO_VALUE;
    }

    uint ver = mb.next_version;
    mb.next_version = mb.next_version + 1;
    uint pv = mb.m.new_mem_phi(mb.c.id_of[b], ops, incs, k, ver, 0, 0);
    free((void*)ops); free((void*)incs);
    if (pv == pear_air::AIR_NO_VALUE) { return pv; }

    /*
     A φ must precede every non-φ in its block, and new_mem_phi appends.
     Move it to the front, past any scalar φ already there.
    */
    Blk* bb = mb.m.blk(mb.c.id_of[b]);
    if (bb != null && bb.value_count > 1)
    {
        usz last = bb.value_count - 1;
        usz insert = 0;
        while (insert < last)
        {
            Val* v = mb.m.val(bb.values[insert]);
            if (v == null) { break; }
            if (v.op != Op.AIR_PHI && v.op != Op.AIR_MEM_PHI && !v.is_phi_hole) { break; }
            insert = insert + 1;
        }
        for (usz i = last; i > insert; i--) { bb.values[i] = bb.values[i - 1]; }
        bb.values[insert] = pv;
    }

    mb.phi_value[b] = pv;
    st.phis_placed = st.phis_placed + 1;
    return pv;
}

/*
 Mark an access that provably aliases nothing else in the function.

 Checked against every other memory access rather than assumed from the
 opcode: an `alloc` whose pointer is stored somewhere escapes, and claiming
 noalias for it would be wrong. The quadratic scan is bounded by the
 memory-op count, which is small relative to value count in practice.
*/
fn void MemBuild.mark_noalias(MemBuild* mb, uint vid, MemStats* st)
{
    uint p = mem_pointer(mb.m, vid);
    if (p == pear_air::AIR_NO_VALUE) { return; }
    uint root = root_of(mb.m, p);
    Val* rv = mb.m.val(root);
    if (rv == null || rv.op != Op.AIR_ALLOC) { return; }

    for (usz i = 1; i < mb.m.value_count; i++)
    {
        Val* o = &mb.m.values[i];
        if (o.block == pear_air::AIR_NO_BLOCK || o.is_phi_hole) { continue; }
        if ((uint)i == vid) { continue; }
        if (is_clobber(o.op))
        {
            // A call could have been handed this pointer. Only safe if the
            // pointer is not among its operands.
            for (usz k = 0; k < o.op_count; k++)
            {
                if (root_of(mb.m, mb.m.operands[o.op_off + k]) == root) { return; }
            }
            continue;
        }
        if (!is_load(o.op) && !is_store(o.op)) { continue; }
        uint op2 = mem_pointer(mb.m, (uint)i);
        if (op2 == pear_air::AIR_NO_VALUE) { continue; }
        if (root_of(mb.m, op2) == root) { continue; }   // same object: fine
        if (may_alias(mb.m, p, op2)) { return; }
    }
    Val* v = mb.m.val(vid);
    if (v != null && !v.facts.mem.no_alias)
    {
        v.facts.mem.no_alias = true;
        st.noalias_marked = st.noalias_marked + 1;
    }
}

/*
 The AIR_MEM_ENTRY token of the current function, which stands for
 version 0. a1 emits one per function; if it is missing (hand-written IR),
 fall back to the first value in the entry block so the operand slot still
 names something real.
*/
fn uint MemBuild.entry_token(MemBuild* mb)
{
    if (mb.entry_tok != pear_air::AIR_NO_VALUE) { return mb.entry_tok; }
    Fn* f = mb.c.f;
    Blk* eb = mb.m.blk(f.entry);
    if (eb != null)
    {
        for (usz i = 0; i < eb.value_count; i++)
        {
            Val* v = mb.m.val(eb.values[i]);
            if (v != null && v.op == Op.AIR_MEM_ENTRY)
            {
                mb.entry_tok = v.id;
                return mb.entry_tok;
            }
        }
    }
    // No token: synthesise one at the top of the entry block.
    uint t = mb.m.new_mem_entry(f.entry, 0, 0);
    if (t != pear_air::AIR_NO_VALUE && eb != null && eb.value_count > 1)
    {
        usz last = eb.value_count - 1;
        for (usz i = last; i > 0; i--) { eb.values[i] = eb.values[i - 1]; }
        eb.values[0] = t;
    }
    mb.entry_tok = t;
    return t;
}

fn void run_function(Air* m, Fn* f, pear_a2_facts::Facts2* facts, MemStats* st)
{
    Cfg c;
    if (!c.init(m, f)) { c.destroy(); return; }
    if (c.n == 0) { c.destroy(); return; }

    MemBuild mb;
    mb.m = m;
    mb.c = &c;
    mb.next_version = 1;
    mb.entry_tok = pear_air::AIR_NO_VALUE;
    mb.in_ver    = (uint*)malloc(c.n * uint::size);
    mb.out_ver   = (uint*)malloc(c.n * uint::size);
    mb.has_def   = (bool*)malloc(c.n);
    mb.needs_phi = (bool*)malloc(c.n);
    mb.phi_value = (uint*)malloc(c.n * uint::size);
    mb.def_value = (uint*)malloc(c.n * uint::size);
    if (mb.in_ver == null || mb.out_ver == null || mb.has_def == null
        || mb.needs_phi == null || mb.phi_value == null || mb.def_value == null)
    {
        mb.destroy(); c.destroy(); return;
    }
    for (usz i = 0; i < c.n; i++)
    {
        mb.in_ver[i] = 0; mb.out_ver[i] = 0;
        mb.has_def[i] = false; mb.needs_phi[i] = false;
        mb.phi_value[i] = pear_air::AIR_NO_VALUE;
        mb.def_value[i] = pear_air::AIR_NO_VALUE;
    }

    // Which blocks define memory?
    for (usz i = 0; i < c.n; i++)
    {
        Blk* b = m.blk(c.id_of[i]);
        if (b == null) { continue; }
        for (usz k = 0; k < b.value_count; k++)
        {
            Val* v = m.val(b.values[k]);
            if (v == null || v.is_phi_hole) { continue; }
            if (is_store(v.op) || is_clobber(v.op)) { mb.has_def[i] = true; break; }
        }
    }

    mb.place_phis(st);
    mb.rename(st);

    // The value that last defined memory in each block, needed by the φ
    // operands. Computed after renaming, when versions are final.
    mb.collect_def_values();
    // Phi operands were filled from def_value during renaming, which for a
    // back edge was not yet known. Re-fill now that every block is done.
    mb.refill_phis();

    if (mb.next_version > st.versions) { st.versions = mb.next_version; }

    // D1: memory facts go into the origin table too, or they do not
    // survive the conversions between here and emission.
    for (usz i = 0; i < c.n; i++)
    {
        Blk* b = m.blk(c.id_of[i]);
        if (b == null) { continue; }
        for (usz k = 0; k < b.value_count; k++)
        {
            Val* v = m.val(b.values[k]);
            if (v == null || v.is_phi_hole) { continue; }
            if (v.facts.mem.kind == pear_erm::MemKind.MEM_NONE) { continue; }
            facts.learn(v.origin, v.facts, pear_a2_facts::FactSource.FS_MEMSSA);
        }
    }

    mb.destroy();
    c.destroy();
}

fn void run(Air* m, pear_a2_facts::Facts2* facts, MemStats* st)
{
    st.init();
    for (usz i = 1; i < m.func_count; i++)
    {
        Fn* f = m.fun((uint)i);
        if (f == null) { continue; }
        run_function(m, f, facts, st);
    }
}

fn void print_stats(MemStats* s)
{
    printf("  M: versions      : %d\n", (int)s.versions);
    printf("  M: defs / uses   : %d / %d\n", (int)s.defs, (int)s.uses);
    printf("  M: mem-phi placed: %d   (a1 places none: it has no join)\n",
           (int)s.phis_placed);
    printf("  M: clobbers      : %d   (calls, perform, asm)\n", (int)s.clobbers);
    printf("  M: entry loads   : %d   (read state from the caller)\n",
           (int)s.entry_loads);
    printf("  M: noalias       : %d\n", (int)s.noalias_marked);
    printf("  M: a1 corrected  : %d   (versions a1's linear walk got wrong)\n",
           (int)s.repaired);
}
