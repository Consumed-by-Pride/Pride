/*
 AIR verifier — build order step 2 in PEAR.md.

 "Verification exists before anything can produce bad IR." This module is
 written before the PNode -> AIR build path deliberately, so that the build
 path has something to be checked by from its first line.

 ── Two families of check ────────────────────────────────────────────────

 STRUCTURAL, inherited from ssi_ir.c3's verify() because that set is sound
 and worth keeping (PEAR.md section 8, "Kept, because they are right"):
   every reachable block has a terminator; succ/pred are symmetric; each φ
   has exactly one operand per predecessor; no dangling value references;
   the terminator's successor count matches its arity.

 SSI, the four strong-SSI properties from Boissinot et al. as restated in
 Tavares et al. 2012 (PEAR.md section 3):
   1. pseudo-definition       every variable has a definition at CFG entry
   2. single reaching-definition
                              each point is reached by at most one
                              definition of each variable
   3. pseudo-use              every variable has a use at CFG exit
   4. single upward-exposed-use
                              from each point at most one use is reachable
                              without passing a previous use

 ── Honesty about what is and is not checked ─────────────────────────────
 Properties 1 and 3 are stated over "variables" in a representation that
 has explicit entry/exit pseudo-instructions. AIR does not materialise
 those, so they are checked in the form they actually take here:
   1 becomes "every operand is dominated by its definition", which is the
     same claim once entry is the unique root
   3 becomes "every value is either used or is an effect/terminator
     operand", i.e. no value is defined and then abandoned
 Both are stated as such at each check, rather than being labelled with the
 paper's name and quietly checking something weaker.

 Property 4 is only meaningful once σ has been placed, so it is checked as
 "no two σ over the same origin are live on the same edge". Before
 split_sigma.c3 exists this is vacuously true, which is reported as
 `sigma_checked = 0` rather than as a pass.
*/

module pear_verify;

import pear_air;
import pfront_core;

alias Air  = pear_air::AirModule;
alias Val  = pear_air::AirValue;
alias Blk  = pear_air::AirBlock;
alias Fn   = pear_air::AirFunc;
alias Op   = pear_air::AirOp;
alias Term = pear_air::AirTerm;

extern fn int   printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn void* realloc(void* p, usz size);
extern fn void  free(void* p);

const usz MAX_REPORTED = 40;

// ════════════════════════════════════════════════════════════════════════
// REPORT
// ════════════════════════════════════════════════════════════════════════

/*
 Counts are reported whether flattering or not. `sigma_count` and
 `phi_count` in particular are the SP-ERM-e-SSI property metrics: a
 conversion that produced zero σ would "verify clean" while not being SSI
 at all, so the counts are part of the output rather than an afterthought.
*/
struct Report
{
    usz errors;
    usz warnings;

    usz blocks_checked;
    usz values_checked;
    usz reachable_blocks;
    usz unreachable_blocks;

    usz phi_count;
    usz sigma_count;
    usz effect_count;

    // How many of the four SSI properties were actually EXERCISED, as
    // opposed to vacuously satisfied. Reported so a suite cannot claim
    // strong-SSI verification on a program with no φ and no σ.
    usz dom_checked;
    usz sigma_checked;

    char*[MAX_REPORTED] msgs;
    uint[MAX_REPORTED]  where;
    usz  msg_count;
}

fn void Report.init(Report* r)
{
    r.errors = 0; r.warnings = 0;
    r.blocks_checked = 0; r.values_checked = 0;
    r.reachable_blocks = 0; r.unreachable_blocks = 0;
    r.phi_count = 0; r.sigma_count = 0; r.effect_count = 0;
    r.dom_checked = 0; r.sigma_checked = 0;
    r.msg_count = 0;
}

fn void Report.err(Report* r, char* msg, uint where)
{
    r.errors = r.errors + 1;
    if (r.msg_count < MAX_REPORTED)
    {
        r.msgs[r.msg_count] = msg;
        r.where[r.msg_count] = where;
        r.msg_count = r.msg_count + 1;
    }
}

fn void Report.warn(Report* r, char* msg, uint where)
{
    r.warnings = r.warnings + 1;
    if (r.msg_count < MAX_REPORTED)
    {
        r.msgs[r.msg_count] = msg;
        r.where[r.msg_count] = where;
        r.msg_count = r.msg_count + 1;
    }
}

fn void print_report(Report* r)
{
    printf("  blocks           : %d (%d reachable, %d unreachable)\n",
           (int)r.blocks_checked, (int)r.reachable_blocks, (int)r.unreachable_blocks);
    printf("  values           : %d\n", (int)r.values_checked);
    printf("  phi / sigma      : %d / %d\n", (int)r.phi_count, (int)r.sigma_count);
    printf("  effectful values : %d\n", (int)r.effect_count);
    printf("  dominance checks : %d\n", (int)r.dom_checked);
    printf("  sigma-edge checks: %d\n", (int)r.sigma_checked);
    printf("  errors / warnings: %d / %d\n", (int)r.errors, (int)r.warnings);
    for (usz i = 0; i < r.msg_count; i++)
    {
        printf("    - %s (at %d)\n", r.msgs[i], (int)r.where[i]);
    }
}

// ════════════════════════════════════════════════════════════════════════
// REACHABILITY
// ════════════════════════════════════════════════════════════════════════

/*
 Mark blocks reachable from the function entry. Unreachable blocks are a
 WARNING, not an error: a1's lowering can legitimately leave one behind
 after folding a constant condition, and a2's DCE is what removes them.
 Treating it as an error would force a1 to do a2's job.
*/
fn void mark_reachable(Air* m, uint entry, bool* seen, usz n)
{
    if (entry == pear_air::AIR_NO_BLOCK) { return; }
    // Explicit worklist. A recursive walk would blow the 64 KB C3 stack
    // limit on a long chain of blocks, which is a real limit here, not a
    // hypothetical one.
    uint* stack = (uint*)malloc(n * uint::size);
    if (stack == null) { return; }
    usz sp = 0;
    stack[sp] = entry; sp = sp + 1;
    seen[entry] = true;
    while (sp > 0)
    {
        sp = sp - 1;
        uint b = stack[sp];
        Blk* bb = m.blk(b);
        if (bb == null) { continue; }
        for (usz i = 0; i < bb.succ_count; i++)
        {
            uint s = bb.succ[i];
            if ((usz)s < n && !seen[s])
            {
                seen[s] = true;
                if (sp < n) { stack[sp] = s; sp = sp + 1; }
            }
        }
    }
    free((void*)stack);
}

// ════════════════════════════════════════════════════════════════════════
// DOMINANCE
// ════════════════════════════════════════════════════════════════════════

/*
 Iterative dominator computation (Cooper–Harvey–Kennedy style, but over a
 simple bitset since AIR functions are small).

 `dom[b]` is a bitset of blocks that dominate b. This is needed for SSI
 property 2 (single reaching definition): an operand's definition must
 dominate its use, or two definitions could reach the same point.

 A dense bitset is fine here — a function with 200 blocks costs 200*25
 bytes. If a2 ever produces functions where this matters, the note in
 PEAR.md D6 applies: report, then degrade, never silently truncate.
*/
struct Dom
{
    ulong* bits;      // n words per block
    usz    words;
    usz    n;
    bool   ok;
}

fn bool Dom.init(Dom* d, usz n)
{
    d.n = n;
    d.words = (n + 63) / 64;
    if (d.words == 0) { d.words = 1; }
    usz total = n * d.words;
    d.bits = (ulong*)malloc(total * ulong::size);
    d.ok = d.bits != null;
    if (!d.ok) { return false; }
    for (usz i = 0; i < total; i++) { d.bits[i] = 0; }
    return true;
}

fn void Dom.destroy(Dom* d)
{
    if (d.bits != null) { free((void*)d.bits); d.bits = null; }
}

fn void Dom.set(Dom* d, usz b, usz x)
{
    if (b >= d.n || x >= d.n) { return; }
    d.bits[b * d.words + x / 64] |= (ulong)1 << (ulong)(x % 64);
}

fn bool Dom.test(Dom* d, usz b, usz x)
{
    if (b >= d.n || x >= d.n) { return false; }
    return (d.bits[b * d.words + x / 64] & ((ulong)1 << (ulong)(x % 64))) != 0;
}

fn void Dom.fill(Dom* d, usz b)
{
    for (usz w = 0; w < d.words; w++) { d.bits[b * d.words + w] = ~(ulong)0; }
}

fn void Dom.clear_row(Dom* d, usz b)
{
    for (usz w = 0; w < d.words; w++) { d.bits[b * d.words + w] = 0; }
}

// dst &= src; returns true if dst changed.
fn bool Dom.intersect(Dom* d, usz dst, usz src)
{
    bool changed = false;
    for (usz w = 0; w < d.words; w++)
    {
        ulong before = d.bits[dst * d.words + w];
        ulong after = before & d.bits[src * d.words + w];
        if (after != before) { changed = true; d.bits[dst * d.words + w] = after; }
    }
    return changed;
}

fn void Dom.copy_row(Dom* d, usz dst, usz src)
{
    for (usz w = 0; w < d.words; w++)
    {
        d.bits[dst * d.words + w] = d.bits[src * d.words + w];
    }
}

/*
 Compute dominators for the blocks of one function.

 dom(entry) = {entry}
 dom(b)     = {b} ∪ (⋂ dom(p) for p in preds(b))

 Iterated to a fixpoint. Only reachable blocks participate: an unreachable
 block has no predecessors, and giving it the universal set would make it
 appear to dominate everything.
*/
fn void compute_dom(Air* m, Fn* f, Dom* d, bool* reach)
{
    // Scratch row at index n-1 is not safe to borrow, so allocate one extra
    // row's worth of space by convention: callers pass nblocks = block_count
    // and the module always has a reserved slot 0, which is never a real
    // block and is used here as scratch.
    const usz SCRATCH = 0;

    for (usz i = 0; i < f.block_count; i++)
    {
        uint b = f.blocks[i];
        if (b == f.entry) { d.clear_row(b); d.set(b, b); }
        else if (reach[b]) { d.fill(b); }
        else { d.clear_row(b); }
    }

    bool changed = true;
    usz guard = 0;
    while (changed && guard < 1000)
    {
        changed = false;
        guard = guard + 1;
        for (usz i = 0; i < f.block_count; i++)
        {
            uint b = f.blocks[i];
            if (b == f.entry || !reach[b]) { continue; }
            Blk* bb = m.blk(b);
            if (bb == null) { continue; }

            bool first = true;
            for (usz pi = 0; pi < bb.pred_count; pi++)
            {
                uint p = bb.pred[pi];
                if (!reach[p]) { continue; }
                if (first) { d.copy_row(SCRATCH, p); first = false; }
                else       { d.intersect(SCRATCH, p); }
            }
            if (first) { continue; }        // no reachable predecessor
            d.set(SCRATCH, b);              // a block dominates itself

            // Commit if different.
            for (usz w = 0; w < d.words; w++)
            {
                if (d.bits[b * d.words + w] != d.bits[SCRATCH * d.words + w])
                {
                    changed = true;
                    break;
                }
            }
            if (changed) { d.copy_row(b, SCRATCH); }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════
// THE CHECKS
// ════════════════════════════════════════════════════════════════════════

/*
 Where in the block a value is defined, so a same-block use can be checked
 against its definition's position. Returns -1 if not found.
*/
fn int position_in_block(Air* m, uint bid, uint vid)
{
    Blk* b = m.blk(bid);
    if (b == null) { return -1; }
    for (usz i = 0; i < b.value_count; i++)
    {
        if (b.values[i] == vid) { return (int)i; }
    }
    return -1;
}

fn void check_function(Air* m, Fn* f, Report* r)
{
    usz n = m.block_count;
    bool* reach = (bool*)malloc(n);
    if (reach == null) { return; }
    for (usz i = 0; i < n; i++) { reach[i] = false; }
    mark_reachable(m, f.entry, reach, n);

    if (f.entry == pear_air::AIR_NO_BLOCK)
    {
        r.err("function has no entry block", f.id);
    }

    Dom d;
    bool have_dom = d.init(n);
    if (have_dom) { compute_dom(m, f, &d, reach); }

    for (usz bi = 0; bi < f.block_count; bi++)
    {
        uint bid = f.blocks[bi];
        Blk* b = m.blk(bid);
        if (b == null) { continue; }
        r.blocks_checked = r.blocks_checked + 1;
        b.reachable = reach[bid];
        if (reach[bid]) { r.reachable_blocks = r.reachable_blocks + 1; }
        else
        {
            r.unreachable_blocks = r.unreachable_blocks + 1;
            // Warning, not error: a2's DCE removes these. See the note at
            // mark_reachable.
            r.warn("unreachable block", bid);
        }

        // ── STRUCTURAL: every reachable block is terminated ─────────────
        if (reach[bid] && b.term == Term.TERM_OPEN)
        {
            r.err("reachable block has no terminator", bid);
        }

        // ── STRUCTURAL: terminator arity matches successor count ────────
        int want = pear_air::term_arity(b.term);
        if (want >= 0 && b.succ_count != (usz)want && b.term != Term.TERM_OPEN)
        {
            r.err("terminator successor count disagrees with its arity", bid);
        }
        if (pear_air::term_is_divergent(b.term) && b.succ_count != 0)
        {
            r.err("divergent terminator has successors", bid);
        }
        if (b.term == Term.TERM_SWITCH)
        {
            // One case value per non-default successor.
            usz want_cases = b.has_default && b.succ_count > 0
                           ? b.succ_count - 1 : b.succ_count;
            if (b.case_count != want_cases)
            {
                r.err("switch case count disagrees with successor count", bid);
            }
        }

        // ── STRUCTURAL: succ/pred symmetry ──────────────────────────────
        for (usz si = 0; si < b.succ_count; si++)
        {
            uint s = b.succ[si];
            Blk* sb = m.blk(s);
            if (sb == null) { r.err("successor does not exist", bid); continue; }
            usz found = 0;
            for (usz pi = 0; pi < sb.pred_count; pi++)
            {
                if (sb.pred[pi] == bid) { found = found + 1; }
            }
            if (found == 0) { r.err("successor does not list this block as a predecessor", bid); }
        }
        for (usz pi = 0; pi < b.pred_count; pi++)
        {
            uint p = b.pred[pi];
            Blk* pb = m.blk(p);
            if (pb == null) { r.err("predecessor does not exist", bid); continue; }
            usz found = 0;
            for (usz si = 0; si < pb.succ_count; si++)
            {
                if (pb.succ[si] == bid) { found = found + 1; }
            }
            if (found == 0) { r.err("predecessor does not list this block as a successor", bid); }
        }

        // ── values ──────────────────────────────────────────────────────
        bool seen_non_phi = false;
        for (usz vi = 0; vi < b.value_count; vi++)
        {
            uint vid = b.values[vi];
            Val* v = m.val(vid);
            if (v == null) { r.err("block lists a value that does not exist", bid); continue; }
            r.values_checked = r.values_checked + 1;

            if (v.block != bid)
            {
                r.err("value's block field disagrees with the block listing it", vid);
            }
            if (pear_air::op_has_effect(v.op)) { r.effect_count = r.effect_count + 1; }

            // ── STRUCTURAL: no dangling operand references ──────────────
            for (usz oi = 0; oi < v.op_count; oi++)
            {
                uint o = m.operands[v.op_off + oi];
                if (o == pear_air::AIR_NO_VALUE)
                {
                    r.err("operand is the null value id", vid);
                    continue;
                }
                if (m.val(o) == null) { r.err("operand references a value that does not exist", vid); }
            }

            if (v.op == Op.AIR_PHI)
            {
                r.phi_count = r.phi_count + 1;

                // ── STRUCTURAL: φ must come before any non-φ ────────────
                // A φ is a parallel copy on the incoming edges, so it has no
                // meaningful position after a real instruction.
                if (seen_non_phi) { r.err("phi appears after a non-phi value", vid); }

                // ── STRUCTURAL: one operand per predecessor ─────────────
                if (v.inc_count != v.op_count)
                {
                    r.err("phi operand count differs from its incoming-block count", vid);
                }
                if (reach[bid] && v.op_count != b.pred_count)
                {
                    r.err("phi has a different number of operands than the block has predecessors", vid);
                }
                // Every incoming block must actually be a predecessor.
                for (usz ii = 0; ii < v.inc_count; ii++)
                {
                    uint inb = m.phi_blocks[v.inc_off + ii];
                    bool is_pred = false;
                    for (usz pi = 0; pi < b.pred_count; pi++)
                    {
                        if (b.pred[pi] == inb) { is_pred = true; break; }
                    }
                    if (!is_pred) { r.err("phi names an incoming block that is not a predecessor", vid); }
                }
            }
            else if (!v.is_phi_hole)
            {
                /*
                 A PHI HOLE does not count as a real instruction.

                 remove_trivial_phi neutralises a trivial φ in place rather
                 than deleting it, because deleting from the middle of a
                 block invalidates every position other code holds. The
                 dead slot can therefore sit BETWEEN two live φ, which is
                 harmless — but counting it as a non-φ made this check
                 report "phi appears after a non-phi value" on correct IR.

                 Verified on a real loop: `while i < n` with two
                 loop-carried variables produces exactly this shape, and
                 the IR was right while the check was too strict.
                */
                seen_non_phi = true;
            }

            if (v.op == Op.AIR_SIGMA)
            {
                r.sigma_count = r.sigma_count + 1;
                if (v.op_count != 1) { r.err("sigma must have exactly one operand", vid); }
                if (v.p.fact == pear_air::AirFact.FACT_NONE)
                {
                    // A σ carrying no fact is pure overhead: it splits a
                    // live range and tells the range analysis nothing. It is
                    // a warning rather than an error because a1 may
                    // legitimately place one before the fact is known.
                    r.warn("sigma carries no refinement fact", vid);
                }
                /*
                 D1. A σ RENAMES a value, so it must carry that value's
                 origin forward. If it started a new lineage, every fact a2
                 learned about the original would be unattributable after
                 the split — which is precisely how `R` ends up decorative.
                */
                uint src = m.operands[v.op_off];
                Val* sv = m.val(src);
                if (sv != null && v.origin != sv.origin)
                {
                    r.err("sigma does not inherit its source's origin (D1)", vid);
                }
            }

            /*
             ── SSI property 2: single reaching definition ────────────────
             Enforced as "the definition of every operand dominates its
             use". With a unique entry, that is equivalent: if a definition
             did not dominate the use, some path would reach the use
             without it, so either another definition reaches (two reaching
             definitions) or none does (use before def).

             φ is the exception and is checked differently: operand i is
             evaluated on the edge from incoming[i], so it must dominate
             that PREDECESSOR's exit, not the φ's own block.
            */
            if (!have_dom || !reach[bid]) { continue; }

            for (usz oi = 0; oi < v.op_count; oi++)
            {
                uint o = m.operands[v.op_off + oi];
                Val* ov = m.val(o);
                if (ov == null) { continue; }
                if (ov.block == pear_air::AIR_NO_BLOCK) { continue; }  // reader placeholder

                r.dom_checked = r.dom_checked + 1;

                if (v.op == Op.AIR_PHI)
                {
                    uint inb = oi < v.inc_count ? m.phi_blocks[v.inc_off + oi]
                                                : pear_air::AIR_NO_BLOCK;
                    if (inb == pear_air::AIR_NO_BLOCK || !reach[inb]) { continue; }
                    if (!d.test(inb, ov.block))
                    {
                        r.err("phi operand's definition does not dominate the incoming edge", vid);
                    }
                    continue;
                }

                if (ov.block == bid)
                {
                    // Same block: the definition must come earlier.
                    int dpos = position_in_block(m, bid, o);
                    int upos = (int)vi;
                    if (dpos < 0 || dpos >= upos)
                    {
                        r.err("operand is used before it is defined in the same block", vid);
                    }
                }
                else if (!d.test(bid, ov.block))
                {
                    r.err("operand's definition does not dominate its use", vid);
                }
            }
        }

        // ── STRUCTURAL: the terminator's own operand ────────────────────
        if (b.term == Term.TERM_BRANCH || b.term == Term.TERM_SWITCH)
        {
            if (b.term_value == pear_air::AIR_NO_VALUE)
            {
                r.err("branch/switch has no scrutinee", bid);
            }
            else if (m.val(b.term_value) == null)
            {
                r.err("terminator scrutinee references a value that does not exist", bid);
            }
        }
        if (b.term == Term.TERM_RET && b.term_value != pear_air::AIR_NO_VALUE)
        {
            if (m.val(b.term_value) == null)
            {
                r.err("return value references a value that does not exist", bid);
            }
        }
    }

    /*
     ── SSI properties 1 and 3, in the form AIR can actually state ───────

     1 (pseudo-definition) becomes: every function PARAMETER is defined in
       the entry block. AIR has no entry pseudo-instruction, so this is the
       concrete content of "every variable has a definition at CFG entry".

     3 (pseudo-use) becomes: no value is defined and then abandoned. A pure
       value with no use is dead code, which is a2's business, so it is a
       WARNING. An EFFECTFUL value with no use is fine — that is the point
       of an effect — so it is exempt.
    */
    for (usz pi = 0; pi < f.param_count; pi++)
    {
        Val* p = m.val(f.params[pi]);
        if (p == null) { r.err("parameter references a value that does not exist", f.id); continue; }
        if (p.op != Op.AIR_PARAM) { r.err("parameter list holds a non-param value", p.id); }
        if (p.block != f.entry)
        {
            r.err("parameter is not defined in the entry block (SSI property 1)", p.id);
        }
    }

    free((void*)reach);
    if (have_dom) { d.destroy(); }
}

/*
 SSI property 3, module-wide: count values that are never used and are not
 effectful. Reported as a warning count rather than a per-value message,
 because on unoptimised a1 output this is expected to be nonzero and a
 flood of messages would drown the real errors.
*/
fn void check_abandoned(Air* m, Report* r)
{
    usz n = m.value_count;
    bool* used = (bool*)malloc(n);
    if (used == null) { return; }
    for (usz i = 0; i < n; i++) { used[i] = false; }

    for (usz i = 1; i < n; i++)
    {
        Val* v = &m.values[i];
        for (usz oi = 0; oi < v.op_count; oi++)
        {
            uint o = m.operands[v.op_off + oi];
            if ((usz)o < n) { used[o] = true; }
        }
    }
    for (usz i = 1; i < m.block_count; i++)
    {
        Blk* b = &m.blocks[i];
        if (b.term_value != pear_air::AIR_NO_VALUE && (usz)b.term_value < n)
        {
            used[b.term_value] = true;
        }
    }
    for (usz i = 1; i < m.func_count; i++)
    {
        Fn* f = &m.funcs[i];
        for (usz pi = 0; pi < f.param_count; pi++)
        {
            if ((usz)f.params[pi] < n) { used[f.params[pi]] = true; }
        }
    }

    usz abandoned = 0;
    for (usz i = 1; i < n; i++)
    {
        Val* v = &m.values[i];
        if (v.block == pear_air::AIR_NO_BLOCK) { continue; }   // reader placeholder
        if (used[i]) { continue; }
        if (pear_air::op_has_effect(v.op)) { continue; }
        if (!pear_air::op_yields_value(v.op)) { continue; }
        abandoned = abandoned + 1;
    }
    if (abandoned > 0)
    {
        r.warnings = r.warnings + abandoned;
        if (r.msg_count < MAX_REPORTED)
        {
            r.msgs[r.msg_count] = "pure values defined but never used (SSI property 3)";
            r.where[r.msg_count] = (uint)abandoned;
            r.msg_count = r.msg_count + 1;
        }
    }
    free((void*)used);
}

/*
 SSI property 4, single upward-exposed-use, in the form it takes here: two
 σ derived from the SAME origin must not both be live out of the same
 block, because then a use downstream could be reached by either and the
 "at most one upward-exposed use" guarantee is gone.

 Before split_sigma.c3 exists there are no σ to check and this is vacuous.
 That is why `sigma_checked` is reported: a suite must not be able to claim
 property 4 holds when nothing exercised it.
*/
fn void check_sigma_edges(Air* m, Report* r)
{
    for (usz bi = 1; bi < m.block_count; bi++)
    {
        Blk* b = &m.blocks[bi];
        if (b.value_count == 0) { continue; }

        for (usz i = 0; i < b.value_count; i++)
        {
            Val* vi_ = m.val(b.values[i]);
            if (vi_ == null || vi_.op != Op.AIR_SIGMA) { continue; }
            for (usz j = i + 1; j < b.value_count; j++)
            {
                Val* vj = m.val(b.values[j]);
                if (vj == null || vj.op != Op.AIR_SIGMA) { continue; }
                if (vi_.origin != vj.origin) { continue; }
                r.sigma_checked = r.sigma_checked + 1;
                /*
                 Two σ over the same origin in one block is CORRECT and
                 expected for a two-way branch: one per outgoing edge. It
                 is only a violation if they carry the same fact, which
                 would mean the split distinguishes nothing.
                */
                if (vi_.p.fact == vj.p.fact)
                {
                    r.err("two sigmas over the same origin carry the same fact (SSI property 4)",
                          vj.id);
                }
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════
// ENTRY POINT
// ════════════════════════════════════════════════════════════════════════

fn void verify(Air* m, Report* r)
{
    r.init();

    // D6: an overflowed module is INCOMPLETE, and every subsequent check
    // would be reasoning about truncated data. Say so loudly rather than
    // reporting a clean verify on partial IR.
    if (m.overflowed)
    {
        r.err("module overflowed during construction; IR is incomplete", 0);
    }

    for (usz i = 1; i < m.func_count; i++)
    {
        check_function(m, &m.funcs[i], r);
    }
    check_abandoned(m, r);
    check_sigma_edges(m, r);
}
