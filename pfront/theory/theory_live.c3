// ============================================================================
// theory_live.c3 — CFG construction, liveness, and Semi-Pruned classification
// ----------------------------------------------------------------------------
// This module supplies the **SP** of SP-ERM-e-SSI.
//
// The three classical placement strategies for φ-functions differ only in how
// many they insert:
//
//   MINIMAL      one φ at every iterated dominance frontier of every
//                definition. Correct, and wasteful: most of those φs are for
//                variables that are dead at the join.
//
//   PRUNED       insert a φ only where the variable is LIVE-IN at the join.
//                Minimal φ count, but it needs full iterative liveness for
//                every variable before any φ can be placed.
//
//   SEMI-PRUNED  the compromise, and what Pride uses. Compute the set of
//                variables that are live ACROSS a block boundary — the
//                "non-local" variables — and place φs only for those. A
//                variable used and killed inside one block can never need a
//                φ, so it is excluded without ever running full liveness.
//
// Briggs, Cooper, Harvey and Simpson ("Practical Improvements to the
// Construction and Destruction of Static Single Assignment Form", SP&E 1998)
// measured semi-pruned as capturing most of pruned's benefit at a fraction of
// the analysis cost, which is exactly the trade Pride wants: the front end
// runs on every keystroke in an editor, the back end does not.
//
// What this module computes, in order:
//
//   1. A CONTROL FLOW GRAPH over the AST. Pride has no goto, so the CFG shape
//      is determined syntactically: `if` forks and rejoins, `while` has a
//      back edge, `return`/`break`/`ub!` terminate.
//   2. Per-block DEF and USE sets (the "locally exposed uses" of the
//      dragon book).
//   3. LIVE-IN / LIVE-OUT by backward iterative dataflow to a fixpoint.
//   4. The NON-LOCAL set: variables live across at least one edge. This is
//      the semi-pruned φ-placement set.
//   5. DEAD DEFINITIONS: a def whose variable is not live-out of the defining
//      block and is never used later in it. These feed the optimizer.
//
// Everything is bitsets over a dense variable numbering, so the dataflow
// inner loop is a word-at-a-time OR rather than a per-variable test.
// ============================================================================

module theory_live;

import pfront_core;
import pfront_lex;

alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

// Capacity. These decide how large a single FUNCTION the analysis can handle
// exactly (not the whole program -- state is reset per function).
//
// The cost is quadratic-ish in LV_MAX_VARS: every BlockInfo carries four
// bitsets of LV_WORDS each, and there are LV_MAX_BLOCKS of them. At 8192
// vars / 4096 blocks that is ~16 MB, which is fine for one heap allocation
// and covers generated code that a human would never write by hand.
//
// Exceeding either cap sets `overflowed` and the report says so -- the
// analysis degrades loudly, never silently.
const usz LV_MAX_BLOCKS = 4096;
const usz LV_MAX_VARS   = 8192;
const usz LV_WORDS      = LV_MAX_VARS / 64;   // 128 words = 8192 bits
const usz LV_MAX_SUCC   = 4;
const usz LV_MAX_STMTS  = 64;
const int LV_MAX_DEPTH  = 300;
const int LV_MAX_ITERS  = 64;

// ════════════════════════════════════════════════════════════════════════════
// BITSET
// ════════════════════════════════════════════════════════════════════════════
// Fixed-width so a BlockInfo is a flat struct with no allocation. 2048
// variables per function is far beyond anything hand-written; the builder
// reports an overflow rather than silently analysing a subset.

struct BitSet
{
    ulong[LV_WORDS] w;
}

fn void bs_clear(BitSet* b)
{
    for (usz i = 0; i < LV_WORDS; i++) { b.w[i] = 0; }
}

fn void bs_set(BitSet* b, usz bit)
{
    if (bit >= LV_MAX_VARS) { return; }
    b.w[bit >> 6] = b.w[bit >> 6] | (1UL << (ulong)(bit & 63));
}

fn bool bs_test(BitSet* b, usz bit)
{
    if (bit >= LV_MAX_VARS) { return false; }
    return (b.w[bit >> 6] & (1UL << (ulong)(bit & 63))) != 0;
}

fn void bs_clear_bit(BitSet* b, usz bit)
{
    if (bit >= LV_MAX_VARS) { return; }
    b.w[bit >> 6] = b.w[bit >> 6] & ~(1UL << (ulong)(bit & 63));
}

// dst |= src, returning whether dst changed. The return value is what drives
// the dataflow fixpoint: iterate until no set changes.
fn bool bs_union(BitSet* dst, BitSet* src)
{
    bool changed = false;
    for (usz i = 0; i < LV_WORDS; i++)
    {
        ulong before = dst.w[i];
        ulong after = before | src.w[i];
        if (after != before) { dst.w[i] = after; changed = true; }
    }
    return changed;
}

// dst = (src \ kill) | gen  — the classic transfer function, fused so the
// whole thing is one pass over the words.
fn bool bs_transfer(BitSet* dst, BitSet* src, BitSet* kill, BitSet* gen)
{
    bool changed = false;
    for (usz i = 0; i < LV_WORDS; i++)
    {
        ulong before = dst.w[i];
        ulong after = (src.w[i] & ~kill.w[i]) | gen.w[i];
        if (after != before) { dst.w[i] = after; changed = true; }
    }
    return changed;
}

fn usz bs_count(BitSet* b)
{
    usz total = 0;
    for (usz i = 0; i < LV_WORDS; i++)
    {
        ulong x = b.w[i];
        // Kernighan popcount: loops once per SET bit, not once per bit.
        while (x != 0) { x = x & (x - 1); total = total + 1; }
    }
    return total;
}

fn bool bs_empty(BitSet* b)
{
    for (usz i = 0; i < LV_WORDS; i++) { if (b.w[i] != 0) { return false; } }
    return true;
}

// ════════════════════════════════════════════════════════════════════════════
// VARIABLE NUMBERING
// ════════════════════════════════════════════════════════════════════════════
// Dense ids so a variable set is a bitset index rather than a pointer list.

struct VarEntry
{
    Node* binder;
    uint  name_id;
    usz   defs;
    usz   uses;
    bool  non_local;      // live across a block boundary -> needs a phi
    bool  addr_taken;     // `&x` seen: conservatively live everywhere
}

const usz LV_VAR_BUCKETS = 16384;   // 2x LV_MAX_VARS

struct VarNumbering
{
    VarEntry[LV_MAX_VARS]    items;
    uint[LV_VAR_BUCKETS]     buckets;   // index+1, 0 = empty
    usz  count;
    bool overflow;
}

fn ulong lv_hash(void* p)
{
    ulong x = (ulong)(usz)p;
    x = x ^ (x >> 30);
    x = x * 0xbf58476d1ce4e5b9UL;
    x = x ^ (x >> 27);
    x = x * 0x94d049bb133111ebUL;
    x = x ^ (x >> 31);
    return x;
}

fn void VarNumbering.init(VarNumbering* v)
{
    v.count = 0;
    v.overflow = false;
    for (usz i = 0; i < LV_VAR_BUCKETS; i++) { v.buckets[i] = 0; }
}

fn int VarNumbering.find(VarNumbering* v, Node* binder)
{
    usz mask = LV_VAR_BUCKETS - 1;
    usz b = (usz)lv_hash((void*)binder) & mask;
    for (usz probe = 0; probe < LV_VAR_BUCKETS; probe++)
    {
        uint slot = v.buckets[b];
        if (slot == 0) { return -1; }
        if (v.items[slot - 1].binder == binder) { return (int)(slot - 1); }
        b = (b + 1) & mask;
    }
    return -1;
}

fn int VarNumbering.intern(VarNumbering* v, Node* binder, uint name)
{
    if (binder == null) { return -1; }
    usz mask = LV_VAR_BUCKETS - 1;
    usz b = (usz)lv_hash((void*)binder) & mask;
    for (usz probe = 0; probe < LV_VAR_BUCKETS; probe++)
    {
        uint slot = v.buckets[b];
        if (slot == 0)
        {
            if (v.count >= LV_MAX_VARS) { v.overflow = true; return -1; }
            usz i = v.count;
            v.items[i].binder = binder;
            v.items[i].name_id = name;
            v.items[i].defs = 0;
            v.items[i].uses = 0;
            v.items[i].non_local = false;
            v.items[i].addr_taken = false;
            v.count = v.count + 1;
            v.buckets[b] = (uint)(i + 1);
            return (int)i;
        }
        if (v.items[slot - 1].binder == binder) { return (int)(slot - 1); }
        b = (b + 1) & mask;
    }
    v.overflow = true;
    return -1;
}

// ════════════════════════════════════════════════════════════════════════════
// CONTROL FLOW GRAPH
// ════════════════════════════════════════════════════════════════════════════
// Pride has structured control flow only: no goto, no computed branch. That
// makes the CFG derivable from the AST shape, which is both simpler and more
// reliable than recovering it from a flattened instruction list.

const int BK_ENTRY  = 0;
const int BK_NORMAL = 1;
const int BK_THEN   = 2;
const int BK_ELSE   = 3;
const int BK_JOIN   = 4;
const int BK_LOOP   = 5;   // loop header: has a back edge into it
const int BK_BODY   = 6;
const int BK_EXIT   = 7;

fn char* block_kind_name(int k)
{
    switch (k)
    {
        case BK_ENTRY:  return "entry";
        case BK_NORMAL: return "block";
        case BK_THEN:   return "then";
        case BK_ELSE:   return "else";
        case BK_JOIN:   return "join";
        case BK_LOOP:   return "loop";
        case BK_BODY:   return "body";
        case BK_EXIT:   return "exit";
        default:        return "?";
    }
}

struct BlockInfo
{
    int    id;
    int    kind;
    Node*  origin;              // AST node this block came from
    int[LV_MAX_SUCC] succ;
    usz    succ_count;
    int[LV_MAX_SUCC] pred;
    usz    pred_count;

    BitSet gen;       // used before defined in this block ("upward exposed")
    BitSet kill;      // defined in this block
    BitSet live_in;
    BitSet live_out;

    bool   terminates;   // ends in return / ub! / trap
    bool   reachable;
}

struct Cfg
{
    BlockInfo[LV_MAX_BLOCKS] blocks;
    usz  count;
    bool overflow;
    int  current;
    int  loop_header;    // innermost enclosing loop, -1 if none
    int  loop_exit;
}

fn void Cfg.init(Cfg* c)
{
    c.count = 0;
    c.overflow = false;
    c.current = -1;
    c.loop_header = -1;
    c.loop_exit = -1;
}

fn int Cfg.new_block(Cfg* c, int kind, Node* origin)
{
    if (c.count >= LV_MAX_BLOCKS) { c.overflow = true; return -1; }
    usz i = c.count;
    c.count = c.count + 1;
    BlockInfo* b = &c.blocks[i];
    b.id = (int)i;
    b.kind = kind;
    b.origin = origin;
    b.succ_count = 0;
    b.pred_count = 0;
    bs_clear(&b.gen);
    bs_clear(&b.kill);
    bs_clear(&b.live_in);
    bs_clear(&b.live_out);
    b.terminates = false;
    b.reachable = false;
    return (int)i;
}

fn void Cfg.add_edge(Cfg* c, int from, int to)
{
    if (from < 0 || to < 0) { return; }
    if ((usz)from >= c.count || (usz)to >= c.count) { return; }
    BlockInfo* f = &c.blocks[from];
    BlockInfo* t = &c.blocks[to];
    // Deduplicate: `if c then x else x` would otherwise add the same edge
    // twice and inflate the predecessor count, which changes nothing
    // semantically but makes the CFG dump misleading.
    for (usz i = 0; i < f.succ_count; i++) { if (f.succ[i] == to) { return; } }
    if (f.succ_count < LV_MAX_SUCC)
    {
        f.succ[f.succ_count] = to;
        f.succ_count = f.succ_count + 1;
    }
    if (t.pred_count < LV_MAX_SUCC)
    {
        t.pred[t.pred_count] = from;
        t.pred_count = t.pred_count + 1;
    }
}

// ════════════════════════════════════════════════════════════════════════════
// LIVENESS
// ════════════════════════════════════════════════════════════════════════════

struct LivenessAnalysis
{
    Cfg*          cfg;
    VarNumbering* vars;

    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;

    // statistics
    usz functions;
    usz blocks_built;
    usz edges;
    usz iterations;
    usz non_local_vars;
    usz local_vars;
    usz dead_defs;
    usz phi_sites;         // semi-pruned phi placements
    usz phi_saved;         // phis a MINIMAL placement would have inserted
    usz addr_taken;
    bool overflowed;
    bool verbose;
}

fn bool LivenessAnalysis.init(LivenessAnalysis* la, pfront_core::DiagBag* d,
                              pfront_core::Interner* it, char* file)
{
    la.diags = d;
    la.interner = it;
    la.file = file;
    la.functions = 0;
    la.blocks_built = 0;
    la.edges = 0;
    la.iterations = 0;
    la.non_local_vars = 0;
    la.local_vars = 0;
    la.dead_defs = 0;
    la.phi_sites = 0;
    la.phi_saved = 0;
    la.addr_taken = 0;
    la.overflowed = false;
    la.verbose = false;

    // Both are far over the 64 KB stack-object limit.
    la.cfg = (Cfg*)malloc(Cfg::size);
    la.vars = (VarNumbering*)malloc(VarNumbering::size);
    if (la.cfg == null || la.vars == null) { la.destroy(); return false; }
    return true;
}

fn void LivenessAnalysis.destroy(LivenessAnalysis* la)
{
    if (la.cfg != null)  { free((void*)la.cfg);  la.cfg = null; }
    if (la.vars != null) { free((void*)la.vars); la.vars = null; }
}

// ── Recording uses and defs ─────────────────────────────────────────────────
// GEN is "used before any definition in this block". So a use is only added
// to GEN if the variable is not already in KILL.

fn void LivenessAnalysis.record_use(LivenessAnalysis* la, int blk, Node* binder)
{
    if (blk < 0 || binder == null) { return; }
    int v = la.vars.intern(binder, binder.name_id);
    if (v < 0) { la.overflowed = true; return; }
    la.vars.items[v].uses = la.vars.items[v].uses + 1;
    BlockInfo* b = &la.cfg.blocks[blk];
    if (!bs_test(&b.kill, (usz)v)) { bs_set(&b.gen, (usz)v); }
}

fn void LivenessAnalysis.record_def(LivenessAnalysis* la, int blk, Node* binder)
{
    if (blk < 0 || binder == null) { return; }
    int v = la.vars.intern(binder, binder.name_id);
    if (v < 0) { la.overflowed = true; return; }
    la.vars.items[v].defs = la.vars.items[v].defs + 1;
    BlockInfo* b = &la.cfg.blocks[blk];
    bs_set(&b.kill, (usz)v);
}

fn void LivenessAnalysis.record_addr(LivenessAnalysis* la, int blk, Node* binder)
{
    if (binder == null) { return; }
    int v = la.vars.intern(binder, binder.name_id);
    if (v < 0) { return; }
    la.vars.items[v].addr_taken = true;
    // A variable whose address escapes may be read or written through the
    // pointer at any point, so treat it as both used and defined here.
    la.record_use(blk, binder);
    la.record_def(blk, binder);
}

// Walk an EXPRESSION recording uses. Assignment is handled by the caller,
// because the left side of an assignment is a def, not a use.
fn void LivenessAnalysis.scan_expr(LivenessAnalysis* la, int blk, Node* e, int depth)
{
    if (e == null || depth > LV_MAX_DEPTH || blk < 0) { return; }

    if (e.kind == Nk.N_EXPR_IDENT)
    {
        if (e.resolved != null) { la.record_use(blk, e.resolved); }
        return;
    }

    if (e.kind == Nk.N_EXPR_REF)
    {
        Node* t = e.child(0);
        if (t != null && t.kind == Nk.N_EXPR_IDENT && t.resolved != null)
        {
            la.record_addr(blk, t.resolved);
            return;
        }
    }

    for (usz i = 0; i < e.child_count; i++)
    {
        la.scan_expr(blk, e.children[i], depth + 1);
    }
}

// ── CFG construction ────────────────────────────────────────────────────────
// Returns the block that control reaches AFTER `n`, or -1 if control does not
// continue (a return terminates the path).

fn int LivenessAnalysis.build_stmt(LivenessAnalysis* la, int blk, Node* n, int depth)
{
    if (n == null || depth > LV_MAX_DEPTH) { return blk; }
    if (blk < 0) { return blk; }   // unreachable: nothing to record

    switch (n.kind)
    {
        case N_BLOCK:
        {
            int cur = blk;
            for (usz i = 0; i < n.child_count; i++)
            {
                cur = la.build_stmt(cur, n.children[i], depth + 1);
                if (cur < 0) { break; }   // rest of the block is unreachable
            }
            return cur;
        }

        case N_DECL_LET:
        {
            // The initializer is evaluated BEFORE the binding exists, so its
            // uses are recorded first. Getting this order wrong makes
            // `let x = x` look like a self-reference rather than a use of an
            // outer `x`.
            Node* binder = n.child(0);
            if (n.child_count > 1) { la.scan_expr(blk, n.child(1), depth + 1); }
            if (binder != null && binder.kind == Nk.N_PAT_IDENT)
            {
                la.record_def(blk, binder);
            }
            else
            {
                // Destructuring: every N_PAT_IDENT inside is a def.
                la.record_pattern_defs(blk, binder, depth + 1);
            }
            return blk;
        }

        case N_STMT_ASSIGN:
        case N_EXPR_ASSIGN:
        {
            Node* lhs = n.child(0);
            Node* rhs = n.child(1);
            la.scan_expr(blk, rhs, depth + 1);
            if (lhs != null && lhs.kind == Nk.N_EXPR_IDENT && lhs.resolved != null)
            {
                la.record_def(blk, lhs.resolved);
            }
            else
            {
                // `a.f = v` / `a[i] = v` READ the base to find the location.
                la.scan_expr(blk, lhs, depth + 1);
            }
            return blk;
        }

        case N_STMT_COMPOUND_ASSIGN:
        {
            Node* lhs = n.child(0);
            la.scan_expr(blk, n.child(1), depth + 1);
            if (lhs != null && lhs.kind == Nk.N_EXPR_IDENT && lhs.resolved != null)
            {
                la.record_use(blk, lhs.resolved);   // reads the old value
                la.record_def(blk, lhs.resolved);
            }
            else { la.scan_expr(blk, lhs, depth + 1); }
            return blk;
        }

        case N_EXPR_IF:
        {
            Node* cond = n.child(0);
            Node* then_b = n.child(1);
            Node* else_b = n.child(2);
            la.scan_expr(blk, cond, depth + 1);

            int tb = la.cfg.new_block(BK_THEN, then_b);
            la.cfg.add_edge(blk, tb);
            int t_end = la.build_stmt(tb, then_b, depth + 1);

            int e_end = blk;
            if (else_b != null)
            {
                int eb = la.cfg.new_block(BK_ELSE, else_b);
                la.cfg.add_edge(blk, eb);
                e_end = la.build_stmt(eb, else_b, depth + 1);
            }

            // Both arms terminating means nothing follows the `if`.
            if (t_end < 0 && e_end < 0) { return -1; }

            int join = la.cfg.new_block(BK_JOIN, n);
            if (t_end >= 0) { la.cfg.add_edge(t_end, join); }
            if (e_end >= 0) { la.cfg.add_edge(e_end, join); }
            if (else_b == null) { la.cfg.add_edge(blk, join); }
            return join;
        }

        case N_EXPR_WHILE:
        {
            // header --> body --> back to header
            //   \-------------------> exit
            int header = la.cfg.new_block(BK_LOOP, n);
            la.cfg.add_edge(blk, header);
            la.scan_expr(header, n.child(0), depth + 1);

            int body = la.cfg.new_block(BK_BODY, n.child(1));
            la.cfg.add_edge(header, body);

            int saved_h = la.cfg.loop_header;
            int exit_b = la.cfg.new_block(BK_JOIN, n);
            int saved_e = la.cfg.loop_exit;
            la.cfg.loop_header = header;
            la.cfg.loop_exit = exit_b;

            int b_end = la.build_stmt(body, n.child(1), depth + 1);
            // THE BACK EDGE. This is what makes liveness iterative: a value
            // defined late in the body and used early is live across it.
            if (b_end >= 0) { la.cfg.add_edge(b_end, header); }

            la.cfg.loop_header = saved_h;
            la.cfg.loop_exit = saved_e;
            la.cfg.add_edge(header, exit_b);
            return exit_b;
        }

        case N_EXPR_FOR:
        {
            int header = la.cfg.new_block(BK_LOOP, n);
            la.cfg.add_edge(blk, header);
            // Children: binder, iterable, body (shapes vary; scan defensively)
            for (usz i = 0; i + 1 < n.child_count; i++)
            {
                Node* c = n.children[i];
                if (c != null && pfront_core::is_pattern(c.kind))
                {
                    la.record_pattern_defs(header, c, depth + 1);
                }
                else { la.scan_expr(header, c, depth + 1); }
            }
            int body = la.cfg.new_block(BK_BODY, n);
            la.cfg.add_edge(header, body);
            int saved_h = la.cfg.loop_header;
            int exit_b = la.cfg.new_block(BK_JOIN, n);
            int saved_e = la.cfg.loop_exit;
            la.cfg.loop_header = header;
            la.cfg.loop_exit = exit_b;
            Node* body_n = n.child_count > 0 ? n.children[n.child_count - 1] : null;
            int b_end = la.build_stmt(body, body_n, depth + 1);
            if (b_end >= 0) { la.cfg.add_edge(b_end, header); }
            la.cfg.loop_header = saved_h;
            la.cfg.loop_exit = saved_e;
            la.cfg.add_edge(header, exit_b);
            return exit_b;
        }

        case N_EXPR_LOOP:
        {
            int header = la.cfg.new_block(BK_LOOP, n);
            la.cfg.add_edge(blk, header);
            int exit_b = la.cfg.new_block(BK_JOIN, n);
            int saved_h = la.cfg.loop_header;
            int saved_e = la.cfg.loop_exit;
            la.cfg.loop_header = header;
            la.cfg.loop_exit = exit_b;
            int b_end = la.build_stmt(header, n.child(0), depth + 1);
            if (b_end >= 0) { la.cfg.add_edge(b_end, header); }
            la.cfg.loop_header = saved_h;
            la.cfg.loop_exit = saved_e;
            // `loop` without a break never exits; the exit block stays
            // unreachable and liveness will show it as such.
            return exit_b;
        }

        case N_EXPR_MATCH:
        {
            Node* scrut = n.child(0);
            la.scan_expr(blk, scrut, depth + 1);
            int join = la.cfg.new_block(BK_JOIN, n);
            bool any_reaches = false;
            for (usz i = 1; i < n.child_count; i++)
            {
                Node* arm = n.children[i];
                if (arm == null) { continue; }
                int ab = la.cfg.new_block(BK_THEN, arm);
                la.cfg.add_edge(blk, ab);
                // An arm's pattern BINDS; its guard and body USE.
                for (usz j = 0; j < arm.child_count; j++)
                {
                    Node* c = arm.children[j];
                    if (c != null && pfront_core::is_pattern(c.kind))
                    {
                        la.record_pattern_defs(ab, c, depth + 1);
                    }
                }
                Node* body = arm.child_count > 0
                           ? arm.children[arm.child_count - 1] : null;
                int a_end = la.build_stmt(ab, body, depth + 1);
                if (a_end >= 0) { la.cfg.add_edge(a_end, join); any_reaches = true; }
            }
            if (!any_reaches && n.child_count > 1) { return -1; }
            return join;
        }

        case N_STMT_RETURN:
        {
            la.scan_expr(blk, n.child(0), depth + 1);
            la.cfg.blocks[blk].terminates = true;
            return -1;
        }

        case N_EXPR_UB:
        case N_EXPR_UNREACHABLE:
        case N_EXPR_TRAP:
        {
            la.cfg.blocks[blk].terminates = true;
            return -1;
        }

        case N_STMT_BREAK:
        {
            if (la.cfg.loop_exit >= 0) { la.cfg.add_edge(blk, la.cfg.loop_exit); }
            return -1;
        }

        case N_STMT_CONTINUE:
        {
            if (la.cfg.loop_header >= 0) { la.cfg.add_edge(blk, la.cfg.loop_header); }
            return -1;
        }

        case N_STMT_EXPR:
            return la.build_stmt(blk, n.child(0), depth + 1);

        default:
        {
            if (pfront_core::is_expr(n.kind))
            {
                la.scan_expr(blk, n, depth + 1);
                return blk;
            }
            int cur = blk;
            for (usz i = 0; i < n.child_count; i++)
            {
                cur = la.build_stmt(cur, n.children[i], depth + 1);
                if (cur < 0) { break; }
            }
            return cur;
        }
    }
}

fn void LivenessAnalysis.record_pattern_defs(LivenessAnalysis* la, int blk,
                                             Node* pat, int depth)
{
    if (pat == null || depth > LV_MAX_DEPTH || blk < 0) { return; }
    if (pat.kind == Nk.N_PAT_IDENT) { la.record_def(blk, pat); return; }
    for (usz i = 0; i < pat.child_count; i++)
    {
        la.record_pattern_defs(blk, pat.children[i], depth + 1);
    }
}

// ── Backward dataflow ───────────────────────────────────────────────────────
//   live_out[b] = ⋃ live_in[s] for s ∈ succ(b)
//   live_in[b]  = gen[b] ∪ (live_out[b] \ kill[b])
//
// Iterated to a fixpoint. Visiting blocks in REVERSE creation order
// approximates reverse-postorder, which converges in far fewer passes than
// forward order for a backward problem.
fn void LivenessAnalysis.solve(LivenessAnalysis* la)
{
    Cfg* c = la.cfg;
    for (int iter = 0; iter < LV_MAX_ITERS; iter++)
    {
        bool changed = false;
        la.iterations = la.iterations + 1;

        usz i = c.count;
        while (i > 0)
        {
            i = i - 1;
            BlockInfo* b = &c.blocks[i];

            BitSet out;
            bs_clear(&out);
            for (usz s = 0; s < b.succ_count; s++)
            {
                int si = b.succ[s];
                if (si < 0 || (usz)si >= c.count) { continue; }
                bs_union(&out, &c.blocks[si].live_in);
            }
            if (bs_union(&b.live_out, &out)) { changed = true; }
            if (bs_transfer(&b.live_in, &b.live_out, &b.kill, &b.gen))
            {
                changed = true;
            }
        }
        if (!changed) { break; }
    }
}

// ── Reachability ────────────────────────────────────────────────────────────
fn void LivenessAnalysis.mark_reachable(LivenessAnalysis* la)
{
    Cfg* c = la.cfg;
    if (c.count == 0) { return; }
    // Iterative flood rather than recursion: a deeply nested function would
    // otherwise risk the stack, and this is O(V+E) either way.
    c.blocks[0].reachable = true;
    bool changed = true;
    int guard = 0;
    while (changed && guard < LV_MAX_ITERS)
    {
        changed = false;
        guard = guard + 1;
        for (usz i = 0; i < c.count; i++)
        {
            if (!c.blocks[i].reachable) { continue; }
            for (usz s = 0; s < c.blocks[i].succ_count; s++)
            {
                int si = c.blocks[i].succ[s];
                if (si < 0 || (usz)si >= c.count) { continue; }
                if (!c.blocks[si].reachable)
                {
                    c.blocks[si].reachable = true;
                    changed = true;
                }
            }
        }
    }
}

// ── Semi-pruned classification ──────────────────────────────────────────────
// A variable is NON-LOCAL if it is live on entry to any block — equivalently,
// if it is live across at least one control-flow edge. Only non-local
// variables can need a φ, which is the whole point of semi-pruned placement.
//
// A variable used and killed entirely inside one block is LOCAL: no φ, and
// the back end can keep it in a register without ever materialising a merge.
fn void LivenessAnalysis.classify(LivenessAnalysis* la)
{
    Cfg* c = la.cfg;
    VarNumbering* vn = la.vars;

    BitSet non_local;
    bs_clear(&non_local);

    for (usz i = 0; i < c.count; i++)
    {
        BlockInfo* b = &c.blocks[i];
        if (!b.reachable) { continue; }
        // Live-IN of a block with more than one predecessor is exactly the
        // set that would need a φ at that join.
        if (b.pred_count > 1)
        {
            for (usz v = 0; v < vn.count; v++)
            {
                if (bs_test(&b.live_in, v))
                {
                    bs_set(&non_local, v);
                    la.phi_sites = la.phi_sites + 1;
                }
            }
            // What MINIMAL placement would have cost: a φ for every variable
            // defined anywhere, at every join, regardless of liveness.
            la.phi_saved = la.phi_saved + vn.count;
        }
        // Live-out across any edge also makes a variable non-local.
        if (b.succ_count > 0)
        {
            for (usz v = 0; v < vn.count; v++)
            {
                if (bs_test(&b.live_out, v)) { bs_set(&non_local, v); }
            }
        }
    }

    for (usz v = 0; v < vn.count; v++)
    {
        bool nl = bs_test(&non_local, v) || vn.items[v].addr_taken;
        vn.items[v].non_local = nl;
        if (nl) { la.non_local_vars = la.non_local_vars + 1; }
        else    { la.local_vars = la.local_vars + 1; }
        if (vn.items[v].addr_taken) { la.addr_taken = la.addr_taken + 1; }
    }

    if (la.phi_saved >= la.phi_sites)
    {
        la.phi_saved = la.phi_saved - la.phi_sites;
    }
    else { la.phi_saved = 0; }
}

// ── Dead definition detection ───────────────────────────────────────────────
// A definition is DEAD if the variable is not live-out of its block and has
// no later use inside the block. Semi-pruned liveness gives this for free:
// a LOCAL variable that is never in any gen set was defined and never read.
fn void LivenessAnalysis.find_dead_defs(LivenessAnalysis* la)
{
    VarNumbering* vn = la.vars;
    for (usz v = 0; v < vn.count; v++)
    {
        VarEntry* e = &vn.items[v];
        if (e.uses == 0 && e.defs > 0 && !e.addr_taken)
        {
            la.dead_defs = la.dead_defs + 1;
        }
    }
}

// Is this binder safe to treat as SSA-local (no φ needed)? The optimizer and
// the future SSI builder both consult this.
fn bool LivenessAnalysis.is_local(LivenessAnalysis* la, Node* binder)
{
    int v = la.vars.find(binder);
    if (v < 0) { return false; }
    return !la.vars.items[v].non_local;
}

fn bool LivenessAnalysis.needs_phi(LivenessAnalysis* la, Node* binder)
{
    int v = la.vars.find(binder);
    if (v < 0) { return false; }
    return la.vars.items[v].non_local;
}

// ── Per-function driver ─────────────────────────────────────────────────────
fn void LivenessAnalysis.run_function(LivenessAnalysis* la, Node* fn_decl)
{
    if (fn_decl == null) { return; }
    la.functions = la.functions + 1;

    la.cfg.init();
    la.vars.init();

    int entry = la.cfg.new_block(BK_ENTRY, fn_decl);
    if (entry < 0) { return; }

    // Parameters and clause patterns are definitions on entry.
    for (usz i = 0; i < fn_decl.child_count; i++)
    {
        Node* c = fn_decl.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.N_DECL_PARAM)
        {
            la.record_pattern_defs(entry, c, 0);
            if (c.kind == Nk.N_PAT_IDENT) { la.record_def(entry, c); }
        }
    }

    int cur = entry;
    for (usz i = 0; i < fn_decl.child_count; i++)
    {
        Node* c = fn_decl.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.N_CLAUSE)
        {
            // Each clause is an alternative entry path: pattern binds, body
            // runs. They do not fall through to one another.
            int cb = la.cfg.new_block(BK_NORMAL, c);
            la.cfg.add_edge(entry, cb);
            for (usz j = 0; j < c.child_count; j++)
            {
                Node* cc = c.children[j];
                if (cc != null && pfront_core::is_pattern(cc.kind))
                {
                    la.record_pattern_defs(cb, cc, 0);
                }
            }
            Node* body = c.child_count > 0 ? c.children[c.child_count - 1] : null;
            la.build_stmt(cb, body, 0);
        }
        else if (c.kind == Nk.N_BLOCK)
        {
            cur = la.build_stmt(cur, c, 0);
        }
    }

    la.blocks_built = la.blocks_built + la.cfg.count;
    for (usz i = 0; i < la.cfg.count; i++)
    {
        la.edges = la.edges + la.cfg.blocks[i].succ_count;
    }

    la.mark_reachable();
    la.solve();
    la.classify();
    la.find_dead_defs();

    if (la.cfg.overflow || la.vars.overflow) { la.overflowed = true; }
}

fn void LivenessAnalysis.run(LivenessAnalysis* la, Node* root)
{
    if (root == null) { return; }
    la.walk(root, 0);
}

fn void LivenessAnalysis.walk(LivenessAnalysis* la, Node* n, int depth)
{
    if (n == null || depth > LV_MAX_DEPTH) { return; }
    if (n.kind == Nk.N_DECL_FN)
    {
        la.run_function(n);
        return;   // one CFG per function; do not descend into nested fns twice
    }
    for (usz i = 0; i < n.child_count; i++) { la.walk(n.children[i], depth + 1); }
}

fn void LivenessAnalysis.dump_cfg(LivenessAnalysis* la)
{
    Cfg* c = la.cfg;
    printf("=== CFG (last function, %d blocks) ===\n", (int)c.count);
    for (usz i = 0; i < c.count; i++)
    {
        BlockInfo* b = &c.blocks[i];
        printf("  b%-3d %-6s", b.id, block_kind_name(b.kind));
        if (!b.reachable) { printf(" UNREACHABLE"); }
        if (b.terminates) { printf(" TERM"); }
        printf("  succ=[");
        for (usz s = 0; s < b.succ_count; s++)
        {
            if (s > 0) { printf(","); }
            printf("b%d", b.succ[s]);
        }
        printf("]  live_in=%d live_out=%d\n",
               (int)bs_count(&b.live_in), (int)bs_count(&b.live_out));
    }
}

fn void LivenessAnalysis.report(LivenessAnalysis* la)
{
    printf("  liveness         : %d fns, %d blocks, %d edges, %d iters\n",
           (int)la.functions, (int)la.blocks_built,
           (int)la.edges, (int)la.iterations);
    printf("  semi-pruned      : %d non-local (need phi), %d block-local\n",
           (int)la.non_local_vars, (int)la.local_vars);
    if (la.phi_sites > 0 || la.phi_saved > 0)
    {
        printf("  phi placement    : %d semi-pruned sites, %d avoided vs minimal\n",
               (int)la.phi_sites, (int)la.phi_saved);
    }
    if (la.dead_defs > 0)
    {
        printf("  dead defs        : %d never-read definitions\n", (int)la.dead_defs);
    }
    if (la.addr_taken > 0)
    {
        printf("  address-taken    : %d (conservatively non-local)\n", (int)la.addr_taken);
    }
    if (la.overflowed)
    {
        printf("  WARNING          : analysis capacity exceeded; results partial\n");
    }
}
