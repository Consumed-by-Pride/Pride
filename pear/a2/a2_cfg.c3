/*
 a2 — control-flow infrastructure shared by every analysis in this stage.

 a1 already has a dominance routine in verify.c3, and this is deliberately
 NOT that one. verify.c3 computes a dense dominator BITSET, which answers
 "does a dominate b" in O(1) and is exactly right for a verifier that asks
 that question a few thousand times. It cannot answer the two questions a2
 needs constantly:

   idom(b)              the immediate dominator — the parent in the
                        dominator TREE. MemorySSA's renaming walk is a
                        pre-order traversal of that tree, and a bitset does
                        not have a tree in it.
   DF(b)                the dominance frontier — where a φ has to go.
                        Cytron's placement algorithm is defined on the
                        frontier and nothing else computes it.

 So this file computes the tree form (Cooper–Harvey–Kennedy, iterating over
 reverse postorder) and derives the frontier from it. Both are also
 computed on the REVERSE graph, giving post-dominators and the
 post-dominance frontier, which is what aggressive DCE needs to decide
 whether a branch is itself dead: a branch is only live if some live
 operation is control-dependent on it, and control dependence IS the
 reverse-graph dominance frontier.

 Every structure here is per-function and freed by the caller. Block ids
 are module-global, so a local dense index 0..n-1 is built first: the
 alternative, indexing arrays by global block id, would allocate
 module-block-count words for every function and turn a 250-function module
 into a quadratic allocation.
*/

module pear_a2_cfg;

import pear_air;
import pfront_core;

alias Air  = pear_air::AirModule;
alias Blk  = pear_air::AirBlock;
alias Fn   = pear_air::AirFunc;
alias Val  = pear_air::AirValue;
alias Op   = pear_air::AirOp;
alias Term = pear_air::AirTerm;

extern fn int   printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn void* realloc(void* p, usz size);
extern fn void  free(void* p);

const int NO_IDX = -1;

// ════════════════════════════════════════════════════════════════════════
// A GROWABLE LIST OF INTS
// ════════════════════════════════════════════════════════════════════════

/*
 Used for dominance-frontier sets and for worklists. D6 applies: this grows
 rather than truncating, and a failed growth sets `failed` so a caller can
 report incompleteness instead of silently analysing a truncated set.
*/
struct IntList
{
    int* v;
    usz  count;
    usz  cap;
    bool failed;
}

fn void IntList.init(IntList* l) { l.v = null; l.count = 0; l.cap = 0; l.failed = false; }

fn void IntList.destroy(IntList* l)
{
    if (l.v != null) { free((void*)l.v); l.v = null; }
    l.count = 0; l.cap = 0;
}

fn void IntList.clear(IntList* l) { l.count = 0; }

fn void IntList.push(IntList* l, int x)
{
    if (l.count + 1 > l.cap)
    {
        usz nc = l.cap == 0 ? 8 : l.cap * 2;
        int* p = (int*)realloc((void*)l.v, nc * int::size);
        if (p == null) { l.failed = true; return; }
        l.v = p;
        l.cap = nc;
    }
    l.v[l.count] = x;
    l.count = l.count + 1;
}

// Push only if not already present. Frontier sets are small (typically 0-2
// entries), so a linear scan beats a hash set here by a wide margin.
fn void IntList.push_unique(IntList* l, int x)
{
    for (usz i = 0; i < l.count; i++) { if (l.v[i] == x) { return; } }
    l.push(x);
}

fn bool IntList.contains(IntList* l, int x)
{
    for (usz i = 0; i < l.count; i++) { if (l.v[i] == x) { return true; } }
    return false;
}

fn int IntList.pop(IntList* l)
{
    if (l.count == 0) { return NO_IDX; }
    l.count = l.count - 1;
    return l.v[l.count];
}

// ════════════════════════════════════════════════════════════════════════
// THE PER-FUNCTION CONTROL-FLOW GRAPH
// ════════════════════════════════════════════════════════════════════════

/*
 `n` local blocks, numbered 0..n-1 in the order AirFunc.blocks lists them.

 Two dominator trees are held, forward and reverse. The reverse one needs a
 virtual exit that every divergent or returning block points to, otherwise a
 function with two `ret`s has no unique sink and post-dominance is
 undefined. That virtual node is index `n`, which is why every reverse
 array is sized n+1.
*/
struct Cfg
{
    Air*  m;
    Fn*   f;
    usz   n;

    uint* id_of;      // local index -> global block id
    int*  idx_of;     // global block id -> local index (NO_IDX if elsewhere)
    usz   idx_cap;    // length of idx_of; == m.block_count

    int*  rpo;        // rpo[i] = local index, i in 0..rpo_count-1
    int*  rpo_num;    // local index -> its position in rpo, NO_IDX if unreachable
    usz   rpo_count;

    int*  idom;       // local index -> local index; entry's idom is itself
    IntList* df;      // dominance frontier, one list per local index

    // Reverse graph. Index n is the virtual exit.
    int*  post_rpo;
    int*  post_rpo_num;
    usz   post_rpo_count;
    int*  ipdom;      // post-dominator tree parent; virtual exit is its own
    IntList* pdf;     // post-dominance frontier == control dependence

    bool  ok;
}

fn bool Cfg.reachable(Cfg* c, int b)
{
    if (b < 0 || (usz)b >= c.n) { return false; }
    return c.rpo_num[b] != NO_IDX;
}

// ── succ/pred access in LOCAL index space ───────────────────────────────

/*
 A successor may legitimately be a block of another function only if the
 IR is malformed; `idx_of` returns NO_IDX in that case and every caller
 skips it. Filtering here rather than at each use site means a cross-
 function edge cannot silently corrupt a dominator computation — it is
 dropped, and verify.c3 is the thing that complains about it.
*/
fn usz Cfg.succ_count(Cfg* c, int b)
{
    Blk* bb = c.m.blk(c.id_of[b]);
    return bb == null ? 0 : bb.succ_count;
}

fn int Cfg.succ(Cfg* c, int b, usz i)
{
    Blk* bb = c.m.blk(c.id_of[b]);
    if (bb == null || i >= bb.succ_count) { return NO_IDX; }
    uint g = bb.succ[i];
    if ((usz)g >= c.idx_cap) { return NO_IDX; }
    return c.idx_of[g];
}

fn usz Cfg.pred_count(Cfg* c, int b)
{
    Blk* bb = c.m.blk(c.id_of[b]);
    return bb == null ? 0 : bb.pred_count;
}

fn int Cfg.pred(Cfg* c, int b, usz i)
{
    Blk* bb = c.m.blk(c.id_of[b]);
    if (bb == null || i >= bb.pred_count) { return NO_IDX; }
    uint g = bb.pred[i];
    if ((usz)g >= c.idx_cap) { return NO_IDX; }
    return c.idx_of[g];
}

// ── construction ────────────────────────────────────────────────────────

fn bool Cfg.init(Cfg* c, Air* m, Fn* f)
{
    c.m = m;
    c.f = f;
    c.n = f.block_count;
    c.ok = false;
    c.id_of = null; c.idx_of = null;
    c.rpo = null; c.rpo_num = null; c.idom = null; c.df = null;
    c.post_rpo = null; c.post_rpo_num = null; c.ipdom = null; c.pdf = null;
    c.rpo_count = 0; c.post_rpo_count = 0;
    if (c.n == 0) { c.ok = true; return true; }

    c.idx_cap = m.block_count;
    c.id_of  = (uint*)malloc(c.n * uint::size);
    c.idx_of = (int*)malloc(c.idx_cap * int::size);
    if (c.id_of == null || c.idx_of == null) { return false; }
    for (usz i = 0; i < c.idx_cap; i++) { c.idx_of[i] = NO_IDX; }
    for (usz i = 0; i < c.n; i++)
    {
        c.id_of[i] = f.blocks[i];
        if ((usz)f.blocks[i] < c.idx_cap) { c.idx_of[f.blocks[i]] = (int)i; }
    }

    usz np = c.n + 1;
    c.rpo          = (int*)malloc(c.n * int::size);
    c.rpo_num      = (int*)malloc(c.n * int::size);
    c.idom         = (int*)malloc(c.n * int::size);
    c.post_rpo     = (int*)malloc(np * int::size);
    c.post_rpo_num = (int*)malloc(np * int::size);
    c.ipdom        = (int*)malloc(np * int::size);
    if (c.rpo == null || c.rpo_num == null || c.idom == null) { return false; }
    if (c.post_rpo == null || c.post_rpo_num == null || c.ipdom == null) { return false; }

    c.df  = (IntList*)malloc(c.n * IntList::size);
    c.pdf = (IntList*)malloc(np * IntList::size);
    if (c.df == null || c.pdf == null) { return false; }
    for (usz i = 0; i < c.n; i++) { c.df[i].init(); }
    for (usz i = 0; i < np; i++) { c.pdf[i].init(); }

    c.build_rpo();
    c.build_idom();
    c.build_df();
    c.build_post_rpo();
    c.build_ipdom();
    c.build_pdf();
    c.ok = true;
    return true;
}

fn void Cfg.destroy(Cfg* c)
{
    if (c.df != null)
    {
        for (usz i = 0; i < c.n; i++) { c.df[i].destroy(); }
        free((void*)c.df); c.df = null;
    }
    if (c.pdf != null)
    {
        for (usz i = 0; i < c.n + 1; i++) { c.pdf[i].destroy(); }
        free((void*)c.pdf); c.pdf = null;
    }
    if (c.id_of != null)        { free((void*)c.id_of); c.id_of = null; }
    if (c.idx_of != null)       { free((void*)c.idx_of); c.idx_of = null; }
    if (c.rpo != null)          { free((void*)c.rpo); c.rpo = null; }
    if (c.rpo_num != null)      { free((void*)c.rpo_num); c.rpo_num = null; }
    if (c.idom != null)         { free((void*)c.idom); c.idom = null; }
    if (c.post_rpo != null)     { free((void*)c.post_rpo); c.post_rpo = null; }
    if (c.post_rpo_num != null) { free((void*)c.post_rpo_num); c.post_rpo_num = null; }
    if (c.ipdom != null)        { free((void*)c.ipdom); c.ipdom = null; }
}

/*
 Reverse postorder by explicit-stack DFS.

 The stack is explicit rather than recursive for the reason stated in
 verify.c3: C3 caps a stack object at 64 KB and a long chain of blocks in a
 generated `match` chain is not hypothetical — stdlib modules reach several
 hundred blocks in one function.

 The two-phase entry (`state`) is the standard trick for emitting postorder
 from an iterative DFS: a node is pushed once to expand and once to emit.
*/
fn void Cfg.build_rpo(Cfg* c)
{
    for (usz i = 0; i < c.n; i++) { c.rpo_num[i] = NO_IDX; }
    c.rpo_count = 0;

    int entry = NO_IDX;
    if ((usz)c.f.entry < c.idx_cap) { entry = c.idx_of[c.f.entry]; }
    if (entry == NO_IDX) { return; }

    bool* seen = (bool*)malloc(c.n);
    int*  stack = (int*)malloc(2 * c.n * int::size);
    bool* state = (bool*)malloc(2 * c.n);          // false = expand, true = emit
    int*  post  = (int*)malloc(c.n * int::size);
    if (seen == null || stack == null || state == null || post == null)
    {
        if (seen != null) { free((void*)seen); }
        if (stack != null) { free((void*)stack); }
        if (state != null) { free((void*)state); }
        if (post != null) { free((void*)post); }
        return;
    }
    for (usz i = 0; i < c.n; i++) { seen[i] = false; }

    usz sp = 0;
    usz pc = 0;
    stack[sp] = entry; state[sp] = false; sp = sp + 1;

    while (sp > 0)
    {
        sp = sp - 1;
        int b = stack[sp];
        bool emit = state[sp];

        if (emit)
        {
            post[pc] = b; pc = pc + 1;
            continue;
        }
        if (seen[b]) { continue; }
        seen[b] = true;

        // Re-push to emit after all descendants have been emitted.
        if (sp + 1 <= 2 * c.n) { stack[sp] = b; state[sp] = true; sp = sp + 1; }

        usz sc = c.succ_count(b);
        for (usz i = 0; i < sc; i++)
        {
            int s = c.succ(b, i);
            if (s == NO_IDX || seen[s]) { continue; }
            if (sp + 1 <= 2 * c.n) { stack[sp] = s; state[sp] = false; sp = sp + 1; }
        }
    }

    // Reverse the postorder.
    for (usz i = 0; i < pc; i++)
    {
        int b = post[pc - 1 - i];
        c.rpo[i] = b;
        c.rpo_num[b] = (int)i;
    }
    c.rpo_count = pc;

    free((void*)seen); free((void*)stack); free((void*)state); free((void*)post);
}

/*
 Intersect two nodes in the partially-built dominator tree by walking both
 up until they meet, always advancing whichever is further from the root.
 `rpo_num` is the depth proxy: a dominator always has a strictly smaller
 reverse-postorder number than the node it dominates.
*/
fn int Cfg.dom_intersect(Cfg* c, int a, int b)
{
    usz guard = 0;
    while (a != b && guard < 4 * c.n + 16)
    {
        guard = guard + 1;
        while (a != b && c.rpo_num[a] > c.rpo_num[b])
        {
            if (c.idom[a] == NO_IDX || c.idom[a] == a) { break; }
            a = c.idom[a];
        }
        while (a != b && c.rpo_num[b] > c.rpo_num[a])
        {
            if (c.idom[b] == NO_IDX || c.idom[b] == b) { break; }
            b = c.idom[b];
        }
        if (c.rpo_num[a] == c.rpo_num[b] && a != b) { break; }   // disjoint: no common dominator
    }
    return a == b ? a : NO_IDX;
}

fn void Cfg.build_idom(Cfg* c)
{
    for (usz i = 0; i < c.n; i++) { c.idom[i] = NO_IDX; }
    if (c.rpo_count == 0) { return; }

    int entry = c.rpo[0];
    c.idom[entry] = entry;

    bool changed = true;
    usz  guard = 0;
    while (changed && guard < c.n + 8)
    {
        changed = false;
        guard = guard + 1;
        for (usz i = 1; i < c.rpo_count; i++)
        {
            int b = c.rpo[i];
            int new_idom = NO_IDX;
            usz pc = c.pred_count(b);
            for (usz pi = 0; pi < pc; pi++)
            {
                int p = c.pred(b, pi);
                if (p == NO_IDX || c.rpo_num[p] == NO_IDX) { continue; }
                if (c.idom[p] == NO_IDX) { continue; }        // not processed yet
                if (new_idom == NO_IDX) { new_idom = p; }
                else
                {
                    int j = c.dom_intersect(p, new_idom);
                    if (j != NO_IDX) { new_idom = j; }
                }
            }
            if (new_idom != NO_IDX && c.idom[b] != new_idom)
            {
                c.idom[b] = new_idom;
                changed = true;
            }
        }
    }
}

/*
 Cytron's dominance frontier: for every join, walk each predecessor up the
 dominator tree until the join's immediate dominator is reached, adding the
 join to every node passed. Linear in the size of the frontier.
*/
fn void Cfg.build_df(Cfg* c)
{
    for (usz i = 0; i < c.n; i++) { c.df[i].clear(); }
    for (usz bi = 0; bi < c.n; bi++)
    {
        int b = (int)bi;
        if (c.rpo_num[b] == NO_IDX) { continue; }
        usz pc = c.pred_count(b);
        if (pc < 2) { continue; }
        int target = c.idom[b];
        for (usz pi = 0; pi < pc; pi++)
        {
            int runner = c.pred(b, pi);
            if (runner == NO_IDX || c.rpo_num[runner] == NO_IDX) { continue; }
            usz guard = 0;
            while (runner != target && runner != NO_IDX && guard < c.n + 4)
            {
                guard = guard + 1;
                c.df[runner].push_unique(b);
                if (c.idom[runner] == runner) { break; }
                runner = c.idom[runner];
            }
        }
    }
}

/*
 Does `a` dominate `b`? Walks the tree; the tree is shallow in practice and
 this avoids carrying a second O(n²) bitset alongside it.
*/
fn bool Cfg.dominates(Cfg* c, int a, int b)
{
    if (a == b) { return true; }
    if (a < 0 || b < 0) { return false; }
    if (c.rpo_num[b] == NO_IDX) { return false; }
    int x = b;
    usz guard = 0;
    while (guard < c.n + 4)
    {
        guard = guard + 1;
        if (x == a) { return true; }
        if (c.idom[x] == NO_IDX || c.idom[x] == x) { return false; }
        x = c.idom[x];
    }
    return false;
}

// ── the reverse graph: post-dominance and control dependence ────────────

/*
 Postorder of the REVERSE graph, rooted at the virtual exit (index n).

 Every block whose terminator has no successors — ret, trap, unreachable,
 ub — is a predecessor of the virtual exit. An infinite loop with no exit
 has no path to it at all and stays unreachable in this traversal, which is
 the correct answer: nothing after it is control-dependent on anything.
*/
fn void Cfg.build_post_rpo(Cfg* c)
{
    usz np = c.n + 1;
    for (usz i = 0; i < np; i++) { c.post_rpo_num[i] = NO_IDX; }
    c.post_rpo_count = 0;
    int vexit = (int)c.n;

    bool* seen  = (bool*)malloc(np);
    int*  stack = (int*)malloc(2 * np * int::size);
    bool* state = (bool*)malloc(2 * np);
    int*  post  = (int*)malloc(np * int::size);
    if (seen == null || stack == null || state == null || post == null)
    {
        if (seen != null) { free((void*)seen); }
        if (stack != null) { free((void*)stack); }
        if (state != null) { free((void*)state); }
        if (post != null) { free((void*)post); }
        return;
    }
    for (usz i = 0; i < np; i++) { seen[i] = false; }

    usz sp = 0;
    usz pc = 0;
    stack[sp] = vexit; state[sp] = false; sp = sp + 1;

    while (sp > 0)
    {
        sp = sp - 1;
        int b = stack[sp];
        bool emit = state[sp];
        if (emit) { post[pc] = b; pc = pc + 1; continue; }
        if (seen[b]) { continue; }
        seen[b] = true;
        if (sp + 1 <= 2 * np) { stack[sp] = b; state[sp] = true; sp = sp + 1; }

        // Reverse-graph successors of b are the Cfg predecessors of b,
        // except for the virtual exit whose reverse-successors are the
        // real exit blocks.
        if (b == vexit)
        {
            for (usz i = 0; i < c.n; i++)
            {
                if (c.succ_count((int)i) != 0) { continue; }
                if (seen[i]) { continue; }
                if (sp + 1 <= 2 * np) { stack[sp] = (int)i; state[sp] = false; sp = sp + 1; }
            }
        }
        else
        {
            usz prc = c.pred_count(b);
            for (usz i = 0; i < prc; i++)
            {
                int p = c.pred(b, i);
                if (p == NO_IDX || seen[p]) { continue; }
                if (sp + 1 <= 2 * np) { stack[sp] = p; state[sp] = false; sp = sp + 1; }
            }
        }
    }

    for (usz i = 0; i < pc; i++)
    {
        int b = post[pc - 1 - i];
        c.post_rpo[i] = b;
        c.post_rpo_num[b] = (int)i;
    }
    c.post_rpo_count = pc;

    free((void*)seen); free((void*)stack); free((void*)state); free((void*)post);
}

fn int Cfg.pdom_intersect(Cfg* c, int a, int b)
{
    usz guard = 0;
    while (a != b && guard < 4 * c.n + 16)
    {
        guard = guard + 1;
        while (a != b && c.post_rpo_num[a] > c.post_rpo_num[b])
        {
            if (c.ipdom[a] == NO_IDX || c.ipdom[a] == a) { break; }
            a = c.ipdom[a];
        }
        while (a != b && c.post_rpo_num[b] > c.post_rpo_num[a])
        {
            if (c.ipdom[b] == NO_IDX || c.ipdom[b] == b) { break; }
            b = c.ipdom[b];
        }
        if (c.post_rpo_num[a] == c.post_rpo_num[b] && a != b) { break; }
    }
    return a == b ? a : NO_IDX;
}

fn void Cfg.build_ipdom(Cfg* c)
{
    usz np = c.n + 1;
    for (usz i = 0; i < np; i++) { c.ipdom[i] = NO_IDX; }
    if (c.post_rpo_count == 0) { return; }
    int vexit = (int)c.n;
    c.ipdom[vexit] = vexit;

    bool changed = true;
    usz  guard = 0;
    while (changed && guard < np + 8)
    {
        changed = false;
        guard = guard + 1;
        for (usz i = 1; i < c.post_rpo_count; i++)
        {
            int b = c.post_rpo[i];
            if (b == vexit) { continue; }
            int new_ipdom = NO_IDX;
            // Reverse-graph predecessors of b are its Cfg successors; a
            // block with no successors has the virtual exit instead.
            usz sc = c.succ_count(b);
            if (sc == 0)
            {
                new_ipdom = vexit;
            }
            else
            {
                for (usz si = 0; si < sc; si++)
                {
                    int s = c.succ(b, si);
                    if (s == NO_IDX || c.post_rpo_num[s] == NO_IDX) { continue; }
                    if (c.ipdom[s] == NO_IDX) { continue; }
                    if (new_ipdom == NO_IDX) { new_ipdom = s; }
                    else
                    {
                        int j = c.pdom_intersect(s, new_ipdom);
                        if (j != NO_IDX) { new_ipdom = j; }
                    }
                }
            }
            if (new_ipdom != NO_IDX && c.ipdom[b] != new_ipdom)
            {
                c.ipdom[b] = new_ipdom;
                changed = true;
            }
        }
    }
}

/*
 Post-dominance frontier == control dependence.

 `b` is in PDF(x) exactly when x has a successor from which b is reachable
 without passing through x's post-dominator — i.e. when the branch at x
 decides whether b executes. Aggressive DCE keeps a branch alive precisely
 when some live block is control-dependent on it, so this is the structure
 that stops DCE from deleting a branch whose arms matter.
*/
fn void Cfg.build_pdf(Cfg* c)
{
    usz np = c.n + 1;
    for (usz i = 0; i < np; i++) { c.pdf[i].clear(); }
    int vexit = (int)c.n;

    for (usz bi = 0; bi < c.n; bi++)
    {
        int b = (int)bi;
        if (c.post_rpo_num[b] == NO_IDX) { continue; }
        usz sc = c.succ_count(b);
        if (sc < 2) { continue; }          // only a real branch splits control
        int target = c.ipdom[b];
        for (usz si = 0; si < sc; si++)
        {
            int runner = c.succ(b, si);
            if (runner == NO_IDX || c.post_rpo_num[runner] == NO_IDX) { continue; }
            usz guard = 0;
            while (runner != target && runner != NO_IDX && runner != vexit && guard < np + 4)
            {
                guard = guard + 1;
                c.pdf[runner].push_unique(b);
                if (c.ipdom[runner] == runner) { break; }
                runner = c.ipdom[runner];
            }
        }
    }
}

// ── iterated dominance frontier: where φ nodes go ───────────────────────

/*
 IDF(S) — the fixpoint of DF over a set of definition blocks. This is the
 exact set of blocks needing a φ for a variable defined in S (Cytron et
 al.), and MemorySSA uses it to place MemoryPhi.

 `in_s` and `out` are caller-provided arrays of length c.n. Returning
 through caller storage keeps this allocation-free in the inner loop, which
 matters because memssa calls it once per aliasing partition.
*/
fn void Cfg.idf(Cfg* c, bool* in_s, bool* out)
{
    for (usz i = 0; i < c.n; i++) { out[i] = false; }

    IntList work;
    work.init();
    for (usz i = 0; i < c.n; i++) { if (in_s[i]) { work.push((int)i); } }

    while (work.count > 0)
    {
        int b = work.pop();
        if (b == NO_IDX) { break; }
        for (usz i = 0; i < c.df[b].count; i++)
        {
            int y = c.df[b].v[i];
            if (out[y]) { continue; }
            out[y] = true;
            work.push(y);          // iterate: a new φ is itself a definition
        }
    }
    work.destroy();
}

/*
 Children of `b` in the dominator tree, appended to `out`.

 Recomputed on demand rather than cached: MemorySSA's renaming walk visits
 each node once, so building a child-list structure would cost the same
 allocation for a single use.
*/
fn void Cfg.dom_children(Cfg* c, int b, IntList* out)
{
    out.clear();
    for (usz i = 0; i < c.n; i++)
    {
        if ((int)i == b) { continue; }
        if (c.rpo_num[i] == NO_IDX) { continue; }
        if (c.idom[i] == b) { out.push((int)i); }
    }
}
