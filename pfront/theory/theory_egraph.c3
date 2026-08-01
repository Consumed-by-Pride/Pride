// ============================================================================
// theory_egraph.c3 — E-graphs and equality saturation (part 20)
// ----------------------------------------------------------------------------
// The term rewriter in `theory_trs` is *destructive*: applying `a + 0 ↦ a`
// throws away `a + 0`. That makes rewriting order-dependent, and it means a
// rule sequence that would have found a better normal form via a temporarily
// worse term can never find it. This is the classic phase-ordering problem.
//
// An E-GRAPH solves it by keeping every equivalent form simultaneously.
//
//   * An E-CLASS is a set of terms known to be equal.
//   * An E-NODE is one term shape whose children are e-class ids, not terms.
//   * The graph maintains CONGRUENCE: if x ≡ y then f(x) ≡ f(y), maintained
//     incrementally by rebuilding after each merge.
//
// EQUALITY SATURATION then runs every rule everywhere, repeatedly, adding
// equalities rather than replacing terms, until nothing new can be derived (or
// a bound is hit). Afterwards an EXTRACTION pass picks the cheapest
// representative from each class. Because no information was destroyed, the
// result is independent of rule order — which is exactly what the destructive
// rewriter cannot promise.
//
// Worked example. With rules
//     x * 2 ↦ x << 1        x * 1 ↦ x        (a * b) / b ↦ a
// the term `(a * 2) / 2` reaches `a` only if `x * 2 ↦ x << 1` is NOT applied
// first. A destructive rewriter that shifts early is stuck with `(a << 1) / 2`.
// Saturation records both forms, the division rule still matches the `a * 2`
// representative, and extraction picks `a`.
//
// Implementation notes:
//   * Union-find with path compression AND union-by-rank for the class merge.
//   * A hashcons from e-node shape to class id gives congruence in O(1)
//     amortised per lookup.
//   * A worklist of "dirty" classes bounds rebuilding to what actually moved.
//   * Extraction is a fixpoint over a cost function; AST size is the default,
//     but the cost model is a parameter so a backend can supply its own.
// ============================================================================

module theory_egraph;

import pfront_lex;
import pfront_core;
import theory_term;
import theory_trs;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;
alias Subst = theory_term::Subst;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz EG_MAX_NODES    = 65536;
const usz EG_MAX_CLASSES  = 32768;
const usz EG_HASH         = 65536;
const usz EG_MAX_CHILDREN = 8;
const usz EG_CLASS_NODES  = 32;
const int EG_MAX_ITERS    = 30;
const int EG_MAX_DEPTH    = 256;

// ── E-nodes ─────────────────────────────────────────────────────────────────
// A term shape whose children are CLASS ids. Two e-nodes with the same
// operator and the same child classes are congruent, hence in the same class.
struct ENode
{
    Nk    kind;
    int   op;              // operator token for binary/unary
    ulong ival;            // literal payload
    uint  name_id;
    int[EG_MAX_CHILDREN] children;
    usz   child_count;
    int   klass;           // owning class (canonical at rebuild time)
    Node* origin;          // an AST node this shape came from, for extraction
    int   next_in_bucket;
}

fn ulong enode_hash(ENode* n)
{
    ulong h = 0xcbf29ce484222325UL;
    h = (h ^ (ulong)(int)n.kind) * 0x100000001b3UL;
    h = (h ^ (ulong)n.op) * 0x100000001b3UL;
    h = (h ^ n.ival) * 0x100000001b3UL;
    h = (h ^ (ulong)n.name_id) * 0x100000001b3UL;
    for (usz i = 0; i < n.child_count; i++)
    {
        h = (h ^ (ulong)n.children[i]) * 0x100000001b3UL;
    }
    return h;
}

fn bool enode_eq(ENode* a, ENode* b)
{
    if (a.kind != b.kind) { return false; }
    if (a.op != b.op) { return false; }
    if (a.ival != b.ival) { return false; }
    if (a.name_id != b.name_id) { return false; }
    if (a.child_count != b.child_count) { return false; }
    for (usz i = 0; i < a.child_count; i++)
    {
        if (a.children[i] != b.children[i]) { return false; }
    }
    return true;
}

// ── E-classes ───────────────────────────────────────────────────────────────
struct EClass
{
    int[EG_CLASS_NODES] nodes;    // e-node indices in this class
    usz                 node_count;
    int[EG_CLASS_NODES] parents;  // e-nodes that reference this class
    usz                 parent_count;
    int                 leader;   // union-find parent
    int                 rank;     // union-by-rank
    usz                 cost;     // best extraction cost
    int                 best_node;
    bool                dirty;
}

struct EGraph
{
    ENode[EG_MAX_NODES]     nodes;
    usz                     node_count;
    EClass[EG_MAX_CLASSES]  classes;
    usz                     class_count;

    int[EG_HASH]            buckets;

    int[EG_MAX_CLASSES]     worklist;
    usz                     worklist_len;

    Arena*                  arena;
    pfront_core::DiagBag*   diags;
    char*                   file;

    usz merges;
    usz rebuilds;
    usz congruence_merges;
    usz hashcons_hits;
    usz saturation_iters;
    bool saturated;
    usz nodes_added;
}

fn void EGraph.init(EGraph* g, Arena* a, pfront_core::DiagBag* d, char* file)
{
    g.node_count = 0;
    g.class_count = 0;
    g.worklist_len = 0;
    for (usz i = 0; i < EG_HASH; i++) { g.buckets[i] = -1; }
    g.arena = a;
    g.diags = d;
    g.file = file;
    g.merges = 0;
    g.rebuilds = 0;
    g.congruence_merges = 0;
    g.hashcons_hits = 0;
    g.saturation_iters = 0;
    g.saturated = false;
    g.nodes_added = 0;
}

// ── Union-find over classes ─────────────────────────────────────────────────
fn int EGraph.find(EGraph* g, int c)
{
    if (c < 0 || (usz)c >= g.class_count) { return c; }
    int root = c;
    int guard = 0;
    while (g.classes[root].leader != root && guard < 4096)
    {
        root = g.classes[root].leader;
        guard = guard + 1;
    }
    // Path compression.
    int cur = c;
    while (g.classes[cur].leader != root)
    {
        int nxt = g.classes[cur].leader;
        g.classes[cur].leader = root;
        cur = nxt;
    }
    return root;
}

fn int EGraph.new_class(EGraph* g)
{
    if (g.class_count >= EG_MAX_CLASSES) { return -1; }
    int id = (int)g.class_count;
    g.class_count = g.class_count + 1;
    EClass* c = &g.classes[id];
    c.node_count = 0;
    c.parent_count = 0;
    c.leader = id;
    c.rank = 0;
    c.cost = 0xFFFFFFFF;
    c.best_node = -1;
    c.dirty = false;
    return id;
}

fn void EGraph.push_worklist(EGraph* g, int c)
{
    int r = g.find(c);
    if (r < 0) { return; }
    if (g.classes[r].dirty) { return; }
    g.classes[r].dirty = true;
    if (g.worklist_len < EG_MAX_CLASSES)
    {
        g.worklist[g.worklist_len] = r;
        g.worklist_len = g.worklist_len + 1;
    }
}

// ── Hashcons lookup ─────────────────────────────────────────────────────────
// Canonicalise a node's children, then look it up. A hit means the shape is
// already present, which is how congruence is discovered.
fn void EGraph.canonicalise(EGraph* g, ENode* n)
{
    for (usz i = 0; i < n.child_count; i++)
    {
        n.children[i] = g.find(n.children[i]);
    }
}

fn int EGraph.lookup(EGraph* g, ENode* probe)
{
    g.canonicalise(probe);
    ulong h = enode_hash(probe);
    usz b = (usz)(h & (ulong)(EG_HASH - 1));
    int cur = g.buckets[b];
    while (cur >= 0)
    {
        if (enode_eq(&g.nodes[cur], probe))
        {
            g.hashcons_hits = g.hashcons_hits + 1;
            return g.find(g.nodes[cur].klass);
        }
        cur = g.nodes[cur].next_in_bucket;
    }
    return -1;
}

// Add an e-node, returning its class. If congruent to an existing node the
// existing class is returned instead of creating a duplicate.
fn int EGraph.add_node(EGraph* g, ENode* probe)
{
    int existing = g.lookup(probe);
    if (existing >= 0) { return existing; }

    if (g.node_count >= EG_MAX_NODES) { return -1; }
    int nid = (int)g.node_count;
    g.node_count = g.node_count + 1;
    g.nodes_added = g.nodes_added + 1;

    int cid = g.new_class();
    if (cid < 0) { return -1; }

    ENode* n = &g.nodes[nid];
    *n = *probe;
    n.klass = cid;

    ulong h = enode_hash(n);
    usz b = (usz)(h & (ulong)(EG_HASH - 1));
    n.next_in_bucket = g.buckets[b];
    g.buckets[b] = nid;

    EClass* c = &g.classes[cid];
    c.nodes[0] = nid;
    c.node_count = 1;

    // Record this node as a parent of each child class, so a later merge of a
    // child knows which parents must be re-canonicalised.
    for (usz i = 0; i < n.child_count; i++)
    {
        int ch = g.find(n.children[i]);
        if (ch < 0 || (usz)ch >= g.class_count) { continue; }
        EClass* cc = &g.classes[ch];
        if (cc.parent_count < EG_CLASS_NODES)
        {
            cc.parents[cc.parent_count] = nid;
            cc.parent_count = cc.parent_count + 1;
        }
    }
    return cid;
}

// Insert an AST subtree, returning its class.
fn int EGraph.add_term(EGraph* g, Node* t, int depth)
{
    if (t == null || depth > EG_MAX_DEPTH) { return -1; }
    ENode probe;
    probe.kind = t.kind;
    probe.op = t.p.op;
    probe.ival = t.p.ival;
    probe.name_id = t.name_id;
    probe.child_count = 0;
    probe.origin = t;
    probe.next_in_bucket = -1;
    probe.klass = -1;
    for (usz i = 0; i < t.child_count && probe.child_count < EG_MAX_CHILDREN; i++)
    {
        int ch = g.add_term(t.children[i], depth + 1);
        if (ch < 0) { continue; }
        probe.children[probe.child_count] = ch;
        probe.child_count = probe.child_count + 1;
    }
    return g.add_node(&probe);
}

// ── Merge ───────────────────────────────────────────────────────────────────
// Assert that two classes are equal. The heavy lifting (restoring congruence)
// is deferred to `rebuild`, which is what keeps merge O(α(n)).
fn bool EGraph.merge(EGraph* g, int a, int b)
{
    int ra = g.find(a);
    int rb = g.find(b);
    if (ra < 0 || rb < 0) { return false; }
    if (ra == rb) { return false; }
    g.merges = g.merges + 1;

    // Union by rank keeps the tree shallow.
    if (g.classes[ra].rank < g.classes[rb].rank)
    {
        int t = ra; ra = rb; rb = t;
    }
    else if (g.classes[ra].rank == g.classes[rb].rank)
    {
        g.classes[ra].rank = g.classes[ra].rank + 1;
    }

    g.classes[rb].leader = ra;

    EClass* dst = &g.classes[ra];
    EClass* src = &g.classes[rb];
    for (usz i = 0; i < src.node_count && dst.node_count < EG_CLASS_NODES; i++)
    {
        dst.nodes[dst.node_count] = src.nodes[i];
        dst.node_count = dst.node_count + 1;
    }
    for (usz i = 0; i < src.parent_count && dst.parent_count < EG_CLASS_NODES; i++)
    {
        dst.parents[dst.parent_count] = src.parents[i];
        dst.parent_count = dst.parent_count + 1;
    }
    src.node_count = 0;
    src.parent_count = 0;

    g.push_worklist(ra);
    return true;
}

// Restore congruence: after merges, parents whose children changed class may
// have become congruent to each other.
fn void EGraph.rebuild(EGraph* g)
{
    int guard = 0;
    while (g.worklist_len > 0 && guard < 4096)
    {
        guard = guard + 1;
        g.rebuilds = g.rebuilds + 1;

        // Take a snapshot: repair may push more work.
        usz n = g.worklist_len;
        g.worklist_len = 0;

        for (usz i = 0; i < n; i++)
        {
            int c = g.find(g.worklist[i]);
            if (c < 0 || (usz)c >= g.class_count) { continue; }
            g.classes[c].dirty = false;
            g.repair(c);
        }
    }
}

fn void EGraph.repair(EGraph* g, int c)
{
    EClass* cls = &g.classes[c];
    // Re-canonicalise every parent and re-insert it into the hashcons. Two
    // parents that now canonicalise identically are congruent and must merge.
    for (usz i = 0; i < cls.parent_count; i++)
    {
        int pn = cls.parents[i];
        if (pn < 0 || (usz)pn >= g.node_count) { continue; }
        ENode* p = &g.nodes[pn];
        g.canonicalise(p);
        int existing = g.lookup(p);
        int own = g.find(p.klass);
        if (existing >= 0 && existing != own)
        {
            if (g.merge(existing, own)) { g.congruence_merges = g.congruence_merges + 1; }
        }
    }
}

// ── E-matching ──────────────────────────────────────────────────────────────
// Match a rewrite-rule pattern against every class. Unlike term matching this
// must consider EVERY representative of a class, since any of them may match.
struct EMatch
{
    int   klass;
    Subst subst;
}

const usz EG_MAX_MATCHES = 4096;

struct MatchSet
{
    EMatch[EG_MAX_MATCHES] items;
    usz                    count;
    usz                    attempts;
}

fn void MatchSet.clear(MatchSet* m) { m.count = 0; }

fn bool EGraph.match_pattern(EGraph* g, Node* pattern, int klass,
                             Subst* s, int depth)
{
    if (pattern == null || depth > EG_MAX_DEPTH) { return false; }
    int c = g.find(klass);
    if (c < 0) { return false; }

    // A pattern variable binds the whole class. The bound term is the class's
    // current best representative, chosen at extraction time.
    if (theory_term::is_pattern_var(pattern))
    {
        if (pattern.kind == Nk.N_PAT_WILDCARD) { return true; }
        // Bind to a synthetic marker carrying the class id, so non-linear
        // patterns compare CLASSES rather than syntactic terms — which is the
        // whole point of matching in an e-graph.
        Node* rep = g.representative(c);
        if (rep == null) { return false; }
        return s.bind(pattern.name_id, rep);
    }

    // Otherwise some e-node in the class must match structurally.
    EClass* cls = &g.classes[c];
    for (usz i = 0; i < cls.node_count; i++)
    {
        int nid = cls.nodes[i];
        if (nid < 0 || (usz)nid >= g.node_count) { continue; }
        ENode* n = &g.nodes[nid];
        if (n.kind != pattern.kind) { continue; }
        if (n.op != pattern.p.op) { continue; }
        if (pattern.kind == Nk.N_EXPR_INT && n.ival != pattern.p.ival) { continue; }
        if (pattern.kind == Nk.N_EXPR_IDENT && n.name_id != pattern.name_id) { continue; }
        if (n.child_count != pattern.child_count) { continue; }

        usz mark = s.mark();
        bool ok = true;
        for (usz k = 0; k < n.child_count && ok; k++)
        {
            ok = g.match_pattern(pattern.children[k], n.children[k], s, depth + 1);
        }
        if (ok) { return true; }
        s.reset(mark);
    }
    return false;
}

fn Node* EGraph.representative(EGraph* g, int klass)
{
    int c = g.find(klass);
    if (c < 0 || (usz)c >= g.class_count) { return null; }
    EClass* cls = &g.classes[c];
    if (cls.best_node >= 0 && (usz)cls.best_node < g.node_count)
    {
        return g.nodes[cls.best_node].origin;
    }
    if (cls.node_count == 0) { return null; }
    return g.nodes[cls.nodes[0]].origin;
}

// Search every class for matches of `pattern`.
fn usz EGraph.search(EGraph* g, Node* pattern, MatchSet* out)
{
    out.clear();
    for (usz c = 0; c < g.class_count; c++)
    {
        if (g.find((int)c) != (int)c) { continue; }   // not a leader
        if (out.count >= EG_MAX_MATCHES) { break; }
        Subst s;
        s.clear();
        out.attempts = out.attempts + 1;
        if (g.match_pattern(pattern, (int)c, &s, 0))
        {
            out.items[out.count].klass = (int)c;
            out.items[out.count].subst = s;
            out.count = out.count + 1;
        }
    }
    return out.count;
}

// ── Equality saturation ─────────────────────────────────────────────────────
// Run every rule everywhere until no new equality is derived. Rules ADD
// equalities; nothing is ever removed, so the outcome does not depend on the
// order rules are tried in.
fn bool EGraph.saturate(EGraph* g, theory_trs::RuleSet* rules, int max_iters)
{
    MatchSet* ms = (MatchSet*)malloc(MatchSet::size);
    if (ms == null) { return false; }

    for (int iter = 0; iter < max_iters && iter < EG_MAX_ITERS; iter++)
    {
        g.saturation_iters = g.saturation_iters + 1;
        usz merges_before = g.merges;

        for (usz r = 0; r < rules.count; r++)
        {
            theory_trs::Rule* rule = &rules.rules[r];
            if (rule.lhs == null || rule.rhs == null) { continue; }

            g.search(rule.lhs, ms);
            for (usz m = 0; m < ms.count; m++)
            {
                // Instantiate the right-hand side under this match, insert it,
                // and assert it equal to the matched class.
                Node* rhs = ms.items[m].subst.instantiate(g.arena, rule.rhs, 0);
                if (rhs == null) { continue; }
                int rc = g.add_term(rhs, 0);
                if (rc < 0) { continue; }
                g.merge(ms.items[m].klass, rc);
            }
        }

        g.rebuild();

        // A fixpoint: no new equality this round means saturation.
        if (g.merges == merges_before)
        {
            g.saturated = true;
            free((void*)ms);
            return true;
        }
        if (g.node_count >= EG_MAX_NODES - 64) { break; }
    }
    free((void*)ms);
    g.saturated = false;
    return false;
}

// ── Extraction ──────────────────────────────────────────────────────────────
// Pick the cheapest representative of each class. Cost is computed to a
// fixpoint because a class's cost depends on its children's, which may be in
// classes not yet costed.
fn usz node_base_cost(ENode* n)
{
    switch (n.kind)
    {
        case N_EXPR_INT:
        case N_EXPR_BOOL:
        case N_EXPR_CHAR:
        case N_EXPR_IDENT:
            return 1;
        case N_EXPR_CALL:
            return 20;      // calls are expensive: prefer inlined arithmetic
        case N_EXPR_BINARY:
        {
            Tk op = (Tk)n.op;
            // A shift is cheaper than a multiply on every target that matters.
            if (op == Tk.TOKEN_LSHIFT || op == Tk.TOKEN_RSHIFT) { return 2; }
            if (op == Tk.TOKEN_STAR) { return 5; }
            if (op == Tk.TOKEN_SLASH || op == Tk.TOKEN_PERCENT) { return 12; }
            return 3;
        }
        case N_EXPR_UNARY:
            return 2;
        default:
            return 4;
    }
}

fn void EGraph.compute_costs(EGraph* g)
{
    for (usz i = 0; i < g.class_count; i++)
    {
        g.classes[i].cost = 0xFFFFFFFF;
        g.classes[i].best_node = -1;
    }

    bool changed = true;
    int rounds = 0;
    while (changed && rounds < 64)
    {
        changed = false;
        rounds = rounds + 1;
        for (usz ni = 0; ni < g.node_count; ni++)
        {
            ENode* n = &g.nodes[ni];
            int c = g.find(n.klass);
            if (c < 0 || (usz)c >= g.class_count) { continue; }

            usz total = node_base_cost(n);
            bool costed = true;
            for (usz k = 0; k < n.child_count; k++)
            {
                int ch = g.find(n.children[k]);
                if (ch < 0 || (usz)ch >= g.class_count) { costed = false; break; }
                usz cc = g.classes[ch].cost;
                if (cc == 0xFFFFFFFF) { costed = false; break; }
                total = total + cc;
            }
            if (!costed) { continue; }
            if (total < g.classes[c].cost)
            {
                g.classes[c].cost = total;
                g.classes[c].best_node = (int)ni;
                changed = true;
            }
        }
    }
}

// Rebuild an AST from the cheapest node of each class.
fn Node* EGraph.extract(EGraph* g, int klass, int depth)
{
    if (depth > EG_MAX_DEPTH) { return null; }
    int c = g.find(klass);
    if (c < 0 || (usz)c >= g.class_count) { return null; }
    EClass* cls = &g.classes[c];
    int best = cls.best_node;
    if (best < 0 || (usz)best >= g.node_count) { return g.representative(c); }

    ENode* n = &g.nodes[best];
    Node* origin = n.origin;
    if (origin == null) { return null; }

    // Leaf: the original node already is the answer.
    if (n.child_count == 0) { return origin; }

    Node* out = g.arena.node(origin.kind, origin.line, origin.col);
    if (out == null) { return origin; }
    out.name_id = origin.name_id;
    out.flags = origin.flags | pfront_core::NF_SYNTHETIC;
    out.p = origin.p;
    out.type_ann = origin.type_ann;
    out.resolved = origin.resolved;
    out.owner = origin.owner;
    for (usz i = 0; i < n.child_count; i++)
    {
        Node* ch = g.extract(n.children[i], depth + 1);
        g.arena.add_child(out, ch);
    }
    return out;
}

fn void EGraph.report(EGraph* g)
{
    usz leaders = 0;
    for (usz i = 0; i < g.class_count; i++)
    {
        if (g.find((int)i) == (int)i) { leaders = leaders + 1; }
    }
    printf("  e-graph          : %d e-nodes, %d classes (%d live)\n",
           (int)g.node_count, (int)g.class_count, (int)leaders);
    printf("  e-graph merges   : %d total (%d by congruence), %d rebuilds\n",
           (int)g.merges, (int)g.congruence_merges, (int)g.rebuilds);
    printf("  saturation       : %d iterations, %s\n",
           (int)g.saturation_iters,
           g.saturated ? "reached fixpoint" : "hit the iteration bound");
    printf("  hashcons         : %d congruence hits\n", (int)g.hashcons_hits);
}

// ── Driver: optimise a term via saturation ──────────────────────────────────
// The whole point: insert, saturate, cost, extract. Order-independent by
// construction, unlike the destructive rewriter.
struct Saturator
{
    EGraph*                eg;
    theory_trs::RuleSet*   rules;
    Arena*                 arena;
    pfront_core::DiagBag*  diags;
    char*                  file;

    usz terms_optimised;
    usz cost_before;
    usz cost_after;
    usz improved;
    bool enabled;
}

fn bool Saturator.init(Saturator* s, Arena* a, theory_trs::RuleSet* rules,
                       pfront_core::DiagBag* d, char* file)
{
    s.eg = (EGraph*)malloc(EGraph::size);
    if (s.eg == null) { return false; }
    s.eg.init(a, d, file);
    s.rules = rules;
    s.arena = a;
    s.diags = d;
    s.file = file;
    s.terms_optimised = 0;
    s.cost_before = 0;
    s.cost_after = 0;
    s.improved = 0;
    s.enabled = true;
    return true;
}

fn void Saturator.destroy(Saturator* s)
{
    if (s.eg != null) { free((void*)s.eg); s.eg = null; }
}

fn Node* Saturator.optimise(Saturator* s, Node* term)
{
    if (!s.enabled || term == null || s.rules.count == 0) { return term; }
    s.terms_optimised = s.terms_optimised + 1;

    int root = s.eg.add_term(term, 0);
    if (root < 0) { return term; }

    s.eg.compute_costs();
    int rc = s.eg.find(root);
    usz before = rc >= 0 ? s.eg.classes[rc].cost : 0;
    s.cost_before = s.cost_before + before;

    s.eg.saturate(s.rules, EG_MAX_ITERS);
    s.eg.compute_costs();

    rc = s.eg.find(root);
    usz after = rc >= 0 ? s.eg.classes[rc].cost : before;
    s.cost_after = s.cost_after + after;
    if (after < before) { s.improved = s.improved + 1; }

    Node* out = s.eg.extract(root, 0);
    return out == null ? term : out;
}

fn void Saturator.report(Saturator* s)
{
    if (s.terms_optimised == 0) { return; }
    printf("  saturation opt   : %d terms, cost %d -> %d (%d improved)\n",
           (int)s.terms_optimised, (int)s.cost_before,
           (int)s.cost_after, (int)s.improved);
    s.eg.report();
}
