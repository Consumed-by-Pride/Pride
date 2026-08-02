// ============================================================================
// theory_term.c3 — shared term substrate for the theory layer (part 11)
// ----------------------------------------------------------------------------
// Every theory component in this folder — the term-rewriting system, the
// multi-stage quotation engine, the pattern-generation compiler, the IRDL
// dialect lowerer — manipulates *terms*: structural fragments of the AST
// treated as first-class data rather than as program text.
//
// They all need the same four services, so those live here exactly once:
//
//   1. STRUCTURAL HASHING     — a stable hash over an AST subtree, ignoring
//      source position but respecting operator, literal value and child order.
//   2. STRUCTURAL EQUALITY    — the companion predicate. Hash agreement is a
//      filter, never a proof; every bucket hit is confirmed with a real
//      structural comparison.
//   3. HASH-CONSING           — interning terms so structurally identical
//      subtrees share one canonical node. This turns term equality into a
//      pointer compare, which the rewriter's non-linear patterns depend on.
//   4. SUBSTITUTION           — capture-avoiding replacement of pattern
//      variables by matched subtrees, with a depth guard so a self-referential
//      binding can never loop.
//
// A note on why hash-consing matters beyond speed: the term rewriter must
// decide whether two occurrences of a pattern variable matched the *same*
// term. Without interning that is a deep comparison at every match attempt;
// with it, it is `a == b`.
// ============================================================================

module theory_term;

import pfront_lex;
import pfront_core;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz HC_BUCKETS   = 65536;
const usz HC_MAX_NODES = 262144;
const int TERM_MAX_DEPTH = 400;

// ── Structural hashing ──────────────────────────────────────────────────────
// FNV-1a over (kind, operator, literal payload, child hashes). Source location
// is deliberately excluded: two occurrences of `x + 1` on different lines are
// the same term.
fn ulong term_hash(Node* n, int depth)
{
    if (n == null) { return 0xcbf29ce484222325UL; }
    if (depth > TERM_MAX_DEPTH) { return 0x9e3779b97f4a7c15UL; }

    ulong h = 0xcbf29ce484222325UL;
    h = (h ^ (ulong)(int)n.kind) * 0x100000001b3UL;
    h = (h ^ (ulong)n.p.op) * 0x100000001b3UL;
    h = (h ^ (ulong)n.name_id) * 0x100000001b3UL;

    switch (n.kind)
    {
        case N_EXPR_INT:
        case N_EXPR_CHAR:
        case N_EXPR_BOOL:
            h = (h ^ n.p.ival) * 0x100000001b3UL;
        case N_EXPR_FLOAT:
            h = (h ^ f64_bits(n.p.fval)) * 0x100000001b3UL;
        case N_EXPR_STRING:
        case N_EXPR_BYTES:
        {
            for (usz i = 0; i < n.p.slen; i++)
            {
                h = (h ^ (ulong)(char)n.p.sptr[i]) * 0x100000001b3UL;
            }
        }
        default:
            break;
    }

    h = (h ^ (ulong)n.child_count) * 0x100000001b3UL;
    for (usz i = 0; i < n.child_count; i++)
    {
        h = (h ^ term_hash(n.children[i], depth + 1)) * 0x100000001b3UL;
    }
    if (n.type_ann != null)
    {
        h = (h ^ (term_hash(n.type_ann, depth + 1) | 1UL)) * 0x100000001b3UL;
    }
    return h;
}

// Reinterpret a double's bits as an integer without a bitcast intrinsic.
fn ulong f64_bits(double v)
{
    ulong out = 0;
    char* src = (char*)&v;
    char* dst = (char*)&out;
    for (usz i = 0; i < 8; i++) { dst[i] = src[i]; }
    return out;
}

// ── Structural equality ─────────────────────────────────────────────────────
fn bool term_eq(Node* a, Node* b, int depth)
{
    if (a == b) { return true; }
    if (a == null || b == null) { return false; }
    if (depth > TERM_MAX_DEPTH) { return false; }
    if (a.kind != b.kind) { return false; }
    if (a.p.op != b.p.op) { return false; }
    if (a.name_id != b.name_id) { return false; }
    if (a.child_count != b.child_count) { return false; }

    switch (a.kind)
    {
        case N_EXPR_INT:
        case N_EXPR_CHAR:
        case N_EXPR_BOOL:
            if (a.p.ival != b.p.ival) { return false; }
        case N_EXPR_FLOAT:
            if (f64_bits(a.p.fval) != f64_bits(b.p.fval)) { return false; }
        case N_EXPR_STRING:
        case N_EXPR_BYTES:
        {
            if (a.p.slen != b.p.slen) { return false; }
            for (usz i = 0; i < a.p.slen; i++)
            {
                if (a.p.sptr[i] != b.p.sptr[i]) { return false; }
            }
        }
        default:
            break;
    }

    for (usz i = 0; i < a.child_count; i++)
    {
        if (!term_eq(a.children[i], b.children[i], depth + 1)) { return false; }
    }
    return true;
}

// ── Hash-consing ────────────────────────────────────────────────────────────
struct HcEntry
{
    Node*  term;
    ulong  hash;
    int    next;      // chain index, 0 = end
}

struct HashCons
{
    int[HC_BUCKETS]       buckets;
    HcEntry[HC_MAX_NODES] entries;
    usz                   count;
    usz                   hits;
    usz                   misses;
    usz                   collisions;
}

fn void HashCons.init(HashCons* hc)
{
    for (usz i = 0; i < HC_BUCKETS; i++) { hc.buckets[i] = 0; }
    hc.count = 1;      // index 0 reserved as the null chain terminator
    hc.hits = 0;
    hc.misses = 0;
    hc.collisions = 0;
}

// Return the canonical representative of `n`. Children must already be
// interned for the result to be a true canonical form, which is why callers
// intern bottom-up.
fn Node* HashCons.intern(HashCons* hc, Node* n)
{
    if (n == null) { return null; }
    ulong h = term_hash(n, 0);
    usz b = (usz)(h & (ulong)(HC_BUCKETS - 1));
    int cur = hc.buckets[b];
    while (cur != 0)
    {
        HcEntry* e = &hc.entries[cur];
        if (e.hash == h)
        {
            if (term_eq(e.term, n, 0)) { hc.hits = hc.hits + 1; return e.term; }
            hc.collisions = hc.collisions + 1;
        }
        cur = e.next;
    }
    if (hc.count >= HC_MAX_NODES) { return n; }
    int id = (int)hc.count;
    hc.count = hc.count + 1;
    hc.entries[id].term = n;
    hc.entries[id].hash = h;
    hc.entries[id].next = hc.buckets[b];
    hc.buckets[b] = id;
    hc.misses = hc.misses + 1;
    return n;
}

// Intern a whole subtree bottom-up, rewriting child pointers to canonical
// representatives as it goes.
fn Node* HashCons.intern_deep(HashCons* hc, Node* n, int depth)
{
    if (n == null || depth > TERM_MAX_DEPTH) { return n; }
    for (usz i = 0; i < n.child_count; i++)
    {
        n.set_child(i, hc.intern_deep(n.children[i], depth + 1));
    }
    return hc.intern(n);
}

fn void HashCons.report(HashCons* hc)
{
    printf("  hash-cons        : %d unique terms, %d shared, %d collisions\n",
           (int)hc.misses, (int)hc.hits, (int)hc.collisions);
}

// ── Term cloning ────────────────────────────────────────────────────────────
// Rewriting must not mutate the original AST: a rule's right-hand side is a
// TEMPLATE that gets instantiated many times. Cloning gives each instantiation
// its own nodes.
fn Node* clone_term(Arena* a, Node* n, int depth)
{
    if (n == null || depth > TERM_MAX_DEPTH) { return null; }
    Node* c = a.node(n.kind, n.line, n.col);
    if (c == null) { return null; }
    c.name_id = n.name_id;
    c.flags = n.flags;
    c.effects = n.effects;
    c.type_ann = n.type_ann;
    c.resolved = n.resolved;
    c.owner = n.owner;
    c.p = n.p;
    for (usz i = 0; i < n.child_count; i++)
    {
        a.add_child(c, clone_term(a, n.children[i], depth + 1));
    }
    return c;
}

// ── Substitution environment ────────────────────────────────────────────────
// Maps a pattern variable (identified by its interned name) to the term it
// matched. Used by the rewriter, the PGL compiler and the IRDL lowerer.
const usz SUBST_CAP = 256;

struct Binding
{
    uint   var_name;
    Node*  term;
    bool   is_sequence;   // matched a variadic tail (`...xs`)
}

struct Subst
{
    Binding[SUBST_CAP] items;
    usz                count;
    usz                lookups;
    usz                conflicts;   // non-linear var bound to differing terms
}

fn void Subst.clear(Subst* s)
{
    s.count = 0;
    s.lookups = 0;
    s.conflicts = 0;
}

fn Node* Subst.lookup(Subst* s, uint name)
{
    s.lookups = s.lookups + 1;
    for (usz i = 0; i < s.count; i++)
    {
        if (s.items[i].var_name == name) { return s.items[i].term; }
    }
    return null;
}

// Bind, enforcing NON-LINEARITY: if the variable already has a binding the
// two terms must be structurally equal, otherwise the match fails. This is
// what makes `f(x, x) ↦ g(x)` reject `f(1, 2)`.
fn bool Subst.bind(Subst* s, uint name, Node* term)
{
    for (usz i = 0; i < s.count; i++)
    {
        if (s.items[i].var_name != name) { continue; }
        Node* prev = s.items[i].term;
        if (prev == term) { return true; }             // hash-consed identity
        if (term_eq(prev, term, 0)) { return true; }   // structural fallback
        s.conflicts = s.conflicts + 1;
        return false;
    }
    if (s.count >= SUBST_CAP) { return false; }
    s.items[s.count].var_name = name;
    s.items[s.count].term = term;
    s.items[s.count].is_sequence = false;
    s.count = s.count + 1;
    return true;
}

fn usz Subst.mark(Subst* s) { return s.count; }
fn void Subst.reset(Subst* s, usz mark) { if (mark <= s.count) { s.count = mark; } }

// Instantiate a template, replacing every bound pattern variable with its
// matched term. Unbound identifiers are copied verbatim.
fn Node* Subst.instantiate(Subst* s, Arena* a, Node* tmpl, int depth)
{
    if (tmpl == null || depth > TERM_MAX_DEPTH) { return null; }

    if (tmpl.kind == Nk.N_EXPR_IDENT && tmpl.name_id != 0)
    {
        Node* bound = s.lookup(tmpl.name_id);
        // Clone rather than share: the same variable may appear twice in the
        // right-hand side, and later passes mutate nodes in place.
        if (bound != null) { return clone_term(a, bound, depth + 1); }
    }

    Node* c = a.node(tmpl.kind, tmpl.line, tmpl.col);
    if (c == null) { return null; }
    c.name_id = tmpl.name_id;
    c.flags = tmpl.flags | pfront_core::NF_SYNTHETIC;
    c.effects = tmpl.effects;
    c.type_ann = tmpl.type_ann;
    c.resolved = tmpl.resolved;
    c.owner = tmpl.owner;
    c.p = tmpl.p;
    for (usz i = 0; i < tmpl.child_count; i++)
    {
        a.add_child(c, s.instantiate(a, tmpl.children[i], depth + 1));
    }
    return c;
}

// ── Term size / depth metrics ───────────────────────────────────────────────
// Used by the rewriter's termination heuristics: a rule whose right-hand side
// is strictly smaller than its left cannot cause divergence on its own.
fn usz term_size(Node* n, int depth)
{
    if (n == null || depth > TERM_MAX_DEPTH) { return 0; }
    usz total = 1;
    for (usz i = 0; i < n.child_count; i++)
    {
        total = total + term_size(n.children[i], depth + 1);
    }
    return total;
}

fn int term_depth(Node* n, int depth)
{
    if (n == null || depth > TERM_MAX_DEPTH) { return 0; }
    int best = 0;
    for (usz i = 0; i < n.child_count; i++)
    {
        int d = term_depth(n.children[i], depth + 1);
        if (d > best) { best = d; }
    }
    return best + 1;
}

// ── Top-symbol key ──────────────────────────────────────────────────────────
// The discrimination-tree index. Two terms can only match if their top symbols
// agree, so bucketing rules by this key reduces "try every rule" to "try the
// two or three rules that could possibly apply".
const int OP_KEY_BASE = 512;

/*
 The key a decision tree switches on: two terms with DIFFERENT keys can
 never match each other, so they belong in different branches.

 Literals are keyed by their VALUE, not merely by node kind, which is the
 same reasoning the operator case already applied. `1` and `2` are both
 N_PAT_LITERAL, so returning the kind made them one constructor: the
 matrix specialiser kept every literal row in every literal branch, the
 wildcard was then reported shadowed once per branch, and
 `match n | 1 | 2 | _` claimed 2 redundant clauses. Any N literal arms
 plus a catch-all scored exactly N -- a count of reaches, not of
 redundant clauses.

 It also made the tree wrong, not just the report: switching on a key
 shared by every literal cannot discriminate between them.

 The value is folded into a distinct band so it cannot collide with a
 node kind or an operator key.
*/
/*
 Key bands.

 These must stay SMALL. theory_trs.c3 uses top_key directly as an index
 into a discrimination table of DISC_KINDS = 1024 buckets and clamps
 anything larger to the last bucket:

     if (k >= DISC_KINDS) { k = DISC_KINDS - 1; }

 So a band at 1,000,000 does not merely waste space -- it funnels every
 literal, variant and call into one shared bucket, which is exactly the
 collapse these keys exist to prevent. The rule index degrades to a
 linear scan of every call-headed rule for every call-headed term.

 The bands are therefore packed just above the node kinds and hashed
 into their range, so distinct names usually land in distinct buckets
 while the whole key space stays inside the table. A hash collision
 costs precision, never correctness: two terms sharing a bucket are
 still compared structurally by term_eq before a rule fires.
*/
const int LIT_KEY_BASE  = 600;
const int VAR_KEY_BASE  = 740;
const int CALL_KEY_BASE = 880;
const int KEY_BAND      = 140;

fn int top_key(Node* n)
{
    if (n == null) { return 0; }
    // Operators are distinguished by their token, not just by node kind: `a+b`
    // and `a*b` are both N_EXPR_BINARY but can never match each other.
    if (n.kind == Nk.N_EXPR_BINARY || n.kind == Nk.N_EXPR_UNARY)
    {
        return OP_KEY_BASE + n.p.op;
    }
    /*
     A literal pattern wraps its constant as a child; a bare literal
     expression carries it directly. Both are keyed by the value.

     Only integer-shaped literals get a value key. A float would need its
     bit pattern and a string its contents, and giving either a partial
     key is worse than giving none: two strings would collide and be
     treated as the same constructor, which is exactly the bug being
     fixed. They keep the kind key and stay conservative -- more branches
     merged than necessary, never fewer.
    */
    Node* lit = n;
    if (n.kind == Nk.N_PAT_LITERAL && n.child_count > 0) { lit = n.children[0]; }
    if (lit != null && (lit.kind == Nk.N_EXPR_INT || lit.kind == Nk.N_EXPR_CHAR
                        || lit.kind == Nk.N_EXPR_BOOL))
    {
        long v = (long)lit.p.ival;
        if (v < 0) { v = -v; }
        return LIT_KEY_BASE + (int)(v % (long)KEY_BAND);
    }
    /*
     A VARIANT is keyed by which variant it is, for exactly the reason a
     literal is keyed by its value: `Some` and `None` are both
     N_PAT_VARIANT, so returning the kind made them one constructor and
     the decision tree could not tell them apart.

     Every exhaustive two-arm variant match in the standard library was
     then reported as having a dead clause -- nine of them in
     stdlib/opt/option.pie alone, which is `match o | Some(_) | None`
     written nine times.

     name_id is the resolved variant's interned name, which is unique per
     variant and stable across the whole compilation.
    */
    if (n.kind == Nk.N_PAT_VARIANT && n.name_id != 0)
    {
        return VAR_KEY_BASE + (int)(n.name_id % (uint)KEY_BAND);
    }
    /*
     A CALL is keyed by its callee, for the third time the same reasoning
     applies: `foo(x)` and `bar(x)` are both N_EXPR_CALL, so returning the
     kind made every call one constructor and the decision tree could not
     tell two rewrite rules apart.

     This is how a rule set for a network protocol -- `emit_msg(m)` and
     `recv_msg(m)`, which can never both match the same term -- was
     reported as having a redundant rule. Rewrite rules are almost always
     headed by a call, so this affected essentially every rule set with
     more than one rule.

     Two spellings reach here. An ordinary call has the callee as child 0;
     a METHOD call (`T.op(a)`, which is what the parser builds for a
     dotted call) carries the operation in its own name_id. Both are keyed
     by that name.
    */
    if (n.kind == Nk.N_EXPR_METHOD && n.name_id != 0)
    {
        return CALL_KEY_BASE + (int)(n.name_id % (uint)KEY_BAND);
    }
    if (n.kind == Nk.N_EXPR_CALL && n.child_count > 0)
    {
        Node* callee = n.children[0];
        if (callee != null && callee.kind == Nk.N_EXPR_IDENT && callee.name_id != 0)
        {
            return CALL_KEY_BASE + (int)(callee.name_id % (uint)KEY_BAND);
        }
        /*
         An indirect call -- through a field, an index, another call --
         has no static callee name. It keeps the kind key and stays
         conservative: more terms treated as possibly-equal, never fewer.
         Inventing a key from a non-name would collide, which is the bug.
        */
    }
    return (int)n.kind;
}

// A pattern variable matches anything, so a rule headed by one cannot be
// indexed and must live in the catch-all bucket.
fn bool is_pattern_var(Node* n)
{
    if (n == null) { return false; }
    if (n.kind == Nk.N_PAT_WILDCARD) { return true; }
    if (n.kind != Nk.N_EXPR_IDENT) { return false; }
    // Lowercase-initial identifiers are holes; uppercase are constructors.
    if (n.p.sptr == null || n.p.slen == 0) { return false; }
    char c = n.p.sptr[0];
    return c >= 'a' && c <= 'z';
}
