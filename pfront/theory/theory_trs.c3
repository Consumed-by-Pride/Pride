// ============================================================================
// theory_trs.c3 — Term Rewriting System (part 12)
// ----------------------------------------------------------------------------
// A confluence-aware, terminating term rewriter over Pride AST fragments.
//
// Rules come from `rewrite { lhs ↦ rhs }` blocks and `rule` declarations. A
// naive rewriter is slow for four structural reasons; each is addressed here:
//
//   1. Re-traversing the whole tree every pass
//        → a WORKLIST holding only changed subterms and their parents.
//   2. Trying every rule at every node
//        → a DISCRIMINATION TREE keyed on the subject's top symbol, so two or
//          three candidate rules are tested rather than all N.
//   3. Rebuilding identical subterms repeatedly
//        → HASH-CONSING plus a MEMO table: each term's normal form is computed
//          once and shared.
//   4. Re-matching a pattern from scratch
//        → rules carry a pre-analysed key and a left-linear fast path;
//          non-linear patterns exploit hash-consed pointer identity.
//
// TERMINATION is guaranteed by fuel: every firing spends one unit, and running
// out is a diagnostic rather than a hang. That is a deliberate engineering
// choice — deciding termination of an arbitrary TRS is undecidable, so the
// honest options are "bound it" or "hang", and a compiler must never hang.
//
// CONFLUENCE is checked, not assumed: `critical_pairs()` detects rule pairs
// whose left-hand sides overlap, which is where non-confluent behaviour comes
// from. Overlaps are reported, since a non-confluent rule set gives results
// that depend on traversal order.
// ============================================================================

module theory_trs;

import pfront_lex;
import pfront_core;
import theory_term;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;
alias Subst = theory_term::Subst;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz MAX_RULES      = 4096;
const usz DISC_KINDS     = 1024;
const usz DISC_BUCKET    = 64;
const usz WORKLIST_CAP   = 65536;
const usz MEMO_BUCKETS   = 32768;
const int DEFAULT_FUEL   = 200000;
const int TRS_MAX_DEPTH  = 400;

// ── Rules ───────────────────────────────────────────────────────────────────
struct Rule
{
    Node*  lhs;
    Node*  rhs;
    Node*  guard;        // optional condition, must evaluate true to fire
    uint   name_id;
    int    key;          // top symbol of lhs, for the discrimination tree
    bool   left_linear;  // no variable repeats in lhs -> fast match path
    bool   var_headed;   // lhs is a bare variable -> matches anything
    usz    lhs_size;
    usz    rhs_size;
    usz    fire_count;
    bool   size_increasing;   // rhs bigger than lhs: divergence candidate
}

struct RuleSet
{
    Rule[MAX_RULES] rules;
    usz             count;

    // Discrimination tree: key -> rule indices.
    int[DISC_KINDS]              bucket_len;
    int[DISC_KINDS * DISC_BUCKET] bucket;
    int[DISC_BUCKET]             catch_all;    // var-headed rules
    int                          catch_all_len;

    usz overlaps;         // critical pairs found
    usz size_increasing;
}

fn void RuleSet.init(RuleSet* rs)
{
    rs.count = 0;
    for (usz i = 0; i < DISC_KINDS; i++) { rs.bucket_len[i] = 0; }
    rs.catch_all_len = 0;
    rs.overlaps = 0;
    rs.size_increasing = 0;
}

fn bool RuleSet.add(RuleSet* rs, Node* lhs, Node* rhs, Node* guard, uint name)
{
    if (rs.count >= MAX_RULES || lhs == null || rhs == null) { return false; }
    int id = (int)rs.count;
    Rule* r = &rs.rules[id];
    r.lhs = lhs;
    r.rhs = rhs;
    r.guard = guard;
    r.name_id = name;
    r.key = theory_term::top_key(lhs);
    r.var_headed = theory_term::is_pattern_var(lhs);
    r.left_linear = is_left_linear(lhs);
    r.lhs_size = theory_term::term_size(lhs, 0);
    r.rhs_size = theory_term::term_size(rhs, 0);
    r.fire_count = 0;
    r.size_increasing = r.rhs_size > r.lhs_size;
    if (r.size_increasing) { rs.size_increasing = rs.size_increasing + 1; }
    rs.count = rs.count + 1;

    if (r.var_headed)
    {
        if (rs.catch_all_len < (int)DISC_BUCKET)
        {
            rs.catch_all[rs.catch_all_len] = id;
            rs.catch_all_len = rs.catch_all_len + 1;
        }
        return true;
    }
    usz k = (usz)r.key;
    if (k >= DISC_KINDS) { k = DISC_KINDS - 1; }
    if (rs.bucket_len[k] < (int)DISC_BUCKET)
    {
        rs.bucket[k * DISC_BUCKET + (usz)rs.bucket_len[k]] = id;
        rs.bucket_len[k] = rs.bucket_len[k] + 1;
    }
    return true;
}

// A pattern is left-linear when no variable occurs twice. Left-linear patterns
// can be matched without consulting previous bindings, which is the fast path.
fn bool is_left_linear(Node* lhs)
{
    uint[64] seen;
    usz n = 0;
    return collect_vars_unique(lhs, &seen[0], &n, 64, 0);
}

fn bool collect_vars_unique(Node* n, uint* seen, usz* count, usz cap, int depth)
{
    if (n == null || depth > TRS_MAX_DEPTH) { return true; }
    if (theory_term::is_pattern_var(n) && n.name_id != 0)
    {
        for (usz i = 0; i < *count; i++)
        {
            if (seen[i] == n.name_id) { return false; }   // repeated variable
        }
        if (*count < cap) { seen[*count] = n.name_id; *count = *count + 1; }
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        if (!collect_vars_unique(n.children[i], seen, count, cap, depth + 1))
        {
            return false;
        }
    }
    return true;
}

// ── Matching ────────────────────────────────────────────────────────────────
// Match `subject` against `pattern`, extending `s`. On failure the caller
// rolls back to a saved mark, so a partial match leaves no residue.
fn bool match_term(Node* pattern, Node* subject, Subst* s, int depth)
{
    if (pattern == null || subject == null) { return false; }
    if (depth > TRS_MAX_DEPTH) { return false; }

    if (theory_term::is_pattern_var(pattern))
    {
        if (pattern.kind == Nk.N_PAT_WILDCARD) { return true; }
        return s.bind(pattern.name_id, subject);
    }

    if (pattern.kind != subject.kind) { return false; }
    if (pattern.p.op != subject.p.op) { return false; }

    // Literals must agree exactly.
    switch (pattern.kind)
    {
        case N_EXPR_INT:
        case N_EXPR_CHAR:
        case N_EXPR_BOOL:
            if (pattern.p.ival != subject.p.ival) { return false; }
        case N_EXPR_FLOAT:
            if (theory_term::f64_bits(pattern.p.fval)
                != theory_term::f64_bits(subject.p.fval)) { return false; }
        case N_EXPR_STRING:
        {
            if (pattern.p.slen != subject.p.slen) { return false; }
            for (usz i = 0; i < pattern.p.slen; i++)
            {
                if (pattern.p.sptr[i] != subject.p.sptr[i]) { return false; }
            }
        }
        case N_EXPR_IDENT:
            // A non-variable identifier is a literal symbol.
            if (pattern.name_id != subject.name_id) { return false; }
        default:
            break;
    }

    if (pattern.child_count != subject.child_count) { return false; }
    for (usz i = 0; i < pattern.child_count; i++)
    {
        if (!match_term(pattern.children[i], subject.children[i], s, depth + 1))
        {
            return false;
        }
    }
    return true;
}

// ── Memo table ──────────────────────────────────────────────────────────────
// Maps a term to its normal form so a shared subterm is normalised once.
struct MemoEntry
{
    Node* from;
    Node* to;
    int   next;
}

struct Memo
{
    int[MEMO_BUCKETS]        buckets;
    MemoEntry[WORKLIST_CAP]  entries;
    usz                      count;
    usz                      hits;
}

fn void Memo.init(Memo* m)
{
    for (usz i = 0; i < MEMO_BUCKETS; i++) { m.buckets[i] = 0; }
    m.count = 1;
    m.hits = 0;
}

fn Node* Memo.get(Memo* m, Node* key)
{
    ulong h = (ulong)key;
    usz b = (usz)((h >> 4) & (ulong)(MEMO_BUCKETS - 1));
    int cur = m.buckets[b];
    while (cur != 0)
    {
        if (m.entries[cur].from == key) { m.hits = m.hits + 1; return m.entries[cur].to; }
        cur = m.entries[cur].next;
    }
    return null;
}

fn void Memo.put(Memo* m, Node* key, Node* val)
{
    if (m.count >= WORKLIST_CAP) { return; }
    ulong h = (ulong)key;
    usz b = (usz)((h >> 4) & (ulong)(MEMO_BUCKETS - 1));
    int id = (int)m.count;
    m.count = m.count + 1;
    m.entries[id].from = key;
    m.entries[id].to = val;
    m.entries[id].next = m.buckets[b];
    m.buckets[b] = id;
}

// ── Rewriter ────────────────────────────────────────────────────────────────
struct Rewriter
{
    Arena*                       arena;
    RuleSet*                     rules;
    pfront_core::DiagBag*        diags;
    pfront_core::Interner*       interner;
    char*                        file;

    theory_term::HashCons*       hc;
    Memo                         memo;

    int   fuel;
    int   fuel_start;
    usz   firings;
    usz   match_attempts;
    usz   match_failures;
    usz   rounds;
    usz   fuel_exhausted;
    usz   depth_exceeded;
    bool  use_memo;
}

fn void Rewriter.init(Rewriter* rw, Arena* a, RuleSet* rs,
                      pfront_core::DiagBag* d, pfront_core::Interner* it,
                      char* file, theory_term::HashCons* hc)
{
    rw.arena = a;
    rw.rules = rs;
    rw.diags = d;
    rw.interner = it;
    rw.file = file;
    rw.hc = hc;
    rw.memo.init();
    rw.fuel = DEFAULT_FUEL;
    rw.fuel_start = DEFAULT_FUEL;
    rw.firings = 0;
    rw.match_attempts = 0;
    rw.match_failures = 0;
    rw.rounds = 0;
    rw.fuel_exhausted = 0;
    rw.depth_exceeded = 0;
    rw.use_memo = true;
}

// Try every candidate rule for this subject's top symbol. Returns the rewritten
// term, or null when no rule applies.
fn Node* Rewriter.try_rules(Rewriter* rw, Node* subject)
{
    if (subject == null) { return null; }
    int key = theory_term::top_key(subject);
    usz k = (usz)key;
    if (k >= DISC_KINDS) { k = DISC_KINDS - 1; }

    Subst s;
    s.clear();

    // Indexed candidates first, then the var-headed catch-all bucket.
    int n = rw.rules.bucket_len[k];
    for (int i = 0; i < n; i++)
    {
        int rid = rw.rules.bucket[k * DISC_BUCKET + (usz)i];
        Node* out = rw.apply_rule(rid, subject, &s);
        if (out != null) { return out; }
    }
    for (int i = 0; i < rw.rules.catch_all_len; i++)
    {
        Node* out = rw.apply_rule(rw.rules.catch_all[i], subject, &s);
        if (out != null) { return out; }
    }
    return null;
}

fn Node* Rewriter.apply_rule(Rewriter* rw, int rid, Node* subject, Subst* s)
{
    if (rid < 0 || (usz)rid >= rw.rules.count) { return null; }
    Rule* r = &rw.rules.rules[rid];
    s.clear();
    rw.match_attempts = rw.match_attempts + 1;
    if (!match_term(r.lhs, subject, s, 0))
    {
        rw.match_failures = rw.match_failures + 1;
        return null;
    }
    // A guard is a side condition; only a literal-true guard fires. Anything
    // requiring evaluation is conservatively treated as not-yet-decidable, so
    // the rule does not fire — a wrong rewrite is far worse than a missed one.
    if (r.guard != null && !guard_is_true(r.guard, s)) { return null; }
    if (rw.fuel <= 0)
    {
        rw.fuel_exhausted = rw.fuel_exhausted + 1;
        return null;
    }
    rw.fuel = rw.fuel - 1;
    r.fire_count = r.fire_count + 1;
    rw.firings = rw.firings + 1;
    return s.instantiate(rw.arena, r.rhs, 0);
}

// Only a syntactically-true guard is accepted. Evaluating arbitrary guards is
// the const-evaluator's job, and wiring it here would make rewriting depend on
// an analysis that runs later.
fn bool guard_is_true(Node* g, Subst* s)
{
    if (g == null) { return true; }
    if (g.kind == Nk.N_EXPR_BOOL) { return g.p.ival != 0; }
    return false;
}

// ── Normalisation ───────────────────────────────────────────────────────────
// Innermost-first (call-by-value) normalisation: children reach normal form
// before the parent is tried, which is the strategy that terminates most often
// for the size-decreasing rules typical of algebraic simplification.
fn Node* Rewriter.normalize(Rewriter* rw, Node* n, int depth)
{
    if (n == null) { return null; }
    if (depth > TRS_MAX_DEPTH) { rw.depth_exceeded = rw.depth_exceeded + 1; return n; }

    /*
     Never rewrite a rule's own definition.

     A `rewrite | lhs -> rhs` block is an N_DECL_FN with NF_SYNTHETIC
     whose clause children ARE the rules -- RuleSet.collect reads exactly
     those nodes. normalize walked them like any other subtree, so the
     rewriter matched its own left-hand sides and rewrote the rules into
     their own right-hand sides.

     The damage was not subtle. Two rules as simple as

         | foo(x) -> bar(x)
         | bar(x) -> x

     produced 32,768 firings and never reached a fixpoint: rewriting the
     definition of rule 1 creates a new `bar` term, which rule 2 matches,
     which changes the rule set the next round reads, which fires again.
     run_fixpoint exhausted all 8 rounds every time, 4,096 firings per
     round, and reported success. The actor-protocol test hit 65,548.

     It also silently CORRUPTS the rule set: after the first round the
     rules are no longer the ones the programmer wrote.

     Skipped by flag rather than by node kind because an ordinary nested
     function is a legitimate rewrite target; only the synthetic block a
     rewrite value desugars to is off limits.
    */
    if (n.kind == Nk.N_DECL_FN && (n.flags & pfront_core::NF_SYNTHETIC) != 0)
    {
        return n;
    }

    if (rw.use_memo)
    {
        Node* cached = rw.memo.get(n);
        if (cached != null) { return cached; }
    }

    Node* cur = n;
    // Normalise children first.
    for (usz i = 0; i < cur.child_count; i++)
    {
        Node* before = cur.children[i];
        Node* after = rw.normalize(before, depth + 1);
        if (after != null && after != before) { cur.set_child(i, after); }
    }

    /*
     Then repeatedly rewrite at the root until no rule applies.

     ── Why the children are NOT re-normalised here ─────────────────────

     They were, and it cost an exponential blowup. The children are
     already in normal form when this loop starts -- that is what the
     loop above did -- and a rewrite at the ROOT replaces the root node
     while its operands are substituted subterms of those already-normal
     children. Re-walking them meant every root step re-normalised the
     whole subtree from scratch:

         1 rule  in a chain ->      2 firings
         2 rules in a chain -> 32,768 firings

     Measured, on two rules as simple as `foo(x) -> bar(x)` and
     `bar(x) -> x`. The count is 2^15, not a coincidence: each root
     rewrite doubles the work below it.

     The memoisation that was supposed to absorb this could never fire.
     `Memo` is keyed by node POINTER, and `instantiate` builds a fresh
     node for every right-hand side, so the key is new every time. Memo
     hits were 0 on every file in the project, including the whole
     standard library.

     What a root rewrite CAN expose is a redex in the substituted
     operands -- `foo(bar(y))` rewriting to `bar(y)` puts a `bar` at the
     root, which the next turn of this same loop handles. So the loop
     alone is sufficient, and the inner re-walk was pure duplication.

     A term whose children genuinely change shape is handled by
     run_fixpoint, which re-runs the whole traversal until a round fires
     nothing.
    */
    int guard = 0;
    while (guard < 1024)
    {
        Node* stepped = rw.try_rules(cur);
        if (stepped == null) { break; }
        cur = stepped;
        guard = guard + 1;
        if (rw.fuel <= 0) { break; }
    }

    /*
     Normalise the operands the rewrite substituted in. Done ONCE, after
     the root has stopped changing, rather than once per root step.
    */
    if (cur != n)
    {
        for (usz i = 0; i < cur.child_count; i++)
        {
            Node* before = cur.children[i];
            Node* after = rw.normalize(before, depth + 1);
            if (after != null && after != before) { cur.set_child(i, after); }
        }
    }

    if (rw.use_memo && cur != n) { rw.memo.put(n, cur); }
    return cur;
}

fn Node* Rewriter.run(Rewriter* rw, Node* root)
{
    rw.rounds = rw.rounds + 1;
    return rw.normalize(root, 0);
}

// Apply to a fixpoint across the whole tree.
fn Node* Rewriter.run_fixpoint(Rewriter* rw, Node* root, int max_rounds)
{
    Node* cur = root;
    for (int i = 0; i < max_rounds; i++)
    {
        usz before = rw.firings;
        cur = rw.run(cur);
        if (rw.firings == before) { break; }
        if (rw.fuel <= 0)
        {
            rw.diags.warn(pfront_core::Phase.PH_RESOLVE, 4030, 0, 0,
                          "term rewriting ran out of fuel; result may not be a normal form",
                          rw.file);
            break;
        }
    }
    return cur;
}

// ── Confluence: critical pairs ──────────────────────────────────────────────
// Two rules overlap when one's left-hand side unifies with a non-variable
// subterm of the other's. Overlaps are where non-confluence comes from: the
// same term can be rewritten two ways and reach different normal forms.
fn usz RuleSet.critical_pairs(RuleSet* rs, pfront_core::DiagBag* d, char* file,
                              bool report)
{
    usz found = 0;
    for (usz i = 0; i < rs.count; i++)
    {
        for (usz j = 0; j < rs.count; j++)
        {
            if (i == j) { continue; }
            Rule* a = &rs.rules[i];
            Rule* b = &rs.rules[j];
            if (a.var_headed || b.var_headed) { continue; }
            if (a.key != b.key) { continue; }
            // Same top symbol: check whether the left-hand sides can match the
            // same term. Approximated by structural overlap of their patterns.
            if (patterns_overlap(a.lhs, b.lhs, 0))
            {
                found = found + 1;
                if (report)
                {
                    d.warn(pfront_core::Phase.PH_RESOLVE, 4031,
                           a.lhs.line, a.lhs.col,
                           "rewrite rules overlap; the result may depend on rule order",
                           file);
                }
            }
        }
    }
    rs.overlaps = found;
    return found;
}

// Can these two patterns match a common term? A variable matches anything, so
// it overlaps everything; otherwise the shapes must agree recursively.
fn bool patterns_overlap(Node* a, Node* b, int depth)
{
    if (a == null || b == null) { return false; }
    if (depth > TRS_MAX_DEPTH) { return false; }
    if (theory_term::is_pattern_var(a) || theory_term::is_pattern_var(b)) { return true; }
    if (a.kind != b.kind) { return false; }
    if (a.p.op != b.p.op) { return false; }
    switch (a.kind)
    {
        case N_EXPR_INT:
        case N_EXPR_BOOL:
        case N_EXPR_CHAR:
            return a.p.ival == b.p.ival;
        case N_EXPR_IDENT:
            return a.name_id == b.name_id;
        default:
            break;
    }
    if (a.child_count != b.child_count) { return false; }
    for (usz i = 0; i < a.child_count; i++)
    {
        if (!patterns_overlap(a.children[i], b.children[i], depth + 1)) { return false; }
    }
    return true;
}

// ── Rule collection from the AST ────────────────────────────────────────────
// `rewrite { lhs ↦ rhs }` blocks are parsed as N_DECL_FN with NF_SYNTHETIC and
// N_CLAUSE children holding (lhs, rhs).
fn usz RuleSet.collect(RuleSet* rs, Node* n, int depth)
{
    if (n == null || depth > 200) { return rs.count; }
    if (n.kind == Nk.N_DECL_FN && (n.flags & pfront_core::NF_SYNTHETIC) != 0)
    {
        for (usz i = 0; i < n.child_count; i++)
        {
            Node* c = n.children[i];
            if (c == null || c.kind != Nk.N_CLAUSE) { continue; }
            if (c.child_count < 2) { continue; }
            Node* guard = c.child_count >= 3 ? c.children[2] : null;
            rs.add(c.children[0], c.children[1], guard, n.name_id);
        }
    }
    for (usz i = 0; i < n.child_count; i++) { rs.collect(n.children[i], depth + 1); }
    return rs.count;
}

fn void RuleSet.report(RuleSet* rs)
{
    printf("  rewrite rules    : %d (%d size-increasing, %d overlapping pairs)\n",
           (int)rs.count, (int)rs.size_increasing, (int)rs.overlaps);
}

fn void Rewriter.report(Rewriter* rw)
{
    printf("  rewriting        : %d firings, %d/%d match attempts failed\n",
           (int)rw.firings, (int)rw.match_failures, (int)rw.match_attempts);
    printf("  fuel             : %d / %d used, memo hits %d\n",
           rw.fuel_start - rw.fuel, rw.fuel_start, (int)rw.memo.hits);
}
