// ============================================================================
// theory_msp.c3 — Multi-Stage Programming + Contextual Modal Type Theory
// ----------------------------------------------------------------------------
// (part 13)
//
// Pride's staging model is CMTT: a quoted fragment is not merely "code as
// data", it carries the lexical environment it depends on. The modal judgment
// is
//
//     Γ ⊢^E e : □_{Γ'}^{L'} τ   at   L
//
// read as: in context Γ, with effects E, the expression e denotes a *contextual
// modal box* — an open code fragment that will evaluate to τ at stage L',
// provided the environment Γ' is supplied. The box is what makes staging sound:
// without recording Γ', a quotation could smuggle a stage-L variable into a
// stage-L+1 context where it does not exist yet.
//
// This module implements:
//
//   1. STAGE LATTICE          — stage levels with quote/splice boundaries and
//      well-stagedness checking. A splice at stage 0 has no surrounding
//      quotation, and is an error, not a warning.
//   2. CROSS-STAGE ESCAPE     — the analysis that catches a variable bound at
//      stage L being referenced at a different stage without passing through
//      a box. This is the soundness property of the whole system.
//   3. QUOTE HASH-CONSING     — identical quotations share one canonical AST,
//      making quote equality a pointer compare.
//   4. OPEN-CODE MATCHING     — macros running at stage L inspect and rewrite
//      code destined for stage L+1, binding spliced subtrees (`~body`).
//   5. LEVEL SHIFTING         — renumbering a fragment's stages when it is
//      spliced into a different level.
//
// The classic soundness rule, and why the escape check exists:
//
//     let x = 5 in <~x>        -- fine: x is spliced, so evaluated at stage 0
//     let x = 5 in <x>         -- x appears at stage 1 where it is not bound
//
// The second is only sound if x's binding is captured in the box's Γ'.
// ============================================================================

module theory_msp;

import pfront_lex;
import pfront_core;
import theory_term;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz MSP_MAX_QUOTES   = 4096;
const usz MSP_MAX_SCOPES   = 512;
const usz MSP_MAX_VARS     = 4096;
const usz MSP_MAX_BINDINGS = 256;
const usz MSP_IDX_CAP      = 16384;
const int MSP_MAX_STAGE    = 64;
const int MSP_MAX_DEPTH    = 400;

// ── Stage lattice ───────────────────────────────────────────────────────────
// A scope records the stage it runs at and whether it was opened by a
// quotation. Splices decrement the stage; quotes increment it.
struct StageScope
{
    int   stage;
    bool  quote_boundary;   // opened by `<...>` / `box[...]`
    Node* owner;
    usz   var_base;         // first variable index belonging to this scope
}

struct ModalVar
{
    uint  name_id;
    int   bound_stage;      // stage at which the binder appears
    Node* binder;
    bool  is_boxed;         // captured in an explicit box environment Γ'
    int   scope_index;
}

struct StageLattice
{
    StageScope[MSP_MAX_SCOPES] scopes;
    usz                        scope_count;
    ModalVar[MSP_MAX_VARS]     vars;
    usz                        var_count;

    int  current_stage;
    int  max_stage_seen;
    int  min_stage_seen;
    usz  quote_depth;
    usz  splice_depth;
}

fn void StageLattice.init(StageLattice* l)
{
    l.scope_count = 0;
    l.var_count = 0;
    l.current_stage = 0;
    l.max_stage_seen = 0;
    l.min_stage_seen = 0;
    l.quote_depth = 0;
    l.splice_depth = 0;
    l.push_scope(0, false, null);
}

fn void StageLattice.push_scope(StageLattice* l, int stage, bool quote_boundary,
                                Node* owner)
{
    if (l.scope_count >= MSP_MAX_SCOPES) { return; }
    StageScope* s = &l.scopes[l.scope_count];
    s.stage = stage;
    s.quote_boundary = quote_boundary;
    s.owner = owner;
    s.var_base = l.var_count;
    l.scope_count = l.scope_count + 1;
    l.current_stage = stage;
    if (stage > l.max_stage_seen) { l.max_stage_seen = stage; }
    if (stage < l.min_stage_seen) { l.min_stage_seen = stage; }
}

fn void StageLattice.pop_scope(StageLattice* l)
{
    if (l.scope_count == 0) { return; }
    l.scope_count = l.scope_count - 1;
    // Variables bound inside the scope leave with it.
    l.var_count = l.scopes[l.scope_count].var_base;
    l.current_stage = l.scope_count > 0 ? l.scopes[l.scope_count - 1].stage : 0;
}

fn void StageLattice.bind(StageLattice* l, uint name_id, Node* binder, bool boxed)
{
    if (l.var_count >= MSP_MAX_VARS || name_id == 0) { return; }
    ModalVar* v = &l.vars[l.var_count];
    v.name_id = name_id;
    v.bound_stage = l.current_stage;
    v.binder = binder;
    v.is_boxed = boxed;
    v.scope_index = (int)l.scope_count - 1;
    l.var_count = l.var_count + 1;
}

fn ModalVar* StageLattice.lookup(StageLattice* l, uint name_id)
{
    // Innermost binding wins.
    usz i = l.var_count;
    while (i > 0)
    {
        i = i - 1;
        if (l.vars[i].name_id == name_id) { return &l.vars[i]; }
    }
    return null;
}

// ── Quote registry (hash-consing) ───────────────────────────────────────────
struct QuoteEntry
{
    Node* quote;
    ulong hash;
    int   stage;
    int   next;
}

struct QuoteRegistry
{
    QuoteEntry[MSP_MAX_QUOTES] entries;
    int[MSP_IDX_CAP]           buckets;
    usz                        count;
    usz                        shared;      // duplicate quotes deduplicated
    usz                        unique;
}

fn void QuoteRegistry.init(QuoteRegistry* r)
{
    for (usz i = 0; i < MSP_IDX_CAP; i++) { r.buckets[i] = 0; }
    r.count = 1;
    r.shared = 0;
    r.unique = 0;
}

fn Node* QuoteRegistry.intern(QuoteRegistry* r, Node* q, int stage)
{
    if (q == null) { return null; }
    ulong h = theory_term::term_hash(q, 0) ^ ((ulong)stage * 0x9e3779b9UL);
    usz b = (usz)(h & (ulong)(MSP_IDX_CAP - 1));
    int cur = r.buckets[b];
    while (cur != 0)
    {
        QuoteEntry* e = &r.entries[cur];
        if (e.hash == h && e.stage == stage && theory_term::term_eq(e.quote, q, 0))
        {
            r.shared = r.shared + 1;
            return e.quote;
        }
        cur = e.next;
    }
    if (r.count >= MSP_MAX_QUOTES) { return q; }
    int id = (int)r.count;
    r.count = r.count + 1;
    r.entries[id].quote = q;
    r.entries[id].hash = h;
    r.entries[id].stage = stage;
    r.entries[id].next = r.buckets[b];
    r.buckets[b] = id;
    r.unique = r.unique + 1;
    return q;
}

// ── Staging checker ─────────────────────────────────────────────────────────
struct StageChecker
{
    StageLattice           lattice;
    QuoteRegistry          quotes;
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    Arena*                 arena;
    char*                  file;

    usz  quotes_seen;
    usz  splices_seen;
    usz  boxes_seen;
    usz  escapes;            // cross-stage variable escapes
    usz  splice_at_zero;     // splice with no enclosing quote
    usz  stage_overflow;
    usz  cross_stage_ok;     // legal cross-stage references (through a box)
}

fn void StageChecker.init(StageChecker* sc, Arena* a, pfront_core::DiagBag* d,
                          pfront_core::Interner* it, char* file)
{
    sc.lattice.init();
    sc.quotes.init();
    sc.diags = d;
    sc.interner = it;
    sc.arena = a;
    sc.file = file;
    sc.quotes_seen = 0;
    sc.splices_seen = 0;
    sc.boxes_seen = 0;
    sc.escapes = 0;
    sc.splice_at_zero = 0;
    sc.stage_overflow = 0;
    sc.cross_stage_ok = 0;
}

// Walk the tree tracking the current stage, binding variables at their stage,
// and reporting any reference that crosses a stage boundary unsoundly.
fn void StageChecker.walk(StageChecker* sc, Node* n, int depth)
{
    if (n == null || depth > MSP_MAX_DEPTH) { return; }

    switch (n.kind)
    {
        case N_EXPR_QUOTE:
        {
            sc.quotes_seen = sc.quotes_seen + 1;

            /*
             REIFICATION SIGILS ARE NOT A STAGING CONSTRUCT.

             `~Tree e`, `~Data e` and `~Bytes e` share the N_EXPR_QUOTE
             node kind with `quote`/`stage`, but they mean something
             different: they reify an expression that is ALREADY in scope
             as a tree / raw data / bytes. They do not defer evaluation to
             a later stage.

             Treating them as a stage bump made the spec's own §18 example
             an error:

                 let node = ~Tree (x + y * z)

             — every outer local inside the sigil was reported as a
             cross-stage escape (E3202). That is a false positive: `x` has
             to be NAMEABLE here, not evaluated later, and §20 states the
             MSP stage is deliberately unrestricted.

             So a sigil walks its body at the CURRENT stage. `quote` and
             `stage`, which really do defer, still bump.
            */
            int sig = n.p.op;
            bool is_reify = sig == (int)pfront_lex::TokenType.TOKEN_SIGIL_TREE
                         || sig == (int)pfront_lex::TokenType.TOKEN_SIGIL_DATA
                         || sig == (int)pfront_lex::TokenType.TOKEN_SIGIL_BYTES;
            if (is_reify)
            {
                for (usz i = 0; i < n.child_count; i++)
                {
                    sc.walk(n.children[i], depth + 1);
                }
                return;
            }

            int next = sc.lattice.current_stage + 1;
            if (next > MSP_MAX_STAGE)
            {
                sc.stage_overflow = sc.stage_overflow + 1;
                sc.diags.error(pfront_core::Phase.PH_RESOLVE, 3200, n.line, n.col,
                               "quotation nesting exceeds the maximum stage level",
                               sc.file);
                return;
            }
            sc.lattice.quote_depth = sc.lattice.quote_depth + 1;
            sc.lattice.push_scope(next, true, n);
            for (usz i = 0; i < n.child_count; i++) { sc.walk(n.children[i], depth + 1); }
            sc.lattice.pop_scope();
            sc.lattice.quote_depth = sc.lattice.quote_depth - 1;
            // Record the quotation for structural sharing.
            sc.quotes.intern(n, next);
            n.p.aux = next;
        }

        case N_EXPR_SPLICE:
        {
            sc.splices_seen = sc.splices_seen + 1;
            int next = sc.lattice.current_stage - 1;
            if (sc.lattice.quote_depth == 0)
            {
                // `~e` outside any quotation has nothing to splice into. This
                // is the dual of an unbalanced closing bracket.
                sc.splice_at_zero = sc.splice_at_zero + 1;
                sc.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3201, n.line, n.col,
                                    "splice appears outside a quotation",
                                    "a splice `~e` may only occur inside `<...>` or a box",
                                    sc.file);
                return;
            }
            sc.lattice.splice_depth = sc.lattice.splice_depth + 1;
            sc.lattice.push_scope(next, false, n);
            for (usz i = 0; i < n.child_count; i++) { sc.walk(n.children[i], depth + 1); }
            sc.lattice.pop_scope();
            sc.lattice.splice_depth = sc.lattice.splice_depth - 1;
            n.p.aux = next;
        }

        case N_DECL_LET:
        case N_DECL_CONST:
        case N_DECL_STATIC:
        {
            // Initialiser runs before the binder enters scope.
            for (usz i = 1; i < n.child_count; i++) { sc.walk(n.children[i], depth + 1); }
            Node* pat = n.child(0);
            if (pat != null) { sc.bind_pattern(pat, false); }
        }

        case N_DECL_FN:
        {
            sc.lattice.push_scope(sc.lattice.current_stage, false, n);
            for (usz i = 0; i < n.child_count; i++)
            {
                Node* c = n.children[i];
                if (c == null) { continue; }
                if (c.kind == Nk.N_CLAUSE)
                {
                    sc.lattice.push_scope(sc.lattice.current_stage, false, c);
                    sc.bind_pattern(c.child(0), false);
                    for (usz j = 1; j < c.child_count; j++) { sc.walk(c.children[j], depth + 1); }
                    sc.lattice.pop_scope();
                }
                else if (c.kind == Nk.N_DECL_PARAM) { sc.bind_pattern(c.child(0), false); }
                else { sc.walk(c, depth + 1); }
            }
            sc.lattice.pop_scope();
        }

        case N_EXPR_IDENT:
        {
            if (n.name_id == 0) { break; }
            ModalVar* v = sc.lattice.lookup(n.name_id);
            if (v == null) { break; }   // free / global: not a staging concern
            if (v.bound_stage == sc.lattice.current_stage) { break; }

            // A cross-stage reference is sound only when the variable was
            // captured in a box environment Γ'. Otherwise the value does not
            // exist at the stage where it is used.
            if (v.is_boxed)
            {
                sc.cross_stage_ok = sc.cross_stage_ok + 1;
                break;
            }
            sc.escapes = sc.escapes + 1;
            sc.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3202, n.line, n.col,
                                "cross-stage variable escape",
                                "capture it in a box environment, or splice it with `~`",
                                sc.file);
        }

        case N_BLOCK:
        {
            sc.lattice.push_scope(sc.lattice.current_stage, false, n);
            for (usz i = 0; i < n.child_count; i++) { sc.walk(n.children[i], depth + 1); }
            sc.lattice.pop_scope();
        }

        default:
        {
            for (usz i = 0; i < n.child_count; i++) { sc.walk(n.children[i], depth + 1); }
        }
    }
}

fn void StageChecker.bind_pattern(StageChecker* sc, Node* pat, bool boxed)
{
    if (pat == null) { return; }
    if (pat.kind == Nk.N_PAT_IDENT && pat.name_id != 0)
    {
        sc.lattice.bind(pat.name_id, pat, boxed);
        return;
    }
    for (usz i = 0; i < pat.child_count; i++) { sc.bind_pattern(pat.children[i], boxed); }
}

fn void StageChecker.report(StageChecker* sc)
{
    printf("  staging          : %d quotes, %d splices, %d boxes (max stage %d)\n",
           (int)sc.quotes_seen, (int)sc.splices_seen, (int)sc.boxes_seen,
           sc.lattice.max_stage_seen);
    printf("  stage soundness  : %d escapes, %d splices at stage 0, %d legal cross-stage\n",
           (int)sc.escapes, (int)sc.splice_at_zero, (int)sc.cross_stage_ok);
    printf("  quote sharing    : %d unique, %d deduplicated\n",
           (int)sc.quotes.unique, (int)sc.quotes.shared);
}

// ── Open-code pattern matching ──────────────────────────────────────────────
// A macro at stage L inspects code destined for stage L+1. The pattern may
// contain splice holes (`~body`) that bind whole subtrees.
struct OpenCodeBinding
{
    uint  name_id;
    Node* captured;
    int   stage;
}

struct OpenCodeMatch
{
    OpenCodeBinding[MSP_MAX_BINDINGS] bindings;
    usz                               count;
    usz                               attempts;
    usz                               successes;
}

fn void OpenCodeMatch.clear(OpenCodeMatch* m) { m.count = 0; }

fn bool OpenCodeMatch.bind(OpenCodeMatch* m, uint name, Node* captured, int stage)
{
    for (usz i = 0; i < m.count; i++)
    {
        if (m.bindings[i].name_id != name) { continue; }
        // Non-linear open-code pattern: both occurrences must capture the same
        // fragment, exactly as in the term rewriter.
        return theory_term::term_eq(m.bindings[i].captured, captured, 0);
    }
    if (m.count >= MSP_MAX_BINDINGS) { return false; }
    m.bindings[m.count].name_id = name;
    m.bindings[m.count].captured = captured;
    m.bindings[m.count].stage = stage;
    m.count = m.count + 1;
    return true;
}

fn Node* OpenCodeMatch.lookup(OpenCodeMatch* m, uint name)
{
    for (usz i = 0; i < m.count; i++)
    {
        if (m.bindings[i].name_id == name) { return m.bindings[i].captured; }
    }
    return null;
}

// Match `subject` (stage L+1 code) against `pattern`, where a splice node in
// the pattern is a capture hole.
fn bool match_open_code(Node* pattern, Node* subject, OpenCodeMatch* m, int depth)
{
    if (pattern == null || subject == null) { return false; }
    if (depth > MSP_MAX_DEPTH) { return false; }

    // A splice in PATTERN position is a hole: `<f(~x)>` captures whatever
    // stands where `~x` appears.
    if (pattern.kind == Nk.N_EXPR_SPLICE)
    {
        Node* hole = pattern.child(0);
        if (hole == null) { return true; }
        if (hole.kind == Nk.N_EXPR_IDENT && hole.name_id != 0)
        {
            return m.bind(hole.name_id, subject, 0);
        }
        return match_open_code(hole, subject, m, depth + 1);
    }

    if (pattern.kind != subject.kind) { return false; }
    if (pattern.p.op != subject.p.op) { return false; }

    switch (pattern.kind)
    {
        case N_EXPR_INT:
        case N_EXPR_BOOL:
        case N_EXPR_CHAR:
            if (pattern.p.ival != subject.p.ival) { return false; }
        case N_EXPR_IDENT:
            if (pattern.name_id != subject.name_id) { return false; }
        default:
            break;
    }

    if (pattern.child_count != subject.child_count) { return false; }
    for (usz i = 0; i < pattern.child_count; i++)
    {
        if (!match_open_code(pattern.children[i], subject.children[i], m, depth + 1))
        {
            return false;
        }
    }
    return true;
}

// Rewrite open code: match, then instantiate the replacement template with the
// captured fragments substituted in.
fn Node* rewrite_open_code(Arena* a, Node* pattern, Node* replacement,
                           Node* subject, OpenCodeMatch* m)
{
    m.clear();
    m.attempts = m.attempts + 1;
    if (!match_open_code(pattern, subject, m, 0)) { return null; }
    m.successes = m.successes + 1;
    return instantiate_open(a, replacement, m, 0);
}

fn Node* instantiate_open(Arena* a, Node* tmpl, OpenCodeMatch* m, int depth)
{
    if (tmpl == null || depth > MSP_MAX_DEPTH) { return null; }

    if (tmpl.kind == Nk.N_EXPR_SPLICE)
    {
        Node* hole = tmpl.child(0);
        if (hole != null && hole.kind == Nk.N_EXPR_IDENT)
        {
            Node* captured = m.lookup(hole.name_id);
            if (captured != null) { return theory_term::clone_term(a, captured, depth); }
        }
    }

    Node* c = a.node(tmpl.kind, tmpl.line, tmpl.col);
    if (c == null) { return null; }
    c.name_id = tmpl.name_id;
    c.flags = tmpl.flags | pfront_core::NF_SYNTHETIC;
    c.p = tmpl.p;
    c.type_ann = tmpl.type_ann;
    c.resolved = tmpl.resolved;
    c.owner = tmpl.owner;
    for (usz i = 0; i < tmpl.child_count; i++)
    {
        a.add_child(c, instantiate_open(a, tmpl.children[i], m, depth + 1));
    }
    return c;
}

// ── Level shifting ──────────────────────────────────────────────────────────
// Splicing a fragment built at stage L into stage L+k requires renumbering
// every stage annotation inside it. Getting this wrong silently produces code
// that runs at the wrong time.
fn usz shift_stages(Node* n, int delta, int depth)
{
    if (n == null || depth > MSP_MAX_DEPTH) { return 0; }
    usz shifted = 0;
    if (n.kind == Nk.N_EXPR_QUOTE || n.kind == Nk.N_EXPR_SPLICE)
    {
        int ns = n.p.aux + delta;
        if (ns >= 0 && ns <= MSP_MAX_STAGE) { n.p.aux = ns; shifted = 1; }
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        shifted = shifted + shift_stages(n.children[i], delta, depth + 1);
    }
    return shifted;
}

// ── Contextual modal boxes ──────────────────────────────────────────────────
// `box[Γ] e at Stage L` — the environment Γ is what makes a cross-stage
// reference legal, so it is recorded explicitly rather than inferred.
struct BoxEnv
{
    uint[MSP_MAX_BINDINGS] names;
    usz                    count;
    int                    stage;
}

fn void BoxEnv.init(BoxEnv* b, int stage)
{
    b.count = 0;
    b.stage = stage;
}

fn bool BoxEnv.add(BoxEnv* b, uint name)
{
    if (b.count >= MSP_MAX_BINDINGS) { return false; }
    for (usz i = 0; i < b.count; i++) { if (b.names[i] == name) { return true; } }
    b.names[b.count] = name;
    b.count = b.count + 1;
    return true;
}

fn bool BoxEnv.contains(BoxEnv* b, uint name)
{
    for (usz i = 0; i < b.count; i++) { if (b.names[i] == name) { return true; } }
    return false;
}

// Verify that every free variable of the boxed expression is listed in Γ.
// An unlisted variable is precisely the escape the modal discipline forbids.
fn usz verify_box_closure(Node* body, BoxEnv* env, pfront_core::DiagBag* d,
                          pfront_core::Interner* it, char* file, int depth)
{
    if (body == null || depth > MSP_MAX_DEPTH) { return 0; }
    usz violations = 0;
    if (body.kind == Nk.N_EXPR_IDENT && body.name_id != 0)
    {
        // Only locally-bound names matter; globals are available at every stage.
        if (body.resolved != null && body.resolved.kind == Nk.N_PAT_IDENT)
        {
            if (!env.contains(body.name_id))
            {
                violations = 1;
                d.error_hint(pfront_core::Phase.PH_RESOLVE, 3203, body.line, body.col,
                             "variable is not captured by the box environment",
                             "add it to the box's environment list Γ",
                             file);
            }
        }
    }
    for (usz i = 0; i < body.child_count; i++)
    {
        violations = violations
                   + verify_box_closure(body.children[i], env, d, it, file, depth + 1);
    }
    return violations;
}
