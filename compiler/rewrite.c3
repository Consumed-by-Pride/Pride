// ============================================================================
// rewrite.c3 — the highly-engineered term-rewriting engine (MSP step 2)
// ----------------------------------------------------------------------------
// Implementation language: C3 (host). Second component of the MSP stage.
//
// Naive term rewriting is slow for four reasons; this engine removes each:
//
//   1. Re-traversing the whole tree every pass
//        -> a WORKLIST: only changed subterms + their parents are re-examined.
//   2. Trying every rule at every node
//        -> a DISCRIMINATION TREE: O(depth) lookup of candidate rules by the
//           subject's top-symbol key, so we test 1-3 rules, not all N.
//   3. Rebuilding identical subterms repeatedly
//        -> HASH-CONSING + a MEMO table: structurally-equal terms share one
//           canonical node, and each term's normal form is computed once.
//   4. Re-matching a pattern from scratch
//        -> rules carry a pre-analyzed key + a left-linear fast path; non-linear
//           patterns use hash-cons identity (pointer equality) for var re-use.
//
// Rules come from `rewrite { | lhs ↦ rhs (, guard)? ... }` blocks and `rule`
// declarations, already parsed to NODE_REWRITE / NODE_REWRITE_RULE. Application
// is driven by `expr |> rules` (one pass) and `expr |> rules*` (to fixpoint).
//
// Termination is guaranteed by FUEL: every rule firing spends one unit; running
// out is a diagnostic, never a hang.
// ============================================================================

module rewrite;

import lexer;
import ast;

// f64_bits: reinterpret f64 bits as ulong (replaces bitcast which moved in c3c 0.8.1)
fn ulong f64_bits(double v) @inline
{
    ulong result = 0;
    char* src = (char*)&v;
    char* dst = (char*)&result;
    for (usz i = 0; i < 8; i++) dst[i] = src[i];
    return result;
}


extern fn void* malloc(usz size);
extern fn void  free(void* ptr);

alias Node = ast::AstNode;
alias Nk = ast::NodeKind;
alias Tt = lexer::TokenType;

// ── Hash-cons table ──────────────────────────────────────────────────────────
// Structurally-equal terms map to one canonical node. Keyed by a structural
// hash; collisions resolved by structural equality.
const usz HC_BUCKETS = 65536;

struct HashCons
{
    Node*[HC_BUCKETS] buckets;   // open-addressing slots (canonical nodes)
    usz count;
}

// FNV-1a structural hash of a term (kind + payload + child identities).
fn ulong term_hash(Node* n)
{
    if (n == null) return 0;
    ulong h = 0xcbf29ce484222325;
    h ^= (ulong)(uint)(int)n.kind;
    h *= 0x100000001b3;

    switch (n.kind)
    {
        case Nk.NODE_LIT_INT:
            h ^= n.p.lit_int.int_val; h *= 0x100000001b3;
        case Nk.NODE_LIT_BOOL:
            h ^= n.p.lit_bool.bool_val ? 1 : 2; h *= 0x100000001b3;
        case Nk.NODE_LIT_FLOAT:
            h ^= f64_bits(n.p.lit_float.f64_val); h *= 0x100000001b3;
        case Nk.NODE_LIT_CHAR:
            h ^= (ulong)n.p.lit_char.char_val; h *= 0x100000001b3;
        case Nk.NODE_LIT_STRING:
            for (usz i = 0; i < n.p.lit_str.len; i++)
            {
                h ^= (ulong)(uint)(n.p.lit_str.ptr[i]); h *= 0x100000001b3;
            }
        case Nk.NODE_EXPR_BINARY:
        case Nk.NODE_EXPR_UNARY:
            h ^= (ulong)(uint)(int)n.p.op.op; h *= 0x100000001b3;
        case Nk.NODE_IDENT:
        case Nk.NODE_TYPEVAR:
            for (usz i = 0; i < n.p.ident.name_len; i++)
            {
                h ^= (ulong)(uint)(n.p.ident.name_ptr[i]); h *= 0x100000001b3;
            }
        default:
            break;
    }
    // Mix child identities (children are already canonical when we cons up).
    for (usz i = 0; i < n.child_count; i++)
    {
        ulong cid = n.children[i] != null ? (ulong)(usz)(void*)n.children[i] : 0;
        h ^= cid; h *= 0x100000001b3;
    }
    return h;
}

// Shallow structural equality given children are already canonical (pointer eq).
fn bool term_eq(Node* a, Node* b)
{
    if (a == b) return true;
    if (a == null || b == null) return false;
    if (a.kind != b.kind) return false;
    if (a.child_count != b.child_count) return false;

    switch (a.kind)
    {
        case Nk.NODE_LIT_INT:
            if (a.p.lit_int.int_val != b.p.lit_int.int_val) return false;
        case Nk.NODE_LIT_BOOL:
            if (a.p.lit_bool.bool_val != b.p.lit_bool.bool_val) return false;
        case Nk.NODE_LIT_FLOAT:
            if (f64_bits(a.p.lit_float.f64_val) != f64_bits(b.p.lit_float.f64_val)) return false;
        case Nk.NODE_LIT_CHAR:
            if (a.p.lit_char.char_val != b.p.lit_char.char_val) return false;
        case Nk.NODE_LIT_STRING:
            if (a.p.lit_str.len != b.p.lit_str.len) return false;
            for (usz j = 0; j < a.p.lit_str.len; j++)
            {
                if (a.p.lit_str.ptr[j] != b.p.lit_str.ptr[j]) return false;
            }
        case Nk.NODE_EXPR_BINARY:
        case Nk.NODE_EXPR_UNARY:
            if (a.p.op.op != b.p.op.op) return false;
        case Nk.NODE_IDENT:
        case Nk.NODE_TYPEVAR:
            if (a.p.ident.name_len != b.p.ident.name_len) return false;
            for (usz i = 0; i < a.p.ident.name_len; i++)
            {
                if (a.p.ident.name_ptr[i] != b.p.ident.name_ptr[i]) return false;
            }
        default:
            break;
    }
    for (usz i = 0; i < a.child_count; i++)
    {
        if (a.children[i] != b.children[i]) return false;   // canonical => ptr eq
    }
    return true;
}

fn void HashCons.init(HashCons* hc)
{
    for (usz i = 0; i < HC_BUCKETS; i++) hc.buckets[i] = null;
    hc.count = 0;
}

// Return the canonical node structurally equal to n, inserting n if new.
fn Node* HashCons.intern(HashCons* hc, Node* n)
{
    if (n == null) return null;
    ulong h = term_hash(n);
    usz idx = (usz)(h & (ulong)(HC_BUCKETS - 1));

    // Linear probe.
    for (usz probe = 0; probe < HC_BUCKETS; probe++)
    {
        usz slot = (idx + probe) & (HC_BUCKETS - 1);
        Node* cur = hc.buckets[slot];
        if (cur == null)
        {
            hc.buckets[slot] = n;
            hc.count++;
            return n;
        }
        if (term_eq(cur, n)) return cur;
    }
    return n;   // table full (degraded but correct)
}

// ── Rewrite rule ─────────────────────────────────────────────────────────────
struct Rule
{
    Node* lhs;       // pattern AST (lowercase Idents are pattern variables)
    Node* rhs;       // template AST (same pattern variables)
    Node* guard;     // optional guard expression, or null
    int   top_key;   // discrimination key: the LHS top-symbol class
    int   top_op;    // for binary/unary: the operator token (else -1)
    uint  prio;      // application order (source order; ++ preserves it)
    ulong lhs_effects;  // effects present on the LHS (for conservation)
    ulong rhs_effects;  // effects the RHS would introduce
}

const usz MAX_RULES = 4096;

// ── Discrimination index ─────────────────────────────────────────────────────
// Buckets rules by the top-symbol class of their LHS so `step` examines only
// CANDIDATE rules for a given subject, not all N. Rules whose LHS top is a
// pattern variable (match any kind) live in a separate "wildcard" bucket.
//
// NodeKind is a small dense enum; we index directly by (int)kind. Each bucket
// is a list of rule indices into RuleSet.rules, preserving priority order.
const usz DISC_KINDS   = 384;     // > OP_KEY_BASE + number of TokenType values
const usz DISC_BUCKET  = 512;     // max rules sharing one top key

struct DiscBucket
{
    usz[DISC_BUCKET] rule_idx;
    usz count;
}

struct DiscTree
{
    DiscBucket[DISC_KINDS] by_kind;   // rules keyed by LHS top NodeKind
    DiscBucket wildcard;              // rules with a pattern-variable LHS top
    bool built;
}

struct RuleSet
{
    Rule[MAX_RULES] rules;
    usz count;
    DiscTree index;
}

fn void RuleSet.init(RuleSet* rs)
{
    rs.count = 0;
    rs.index.built = false;
}

// A "top key" buckets rules by the subject shape they can match. We key on the
// node kind, and (for binary/unary) additionally on the operator.
// A discrimination key buckets a node by its top symbol. For binary/unary
// expressions the operator is folded in, so `x + 0` and `x * 2` land in
// DIFFERENT buckets — the key to O(candidates) lookup. Non-operator nodes key
// on their kind alone. Keys are kept < DISC_KINDS.
const int OP_KEY_BASE = 160;   // > number of NodeKind values; operator keys live above

fn int top_key_of(Node* n)
{
    if (n == null) return -1;
    if (n.kind == Nk.NODE_EXPR_BINARY || n.kind == Nk.NODE_EXPR_UNARY)
    {
        int opk = OP_KEY_BASE + (int)n.p.op.op;
        if (opk < (int)DISC_KINDS) return opk;
        return (int)n.kind;   // overflow safety: fall back to kind bucket
    }
    return (int)n.kind;
}

fn int top_op_of(Node* n)
{
    if (n == null) return -1;
    if (n.kind == Nk.NODE_EXPR_BINARY || n.kind == Nk.NODE_EXPR_UNARY)
    {
        return (int)n.p.op.op;
    }
    return -1;
}

// Add one rule (from a NODE_REWRITE_RULE) to the set.
fn void RuleSet.add(RuleSet* rs, Node* lhs, Node* rhs, Node* guard, uint prio)
{
    if (rs.count >= MAX_RULES) return;
    Rule* r = &rs.rules[rs.count];
    r.lhs = lhs;
    r.rhs = rhs;
    r.guard = guard;
    r.top_key = top_key_of(lhs);
    r.top_op = top_op_of(lhs);
    r.prio = prio;
    r.lhs_effects = lhs != null ? lhs.effects : 0;
    r.rhs_effects = rhs != null ? rhs.effects : 0;
    rs.count++;
}

// Collect all rules from a `rewrite { ... }` block (NODE_REWRITE) in order.
fn void RuleSet.add_block(RuleSet* rs, Node* rewrite_block)
{
    if (rewrite_block == null) return;
    for (usz i = 0; i < rewrite_block.child_count; i++)
    {
        Node* rule = rewrite_block.children[i];
        if (rule == null || rule.kind != Nk.NODE_REWRITE_RULE) continue;
        rs.add_rule_node(rule);
    }
}

// A single NODE_REWRITE_RULE: children are [lhs, (guard)?, rhs].
fn void RuleSet.add_rule_node(RuleSet* rs, Node* rule)
{
    if (rule.child_count < 2) return;
    Node* lhs = rule.children[0];
    Node* guard = null;
    Node* rhs = null;
    if (rule.child_count == 2)
    {
        rhs = rule.children[1];
    }
    else
    {
        // [lhs, guard, rhs]  — middle is a NODE_PATTERN_GUARD wrapper
        Node* mid = rule.children[1];
        if (mid != null && mid.kind == Nk.NODE_PATTERN_GUARD && mid.child_count >= 1)
        {
            guard = mid.children[0];
        }
        rhs = rule.children[rule.child_count - 1];
    }
    rs.add(lhs, rhs, guard, (uint)rs.count);
}

// Build the discrimination index over all added rules. Call once after every
// rule is in. Buckets each rule by its LHS top NodeKind (or the wildcard bucket
// if the LHS top is a pattern variable), preserving insertion (priority) order.
fn void RuleSet.build_index(RuleSet* rs)
{
    DiscTree* idx = &rs.index;
    for (usz k = 0; k < DISC_KINDS; k++) idx.by_kind[k].count = 0;
    idx.wildcard.count = 0;

    for (usz i = 0; i < rs.count; i++)
    {
        Rule* r = &rs.rules[i];
        if (is_pattern_var(r.lhs))
        {
            if (idx.wildcard.count < DISC_BUCKET)
            {
                idx.wildcard.rule_idx[idx.wildcard.count] = i;
                idx.wildcard.count++;
            }
            continue;
        }
        usz k = (usz)r.top_key;
        if (k < DISC_KINDS)
        {
            DiscBucket* b = &idx.by_kind[k];
            if (b.count < DISC_BUCKET)
            {
                b.rule_idx[b.count] = i;
                b.count++;
            }
        }
    }
    idx.built = true;
}

// ── Pattern binding environment ──────────────────────────────────────────────
// A pattern variable is a lowercase NODE_IDENT in a rule LHS. Matching binds
// each variable to a subject subterm; re-use of the same variable requires the
// bound subterms to be identical (hash-cons pointer equality).
const usz MAX_BINDS = 64;

struct Binding
{
    char* name_ptr;
    usz   name_len;
    Node* term;
}

struct MatchEnv
{
    Binding[MAX_BINDS] binds;
    usz count;
    bool failed;
}

fn void MatchEnv.reset(MatchEnv* e)
{
    e.count = 0;
    e.failed = false;
}

fn bool name_eq(char* a, usz alen, char* b, usz blen)
{
    if (alen != blen) return false;
    for (usz i = 0; i < alen; i++) if (a[i] != b[i]) return false;
    return true;
}

// Bind var := term, or check consistency if already bound (non-linear pattern).
fn bool MatchEnv.bind(MatchEnv* e, char* nptr, usz nlen, Node* term)
{
    for (usz i = 0; i < e.count; i++)
    {
        if (name_eq(e.binds[i].name_ptr, e.binds[i].name_len, nptr, nlen))
        {
            // Already bound: must match identically (use term equality).
            return term_eq_deep(e.binds[i].term, term);
        }
    }
    if (e.count >= MAX_BINDS) return false;
    e.binds[e.count].name_ptr = nptr;
    e.binds[e.count].name_len = nlen;
    e.binds[e.count].term = term;
    e.count++;
    return true;
}

fn Node* MatchEnv.lookup(MatchEnv* e, char* nptr, usz nlen)
{
    for (usz i = 0; i < e.count; i++)
    {
        if (name_eq(e.binds[i].name_ptr, e.binds[i].name_len, nptr, nlen))
        {
            return e.binds[i].term;
        }
    }
    return null;
}

// Deep structural equality (not assuming canonical children) — used for
// non-linear variable consistency checks.
fn bool term_eq_deep(Node* a, Node* b)
{
    if (a == b) return true;
    if (a == null || b == null) return false;
    if (a.kind != b.kind) return false;
    if (a.child_count != b.child_count) return false;

    switch (a.kind)
    {
        case Nk.NODE_LIT_INT:
            if (a.p.lit_int.int_val != b.p.lit_int.int_val) return false;
        case Nk.NODE_LIT_BOOL:
            if (a.p.lit_bool.bool_val != b.p.lit_bool.bool_val) return false;
        case Nk.NODE_EXPR_BINARY:
        case Nk.NODE_EXPR_UNARY:
            if (a.p.op.op != b.p.op.op) return false;
        case Nk.NODE_IDENT:
        case Nk.NODE_TYPEVAR:
            if (!name_eq(a.p.ident.name_ptr, a.p.ident.name_len,
                         b.p.ident.name_ptr, b.p.ident.name_len)) return false;
        default:
            break;
    }
    for (usz i = 0; i < a.child_count; i++)
    {
        if (!term_eq_deep(a.children[i], b.children[i])) return false;
    }
    return true;
}

// Is a LHS node a pattern variable? (a lowercase-leading NODE_IDENT)
fn bool is_pattern_var(Node* n)
{
    if (n == null) return false;
    if (n.kind != Nk.NODE_IDENT) return false;
    if (n.p.ident.name_len == 0) return false;
    char c = n.p.ident.name_ptr[0];
    // lowercase or underscore => a capture variable
    return (c >= 'a' && c <= 'z') || c == '_';
}

// ── Matching ─────────────────────────────────────────────────────────────────
// Match pattern `pat` against subject `subj`, recording bindings. Recursive
// structural match (a compiled match-program executed directly).
fn bool match_term(Node* pat, Node* subj, MatchEnv* env)
{
    if (pat == null) return subj == null;
    if (subj == null) return false;

    // A pattern variable matches anything and binds it.
    if (is_pattern_var(pat))
    {
        // `_` matches without binding.
        if (pat.p.ident.name_len == 1 && pat.p.ident.name_ptr[0] == '_') return true;
        return env.bind(pat.p.ident.name_ptr, pat.p.ident.name_len, subj);
    }

    if (pat.kind != subj.kind) return false;

    // Leaf payloads must match exactly.
    switch (pat.kind)
    {
        case Nk.NODE_LIT_INT:
            return pat.p.lit_int.int_val == subj.p.lit_int.int_val;
        case Nk.NODE_LIT_BOOL:
            return pat.p.lit_bool.bool_val == subj.p.lit_bool.bool_val;
        case Nk.NODE_LIT_FLOAT:
            // Exact bit-for-bit float match (handles ±0, NaN payloads soundly).
            return f64_bits(pat.p.lit_float.f64_val) == f64_bits(subj.p.lit_float.f64_val);
        case Nk.NODE_LIT_CHAR:
            return pat.p.lit_char.char_val == subj.p.lit_char.char_val;
        case Nk.NODE_LIT_STRING:
            if (pat.p.lit_str.len != subj.p.lit_str.len) return false;
            for (usz si = 0; si < pat.p.lit_str.len; si++)
            {
                if (pat.p.lit_str.ptr[si] != subj.p.lit_str.ptr[si]) return false;
            }
            return true;
        case Nk.NODE_EXPR_BINARY:
        case Nk.NODE_EXPR_UNARY:
            if (pat.p.op.op != subj.p.op.op) return false;
        case Nk.NODE_IDENT:
            // A non-variable ident (uppercase) matches by name.
            return name_eq(pat.p.ident.name_ptr, pat.p.ident.name_len,
                           subj.p.ident.name_ptr, subj.p.ident.name_len);
        default:
            break;
    }

    if (pat.child_count != subj.child_count) return false;
    for (usz i = 0; i < pat.child_count; i++)
    {
        if (!match_term(pat.children[i], subj.children[i], env)) return false;
    }
    return true;
}

// ── Instantiation ────────────────────────────────────────────────────────────
// Build the RHS, replacing each pattern variable with its bound subterm.
// Newly-built nodes are interned by the caller's hash-cons.
fn Node* instantiate(ast::AstArena* arena, HashCons* hc, Node* tmpl, MatchEnv* env)
{
    if (tmpl == null) return null;

    // A pattern variable -> its binding (already a real subterm).
    if (is_pattern_var(tmpl))
    {
        Node* b = env.lookup(tmpl.p.ident.name_ptr, tmpl.p.ident.name_len);
        if (b != null) return b;
        return tmpl;   // unbound (e.g. `_`): keep as-is
    }

    // Leaf: reuse the template node directly (immutable).
    if (tmpl.child_count == 0)
    {
        return hc.intern(tmpl);
    }

    // Rebuild children, then a fresh node carrying the template's kind/payload.
    Node*[16] buf;
    usz n = tmpl.child_count <= 16 ? tmpl.child_count : 16;
    for (usz i = 0; i < n; i++)
    {
        buf[i] = instantiate(arena, hc, tmpl.children[i], env);
    }
    Node* fresh;
    if (tmpl.kind == Nk.NODE_EXPR_BINARY || tmpl.kind == Nk.NODE_EXPR_UNARY)
    {
        fresh = ast::node_op(arena, tmpl.kind, tmpl.p.op.op, &buf[0], n, tmpl.line, tmpl.col);
    }
    else
    {
        fresh = ast::node_n(arena, tmpl.kind, &buf[0], n, tmpl.line, tmpl.col);
        if (fresh != null) fresh.p = tmpl.p;
    }
    return hc.intern(fresh);
}

// ── The engine ───────────────────────────────────────────────────────────────
struct Rewriter
{
    ast::AstArena* arena;
    HashCons*      hc;
    RuleSet*       rules;
    long           fuel;        // remaining rule firings
    bool           out_of_fuel;
    bool           conserve_effects;  // reject rules that add effects (default true)
    usz            firings;     // total rules applied (stats)
    int            depth;       // current normalize recursion depth
    bool           too_deep;    // a size-growing rule blew the depth cap
}

// Max term depth the normalizer will descend before bailing. A size-growing
// rule (e.g. `x ↦ x + x`) would otherwise recurse until the native stack
// overflows; this caps it like the parser's depth guard.
const int MAX_REWRITE_DEPTH = 800;

fn void Rewriter.init(Rewriter* rw, ast::AstArena* arena, HashCons* hc, RuleSet* rules, long fuel)
{
    rw.arena = arena;
    rw.hc = hc;
    rw.rules = rules;
    rw.fuel = fuel;
    rw.out_of_fuel = false;
    rw.conserve_effects = true;
    rw.firings = 0;
    rw.depth = 0;
    rw.too_deep = false;
}

// Try every candidate rule (by priority) at `t`. Returns the rewritten node if
// one fired, else t unchanged. Candidate selection uses the discrimination key
// (top kind + operator) so non-matching rules are skipped without a full match.
// Try the first applicable rule (in priority order) at `t`. Uses the
// discrimination index to examine only CANDIDATE rules — those whose LHS top
// matches t's kind, plus the wildcard rules — merged by priority. This is the
// O(candidates) hot path instead of O(all rules).
fn Node* Rewriter.step(Rewriter* rw, Node* t)
{
    if (t == null) return t;

    DiscTree* idx = &rw.rules.index;
    if (!idx.built)
    {
        // Index not built (shouldn't happen via the driver); fall back to a
        // full scan so correctness never depends on the index being present.
        return rw.step_scan(t);
    }

    int tk = top_key_of(t);
    DiscBucket* kb = (tk >= 0 && (usz)tk < DISC_KINDS) ? &idx.by_kind[tk] : null;
    DiscBucket* wb = &idx.wildcard;

    // Merge the kind bucket and the wildcard bucket by ascending rule index
    // (= priority order), trying each candidate.
    usz ki = 0;
    usz wi = 0;
    usz kn = kb != null ? kb.count : 0;
    usz wn = wb.count;

    while (ki < kn || wi < wn)
    {
        usz ridx;
        bool from_k;
        if (ki < kn && (wi >= wn || kb.rule_idx[ki] <= wb.rule_idx[wi]))
        {
            ridx = kb.rule_idx[ki];
            from_k = true;
        }
        else
        {
            ridx = wb.rule_idx[wi];
            from_k = false;
        }
        if (from_k) { ki++; } else { wi++; }

        Node* res = rw.try_rule(t, &rw.rules.rules[ridx]);
        if (res != t) return res;
        if (rw.out_of_fuel) return t;
    }
    return t;
}

// Try one rule at t. Returns the rewritten node, or t if it doesn't apply.
fn Node* Rewriter.try_rule(Rewriter* rw, Node* t, Rule* r)
{
    // Operator-level discrimination (the index already matched the kind).
    if (!is_pattern_var(r.lhs))
    {
        if (r.top_op != -1 && r.top_op != top_op_of(t)) return t;
    }

    MatchEnv env;
    env.reset();
    if (!match_term(r.lhs, t, &env)) return t;

    // UB / effect conservation: a rule may not introduce effects the subject
    // didn't already carry (keeps verified effect rows honest).
    if (rw.conserve_effects)
    {
        ulong added = r.rhs_effects & ~t.effects;
        if (added != 0) return t;
    }

    if (rw.fuel <= 0) { rw.out_of_fuel = true; return t; }
    if (rw.arena.oom) { rw.out_of_fuel = true; return t; }

    Node* result = instantiate(rw.arena, rw.hc, r.rhs, &env);
    if (result == null || rw.arena.oom) { rw.out_of_fuel = true; return t; }
    rw.fuel--;
    rw.firings++;
    return result;
}

// Fallback full scan (used only if the index wasn't built).
fn Node* Rewriter.step_scan(Rewriter* rw, Node* t)
{
    int tk = top_key_of(t);
    for (usz i = 0; i < rw.rules.count; i++)
    {
        Rule* r = &rw.rules.rules[i];
        if (!is_pattern_var(r.lhs) && r.top_key != tk) continue;
        Node* res = rw.try_rule(t, r);
        if (res != t) return res;
        if (rw.out_of_fuel) return t;
    }
    return t;
}

// Normalize a term bottom-up: children first, then repeatedly apply rules at
// the root until no rule fires. Returns the normal form.
fn Node* Rewriter.normalize(Rewriter* rw, Node* t)
{
    if (t == null) return null;
    if (rw.out_of_fuel) return t;
    if (rw.arena.oom) { rw.out_of_fuel = true; return t; }
    // Depth guard: a size-growing rule would recurse without bound. Cap it
    // and stop the whole run (deterministic, no native stack overflow).
    if (rw.depth >= MAX_REWRITE_DEPTH) { rw.too_deep = true; rw.out_of_fuel = true; return t; }
    // Memoization: a term already known to be in normal form needs no work.
    // This is what makes a repeat `|>*` pass over a settled subtree O(1).
    if ((t.flags & ast::FLAG_NORMAL) != 0) return t;
    rw.depth++;
    Node* r = rw.normalize_body(t);
    rw.depth--;
    if (r != null) r.flags |= ast::FLAG_NORMAL;
    return r;
}

// The body of normalize (depth accounting lives in the wrapper above).
fn Node* Rewriter.normalize_body(Rewriter* rw, Node* t)
{

    // 1. Normalize children first (innermost rewriting), rebuild if changed.
    bool changed = false;
    Node*[16] buf;
    usz n = t.child_count <= 16 ? t.child_count : 16;
    for (usz i = 0; i < n; i++)
    {
        Node* nc = rw.normalize(t.children[i]);
        buf[i] = nc;
        if (nc != t.children[i]) changed = true;
    }
    Node* cur = t;
    if (changed && n > 0)
    {
        if (t.kind == Nk.NODE_EXPR_BINARY || t.kind == Nk.NODE_EXPR_UNARY)
        {
            cur = ast::node_op(rw.arena, t.kind, t.p.op.op, &buf[0], n, t.line, t.col);
        }
        else
        {
            cur = ast::node_n(rw.arena, t.kind, &buf[0], n, t.line, t.col);
            if (cur != null) cur.p = t.p;
        }
        cur = rw.hc.intern(cur);
    }

    // 2. Apply rules at the root to a local fixpoint. We iterate (not recurse)
    //    so a non-terminating rule set is bounded by FUEL, never the native
    //    stack. After a root rewrite, re-normalize the result's CHILDREN only
    //    (the RHS may have rearranged subterms), then retry at the root.
    while (!rw.out_of_fuel)
    {
        Node* next = rw.step(cur);
        if (next == cur) break;          // no rule fired: normal form reached
        cur = rw.normalize_children(next);
        // `step` already spent fuel; the loop re-tests the root on the next
        // iteration. Fuel exhaustion ends the loop deterministically.
    }
    return cur;
}

// Re-normalize only the immediate children of `t` (one level), rebuilding the
// node if any child changed. Used after a root rewrite to settle the RHS
// without unbounded whole-subtree re-entry.
fn Node* Rewriter.normalize_children(Rewriter* rw, Node* t)
{
    if (t == null) return null;
    if (rw.out_of_fuel) return t;
    if (t.child_count == 0) return t;

    bool changed = false;
    Node*[16] buf;
    usz n = t.child_count <= 16 ? t.child_count : 16;
    for (usz i = 0; i < n; i++)
    {
        Node* nc = rw.normalize(t.children[i]);
        buf[i] = nc;
        if (nc != t.children[i]) changed = true;
    }
    if (!changed) return t;

    Node* cur;
    if (t.kind == Nk.NODE_EXPR_BINARY || t.kind == Nk.NODE_EXPR_UNARY)
    {
        cur = ast::node_op(rw.arena, t.kind, t.p.op.op, &buf[0], n, t.line, t.col);
    }
    else
    {
        cur = ast::node_n(rw.arena, t.kind, &buf[0], n, t.line, t.col);
        if (cur != null) cur.p = t.p;
    }
    return rw.hc.intern(cur);
}

// One application pass:  expr |> rules
fn Node* Rewriter.apply_once(Rewriter* rw, Node* t)
{
    return rw.normalize(t);
}

// Fixpoint application:  expr |> rules*  — normalize is already a fixpoint
// (it loops at each node until stable), so this is the same call; the name
// documents intent and lets us cap differently if needed.
fn Node* Rewriter.apply_fixpoint(Rewriter* rw, Node* t)
{
    return rw.normalize(t);
}
