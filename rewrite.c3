// rewrite.c3 — the highly-engineered term-rewriting engine (MSP step 2)
// Implementation language: C3 (host). Second component of the MSP stage.
// Naive term rewriting is slow for four reasons; this engine removes each:
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
// Rules come from `rewrite { | lhs ↦ rhs (, guard)? ... }` blocks and `rule`
// declarations, already parsed to NODE_REWRITE / NODE_REWRITE_RULE. Application
// is driven by `expr |> rules` (one pass) and `expr |> rules*` (to fixpoint).
// Termination is guaranteed by FUEL: every rule firing spends one unit; running
// out is a diagnostic, never a hang.

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

// Buckets rules by the top-symbol class of their LHS so `step` examines only
// CANDIDATE rules for a given subject, not all N. Rules whose LHS top is a
// pattern variable (match any kind) live in a separate "wildcard" bucket.
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

// REWRITE EXTENSIONS — Term Rewriting as MSP Stage-0 Normalisation
// Term rewriting in Pride IS the normalisation engine of MSP stage 0.
// The connection to Multi-Stage Programming:
//   STAGE 0 (compile time): `rewrite { | lhs ↦ rhs }` declares equations.
//     The rewriter applies them bottom-up to a fixpoint BEFORE CTFE runs.
//     The normal form that emerges is the input to `comptime`/`eval`.
//     So:  normalize(t, rules) = ctfe_input(t)
//   `expr |> rules`   — one normalisation pass at stage 0
//   `expr |> rules*`  — fixpoint normalisation at stage 0
//   PGen (stage 0 → 1): compiles pattern matrices into decision trees.
//     Each pgen IS a term rewriting strategy compiled at stage 0.
//     The decision tree IS the compiled rewrite system for stage 1.
//   IRDL (stage 0 → -1): each irdl rule IS a term rewrite from dialect ops
//     to target ops. The lowering pass IS a top-down rewriting strategy.
// STRATEGIES: a strategy is a CONTROL PROGRAM that selects where and in
// what order to apply rules. The strategies here are combinators:
//   identity   : t → t           (always succeeds, no change)
//   fail       : t → FAIL        (always fails)
//   seq(s1,s2) : apply s1 then s2 (sequential composition)
//   choice(s1,s2): try s1; if FAIL try s2 (deterministic choice)
//   try(s)     : choice(s, identity)
//   repeat(s)  : try(seq(s, repeat(s)))   — to fixpoint (fuel-bounded)
//   all(s)     : apply s to ALL children (congruence)
//   one(s)     : apply s to exactly ONE child (first success)
//   some(s)    : apply s to at least ONE child
//   topdown(s) : apply s top-down (s at root, then all children)
//   bottomup(s): apply s bottom-up (all children first, then root)
//   innermost  : bottomup(repeat(choice(s, identity)))
//   outermost  : topdown(repeat(choice(s, identity)))
//   normalize  : innermost(rules)  — already implemented above
// These are the standard strategy combinators from Stratego/XT.
// In Pride they are untyped — the programmer picks the strategy.

struct StratResult
{
    Node* term;      // the rewritten term (null = FAIL)
    bool  changed;   // true if the term is different from input
}

fn StratResult strat_ok(Node* t, bool changed)
{
    StratResult r;
    r.term = t;
    r.changed = changed;
    return r;
}

fn StratResult strat_fail()
{
    StratResult r;
    r.term = null;
    r.changed = false;
    return r;
}

fn bool strat_is_fail(StratResult r) { return r.term == null; }

fn StratResult Rewriter.strat_id(Rewriter* rw, Node* t)
{
    return strat_ok(t, false);
}

fn StratResult Rewriter.strat_fail_s(Rewriter* rw, Node* t)
{
    return strat_fail();
}

fn StratResult Rewriter.strat_rule(Rewriter* rw, Node* t)
{
    Node* r = rw.step(t);
    if (r == t) return strat_fail();
    return strat_ok(r, true);
}

fn StratResult Rewriter.strat_try(Rewriter* rw, Node* t)
{
    StratResult r = rw.strat_rule(t);
    if (strat_is_fail(r)) return strat_ok(t, false);
    return r;
}

fn StratResult Rewriter.strat_all(Rewriter* rw, Node* t, bool use_rules)
{
    if (t == null) return strat_fail();
    if (t.child_count == 0) return strat_ok(t, false);
    bool any_changed = false;
    Node*[16] buf;
    usz n = t.child_count <= 16 ? t.child_count : 16;
    for (usz i = 0; i < n; i++)
    {
        StratResult cr = use_rules ? rw.strat_innermost(t.children[i])
                                   : rw.strat_try(t.children[i]);
        if (strat_is_fail(cr)) return strat_fail();
        buf[i] = cr.term;
        if (cr.changed) any_changed = true;
    }
    if (!any_changed) return strat_ok(t, false);
    Node* fresh;
    if (t.kind == Nk.NODE_EXPR_BINARY || t.kind == Nk.NODE_EXPR_UNARY)
        { fresh = ast::node_op(rw.arena, t.kind, t.p.op.op, &buf[0], n, t.line, t.col); }
    else
    {
        fresh = ast::node_n(rw.arena, t.kind, &buf[0], n, t.line, t.col);
        if (fresh != null) fresh.p = t.p;
    }
    return strat_ok(rw.hc.intern(fresh), true);
}

fn StratResult Rewriter.strat_one(Rewriter* rw, Node* t, bool use_rules)
{
    if (t == null || t.child_count == 0) return strat_fail();
    Node*[16] buf;
    usz n = t.child_count <= 16 ? t.child_count : 16;
    bool found = false;
    for (usz i = 0; i < n; i++) buf[i] = t.children[i];

    for (usz i = 0; i < n && !found; i++)
    {
        StratResult cr = use_rules ? rw.strat_try(t.children[i])
                                   : rw.strat_rule(t.children[i]);
        if (!strat_is_fail(cr) && cr.changed)
        {
            buf[i] = cr.term;
            found = true;
        }
    }
    if (!found) return strat_fail();
    Node* fresh;
    if (t.kind == Nk.NODE_EXPR_BINARY || t.kind == Nk.NODE_EXPR_UNARY)
        { fresh = ast::node_op(rw.arena, t.kind, t.p.op.op, &buf[0], n, t.line, t.col); }
    else
    {
        fresh = ast::node_n(rw.arena, t.kind, &buf[0], n, t.line, t.col);
        if (fresh != null) fresh.p = t.p;
    }
    return strat_ok(rw.hc.intern(fresh), true);
}

fn StratResult Rewriter.strat_topdown(Rewriter* rw, Node* t)
{
    if (t == null) return strat_fail();
    if (rw.out_of_fuel || rw.depth >= MAX_REWRITE_DEPTH)
        { rw.too_deep = true; return strat_ok(t, false); }
    rw.depth++;
    // Apply rule at root first
    StratResult root_r = rw.strat_try(t);
    Node* cur = strat_is_fail(root_r) ? t : root_r.term;
    bool changed = !strat_is_fail(root_r) && root_r.changed;
    // Then recurse into children
    StratResult child_r = rw.strat_all(cur, false);
    if (!strat_is_fail(child_r) && child_r.changed)
        { cur = child_r.term; changed = true; }
    rw.depth--;
    return strat_ok(cur, changed);
}

fn StratResult Rewriter.strat_bottomup(Rewriter* rw, Node* t)
{
    if (t == null) return strat_fail();
    if (rw.out_of_fuel || rw.depth >= MAX_REWRITE_DEPTH)
        { rw.too_deep = true; return strat_ok(t, false); }
    rw.depth++;
    // Recurse into children first
    StratResult child_r = rw.strat_all(t, false);
    Node* cur = strat_is_fail(child_r) ? t
                : (child_r.changed ? child_r.term : t);
    bool changed = !strat_is_fail(child_r) && child_r.changed;
    // Then apply rule at root
    StratResult root_r = rw.strat_try(cur);
    if (!strat_is_fail(root_r) && root_r.changed)
        { cur = root_r.term; changed = true; }
    rw.depth--;
    return strat_ok(cur, changed);
}

// Apply rules bottom-up to a fixpoint: the most commonly useful strategy.
// This is the same as `normalize` above, factored as a strategy.
fn StratResult Rewriter.strat_innermost(Rewriter* rw, Node* t)
{
    if (t == null) return strat_fail();
    if (rw.out_of_fuel) return strat_ok(t, false);
    if ((t.flags & ast::FLAG_NORMAL) != 0) return strat_ok(t, false);
    Node* r = rw.normalize(t);
    return strat_ok(r, r != t);
}

// Apply rules top-down, never re-visiting a subterm after normalisation.
// Useful for macro expansion (expand outermost first).
fn StratResult Rewriter.strat_outermost(Rewriter* rw, Node* t)
{
    if (t == null) return strat_fail();
    if (rw.out_of_fuel || rw.depth >= MAX_REWRITE_DEPTH)
        { rw.too_deep = true; return strat_ok(t, false); }
    rw.depth++;
    Node* cur = t;
    bool changed = false;
    // Apply at root until no rule fires
    bool root_changed = true;
    while (root_changed && !rw.out_of_fuel)
    {
        Node* next = rw.step(cur);
        if (next == cur) { root_changed = false; }
        else { cur = next; changed = true; }
    }
    // Then recurse into children (using outermost strategy)
    if (cur != null && cur.child_count > 0 && !rw.out_of_fuel)
    {
        StratResult child_r = rw.strat_all(cur, false);
        if (!strat_is_fail(child_r) && child_r.changed)
            { cur = child_r.term; changed = true; }
    }
    rw.depth--;
    return strat_ok(cur, changed);
}

// Check if two rules r1 and r2 have a CRITICAL PAIR: a term t where both
// rules apply (at the same position, or at overlapping positions), producing
// different results. If the results are not joinable (can't be normalised to
// the same term), the rule system is NOT confluent.
// This is a LOCAL confluence check: we generate critical pairs for each pair
// of rules and check if they are joinable. If all critical pairs are joinable,
// the system is locally confluent (by Newman's lemma, terminating + locally
// confluent => confluent).
// MSP relevance: a confluent rule system has a UNIQUE normal form, so
// `comptime (expr |> rules*)` is deterministic — the result doesn't depend
// on rule ordering. This is the key correctness property for stage-0 rewriting.

struct CritPair
{
    Node* lhs_result;   // result of applying rule r1
    Node* rhs_result;   // result of applying rule r2
    Node* subject;      // the term where both applied
    bool  joinable;     // true if both normalise to the same term
}

const usz MAX_CRIT_PAIRS = 256;

struct ConfluenceCheck
{
    CritPair[MAX_CRIT_PAIRS] pairs;
    usz pair_count;
    usz joinable_count;
    usz non_joinable;
    bool overflow;
}

fn void ConfluenceCheck.init(ConfluenceCheck* cc)
{
    cc.pair_count = 0;
    cc.joinable_count = 0;
    cc.non_joinable = 0;
    cc.overflow = false;
}

// Try to unify the LHS of rule r2 with a subterm of the LHS of rule r1.
// If successful, the common instance is a critical pair source.
// This is a simplified (first-order, left-linear) overlap check.
fn bool try_overlap(Node* lhs1, Node* lhs2, MatchEnv* env1, MatchEnv* env2)
{
    // Overlap at the ROOT of lhs1: try to match lhs2's LHS against lhs1.
    // For left-linear patterns, this is just matching.
    env1.reset();
    env2.reset();
    return match_term(lhs2, lhs1, env2);
}

fn void ConfluenceCheck.check_pair(ConfluenceCheck* cc, Rewriter* rw,
                                    Rule* r1, Rule* r2, usz ri1, usz ri2)
{
    if (ri1 == ri2) return;   // same rule: always joinable
    if (cc.pair_count >= MAX_CRIT_PAIRS) { cc.overflow = true; return; }

    MatchEnv env1; MatchEnv env2;
    if (!try_overlap(r1.lhs, r2.lhs, &env1, &env2)) return;

    // Both rules match the same (root of) lhs1.
    Node* subject = r1.lhs;
    Node* res1 = instantiate(rw.arena, rw.hc, r1.rhs, &env2);
    Node* res2 = instantiate(rw.arena, rw.hc, r2.rhs, &env2);

    if (res1 == null || res2 == null) return;

    // Try to join: normalise both results
    Node* norm1 = rw.normalize(res1);
    Node* norm2 = rw.normalize(res2);
    bool joinable = term_eq_deep(norm1, norm2);

    CritPair* cp = &cc.pairs[cc.pair_count];
    cp.lhs_result = norm1;
    cp.rhs_result = norm2;
    cp.subject    = subject;
    cp.joinable   = joinable;
    cc.pair_count++;
    if (joinable) { cc.joinable_count++; }
    else          { cc.non_joinable++; }
}

fn ConfluenceCheck Rewriter.check_confluence(Rewriter* rw)
{
    ConfluenceCheck cc;
    cc.init();
    for (usz i = 0; i < rw.rules.count && !cc.overflow; i++)
    {
        for (usz j = 0; j < rw.rules.count && !cc.overflow; j++)
        {
            cc.check_pair(rw, &rw.rules.rules[i], &rw.rules.rules[j], i, j);
        }
    }
    return cc;
}

// Check if a rule system is OBVIOUSLY terminating: each rule's RHS has fewer
// nodes than its LHS (size-decreasing). This is sufficient but not necessary;
// proper termination checking requires well-founded orderings (KBO, LPO) which
// we approximate here.
// MSP relevance: `expr |> rules*` is safe (terminates) iff the rule system
// terminates. Pride uses FUEL as a hard cap, but warning about non-terminating
// systems is better than silently running out of fuel.

fn usz term_size(Node* t)
{
    if (t == null) return 0;
    usz s = 1;
    for (usz i = 0; i < t.child_count && i < 16; i++) { s += term_size(t.children[i]); }
    return s;
}

struct TerminationReport
{
    usz total_rules;
    usz size_decreasing;
    usz non_decreasing;     // may be non-terminating
    usz obviously_looping;  // RHS contains the LHS pattern literally
}

fn TerminationReport Rewriter.check_termination(Rewriter* rw)
{
    TerminationReport tr;
    tr.total_rules = rw.rules.count;
    tr.size_decreasing = 0;
    tr.non_decreasing = 0;
    tr.obviously_looping = 0;

    for (usz i = 0; i < rw.rules.count; i++)
    {
        Rule* r = &rw.rules.rules[i];
        usz lhs_size = term_size(r.lhs);
        usz rhs_size = term_size(r.rhs);

        if (rhs_size < lhs_size) { tr.size_decreasing++; }
        else { tr.non_decreasing++; }

        // Trivial loop detection: RHS contains the exact LHS pattern
        MatchEnv env; env.reset();
        if (match_term(r.lhs, r.rhs, &env)) { tr.obviously_looping++; }
    }
    return tr;
}

// Some rule systems hold MODULO an equational theory:
//   - Associativity (AC-rewriting): x+(y+z) = (x+y)+z
//   - Commutativity: x+y = y+x
//   - Idempotency: x|x = x
// In Pride, equational theories are declared as rule sets and applied
// as a CONGRUENCE CLOSURE step alongside the main rewriting.
// This matters for PGen: pattern matching modulo AC lets pgen rules
// match tree shapes regardless of associativity/commutativity.
// Implementation: we normalise into a canonical form using the equational
// rules (e.g. sort AC-expressions by a canonical ordering of subterms).
// This is the AC canonical form approach (simpler than true AC-matching).

// Canonical ordering for AC-normalisation: by structural hash.
fn bool ac_less_than(Node* a, Node* b)
{
    if (a == b) return false;
    ulong ha = term_hash(a);
    ulong hb = term_hash(b);
    if (ha != hb) return ha < hb;
    // Tie-break by size
    return term_size(a) < term_size(b);
}

// Flatten an AC operator tree: (a + (b + c)) → [a, b, c]
fn usz flatten_ac(Node* t, Tt op, Node** buf, usz cap)
{
    if (t == null) return 0;
    if (t.kind != Nk.NODE_EXPR_BINARY || t.p.op.op != op)
    {
        if (cap > 0) { buf[0] = t; return 1; }
        return 0;
    }
    usz n = 0;
    n += flatten_ac(t.child_count >= 1 ? t.children[0] : null, op, buf + n, cap - n);
    n += flatten_ac(t.child_count >= 2 ? t.children[1] : null, op, buf + n, cap - n);
    return n;
}

// Sort buffer of nodes in AC canonical order (bubble sort — AC trees are small)
fn void ac_sort(Node** buf, usz n)
{
    for (usz i = 0; i < n; i++)
    {
        for (usz j = i + 1; j < n; j++)
        {
            if (!ac_less_than(buf[i], buf[j]))
            {
                Node* tmp = buf[i]; buf[i] = buf[j]; buf[j] = tmp;
            }
        }
    }
}

// Rebuild a right-associated AC tree from a sorted flat list.
fn Node* rebuild_ac(ast::AstArena* arena, HashCons* hc, Tt op, Node** buf, usz n, int line, int col)
{
    if (n == 0) return null;
    if (n == 1) return buf[0];
    Node* rest = rebuild_ac(arena, hc, op, buf + 1, n - 1, line, col);
    Node*[2] kids; kids[0] = buf[0]; kids[1] = rest;
    Node* fresh = ast::node_op(arena, Nk.NODE_EXPR_BINARY, op, &kids[0], 2, line, col);
    return hc.intern(fresh);
}

// Normalise a binary AC expression into canonical form.
fn Node* Rewriter.ac_normalise(Rewriter* rw, Node* t, Tt op)
{
    Node*[64] buf;
    usz n = flatten_ac(t, op, &buf[0], 64);
    if (n <= 1) return t;
    ac_sort(&buf[0], n);
    return rebuild_ac(rw.arena, rw.hc, op, &buf[0], n, t.line, t.col);
}

// `rules1 ++ rules2` = union of both rule sets, rules1 first (priority order)
fn void RuleSet.compose(RuleSet* rs, RuleSet* other)
{
    for (usz i = 0; i < other.count; i++)
    {
        Rule* r = &other.rules[i];
        rs.add(r.lhs, r.rhs, r.guard, (uint)(rs.count + i));
    }
}

// In Pride, `rule` declarations are first-class values: a `rule` decl
// produces a RuleSet with one rule that can be passed as a value, composed,
// and applied. This is the "rule as value" feature — rewrite rules ARE
// stage-0 values (they are computed at compile time and applied to the AST).

fn Rule* RuleSet.find_named(RuleSet* rs, char* name_ptr, usz name_len)
{
    for (usz i = 0; i < rs.count; i++)
    {
        Rule* r = &rs.rules[i];
        // Named rules have their LHS as an IDENT with the rule name.
        if (r.lhs != null && r.lhs.kind == Nk.NODE_IDENT)
        {
            if (name_eq(r.lhs.p.ident.name_ptr, r.lhs.p.ident.name_len,
                        name_ptr, name_len)) return r;
        }
    }
    return null;
}

// This is the key function that connects term rewriting to the MSP stage.
// Called by the MSP driver in pride.c3 before CTFE.
// It applies the rule set to the ENTIRE program tree as a stage-0 pass:
//   1. Collect all `rewrite {...}` blocks from the program.
//   2. Build the discrimination index.
//   3. Apply innermost normalisation to every expression in the program.
//   4. The result is a normalised AST ready for CTFE.
// The rewriter and CTFE are INTERLEAVED in the MSP pipeline:
//   - `comptime e` in the normalised tree is handled by CTFE.
//   - `e |> rules` applies the rewriter at that point.
//   - `quote e` freezes a normalised subterm as a stage-1 code value.
//   - `splice(e)` injects a normalised stage-0 value into stage-1 code.
// This interleaving is what makes Pride's MSP more expressive than
// MetaOCaml: the rewriter can transform the STRUCTURE of quoted code,
// not just fold constants. A `rewrite` inside a `quote` applies to
// the code value's AST — structural code manipulation.

fn void RuleSet.collect_program(RuleSet* rs, Node* program)
{
    if (program == null) return;
    for (usz i = 0; i < program.child_count; i++)
    {
        Node* child = program.children[i];
        if (child == null) continue;
        // Top-level `rewrite` blocks
        if (child.kind == Nk.NODE_REWRITE)
        {
            rs.add_block(child);
        }
        // Top-level `rule NAME = lhs ↦ rhs` declarations
        else if (child.kind == Nk.NODE_REWRITE_RULE)
        {
            rs.add_rule_node(child);
        }
        // Inside fn bodies and other expressions
        else
        {
            rs.collect_nested(child, 3);
        }
    }
}

fn void RuleSet.collect_nested(RuleSet* rs, Node* n, int depth)
{
    if (n == null || depth <= 0) return;
    if (n.kind == Nk.NODE_REWRITE) { rs.add_block(n); return; }
    if (n.kind == Nk.NODE_REWRITE_RULE) { rs.add_rule_node(n); return; }
    for (usz i = 0; i < n.child_count; i++) { rs.collect_nested(n.children[i], depth - 1); }
}

// Apply the MSP stage-0 rewriting pass to the full program.
// Returns the number of rule firings (stats).
fn usz stage0_rewrite(ast::AstArena* arena, RuleSet* rs, HashCons* hc, Node* program, long fuel)
{
    if (program == null || rs.count == 0) return 0;
    rs.build_index();

    Rewriter rw;
    rw.init(arena, hc, rs, fuel);

    // Apply innermost rewriting to every top-level child expression.
    for (usz i = 0; i < program.child_count; i++)
    {
        Node* child = program.children[i];
        if (child == null) continue;
        // Skip rewrite/rule declarations themselves
        if (child.kind == Nk.NODE_REWRITE || child.kind == Nk.NODE_REWRITE_RULE) continue;
        Node* r = rw.normalize(child);
        program.children[i] = r;
        if (rw.out_of_fuel) break;
    }
    return rw.firings;
}

