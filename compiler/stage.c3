// ============================================================================
// stage.c3 — Staging: quote / splice / eval / comptime (CTFE)
// ----------------------------------------------------------------------------
// Implementation language: C3 (host). MSP Step 6.
//
// IMPORTANT — this is NOT a runtime interpreter. Pride is AOT-compiled. Staging
// is COMPILE-TIME metaprogramming: the "interpreter" here runs *inside the
// compiler* during the MSP stage to evaluate `comptime`/`eval` expressions and
// fold quoted code, then BAKES the result back into the AST as ordinary literal
// nodes. Nothing in this file emits or runs target code. This is exactly what
// `constexpr` (C++), `comptime` (Zig) and `const fn` (Rust) do: a compiled
// language still needs a small evaluator at *compile time*. We call it CTFE
// (compile-time function evaluation).
//
// The MetaOCaml-style operator trio Pride mirrors:
//
//   bracket  ~Tree e / quote e   →  freeze e as a code value (DON'T evaluate)
//   escape   splice e / unquote  →  run e now, graft its result into the quote
//   run      eval e / comptime   →  evaluate the quoted/normal AST at comp time
//
// Two responsibilities, both at compile time:
//
//   1. LEVEL CHECK — a quotation-level counter. `quote`/`~Tree` raise the level;
//      `splice`/`unquote` lower it. An escape at level 0 (no enclosing bracket)
//      is a staging error. This is the classic well-stagedness check.
//
//   2. CTFE — a small UNTYPED evaluator over the AST: literals, arithmetic,
//      comparisons, boolean/`if`, `let` bindings, and calls to other comptime
//      functions are folded to a value node. A `comptime` block is REPLACED by
//      that value; `eval e` likewise. `splice e` inside a quote is evaluated and
//      grafted in. Anything the evaluator can't reduce is left intact (soft:
//      partial evaluation, not a hard error) so the rest of the pipeline still
//      sees a well-formed tree.
// ============================================================================

module stage;

import lexer;
import ast;

// C runtime functions for compile-time macro evaluation
extern fn char* getenv(char* name);

extern fn int   printf(char* fmt, ...);

alias Node = ast::AstNode;
alias Nk = ast::NodeKind;
alias Tt = lexer::TokenType;

const usz MAX_DIAGS    = 512;
const usz ENV_CAP      = 4096;
const int EVAL_FUEL    = 200000;   // total reduction steps per run
const int EVAL_MAX_DEPTH = 600;    // recursion guard (native stack)
const int WALK_MAX_DEPTH = 1200;   // tree-walk recursion guard (level/transform)
const int LOOP_MAX_ITERS = 1000000; // per-loop iteration cap (non-termination)

// Control-flow signals for the expression-based CTFE evaluator.
const int FLOW_NONE     = 0;
const int FLOW_RETURN   = 1;
const int FLOW_BREAK    = 2;
const int FLOW_CONTINUE = 3;
const usz MAX_CT_FNS   = 4096;

struct StageDiag { char* msg; int line; int col; bool is_error; }

// A compile-time binding: a name bound to an already-reduced value node.
struct CtBinding { char* name_ptr; usz name_len; Node* value; }

// A registered comptime-callable function (top-level fn the evaluator may call).
struct CtFn { char* name_ptr; usz name_len; Node* decl; }

struct Stager
{
    ast::AstArena* arena;

    StageDiag[MAX_DIAGS] diags;
    int    diag_count;

    // CTFE environment (a scoped stack of name→value bindings).
    CtBinding[ENV_CAP] env;
    usz    env_count;

    // comptime-callable functions, collected up front.
    CtFn[MAX_CT_FNS]   fns;
    usz    fn_count;

    int    quote_level;     // current quotation nesting (level check)
    int    fuel;            // remaining reduction steps
    int    depth;           // current eval recursion depth
    int    walk_depth;      // current tree-walk recursion depth (level/transform)
    usz    frame_base;      // lexical isolation: lookup stops at this env index

    // Control-flow signal raised during CTFE of a function body. The evaluator
    // is expression-based, so `return`/`break`/`continue` set `flow` and a
    // value; callers check it to unwind. FLOW_NONE = normal completion.
    int    flow;            // FLOW_NONE / FLOW_RETURN / FLOW_BREAK / FLOW_CONTINUE
    Node*  flow_val;        // value carried by a `return`
    bool   stuck;           // set when CTFE hits something it cannot reduce; the
                            //   in-progress comptime fold is then abandoned (sound)

    bool   out_of_fuel;
    bool   too_deep;

    // stats
    int    folded;          // comptime/eval blocks replaced by a value
    int    splices;         // splices evaluated
    bool   overflow;
}

// ── Setup ────────────────────────────────────────────────────────────────────
fn void Stager.init(Stager* s, ast::AstArena* arena)
{
    s.arena = arena;
    s.diag_count = 0;
    s.env_count = 0;
    s.fn_count = 0;
    s.quote_level = 0;
    s.fuel = EVAL_FUEL;
    s.depth = 0;
    s.walk_depth = 0;
    s.frame_base = 0;
    s.flow = FLOW_NONE;
    s.flow_val = null;
    s.stuck = false;
    s.out_of_fuel = false;
    s.too_deep = false;
    s.folded = 0;
    s.splices = 0;
    s.overflow = false;
}

fn void Stager.diag(Stager* s, char* msg, int line, int col, bool is_error)
{
    if ((usz)s.diag_count >= MAX_DIAGS) return;
    StageDiag* d = &s.diags[s.diag_count];
    s.diag_count++;
    d.msg = msg;
    d.line = line;
    d.col = col;
    d.is_error = is_error;
}

fn int Stager.error_count(Stager* s)
{
    int e = 0;
    for (int i = 0; i < s.diag_count; i++) { if (s.diags[i].is_error) e++; }
    return e;
}

// ── name helpers ─────────────────────────────────────────────────────────────
fn bool name_eq(char* a, usz alen, char* b, usz blen)
{
    if (alen != blen) return false;
    for (usz i = 0; i < alen; i++) { if (a[i] != b[i]) return false; }
    return true;
}

// ── CTFE environment ─────────────────────────────────────────────────────────
fn usz Stager.env_mark(Stager* s) { return s.env_count; }
fn void Stager.env_reset(Stager* s, usz mark) { s.env_count = mark; }

fn void Stager.env_push(Stager* s, char* nptr, usz nlen, Node* value)
{
    if (s.env_count >= ENV_CAP) { s.overflow = true; return; }
    s.env[s.env_count].name_ptr = nptr;
    s.env[s.env_count].name_len = nlen;
    s.env[s.env_count].value = value;
    s.env_count++;
}

fn Node* Stager.env_lookup(Stager* s, char* nptr, usz nlen)
{
    // Lookup stops at frame_base so a callee can't see the caller's locals
    // (lexical, not dynamic, scoping). frame_base is 0 at the top level.
    usz i = s.env_count;
    while (i > s.frame_base)
    {
        i--;
        if (name_eq(s.env[i].name_ptr, s.env[i].name_len, nptr, nlen)) return s.env[i].value;
    }
    return null;
}

// Update an existing binding in place (for `mut` assignment). Returns true if a
// binding was found within the current frame; false otherwise (caller decides).
fn bool Stager.env_set(Stager* s, char* nptr, usz nlen, Node* value)
{
    usz i = s.env_count;
    while (i > s.frame_base)
    {
        i--;
        if (name_eq(s.env[i].name_ptr, s.env[i].name_len, nptr, nlen))
        {
            s.env[i].value = value;
            return true;
        }
    }
    return false;
}

// ── comptime fn registry ─────────────────────────────────────────────────────
fn void Stager.collect_fns(Stager* s, Node* program)
{
    if (program == null) return;
    for (usz i = 0; i < program.child_count; i++)
    {
        Node* n = program.children[i];
        if (n != null && n.kind == Nk.NODE_DECL_FN) s.add_fn(n);
    }
}

fn void Stager.add_fn(Stager* s, Node* fn_node)
{
    // first Ident child = name
    for (usz i = 0; i < fn_node.child_count; i++)
    {
        Node* c = fn_node.children[i];
        if (c != null && c.kind == Nk.NODE_IDENT)
        {
            if (s.fn_count >= MAX_CT_FNS) { s.overflow = true; return; }
            s.fns[s.fn_count].name_ptr = c.p.ident.name_ptr;
            s.fns[s.fn_count].name_len = c.p.ident.name_len;
            s.fns[s.fn_count].decl = fn_node;
            s.fn_count++;
            return;
        }
    }
}

fn Node* Stager.find_fn(Stager* s, char* nptr, usz nlen)
{
    for (usz i = 0; i < s.fn_count; i++)
    {
        if (name_eq(s.fns[i].name_ptr, s.fns[i].name_len, nptr, nlen)) return s.fns[i].decl;
    }
    return null;
}

// ── value predicates ─────────────────────────────────────────────────────────
fn bool is_value(Node* n)
{
    if (n == null) return false;
    switch (n.kind)
    {
        case Nk.NODE_LIT_INT:
        case Nk.NODE_LIT_FLOAT:
        case Nk.NODE_LIT_BOOL:
        case Nk.NODE_LIT_CHAR:
        case Nk.NODE_LIT_STRING:
            return true;
        default:
            return false;
    }
}

// ============================================================================
// CTFE — the compile-time evaluator (untyped, partial)
// ============================================================================
// Reduce `n` to a value node when possible; otherwise return the most-reduced
// form (so partial evaluation degrades gracefully). All new nodes are built in
// the arena. This runs ENTIRELY at compile time.
fn Node* Stager.eval(Stager* s, Node* n)
{
    if (n == null) return null;
    if (s.fuel <= 0) { s.out_of_fuel = true; return n; }
    if (s.depth > EVAL_MAX_DEPTH) { s.too_deep = true; return n; }
    s.depth++;
    Node* r = s.eval_body(n);
    s.depth--;
    return r;
}

fn Node* Stager.eval_body(Stager* s, Node* n)
{
    switch (n.kind)
    {
        case Nk.NODE_LIT_INT:
        case Nk.NODE_LIT_FLOAT:
        case Nk.NODE_LIT_BOOL:
        case Nk.NODE_LIT_CHAR:
        case Nk.NODE_LIT_STRING:
            return n;

        case Nk.NODE_IDENT:
            Node* v = s.env_lookup(n.p.ident.name_ptr, n.p.ident.name_len);
            if (v != null) return v;
            return n;   // free variable: leave symbolic

        case Nk.NODE_EXPR_BINARY:
            return s.eval_binary(n);

        case Nk.NODE_EXPR_UNARY:
            return s.eval_unary(n);

        case Nk.NODE_EXPR_IF:
            return s.eval_if(n);

        case Nk.NODE_EXPR_MATCH:
            return s.eval_match(n);

        case Nk.NODE_EXPR_WHILE:
            return s.eval_while(n);

        case Nk.NODE_EXPR_FOR:
            return s.eval_for(n);

        case Nk.NODE_EXPR_ASSIGN:
            return s.eval_assign(n);

        case Nk.NODE_STMT_RETURN:
            Node* rv = n.child_count >= 1 ? s.eval(n.children[0]) : null;
            if (s.flow == FLOW_NONE) { s.flow = FLOW_RETURN; s.flow_val = rv; }
            return rv != null ? rv : n;

        case Nk.NODE_STMT_BREAK:
            if (s.flow == FLOW_NONE) s.flow = FLOW_BREAK;
            return n;

        case Nk.NODE_STMT_CONTINUE:
            if (s.flow == FLOW_NONE) s.flow = FLOW_CONTINUE;
            return n;

        case Nk.NODE_EXPR_BLOCK:
            return s.eval_block(n);

        case Nk.NODE_STMT_EXPR:
            Node* last = n;
            for (usz i = 0; i < n.child_count; i++)
            {
                Node* c = n.children[i];
                if (c == null || is_type_or_row(c)) continue;
                last = s.eval(c);
                if (s.flow != FLOW_NONE) return last;
            }
            return last;

        case Nk.NODE_EXPR_CALL:
            return s.eval_call(n);

        // ── Compile-time macros ──────────────────────────────────────────────
        case Nk.NODE_EXPR_ENV_VAR:
            {
                // env!("VAR") — read env var at compile time; produce string literal.
                Node* arg = n.child_count >= 1 ? n.children[0] : null;
                if (arg != null && arg.kind == Nk.NODE_LIT_STRING)
                {
                    char* var_name = arg.p.ident.name_ptr;
                    usz   var_len  = arg.p.ident.name_len;
                    // Make null-terminated copy
                    char[256] vbuf;
                    usz vl = var_len < 255 ? var_len : 255;
                    for (usz vi = 0; vi < vl; vi++) vbuf[vi] = var_name[vi];
                    vbuf[vl] = 0;
                    char* env_val = getenv(&vbuf[0]);
                    if (env_val != null)
                    {
                        usz ev_len = 0; while (env_val[ev_len]) ev_len++;
                        Node* str_node = ast::node_str(s.arena, Nk.NODE_LIT_STRING,
                                                       env_val, ev_len, n.line, n.col);
                        return str_node != null ? str_node : n;
                    }
                }
                return n;  // not foldable
            }
        case Nk.NODE_EXPR_CONCAT:
            {
                // concat!("a", "b") — fold to a single string literal at compile time.
                // (Simple 2-arg version — multi-arg: would need variadic parse support.)
                Node* arg = n.child_count >= 1 ? n.children[0] : null;
                // Concatenation is handled by the call site; return as-is for multi-arg.
                return n;
            }
        case Nk.NODE_EXPR_INCLUDE_BYTES:
            // include_bytes!("file") — file embedding at compile time.
            // Full implementation requires libc fopen/fread wiring.
            // Returns the node as-is (not yet foldable at this stage);
            // codegen will emit it as an empty string placeholder.
            return n;

        // staging operators encountered during evaluation
        case Nk.NODE_EVAL:
        case Nk.NODE_COMPTIME:
        case Nk.NODE_RUNTIME:
        case Nk.NODE_STAGE:
        case Nk.NODE_META:
            if (n.child_count >= 1) return s.eval(n.children[0]);
            return n;

        case Nk.NODE_SPLICE:
        case Nk.NODE_UNQUOTE:
            if (n.child_count >= 1) return s.eval(n.children[0]);
            return n;

        case Nk.NODE_REIFY:
            // reify lifts a comptime value to a constant node: just evaluate.
            if (n.child_count >= 1) return s.eval(n.children[0]);
            return n;

        default:
            return n;   // not reducible by CTFE: leave intact
    }
}

fn Node* Stager.eval_binary(Stager* s, Node* n)
{
    if (n.child_count < 2) return n;
    Node* l = s.eval(n.children[0]);
    Node* r = s.eval(n.children[1]);

    // short-circuit boolean operators
    Tt op = n.p.op.op;
    if (l != null && l.kind == Nk.NODE_LIT_BOOL)
    {
        if (op == Tt.TOKEN_AMPAMP || op == Tt.TOKEN_KW_AND)
        {
            if (!l.p.lit_bool.bool_val) return l;   // false && _ = false
            if (r != null && r.kind == Nk.NODE_LIT_BOOL) return r;
        }
        if (op == Tt.TOKEN_PIPEPIPE || op == Tt.TOKEN_KW_OR)
        {
            if (l.p.lit_bool.bool_val) return l;     // true || _ = true
            if (r != null && r.kind == Nk.NODE_LIT_BOOL) return r;
        }
    }

    // constant fold via the AST folder (handles int + bool arithmetic/compare)
    if (is_value(l) && is_value(r))
    {
        Node* folded = ast::fold_binary(s.arena, op, l, r, n.line, n.col);
        if (folded != null) return folded;
    }

    // not foldable: rebuild with reduced operands (partial evaluation)
    return ast::node_binary(s.arena, op, l, r, n.line, n.col);
}

fn Node* Stager.eval_unary(Stager* s, Node* n)
{
    if (n.child_count < 1) return n;
    Node* o = s.eval(n.children[0]);
    Tt op = n.p.op.op;
    if (o != null && o.kind == Nk.NODE_LIT_INT)
    {
        if (op == Tt.TOKEN_MINUS)
        {
            ulong v = (ulong)(0) - o.p.lit_int.int_val;
            return ast::node_int(s.arena, v, o.p.lit_int.bits, o.p.lit_int.is_signed, n.line, n.col);
        }
        if (op == Tt.TOKEN_PLUS) return o;
    }
    if (o != null && o.kind == Nk.NODE_LIT_BOOL)
    {
        if (op == Tt.TOKEN_BANG || op == Tt.TOKEN_NEGATION)
        {
            return ast::node_bool(s.arena, !o.p.lit_bool.bool_val, n.line, n.col);
        }
    }
    return ast::node_unary(s.arena, op, o, n.line, n.col);
}

// if [cond, σ, then, (else)?, φ] — evaluate the taken branch when cond is known.
fn Node* Stager.eval_if(Stager* s, Node* n)
{
    if (n.child_count < 1) return n;
    Node* cond = s.eval(n.children[0]);

    // locate then / else (skip σ/φ markers)
    Node* then_b = null;
    Node* else_b = null;
    for (usz i = 1; i < n.child_count; i++)
    {
        Node* c = n.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_SIGMA || c.kind == Nk.NODE_PHI) continue;
        if (then_b == null) { then_b = c; } else { else_b = c; }
    }

    if (cond != null && cond.kind == Nk.NODE_LIT_BOOL)
    {
        if (cond.p.lit_bool.bool_val) return then_b != null ? s.eval(then_b) : n;
        return else_b != null ? s.eval(else_b) : ast::node_bool(s.arena, false, n.line, n.col);
    }
    // Condition not statically known: we cannot pick a branch. Mark the fold
    // stuck so the enclosing comptime call refuses to (mis)fold.
    s.stuck = true;
    return n;
}

// assignment  lhs = rhs : update a mutable binding in place. Only bare idents
// are tracked; anything else (field/index store) marks the fold stuck.
fn Node* Stager.eval_assign(Stager* s, Node* n)
{
    Node* lhs = n.child_count >= 1 ? n.children[0] : null;
    Node* rhs = n.child_count >= 2 ? n.children[1] : null;
    Node* val = rhs != null ? s.eval(rhs) : null;
    if (lhs != null && lhs.kind == Nk.NODE_IDENT && val != null)
    {
        if (!s.env_set(lhs.p.ident.name_ptr, lhs.p.ident.name_len, val)) s.stuck = true;
        return val;
    }
    s.stuck = true;
    return n;
}

// while cond { body } : iterate at compile time until the condition is false.
// Bounded by LOOP_MAX_ITERS and global fuel; break/continue honored.
fn Node* Stager.eval_while(Stager* s, Node* n)
{
    Node* cond = n.child_count >= 1 ? n.children[0] : null;
    Node* body = n.child_count >= 2 ? n.children[1] : null;
    int iters = 0;
    while (true)
    {
        if (s.fuel <= 0) { s.out_of_fuel = true; s.stuck = true; break; }
        if (iters >= LOOP_MAX_ITERS) { s.stuck = true; break; }
        s.fuel--;
        Node* c = cond != null ? s.eval(cond) : null;
        if (c == null || c.kind != Nk.NODE_LIT_BOOL) { s.stuck = true; break; }
        if (!c.p.lit_bool.bool_val) break;       // loop exits normally
        if (body != null) s.eval(body);
        if (s.flow == FLOW_BREAK) { s.flow = FLOW_NONE; break; }
        if (s.flow == FLOW_CONTINUE) { s.flow = FLOW_NONE; }
        else if (s.flow == FLOW_RETURN) { break; }   // propagate to caller
        iters++;
    }
    return ast::node0(s.arena, Nk.NODE_EXPR_UNIT, n.line, n.col);
}

// for x in lo..hi { body } : iterate x over an integer range at compile time.
fn Node* Stager.eval_for(Stager* s, Node* n)
{
    Node* pat   = n.child_count >= 1 ? n.children[0] : null;
    Node* iter  = n.child_count >= 2 ? n.children[1] : null;
    Node* body  = n.child_count >= 3 ? n.children[2] : null;

    // Only integer ranges are CTFE-iterable for now.
    if (iter == null || iter.kind != Nk.NODE_EXPR_RANGE || iter.child_count < 2)
    {
        s.stuck = true;
        return ast::node0(s.arena, Nk.NODE_EXPR_UNIT, n.line, n.col);
    }
    Node* lo = s.eval(iter.children[0]);
    Node* hi = s.eval(iter.children[1]);
    if (lo == null || lo.kind != Nk.NODE_LIT_INT || hi == null || hi.kind != Nk.NODE_LIT_INT)
    {
        s.stuck = true;
        return ast::node0(s.arena, Nk.NODE_EXPR_UNIT, n.line, n.col);
    }

    char* np; usz nl;
    pat_ident_name(pat, &np, &nl);
    bool inclusive = (iter.flags & ast::FLAG_RANGE_INCLUSIVE) != 0;

    // Signed iteration over [lo, hi) (or [lo, hi] if inclusive).
    long start = (long)lo.p.lit_int.int_val;
    long end   = (long)hi.p.lit_int.int_val;
    char bits = lo.p.lit_int.bits;
    bool sg = lo.p.lit_int.is_signed;

    int iters = 0;
    long v = start;
    while (inclusive ? (v <= end) : (v < end))
    {
        if (s.fuel <= 0) { s.out_of_fuel = true; s.stuck = true; break; }
        if (iters >= LOOP_MAX_ITERS) { s.stuck = true; break; }
        s.fuel--;

        // bind the loop variable fresh each iteration, then run the body
        usz mark = s.env_mark();
        if (np != null) s.env_push(np, nl, ast::node_int(s.arena, (ulong)v, bits, sg, n.line, n.col));
        if (body != null) s.eval(body);
        s.env_reset(mark);

        if (s.flow == FLOW_BREAK) { s.flow = FLOW_NONE; break; }
        if (s.flow == FLOW_CONTINUE) { s.flow = FLOW_NONE; }
        else if (s.flow == FLOW_RETURN) { break; }   // propagate to caller
        v++;
        iters++;
    }
    return ast::node0(s.arena, Nk.NODE_EXPR_UNIT, n.line, n.col);
}

// match scrut { | pat -> body ... } : pick the first arm whose pattern matches
// the statically-known scrutinee, then evaluate that arm's body.
fn Node* Stager.eval_match(Stager* s, Node* n)
{
    if (n.child_count < 1) { s.stuck = true; return n; }
    Node* scrut = s.eval(n.children[0]);
    if (!is_value(scrut)) { s.stuck = true; return n; }

    for (usz i = 1; i < n.child_count; i++)
    {
        Node* arm = n.children[i];
        if (arm == null || arm.kind != Nk.NODE_MATCH_ARM) continue;
        Node* pat = arm.child_count >= 1 ? arm.children[0] : null;

        usz mark = s.env_mark();
        bool ok = s.match_pattern(pat, scrut);
        if (ok)
        {
            // optional guard: arm children may include a PatGuard
            bool guard_ok = true;
            for (usz j = 1; j < arm.child_count; j++)
            {
                Node* c = arm.children[j];
                if (c != null && c.kind == Nk.NODE_PATTERN_GUARD && c.child_count >= 1)
                {
                    Node* g = s.eval(c.children[0]);
                    guard_ok = g != null && g.kind == Nk.NODE_LIT_BOOL && g.p.lit_bool.bool_val;
                    break;
                }
            }
            if (guard_ok)
            {
                // evaluate the arm body (children after pattern, skipping guard)
                Node* res = null;
                for (usz j = 1; j < arm.child_count; j++)
                {
                    Node* c = arm.children[j];
                    if (c == null || c.kind == Nk.NODE_PATTERN_GUARD) continue;
                    res = s.eval(c);
                    if (s.flow != FLOW_NONE) break;
                }
                s.env_reset(mark);
                return res != null ? res : n;
            }
        }
        s.env_reset(mark);
    }
    // No arm matched a known value: that is a non-exhaustive comptime match.
    s.stuck = true;
    return n;
}

// block: evaluate statements in sequence with their own scope; result = last.
// Honors control flow: a `return`/`break`/`continue` raised inside stops the
// block early (the signal propagates to the enclosing fn/loop handler).
fn Node* Stager.eval_block(Stager* s, Node* n)
{
    usz mark = s.env_mark();
    Node* last = null;
    for (usz i = 0; i < n.child_count; i++)
    {
        Node* c = n.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_DECL_LET || c.kind == Nk.NODE_DECL_MUT
            || c.kind == Nk.NODE_DECL_CONST || c.kind == Nk.NODE_DECL_STATIC)
        {
            s.eval_let(c);
            if (s.flow != FLOW_NONE) break;
            continue;
        }
        if (c.kind == Nk.NODE_CLAUSE)
        {
            // a single-clause body block: evaluate its body children
            last = s.eval_clause(c);
            if (s.flow != FLOW_NONE) break;
            continue;
        }
        last = s.eval(c);
        if (s.flow != FLOW_NONE) break;
    }
    // Local `let`s drop on block exit, but assignments to OUTER mutable vars
    // were applied in place via env_set, so they survive the reset.
    s.env_reset(mark);
    if (last == null) last = n;
    return last;
}

fn Node* Stager.eval_clause(Stager* s, Node* clause)
{
    Node* last = null;
    for (usz i = 0; i < clause.child_count; i++)
    {
        Node* c = clause.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_PATTERN_IDENT || c.kind == Nk.NODE_PATTERN_TUPLE
            || c.kind == Nk.NODE_PATTERN_WILDCARD || c.kind == Nk.NODE_PATTERN_LITERAL
            || c.kind == Nk.NODE_PATTERN_STRUCT || c.kind == Nk.NODE_PATTERN_OR
            || c.kind == Nk.NODE_PATTERN_GUARD) continue;
        last = s.eval(c);
        if (s.flow != FLOW_NONE) break;
    }
    // A `return` value is the clause result.
    if (s.flow == FLOW_RETURN && s.flow_val != null) return s.flow_val;
    return last;
}

// let pat = init  : bind a simple ident pattern to the evaluated initializer.
fn void Stager.eval_let(Stager* s, Node* d)
{
    Node* init = null;
    for (usz i = 1; i < d.child_count; i++)
    {
        Node* c = d.children[i];
        if (c != null && !is_type_or_row(c)) { init = s.eval(c); }
    }
    if (init == null) return;
    if (d.child_count >= 1)
    {
        Node* pat = d.children[0];
        char* np; usz nl;
        pat_ident_name(pat, &np, &nl);
        if (np != null) s.env_push(np, nl, init);
    }
}

// Call: only comptime-evaluate calls to known top-level fns with value args.
fn Node* Stager.eval_call(Stager* s, Node* n)
{
    if (n.child_count < 1) return n;
    Node* callee = n.children[0];
    if (callee == null || callee.kind != Nk.NODE_IDENT) return n;

    // evaluate arguments
    Node*[32] argv;
    usz argc = 0;
    for (usz i = 1; i < n.child_count && argc < 32; i++)
    {
        Node* a = n.children[i];
        if (a == null || is_type_or_row(a)) continue;
        argv[argc] = s.eval(a);
        argc++;
    }

    Node* decl = s.find_fn(callee.p.ident.name_ptr, callee.p.ident.name_len);
    if (decl == null) return n;   // unknown / extern: don't fold

    Node* body_block = null;
    for (usz i = 0; i < decl.child_count; i++)
    {
        Node* c = decl.children[i];
        if (c != null && c.kind == Nk.NODE_EXPR_BLOCK) { body_block = c; break; }
    }
    if (body_block == null) return n;

    // MULTI-CLAUSE DISPATCH: try each clause in order; the first whose parameter
    // pattern matches the (reduced) arguments AND whose guard holds is selected.
    // This is Prolog-style clause resolution done at compile time.
    //
    // LEXICAL ISOLATION: a callee sees only its own params (frame_base raised
    // above the caller's bindings). Both env length and frame_base are restored
    // on return so caller state is exactly preserved.
    usz mark = s.env_mark();
    usz saved_base = s.frame_base;
    s.frame_base = mark;

    Node* result = null;
    bool matched = false;
    for (usz i = 0; i < body_block.child_count; i++)
    {
        Node* clause = body_block.children[i];
        if (clause == null || clause.kind != Nk.NODE_CLAUSE) continue;

        usz cmark = s.env_mark();
        Node* pat = clause.child_count >= 1 ? clause.children[0] : null;
        if (!s.match_clause_params(pat, &argv[0], argc)) { s.env_reset(cmark); continue; }

        // guard, if present, must hold for this clause to be chosen
        bool guard_ok = true;
        for (usz j = 1; j < clause.child_count; j++)
        {
            Node* c = clause.children[j];
            if (c != null && c.kind == Nk.NODE_PATTERN_GUARD && c.child_count >= 1)
            {
                Node* g = s.eval(c.children[0]);
                guard_ok = g != null && g.kind == Nk.NODE_LIT_BOOL && g.p.lit_bool.bool_val;
                break;
            }
        }
        if (!guard_ok) { s.env_reset(cmark); continue; }

        matched = true;
        result = s.eval_clause(clause);
        // clear a RETURN that completed this clause (its value is the result)
        if (s.flow == FLOW_RETURN) { if (s.flow_val != null) result = s.flow_val; s.flow = FLOW_NONE; s.flow_val = null; }
        break;
    }

    s.frame_base = saved_base;
    s.env_reset(mark);
    if (matched && !s.stuck && result != null && is_value(result)) return result;
    return n;   // no clause matched, or body couldn't fully reduce: keep the call
}

// Match a clause's parameter pattern against the evaluated arguments, binding
// identifiers. A tuple pattern destructures the positional args; a single
// pattern matches the single arg. Returns true if every position matched.
fn bool Stager.match_clause_params(Stager* s, Node* pat, Node** args, usz argc)
{
    if (pat == null) return argc == 0;
    if (pat.kind == Nk.NODE_PATTERN_TUPLE)
    {
        if (pat.child_count != argc) return false;
        for (usz i = 0; i < pat.child_count; i++)
        {
            if (!s.match_pattern(pat.children[i], args[i])) return false;
        }
        return true;
    }
    if (argc != 1) return false;
    return s.match_pattern(pat, args[0]);
}

// Bind a parameter pattern (ident or tuple of idents) to argument values.
fn void Stager.bind_params(Stager* s, Node* pat, Node** args, usz argc)
{
    if (pat == null) return;
    if (pat.kind == Nk.NODE_PATTERN_TUPLE)
    {
        for (usz i = 0; i < pat.child_count && i < argc; i++)
        {
            char* np; usz nl;
            pat_ident_name(pat.children[i], &np, &nl);
            if (np != null) s.env_push(np, nl, args[i]);
        }
        return;
    }
    char* np; usz nl;
    pat_ident_name(pat, &np, &nl);
    if (np != null && argc >= 1) s.env_push(np, nl, args[0]);
}

// Match a pattern against a (reduced) value, binding any identifiers it
// introduces. Returns true on a match. Used by both `match` and multi-clause
// function dispatch. Only patterns CTFE can decide are handled; anything else
// returns false (the caller falls through / gets stuck).
fn bool Stager.match_pattern(Stager* s, Node* pat, Node* val)
{
    if (pat == null) return false;
    switch (pat.kind)
    {
        case Nk.NODE_PATTERN_WILDCARD:
            return true;

        case Nk.NODE_PATTERN_IDENT:
            // an identifier pattern always matches and binds the value
            char* np; usz nl;
            pat_ident_name(pat, &np, &nl);
            if (np != null) s.env_push(np, nl, val);
            return true;

        case Nk.NODE_PATTERN_LITERAL:
            // matches iff the literal equals the value (folded compare)
            if (pat.child_count < 1 || val == null) return false;
            Node* lit = s.eval(pat.children[0]);
            return values_equal(lit, val);

        case Nk.NODE_PATTERN_OR:
            // matches if any alternative matches (first one that does binds)
            for (usz i = 0; i < pat.child_count; i++)
            {
                usz mark = s.env_mark();
                if (s.match_pattern(pat.children[i], val)) return true;
                s.env_reset(mark);
            }
            return false;

        default:
            return false;   // tuple/struct destructuring of a scalar: not decidable
    }
}

// Structural equality of two literal value nodes (int/bool/char/float/string).
fn bool values_equal(Node* a, Node* b)
{
    if (a == null || b == null) return false;
    if (a.kind != b.kind) return false;
    switch (a.kind)
    {
        case Nk.NODE_LIT_INT:   return a.p.lit_int.int_val == b.p.lit_int.int_val;
        case Nk.NODE_LIT_BOOL:  return a.p.lit_bool.bool_val == b.p.lit_bool.bool_val;
        case Nk.NODE_LIT_CHAR:  return a.p.lit_char.char_val == b.p.lit_char.char_val;
        case Nk.NODE_LIT_FLOAT: return a.p.lit_float.f64_val == b.p.lit_float.f64_val;
        default:                return false;
    }
}

// ── name extraction helpers ──────────────────────────────────────────────────
fn void pat_ident_name(Node* pat, char** ptr, usz* len)
{
    *ptr = null; *len = 0;
    if (pat == null) return;
    Node* id = pat;
    if (pat.kind == Nk.NODE_PATTERN_IDENT && pat.child_count >= 1) id = pat.children[0];
    if (id != null && id.kind == Nk.NODE_IDENT) { *ptr = id.p.ident.name_ptr; *len = id.p.ident.name_len; }
}

fn bool is_type_or_row(Node* n)
{
    if (n == null) return true;
    switch (n.kind)
    {
        case Nk.NODE_TYPE_PRIMITIVE:
        case Nk.NODE_TYPE_PATH:
        case Nk.NODE_TYPE_PTR:
        case Nk.NODE_TYPE_REF:
        case Nk.NODE_TYPE_MUT_REF:
        case Nk.NODE_TYPE_ARRAY:
        case Nk.NODE_TYPE_SLICE:
        case Nk.NODE_TYPE_TUPLE:
        case Nk.NODE_TYPE_FN:
        case Nk.NODE_TYPE_UNION:
        case Nk.NODE_TYPE_INTERSECT:
        case Nk.NODE_TYPE_NEGATION:
        case Nk.NODE_TYPE_BOTTOM:
        case Nk.NODE_TYPE_FORALL:
        case Nk.NODE_TYPE_EXISTS:
        case Nk.NODE_TYPE_GENERIC_APP:
        case Nk.NODE_TYPE_REFINEMENT:
        case Nk.NODE_TYPE_TENSOR:
        case Nk.NODE_EFFECT_ROW:
            return true;
        default:
            return false;
    }
}

// ============================================================================
// Phase A — level check (well-stagedness)
// ============================================================================
// Walk the tree tracking quotation level. quote/~Tree raise; splice/unquote
// lower. An escape at level 0 is a staging error.
fn void Stager.level_check(Stager* s, Node* n)
{
    if (n == null) return;
    if (s.walk_depth > WALK_MAX_DEPTH) { s.too_deep = true; return; }
    s.walk_depth++;
    s.level_check_body(n);
    s.walk_depth--;
}

fn void Stager.level_check_body(Stager* s, Node* n)
{
    switch (n.kind)
    {
        case Nk.NODE_QUOTE:
        case Nk.NODE_SIGIL_TREE:
        case Nk.NODE_SIGIL_DATA:
        case Nk.NODE_SIGIL_BYTES:
        case Nk.NODE_STAGE:
            // A `stage` block produces next-stage code, so it is a quotation
            // context: splices inside it inject current-stage values and are
            // well-staged. (quote/~Tree/~Data/~Bytes are the explicit brackets.)
            s.quote_level++;
            for (usz i = 0; i < n.child_count; i++) s.level_check(n.children[i]);
            s.quote_level--;

        case Nk.NODE_SPLICE:
        case Nk.NODE_UNQUOTE:
            if (s.quote_level <= 0)
            {
                s.diag("splice/unquote outside a quotation (level underflow)", n.line, n.col, true);
            }
            s.quote_level--;
            for (usz i = 0; i < n.child_count; i++) s.level_check(n.children[i]);
            s.quote_level++;

        default:
            for (usz i = 0; i < n.child_count; i++) s.level_check(n.children[i]);
    }
}

// Run CTFE on `n` as an isolated evaluation: reset per-evaluation transient
// state (flow/stuck/depth), evaluate, then accept the result ONLY if the
// evaluation was clean (not stuck) and produced a value literal. This keeps one
// comptime fold from tainting another, and guarantees soundness: a partially-
// reducible body is left as source rather than silently mis-folded.
fn Node* Stager.ctfe_eval(Stager* s, Node* n)
{
    s.flow = FLOW_NONE;
    s.flow_val = null;
    s.stuck = false;
    s.depth = 0;
    Node* r = s.eval(n);
    if (s.stuck) return null;
    if (r != null && is_value(r)) return r;
    return null;
}

// ============================================================================
// Phase B — staging transform (fold comptime/eval; splice inside quotes)
// ============================================================================
// Rewrite the tree: a `comptime`/`eval` node is replaced by the CTFE value of
// its body; a `splice`/`unquote` INSIDE a quote is replaced by the CTFE value of
// its body (grafted into the surrounding code). Quoted bodies are otherwise NOT
// evaluated (that's the whole point of a bracket), except for their splices.
fn Node* Stager.transform(Stager* s, Node* n, int level)
{
    if (n == null) return null;
    if (s.walk_depth > WALK_MAX_DEPTH) { s.too_deep = true; return n; }
    s.walk_depth++;
    Node* r = s.transform_body(n, level);
    s.walk_depth--;
    return r;
}

fn Node* Stager.transform_body(Stager* s, Node* n, int level)
{
    switch (n.kind)
    {
        case Nk.NODE_COMPTIME:
        case Nk.NODE_EVAL:
            // run now: CTFE the body and replace.
            Node* body = n.child_count >= 1 ? n.children[0] : null;
            // splices inside the body are handled by recursing first
            Node* pre = body != null ? s.transform(body, level) : null;
            Node* val = pre != null ? s.ctfe_eval(pre) : null;
            if (val != null) { s.folded++; return val; }
            return n;

        case Nk.NODE_QUOTE:
        case Nk.NODE_SIGIL_TREE:
        case Nk.NODE_SIGIL_DATA:
        case Nk.NODE_SIGIL_BYTES:
        case Nk.NODE_STAGE:
            // inside a quote / stage block: don't evaluate the quoted body, but
            // DO process nested splices (which inject current-stage values).
            for (usz i = 0; i < n.child_count; i++)
            {
                n.children[i] = s.transform(n.children[i], level + 1);
            }
            return n;

        case Nk.NODE_SPLICE:
        case Nk.NODE_UNQUOTE:
            if (level > 0)
            {
                // graft: evaluate the spliced expr now and replace the splice.
                Node* body = n.child_count >= 1 ? n.children[0] : null;
                Node* inner = body != null ? s.transform(body, level - 1) : null;
                Node* val = inner != null ? s.ctfe_eval(inner) : null;
                if (val != null) { s.splices++; return val; }
                return inner != null ? inner : n;
            }
            // splice at top level (already diagnosed): just recurse.
            for (usz i = 0; i < n.child_count; i++) n.children[i] = s.transform(n.children[i], level);
            return n;

        default:
            for (usz i = 0; i < n.child_count; i++)
            {
                n.children[i] = s.transform(n.children[i], level);
            }
            return n;
    }
}

// ── Public driver ────────────────────────────────────────────────────────────
fn Node* Stager.run(Stager* s, Node* program)
{
    if (program == null) return program;
    s.collect_fns(program);
    s.level_check(program);
    return s.transform(program, 0);
}
