// effectcheck.c3 — Pride algebraic-effect checker
// Implementation language: C3 (host).
// Pipeline:  ... -> Resolver -> TypeChecker -> EffectChecker (this) -> ...
// Pride's core promise (v.md §1, §15, §22): "No hidden behavior." Every effect
// a function can perform must appear in its declared effect row `! [...]`.
// This pass:
//   1. Computes each fn's DECLARED effects from its `! [...]` row:
//        - builtin names  IO / Alloc / Unsafe / UB / Panic  -> a bitmask
//        - user effect names (e.g. State, Log) -> a set of effect-decl nodes
//        - an open tail `..r` -> the row is polymorphic (suppress "undeclared")
//   2. Computes each fn's ACTUAL effects by walking its body:
//        - builtin bits already OR-propagated by the parser (Alloc/UB/...)
//        - user effects from effect-operation calls  (Effect.op(...))
//        - effects of called functions (their declared rows)
//        - effects DISCHARGED by an enclosing `handle` are removed
//   3. CHECKS actual ⊆ declared. A performed-but-undeclared effect is a soft
//      warning (v.md §20.4 soft typing); `--strict` promotes it to an error.
//      `ub!` must surface as UB; `alloc`/`free` as Alloc; inline asm as Unsafe.
// NOTE: This pass deliberately does NOT analyse MSP / metaprogramming bodies
// (rewrite / pgen / comptime / quote / splice / eval). Per the vision, the MSP
// stage is untyped and unrestricted — it may perform arbitrary effects by
// design — so we skip effect enforcement inside those nodes.

module effectcheck;

import lexer;
import ast;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);

alias Node = ast::AstNode;
alias Nk = ast::NodeKind;

// A computed effect set: a builtin bitmask plus a list of user effect decls and
// an "open" flag (the row carried `..r`, so it admits any further effects).
const usz MAX_USER_EFFECTS = 64;

struct EffectSet
{
    ulong builtin;                       // OR of ast::EFFECT_* bits
    Node*[MAX_USER_EFFECTS] users;       // distinct effect-decl nodes
    usz   user_count;
    bool  open;                          // had a `..r` polymorphic tail
}

fn void EffectSet.clear(EffectSet* s)
{
    s.builtin = ast::EFFECT_PURE;
    s.user_count = 0;
    s.open = false;
}

fn void EffectSet.add_builtin(EffectSet* s, ulong bits)
{
    s.builtin |= bits;
}

fn void EffectSet.add_user(EffectSet* s, Node* eff_decl)
{
    if (eff_decl == null) return;
    for (usz i = 0; i < s.user_count; i++)
    {
        if (s.users[i] == eff_decl) return;   // already present
    }
    if (s.user_count < MAX_USER_EFFECTS)
    {
        s.users[s.user_count] = eff_decl;
        s.user_count++;
    }
}

fn bool EffectSet.has_user(EffectSet* s, Node* eff_decl)
{
    for (usz i = 0; i < s.user_count; i++)
    {
        if (s.users[i] == eff_decl) return true;
    }
    return false;
}

fn void EffectSet.union_with(EffectSet* dst, EffectSet* src)
{
    dst.builtin |= src.builtin;
    if (src.open) dst.open = true;
    for (usz i = 0; i < src.user_count; i++)
    {
        dst.add_user(src.users[i]);
    }
}

// One diagnostic.
struct EffectError
{
    char* msg;
    int   line;
    int   col;
    bool  is_error;
}

struct EffectChecker
{
    bool strict;

    EffectError[1024] diags;
    int diag_count;
    int error_count;
    int warning_count;

    // The declared effects of the function currently being checked, plus the
    // effects discharged by enclosing `handle` blocks (a stack of sets).
    EffectSet declared;
    EffectSet[64] handler_stack;   // effects handled by enclosing handles
    int handler_top;               // -1 when empty

    int gather_depth;              // recursion guard against deep expr trees
}

// Cap on effect-gathering recursion depth (degrade gracefully, never overflow).
const int EFFECT_MAX_DEPTH = 1200;

fn void EffectChecker.init(EffectChecker* self, bool strict)
{
    self.strict = strict;
    self.diag_count = 0;
    self.error_count = 0;
    self.warning_count = 0;
    self.handler_top = -1;
    self.gather_depth = 0;
}

fn void EffectChecker.diag(EffectChecker* self, char* msg, int line, int col)
{
    bool is_error = self.strict;
    if (is_error) { self.error_count++; }
    else { self.warning_count++; }

    if (self.diag_count < 1024)
    {
        EffectError e;
        e.msg = msg;
        e.line = line;
        e.col = col;
        e.is_error = is_error;
        self.diags[self.diag_count] = e;
        self.diag_count++;
    }
}

fn bool span_eq(char* p, usz len, char* lit, usz lit_len)
{
    if (len != lit_len) return false;
    for (usz i = 0; i < len; i++) if (p[i] != lit[i]) return false;
    return true;
}

// Map a builtin effect name to its bitmask, or 0 if it's a user effect name.
fn ulong builtin_effect_bit(char* p, usz len)
{
    if (span_eq(p, len, "IO", 2))     return ast::EFFECT_IO;
    if (span_eq(p, len, "Alloc", 5))  return ast::EFFECT_ALLOC;
    if (span_eq(p, len, "Unsafe", 6)) return ast::EFFECT_UNSAFE;
    if (span_eq(p, len, "UB", 2))     return ast::EFFECT_UB;
    if (span_eq(p, len, "Panic", 5))  return ast::EFFECT_PANIC;
    return 0;
}

fn char* builtin_effect_name(ulong bit)
{
    if (bit == ast::EFFECT_IO)     return "IO";
    if (bit == ast::EFFECT_ALLOC)  return "Alloc";
    if (bit == ast::EFFECT_UNSAFE) return "Unsafe";
    if (bit == ast::EFFECT_UB)     return "UB";
    if (bit == ast::EFFECT_PANIC)  return "Panic";
    return "?";
}

// A NODE_TYPE_FN may be  [arg, ret]  or  [innerFn, EffectRow]. Find the row.
fn Node* fn_effect_row(Node* sig)
{
    if (sig == null || sig.kind != Nk.NODE_TYPE_FN) return null;
    for (usz i = 0; i < sig.child_count; i++)
    {
        Node* c = sig.children[i];
        if (c != null && c.kind == Nk.NODE_EFFECT_ROW) return c;
    }
    return null;
}

// Parse a NODE_EFFECT_ROW into an EffectSet. Row children are EFFECT_REF
// (a named effect) and EFFECT_OPEN (the ..r tail).
fn void EffectChecker.read_row(EffectChecker* self, Node* row, EffectSet* out)
{
    out.clear();
    if (row == null) return;

    if ((row.flags & ast::FLAG_OPEN_ROW) != 0) out.open = true;

    for (usz i = 0; i < row.child_count; i++)
    {
        Node* ref = row.children[i];
        if (ref == null) continue;

        if (ref.kind == Nk.NODE_EFFECT_OPEN)
        {
            out.open = true;
            continue;
        }
        if (ref.kind != Nk.NODE_EFFECT_REF) continue;

        Node* name = ref.child_count >= 1 ? ref.children[0] : null;
        if (name == null) continue;

        // If the effect name resolves to a user `effect` declaration, treat it
        // as that user effect (so a row `! [IO]` and a call `IO.op` agree, even
        // when the user named their effect "IO"). Otherwise fall back to the
        // builtin bit for the well-known names.
        if (name.resolved != null && name.resolved.kind == Nk.NODE_DECL_EFFECT)
        {
            out.add_user(name.resolved);
            continue;
        }

        ulong bit = builtin_effect_bit(name.p.ident.name_ptr, name.p.ident.name_len);
        if (bit != 0)
        {
            out.add_builtin(bit);
        }
        else if (name.resolved != null)
        {
            // a user-defined effect (resolved to its `effect X` decl)
            out.add_user(name.resolved);
        }
        else
        {
            // unresolved effect name: treat as open so we don't false-warn.
            out.open = true;
        }
    }
}

// Locate a function's signature type node (NODE_TYPE_FN).
fn Node* fn_signature(Node* fn_node)
{
    for (usz i = 1; i < fn_node.child_count; i++)
    {
        Node* c = fn_node.children[i];
        if (c != null && c.kind == Nk.NODE_TYPE_FN) return c;
    }
    return null;
}

// An effect-op call looks like  Effect.op(args)  -> a MethodCall whose child 0
// (or a FIELD's base) resolves to a NODE_DECL_EFFECT. Returns that decl or null.
fn Node* effect_of_op_call(Node* call)
{
    if (call == null) return null;

    Node* base = null;
    if (call.kind == Nk.NODE_EXPR_METHOD_CALL && call.child_count >= 1)
    {
        base = call.children[0];
    }
    else if (call.kind == Nk.NODE_EXPR_FIELD && call.child_count >= 1)
    {
        base = call.children[0];
    }
    else
    {
        return null;
    }

    if (base != null && base.resolved != null
        && base.resolved.kind == Nk.NODE_DECL_EFFECT)
    {
        return base.resolved;
    }
    return null;
}

// A plain call  f(args)  -> the callee's fn declaration, if resolved.
fn Node* callee_fn_decl(Node* call)
{
    if (call == null || call.kind != Nk.NODE_EXPR_CALL) return null;
    if (call.child_count < 1) return null;
    Node* callee = call.children[0];
    if (callee != null && callee.resolved != null
        && callee.resolved.kind == Nk.NODE_DECL_FN)
    {
        return callee.resolved;
    }
    return null;
}

// Walk an expression/body subtree, accumulating the effects it performs into
// `acc`. `handled` are user-effect decls discharged by enclosing handlers.
fn void EffectChecker.gather(EffectChecker* self, Node* n, EffectSet* acc)
{
    if (n == null) return;
    if (self.gather_depth > EFFECT_MAX_DEPTH) return;
    self.gather_depth++;
    self.gather_body(n, acc);
    self.gather_depth--;
}

fn void EffectChecker.gather_body(EffectChecker* self, Node* n, EffectSet* acc)
{
    switch (n.kind)
    {
        case Nk.NODE_UB_BANG:
            acc.add_builtin(ast::EFFECT_UB);
            // operands (the message) carry nothing further

        case Nk.NODE_EXPR_POISON:
            acc.add_builtin(ast::EFFECT_UB);

        case Nk.NODE_EXPR_ALLOC:
        case Nk.NODE_EXPR_FREE:
            acc.add_builtin(ast::EFFECT_ALLOC);
            self.gather_children(n, acc);

        case Nk.NODE_STMT_ASM:
            acc.add_builtin(ast::EFFECT_UNSAFE);

        case Nk.NODE_EXPR_SYSCALL:
            // A raw kernel syscall is the project's own idiomatic way to do
            // I/O (see examples/*.pie, tests/exec/*.pie), so it must actually
            // be tracked by the effect checker, not silently treated as pure.
            acc.add_builtin(ast::EFFECT_IO);
            self.gather_children(n, acc);

        case Nk.NODE_STMT_ASSERT:
        case Nk.NODE_STMT_INVARIANT:
            acc.add_builtin(ast::EFFECT_PANIC);
            self.gather_children(n, acc);

        case Nk.NODE_EXPR_METHOD_CALL:
            Node* eff = effect_of_op_call(n);
            if (eff != null && !self.is_handled(eff))
            {
                acc.add_user(eff);
            }
            self.gather_children(n, acc);

        case Nk.NODE_EXPR_CALL:
            Node* fdecl = callee_fn_decl(n);
            if (fdecl != null)
            {
                self.add_fn_effects(fdecl, acc);
            }
            self.gather_children(n, acc);

        case Nk.NODE_EXPR_FIELD:
            // Effect.op used as a value (rare) — still a perform.
            Node* feff = effect_of_op_call(n);
            if (feff != null && !self.is_handled(feff)) acc.add_user(feff);
            self.gather_children(n, acc);

        case Nk.NODE_EFFECT_HANDLE:
            self.gather_handle(n, acc);

        case Nk.NODE_REWRITE:
        case Nk.NODE_REWRITE_RULE:
        case Nk.NODE_PGEN:
        case Nk.NODE_STAGE:
        case Nk.NODE_QUOTE:
        case Nk.NODE_SPLICE:
        case Nk.NODE_UNQUOTE:
        case Nk.NODE_REIFY:
        case Nk.NODE_EVAL:
        case Nk.NODE_COMPTIME:
        case Nk.NODE_RUNTIME:
        case Nk.NODE_FIXPOINT:
        case Nk.NODE_META:
        case Nk.NODE_GENERATE:
        case Nk.NODE_LOWER:
        case Nk.NODE_SIGIL_TREE:
        case Nk.NODE_SIGIL_DATA:
        case Nk.NODE_SIGIL_BYTES:
        case Nk.NODE_IRDL:
        case Nk.NODE_DIALECT:
            break;   // do not enforce effects inside MSP bodies

        case Nk.NODE_DECL_FN:
            break;

        default:
            self.gather_children(n, acc);
    }
}

fn void EffectChecker.gather_children(EffectChecker* self, Node* n, EffectSet* acc)
{
    for (usz i = 0; i < n.child_count; i++)
    {
        self.gather(n.children[i], acc);
    }
}

// `handle computation arms...` — the arms discharge the effects they match,
// so within the computation those user effects are considered handled.
fn void EffectChecker.gather_handle(EffectChecker* self, Node* h, EffectSet* acc)
{
    // Collect the user effects this handle discharges (from its arm op-heads).
    EffectSet discharged;
    discharged.clear();
    for (usz i = 0; i < h.child_count; i++)
    {
        Node* arm = h.children[i];
        if (arm == null || arm.kind != Nk.NODE_HANDLER_ARM) continue;
        Node* head = arm.child_count >= 1 ? arm.children[0] : null;
        // head is Effect.op (a FIELD) whose base resolves to the effect decl.
        if (head != null && head.kind == Nk.NODE_EXPR_FIELD && head.child_count >= 1)
        {
            Node* basis = head.children[0];
            if (basis != null && basis.resolved != null
                && basis.resolved.kind == Nk.NODE_DECL_EFFECT)
            {
                discharged.add_user(basis.resolved);
            }
        }
    }

    // Push the discharged set; gather the computation (child 0) and arm bodies
    // under that handler scope, then pop.
    self.push_handler(&discharged);

    for (usz i = 0; i < h.child_count; i++)
    {
        Node* c = h.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_HANDLER_ARM)
        {
            // arm bodies run *outside* their own discharge for the matched op,
            // but may perform other effects — gather the body (last child).
            if (c.child_count >= 1)
            {
                self.gather(c.children[c.child_count - 1], acc);
            }
        }
        else
        {
            // the computation being handled
            self.gather(c, acc);
        }
    }

    self.pop_handler();
}

// Add a called function's declared effects into the accumulator.
fn void EffectChecker.add_fn_effects(EffectChecker* self, Node* fn_decl, EffectSet* acc)
{
    Node* sig = fn_signature(fn_decl);
    Node* row = fn_effect_row(sig);
    if (row == null) return;   // pure function: contributes nothing

    EffectSet callee;
    self.read_row(row, &callee);

    // Builtin bits always propagate.
    acc.add_builtin(callee.builtin);
    if (callee.open) acc.open = true;
    // User effects propagate unless discharged by an enclosing handle.
    for (usz i = 0; i < callee.user_count; i++)
    {
        if (!self.is_handled(callee.users[i])) acc.add_user(callee.users[i]);
    }
}

fn void EffectChecker.push_handler(EffectChecker* self, EffectSet* discharged)
{
    if (self.handler_top + 1 < 64)
    {
        self.handler_top++;
        self.handler_stack[self.handler_top] = *discharged;
    }
}

fn void EffectChecker.pop_handler(EffectChecker* self)
{
    if (self.handler_top >= 0) self.handler_top--;
}

fn bool EffectChecker.is_handled(EffectChecker* self, Node* eff_decl)
{
    for (int i = self.handler_top; i >= 0; i--)
    {
        if (self.handler_stack[i].has_user(eff_decl)) return true;
    }
    return false;
}

fn void EffectChecker.check_program(EffectChecker* self, Node* program)
{
    if (program == null) return;
    self.walk_decls(program);
}

fn void EffectChecker.walk_decls(EffectChecker* self, Node* scope)
{
    for (usz i = 0; i < scope.child_count; i++)
    {
        Node* d = scope.children[i];
        if (d == null) continue;

        switch (d.kind)
        {
            case Nk.NODE_DECL_FN:
                self.check_fn(d);
            case Nk.NODE_DECL_MOD:
                for (usz j = 0; j < d.child_count; j++)
                {
                    Node* b = d.children[j];
                    if (b != null && b.kind == Nk.NODE_EXPR_BLOCK) self.walk_decls(b);
                }
            default:
                break;
        }
    }
}

// Check one function: actual effects ⊆ declared effects.
fn void EffectChecker.check_fn(EffectChecker* self, Node* fn_node)
{
    Node* sig = fn_signature(fn_node);
    Node* row = fn_effect_row(sig);

    EffectSet declared;
    self.read_row(row, &declared);

    // Gather the actual effects performed across all clause bodies.
    EffectSet actual;
    actual.clear();
    self.handler_top = -1;

    for (usz i = 0; i < fn_node.child_count; i++)
    {
        Node* c = fn_node.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_EXPR_BLOCK)
        {
            for (usz j = 0; j < c.child_count; j++)
            {
                Node* clause = c.children[j];
                if (clause == null) continue;
                if (clause.kind == Nk.NODE_CLAUSE && clause.child_count >= 1)
                {
                    // gather over the clause body (last child)
                    self.gather(clause.children[clause.child_count - 1], &actual);
                }
                else
                {
                    self.gather(clause, &actual);
                }
            }
        }
    }

    // Compare: each actual effect must be present in `declared` (unless the
    // declared row is open, which admits anything).
    self.report_missing(fn_node, &actual, &declared);

    // Recurse into nested fn declarations inside clause bodies.
    self.check_nested_fns(fn_node);
}

// Walk nested fn declarations (e.g. local helpers) and check them too.
fn void EffectChecker.check_nested_fns(EffectChecker* self, Node* n)
{
    self.check_nested_fns_d(n, 0);
}

fn void EffectChecker.check_nested_fns_d(EffectChecker* self, Node* n, int depth)
{
    if (depth > EFFECT_MAX_DEPTH) return;
    for (usz i = 0; i < n.child_count; i++)
    {
        Node* c = n.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_DECL_FN)
        {
            self.check_fn(c);
        }
        else
        {
            self.check_nested_fns_d(c, depth + 1);
        }
    }
}

// Emit a soft warning for every effect performed but not declared.
fn void EffectChecker.report_missing(EffectChecker* self, Node* fn_node, EffectSet* actual, EffectSet* declared)
{
    if (declared.open) return;   // polymorphic row admits any extra effect

    // Builtin bits.
    ulong missing = actual.builtin & ~declared.builtin;
    ulong probe = 1;
    for (int i = 0; i < 8; i++)
    {
        ulong bit = probe << (ulong)i;
        if ((missing & bit) != 0)
        {
            self.diag(undeclared_msg(bit), fn_node.line, fn_node.col);
        }
    }

    // User effects.
    for (usz i = 0; i < actual.user_count; i++)
    {
        if (!declared.has_user(actual.users[i]))
        {
            self.diag("performs an undeclared effect (add it to the function's ! [...] row)",
                fn_node.line, fn_node.col);
        }
    }
}

fn char* undeclared_msg(ulong bit)
{
    if (bit == ast::EFFECT_IO)     return "performs IO but does not declare ! [IO]";
    if (bit == ast::EFFECT_ALLOC)  return "allocates/frees but does not declare ! [Alloc]";
    if (bit == ast::EFFECT_UNSAFE) return "uses unsafe/asm but does not declare ! [Unsafe]";
    if (bit == ast::EFFECT_UB)     return "may trigger UB but does not declare ! [UB]";
    if (bit == ast::EFFECT_PANIC)  return "may panic but does not declare ! [Panic]";
    return "performs an undeclared builtin effect";
}
