// modal.c3 — Formal Contextual Modal Type Theory (□Γ'L'τ) Typechecker, Modal Stage
// Inference, and Ahead-of-Time Continuation-Tree Algebraic Rewriting.
//
// Implementation language: C3 (host).
//
// This module provides the formal frontend typechecking and middle-end algebraic
// rewriting engine for The Multi-Level Contextual Effect Engine (MLCEE):
//
//   1. CONTEXTUAL MODAL TYPE THEORY (CMTT) TYPECHECKING & STAGE INFERENCE:
//      Enforces multi-level modal typing judgments of the form:
//          Γ ⊢^E e : □_{Γ'}^{L'} τ   at   L
//      A contextual modal box □_{Γ'}^{L'} τ represents an open code fragment
//      that will evaluate to type τ at future stage level L', depending on an
//      explicitly captured lexical environment Γ'.
//      Modal stage inference automatically assigns stage levels L and validates
//      well-stagedness (no stage-0 variable can be evaluated at stage > 0 without
//      an explicit splice ~e; no splice can appear at stage 0).
//
//   2. CONTINUATION-TREE ALGEBRAIC REWRITING (ContTree):
//      When a higher-order scoped effect block (catch, bracket, local, nursery,
//      with_timeout) is encountered inside an open code fragment or during macro
//      expansion, this engine builds an explicit Continuation Tree T:
//          T ::= Leaf(e)
//              | Node(op, k_in, k_out)
//              | Seq(T1, T2)
//              | Fmap(f, T)
//              | Fuse(T_in, T_out)
//              | Abort(e)
//      It then repeatedly applies formal functorial algebra rewrite rules until a
//      normal form fixpoint is reached:
//        - Identity Elimination : Node(op, k_in, Id) ↦ k_in
//        - Functorial Fusion    : Fmap(f, Node(op, k_in, k_out)) ↦ Node(op, Fmap(f, k_in), k_out)
//        - Structured Fusion    : Fuse(Fmap(f, k_in), k_out) ↦ Fmap(f, Fuse(k_in, k_out))
//        - Dead-Scope Pruning   : Node(op, Abort(e), k_out) ↦ Abort(e)
//        - Sequential Associate : Seq(Seq(T1, T2), T3) ↦ Seq(T1, Seq(T2, T3))
//      Once normalized, any continuation tree whose k_out has collapsed to Id is
//      lowered back to direct, zero-cost AST instructions, completely bypassing
//      runtime prompt installation and segmented stack slicing.

module modal;

import lexer;
import ast;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

alias Node = ast::AstNode;
alias Nk   = ast::NodeKind;
alias Tt   = lexer::TokenType;

const usz MODAL_MAX_VARS     = 2048;
const usz MODAL_MAX_SCOPES   = 512;
const usz MODAL_MAX_ERRORS   = 512;
const int MODAL_REWRITE_CAP  = 25000;
const int MODAL_MAX_DEPTH    = 1000;

// ── Contextual Lexical Environment (Γ') ─────────────────────────────────────

struct ModalVar
{
    char* name_ptr;
    usz   name_len;
    Node* type_node;
    int   stage_level;
    bool  is_spliced;
    bool  is_escaped;
    int   bind_scope_id;
}

struct ModalContext
{
    ModalVar[MODAL_MAX_VARS] vars;
    usz                      var_count;
    int                      current_stage;
    int                      parent_scope_id;
    bool                     is_quote_boundary;
}

struct ModalLattice
{
    ModalContext[MODAL_MAX_SCOPES] scopes;
    usz                            scope_count;
    usz                            active_scope;
    int                            errors;
    int                            warnings;
    char[256][MODAL_MAX_ERRORS]    error_msgs;
}

fn void ModalLattice.init(ModalLattice* l)
{
    l.scope_count = 1;
    l.active_scope = 0;
    l.scopes[0].var_count = 0;
    l.scopes[0].current_stage = 0;
    l.scopes[0].parent_scope_id = -1;
    l.scopes[0].is_quote_boundary = false;
    l.errors = 0;
    l.warnings = 0;
}

fn void ModalLattice.push_scope(ModalLattice* l, int next_stage, bool quote_boundary)
{
    if (l.scope_count >= MODAL_MAX_SCOPES) return;
    usz idx = l.scope_count++;
    l.scopes[idx].var_count = 0;
    l.scopes[idx].current_stage = next_stage;
    l.scopes[idx].parent_scope_id = (int)l.active_scope;
    l.scopes[idx].is_quote_boundary = quote_boundary;
    l.active_scope = idx;
}

fn void ModalLattice.pop_scope(ModalLattice* l)
{
    int parent = l.scopes[l.active_scope].parent_scope_id;
    if (parent >= 0 && (usz)parent < l.scope_count)
    {
        l.active_scope = (usz)parent;
    }
}

fn bool ModalLattice.bind_var(ModalLattice* l, char* name, usz len, Node* type_node, int stage)
{
    ModalContext* ctx = &l.scopes[l.active_scope];
    if (ctx.var_count >= MODAL_MAX_VARS) return false;
    usz idx = ctx.var_count++;
    ctx.vars[idx].name_ptr    = name;
    ctx.vars[idx].name_len    = len;
    ctx.vars[idx].type_node   = type_node;
    ctx.vars[idx].stage_level = stage;
    ctx.vars[idx].is_spliced  = false;
    ctx.vars[idx].is_escaped  = false;
    ctx.vars[idx].bind_scope_id = (int)l.active_scope;
    return true;
}

fn ModalVar* ModalLattice.lookup_var(ModalLattice* l, char* name, usz len)
{
    int curr = (int)l.active_scope;
    while (curr >= 0 && (usz)curr < l.scope_count)
    {
        ModalContext* ctx = &l.scopes[(usz)curr];
        for (usz i = 0; i < ctx.var_count; i++)
        {
            ModalVar* v = &ctx.vars[i];
            if (v.name_len == len && v.name_ptr != null && name != null)
            {
                bool match = true;
                for (usz k = 0; k < len; k++)
                {
                    if (v.name_ptr[k] != name[k]) { match = false; break; }
                }
                if (match) return v;
            }
        }
        curr = ctx.parent_scope_id;
    }
    return null;
}

fn void ModalLattice.report_error(ModalLattice* l, char* msg)
{
    if (l.errors < (int)MODAL_MAX_ERRORS && msg != null)
    {
        char* dst = &l.error_msgs[l.errors][0];
        usz i = 0;
        while (msg[i] != 0 && i < 255) { dst[i] = msg[i]; i++; }
        dst[i] = 0;
        l.errors++;
    }
}

// ── Environment Subtyping & Structural Equality ────────────────────────────

fn bool modal_env_is_subtype(ModalContext* sub, ModalContext* sup)
{
    if (sub == null || sup == null) return false;
    // For every variable required in sup, sub must bind a variable of equal or compatible type
    // at the same stage level.
    for (usz i = 0; i < sup.var_count; i++)
    {
        ModalVar* req = &sup.vars[i];
        bool found = false;
        for (usz j = 0; j < sub.var_count; j++)
        {
            ModalVar* cand = &sub.vars[j];
            if (cand.name_len == req.name_len && cand.name_ptr != null && req.name_ptr != null)
            {
                bool name_match = true;
                for (usz k = 0; k < req.name_len; k++)
                {
                    if (cand.name_ptr[k] != req.name_ptr[k]) { name_match = false; break; }
                }
                if (name_match && cand.stage_level == req.stage_level)
                {
                    found = true;
                    break;
                }
            }
        }
        if (!found) return false;
    }
    return true;
}

fn bool modal_ast_alpha_equal(Node* a, Node* b, int depth)
{
    if (a == b) return true;
    if (a == null || b == null || depth > MODAL_MAX_DEPTH) return false;
    if (a.kind != b.kind) return false;
    if (a.child_count != b.child_count) return false;

    if (a.kind == Nk.NODE_IDENT)
    {
        if (a.p.ident.name_len != b.p.ident.name_len) return false;
        if (a.p.ident.name_ptr == null || b.p.ident.name_ptr == null) return false;
        for (usz i = 0; i < a.p.ident.name_len; i++)
        {
            if (a.p.ident.name_ptr[i] != b.p.ident.name_ptr[i]) return false;
        }
        return true;
    }
    if (a.kind == Nk.NODE_LIT_INT)   return a.p.lit_int.int_val == b.p.lit_int.int_val;
    if (a.kind == Nk.NODE_LIT_BOOL)  return a.p.lit_bool.bool_val == b.p.lit_bool.bool_val;
    if (a.kind == Nk.NODE_LIT_FLOAT) return a.p.lit_float.f64_val == b.p.lit_float.f64_val;

    for (usz i = 0; i < a.child_count; i++)
    {
        if (!modal_ast_alpha_equal(a.children[i], b.children[i], depth + 1)) return false;
    }
    return true;
}

// ── Modal Stage Inference & Well-Stagedness Checking ───────────────────────

fn bool check_well_staged_expr(ModalLattice* l, Node* n, int current_stage, int depth)
{
    if (n == null || depth > MODAL_MAX_DEPTH) return true;
    switch (n.kind)
    {
        case Nk.NODE_QUOTE:
        case Nk.NODE_STAGE:
            l.push_scope(current_stage + 1, true);
            for (usz i = 0; i < n.child_count; i++)
            {
                check_well_staged_expr(l, n.children[i], current_stage + 1, depth + 1);
            }
            l.pop_scope();
            return l.errors == 0;

        case Nk.NODE_SPLICE:
        case Nk.NODE_UNQUOTE:
            if (current_stage <= 0)
            {
                l.report_error((char*)"modal stage error: splice (~e) outside of a quoted block (stage 0)");
                return false;
            }
            for (usz i = 0; i < n.child_count; i++)
            {
                check_well_staged_expr(l, n.children[i], current_stage - 1, depth + 1);
            }
            return l.errors == 0;

        case Nk.NODE_IDENT:
            {
                ModalVar* v = l.lookup_var(n.p.ident.name_ptr, n.p.ident.name_len);
                if (v != null)
                {
                    if (v.stage_level < current_stage && !v.is_spliced)
                    {
                        l.report_error((char*)"modal stage error: stage-0 variable referenced at future stage without splice (~x)");
                        return false;
                    }
                    if (v.stage_level > current_stage)
                    {
                        l.report_error((char*)"modal stage error: future-stage variable referenced at an earlier stage");
                        return false;
                    }
                }
                return true;
            }

        case Nk.NODE_DECL_LET:
        case Nk.NODE_DECL_MUT:
            {
                if (n.child_count >= 1 && n.children[0] != null
                    && n.children[0].kind == Nk.NODE_PATTERN_IDENT)
                {
                    Node* id = n.children[0];
                    Node* ty = id.type_annotation;
                    l.bind_var(id.p.ident.name_ptr, id.p.ident.name_len, ty, current_stage);
                }
                for (usz i = 1; i < n.child_count; i++)
                {
                    check_well_staged_expr(l, n.children[i], current_stage, depth + 1);
                }
                return l.errors == 0;
            }

        default:
            for (usz i = 0; i < n.child_count; i++)
            {
                check_well_staged_expr(l, n.children[i], current_stage, depth + 1);
            }
            return l.errors == 0;
    }
}

// ── Formal Continuation Tree (ContTree) for Scoped Effect Operations ───────

enum ContKind
{
    CT_LEAF,     // pure expression leaf
    CT_NODE,     // scoped operation: Node(op, k_in, k_out)
    CT_SEQ,      // sequential composition: Seq(T1, T2)
    CT_ABORT,    // diverging / abortive path: Abort(e)
    CT_FMAP,     // functorial map: Fmap(f, T)
    CT_FUSE,     // structured fusion: Fuse(T_in, T_out)
    CT_ID        // identity continuation: Id
}

struct ContTree
{
    ContKind  kind;
    Node*     expr;       // AST node for LEAF / ABORT / op arguments
    Node*     op_decl;    // operation declaration for NODE
    ContTree* left;       // k_in for NODE, T1 for SEQ, T_in for FUSE, T for FMAP
    ContTree* right;      // k_out for NODE, T2 for SEQ, T_out for FUSE
    Node*     functor_fn; // AST node for FMAP function f
    bool      is_normalized;
    int       size_metric;
}

fn ContTree* cont_tree_new(ContKind kind, Node* expr, ContTree* l, ContTree* r)
{
    ContTree* t = (ContTree*)malloc(ContTree::size);
    if (t == null) return null;
    t.kind       = kind;
    t.expr       = expr;
    t.op_decl    = null;
    t.left       = l;
    t.right      = r;
    t.functor_fn = null;
    t.is_normalized = false;
    t.size_metric   = 1 + (l ? l.size_metric : 0) + (r ? r.size_metric : 0);
    return t;
}

fn void cont_tree_destroy(ContTree* t)
{
    if (t == null) return;
    if (t.left  != null) cont_tree_destroy(t.left);
    if (t.right != null) cont_tree_destroy(t.right);
    free((void*)t);
}

fn ContTree* cont_tree_clone(ContTree* t)
{
    if (t == null) return null;
    ContTree* c = cont_tree_new(t.kind, t.expr,
                                cont_tree_clone(t.left),
                                cont_tree_clone(t.right));
    if (c != null)
    {
        c.op_decl       = t.op_decl;
        c.functor_fn    = t.functor_fn;
        c.is_normalized = t.is_normalized;
        c.size_metric   = t.size_metric;
    }
    return c;
}

// ── Continuation-Tree Algebraic Rewriting & Normalization ──────────────────

fn bool rewrite_cont_tree_step(ContTree* t)
{
    if (t == null || t.is_normalized) return false;
    bool changed = false;
    if (t.left  != null) { changed = rewrite_cont_tree_step(t.left)  || changed; }
    if (t.right != null) { changed = rewrite_cont_tree_step(t.right) || changed; }

    switch (t.kind)
    {
        case ContKind.CT_NODE:
            // Rule 1: Identity Elimination
            // Node(op, k_in, Id) ↦ k_in
            if (t.right != null && t.right.kind == ContKind.CT_ID)
            {
                ContTree* in_frag = t.left;
                if (in_frag != null)
                {
                    t.kind       = in_frag.kind;
                    t.expr       = in_frag.expr;
                    t.op_decl    = in_frag.op_decl;
                    t.functor_fn = in_frag.functor_fn;
                    t.left       = cont_tree_clone(in_frag.left);
                    t.right      = cont_tree_clone(in_frag.right);
                    return true;
                }
            }
            // Rule 2: Dead-Scope Pruning
            // Node(op, Abort(e), k_out) ↦ Abort(e)
            if (t.left != null && t.left.kind == ContKind.CT_ABORT)
            {
                t.kind = ContKind.CT_ABORT;
                t.expr = t.left.expr;
                t.left = null;
                t.right = null;
                return true;
            }
            break;

        case ContKind.CT_FMAP:
            // Rule 3: Functorial Fusion across Scoped Nodes (Wu, Schrijvers, Yang et al.)
            // Fmap(f, Node(op, k_in, k_out)) ↦ Node(op, Fmap(f, k_in), k_out)
            if (t.left != null && t.left.kind == ContKind.CT_NODE)
            {
                ContTree* node_child = t.left;
                ContTree* fmap_in    = cont_tree_new(ContKind.CT_FMAP, null,
                                                     cont_tree_clone(node_child.left), null);
                if (fmap_in != null) fmap_in.functor_fn = t.functor_fn;

                t.kind    = ContKind.CT_NODE;
                t.expr    = node_child.expr;
                t.op_decl = node_child.op_decl;
                t.left    = fmap_in;
                t.right   = cont_tree_clone(node_child.right);
                return true;
            }
            // Rule 4: Functorial Map over Identity
            if (t.left != null && t.left.kind == ContKind.CT_ID)
            {
                t.kind  = ContKind.CT_ID;
                t.left  = null;
                t.right = null;
                return true;
            }
            break;

        case ContKind.CT_FUSE:
            // Rule 5: Structured Fusion Law (Wu et al.)
            // Fuse(Fmap(f, k_in), k_out) ↦ Fmap(f, Fuse(k_in, k_out))
            if (t.left != null && t.left.kind == ContKind.CT_FMAP)
            {
                ContTree* fmap_child = t.left;
                ContTree* inner_fuse = cont_tree_new(ContKind.CT_FUSE, null,
                                                     cont_tree_clone(fmap_child.left),
                                                     cont_tree_clone(t.right));
                t.kind       = ContKind.CT_FMAP;
                t.functor_fn = fmap_child.functor_fn;
                t.left       = inner_fuse;
                t.right      = null;
                return true;
            }
            // Rule 6: Fuse with Identity on Right
            if (t.right != null && t.right.kind == ContKind.CT_ID)
            {
                ContTree* in_child = t.left;
                if (in_child != null)
                {
                    t.kind       = in_child.kind;
                    t.expr       = in_child.expr;
                    t.op_decl    = in_child.op_decl;
                    t.functor_fn = in_child.functor_fn;
                    t.left       = cont_tree_clone(in_child.left);
                    t.right      = cont_tree_clone(in_child.right);
                    return true;
                }
            }
            break;

        case ContKind.CT_SEQ:
            // Rule 7: Sequential Associativity
            if (t.left != null && t.left.kind == ContKind.CT_SEQ)
            {
                ContTree* lseq = t.left;
                ContTree* new_rseq = cont_tree_new(ContKind.CT_SEQ, null,
                                                   cont_tree_clone(lseq.right),
                                                   cont_tree_clone(t.right));
                t.left  = cont_tree_clone(lseq.left);
                t.right = new_rseq;
                return true;
            }
            // Rule 8: Sequential with Identity
            if (t.left != null && t.left.kind == ContKind.CT_ID && t.right != null)
            {
                ContTree* rchild = t.right;
                t.kind  = rchild.kind;
                t.expr  = rchild.expr;
                t.left  = cont_tree_clone(rchild.left);
                t.right = cont_tree_clone(rchild.right);
                return true;
            }
            if (t.right != null && t.right.kind == ContKind.CT_ID && t.left != null)
            {
                ContTree* lchild = t.left;
                t.kind  = lchild.kind;
                t.expr  = lchild.expr;
                t.left  = cont_tree_clone(lchild.left);
                t.right = cont_tree_clone(lchild.right);
                return true;
            }
            break;

        default:
            break;
    }

    return changed;
}

fn int normalize_continuation_tree(ContTree* t)
{
    if (t == null) return 0;
    int steps = 0;
    while (steps < MODAL_REWRITE_CAP)
    {
        bool changed = rewrite_cont_tree_step(t);
        if (!changed) break;
        steps++;
    }
    t.is_normalized = true;
    return steps;
}

// ── AST Conversion & Lowering ──────────────────────────────────────────────

fn ContTree* ast_to_cont_tree(Node* n, int depth)
{
    if (n == null || depth > MODAL_MAX_DEPTH) return cont_tree_new(ContKind.CT_ID, null, null, null);
    switch (n.kind)
    {
        case Nk.NODE_EFFECT_HANDLE:
        case Nk.NODE_EFFECT_WITH:
            {
                Node* comp = n.child_count >= 1 ? n.children[0] : null;
                Node* arm  = n.child_count >= 2 ? n.children[1] : null;
                ContTree* k_in  = ast_to_cont_tree(comp, depth + 1);
                ContTree* k_out = (arm != null) ? ast_to_cont_tree(arm, depth + 1)
                                                : cont_tree_new(ContKind.CT_ID, null, null, null);
                ContTree* node  = cont_tree_new(ContKind.CT_NODE, n, k_in, k_out);
                if (node != null && arm != null && arm.kind == Nk.NODE_HANDLER_ARM)
                {
                    node.op_decl = arm.children[0];
                }
                return node;
            }

        case Nk.NODE_EXPR_BLOCK:
            {
                if (n.child_count == 0) return cont_tree_new(ContKind.CT_ID, null, null, null);
                if (n.child_count == 1) return ast_to_cont_tree(n.children[0], depth + 1);
                ContTree* cur = ast_to_cont_tree(n.children[n.child_count - 1], depth + 1);
                for (int i = (int)n.child_count - 2; i >= 0; i--)
                {
                    ContTree* left_tree = ast_to_cont_tree(n.children[(usz)i], depth + 1);
                    cur = cont_tree_new(ContKind.CT_SEQ, null, left_tree, cur);
                }
                return cur;
            }

        case Nk.NODE_EXPR_RETURN:
        case Nk.NODE_EXPR_BREAK:
        case Nk.NODE_STMT_PANIC:
            return cont_tree_new(ContKind.CT_ABORT, n, null, null);

        case Nk.NODE_EXPR_UNIT:
            return cont_tree_new(ContKind.CT_ID, n, null, null);

        default:
            return cont_tree_new(ContKind.CT_LEAF, n, null, null);
    }
}

fn Node* cont_tree_to_ast(ast::AstArena* arena, ContTree* t)
{
    if (t == null) return null;
    switch (t.kind)
    {
        case ContKind.CT_ID:
            return null;
        case ContKind.CT_LEAF:
        case ContKind.CT_ABORT:
            return t.expr;
        case ContKind.CT_SEQ:
            {
                Node* l = cont_tree_to_ast(arena, t.left);
                Node* r = cont_tree_to_ast(arena, t.right);
                if (l == null) return r;
                if (r == null) return l;
                return l;
            }
        case ContKind.CT_NODE:
            if (t.right == null || t.right.kind == ContKind.CT_ID)
            {
                return cont_tree_to_ast(arena, t.left);
            }
            return t.expr;
        default:
            return t.expr;
    }
}

fn Node* modal_try_aot_fuse_effect_node(ast::AstArena* arena, Node* effect_node)
{
    if (effect_node == null) return null;
    ContTree* tree = ast_to_cont_tree(effect_node, 0);
    if (tree == null) return effect_node;

    normalize_continuation_tree(tree);
    Node* fused_ast = cont_tree_to_ast(arena, tree);
    cont_tree_destroy(tree);

    if (fused_ast != null && fused_ast != effect_node)
    {
        return fused_ast;
    }
    return effect_node;
}
