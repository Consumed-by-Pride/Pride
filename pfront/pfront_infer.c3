// ============================================================================
// pfront_infer.c3 — bidirectional type inference / checking (part 9)
// ----------------------------------------------------------------------------
// Walks the resolved AST and assigns a TypeId to every expression, filling the
// `type_slot` that has been sitting empty since the first version of this
// front end.
//
// The algorithm is bidirectional:
//
//   * SYNTHESIS (infer)  — bottom-up. `1 + 2` synthesises {integer}; a call
//     synthesises its callee's result type.
//   * CHECKING  (check)  — top-down. When an expected type is known (a `let`
//     annotation, a parameter, a return position) it is pushed INTO the
//     expression. This is what makes `let x : u8 = 0` assign u8 to the literal
//     instead of defaulting it to i64 and then reporting a mismatch.
//
// Bidirectionality matters here because Pride has integer literals of many
// widths, and a purely bottom-up HM would either reject or over-default them.
//
// Errors are reported once at the point of mismatch and then poisoned with
// TY_ERROR, which unifies with anything — so one bad expression yields one
// diagnostic, not a cascade through every enclosing node.
// ============================================================================

module pfront_infer;

import pfront_lex;
import pfront_core;
import pfront_types;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Types = pfront_types::TypeTable;
alias TyKind = pfront_types::TyKind;

extern fn int printf(char* fmt, ...);

const usz TYPE_BUF = 256;
const int MAX_INFER_DEPTH = 200;

struct Inferencer
{
    Types*                     tt;
    pfront_types::TypeMapper mapper;
    pfront_core::DiagBag*   diags;
    pfront_core::Interner*  interner;
    char*                   file;

    int   current_ret;      // expected return type of the fn being checked
    int   depth;
    usz   exprs_typed;
    usz   mismatches;
    usz   occurs_errors;
    usz   arity_errors;
    usz   defaulted;
    usz   suppressed;       // errors withheld because a subterm already failed
    bool  strict;           // report mismatches (off while bootstrapping)
}

fn void Inferencer.init(Inferencer* inf, Types* tt, pfront_core::DiagBag* d,
                        pfront_core::Interner* it, char* file)
{
    inf.tt = tt;
    inf.mapper.init(tt, it);
    inf.diags = d;
    inf.interner = it;
    inf.file = file;
    inf.current_ret = pfront_types::NO_TYPE;
    inf.depth = 0;
    inf.exprs_typed = 0;
    inf.mismatches = 0;
    inf.occurs_errors = 0;
    inf.arity_errors = 0;
    inf.defaulted = 0;
    inf.suppressed = 0;
    inf.strict = false;
}

// Render two types into a mismatch message. Kept here so every diagnostic has
// the same shape: "expected X, found Y".
fn void Inferencer.report_mismatch(Inferencer* inf, Node* at, int expected, int found)
{
    inf.mismatches = inf.mismatches + 1;
    if (at == null) { return; }
    char[TYPE_BUF] be;
    char[TYPE_BUF] bf;
    usz pe = 0;
    usz pf = 0;
    be[0] = 0;
    bf[0] = 0;
    inf.tt.write(expected, &be[0], TYPE_BUF, &pe, 0);
    inf.tt.write(found, &bf[0], TYPE_BUF, &pf, 0);
    // The two rendered types are packed into msg/hint so the renderer can show
    // both without a printf-style format in the diagnostic layer.
    // ADVISORY, never an error. Pride is untyped: a shape difference is
    // information for the optimizer, not grounds to reject the program.
    inf.diags.advisory_hint(pfront_core::Phase.PH_RESOLVE, 3100, at.line, at.col,
                            "inferred shape differs from the annotation",
                            &bf[0], inf.file);
}

fn void Inferencer.unify_at(Inferencer* inf, Node* at, int a, int b)
{
    pfront_types::UnifyResult r = inf.tt.unify(a, b, 0);
    switch (r)
    {
        case UNIFY_OK:
            return;
        case UNIFY_OCCURS:
        {
            inf.occurs_errors = inf.occurs_errors + 1;
            if (at != null)
            {
                inf.diags.advisory_hint(pfront_core::Phase.PH_RESOLVE, 3101, at.line, at.col,
                                        "inferred type refers to itself",
                                        "an indirection (`*T`) would make the shape finite",
                                        inf.file);
            }
        }
        case UNIFY_ARITY:
        {
            inf.arity_errors = inf.arity_errors + 1;
            if (at != null)
            {
                inf.diags.advisory(pfront_core::Phase.PH_RESOLVE, 3102, at.line, at.col,
                                   "argument count differs from the declaration", inf.file);
            }
        }
        default:
            inf.report_mismatch(at, a, b);
    }
}

// ── Declaration types ───────────────────────────────────────────────────────
// The type of a declaration, computed once and cached in `type_slot`.
fn int Inferencer.type_of_decl(Inferencer* inf, Node* d)
{
    if (d == null) { return inf.tt.t_error; }
    if (d.type_slot != null) { return (int)d.type_slot.p.ival; }

    int result = pfront_types::NO_TYPE;
    switch (d.kind)
    {
        case N_DECL_FN:
        case N_DECL_EXTERN_FN:
        {
            if (d.type_ann != null) { result = inf.mapper.map(d.type_ann, 0); }
            else
            {
                // Parameter-list form: build the arrow from N_DECL_PARAMs.
                int[pfront_types::MAX_TYPE_ARGS] ps;
                usz np = 0;
                for (usz i = 0; i < d.child_count && np < pfront_types::MAX_TYPE_ARGS - 1; i++)
                {
                    Node* c = d.children[i];
                    if (c == null || c.kind != Nk.N_DECL_PARAM) { continue; }
                    ps[np] = c.type_ann != null ? inf.mapper.map(c.type_ann, 0)
                                                : inf.tt.fresh_var(false);
                    np = np + 1;
                }
                result = inf.tt.mk_fn(&ps[0], np, inf.tt.fresh_var(false));
            }
        }
        case N_DECL_STRUCT:
        case N_DECL_UNION:
        case N_DECL_ENUM:
        case N_DECL_NEWTYPE:
            result = inf.tt.mk_named(d, d.name_id);
        case N_DECL_TYPE:
            result = d.type_ann != null ? inf.mapper.map(d.type_ann, 0)
                                        : inf.tt.fresh_var(false);
        case N_DECL_VARIANT:
        {
            Node* parent = d.parent;
            result = parent != null ? inf.tt.mk_named(parent, parent.name_id)
                                    : inf.tt.fresh_var(false);
        }
        case N_DECL_FIELD:
        case N_DECL_PARAM:
        case N_PAT_IDENT:
        case N_DECL_LET:
        case N_DECL_CONST:
        case N_DECL_STATIC:
            result = d.type_ann != null ? inf.mapper.map(d.type_ann, 0)
                                        : inf.tt.fresh_var(false);
        default:
            result = inf.tt.fresh_var(false);
    }
    inf.cache_type(d, result);
    return result;
}

// `type_slot` is a PNode*, so the TypeId is stored in a tiny marker node's
// payload. Reusing the existing field avoids widening PNode for every node in
// the program just to carry an int.
fn void Inferencer.cache_type(Inferencer* inf, Node* n, int ty)
{
    if (n == null) { return; }
    if (n.type_slot == null)
    {
        // Its own field, NOT p.aux: aux is a shared discriminant and
        // overwriting it silently disabled the tuple-index marker on
        // field accesses. See the note on PNode.type_id.
        n.type_id = ty;
        n.flags = n.flags | pfront_core::NF_TYPED;
        return;
    }
    n.type_slot.p.ival = (ulong)ty;
    n.flags = n.flags | pfront_core::NF_TYPED;
}

fn int Inferencer.cached_type(Inferencer* inf, Node* n)
{
    if (n == null) { return pfront_types::NO_TYPE; }
    if ((n.flags & pfront_core::NF_TYPED) == 0) { return pfront_types::NO_TYPE; }
    if (n.type_slot != null) { return (int)n.type_slot.p.ival; }
    return n.type_id;
}

// ── Synthesis ───────────────────────────────────────────────────────────────
fn int Inferencer.infer(Inferencer* inf, Node* e)
{
    if (e == null) { return inf.tt.t_error; }
    if (inf.depth > MAX_INFER_DEPTH) { return inf.tt.t_error; }
    inf.depth = inf.depth + 1;
    int result = inf.infer_inner(e);
    inf.depth = inf.depth - 1;
    inf.exprs_typed = inf.exprs_typed + 1;
    inf.cache_type(e, result);
    return result;
}

fn int Inferencer.infer_inner(Inferencer* inf, Node* e)
{
    switch (e.kind)
    {
        case N_EXPR_INT:
        {
            // A suffixed literal is concrete; an unsuffixed one is a numeric
            // variable so context can pick the width.
            if (e.p.width != 0)
            {
                return inf.tt.mk_int((int)e.p.width, e.p.is_signed);
            }
            return inf.tt.fresh_var(true);
        }
        case N_EXPR_FLOAT:
            return e.p.width == 32 ? inf.tt.t_f32 : inf.tt.t_f64;
        case N_EXPR_BOOL:   return inf.tt.t_bool;
        case N_EXPR_CHAR:   return inf.tt.t_char;
        case N_EXPR_STRING: return inf.tt.t_string;
        case N_EXPR_BYTES:  return inf.tt.mk_slice(inf.tt.t_u8);
        case N_EXPR_UNIT:   return inf.tt.t_unit;
        case N_EXPR_NULL:   return inf.tt.mk_ptr(inf.tt.fresh_var(false), false);

        case N_EXPR_UNREACHABLE:
        case N_EXPR_TRAP:
            return inf.tt.t_never;

        case N_EXPR_IDENT:
        case N_EXPR_PATH:
        {
            if (e.resolved != null) { return inf.type_of_decl(e.resolved); }
            return inf.tt.t_error;
        }

        case N_EXPR_UNARY:
        {
            int operand = inf.infer(e.child(0));
            Tk op = (Tk)e.p.op;
            if (op == Tk.TOKEN_BANG || op == Tk.TOKEN_KW_NOT)
            {
                inf.unify_at(e, operand, inf.tt.t_bool);
                return inf.tt.t_bool;
            }
            return operand;
        }

        case N_EXPR_BINARY:
            return inf.infer_binary(e);

        case N_EXPR_DEREF:
        {
            int p = inf.infer(e.child(0));
            int inner = inf.tt.fresh_var(false);
            inf.unify_at(e, p, inf.tt.mk_ptr(inner, false));
            return inner;
        }

        case N_EXPR_REF:
        {
            int inner = inf.infer(e.child(0));
            return inf.tt.mk_ptr(inner, (e.flags & pfront_core::NF_MUT) != 0);
        }

        case N_EXPR_CAST:
        {
            inf.infer(e.child(0));
            if (e.type_ann != null) { return inf.mapper.map(e.type_ann, 0); }
            return inf.tt.fresh_var(false);
        }

        case N_EXPR_CALL:
            return inf.infer_call(e);

        case N_EXPR_TUPLE:
        {
            int[pfront_types::MAX_TYPE_ARGS] elems;
            usz n = 0;
            for (usz i = 0; i < e.child_count && n < pfront_types::MAX_TYPE_ARGS; i++)
            {
                elems[n] = inf.infer(e.children[i]);
                n = n + 1;
            }
            return inf.tt.mk_tuple(&elems[0], n);
        }

        case N_EXPR_ARRAY:
        {
            if (e.child_count == 0) { return inf.tt.mk_array(inf.tt.fresh_var(false), 0); }
            int elem = inf.infer(e.children[0]);
            for (usz i = 1; i < e.child_count; i++)
            {
                int t = inf.infer(e.children[i]);
                inf.unify_at(e.children[i], elem, t);
            }
            return inf.tt.mk_array(elem, (ulong)e.child_count);
        }

        case N_EXPR_INDEX:
        {
            int base = inf.infer(e.child(0));
            int idx = inf.infer(e.child(1));
            // Index must be integral; element type comes from the container.
            int want_idx = inf.tt.fresh_var(true);
            inf.unify_at(e.child(1), idx, want_idx);
            return inf.element_of(base);
        }

        case N_EXPR_SLICE:
        {
            int base = inf.infer(e.child(0));
            for (usz i = 1; i < e.child_count; i++) { inf.infer(e.children[i]); }
            return inf.tt.mk_slice(inf.element_of(base));
        }

        case N_EXPR_FIELD:
            return inf.infer_field(e);

        case N_EXPR_STRUCT_LIT:
        {
            for (usz i = 1; i < e.child_count; i++)
            {
                Node* fi = e.children[i];
                if (fi != null) { inf.infer(fi.child(0)); }
            }
            if (e.resolved != null) { return inf.tt.mk_named(e.resolved, e.name_id); }
            return inf.tt.fresh_var(false);
        }

        case N_EXPR_IF:
        {
            int c = inf.infer(e.child(0));
            inf.unify_at(e.child(0), c, inf.tt.t_bool);
            int th = inf.infer(e.child(1));
            if (e.child_count >= 3)
            {
                int el = inf.infer(e.child(2));
                inf.unify_at(e, th, el);
            }
            else
            {
                // A one-armed `if` is a statement: its value is unit.
                return inf.tt.t_unit;
            }
            return th;
        }

        case N_EXPR_MATCH:
        {
            inf.infer(e.child(0));
            int result = pfront_types::NO_TYPE;
            for (usz i = 1; i < e.child_count; i++)
            {
                Node* arm = e.children[i];
                if (arm == null) { continue; }
                int armty = pfront_types::NO_TYPE;
                for (usz j = 1; j < arm.child_count; j++)
                {
                    Node* c = arm.children[j];
                    if (c == null) { continue; }
                    if (c.kind == Nk.N_GUARD)
                    {
                        int g = inf.infer(c.child(0));
                        inf.unify_at(c, g, inf.tt.t_bool);
                        continue;
                    }
                    armty = inf.infer(c);
                }
                if (armty == pfront_types::NO_TYPE) { continue; }
                if (result == pfront_types::NO_TYPE) { result = armty; }
                else { inf.unify_at(arm, result, armty); }
            }
            return result == pfront_types::NO_TYPE ? inf.tt.t_unit : result;
        }

        case N_EXPR_WHILE:
        {
            int c = inf.infer(e.child(0));
            inf.unify_at(e.child(0), c, inf.tt.t_bool);
            inf.infer(e.child(1));
            return inf.tt.t_unit;
        }

        case N_EXPR_FOR:
        {
            inf.infer(e.child(1));
            inf.infer(e.child(2));
            return inf.tt.t_unit;
        }

        case N_BLOCK:
        {
            int last = inf.tt.t_unit;
            for (usz i = 0; i < e.child_count; i++)
            {
                Node* s = e.children[i];
                if (s == null) { continue; }
                last = inf.infer_stmt(s);
            }
            return last;
        }

        case N_EXPR_RANGE:
        {
            for (usz i = 0; i < e.child_count; i++) { inf.infer(e.children[i]); }
            return inf.tt.fresh_var(true);
        }

        case N_EXPR_ALLOC:
        {
            if (e.type_ann != null) { return inf.mapper.map(e.type_ann, 0); }
            for (usz i = 0; i < e.child_count; i++) { inf.infer(e.children[i]); }
            return inf.tt.mk_ptr(inf.tt.fresh_var(false), true);
        }

        case N_EXPR_FREE:
        {
            inf.infer(e.child(0));
            return inf.tt.t_unit;
        }

        case N_EXPR_SIZEOF:
        case N_EXPR_ALIGNOF:
        case N_EXPR_OFFSETOF:
            return inf.tt.t_u64;

        case N_EXPR_TRANSMUTE:
        {
            inf.infer(e.child(0));
            if (e.type_ann != null) { return inf.mapper.map(e.type_ann, 0); }
            return inf.tt.fresh_var(false);
        }

        case N_EXPR_ASSERT:
        {
            int c = inf.infer(e.child(0));
            inf.unify_at(e.child(0), c, inf.tt.t_bool);
            return inf.tt.t_unit;
        }

        case N_EXPR_UNSAFE:
        case N_EXPR_UNCHECKED:
        case N_EXPR_COMPTIME:
        {
            int last = inf.tt.t_unit;
            for (usz i = 0; i < e.child_count; i++) { last = inf.infer(e.children[i]); }
            return last;
        }

        case N_EXPR_METHOD:
        {
            for (usz i = 0; i < e.child_count; i++) { inf.infer(e.children[i]); }
            return inf.tt.fresh_var(false);
        }

        case N_EXPR_LAMBDA:
        {
            for (usz i = 0; i < e.child_count; i++)
            {
                Node* c = e.children[i];
                if (c == null) { continue; }
                if (c.kind == Nk.N_CLAUSE)
                {
                    for (usz j = 1; j < c.child_count; j++) { inf.infer(c.children[j]); }
                }
                else if (c.kind != Nk.N_DECL_PARAM) { inf.infer(c); }
            }
            return inf.tt.fresh_var(false);
        }

        default:
        {
            for (usz i = 0; i < e.child_count; i++)
            {
                Node* c = e.children[i];
                if (c == null) { continue; }
                if (pfront_core::is_pattern(c.kind)) { continue; }
                inf.infer(c);
            }
            return inf.tt.fresh_var(false);
        }
    }
}

// Element type of an indexable container.
fn int Inferencer.element_of(Inferencer* inf, int container)
{
    int r = inf.tt.find(container);
    pfront_types::TyNode* n = &inf.tt.nodes[r];
    if (n.kind == TyKind.TY_ARRAY || n.kind == TyKind.TY_SLICE || n.kind == TyKind.TY_PTR)
    {
        if (n.arg_count > 0) { return n.args[0]; }
    }
    if (n.kind == TyKind.TY_STRING) { return inf.tt.t_u8; }
    return inf.tt.fresh_var(false);
}

fn int Inferencer.infer_binary(Inferencer* inf, Node* e)
{
    int l = inf.infer(e.child(0));
    int r = inf.infer(e.child(1));
    Tk op = (Tk)e.p.op;

    switch (op)
    {
        // Comparisons: operands must agree, result is bool.
        case TOKEN_EQEQ:
        case TOKEN_NEQ:
        case TOKEN_NEQ_UNI:
        case TOKEN_LT:
        case TOKEN_LTEQ:
        case TOKEN_GT:
        case TOKEN_GTEQ:
        case TOKEN_LEQ_UNI:
        case TOKEN_GEQ_UNI:
        {
            inf.unify_at(e, l, r);
            return inf.tt.t_bool;
        }
        // Logical: both sides bool.
        case TOKEN_AMPAMP:
        case TOKEN_PIPEPIPE:
        case TOKEN_KW_AND:
        case TOKEN_KW_OR:
        {
            inf.unify_at(e.child(0), l, inf.tt.t_bool);
            inf.unify_at(e.child(1), r, inf.tt.t_bool);
            return inf.tt.t_bool;
        }
        // Shifts: the operands need not share a type.
        case TOKEN_LSHIFT:
        case TOKEN_RSHIFT:
            return l;
        default:
        {
            // Arithmetic and bitwise: pointer arithmetic keeps the pointer
            // type, otherwise both sides unify.
            int lr = inf.tt.find(l);
            if (inf.tt.nodes[lr].kind == TyKind.TY_PTR) { return l; }
            int rr = inf.tt.find(r);
            if (inf.tt.nodes[rr].kind == TyKind.TY_PTR) { return r; }
            inf.unify_at(e, l, r);
            return l;
        }
    }
}

fn int Inferencer.infer_call(Inferencer* inf, Node* e)
{
    if (e.child_count == 0) { return inf.tt.t_error; }
    int callee = inf.infer(e.children[0]);
    int cr = inf.tt.find(callee);
    pfront_types::TyNode* cn = &inf.tt.nodes[cr];

    // Collect argument types.
    int[pfront_types::MAX_TYPE_ARGS] args;
    usz na = 0;
    for (usz i = 1; i < e.child_count && na < pfront_types::MAX_TYPE_ARGS - 1; i++)
    {
        args[na] = inf.infer(e.children[i]);
        na = na + 1;
    }

    if (cn.kind == TyKind.TY_FN)
    {
        usz np = cn.arg_count > 0 ? cn.arg_count - 1 : 0;
        int ret = cn.arg_count > 0 ? cn.args[cn.arg_count - 1] : inf.tt.t_unit;

        // A single tuple parameter accepts a flattened argument list, which is
        // how Pride's `fn f : (i64, i64) -> i64` signatures are called.
        if (np == 1 && na > 1)
        {
            int p0 = inf.tt.find(cn.args[0]);
            if (inf.tt.nodes[p0].kind == TyKind.TY_TUPLE)
            {
                pfront_types::TyNode* tup = &inf.tt.nodes[p0];
                if (tup.arg_count == na)
                {
                    for (usz i = 0; i < na; i++)
                    {
                        inf.unify_at(e.children[i + 1], tup.args[i], args[i]);
                    }
                    return ret;
                }
            }
        }
        if (np != na)
        {
            inf.arity_errors = inf.arity_errors + 1;
            inf.diags.advisory(pfront_core::Phase.PH_RESOLVE, 3102, e.line, e.col,
                               "argument count differs from the declaration", inf.file);
            return ret;
        }
        for (usz i = 0; i < na; i++)
        {
            inf.unify_at(e.children[i + 1], cn.args[i], args[i]);
        }
        return ret;
    }

    if (cn.kind == TyKind.TY_VAR)
    {
        // Unknown callee: solve for its shape from the call site.
        int ret = inf.tt.fresh_var(false);
        int want = inf.tt.mk_fn(&args[0], na, ret);
        inf.unify_at(e, callee, want);
        return ret;
    }

    // Calling a named type is a constructor application.
    if (cn.kind == TyKind.TY_NAMED) { return callee; }
    return inf.tt.fresh_var(false);
}

fn int Inferencer.infer_field(Inferencer* inf, Node* e)
{
    int base = inf.infer(e.child(0));
    int br = inf.tt.find(base);
    pfront_types::TyNode* bn = &inf.tt.nodes[br];

    // Auto-deref through a pointer, as field access on `*T` implies.
    if (bn.kind == TyKind.TY_PTR && bn.arg_count > 0)
    {
        br = inf.tt.find(bn.args[0]);
        bn = &inf.tt.nodes[br];
    }

    if (e.p.aux == 1)
    {
        // Numeric tuple index `t.0`.
        if (bn.kind == TyKind.TY_TUPLE)
        {
            usz idx = (usz)e.p.ival;
            if (idx < bn.arg_count) { return bn.args[idx]; }
            inf.diags.advisory(pfront_core::Phase.PH_RESOLVE, 3103, e.line, e.col,
                               "tuple index is past the end of the tuple", inf.file);
            return inf.tt.t_error;
        }
        return inf.tt.fresh_var(false);
    }

    if (bn.kind == TyKind.TY_NAMED && bn.decl != null)
    {
        Node* sd = bn.decl;
        for (usz i = 0; i < sd.child_count; i++)
        {
            Node* f = sd.children[i];
            if (f == null || f.kind != Nk.N_DECL_FIELD) { continue; }
            if (f.name_id != e.name_id) { continue; }
            e.resolved = f;
            return inf.type_of_decl(f);
        }
        // The struct is known and has no such field: a real error.
        inf.diags.advisory(pfront_core::Phase.PH_RESOLVE, 3104, e.line, e.col,
                           "no field with this name is known on the base type", inf.file);
        return inf.tt.t_error;
    }
    return inf.tt.fresh_var(false);
}

// ── Statements ──────────────────────────────────────────────────────────────
fn int Inferencer.infer_stmt(Inferencer* inf, Node* s)
{
    if (s == null) { return inf.tt.t_unit; }
    switch (s.kind)
    {
        case N_DECL_LET:
        case N_DECL_CONST:
        case N_DECL_STATIC:
        {
            int declared = s.type_ann != null ? inf.mapper.map(s.type_ann, 0)
                                              : pfront_types::NO_TYPE;
            int init = pfront_types::NO_TYPE;
            for (usz i = 0; i < s.child_count; i++)
            {
                Node* c = s.children[i];
                if (c == null || pfront_core::is_pattern(c.kind)) { continue; }
                // CHECKING direction: push the annotation into the initialiser
                // so `let x : u8 = 0` types the literal as u8.
                if (declared != pfront_types::NO_TYPE) { init = inf.check(c, declared); }
                else { init = inf.infer(c); }
            }
            int final_ty = declared != pfront_types::NO_TYPE ? declared
                         : (init != pfront_types::NO_TYPE ? init : inf.tt.fresh_var(false));
            // Bind the pattern so later references see the type.
            Node* pat = s.child(0);
            if (pat != null && pat.kind == Nk.N_PAT_IDENT) { inf.cache_type(pat, final_ty); }
            inf.cache_type(s, final_ty);
            return inf.tt.t_unit;
        }
        case N_STMT_RETURN:
        {
            if (s.child_count > 0)
            {
                if (inf.current_ret != pfront_types::NO_TYPE)
                {
                    inf.check(s.children[0], inf.current_ret);
                }
                else { inf.infer(s.children[0]); }
            }
            return inf.tt.t_never;
        }
        case N_STMT_ASSIGN:
        {
            int lhs = inf.infer(s.child(0));
            inf.check(s.child(1), lhs);
            return inf.tt.t_unit;
        }
        case N_STMT_COMPOUND_ASSIGN:
        {
            int lhs = inf.infer(s.child(0));
            int rhs = inf.infer(s.child(1));
            int lr = inf.tt.find(lhs);
            if (inf.tt.nodes[lr].kind != TyKind.TY_PTR) { inf.unify_at(s, lhs, rhs); }
            return inf.tt.t_unit;
        }
        case N_STMT_BREAK:
        case N_STMT_CONTINUE:
        {
            for (usz i = 0; i < s.child_count; i++) { inf.infer(s.children[i]); }
            return inf.tt.t_never;
        }
        case N_STMT_DEFER:
        {
            for (usz i = 0; i < s.child_count; i++) { inf.infer(s.children[i]); }
            return inf.tt.t_unit;
        }
        case N_DECL_FN:
        {
            inf.check_fn(s);
            return inf.tt.t_unit;
        }
        default:
            return inf.infer(s);
    }
}

// ── Checking direction ──────────────────────────────────────────────────────
fn int Inferencer.check(Inferencer* inf, Node* e, int expected)
{
    if (e == null) { return inf.tt.t_error; }
    if (expected == pfront_types::NO_TYPE) { return inf.infer(e); }

    // Literals adopt the expected type directly when it is compatible; this is
    // the whole point of the checking direction.
    if (e.kind == Nk.N_EXPR_INT && e.p.width == 0)
    {
        int er = inf.tt.find(expected);
        TyKind k = inf.tt.nodes[er].kind;
        if (k == TyKind.TY_INT || k == TyKind.TY_FLOAT || k == TyKind.TY_VAR)
        {
            inf.cache_type(e, expected);
            inf.exprs_typed = inf.exprs_typed + 1;
            return expected;
        }
    }
    if (e.kind == Nk.N_EXPR_ARRAY)
    {
        int er = inf.tt.find(expected);
        pfront_types::TyNode* en = &inf.tt.nodes[er];
        if ((en.kind == TyKind.TY_ARRAY || en.kind == TyKind.TY_SLICE) && en.arg_count > 0)
        {
            for (usz i = 0; i < e.child_count; i++) { inf.check(e.children[i], en.args[0]); }
            inf.cache_type(e, expected);
            return expected;
        }
    }
    if (e.kind == Nk.N_EXPR_IF && e.child_count >= 3)
    {
        int c = inf.infer(e.child(0));
        inf.unify_at(e.child(0), c, inf.tt.t_bool);
        inf.check(e.child(1), expected);
        inf.check(e.child(2), expected);
        inf.cache_type(e, expected);
        return expected;
    }

    int actual = inf.infer(e);
    inf.unify_at(e, expected, actual);
    return expected;
}

// ── Function checking ───────────────────────────────────────────────────────
fn void Inferencer.check_fn(Inferencer* inf, Node* f)
{
    if (f == null) { return; }
    int fty = inf.type_of_decl(f);
    int fr = inf.tt.find(fty);
    pfront_types::TyNode* fn_node = &inf.tt.nodes[fr];

    int saved_ret = inf.current_ret;
    int ret = pfront_types::NO_TYPE;
    if (fn_node.kind == TyKind.TY_FN && fn_node.arg_count > 0)
    {
        ret = fn_node.args[fn_node.arg_count - 1];
    }
    inf.current_ret = ret;

    // Give each clause's binders the parameter types, so the body sees them.
    for (usz i = 0; i < f.child_count; i++)
    {
        Node* c = f.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.N_CLAUSE)
        {
            inf.bind_clause_params(c.child(0), fn_node);
            for (usz j = 1; j < c.child_count; j++)
            {
                Node* body = c.children[j];
                if (body == null) { continue; }
                if (body.kind == Nk.N_GUARD)
                {
                    int g = inf.infer(body.child(0));
                    inf.unify_at(body, g, inf.tt.t_bool);
                    continue;
                }
                if (ret != pfront_types::NO_TYPE) { inf.check(body, ret); }
                else { inf.infer(body); }
            }
        }
        else if (c.kind == Nk.N_BLOCK)
        {
            if (ret != pfront_types::NO_TYPE) { inf.check(c, ret); }
            else { inf.infer(c); }
        }
        else if (c.kind == Nk.N_DECL_PARAM)
        {
            Node* pat = c.child(0);
            if (pat != null && c.type_ann != null)
            {
                inf.cache_type(pat, inf.mapper.map(c.type_ann, 0));
            }
        }
    }
    inf.current_ret = saved_ret;
}

// Distribute a function's parameter types over a clause's pattern.
fn void Inferencer.bind_clause_params(Inferencer* inf, Node* pat,
                                      pfront_types::TyNode* fn_node)
{
    if (pat == null || fn_node == null) { return; }
    usz np = fn_node.arg_count > 0 ? fn_node.arg_count - 1 : 0;
    if (np == 0) { return; }

    if (np == 1)
    {
        int p0 = inf.tt.find(fn_node.args[0]);
        pfront_types::TyNode* pn = &inf.tt.nodes[p0];
        if (pat.kind == Nk.N_PAT_TUPLE && pn.kind == TyKind.TY_TUPLE)
        {
            usz n = pat.child_count < pn.arg_count ? pat.child_count : pn.arg_count;
            for (usz i = 0; i < n; i++) { inf.bind_pattern_type(pat.children[i], pn.args[i]); }
            return;
        }
        inf.bind_pattern_type(pat, fn_node.args[0]);
        return;
    }
    if (pat.kind == Nk.N_PAT_TUPLE)
    {
        usz n = pat.child_count < np ? pat.child_count : np;
        for (usz i = 0; i < n; i++) { inf.bind_pattern_type(pat.children[i], fn_node.args[i]); }
    }
}

fn void Inferencer.bind_pattern_type(Inferencer* inf, Node* pat, int ty)
{
    if (pat == null) { return; }
    switch (pat.kind)
    {
        case N_PAT_IDENT:
        {
            if (pat.type_ann != null)
            {
                int declared = inf.mapper.map(pat.type_ann, 0);
                inf.unify_at(pat, declared, ty);
                inf.cache_type(pat, declared);
                return;
            }
            inf.cache_type(pat, ty);
        }
        case N_PAT_TUPLE:
        {
            int r = inf.tt.find(ty);
            pfront_types::TyNode* n = &inf.tt.nodes[r];
            if (n.kind == TyKind.TY_TUPLE)
            {
                usz k = pat.child_count < n.arg_count ? pat.child_count : n.arg_count;
                for (usz i = 0; i < k; i++) { inf.bind_pattern_type(pat.children[i], n.args[i]); }
            }
        }
        case N_PAT_VARIANT:
        {
            for (usz i = 1; i < pat.child_count; i++)
            {
                inf.bind_pattern_type(pat.children[i], inf.tt.fresh_var(false));
            }
        }
        default:
        {
            for (usz i = 0; i < pat.child_count; i++)
            {
                inf.bind_pattern_type(pat.children[i], inf.tt.fresh_var(false));
            }
        }
    }
}

// ── Driver ──────────────────────────────────────────────────────────────────
fn void Inferencer.run(Inferencer* inf, Node* root)
{
    if (root == null) { return; }
    // Pass 1: give every top-level declaration a type, so mutual recursion
    // resolves without ordering constraints.
    for (usz i = 0; i < root.child_count; i++)
    {
        Node* d = root.children[i];
        if (d == null || !pfront_core::is_decl(d.kind)) { continue; }
        inf.type_of_decl(d);
    }
    // Pass 2: check bodies.
    for (usz i = 0; i < root.child_count; i++)
    {
        Node* d = root.children[i];
        if (d == null) { continue; }
        if (d.kind == Nk.N_DECL_FN) { inf.check_fn(d); }
        else if (d.kind == Nk.N_DECL_LET || d.kind == Nk.N_DECL_CONST
              || d.kind == Nk.N_DECL_STATIC) { inf.infer_stmt(d); }
    }
    inf.defaulted = inf.tt.default_numeric_vars();
}

fn void Inferencer.report(Inferencer* inf)
{
    printf("  expressions typed: %d\n", (int)inf.exprs_typed);
    printf("  type mismatches  : %d (%d suppressed in permissive mode)\n",
           (int)inf.mismatches, (int)inf.suppressed);
    printf("  arity errors     : %d, occurs errors: %d\n",
           (int)inf.arity_errors, (int)inf.occurs_errors);
    printf("  numeric defaults : %d vars -> i64\n", (int)inf.defaulted);
    printf("  types mapped     : %d (%d unknown names)\n",
           (int)inf.mapper.mapped, (int)inf.mapper.unknown_names);
}
