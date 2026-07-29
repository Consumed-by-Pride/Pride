// typecheck.c3 — Pride type checker (semantic subtyping, soft typing)
// Implementation language: C3 (host).
// Pipeline:  ... -> Parser -> AST -> Resolver -> TypeChecker (this) -> ...
// Design (v.md §20):
//   - Types are SETS OF VALUES. The algebra is a lattice:
//       A ∩ B  intersection   A ∪ B  union   ¬A  negation   ⊥  bottom (empty)
//     plus primitives (i8..u64, f32/f64, bool, ptr, Str, unit), pointers,
//     arrays/slices, tuples, and function types.
//   - We SYNTHESIZE a type for each expression and CHECK it against the
//     expected type using a structural `subtype` relation over the lattice.
//   - SOFT TYPING (§20.4): a mismatch is a WARNING by default; `--strict`
//     promotes warnings to errors. The checker never aborts.
//   - Constant folding already happened in the parser; we just read literals.
// Types are themselves AstNodes (NODE_TYPE_*), built in the same arena, so the
// checker can attach a synthesized type to any node via `node.type_annotation`.

module typecheck;

import lexer;
import ast;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);

alias Node = ast::AstNode;
alias Nk = ast::NodeKind;

// Primitive type tags. Kept as a small enum so subtyping over numerics is cheap.
enum Prim : int
{
    PRIM_NONE,    // not a primitive
    PRIM_I8, PRIM_I16, PRIM_I32, PRIM_I64, PRIM_I128,
    PRIM_U8, PRIM_U16, PRIM_U32, PRIM_U64, PRIM_U128,
    PRIM_ISIZE, PRIM_USIZE,
    PRIM_F32, PRIM_F64,
    PRIM_BOOL,
    PRIM_PTR,
    PRIM_STR,
    PRIM_CHAR,
    PRIM_UNIT
}

// One diagnostic. `is_error` distinguishes a hard error from a soft warning.
struct TypeError
{
    char* msg;
    int   line;
    int   col;
    bool  is_error;
}

struct TypeChecker
{
    ast::AstArena* arena;   // for synthesizing type nodes
    bool strict;            // --strict: promote soft warnings to errors
    Node* current_self_type; // Self = implementing type in impl blocks

    // Cached canonical primitive type nodes (built lazily, interned by us).
    Node*[16] prim_cache;

    TypeError[1024] diags;
    int diag_count;
    int error_count;
    int warning_count;

    // Recursion-depth guard for the subtyping/equality relations, which recurse
    // over arbitrarily deep type expressions (e.g. 1000-deep `∩`/`∪` chains).
    // Past the cap we answer permissively rather than overflow the stack.
    int sub_depth;
}

const int MAX_SUBTYPE_DEPTH = 600;

fn void TypeChecker.init(TypeChecker* self, ast::AstArena* arena, bool strict)
{
    self.arena = arena;
    self.strict = strict;
    self.diag_count = 0;
    self.error_count = 0;
    self.warning_count = 0;
    self.sub_depth = 0;
    for (int i = 0; i < 16; i++) self.prim_cache[i] = null;
}

fn void TypeChecker.diag(TypeChecker* self, char* msg, int line, int col, bool hard)
{
    bool is_error = hard || self.strict;
    if (is_error) { self.error_count++; }
    else { self.warning_count++; }

    if (self.diag_count < 1024)
    {
        TypeError e;
        e.msg = msg;
        e.line = line;
        e.col = col;
        e.is_error = is_error;
        self.diags[self.diag_count] = e;
        self.diag_count++;
    }
}

// A soft (type) mismatch — warning by default, error under --strict.
fn void TypeChecker.soft(TypeChecker* self, char* msg, int line, int col)
{
    self.diag(msg, line, col, false);
}

// A hard error (always an error, even without --strict).
fn void TypeChecker.hard(TypeChecker* self, char* msg, int line, int col)
{
    self.diag(msg, line, col, true);
}

fn bool span_eq(char* p, usz len, char* lit, usz lit_len)
{
    if (len != lit_len) return false;
    for (usz i = 0; i < len; i++) if (p[i] != lit[i]) return false;
    return true;
}

// Map a primitive type name span to its Prim tag.
fn Prim prim_of_name(char* p, usz len)
{
    if (span_eq(p, len, "i8", 2))   return Prim.PRIM_I8;
    if (span_eq(p, len, "i16", 3))  return Prim.PRIM_I16;
    if (span_eq(p, len, "i32", 3))  return Prim.PRIM_I32;
    if (span_eq(p, len, "i64", 3))  return Prim.PRIM_I64;
    if (span_eq(p, len, "i128", 4)) return Prim.PRIM_I128;
    if (span_eq(p, len, "isize", 5))return Prim.PRIM_ISIZE;
    if (span_eq(p, len, "u8", 2))   return Prim.PRIM_U8;
    if (span_eq(p, len, "u16", 3))  return Prim.PRIM_U16;
    if (span_eq(p, len, "u32", 3))  return Prim.PRIM_U32;
    if (span_eq(p, len, "u64", 3))  return Prim.PRIM_U64;
    if (span_eq(p, len, "u128", 4)) return Prim.PRIM_U128;
    if (span_eq(p, len, "usize", 5))return Prim.PRIM_USIZE;
    if (span_eq(p, len, "f32", 3))  return Prim.PRIM_F32;
    if (span_eq(p, len, "f64", 3))  return Prim.PRIM_F64;
    if (span_eq(p, len, "bool", 4)) return Prim.PRIM_BOOL;
    if (span_eq(p, len, "ptr", 3))  return Prim.PRIM_PTR;
    if (span_eq(p, len, "Str", 3))  return Prim.PRIM_STR;
    if (span_eq(p, len, "char", 4)) return Prim.PRIM_CHAR;
    return Prim.PRIM_NONE;
}

fn Prim type_prim(Node* t)
{
    if (t == null) return Prim.PRIM_NONE;
    if (t.kind == Nk.NODE_TYPE_PRIMITIVE)
    {
        return prim_of_name(t.p.ident.name_ptr, t.p.ident.name_len);
    }
    if (t.kind == Nk.NODE_EXPR_UNIT) return Prim.PRIM_UNIT;
    return Prim.PRIM_NONE;
}

fn bool prim_is_int(Prim p)
{
    switch (p)
    {
        case PRIM_I8: case PRIM_I16: case PRIM_I32: case PRIM_I64: case PRIM_I128:
        case PRIM_U8: case PRIM_U16: case PRIM_U32: case PRIM_U64: case PRIM_U128:
        case PRIM_ISIZE: case PRIM_USIZE:
            return true;
        default:
            return false;
    }
}

fn bool prim_is_float(Prim p)
{
    return p == Prim.PRIM_F32 || p == Prim.PRIM_F64;
}

fn bool prim_is_numeric(Prim p)
{
    return prim_is_int(p) || prim_is_float(p);
}

fn bool prim_is_signed(Prim p)
{
    return p == Prim.PRIM_I8 || p == Prim.PRIM_I16 || p == Prim.PRIM_I32
        || p == Prim.PRIM_I64 || p == Prim.PRIM_I128 || p == Prim.PRIM_ISIZE;
}

fn char* prim_name(Prim p)
{
    switch (p)
    {
        case PRIM_I8:   return "i8";
        case PRIM_I16:  return "i16";
        case PRIM_I32:  return "i32";
        case PRIM_I64:   return "i64";
        case PRIM_I128:  return "i128";
        case PRIM_ISIZE:  return "isize";
        case PRIM_U8:    return "u8";
        case PRIM_U16:  return "u16";
        case PRIM_U32:  return "u32";
        case PRIM_U64:   return "u64";
        case PRIM_U128:  return "u128";
        case PRIM_USIZE:  return "usize";
        case PRIM_F32:   return "f32";
        case PRIM_F64:  return "f64";
        case PRIM_BOOL: return "bool";
        case PRIM_PTR:  return "ptr";
        case PRIM_STR:  return "Str";
        case PRIM_CHAR: return "char";
        case PRIM_UNIT: return "()";
        default:        return "?";
    }
}

// Build (and cache) a canonical primitive type node.
fn Node* TypeChecker.mk_prim(TypeChecker* self, Prim p)
{
    int idx = (int)p;
    if (idx >= 0 && idx < 16 && self.prim_cache[idx] != null) return self.prim_cache[idx];

    Node* n;
    if (p == Prim.PRIM_UNIT)
    {
        n = ast::node0(self.arena, Nk.NODE_EXPR_UNIT, 0, 0);
    }
    else
    {
        char* name = prim_name(p);
        usz len = cstr_len(name);
        n = ast::node_name(self.arena, Nk.NODE_TYPE_PRIMITIVE, name, len, 0, 0);
    }
    if (idx >= 0 && idx < 16) self.prim_cache[idx] = n;
    return n;
}

fn usz cstr_len(char* s)
{
    usz n = 0;
    while (s[n] != 0) n++;
    return n;
}

fn Node* TypeChecker.mk_bottom(TypeChecker* self)
{
    return ast::node_bottom(self.arena, 0, 0);
}

// subtype(a, b) is "every value of type a is also a value of type b".
// Soundly conservative: when unsure (unresolved typevars, opaque paths) we
// return true so soft typing doesn't spam false warnings.
// Follow a type-alias reference (a NODE_TYPEVAR resolved to a `type X = ...`
// declaration) to the underlying type. Bounded to avoid alias cycles.
fn Node* TypeChecker.unfold(TypeChecker* self, Node* t)
{
    int guard = 0;
    while (t != null && t.kind == Nk.NODE_TYPEVAR && t.resolved != null && guard < 32)
    {
        Node* decl = t.resolved;
        if (decl.kind != Nk.NODE_DECL_TYPE) break;
        // type Name <generics>? = body  — the body is the last child.
        Node* body = decl.child_count >= 1 ? decl.children[decl.child_count - 1] : null;
        // Don't unfold to struct/union decls (those are nominal, not aliases).
        if (body == null) break;
        if (body.kind == Nk.NODE_DECL_STRUCT || body.kind == Nk.NODE_DECL_UNION) break;
        if (body == t) break;
        t = body;
        guard++;
    }
    return t;
}

// True when `t` denotes a non-scalar VALUE layout: a tuple type or a
// struct/union declaration (seen directly or through a nominal type name).
// Scalars (int/float/bool/ptr) return false. Used to gate meaningless
// aggregate → scalar `as` casts.
fn bool TypeChecker.is_aggregate_ty(TypeChecker* self, Node* t)
{
    if (t == null) return false;
    if (t.kind == Nk.NODE_TYPE_TUPLE) return true;
    if (t.kind == Nk.NODE_DECL_STRUCT || t.kind == Nk.NODE_DECL_UNION) return true;
    if (t.kind == Nk.NODE_TYPEVAR && t.resolved != null)
    {
        Node* d = t.resolved;
        if (d.kind == Nk.NODE_DECL_STRUCT || d.kind == Nk.NODE_DECL_UNION) return true;
        if (d.kind == Nk.NODE_DECL_TYPE && d.child_count >= 1)
        {
            Node* body = d.children[d.child_count - 1];
            return body != null
               && (body.kind == Nk.NODE_DECL_STRUCT || body.kind == Nk.NODE_DECL_UNION);
        }
    }
    return false;
}

fn bool TypeChecker.subtype(TypeChecker* self, Node* a, Node* b)
{
    // Depth-guarded wrapper: a 1000-deep ∩/∪ type chain would otherwise recurse
    // until the stack overflows. Past the cap, answer permissively (soft typing).
    if (self.sub_depth >= MAX_SUBTYPE_DEPTH) return true;
    self.sub_depth++;
    bool r = self.subtype_body(a, b);
    self.sub_depth--;
    return r;
}

fn bool TypeChecker.subtype_body(TypeChecker* self, Node* a, Node* b)
{
    a = self.unfold(a);
    b = self.unfold(b);
    if (a == null || b == null) return true;     // unknown: be permissive
    if (a == b) return true;

    // ⊥ <: anything (empty set is a subset of every set).
    if (a.kind == Nk.NODE_TYPE_BOTTOM || a.kind == Nk.NODE_LIT_BOTTOM) return true;

    // a <: (B1 ∪ B2)  iff  a <: B1  or  a <: B2
    if (b.kind == Nk.NODE_TYPE_UNION)
    {
        for (usz i = 0; i < b.child_count; i++)
        {
            if (self.subtype(a, b.children[i])) return true;
        }
        return false;
    }
    // (A1 ∪ A2) <: b  iff  A1 <: b  and  A2 <: b
    if (a.kind == Nk.NODE_TYPE_UNION)
    {
        for (usz i = 0; i < a.child_count; i++)
        {
            if (!self.subtype(a.children[i], b)) return false;
        }
        return true;
    }

    // a <: (B1 ∩ B2)  iff  a <: B1  and  a <: B2
    if (b.kind == Nk.NODE_TYPE_INTERSECT)
    {
        for (usz i = 0; i < b.child_count; i++)
        {
            if (!self.subtype(a, b.children[i])) return false;
        }
        return true;
    }
    // (A1 ∩ A2) <: b  iff  A1 <: b  or  A2 <: b
    if (a.kind == Nk.NODE_TYPE_INTERSECT)
    {
        for (usz i = 0; i < a.child_count; i++)
        {
            if (self.subtype(a.children[i], b)) return true;
        }
        return false;
    }

    // Refinements (e.g. i32 ∩ (> 0)) are predicates we don't evaluate here;
    // treat a refinement as compatible with its base on the value level.
    if (b.kind == Nk.NODE_TYPE_REFINEMENT) return true;
    if (a.kind == Nk.NODE_TYPE_REFINEMENT) return true;

    // Negation: a <: ¬B  holds exactly when a and B are provably DISJOINT
    // (no value belongs to both). We can decide this for primitives, pointers,
    // and unions; otherwise we stay permissive (soft typing).
    if (b.kind == Nk.NODE_TYPE_NEGATION)
    {
        Node* inner = b.child_count >= 1 ? b.children[0] : null;
        if (inner == null) return true;
        return self.disjoint(a, inner);
    }
    // (A1 ∩ ¬A2) etc. on the left: an intersection with a negation is handled
    // by the intersect rules above; a bare ¬A on the left is permissive.
    if (a.kind == Nk.NODE_TYPE_NEGATION) return true;

    // Primitives: exact identity (Pride has NO implicit numeric promotion).
    Prim pa = type_prim(a);
    Prim pb = type_prim(b);
    if (pa != Prim.PRIM_NONE && pb != Prim.PRIM_NONE)
    {
        return pa == pb;
    }

    // Array-to-element pointer decay: *[T; N] <: *T. An allocated array's
    // address IS the address of its first element — exactly what
    // `let p : *i64 = alloc [i64; 10]` means (v.md §15). Applied before the
    // invariant rule, which would otherwise reject the allocation idiom.
    if (a.kind == Nk.NODE_TYPE_PTR && a.child_count >= 1
        && b.kind == Nk.NODE_TYPE_PTR && b.child_count >= 1)
    {
        Node* aelem = self.unfold(a.children[0]);
        if (aelem != null && aelem.kind == Nk.NODE_TYPE_ARRAY
            && aelem.child_count >= 1)
        { return self.subtype(aelem.children[0], b.children[0]); }
    }
    // Pointers: *T <: *U iff T <: U and U <: T (invariant). ptr is top pointer.
    if (a.kind == Nk.NODE_TYPE_PTR && b.kind == Nk.NODE_TYPE_PTR)
    {
        Node* ta = a.child_count >= 1 ? a.children[0] : null;
        Node* tb = b.child_count >= 1 ? b.children[0] : null;
        return self.same_type(ta, tb);
    }
    // any typed pointer <: ptr (the untyped pointer)
    if (a.kind == Nk.NODE_TYPE_PTR && pb == Prim.PRIM_PTR) return true;
    if (pa == Prim.PRIM_PTR && b.kind == Nk.NODE_TYPE_PTR) return true;

    // null literal is a subtype of any pointer type.
    if (a.kind == Nk.NODE_LIT_NULL && (b.kind == Nk.NODE_TYPE_PTR || pb == Prim.PRIM_PTR)) return true;

    // Tuples: componentwise, same arity.
    if (a.kind == Nk.NODE_TYPE_TUPLE && b.kind == Nk.NODE_TYPE_TUPLE)
    {
        if (a.child_count != b.child_count) return false;
        for (usz i = 0; i < a.child_count; i++)
        {
            if (!self.subtype(a.children[i], b.children[i])) return false;
        }
        return true;
    }

    // Tensors: same rank, compatible element type, and matching constant dims.
    // A dimension that is non-constant on either side is treated as a wildcard.
    // Element compatibility is lenient between float kinds (a tensor literal's
    // f64 elements adapt to a declared f32 tensor), matching scalar literals.
    if (a.kind == Nk.NODE_TYPE_TENSOR && b.kind == Nk.NODE_TYPE_TENSOR)
    {
        if (a.child_count != b.child_count) return false;   // differing rank
        Node* ae = a.child_count >= 1 ? a.children[0] : null;
        Node* be = b.child_count >= 1 ? b.children[0] : null;
        if (!self.elem_compatible(ae, be)) return false;    // element type
        for (usz i = 1; i < a.child_count; i++)
        {
            long da = tensor_dim_const(a.children[i]);
            long db = tensor_dim_const(b.children[i]);
            if (da >= 0 && db >= 0 && da != db) return false;
        }
        return true;
    }

    // Arrays / slices: element-compatible.
    if ((a.kind == Nk.NODE_TYPE_ARRAY || a.kind == Nk.NODE_TYPE_SLICE)
        && (b.kind == Nk.NODE_TYPE_ARRAY || b.kind == Nk.NODE_TYPE_SLICE))
    {
        Node* ea = a.child_count >= 1 ? a.children[0] : null;
        Node* eb = b.child_count >= 1 ? b.children[0] : null;
        return self.same_type(ea, eb);
    }

    // Function types: contravariant in argument, covariant in result.
    if (a.kind == Nk.NODE_TYPE_FN && b.kind == Nk.NODE_TYPE_FN)
    {
        Node* a_arg = a.child_count >= 1 ? a.children[0] : null;
        Node* a_ret = a.child_count >= 2 ? a.children[1] : null;
        Node* b_arg = b.child_count >= 1 ? b.children[0] : null;
        Node* b_ret = b.child_count >= 2 ? b.children[1] : null;
        return self.subtype(b_arg, a_arg) && self.subtype(a_ret, b_ret);
    }

    // Named/path types and unresolved type variables: compare by identity of
    // the resolved declaration when available, else by name; else be permissive.
    if (a.kind == Nk.NODE_TYPEVAR && b.kind == Nk.NODE_TYPEVAR)
    {
        if (a.resolved != null && a.resolved == b.resolved) return true;
        return self.same_type(a, b);
    }

    if (a.kind == Nk.NODE_TYPE_GENERIC_APP || b.kind == Nk.NODE_TYPE_GENERIC_APP) return true;
    if (a.kind == Nk.NODE_TYPE_PATH || b.kind == Nk.NODE_TYPE_PATH) return true;
    if (a.kind == Nk.NODE_TYPEVAR || b.kind == Nk.NODE_TYPEVAR) return true;
    if (a.kind == Nk.NODE_TYPE_FORALL || b.kind == Nk.NODE_TYPE_FORALL) return true;
    if (a.kind == Nk.NODE_TYPE_EXISTS || b.kind == Nk.NODE_TYPE_EXISTS) return true;

    // Unit type
    if (pa == Prim.PRIM_UNIT && pb == Prim.PRIM_UNIT) return true;

    // Different concrete shapes: not a subtype.
    return false;
}

// Element-type compatibility for tensors: exact, or float↔float / int↔int
// (so a literal tensor's inferred default element adapts to the declared one).
fn bool TypeChecker.elem_compatible(TypeChecker* self, Node* a, Node* b)
{
    if (self.same_type(a, b)) return true;
    Prim pa = type_prim(self.unfold(a));
    Prim pb = type_prim(self.unfold(b));
    if (prim_is_float(pa) && prim_is_float(pb)) return true;
    if (prim_is_int(pa) && prim_is_int(pb)) return true;
    return false;
}

// Structural type equality (mutual subtyping for the simple cases).
// Are types `a` and `b` provably disjoint (no value in both)? Used to decide
// `a <: ¬b`. Conservative: returns true only when we can prove disjointness;
// returns false ("might overlap") otherwise, keeping soft typing permissive.
fn bool TypeChecker.disjoint(TypeChecker* self, Node* a, Node* b)
{
    if (self.sub_depth >= MAX_SUBTYPE_DEPTH) return false;   // can't prove: assume overlap
    self.sub_depth++;
    bool r = self.disjoint_body(a, b);
    self.sub_depth--;
    return r;
}

fn bool TypeChecker.disjoint_body(TypeChecker* self, Node* a, Node* b)
{
    a = self.unfold(a);
    b = self.unfold(b);
    if (a == null || b == null) return false;

    // A union is disjoint from b iff every member is disjoint from b.
    if (a.kind == Nk.NODE_TYPE_UNION)
    {
        for (usz i = 0; i < a.child_count; i++)
        {
            if (!self.disjoint(a.children[i], b)) return false;
        }
        return true;
    }
    if (b.kind == Nk.NODE_TYPE_UNION)
    {
        for (usz i = 0; i < b.child_count; i++)
        {
            if (!self.disjoint(a, b.children[i])) return false;
        }
        return true;
    }

    // Distinct value-kinds (number vs bool vs pointer) are disjoint.
    int ka = self.value_kind(a);
    int kb = self.value_kind(b);
    if (ka != VK_UNKNOWN && kb != VK_UNKNOWN && ka != kb) return true;

    // Two distinct primitives are disjoint (i32 and i64 share no values).
    Prim pa = type_prim(a);
    Prim pb = type_prim(b);
    if (pa != Prim.PRIM_NONE && pb != Prim.PRIM_NONE) return pa != pb;

    // Distinct named struct/union types are disjoint (nominal).
    if (a.kind == Nk.NODE_TYPEVAR && b.kind == Nk.NODE_TYPEVAR
        && a.resolved != null && b.resolved != null)
    {
        return a.resolved != b.resolved;
    }

    return false;   // can't prove disjoint -> assume they might overlap
}

fn bool TypeChecker.same_type(TypeChecker* self, Node* a, Node* b)
{
    if (self.sub_depth >= MAX_SUBTYPE_DEPTH) return true;
    self.sub_depth++;
    bool r = self.same_type_body(a, b);
    self.sub_depth--;
    return r;
}

fn bool TypeChecker.same_type_body(TypeChecker* self, Node* a, Node* b)
{
    if (a == null || b == null) return true;
    if (a == b) return true;

    Prim pa = type_prim(a);
    Prim pb = type_prim(b);
    if (pa != Prim.PRIM_NONE && pb != Prim.PRIM_NONE) return pa == pb;

    if (a.kind != b.kind) return false;

    // Compare names for named types / type variables.
    if (a.kind == Nk.NODE_TYPEVAR || a.kind == Nk.NODE_TYPE_PRIMITIVE)
    {
        if (a.resolved != null && a.resolved == b.resolved) return true;
        return span_eq(a.p.ident.name_ptr, a.p.ident.name_len,
                       b.p.ident.name_ptr, b.p.ident.name_len);
    }

    if (a.child_count != b.child_count) return false;
    for (usz i = 0; i < a.child_count; i++)
    {
        if (!self.same_type(a.children[i], b.children[i])) return false;
    }
    return true;
}

// Infer the type of an expression node, caching it on node.type_annotation.
// Returns null when the type is genuinely unknown (kept permissive downstream).
fn Node* TypeChecker.synth(TypeChecker* self, Node* e)
{
    if (e == null) return null;
    if (e.type_annotation != null) return e.type_annotation;
    // Already visited (even if its type came out unknown): don't re-emit
    // diagnostics for the same node on a second walk.
    if ((e.flags & ast::FLAG_TYPED) != 0) return null;
    // Depth guard: deep expression/type trees would overflow the stack.
    if (self.sub_depth >= MAX_SUBTYPE_DEPTH) return null;
    e.flags |= ast::FLAG_TYPED;

    self.sub_depth++;
    Node* t = self.synth_uncached(e);
    self.sub_depth--;
    if (t != null) e.type_annotation = t;
    return t;
}

fn Node* TypeChecker.synth_uncached(TypeChecker* self, Node* e)
{
    switch (e.kind)
    {
        case Nk.NODE_LIT_INT:
            // Default integer literal type is i64 (v.md §3.4).
            return self.int_lit_type(e);
        case Nk.NODE_LIT_FLOAT:
            // Honour the parsed width suffix: `2.0f32` IS an f32 (the parser
            // records it in lit_float.bits). Typing it f64 made every mixed
            // f32 expression promote to f64 while codegen emitted f32
            // operands — the val's annotation and its LLVM type disagreed
            // (e.g. `fptosi double` on a float). Default f64 unchanged.
            if (e.p.lit_float.bits == 32) { return self.mk_prim(Prim.PRIM_F32); }
            return self.mk_prim(Prim.PRIM_F64);
        case Nk.NODE_LIT_BOOL:
            return self.mk_prim(Prim.PRIM_BOOL);
        case Nk.NODE_LIT_CHAR:
            return self.mk_prim(Prim.PRIM_CHAR);
        case Nk.NODE_LIT_STRING:
            return self.mk_prim(Prim.PRIM_STR);
        case Nk.NODE_LIT_RAW_BYTES:
            // b"..." is *u8
            return ast::node1(self.arena, Nk.NODE_TYPE_PTR, self.mk_prim(Prim.PRIM_U8), 0, 0);
        case Nk.NODE_LIT_NULL:
            return self.mk_prim(Prim.PRIM_PTR);
        case Nk.NODE_LIT_BOTTOM:
        case Nk.NODE_UB_BANG:
        case Nk.NODE_STMT_UNREACHABLE:
        case Nk.NODE_STMT_TRAP:
            return self.mk_bottom();

        case Nk.NODE_EXPR_UNIT:
            return self.mk_prim(Prim.PRIM_UNIT);

        case Nk.NODE_IDENT:
        case Nk.NODE_TYPEVAR:
            return self.synth_name(e);

        case Nk.NODE_EXPR_BINARY:
            return self.synth_binary(e);
        case Nk.NODE_EXPR_UNARY:
            return self.synth_unary(e);
        case Nk.NODE_EXPR_ALLOC:
            // `alloc T` / `alloc [T; N]` is a fresh pointer to the type
            // child (v.md §15). Without a synthesis the binder stayed
            // untyped, and a later `*p` deref fell to the junk `ptr`
            // fallback — loading the pointee AS a ptr (invalid IR the moment
            // an integer consumer saw it; `q as i32`-style casts hid it).
            if (e.child_count >= 1 && e.children[0] != null)
            {
                self.synth(e.children[0]);   // type errors inside the type child
                return ast::node1(self.arena, Nk.NODE_TYPE_PTR, e.children[0],
                                  e.line, e.col);
            }
            return null;
        case Nk.NODE_EXPR_ASSIGN:
            return self.synth_assign(e);

        case Nk.NODE_EXPR_CALL:
            return self.synth_call(e);

        case Nk.NODE_EXPR_TENSOR_LIT:
            return self.synth_tensor_lit(e);

        case Nk.NODE_EXPR_MATMUL:
            return self.synth_matmul(e);

        case Nk.NODE_EXPR_FIELD:
            return self.synth_field(e);

        case Nk.NODE_EXPR_METHOD_CALL:
            return self.synth_method_call(e);

        case Nk.NODE_EXPR_INDEX:
            return self.synth_index(e);

        case Nk.NODE_EXPR_STRUCT_LIT:
            return self.synth_struct_lit(e);

        case Nk.NODE_EXPR_FORMAT:
            // format!(...) produces the runtime format record { ptr, i64, i64 }.
            // Synthesize the template + argument expressions, and give the
            // result its TRUE aggregate type: it used to be untyped, so
            // consumers checked against nothing and `s as i64` compiled to
            // the invalid `bitcast i64 <struct>` (llvm-as rejects).
            for (usz ffi = 0; ffi < e.child_count; ffi++)
            {
                if (e.children[ffi] != null) self.synth(e.children[ffi]);
            }
            return ast::node3(self.arena, Nk.NODE_TYPE_TUPLE,
                              self.mk_prim(Prim.PRIM_PTR),
                              self.mk_prim(Prim.PRIM_I64),
                              self.mk_prim(Prim.PRIM_I64),
                              0, 0);

        case Nk.NODE_EXPR_TUPLE_LIT:
            // `(a, b, ...)` is the tuple of its element types. The
            // tuple-DESTRUCTURING let (`let (c, n) = (Blue, 7)`) stamps its
            // binders componentwise from exactly this synthesis — without it
            // the literal typed to null, the destructure stamped nothing, and
            // a match over a destructured enum binder compiled every arm as a
            // plain binder: no tag test existed in the lowering, so the FIRST
            // arm always fired no matter the scrutinee's tag.
            {
                Node* tt = ast::node_raw(self.arena, Nk.NODE_TYPE_TUPLE,
                                         e.line, e.col);
                if (tt == null) return null;
                bool complete = true;
                for (usz i = 0; i < e.child_count; i++)
                {
                    Node* et = self.synth(e.children[i]);
                    if (et == null) complete = false;
                    ast::add_child(self.arena, tt, et);
                }
                // All-or-nothing: a tuple type carrying null holes would be a
                // new hazard for every consumer walking type children; keep
                // the previous honest "unknown" for that case instead.
                if (!complete) return null;
                return tt;
            }

        case Nk.NODE_EXPR_CAST:
            // expr as Type — result is the target type (child 1).
            {
                Node* st = e.child_count >= 1 ? self.synth(e.children[0]) : null;
                Node* dt = e.child_count >= 2 ? e.children[1] : null;
                if (st != null && dt != null
                    && self.is_aggregate_ty(st) && !self.is_aggregate_ty(dt))
                {
                    // Aggregate → non-aggregate casts have no meaningful
                    // lowering: codegen used to emit the invalid
                    // `bitcast { ptr, i64, i64 } %x to i64` (which llvm-as
                    // rejects, or worse, silently truncates). Destructure the
                    // struct/tuple first; scalar↔scalar, ptr↔int and
                    // same-shape aggregate casts are unaffected.
                    self.hard("cannot cast a struct/tuple value to a scalar or pointer type (extract a field or component first)",
                              e.line, e.col);
                }
                return dt;
            }

        case Nk.NODE_EXPR_IF:
            return self.synth_if(e);

        case Nk.NODE_EXPR_MATCH:
            return self.synth_match(e);

        case Nk.NODE_EXPR_WHILE:
            return self.synth_while(e);

        case Nk.NODE_EXPR_BLOCK:
            return self.synth_block(e);

        case Nk.NODE_EXPR_FOR:
            // for binder in iterable — the lowering supports integer RANGES
            // (`lo..hi`, `lo..=hi`, `lo..hi by step`) only. Any other iterable
            // (array literal, tuple, an arbitrary expr) used to walk into a
            // lowering that fabricated an undefined loop variable and a
            // constant-zero guard: a silently broken module that even
            // llvm-as rejects. Loud here, so emission is skipped instead.
            {
                Node* iter = e.child_count >= 2 ? e.children[1] : null;
                if (iter != null
                    && iter.kind != Nk.NODE_EXPR_RANGE
                    && iter.kind != Nk.NODE_EXPR_RANGE_STEP)
                {
                    self.hard("for-loops iterate integer ranges (for i in lo..hi, lo..=hi, lo..hi by step)",
                              iter.line, iter.col);
                }
                for (usz fci = 0; fci < e.child_count; fci++)
                {
                    if (e.children[fci] != null) self.synth(e.children[fci]);
                }
                return null;
            }

        case Nk.NODE_EXPR_RANGE:
            if (e.child_count >= 1) return self.synth(e.children[0]);
            return null;

        case Nk.NODE_EXPR_RANGE_STEP:
            // start..end by step — synthesize all three operands (so the step
            // expression is type-checked too); the range's element type is the
            // start operand's type, matching NODE_EXPR_RANGE above.
            {
                Node* step_ty = e.child_count >= 3 ? self.synth(e.children[2]) : null;
                if (step_ty != null)
                {
                    Prim step_prim = type_prim(self.unfold(step_ty));
                    if (step_prim != Prim.PRIM_NONE && !prim_is_numeric(step_prim))
                    {
                        self.soft("range step must be numeric", e.line, e.col);
                    }
                }
                if (e.child_count >= 2) self.synth(e.children[1]);
                if (e.child_count >= 1) return self.synth(e.children[0]);
            }
            return null;

        case Nk.NODE_EXPR_PIPELINE:
        case Nk.NODE_FIXPOINT:
            // value flows through the pipeline; type of the left operand.
            if (e.child_count >= 1) return self.synth(e.children[0]);
            return null;

        case Nk.NODE_EFFECT_HANDLE:
            // handle computation | arm... — the expression's type is the
            // computation's type: a handler discharges effects, it does not
            // change the value type (each arm ends in resume(...) or yields
            // a fallback value coercion-compatible with the computation).
            // Without this case the generic default below walked the children
            // but stamped NOTHING on the handle node itself, so the join φ
            // in the ssi lowering (and any consumer of the handle's value —
            // a surrounding `+`, a binding ascription, a return) had no type
            // to bind to: inference then fell to the arm operand, which is
            // ABI-shaped (`ptr`, by resume's declared return) — producing
            // `phi ptr [ 42, ... ]` (llvm-as rejects) or GEPs on ptrs.
            {
                Node* comp_t = null;
                for (usz hi = 0; hi < e.child_count; hi++)
                {
                    Node* ec = e.children[hi];
                    if (ec == null) continue;
                    Node* t = self.synth(ec);
                    if (hi == 0 && ec.kind != Nk.NODE_HANDLER_ARM) comp_t = t;
                }
                return comp_t;
            }

        case Nk.NODE_HANDLER_ARM:
        {
            // Argument binders receive the op's DECLARED parameter types —
            // arity-driven, the same ground truth the lowering uses to lay
            // out the runtime arg slots (an effective binder beyond the op's
            // arity is the continuation k). Without this every binder fell
            // back to i64 at codegen: a float op arg came back through its
            // slot as raw bits fed to an integer op (`mul nsw i64 %x, 2.0`).
            long nargs = ast::effect_op_arity_of_arm(e);
            Node* op_decl = ast::effect_op_decl_of_arm(e);
            usz alast = e.child_count >= 1 ? e.child_count - 1 : 0;

            // Continuation slot: exactly one EFFECTIVE binder beyond arity.
            usz cont_i = 0;
            if (nargs >= 0)
            {
                usz eff = 0;
                usz last_eff = 0;
                for (usz ci = 1; ci < alast; ci++)
                {
                    if (ast::is_arm_unit_binder(e.children[ci])) continue;
                    eff++;
                    last_eff = ci;
                }
                if ((long)eff == nargs + 1) cont_i = last_eff;
            }

            int aslot = 0;
            for (usz i = 1; i < alast; i++)
            {
                Node* b = e.children[i];
                if (b == null || i == cont_i) continue;
                if (ast::is_arm_unit_binder(b)) continue;
                aslot = self.stamp_arm_pattern(b, op_decl, aslot);
            }

            // Head + body synthesize normally (resolution and effect checking
            // both need the body walked in this scope).
            Node* bt = null;
            for (usz i = 0; i < e.child_count; i++)
            {
                Node* c = e.children[i];
                if (c == null || i == alast) continue;
                self.synth(c);
            }
            if (alast >= 1)
            {
                bt = self.synth(e.children[alast]);
            }
            return bt;
        }

        default:
            // Recurse so nested expressions still get checked, but report no type.
            for (usz i = 0; i < e.child_count; i++) self.synth(e.children[i]);
            return null;
    }
}

// A call  f(a, b, ...). Child 0 is the callee; children 1.. are arguments.
// Synthesizes argument types, then instantiates the callee's (possibly generic)
// signature to recover a concrete result type.
fn Node* TypeChecker.synth_call(TypeChecker* self, Node* e)
{
    // Newtype construction: Dollars(expr) — callee resolves to NODE_DECL_NEWTYPE.
    // The result type is the newtype itself (its name typevar).
    {
        Node* callee_n = e.child_count >= 1 ? e.children[0] : null;
        if (callee_n != null && callee_n.resolved != null
            && callee_n.resolved.kind == Nk.NODE_DECL_NEWTYPE)
        {
            // Synthesize the argument (the underlying value).
            for (usz ai = 1; ai < e.child_count; ai++)
            { self.synth(e.children[ai]); }
            // Return the newtype name as the type of the call expression.
            e.type_annotation = callee_n;
            return callee_n;
        }
    }

    // Enum variant construction: Some(x), None, Ok(v), Err(e)
    // The callee resolves to a NODE_ENUM_VARIANT; return the parent enum type.
    {
        Node* callee_n = e.child_count >= 1 ? e.children[0] : null;
        if (callee_n != null && callee_n.resolved != null
            && callee_n.resolved.kind == Nk.NODE_ENUM_VARIANT)
        {
            Node* variant = callee_n.resolved;
            // The variant is back-linked to its owning DECL_ENUM via .resolved
            // (see decl_type's NODE_ENUM_VARIANT case for why .resolved and
            // not .type_annotation). Synthesize the payload args, then the
            // construction's type IS the enum's tagged repr — annotating it
            // with the variant's name ident collapsed to an opaque ptr in
            // codegen (tensor heap path, invalid `store double` of ints).
            for (usz ai = 1; ai < e.child_count; ai++)
            { self.synth(e.children[ai]); }
            if (variant.resolved != null && variant.resolved.kind == Nk.NODE_DECL_ENUM)
            {
                e.type_annotation = variant.resolved;
                return variant.resolved;
            }
            if (variant.child_count >= 1)
            {
                Node* vname = variant.children[0];
                e.type_annotation = vname;
                return vname;
            }
        }
    }

    if (e.child_count < 1) return null;

    // Synthesize every argument first (drives nested checks too).
    for (usz i = 1; i < e.child_count; i++)
    {
        self.synth(e.children[i]);
    }

    Node* callee = e.children[0];
    self.synth(callee);

    // The callee's signature: prefer the resolved fn declaration's signature.
    Node* sig = null;
    if (callee != null && callee.resolved != null
        && callee.resolved.kind == Nk.NODE_DECL_FN)
    {
        sig = self.fn_signature_type(callee.resolved);
    }
    else if (callee != null && callee.kind == Nk.NODE_EXPR_FIELD)
    {
        // Cross-module call: `m::sq(n)`. Resolve the member fn in its module.
        Node* xmem = self.cross_module_member(callee);
        if (xmem != null && xmem.kind == Nk.NODE_DECL_FN)
        {
            sig = self.fn_signature_type(xmem);
            if (callee.child_count >= 2) callee.children[1].resolved = xmem;
        }
    }
    if (sig == null && callee != null && callee.type_annotation != null
        && callee.type_annotation.kind == Nk.NODE_TYPE_FN)
    {
        sig = callee.type_annotation;
    }
    if (sig == null)
    {
        // No callable signature. If the callee has a KNOWN non-function type
        // (a primitive, pointer, or aggregate), calling it is a mistake a
        // library author would otherwise hit silently. Stay quiet when the
        // type is unknown/abstract (generic param, cross-module, unresolved).
        if (callee != null)
        {
            Node* ct = self.unfold(callee.type_annotation);
            if (ct != null && !is_generic_param_type(ct))
            {
                bool non_callable = false;
                Prim cp = type_prim(ct);
                if (prim_is_numeric(cp) || cp == Prim.PRIM_BOOL
                    || cp == Prim.PRIM_CHAR || cp == Prim.PRIM_STR)
                {
                    non_callable = true;
                }
                else if (ct.kind == Nk.NODE_TYPE_TUPLE
                    || ct.kind == Nk.NODE_TYPE_ARRAY
                    || ct.kind == Nk.NODE_TYPE_SLICE)
                {
                    non_callable = true;
                }
                else if (self.is_aggregate_type(ct))
                {
                    non_callable = true;
                }
                if (non_callable)
                {
                    self.soft("call of a non-function value", e.line, e.col);
                }
            }
        }
        return null;
    }

    // Instantiate with the actual argument nodes.
    usz argc = e.child_count - 1;
    Node* result = self.instantiate_call(sig, &e.children[1], argc);

    // Check each actual argument against the (instantiated) parameter type.
    self.check_call_args(sig, &e.children[1], argc, e);

    return result;
}

// Verify call arguments fit the declared parameter type(s). For a generic
// callee, parameter types are instantiated from the same inference, so a
// concrete mismatch (e.g. i64 where i32 expected) is reported (soft).
fn void TypeChecker.check_call_args(TypeChecker* self, Node* sig, Node** args, usz argc, Node* call_site)
{
    // Recover the parameter type (unwrapping the effect-row form).
    Node* param_t = null;
    Node* lhs = sig.child_count >= 1 ? sig.children[0] : null;
    Node* rhs = sig.child_count >= 2 ? sig.children[1] : null;
    if (rhs != null && rhs.kind == Nk.NODE_EFFECT_ROW
        && lhs != null && lhs.kind == Nk.NODE_TYPE_FN)
    {
        param_t = lhs.child_count >= 1 ? lhs.children[0] : null;
    }
    else
    {
        param_t = lhs;
    }
    if (param_t == null) return;

    // Determine how many arguments the signature expects:
    //   ()        -> 0   (unit parameter)
    //   (A, B, …) -> N   (tuple parameter)
    //   T         -> 1   (single parameter)
    Node* pcount_t = self.unfold(param_t);
    usz expected_count = 1;
    if (pcount_t != null && pcount_t.kind == Nk.NODE_EXPR_UNIT)
    {
        expected_count = 0;
    }
    else if (pcount_t != null && pcount_t.kind == Nk.NODE_TYPE_TUPLE)
    {
        expected_count = pcount_t.child_count;
    }
    if (argc != expected_count)
    {
        if (argc < expected_count)
        {
            self.soft("too few arguments in call", call_site.line, call_site.col);
        }
        else
        {
            self.soft("too many arguments in call", call_site.line, call_site.col);
        }
    }

    // Build the same inference bindings so generic params resolve concretely.
    TypeBindings b;
    b.clear();
    Node* pt = self.unfold(param_t);
    if (pt != null && pt.kind == Nk.NODE_TYPE_TUPLE)
    {
        for (usz i = 0; i < pt.child_count && i < argc; i++)
        {
            Node* at = self.synth(args[i]);
            self.unify(pt.children[i], at, &b);
            Node* expected = self.substitute(pt.children[i], &b, 0);
            if (at != null && expected != null && !self.arg_fits(args[i], at, expected))
            {
                self.soft("call argument type does not match parameter type", args[i].line, args[i].col);
            }
        }
    }
    else if (argc >= 1)
    {
        Node* at = self.synth(args[0]);
        self.unify(param_t, at, &b);
        Node* expected = self.substitute(param_t, &b, 0);
        if (at != null && expected != null && !self.arg_fits(args[0], at, expected))
        {
            self.soft("call argument type does not match parameter type", args[0].line, args[0].col);
        }
    }

    // For each generic parameter that was inferred to a concrete type, verify
    // the inferred type satisfies the parameter's declared constraint.
    self.check_constraints(&b, call_site);
}

// Check that every inferred binding satisfies its parameter's constraint.
// A constraint is the second child of a NODE_PARAM: `T : Constraint`. The
// inferred type must be a subtype of (i.e. fit within) the constraint type.
fn void TypeChecker.check_constraints(TypeChecker* self, TypeBindings* b, Node* call_site)
{
    for (usz i = 0; i < b.count; i++)
    {
        Node* param = b.params[i];
        Node* inferred = b.args[i];
        if (param == null || inferred == null) continue;
        if (param.kind != Nk.NODE_PARAM) continue;
        if (param.child_count < 2) continue;          // no constraint

        Node* constraint = param.children[1];
        if (constraint == null) continue;

        if (!self.satisfies_constraint(inferred, constraint))
        {
            self.soft("type argument does not satisfy the generic constraint", call_site.line, call_site.col);
        }
    }
}

// Does `inferred` satisfy `constraint`? A constraint is one of:
//   * a built-in CONCEPT name (Num/Numeric/Int/Integer/Float/Ord/Eq) — checked
//     structurally against the inferred primitive,
//   * a generic-app concept (e.g. Eq<T>) — head concept checked, args ignored,
//   * any other type — checked by ordinary subtyping (so `T : SomeType` works),
//   * an unknown bare name — treated as satisfiable (soft: don't false-warn).
fn bool TypeChecker.satisfies_constraint(TypeChecker* self, Node* inferred, Node* constraint)
{
    Node* c = constraint;
    // peel a generic-app to its head concept
    if (c != null && c.kind == Nk.NODE_TYPE_GENERIC_APP && c.child_count >= 1) c = c.children[0];
    if (c == null) return true;

    if (c.kind == Nk.NODE_TYPEVAR || c.kind == Nk.NODE_IDENT)
    {
        char* nm = c.p.ident.name_ptr;
        usz len = c.p.ident.name_len;
        Prim p = type_prim(self.unfold(inferred));

        if (span_eq(nm, len, "Num", 3) || span_eq(nm, len, "Numeric", 7))
        {
            return prim_is_numeric(p);
        }
        if (span_eq(nm, len, "Int", 3) || span_eq(nm, len, "Integer", 7))
        {
            return prim_is_int(p);
        }
        if (span_eq(nm, len, "Float", 5) || span_eq(nm, len, "Floating", 8))
        {
            return prim_is_float(p);
        }
        if (span_eq(nm, len, "Ord", 3) || span_eq(nm, len, "Eq", 2)
            || span_eq(nm, len, "Comparable", 10))
        {
            // comparable/equatable scalars: numerics, bool, char
            return prim_is_numeric(p) || p == Prim.PRIM_BOOL || p == Prim.PRIM_CHAR;
        }
        // a resolved user trait/type, or an unknown concept name: be lenient
        if (c.resolved != null) return self.subtype(inferred, constraint);
        return true;   // unknown built-in concept → don't false-warn (soft)
    }
    // a structural type constraint
    return self.subtype(inferred, constraint);
}

// An argument fits a parameter if it's a subtype, OR it's an untyped integer
// literal targeting a numeric parameter (literals adapt to context, matching
// the arithmetic/comparison rules elsewhere).
// A type that is a generic type parameter (`T` resolving to its NODE_PARAM
// generic declaration). Such types are abstract within a generic body.
fn bool is_generic_param_type(Node* t)
{
    if (t == null) return false;
    return t.kind == Nk.NODE_TYPEVAR && t.resolved != null && t.resolved.kind == Nk.NODE_PARAM;
}

fn bool TypeChecker.arg_fits(TypeChecker* self, Node* arg, Node* actual, Node* expected)
{
    if (self.subtype(actual, expected)) return true;
    // A generic type parameter (`T` in `struct Box<T>` / `fn f<T>`) is abstract:
    // any value fits it, and a value of an abstract type fits any target. Real
    // monomorphization happens at call sites via inference; here `T` is opaque,
    // so refusing would produce false "mismatch" warnings inside generic bodies.
    if (is_generic_param_type(expected) || is_generic_param_type(actual)) return true;
    if (arg != null && arg.kind == Nk.NODE_LIT_INT)
    {
        Prim pe = type_prim(self.unfold(expected));
        if (prim_is_numeric(pe)) return true;
    }
    if (arg != null && arg.kind == Nk.NODE_LIT_FLOAT)
    {
        Prim pe = type_prim(self.unfold(expected));
        if (prim_is_float(pe)) return true;
    }
    // An UNTYPED-numeric expression (a bare int/float literal, or an if/match
    // whose every branch is itself untyped-numeric) adapts to a numeric target.
    // This lets `| n -> if c then 1 else 2` satisfy an i32 return even though
    // bare literals default to i64. Pride has no implicit promotion between
    // *typed* numerics, but unconstrained literals still take their context.
    if (arg != null && is_untyped_numeric_expr(arg))
    {
        Prim pe = type_prim(self.unfold(expected));
        Prim pa = type_prim(self.unfold(actual));
        // int-literal expr fits any numeric; float-literal expr fits floats only
        if (prim_is_float(pa)) { if (prim_is_float(pe)) return true; }
        else if (prim_is_numeric(pe)) return true;
    }
    return false;
}

// Is `e` an expression built only from untyped numeric literals via context-
// transparent forms (if / match / parens / blocks ending in such)? Such an
// expression's apparent type came from literal defaulting, so it may adapt to a
// numeric context. Conservative: any non-literal leaf makes it NOT untyped.
fn bool is_untyped_numeric_expr(Node* e)
{
    if (e == null) return false;
    switch (e.kind)
    {
        case Nk.NODE_LIT_INT:
        case Nk.NODE_LIT_FLOAT:
            return true;
        case Nk.NODE_EXPR_IF:
            // children: [cond, σ, then, (else)?, φ] — every branch body must be
            // untyped numeric. Skip cond/σ/φ markers.
            bool seen1 = false;
            for (usz i = 1; i < e.child_count; i++)
            {
                Node* c = e.children[i];
                if (c == null) continue;
                if (c.kind == Nk.NODE_SIGMA || c.kind == Nk.NODE_PHI) continue;
                if (!is_untyped_numeric_expr(c)) return false;
                seen1 = true;
            }
            return seen1;
        case Nk.NODE_EXPR_MATCH:
            // children: [scrut, σ, arm*, φ]; each arm's body must be untyped num
            bool seen2 = false;
            for (usz i = 1; i < e.child_count; i++)
            {
                Node* arm = e.children[i];
                if (arm == null || arm.kind != Nk.NODE_MATCH_ARM) continue;
                Node* body = arm.child_count >= 1 ? arm.children[arm.child_count - 1] : null;
                if (!is_untyped_numeric_expr(body)) return false;
                seen2 = true;
            }
            return seen2;
        default:
            return false;
    }
}

// A tensor type node: NODE_TYPE_TENSOR[elem, dim0, dim1, ...]. We read the
// element type and the constant dimensions (only constant int dims are checked;
// non-constant/generic dims are treated as "unknown" and skipped in shape math).

// Read a dimension as a constant, or -1 if not a known constant.
fn long tensor_dim_const(Node* dim)
{
    if (dim == null) return -1;
    if (dim.kind == Nk.NODE_LIT_INT) return (long)dim.p.lit_int.int_val;
    return -1;
}

// Build a Tensor type node from an element type and up to 4 constant dims.
fn Node* TypeChecker.mk_tensor(TypeChecker* self, Node* elem, long* dims, usz ndim)
{
    Node*[8] buf;
    usz n = 0;
    buf[n] = elem; n++;
    for (usz i = 0; i < ndim && n < 8; i++)
    {
        buf[n] = ast::node_int(self.arena, (ulong)dims[i], 64, true, 0, 0);
        n++;
    }
    return ast::node_n(self.arena, Nk.NODE_TYPE_TENSOR, &buf[0], n, 0, 0);
}

// Synthesize a tensor literal's type by inferring its shape from nesting and
// its element type from the leaves. Reports ragged (non-rectangular) shapes.
fn Node* TypeChecker.synth_tensor_lit(TypeChecker* self, Node* e)
{
    usz outer = e.child_count;

    // Empty tensor: unknown element type, shape [0].
    if (outer == 0)
    {
        long[1] d;
        d[0] = 0;
        return self.mk_tensor(self.mk_prim(Prim.PRIM_F64), &d[0], 1);
    }

    Node* first = e.children[0];
    bool nested = first != null && first.kind == Nk.NODE_EXPR_TENSOR_LIT;

    if (!nested)
    {
        // Rank-1 (vector): synth each element, element type is the join.
        Node* elem_t = null;
        for (usz i = 0; i < outer; i++)
        {
            Node* it = self.synth(e.children[i]);
            if (elem_t == null) elem_t = it;
        }
        if (elem_t == null) elem_t = self.mk_prim(Prim.PRIM_F64);
        long[1] d;
        d[0] = (long)outer;
        return self.mk_tensor(elem_t, &d[0], 1);
    }

    // Rank>=2: every row must be a tensor literal of equal shape (rectangular).
    // The result rank is 1 + (row rank); we read the first row's full shape and
    // prepend `outer`, so arbitrary-rank literals (rank-3, rank-4, …) work.
    usz inner = first.child_count;
    Node* elem_t = null;
    Node* row0_ty = null;
    for (usz i = 0; i < outer; i++)
    {
        Node* row = e.children[i];
        Node* rt = self.synth(row);   // recurse: row type (its own tensor shape)
        if (row == null) continue;
        if (row.kind != Nk.NODE_EXPR_TENSOR_LIT || row.child_count != inner)
        {
            self.soft("ragged tensor literal: rows have differing shapes", e.line, e.col);
        }
        if (rt != null && rt.kind == Nk.NODE_TYPE_TENSOR && rt.child_count >= 1)
        {
            if (row0_ty == null) row0_ty = rt;
            if (elem_t == null) elem_t = rt.children[0];   // element type
        }
    }
    if (elem_t == null) elem_t = self.mk_prim(Prim.PRIM_F64);

    // Build dims = [outer] ++ row0_dims  (row0_ty is TENSOR[elem, dim0, dim1, ...]).
    long[8] d;
    usz nd = 0;
    d[nd] = (long)outer; nd++;
    if (row0_ty != null)
    {
        for (usz i = 1; i < row0_ty.child_count && nd < 8; i++)
        {
            d[nd] = tensor_dim_const(row0_ty.children[i]); nd++;
        }
    }
    else
    {
        d[nd] = (long)inner; nd++;
    }
    return self.mk_tensor(elem_t, &d[0], nd);
}

// Given a type, return the struct/union declaration's field block, following
// type aliases and one level of pointer (for auto-deref). Returns null if the
// type is not a (pointer to a) struct/union.
fn Node* TypeChecker.struct_fields_of(TypeChecker* self, Node* ty)
{
    Node* t = self.unfold(ty);
    if (t == null) return null;

    // Auto-deref one pointer level:  p.x  where  p : *Vec
    if (t.kind == Nk.NODE_TYPE_PTR && t.child_count >= 1)
    {
        t = self.unfold(t.children[0]);
    }
    if (t == null) return null;

    // A generic application `Box<i32>` / `Stack<T>`: the fields live on the head
    // type constructor. Peel to the head (and unfold an alias under it).
    if (t.kind == Nk.NODE_TYPE_GENERIC_APP && t.child_count >= 1)
    {
        t = self.unfold(t.children[0]);
        if (t == null) return null;
    }

    // A module-qualified type `geom::Point` (NODE_TYPE_PATH[modHead, member]):
    // resolve the member type declaration inside its module.
    if (t.kind == Nk.NODE_TYPE_PATH && t.child_count >= 2)
    {
        Node* head = t.children[0];
        Node* member = t.children[t.child_count - 1];
        Node* moddecl = (head != null && head.resolved != null
            && head.resolved.kind == Nk.NODE_DECL_MOD) ? head.resolved : null;
        if (moddecl != null && member != null)
        {
            char* mp;
            usz ml;
            if (tc_name_of(member, &mp, &ml))
            {
                Node* td = mod_member_decl(moddecl, mp, ml);
                if (td != null) t = td;   // a struct/type decl; fall through
            }
        }
    }

    // A named type:  TypeVar resolved to its declaration. Two forms:
    //   * `type X = struct …`  → NODE_DECL_TYPE whose body is a Struct/Union,
    //   * `struct X …`         → NODE_DECL_STRUCT/UNION directly.
    Node* decl = null;
    if (t.kind == Nk.NODE_TYPEVAR && t.resolved != null) decl = t.resolved;
    // `t` may already BE a declaration (resolved from a module-qualified type).
    if (t.kind == Nk.NODE_DECL_STRUCT || t.kind == Nk.NODE_DECL_UNION
        || t.kind == Nk.NODE_DECL_TYPE) decl = t;
    if (decl == null) return null;

    Node* body = null;
    if (decl.kind == Nk.NODE_DECL_STRUCT || decl.kind == Nk.NODE_DECL_UNION)
    {
        body = decl;   // the decl itself carries the field block
    }
    else if (decl.kind == Nk.NODE_DECL_TYPE)
    {
        // body is the alias's last child: a Struct/Union node
        Node* b = decl.child_count >= 1 ? decl.children[decl.child_count - 1] : null;
        if (b != null && (b.kind == Nk.NODE_DECL_STRUCT || b.kind == Nk.NODE_DECL_UNION)) body = b;
    }
    if (body == null) return null;

    for (usz i = 0; i < body.child_count; i++)
    {
        Node* c = body.children[i];
        if (c != null && c.kind == Nk.NODE_EXPR_BLOCK) return c;
    }
    return null;
}

// Look up a field by name in a field block; returns its declared type or null.
fn Node* field_type(Node* fields, char* name, usz len)
{
    if (fields == null) return null;
    for (usz i = 0; i < fields.child_count; i++)
    {
        Node* fd = fields.children[i];
        if (fd == null || fd.kind != Nk.NODE_FIELD_DECL) continue;
        Node* nm = fd.child_count >= 1 ? fd.children[0] : null;
        if (nm == null) continue;
        if (span_eq(nm.p.ident.name_ptr, nm.p.ident.name_len, name, len))
        {
            return fd.child_count >= 2 ? fd.children[1] : null;
        }
    }
    return null;
}

fn bool field_exists(Node* fields, char* name, usz len)
{
    if (fields == null) return false;
    for (usz i = 0; i < fields.child_count; i++)
    {
        Node* fd = fields.children[i];
        if (fd == null || fd.kind != Nk.NODE_FIELD_DECL) continue;
        Node* nm = fd.child_count >= 1 ? fd.children[0] : null;
        if (nm != null && span_eq(nm.p.ident.name_ptr, nm.p.ident.name_len, name, len)) return true;
    }
    return false;
}

// Field access:  base.field  (Field[base, name]). Validates the field exists on
// the base's (auto-derefed) struct type and returns its type.
// Resolve a value expression to the module declaration it names, if any.
// Handles a direct module use (`mathx::sq` where `mathx` resolves to a Mod) and
// an aliased import (`use mathx as m` — `m` resolves to the Use node, whose
// resolver-stamped `type_annotation` points at the Mod decl).
fn Node* TypeChecker.mod_decl_of(TypeChecker* self, Node* base)
{
    if (base == null || base.resolved == null) return null;
    Node* r = base.resolved;
    if (r.kind == Nk.NODE_DECL_MOD) return r;
    // a `use ... as alias` node: the resolver stamps the target Mod on its
    // type_annotation; child 0 (the module path head) may also be linked.
    // (The parser only ever builds NODE_DECL_IMPORT for `use` statements —
    // NODE_DECL_USE is legacy/unused — but resolve.c3 treats both kinds
    // identically, so both must be checked here too.)
    if (r.kind == Nk.NODE_DECL_USE || r.kind == Nk.NODE_DECL_IMPORT)
    {
        if (r.type_annotation != null && r.type_annotation.kind == Nk.NODE_DECL_MOD)
        {
            return r.type_annotation;
        }
        if (r.child_count >= 1)
        {
            Node* path = r.children[0];
            Node* head = path;
            if (path != null && path.kind == Nk.NODE_MODULE_PATH && path.child_count >= 1)
            {
                head = path.children[0];
            }
            if (head != null && head.resolved != null && head.resolved.kind == Nk.NODE_DECL_MOD)
            {
                return head.resolved;
            }
        }
    }
    return null;
}

// Extract an identifier/typevar node's name span (typecheck-local; resolve's
// name_of lives in another module).
fn bool tc_name_of(Node* n, char** out_ptr, usz* out_len)
{
    if (n == null) return false;
    if (n.kind != Nk.NODE_IDENT && n.kind != Nk.NODE_TYPEVAR) return false;
    *out_ptr = n.p.ident.name_ptr;
    *out_len = n.p.ident.name_len;
    return true;
}

// Find a named member declaration inside a module's body block.
fn Node* mod_member_decl(Node* moddecl, char* name_ptr, usz name_len)
{
    if (moddecl == null) return null;
    for (usz i = 0; i < moddecl.child_count; i++)
    {
        Node* blk = moddecl.children[i];
        if (blk == null || blk.kind != Nk.NODE_EXPR_BLOCK) continue;
        for (usz j = 0; j < blk.child_count; j++)
        {
            Node* d = blk.children[j];
            if (d == null) continue;
            Node* dn = d.child_count >= 1 ? d.children[0] : null;
            if (dn == null) continue;
            char* p;
            usz l;
            if (!tc_name_of(dn, &p, &l)) continue;
            if (span_eq(p, l, name_ptr, name_len)) return d;
        }
    }
    return null;
}

// Resolve a cross-module member reference `Field[modBase, member]` to the member
// declaration (fn / type / const / ...), or null if not a module member access.
fn Node* TypeChecker.cross_module_member(TypeChecker* self, Node* fieldnode)
{
    if (fieldnode == null || fieldnode.kind != Nk.NODE_EXPR_FIELD || fieldnode.child_count < 2)
    {
        return null;
    }
    Node* base = fieldnode.children[0];
    Node* mname = fieldnode.children[1];
    Node* moddecl = self.mod_decl_of(base);
    if (moddecl == null || mname == null) return null;
    char* p;
    usz l;
    if (!tc_name_of(mname, &p, &l)) return null;
    return mod_member_decl(moddecl, p, l);
}

fn Node* TypeChecker.synth_field(TypeChecker* self, Node* e)
{
    if (e.child_count < 2) return null;
    Node* base = e.children[0];
    Node* name = e.children[1];

    // Cross-module member access: `m::value` / `mathx::CONST`. Resolve the
    // member declaration in its module and return its type. (A cross-module
    // function used as a value yields its fn-type.)
    Node* xmem = self.cross_module_member(e);
    if (xmem != null)
    {
        // Link the member name to its declaration for downstream passes.
        name.resolved = xmem;
        if (xmem.kind == Nk.NODE_DECL_FN) return self.fn_signature_type(xmem);
        // let/const/static: use the declared/inferred type if present.
        if (xmem.type_annotation != null) return xmem.type_annotation;
        return null;
    }

    Node* bt = self.synth(base);

    // If the base is a module/effect path or its type is unknown, don't warn
    // (could be qualified access like math::sin, handled elsewhere).
    if (bt == null) return null;

    // The base has an abstract generic-parameter type (e.g. `b.val` where val:T
    // inside a generic body). We can't know its fields until monomorphization,
    // so stay silent and return an abstract type rather than false-warning.
    if (is_generic_param_type(self.unfold(bt))) return null;

    // Untagged C-union field access (r13, v.md §9): `fb.i` reinterprets the
    // one shared 64-bit cell at that field's payload type — "same bytes,
    // different interpretation". This is the union's legitimate field
    // operation, so it synthesizes the payload type itself (a union is not a
    // struct; struct_fields_of only covers the tagged-repr internals).
    {
        Node* udecl = ast::union_decl_of(bt);
        if (udecl != null && ast::union_is_c_union(udecl) && name != null)
        {
            Node* payload_ty = null;
            int ord = ast::union_variant_lookup(udecl,
                name.p.ident.name_ptr, name.p.ident.name_len, &payload_ty);
            if (ord >= 0 && payload_ty != null) { return payload_ty; }
            self.soft("unknown field in union type", name.line, name.col);
            return null;
        }
    }

    Node* fields = self.struct_fields_of(bt);
    if (fields == null)
    {
        // A plain string literal binds as PRIM_STR (not a tuple); the runtime
        // repr is PrideStr { ptr, len } (runtime/compiler_rt.c). Map the two
        // slots by that layout — without this `s.len` on a let-bound literal
        // drew a misleading "field access on a non-struct value", and the
        // field went untyped downstream. `.cap` is NOT in the repr (it's a
        // property of the runtime's growable builder only): an unambiguous
        // hard error, since continuing used to GEP field 2 of a 2-field
        // record — invalid IR.
        if (name != null && name.kind == Nk.NODE_IDENT)
        {
            Node* btf = self.unfold(bt);
            if (btf != null && type_prim(btf) == Prim.PRIM_STR)
            {
                char* np = name.p.ident.name_ptr; usz nl = name.p.ident.name_len;
                if (nl == 3 && np[0]=='p' && np[1]=='t' && np[2]=='r')
                { return self.mk_prim(Prim.PRIM_PTR); }
                if (nl == 3 && np[0]=='l' && np[1]=='e' && np[2]=='n')
                { return self.mk_prim(Prim.PRIM_I64); }
                if (nl == 3 && np[0]=='c' && np[1]=='a' && np[2]=='p')
                {
                    self.hard("string has no `cap` field (Str is { ptr, len })",
                              name.line, name.col);
                    return null;
                }
                self.soft("unknown field in string (ptr, len exist)",
                          name.line, name.col);
                return null;
            }
        }
        // String/format record { ptr, i64(len), i64(cap) }: named slots by
        // layout (v.md §10.2 uses s.len on a Str). The type is a tuple, so
        // struct_fields_of saw nothing and this used to fall through to the
        // generic "non-struct" soft-warning while codegen defaulted the GEP
        // index to 0 — .len silently loaded the data POINTER. Resolve the
        // three layout names here; anything else stays the honest warning.
        Node* bt2 = self.unfold(bt);
        bool str_shape = bt2 != null && bt2.kind == Nk.NODE_TYPE_TUPLE
            && bt2.child_count >= 2 && bt2.children[0] != null
            && type_prim(self.unfold(bt2.children[0])) == Prim.PRIM_PTR;
        if (str_shape && name != null && name.kind == Nk.NODE_IDENT)
        {
            char* np = name.p.ident.name_ptr; usz nl = name.p.ident.name_len;
            if (nl == 3 && np[0]=='p' && np[1]=='t' && np[2]=='r')
            { return bt2.children[0]; }
            if (nl == 3 && np[0]=='l' && np[1]=='e' && np[2]=='n')
            { return bt2.children[1]; }
            if (nl == 3 && np[0]=='c' && np[1]=='a' && np[2]=='p'
                && bt2.child_count >= 3)
            { return bt2.children[2]; }
            self.soft("unknown field in string record (ptr, len, cap exist)", name.line, name.col);
            return null;
        }
        // A module-qualified type (`geom::Point`) we could not resolve to a
        // concrete struct (e.g. the module member isn't a struct, or it's an
        // unresolved cross-module reference): stay abstract-soft rather than
        // emit a misleading "non-struct" warning.
        Node* bu = self.unfold(bt);
        if (bu != null && bu.kind == Nk.NODE_TYPE_GENERIC_APP && bu.child_count >= 1)
        {
            bu = self.unfold(bu.children[0]);
        }
        if (bu != null && (bu.kind == Nk.NODE_TYPE_PATH || bu.kind == Nk.NODE_MODULE_PATH)) return null;

        // Base is typed but not a struct/pointer-to-struct: field access invalid.
        self.soft("field access on a non-struct value", e.line, e.col);
        return null;
    }

    if (name == null) return null;
    Node* ft = field_type(fields, name.p.ident.name_ptr, name.p.ident.name_len);
    if (ft == null)
    {
        self.soft("unknown field", name.line, name.col);
        return null;
    }
    // Generic-struct instantiation base (`pr.fst` with `pr : Pair<i64, f64>`):
    // the decl's field type names the type parameter — substitute the
    // instantiation's argument, or every consumer sees the boxed parameter
    // type instead of the concrete field type.  No-op for concrete bases.
    ft = ast::generic_payload_subst(bt, ft);
    return ft;
}

// Method-style call  base.name(args)  (MethodCall[base, name, args...]).
// Pride has no method system (functions are free and clause-based, v.md §6),
// so `v.foo(...)` means: access field `foo` on the base's struct (it must be a
// function-typed field), then call it. The field must exist; unknown members
// are flagged. The base type is synthesized so field lookup auto-derefs.
fn Node* TypeChecker.synth_method_call(TypeChecker* self, Node* e)
{
    if (e.child_count < 2) return null;
    Node* base = e.children[0];
    Node* name = e.children[1];

    // Synthesize the args (drives nested checks) regardless of resolution.
    for (usz i = 2; i < e.child_count; i++) self.synth(e.children[i]);

    Node* bt = self.synth(base);
    // Union variant constructor: `U.variant(args)` — the base name resolves
    // to a union decl and the member to one of its variants. The value's
    // type is the union's nominal type (the base TypeVar itself). Without
    // this the constructor typechecked to nothing: `let o = Opt.some(41)`
    // stayed untyped, so a later `match o` never learned its scrutinee was a
    // union and variant arms fell through to the irrefutable legacy path.
    if (bt == null && base != null && name != null && name.p.ident.name_ptr != null)
    {
        Node* udecl = ast::union_decl_of(base);
        if (udecl != null)
        {
            Node* payload_ty = null;
            int vord = ast::union_variant_lookup(udecl,
                name.p.ident.name_ptr, name.p.ident.name_len, &payload_ty);
            if (vord >= 0)
            {
                // Untagged C-union (r13): the whole value is one 64-bit
                // bitbox, so an aggregate payload (tuple/struct/array)
                // physically cannot fit the cell. Fail loudly instead of
                // silently truncating somebody's struct to 8 bytes.
                if (ast::union_is_c_union(udecl)
                    && !ast::union_payload_is_scalar(payload_ty))
                {
                    self.hard("C-union field payload doesn't fit the 64-bit cell "
                              "(untagged unions hold one scalar per field)",
                              e.line, e.col);
                }
                e.type_annotation = base;
                return base;
            }
        }
    }
    if (bt == null || name == null) return null;

    Node* fields = self.struct_fields_of(bt);
    if (fields == null)
    {
        self.soft("method-style call on a non-struct value (Pride has no methods; use a free function)", e.line, e.col);
        return null;
    }

    Node* ft = field_type(fields, name.p.ident.name_ptr, name.p.ident.name_len);
    if (ft == null)
    {
        self.soft("unknown member in method-style call", name.line, name.col);
        return null;
    }

    // If the field is function-typed, the call yields its return type.
    Node* fu = self.unfold(ft);
    if (fu != null && fu.kind == Nk.NODE_TYPE_FN)
    {
        Node* lhs = fu.child_count >= 1 ? fu.children[0] : null;
        Node* rhs = fu.child_count >= 2 ? fu.children[1] : null;
        if (rhs != null && rhs.kind == Nk.NODE_EFFECT_ROW
            && lhs != null && lhs.kind == Nk.NODE_TYPE_FN)
        {
            return lhs.child_count >= 2 ? lhs.children[1] : null;
        }
        return rhs;
    }

    // Field exists but isn't callable.
    self.soft("member is not a function and cannot be called", name.line, name.col);
    return ft;
}

// Indexing:  base[i]  (Index[base, idx]). The base must be a pointer, array,
// slice, or tensor; the result is the element type.
fn Node* TypeChecker.synth_index(TypeChecker* self, Node* e)
{
    if (e.child_count < 1) return null;
    Node* bt = self.unfold(self.synth(e.children[0]));
    Node* idx_t = null;
    if (e.child_count >= 2) idx_t = self.synth(e.children[1]);   // index expr

    // The index operand itself must be an integer (or a bare untyped integer
    // literal, or an unresolved/generic type we can't judge). Indexing with a
    // bool/float/aggregate is a mistake a caller would otherwise hit silently
    // (e.g. `arr[true]` or `arr[1.0]`), matching the soft-typing style used
    // for arithmetic/comparison elsewhere in this checker.
    if (idx_t != null && e.child_count >= 2)
    {
        Node* uidx = self.unfold(idx_t);
        if (!is_generic_param_type(uidx))
        {
            Prim pidx = type_prim(uidx);
            bool idx_is_int_literal = self.is_int_literal(e.children[1]);
            if (pidx != Prim.PRIM_NONE && !prim_is_numeric(pidx) && !idx_is_int_literal)
            {
                self.soft("index expression must be an integer", e.children[1].line, e.children[1].col);
            }
            else if (pidx != Prim.PRIM_NONE && prim_is_float(pidx))
            {
                self.soft("index expression must be an integer, not a float", e.children[1].line, e.children[1].col);
            }
        }
    }

    if (bt == null) return null;

    switch (bt.kind)
    {
        case Nk.NODE_TYPE_PTR:
        case Nk.NODE_TYPE_ARRAY:
        case Nk.NODE_TYPE_SLICE:
            return bt.child_count >= 1 ? bt.children[0] : null;
        case Nk.NODE_TYPE_TENSOR:
            // Tensor indexing drops ONE rank: Tensor<T; d0, d1, ...> →
            // Tensor<T; d1, ...>; only a rank-1 index yields the bare
            // element. (Yielding T for every rank meant `t[i][j]` typed and
            // lowered the outer index as though it indexed an f64 — the
            // row's rank header was then read as the value.)
            if (bt.child_count > 2)
            {
                // Result is [elem, dims[1..]] = children[0] + children[2..].
                Node*[8] tbuf;
                usz tn = 0;
                tbuf[tn] = bt.children[0]; tn++;
                for (usz ti = 2; ti < bt.child_count && tn < 8; ti++)
                { tbuf[tn] = bt.children[ti]; tn++; }
                return ast::node_n(self.arena, Nk.NODE_TYPE_TENSOR, &tbuf[0],
                                   tn, e.line, e.col);
            }
            return bt.child_count >= 1 ? bt.children[0] : null;
        default:
            // A Str is indexable: `s[i]` is the byte at offset i —
            // v.md §10.2 writes `IO.write_byte(s[i])`, and write_byte takes
            // u8, so the element type is u8. Without this arm a string base
            // fell to "indexing a non-indexable value" and downstream codegen
            // coerced whatever the tuple path produced.
            if (type_prim(bt) == Prim.PRIM_STR) return self.mk_prim(Prim.PRIM_U8);
            // ptr (untyped) indexes to unknown; anything else is an error.
            if (type_prim(bt) == Prim.PRIM_PTR) return null;
            self.soft("indexing a non-indexable value (expected pointer/array/slice)", e.line, e.col);
            return null;
    }
}

// Struct literal:  Name { field: val, ... }  (StructLit[typeName, FieldInit*]).
// Validates that every initializer names a real field whose type accepts the
// value, and warns about missing fields.
fn Node* TypeChecker.synth_struct_lit(TypeChecker* self, Node* e)
{
    if (e.child_count < 1) return null;
    Node* tyname = e.children[0];

    // Resolve the named type to its field block.
    Node* fields = self.struct_fields_of(tyname);
    if (fields == null)
    {
        // Struct-update syntax: base_val { field: val, ... }
        // tyname is the base value (e.g. Ident 'c1'), not a type name.
        // Synthesize the base value to get its type, then use THAT as the struct type.
        Node* base_ty = self.synth(tyname);
        // Synthesize all field values too.
        for (usz i = 1; i < e.child_count; i++)
        {
            Node* fi = e.children[i];
            if (fi != null && fi.child_count >= 2) self.synth(fi.children[1]);
        }
        // Return the base type (so the update expression has same type as base).
        // Set type_annotation on e so codegen can see the struct type.
        if (base_ty != null)
        {
            // Struct-UPDATE on an untagged C-union (`u { f: ... }`): the
            // repr is one 64-bit cell — updating one field while "keeping"
            // the others has no meaning on overlapping storage, and the
            // lowering cannot express it.  Loud rejection beats invalid IR.
            Node* upd_udecl = ast::union_decl_of(base_ty);
            if (ast::union_is_c_union(upd_udecl))
            {
                self.hard("update syntax on an untagged C-union is unsupported — construct the value from a single field instead",
                          e.line, e.col);
            }
            e.type_annotation = base_ty;
            return base_ty;
        }
        return tyname;
    }

    // Untagged C-union literal (one shared 64-bit cell — v.md §9): a
    // construction writes a SINGLE interpretation into the cell; listing
    // several fields would make later initialisers overlap earlier ones.
    // Require exactly one provided field (the value check below still runs
    // against the field's payload type).
    Node* lit_udecl = ast::union_decl_of(tyname);
    if (ast::union_is_c_union(lit_udecl))
    {
        int provided = 0;
        for (usz i = 1; i < e.child_count; i++)
        {
            Node* fi = e.children[i];
            if (fi != null && fi.kind == Nk.NODE_FIELD_INIT) provided++;
        }
        if (provided != 1)
        {
            self.hard("untagged C-union construction takes exactly one field — its fields overlap one 64-bit cell",
                      e.line, e.col);
        }
    }

    // Check each provided field initializer.
    for (usz i = 1; i < e.child_count; i++)
    {
        Node* fi = e.children[i];
        if (fi == null || fi.kind != Nk.NODE_FIELD_INIT) continue;
        Node* fname = fi.child_count >= 1 ? fi.children[0] : null;
        if (fname == null) continue;

        Node* ft = field_type(fields, fname.p.ident.name_ptr, fname.p.ident.name_len);
        if (ft == null)
        {
            self.soft("unknown field in struct literal", fname.line, fname.col);
            continue;
        }
        // `name: value` — check the value against the field type.
        if (fi.child_count >= 2)
        {
            Node* val = fi.children[1];
            Node* vt = self.synth(val);
            if (vt != null && !self.arg_fits(val, vt, ft))
            {
                self.soft("struct field value type does not match field type", val.line, val.col);
            }
        }
    }

    // Warn about required fields that were not provided.  (A C-union literal
    // provides exactly one interpretation by construction — the cell never
    // "contains all fields", so the missing-field warning is meaningless.)
    if (!ast::union_is_c_union(lit_udecl))
    {
        for (usz i = 0; i < fields.child_count; i++)
        {
            Node* fd = fields.children[i];
            if (fd == null || fd.kind != Nk.NODE_FIELD_DECL) continue;
            Node* fn_name = fd.child_count >= 1 ? fd.children[0] : null;
            if (fn_name == null) continue;
            if (!struct_lit_has_field(e, fn_name.p.ident.name_ptr, fn_name.p.ident.name_len))
            {
                self.soft("missing field in struct literal", e.line, e.col);
            }
        }
    }

    // The literal's type is the named type.
    return tyname;
}

fn bool struct_lit_has_field(Node* lit, char* name, usz len)
{
    for (usz i = 1; i < lit.child_count; i++)
    {
        Node* fi = lit.children[i];
        if (fi == null || fi.kind != Nk.NODE_FIELD_INIT) continue;
        Node* fn_name = fi.child_count >= 1 ? fi.children[0] : null;
        if (fn_name != null && span_eq(fn_name.p.ident.name_ptr, fn_name.p.ident.name_len, name, len)) return true;
    }
    return false;
}

// Matmul typing:  (m×k) @ (k×n) -> (m×n);  (k) @ (k×n) -> (n);  (m×k) @ (k) -> (m).
// Inner dimensions must agree when both are known constants.
fn Node* TypeChecker.synth_matmul(TypeChecker* self, Node* e)
{
    Node* lt = e.child_count >= 1 ? self.unfold(self.synth(e.children[0])) : null;
    Node* rt = e.child_count >= 2 ? self.unfold(self.synth(e.children[1])) : null;

    if (lt == null || rt == null) return null;
    if (lt.kind != Nk.NODE_TYPE_TENSOR || rt.kind != Nk.NODE_TYPE_TENSOR)
    {
        self.soft("@ (matmul) requires tensor operands", e.line, e.col);
        return null;
    }

    // Element type comes from the left operand.
    Node* elem = lt.child_count >= 1 ? lt.children[0] : null;

    usz lrank = lt.child_count >= 1 ? lt.child_count - 1 : 0;
    usz rrank = rt.child_count >= 1 ? rt.child_count - 1 : 0;

    // Pull dimensions (child indices 1..) as constants.
    long l0 = lrank >= 1 ? tensor_dim_const(lt.children[1]) : -1;
    long l1 = lrank >= 2 ? tensor_dim_const(lt.children[2]) : -1;
    long r0 = rrank >= 1 ? tensor_dim_const(rt.children[1]) : -1;
    long r1 = rrank >= 2 ? tensor_dim_const(rt.children[2]) : -1;

    // matrix @ matrix : (m×k)@(k×n) -> (m×n)
    if (lrank == 2 && rrank == 2)
    {
        if (l1 >= 0 && r0 >= 0 && l1 != r0)
        {
            self.soft("matmul shape mismatch: inner dimensions differ", e.line, e.col);
        }
        long[2] d;
        d[0] = l0;
        d[1] = r1;
        return self.mk_tensor(elem, &d[0], 2);
    }
    // matrix @ vector : (m×k)@(k) -> (m)
    if (lrank == 2 && rrank == 1)
    {
        if (l1 >= 0 && r0 >= 0 && l1 != r0)
        {
            self.soft("matmul shape mismatch: matrix columns != vector length", e.line, e.col);
        }
        long[1] d;
        d[0] = l0;
        return self.mk_tensor(elem, &d[0], 1);
    }
    // vector @ matrix : (k)@(k×n) -> (n)
    if (lrank == 1 && rrank == 2)
    {
        if (l0 >= 0 && r0 >= 0 && l0 != r0)
        {
            self.soft("matmul shape mismatch: vector length != matrix rows", e.line, e.col);
        }
        long[1] d;
        d[0] = r1;
        return self.mk_tensor(elem, &d[0], 1);
    }
    // vector @ vector : (k)@(k) -> scalar (dot product)
    if (lrank == 1 && rrank == 1)
    {
        if (l0 >= 0 && r0 >= 0 && l0 != r0)
        {
            self.soft("matmul shape mismatch: dot-product lengths differ", e.line, e.col);
        }
        return elem;
    }

    return null;
}

// Integer literal: honor a type suffix if present, else default i64.
fn Node* TypeChecker.int_lit_type(TypeChecker* self, Node* e)
{
    char bits = e.p.lit_int.bits;
    bool sg = e.p.lit_int.is_signed;
    // The parser stores bits=64, signed=true by default. Map to a Prim.
    if (bits == 8)  return self.mk_prim(sg ? Prim.PRIM_I8  : Prim.PRIM_U8);
    if (bits == 16) return self.mk_prim(sg ? Prim.PRIM_I16 : Prim.PRIM_U16);
    if (bits == 32) return self.mk_prim(sg ? Prim.PRIM_I32 : Prim.PRIM_U32);
    return self.mk_prim(sg ? Prim.PRIM_I64 : Prim.PRIM_U64);
}

// A name's type comes from the declaration it resolved to.
fn Node* TypeChecker.synth_name(TypeChecker* self, Node* e)
{
    Node* decl = e.resolved;
    if (decl == null) return null;   // unresolved (resolver already warned)
    return self.decl_type(decl);
}

// Compute the type a declaration provides to its uses.
fn Node* TypeChecker.decl_type(TypeChecker* self, Node* decl)
{
    switch (decl.kind)
    {
        case Nk.NODE_DECL_LET:
        case Nk.NODE_DECL_MUT:
        case Nk.NODE_DECL_CONST:
        case Nk.NODE_DECL_STATIC:
            return self.binding_decl_type(decl);

        case Nk.NODE_PATTERN_IDENT:
            // A pattern binder. Its type is stamped on by bind_pattern_types
            // (function parameters) when the signature is known.
            return decl.type_annotation;

        case Nk.NODE_DECL_FN:
            return self.fn_signature_type(decl);

        case Nk.NODE_PARAM:
            // generic/where param: a type variable — leave abstract.
            return null;

        case Nk.NODE_ENUM_VARIANT:
            // A variant constructor — its type is the OWNING enum's repr.
            // The resolver back-links every variant to its DECL_ENUM in
            // .resolved (never .type_annotation: mono's clone_node would
            // chase that into a variant→enum→children→variant cycle).
            // Returning the DECL_ENUM gives codegen the tagged
            // { i32, i64 } repr through type_to_llvm and keeps enum
            // machinery (enum_decl_of) happy on every value/pattern
            // annotation. The old answer — the variant's own name ident —
            // eroded to an opaque `ptr` downstream, sending tagged ctor
            // values down the tensor heap path (malloc + `store double`
            // of integer constants: invalid LLVM, and an unmarshalable
            // argument at call sites).
            if (decl.resolved != null && decl.resolved.kind == Nk.NODE_DECL_ENUM)
            { return decl.resolved; }
            return decl.child_count >= 1 ? decl.children[0] : null;

        default:
            return null;
    }
}

// let/const/static: [pattern/name, (type)?, (effectrow)?, (init)?]
// Prefer the explicit annotation; otherwise infer from the initializer.
fn Node* TypeChecker.binding_decl_type(TypeChecker* self, Node* decl)
{
    // Find an explicit type child (a NODE_TYPE_* or unit) if present.
    for (usz i = 1; i < decl.child_count; i++)
    {
        Node* c = decl.children[i];
        if (c != null && is_type_node(c)) return c;
    }
    // Otherwise infer from the last child (the initializer), if any.
    if (decl.child_count >= 2)
    {
        Node* last = decl.children[decl.child_count - 1];
        if (last != null && !is_type_node(last) && last.kind != Nk.NODE_EFFECT_ROW
            && last.kind != Nk.NODE_PATTERN_IDENT)
        {
            return self.synth(last);
        }
    }
    return null;
}

// fn: child 0 name, then optional generics, then the signature type (NODE_TYPE_FN).
fn Node* TypeChecker.fn_signature_type(TypeChecker* self, Node* fn_node)
{
    for (usz i = 1; i < fn_node.child_count; i++)
    {
        Node* c = fn_node.children[i];
        if (c != null && c.kind == Nk.NODE_TYPE_FN) return c;
    }
    return null;
}

// A bindings table mapping a generic type-parameter declaration (a NODE_PARAM
// inside a <...> list, the node a TypeVar use resolves to) to its inferred
// concrete type at a call site.
const usz MAX_TYPE_ARGS = 32;

struct TypeBindings
{
    Node*[MAX_TYPE_ARGS] params;   // the generic Param decl nodes
    Node*[MAX_TYPE_ARGS] args;     // the inferred concrete types
    usz count;
}

fn void TypeBindings.clear(TypeBindings* b)
{
    b.count = 0;
}

// Record param := arg (first binding wins; later unifications just check).
fn void TypeBindings.bind(TypeBindings* b, Node* param, Node* arg)
{
    if (param == null || arg == null) return;
    for (usz i = 0; i < b.count; i++)
    {
        if (b.params[i] == param) return;   // already bound
    }
    if (b.count < MAX_TYPE_ARGS)
    {
        b.params[b.count] = param;
        b.args[b.count] = arg;
        b.count++;
    }
}

fn Node* TypeBindings.lookup(TypeBindings* b, Node* param)
{
    for (usz i = 0; i < b.count; i++)
    {
        if (b.params[i] == param) return b.args[i];
    }
    return null;
}

// Is `t` a reference to a generic type parameter? (a TypeVar resolved to a
// NODE_PARAM that lives in a generic <...> list). Returns the Param or null.
fn Node* generic_param_of(Node* t)
{
    if (t == null) return null;
    if (t.kind != Nk.NODE_TYPEVAR) return null;
    Node* d = t.resolved;
    if (d != null && d.kind == Nk.NODE_PARAM) return d;
    return null;
}

// Unify a declared (possibly generic) type against an actual concrete type,
// recording type-variable bindings. Best-effort and structural; on shape
// mismatch it simply stops (soft typing handles the rest).
fn void TypeChecker.unify(TypeChecker* self, Node* declared, Node* actual, TypeBindings* b)
{
    declared = self.unfold(declared);
    actual = self.unfold(actual);
    if (declared == null || actual == null) return;

    // A bare generic parameter binds to the actual type.
    Node* gp = generic_param_of(declared);
    if (gp != null)
    {
        b.bind(gp, actual);
        return;
    }

    // Structural recursion through matching shapes.
    if (declared.kind != actual.kind) return;

    switch (declared.kind)
    {
        case Nk.NODE_TYPE_PTR:
        case Nk.NODE_TYPE_REF:
        case Nk.NODE_TYPE_MUT_REF:
        case Nk.NODE_TYPE_SLICE:
            if (declared.child_count >= 1 && actual.child_count >= 1)
            {
                self.unify(declared.children[0], actual.children[0], b);
            }
        case Nk.NODE_TYPE_ARRAY:
            if (declared.child_count >= 1 && actual.child_count >= 1)
            {
                self.unify(declared.children[0], actual.children[0], b);
            }
        case Nk.NODE_TYPE_TUPLE:
        case Nk.NODE_TYPE_FN:
            if (declared.child_count == actual.child_count)
            {
                for (usz i = 0; i < declared.child_count; i++)
                {
                    self.unify(declared.children[i], actual.children[i], b);
                }
            }
        case Nk.NODE_TYPE_GENERIC_APP:
            if (declared.child_count == actual.child_count)
            {
                for (usz i = 0; i < declared.child_count; i++)
                {
                    self.unify(declared.children[i], actual.children[i], b);
                }
            }
        default:
            break;
    }
}

// Substitute generic parameters in `t` with their bound concrete types,
// returning a fresh type tree. Types with no substitutions are returned as-is
// (no needless cloning). Bounded recursion depth for safety.
fn Node* TypeChecker.substitute(TypeChecker* self, Node* t, TypeBindings* b, int depth)
{
    if (t == null || depth > 64) return t;

    // A generic parameter use -> its bound type (or unchanged if unbound).
    Node* gp = generic_param_of(t);
    if (gp != null)
    {
        Node* bound = b.lookup(gp);
        return bound != null ? bound : t;
    }

    // Leaves with no children: nothing to substitute.
    if (t.child_count == 0) return t;
    if (!is_type_node(t)) return t;

    // Substitute children; only clone if something actually changed.
    bool changed = false;
    Node*[16] buf;
    usz n = t.child_count <= 16 ? t.child_count : 16;
    for (usz i = 0; i < n; i++)
    {
        Node* sub = self.substitute(t.children[i], b, depth + 1);
        buf[i] = sub;
        if (sub != t.children[i]) changed = true;
    }
    if (!changed) return t;

    Node* fresh = ast::node_n(self.arena, t.kind, &buf[0], n, t.line, t.col);
    if (fresh != null) fresh.p = t.p;
    return fresh;
}

// Instantiate a generic function signature at a call: infer type args from the
// actual argument types, then substitute them into the return type.
// `sig` is the NODE_TYPE_FN; `args` are the call's argument nodes.
fn Node* TypeChecker.instantiate_call(TypeChecker* self, Node* sig, Node** args, usz argc)
{
    if (sig == null || sig.kind != Nk.NODE_TYPE_FN) return null;

    // Recover the parameter type and return type (handle the effect-row form
    // NODE_TYPE_FN[innerFn, EffectRow]).
    Node* param_t = null;
    Node* ret_t = null;
    Node* lhs = sig.child_count >= 1 ? sig.children[0] : null;
    Node* rhs = sig.child_count >= 2 ? sig.children[1] : null;
    if (rhs != null && rhs.kind == Nk.NODE_EFFECT_ROW
        && lhs != null && lhs.kind == Nk.NODE_TYPE_FN)
    {
        param_t = lhs.child_count >= 1 ? lhs.children[0] : null;
        ret_t = lhs.child_count >= 2 ? lhs.children[1] : null;
    }
    else
    {
        param_t = lhs;
        ret_t = rhs;
    }
    if (ret_t == null) return null;

    TypeBindings b;
    b.clear();

    // Unify the declared parameter type against the actual arguments.
    // A single param matches one arg; a tuple param matches positional args.
    if (param_t != null)
    {
        Node* pt = self.unfold(param_t);
        if (pt != null && pt.kind == Nk.NODE_TYPE_TUPLE && argc >= 1)
        {
            for (usz i = 0; i < pt.child_count && i < argc; i++)
            {
                Node* at = self.synth(args[i]);
                self.unify(pt.children[i], at, &b);
            }
        }
        else if (argc >= 1)
        {
            Node* at = self.synth(args[0]);
            self.unify(param_t, at, &b);
        }
    }

    if (b.count == 0) return ret_t;   // nothing inferred: monomorphic return
    return self.substitute(ret_t, &b, 0);
}

fn bool is_type_node(Node* n)
{
    if (n == null) return false;
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
            return true;
        default:
            return false;
    }
}

// Binary operator typing. Arithmetic requires matching numeric operands and
// yields that type; comparisons yield bool; logical require/yield bool.
fn Node* TypeChecker.synth_binary(TypeChecker* self, Node* e)
{
    Node* l = e.child_count >= 1 ? self.synth(e.children[0]) : null;
    Node* r = e.child_count >= 2 ? self.synth(e.children[1]) : null;
    lexer::TokenType op = e.p.op.op;

    switch (op)
    {
        // Comparisons -> bool
        case lexer::TokenType.TOKEN_EQEQ:
        case lexer::TokenType.TOKEN_NEQ:
        case lexer::TokenType.TOKEN_NEQ_UNI:
        case lexer::TokenType.TOKEN_LT:
        case lexer::TokenType.TOKEN_GT:
        case lexer::TokenType.TOKEN_LTEQ:
        case lexer::TokenType.TOKEN_GTEQ:
        case lexer::TokenType.TOKEN_LEQ_UNI:
        case lexer::TokenType.TOKEN_GEQ_UNI:
            self.check_comparable(e, l, r, op);
            self.check_same_numeric_or_eq(e, l, r);
            return self.mk_prim(Prim.PRIM_BOOL);

        // Set membership  x ∈ s  -> bool
        case lexer::TokenType.TOKEN_ELEMENT:
            return self.mk_prim(Prim.PRIM_BOOL);

        // Logical -> bool, operands should be bool
        case lexer::TokenType.TOKEN_KW_AND:
        case lexer::TokenType.TOKEN_KW_OR:
        case lexer::TokenType.TOKEN_AMPAMP:
        case lexer::TokenType.TOKEN_PIPEPIPE:
            self.expect_bool(e.children[0], l);
            self.expect_bool(e.children[1], r);
            return self.mk_prim(Prim.PRIM_BOOL);

        // Bitwise & shift -> integers only (floats have no bit representation
        // at the language level). Pride lets you do bit-twiddling, but only on
        // integer types — a float shift is almost always a mistake.
        case lexer::TokenType.TOKEN_AMP:
        case lexer::TokenType.TOKEN_PIPE:
        case lexer::TokenType.TOKEN_XOR:
        case lexer::TokenType.TOKEN_LSHIFT:
        case lexer::TokenType.TOKEN_RSHIFT:
            return self.synth_bitwise(e, l, r);

        // Division / modulo -> numeric; also flag a literal-zero divisor, which
        // is declared UB territory (use ub! or guard it explicitly).
        case lexer::TokenType.TOKEN_SLASH:
        case lexer::TokenType.TOKEN_PERCENT:
            self.check_divisor(e);
            return self.synth_arith(e, l, r);

        // Remaining arithmetic (+ - *) -> numeric, operands must match
        default:
            return self.synth_arith(e, l, r);
    }
}

// Bitwise/shift operators require integer operands and yield an integer type.
fn Node* TypeChecker.synth_bitwise(TypeChecker* self, Node* e, Node* l, Node* r)
{
    Prim pl = type_prim(l);
    Prim pr = type_prim(r);

    if (pl != Prim.PRIM_NONE && !prim_is_int(pl) && !self.is_int_literal(e.children[0]))
    {
        self.soft("bitwise/shift operator requires integer operands (not floats)", e.line, e.col);
    }
    else if (pr != Prim.PRIM_NONE && !prim_is_int(pr) && !self.is_int_literal(e.children[1]))
    {
        self.soft("bitwise/shift operator requires integer operands (not floats)", e.line, e.col);
    }

    // A shift amount that is a literal >= the left operand's bit width (or
    // negative, when read as signed) is undefined behavior at the machine
    // level (LLVM's shl/lshr/ashr are poison in that case) — flag it here so
    // it isn't a silent runtime footgun (mirrors check_divisor's treatment of
    // literal-zero divisors as a surfaced, soft "declared UB" diagnostic).
    bool is_shift = (e.p.op.op == lexer::TokenType.TOKEN_LSHIFT
                   || e.p.op.op == lexer::TokenType.TOKEN_RSHIFT);
    if (is_shift && e.child_count >= 2 && e.children[1] != null
        && e.children[1].kind == Nk.NODE_LIT_INT)
    {
        long shift_amount = (long)e.children[1].p.lit_int.int_val;
        int lhs_bits = prim_bit_width(pl);
        if (lhs_bits <= 0) lhs_bits = 64;   // unknown left type: assume the widest case
        if (shift_amount < 0 || shift_amount >= (long)lhs_bits)
        {
            self.soft("shift amount is out of range for the operand's width (undefined behavior)",
                e.children[1].line, e.children[1].col);
        }
    }

    // Result follows the non-literal operand's integer type.
    if (l != null && prim_is_int(pl)) return l;
    if (r != null && prim_is_int(pr)) return r;
    if (l != null) return l;
    return r;
}

// Bit width of an integer primitive, or 0 if `p` isn't a fixed-width integer.
fn int prim_bit_width(Prim p)
{
    switch (p)
    {
        case PRIM_I8: case PRIM_U8: return 8;
        case PRIM_I16: case PRIM_U16: return 16;
        case PRIM_I32: case PRIM_U32: return 32;
        case PRIM_I64: case PRIM_U64: case PRIM_ISIZE: case PRIM_USIZE: return 64;
        case PRIM_I128: case PRIM_U128: return 128;
        default: return 0;
    }
}

fn bool TypeChecker.is_int_literal(TypeChecker* self, Node* n)
{
    return n != null && n.kind == Nk.NODE_LIT_INT;
}

// Flag a division/modulo whose divisor is the integer literal 0. This is
// declared UB in Pride — the parser refuses to fold it, and we surface a
// soft warning so it isn't silent. (Non-literal zeros are the programmer's
// responsibility — "shoot yourself in the foot, with precision".)
fn void TypeChecker.check_divisor(TypeChecker* self, Node* e)
{
    if (e.child_count < 2) return;
    Node* d = e.children[1];
    if (d == null) return;
    if (d.kind == Nk.NODE_LIT_INT && d.p.lit_int.int_val == 0)
    {
        self.soft("division or modulo by literal zero (declared UB; guard it or use ub!)", e.line, e.col);
    }
}

fn Node* TypeChecker.synth_arith(TypeChecker* self, Node* e, Node* l, Node* r)
{
    // Elementwise arithmetic on tensors (`a + b`, hypervector bundling in HDC):
    // both operands must have the same shape. A rank or constant-dim mismatch is
    // a real error a numerics/HDC author would otherwise hit silently.
    Node* lu = self.unfold(l);
    Node* ru = self.unfold(r);
    if (lu != null && ru != null
        && lu.kind == Nk.NODE_TYPE_TENSOR && ru.kind == Nk.NODE_TYPE_TENSOR)
    {
        if (lu.child_count != ru.child_count)
        {
            self.soft("elementwise tensor op shape mismatch: differing rank", e.line, e.col);
        }
        else
        {
            for (usz i = 1; i < lu.child_count; i++)
            {
                long da = tensor_dim_const(lu.children[i]);
                long db = tensor_dim_const(ru.children[i]);
                if (da >= 0 && db >= 0 && da != db)
                {
                    self.soft("elementwise tensor op shape mismatch: dimensions differ", e.line, e.col);
                    break;
                }
            }
        }
        return l;   // result has the left tensor's shape
    }

    Prim pl = type_prim(l);
    Prim pr = type_prim(r);

    if (pl != Prim.PRIM_NONE && pr != Prim.PRIM_NONE)
    {
        if (!prim_is_numeric(pl) || !prim_is_numeric(pr))
        {
            self.soft("arithmetic on non-numeric operand", e.line, e.col);
        }
        else if (pl != pr)
        {
            // No implicit numeric promotion in Pride (v.md §4) — but an
            // untyped integer literal adapts to the other operand's type, so
            // `n:i32 * 2` is fine. Flag only genuine mismatches.
            bool literal_adapts = self.lit_int_fits(e.children[0], pr)
                || self.lit_int_fits(e.children[1], pl);
            if (!literal_adapts)
            {
                self.soft("numeric type mismatch in binary expression (no implicit promotion)", e.line, e.col);
            }
            // The concrete (non-literal) operand's type wins as the result.
            if (e.children[0] != null && e.children[0].kind == Nk.NODE_LIT_INT) return r;
            return l;
        }
    }
    // Result follows the left operand's type when known, else the right.
    if (l != null) return l;
    return r;
}

// True if `t` is an aggregate (struct / union / tuple / array / slice) type.
// These have no built-in comparison in Pride — there is no operator overloading
// and no structural equality/ordering, so `a < b` or `a == b` on whole
// aggregates is a mistake a library author would otherwise hit silently.
// Generic parameters are deliberately NOT treated as aggregates here (they are
// abstract — a `T : Ord`/`T : Eq` body must still type-check).
fn bool TypeChecker.is_aggregate_type(TypeChecker* self, Node* ty)
{
    Node* t = self.unfold(ty);
    if (t == null) return false;
    if (is_generic_param_type(t)) return false;
    switch (t.kind)
    {
        case Nk.NODE_TYPE_TUPLE:
        case Nk.NODE_TYPE_ARRAY:
        case Nk.NODE_TYPE_SLICE:
            return true;
        case Nk.NODE_TYPE_GENERIC_APP:
            // Box<i32> etc — peel to the head constructor.
            if (t.child_count >= 1) return self.is_aggregate_type(t.children[0]);
            return false;
        case Nk.NODE_TYPEVAR:
            if (t.resolved != null)
            {
                Node* d = t.resolved;
                if (d.kind == Nk.NODE_DECL_STRUCT || d.kind == Nk.NODE_DECL_UNION)
                {
                    return true;
                }
                // `type X = struct …` — alias whose body is a struct/union.
                if (d.kind == Nk.NODE_DECL_TYPE && d.child_count >= 1)
                {
                    Node* b = d.children[d.child_count - 1];
                    if (b != null
                        && (b.kind == Nk.NODE_DECL_STRUCT || b.kind == Nk.NODE_DECL_UNION))
                    {
                        return true;
                    }
                }
            }
            return false;
        default:
            return false;
    }
}

// Reject comparison / ordering on operands that have no defined comparison:
//   * aggregate types (struct/union/tuple/array/slice) — no structural cmp,
//   * bool for ordering operators (`<` `>` `<=` `>=`) — booleans are not ordered.
// Equality on bool IS allowed. Pointers and numbers fall through to the
// numeric/eq path. Generic params are abstract and skipped.
fn void TypeChecker.check_comparable(TypeChecker* self, Node* e, Node* l, Node* r,
    lexer::TokenType op)
{
    if (is_generic_param_type(l) || is_generic_param_type(r)) return;

    if (self.is_aggregate_type(l) || self.is_aggregate_type(r))
    {
        self.soft("comparison is not defined for aggregate types (no operator overloading or structural comparison)",
            e.line, e.col);
        return;
    }

    bool is_order = op != lexer::TokenType.TOKEN_EQEQ
        && op != lexer::TokenType.TOKEN_NEQ
        && op != lexer::TokenType.TOKEN_NEQ_UNI;
    if (is_order)
    {
        Prim pl = type_prim(self.unfold(l));
        Prim pr = type_prim(self.unfold(r));
        if (pl == Prim.PRIM_BOOL || pr == Prim.PRIM_BOOL)
        {
            self.soft("ordering operators are not defined for bool (use == / != instead)",
                e.line, e.col);
        }
    }
}

fn void TypeChecker.check_same_numeric_or_eq(TypeChecker* self, Node* e, Node* l, Node* r)
{
    // Cross-kind comparisons (e.g. pointer == integer, bool == integer) are
    // almost always a mistake — flag them even when one side is a pointer,
    // which the numeric-only path below would otherwise miss.
    if (l != null && r != null)
    {
        int ka = self.value_kind(l);
        int kb = self.value_kind(r);
        // null (pointer literal) is comparable to any pointer; allow that.
        bool null_ptr_ok = (l.kind == Nk.NODE_LIT_NULL && kb == VK_PTR)
            || (r.kind == Nk.NODE_LIT_NULL && ka == VK_PTR);
        if (ka != VK_UNKNOWN && kb != VK_UNKNOWN && ka != kb && !null_ptr_ok)
        {
            self.soft("comparison between incompatible kinds (e.g. pointer vs number)", e.line, e.col);
            return;
        }
    }

    Prim pl = type_prim(l);
    Prim pr = type_prim(r);
    if (pl == Prim.PRIM_NONE || pr == Prim.PRIM_NONE) return;
    if (pl == pr) return;

    // An untyped integer literal adapts to the other side's integer type, so
    // `n:i32 > 0` is fine (the 0 takes i32). Only flag genuine mismatches.
    if (self.lit_int_fits(e.children[0], pr)) return;
    if (self.lit_int_fits(e.children[1], pl)) return;

    self.soft("comparison between different numeric types", e.line, e.col);
}

// Coarse value-kind classification for cross-kind comparison checks.
const int VK_UNKNOWN = 0;
const int VK_NUMBER  = 1;
const int VK_BOOL    = 2;
const int VK_PTR     = 3;

fn int TypeChecker.value_kind(TypeChecker* self, Node* t)
{
    Node* u = self.unfold(t);
    if (u == null) return VK_UNKNOWN;
    if (u.kind == Nk.NODE_TYPE_PTR) return VK_PTR;
    Prim p = type_prim(u);
    if (p == Prim.PRIM_PTR) return VK_PTR;
    if (p == Prim.PRIM_BOOL) return VK_BOOL;
    if (prim_is_numeric(p)) return VK_NUMBER;
    return VK_UNKNOWN;
}

// True if `n` is an untyped (no-suffix) integer literal that can take type `p`.
fn bool TypeChecker.lit_int_fits(TypeChecker* self, Node* n, Prim p)
{
    if (n == null) return false;
    if (n.kind != Nk.NODE_LIT_INT) return false;
    if (!prim_is_numeric(p)) return false;
    // The parser marks suffix-less literals with the default bits=64/signed.
    // We treat any integer literal as adaptable to any numeric target here;
    // overflow checking is a later (codegen) concern.
    return true;
}

fn void TypeChecker.expect_bool(TypeChecker* self, Node* site, Node* t)
{
    if (t == null) return;
    if (type_prim(t) != Prim.PRIM_BOOL)
    {
        int ln = site != null ? site.line : 0;
        int cl = site != null ? site.col : 0;
        self.soft("expected bool operand for logical operator", ln, cl);
    }
}

// Unary operators.
// Assignment  lhs = rhs  (also += -= etc). Yields unit. Enforces that the
// target is a mutable, assignable location:
//   - a `let mut` binding   (binder flagged FLAG_MUT)
//   - a field / index of a mutable / pointer target
// Writing to an immutable `let` or a function parameter is reported (soft).
fn Node* TypeChecker.synth_assign(TypeChecker* self, Node* e)
{
    Node* lhs = e.child_count >= 1 ? e.children[0] : null;
    Node* rhs = e.child_count >= 2 ? e.children[1] : null;

    Node* lt = self.synth(lhs);
    Node* rt = self.synth(rhs);

    // Mutability of the assignment target.
    if (!self.is_assignable(lhs))
    {
        self.soft("assignment to an immutable binding (declare it `let mut`)",
            lhs != null ? lhs.line : e.line, lhs != null ? lhs.col : e.col);
    }

    // Value/target type compatibility (soft), with literal adaptation.
    if (lt != null && rt != null && rhs != null && !self.arg_fits(rhs, rt, lt))
    {
        self.soft("assigned value type does not match the target type", rhs.line, rhs.col);
    }

    return self.mk_prim(Prim.PRIM_UNIT);
}

// Is `target` a writable location?
fn bool TypeChecker.is_assignable(TypeChecker* self, Node* target)
{
    if (target == null) return true;   // unknown: don't false-warn
    switch (target.kind)
    {
        case Nk.NODE_IDENT:
        case Nk.NODE_TYPEVAR:
            // A bare name: writable only if its binder is mutable.
            Node* decl = target.resolved;
            if (decl == null) return true;   // unresolved: resolver already warned
            // Mutable `let mut` binders carry FLAG_MUT (stamped at parse time).
            if ((decl.flags & ast::FLAG_MUT) != 0) return true;
            // `mut`-kinded decls are mutable too.
            if (decl.kind == Nk.NODE_DECL_MUT) return true;
            return false;
        case Nk.NODE_EXPR_FIELD:
            // Writing through a field: writable if the base is (or a pointer).
            if (target.child_count >= 1) return self.is_lvalue_base(target.children[0]);
            return true;
        case Nk.NODE_EXPR_INDEX:
            // Writing through an index: pointers/arrays are writable locations.
            return true;
        case Nk.NODE_EXPR_UNARY:
            // *p = ...  writing through a dereference is allowed.
            if (target.p.op.op == lexer::TokenType.TOKEN_STAR) return true;
            return false;
        default:
            return false;   // literals, calls, etc. are not assignable
    }
}

// The base of a field write is an lvalue if it's a mutable binding, a pointer
// (auto-deref makes `p.x = ...` a write through the pointer), or itself a
// writable field/index chain.
fn bool TypeChecker.is_lvalue_base(TypeChecker* self, Node* base)
{
    if (base == null) return true;
    // Through a pointer, the pointee is writable.
    Node* bt = self.unfold(self.synth(base));
    if (bt != null && bt.kind == Nk.NODE_TYPE_PTR) return true;
    if (bt != null && type_prim(bt) == Prim.PRIM_PTR) return true;
    return self.is_assignable(base);
}

fn Node* TypeChecker.synth_unary(TypeChecker* self, Node* e)
{
    Node* operand = e.child_count >= 1 ? self.synth(e.children[0]) : null;
    lexer::TokenType op = e.p.op.op;

    switch (op)
    {
        case lexer::TokenType.TOKEN_KW_NOT:
        case lexer::TokenType.TOKEN_BANG:
            self.expect_bool(e.children[0], operand);
            return self.mk_prim(Prim.PRIM_BOOL);

        case lexer::TokenType.TOKEN_MINUS:
        case lexer::TokenType.TOKEN_PLUS:
            return operand;

        case lexer::TokenType.TOKEN_STAR:
            // dereference: *T -> T  (requires a pointer operand)
            Node* ud = self.unfold(operand);
            if (ud != null && ud.kind == Nk.NODE_TYPE_PTR && ud.child_count >= 1)
            {
                return ud.children[0];
            }
            // A known non-pointer operand cannot be dereferenced. (Unknown
            // operand types stay silent — soft typing avoids false warnings.)
            if (ud != null && type_prim(ud) != Prim.PRIM_NONE)
            {
                self.soft("dereference of a non-pointer value", e.line, e.col);
            }
            return null;

        case lexer::TokenType.TOKEN_AMP:
            // address-of: T -> *T
            if (operand != null) return ast::node1(self.arena, Nk.NODE_TYPE_PTR, operand, e.line, e.col);
            return null;

        default:
            return operand;
    }
}

// if: [cond, sigma, then, (elif|else)?, phi]. Condition must be bool; the
// expression's type is the join (union) of the branch types.
// True if `ty` denotes a union type (a sum type). Used to know that a struct
// pattern over it is refutable (matches only one variant), so the linter must
// not treat it as a catch-all.
fn bool TypeChecker.is_union_type(TypeChecker* self, Node* ty)
{
    Node* t = self.unfold(ty);
    if (t == null) return false;
    if (t.kind == Nk.NODE_TYPE_PTR && t.child_count >= 1) t = self.unfold(t.children[0]);
    if (t == null) return false;
    if (t.kind == Nk.NODE_TYPE_GENERIC_APP && t.child_count >= 1) t = self.unfold(t.children[0]);
    if (t == null) return false;
    if (t.kind == Nk.NODE_TYPE_UNION) return true;
    if (t.kind == Nk.NODE_TYPEVAR && t.resolved != null)
    {
        Node* d = t.resolved;
        if (d.kind == Nk.NODE_DECL_UNION || d.kind == Nk.NODE_DECL_ENUM) return true;
        if (d.kind == Nk.NODE_DECL_TYPE && d.child_count >= 1)
        {
            Node* b = d.children[d.child_count - 1];
            if (b != null && (b.kind == Nk.NODE_DECL_UNION || b.kind == Nk.NODE_DECL_ENUM)) return true;
        }
    }
    return false;
}

// match scrut σ arm* φ — synthesize the scrutinee, bind each arm's pattern
// against it, mark refutable patterns (struct/tuple over a union variant), and
// join the arm body types.
fn Node* TypeChecker.synth_match(TypeChecker* self, Node* e)
{
    Node* scrut = e.child_count >= 1 ? self.synth(e.children[0]) : null;
    bool scrut_is_union = scrut != null && self.is_union_type(scrut);

    Node* joined = null;
    bool have = false;
    for (usz i = 1; i < e.child_count; i++)
    {
        Node* arm = e.children[i];
        if (arm == null || arm.kind != Nk.NODE_MATCH_ARM) continue;

        Node* pat = arm.child_count >= 1 ? arm.children[0] : null;
        // A struct/tuple/literal pattern over a union scrutinee constrains the
        // variant, so it is refutable — stamp it so the linter won't treat it
        // as a catch-all and wrongly flag following arms as unreachable.
        if (scrut_is_union && pat != null && pat.kind == Nk.NODE_PATTERN_STRUCT)
        {
            pat.flags |= ast::FLAG_REFUTABLE;
            // Resolve variant names against the union's variant list, type the
            // payload binders, and stamp the pattern with the union type —
            // the lowering recovers the discriminant from that annotation.
            // Previously only fn-CLAUSE patterns were bound; match arms fell
            // through to the legacy irrefutable path and miscompiled (the
            // result φ referenced unbound payload parameters).
            self.bind_pattern_types(pat, scrut);
        }
        if (scrut != null && pat != null && pat.kind == Nk.NODE_PATTERN_IDENT)
        {
            self.bind_pattern_types(pat, scrut);
        }
        else if (scrut != null && pat != null && pat.kind == Nk.NODE_PATTERN_OR)
        {
            self.bind_pattern_types(pat, scrut);
        }
        else if (scrut != null && pat != null && pat.kind == Nk.NODE_PATTERN_TUPLE)
        {
            // Tuple arms destructure the scrutinee (aliasing/projection
            // lowering). Components must be IRREFUTABLE: a literal or nested
            // pattern inside a match tuple arm would need decision-tree
            // component testing, which was never implemented — it previously
            // accepted EVERY tuple silently (a miscompile). Bind the
            // component to a name and refine with a guard instead.
            self.bind_pattern_types(pat, scrut);
            for (usz k = 0; k < pat.child_count; k++)
            {
                Node* comp = pat.children[k];
                if (comp == null) continue;
                // Literal components ARE supported: the lowering folds a
                // per-component equality test into the arm's dispatch block
                // (fn clauses accept the same shapes via clause_test), which
                // is exactly the spec's `| (0, 0) -> ...` tuple matching.
                // NESTED struct/tuple/or components still need a decision
                // tree — keep the hard error for those.
                if (comp.kind == Nk.NODE_PATTERN_STRUCT
                    || comp.kind == Nk.NODE_PATTERN_TUPLE   || comp.kind == Nk.NODE_PATTERN_OR)
                {
                    self.hard("refutable component in a match tuple pattern (bind it and refine with a guard)",
                              comp.line, comp.col);
                }
            }
        }

        // Synthesize guard + body.
        for (usz j = 1; j < arm.child_count; j++)
        {
            Node* c = arm.children[j];
            if (c == null) continue;
            if (c.kind == Nk.NODE_PATTERN_GUARD)
            {
                if (c.child_count >= 1) self.synth(c.children[0]);
                continue;
            }
            Node* bt = self.synth(c);
            if (!have) { joined = bt; have = true; }
            else if (bt != null && joined != null && !self.same_type(joined, bt))
            {
                joined = ast::node2(self.arena, Nk.NODE_TYPE_UNION, joined, bt, e.line, e.col);
            }
        }
    }

    // Union exhaustiveness: if the scrutinee is a union and every variant is
    // matched, mark the match total so the linter won't false-warn.
    if (scrut_is_union)
    {
        Node* variants = self.union_variants_of(scrut);
        if (variants != null && self.union_match_exhaustive(variants, e, false))
        {
            e.flags |= ast::FLAG_EXHAUSTIVE;
        }
    }
    return joined;
}

// while cond body — the condition must be bool. Same learner-friendly check as
// `if`. The loop is a statement; its value type is unit.
fn Node* TypeChecker.synth_while(TypeChecker* self, Node* e)
{
    if (e.child_count >= 1)
    {
        Node* condn = e.children[0];
        Node* cond = self.synth(condn);
        if (cond != null && type_prim(cond) != Prim.PRIM_BOOL)
        {
            if (condn != null && condn.kind == Nk.NODE_EXPR_ASSIGN
                && condn.p.op.op == lexer::TokenType.TOKEN_EQ)
            {
                self.soft("condition is an assignment (`=`); did you mean `==`?",
                    condn.line, condn.col);
            }
            else
            {
                self.soft("while condition is not bool", condn.line, condn.col);
            }
        }
    }
    // Check the body.
    for (usz i = 1; i < e.child_count; i++)
    {
        if (e.children[i] != null) self.synth(e.children[i]);
    }
    return self.mk_prim(Prim.PRIM_UNIT);
}

fn Node* TypeChecker.synth_if(TypeChecker* self, Node* e)
{
    if (e.child_count >= 1)
    {
        Node* condn = e.children[0];
        Node* cond = self.synth(condn);
        if (cond != null && type_prim(cond) != Prim.PRIM_BOOL)
        {
            // Common learner slip: `if x = 5` (assignment) instead of `x == 5`.
            // The assignment yields unit, never bool — point right at it.
            if (condn != null && condn.kind == Nk.NODE_EXPR_ASSIGN
                && condn.p.op.op == lexer::TokenType.TOKEN_EQ)
            {
                self.soft("condition is an assignment (`=`); did you mean `==`?",
                    condn.line, condn.col);
            }
            else
            {
                self.soft("if condition is not bool", condn.line, condn.col);
            }
        }
    }

    // Synthesize the branch bodies (skip sigma/phi markers).
    Node* then_t = null;
    Node* else_t = null;
    for (usz i = 1; i < e.child_count; i++)
    {
        Node* c = e.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_SIGMA || c.kind == Nk.NODE_PHI) continue;
        Node* ct = self.synth(c);
        if (then_t == null) { then_t = ct; }
        else { else_t = ct; }
    }

    if (then_t == null) return null;
    if (else_t == null) return then_t;
    if (self.same_type(then_t, else_t)) return then_t;
    // Branches differ -> union type (semantic subtyping join).
    return ast::node2(self.arena, Nk.NODE_TYPE_UNION, then_t, else_t, e.line, e.col);
}

// block: type is the type of its last expression-ish child.
fn Node* TypeChecker.synth_block(TypeChecker* self, Node* e)
{
    Node* last_t = null;
    for (usz i = 0; i < e.child_count; i++)
    {
        Node* c = e.children[i];
        if (c == null) continue;
        // Let/mut bindings inside a block must go through check_binding so the
        // binder pattern gets its type stamped — subsequent index/field accesses
        // on the bound name depend on that annotation being present.
        if (c.kind == Nk.NODE_DECL_LET || c.kind == Nk.NODE_DECL_MUT
            || c.kind == Nk.NODE_DECL_CONST || c.kind == Nk.NODE_DECL_STATIC)
        {
            self.check_binding(c);
            last_t = self.mk_prim(Prim.PRIM_UNIT);
            continue;
        }
        if (c.kind == Nk.NODE_DECL_FN)
        {
            self.check_fn(c);
            last_t = self.mk_prim(Prim.PRIM_UNIT);
            continue;
        }
        last_t = self.synth(c);
    }
    return last_t;
}

fn void TypeChecker.check(TypeChecker* self, Node* e, Node* expected)
{
    // `let bits : u32 = transmute(3.14f32)` (v.md §776): the transmute's
    // TARGET type comes from the ascription — there is no other syntactic
    // place for it. Stamp it so codegen's bitcast arm sees an honest dst
    // type (bottom-up synth alone would default the val to i64 and the
    // f32 bits would never survive).
    if (e != null && e.kind == Nk.NODE_EXPR_TRANSMUTE
        && expected != null && e.type_annotation == null)
    {
        e.type_annotation = expected;
    }
    // Ascribing a closure literal — `let f : (T -> U) = | x -> ...` —
    // propagates the fn type INTO the literal: every clause's binders take
    // the domain type and every body is checked against the codomain (via
    // check_clause, the same routine fn decls use). Without this the clause
    // binders stayed untyped, so the closure thunk's LLVM parameters fell
    // back to generic i64 slots and could not marshal aggregate arguments
    // (unions, tuples, fn values) even though the user fully annotated the
    // closure's type.
    if (e != null && e.kind == Nk.NODE_EXPR_CLOSURE && expected != null)
    {
        Node* ft = self.unfold(expected);
        if (ft != null && ft.kind == Nk.NODE_TYPE_FN)
        {
            Node* dom = ft.child_count >= 1 ? ft.children[0] : null;
            Node* cod = ft.child_count >= 2 ? ft.children[1] : null;
            // Peel effect-row form: TYPE_FN[dom->cod, EFFECT_ROW]
            if (cod != null && cod.kind == Nk.NODE_EFFECT_ROW
                && dom != null && dom.kind == Nk.NODE_TYPE_FN)
            {
                Node* icod = dom.child_count >= 2 ? dom.children[1] : null;
                dom = dom.child_count >= 1 ? dom.children[0] : null;
                cod = icod;
            }
            for (usz ci = 0; ci < e.child_count; ci++)
            {
                Node* cl = e.children[ci];
                if (cl != null && cl.kind == Nk.NODE_CLAUSE)
                {
                    self.check_clause(cl, dom, cod);
                    // The thunk's return type is recovered from a clause
                    // body's type annotation downstream; synth computes but
                    // does not always STAMP it on the body node (match
                    // expressions notably). Stamp the checked type so the
                    // thunk define header, its ret coercion, and every call
                    // site agree on one result type.
                    if (cod != null && cl.child_count >= 2)
                    {
                        Node* cbody = cl.children[cl.child_count - 1];
                        if (cbody != null && cbody.type_annotation == null)
                        {
                            Node* bt = self.synth(cbody);
                            cbody.type_annotation = (bt != null) ? bt : cod;
                        }
                    }
                }
            }
        }
    }
    Node* actual = self.synth(e);
    if (actual == null || expected == null) return;   // unknown: permit
    // Use arg_fits so untyped numeric literals adapt to the expected type
    // (e.g. `let x : i32 = 0` — the literal 0 takes i32, no false mismatch).
    if (!self.arg_fits(e, actual, expected))
    {
        self.soft("type mismatch (soft): value does not fit the expected type", e.line, e.col);
    }
    // A struct literal checked against a generic-struct instantiation type
    // takes the instantiation as its stamp (see the helper).
    self.stamp_expected_struct_lit(e, expected);
}

// A struct literal checked against a GENERIC-STRUCT INSTANTIATION
// (`Pair { fst: a, snd: b } : Pair<i64, f64>`) IS the instantiation — not
// the bare head TypeVar its syntax mentions.  Stamp it so codegen prints the
// substituted record (insertvalue repr, return ABI, field projections).
// Field validation already ran during synth against the decl's field list,
// so nothing is lost by overwriting the stamp.  Shared by check()
// (let/assignment positions) and check_clause (return position).
fn void TypeChecker.stamp_expected_struct_lit(TypeChecker* self, Node* e, Node* expected)
{
    if (e == null || e.kind != Nk.NODE_EXPR_STRUCT_LIT || expected == null) return;
    Node* un = self.unfold(expected);
    if (un == null || un.kind != Nk.NODE_TYPE_GENERIC_APP) return;
    Node* app_decl = ast::struct_decl_of(un);
    Node* lit_head = e.child_count >= 1 ? e.children[0] : null;
    Node* lit_decl = ast::struct_decl_of(lit_head);
    if (app_decl != null && lit_decl != null && app_decl == lit_decl)
    {
        e.type_annotation = un;
    }
}

fn void TypeChecker.check_program(TypeChecker* self, Node* program)
{
    if (program == null) return;
    for (usz i = 0; i < program.child_count; i++)
    {
        self.check_decl(program.children[i]);
    }
}

fn void TypeChecker.check_decl(TypeChecker* self, Node* d)
{
    if (d == null) return;
    if (d.kind == Nk.NODE_DECL_INTERFACE || d.kind == Nk.NODE_DECL_IMPL)
    {
        // Find the implementing type for impl blocks (child after generics/interface name).
        // The implementing type is used to resolve Self references.
        Node* impl_type = null;
        if (d.kind == Nk.NODE_DECL_IMPL)
        {
            // impl children: [interface_name, generics?, impl_type, where?, fn*]
            // Find the first non-generic, non-interface child that is a type node.
            for (usz ci = 1; ci < d.child_count; ci++)
            {
                Node* ch = d.children[ci];
                if (ch == null) continue;
                if (ch.kind == Nk.NODE_DECL_FN) break;  // reached methods
                if (ch.kind == Nk.NODE_TYPEVAR || ch.kind == Nk.NODE_TYPE_PRIMITIVE
                    || ch.kind == Nk.NODE_TYPE_PTR || ch.kind == Nk.NODE_TYPE_TUPLE)
                { impl_type = ch; break; }
            }
        }
        // Store impl_type in checker state so check_fn can resolve Self.
        Node* prev_self = self.current_self_type;
        self.current_self_type = impl_type;
        // Type-check all method declarations/definitions inside
        for (usz mi = 1; mi < d.child_count; mi++)
        {
            Node* ch = d.children[mi];
            if (ch != null && ch.kind == Nk.NODE_DECL_FN) self.check_fn(ch);
        }
        self.current_self_type = prev_self;
        return;
    }
    if (d.kind == Nk.NODE_DECL_ENUM)
    {
        // Resolve payload types for each variant
        for (usz vi = 1; vi < d.child_count; vi++)
        {
            Node* evar = d.children[vi];
            if (evar == null || evar.kind != Nk.NODE_ENUM_VARIANT) continue;
            for (usz fi = 1; fi < evar.child_count; fi++)
            {
                Node* field = evar.children[fi];
                if (field != null && field.child_count >= 1)
                { self.synth(field.children[0]); }
            }
        }
        return;
    }

    if (d == null) return;

    switch (d.kind)
    {
        case Nk.NODE_DECL_FN:
            self.check_fn(d);
        case Nk.NODE_DECL_LET:
        case Nk.NODE_DECL_MUT:
        case Nk.NODE_DECL_CONST:
        case Nk.NODE_DECL_STATIC:
            self.check_binding(d);
        case Nk.NODE_DECL_MOD:
            for (usz i = 0; i < d.child_count; i++)
            {
                Node* c = d.children[i];
                if (c != null && c.kind == Nk.NODE_EXPR_BLOCK)
                {
                    for (usz j = 0; j < c.child_count; j++) self.check_decl(c.children[j]);
                }
            }
        default:
            // type/struct/union/effect/irdl/etc.: walk for nested exprs.
            self.walk(d);
    }
}

// let/const/static: if both an explicit type and an initializer exist, the
// initializer must be a subtype of the declared type (soft).
fn void TypeChecker.check_binding(TypeChecker* self, Node* d)
{
    Node* declared = null;
    Node* init = null;

    for (usz i = 1; i < d.child_count; i++)
    {
        Node* c = d.children[i];
        if (c == null) continue;
        if (is_type_node(c)) { declared = c; continue; }
        if (c.kind == Nk.NODE_EFFECT_ROW) continue;
        init = c;   // last non-type, non-row child is the initializer
    }

    Node* bound_type = declared;
    if (init != null)
    {
        if (declared != null) { self.check(init, declared); }
        else { bound_type = self.synth(init); }
    }

    // Stamp the binder pattern with the binding's type so later uses (which
    // resolve to the pattern binder) can read it back via synth_name.
    if (bound_type != null && d.child_count >= 1)
    {
        self.bind_pattern_types(d.children[0], bound_type);
    }
}

// fn: extract the declared return type from the signature, then check each
// clause body against it.
// Return the field/variant block (NODE_EXPR_BLOCK) of a union type, or null.
fn Node* TypeChecker.union_variants_of(TypeChecker* self, Node* ty)
{
    Node* t = self.unfold(ty);
    if (t == null) return null;
    if (t.kind == Nk.NODE_TYPE_PTR && t.child_count >= 1) t = self.unfold(t.children[0]);
    if (t == null) return null;
    if (t.kind == Nk.NODE_TYPE_GENERIC_APP && t.child_count >= 1) t = self.unfold(t.children[0]);
    if (t == null) return null;
    Node* decl = null;
    if (t.kind == Nk.NODE_TYPEVAR && t.resolved != null) decl = t.resolved;
    if (decl == null) return null;
    Node* body = null;
    if (decl.kind == Nk.NODE_DECL_UNION)
    {
        body = decl;
    }
    if (decl.kind == Nk.NODE_DECL_ENUM)
    {
        // Enum: children[1..] are NODE_ENUM_VARIANT nodes
        // Return the enum decl itself as the "variants" node — union_match_exhaustive
        // will iterate its children
        return decl;
    }

    else if (decl.kind == Nk.NODE_DECL_TYPE && decl.child_count >= 1)
    {
        Node* b = decl.children[decl.child_count - 1];
        if (b != null && b.kind == Nk.NODE_DECL_UNION) body = b;
    }
    if (body == null) return null;
    for (usz i = 0; i < body.child_count; i++)
    {
        Node* c = body.children[i];
        if (c != null && c.kind == Nk.NODE_EXPR_BLOCK) return c;
    }
    return null;
}

// The single variant name a struct pattern selects (`{ some: v }` -> "some"),
// or null if it is not a single-field variant pattern. Also reports whether the
// arm carrying it has a guard (a guarded arm cannot complete coverage).
fn Node* struct_pat_variant_field(Node* pat)
{
    if (pat == null || pat.kind != Nk.NODE_PATTERN_STRUCT) return null;
    if (pat.child_count != 1) return null;          // a variant matches one tag
    Node* f = pat.children[0];
    if (f == null || f.kind != Nk.NODE_PATTERN_FIELD || f.child_count < 1) return null;
    Node* name = f.children[0];
    if (name == null || (name.kind != Nk.NODE_IDENT && name.kind != Nk.NODE_TYPEVAR)) return null;
    return name;
}

fn bool ident_name_eq(Node* a, Node* b)
{
    if (a == null || b == null) return false;
    if (a.p.ident.name_len != b.p.ident.name_len) return false;
    for (usz i = 0; i < a.p.ident.name_len; i++)
    {
        if (a.p.ident.name_ptr[i] != b.p.ident.name_ptr[i]) return false;
    }
    return true;
}

// Check whether the given clause/arm patterns cover every variant of a union.
// `patterns` is the parent block of clauses/arms; `is_clause` selects the node
// kind. Returns true (and the caller stamps FLAG_EXHAUSTIVE) when every union
// variant is matched by an unguarded single-variant struct pattern.
fn bool TypeChecker.union_match_exhaustive(TypeChecker* self, Node* variants, Node* parent, bool is_clause)
{
    // If the "variants" node is a NODE_DECL_ENUM, its ENUM_VARIANT children
    // are the variants. Map them to field-like names for matching.
    if (variants != null && variants.kind == Nk.NODE_DECL_ENUM)
    {
        int covered = 0; int total = 0;
        for (usz vi = 1; vi < variants.child_count; vi++)
        {
            Node* evar = variants.children[vi];
            if (evar == null || evar.kind != Nk.NODE_ENUM_VARIANT) continue;
            total++;
            // Check if any arm of the match/clause covers this variant name
            for (usz ai = 0; ai < parent.child_count; ai++)
            {
                Node* arm = parent.children[ai];
                if (arm == null) continue;
                Node* pat = arm.child_count >= 1 ? arm.children[0] : null;
                if (pat == null) continue;
                if (pat.kind == Nk.NODE_WILDCARD || pat.kind == Nk.NODE_PATTERN_WILDCARD)
                { covered = total; break; }
                if (pat.kind == Nk.NODE_PATTERN_IDENT || pat.kind == Nk.NODE_IDENT)
                {
                    // Check name matches variant
                    if (evar.child_count >= 1 && evar.children[0] != null)
                    {
                        Node* vname = evar.children[0];
                        if (vname.p.ident.name_len == pat.p.ident.name_len)
                        {
                            bool nm = true;
                            for (usz ci = 0; ci < vname.p.ident.name_len; ci++)
                            { if (vname.p.ident.name_ptr[ci] != pat.p.ident.name_ptr[ci]) { nm = false; break; } }
                            if (nm) { covered++; break; }
                        }
                    }
                }
            }
        }
        return total > 0 && covered >= total;
    }

    if (variants == null) return false;
    usz nvar = 0;
    for (usz i = 0; i < variants.child_count; i++)
    {
        Node* fd = variants.children[i];
        if (fd != null && fd.kind == Nk.NODE_FIELD_DECL) nvar++;
    }
    if (nvar == 0) return false;

    // For each declared variant, was it covered by an unguarded variant pattern?
    usz covered = 0;
    for (usz vi = 0; vi < variants.child_count; vi++)
    {
        Node* fd = variants.children[vi];
        if (fd == null || fd.kind != Nk.NODE_FIELD_DECL || fd.child_count < 1) continue;
        Node* vname = fd.children[0];
        bool seen = false;
        for (usz pi = 0; pi < parent.child_count; pi++)
        {
            Node* item = parent.children[pi];
            if (item == null) continue;
            Nk want = is_clause ? Nk.NODE_CLAUSE : Nk.NODE_MATCH_ARM;
            if (item.kind != want) continue;
            // skip guarded arms/clauses for coverage purposes
            bool guarded = false;
            for (usz k = 0; k < item.child_count; k++)
            {
                if (item.children[k] != null && item.children[k].kind == Nk.NODE_PATTERN_GUARD)
                {
                    guarded = true;
                }
            }
            if (guarded) continue;
            Node* pat = item.child_count >= 1 ? item.children[0] : null;
            Node* pf = struct_pat_variant_field(pat);
            if (pf != null && ident_name_eq(pf, vname)) { seen = true; break; }
        }
        if (seen) covered++;
    }
    return covered == nvar;
}

fn void TypeChecker.check_fn(TypeChecker* self, Node* fn_node)
{
    Node* sig = self.fn_signature_type(fn_node);

    // Signature shape: NODE_TYPE_FN[arg, ret], optionally wrapped as
    // NODE_TYPE_FN[NODE_TYPE_FN[arg, ret], NODE_EFFECT_ROW] when an effect row
    // is attached. Unwrap to recover the argument and return types.
    Node* arg = null;
    Node* ret = null;
    if (sig != null && sig.kind == Nk.NODE_TYPE_FN)
    {
        Node* lhs = sig.child_count >= 1 ? sig.children[0] : null;
        Node* rhs = sig.child_count >= 2 ? sig.children[1] : null;
        if (rhs != null && rhs.kind == Nk.NODE_EFFECT_ROW
            && lhs != null && lhs.kind == Nk.NODE_TYPE_FN)
        {
            // effect-row form: real signature is the inner fn-type.
            arg = lhs.child_count >= 1 ? lhs.children[0] : null;
            ret = lhs.child_count >= 2 ? lhs.children[1] : null;
        }
        else
        {
            arg = lhs;
            ret = rhs;
        }
    }

    // Apply `where C = T` bindings to the argument/return types, so a return
    // type written as a type variable is checked against its where-binding.
    arg = self.apply_where(fn_node, arg);
    ret = self.apply_where(fn_node, ret);

    // Walk clauses, binding parameter types from `arg` and checking each body
    // against the return type `ret`.
    for (usz i = 0; i < fn_node.child_count; i++)
    {
        Node* c = fn_node.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_EXPR_BLOCK)
        {
            for (usz j = 0; j < c.child_count; j++)
            {
                Node* clause = c.children[j];
                if (clause != null && clause.kind == Nk.NODE_CLAUSE)
                {
                    self.check_clause(clause, arg, ret);
                }
                else
                {
                    self.walk(clause);
                }
            }
            // If the parameter is a union and the clauses cover every variant,
            // the clause set is total — stamp it so the linter does not emit a
            // false "non-exhaustive" warning (it cannot see union variants).
            Node* variants = self.union_variants_of(arg);
            if (variants != null && self.union_match_exhaustive(variants, c, true))
            {
                c.flags |= ast::FLAG_EXHAUSTIVE;
            }
        }
    }
}

// Apply the function's `where C = T` equality bindings to a type: if `ty` is a
// type variable that a where-clause equates to a concrete type, return that
// concrete type. Other types are returned unchanged. (One level; sufficient for
// the `where C = Pair<...>` style in v.md §18.)
fn Node* TypeChecker.apply_where(TypeChecker* self, Node* fn_node, Node* ty)
{
    if (ty == null) return ty;
    // The equality applies under a pointer constructor as well: with
    // `where C = A`, the return type `*C` must compare equal to the body's
    // `*A` (the clause-body check is syntactic). One constructor level is
    // enough in practice (v.md §18 examples are all `*C`-shaped).
    if (ty.kind == Nk.NODE_TYPE_PTR && ty.child_count >= 1
        && ty.children[0] != null && ty.children[0].kind == Nk.NODE_TYPEVAR)
    {
        Node* inner = self.apply_where(fn_node, ty.children[0]);
        if (inner != ty.children[0])
        {
            return ast::node1(self.arena, Nk.NODE_TYPE_PTR, inner, ty.line, ty.col);
        }
        return ty;
    }
    if (ty.kind != Nk.NODE_TYPEVAR) return ty;
    if (ty.resolved == null) return ty;

    for (usz i = 0; i < fn_node.child_count; i++)
    {
        Node* wc = fn_node.children[i];
        if (wc == null || wc.kind != Nk.NODE_WHERE_CLAUSE) continue;
        // Each constraint is itself a NODE_WHERE_CLAUSE child of the form
        // [lhs, rhs] for an equality `C = T`.
        for (usz j = 0; j < wc.child_count; j++)
        {
            Node* cons = wc.children[j];
            if (cons == null || cons.kind != Nk.NODE_WHERE_CLAUSE) continue;
            if (cons.child_count < 2) continue;   // not an equality form
            Node* lhs = cons.children[0];
            Node* rhs = cons.children[1];
            if (lhs == null || rhs == null) continue;
            // Match when the where-LHS names the same type-parameter decl.
            if (lhs.kind == Nk.NODE_TYPEVAR && lhs.resolved == ty.resolved)
            {
                return rhs;
            }
        }
    }
    return ty;
}

// A clause: [param-pattern?, guard?, body]. We give the parameter pattern's
// binders the function's argument type, then check the body against `ret`.
fn void TypeChecker.check_clause(TypeChecker* self, Node* clause, Node* arg, Node* ret)
{
    if (clause.child_count == 0) return;

    // First child is the parameter pattern (when present).
    Node* first = clause.children[0];
    if (first != null && is_pattern_node(first))
    {
        // A struct pattern over a union parameter is refutable (matches one
        // variant), so mark it so the linter won't treat it as a catch-all and
        // wrongly flag following clauses as unreachable.
        if (arg != null && first.kind == Nk.NODE_PATTERN_STRUCT && self.is_union_type(arg))
        {
            first.flags |= ast::FLAG_REFUTABLE;
        }
        self.bind_pattern_types(first, arg);
    }

    // Type-check any clause guard (`| pat, guard -> body`). The guard is a
    // NODE_PATTERN_GUARD child between the pattern and the body; it must be a
    // bool condition. Without this, guards escaped type-checking entirely.
    for (usz gi = 1; gi + 1 < clause.child_count; gi++)
    {
        Node* g = clause.children[gi];
        if (g == null || g.kind != Nk.NODE_PATTERN_GUARD) continue;
        if (g.child_count >= 1)
        {
            Node* gexpr = g.children[0];
            self.walk(gexpr);
            Node* gt = self.synth(gexpr);
            if (gt != null && type_prim(gt) != Prim.PRIM_BOOL)
            {
                self.soft("clause guard is not a bool condition", gexpr.line, gexpr.col);
            }
        }
    }

    Node* body = clause.children[clause.child_count - 1];

    // Walk the body so all sub-expressions get synthesized/checked.
    self.walk(body);

    if (ret != null && body != null)
    {
        // `fn float_bits : f32 -> u32 | x -> transmute(x)` (conformance 89):
        // like the let-ascription case in check(), the only syntactic place
        // for the transmute's TARGET type is the fn's declared codomain.
        if (body.kind == Nk.NODE_EXPR_TRANSMUTE && body.type_annotation == null)
        {
            body.type_annotation = ret;
        }
        // Likewise: a struct-literal body returned from a fn whose codomain
        // is a generic-struct instantiation (`-> Pair<i64, f64>` where the
        // body is `Pair { ... }`) takes the instantiation as its stamp.
        self.stamp_expected_struct_lit(body, ret);
        Node* bt = self.synth(body);
        // arg_fits allows an untyped numeric literal body to adapt to the
        // declared numeric return type (e.g. `| () -> 42` for `-> i32`).
        if (bt != null && !self.arg_fits(body, bt, ret))
        {
            self.soft("clause body type does not match declared return type", body.line, body.col);
        }
    }
}

// Distribute a parameter type over a pattern, recording each binder's type on
// its PatIdent's inner name node (so `synth_name` can read it back).
// Stamp a handler-arm ARGUMENT pattern with the declared op parameter types,
// flattening tuple patterns onto the op's flat arg-slot positions — exactly
// the same walk the lowering's emit_arm_arg_params performs (it emits one
// IR_PARAM per flattened slot; here we bind one TYPE per flattened slot).
// Returns the next free slot index.
fn int TypeChecker.stamp_arm_pattern(TypeChecker* self, Node* pat, Node* op_decl, int slot)
{
    if (pat == null) return slot;
    if (pat.kind == Nk.NODE_PATTERN_TUPLE)
    {
        for (usz i = 0; i < pat.child_count; i++)
        { slot = self.stamp_arm_pattern(pat.children[i], op_decl, slot); }
        return slot;
    }
    if (pat.kind == Nk.NODE_PATTERN_IDENT)
    {
        Node* pty = ast::effect_op_param_type(op_decl, slot);
        if (pty != null) { self.bind_pattern_types(pat, pty); }
        return slot + 1;
    }
    // Wildcards/literals consume a slot but bind nothing.
    return slot + 1;
}

fn void TypeChecker.bind_pattern_types(TypeChecker* self, Node* pat, Node* ty)
{
    if (pat == null) return;

    switch (pat.kind)
    {
        case Nk.NODE_PATTERN_IDENT:
            // child 0 is the name; stamp the type onto it and the pattern.
            if (pat.child_count >= 1 && ty != null)
            {
                pat.children[0].type_annotation = ty;
                pat.type_annotation = ty;
            }

        case Nk.NODE_PATTERN_OR:
            // Bind every alternative to the scrutinee type (ident binders get
            // stamped; literals are checked by the caller's body walk). Only
            // literals, binders and '_' are lowered — a struct/tuple/union
            // alternative would need decision-tree dispatch that does not
            // exist, and previously compiled to a DEAD arm silently.
            // NOTE: do NOT stamp the OR node itself — the lowering's test
            // IR_BINs carry it as src and would wrongly inherit the
            // scrutinee type instead of i1.
            for (usz oi = 0; oi < pat.child_count; oi++)
            {
                Node* alt = pat.children[oi];
                if (alt == null) continue;
                if (alt.kind != Nk.NODE_PATTERN_LITERAL
                    && alt.kind != Nk.NODE_PATTERN_IDENT
                    && alt.kind != Nk.NODE_PATTERN_WILDCARD)
                {
                    self.hard("unsupported alternative in an or-pattern (only literals, binders and '_' are lowered; use separate arms)",
                              alt.line, alt.col);
                    continue;
                }
                self.bind_pattern_types(alt, ty);
            }
        case Nk.NODE_PATTERN_TUPLE:
            // Always stamp the tuple pattern itself with the given type.
            // This lets IR_PARAM codegen find the type via pv.src.type_annotation
            // when the param src is the tuple pattern node.
            pat.type_annotation = ty;
            // Distribute a tuple type componentwise.
            Node* tt = self.unfold(ty);
            if (tt != null && tt.kind == Nk.NODE_TYPE_TUPLE
                && tt.child_count == pat.child_count)
            {
                for (usz i = 0; i < pat.child_count; i++)
                {
                    self.bind_pattern_types(pat.children[i], tt.children[i]);
                }
            }
            else if (pat.child_count == 1 && pat.children[0] != null)
            {
                // Single-element "parenthesised" pattern (x) against a non-tuple
                // type: bind the inner binder to ty directly.
                // e.g. fn f : (i64) -> i64  |  (x) -> x   => x : i64
                self.bind_pattern_types(pat.children[0], ty);
            }
            else if (tt != null && tt.kind == Nk.NODE_TYPE_TUPLE
                     && tt.child_count > 0 && pat.child_count > 0)
            {
                // Tuple PATTERN vs tuple DOMAIN arity mismatch. Binding a
                // prefix silently (the old behaviour) left the trailing
                // binders untyped, which downstream lowered into unbound SSA
                // values — a miscompile, not an inconvenience. It is now a
                // hard type error: destructure exactly the domain arity, or
                // bind the whole tuple under one name instead.
                self.hard("pattern arity does not match tuple domain arity",
                          pat.line, pat.col);
            }
            else if (tt != null && tt.kind != Nk.NODE_TYPE_TUPLE && pat.child_count >= 2)
            {
                // Tuple pattern against a non-tuple type: equally a hard
                // error (was silently ignored, leaving the binders untyped).
                self.hard("tuple pattern against non-tuple type", pat.line, pat.col);
            }

        // Newtype destructuring:  Dollars(d)  — PatStruct[TypeVar, PatIdent]
        // child[0] = the newtype name (TypeVar), child[1..] = field binders.
        // The single binder gets the newtype's underlying type.
        case Nk.NODE_PATTERN_STRUCT:
            {
                bool field_form = pat.child_count >= 1 && pat.children[0] != null
                              && pat.children[0].kind == Nk.NODE_PATTERN_FIELD;
                if (field_form && ast::union_decl_of(ty) != null)
                {
                    // Union-variant pattern `{ name: binder }`: resolve every
                    // field against the union's variant list, type the binder
                    // with the variant payload, and stamp the pattern with
                    // the union type (lowering recovers the union decl from
                    // that annotation to compute the discriminant).
                    Node* udecl = ast::union_decl_of(ty);
                    // Untagged C-union (r13): the repr is one 64-bit cell
                    // with NO discriminant slot — there is nothing a variant
                    // pattern could test. v.md §9 makes fields (not matches)
                    // the interpretation mechanism, so reject loudly.
                    if (ast::union_is_c_union(udecl))
                    {
                        self.hard("untagged C-union has no discriminant — access its fields, don't match it",
                                  pat.line, pat.col);
                        return;
                    }
                    pat.type_annotation = ty;
                    pat.flags |= ast::FLAG_REFUTABLE;
                    for (usz vi2 = 0; vi2 < pat.child_count; vi2++)
                    {
                        Node* pf = pat.children[vi2];
                        if (pf == null || pf.kind != Nk.NODE_PATTERN_FIELD || pf.child_count < 2) continue;
                        Node* vn = pf.children[0];
                        Node* bind = pf.children[1];
                        if (vn == null) continue;
                        Node* payload_ty = null;
                        int ord = ast::union_variant_lookup(
                            udecl, vn.p.ident.name_ptr, vn.p.ident.name_len, &payload_ty);
                        if (ord < 0)
                        {
                            self.hard("unknown variant in union pattern (check the union's variant list)",
                                      vn.line, vn.col);
                            continue;
                        }
                        // Generic union (`Maybe<i64>`): the decl's payload
                        // names the type parameter — substitute it with the
                        // instantiation's argument before scalar typing.
                        payload_ty = ast::generic_payload_subst(ty, payload_ty);
                        if (bind != null && bind.kind == Nk.NODE_PATTERN_IDENT)
                        {
                            // Unit payload: a `marker` binder is tolerated (the
                            // lowering binds it to the variant's unit value) but
                            // it carries NO type — stamping `()` would make a
                            // returned marker (`{ none: n } -> n`, conformance
                            // 63) trip the clause-body/return-type consistency
                            // check. There is nothing to prove about a
                            // zero-width value; soft typing leaves it alone.
                            if (payload_ty != null && payload_ty.kind == Nk.NODE_EXPR_UNIT)
                            {
                                continue;
                            }
                            if (!ast::union_payload_is_scalar(payload_ty))
                            {
                                self.hard("variant payload is not lowered yet (only scalar payloads fit the { i32, i64 } repr)",
                                          bind.line, bind.col);
                            }
                            self.bind_pattern_types(bind, payload_ty);
                            pf.type_annotation = payload_ty;
                        }
                    }
                }
                else if (field_form && ast::struct_decl_of(ty) != null)
                {
                    // Plain-struct destructuring (v.md §5 `let { x, y } = p`,
                    // `{ fst: a, snd: b }` on fn clauses): IRREFUTABLE —
                    // the field names select, the binders receive the field
                    // values.  This used to be mistaken for a union-variant
                    // pattern: shorthand fields were silently skipped (the
                    // binders were never stamped, and the lowering bound
                    // nothing — uses read as 0) and the explicit form
                    // hard-errored "unknown variant in union pattern".
                    Node* sdecl = ast::struct_decl_of(ty);
                    pat.type_annotation = ty;
                    for (usz fi = 0; fi < pat.child_count; fi++)
                    {
                        Node* pf = pat.children[fi];
                        if (pf == null || pf.kind != Nk.NODE_PATTERN_FIELD
                            || pf.child_count < 1) continue;
                        Node* vn = pf.children[0];
                        if (vn == null || vn.p.ident.name_ptr == null) continue;
                        Node* fty = null;
                        int ford = ast::struct_field_lookup(sdecl,
                            vn.p.ident.name_ptr, vn.p.ident.name_len, &fty);
                        if (ford < 0)
                        {
                            self.hard("unknown field in struct pattern (check the struct's field list)",
                                      vn.line, vn.col);
                            continue;
                        }
                        // Generic struct (`Pair<i64, bool>`): substitute the
                        // decl's type parameter with the instantiation's
                        // argument before scalar typing.
                        fty = ast::generic_payload_subst(ty, fty);
                        pf.type_annotation = fty;
                        if (pf.child_count >= 2 && pf.children[1] != null
                            && pf.children[1].kind != Nk.NODE_PATTERN_LITERAL)
                        {
                            // `{ name: subpattern }` — bind recursively
                            // (nested tuples/structs work naturally).
                            self.bind_pattern_types(pf.children[1], fty);
                        }
                        else if (pf.child_count < 2)
                        {
                            // Shorthand `{ x }`: the name IS the binder — the
                            // resolver keys uses to the FIELD node
                            // (bind_pattern_field), so the stamped field node
                            // above is what downstream reads.
                            vn.type_annotation = fty;
                        }
                        // `{ name: literal }` in binding position: a literal
                        // cannot bind and a let-pattern must be irrefutable —
                        // tolerated silently, same convention as tuple lets.
                    }
                }
                else if (ty != null && pat.child_count >= 2)
                {
                // Resolve underlying type from the newtype decl.
                Node* nt_name = pat.children[0];
                Node* underlying = ty;   // default: same type
                if (nt_name != null && nt_name.resolved != null
                    && nt_name.resolved.kind == Nk.NODE_DECL_NEWTYPE
                    && nt_name.resolved.child_count >= 2)
                {
                    underlying = nt_name.resolved.children[1];
                }
                // Bind each field binder to the underlying type.
                // For single-field newtypes there's exactly one binder.
                for (usz i = 1; i < pat.child_count; i++)
                {
                    Node* fp = pat.children[i];
                    if (fp != null) self.bind_pattern_types(fp, underlying);
                }
                }
            }

        default:
            break;   // wildcard / literal: nothing to bind here
    }
}

fn bool is_pattern_node(Node* n)
{
    if (n == null) return false;
    switch (n.kind)
    {
        case Nk.NODE_PATTERN_WILDCARD:
        case Nk.NODE_PATTERN_LITERAL:
        case Nk.NODE_PATTERN_IDENT:
        case Nk.NODE_PATTERN_TUPLE:
        case Nk.NODE_PATTERN_STRUCT:
        case Nk.NODE_PATTERN_UNION:
        case Nk.NODE_PATTERN_OR:
            return true;
        default:
            return false;
    }
}

// Generic recursive walk that synthesizes types for every expression it meets
// and recurses into declarations it understands.
fn void TypeChecker.walk(TypeChecker* self, Node* n)
{
    if (n == null) return;
    if (self.sub_depth >= MAX_SUBTYPE_DEPTH) return;
    self.sub_depth++;
    self.walk_body(n);
    self.sub_depth--;
}

fn void TypeChecker.walk_body(TypeChecker* self, Node* n)
{
    switch (n.kind)
    {
        case Nk.NODE_DECL_FN:
            self.check_fn(n);
            return;
        case Nk.NODE_DECL_LET:
        case Nk.NODE_DECL_MUT:
        case Nk.NODE_DECL_CONST:
        case Nk.NODE_DECL_STATIC:
            self.check_binding(n);
            return;
        default:
            break;
    }

    // Synthesize a type for expression nodes (also drives nested checks).
    if (is_expr(n))
    {
        self.synth(n);
        return;
    }

    // Otherwise recurse structurally.
    for (usz i = 0; i < n.child_count; i++)
    {
        self.walk(n.children[i]);
    }
}

fn bool is_expr(Node* n)
{
    if (n == null) return false;
    switch (n.kind)
    {
        case Nk.NODE_LIT_INT:
        case Nk.NODE_LIT_FLOAT:
        case Nk.NODE_LIT_BOOL:
        case Nk.NODE_LIT_CHAR:
        case Nk.NODE_LIT_STRING:
        case Nk.NODE_LIT_RAW_BYTES:
        case Nk.NODE_LIT_NULL:
        case Nk.NODE_IDENT:
        case Nk.NODE_EXPR_BINARY:
        case Nk.NODE_EXPR_UNARY:
        case Nk.NODE_EXPR_ASSIGN:
        case Nk.NODE_EXPR_CAST:
        case Nk.NODE_EXPR_IF:
        case Nk.NODE_EXPR_RANGE:
        case Nk.NODE_EXPR_PIPELINE:
        case Nk.NODE_EXPR_CALL:
        case Nk.NODE_EXPR_TENSOR_LIT:
        case Nk.NODE_EXPR_MATMUL:
        case Nk.NODE_EXPR_FIELD:
        case Nk.NODE_EXPR_METHOD_CALL:
        case Nk.NODE_EXPR_INDEX:
        case Nk.NODE_EXPR_STRUCT_LIT:
            return true;
        default:
            return false;
    }
}
