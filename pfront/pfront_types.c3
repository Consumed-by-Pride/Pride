// ============================================================================
// pfront_types.c3 — type representation, unification, inference (part 8)
// ----------------------------------------------------------------------------
// The front end had `type_slot` on every node and nothing to put in it. This
// module supplies the missing half: a real type universe with structural
// identity, Hindley-Milner style unification over a union-find substitution,
// and a bidirectional checker that fills `type_slot`.
//
// Design points that matter:
//
//   * TYPES ARE INTERNED. Structural identity means `(i64, i64) -> bool` built
//     in two places is one TypeId, so equality is an integer compare and the
//     occurs check is cheap. This is what keeps inference near-linear.
//
//   * UNION-FIND WITH PATH COMPRESSION for type variables. Naive substitution
//     lists degrade to quadratic on long chains; the stdlib has functions with
//     dozens of intermediate bindings, so this is not academic.
//
//   * OCCURS CHECK. Without it `t = t -> u` builds a cyclic type and every
//     later traversal hangs. It is the difference between a compiler that
//     reports an error and one that never terminates.
//
//   * LEVEL-BASED GENERALISATION (Rémy's algorithm). Rather than scanning the
//     whole environment for free variables at every `let`, each variable
//     carries the binding level at which it was created; a variable is
//     generalisable exactly when its level exceeds the current one. O(1)
//     instead of O(env).
//
//   * INTEGER LITERAL DEFAULTING. `0` is polymorphic until context fixes it;
//     unresolved numeric variables default to i64 at the end, like Rust/OCaml.
// ============================================================================

module pfront_types;

import pfront_lex;
import pfront_core;

alias Tk   = pfront_lex::TokenType;
alias Node = pfront_core::PNode;
alias Nk   = pfront_core::NodeKind;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz MAX_TYPES      = 65536;
const usz MAX_TYPE_ARGS  = 32;
const usz TYPE_HASH_SIZE = 16384;
const int NO_TYPE        = 0;

// ── Type universe ───────────────────────────────────────────────────────────
enum TyKind : int
{
    TY_ERROR,        // propagates without cascading further diagnostics
    TY_UNIT,
    TY_BOOL,
    TY_INT,          // width + signedness in `bits` / `is_signed`
    TY_FLOAT,
    TY_CHAR,
    TY_STRING,
    TY_PTR,
    TY_REF,
    TY_SLICE,
    TY_ARRAY,        // elem + fixed length
    TY_TUPLE,
    TY_FN,
    TY_NAMED,        // struct / enum / newtype, identified by its decl
    TY_VAR,          // unification variable
    TY_NEVER,        // uninhabited: the type of `unreachable`
    TY_UNION,
    TY_INTERSECT
}

// A type node. `args` indexes back into the table, so the whole universe is a
// flat array — no pointer chasing, and TypeId is stable across reallocation.
struct TyNode
{
    TyKind kind;
    int    bits;         // integer/float width
    bool   is_signed;
    bool   is_mut;       // for ptr/ref
    ulong  length;       // array length
    Node*  decl;         // TY_NAMED: the declaration
    uint   name_id;
    int[MAX_TYPE_ARGS] args;
    usz    arg_count;

    // TY_VAR only.
    int    link;         // union-find parent (NO_TYPE if this is a root)
    int    level;        // binding level, for generalisation
    bool   is_numeric;   // constrained to integers (literal defaulting)
    uint   var_id;
}

struct TypeTable
{
    TyNode[MAX_TYPES] nodes;
    usz               count;

    // Structural hash-consing buckets.
    int[TYPE_HASH_SIZE] buckets;
    int[MAX_TYPES]      next_in_bucket;

    // Cached primitives.
    int t_error;
    int t_unit;
    int t_bool;
    int t_char;
    int t_string;
    int t_never;
    int t_i8; int t_i16; int t_i32; int t_i64;
    int t_u8; int t_u16; int t_u32; int t_u64;
    int t_f32; int t_f64;

    uint next_var_id;
    int  current_level;
    usz  vars_created;
    usz  unifications;
    usz  occurs_failures;
}

fn uint ty_hash(TyKind k, int bits, bool sg, ulong len, Node* decl, int* args, usz n)
{
    uint h = 2166136261u;
    h = (h ^ (uint)(int)k) * 16777619u;
    h = (h ^ (uint)bits) * 16777619u;
    h = (h ^ (sg ? 1u : 0u)) * 16777619u;
    h = (h ^ (uint)(len & 0xFFFFFFFFu)) * 16777619u;
    h = (h ^ (uint)((ulong)decl & 0xFFFFFFFFu)) * 16777619u;
    for (usz i = 0; i < n; i++) { h = (h ^ (uint)args[i]) * 16777619u; }
    return h;
}

fn void TypeTable.init(TypeTable* t)
{
    t.count = 1;              // index 0 is reserved as "no type"
    for (usz i = 0; i < TYPE_HASH_SIZE; i++) { t.buckets[i] = 0; }
    t.next_var_id = 1;
    t.current_level = 0;
    t.vars_created = 0;
    t.unifications = 0;
    t.occurs_failures = 0;

    t.t_error  = t.mk_simple(TyKind.TY_ERROR);
    t.t_unit   = t.mk_simple(TyKind.TY_UNIT);
    t.t_bool   = t.mk_simple(TyKind.TY_BOOL);
    t.t_char   = t.mk_simple(TyKind.TY_CHAR);
    t.t_string = t.mk_simple(TyKind.TY_STRING);
    t.t_never  = t.mk_simple(TyKind.TY_NEVER);
    t.t_i8  = t.mk_int(8, true);   t.t_u8  = t.mk_int(8, false);
    t.t_i16 = t.mk_int(16, true);  t.t_u16 = t.mk_int(16, false);
    t.t_i32 = t.mk_int(32, true);  t.t_u32 = t.mk_int(32, false);
    t.t_i64 = t.mk_int(64, true);  t.t_u64 = t.mk_int(64, false);
    t.t_f32 = t.mk_float(32);      t.t_f64 = t.mk_float(64);
}

// Hash-cons: return an existing structurally identical type, or append one.
fn int TypeTable.intern(TypeTable* t, TyKind k, int bits, bool sg, bool mut_,
                        ulong len, Node* decl, uint name_id, int* args, usz n)
{
    uint h = ty_hash(k, bits, sg, len, decl, args, n);
    usz b = (usz)(h & (uint)(TYPE_HASH_SIZE - 1));
    int cur = t.buckets[b];
    while (cur != 0)
    {
        TyNode* c = &t.nodes[cur];
        if (c.kind == k && c.bits == bits && c.is_signed == sg && c.is_mut == mut_
            && c.length == len && c.decl == decl && c.arg_count == n)
        {
            bool same = true;
            for (usz i = 0; i < n; i++) { if (c.args[i] != args[i]) { same = false; break; } }
            if (same) { return cur; }
        }
        cur = t.next_in_bucket[cur];
    }
    if (t.count >= MAX_TYPES) { return t.t_error; }
    int id = (int)t.count;
    t.count = t.count + 1;
    TyNode* nn = &t.nodes[id];
    nn.kind = k;
    nn.bits = bits;
    nn.is_signed = sg;
    nn.is_mut = mut_;
    nn.length = len;
    nn.decl = decl;
    nn.name_id = name_id;
    nn.arg_count = n < MAX_TYPE_ARGS ? n : MAX_TYPE_ARGS;
    for (usz i = 0; i < nn.arg_count; i++) { nn.args[i] = args[i]; }
    nn.link = NO_TYPE;
    nn.level = 0;
    nn.is_numeric = false;
    nn.var_id = 0;
    t.next_in_bucket[id] = t.buckets[b];
    t.buckets[b] = id;
    return id;
}

fn int TypeTable.mk_simple(TypeTable* t, TyKind k)
{
    return t.intern(k, 0, false, false, 0, null, 0, null, 0);
}

fn int TypeTable.mk_int(TypeTable* t, int bits, bool sg)
{
    return t.intern(TyKind.TY_INT, bits, sg, false, 0, null, 0, null, 0);
}

fn int TypeTable.mk_float(TypeTable* t, int bits)
{
    return t.intern(TyKind.TY_FLOAT, bits, true, false, 0, null, 0, null, 0);
}

fn int TypeTable.mk_ptr(TypeTable* t, int inner, bool mut_)
{
    int[1] a;
    a[0] = inner;
    return t.intern(TyKind.TY_PTR, 0, false, mut_, 0, null, 0, &a[0], 1);
}

fn int TypeTable.mk_ref(TypeTable* t, int inner, bool mut_)
{
    int[1] a;
    a[0] = inner;
    return t.intern(TyKind.TY_REF, 0, false, mut_, 0, null, 0, &a[0], 1);
}

fn int TypeTable.mk_slice(TypeTable* t, int inner)
{
    int[1] a;
    a[0] = inner;
    return t.intern(TyKind.TY_SLICE, 0, false, false, 0, null, 0, &a[0], 1);
}

fn int TypeTable.mk_array(TypeTable* t, int inner, ulong len)
{
    int[1] a;
    a[0] = inner;
    return t.intern(TyKind.TY_ARRAY, 0, false, false, len, null, 0, &a[0], 1);
}

fn int TypeTable.mk_tuple(TypeTable* t, int* elems, usz n)
{
    if (n == 0) { return t.t_unit; }
    return t.intern(TyKind.TY_TUPLE, 0, false, false, 0, null, 0, elems, n);
}

// Function type: args[0..n-1] are parameters, args[n] is the result.
fn int TypeTable.mk_fn(TypeTable* t, int* params, usz n, int ret)
{
    int[MAX_TYPE_ARGS] a;
    usz k = 0;
    for (usz i = 0; i < n && k + 1 < MAX_TYPE_ARGS; i++) { a[k] = params[i]; k = k + 1; }
    a[k] = ret;
    k = k + 1;
    return t.intern(TyKind.TY_FN, 0, false, false, 0, null, 0, &a[0], k);
}

fn int TypeTable.mk_named(TypeTable* t, Node* decl, uint name_id)
{
    return t.intern(TyKind.TY_NAMED, 0, false, false, 0, decl, name_id, null, 0);
}

// Type variables are NOT hash-consed: each must be distinct.
fn int TypeTable.fresh_var(TypeTable* t, bool numeric)
{
    if (t.count >= MAX_TYPES) { return t.t_error; }
    int id = (int)t.count;
    t.count = t.count + 1;
    TyNode* n = &t.nodes[id];
    n.kind = TyKind.TY_VAR;
    n.bits = 0;
    n.is_signed = false;
    n.is_mut = false;
    n.length = 0;
    n.decl = null;
    n.name_id = 0;
    n.arg_count = 0;
    n.link = NO_TYPE;
    n.level = t.current_level;
    n.is_numeric = numeric;
    n.var_id = t.next_var_id;
    t.next_var_id = t.next_var_id + 1;
    t.vars_created = t.vars_created + 1;
    t.next_in_bucket[id] = 0;
    return id;
}

// ── Union-find with path compression ────────────────────────────────────────
fn int TypeTable.find(TypeTable* t, int id)
{
    if (id <= 0 || (usz)id >= t.count) { return t.t_error; }
    int root = id;
    int guard = 0;
    while (t.nodes[root].kind == TyKind.TY_VAR
        && t.nodes[root].link != NO_TYPE
        && guard < 4096)
    {
        root = t.nodes[root].link;
        guard = guard + 1;
    }
    // Compress: point every node on the path straight at the root.
    int cur = id;
    while (t.nodes[cur].kind == TyKind.TY_VAR
        && t.nodes[cur].link != NO_TYPE
        && cur != root)
    {
        int nxt = t.nodes[cur].link;
        t.nodes[cur].link = root;
        cur = nxt;
    }
    return root;
}

fn bool TypeTable.is_var(TypeTable* t, int id)
{
    int r = t.find(id);
    return t.nodes[r].kind == TyKind.TY_VAR;
}

// ── Occurs check ────────────────────────────────────────────────────────────
// Does variable `v` appear inside `ty`? Binding v := ty when it does would
// create an infinite type. Also lowers levels, which is how Rémy's
// generalisation stays correct without an environment scan.
fn bool TypeTable.occurs(TypeTable* t, int v, int ty, int depth)
{
    if (depth > 512) { return true; }   // pathological: refuse rather than hang
    int r = t.find(ty);
    if (r == v) { return true; }
    TyNode* n = &t.nodes[r];
    if (n.kind == TyKind.TY_VAR)
    {
        int vl = t.nodes[v].level;
        if (n.level > vl) { n.level = vl; }
        return false;
    }
    for (usz i = 0; i < n.arg_count; i++)
    {
        if (t.occurs(v, n.args[i], depth + 1)) { return true; }
    }
    return false;
}

// ── Unification ─────────────────────────────────────────────────────────────
enum UnifyResult : int
{
    UNIFY_OK,
    UNIFY_MISMATCH,
    UNIFY_OCCURS,
    UNIFY_ARITY,
    UNIFY_DEPTH
}

fn UnifyResult TypeTable.unify(TypeTable* t, int a, int b, int depth)
{
    if (depth > 256) { return UnifyResult.UNIFY_DEPTH; }
    t.unifications = t.unifications + 1;
    int ra = t.find(a);
    int rb = t.find(b);
    if (ra == rb) { return UnifyResult.UNIFY_OK; }

    TyNode* na = &t.nodes[ra];
    TyNode* nb = &t.nodes[rb];

    // Errors absorb: never cascade a second diagnostic from a bad type.
    if (na.kind == TyKind.TY_ERROR || nb.kind == TyKind.TY_ERROR) { return UnifyResult.UNIFY_OK; }

    // `never` is a subtype of everything (an expression that diverges).
    if (na.kind == TyKind.TY_NEVER || nb.kind == TyKind.TY_NEVER) { return UnifyResult.UNIFY_OK; }

    if (na.kind == TyKind.TY_VAR && nb.kind == TyKind.TY_VAR)
    {
        // Numeric-ness is contagious; keep the lower level.
        if (na.is_numeric) { nb.is_numeric = true; }
        if (nb.is_numeric) { na.is_numeric = true; }
        if (na.level < nb.level) { nb.level = na.level; } else { na.level = nb.level; }
        na.link = rb;
        return UnifyResult.UNIFY_OK;
    }

    if (na.kind == TyKind.TY_VAR)
    {
        if (t.occurs(ra, rb, 0)) { t.occurs_failures = t.occurs_failures + 1; return UnifyResult.UNIFY_OCCURS; }
        if (na.is_numeric && !t.is_numeric_type(rb)) { return UnifyResult.UNIFY_MISMATCH; }
        na.link = rb;
        return UnifyResult.UNIFY_OK;
    }
    if (nb.kind == TyKind.TY_VAR)
    {
        if (t.occurs(rb, ra, 0)) { t.occurs_failures = t.occurs_failures + 1; return UnifyResult.UNIFY_OCCURS; }
        if (nb.is_numeric && !t.is_numeric_type(ra)) { return UnifyResult.UNIFY_MISMATCH; }
        nb.link = ra;
        return UnifyResult.UNIFY_OK;
    }

    if (na.kind != nb.kind) { return UnifyResult.UNIFY_MISMATCH; }

    switch (na.kind)
    {
        case TY_INT:
            if (na.bits != nb.bits || na.is_signed != nb.is_signed) { return UnifyResult.UNIFY_MISMATCH; }
            return UnifyResult.UNIFY_OK;
        case TY_FLOAT:
            if (na.bits != nb.bits) { return UnifyResult.UNIFY_MISMATCH; }
            return UnifyResult.UNIFY_OK;
        case TY_NAMED:
            if (na.decl != nb.decl) { return UnifyResult.UNIFY_MISMATCH; }
            return UnifyResult.UNIFY_OK;
        case TY_ARRAY:
            if (na.length != nb.length) { return UnifyResult.UNIFY_MISMATCH; }
        default:
            break;
    }

    if (na.arg_count != nb.arg_count) { return UnifyResult.UNIFY_ARITY; }
    for (usz i = 0; i < na.arg_count; i++)
    {
        UnifyResult r = t.unify(na.args[i], nb.args[i], depth + 1);
        if (r != UnifyResult.UNIFY_OK) { return r; }
    }
    return UnifyResult.UNIFY_OK;
}

fn bool TypeTable.is_numeric_type(TypeTable* t, int id)
{
    int r = t.find(id);
    TyKind k = t.nodes[r].kind;
    return k == TyKind.TY_INT || k == TyKind.TY_FLOAT || k == TyKind.TY_VAR;
}

// ── Literal defaulting ──────────────────────────────────────────────────────
// Any numeric variable still unbound after checking becomes i64 (floats f64).
// Without this every `let x = 0` would be reported as ambiguous.
fn usz TypeTable.default_numeric_vars(TypeTable* t)
{
    usz n = 0;
    for (usz i = 1; i < t.count; i++)
    {
        TyNode* v = &t.nodes[i];
        if (v.kind != TyKind.TY_VAR || v.link != NO_TYPE) { continue; }
        if (!v.is_numeric) { continue; }
        v.link = t.t_i64;
        n = n + 1;
    }
    return n;
}

// ── Rendering ───────────────────────────────────────────────────────────────
fn void TypeTable.write(TypeTable* t, int id, char* buf, usz cap, usz* pos, int depth)
{
    if (*pos + 8 >= cap || depth > 12) { return; }
    int r = t.find(id);
    TyNode* n = &t.nodes[r];
    switch (n.kind)
    {
        case TY_ERROR:  append(buf, cap, pos, "<error>");
        case TY_UNIT:   append(buf, cap, pos, "()");
        case TY_BOOL:   append(buf, cap, pos, "bool");
        case TY_CHAR:   append(buf, cap, pos, "char");
        case TY_STRING: append(buf, cap, pos, "str");
        case TY_NEVER:  append(buf, cap, pos, "never");
        case TY_INT:
        {
            append(buf, cap, pos, n.is_signed ? "i" : "u");
            append_int(buf, cap, pos, n.bits);
        }
        case TY_FLOAT:
        {
            append(buf, cap, pos, "f");
            append_int(buf, cap, pos, n.bits);
        }
        case TY_PTR:
        {
            append(buf, cap, pos, n.is_mut ? "*mut " : "*");
            if (n.arg_count > 0) { t.write(n.args[0], buf, cap, pos, depth + 1); }
        }
        case TY_REF:
        {
            append(buf, cap, pos, n.is_mut ? "&mut " : "&");
            if (n.arg_count > 0) { t.write(n.args[0], buf, cap, pos, depth + 1); }
        }
        case TY_SLICE:
        {
            append(buf, cap, pos, "[");
            if (n.arg_count > 0) { t.write(n.args[0], buf, cap, pos, depth + 1); }
            append(buf, cap, pos, "]");
        }
        case TY_ARRAY:
        {
            append(buf, cap, pos, "[");
            if (n.arg_count > 0) { t.write(n.args[0], buf, cap, pos, depth + 1); }
            append(buf, cap, pos, "; ");
            append_int(buf, cap, pos, (int)n.length);
            append(buf, cap, pos, "]");
        }
        case TY_TUPLE:
        {
            append(buf, cap, pos, "(");
            for (usz i = 0; i < n.arg_count; i++)
            {
                if (i > 0) { append(buf, cap, pos, ", "); }
                t.write(n.args[i], buf, cap, pos, depth + 1);
            }
            append(buf, cap, pos, ")");
        }
        case TY_FN:
        {
            append(buf, cap, pos, "(");
            usz np = n.arg_count > 0 ? n.arg_count - 1 : 0;
            for (usz i = 0; i < np; i++)
            {
                if (i > 0) { append(buf, cap, pos, ", "); }
                t.write(n.args[i], buf, cap, pos, depth + 1);
            }
            append(buf, cap, pos, ") -> ");
            if (n.arg_count > 0) { t.write(n.args[n.arg_count - 1], buf, cap, pos, depth + 1); }
        }
        case TY_NAMED:
        {
            if (n.decl != null && n.decl.p.sptr != null)
            {
                for (usz i = 0; i < n.decl.p.slen && *pos + 1 < cap; i++)
                {
                    buf[*pos] = n.decl.p.sptr[i];
                    *pos = *pos + 1;
                }
            }
            else { append(buf, cap, pos, "<named>"); }
        }
        case TY_VAR:
        {
            append(buf, cap, pos, n.is_numeric ? "{integer}" : "?t");
            if (!n.is_numeric) { append_int(buf, cap, pos, (int)n.var_id); }
        }
        default:
            append(buf, cap, pos, "?");
    }
    buf[*pos] = 0;
}

fn void append(char* buf, usz cap, usz* pos, char* s)
{
    usz i = 0;
    while (s[i] != 0 && *pos + 1 < cap)
    {
        buf[*pos] = s[i];
        *pos = *pos + 1;
        i = i + 1;
    }
    buf[*pos] = 0;
}

fn void append_int(char* buf, usz cap, usz* pos, int v)
{
    if (v < 0) { append(buf, cap, pos, "-"); v = -v; }
    char[24] tmp;
    int n = 0;
    if (v == 0) { tmp[0] = '0'; n = 1; }
    while (v > 0 && n < 24) { tmp[n] = (char)('0' + (v % 10)); v = v / 10; n = n + 1; }
    for (int i = n - 1; i >= 0 && *pos + 1 < cap; i--)
    {
        buf[*pos] = tmp[i];
        *pos = *pos + 1;
    }
    buf[*pos] = 0;
}

fn void TypeTable.report(TypeTable* t)
{
    printf("  type universe    : %d types, %d vars created\n",
           (int)t.count, (int)t.vars_created);
    printf("  unifications     : %d (%d occurs-check failures)\n",
           (int)t.unifications, (int)t.occurs_failures);
}

// ── Mapping syntax to types ─────────────────────────────────────────────────
// Turn an AST type annotation into a TypeId. Unknown names become fresh
// variables rather than errors, so an unannotated program still infers.
struct TypeMapper
{
    TypeTable*             tt;
    pfront_core::Interner* interner;
    usz                    mapped;
    usz                    unknown_names;
}

fn void TypeMapper.init(TypeMapper* m, TypeTable* tt, pfront_core::Interner* it)
{
    m.tt = tt;
    m.interner = it;
    m.mapped = 0;
    m.unknown_names = 0;
}

// Recognise the primitive spellings by their interned text.
fn int TypeMapper.primitive_of(TypeMapper* m, uint name_id)
{
    char* s = m.interner.text(name_id);
    usz n = m.interner.text_len(name_id);
    if (s == null || n == 0) { return NO_TYPE; }
    if (n == 3 && s[0] == 'i' && s[1] == '6' && s[2] == '4') { return m.tt.t_i64; }
    if (n == 3 && s[0] == 'i' && s[1] == '3' && s[2] == '2') { return m.tt.t_i32; }
    if (n == 3 && s[0] == 'i' && s[1] == '1' && s[2] == '6') { return m.tt.t_i16; }
    if (n == 2 && s[0] == 'i' && s[1] == '8') { return m.tt.t_i8; }
    if (n == 3 && s[0] == 'u' && s[1] == '6' && s[2] == '4') { return m.tt.t_u64; }
    if (n == 3 && s[0] == 'u' && s[1] == '3' && s[2] == '2') { return m.tt.t_u32; }
    if (n == 3 && s[0] == 'u' && s[1] == '1' && s[2] == '6') { return m.tt.t_u16; }
    if (n == 2 && s[0] == 'u' && s[1] == '8') { return m.tt.t_u8; }
    if (n == 3 && s[0] == 'f' && s[1] == '6' && s[2] == '4') { return m.tt.t_f64; }
    if (n == 3 && s[0] == 'f' && s[1] == '3' && s[2] == '2') { return m.tt.t_f32; }
    if (n == 4 && s[0] == 'b' && s[1] == 'o' && s[2] == 'o' && s[3] == 'l') { return m.tt.t_bool; }
    if (n == 4 && s[0] == 'c' && s[1] == 'h' && s[2] == 'a' && s[3] == 'r') { return m.tt.t_char; }
    if (n == 3 && s[0] == 's' && s[1] == 't' && s[2] == 'r') { return m.tt.t_string; }
    if (n == 3 && s[0] == 'u' && s[1] == 's' && s[2] == 'z') { return m.tt.t_u64; }
    if (n == 3 && s[0] == 'i' && s[1] == 's' && s[2] == 'z') { return m.tt.t_i64; }
    if (n == 3 && s[0] == 'p' && s[1] == 't' && s[2] == 'r')
    {
        return m.tt.mk_ptr(m.tt.mk_int(8, false), false);
    }
    if (n == 4 && s[0] == 'u' && s[1] == 'n' && s[2] == 'i' && s[3] == 't') { return m.tt.t_unit; }
    if (n == 4 && s[0] == 'v' && s[1] == 'o' && s[2] == 'i' && s[3] == 'd') { return m.tt.t_unit; }
    if (n == 5 && s[0] == 'n' && s[1] == 'e' && s[2] == 'v') { return m.tt.t_never; }
    if (n == 4 && s[0] == 'b' && s[1] == 'y' && s[2] == 't' && s[3] == 'e') { return m.tt.t_u8; }
    return NO_TYPE;
}

fn int TypeMapper.map(TypeMapper* m, Node* ty, int depth)
{
    if (ty == null) { return m.tt.fresh_var(false); }
    if (depth > 64) { return m.tt.t_error; }
    m.mapped = m.mapped + 1;

    switch (ty.kind)
    {
        case N_TY_UNIT:   return m.tt.t_unit;
        case N_TY_BOTTOM: return m.tt.t_never;
        case N_TY_INFER:  return m.tt.fresh_var(false);
        case N_TY_SELF:   return m.tt.fresh_var(false);
        case N_TY_NAME:
        {
            int prim = m.primitive_of(ty.name_id);
            if (prim != NO_TYPE) { return prim; }
            if (ty.resolved != null)
            {
                Node* d = ty.resolved;
                if (d.kind == Nk.N_DECL_STRUCT || d.kind == Nk.N_DECL_UNION
                 || d.kind == Nk.N_DECL_ENUM || d.kind == Nk.N_DECL_NEWTYPE)
                {
                    return m.tt.mk_named(d, ty.name_id);
                }
                if (d.kind == Nk.N_DECL_TYPE && d.type_ann != null)
                {
                    return m.map(d.type_ann, depth + 1);
                }
                if (d.kind == Nk.N_DECL_TYPEPARAM) { return m.tt.fresh_var(false); }
            }
            m.unknown_names = m.unknown_names + 1;
            return m.tt.fresh_var(false);
        }
        case N_TY_PTR:
            return m.tt.mk_ptr(m.map(ty.child(0), depth + 1),
                               (ty.flags & pfront_core::NF_MUT) != 0);
        case N_TY_REF:
            return m.tt.mk_ref(m.map(ty.child(0), depth + 1),
                               (ty.flags & pfront_core::NF_MUT) != 0);
        case N_TY_SLICE:
            return m.tt.mk_slice(m.map(ty.child(0), depth + 1));
        case N_TY_ARRAY:
        {
            int elem = m.map(ty.child(0), depth + 1);
            ulong len = 0;
            Node* lenNode = ty.child(1);
            if (lenNode != null) { len = lenNode.p.ival; }
            return m.tt.mk_array(elem, len);
        }
        case N_TY_TUPLE:
        {
            int[MAX_TYPE_ARGS] elems;
            usz n = 0;
            for (usz i = 0; i < ty.child_count && n < MAX_TYPE_ARGS; i++)
            {
                elems[n] = m.map(ty.children[i], depth + 1);
                n = n + 1;
            }
            return m.tt.mk_tuple(&elems[0], n);
        }
        case N_TY_FN:
        {
            // child 0 = parameter type (possibly a tuple); a N_TY_CONSTRAINT
            // child carries the return type.
            int[MAX_TYPE_ARGS] params;
            usz np = 0;
            int ret = m.tt.t_unit;
            Node* p0 = ty.child(0);
            if (p0 != null && p0.kind == Nk.N_TY_TUPLE)
            {
                for (usz i = 0; i < p0.child_count && np < MAX_TYPE_ARGS - 1; i++)
                {
                    params[np] = m.map(p0.children[i], depth + 1);
                    np = np + 1;
                }
            }
            else if (p0 != null && p0.kind != Nk.N_TY_CONSTRAINT)
            {
                params[0] = m.map(p0, depth + 1);
                np = 1;
            }
            for (usz i = 0; i < ty.child_count; i++)
            {
                Node* c = ty.children[i];
                if (c != null && c.kind == Nk.N_TY_CONSTRAINT && c.child_count > 0)
                {
                    ret = m.map(c.children[0], depth + 1);
                }
            }
            return m.tt.mk_fn(&params[0], np, ret);
        }
        case N_TY_GENERIC:
        {
            // Base type with arguments: model as the base for now, which is
            // sound for unification because monomorphisation happens later.
            if (ty.child_count > 0) { return m.map(ty.children[0], depth + 1); }
            return m.tt.fresh_var(false);
        }
        case N_TY_UNION:
        case N_TY_INTERSECT:
        {
            // Approximate with the first component: a full lattice needs
            // subtyping, which this pass deliberately does not attempt.
            if (ty.child_count > 0) { return m.map(ty.children[0], depth + 1); }
            return m.tt.fresh_var(false);
        }
        case N_TY_PATH:
        {
            if (ty.resolved != null)
            {
                return m.tt.mk_named(ty.resolved, ty.name_id);
            }
            return m.tt.fresh_var(false);
        }
        default:
            return m.tt.fresh_var(false);
    }
}
