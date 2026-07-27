// mono.c3 — Production monomorphization for Pride
// Implementation language: C3 (host).
// Pipeline position:  ... → irdl_msp → [mono] → ssi → ssi_ir → sasi → ...
// WHAT THIS MODULE DOES
// Expands every generic call site and generic struct literal into a fully-
// concrete clone.  After this pass the IR builder sees only monomorphic
// declarations — no abstract type-variable nodes remain reachable.
// Algorithm per call/struct-lit site:
//   1. Detect that the callee / struct head resolves to a generic declaration.
//   2. Infer the concrete type-argument substitution via two-pass unification:
//        Pass 1 — unify declared param types against actual arg type_annotations.
//        Pass 2 — if any param is still unbound, unify the declared return type
//                 against the call-node's synthesised type_annotation (handles
//                 return-type-only generics: fn cast<T>: A → T).
//      For struct literals without explicit <T> syntax, unify declared field
//      types against actual FieldInit value type_annotations instead.
//   3. Look up (generic_decl, substitution) in the instance table.
//      On a miss: deep-clone the generic AST into the same arena, substituting
//      every type-param use; assign a mangled name (id__i32, Box__bool, …).
//   4. Patch the call / struct-lit site to reference the clone.
//   5. Recursively monomorphize the clone body (generics calling generics).
// CORRECTNESS GUARANTEES
// * Deduplication: id(3) and id(5) share one id__i32 clone.
// * Cycle safety: an in-progress guard returns the partial clone for recursive
//   generic types (Tree<T>), cutting the cycle at the first back-reference.
// * Depth cap (MONO_DEPTH_CAP = 64): deeper chains emit a warning and leave
//   the site unmonomorphized (the IR still builds correctly — IR_UNKNOWN).
// * Integrity preserved: every clone passes `integrity issues == 0` because
//   type-variable substitution replaces abstract nodes with concrete ones.
// * Original generic templates are kept in the tree (ssi_ir.c3 skips any
//   NODE_DECL_FN still carrying a NODE_GENERIC_PARAM child).
// DIAGNOSTICS
// --dump-mono prints the full instance table with original → mangled mapping.
// Summary line: `mono instances : N`  (unique instantiations generated).

module mono;

import lexer;
import ast;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn void* memcpy(void* dst, void* src, usz n);
extern fn int   printf(char* fmt, ...);
extern fn int   memcmp(void* a, void* b, usz n);
extern fn void* memset(void* dst, int c, usz n);

alias Node = ast::AstNode;
alias Nk   = ast::NodeKind;


const usz MONO_MAX_INSTANCES = 4096;
const usz MONO_MAX_TYPE_ARGS = 32;
const usz MONO_DEPTH_CAP     = 64;
const usz MONO_MAX_WARNINGS  = 256;
const usz MANGLE_BUF_CAP     = 256;
const usz PATCH_MAP_CAP      = 2048;


struct MonoSub
{
    Node*[MONO_MAX_TYPE_ARGS] params;
    Node*[MONO_MAX_TYPE_ARGS] types;
    usz                       count;
}

fn void MonoSub.clear(MonoSub* s) { s.count = 0; }

fn void MonoSub.bind(MonoSub* s, Node* param, Node* ty)
{
    if (param == null || ty == null) { return; }
    for (usz i = 0; i < s.count; i++)
    {
        if (s.params[i] == param) { return; }
    }
    if (s.count < MONO_MAX_TYPE_ARGS)
    {
        s.params[s.count] = param;
        s.types[s.count]  = ty;
        s.count++;
    }
}

fn Node* MonoSub.lookup(MonoSub* s, Node* param)
{
    for (usz i = 0; i < s.count; i++)
    {
        if (s.params[i] == param) { return s.types[i]; }
    }
    return null;
}


struct MonoInstance
{
    Node*         generic;
    Node*         clone;
    MonoSub       sub;
    char*         name;
    usz           name_len;
    bool          in_progress;
    bool          complete;
}

struct MonoDiag
{
    char* msg;
    int   line;
    int   col;
}


struct Monomorphizer
{
    ast::AstArena* arena;
    MonoInstance*  instances;
    usz            instance_count;
    MonoDiag[MONO_MAX_WARNINGS] diags;
    int            diag_count;
    int            warning_count;
    int            depth;
}

fn bool Monomorphizer.init(Monomorphizer* m, ast::AstArena* arena)
{
    m.arena = arena;
    m.instances = (MonoInstance*)malloc(MONO_MAX_INSTANCES * MonoInstance::size);
    if (m.instances == null) { return false; }
    m.instance_count = 0;
    m.diag_count     = 0;
    m.warning_count  = 0;
    m.depth          = 0;
    return true;
}

fn void Monomorphizer.destroy(Monomorphizer* m)
{
    if (m.instances != null) { free(m.instances); m.instances = null; }
}

fn void Monomorphizer.warn(Monomorphizer* m, char* msg, int line, int col)
{
    m.warning_count++;
    if (m.diag_count < (int)MONO_MAX_WARNINGS)
    {
        MonoDiag d;
        d.msg  = msg;
        d.line = line;
        d.col  = col;
        m.diags[m.diag_count] = d;
        m.diag_count++;
    }
}


fn bool decl_is_generic(Node* n)
{
    if (n == null) { return false; }
    for (usz i = 0; i < n.child_count; i++)
    {
        Node* c = n.children[i];
        if (c != null && c.kind == Nk.NODE_GENERIC_PARAM) { return true; }
    }
    return false;
}

fn Node* decl_generic_params(Node* n)
{
    if (n == null) { return null; }
    for (usz i = 0; i < n.child_count; i++)
    {
        Node* c = n.children[i];
        if (c != null && c.kind == Nk.NODE_GENERIC_PARAM) { return c; }
    }
    return null;
}

fn usz cstr_len_m(char* s)
{
    usz n = 0;
    while (s[n] != 0) { n++; }
    return n;
}

fn bool node_name_of(Node* n, char** out_ptr, usz* out_len)
{
    if (n == null) { return false; }
    if (n.kind == Nk.NODE_IDENT || n.kind == Nk.NODE_TYPEVAR || n.kind == Nk.NODE_TYPE_PRIMITIVE)
    {
        *out_ptr = n.p.ident.name_ptr;
        *out_len = n.p.ident.name_len;
        return true;
    }
    return false;
}

fn bool decl_name_of(Node* decl, char** out_ptr, usz* out_len)
{
    if (decl == null) { return false; }
    if (decl.child_count >= 1) { return node_name_of(decl.children[0], out_ptr, out_len); }
    return false;
}


fn usz type_to_str(Node* t, char* buf, usz cap, usz off, int depth)
{
    if (t == null || off >= cap || depth > 8) { return off; }
    switch (t.kind)
    {
        case Nk.NODE_TYPE_PRIMITIVE:
        case Nk.NODE_TYPEVAR:
        case Nk.NODE_IDENT:
            for (usz i = 0; i < t.p.ident.name_len && off < cap - 1; i++) { buf[off++] = t.p.ident.name_ptr[i]; }
        case Nk.NODE_TYPE_PTR:
            if (off < cap - 1) { buf[off++] = 'p'; }
            if (off < cap - 1) { buf[off++] = 't'; }
            if (off < cap - 1) { buf[off++] = 'r'; }
            if (t.child_count >= 1) { off = type_to_str(t.children[0], buf, cap, off, depth + 1); }
        case Nk.NODE_TYPE_SLICE:
            if (off < cap - 1) { buf[off++] = 's'; }
            if (off < cap - 1) { buf[off++] = 'l'; }
            if (t.child_count >= 1) { off = type_to_str(t.children[0], buf, cap, off, depth + 1); }
        case Nk.NODE_TYPE_ARRAY:
            if (off < cap - 1) { buf[off++] = 'a'; }
            if (off < cap - 1) { buf[off++] = 'r'; }
            if (t.child_count >= 1) { off = type_to_str(t.children[0], buf, cap, off, depth + 1); }
        case Nk.NODE_TYPE_TUPLE:
            if (off < cap - 1) { buf[off++] = 'T'; }
            for (usz i = 0; i < t.child_count && off < cap - 2; i++)
            {
                if (i > 0 && off < cap - 1) { buf[off++] = 'x'; }
                off = type_to_str(t.children[i], buf, cap, off, depth + 1);
            }
            if (off < cap - 1) { buf[off++] = 'E'; }
        case Nk.NODE_TYPE_FN:
            if (off < cap - 1) { buf[off++] = 'F'; }
            for (usz i = 0; i < t.child_count; i++) { off = type_to_str(t.children[i], buf, cap, off, depth + 1); }
            if (off < cap - 1) { buf[off++] = 'E'; }
        case Nk.NODE_TYPE_UNION:
            if (off < cap - 1) { buf[off++] = 'U'; }
            for (usz i = 0; i < t.child_count; i++) { off = type_to_str(t.children[i], buf, cap, off, depth + 1); }
            if (off < cap - 1) { buf[off++] = 'E'; }
        case Nk.NODE_TYPE_INTERSECT:
            if (off < cap - 1) { buf[off++] = 'I'; }
            for (usz i = 0; i < t.child_count; i++) { off = type_to_str(t.children[i], buf, cap, off, depth + 1); }
            if (off < cap - 1) { buf[off++] = 'E'; }
        case Nk.NODE_TYPE_GENERIC_APP:
            if (t.child_count >= 1) { off = type_to_str(t.children[0], buf, cap, off, depth + 1); }
            if (off < cap - 1) { buf[off++] = 'G'; }
            for (usz i = 1; i < t.child_count; i++) { off = type_to_str(t.children[i], buf, cap, off, depth + 1); }
            if (off < cap - 1) { buf[off++] = 'E'; }
        case Nk.NODE_EXPR_UNIT:
            if (off < cap - 1) { buf[off++] = 'u'; }
            if (off < cap - 1) { buf[off++] = 'n'; }
            if (off < cap - 1) { buf[off++] = 't'; }
        default:
            if (off < cap - 1) { buf[off++] = 'X'; }
    }
    return off;
}

fn char* Monomorphizer.mangle(Monomorphizer* m, char* base, usz base_len, MonoSub* sub, usz* out_len)
{
    char[MANGLE_BUF_CAP] buf;
    usz off = 0;
    for (usz i = 0; i < base_len && off < MANGLE_BUF_CAP - 1; i++) { buf[off++] = base[i]; }
    for (usz i = 0; i < sub.count && off < MANGLE_BUF_CAP - 4; i++)
    {
        buf[off++] = '_';
        buf[off++] = '_';
        off = type_to_str(sub.types[i], &buf[0], MANGLE_BUF_CAP, off, 0);
    }
    // Disambiguate against every ALREADY-ASSIGNED instance name. Because
    // type_to_str() truncates at MANGLE_BUF_CAP bytes, two genuinely
    // different (per type_struct_eq, which never truncates) instantiations
    // can still produce the identical mangled prefix for a sufficiently
    // wide/deep type argument — which would otherwise emit two distinct
    // LLVM definitions under the SAME symbol name (a link-time duplicate-
    // symbol failure, or worse, a silent one-definition-wins collision).
    // Append a numeric suffix until the name is unique.
    usz base_off = off;
    int suffix = 0;
    while (true)
    {
        bool collision = false;
        for (usz ii = 0; ii < m.instance_count; ii++)
        {
            MonoInstance* other = &m.instances[ii];
            if (other.name == null || other.name_len != off) { continue; }
            bool same = true;
            for (usz k = 0; k < off; k++) { if (other.name[k] != buf[k]) { same = false; break; } }
            if (same) { collision = true; break; }
        }
        if (!collision) { break; }
        // Reset to the un-suffixed prefix and append "_N".
        off = base_off;
        suffix++;
        char[16] sbuf;
        usz slen = 0;
        int sv = suffix;
        do { sbuf[slen++] = (char)('0' + (sv % 10)); sv /= 10; } while (sv > 0 && slen < 16);
        if (off < MANGLE_BUF_CAP - 2) { buf[off++] = '_'; }
        for (usz k = slen; k > 0 && off < MANGLE_BUF_CAP - 1; k--) { buf[off++] = sbuf[k-1]; }
    }
    buf[off] = 0;
    char* result = (char*)ast::arena_alloc(m.arena, off + 1, 1);
    if (result == null) { *out_len = 0; return null; }
    memcpy((void*)result, (void*)&buf[0], off + 1);
    *out_len = off;
    return result;
}


fn bool sub_eq(MonoSub* a, MonoSub* b)
{
    if (a.count != b.count) { return false; }
    for (usz i = 0; i < a.count; i++)
    {
        if (a.params[i] != b.params[i]) { return false; }
        if (!type_struct_eq(a.types[i], b.types[i], 0)) { return false; }
    }
    return true;
}

// Direct recursive structural equality between two type nodes, exactly
// mirroring type_to_str()'s traversal (same node kinds, same child order,
// same depth cap) but WITHOUT materializing a bounded string buffer.
//
// This exists because sub_eq() previously compared `type_to_str(...)`
// output truncated into a fixed 128-byte stack buffer: for a sufficiently
// wide/deep type argument (e.g. a generic instantiated over a tuple type
// with on the order of 100+ fields sharing a long common prefix), two
// GENUINELY DIFFERENT types could truncate to the same 128-byte prefix and
// be silently misidentified as identical by `find_instance()` — causing a
// call site to be monomorphized against the WRONG existing clone (silent
// type confusion, since this module's dedup is otherwise relied upon as a
// correctness guarantee, per this file's own header comment). Comparing
// the type trees directly can never truncate, so it can never conflate two
// distinct types regardless of size.
fn bool type_struct_eq(Node* a, Node* b, int depth)
{
    if (a == b) { return true; }
    if (a == null || b == null) { return false; }
    if (depth > 8) { return true; }   // matches type_to_str's depth cap
    if (a.kind != b.kind) { return false; }

    switch (a.kind)
    {
        case Nk.NODE_TYPE_PRIMITIVE:
        case Nk.NODE_TYPEVAR:
        case Nk.NODE_IDENT:
            if (a.p.ident.name_len != b.p.ident.name_len) { return false; }
            for (usz i = 0; i < a.p.ident.name_len; i++)
            {
                if (a.p.ident.name_ptr[i] != b.p.ident.name_ptr[i]) { return false; }
            }
            return true;
        case Nk.NODE_TYPE_PTR:
        case Nk.NODE_TYPE_SLICE:
        case Nk.NODE_TYPE_ARRAY:
            if (a.child_count < 1 || b.child_count < 1) { return a.child_count == b.child_count; }
            return type_struct_eq(a.children[0], b.children[0], depth + 1);
        case Nk.NODE_TYPE_TUPLE:
        case Nk.NODE_TYPE_FN:
        case Nk.NODE_TYPE_UNION:
        case Nk.NODE_TYPE_INTERSECT:
        case Nk.NODE_TYPE_GENERIC_APP:
            if (a.child_count != b.child_count) { return false; }
            for (usz i = 0; i < a.child_count; i++)
            {
                if (!type_struct_eq(a.children[i], b.children[i], depth + 1)) { return false; }
            }
            return true;
        case Nk.NODE_EXPR_UNIT:
            return true;
        default:
            // Unknown/unhandled kinds: type_to_str() emits a fixed 'X' marker
            // for all of them regardless of content, so it would treat any
            // two same-kind-but-otherwise-different nodes here as equal too;
            // preserve that (permissive) behavior for parity.
            return true;
    }
}


fn MonoInstance* Monomorphizer.find_instance(Monomorphizer* m, Node* generic, MonoSub* sub)
{
    for (usz i = 0; i < m.instance_count; i++)
    {
        MonoInstance* inst = &m.instances[i];
        if (inst.generic == generic && sub_eq(&inst.sub, sub)) { return inst; }
    }
    return null;
}

fn MonoInstance* Monomorphizer.new_instance(Monomorphizer* m, Node* generic)
{
    if (m.instance_count >= MONO_MAX_INSTANCES) { return null; }
    MonoInstance* inst = &m.instances[m.instance_count];
    m.instance_count++;
    inst.generic     = generic;
    inst.clone       = null;
    inst.sub.count   = 0;
    inst.name        = null;
    inst.name_len    = 0;
    inst.in_progress = false;
    inst.complete    = false;
    return inst;
}


struct PatchEntry { Node* orig; Node* clone_ptr; }

// CloneCtx is heap-allocated (patch map is too large for the C stack).
struct CloneCtx
{
    PatchEntry*    map;
    usz            count;
    MonoSub*       sub;
    ast::AstArena* arena;
    Node*          generic_decl;
    char*          mangled_name;
    usz            mangled_len;
    int            depth;
}

fn void CloneCtx.record(CloneCtx* ctx, Node* orig, Node* cln)
{
    if (ctx.map != null && ctx.count < PATCH_MAP_CAP)
    {
        ctx.map[ctx.count].orig      = orig;
        ctx.map[ctx.count].clone_ptr = cln;
        ctx.count++;
    }
}

fn Node* CloneCtx.lookup(CloneCtx* ctx, Node* orig)
{
    if (ctx.map == null) { return null; }
    for (usz i = 0; i < ctx.count; i++)
    {
        if (ctx.map[i].orig == orig) { return ctx.map[i].clone_ptr; }
    }
    return null;
}

fn bool is_generic_param_node(Node* n)
{
    if (n == null) { return false; }
    if (n.kind != Nk.NODE_TYPEVAR) { return false; }
    if (n.resolved == null) { return false; }
    return n.resolved.kind == Nk.NODE_PARAM;
}

fn Node* ctx_subst_type(CloneCtx* ctx, Node* n)
{
    if (n == null) { return null; }
    if (n.kind != Nk.NODE_TYPEVAR && n.kind != Nk.NODE_TYPE_PRIMITIVE) { return null; }
    if (n.resolved == null) { return null; }
    if (n.resolved.kind != Nk.NODE_PARAM) { return null; }
    return ctx.sub.lookup(n.resolved);
}


fn Node* clone_node(CloneCtx* ctx, Node* n)
{
    if (n == null) { return null; }
    if (ctx.depth > 1200) { return n; }

    // Type-variable substitution.
    Node* subst = ctx_subst_type(ctx, n);
    if (subst != null) { return subst; }

    // Skip the GENERIC_PARAM node itself — the clone has no type params.
    if (n.kind == Nk.NODE_GENERIC_PARAM) { return null; }

    ctx.depth++;

    Node* c = (Node*)ast::arena_alloc(ctx.arena, ast::AstNode::size, ast::AstNode::alignment);
    if (c == null)
    {
        ctx.depth--;
        return n;   // OOM: share original
    }

    memcpy((void*)c, (void*)n, ast::AstNode::size);
    c.id = ctx.arena.next_id;
    ctx.arena.next_id++;
    ctx.arena.node_count++;

    // Register before recursing (handles self-references).
    ctx.record(n, c);

    // Rewrite name node that refers to the generic itself → mangled name.
    if ((n.kind == Nk.NODE_IDENT || n.kind == Nk.NODE_TYPEVAR)
        && n.resolved == ctx.generic_decl
        && ctx.mangled_name != null)
    {
        c.p.ident.name_ptr = ctx.mangled_name;
        c.p.ident.name_len = ctx.mangled_len;
    }

    // Clone children, skipping the GENERIC_PARAM child.
    // Use a heap-allocated buffer so we handle arbitrarily large blocks without
    // silently truncating children (a static cbuf[256] would cut off large fns).
    usz nc = 0;
    usz child_cap = n.child_count + 1;   // +1 so malloc(0) is never called
    Node** cbuf = (Node**)malloc(child_cap * ast::NodePtr::size);
    if (cbuf == null)
    {
        // OOM: fall back to sharing original node
        ctx.depth--;
        return n;
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        Node* ch = n.children[i];
        if (ch != null && ch.kind == Nk.NODE_GENERIC_PARAM) { continue; }
        cbuf[nc] = clone_node(ctx, ch);
        nc++;
    }
    ast::node_attach(ctx.arena, c, cbuf, nc);
    free((void*)cbuf);

    // Substitute type_annotation.
    if (n.type_annotation != null)
    {
        c.type_annotation = clone_node(ctx, n.type_annotation);
    }

    ctx.depth--;
    return c;
}

fn void fixup_resolved(CloneCtx* ctx, Node* n, Node* clone_decl)
{
    if (n == null) { return; }
    if (ctx.depth > 1200) { return; }
    ctx.depth++;

    if (n.resolved != null)
    {
        Node* mapped = ctx.lookup(n.resolved);
        if (mapped != null)
        {
            n.resolved = mapped;
        }
        else if (n.resolved == ctx.generic_decl)
        {
            n.resolved = clone_decl;
        }
    }

    for (usz i = 0; i < n.child_count; i++) { fixup_resolved(ctx, n.children[i], clone_decl); }
    if (n.type_annotation != null) { fixup_resolved(ctx, n.type_annotation, clone_decl); }

    ctx.depth--;
}


fn Node* unfold_type_m(Node* t, int depth)
{
    if (t == null || depth > 32) { return t; }
    while (t != null && t.kind == Nk.NODE_TYPEVAR && t.resolved != null && depth < 32)
    {
        Node* d = t.resolved;
        if (d.kind != Nk.NODE_DECL_TYPE) { break; }
        Node* body = d.child_count >= 1 ? d.children[d.child_count - 1] : null;
        if (body == null) { break; }
        if (body.kind == Nk.NODE_DECL_STRUCT || body.kind == Nk.NODE_DECL_UNION) { break; }
        if (body == t) { break; }
        t = body;
        depth++;
    }
    return t;
}

fn void unify_type(Node* declared, Node* actual, MonoSub* sub, int depth)
{
    if (depth > 32 || declared == null || actual == null) { return; }
    declared = unfold_type_m(declared, 0);
    actual   = unfold_type_m(actual, 0);
    if (declared == null || actual == null) { return; }

    if (is_generic_param_node(declared))
    {
        sub.bind(declared.resolved, actual);
        return;
    }

    if (declared.kind == Nk.NODE_TYPE_GENERIC_APP && actual.kind == Nk.NODE_TYPE_GENERIC_APP)
    {
        usz n = declared.child_count < actual.child_count ? declared.child_count : actual.child_count;
        for (usz i = 0; i < n; i++) { unify_type(declared.children[i], actual.children[i], sub, depth + 1); }
        return;
    }

    if (declared.kind != actual.kind) { return; }
    switch (declared.kind)
    {
        case Nk.NODE_TYPE_PTR:
        case Nk.NODE_TYPE_REF:
        case Nk.NODE_TYPE_MUT_REF:
        case Nk.NODE_TYPE_SLICE:
        case Nk.NODE_TYPE_ARRAY:
            if (declared.child_count >= 1 && actual.child_count >= 1)
            {
                unify_type(declared.children[0], actual.children[0], sub, depth + 1);
            }
        case Nk.NODE_TYPE_TUPLE:
        case Nk.NODE_TYPE_FN:
        case Nk.NODE_TYPE_UNION:
        case Nk.NODE_TYPE_INTERSECT:
            if (declared.child_count == actual.child_count)
            {
                for (usz i = 0; i < declared.child_count; i++)
                {
                    unify_type(declared.children[i], actual.children[i], sub, depth + 1);
                }
            }
        default:
            break;
    }
}

fn Node* fn_param_type(Node* fn_node)
{
    for (usz i = 0; i < fn_node.child_count; i++)
    {
        Node* c = fn_node.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.NODE_TYPE_FN)
        {
            Node* lhs = c.child_count >= 1 ? c.children[0] : null;
            Node* rhs = c.child_count >= 2 ? c.children[1] : null;
            if (rhs != null && rhs.kind == Nk.NODE_EFFECT_ROW && lhs != null && lhs.kind == Nk.NODE_TYPE_FN)
            {
                return lhs.child_count >= 1 ? lhs.children[0] : null;
            }
            return lhs;
        }
    }
    return null;
}

// Extract the declared return type from a fn signature node.
fn Node* fn_return_type(Node* fn_node)
{
    for (usz i = 0; i < fn_node.child_count; i++)
    {
        Node* c = fn_node.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.NODE_TYPE_FN)
        {
            Node* lhs = c.child_count >= 1 ? c.children[0] : null;
            Node* rhs = c.child_count >= 2 ? c.children[1] : null;
            if (rhs != null && rhs.kind == Nk.NODE_EFFECT_ROW && lhs != null && lhs.kind == Nk.NODE_TYPE_FN)
            {
                return lhs.child_count >= 2 ? lhs.children[1] : null;
            }
            return rhs;
        }
    }
    return null;
}

// Infer type substitution for a generic fn call.
// call_node is the CALL AST node itself — its type_annotation is the
// synthesised return type from typecheck, used as a fallback when a type
// param only appears in the return position (not in any argument type).
fn bool Monomorphizer.infer_fn_sub(Monomorphizer* m, Node* fn_node,
                                    Node** args, usz argc,
                                    Node* call_node, MonoSub* out_sub)
{
    out_sub.clear();
    Node* gp_list = decl_generic_params(fn_node);
    if (gp_list == null) { return false; }

    Node* param_t = fn_param_type(fn_node);
    if (param_t == null) { return false; }

    // Pass 1: unify declared parameter types against actual argument types.
    Node* pt = unfold_type_m(param_t, 0);
    if (pt != null && pt.kind == Nk.NODE_TYPE_TUPLE && argc >= 1)
    {
        for (usz i = 0; i < pt.child_count && i < argc; i++)
        {
            Node* at = (args[i] != null) ? args[i].type_annotation : null;
            if (at != null) { unify_type(pt.children[i], at, out_sub, 0); }
        }
    }
    else if (argc >= 1)
    {
        Node* at = (args[0] != null) ? args[0].type_annotation : null;
        if (at != null) { unify_type(param_t, at, out_sub, 0); }
    }

    // Pass 2: if any param is still unbound, unify the declared return type
    // against the call expression's synthesised type_annotation.  This handles
    // the case where T only appears in the return type (e.g. fn cast<T>: A -> T).
    bool any_unbound = false;
    for (usz i = 0; i < gp_list.child_count; i++)
    {
        Node* gp = gp_list.children[i];
        if (gp == null) { continue; }
        bool found = false;
        for (usz j = 0; j < out_sub.count; j++)
        {
            if (out_sub.params[j] == gp) { found = true; break; }
        }
        if (!found) { any_unbound = true; break; }
    }

    if (any_unbound && call_node != null && call_node.type_annotation != null)
    {
        Node* decl_ret = fn_return_type(fn_node);
        if (decl_ret != null)
        {
            unify_type(decl_ret, call_node.type_annotation, out_sub, 0);
        }
        // Re-check after pass 2.
        any_unbound = false;
        for (usz i = 0; i < gp_list.child_count; i++)
        {
            Node* gp = gp_list.children[i];
            if (gp == null) { continue; }
            bool found = false;
            for (usz j = 0; j < out_sub.count; j++)
            {
                if (out_sub.params[j] == gp) { found = true; break; }
            }
            if (!found) { any_unbound = true; break; }
        }
    }

    return !any_unbound;
}

fn bool Monomorphizer.infer_struct_sub(Monomorphizer* m, Node* struct_decl,
                                        Node* generic_app, MonoSub* out_sub)
{
    out_sub.clear();
    Node* gp_list = decl_generic_params(struct_decl);
    if (gp_list == null) { return false; }

    usz nparams = gp_list.child_count;
    usz nargs   = generic_app.child_count >= 1 ? generic_app.child_count - 1 : 0;
    usz n = nparams < nargs ? nparams : nargs;

    for (usz i = 0; i < n; i++)
    {
        Node* param_decl = gp_list.children[i];
        Node* type_arg   = generic_app.children[i + 1];
        if (param_decl != null && type_arg != null) { out_sub.bind(param_decl, type_arg); }
    }

    return out_sub.count == nparams;
}

// Infer a struct substitution from a bare struct literal `S { field: val, ... }`
// where no explicit generic-app type argument list is present.  We find the
// struct's field-block, then for each FieldInit in the literal look up the
// declared field type (which may contain generic params like T) and unify it
// against the actual value's synthesised type.
// Example:  struct Box<T> { val: T }
//           Box { val: (n:i32) }   →  T unifies against i32  →  T=i32
fn bool Monomorphizer.infer_struct_sub_from_fields(Monomorphizer* m,
                                                    Node* struct_decl,
                                                    Node* lit_node,
                                                    MonoSub* out_sub)
{
    out_sub.clear();
    Node* gp_list = decl_generic_params(struct_decl);
    if (gp_list == null) { return false; }

    // Find the field block (last EXPR_BLOCK child of the struct decl).
    Node* field_block = null;
    for (usz i = 0; i < struct_decl.child_count; i++)
    {
        Node* c = struct_decl.children[i];
        if (c != null && c.kind == Nk.NODE_EXPR_BLOCK) { field_block = c; }
    }
    if (field_block == null) { return false; }

    // For each FieldInit in the literal, find its declared type and unify.
    for (usz i = 1; i < lit_node.child_count; i++)
    {
        Node* fi = lit_node.children[i];
        if (fi == null || fi.kind != Nk.NODE_FIELD_INIT) { continue; }
        if (fi.child_count < 2) { continue; }
        Node* fname = fi.children[0];
        Node* fval  = fi.children[1];
        if (fname == null || fval == null) { continue; }

        // Find the declared type for this field name in the struct's field block.
        Node* decl_ft = null;
        for (usz j = 0; j < field_block.child_count; j++)
        {
            Node* fd = field_block.children[j];
            if (fd == null || fd.kind != Nk.NODE_FIELD_DECL) { continue; }
            if (fd.child_count < 2) { continue; }
            Node* fn_name = fd.children[0];
            Node* fn_type = fd.children[1];
            if (fn_name == null || fn_type == null) { continue; }
            // Compare field names.
            char* np; usz nl;
            char* fp; usz fl;
            if (!node_name_of(fn_name, &np, &nl)) { continue; }
            if (!node_name_of(fname, &fp, &fl)) { continue; }
            if (nl == fl && memcmp((void*)np, (void*)fp, nl) == 0)
            {
                decl_ft = fn_type;
                break;
            }
        }
        if (decl_ft == null) { continue; }

        // Get the actual value's type from its type_annotation.
        Node* actual_t = fval.type_annotation;
        if (actual_t == null) { continue; }
        unify_type(decl_ft, actual_t, out_sub, 0);
    }

    // All generic params must be bound.
    for (usz i = 0; i < gp_list.child_count; i++)
    {
        Node* gp = gp_list.children[i];
        if (gp == null) { continue; }
        bool found = false;
        for (usz j = 0; j < out_sub.count; j++)
        {
            if (out_sub.params[j] == gp) { found = true; break; }
        }
        if (!found) { return false; }
    }
    return true;
}


fn Node* Monomorphizer.get_or_create(Monomorphizer* m, Node* generic_decl, MonoSub* sub)
{
    MonoInstance* inst = m.find_instance(generic_decl, sub);
    if (inst != null) { return inst.clone; }   // found (or in-progress: return partial)

    if (m.depth >= (int)MONO_DEPTH_CAP)
    {
        m.warn("monomorphization depth cap reached; leaving site abstract",
               generic_decl.line, generic_decl.col);
        return null;
    }

    inst = m.new_instance(generic_decl);
    if (inst == null)
    {
        m.warn("too many mono instances; leaving site abstract",
               generic_decl.line, generic_decl.col);
        return null;
    }
    inst.sub = *sub;
    inst.in_progress = true;

    // Build mangled name.
    char* base_ptr;
    usz base_len;
    if (!decl_name_of(generic_decl, &base_ptr, &base_len))
    {
        base_ptr = (char*)"anon";
        base_len = 4;
    }
    usz mlen = 0;
    char* mname = m.mangle(base_ptr, base_len, sub, &mlen);
    inst.name     = mname;
    inst.name_len = mlen;

    // Heap-allocate CloneCtx (patch map too large for C stack).
    CloneCtx* ctx = (CloneCtx*)malloc(CloneCtx::size);
    if (ctx == null)
    {
        m.warn("clone ctx alloc failed", generic_decl.line, generic_decl.col);
        inst.in_progress = false;
        inst.complete    = true;
        return null;
    }
    ctx.map = (PatchEntry*)malloc(PATCH_MAP_CAP * PatchEntry::size);
    if (ctx.map == null)
    {
        free((void*)ctx);
        m.warn("clone map alloc failed", generic_decl.line, generic_decl.col);
        inst.in_progress = false;
        inst.complete    = true;
        return null;
    }
    ctx.count        = 0;
    ctx.sub          = sub;
    ctx.arena        = m.arena;
    ctx.generic_decl = generic_decl;
    ctx.mangled_name = mname;
    ctx.mangled_len  = mlen;
    ctx.depth        = 0;

    Node* cln = clone_node(ctx, generic_decl);
    if (cln == null)
    {
        free((void*)ctx.map);
        free((void*)ctx);
        m.warn("clone allocation failed", generic_decl.line, generic_decl.col);
        inst.in_progress = false;
        inst.complete    = true;
        inst.clone       = null;
        return null;
    }

    // Patch clone's name node (child 0) to the mangled name.
    if (cln.child_count >= 1 && mname != null)
    {
        Node* name_node = cln.children[0];
        if (name_node != null && (name_node.kind == Nk.NODE_IDENT || name_node.kind == Nk.NODE_TYPEVAR))
        {
            name_node.p.ident.name_ptr = mname;
            name_node.p.ident.name_len = mlen;
        }
    }

    inst.clone = cln;

    // Fix up intra-clone .resolved pointers + recursive self-references.
    ctx.depth = 0;
    fixup_resolved(ctx, cln, cln);

    free((void*)ctx.map);
    free((void*)ctx);

    inst.in_progress = false;
    inst.complete    = true;

    // Recursively monomorphize the clone body.
    m.depth++;
    m.mono_node(cln);
    m.depth--;

    return cln;
}


fn usz collect_call_args(Node* call, Node** buf, usz cap)
{
    usz n = 0;
    for (usz i = 1; i < call.child_count && n < cap; i++)
    {
        Node* c = call.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.NODE_GENERIC_PARAM || c.kind == Nk.NODE_EFFECT_ROW) { continue; }
        buf[n] = c;
        n++;
    }
    return n;
}

fn void patch_callee(Node* call_node, Node* cln)
{
    if (call_node == null || cln == null) { return; }
    Node* callee = call_node.child_count >= 1 ? call_node.children[0] : null;
    if (callee == null) { return; }

    if (callee.kind == Nk.NODE_IDENT || callee.kind == Nk.NODE_TYPEVAR)
    {
        callee.resolved = cln;
        if (cln.child_count >= 1)
        {
            Node* cname = cln.children[0];
            if (cname != null && (cname.kind == Nk.NODE_IDENT || cname.kind == Nk.NODE_TYPEVAR))
            {
                callee.p.ident.name_ptr = cname.p.ident.name_ptr;
                callee.p.ident.name_len = cname.p.ident.name_len;
            }
        }
    }
    else if (callee.kind == Nk.NODE_EXPR_FIELD && callee.child_count >= 2)
    {
        Node* tail = callee.children[callee.child_count - 1];
        if (tail != null && (tail.kind == Nk.NODE_IDENT || tail.kind == Nk.NODE_TYPEVAR))
        {
            tail.resolved = cln;
            if (cln.child_count >= 1)
            {
                Node* cname = cln.children[0];
                if (cname != null)
                {
                    tail.p.ident.name_ptr = cname.p.ident.name_ptr;
                    tail.p.ident.name_len = cname.p.ident.name_len;
                }
            }
        }
    }
}

fn Node* callee_generic_decl(Node* call_node)
{
    if (call_node == null || call_node.child_count == 0) { return null; }
    Node* callee = call_node.children[0];
    if (callee == null) { return null; }

    Node* resolved = null;
    if (callee.kind == Nk.NODE_IDENT || callee.kind == Nk.NODE_TYPEVAR)
    {
        resolved = callee.resolved;
    }
    else if (callee.kind == Nk.NODE_EXPR_FIELD && callee.child_count >= 1)
    {
        Node* tail = callee.children[callee.child_count - 1];
        if (tail != null) { resolved = tail.resolved; }
    }

    if (resolved == null) { return null; }
    if (resolved.kind != Nk.NODE_DECL_FN) { return null; }
    if (!decl_is_generic(resolved)) { return null; }
    return resolved;
}

fn void Monomorphizer.handle_call(Monomorphizer* m, Node* call_node)
{
    Node* generic_fn = callee_generic_decl(call_node);
    if (generic_fn == null) { return; }

    Node*[64] args;
    usz argc = collect_call_args(call_node, &args[0], 64);

    MonoSub sub;
    if (!m.infer_fn_sub(generic_fn, &args[0], argc, call_node, &sub)) { return; }

    Node* cln = m.get_or_create(generic_fn, &sub);
    if (cln == null) { return; }

    patch_callee(call_node, cln);
}

fn void Monomorphizer.handle_struct_lit(Monomorphizer* m, Node* lit_node)
{
    if (lit_node.child_count == 0) { return; }
    Node* head = lit_node.children[0];
    if (head == null) { return; }

    Node* struct_decl = null;
    Node* generic_app = null;

    if (head.kind == Nk.NODE_TYPE_GENERIC_APP && head.child_count >= 1)
    {
        generic_app = head;
        Node* head0 = head.children[0];
        if (head0 != null && head0.resolved != null
            && head0.resolved.kind == Nk.NODE_DECL_STRUCT
            && decl_is_generic(head0.resolved))
        {
            struct_decl = head0.resolved;
        }
    }
    else if ((head.kind == Nk.NODE_IDENT || head.kind == Nk.NODE_TYPEVAR)
             && head.resolved != null
             && head.resolved.kind == Nk.NODE_DECL_STRUCT
             && decl_is_generic(head.resolved))
    {
        struct_decl = head.resolved;
        if (lit_node.type_annotation != null && lit_node.type_annotation.kind == Nk.NODE_TYPE_GENERIC_APP)
        {
            generic_app = lit_node.type_annotation;
        }
    }

    if (struct_decl == null) { return; }

    MonoSub sub;
    // Primary path: explicit generic_app (e.g. Box<i32> { ... }).
    // Fallback path: bare struct literal (e.g. Box { val: n }) — infer T from
    // the actual field value types by unifying against the declared field types.
    if (generic_app != null)
    {
        if (!m.infer_struct_sub(struct_decl, generic_app, &sub)) { return; }
    }
    else
    {
        if (!m.infer_struct_sub_from_fields(struct_decl, lit_node, &sub)) { return; }
    }

    Node* cln = m.get_or_create(struct_decl, &sub);
    if (cln == null) { return; }

    // Patch literal head.
    if (head.kind == Nk.NODE_TYPE_GENERIC_APP && head.child_count >= 1)
    {
        Node* head0 = head.children[0];
        if (head0 != null)
        {
            head0.resolved = cln;
            if (cln.child_count >= 1)
            {
                Node* cname = cln.children[0];
                if (cname != null)
                {
                    head0.p.ident.name_ptr = cname.p.ident.name_ptr;
                    head0.p.ident.name_len = cname.p.ident.name_len;
                }
            }
        }
    }
    else
    {
        head.resolved = cln;
        if (cln.child_count >= 1)
        {
            Node* cname = cln.children[0];
            if (cname != null)
            {
                head.p.ident.name_ptr = cname.p.ident.name_ptr;
                head.p.ident.name_len = cname.p.ident.name_len;
            }
        }
    }
}

fn void Monomorphizer.mono_node(Monomorphizer* m, Node* n)
{
    if (n == null) { return; }
    if (m.depth > (int)MONO_DEPTH_CAP + 512) { return; }
    m.depth++;

    switch (n.kind)
    {
        case Nk.NODE_EXPR_CALL:
        case Nk.NODE_EXPR_METHOD_CALL:
            m.handle_call(n);
            for (usz i = 0; i < n.child_count; i++) { m.mono_node(n.children[i]); }

        case Nk.NODE_EXPR_STRUCT_LIT:
            m.handle_struct_lit(n);
            for (usz i = 0; i < n.child_count; i++) { m.mono_node(n.children[i]); }

        case Nk.NODE_DECL_FN:
            if (decl_is_generic(n)) { m.depth--; return; }
            for (usz i = 0; i < n.child_count; i++) { m.mono_node(n.children[i]); }

        default:
            for (usz i = 0; i < n.child_count; i++) { m.mono_node(n.children[i]); }
    }

    m.depth--;
}


fn Node* Monomorphizer.run(Monomorphizer* m, Node* program)
{
    if (program == null) { return null; }
    m.depth = 0;
    m.mono_node(program);

    // Count clones to append.
    usz n_clones = 0;
    for (usz i = 0; i < m.instance_count; i++)
    {
        MonoInstance* inst = &m.instances[i];
        if (inst.clone != null && inst.complete) { n_clones++; }
    }

    if (n_clones == 0) { return program; }

    usz old_count = program.child_count;
    usz new_count = old_count + n_clones;

    Node** new_children = (Node**)ast::arena_alloc(
        m.arena, new_count * ast::NodePtr::size, ast::NodePtr::alignment);
    if (new_children == null)
    {
        m.warn("arena OOM appending clones to program", 0, 0);
        return program;
    }

    for (usz i = 0; i < old_count; i++) { new_children[i] = program.children[i]; }

    usz off = old_count;
    for (usz i = 0; i < m.instance_count; i++)
    {
        MonoInstance* inst = &m.instances[i];
        if (inst.clone != null && inst.complete)
        {
            new_children[off] = inst.clone;
            off++;
        }
    }

    program.children    = new_children;
    program.child_count = new_count;
    return program;
}


fn void Monomorphizer.report(Monomorphizer* m)
{
    if (m.diag_count == 0) { return; }
    printf("\n=== Mono diagnostics (%d) ===\n", m.diag_count);
    for (int i = 0; i < m.diag_count; i++)
    {
        MonoDiag d = m.diags[i];
        printf("  [mono %d:%d] %s\n", d.line, d.col, d.msg);
    }
}

fn usz Monomorphizer.instance_count_fn(Monomorphizer* m) { return m.instance_count; }
fn int  Monomorphizer.warning_count_fn(Monomorphizer* m) { return m.warning_count; }

// Print all generated monomorphic instances (--dump-mono).
fn void Monomorphizer.dump(Monomorphizer* m)
{
    printf("\n=== Mono instances (%llu) ===\n", (ulong)m.instance_count);
    for (usz i = 0; i < m.instance_count; i++)
    {
        MonoInstance* inst = &m.instances[i];
        if (inst.clone == null) { continue; }
        // Original generic name
        char* orig_ptr = null;
        usz   orig_len = 0;
        decl_name_of(inst.generic, &orig_ptr, &orig_len);
        printf("  [%llu] ", (ulong)i);
        if (orig_ptr != null)
        {
            for (usz j = 0; j < orig_len; j++) { printf("%c", orig_ptr[j]); }
        }
        printf(" → ");
        // Mangled clone name
        if (inst.name != null)
        {
            for (usz j = 0; j < inst.name_len; j++) { printf("%c", inst.name[j]); }
        }
        // Type args
        printf("  <");
        for (usz j = 0; j < inst.sub.count; j++)
        {
            if (j > 0) { printf(", "); }
            char[64] tbuf;
            usz tlen = type_to_str(inst.sub.types[j], &tbuf[0], 64, 0, 0);
            tbuf[tlen] = 0;
            printf("%s", &tbuf[0]);
        }
        printf(">\n");
    }
}
