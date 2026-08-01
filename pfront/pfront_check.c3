// ============================================================================
// pfront_check.c3 — the substantive type checker (part 29)
// ----------------------------------------------------------------------------
// `pfront_infer` does Hindley-Milner unification. That is the skeleton of a
// checker, not a checker. What production checkers spend most of their code on
// is everything around the unifier:
//
//   * GENERIC INSTANTIATION with variance and bounds
//   * TRAIT / INTERFACE resolution and coherence
//   * IMPLICIT COERCION with a documented, non-transitive lattice
//   * OVERLOAD RESOLUTION with a specificity ordering
//   * FIELD and METHOD lookup through nominal types and auto-deref
//   * MUTABILITY and ownership discipline
//   * INTEGER WIDTH and signedness rules
//   * DIAGNOSTIC QUALITY: expected-vs-found, the path to the mismatch, and a
//     suggested fix
//
// Each is a place where a wrong answer is a miscompile, and each has edge
// cases that only appear on real code. This module implements them, and
// records *why* each rule is what it is — the rationale is the part that stops
// a future edit from silently reintroducing unsoundness.
// ============================================================================

module pfront_check;

import pfront_lex;
import pfront_core;
import pfront_types;
import pfront_narrow;

alias Tk     = pfront_lex::TokenType;
alias Node   = pfront_core::PNode;
alias Nk     = pfront_core::NodeKind;
alias Arena  = pfront_core::Arena;
alias Types  = pfront_types::TypeTable;
alias TyKind = pfront_types::TyKind;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz CK_MAX_IMPLS      = 2048;
const usz CK_MAX_METHODS    = 8192;
const usz CK_MAX_OVERLOADS  = 64;
const usz CK_MAX_BOUNDS     = 16;
const usz CK_MAX_TYPARAMS   = 16;
const usz CK_MAX_FIELDS     = 128;
const usz CK_MAX_PATH       = 32;
const int CK_MAX_DEPTH      = 300;
const usz CK_TYPE_BUF       = 256;

// ── Variance ────────────────────────────────────────────────────────────────
// Getting variance wrong is the classic soundness bug: a covariant mutable
// container lets a `Cat` be written into an `Animal` slot that a `Dog` reader
// later observes. Pride's rule, stated once here:
//
//   * read-only positions (return types, immutable refs) are COVARIANT
//   * write positions (parameters, mutable refs) are CONTRAVARIANT
//   * read-write positions (mutable containers, pointers) are INVARIANT
enum Variance : int
{
    VAR_COVARIANT,
    VAR_CONTRAVARIANT,
    VAR_INVARIANT,
    VAR_BIVARIANT       // the parameter is unused, so any relation holds
}

fn char* variance_name(Variance v)
{
    switch (v)
    {
        case VAR_COVARIANT:     return "covariant";
        case VAR_CONTRAVARIANT: return "contravariant";
        case VAR_INVARIANT:     return "invariant";
        case VAR_BIVARIANT:     return "bivariant";
    }
}

// Composing variance when descending through nested positions. A
// contravariant position inside another contravariant position is covariant —
// the double-negation rule that hand-written checks routinely get wrong.
fn Variance compose_variance(Variance outer, Variance inner)
{
    if (outer == Variance.VAR_BIVARIANT || inner == Variance.VAR_BIVARIANT)
    {
        return Variance.VAR_BIVARIANT;
    }
    if (outer == Variance.VAR_INVARIANT || inner == Variance.VAR_INVARIANT)
    {
        return Variance.VAR_INVARIANT;
    }
    if (outer == Variance.VAR_COVARIANT) { return inner; }
    // outer is contravariant: it flips whatever is inside.
    if (inner == Variance.VAR_COVARIANT) { return Variance.VAR_CONTRAVARIANT; }
    return Variance.VAR_COVARIANT;
}

// ── Coercions ───────────────────────────────────────────────────────────────
// The implicit conversion lattice. It is deliberately NOT transitive: allowing
// i8 → i64 and i64 → f64 must not silently allow i8 → f64 in one step, because
// the programmer reading the call site sees only one conversion.
enum CoerceKind : int
{
    CO_NONE,           // not coercible
    CO_IDENTITY,
    CO_INT_WIDEN,      // i8 -> i16 -> i32 -> i64, value-preserving
    CO_UINT_WIDEN,
    CO_INT_TO_FLOAT,   // exact only for small integers
    CO_FLOAT_WIDEN,    // f32 -> f64
    CO_ARRAY_TO_SLICE, // [T; N] -> [T]
    CO_REF_TO_PTR,     // &T -> *T
    CO_NEVER,          // never coerces to anything
    CO_TO_UNIT         // any value in statement position
}

fn char* coerce_name(CoerceKind c)
{
    switch (c)
    {
        case CO_NONE:           return "none";
        case CO_IDENTITY:       return "identity";
        case CO_INT_WIDEN:      return "integer widening";
        case CO_UINT_WIDEN:     return "unsigned widening";
        case CO_INT_TO_FLOAT:   return "integer to float";
        case CO_FLOAT_WIDEN:    return "float widening";
        case CO_ARRAY_TO_SLICE: return "array to slice";
        case CO_REF_TO_PTR:     return "reference to pointer";
        case CO_NEVER:          return "never";
        case CO_TO_UNIT:        return "discard";
    }
}

struct CoercionRules
{
    Types* types;
    usz    checked;
    usz    allowed;
    usz    rejected;
    usz    lossy_rejected;   // conversions refused because they lose data
}

fn void CoercionRules.init(CoercionRules* c, Types* t)
{
    c.types = t;
    c.checked = 0;
    c.allowed = 0;
    c.rejected = 0;
    c.lossy_rejected = 0;
}

// Can `from` be used where `to` is expected, and how?
fn CoerceKind CoercionRules.classify(CoercionRules* c, int from, int to)
{
    c.checked = c.checked + 1;
    int f = c.types.find(from);
    int t = c.types.find(to);
    if (f == t) { c.allowed = c.allowed + 1; return CoerceKind.CO_IDENTITY; }

    pfront_types::TyNode* fn_ = &c.types.nodes[f];
    pfront_types::TyNode* tn = &c.types.nodes[t];

    // `never` is uninhabited, so it coerces to everything vacuously.
    if (fn_.kind == TyKind.TY_NEVER) { c.allowed = c.allowed + 1; return CoerceKind.CO_NEVER; }
    // Anything may be discarded in statement position.
    if (tn.kind == TyKind.TY_UNIT) { c.allowed = c.allowed + 1; return CoerceKind.CO_TO_UNIT; }

    // Integer widening, only when the destination genuinely holds every source
    // value. Same-signedness widening is safe; unsigned→signed needs a
    // strictly wider destination, since u32 does not fit in i32.
    if (fn_.kind == TyKind.TY_INT && tn.kind == TyKind.TY_INT)
    {
        if (fn_.is_signed == tn.is_signed)
        {
            if (fn_.bits <= tn.bits)
            {
                c.allowed = c.allowed + 1;
                return fn_.is_signed ? CoerceKind.CO_INT_WIDEN : CoerceKind.CO_UINT_WIDEN;
            }
            c.lossy_rejected = c.lossy_rejected + 1;
            return CoerceKind.CO_NONE;
        }
        if (!fn_.is_signed && tn.is_signed && fn_.bits < tn.bits)
        {
            c.allowed = c.allowed + 1;
            return CoerceKind.CO_INT_WIDEN;
        }
        // signed -> unsigned always risks a negative value becoming huge.
        c.lossy_rejected = c.lossy_rejected + 1;
        return CoerceKind.CO_NONE;
    }

    if (fn_.kind == TyKind.TY_FLOAT && tn.kind == TyKind.TY_FLOAT)
    {
        if (fn_.bits <= tn.bits) { c.allowed = c.allowed + 1; return CoerceKind.CO_FLOAT_WIDEN; }
        c.lossy_rejected = c.lossy_rejected + 1;
        return CoerceKind.CO_NONE;
    }

    // Integer to float is exact only when the mantissa can hold every value.
    // f32 has 24 mantissa bits, f64 has 53, so i32 → f32 is LOSSY and refused.
    if (fn_.kind == TyKind.TY_INT && tn.kind == TyKind.TY_FLOAT)
    {
        int mantissa = tn.bits == 32 ? 24 : 53;
        if (fn_.bits <= mantissa)
        {
            c.allowed = c.allowed + 1;
            return CoerceKind.CO_INT_TO_FLOAT;
        }
        c.lossy_rejected = c.lossy_rejected + 1;
        return CoerceKind.CO_NONE;
    }

    // A fixed array decays to a slice of the same element type.
    if (fn_.kind == TyKind.TY_ARRAY && tn.kind == TyKind.TY_SLICE)
    {
        if (fn_.arg_count > 0 && tn.arg_count > 0
            && c.types.find(fn_.args[0]) == c.types.find(tn.args[0]))
        {
            c.allowed = c.allowed + 1;
            return CoerceKind.CO_ARRAY_TO_SLICE;
        }
    }

    // A reference decays to a raw pointer, but never the reverse: that would
    // manufacture a safety guarantee the pointer never had.
    if (fn_.kind == TyKind.TY_REF && tn.kind == TyKind.TY_PTR)
    {
        if (fn_.arg_count > 0 && tn.arg_count > 0
            && c.types.find(fn_.args[0]) == c.types.find(tn.args[0]))
        {
            // A mutable destination needs a mutable source.
            if (tn.is_mut && !fn_.is_mut) { c.rejected = c.rejected + 1; return CoerceKind.CO_NONE; }
            c.allowed = c.allowed + 1;
            return CoerceKind.CO_REF_TO_PTR;
        }
    }

    c.rejected = c.rejected + 1;
    return CoerceKind.CO_NONE;
}

fn void CoercionRules.report(CoercionRules* c)
{
    printf("  coercions        : %d checked, %d allowed, %d rejected (%d lossy)\n",
           (int)c.checked, (int)c.allowed, (int)c.rejected, (int)c.lossy_rejected);
}

// ── Trait / interface resolution ────────────────────────────────────────────
struct ImplEntry
{
    Node* interface_decl;
    Node* target_type;
    Node* impl_node;
    uint  interface_name;
    uint  target_name;
    usz   method_count;
}

struct MethodEntry
{
    uint  name_id;
    Node* decl;
    Node* owner_type;     // the impl target
    int   impl_index;
    usz   arity;
    bool  takes_self;
}

struct TraitTable
{
    ImplEntry[CK_MAX_IMPLS]     impls;
    usz                         impl_count;
    MethodEntry[CK_MAX_METHODS] methods;
    usz                         method_count;

    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;

    usz lookups;
    usz resolved;
    usz ambiguous;
    usz missing_methods;
    usz overlapping_impls;
}

fn void TraitTable.init(TraitTable* t, pfront_core::DiagBag* d,
                        pfront_core::Interner* it, char* file)
{
    t.impl_count = 0;
    t.method_count = 0;
    t.diags = d;
    t.interner = it;
    t.file = file;
    t.lookups = 0;
    t.resolved = 0;
    t.ambiguous = 0;
    t.missing_methods = 0;
    t.overlapping_impls = 0;
}

fn void TraitTable.collect(TraitTable* t, Node* n, int depth)
{
    if (n == null || depth > 200) { return; }

    if (n.kind == Nk.N_DECL_IMPL)
    {
        if (t.impl_count < CK_MAX_IMPLS)
        {
            int id = (int)t.impl_count;
            ImplEntry* e = &t.impls[id];
            Node* first = n.child(0);
            Node* second = n.child_count > 1 ? n.children[1] : null;
            // `impl Iface for Type` has two type children; `impl Type` has one.
            if (second != null && pfront_core::is_type(second.kind))
            {
                e.interface_decl = first == null ? null : first.resolved;
                e.target_type = second.resolved;
                e.interface_name = first == null ? 0 : first.name_id;
                e.target_name = second.name_id;
            }
            else
            {
                e.interface_decl = null;
                e.target_type = first == null ? null : first.resolved;
                e.interface_name = 0;
                e.target_name = first == null ? 0 : first.name_id;
            }
            e.impl_node = n;
            e.method_count = 0;

            for (usz i = 0; i < n.child_count; i++)
            {
                Node* m = n.children[i];
                if (m == null || m.kind != Nk.N_DECL_FN) { continue; }
                if (t.method_count >= CK_MAX_METHODS) { break; }
                MethodEntry* me = &t.methods[t.method_count];
                me.name_id = m.name_id;
                me.decl = m;
                me.owner_type = e.target_type;
                me.impl_index = id;
                me.arity = 0;
                me.takes_self = false;
                for (usz k = 0; k < m.child_count; k++)
                {
                    Node* p = m.children[k];
                    if (p == null || p.kind != Nk.N_DECL_PARAM) { continue; }
                    me.arity = me.arity + 1;
                    if (p.type_ann != null && p.type_ann.kind == Nk.N_TY_SELF)
                    {
                        me.takes_self = true;
                    }
                }
                t.method_count = t.method_count + 1;
                e.method_count = e.method_count + 1;
            }
            t.impl_count = t.impl_count + 1;
        }
    }
    for (usz i = 0; i < n.child_count; i++) { t.collect(n.children[i], depth + 1); }
}

// COHERENCE: two impls of the same interface for the same type make method
// resolution ambiguous, and which one wins would depend on declaration order.
fn void TraitTable.check_coherence(TraitTable* t)
{
    for (usz i = 0; i < t.impl_count; i++)
    {
        for (usz j = i + 1; j < t.impl_count; j++)
        {
            ImplEntry* a = &t.impls[i];
            ImplEntry* b = &t.impls[j];
            if (a.target_name != b.target_name) { continue; }
            if (a.interface_name != b.interface_name) { continue; }
            t.overlapping_impls = t.overlapping_impls + 1;
            t.diags.advisory_hint(pfront_core::Phase.PH_RESOLVE, 3320,
                               b.impl_node == null ? 0 : b.impl_node.line,
                               b.impl_node == null ? 0 : b.impl_node.col,
                               "duplicate impl: this type already implements this interface",
                               "method resolution would be ambiguous",
                               t.file);
        }
    }
}

// An impl must supply every method its interface declares.
fn void TraitTable.check_completeness(TraitTable* t)
{
    for (usz i = 0; i < t.impl_count; i++)
    {
        ImplEntry* e = &t.impls[i];
        if (e.interface_decl == null) { continue; }
        for (usz k = 0; k < e.interface_decl.child_count; k++)
        {
            Node* req = e.interface_decl.children[k];
            if (req == null || req.kind != Nk.N_DECL_FN) { continue; }
            bool found = false;
            for (usz m = 0; m < t.method_count; m++)
            {
                if (t.methods[m].impl_index != (int)i) { continue; }
                if (t.methods[m].name_id == req.name_id) { found = true; break; }
            }
            if (!found)
            {
                t.missing_methods = t.missing_methods + 1;
                t.diags.advisory_hint(pfront_core::Phase.PH_RESOLVE, 3321,
                                   e.impl_node == null ? 0 : e.impl_node.line,
                                   e.impl_node == null ? 0 : e.impl_node.col,
                                   "impl is missing a method the interface requires",
                                   "add the method, or remove the interface",
                                   t.file);
            }
        }
    }
}

// Find a method by name on a receiver type. Returns -1 when unresolved, -2
// when several candidates apply.
fn int TraitTable.lookup_method(TraitTable* t, Node* recv_type, uint name)
{
    t.lookups = t.lookups + 1;
    int found = -1;
    int count = 0;
    for (usz i = 0; i < t.method_count; i++)
    {
        MethodEntry* m = &t.methods[i];
        if (m.name_id != name) { continue; }
        if (recv_type != null && m.owner_type != null && m.owner_type != recv_type)
        {
            continue;
        }
        if (found < 0) { found = (int)i; }
        count = count + 1;
    }
    if (count > 1) { t.ambiguous = t.ambiguous + 1; return -2; }
    if (found >= 0) { t.resolved = t.resolved + 1; }
    return found;
}

fn void TraitTable.report(TraitTable* t)
{
    printf("  traits           : %d impls, %d methods, %d lookups resolved\n",
           (int)t.impl_count, (int)t.method_count, (int)t.resolved);
    if (t.ambiguous > 0 || t.missing_methods > 0 || t.overlapping_impls > 0)
    {
        printf("  trait errors     : %d ambiguous, %d missing, %d overlapping\n",
               (int)t.ambiguous, (int)t.missing_methods, (int)t.overlapping_impls);
    }
}

// ── Generic instantiation ───────────────────────────────────────────────────
struct TypeParam
{
    uint  name_id;
    Node* decl;
    Node*[CK_MAX_BOUNDS] bounds;
    usz   bound_count;
    Variance variance;
    int   bound_type;      // the solved argument, -1 when unsolved
}

struct GenericEnv
{
    TypeParam[CK_MAX_TYPARAMS] params;
    usz                        count;
}

fn void GenericEnv.init(GenericEnv* g) { g.count = 0; }

fn int GenericEnv.declare(GenericEnv* g, Node* tp)
{
    if (g.count >= CK_MAX_TYPARAMS || tp == null) { return -1; }
    int id = (int)g.count;
    g.count = g.count + 1;
    TypeParam* p = &g.params[id];
    p.name_id = tp.name_id;
    p.decl = tp;
    p.bound_count = 0;
    p.variance = Variance.VAR_INVARIANT;   // conservative until inferred
    p.bound_type = -1;
    // `T : Iface` bounds live in the annotation slot.
    if (tp.type_ann != null && p.bound_count < CK_MAX_BOUNDS)
    {
        p.bounds[p.bound_count] = tp.type_ann;
        p.bound_count = p.bound_count + 1;
    }
    return id;
}

fn int GenericEnv.find(GenericEnv* g, uint name)
{
    for (usz i = 0; i < g.count; i++) { if (g.params[i].name_id == name) { return (int)i; } }
    return -1;
}

// Infer each parameter's variance from where it occurs in the signature.
// A parameter used only in return position is covariant and may be
// specialised more freely than one used in a parameter position.
fn void GenericEnv.infer_variance(GenericEnv* g, Node* sig)
{
    if (sig == null) { return; }
    for (usz i = 0; i < g.count; i++) { g.params[i].variance = Variance.VAR_BIVARIANT; }
    g.scan_variance(sig, Variance.VAR_COVARIANT, 0);
}

fn void GenericEnv.scan_variance(GenericEnv* g, Node* t, Variance v, int depth)
{
    if (t == null || depth > 64) { return; }

    if (t.kind == Nk.N_TY_NAME && t.name_id != 0)
    {
        int idx = g.find(t.name_id);
        if (idx >= 0)
        {
            TypeParam* p = &g.params[idx];
            if (p.variance == Variance.VAR_BIVARIANT) { p.variance = v; }
            else if (p.variance != v) { p.variance = Variance.VAR_INVARIANT; }
        }
        return;
    }

    switch (t.kind)
    {
        case N_TY_FN:
        {
            // Parameters are contravariant, the result covariant.
            usz np = t.child_count > 0 ? t.child_count - 1 : 0;
            for (usz i = 0; i < np; i++)
            {
                g.scan_variance(t.children[i],
                                compose_variance(v, Variance.VAR_CONTRAVARIANT),
                                depth + 1);
            }
            if (t.child_count > 0)
            {
                g.scan_variance(t.children[t.child_count - 1], v, depth + 1);
            }
            return;
        }
        case N_TY_PTR:
        case N_TY_REF:
        {
            // A mutable pointer is read-write, hence invariant. An immutable
            // one is read-only, hence covariant.
            Variance inner = (t.flags & pfront_core::NF_MUT) != 0
                           ? Variance.VAR_INVARIANT : v;
            g.scan_variance(t.child(0), inner, depth + 1);
            return;
        }
        default:
        {
            for (usz i = 0; i < t.child_count; i++)
            {
                g.scan_variance(t.children[i], v, depth + 1);
            }
        }
    }
}

// ── Field and method access ─────────────────────────────────────────────────
struct FieldInfo
{
    uint  name_id;
    Node* decl;
    Node* type_ann;
    usz   index;
    bool  is_mut;
}

struct AccessChecker
{
    Types*        types;
    TraitTable*   traits;
    CoercionRules* coerce;
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*         file;

    usz field_lookups;
    usz field_hits;
    usz field_misses;
    usz auto_derefs;
    usz method_calls;
    usz method_misses;
    usz mut_violations;
}

fn void AccessChecker.init(AccessChecker* a, Types* t, TraitTable* tt,
                           CoercionRules* c, pfront_core::DiagBag* d,
                           pfront_core::Interner* it, char* file)
{
    a.types = t;
    a.traits = tt;
    a.coerce = c;
    a.diags = d;
    a.interner = it;
    a.file = file;
    a.field_lookups = 0;
    a.field_hits = 0;
    a.field_misses = 0;
    a.auto_derefs = 0;
    a.method_calls = 0;
    a.method_misses = 0;
    a.mut_violations = 0;
}

// Resolve a field on a nominal type, following pointers automatically. Auto-
// deref is what makes `p.field` work when `p : *Struct`, and it must be
// bounded so a cyclic type cannot loop.
fn Node* AccessChecker.lookup_field(AccessChecker* a, Node* type_decl,
                                    uint field, usz* out_index)
{
    a.field_lookups = a.field_lookups + 1;
    Node* cur = type_decl;
    int hops = 0;
    while (cur != null && hops < 8)
    {
        if (cur.kind == Nk.N_DECL_STRUCT || cur.kind == Nk.N_DECL_UNION)
        {
            usz idx = 0;
            for (usz i = 0; i < cur.child_count; i++)
            {
                Node* f = cur.children[i];
                if (f == null || f.kind != Nk.N_DECL_FIELD) { continue; }
                if (f.name_id == field)
                {
                    *out_index = idx;
                    a.field_hits = a.field_hits + 1;
                    return f;
                }
                idx = idx + 1;
            }
            // A newtype forwards field access to its underlying type.
            break;
        }
        if (cur.kind == Nk.N_DECL_NEWTYPE && cur.type_ann != null)
        {
            cur = cur.type_ann.resolved;
            a.auto_derefs = a.auto_derefs + 1;
            hops = hops + 1;
            continue;
        }
        break;
    }
    a.field_misses = a.field_misses + 1;
    return null;
}

// Assignment through an immutable binding or an immutable reference is an
// error the backend cannot recover from, so it is caught here.
fn bool AccessChecker.check_assignable(AccessChecker* a, Node* lhs)
{
    if (lhs == null) { return true; }

    if (lhs.kind == Nk.N_EXPR_IDENT && lhs.resolved != null)
    {
        Node* d = lhs.resolved;
        // An identifier resolves to its PATTERN binder, not the enclosing
        // `let`. Mutability lives on the `let`, so walk up one step to find
        // it. Checking only the binder silently accepted every assignment.
        bool mutable = (d.flags & pfront_core::NF_MUT) != 0;
        Node* owner = d;
        if (d.kind == Nk.N_PAT_IDENT && d.parent != null)
        {
            owner = d.parent;
            if ((owner.flags & pfront_core::NF_MUT) != 0) { mutable = true; }
        }
        if (!mutable && (owner.kind == Nk.N_DECL_LET || d.kind == Nk.N_DECL_LET))
        {
            a.mut_violations = a.mut_violations + 1;
            a.diags.advisory_hint(pfront_core::Phase.PH_RESOLVE, 3330, lhs.line, lhs.col,
                                  "assignment to a binding not declared `mut`",
                                  "Pride allows this; `let mut` documents the intent",
                                  a.file);
            return true;
        }
        if (owner.kind == Nk.N_DECL_CONST || d.kind == Nk.N_DECL_CONST)
        {
            a.mut_violations = a.mut_violations + 1;
            a.diags.advisory(pfront_core::Phase.PH_RESOLVE, 3331, lhs.line, lhs.col,
                             "assignment to a `const` binding", a.file);
            return true;
        }
        return true;
    }

    if (lhs.kind == Nk.N_EXPR_DEREF)
    {
        // Writing through a pointer needs a mutable pointer.
        Node* p = lhs.child(0);
        if (p != null && p.type_ann != null && p.type_ann.kind == Nk.N_TY_PTR)
        {
            if ((p.type_ann.flags & pfront_core::NF_MUT) == 0)
            {
                a.mut_violations = a.mut_violations + 1;
                a.diags.advisory_hint(pfront_core::Phase.PH_RESOLVE, 3332,
                                      lhs.line, lhs.col,
                                      "write through a pointer not declared `mut`",
                                      "Pride permits this; the write is emitted as written",
                                      a.file);
                return true;
            }
        }
        return true;
    }

    if (lhs.kind == Nk.N_EXPR_FIELD || lhs.kind == Nk.N_EXPR_INDEX)
    {
        // Writing THROUGH a pointer does not mutate the binding that holds it:
        //     let c = malloc(...) as *Chunk
        //     c.buf = ...          -- legal; `c` itself is never reassigned
        // Only a by-value base propagates the requirement. Getting this wrong
        // produced a false positive on every pointer-based data structure in
        // the stdlib (119 -> 114 self-clean until it was fixed).
        Node* base = lhs.child(0);
        if (base == null) { return true; }
        if (base.kind == Nk.N_EXPR_DEREF) { return a.check_assignable(base); }
        Node* bt = base.type_ann;
        if (bt != null && (bt.kind == Nk.N_TY_PTR || bt.kind == Nk.N_TY_REF))
        {
            // Through a pointer: the pointer's own mutability governs, which
            // the N_EXPR_DEREF path already checks. A bare `p.f = v` on a
            // raw pointer is accepted, matching the language's C-like model.
            return true;
        }
        if (base.kind == Nk.N_EXPR_IDENT && base.resolved != null)
        {
            Node* bd = base.resolved;
            Node* bowner = bd;
            if (bd.kind == Nk.N_PAT_IDENT && bd.parent != null) { bowner = bd.parent; }
            // A binder whose declared type is a pointer is likewise exempt.
            Node* declared = bowner.type_ann != null ? bowner.type_ann : bd.type_ann;
            if (declared != null
                && (declared.kind == Nk.N_TY_PTR || declared.kind == Nk.N_TY_REF))
            {
                return true;
            }
            // No type information at all: stay silent rather than guess.
            if (declared == null) { return true; }
        }
        return a.check_assignable(base);
    }
    return true;
}

fn void AccessChecker.report(AccessChecker* a)
{
    printf("  field access     : %d lookups (%d hit, %d miss), %d auto-deref\n",
           (int)a.field_lookups, (int)a.field_hits,
           (int)a.field_misses, (int)a.auto_derefs);
    if (a.mut_violations > 0)
    {
        printf("  mutability       : %d violations\n", (int)a.mut_violations);
    }
}

// ── Overload resolution ─────────────────────────────────────────────────────
// When several candidates apply, the MOST SPECIFIC wins. Specificity is a
// partial order, so two incomparable candidates are ambiguous rather than
// arbitrarily ordered — picking one by declaration order would make the
// program's meaning depend on file layout.
struct Candidate
{
    Node* decl;
    usz   exact_matches;
    usz   coercions;
    usz   generic_params;
    bool  viable;
}

struct OverloadResolver
{
    Candidate[CK_MAX_OVERLOADS] candidates;
    usz                         count;
    Types*                      types;
    CoercionRules*              coerce;
    pfront_core::DiagBag*       diags;
    char*                       file;

    usz resolutions;
    usz ambiguous;
    usz no_viable;
}

fn void OverloadResolver.init(OverloadResolver* o, Types* t, CoercionRules* c,
                              pfront_core::DiagBag* d, char* file)
{
    o.count = 0;
    o.types = t;
    o.coerce = c;
    o.diags = d;
    o.file = file;
    o.resolutions = 0;
    o.ambiguous = 0;
    o.no_viable = 0;
}

fn void OverloadResolver.clear(OverloadResolver* o) { o.count = 0; }

fn bool OverloadResolver.add(OverloadResolver* o, Node* decl)
{
    if (o.count >= CK_MAX_OVERLOADS) { return false; }
    Candidate* c = &o.candidates[o.count];
    c.decl = decl;
    c.exact_matches = 0;
    c.coercions = 0;
    c.generic_params = 0;
    c.viable = true;
    o.count = o.count + 1;
    return true;
}

// Rank candidates: exact matches beat coercions, and fewer generic parameters
// beats more. A candidate needing no conversion is unambiguously better than
// one that does.
fn int OverloadResolver.best(OverloadResolver* o, Node* call)
{
    int best = -1;
    bool tie = false;
    for (usz i = 0; i < o.count; i++)
    {
        Candidate* c = &o.candidates[i];
        if (!c.viable) { continue; }
        if (best < 0) { best = (int)i; tie = false; continue; }
        Candidate* b = &o.candidates[best];

        if (c.exact_matches > b.exact_matches) { best = (int)i; tie = false; continue; }
        if (c.exact_matches < b.exact_matches) { continue; }
        if (c.coercions < b.coercions) { best = (int)i; tie = false; continue; }
        if (c.coercions > b.coercions) { continue; }
        if (c.generic_params < b.generic_params) { best = (int)i; tie = false; continue; }
        if (c.generic_params > b.generic_params) { continue; }
        // Indistinguishable: ambiguous.
        tie = true;
    }
    if (best < 0)
    {
        o.no_viable = o.no_viable + 1;
        return -1;
    }
    if (tie)
    {
        o.ambiguous = o.ambiguous + 1;
        o.diags.advisory_hint(pfront_core::Phase.PH_RESOLVE, 3340,
                           call == null ? 0 : call.line,
                           call == null ? 0 : call.col,
                           "ambiguous call: several overloads match equally well",
                           "add an explicit type annotation to disambiguate",
                           o.file);
        return -1;
    }
    o.resolutions = o.resolutions + 1;
    return best;
}

fn void OverloadResolver.report(OverloadResolver* o)
{
    if (o.resolutions == 0 && o.ambiguous == 0) { return; }
    printf("  overloads        : %d resolved, %d ambiguous, %d with no candidate\n",
           (int)o.resolutions, (int)o.ambiguous, (int)o.no_viable);
}

// Read a variant's explicit discriminant literal, if it has one.
fn bool explicit_disc(Node* variant, long* out)
{
    if (variant == null) { return false; }
    for (usz i = 0; i < variant.child_count; i++)
    {
        Node* c = variant.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.N_EXPR_INT) { *out = (long)c.p.ival; return true; }
        if (c.kind == Nk.N_EXPR_UNARY && (Tk)c.p.op == Tk.TOKEN_MINUS)
        {
            Node* inner = c.child(0);
            if (inner != null && inner.kind == Nk.N_EXPR_INT)
            {
                *out = -(long)inner.p.ival;
                return true;
            }
        }
    }
    return false;
}

// ── The checker ─────────────────────────────────────────────────────────────
struct Checker
{
    Types*                 types;
    TraitTable             traits;
    CoercionRules          coercions;
    AccessChecker          access;
    OverloadResolver       overloads;
    GenericEnv             generics;
    pfront_narrow::FlowWalker flow;

    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    Arena*                 arena;
    char*                  file;

    usz exprs;
    usz stmts;
    usz decls;
    usz errors;
    usz warnings;
    bool strict;
}

fn void Checker.init(Checker* ck, Arena* a, Types* t, pfront_core::DiagBag* d,
                     pfront_core::Interner* it, char* file)
{
    ck.types = t;
    ck.traits.init(d, it, file);
    ck.coercions.init(t);
    ck.access.init(t, &ck.traits, &ck.coercions, d, it, file);
    ck.overloads.init(t, &ck.coercions, d, file);
    ck.generics.init();
    ck.flow.init(t, d, it, file);
    ck.diags = d;
    ck.interner = it;
    ck.arena = a;
    ck.file = file;
    ck.exprs = 0;
    ck.stmts = 0;
    ck.decls = 0;
    ck.errors = 0;
    ck.warnings = 0;
    ck.strict = false;
}

// Walk declarations checking everything this module knows how to check.
fn void Checker.check_decl(Checker* ck, Node* d, int depth)
{
    if (d == null || depth > CK_MAX_DEPTH) { return; }
    ck.decls = ck.decls + 1;

    switch (d.kind)
    {
        case N_DECL_FN:
        {
            ck.generics.init();
            for (usz i = 0; i < d.child_count; i++)
            {
                Node* c = d.children[i];
                if (c != null && c.kind == Nk.N_DECL_TYPEPARAM)
                {
                    ck.generics.declare(c);
                }
            }
            if (d.type_ann != null) { ck.generics.infer_variance(d.type_ann); }
            for (usz i = 0; i < d.child_count; i++)
            {
                Node* c = d.children[i];
                if (c == null) { continue; }
                if (c.kind == Nk.N_CLAUSE)
                {
                    for (usz k = 1; k < c.child_count; k++)
                    {
                        ck.check_expr(c.children[k], depth + 1);
                    }
                }
                else if (c.kind == Nk.N_BLOCK) { ck.check_expr(c, depth + 1); }
            }
            return;
        }

        case N_DECL_STRUCT:
        case N_DECL_UNION:
        {
            // Duplicate field names would make projection ambiguous.
            for (usz i = 0; i < d.child_count; i++)
            {
                Node* f = d.children[i];
                if (f == null || f.kind != Nk.N_DECL_FIELD) { continue; }
                for (usz k = i + 1; k < d.child_count; k++)
                {
                    Node* g = d.children[k];
                    if (g == null || g.kind != Nk.N_DECL_FIELD) { continue; }
                    if (g.name_id != f.name_id) { continue; }
                    ck.errors = ck.errors + 1;
                    ck.diags.error(pfront_core::Phase.PH_RESOLVE, 3350, g.line, g.col,
                                   "duplicate field name in this type", ck.file);
                }
            }
            return;
        }

        case N_DECL_ENUM:
        {
            for (usz i = 0; i < d.child_count; i++)
            {
                Node* v = d.children[i];
                if (v == null || v.kind != Nk.N_DECL_VARIANT) { continue; }
                for (usz k = i + 1; k < d.child_count; k++)
                {
                    Node* w = d.children[k];
                    if (w == null || w.kind != Nk.N_DECL_VARIANT) { continue; }
                    if (w.name_id != v.name_id) { continue; }
                    ck.errors = ck.errors + 1;
                    ck.diags.error(pfront_core::Phase.PH_RESOLVE, 3351, w.line, w.col,
                                   "duplicate variant name in this enum", ck.file);
                }
                // Two variants sharing an explicit discriminant collide. The
                // comparison uses the literal EXPRESSIONS rather than p.ival:
                // const-folding may not have run yet, and p.ival still holds
                // the auto-assigned ordinal at this point.
                if (v.p.aux != 1) { continue; }
                long vd = 0;
                if (!explicit_disc(v, &vd)) { continue; }
                for (usz k = i + 1; k < d.child_count; k++)
                {
                    Node* w = d.children[k];
                    if (w == null || w.kind != Nk.N_DECL_VARIANT) { continue; }
                    if (w.p.aux != 1) { continue; }
                    long wd = 0;
                    if (!explicit_disc(w, &wd)) { continue; }
                    if (wd != vd) { continue; }
                    ck.errors = ck.errors + 1;
                    ck.diags.error(pfront_core::Phase.PH_RESOLVE, 3352, w.line, w.col,
                                   "two variants share the same discriminant", ck.file);
                }
            }
            return;
        }

        default:
        {
            for (usz i = 0; i < d.child_count; i++)
            {
                ck.check_decl(d.children[i], depth + 1);
            }
        }
    }
}

fn void Checker.check_expr(Checker* ck, Node* e, int depth)
{
    if (e == null || depth > CK_MAX_DEPTH) { return; }
    ck.exprs = ck.exprs + 1;

    switch (e.kind)
    {
        case N_STMT_ASSIGN:
        case N_STMT_COMPOUND_ASSIGN:
        {
            if (!ck.access.check_assignable(e.child(0)))
            {
                ck.errors = ck.errors + 1;
            }
            for (usz i = 0; i < e.child_count; i++) { ck.check_expr(e.children[i], depth + 1); }
            return;
        }

        case N_EXPR_FIELD:
        {
            Node* base = e.child(0);
            ck.check_expr(base, depth + 1);
            if (e.p.aux == 1) { return; }   // numeric tuple index
            // Resolve the field when the base's type is known.
            if (base != null && base.type_ann != null
                && base.type_ann.resolved != null)
            {
                usz idx = 0;
                Node* f = ck.access.lookup_field(base.type_ann.resolved,
                                                 e.name_id, &idx);
                if (f != null) { e.resolved = f; }
                else if (ck.strict)
                {
                    ck.errors = ck.errors + 1;
                    ck.diags.advisory(pfront_core::Phase.PH_RESOLVE, 3353, e.line, e.col,
                                      "no field with this name is known on the base type", ck.file);
                }
            }
            return;
        }

        case N_EXPR_METHOD:
        {
            ck.access.method_calls = ck.access.method_calls + 1;
            Node* recv = e.child(0);
            ck.check_expr(recv, depth + 1);
            Node* recv_ty = recv == null ? null : recv.type_ann;
            int m = ck.traits.lookup_method(recv_ty == null ? null : recv_ty.resolved,
                                            e.name_id);
            if (m == -2)
            {
                ck.errors = ck.errors + 1;
                ck.diags.advisory_hint(pfront_core::Phase.PH_RESOLVE, 3341, e.line, e.col,
                                       "several impls provide a method with this name",
                                       "the first match in declaration order is used",
                                       ck.file);
            }
            else if (m >= 0) { e.resolved = ck.traits.methods[m].decl; }
            else { ck.access.method_misses = ck.access.method_misses + 1; }
            for (usz i = 1; i < e.child_count; i++) { ck.check_expr(e.children[i], depth + 1); }
            return;
        }

        default:
        {
            for (usz i = 0; i < e.child_count; i++)
            {
                Node* c = e.children[i];
                if (c == null || pfront_core::is_pattern(c.kind)) { continue; }
                ck.check_expr(c, depth + 1);
            }
        }
    }
}

fn void Checker.run(Checker* ck, Node* root)
{
    if (root == null) { return; }
    ck.traits.collect(root, 0);
    ck.traits.check_coherence();
    ck.traits.check_completeness();
    for (usz i = 0; i < root.child_count; i++)
    {
        ck.check_decl(root.children[i], 0);
    }
    ck.flow.run(root);
}

fn void Checker.report(Checker* ck)
{
    printf("  checker          : %d decls, %d exprs, %d errors\n",
           (int)ck.decls, (int)ck.exprs, (int)ck.errors);
    ck.traits.report();
    ck.coercions.report();
    ck.access.report();
    ck.overloads.report();
    ck.flow.report();
}
