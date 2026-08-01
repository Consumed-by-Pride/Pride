// ============================================================================
// theory_poly.c3 — polymorphism: constraint solving and real instantiation
// ----------------------------------------------------------------------------
// `theory_effects::Monomorphiser` is a CENSUS. It counts how many generics
// exist and how many call sites instantiate them, mangles a name for each,
// and stops. It never produces a specialised body, never checks a bound, and
// never tells you what `T` actually was at a given call.
//
// This module does the work the census stands in for:
//
//   1. TYPE-PARAMETER ENVIRONMENT — every `<T, U: Ord>` in scope, with its
//      declared bounds and inferred variance.
//   2. UNIFICATION against a call's actual arguments, producing a SUBSTITUTION
//      θ = {T ↦ i64, U ↦ Str}. This is what "inferring the type arguments"
//      means, and without it a generic call carries no information at all.
//   3. BOUND CHECKING — `T : Ord` must be satisfied by the chosen argument.
//   4. INSTANTIATION — clone the generic's signature with θ applied, so the
//      instance has a REAL monomorphic type rather than a mangled name.
//   5. ESCAPE DETECTION — a type parameter that appears in a return position
//      but in no argument position cannot be inferred from the call.
//
// Design notes:
//
//   * Substitution is CAPTURE-AVOIDING by construction: type parameters are
//     resolved to their `N_DECL_TYPEPARAM` binder by the resolver, so two
//     `T`s from different declarations are different pointers and cannot
//     collide. Comparing by name would have merged them.
//
//   * Cloning is STRUCTURAL and bounded. A generic that instantiates itself
//     with a strictly larger argument (`f<T>` calling `f<List<T>>`) does not
//     terminate; depth is capped and the case is reported rather than hung on.
//
//   * The pass is ADVISORY, like everything else in an untyped language. It
//     reports what it could not infer; it never rejects the program.
// ============================================================================

module theory_poly;

import pfront_core;
import pfront_lex;

alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz PY_MAX_PARAMS   = 32;      // type parameters in one declaration
const usz PY_MAX_SUBST    = 64;      // bindings in one substitution
const usz PY_MAX_INST     = 4096;    // distinct instantiations per program
const usz PY_MAX_BOUNDS   = 8;
const int PY_MAX_DEPTH    = 200;
const int PY_MAX_INST_DEPTH = 24;    // recursive-instantiation cutoff

// ════════════════════════════════════════════════════════════════════════════
// VARIANCE
// ════════════════════════════════════════════════════════════════════════════
// Where a parameter appears decides how instances relate. Function arguments
// flip the sign; results preserve it. A parameter used in both is invariant.

const int VAR_BIVARIANT     = 0;   // appears nowhere
const int VAR_COVARIANT     = 1;   // result position only
const int VAR_CONTRAVARIANT = 2;   // argument position only
const int VAR_INVARIANT     = 3;   // both, or under a mutable pointer

fn char* variance_name(int v)
{
    switch (v)
    {
        case VAR_BIVARIANT:     return "bivariant";
        case VAR_COVARIANT:     return "covariant";
        case VAR_CONTRAVARIANT: return "contravariant";
        default:                return "invariant";
    }
}

// Joining two occurrences: co + contra = invariant.
fn int variance_join(int a, int b)
{
    if (a == VAR_BIVARIANT) { return b; }
    if (b == VAR_BIVARIANT) { return a; }
    if (a == b) { return a; }
    return VAR_INVARIANT;
}

// Descending through a contravariant position flips the sign.
fn int variance_flip(int v)
{
    if (v == VAR_COVARIANT)     { return VAR_CONTRAVARIANT; }
    if (v == VAR_CONTRAVARIANT) { return VAR_COVARIANT; }
    return v;
}

// ════════════════════════════════════════════════════════════════════════════
// SUBSTITUTION
// ════════════════════════════════════════════════════════════════════════════
// θ maps a type-parameter BINDER (not a name) to a concrete type node.

struct SubstEntry
{
    Node* param;      // the N_DECL_TYPEPARAM this binds
    Node* value;      // the type it stands for
}

struct Subst
{
    SubstEntry[PY_MAX_SUBST] items;
    usz  count;
    bool overflow;
}

fn void Subst.init(Subst* s) { s.count = 0; s.overflow = false; }

fn Node* Subst.lookup(Subst* s, Node* param)
{
    if (param == null) { return null; }
    for (usz i = 0; i < s.count; i++)
    {
        if (s.items[i].param == param) { return s.items[i].value; }
    }
    return null;
}

// Bind, or report a CONFLICT if the parameter already stands for something
// structurally different. `f(x: T, y: T)` called as `f(1, "a")` is the case
// this catches — and in an untyped language it is advice, not an error.
fn bool Subst.bind(Subst* s, Node* param, Node* value)
{
    if (param == null || value == null) { return true; }
    Node* prev = s.lookup(param);
    if (prev != null) { return type_eq(prev, value, 0); }
    if (s.count >= PY_MAX_SUBST) { s.overflow = true; return true; }
    s.items[s.count].param = param;
    s.items[s.count].value = value;
    s.count = s.count + 1;
    return true;
}

// Structural type equality. Compares RESOLVED targets so two spellings of the
// same type (an alias and its definition) are not treated as different.
fn bool type_eq(Node* a, Node* b, int depth)
{
    if (a == b) { return true; }
    if (a == null || b == null) { return false; }
    if (depth > PY_MAX_DEPTH) { return false; }
    if (a.kind != b.kind) { return false; }
    if (a.kind == Nk.N_TY_NAME)
    {
        if (a.resolved != null && b.resolved != null)
        {
            return a.resolved == b.resolved;
        }
        return a.name_id == b.name_id;
    }
    if (a.child_count != b.child_count) { return false; }
    for (usz i = 0; i < a.child_count; i++)
    {
        if (!type_eq(a.children[i], b.children[i], depth + 1)) { return false; }
    }
    return true;
}

// ════════════════════════════════════════════════════════════════════════════
// TYPE PARAMETERS
// ════════════════════════════════════════════════════════════════════════════

struct ParamInfo
{
    Node* decl;                        // the N_DECL_TYPEPARAM
    uint  name_id;
    Node*[PY_MAX_BOUNDS] bounds;       // `T : Ord` constraints
    usz   bound_count;
    int   variance;
    bool  in_args;                     // appears in an argument position
    bool  in_result;                   // appears in the return type
}

struct ParamEnv
{
    ParamInfo[PY_MAX_PARAMS] params;
    usz count;
}

fn void ParamEnv.init(ParamEnv* e) { e.count = 0; }

fn int ParamEnv.find(ParamEnv* e, Node* decl)
{
    for (usz i = 0; i < e.count; i++)
    {
        if (e.params[i].decl == decl) { return (int)i; }
    }
    return -1;
}

fn int ParamEnv.declare(ParamEnv* e, Node* tp)
{
    if (tp == null) { return -1; }
    int at = e.find(tp);
    if (at >= 0) { return at; }
    if (e.count >= PY_MAX_PARAMS) { return -1; }
    usz i = e.count;
    e.count = e.count + 1;
    ParamInfo* p = &e.params[i];
    p.decl = tp;
    p.name_id = tp.name_id;
    p.bound_count = 0;
    p.variance = VAR_BIVARIANT;
    p.in_args = false;
    p.in_result = false;
    // `<T : Ord>` — the bound arrives as a child of the type parameter.
    for (usz c = 0; c < tp.child_count && p.bound_count < PY_MAX_BOUNDS; c++)
    {
        Node* b = tp.children[c];
        if (b == null) { continue; }
        if (pfront_core::is_type(b.kind) || b.kind == Nk.N_TY_CONSTRAINT)
        {
            p.bounds[p.bound_count] = b;
            p.bound_count = p.bound_count + 1;
        }
    }
    return (int)i;
}

// Collect every `<T, U>` declared on `decl`.
fn void ParamEnv.collect(ParamEnv* e, Node* decl)
{
    if (decl == null) { return; }
    for (usz i = 0; i < decl.child_count; i++)
    {
        Node* c = decl.children[i];
        if (c != null && c.kind == Nk.N_DECL_TYPEPARAM) { e.declare(c); }
    }
}

// Walk a signature recording where each parameter appears. `sign` is the
// variance of the position currently being descended into.
fn void ParamEnv.scan_positions(ParamEnv* e, Node* ty, int sign, bool is_result,
                                int depth)
{
    if (ty == null || depth > PY_MAX_DEPTH) { return; }

    if (ty.kind == Nk.N_TY_NAME && ty.resolved != null)
    {
        int at = e.find(ty.resolved);
        if (at >= 0)
        {
            e.params[at].variance = variance_join(e.params[at].variance, sign);
            if (is_result) { e.params[at].in_result = true; }
            else           { e.params[at].in_args = true; }
        }
        return;
    }

    // A function type is contravariant in its arguments, covariant in its
    // result. This is the rule that makes `(A -> B) -> C` flip twice and
    // come back to covariant for A.
    if (ty.kind == Nk.N_TY_FN)
    {
        usz n = ty.child_count;
        for (usz i = 0; i < n; i++)
        {
            Node* c = ty.children[i];
            if (c == null) { continue; }
            if (c.kind == Nk.N_TY_CONSTRAINT)
            {
                // the wrapped return type
                for (usz j = 0; j < c.child_count; j++)
                {
                    e.scan_positions(c.children[j], sign, true, depth + 1);
                }
            }
            else
            {
                e.scan_positions(c, variance_flip(sign), false, depth + 1);
            }
        }
        return;
    }

    // A mutable pointer is invariant: you can both read and write through it.
    if (ty.kind == Nk.N_TY_PTR || ty.kind == Nk.N_TY_REF)
    {
        int inner = (ty.flags & pfront_core::NF_MUT) != 0 ? VAR_INVARIANT : sign;
        for (usz i = 0; i < ty.child_count; i++)
        {
            e.scan_positions(ty.children[i], inner, is_result, depth + 1);
        }
        return;
    }

    for (usz i = 0; i < ty.child_count; i++)
    {
        e.scan_positions(ty.children[i], sign, is_result, depth + 1);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// MATCHING — one-way unification, parameters on the left only
// ════════════════════════════════════════════════════════════════════════════
// `match_type(pattern, concrete, θ)` extends θ so that θ(pattern) = concrete.
// Only the pattern side may contain type parameters, which is what makes this
// matching rather than full unification and keeps it linear.

fn bool match_type(ParamEnv* e, Node* pat, Node* act, Subst* out, int depth)
{
    if (pat == null || act == null) { return true; }   // unknown: no constraint
    if (depth > PY_MAX_DEPTH) { return false; }

    // A bare type parameter matches anything, and binds.
    if (pat.kind == Nk.N_TY_NAME && pat.resolved != null)
    {
        if (e.find(pat.resolved) >= 0)
        {
            return out.bind(pat.resolved, act);
        }
    }

    if (pat.kind != act.kind) { return false; }

    if (pat.kind == Nk.N_TY_NAME)
    {
        if (pat.resolved != null && act.resolved != null)
        {
            return pat.resolved == act.resolved;
        }
        return pat.name_id == act.name_id;
    }

    if (pat.child_count != act.child_count) { return false; }
    for (usz i = 0; i < pat.child_count; i++)
    {
        if (!match_type(e, pat.children[i], act.children[i], out, depth + 1))
        {
            return false;
        }
    }
    return true;
}

// ════════════════════════════════════════════════════════════════════════════
// SUBSTITUTION APPLICATION — build the instantiated type
// ════════════════════════════════════════════════════════════════════════════
// Clones `ty` with θ applied. Nodes with no parameter inside are SHARED
// rather than copied: most of a signature is monomorphic, and copying it all
// would multiply arena use by the instantiation count for no benefit.

fn bool mentions_param(ParamEnv* e, Node* ty, int depth)
{
    if (ty == null || depth > PY_MAX_DEPTH) { return false; }
    if (ty.kind == Nk.N_TY_NAME && ty.resolved != null
        && e.find(ty.resolved) >= 0)
    {
        return true;
    }
    for (usz i = 0; i < ty.child_count; i++)
    {
        if (mentions_param(e, ty.children[i], depth + 1)) { return true; }
    }
    return false;
}

fn Node* apply_subst(Arena* a, ParamEnv* e, Node* ty, Subst* s, int depth)
{
    if (ty == null || depth > PY_MAX_DEPTH) { return ty; }

    if (ty.kind == Nk.N_TY_NAME && ty.resolved != null)
    {
        Node* bound = s.lookup(ty.resolved);
        if (bound != null) { return bound; }
        return ty;
    }

    // Nothing to rewrite underneath: share the subtree.
    if (!mentions_param(e, ty, 0)) { return ty; }

    Node* copy = a.node(ty.kind, ty.line, ty.col);
    if (copy == null) { return ty; }
    copy.name_id  = ty.name_id;
    copy.flags    = ty.flags | pfront_core::NF_SYNTHETIC;
    copy.resolved = ty.resolved;
    copy.p        = ty.p;
    for (usz i = 0; i < ty.child_count; i++)
    {
        Node* c = apply_subst(a, e, ty.children[i], s, depth + 1);
        a.add_child(copy, c);
    }
    return copy;
}

// ════════════════════════════════════════════════════════════════════════════
// INSTANCES
// ════════════════════════════════════════════════════════════════════════════

struct PolyInstance
{
    Node* generic;          // the polymorphic declaration
    Node* inst_type;        // its signature with θ applied — the real payoff
    Subst subst;
    usz   use_count;
    int   depth;
    bool  complete;         // every parameter was inferred
}

struct Polymorphism
{
    PolyInstance*          instances;   // heap: PY_MAX_INST * sizeof is large
    usz                    count;
    ParamEnv*              env;

    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    Arena*                 arena;
    char*                  file;

    // statistics
    usz generics_seen;
    usz calls_checked;
    usz inferred_ok;
    usz partial_infers;      // some parameter could not be determined
    usz conflicts;           // one parameter forced to two different types
    usz bound_checks;
    usz bound_failures;
    usz uninferable;         // parameter only in result position
    usz substitutions;       // type nodes actually rewritten
    usz shared_subtrees;     // monomorphic subtrees shared, not copied
    usz recursion_cutoffs;
    usz synth_types;         // literal argument types synthesised for matching
    bool overflowed;
}

fn bool Polymorphism.init(Polymorphism* py, Arena* a, pfront_core::DiagBag* d,
                          pfront_core::Interner* it, char* file)
{
    py.arena = a;
    py.diags = d;
    py.interner = it;
    py.file = file;
    py.count = 0;
    py.generics_seen = 0;
    py.calls_checked = 0;
    py.inferred_ok = 0;
    py.partial_infers = 0;
    py.conflicts = 0;
    py.bound_checks = 0;
    py.bound_failures = 0;
    py.uninferable = 0;
    py.substitutions = 0;
    py.shared_subtrees = 0;
    py.recursion_cutoffs = 0;
    py.synth_types = 0;
    py.overflowed = false;

    py.instances = (PolyInstance*)malloc(PolyInstance::size * PY_MAX_INST);
    py.env = (ParamEnv*)malloc(ParamEnv::size);
    if (py.instances == null || py.env == null) { py.destroy(); return false; }
    py.env.init();
    return true;
}

fn void Polymorphism.destroy(Polymorphism* py)
{
    if (py.instances != null) { free((void*)py.instances); py.instances = null; }
    if (py.env != null) { free((void*)py.env); py.env = null; }
}

// Find an existing instance with the same generic and the same θ.
fn int Polymorphism.find_instance(Polymorphism* py, Node* generic, Subst* s)
{
    for (usz i = 0; i < py.count; i++)
    {
        PolyInstance* pi = &py.instances[i];
        if (pi.generic != generic) { continue; }
        if (pi.subst.count != s.count) { continue; }
        bool same = true;
        for (usz k = 0; k < s.count; k++)
        {
            Node* mine = pi.subst.lookup(s.items[k].param);
            if (mine == null || !type_eq(mine, s.items[k].value, 0))
            {
                same = false;
                break;
            }
        }
        if (same) { return (int)i; }
    }
    return -1;
}

// ── Bound checking ──────────────────────────────────────────────────────────
// `T : Ord` means the chosen argument must satisfy Ord. Without a trait
// solver the honest check is structural: the bound must name something that
// resolves. Reporting "cannot verify" is better than silently claiming it.
fn bool Polymorphism.check_bounds(Polymorphism* py, ParamInfo* p, Node* actual)
{
    if (p.bound_count == 0) { return true; }
    py.bound_checks = py.bound_checks + 1;
    for (usz i = 0; i < p.bound_count; i++)
    {
        Node* b = p.bounds[i];
        if (b == null) { continue; }
        if (b.resolved == null && b.name_id != 0)
        {
            py.bound_failures = py.bound_failures + 1;
            py.diags.advisory(pfront_core::Phase.PH_RESOLVE, 3270,
                              actual == null ? 0 : actual.line,
                              actual == null ? 0 : actual.col,
                              "cannot verify this type parameter's bound",
                              py.file);
            return false;
        }
    }
    return true;
}

// The actual type of an argument expression, as a type NODE we can match
// against. Annotated expressions carry one already; literals do not — their
// type lives in the payload (`p.width` / `p.is_signed`), so synthesise it.
//
// Without this every call to a generic looked like "argument type unknown"
// and nothing was ever inferred: `identity(5i64)` could not bind `T ↦ i64`.
fn Node* Polymorphism.type_of_arg(Polymorphism* py, Node* arg)
{
    if (arg == null) { return null; }
    if (arg.type_ann != null)  { return arg.type_ann; }
    if (arg.type_slot != null) { return arg.type_slot; }

    char* name = null;
    switch (arg.kind)
    {
        case N_EXPR_INT:
            // The suffix picked the width; default is i64 (v.md §4).
            if (arg.p.width == 8)  { name = arg.p.is_signed ? "i8"  : "u8";  }
            else if (arg.p.width == 16) { name = arg.p.is_signed ? "i16" : "u16"; }
            else if (arg.p.width == 32) { name = arg.p.is_signed ? "i32" : "u32"; }
            else { name = arg.p.is_signed ? "i64" : "u64"; }
        case N_EXPR_FLOAT:
            name = arg.p.width == 32 ? "f32" : "f64";
        case N_EXPR_BOOL:   name = "bool";
        case N_EXPR_CHAR:   name = "char";
        case N_EXPR_STRING: name = "Str";
        case N_EXPR_NULL:   name = "ptr";
        case N_EXPR_UNIT:   name = "()";
        default:
            // An identifier's type is its binder's declared type, when it
            // has one. This is what lets `identity(x)` infer from a typed
            // parameter rather than only from literals.
            if (arg.kind == Nk.N_EXPR_IDENT && arg.resolved != null)
            {
                Node* d = arg.resolved;
                if (d.type_ann != null) { return d.type_ann; }
                if (d.parent != null && d.parent.type_ann != null)
                {
                    return d.parent.type_ann;
                }
            }
            return null;
    }
    if (name == null) { return null; }

    Node* ty = py.arena.node(Nk.N_TY_NAME, arg.line, arg.col);
    if (ty == null) { return null; }
    usz len = 0;
    while (name[len] != 0) { len = len + 1; }
    ty.name_id = py.interner.intern(name, len);
    ty.flags = ty.flags | pfront_core::NF_SYNTHETIC;
    py.synth_types = py.synth_types + 1;
    return ty;
}

// ── The core: infer θ at a call site ────────────────────────────────────────
fn int Polymorphism.instantiate_call(Polymorphism* py, Node* call, Node* decl,
                                     int depth)
{
    if (decl == null || call == null) { return -1; }

    py.env.init();
    py.env.collect(decl);
    if (py.env.count == 0) { return -1; }

    py.calls_checked = py.calls_checked + 1;

    // Record where each parameter appears, so an uninferable one is visible.
    if (decl.type_ann != null)
    {
        py.env.scan_positions(decl.type_ann, VAR_COVARIANT, false, 0);
    }

    // Match each declared parameter type against the actual argument type.
    Subst theta;
    theta.init();
    bool conflict = false;

    Node* sig = decl.type_ann;
    if (sig != null && sig.kind == Nk.N_TY_FN)
    {
        // A multi-argument signature is written `(A, B) -> R`, and the
        // parser represents the parameter list as ONE `ty-tuple` child, not
        // as N separate children. Pairing children positionally against the
        // call's arguments therefore matched the whole tuple against the
        // first argument, and every 2-parameter generic reported a bogus
        // conflict. Unwrap the tuple first.
        Node* params = null;
        for (usz i = 0; i < sig.child_count; i++)
        {
            Node* c = sig.children[i];
            if (c == null || c.kind == Nk.N_TY_CONSTRAINT) { continue; }
            params = c;
            break;
        }

        usz nparams = 1;
        bool tupled = params != null && params.kind == Nk.N_TY_TUPLE;
        if (tupled) { nparams = params.child_count; }

        for (usz i = 0; i < nparams; i++)
        {
            Node* pty = tupled ? params.children[i] : params;
            usz argi = i + 1;              // children[0] of a call is the callee
            if (pty == null || argi >= call.child_count) { break; }
            Node* arg = call.children[argi];
            if (arg == null) { continue; }
            Node* aty = py.type_of_arg(arg);
            if (aty == null) { continue; }
            if (!match_type(py.env, pty, aty, &theta, 0))
            {
                conflict = true;
            }
        }
    }

    if (conflict)
    {
        py.conflicts = py.conflicts + 1;
        py.diags.advisory_hint(pfront_core::Phase.PH_RESOLVE, 3271,
                               call.line, call.col,
                               "one type parameter is used at two different types",
                               "the first binding is kept",
                               py.file);
    }

    // A parameter that appears only in the RESULT cannot be inferred from the
    // arguments — the call site must annotate it. Worth saying plainly.
    bool complete = true;
    for (usz i = 0; i < py.env.count; i++)
    {
        ParamInfo* p = &py.env.params[i];
        if (theta.lookup(p.decl) != null)
        {
            py.check_bounds(p, theta.lookup(p.decl));
            continue;
        }
        complete = false;
        if (p.in_result && !p.in_args)
        {
            py.uninferable = py.uninferable + 1;
            py.diags.advisory_hint(pfront_core::Phase.PH_RESOLVE, 3272,
                                   call.line, call.col,
                                   "this type parameter appears only in the result",
                                   "it cannot be inferred from the arguments",
                                   py.file);
        }
    }
    if (complete) { py.inferred_ok = py.inferred_ok + 1; }
    else          { py.partial_infers = py.partial_infers + 1; }

    // Reuse an identical instance rather than minting a second one.
    int existing = py.find_instance(decl, &theta);
    if (existing >= 0)
    {
        py.instances[existing].use_count = py.instances[existing].use_count + 1;
        return existing;
    }

    if (depth > PY_MAX_INST_DEPTH)
    {
        py.recursion_cutoffs = py.recursion_cutoffs + 1;
        py.diags.advisory_hint(pfront_core::Phase.PH_RESOLVE, 3273,
                               call.line, call.col,
                               "generic instantiation nests very deeply",
                               "a type parameter may be growing on each call",
                               py.file);
        return -1;
    }

    if (py.count >= PY_MAX_INST) { py.overflowed = true; return -1; }

    usz id = py.count;
    py.count = py.count + 1;
    PolyInstance* pi = &py.instances[id];
    pi.generic = decl;
    pi.subst = theta;
    pi.use_count = 1;
    pi.depth = depth;
    pi.complete = complete;

    // THE PAYOFF: the signature with θ applied. This is a real monomorphic
    // type, not a mangled name — the middle end can consume it directly.
    if (sig != null && theta.count > 0)
    {
        usz before = py.arena.node_count;
        pi.inst_type = apply_subst(py.arena, py.env, sig, &theta, 0);
        usz made = py.arena.node_count - before;
        py.substitutions = py.substitutions + made;
        if (made == 0) { py.shared_subtrees = py.shared_subtrees + 1; }
    }
    else
    {
        pi.inst_type = sig;
    }

    // Attach the instantiated type to the call so later passes can read it
    // without redoing the inference.
    if (pi.inst_type != null && call.type_slot == null)
    {
        call.type_slot = pi.inst_type;
    }
    return (int)id;
}

// ── Walk ────────────────────────────────────────────────────────────────────
fn bool decl_is_generic(Node* d)
{
    if (d == null) { return false; }
    for (usz i = 0; i < d.child_count; i++)
    {
        Node* c = d.children[i];
        if (c != null && c.kind == Nk.N_DECL_TYPEPARAM) { return true; }
    }
    return false;
}

fn void Polymorphism.walk(Polymorphism* py, Node* n, int depth)
{
    if (n == null || depth > PY_MAX_DEPTH) { return; }

    if (pfront_core::is_decl(n.kind) && decl_is_generic(n))
    {
        py.generics_seen = py.generics_seen + 1;
    }

    if (n.kind == Nk.N_EXPR_CALL && n.child_count > 0)
    {
        Node* callee = n.children[0];
        if (callee != null && callee.resolved != null
            && decl_is_generic(callee.resolved))
        {
            py.instantiate_call(n, callee.resolved, depth);
        }
    }

    // A method call resolves to its declaration directly rather than through
    // a callee child.
    if (n.kind == Nk.N_EXPR_METHOD && n.resolved != null
        && decl_is_generic(n.resolved))
    {
        py.instantiate_call(n, n.resolved, depth);
    }

    for (usz i = 0; i < n.child_count; i++)
    {
        py.walk(n.children[i], depth + 1);
    }
}

fn void Polymorphism.run(Polymorphism* py, Node* root)
{
    if (root == null) { return; }
    py.walk(root, 0);
}

fn void Polymorphism.report(Polymorphism* py)
{
    if (py.generics_seen == 0 && py.calls_checked == 0) { return; }
    printf("  polymorphism     : %d generics, %d calls, %d instances\n",
           (int)py.generics_seen, (int)py.calls_checked, (int)py.count);
    printf("  inference        : %d fully inferred, %d partial\n",
           (int)py.inferred_ok, (int)py.partial_infers);
    if (py.substitutions > 0 || py.shared_subtrees > 0)
    {
        printf("  substitution     : %d nodes rewritten, %d subtrees shared\n",
               (int)py.substitutions, (int)py.shared_subtrees);
    }
    if (py.bound_checks > 0)
    {
        printf("  bounds           : %d checked, %d unverifiable\n",
               (int)py.bound_checks, (int)py.bound_failures);
    }
    if (py.conflicts > 0 || py.uninferable > 0)
    {
        printf("  problems         : %d conflicts, %d uninferable\n",
               (int)py.conflicts, (int)py.uninferable);
    }
    if (py.recursion_cutoffs > 0)
    {
        printf("  recursion        : %d instantiations cut off\n",
               (int)py.recursion_cutoffs);
    }
    if (py.overflowed)
    {
        printf("  WARNING          : instance table full; results partial\n");
    }
}
