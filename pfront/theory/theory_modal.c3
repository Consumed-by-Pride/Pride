// ============================================================================
// theory_modal.c3 — scoped effects, continuation algebra, UB, subtyping
// ----------------------------------------------------------------------------
// (part 15)
//
// Four related semantic layers that all concern *what a program may do*, as
// opposed to what shape its terms have.
//
// PART A — HIGHER-ORDER & SCOPED EFFECTS
//   An ordinary algebraic effect operation takes values and returns a value.
//   A *scoped* operation takes a COMPUTATION: `catch`, `bracket`, `local`,
//   `nursery`, `with_timeout` all delimit a region rather than occurring at a
//   point. That distinction is why they cannot be encoded as plain operations:
//   their continuation splits into an inner part (k_in, inside the scope) and
//   an outer part (k_out, after it).
//
// PART B — CONTINUATION-TREE ALGEBRA
//   Scoped operations are represented as an explicit tree
//
//       T ::= Leaf(e) | Node(op, k_in, k_out) | Seq(T1,T2)
//           | Fmap(f, T) | Fuse(T_in, T_out) | Abort(e)
//
//   and normalised by functorial rewrite rules:
//
//       Node(op, k_in, Id)          ↦ k_in            (identity elimination)
//       Fmap(f, Node(op, ki, ko))   ↦ Node(op, Fmap(f,ki), ko)   (fusion)
//       Fuse(Fmap(f, ki), ko)       ↦ Fmap(f, Fuse(ki, ko))
//       Node(op, Abort(e), ko)      ↦ Abort(e)        (dead-scope pruning)
//       Seq(Seq(T1,T2), T3)         ↦ Seq(T1, Seq(T2,T3))  (associativity)
//
//   When a tree normalises to one whose k_out is Id, the whole scope lowers to
//   direct calls — no prompt installation, no stack slicing at runtime.
//
// PART C — EXPLICIT UNDEFINED BEHAVIOUR
//   `ub! "reason"` is a *promise*, not an escape hatch: it asserts the branch
//   is unreachable. This tracks where UB is claimed, proves the claims are
//   inside `unsafe`, and propagates the UB effect so callers know.
//
// PART D — SEMANTIC SUBTYPING
//   Types are read as sets of values, so subtyping is set inclusion computed
//   structurally. Unions and intersections then behave as they should:
//   `A ∪ B <: C` exactly when `A <: C` and `B <: C`. Purely syntactic
//   comparison cannot get that right.
// ============================================================================

module theory_modal;

import pfront_lex;
import pfront_core;
import theory_term;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz CT_POOL         = 16384;
const int CT_REWRITE_CAP  = 25000;
const int MODAL_MAX_DEPTH = 400;
const usz MAX_SCOPED_OPS  = 512;
const usz SUBTYPE_MEMO    = 4096;

// ════════════════════════════════════════════════════════════════════════════
// PART A — SCOPED EFFECT REGISTRY
// ════════════════════════════════════════════════════════════════════════════
enum OpShape : int
{
    OP_ALGEBRAIC,    // value -> value; continuation is untouched
    OP_SCOPED,       // takes a computation; splits the continuation
    OP_HIGHER_ORDER  // takes a function that itself performs effects
}

struct ScopedOp
{
    uint    name_id;
    uint    effect_name;
    OpShape shape;
    Node*   decl;
    usz     arity;
    bool    resumes_once;      // linear continuation (bracket, with_timeout)
    bool    may_abort;         // can discard k_in (catch)
    usz     use_count;
}

struct ScopedRegistry
{
    ScopedOp[MAX_SCOPED_OPS] ops;
    usz                      count;
    pfront_core::DiagBag*    diags;
    pfront_core::Interner*   interner;
    char*                    file;

    usz scoped_count;
    usz higher_order_count;
    usz misuse;
}

fn void ScopedRegistry.init(ScopedRegistry* r, pfront_core::DiagBag* d,
                            pfront_core::Interner* it, char* file)
{
    r.count = 0;
    r.diags = d;
    r.interner = it;
    r.file = file;
    r.scoped_count = 0;
    r.higher_order_count = 0;
    r.misuse = 0;
}

// Classify an operation by its declared signature. An operation whose
// parameter is itself a function type takes a computation, which is what makes
// it scoped rather than algebraic.
fn OpShape classify_op(Node* op_decl)
{
    if (op_decl == null) { return OpShape.OP_ALGEBRAIC; }
    for (usz i = 0; i < op_decl.child_count; i++)
    {
        Node* c = op_decl.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.N_TY_FN) { return OpShape.OP_SCOPED; }
        if (c.kind == Nk.N_TY_TUPLE)
        {
            for (usz k = 0; k < c.child_count; k++)
            {
                Node* e = c.children[k];
                if (e != null && e.kind == Nk.N_TY_FN) { return OpShape.OP_HIGHER_ORDER; }
            }
        }
    }
    return OpShape.OP_ALGEBRAIC;
}

// Well-known scoped operations get their control properties from their name,
// because their semantics are fixed by the runtime rather than the signature.
fn void classify_by_name(ScopedOp* op, char* name, usz len)
{
    op.resumes_once = false;
    op.may_abort = false;
    if (name == null) { return; }
    if (len == 5 && name[0] == 'c' && name[1] == 'a' && name[2] == 't')
    {
        op.may_abort = true;          // catch discards the inner continuation
        op.shape = OpShape.OP_SCOPED;
    }
    if (len == 7 && name[0] == 'b' && name[1] == 'r')
    {
        op.resumes_once = true;       // bracket: acquire/release is linear
        op.shape = OpShape.OP_SCOPED;
    }
    if (len == 12 && name[0] == 'w' && name[1] == 'i')
    {
        op.resumes_once = true;       // with_timeout
        op.shape = OpShape.OP_SCOPED;
    }
    if (len == 7 && name[0] == 'n' && name[1] == 'u')
    {
        op.shape = OpShape.OP_SCOPED; // nursery
    }
}

fn void ScopedRegistry.register_effects(ScopedRegistry* r, Node* n, int depth)
{
    if (n == null || depth > 200) { return; }
    if (n.kind == Nk.N_DECL_EFFECT)
    {
        for (usz i = 0; i < n.child_count; i++)
        {
            Node* op = n.children[i];
            if (op == null || op.kind != Nk.N_DECL_EFFECT_OP) { continue; }
            if (r.count >= MAX_SCOPED_OPS) { break; }
            ScopedOp* so = &r.ops[r.count];
            so.name_id = op.name_id;
            so.effect_name = n.name_id;
            so.shape = classify_op(op);
            so.decl = op;
            so.arity = op.child_count;
            so.use_count = 0;
            classify_by_name(so, op.p.sptr, op.p.slen);
            if (so.shape == OpShape.OP_SCOPED) { r.scoped_count = r.scoped_count + 1; }
            if (so.shape == OpShape.OP_HIGHER_ORDER)
            {
                r.higher_order_count = r.higher_order_count + 1;
            }
            r.count = r.count + 1;
        }
    }
    for (usz i = 0; i < n.child_count; i++) { r.register_effects(n.children[i], depth + 1); }
}

fn ScopedOp* ScopedRegistry.find(ScopedRegistry* r, uint name)
{
    for (usz i = 0; i < r.count; i++)
    {
        if (r.ops[i].name_id == name) { return &r.ops[i]; }
    }
    return null;
}

// A scoped operation whose continuation is linear must not be resumed twice.
// Two `resume` calls in one handler arm is the classic violation.
fn void ScopedRegistry.check_linearity(ScopedRegistry* r, Node* arm, int depth)
{
    if (arm == null) { return; }
    ScopedOp* op = r.find(arm.name_id);
    if (op == null || !op.resumes_once) { return; }
    usz resumes = count_resumes(arm, 0);
    if (resumes > 1)
    {
        r.misuse = r.misuse + 1;
        r.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3220, arm.line, arm.col,
                           "scoped operation resumed more than once",
                           "this operation's continuation is linear: resume it at most once",
                           r.file);
    }
}

fn usz count_resumes(Node* n, int depth)
{
    if (n == null || depth > MODAL_MAX_DEPTH) { return 0; }
    usz total = n.kind == Nk.N_EXPR_RESUME ? 1 : 0;
    for (usz i = 0; i < n.child_count; i++) { total = total + count_resumes(n.children[i], depth + 1); }
    return total;
}

fn void ScopedRegistry.report(ScopedRegistry* r)
{
    printf("  effect ops       : %d total (%d scoped, %d higher-order)\n",
           (int)r.count, (int)r.scoped_count, (int)r.higher_order_count);
    if (r.misuse > 0)
    {
        printf("  effect misuse    : %d linearity violations\n", (int)r.misuse);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// PART B — CONTINUATION TREE ALGEBRA
// ════════════════════════════════════════════════════════════════════════════
enum CtKind : int
{
    CT_LEAF,      // a pure expression
    CT_ID,        // the identity continuation
    CT_NODE,      // Node(op, k_in, k_out)
    CT_SEQ,       // Seq(T1, T2)
    CT_FMAP,      // Fmap(f, T)
    CT_FUSE,      // Fuse(T_in, T_out)
    CT_ABORT      // Abort(e): control leaves, nothing after runs
}

struct CtNode
{
    CtKind kind;
    int    a;        // first child index (-1 when absent)
    int    b;        // second child index
    Node*  payload;  // expression / operation / function
    uint   op_name;
    bool   normalised;
}

struct ContTree
{
    CtNode[CT_POOL] pool;
    usz             count;
    int             root;

    usz rewrites;
    usz identity_elim;
    usz fusions;
    usz dead_scope;
    usz assoc;
    int fuel;
    usz lowered_direct;    // scopes that became zero-cost
}

fn void ContTree.init(ContTree* t)
{
    t.count = 0;
    t.root = -1;
    t.rewrites = 0;
    t.identity_elim = 0;
    t.fusions = 0;
    t.dead_scope = 0;
    t.assoc = 0;
    t.fuel = CT_REWRITE_CAP;
    t.lowered_direct = 0;
}

fn int ContTree.mk(ContTree* t, CtKind k, int a, int b, Node* payload, uint op)
{
    if (t.count >= CT_POOL) { return -1; }
    int id = (int)t.count;
    t.count = t.count + 1;
    CtNode* n = &t.pool[id];
    n.kind = k;
    n.a = a;
    n.b = b;
    n.payload = payload;
    n.op_name = op;
    n.normalised = false;
    return id;
}

// Build a continuation tree from an effect-handling expression.
fn int ContTree.build(ContTree* t, Node* e, ScopedRegistry* reg, int depth)
{
    if (e == null || depth > MODAL_MAX_DEPTH) { return t.mk(CtKind.CT_ID, -1, -1, null, 0); }

    switch (e.kind)
    {
        case N_EXPR_HANDLE:
        {
            // handle comp | arms  →  Node(op, k_in = comp, k_out = arms)
            int k_in = t.build(e.child(0), reg, depth + 1);
            int k_out = t.mk(CtKind.CT_ID, -1, -1, null, 0);
            for (usz i = 1; i < e.child_count; i++)
            {
                Node* arm = e.children[i];
                if (arm == null) { continue; }
                int arm_t = t.build(arm.child(arm.child_count - 1), reg, depth + 1);
                k_out = t.mk(CtKind.CT_SEQ, k_out, arm_t, arm, arm.name_id);
            }
            return t.mk(CtKind.CT_NODE, k_in, k_out, e, e.name_id);
        }

        case N_EXPR_PERFORM:
        {
            int k_in = t.mk(CtKind.CT_LEAF, -1, -1, e, e.name_id);
            int k_out = t.mk(CtKind.CT_ID, -1, -1, null, 0);
            return t.mk(CtKind.CT_NODE, k_in, k_out, e, e.name_id);
        }

        case N_EXPR_UNREACHABLE:
        case N_EXPR_TRAP:
            return t.mk(CtKind.CT_ABORT, -1, -1, e, 0);

        case N_BLOCK:
        {
            int acc = -1;
            for (usz i = 0; i < e.child_count; i++)
            {
                int sub = t.build(e.children[i], reg, depth + 1);
                acc = acc < 0 ? sub : t.mk(CtKind.CT_SEQ, acc, sub, null, 0);
            }
            return acc < 0 ? t.mk(CtKind.CT_ID, -1, -1, null, 0) : acc;
        }

        default:
            return t.mk(CtKind.CT_LEAF, -1, -1, e, 0);
    }
}

// One normalisation step. Returns the (possibly new) node index.
fn int ContTree.step(ContTree* t, int id, int depth)
{
    if (id < 0 || depth > MODAL_MAX_DEPTH || t.fuel <= 0) { return id; }
    CtNode* n = &t.pool[id];

    // Normalise children first.
    if (n.a >= 0) { n.a = t.step(n.a, depth + 1); }
    if (n.b >= 0) { n.b = t.step(n.b, depth + 1); }

    switch (n.kind)
    {
        case CT_NODE:
        {
            // Dead-scope pruning: an aborting inner continuation makes the
            // whole node abort — nothing after the scope can run.
            if (n.a >= 0 && t.pool[n.a].kind == CtKind.CT_ABORT)
            {
                t.dead_scope = t.dead_scope + 1;
                t.rewrites = t.rewrites + 1;
                t.fuel = t.fuel - 1;
                return n.a;
            }
            // Identity elimination: a scope with a trivial outer continuation
            // is just its body, so the prompt can be dropped entirely.
            if (n.b >= 0 && t.pool[n.b].kind == CtKind.CT_ID)
            {
                t.identity_elim = t.identity_elim + 1;
                t.rewrites = t.rewrites + 1;
                t.lowered_direct = t.lowered_direct + 1;
                t.fuel = t.fuel - 1;
                return n.a;
            }
        }

        case CT_FMAP:
        {
            // Functorial fusion: push the map inside the node's inner
            // continuation so the two traversals become one.
            if (n.b >= 0 && t.pool[n.b].kind == CtKind.CT_NODE)
            {
                CtNode* inner = &t.pool[n.b];
                int mapped = t.mk(CtKind.CT_FMAP, n.a, inner.a, n.payload, n.op_name);
                t.fusions = t.fusions + 1;
                t.rewrites = t.rewrites + 1;
                t.fuel = t.fuel - 1;
                return t.mk(CtKind.CT_NODE, mapped, inner.b, inner.payload, inner.op_name);
            }
        }

        case CT_FUSE:
        {
            // Structured fusion: hoist a map out of the fused pair.
            if (n.a >= 0 && t.pool[n.a].kind == CtKind.CT_FMAP)
            {
                CtNode* fm = &t.pool[n.a];
                int fused = t.mk(CtKind.CT_FUSE, fm.b, n.b, null, 0);
                t.fusions = t.fusions + 1;
                t.rewrites = t.rewrites + 1;
                t.fuel = t.fuel - 1;
                return t.mk(CtKind.CT_FMAP, fm.a, fused, fm.payload, fm.op_name);
            }
        }

        case CT_SEQ:
        {
            // Right-associate so sequential composition has a canonical shape.
            if (n.a >= 0 && t.pool[n.a].kind == CtKind.CT_SEQ)
            {
                CtNode* left = &t.pool[n.a];
                int rest = t.mk(CtKind.CT_SEQ, left.b, n.b, null, 0);
                t.assoc = t.assoc + 1;
                t.rewrites = t.rewrites + 1;
                t.fuel = t.fuel - 1;
                return t.mk(CtKind.CT_SEQ, left.a, rest, null, 0);
            }
            // An aborting left branch makes the sequence abort.
            if (n.a >= 0 && t.pool[n.a].kind == CtKind.CT_ABORT)
            {
                t.dead_scope = t.dead_scope + 1;
                t.rewrites = t.rewrites + 1;
                t.fuel = t.fuel - 1;
                return n.a;
            }
            // Identity on either side is absorbed.
            if (n.a >= 0 && t.pool[n.a].kind == CtKind.CT_ID) { return n.b; }
            if (n.b >= 0 && t.pool[n.b].kind == CtKind.CT_ID) { return n.a; }
        }

        default:
            break;
    }
    n.normalised = true;
    return id;
}

fn void ContTree.normalise(ContTree* t, int max_rounds)
{
    for (int i = 0; i < max_rounds; i++)
    {
        usz before = t.rewrites;
        t.root = t.step(t.root, 0);
        if (t.rewrites == before) { break; }
        if (t.fuel <= 0) { break; }
    }
}

fn void ContTree.report(ContTree* t)
{
    printf("  cont-tree        : %d nodes, %d rewrites\n", (int)t.count, (int)t.rewrites);
    printf("  cont-tree rules  : %d identity, %d fusion, %d dead-scope, %d assoc\n",
           (int)t.identity_elim, (int)t.fusions, (int)t.dead_scope, (int)t.assoc);
    printf("  zero-cost scopes : %d lowered to direct calls\n", (int)t.lowered_direct);
}

// ════════════════════════════════════════════════════════════════════════════
// PART C — EXPLICIT UNDEFINED BEHAVIOUR
// ════════════════════════════════════════════════════════════════════════════
struct UbTracker
{
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;

    usz ub_sites;
    usz ub_outside_unsafe;
    usz assumes;
    usz unreachable_claims;
    usz undocumented;      // `ub!` with no explanatory string
    int unsafe_depth;
}

fn void UbTracker.init(UbTracker* u, pfront_core::DiagBag* d,
                       pfront_core::Interner* it, char* file)
{
    u.diags = d;
    u.interner = it;
    u.file = file;
    u.ub_sites = 0;
    u.ub_outside_unsafe = 0;
    u.assumes = 0;
    u.unreachable_claims = 0;
    u.undocumented = 0;
    u.unsafe_depth = 0;
}

fn void UbTracker.walk(UbTracker* u, Node* n, int depth)
{
    if (n == null || depth > MODAL_MAX_DEPTH) { return; }

    switch (n.kind)
    {
        case N_EXPR_UNSAFE:
        {
            u.unsafe_depth = u.unsafe_depth + 1;
            for (usz i = 0; i < n.child_count; i++) { u.walk(n.children[i], depth + 1); }
            u.unsafe_depth = u.unsafe_depth - 1;
            return;
        }
        case N_EXPR_UB:
        {
            u.ub_sites = u.ub_sites + 1;
            // Declaring UB is a promise the compiler may exploit; it belongs
            // inside `unsafe` where the reader expects such promises.
            if (u.unsafe_depth == 0)
            {
                u.ub_outside_unsafe = u.ub_outside_unsafe + 1;
                u.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3230, n.line, n.col,
                                   "`ub!` outside an `unsafe` block",
                                   "wrap it in `unsafe`: declaring UB is a proof obligation",
                                   u.file);
            }
            // An undocumented UB claim cannot be reviewed.
            if (n.child_count == 0)
            {
                u.undocumented = u.undocumented + 1;
                u.diags.warn(pfront_core::Phase.PH_RESOLVE, 4050, n.line, n.col,
                             "`ub!` has no explanation string", u.file);
            }
        }
        case N_EXPR_ASSUME:
        {
            u.assumes = u.assumes + 1;
            if (u.unsafe_depth == 0)
            {
                u.diags.warn(pfront_core::Phase.PH_RESOLVE, 4051, n.line, n.col,
                             "`assume` outside `unsafe`: a false assumption is UB",
                             u.file);
            }
        }
        case N_EXPR_UNREACHABLE:
            u.unreachable_claims = u.unreachable_claims + 1;
        default:
            break;
    }
    for (usz i = 0; i < n.child_count; i++) { u.walk(n.children[i], depth + 1); }
}

fn void UbTracker.report(UbTracker* u)
{
    printf("  explicit UB      : %d `ub!` sites (%d outside unsafe, %d undocumented)\n",
           (int)u.ub_sites, (int)u.ub_outside_unsafe, (int)u.undocumented);
    printf("  assumptions      : %d assume, %d unreachable claims\n",
           (int)u.assumes, (int)u.unreachable_claims);
}

// ════════════════════════════════════════════════════════════════════════════
// PART D — SEMANTIC SUBTYPING
// ════════════════════════════════════════════════════════════════════════════
// Types denote sets of values; subtyping is inclusion. Computing it
// structurally is what makes unions and intersections behave correctly:
//
//     A ∪ B <: C   iff   A <: C  and  B <: C
//     A <: B ∩ C   iff   A <: B  and  A <: C
//     A <: B ∪ C   if    A <: B  or   A <: C
//     ⊥ <: A       always      (empty set)
//
// A syntactic comparison gets every one of these wrong.
struct SubtypeCache
{
    Node*[SUBTYPE_MEMO] lhs;
    Node*[SUBTYPE_MEMO] rhs;
    bool[SUBTYPE_MEMO]  result;
    usz                 count;
    usz                 hits;
    usz                 queries;
}

fn void SubtypeCache.init(SubtypeCache* c)
{
    c.count = 0;
    c.hits = 0;
    c.queries = 0;
}

fn bool SubtypeCache.get(SubtypeCache* c, Node* a, Node* b, bool* out)
{
    for (usz i = 0; i < c.count; i++)
    {
        if (c.lhs[i] == a && c.rhs[i] == b) { *out = c.result[i]; c.hits = c.hits + 1; return true; }
    }
    return false;
}

fn void SubtypeCache.put(SubtypeCache* c, Node* a, Node* b, bool r)
{
    if (c.count >= SUBTYPE_MEMO) { return; }
    c.lhs[c.count] = a;
    c.rhs[c.count] = b;
    c.result[c.count] = r;
    c.count = c.count + 1;
}

fn bool is_bottom(Node* t)
{
    return t != null && t.kind == Nk.N_TY_BOTTOM;
}

// Structural subtyping with union/intersection distribution.
fn bool subtype(SubtypeCache* c, Node* a, Node* b, int depth)
{
    if (a == null || b == null) { return false; }
    if (a == b) { return true; }
    if (depth > 64) { return false; }
    c.queries = c.queries + 1;

    bool cached = false;
    if (c.get(a, b, &cached)) { return cached; }

    bool result = subtype_uncached(c, a, b, depth);
    c.put(a, b, result);
    return result;
}

fn bool subtype_uncached(SubtypeCache* c, Node* a, Node* b, int depth)
{
    // Bottom is the empty set: included in everything.
    if (is_bottom(a)) { return true; }
    // `_` (inference hole) is compatible in both directions.
    if (a.kind == Nk.N_TY_INFER || b.kind == Nk.N_TY_INFER) { return true; }

    // Left union: every member must be included.
    if (a.kind == Nk.N_TY_UNION)
    {
        for (usz i = 0; i < a.child_count; i++)
        {
            if (!subtype(c, a.children[i], b, depth + 1)) { return false; }
        }
        return true;
    }
    // Right intersection: must be included in every member.
    if (b.kind == Nk.N_TY_INTERSECT)
    {
        for (usz i = 0; i < b.child_count; i++)
        {
            if (!subtype(c, a, b.children[i], depth + 1)) { return false; }
        }
        return true;
    }
    // Right union: inclusion in any member suffices.
    if (b.kind == Nk.N_TY_UNION)
    {
        for (usz i = 0; i < b.child_count; i++)
        {
            if (subtype(c, a, b.children[i], depth + 1)) { return true; }
        }
        return false;
    }
    // Left intersection: any member being included suffices.
    if (a.kind == Nk.N_TY_INTERSECT)
    {
        for (usz i = 0; i < a.child_count; i++)
        {
            if (subtype(c, a.children[i], b, depth + 1)) { return true; }
        }
        return false;
    }
    // Negation: ¬A <: ¬B exactly when B <: A (contravariant).
    if (a.kind == Nk.N_TY_NEGATION && b.kind == Nk.N_TY_NEGATION)
    {
        return subtype(c, b.child(0), a.child(0), depth + 1);
    }

    if (a.kind != b.kind) { return false; }

    switch (a.kind)
    {
        case N_TY_NAME:
            return a.name_id == b.name_id
                || (a.resolved != null && a.resolved == b.resolved);
        case N_TY_PTR:
        case N_TY_REF:
        {
            // Pointers are INVARIANT in their referent: a `*Derived` is not a
            // `*Base`, because writing through it would break the invariant.
            if (!subtype(c, a.child(0), b.child(0), depth + 1)) { return false; }
            if (!subtype(c, b.child(0), a.child(0), depth + 1)) { return false; }
            // A mutable pointer may be used where an immutable one is wanted.
            bool a_mut = (a.flags & pfront_core::NF_MUT) != 0;
            bool b_mut = (b.flags & pfront_core::NF_MUT) != 0;
            if (b_mut && !a_mut) { return false; }
            return true;
        }
        case N_TY_SLICE:
            return subtype(c, a.child(0), b.child(0), depth + 1);
        case N_TY_ARRAY:
        {
            Node* al = a.child(1);
            Node* bl = b.child(1);
            if (al != null && bl != null && al.p.ival != bl.p.ival) { return false; }
            return subtype(c, a.child(0), b.child(0), depth + 1);
        }
        case N_TY_TUPLE:
        {
            if (a.child_count != b.child_count) { return false; }
            for (usz i = 0; i < a.child_count; i++)
            {
                if (!subtype(c, a.children[i], b.children[i], depth + 1)) { return false; }
            }
            return true;
        }
        case N_TY_FN:
        {
            // Functions: CONTRAVARIANT in parameters, COVARIANT in the result.
            // Getting the direction backwards is the classic unsoundness.
            if (a.child_count == 0 || b.child_count == 0) { return false; }
            if (!subtype(c, b.children[0], a.children[0], depth + 1)) { return false; }
            Node* ar = a.children[a.child_count - 1];
            Node* br = b.children[b.child_count - 1];
            return subtype(c, ar, br, depth + 1);
        }
        default:
            return theory_term::term_eq(a, b, 0);
    }
}

// The least upper bound of two types: their union, simplified when one side
// already contains the other.
fn Node* join_types(Arena* ar, SubtypeCache* c, Node* a, Node* b)
{
    if (a == null) { return b; }
    if (b == null) { return a; }
    if (subtype(c, a, b, 0)) { return b; }
    if (subtype(c, b, a, 0)) { return a; }
    Node* u = ar.node(Nk.N_TY_UNION, a.line, a.col);
    if (u == null) { return a; }
    ar.add_child(u, a);
    ar.add_child(u, b);
    return u;
}

// The greatest lower bound: their intersection.
fn Node* meet_types(Arena* ar, SubtypeCache* c, Node* a, Node* b)
{
    if (a == null) { return b; }
    if (b == null) { return a; }
    if (subtype(c, a, b, 0)) { return a; }
    if (subtype(c, b, a, 0)) { return b; }
    Node* i = ar.node(Nk.N_TY_INTERSECT, a.line, a.col);
    if (i == null) { return a; }
    ar.add_child(i, a);
    ar.add_child(i, b);
    return i;
}

fn void SubtypeCache.report(SubtypeCache* c)
{
    printf("  subtyping        : %d queries, %d cached (%d entries)\n",
           (int)c.queries, (int)c.hits, (int)c.count);
}
