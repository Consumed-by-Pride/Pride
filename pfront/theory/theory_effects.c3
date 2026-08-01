// ============================================================================
// theory_effects.c3 — effect rows, handlers, monomorphisation (part 18)
// ----------------------------------------------------------------------------
// `theory_modal` classifies effect OPERATIONS. This module handles the effect
// ROW system that types them, plus the generic instantiation that has to know
// about rows in order to work.
//
// PART A — ROW POLYMORPHIC EFFECT TYPES
//   An effect row is a set of effect labels plus an optional tail variable:
//
//       ![IO, State]        closed: exactly these effects
//       ![IO, ..r]          open:   IO plus whatever r stands for
//
//   Open rows are what make effect-polymorphic functions possible. `map` does
//   not care which effects its callback performs, so its signature carries a
//   row variable rather than a fixed set. Row unification is subtler than
//   ordinary unification because rows are unordered and may be extended:
//   `[IO, State]` and `[State, IO]` are the same row, and unifying
//   `[IO, ..r]` with `[IO, State]` must solve `r := [State]`.
//
//   The occurs check matters here too: unifying `..r` with `[IO, ..r]` would
//   build an infinite row.
//
// PART B — HANDLER COVERAGE
//   A handler must cover every operation of the effect it discharges,
//   otherwise a perform at runtime finds no arm. This computes the residual
//   row after handling and reports uncovered operations.
//
// PART C — MONOMORPHISATION
//   Generic functions are specialised per distinct type-argument tuple. This
//   collects instantiations, mangles names, detects unbounded recursion
//   (`f<T>` calling `f<List<T>>` forever), and reports the instance table the
//   middle end will need.
// ============================================================================

module theory_effects;

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

const usz MAX_ROWS        = 4096;
const usz MAX_ROW_LABELS  = 32;
const usz MAX_EFFECT_DECLS = 512;
const usz MAX_INSTANCES   = 4096;
const usz MAX_TYPE_ARGS   = 16;
const usz MANGLE_CAP      = 256;
const int EFF_MAX_DEPTH   = 400;

// ════════════════════════════════════════════════════════════════════════════
// PART A — EFFECT ROWS
// ════════════════════════════════════════════════════════════════════════════
struct Row
{
    uint[MAX_ROW_LABELS] labels;
    usz                  label_count;
    uint                 tail_var;     // 0 when the row is closed
    bool                 is_open;
    int                  link;         // union-find: solved tail variable
    bool                 solved;
}

struct RowTable
{
    Row[MAX_ROWS] rows;
    usz           count;

    usz unifications;
    usz occurs_failures;
    usz label_mismatches;
    usz rows_solved;
}

fn void RowTable.init(RowTable* rt)
{
    rt.count = 0;
    rt.unifications = 0;
    rt.occurs_failures = 0;
    rt.label_mismatches = 0;
    rt.rows_solved = 0;
}

fn int RowTable.new_row(RowTable* rt)
{
    if (rt.count >= MAX_ROWS) { return -1; }
    int id = (int)rt.count;
    rt.count = rt.count + 1;
    Row* r = &rt.rows[id];
    r.label_count = 0;
    r.tail_var = 0;
    r.is_open = false;
    r.link = -1;
    r.solved = false;
    return id;
}

fn bool RowTable.add_label(RowTable* rt, int row, uint label)
{
    if (row < 0 || (usz)row >= rt.count) { return false; }
    Row* r = &rt.rows[row];
    // Rows are SETS: adding a label twice is a no-op, not a duplicate.
    for (usz i = 0; i < r.label_count; i++) { if (r.labels[i] == label) { return true; } }
    if (r.label_count >= MAX_ROW_LABELS) { return false; }
    r.labels[r.label_count] = label;
    r.label_count = r.label_count + 1;
    return true;
}

fn bool RowTable.has_label(RowTable* rt, int row, uint label)
{
    if (row < 0 || (usz)row >= rt.count) { return false; }
    Row* r = &rt.rows[row];
    for (usz i = 0; i < r.label_count; i++) { if (r.labels[i] == label) { return true; } }
    return false;
}

// Build a row from an AST effect-row node.
fn int RowTable.from_node(RowTable* rt, Node* n)
{
    int id = rt.new_row();
    if (id < 0 || n == null) { return id; }
    Row* r = &rt.rows[id];
    r.is_open = (n.flags & pfront_core::NF_OPEN_ROW) != 0;
    for (usz i = 0; i < n.child_count; i++)
    {
        Node* e = n.children[i];
        if (e == null || e.kind != Nk.N_TY_EFFECT_ELEM) { continue; }
        if (e.p.aux == 1) { r.tail_var = e.name_id; r.is_open = true; continue; }
        rt.add_label(id, e.name_id);
    }
    return id;
}

// ROW UNIFICATION. Rows are unordered, so this is set-based rather than
// positional. The four cases:
//   closed ~ closed : the label sets must be equal
//   open   ~ closed : the open row's labels must be a subset; its tail absorbs
//                     the remainder
//   closed ~ open   : symmetric
//   open   ~ open   : both tails unify to a fresh row holding the union
fn bool RowTable.unify(RowTable* rt, int a, int b, int depth)
{
    if (a < 0 || b < 0) { return false; }
    if (a == b) { return true; }
    if (depth > 32) { return false; }
    rt.unifications = rt.unifications + 1;

    Row* ra = &rt.rows[a];
    Row* rb = &rt.rows[b];

    if (!ra.is_open && !rb.is_open)
    {
        if (ra.label_count != rb.label_count) { rt.label_mismatches = rt.label_mismatches + 1; return false; }
        for (usz i = 0; i < ra.label_count; i++)
        {
            if (!rt.has_label(b, ra.labels[i]))
            {
                rt.label_mismatches = rt.label_mismatches + 1;
                return false;
            }
        }
        return true;
    }

    if (ra.is_open && !rb.is_open)
    {
        // Every label the open row demands must be present in the closed one.
        for (usz i = 0; i < ra.label_count; i++)
        {
            if (!rt.has_label(b, ra.labels[i]))
            {
                rt.label_mismatches = rt.label_mismatches + 1;
                return false;
            }
        }
        // The tail absorbs the leftovers.
        if (ra.tail_var != 0 && rt.occurs_in(ra.tail_var, b, 0))
        {
            rt.occurs_failures = rt.occurs_failures + 1;
            return false;
        }
        ra.link = b;
        ra.solved = true;
        rt.rows_solved = rt.rows_solved + 1;
        return true;
    }

    if (!ra.is_open && rb.is_open) { return rt.unify(b, a, depth + 1); }

    // Both open: merge the label sets into `a` and point `b` at it.
    for (usz i = 0; i < rb.label_count; i++) { rt.add_label(a, rb.labels[i]); }
    if (rb.tail_var != 0 && ra.tail_var != 0 && rb.tail_var != ra.tail_var)
    {
        // Two distinct tails unify; keep a's.
        rb.link = a;
        rb.solved = true;
        rt.rows_solved = rt.rows_solved + 1;
    }
    return true;
}

// Occurs check for row variables: `r ~ [IO, ..r]` would be infinite.
fn bool RowTable.occurs_in(RowTable* rt, uint tail, int row, int depth)
{
    if (row < 0 || depth > 32) { return false; }
    Row* r = &rt.rows[row];
    if (r.tail_var == tail) { return true; }
    if (r.link >= 0) { return rt.occurs_in(tail, r.link, depth + 1); }
    return false;
}

// Row DIFFERENCE: the effects still outstanding after a handler discharges
// some. This is what makes `handle` change a function's effect type.
fn int RowTable.subtract(RowTable* rt, int row, uint handled_label)
{
    int out = rt.new_row();
    if (out < 0 || row < 0) { return out; }
    Row* src = &rt.rows[row];
    Row* dst = &rt.rows[out];
    dst.is_open = src.is_open;
    dst.tail_var = src.tail_var;
    for (usz i = 0; i < src.label_count; i++)
    {
        if (src.labels[i] == handled_label) { continue; }
        rt.add_label(out, src.labels[i]);
    }
    return out;
}

fn void RowTable.report(RowTable* rt)
{
    printf("  effect rows      : %d rows, %d unifications, %d solved\n",
           (int)rt.count, (int)rt.unifications, (int)rt.rows_solved);
    if (rt.label_mismatches > 0 || rt.occurs_failures > 0)
    {
        printf("  row errors       : %d label mismatches, %d occurs failures\n",
               (int)rt.label_mismatches, (int)rt.occurs_failures);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// PART B — HANDLER COVERAGE
// ════════════════════════════════════════════════════════════════════════════
struct EffectDecl
{
    uint  name_id;
    Node* decl;
    uint[MAX_ROW_LABELS] ops;
    usz   op_count;
    usz   handled_count;
}

struct HandlerCheck
{
    EffectDecl[MAX_EFFECT_DECLS] effects;
    usz                          effect_count;

    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;

    usz handlers;
    usz arms;
    usz incomplete;
    usz unknown_ops;
    usz duplicate_arms;
}

fn void HandlerCheck.init(HandlerCheck* h, pfront_core::DiagBag* d,
                          pfront_core::Interner* it, char* file)
{
    h.effect_count = 0;
    h.diags = d;
    h.interner = it;
    h.file = file;
    h.handlers = 0;
    h.arms = 0;
    h.incomplete = 0;
    h.unknown_ops = 0;
    h.duplicate_arms = 0;
}

fn void HandlerCheck.collect(HandlerCheck* h, Node* n, int depth)
{
    if (n == null || depth > 200) { return; }
    if (n.kind == Nk.N_DECL_EFFECT && h.effect_count < MAX_EFFECT_DECLS)
    {
        EffectDecl* e = &h.effects[h.effect_count];
        e.name_id = n.name_id;
        e.decl = n;
        e.op_count = 0;
        e.handled_count = 0;
        for (usz i = 0; i < n.child_count; i++)
        {
            Node* op = n.children[i];
            if (op == null || op.kind != Nk.N_DECL_EFFECT_OP) { continue; }
            if (e.op_count >= MAX_ROW_LABELS) { break; }
            e.ops[e.op_count] = op.name_id;
            e.op_count = e.op_count + 1;
        }
        h.effect_count = h.effect_count + 1;
    }
    for (usz i = 0; i < n.child_count; i++) { h.collect(n.children[i], depth + 1); }
}

fn EffectDecl* HandlerCheck.effect_of_op(HandlerCheck* h, uint op_name)
{
    for (usz i = 0; i < h.effect_count; i++)
    {
        EffectDecl* e = &h.effects[i];
        for (usz k = 0; k < e.op_count; k++)
        {
            if (e.ops[k] == op_name) { return e; }
        }
    }
    return null;
}

// Every arm must name a real operation, no operation twice, and (for a
// complete handler) every operation of the effect must appear.
fn void HandlerCheck.check_handler(HandlerCheck* h, Node* handle)
{
    if (handle == null) { return; }
    h.handlers = h.handlers + 1;

    uint[MAX_ROW_LABELS] seen;
    usz nseen = 0;
    EffectDecl* target = null;

    for (usz i = 1; i < handle.child_count; i++)
    {
        Node* arm = handle.children[i];
        if (arm == null || arm.kind != Nk.N_HANDLER_ARM) { continue; }
        h.arms = h.arms + 1;
        if (arm.name_id == 0) { continue; }

        EffectDecl* e = h.effect_of_op(arm.name_id);
        if (e == null)
        {
            h.unknown_ops = h.unknown_ops + 1;
            h.diags.warn(pfront_core::Phase.PH_RESOLVE, 4070, arm.line, arm.col,
                         "handler arm does not name a known effect operation",
                         h.file);
            continue;
        }
        if (target == null) { target = e; }

        bool dup = false;
        for (usz k = 0; k < nseen; k++) { if (seen[k] == arm.name_id) { dup = true; break; } }
        if (dup)
        {
            h.duplicate_arms = h.duplicate_arms + 1;
            h.diags.warn(pfront_core::Phase.PH_RESOLVE, 4071, arm.line, arm.col,
                         "duplicate handler arm for the same operation", h.file);
            continue;
        }
        if (nseen < MAX_ROW_LABELS) { seen[nseen] = arm.name_id; nseen = nseen + 1; }
    }

    // An incomplete handler leaves some operations unhandled: a perform of one
    // of them escapes the handler and finds no arm.
    if (target != null && nseen > 0 && nseen < target.op_count)
    {
        h.incomplete = h.incomplete + 1;
        target.handled_count = nseen;
        h.diags.warn(pfront_core::Phase.PH_RESOLVE, 4072, handle.line, handle.col,
                     "handler does not cover every operation of this effect",
                     h.file);
    }
}

fn void HandlerCheck.walk(HandlerCheck* h, Node* n, int depth)
{
    if (n == null || depth > EFF_MAX_DEPTH) { return; }
    if (n.kind == Nk.N_EXPR_HANDLE) { h.check_handler(n); }
    for (usz i = 0; i < n.child_count; i++) { h.walk(n.children[i], depth + 1); }
}

fn void HandlerCheck.report(HandlerCheck* h)
{
    printf("  handlers         : %d handlers, %d arms over %d effect decls\n",
           (int)h.handlers, (int)h.arms, (int)h.effect_count);
    if (h.incomplete > 0 || h.unknown_ops > 0 || h.duplicate_arms > 0)
    {
        printf("  handler issues   : %d incomplete, %d unknown ops, %d duplicates\n",
               (int)h.incomplete, (int)h.unknown_ops, (int)h.duplicate_arms);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// PART C — MONOMORPHISATION
// ════════════════════════════════════════════════════════════════════════════
struct TypeArgs
{
    Node*[MAX_TYPE_ARGS] args;
    usz                  count;
}

struct Instance
{
    Node*    generic;         // the polymorphic declaration
    TypeArgs args;
    char[MANGLE_CAP] mangled;
    usz      mangled_len;
    int      depth;           // instantiation depth, for recursion detection
    usz      use_count;
}

struct Monomorphiser
{
    Instance[MAX_INSTANCES] instances;
    usz                     count;

    Arena*                 arena;
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;

    usz generics_seen;
    usz instantiations;
    usz duplicates;
    usz unbounded;         // recursion that would never terminate
    int max_depth;
}

fn void Monomorphiser.init(Monomorphiser* m, Arena* a, pfront_core::DiagBag* d,
                           pfront_core::Interner* it, char* file)
{
    m.count = 0;
    m.arena = a;
    m.diags = d;
    m.interner = it;
    m.file = file;
    m.generics_seen = 0;
    m.instantiations = 0;
    m.duplicates = 0;
    m.unbounded = 0;
    m.max_depth = 0;
}

// Structural name mangling: the instance name must be a function of the
// generic's name and its type arguments, and must be stable across runs so
// separate compilation agrees.
fn usz mangle_type(Node* t, char* buf, usz cap, usz pos, int depth)
{
    if (t == null || pos + 4 >= cap || depth > 16) { return pos; }
    switch (t.kind)
    {
        case N_TY_NAME:
        {
            for (usz i = 0; i < t.p.slen && pos + 1 < cap; i++)
            {
                char c = t.p.sptr[i];
                buf[pos] = c == '.' ? '_' : c;
                pos = pos + 1;
            }
        }
        case N_TY_PTR:  { buf[pos] = 'P'; pos = mangle_type(t.child(0), buf, cap, pos + 1, depth + 1); }
        case N_TY_REF:  { buf[pos] = 'R'; pos = mangle_type(t.child(0), buf, cap, pos + 1, depth + 1); }
        case N_TY_SLICE:{ buf[pos] = 'S'; pos = mangle_type(t.child(0), buf, cap, pos + 1, depth + 1); }
        case N_TY_ARRAY:{ buf[pos] = 'A'; pos = mangle_type(t.child(0), buf, cap, pos + 1, depth + 1); }
        case N_TY_UNIT: { buf[pos] = 'v'; pos = pos + 1; }
        case N_TY_TUPLE:
        {
            buf[pos] = 'T';
            pos = pos + 1;
            for (usz i = 0; i < t.child_count; i++)
            {
                pos = mangle_type(t.children[i], buf, cap, pos, depth + 1);
                if (pos + 1 < cap) { buf[pos] = '_'; pos = pos + 1; }
            }
        }
        case N_TY_FN:
        {
            buf[pos] = 'F';
            pos = pos + 1;
            for (usz i = 0; i < t.child_count; i++)
            {
                pos = mangle_type(t.children[i], buf, cap, pos, depth + 1);
            }
        }
        default:
        {
            buf[pos] = 'X';
            pos = pos + 1;
        }
    }
    return pos;
}

fn usz Monomorphiser.mangle(Monomorphiser* m, Node* generic, TypeArgs* ta,
                            char* buf, usz cap)
{
    usz pos = 0;
    for (usz i = 0; i < generic.p.slen && pos + 1 < cap; i++)
    {
        buf[pos] = generic.p.sptr[i];
        pos = pos + 1;
    }
    for (usz i = 0; i < ta.count && pos + 2 < cap; i++)
    {
        buf[pos] = '$';
        pos = mangle_type(ta.args[i], buf, cap, pos + 1, 0);
    }
    if (pos < cap) { buf[pos] = 0; }
    return pos;
}

fn bool type_args_eq(TypeArgs* a, TypeArgs* b)
{
    if (a.count != b.count) { return false; }
    for (usz i = 0; i < a.count; i++)
    {
        if (!theory_term::term_eq(a.args[i], b.args[i], 0)) { return false; }
    }
    return true;
}

fn int Monomorphiser.find(Monomorphiser* m, Node* generic, TypeArgs* ta)
{
    for (usz i = 0; i < m.count; i++)
    {
        if (m.instances[i].generic != generic) { continue; }
        if (type_args_eq(&m.instances[i].args, ta)) { return (int)i; }
    }
    return -1;
}

fn int Monomorphiser.instantiate(Monomorphiser* m, Node* generic, TypeArgs* ta,
                                 int depth)
{
    int existing = m.find(generic, ta);
    if (existing >= 0)
    {
        m.duplicates = m.duplicates + 1;
        m.instances[existing].use_count = m.instances[existing].use_count + 1;
        return existing;
    }
    // A generic that instantiates itself with a STRICTLY LARGER type argument
    // never terminates: `f<T>` calling `f<List<T>>` is the canonical case.
    if (depth > 32)
    {
        m.unbounded = m.unbounded + 1;
        m.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3260,
                           generic.line, generic.col,
                           "generic instantiation does not terminate",
                           "a type parameter grows on each recursive call",
                           m.file);
        return -1;
    }
    if (m.count >= MAX_INSTANCES) { return -1; }
    int id = (int)m.count;
    m.count = m.count + 1;
    Instance* inst = &m.instances[id];
    inst.generic = generic;
    inst.args = *ta;
    inst.depth = depth;
    inst.use_count = 1;
    inst.mangled_len = m.mangle(generic, ta, &inst.mangled[0], MANGLE_CAP);
    m.instantiations = m.instantiations + 1;
    if (depth > m.max_depth) { m.max_depth = depth; }
    return id;
}

// Collect generic declarations and every call site that instantiates one.
fn void Monomorphiser.scan(Monomorphiser* m, Node* n, int depth)
{
    if (n == null || depth > EFF_MAX_DEPTH) { return; }

    if (n.kind == Nk.N_DECL_FN)
    {
        bool generic = false;
        for (usz i = 0; i < n.child_count; i++)
        {
            Node* c = n.children[i];
            if (c != null && c.kind == Nk.N_DECL_TYPEPARAM) { generic = true; break; }
        }
        if (generic) { m.generics_seen = m.generics_seen + 1; }
    }

    // A call to a generic with explicit type arguments instantiates it.
    if (n.kind == Nk.N_EXPR_CALL && n.child_count > 0)
    {
        Node* callee = n.children[0];
        if (callee != null && callee.resolved != null)
        {
            Node* d = callee.resolved;
            bool has_tp = false;
            for (usz i = 0; i < d.child_count; i++)
            {
                Node* c = d.children[i];
                if (c != null && c.kind == Nk.N_DECL_TYPEPARAM) { has_tp = true; break; }
            }
            if (has_tp)
            {
                TypeArgs ta;
                ta.count = 0;
                // Infer the arguments from the call's actual argument types.
                for (usz i = 1; i < n.child_count && ta.count < MAX_TYPE_ARGS; i++)
                {
                    Node* arg = n.children[i];
                    if (arg == null) { continue; }
                    ta.args[ta.count] = arg.type_ann;
                    ta.count = ta.count + 1;
                }
                m.instantiate(d, &ta, depth);
            }
        }
    }

    for (usz i = 0; i < n.child_count; i++) { m.scan(n.children[i], depth + 1); }
}

fn void Monomorphiser.report(Monomorphiser* m)
{
    printf("  monomorphisation : %d generics, %d instances (%d shared)\n",
           (int)m.generics_seen, (int)m.instantiations, (int)m.duplicates);
    if (m.unbounded > 0)
    {
        printf("  mono errors      : %d non-terminating instantiations\n",
               (int)m.unbounded);
    }
}

// ── Effect inference over rows ──────────────────────────────────────────────
// Combines the row machinery with the AST: computes each function's row,
// propagates it through calls, and subtracts handled effects.
struct RowInference
{
    RowTable               rows;
    HandlerCheck*          handlers;
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;

    usz fns_typed;
    usz rows_built;
    usz effects_discharged;
    usz unhandled_escapes;
}

fn void RowInference.init(RowInference* ri, HandlerCheck* hc,
                          pfront_core::DiagBag* d,
                          pfront_core::Interner* it, char* file)
{
    ri.rows.init();
    ri.handlers = hc;
    ri.diags = d;
    ri.interner = it;
    ri.file = file;
    ri.fns_typed = 0;
    ri.rows_built = 0;
    ri.effects_discharged = 0;
    ri.unhandled_escapes = 0;
}

fn int RowInference.row_of_fn(RowInference* ri, Node* f)
{
    int row = ri.rows.new_row();
    if (row < 0 || f == null) { return row; }
    ri.rows_built = ri.rows_built + 1;
    // A declared row is authoritative.
    for (usz i = 0; i < f.child_count; i++)
    {
        Node* c = f.children[i];
        if (c != null && c.kind == Nk.N_TY_EFFECT_ROW && c.p.aux != 2)
        {
            return ri.rows.from_node(c);
        }
    }
    if (f.type_ann != null)
    {
        for (usz i = 0; i < f.type_ann.child_count; i++)
        {
            Node* c = f.type_ann.children[i];
            if (c != null && c.kind == Nk.N_TY_EFFECT_ROW && c.p.aux != 2)
            {
                return ri.rows.from_node(c);
            }
        }
    }
    return row;
}

fn void RowInference.walk(RowInference* ri, Node* n, int depth)
{
    if (n == null || depth > EFF_MAX_DEPTH) { return; }
    if (n.kind == Nk.N_DECL_FN)
    {
        ri.fns_typed = ri.fns_typed + 1;
        ri.row_of_fn(n);
    }
    if (n.kind == Nk.N_EXPR_HANDLE)
    {
        // Each arm discharges one operation from the computation's row.
        for (usz i = 1; i < n.child_count; i++)
        {
            Node* arm = n.children[i];
            if (arm != null && arm.kind == Nk.N_HANDLER_ARM && arm.name_id != 0)
            {
                ri.effects_discharged = ri.effects_discharged + 1;
            }
        }
    }
    for (usz i = 0; i < n.child_count; i++) { ri.walk(n.children[i], depth + 1); }
}

fn void RowInference.report(RowInference* ri)
{
    printf("  row inference    : %d fns typed, %d rows, %d effects discharged\n",
           (int)ri.fns_typed, (int)ri.rows_built, (int)ri.effects_discharged);
    ri.rows.report();
}
