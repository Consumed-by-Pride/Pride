// ============================================================================
// theory_rowinfer.c3 — principal-type effect inference over rows (part 22)
// ----------------------------------------------------------------------------
// `theory_effects` builds and unifies rows. This module does the harder job:
// INFERRING them, so a function's effect signature need not be written down.
//
// The system is Rémy-style row polymorphism with scoped effect handling:
//
//     Γ ⊢ e : τ ! ρ
//
// where ρ is a row — a set of effect labels plus an optional tail variable.
// The inference rules that matter:
//
//   (VAR)      Γ,x:τ ⊢ x : τ ! ∅              a variable performs nothing
//   (APP)      Γ ⊢ f : τ₁→τ₂!ρf   Γ ⊢ a : τ₁!ρa
//              ─────────────────────────────────────
//              Γ ⊢ f a : τ₂ ! ρf ∪ ρa ∪ ρlatent
//   (PERFORM)  Γ ⊢ perform E.op(a) : τ ! {E} ∪ ρa
//   (HANDLE)   Γ ⊢ c : τ ! {E} ∪ ρ    arms cover E
//              ─────────────────────────────────────
//              Γ ⊢ handle c with H : τ' ! ρ        E is DISCHARGED
//
// The (HANDLE) rule is what makes effect systems worth having: handling an
// effect removes it from the row, so `main` can be pure even though its
// callees perform State and IO.
//
// PRINCIPALITY. Every expression gets a MOST GENERAL row: one with a tail
// variable that any concrete row can instantiate. `map` therefore infers
// `(a→b!ρ) → [a] → [b] ! ρ` rather than committing to a fixed effect set, and
// the same definition works with pure and effectful callbacks.
//
// Generalisation uses LEVELS (as in the type inferencer): a row variable is
// generalisable exactly when its level exceeds the current binding level.
// Without that check, a row variable shared with an enclosing scope would be
// quantified and the inference would be unsound.
// ============================================================================

module theory_rowinfer;

import pfront_lex;
import pfront_core;
import theory_term;
import theory_effects;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz RI_MAX_ROWS     = 8192;
const usz RI_MAX_LABELS   = 32;
const usz RI_MAX_SCHEMES  = 2048;
const usz RI_MAX_ENV      = 4096;
const usz RI_MAX_QUANT    = 16;
const int RI_MAX_DEPTH    = 300;

// ── Rows with levels ────────────────────────────────────────────────────────
// A row is a set of labels plus an optional tail. `link` implements union-find
// over tails, `level` drives generalisation.
struct IRow
{
    uint[RI_MAX_LABELS] labels;
    usz                 label_count;
    int                 tail;        // row-variable id, -1 when closed
    int                 link;        // resolved tail, -1 when unresolved
    int                 level;
    bool                generalised;
    uint                var_name;    // source name for a written `..r`
}

struct RowStore
{
    IRow[RI_MAX_ROWS] rows;
    usz               count;
    int               current_level;
    int               next_var;

    usz unifications;
    usz occurs_hits;
    usz label_conflicts;
    usz tails_solved;
    usz generalisations;
    usz instantiations;
}

fn void RowStore.init(RowStore* rs)
{
    rs.count = 0;
    rs.current_level = 0;
    rs.next_var = 1;
    rs.unifications = 0;
    rs.occurs_hits = 0;
    rs.label_conflicts = 0;
    rs.tails_solved = 0;
    rs.generalisations = 0;
    rs.instantiations = 0;
}

fn int RowStore.empty_row(RowStore* rs)
{
    if (rs.count >= RI_MAX_ROWS) { return -1; }
    int id = (int)rs.count;
    rs.count = rs.count + 1;
    IRow* r = &rs.rows[id];
    r.label_count = 0;
    r.tail = -1;
    r.link = -1;
    r.level = rs.current_level;
    r.generalised = false;
    r.var_name = 0;
    return id;
}

// An OPEN row: `{} ∪ ρ` for a fresh ρ. This is the most general row, and the
// starting point for any expression whose effects are not yet known.
fn int RowStore.open_row(RowStore* rs)
{
    int id = rs.empty_row();
    if (id < 0) { return id; }
    rs.rows[id].tail = rs.next_var;
    rs.next_var = rs.next_var + 1;
    return id;
}

fn int RowStore.singleton(RowStore* rs, uint label)
{
    int id = rs.empty_row();
    if (id < 0) { return id; }
    rs.add_label(id, label);
    return id;
}

fn bool RowStore.add_label(RowStore* rs, int row, uint label)
{
    if (row < 0 || (usz)row >= rs.count || label == 0) { return false; }
    IRow* r = &rs.rows[row];
    for (usz i = 0; i < r.label_count; i++) { if (r.labels[i] == label) { return true; } }
    if (r.label_count >= RI_MAX_LABELS) { return false; }
    r.labels[r.label_count] = label;
    r.label_count = r.label_count + 1;
    return true;
}

fn bool RowStore.has(RowStore* rs, int row, uint label)
{
    int r = rs.resolve(row);
    if (r < 0) { return false; }
    IRow* rr = &rs.rows[r];
    for (usz i = 0; i < rr.label_count; i++) { if (rr.labels[i] == label) { return true; } }
    return false;
}

// Follow the tail links to the row that actually represents this one.
fn int RowStore.resolve(RowStore* rs, int row)
{
    if (row < 0 || (usz)row >= rs.count) { return -1; }
    int cur = row;
    int guard = 0;
    while (rs.rows[cur].link >= 0 && guard < 1024)
    {
        cur = rs.rows[cur].link;
        guard = guard + 1;
    }
    // Path compression.
    int walk = row;
    while (rs.rows[walk].link >= 0 && walk != cur)
    {
        int nxt = rs.rows[walk].link;
        rs.rows[walk].link = cur;
        walk = nxt;
    }
    return cur;
}

// UNION: ρ₁ ∪ ρ₂. Used by (APP), where a call performs whatever the function
// and the argument perform, plus the callee's latent effects.
fn int RowStore.union_rows(RowStore* rs, int a, int b)
{
    int ra = rs.resolve(a);
    int rb = rs.resolve(b);
    if (ra < 0) { return rb; }
    if (rb < 0) { return ra; }
    if (ra == rb) { return ra; }

    int out = rs.empty_row();
    if (out < 0) { return ra; }
    IRow* dst = &rs.rows[out];
    IRow* x = &rs.rows[ra];
    IRow* y = &rs.rows[rb];

    for (usz i = 0; i < x.label_count; i++) { rs.add_label(out, x.labels[i]); }
    for (usz i = 0; i < y.label_count; i++) { rs.add_label(out, y.labels[i]); }

    // The union is open when either side is: an unknown tail contaminates.
    if (x.tail >= 0) { dst.tail = x.tail; }
    else if (y.tail >= 0) { dst.tail = y.tail; }

    int lvl = x.level < y.level ? x.level : y.level;
    dst.level = lvl;
    return out;
}

// DIFFERENCE: ρ \ {E}. This is the (HANDLE) rule — discharging an effect.
fn int RowStore.remove_label(RowStore* rs, int row, uint label)
{
    int r = rs.resolve(row);
    if (r < 0) { return r; }
    int out = rs.empty_row();
    if (out < 0) { return r; }
    IRow* src = &rs.rows[r];
    IRow* dst = &rs.rows[out];
    for (usz i = 0; i < src.label_count; i++)
    {
        if (src.labels[i] == label) { continue; }
        rs.add_label(out, src.labels[i]);
    }
    dst.tail = src.tail;
    dst.level = src.level;
    return out;
}

// OCCURS CHECK over tails. Unifying ρ with `{IO} ∪ ρ` builds an infinite row,
// and every later traversal of it would not terminate.
fn bool RowStore.occurs(RowStore* rs, int tail, int row, int depth)
{
    if (tail < 0 || depth > 64) { return false; }
    int r = rs.resolve(row);
    if (r < 0) { return false; }
    if (rs.rows[r].tail == tail) { return true; }
    return false;
}

// UNIFICATION. Rows are unordered sets, so this is not positional.
fn bool RowStore.unify(RowStore* rs, int a, int b, int depth)
{
    if (depth > 64) { return false; }
    int ra = rs.resolve(a);
    int rb = rs.resolve(b);
    if (ra < 0 || rb < 0) { return false; }
    if (ra == rb) { return true; }
    rs.unifications = rs.unifications + 1;

    IRow* x = &rs.rows[ra];
    IRow* y = &rs.rows[rb];

    bool x_open = x.tail >= 0;
    bool y_open = y.tail >= 0;

    if (!x_open && !y_open)
    {
        // Both closed: the label SETS must coincide exactly.
        if (x.label_count != y.label_count)
        {
            rs.label_conflicts = rs.label_conflicts + 1;
            return false;
        }
        for (usz i = 0; i < x.label_count; i++)
        {
            if (!rs.has(rb, x.labels[i]))
            {
                rs.label_conflicts = rs.label_conflicts + 1;
                return false;
            }
        }
        return true;
    }

    if (x_open && !y_open)
    {
        // x's labels must all be in y; x's tail absorbs the rest.
        for (usz i = 0; i < x.label_count; i++)
        {
            if (!rs.has(rb, x.labels[i]))
            {
                rs.label_conflicts = rs.label_conflicts + 1;
                return false;
            }
        }
        if (rs.occurs(x.tail, rb, 0))
        {
            rs.occurs_hits = rs.occurs_hits + 1;
            return false;
        }
        x.link = rb;
        rs.tails_solved = rs.tails_solved + 1;
        // Lower the level so generalisation stays sound.
        if (y.level > x.level) { y.level = x.level; }
        return true;
    }

    if (!x_open && y_open) { return rs.unify(b, a, depth + 1); }

    // Both open: merge labels, then identify the tails.
    for (usz i = 0; i < y.label_count; i++) { rs.add_label(ra, y.labels[i]); }
    if (x.tail != y.tail)
    {
        if (rs.occurs(y.tail, ra, 0))
        {
            rs.occurs_hits = rs.occurs_hits + 1;
            return false;
        }
        y.link = ra;
        rs.tails_solved = rs.tails_solved + 1;
    }
    if (y.level < x.level) { x.level = y.level; }
    return true;
}

// SUBSUMPTION: is every effect of `sub` present in `sup`? Used when checking a
// definition against a written signature. A function may perform FEWER effects
// than declared, never more.
fn bool RowStore.subsumes(RowStore* rs, int sup, int sub)
{
    int a = rs.resolve(sup);
    int b = rs.resolve(sub);
    if (a < 0 || b < 0) { return false; }
    IRow* need = &rs.rows[b];
    for (usz i = 0; i < need.label_count; i++)
    {
        if (!rs.has(a, need.labels[i]))
        {
            // An open supertype can absorb the extra label.
            if (rs.rows[a].tail < 0) { return false; }
        }
    }
    return true;
}

// ── Row schemes (polymorphism) ──────────────────────────────────────────────
// A scheme is `∀ρ₁..ρₙ. row` — the quantified variables are the ones
// generalisable at this level.
struct RowScheme
{
    int  row;
    int[RI_MAX_QUANT] quantified;
    usz  quant_count;
    uint owner_name;
}

struct SchemeTable
{
    RowScheme[RI_MAX_SCHEMES] schemes;
    usz                       count;
}

fn void SchemeTable.init(SchemeTable* st) { st.count = 0; }

// GENERALISE: quantify every tail whose level exceeds the current one. A
// variable at or below the current level is shared with an enclosing scope and
// must NOT be quantified — that is the classic unsoundness this check prevents.
fn int SchemeTable.generalise(SchemeTable* st, RowStore* rs, int row, uint owner)
{
    if (st.count >= RI_MAX_SCHEMES) { return -1; }
    int id = (int)st.count;
    st.count = st.count + 1;
    RowScheme* s = &st.schemes[id];
    s.row = rs.resolve(row);
    s.quant_count = 0;
    s.owner_name = owner;

    if (s.row >= 0)
    {
        IRow* r = &rs.rows[s.row];
        if (r.tail >= 0 && r.level > rs.current_level && s.quant_count < RI_MAX_QUANT)
        {
            s.quantified[s.quant_count] = r.tail;
            s.quant_count = s.quant_count + 1;
            r.generalised = true;
            rs.generalisations = rs.generalisations + 1;
        }
    }
    return id;
}

// INSTANTIATE: replace each quantified tail with a fresh one, so two uses of
// the same polymorphic function do not accidentally share a row variable.
fn int SchemeTable.instantiate(SchemeTable* st, RowStore* rs, int scheme)
{
    if (scheme < 0 || (usz)scheme >= st.count) { return -1; }
    RowScheme* s = &st.schemes[scheme];
    rs.instantiations = rs.instantiations + 1;

    int src = rs.resolve(s.row);
    if (src < 0) { return -1; }
    int out = rs.empty_row();
    if (out < 0) { return src; }
    IRow* from = &rs.rows[src];
    IRow* to = &rs.rows[out];
    for (usz i = 0; i < from.label_count; i++) { rs.add_label(out, from.labels[i]); }
    if (s.quant_count > 0)
    {
        to.tail = rs.next_var;
        rs.next_var = rs.next_var + 1;
    }
    else
    {
        to.tail = from.tail;
    }
    to.level = rs.current_level;
    return out;
}

// ── Inference environment ───────────────────────────────────────────────────
struct RowBinding
{
    uint name_id;
    int  scheme;     // -1 for a monomorphic row
    int  row;
}

struct RowEnv
{
    RowBinding[RI_MAX_ENV] items;
    usz                    count;
    usz[256]               frames;
    usz                    frame_count;
}

fn void RowEnv.init(RowEnv* e)
{
    e.count = 0;
    e.frame_count = 0;
    e.push();
}

fn void RowEnv.push(RowEnv* e)
{
    if (e.frame_count >= 256) { return; }
    e.frames[e.frame_count] = e.count;
    e.frame_count = e.frame_count + 1;
}

fn void RowEnv.pop(RowEnv* e)
{
    if (e.frame_count == 0) { return; }
    e.frame_count = e.frame_count - 1;
    e.count = e.frames[e.frame_count];
}

fn void RowEnv.bind(RowEnv* e, uint name, int scheme, int row)
{
    if (e.count >= RI_MAX_ENV) { return; }
    e.items[e.count].name_id = name;
    e.items[e.count].scheme = scheme;
    e.items[e.count].row = row;
    e.count = e.count + 1;
}

fn RowBinding* RowEnv.lookup(RowEnv* e, uint name)
{
    usz i = e.count;
    while (i > 0)
    {
        i = i - 1;
        if (e.items[i].name_id == name) { return &e.items[i]; }
    }
    return null;
}

// ── The inference engine ────────────────────────────────────────────────────
struct RowInferencer
{
    RowStore    store;
    SchemeTable schemes;
    RowEnv      env;

    theory_effects::HandlerCheck* handlers;
    pfront_core::DiagBag*         diags;
    pfront_core::Interner*        interner;
    Arena*                        arena;
    char*                         file;

    usz exprs;
    usz fns_inferred;
    usz performs;
    usz handles;
    usz discharged;
    usz escaped;          // effects performed but never handled
    usz signature_errors; // inferred row exceeds the declared one
    bool strict;
}

fn void RowInferencer.init(RowInferencer* ri, Arena* a,
                           theory_effects::HandlerCheck* hc,
                           pfront_core::DiagBag* d,
                           pfront_core::Interner* it, char* file)
{
    ri.store.init();
    ri.schemes.init();
    ri.env.init();
    ri.handlers = hc;
    ri.diags = d;
    ri.interner = it;
    ri.arena = a;
    ri.file = file;
    ri.exprs = 0;
    ri.fns_inferred = 0;
    ri.performs = 0;
    ri.handles = 0;
    ri.discharged = 0;
    ri.escaped = 0;
    ri.signature_errors = 0;
    ri.strict = false;
}

// Infer the effect row of an expression. Returns a row id.
fn int RowInferencer.infer(RowInferencer* ri, Node* e, int depth)
{
    if (e == null || depth > RI_MAX_DEPTH) { return ri.store.empty_row(); }
    ri.exprs = ri.exprs + 1;

    switch (e.kind)
    {
        // (VAR) and literals perform nothing.
        case N_EXPR_INT:
        case N_EXPR_FLOAT:
        case N_EXPR_BOOL:
        case N_EXPR_CHAR:
        case N_EXPR_STRING:
        case N_EXPR_UNIT:
        case N_EXPR_NULL:
            return ri.store.empty_row();

        case N_EXPR_IDENT:
        {
            RowBinding* b = ri.env.lookup(e.name_id);
            if (b != null)
            {
                if (b.scheme >= 0)
                {
                    return ri.schemes.instantiate(&ri.store, b.scheme);
                }
                return b.row;
            }
            // Referring to an effect operation without performing it still
            // mentions the effect.
            if (e.resolved != null && e.resolved.kind == Nk.N_DECL_EFFECT_OP)
            {
                theory_effects::EffectDecl* ed =
                    ri.handlers.effect_of_op(e.resolved.name_id);
                if (ed != null) { return ri.store.singleton(ed.name_id); }
            }
            return ri.store.empty_row();
        }

        // (PERFORM): the operation's own effect, plus the arguments'.
        case N_EXPR_PERFORM:
        {
            ri.performs = ri.performs + 1;
            int row = ri.store.empty_row();
            uint eff = 0;
            Node* path = e.child(0);
            if (path != null && path.child_count > 0)
            {
                // The head of `E.op` names the effect.
                Node* head = path.children[0];
                if (head != null) { eff = head.name_id; }
            }
            if (eff == 0 && e.name_id != 0)
            {
                theory_effects::EffectDecl* ed = ri.handlers.effect_of_op(e.name_id);
                if (ed != null) { eff = ed.name_id; }
            }
            if (eff != 0) { row = ri.store.singleton(eff); }
            for (usz i = 1; i < e.child_count; i++)
            {
                row = ri.store.union_rows(row, ri.infer(e.children[i], depth + 1));
            }
            return row;
        }

        // (HANDLE): infer the computation's row, then DISCHARGE what the arms
        // cover. This is the rule that lets effects disappear.
        case N_EXPR_HANDLE:
        {
            ri.handles = ri.handles + 1;
            int comp = ri.infer(e.child(0), depth + 1);
            for (usz i = 1; i < e.child_count; i++)
            {
                Node* arm = e.children[i];
                if (arm == null || arm.kind != Nk.N_HANDLER_ARM) { continue; }
                theory_effects::EffectDecl* ed =
                    ri.handlers.effect_of_op(arm.name_id);
                if (ed == null) { continue; }
                comp = ri.store.remove_label(comp, ed.name_id);
                ri.discharged = ri.discharged + 1;
                // The arm body itself may perform effects, which are NOT
                // discharged: they escape into the surrounding computation.
                for (usz k = 1; k < arm.child_count; k++)
                {
                    comp = ri.store.union_rows(comp, ri.infer(arm.children[k], depth + 1));
                }
            }
            return comp;
        }

        // (APP): the union of callee, arguments, and the callee's latent row.
        case N_EXPR_CALL:
        {
            int row = ri.store.empty_row();
            Node* callee = e.child(0);
            if (callee != null)
            {
                row = ri.store.union_rows(row, ri.infer(callee, depth + 1));
                if (callee.resolved != null)
                {
                    int latent = ri.latent_row(callee.resolved);
                    row = ri.store.union_rows(row, latent);
                }
            }
            for (usz i = 1; i < e.child_count; i++)
            {
                row = ri.store.union_rows(row, ri.infer(e.children[i], depth + 1));
            }
            return row;
        }

        case N_DECL_FN:
        {
            ri.infer_fn(e, depth);
            return ri.store.empty_row();
        }

        case N_BLOCK:
        {
            ri.env.push();
            int row = ri.store.empty_row();
            for (usz i = 0; i < e.child_count; i++)
            {
                row = ri.store.union_rows(row, ri.infer(e.children[i], depth + 1));
            }
            ri.env.pop();
            return row;
        }

        default:
        {
            int row = ri.store.empty_row();
            for (usz i = 0; i < e.child_count; i++)
            {
                Node* c = e.children[i];
                if (c == null || pfront_core::is_pattern(c.kind)) { continue; }
                row = ri.store.union_rows(row, ri.infer(c, depth + 1));
            }
            return row;
        }
    }
}

// The declared (latent) row of a function, or an open row when unwritten.
fn int RowInferencer.latent_row(RowInferencer* ri, Node* fn_decl)
{
    if (fn_decl == null) { return ri.store.empty_row(); }
    Node* written = find_row_node(fn_decl);
    if (written == null) { return ri.store.empty_row(); }
    return ri.row_from_node(written);
}

fn Node* find_row_node(Node* fn_decl)
{
    for (usz i = 0; i < fn_decl.child_count; i++)
    {
        Node* c = fn_decl.children[i];
        if (c != null && c.kind == Nk.N_TY_EFFECT_ROW && c.p.aux != 2) { return c; }
    }
    if (fn_decl.type_ann != null)
    {
        for (usz i = 0; i < fn_decl.type_ann.child_count; i++)
        {
            Node* c = fn_decl.type_ann.children[i];
            if (c != null && c.kind == Nk.N_TY_EFFECT_ROW && c.p.aux != 2) { return c; }
        }
    }
    return null;
}

fn int RowInferencer.row_from_node(RowInferencer* ri, Node* n)
{
    int row = ri.store.empty_row();
    if (row < 0 || n == null) { return row; }
    for (usz i = 0; i < n.child_count; i++)
    {
        Node* el = n.children[i];
        if (el == null || el.kind != Nk.N_TY_EFFECT_ELEM) { continue; }
        if (el.p.aux == 1)
        {
            // `..r` tail variable.
            ri.store.rows[row].tail = ri.store.next_var;
            ri.store.rows[row].var_name = el.name_id;
            ri.store.next_var = ri.store.next_var + 1;
            continue;
        }
        ri.store.add_label(row, el.name_id);
    }
    if ((n.flags & pfront_core::NF_OPEN_ROW) != 0 && ri.store.rows[row].tail < 0)
    {
        ri.store.rows[row].tail = ri.store.next_var;
        ri.store.next_var = ri.store.next_var + 1;
    }
    return row;
}

// Infer a function's row and check it against any written signature.
fn void RowInferencer.infer_fn(RowInferencer* ri, Node* f, int depth)
{
    if (f == null) { return; }
    ri.fns_inferred = ri.fns_inferred + 1;

    ri.store.current_level = ri.store.current_level + 1;
    ri.env.push();

    int inferred = ri.store.empty_row();
    for (usz i = 0; i < f.child_count; i++)
    {
        Node* c = f.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.N_CLAUSE)
        {
            ri.env.push();
            for (usz k = 1; k < c.child_count; k++)
            {
                inferred = ri.store.union_rows(inferred, ri.infer(c.children[k], depth + 1));
            }
            ri.env.pop();
        }
        else if (c.kind == Nk.N_BLOCK)
        {
            inferred = ri.store.union_rows(inferred, ri.infer(c, depth + 1));
        }
    }

    // If a row was written, the inferred one must be subsumed by it: a
    // function may perform fewer effects than declared, never more.
    Node* written = find_row_node(f);
    if (written != null)
    {
        int declared = ri.row_from_node(written);
        if (!ri.store.subsumes(declared, inferred))
        {
            ri.signature_errors = ri.signature_errors + 1;
            if (ri.strict)
            {
                ri.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3290,
                                    f.line, f.col,
                                    "function performs effects not listed in its signature",
                                    "add the missing effects, or handle them internally",
                                    ri.file);
            }
        }
    }
    else
    {
        // No signature: generalise, giving the principal (most general) row.
        ri.schemes.generalise(&ri.store, inferred, f.name_id);
    }

    ri.env.pop();
    ri.store.current_level = ri.store.current_level - 1;
}

// Effects reaching `main` unhandled are a program-level error: there is no
// outer handler left to discharge them.
fn void RowInferencer.check_main(RowInferencer* ri, Node* root)
{
    for (usz i = 0; i < root.child_count; i++)
    {
        Node* d = root.children[i];
        if (d == null || d.kind != Nk.N_DECL_FN) { continue; }
        if (d.p.slen != 4) { continue; }
        if (d.p.sptr == null) { continue; }
        if (d.p.sptr[0] != 'm' || d.p.sptr[1] != 'a') { continue; }

        int row = ri.store.empty_row();
        for (usz k = 0; k < d.child_count; k++)
        {
            Node* c = d.children[k];
            if (c == null) { continue; }
            if (c.kind == Nk.N_CLAUSE)
            {
                for (usz j = 1; j < c.child_count; j++)
                {
                    row = ri.store.union_rows(row, ri.infer(c.children[j], 0));
                }
            }
        }
        int r = ri.store.resolve(row);
        if (r < 0) { continue; }
        usz n = ri.store.rows[r].label_count;
        if (n > 0)
        {
            ri.escaped = ri.escaped + n;
            // Reported as a note by default: a runtime may install ambient
            // handlers for IO, so this is informative rather than fatal.
            ri.diags.add(pfront_core::Severity.SEV_NOTE,
                         pfront_core::Phase.PH_RESOLVE, 3291, d.line, d.col,
                         "effects reach the entry point unhandled", null, ri.file);
        }
    }
}

fn void RowInferencer.run(RowInferencer* ri, Node* root)
{
    if (root == null) { return; }
    for (usz i = 0; i < root.child_count; i++)
    {
        Node* d = root.children[i];
        if (d == null) { continue; }
        if (d.kind == Nk.N_DECL_FN) { ri.infer_fn(d, 0); }
        else if (d.kind == Nk.N_MODULE) { ri.run(d); }
    }
    ri.check_main(root);
}

fn void RowInferencer.report(RowInferencer* ri)
{
    printf("  row inference    : %d fns, %d exprs, %d performs, %d handles\n",
           (int)ri.fns_inferred, (int)ri.exprs, (int)ri.performs, (int)ri.handles);
    printf("  effect discharge : %d discharged, %d escape to entry\n",
           (int)ri.discharged, (int)ri.escaped);
    printf("  row solving      : %d unifications, %d tails solved, %d occurs blocked\n",
           (int)ri.store.unifications, (int)ri.store.tails_solved,
           (int)ri.store.occurs_hits);
    printf("  row polymorphism : %d generalised, %d instantiated\n",
           (int)ri.store.generalisations, (int)ri.store.instantiations);
    if (ri.signature_errors > 0)
    {
        printf("  signature errors : %d fns perform undeclared effects\n",
               (int)ri.signature_errors);
    }
}
