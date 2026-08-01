// ============================================================================
// theory_bidi.c3 — bidirectional CMTT with native box types (part 23)
// ----------------------------------------------------------------------------
// `theory_cmtt` checks the modal judgment structurally. This module makes the
// box a FIRST-CLASS TYPE in a bidirectional discipline, so box types can be
// inferred rather than only checked.
//
// Bidirectional typing splits the rules into two mutually recursive modes:
//
//     Γ ⊢ e ⇒ τ     SYNTHESIS  — read the type off the term
//     Γ ⊢ e ⇐ τ     CHECKING   — push an expected type into the term
//
// The split matters for staging because a quotation's type genuinely cannot be
// synthesised in general: `<x + y>` could be `□(i64)` or `□(f64)` depending on
// context. In checking mode the expected `□_{Γ'}^{L}τ` tells us what the body
// must produce; in synthesis mode we infer what we can and leave a metavariable
// otherwise.
//
// The modal rules, in bidirectional form:
//
//   (BOX-I ⇐)   Γ, Γ' ⊢ e ⇐ τ at L+1
//               ─────────────────────────────
//               Γ ⊢ box[Γ'] e ⇐ □_{Γ'}^{L+1} τ  at L
//
//   (BOX-E ⇒)   Γ ⊢ e ⇒ □_{Γ'}^{L} τ      Γ ⊇ Γ'
//               ─────────────────────────────────
//               Γ ⊢ ~e ⇒ τ  at L
//
//   (RUN ⇒)     Γ ⊢ e ⇒ □_{∅}^{0} τ
//               ─────────────────────
//               Γ ⊢ run e ⇒ τ
//               — only a CLOSED box may be run; an open one still depends on
//                 an environment that does not exist at runtime.
//
//   (SUB)       Γ ⊢ e ⇒ τ₁    τ₁ <: τ₂
//               ─────────────────────────
//               Γ ⊢ e ⇐ τ₂
//               — the single place where subtyping enters, which is what keeps
//                 the rest of the system syntax-directed.
//
// Every rule is syntax-directed apart from (SUB), so there is no backtracking
// and error messages point at the actual mismatch rather than at the whole
// enclosing expression.
// ============================================================================

module theory_bidi;

import pfront_lex;
import pfront_core;
import theory_term;
import theory_cmtt;
import theory_modal;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;
alias Level = theory_cmtt::Level;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz BD_MAX_TYPES  = 16384;
const usz BD_MAX_META   = 4096;
const usz BD_MAX_ARGS   = 16;
const int BD_MAX_DEPTH  = 300;

// ── Modal type representation ───────────────────────────────────────────────
// The box is a real type former here, not an annotation on the side.
enum MTKind : int
{
    MT_UNKNOWN,     // metavariable, to be solved
    MT_BASE,        // an ordinary type from the AST
    MT_BOX,         // □_{Γ}^{L} τ
    MT_ARROW,       // τ₁ → τ₂
    MT_PRODUCT,     // τ₁ × … × τₙ
    MT_CODE,        // code of unknown type: □ with everything unspecified
    MT_ERROR
}

struct MType
{
    MTKind kind;
    Node*  base;                 // MT_BASE
    int[BD_MAX_ARGS] args;       // MT_ARROW / MT_PRODUCT / MT_BOX payload
    usz    arg_count;
    int    ctx;                  // MT_BOX: the context Γ'
    Level  level;                // MT_BOX: the level L'
    int    link;                 // metavariable resolution (union-find)
    int    meta_id;
    bool   solved;
}

struct MTypeStore
{
    MType[BD_MAX_TYPES] types;
    usz                 count;
    int                 next_meta;

    int t_error;
    int t_unknown;

    usz metas_created;
    usz metas_solved;
    usz occurs_blocked;
}

fn void MTypeStore.init(MTypeStore* s)
{
    s.count = 0;
    s.next_meta = 1;
    s.metas_created = 0;
    s.metas_solved = 0;
    s.occurs_blocked = 0;
    s.t_error = s.mk(MTKind.MT_ERROR);
    s.t_unknown = s.mk(MTKind.MT_UNKNOWN);
}

fn int MTypeStore.mk(MTypeStore* s, MTKind k)
{
    if (s.count >= BD_MAX_TYPES) { return 0; }
    int id = (int)s.count;
    s.count = s.count + 1;
    MType* t = &s.types[id];
    t.kind = k;
    t.base = null;
    t.arg_count = 0;
    t.ctx = -1;
    t.level = theory_cmtt::level_const(0);
    t.link = -1;
    t.meta_id = 0;
    t.solved = false;
    return id;
}

fn int MTypeStore.fresh_meta(MTypeStore* s)
{
    int id = s.mk(MTKind.MT_UNKNOWN);
    s.types[id].meta_id = s.next_meta;
    s.next_meta = s.next_meta + 1;
    s.metas_created = s.metas_created + 1;
    return id;
}

fn int MTypeStore.mk_base(MTypeStore* s, Node* ty)
{
    int id = s.mk(MTKind.MT_BASE);
    s.types[id].base = ty;
    return id;
}

fn int MTypeStore.mk_box(MTypeStore* s, int inner, int ctx, Level lvl)
{
    int id = s.mk(MTKind.MT_BOX);
    MType* t = &s.types[id];
    t.args[0] = inner;
    t.arg_count = 1;
    t.ctx = ctx;
    t.level = lvl;
    return id;
}

fn int MTypeStore.mk_arrow(MTypeStore* s, int from, int to)
{
    int id = s.mk(MTKind.MT_ARROW);
    MType* t = &s.types[id];
    t.args[0] = from;
    t.args[1] = to;
    t.arg_count = 2;
    return id;
}

// Follow metavariable links.
fn int MTypeStore.resolve(MTypeStore* s, int t)
{
    if (t < 0 || (usz)t >= s.count) { return s.t_error; }
    int cur = t;
    int guard = 0;
    while (s.types[cur].link >= 0 && guard < 1024)
    {
        cur = s.types[cur].link;
        guard = guard + 1;
    }
    int walk = t;
    while (s.types[walk].link >= 0 && walk != cur)
    {
        int nxt = s.types[walk].link;
        s.types[walk].link = cur;
        walk = nxt;
    }
    return cur;
}

// Occurs check for metavariables: solving `?a := □(?a)` builds an infinite type.
fn bool MTypeStore.occurs(MTypeStore* s, int meta, int ty, int depth)
{
    if (depth > 64) { return true; }
    int r = s.resolve(ty);
    if (r == meta) { return true; }
    MType* t = &s.types[r];
    for (usz i = 0; i < t.arg_count; i++)
    {
        if (s.occurs(meta, t.args[i], depth + 1)) { return true; }
    }
    return false;
}

fn bool MTypeStore.solve(MTypeStore* s, int meta, int ty)
{
    int m = s.resolve(meta);
    int t = s.resolve(ty);
    if (m == t) { return true; }
    if (s.types[m].kind != MTKind.MT_UNKNOWN) { return false; }
    if (s.occurs(m, t, 0))
    {
        s.occurs_blocked = s.occurs_blocked + 1;
        return false;
    }
    s.types[m].link = t;
    s.types[m].solved = true;
    s.metas_solved = s.metas_solved + 1;
    return true;
}

// Unify two modal types.
fn bool MTypeStore.unify(MTypeStore* s, int a, int b, int depth)
{
    if (depth > 64) { return false; }
    int ra = s.resolve(a);
    int rb = s.resolve(b);
    if (ra == rb) { return true; }

    MType* x = &s.types[ra];
    MType* y = &s.types[rb];

    // Errors absorb, so one bad type does not cascade.
    if (x.kind == MTKind.MT_ERROR || y.kind == MTKind.MT_ERROR) { return true; }
    if (x.kind == MTKind.MT_UNKNOWN) { return s.solve(ra, rb); }
    if (y.kind == MTKind.MT_UNKNOWN) { return s.solve(rb, ra); }
    // MT_CODE is a box of unspecified shape: compatible with any box.
    if (x.kind == MTKind.MT_CODE && y.kind == MTKind.MT_BOX) { return true; }
    if (y.kind == MTKind.MT_CODE && x.kind == MTKind.MT_BOX) { return true; }
    if (x.kind != y.kind) { return false; }

    if (x.kind == MTKind.MT_BOX)
    {
        // Two boxes agree only at the same LEVEL: `□^1 i64` and `□^2 i64`
        // describe code for different stages and are not interchangeable.
        if (!theory_cmtt::level_eq(x.level, y.level)) { return false; }
    }
    if (x.kind == MTKind.MT_BASE)
    {
        return theory_term::term_eq(x.base, y.base, 0);
    }
    if (x.arg_count != y.arg_count) { return false; }
    for (usz i = 0; i < x.arg_count; i++)
    {
        if (!s.unify(x.args[i], y.args[i], depth + 1)) { return false; }
    }
    return true;
}

fn void MTypeStore.write(MTypeStore* s, int t, char* buf, usz cap, usz* pos, int depth)
{
    if (*pos + 8 >= cap || depth > 8) { return; }
    int r = s.resolve(t);
    MType* ty = &s.types[r];
    switch (ty.kind)
    {
        case MT_UNKNOWN:
        {
            append_str(buf, cap, pos, "?m");
            append_num(buf, cap, pos, ty.meta_id);
        }
        case MT_ERROR:   append_str(buf, cap, pos, "<error>");
        case MT_CODE:    append_str(buf, cap, pos, "<code>");
        case MT_BASE:
        {
            if (ty.base != null && ty.base.p.sptr != null)
            {
                for (usz i = 0; i < ty.base.p.slen && *pos + 1 < cap; i++)
                {
                    buf[*pos] = ty.base.p.sptr[i];
                    *pos = *pos + 1;
                }
            }
            else { append_str(buf, cap, pos, "?"); }
        }
        case MT_BOX:
        {
            append_str(buf, cap, pos, "[]^");
            append_num(buf, cap, pos, ty.level.base);
            append_str(buf, cap, pos, " ");
            if (ty.arg_count > 0) { s.write(ty.args[0], buf, cap, pos, depth + 1); }
        }
        case MT_ARROW:
        {
            if (ty.arg_count > 0) { s.write(ty.args[0], buf, cap, pos, depth + 1); }
            append_str(buf, cap, pos, " -> ");
            if (ty.arg_count > 1) { s.write(ty.args[1], buf, cap, pos, depth + 1); }
        }
        default:
            append_str(buf, cap, pos, "?");
    }
    buf[*pos] = 0;
}

fn void append_str(char* buf, usz cap, usz* pos, char* s)
{
    usz i = 0;
    while (s[i] != 0 && *pos + 1 < cap) { buf[*pos] = s[i]; *pos = *pos + 1; i = i + 1; }
    buf[*pos] = 0;
}

fn void append_num(char* buf, usz cap, usz* pos, int v)
{
    if (v < 0) { append_str(buf, cap, pos, "-"); v = -v; }
    char[24] tmp;
    int n = 0;
    if (v == 0) { tmp[0] = '0'; n = 1; }
    while (v > 0 && n < 24) { tmp[n] = (char)('0' + (v % 10)); v = v / 10; n = n + 1; }
    for (int i = n - 1; i >= 0 && *pos + 1 < cap; i--) { buf[*pos] = tmp[i]; *pos = *pos + 1; }
    buf[*pos] = 0;
}

// ── The bidirectional checker ───────────────────────────────────────────────
struct BidiChecker
{
    MTypeStore                    store;
    theory_cmtt::ContextPool      ctxs;
    theory_modal::SubtypeCache*   subtypes;

    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    Arena*                 arena;
    char*                  file;

    /*
     Storage for the rendered type in a mismatch diagnostic.

     A DiagBag keeps `hint` as a bare char* and prints it with %s long
     after the producing call returns, so this cannot be a local in
     report_mismatch -- which is where it was. Same dangling-stack-buffer
     bug as theory_pglcert.c3's witness rendering, found by the same
     sweep for `char[N]` locals reaching a diag call.

     Unlike that one this needed no torture case to be wrong; it was
     simply never observed, because --strict-types has to be on for the
     diagnostic to be emitted at all.
    */
    char[128]              mismatch_buf;

    int   current_ctx;
    Level current_level;

    usz synths;
    usz checks;
    usz box_intros;
    usz box_elims;
    usz runs;
    usz sub_uses;
    usz mismatches;
    usz open_box_runs;     // attempts to run a box with a non-empty context
    usz level_mismatches;
    bool strict;
}

fn void BidiChecker.init(BidiChecker* bc, Arena* a,
                         theory_modal::SubtypeCache* sc,
                         pfront_core::DiagBag* d,
                         pfront_core::Interner* it, char* file)
{
    bc.store.init();
    bc.ctxs.init();
    bc.subtypes = sc;
    bc.diags = d;
    bc.interner = it;
    bc.arena = a;
    bc.file = file;
    bc.current_level = theory_cmtt::level_const(0);
    bc.current_ctx = bc.ctxs.new_context(-1, bc.current_level);
    bc.synths = 0;
    bc.checks = 0;
    bc.box_intros = 0;
    bc.box_elims = 0;
    bc.runs = 0;
    bc.sub_uses = 0;
    bc.mismatches = 0;
    bc.open_box_runs = 0;
    bc.level_mismatches = 0;
    bc.strict = false;
}

// ── SYNTHESIS:  Γ ⊢ e ⇒ τ ───────────────────────────────────────────────────
fn int BidiChecker.synth(BidiChecker* bc, Node* e, int depth)
{
    if (e == null || depth > BD_MAX_DEPTH) { return bc.store.t_error; }
    bc.synths = bc.synths + 1;

    switch (e.kind)
    {
        case N_EXPR_INT:
        case N_EXPR_FLOAT:
        case N_EXPR_BOOL:
        case N_EXPR_CHAR:
        case N_EXPR_STRING:
        case N_EXPR_UNIT:
            return bc.store.mk_base(e.type_ann);

        case N_EXPR_IDENT:
        {
            theory_cmtt::CtxEntry* entry = bc.ctxs.lookup(bc.current_ctx, e.name_id);
            if (entry != null)
            {
                // Using a variable bound at another level requires it to have
                // come through a box.
                if (!theory_cmtt::level_eq(entry.level, bc.current_level)
                    && !entry.from_box)
                {
                    bc.level_mismatches = bc.level_mismatches + 1;
                }
                return bc.store.mk_base(entry.type_node);
            }
            if (e.resolved != null) { return bc.store.mk_base(e.resolved.type_ann); }
            return bc.store.fresh_meta();
        }

        // (BOX-I) in synthesis mode: the body's type is inferred, so the box
        // type is built from whatever comes back.
        case N_EXPR_QUOTE:
        {
            bc.box_intros = bc.box_intros + 1;
            Level inner = e.p.aux != 0
                        ? theory_cmtt::level_const(e.p.aux)
                        : theory_cmtt::level_shift(bc.current_level, 1);

            int box_ctx = bc.ctxs.new_context(bc.current_ctx, inner);
            bc.populate_box_ctx(e, box_ctx);

            Level saved_l = bc.current_level;
            int saved_c = bc.current_ctx;
            bc.current_level = inner;
            bc.current_ctx = box_ctx;

            int body_ty = bc.store.fresh_meta();
            Node* body = bc.box_body(e);
            if (body != null) { body_ty = bc.synth(body, depth + 1); }

            bc.current_level = saved_l;
            bc.current_ctx = saved_c;
            return bc.store.mk_box(body_ty, box_ctx, inner);
        }

        // (BOX-E): splicing opens a box, which requires context subsumption.
        case N_EXPR_SPLICE:
        {
            bc.box_elims = bc.box_elims + 1;
            Level outer = theory_cmtt::level_shift(bc.current_level, -1);
            Level saved = bc.current_level;
            bc.current_level = outer;

            int inner_ty = bc.store.fresh_meta();
            Node* operand = e.child(0);
            if (operand != null)
            {
                int got = bc.synth(operand, depth + 1);
                int r = bc.store.resolve(got);
                if (bc.store.types[r].kind == MTKind.MT_BOX)
                {
                    // Γ ⊇ Γ' — the current context must supply everything the
                    // box demands. Omitting this check is the classic CMTT
                    // unsoundness: a fragment could be opened where its free
                    // variables do not exist.
                    int need = bc.store.types[r].ctx;
                    if (need >= 0 && !bc.ctxs.subsumes(bc.current_ctx, need))
                    {
                        if (bc.strict)
                        {
                            bc.diags.error_hint(pfront_core::Phase.PH_RESOLVE,
                                                3300, e.line, e.col,
                                                "box environment is not available here",
                                                "the current scope lacks a variable the box captured",
                                                bc.file);
                        }
                    }
                    if (bc.store.types[r].arg_count > 0)
                    {
                        inner_ty = bc.store.types[r].args[0];
                    }
                }
            }
            bc.current_level = saved;
            return inner_ty;
        }

        case N_EXPR_CALL:
        {
            Node* callee = e.child(0);
            int fty = callee == null ? bc.store.fresh_meta() : bc.synth(callee, depth + 1);
            for (usz i = 1; i < e.child_count; i++) { bc.synth(e.children[i], depth + 1); }
            int r = bc.store.resolve(fty);
            if (bc.store.types[r].kind == MTKind.MT_ARROW
                && bc.store.types[r].arg_count > 1)
            {
                return bc.store.types[r].args[1];
            }
            return bc.store.fresh_meta();
        }

        case N_EXPR_IF:
        {
            bc.synth(e.child(0), depth + 1);
            int t = bc.synth(e.child(1), depth + 1);
            if (e.child_count >= 3)
            {
                int f = bc.synth(e.child(2), depth + 1);
                // Both branches must agree; the joint type is their unifier.
                if (!bc.store.unify(t, f, 0)) { bc.report_mismatch(e, t, f); }
            }
            return t;
        }

        case N_BLOCK:
        {
            int ctx = bc.ctxs.new_context(bc.current_ctx, bc.current_level);
            int saved = bc.current_ctx;
            if (ctx >= 0) { bc.current_ctx = ctx; }
            int last = bc.store.mk_base(null);
            for (usz i = 0; i < e.child_count; i++)
            {
                last = bc.synth_stmt(e.children[i], depth + 1);
            }
            bc.current_ctx = saved;
            return last;
        }

        default:
        {
            for (usz i = 0; i < e.child_count; i++)
            {
                Node* c = e.children[i];
                if (c == null || pfront_core::is_pattern(c.kind)) { continue; }
                bc.synth(c, depth + 1);
            }
            return e.type_ann != null ? bc.store.mk_base(e.type_ann)
                                      : bc.store.fresh_meta();
        }
    }
}

fn int BidiChecker.synth_stmt(BidiChecker* bc, Node* s, int depth)
{
    if (s == null) { return bc.store.mk_base(null); }
    if (s.kind == Nk.N_DECL_LET)
    {
        int declared = s.type_ann != null ? bc.store.mk_base(s.type_ann) : -1;
        for (usz i = 1; i < s.child_count; i++)
        {
            Node* c = s.children[i];
            if (c == null || pfront_core::is_pattern(c.kind)) { continue; }
            // CHECKING direction when an annotation is present, synthesis
            // otherwise. That is the whole point of being bidirectional.
            if (declared >= 0) { bc.check(c, declared, depth + 1); }
            else { declared = bc.synth(c, depth + 1); }
        }
        Node* pat = s.child(0);
        if (pat != null && pat.kind == Nk.N_PAT_IDENT && pat.name_id != 0)
        {
            bc.ctxs.extend(bc.current_ctx, pat.name_id, s.type_ann,
                           bc.current_level, theory_cmtt::Kind.KIND_TYPE, false);
        }
        return bc.store.mk_base(null);
    }
    return bc.synth(s, depth);
}

// ── CHECKING:  Γ ⊢ e ⇐ τ ────────────────────────────────────────────────────
fn bool BidiChecker.check(BidiChecker* bc, Node* e, int expected, int depth)
{
    if (e == null || depth > BD_MAX_DEPTH) { return false; }
    bc.checks = bc.checks + 1;

    int exp = bc.store.resolve(expected);
    MType* et = &bc.store.types[exp];

    // (BOX-I ⇐): checking a quotation against a box type pushes the inner
    // type into the body, which is what synthesis alone cannot do.
    if (e.kind == Nk.N_EXPR_QUOTE && et.kind == MTKind.MT_BOX)
    {
        bc.box_intros = bc.box_intros + 1;
        Level inner = et.level;
        int box_ctx = et.ctx >= 0 ? et.ctx
                                  : bc.ctxs.new_context(bc.current_ctx, inner);
        bc.populate_box_ctx(e, box_ctx);

        Level saved_l = bc.current_level;
        int saved_c = bc.current_ctx;
        bc.current_level = inner;
        bc.current_ctx = box_ctx;

        bool ok = true;
        Node* body = bc.box_body(e);
        if (body != null && et.arg_count > 0)
        {
            ok = bc.check(body, et.args[0], depth + 1);
        }

        bc.current_level = saved_l;
        bc.current_ctx = saved_c;
        return ok;
    }

    // An if-expression checks both branches against the expectation rather
    // than synthesising one and unifying, which gives better error locations.
    if (e.kind == Nk.N_EXPR_IF && e.child_count >= 3)
    {
        bc.synth(e.child(0), depth + 1);
        bool a = bc.check(e.child(1), expected, depth + 1);
        bool b = bc.check(e.child(2), expected, depth + 1);
        return a && b;
    }

    // (SUB): fall back to synthesis and check the subtype relation. This is
    // the ONLY non-syntax-directed rule, which is what keeps the system
    // deterministic everywhere else.
    int got = bc.synth(e, depth);
    bc.sub_uses = bc.sub_uses + 1;
    if (bc.store.unify(got, expected, 0)) { return true; }

    // Structural unification failed; try semantic subtyping on base types.
    int g = bc.store.resolve(got);
    if (bc.store.types[g].kind == MTKind.MT_BASE
        && et.kind == MTKind.MT_BASE
        && bc.subtypes != null)
    {
        if (theory_modal::subtype(bc.subtypes, bc.store.types[g].base, et.base, 0))
        {
            return true;
        }
    }
    bc.report_mismatch(e, expected, got);
    return false;
}

fn void BidiChecker.report_mismatch(BidiChecker* bc, Node* at, int expected, int got)
{
    bc.mismatches = bc.mismatches + 1;
    if (!bc.strict || at == null) { return; }
    /*
     `be` stays a local: it is rendered and never escapes. `bg` becomes
     the hint, so it must outlive this frame and lives on the checker.
    */
    char[128] be;
    usz pe = 0;
    usz pg = 0;
    be[0] = 0;
    bc.mismatch_buf[0] = 0;
    bc.store.write(expected, &be[0], 128, &pe, 0);
    bc.store.write(got, &bc.mismatch_buf[0], 128, &pg, 0);
    bc.diags.add(pfront_core::Severity.SEV_ERROR, pfront_core::Phase.PH_RESOLVE,
                 3301, at.line, at.col, "modal type mismatch",
                 &bc.mismatch_buf[0], bc.file);
}

// The box environment list, if the quotation carries one.
fn void BidiChecker.populate_box_ctx(BidiChecker* bc, Node* quote, int box_ctx)
{
    if (box_ctx < 0) { return; }
    for (usz i = 0; i < quote.child_count; i++)
    {
        Node* c = quote.children[i];
        if (c == null || c.kind != Nk.N_TY_EFFECT_ROW || c.p.aux != 2) { continue; }
        for (usz k = 0; k < c.child_count; k++)
        {
            Node* v = c.children[k];
            if (v == null || v.name_id == 0) { continue; }
            theory_cmtt::CtxEntry* outer = bc.ctxs.lookup(bc.current_ctx, v.name_id);
            Level lv = outer != null ? outer.level : bc.current_level;
            bc.ctxs.extend(box_ctx, v.name_id, v.type_ann, lv,
                           theory_cmtt::Kind.KIND_TYPE, true);
        }
    }
}

fn Node* BidiChecker.box_body(BidiChecker* bc, Node* quote)
{
    Node* body = null;
    for (usz i = 0; i < quote.child_count; i++)
    {
        Node* c = quote.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.N_TY_EFFECT_ROW && c.p.aux == 2) { continue; }
        body = c;
    }
    return body;
}

// (RUN): only a CLOSED box may be run. An open one depends on an environment
// that will not exist at runtime, so running it is meaningless.
fn bool BidiChecker.check_run(BidiChecker* bc, Node* e, int box_ty)
{
    bc.runs = bc.runs + 1;
    int r = bc.store.resolve(box_ty);
    MType* t = &bc.store.types[r];
    if (t.kind != MTKind.MT_BOX) { return false; }
    if (t.ctx < 0) { return true; }
    if ((usz)t.ctx >= bc.ctxs.context_count) { return true; }
    if (bc.ctxs.contexts[t.ctx].count == 0) { return true; }

    bc.open_box_runs = bc.open_box_runs + 1;
    if (bc.strict)
    {
        bc.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3302, e.line, e.col,
                            "cannot run an open code fragment",
                            "the box still depends on captured variables; splice it instead",
                            bc.file);
    }
    return false;
}

fn void BidiChecker.run(BidiChecker* bc, Node* root)
{
    if (root == null) { return; }
    for (usz i = 0; i < root.child_count; i++)
    {
        Node* d = root.children[i];
        if (d == null) { continue; }
        if (d.kind == Nk.N_DECL_FN)
        {
            int ctx = bc.ctxs.new_context(bc.current_ctx, bc.current_level);
            int saved = bc.current_ctx;
            if (ctx >= 0) { bc.current_ctx = ctx; }
            for (usz k = 0; k < d.child_count; k++)
            {
                Node* c = d.children[k];
                if (c == null) { continue; }
                if (c.kind == Nk.N_CLAUSE)
                {
                    for (usz j = 1; j < c.child_count; j++)
                    {
                        bc.synth(c.children[j], 0);
                    }
                }
                else if (c.kind == Nk.N_BLOCK) { bc.synth(c, 0); }
            }
            bc.current_ctx = saved;
        }
        else if (d.kind == Nk.N_MODULE) { bc.run(d); }
    }
}

fn void BidiChecker.report(BidiChecker* bc)
{
    printf("  bidirectional    : %d synth, %d check, %d subsumptions\n",
           (int)bc.synths, (int)bc.checks, (int)bc.sub_uses);
    printf("  modal types      : %d box-intro, %d box-elim, %d runs\n",
           (int)bc.box_intros, (int)bc.box_elims, (int)bc.runs);
    printf("  metavariables    : %d created, %d solved, %d occurs-blocked\n",
           (int)bc.store.metas_created, (int)bc.store.metas_solved,
           (int)bc.store.occurs_blocked);
    if (bc.mismatches > 0 || bc.open_box_runs > 0 || bc.level_mismatches > 0)
    {
        printf("  modal errors     : %d mismatches, %d open-box runs, %d level errors\n",
               (int)bc.mismatches, (int)bc.open_box_runs, (int)bc.level_mismatches);
    }
}
