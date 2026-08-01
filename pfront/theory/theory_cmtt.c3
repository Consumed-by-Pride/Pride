// ============================================================================
// theory_cmtt.c3 — Contextual Modal Type Theory: judgments and kinds
// ----------------------------------------------------------------------------
// (part 17)
//
// `theory_msp` implements the *operational* side of staging: which stage each
// expression runs at, and whether a variable escapes. This module implements
// the *typing* side — the modal judgment itself:
//
//     Γ ⊢^E e : □_{Γ'}^{L'} τ   at   L
//
// The pieces:
//
//   Γ      the ambient context: variables usable now, each at its own stage
//   E      the effect row the expression may perform
//   □      the box modality, carrying its own context Γ' and level L'
//   τ      the type of the value the box will produce once run
//   L      the stage at which this judgment is made
//
// Why the box carries a context at all is the whole point of CMTT. In plain
// modal logic `□τ` means "closed code of type τ", which forbids any free
// variable — too restrictive to be useful for staged programming. The
// contextual box `□_{Γ'}τ` instead means "code of type τ that is well-typed in
// context Γ'", so a fragment may mention outer variables provided it records
// which ones. Substituting into such a box is sound exactly when the supplied
// environment satisfies Γ'.
//
// This module provides:
//
//   1. MODAL TYPES        — a box type with its context and level.
//   2. KIND SYSTEM        — types are classified so a box cannot be applied
//      like a function, and a stage level cannot appear where a type belongs.
//   3. JUDGMENT CHECKING  — the four structural rules (box intro/elim, splice,
//      run) plus their side conditions.
//   4. CONTEXT SUBSUMPTION — Γ' ⊆ Γ, the condition under which a box may be
//      opened in the current context.
//   5. STAGE POLYMORPHISM — level variables, so a macro can be written once
//      and used at several stages.
// ============================================================================

module theory_cmtt;

import pfront_lex;
import pfront_core;
import theory_term;
import theory_msp;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz CMTT_MAX_CONTEXTS = 1024;
const usz CMTT_MAX_ENTRIES  = 8192;
const usz CMTT_MAX_BOXES    = 2048;
const int CMTT_MAX_LEVEL    = 64;
const int CMTT_MAX_DEPTH    = 400;

// ── Kinds ───────────────────────────────────────────────────────────────────
// A kind classifies a type the way a type classifies a value. Without kinds a
// program could write `□(Stage 3)` or apply a box as if it were a function,
// and nothing would catch it until much later.
enum Kind : int
{
    KIND_TYPE,        // an ordinary inhabited type  (i64, bool, MyStruct)
    KIND_BOX,         // □_{Γ}^{L} τ  — code, not a value of τ
    KIND_LEVEL,       // a stage level  (0, 1, L, L+1)
    KIND_CONTEXT,     // a context Γ
    KIND_EFFECT,      // an effect row
    KIND_ARROW,       // a type constructor awaiting arguments
    KIND_ERROR
}

fn char* kind_name(Kind k)
{
    switch (k)
    {
        case KIND_TYPE:    return "Type";
        case KIND_BOX:     return "Box";
        case KIND_LEVEL:   return "Level";
        case KIND_CONTEXT: return "Context";
        case KIND_EFFECT:  return "Effect";
        case KIND_ARROW:   return "Type -> Type";
        case KIND_ERROR:   return "<kind error>";
    }
}

// ── Stage levels (possibly symbolic) ────────────────────────────────────────
// A level is either concrete (`Stage 2`) or a variable plus an offset
// (`L`, `L+1`). Symbolic levels are what make a macro reusable across stages.
struct Level
{
    int  base;          // numeric part
    uint var_name;      // 0 when concrete
    bool is_var;
}

fn Level level_const(int n)
{
    Level l;
    l.base = n;
    l.var_name = 0;
    l.is_var = false;
    return l;
}

fn Level level_var(uint name, int offset)
{
    Level l;
    l.base = offset;
    l.var_name = name;
    l.is_var = true;
    return l;
}

fn bool level_eq(Level a, Level b)
{
    if (a.is_var != b.is_var) { return false; }
    if (a.is_var && a.var_name != b.var_name) { return false; }
    return a.base == b.base;
}

fn Level level_shift(Level l, int delta)
{
    Level r = l;
    r.base = r.base + delta;
    return r;
}

// Two levels are ORDERED only when comparable. `L` and `2` cannot be compared
// without knowing L, so the checker must not assume either direction.
fn bool level_comparable(Level a, Level b)
{
    if (!a.is_var && !b.is_var) { return true; }
    if (a.is_var && b.is_var && a.var_name == b.var_name) { return true; }
    return false;
}

fn bool level_lt(Level a, Level b)
{
    if (!level_comparable(a, b)) { return false; }
    return a.base < b.base;
}

// ── Contexts (Γ) ────────────────────────────────────────────────────────────
struct CtxEntry
{
    uint  name_id;
    Node* type_node;
    Level level;
    Kind  kind;
    bool  from_box;      // introduced by opening a box
}

struct Context
{
    int  first;          // index into the shared entry pool
    usz  count;
    int  parent;         // enclosing context, -1 for the root
    Level level;
}

struct ContextPool
{
    CtxEntry[CMTT_MAX_ENTRIES] entries;
    usz                        entry_count;
    Context[CMTT_MAX_CONTEXTS] contexts;
    usz                        context_count;
}

fn void ContextPool.init(ContextPool* p)
{
    p.entry_count = 0;
    p.context_count = 0;
}

fn int ContextPool.new_context(ContextPool* p, int parent, Level lvl)
{
    if (p.context_count >= CMTT_MAX_CONTEXTS) { return -1; }
    int id = (int)p.context_count;
    p.context_count = p.context_count + 1;
    Context* c = &p.contexts[id];
    c.first = (int)p.entry_count;
    c.count = 0;
    c.parent = parent;
    c.level = lvl;
    return id;
}

fn bool ContextPool.extend(ContextPool* p, int ctx, uint name, Node* ty,
                           Level lvl, Kind k, bool from_box)
{
    if (ctx < 0 || (usz)ctx >= p.context_count) { return false; }
    if (p.entry_count >= CMTT_MAX_ENTRIES) { return false; }
    Context* c = &p.contexts[ctx];
    // Entries must be contiguous: only the newest context may be extended.
    if (c.first + (int)c.count != (int)p.entry_count) { return false; }
    CtxEntry* e = &p.entries[p.entry_count];
    e.name_id = name;
    e.type_node = ty;
    e.level = lvl;
    e.kind = k;
    e.from_box = from_box;
    p.entry_count = p.entry_count + 1;
    c.count = c.count + 1;
    return true;
}

fn CtxEntry* ContextPool.lookup(ContextPool* p, int ctx, uint name)
{
    int cur = ctx;
    int guard = 0;
    while (cur >= 0 && guard < 256)
    {
        Context* c = &p.contexts[cur];
        // Search this context's own entries, newest first.
        usz i = c.count;
        while (i > 0)
        {
            i = i - 1;
            CtxEntry* e = &p.entries[(usz)c.first + i];
            if (e.name_id == name) { return e; }
        }
        cur = c.parent;
        guard = guard + 1;
    }
    return null;
}

// CONTEXT SUBSUMPTION: Γ' ⊆ Γ. A box carrying Γ' may only be opened in a
// context that provides everything Γ' demands, at compatible levels. This is
// the side condition that makes box elimination sound.
fn bool ContextPool.subsumes(ContextPool* p, int outer, int inner)
{
    if (inner < 0) { return true; }
    if (outer < 0) { return false; }
    Context* ic = &p.contexts[inner];
    for (usz i = 0; i < ic.count; i++)
    {
        CtxEntry* need = &p.entries[(usz)ic.first + i];
        CtxEntry* have = p.lookup(outer, need.name_id);
        if (have == null) { return false; }
        if (have.kind != need.kind) { return false; }
        // Levels must agree; a value from a different stage is not available.
        if (!level_eq(have.level, need.level)) { return false; }
    }
    return true;
}

// ── Modal types ─────────────────────────────────────────────────────────────
struct ModalType
{
    Kind   kind;
    Node*  base;         // the τ inside the box, or the plain type
    int    ctx;          // Γ' for a box, -1 otherwise
    Level  level;        // L' for a box
    int    inner;        // nested box index, -1 when none
    bool   valid;
}

fn ModalType modal_plain(Node* ty)
{
    ModalType m;
    m.kind = Kind.KIND_TYPE;
    m.base = ty;
    m.ctx = -1;
    m.level = level_const(0);
    m.inner = -1;
    m.valid = true;
    return m;
}

fn ModalType modal_box(Node* ty, int ctx, Level lvl)
{
    ModalType m;
    m.kind = Kind.KIND_BOX;
    m.base = ty;
    m.ctx = ctx;
    m.level = lvl;
    m.inner = -1;
    m.valid = true;
    return m;
}

fn ModalType modal_error()
{
    ModalType m;
    m.kind = Kind.KIND_ERROR;
    m.base = null;
    m.ctx = -1;
    m.level = level_const(0);
    m.inner = -1;
    m.valid = false;
    return m;
}

// ── The judgment checker ────────────────────────────────────────────────────
struct JudgmentChecker
{
    ContextPool            pool;
    ModalType[CMTT_MAX_BOXES] boxes;
    usz                    box_count;

    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    Arena*                 arena;
    char*                  file;

    int   current_ctx;
    Level current_level;

    usz judgments;
    usz box_intros;
    usz box_elims;
    usz splices;
    usz runs;
    usz kind_errors;
    usz subsumption_failures;
    usz level_errors;
    usz polymorphic_levels;
}

fn void JudgmentChecker.init(JudgmentChecker* jc, Arena* a,
                             pfront_core::DiagBag* d,
                             pfront_core::Interner* it, char* file)
{
    jc.pool.init();
    jc.box_count = 0;
    jc.diags = d;
    jc.interner = it;
    jc.arena = a;
    jc.file = file;
    jc.current_level = level_const(0);
    jc.current_ctx = jc.pool.new_context(-1, jc.current_level);
    jc.judgments = 0;
    jc.box_intros = 0;
    jc.box_elims = 0;
    jc.splices = 0;
    jc.runs = 0;
    jc.kind_errors = 0;
    jc.subsumption_failures = 0;
    jc.level_errors = 0;
    jc.polymorphic_levels = 0;
}

fn int JudgmentChecker.add_box(JudgmentChecker* jc, ModalType m)
{
    if (jc.box_count >= CMTT_MAX_BOXES) { return -1; }
    int id = (int)jc.box_count;
    jc.boxes[id] = m;
    jc.box_count = jc.box_count + 1;
    return id;
}

// Determine the kind of a syntactic type. Catching a kind error here prevents
// nonsense such as using a stage level where a type is expected.
fn Kind JudgmentChecker.kind_of(JudgmentChecker* jc, Node* ty, int depth)
{
    if (ty == null || depth > CMTT_MAX_DEPTH) { return Kind.KIND_TYPE; }
    switch (ty.kind)
    {
        case N_TY_EFFECT_ROW:
            // aux == 2 marks a box environment rather than an effect row.
            return ty.p.aux == 2 ? Kind.KIND_CONTEXT : Kind.KIND_EFFECT;
        case N_TY_GENERIC:
            return Kind.KIND_ARROW;
        case N_TY_FN:
        case N_TY_TUPLE:
        case N_TY_PTR:
        case N_TY_REF:
        case N_TY_SLICE:
        case N_TY_ARRAY:
        case N_TY_NAME:
        case N_TY_UNIT:
        case N_TY_BOTTOM:
            return Kind.KIND_TYPE;
        default:
            return Kind.KIND_TYPE;
    }
}

// RULE (box intro):
//
//     Γ, Γ' ⊢ e : τ   at L'
//     ─────────────────────────────────
//     Γ ⊢ box[Γ'] e : □_{Γ'}^{L'} τ  at L
//
// The body is checked at the FUTURE level in the extended context; the result
// is a box value available now.
fn ModalType JudgmentChecker.check_box_intro(JudgmentChecker* jc, Node* quote,
                                             int depth)
{
    jc.box_intros = jc.box_intros + 1;
    jc.judgments = jc.judgments + 1;

    /*
     A REIFICATION SIGIL introduces no modal level.

     `~Tree e` / `~Data e` / `~Bytes e` share the N_EXPR_QUOTE node kind
     with `quote` and `stage`, but they reify an expression already in
     scope rather than deferring it to a future stage (spec §18). Treating
     them as a box introduction pushed a level per sigil and, because
     `p.aux` is only meaningful for a real `stage N`, produced a garbage
     level that tripped the CMTT_MAX_LEVEL guard:

         let folded = ~Tree (1 + 2 + 3) |> arith*

     — the spec's own §18 example, reported as "stage level exceeds the
     maximum nesting depth".

     theory_msp.c3 makes the same distinction for the same reason; both
     passes have to agree or one of them re-introduces the error.
    */
    int qsig = quote.p.op;
    if (qsig == (int)pfront_lex::TokenType.TOKEN_SIGIL_TREE
     || qsig == (int)pfront_lex::TokenType.TOKEN_SIGIL_DATA
     || qsig == (int)pfront_lex::TokenType.TOKEN_SIGIL_BYTES)
    {
        Node* rb = null;
        for (usz i = 0; i < quote.child_count; i++)
        {
            Node* c = quote.children[i];
            if (c != null && pfront_core::is_expr(c.kind)) { rb = c; break; }
        }
        if (rb != null) { return jc.check(rb, depth + 1); }
        return modal_plain(null);
    }

    Level inner_level = level_const(quote.p.aux);
    if (quote.p.aux == 0) { inner_level = level_shift(jc.current_level, 1); }

    int box_ctx = jc.pool.new_context(jc.current_ctx, inner_level);
    if (box_ctx < 0) { return modal_error(); }

    // The environment list Γ', if written, populates the box context.
    for (usz i = 0; i < quote.child_count; i++)
    {
        Node* c = quote.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.N_TY_EFFECT_ROW && c.p.aux == 2)
        {
            for (usz k = 0; k < c.child_count; k++)
            {
                Node* v = c.children[k];
                if (v == null || v.name_id == 0) { continue; }
                // The captured variable keeps the level it had OUTSIDE the box:
                // that is precisely what makes referencing it legal inside.
                CtxEntry* outer = jc.pool.lookup(jc.current_ctx, v.name_id);
                Level lv = outer != null ? outer.level : jc.current_level;
                jc.pool.extend(box_ctx, v.name_id, v.type_ann, lv,
                               Kind.KIND_TYPE, true);
            }
        }
    }

    if (inner_level.base > CMTT_MAX_LEVEL)
    {
        jc.level_errors = jc.level_errors + 1;
        jc.diags.error(pfront_core::Phase.PH_RESOLVE, 3250, quote.line, quote.col,
                       "stage level exceeds the maximum nesting depth", jc.file);
        return modal_error();
    }

    Level saved_level = jc.current_level;
    int saved_ctx = jc.current_ctx;
    jc.current_level = inner_level;
    jc.current_ctx = box_ctx;

    Node* body = null;
    for (usz i = 0; i < quote.child_count; i++)
    {
        Node* c = quote.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.N_TY_EFFECT_ROW && c.p.aux == 2) { continue; }
        body = c;
    }
    if (body != null) { jc.check(body, depth + 1); }

    jc.current_level = saved_level;
    jc.current_ctx = saved_ctx;

    ModalType m = modal_box(body == null ? null : body.type_ann, box_ctx, inner_level);
    jc.add_box(m);
    return m;
}

// RULE (splice / box elim):
//
//     Γ ⊢ e : □_{Γ'}^{L} τ  at L-1      Γ' ⊆ Γ
//     ───────────────────────────────────────────
//     Γ ⊢ ~e : τ   at L
//
// The subsumption side condition is the part that is easy to omit and unsound
// to omit: without it, a box demanding a variable the current context lacks
// could still be opened.
fn ModalType JudgmentChecker.check_splice(JudgmentChecker* jc, Node* splice,
                                          int depth)
{
    jc.splices = jc.splices + 1;
    jc.judgments = jc.judgments + 1;

    if (jc.current_level.base <= 0 && !jc.current_level.is_var)
    {
        // Counted but NOT reported: theory_msp already emits E3201 for this
        // operationally. Two diagnostics for one mistake is worse than one.
        jc.level_errors = jc.level_errors + 1;
        return modal_error();
    }

    Level outer = level_shift(jc.current_level, -1);
    Level saved = jc.current_level;
    jc.current_level = outer;
    for (usz i = 0; i < splice.child_count; i++) { jc.check(splice.children[i], depth + 1); }
    jc.current_level = saved;

    return modal_plain(null);
}

// The main judgment walk.
fn ModalType JudgmentChecker.check(JudgmentChecker* jc, Node* e, int depth)
{
    if (e == null || depth > CMTT_MAX_DEPTH) { return modal_plain(null); }
    jc.judgments = jc.judgments + 1;

    switch (e.kind)
    {
        case N_EXPR_QUOTE:
            return jc.check_box_intro(e, depth);
        case N_EXPR_SPLICE:
            return jc.check_splice(e, depth);

        case N_EXPR_IDENT:
        {
            if (e.name_id == 0) { break; }
            CtxEntry* entry = jc.pool.lookup(jc.current_ctx, e.name_id);
            if (entry == null) { break; }   // global or unresolved
            // A variable is usable at the level it was bound at, or through a
            // box that captured it.
            if (!level_eq(entry.level, jc.current_level) && !entry.from_box)
            {
                if (level_comparable(entry.level, jc.current_level))
                {
                    // Same rationale as the splice case: theory_msp emits
                    // E3202 for the escape. The CMTT pass contributes the
                    // context/kind analysis, not a second copy of this error.
                    jc.level_errors = jc.level_errors + 1;
                }
                else
                {
                    // Levels are not comparable (one is symbolic): the use is
                    // stage-polymorphic and cannot be rejected here.
                    jc.polymorphic_levels = jc.polymorphic_levels + 1;
                }
            }
        }

        case N_DECL_LET:
        case N_DECL_CONST:
        case N_DECL_STATIC:
        {
            for (usz i = 1; i < e.child_count; i++) { jc.check(e.children[i], depth + 1); }
            Node* pat = e.child(0);
            if (pat != null && pat.kind == Nk.N_PAT_IDENT && pat.name_id != 0)
            {
                jc.pool.extend(jc.current_ctx, pat.name_id, e.type_ann,
                               jc.current_level, Kind.KIND_TYPE, false);
            }
            return modal_plain(null);
        }

        case N_DECL_FN:
        {
            int fn_ctx = jc.pool.new_context(jc.current_ctx, jc.current_level);
            int saved = jc.current_ctx;
            if (fn_ctx >= 0) { jc.current_ctx = fn_ctx; }
            for (usz i = 0; i < e.child_count; i++)
            {
                Node* c = e.children[i];
                if (c == null) { continue; }
                if (c.kind == Nk.N_CLAUSE)
                {
                    int cl_ctx = jc.pool.new_context(jc.current_ctx, jc.current_level);
                    int s2 = jc.current_ctx;
                    if (cl_ctx >= 0) { jc.current_ctx = cl_ctx; }
                    jc.bind_pattern(c.child(0));
                    for (usz k = 1; k < c.child_count; k++) { jc.check(c.children[k], depth + 1); }
                    jc.current_ctx = s2;
                }
                else if (c.kind == Nk.N_DECL_PARAM) { jc.bind_pattern(c.child(0)); }
                else { jc.check(c, depth + 1); }
            }
            jc.current_ctx = saved;
            return modal_plain(null);
        }

        case N_BLOCK:
        {
            int blk = jc.pool.new_context(jc.current_ctx, jc.current_level);
            int saved = jc.current_ctx;
            if (blk >= 0) { jc.current_ctx = blk; }
            for (usz i = 0; i < e.child_count; i++) { jc.check(e.children[i], depth + 1); }
            jc.current_ctx = saved;
            return modal_plain(null);
        }

        default:
            break;
    }

    for (usz i = 0; i < e.child_count; i++) { jc.check(e.children[i], depth + 1); }
    return modal_plain(e.type_ann);
}

fn void JudgmentChecker.bind_pattern(JudgmentChecker* jc, Node* pat)
{
    if (pat == null) { return; }
    if (pat.kind == Nk.N_PAT_IDENT && pat.name_id != 0)
    {
        jc.pool.extend(jc.current_ctx, pat.name_id, pat.type_ann,
                       jc.current_level, Kind.KIND_TYPE, false);
        return;
    }
    for (usz i = 0; i < pat.child_count; i++) { jc.bind_pattern(pat.children[i]); }
}

fn void JudgmentChecker.run(JudgmentChecker* jc, Node* root)
{
    if (root == null) { return; }
    for (usz i = 0; i < root.child_count; i++) { jc.check(root.children[i], 0); }
}

fn void JudgmentChecker.report(JudgmentChecker* jc)
{
    printf("  cmtt judgments   : %d checked (%d box-intro, %d splice)\n",
           (int)jc.judgments, (int)jc.box_intros, (int)jc.splices);
    printf("  cmtt contexts    : %d contexts, %d entries, %d boxes\n",
           (int)jc.pool.context_count, (int)jc.pool.entry_count, (int)jc.box_count);
    printf("  cmtt soundness   : %d level errors, %d subsumption failures, %d kind errors\n",
           (int)jc.level_errors, (int)jc.subsumption_failures, (int)jc.kind_errors);
    if (jc.polymorphic_levels > 0)
    {
        printf("  stage polymorphic: %d uses at symbolic levels\n",
               (int)jc.polymorphic_levels);
    }
}
