// ============================================================================
// theory_bridge.c3 — parser ↔ theory integration surface (part 27)
// ----------------------------------------------------------------------------
// The theory modules operate on the AST, but several of them need information
// the parser has and the AST alone does not preserve. This module is the
// bridge: it holds the small amount of glue that would otherwise be scattered
// across the parser and the theory passes, and keeps that glue testable.
//
// It provides:
//
//   1. SYNTAX CLASSIFICATION — which theory pass owns a given node, so the
//      pipeline can skip passes whose constructs do not appear at all. On a
//      file with no quotations there is no reason to run the stage checker.
//   2. FEATURE DETECTION     — a one-pass scan producing a feature bitmap,
//      used both for pass selection and for the report.
//   3. NODE CONSTRUCTION     — helpers the parser calls to build theory nodes
//      with the right payload conventions, so the encoding lives in one place
//      rather than being duplicated at each construction site.
//   4. PAYLOAD CONVENTIONS   — documented and enforced. Several theory nodes
//      overload `p.aux` for different meanings; getting that wrong is a silent
//      misinterpretation, so the accessors are centralised here.
// ============================================================================

module theory_bridge;

import pfront_lex;
import pfront_core;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn int printf(char* fmt, ...);

// ── Feature bitmap ──────────────────────────────────────────────────────────
// One bit per theory construct. Scanning once and consulting the bitmap is
// cheaper than every pass walking the tree to discover it has nothing to do.
const uint FEAT_QUOTE      = 1;
const uint FEAT_SPLICE     = 2;
const uint FEAT_BOX        = 4;
const uint FEAT_STAGE      = 8;
const uint FEAT_PERFORM    = 16;
const uint FEAT_HANDLE     = 32;
const uint FEAT_RESUME     = 64;
const uint FEAT_EFFECT_DECL = 128;
const uint FEAT_REWRITE    = 256;
const uint FEAT_PGEN       = 512;
const uint FEAT_DIALECT    = 1024;
const uint FEAT_IRDL       = 2048;
const uint FEAT_UB         = 4096;
const uint FEAT_COMPTIME   = 8192;
const uint FEAT_UNION_TY   = 16384;
const uint FEAT_INTERSECT_TY = 32768;
const uint FEAT_NEGATION_TY  = 65536;
const uint FEAT_GENERIC    = 131072;
const uint FEAT_MATCH      = 262144;
const uint FEAT_UNSAFE     = 524288;

// ── Payload conventions ─────────────────────────────────────────────────────
// `p.aux` is overloaded across node kinds. Every meaning is listed here so a
// reader never has to guess, and every access goes through an accessor so a
// change to the encoding is a one-line edit.
//
//   N_EXPR_QUOTE      p.aux = target stage level
//   N_EXPR_SPLICE     p.aux = resulting stage level
//   N_TY_EFFECT_ROW   p.aux = 2 marks a BOX ENVIRONMENT (Γ'), not an effect row
//   N_TY_EFFECT_ELEM  p.aux = 1 marks the open-row TAIL variable (`..r`)
//   N_DECL_FN         p.aux = 2 marks a PGEN clause set
//   N_DECL_INTERFACE  p.aux = 3 marks an IRDL lowering block
//   N_DECL_VARIANT    p.aux = 1 marks an explicit discriminant
//   N_EXPR_FIELD      p.aux = 1 marks a NUMERIC tuple index
const int AUX_BOX_ENV      = 2;
const int AUX_ROW_TAIL     = 1;
const int AUX_PGEN         = 2;
const int AUX_IRDL_BLOCK   = 3;
const int AUX_EXPLICIT_DISC = 1;
const int AUX_TUPLE_INDEX  = 1;

fn bool is_box_env(Node* n)
{
    return n != null && n.kind == Nk.N_TY_EFFECT_ROW && n.p.aux == AUX_BOX_ENV;
}

fn bool is_effect_row(Node* n)
{
    return n != null && n.kind == Nk.N_TY_EFFECT_ROW && n.p.aux != AUX_BOX_ENV;
}

fn bool is_row_tail(Node* n)
{
    return n != null && n.kind == Nk.N_TY_EFFECT_ELEM && n.p.aux == AUX_ROW_TAIL;
}

fn bool is_pgen_decl(Node* n)
{
    return n != null && n.kind == Nk.N_DECL_FN
        && (n.flags & pfront_core::NF_SYNTHETIC) != 0
        && n.p.aux == AUX_PGEN;
}

fn bool is_rewrite_decl(Node* n)
{
    return n != null && n.kind == Nk.N_DECL_FN
        && (n.flags & pfront_core::NF_SYNTHETIC) != 0
        && n.p.aux != AUX_PGEN;
}

fn bool is_irdl_block(Node* n)
{
    return n != null && n.kind == Nk.N_DECL_INTERFACE
        && (n.flags & pfront_core::NF_SYNTHETIC) != 0
        && n.p.aux == AUX_IRDL_BLOCK;
}

fn bool is_dialect_decl(Node* n)
{
    return n != null && n.kind == Nk.N_DECL_INTERFACE
        && (n.flags & pfront_core::NF_SYNTHETIC) != 0
        && n.p.aux != AUX_IRDL_BLOCK;
}

fn int stage_level_of(Node* n)
{
    if (n == null) { return 0; }
    if (n.kind != Nk.N_EXPR_QUOTE && n.kind != Nk.N_EXPR_SPLICE) { return 0; }
    return n.p.aux;
}

// ── Feature scan ────────────────────────────────────────────────────────────
struct FeatureScan
{
    uint features;
    usz  quotes;
    usz  splices;
    usz  boxes;
    usz  performs;
    usz  handles;
    usz  effect_decls;
    usz  rewrite_blocks;
    usz  pgen_blocks;
    usz  dialects;
    usz  irdl_blocks;
    usz  ub_sites;
    usz  comptime_blocks;
    usz  set_types;
    usz  generics;
    usz  matches;
    usz  nodes_scanned;
}

fn void FeatureScan.init(FeatureScan* f)
{
    f.features = 0;
    f.quotes = 0;
    f.splices = 0;
    f.boxes = 0;
    f.performs = 0;
    f.handles = 0;
    f.effect_decls = 0;
    f.rewrite_blocks = 0;
    f.pgen_blocks = 0;
    f.dialects = 0;
    f.irdl_blocks = 0;
    f.ub_sites = 0;
    f.comptime_blocks = 0;
    f.set_types = 0;
    f.generics = 0;
    f.matches = 0;
    f.nodes_scanned = 0;
}

fn void FeatureScan.scan(FeatureScan* f, Node* n, int depth)
{
    if (n == null || depth > 400) { return; }
    f.nodes_scanned = f.nodes_scanned + 1;

    switch (n.kind)
    {
        case N_EXPR_QUOTE:
        {
            f.features = f.features | FEAT_QUOTE;
            f.quotes = f.quotes + 1;
            if (n.p.aux != 0) { f.features = f.features | FEAT_STAGE; }
            // A quotation carrying an environment list is a CMTT box, which is
            // a strictly stronger construct than a bare quotation.
            for (usz i = 0; i < n.child_count; i++)
            {
                if (is_box_env(n.children[i]))
                {
                    f.features = f.features | FEAT_BOX;
                    f.boxes = f.boxes + 1;
                }
            }
        }
        case N_EXPR_SPLICE:
        {
            f.features = f.features | FEAT_SPLICE;
            f.splices = f.splices + 1;
        }
        case N_EXPR_PERFORM:
        {
            f.features = f.features | FEAT_PERFORM;
            f.performs = f.performs + 1;
        }
        case N_EXPR_HANDLE:
        {
            f.features = f.features | FEAT_HANDLE;
            f.handles = f.handles + 1;
        }
        case N_EXPR_RESUME:
            f.features = f.features | FEAT_RESUME;
        case N_DECL_EFFECT:
        {
            f.features = f.features | FEAT_EFFECT_DECL;
            f.effect_decls = f.effect_decls + 1;
        }
        case N_EXPR_UB:
        {
            f.features = f.features | FEAT_UB;
            f.ub_sites = f.ub_sites + 1;
        }
        case N_EXPR_UNSAFE:
            f.features = f.features | FEAT_UNSAFE;
        case N_EXPR_COMPTIME:
        {
            f.features = f.features | FEAT_COMPTIME;
            f.comptime_blocks = f.comptime_blocks + 1;
        }
        case N_EXPR_MATCH:
        {
            f.features = f.features | FEAT_MATCH;
            f.matches = f.matches + 1;
        }
        case N_TY_UNION:
        {
            f.features = f.features | FEAT_UNION_TY;
            f.set_types = f.set_types + 1;
        }
        case N_TY_INTERSECT:
        {
            f.features = f.features | FEAT_INTERSECT_TY;
            f.set_types = f.set_types + 1;
        }
        case N_TY_NEGATION:
        {
            f.features = f.features | FEAT_NEGATION_TY;
            f.set_types = f.set_types + 1;
        }
        case N_DECL_TYPEPARAM:
        {
            f.features = f.features | FEAT_GENERIC;
            f.generics = f.generics + 1;
        }
        case N_DECL_FN:
        {
            if (is_pgen_decl(n))
            {
                f.features = f.features | FEAT_PGEN;
                f.pgen_blocks = f.pgen_blocks + 1;
            }
            else if (is_rewrite_decl(n))
            {
                f.features = f.features | FEAT_REWRITE;
                f.rewrite_blocks = f.rewrite_blocks + 1;
            }
        }
        case N_DECL_INTERFACE:
        {
            if (is_irdl_block(n))
            {
                f.features = f.features | FEAT_IRDL;
                f.irdl_blocks = f.irdl_blocks + 1;
            }
            else if (is_dialect_decl(n))
            {
                f.features = f.features | FEAT_DIALECT;
                f.dialects = f.dialects + 1;
            }
        }
        default:
            break;
    }

    for (usz i = 0; i < n.child_count; i++) { f.scan(n.children[i], depth + 1); }
    if (n.type_ann != null) { f.scan(n.type_ann, depth + 1); }
}

fn bool FeatureScan.has(FeatureScan* f, uint feature)
{
    return (f.features & feature) != 0;
}

// Which theory passes are worth running on this program? Skipping a pass whose
// constructs are absent is not just a speed win: it keeps the report free of
// rows of zeroes that obscure the numbers that matter.
fn bool FeatureScan.needs_staging(FeatureScan* f)
{
    return f.has(FEAT_QUOTE) || f.has(FEAT_SPLICE) || f.has(FEAT_BOX)
        || f.has(FEAT_STAGE);
}

fn bool FeatureScan.needs_effects(FeatureScan* f)
{
    return f.has(FEAT_PERFORM) || f.has(FEAT_HANDLE) || f.has(FEAT_RESUME)
        || f.has(FEAT_EFFECT_DECL);
}

fn bool FeatureScan.needs_rewriting(FeatureScan* f)
{
    return f.has(FEAT_REWRITE);
}

fn bool FeatureScan.needs_irdl(FeatureScan* f)
{
    return f.has(FEAT_DIALECT) || f.has(FEAT_IRDL);
}

fn bool FeatureScan.needs_pgl(FeatureScan* f)
{
    return f.has(FEAT_PGEN) || f.has(FEAT_MATCH);
}

fn bool FeatureScan.needs_subtyping(FeatureScan* f)
{
    return f.has(FEAT_UNION_TY) || f.has(FEAT_INTERSECT_TY)
        || f.has(FEAT_NEGATION_TY);
}

fn bool FeatureScan.needs_partial_eval(FeatureScan* f)
{
    return f.has(FEAT_COMPTIME) || f.has(FEAT_STAGE);
}

fn bool FeatureScan.needs_mono(FeatureScan* f)
{
    return f.has(FEAT_GENERIC);
}

fn void FeatureScan.report(FeatureScan* f)
{
    printf("  theory features  : ");
    bool first = true;
    if (f.has(FEAT_QUOTE))        { printf("%squote", first ? "" : " "); first = false; }
    if (f.has(FEAT_SPLICE))       { printf("%ssplice", first ? "" : " "); first = false; }
    if (f.has(FEAT_BOX))          { printf("%sbox", first ? "" : " "); first = false; }
    if (f.has(FEAT_PERFORM))      { printf("%sperform", first ? "" : " "); first = false; }
    if (f.has(FEAT_HANDLE))       { printf("%shandle", first ? "" : " "); first = false; }
    if (f.has(FEAT_EFFECT_DECL))  { printf("%seffect", first ? "" : " "); first = false; }
    if (f.has(FEAT_REWRITE))      { printf("%srewrite", first ? "" : " "); first = false; }
    if (f.has(FEAT_PGEN))         { printf("%spgen", first ? "" : " "); first = false; }
    if (f.has(FEAT_DIALECT))      { printf("%sdialect", first ? "" : " "); first = false; }
    if (f.has(FEAT_IRDL))         { printf("%sirdl", first ? "" : " "); first = false; }
    if (f.has(FEAT_UB))           { printf("%sub", first ? "" : " "); first = false; }
    if (f.has(FEAT_COMPTIME))     { printf("%scomptime", first ? "" : " "); first = false; }
    if (f.has(FEAT_UNION_TY))     { printf("%sunion-ty", first ? "" : " "); first = false; }
    if (f.has(FEAT_INTERSECT_TY)) { printf("%sintersect-ty", first ? "" : " "); first = false; }
    if (f.has(FEAT_NEGATION_TY))  { printf("%snegation-ty", first ? "" : " "); first = false; }
    if (f.has(FEAT_GENERIC))      { printf("%sgeneric", first ? "" : " "); first = false; }
    if (first) { printf("(none)"); }
    printf("\n");
    printf("  theory counts    : %d quotes, %d performs, %d matches, %d set-types\n",
           (int)f.quotes, (int)f.performs, (int)f.matches, (int)f.set_types);
}

// ── Parser construction helpers ─────────────────────────────────────────────
// The parser calls these so the payload conventions above are applied in one
// place. Building a box environment by hand at each site is how encodings
// drift apart.
fn Node* make_box_env(Arena* a, int line, int col)
{
    Node* env = a.node(Nk.N_TY_EFFECT_ROW, line, col);
    if (env == null) { return null; }
    env.p.aux = AUX_BOX_ENV;
    return env;
}

fn Node* make_row_tail(Arena* a, uint name, int line, int col)
{
    Node* el = a.node(Nk.N_TY_EFFECT_ELEM, line, col);
    if (el == null) { return null; }
    el.name_id = name;
    el.p.aux = AUX_ROW_TAIL;
    return el;
}

fn Node* make_quote(Arena* a, Node* body, int stage, int line, int col)
{
    Node* q = a.node(Nk.N_EXPR_QUOTE, line, col);
    if (q == null) { return null; }
    q.p.aux = stage;
    a.add_child(q, body);
    return q;
}

fn Node* make_splice(Arena* a, Node* body, int stage, int line, int col)
{
    Node* s = a.node(Nk.N_EXPR_SPLICE, line, col);
    if (s == null) { return null; }
    s.p.aux = stage;
    a.add_child(s, body);
    return s;
}

// Build a union type from two operands, flattening nested unions so the DNF
// converter sees a wide node rather than a right-leaning chain.
fn Node* make_union(Arena* a, Node* x, Node* y)
{
    if (x == null) { return y; }
    if (y == null) { return x; }
    Node* u = a.node(Nk.N_TY_UNION, x.line, x.col);
    if (u == null) { return x; }
    if (x.kind == Nk.N_TY_UNION)
    {
        for (usz i = 0; i < x.child_count; i++) { a.add_child(u, x.children[i]); }
    }
    else { a.add_child(u, x); }
    if (y.kind == Nk.N_TY_UNION)
    {
        for (usz i = 0; i < y.child_count; i++) { a.add_child(u, y.children[i]); }
    }
    else { a.add_child(u, y); }
    return u;
}

fn Node* make_intersect(Arena* a, Node* x, Node* y)
{
    if (x == null) { return y; }
    if (y == null) { return x; }
    Node* n = a.node(Nk.N_TY_INTERSECT, x.line, x.col);
    if (n == null) { return x; }
    if (x.kind == Nk.N_TY_INTERSECT)
    {
        for (usz i = 0; i < x.child_count; i++) { a.add_child(n, x.children[i]); }
    }
    else { a.add_child(n, x); }
    if (y.kind == Nk.N_TY_INTERSECT)
    {
        for (usz i = 0; i < y.child_count; i++) { a.add_child(n, y.children[i]); }
    }
    else { a.add_child(n, y); }
    return n;
}

// ── Consistency audit ───────────────────────────────────────────────────────
// Verify the payload conventions actually hold in a built tree. A node using
// `p.aux` inconsistently is a silent misinterpretation, not a crash, so it is
// worth checking explicitly.
struct ConventionAudit
{
    pfront_core::DiagBag* diags;
    char* file;
    usz checked;
    usz violations;
}

fn void ConventionAudit.init(ConventionAudit* c, pfront_core::DiagBag* d, char* file)
{
    c.diags = d;
    c.file = file;
    c.checked = 0;
    c.violations = 0;
}

fn void ConventionAudit.walk(ConventionAudit* c, Node* n, int depth)
{
    if (n == null || depth > 400) { return; }
    c.checked = c.checked + 1;

    // A box environment must contain only identifiers.
    if (is_box_env(n))
    {
        for (usz i = 0; i < n.child_count; i++)
        {
            Node* v = n.children[i];
            if (v == null) { continue; }
            if (v.kind != Nk.N_EXPR_IDENT)
            {
                c.violations = c.violations + 1;
                c.diags.warn(pfront_core::Phase.PH_RESOLVE, 4110, v.line, v.col,
                             "box environment contains a non-identifier",
                             c.file);
            }
        }
    }

    // A quotation's stage level must be non-negative.
    if (n.kind == Nk.N_EXPR_QUOTE && n.p.aux < 0)
    {
        c.violations = c.violations + 1;
        c.diags.warn(pfront_core::Phase.PH_RESOLVE, 4111, n.line, n.col,
                     "quotation has a negative stage level", c.file);
    }

    // An effect row's tail marker must be the LAST element: `[..r, IO]` is not
    // meaningful, since the tail absorbs everything after it.
    if (is_effect_row(n))
    {
        bool seen_tail = false;
        for (usz i = 0; i < n.child_count; i++)
        {
            Node* el = n.children[i];
            if (el == null) { continue; }
            if (seen_tail)
            {
                c.violations = c.violations + 1;
                c.diags.warn(pfront_core::Phase.PH_RESOLVE, 4112, el.line, el.col,
                             "effect appears after the row tail variable",
                             c.file);
                break;
            }
            if (is_row_tail(el)) { seen_tail = true; }
        }
    }

    for (usz i = 0; i < n.child_count; i++) { c.walk(n.children[i], depth + 1); }
    if (n.type_ann != null) { c.walk(n.type_ann, depth + 1); }
}

fn void ConventionAudit.report(ConventionAudit* c)
{
    if (c.violations == 0) { return; }
    printf("  convention audit : %d nodes, %d payload violations\n",
           (int)c.checked, (int)c.violations);
}
