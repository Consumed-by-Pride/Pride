// ============================================================================
// theory_check.c3 — gradual ("untyped") checking + theory pipeline (part 16)
// ----------------------------------------------------------------------------
// Two things live here.
//
// PART A — GRADUAL / UNTYPED CHECKING
//   `pfront_infer` is a Hindley-Milner checker: it wants every expression to
//   have one principal type. Real Pride code is not fully annotated, and a
//   strict checker on under-annotated code produces noise rather than signal.
//
//   The gradual checker takes the other approach. Every expression gets a
//   COARSE SORT rather than a precise type:
//
//       Unknown · Scalar · Aggregate · Pointer · Callable · Effectful · Never
//
//   Sorts form a lattice with `Unknown` as top: anything is consistent with
//   Unknown, so an unannotated program never produces a diagnostic. What it
//   still catches are *sort-level* contradictions that are wrong under any
//   typing — calling a scalar, indexing a function, branching on an aggregate.
//   Those are real bugs regardless of annotation coverage, which is why this
//   pass can be on by default while `--strict-types` cannot.
//
//   This is the "consistency" relation of gradual typing: `~` is reflexive and
//   symmetric but deliberately NOT transitive, since `Int ~ Unknown` and
//   `Unknown ~ Bool` must not imply `Int ~ Bool`.
//
// PART B — THEORY PIPELINE
//   One entry point that runs the whole theory layer in dependency order and
//   reports it as a unit, so the driver stays a driver.
// ============================================================================

module theory_check;

import pfront_lex;
import pfront_core;
import theory_term;
import theory_trs;
import theory_msp;
import theory_irdl;
import theory_modal;
import theory_cmtt;
import theory_effects;
import theory_verify;
import theory_egraph;
import theory_stage;
import theory_rowinfer;
import theory_bidi;
import theory_irdlverify;
import theory_pglcert;
import theory_subtype;
import theory_bridge;
import theory_absint;
import theory_opt;
import theory_live;
import theory_poly;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn void* malloc(usz size);
extern fn long  clock();
const long CLOCKS_PER_MS = 1000;   // CLOCKS_PER_SEC is 1e6 on Linux
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const int CHECK_MAX_DEPTH = 400;

// ════════════════════════════════════════════════════════════════════════════
// PART A — GRADUAL SORTS
// ════════════════════════════════════════════════════════════════════════════
enum Sort : int
{
    SORT_UNKNOWN,     // top of the lattice: consistent with everything
    SORT_NEVER,       // bottom: diverges, consistent with everything
    SORT_UNIT,
    SORT_BOOL,
    SORT_INT,
    SORT_FLOAT,
    SORT_CHAR,
    SORT_STRING,
    SORT_POINTER,
    SORT_AGGREGATE,   // struct / tuple / array / slice
    SORT_CALLABLE,    // function or closure
    SORT_EFFECT,      // an effect operation
    SORT_TYPE         // a type used as a value (constructor position)
}

fn char* sort_name(Sort s)
{
    switch (s)
    {
        case SORT_UNKNOWN:   return "unknown";
        case SORT_NEVER:     return "never";
        case SORT_UNIT:      return "unit";
        case SORT_BOOL:      return "bool";
        case SORT_INT:       return "int";
        case SORT_FLOAT:     return "float";
        case SORT_CHAR:      return "char";
        case SORT_STRING:    return "string";
        case SORT_POINTER:   return "pointer";
        case SORT_AGGREGATE: return "aggregate";
        case SORT_CALLABLE:  return "callable";
        case SORT_EFFECT:    return "effect";
        case SORT_TYPE:      return "type";
    }
}

// Gradual CONSISTENCY. Reflexive and symmetric, deliberately not transitive:
// Unknown is compatible with everything, which is what lets partially
// annotated code pass without inventing types for it.
fn bool consistent(Sort a, Sort b)
{
    if (a == b) { return true; }
    if (a == Sort.SORT_UNKNOWN || b == Sort.SORT_UNKNOWN) { return true; }
    if (a == Sort.SORT_NEVER || b == Sort.SORT_NEVER) { return true; }
    // Numeric tower: integers and floats mix in arithmetic contexts.
    if (a == Sort.SORT_INT && b == Sort.SORT_FLOAT) { return true; }
    if (a == Sort.SORT_FLOAT && b == Sort.SORT_INT) { return true; }
    // char is an integer at the representation level.
    if (a == Sort.SORT_CHAR && b == Sort.SORT_INT) { return true; }
    if (a == Sort.SORT_INT && b == Sort.SORT_CHAR) { return true; }
    // A pointer is an address; comparing or casting to an integer is normal in
    // a systems language.
    if (a == Sort.SORT_POINTER && b == Sort.SORT_INT) { return true; }
    if (a == Sort.SORT_INT && b == Sort.SORT_POINTER) { return true; }
    // Strings and slices share a representation.
    if (a == Sort.SORT_STRING && b == Sort.SORT_AGGREGATE) { return true; }
    if (a == Sort.SORT_AGGREGATE && b == Sort.SORT_STRING) { return true; }
    // A callable is reachable through a pointer.
    if (a == Sort.SORT_CALLABLE && b == Sort.SORT_POINTER) { return true; }
    if (a == Sort.SORT_POINTER && b == Sort.SORT_CALLABLE) { return true; }
    return false;
}

// Join two sorts: the most precise sort consistent with both, else Unknown.
fn Sort join_sorts(Sort a, Sort b)
{
    if (a == b) { return a; }
    if (a == Sort.SORT_NEVER) { return b; }
    if (b == Sort.SORT_NEVER) { return a; }
    if (a == Sort.SORT_UNKNOWN || b == Sort.SORT_UNKNOWN) { return Sort.SORT_UNKNOWN; }
    if ((a == Sort.SORT_INT && b == Sort.SORT_FLOAT)
     || (a == Sort.SORT_FLOAT && b == Sort.SORT_INT)) { return Sort.SORT_FLOAT; }
    return Sort.SORT_UNKNOWN;
}

fn Sort sort_of_type(Node* t, int depth)
{
    if (t == null || depth > 32) { return Sort.SORT_UNKNOWN; }
    switch (t.kind)
    {
        case N_TY_UNIT:      return Sort.SORT_UNIT;
        case N_TY_BOTTOM:    return Sort.SORT_NEVER;
        case N_TY_PTR:
        case N_TY_REF:       return Sort.SORT_POINTER;
        case N_TY_SLICE:
        case N_TY_ARRAY:
        case N_TY_TUPLE:     return Sort.SORT_AGGREGATE;
        case N_TY_FN:        return Sort.SORT_CALLABLE;
        case N_TY_INFER:     return Sort.SORT_UNKNOWN;
        case N_TY_NAME:
        {
            char* s = t.p.sptr;
            usz n = t.p.slen;
            if (s == null || n == 0) { return Sort.SORT_UNKNOWN; }
            if ((s[0] == 'i' || s[0] == 'u') && n >= 2 && s[1] >= '0' && s[1] <= '9')
            {
                return Sort.SORT_INT;
            }
            if (s[0] == 'f' && n >= 2 && s[1] >= '0' && s[1] <= '9') { return Sort.SORT_FLOAT; }
            if (n == 4 && s[0] == 'b' && s[1] == 'o') { return Sort.SORT_BOOL; }
            if (n == 4 && s[0] == 'c' && s[1] == 'h') { return Sort.SORT_CHAR; }
            if (n == 3 && s[0] == 's' && s[1] == 't') { return Sort.SORT_STRING; }
            if (n == 3 && s[0] == 'p' && s[1] == 't') { return Sort.SORT_POINTER; }
            if (n == 3 && s[0] == 'u' && s[1] == 's') { return Sort.SORT_INT; }
            if (n == 3 && s[0] == 'i' && s[1] == 's') { return Sort.SORT_INT; }
            // A resolved struct/enum name denotes an aggregate.
            if (t.resolved != null)
            {
                Nk k = t.resolved.kind;
                if (k == Nk.N_DECL_STRUCT || k == Nk.N_DECL_UNION
                 || k == Nk.N_DECL_ENUM) { return Sort.SORT_AGGREGATE; }
            }
            return Sort.SORT_UNKNOWN;
        }
        default:
            return Sort.SORT_UNKNOWN;
    }
}

struct GradualChecker
{
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;

    usz exprs;
    usz sort_errors;
    usz calls_checked;
    usz indexes_checked;
    usz conditions_checked;
    usz unknown_sorts;
    bool strict;
}

fn void GradualChecker.init(GradualChecker* g, pfront_core::DiagBag* d,
                            pfront_core::Interner* it, char* file)
{
    g.diags = d;
    g.interner = it;
    g.file = file;
    g.exprs = 0;
    g.sort_errors = 0;
    g.calls_checked = 0;
    g.indexes_checked = 0;
    g.conditions_checked = 0;
    g.unknown_sorts = 0;
    g.strict = false;
}

// Infer a coarse sort. Deliberately shallow: this must never be expensive, and
// Unknown is always a safe answer.
fn Sort GradualChecker.sort_of(GradualChecker* g, Node* e, int depth)
{
    if (e == null || depth > CHECK_MAX_DEPTH) { return Sort.SORT_UNKNOWN; }
    g.exprs = g.exprs + 1;

    switch (e.kind)
    {
        case N_EXPR_INT:         return Sort.SORT_INT;
        case N_EXPR_FLOAT:       return Sort.SORT_FLOAT;
        case N_EXPR_BOOL:        return Sort.SORT_BOOL;
        case N_EXPR_CHAR:        return Sort.SORT_CHAR;
        case N_EXPR_STRING:      return Sort.SORT_STRING;
        case N_EXPR_BYTES:       return Sort.SORT_AGGREGATE;
        case N_EXPR_UNIT:        return Sort.SORT_UNIT;
        case N_EXPR_NULL:        return Sort.SORT_POINTER;
        case N_EXPR_UNREACHABLE:
        case N_EXPR_TRAP:        return Sort.SORT_NEVER;
        case N_EXPR_TUPLE:
        case N_EXPR_ARRAY:
        case N_EXPR_STRUCT_LIT:  return Sort.SORT_AGGREGATE;
        case N_EXPR_LAMBDA:      return Sort.SORT_CALLABLE;
        case N_EXPR_REF:         return Sort.SORT_POINTER;
        case N_EXPR_ALLOC:       return Sort.SORT_POINTER;
        case N_EXPR_SIZEOF:
        case N_EXPR_ALIGNOF:
        case N_EXPR_OFFSETOF:    return Sort.SORT_INT;
        case N_EXPR_PERFORM:     return Sort.SORT_UNKNOWN;

        case N_EXPR_IDENT:
        {
            if (e.resolved == null) { g.unknown_sorts = g.unknown_sorts + 1; return Sort.SORT_UNKNOWN; }
            Node* d = e.resolved;
            if (d.kind == Nk.N_DECL_FN || d.kind == Nk.N_DECL_EXTERN_FN)
            {
                return Sort.SORT_CALLABLE;
            }
            if (d.kind == Nk.N_DECL_EFFECT_OP) { return Sort.SORT_EFFECT; }
            if (d.kind == Nk.N_DECL_STRUCT || d.kind == Nk.N_DECL_ENUM
             || d.kind == Nk.N_DECL_UNION) { return Sort.SORT_TYPE; }
            if (d.kind == Nk.N_DECL_VARIANT) { return Sort.SORT_AGGREGATE; }
            if (d.type_ann != null) { return sort_of_type(d.type_ann, 0); }
            return Sort.SORT_UNKNOWN;
        }

        case N_EXPR_CAST:
            return sort_of_type(e.type_ann, 0);

        case N_EXPR_DEREF:
            return Sort.SORT_UNKNOWN;   // whatever the pointee is

        case N_EXPR_BINARY:
        {
            Tk op = (Tk)e.p.op;
            switch (op)
            {
                case TOKEN_EQEQ:
                case TOKEN_NEQ:
                case TOKEN_LT:
                case TOKEN_LTEQ:
                case TOKEN_GT:
                case TOKEN_GTEQ:
                case TOKEN_AMPAMP:
                case TOKEN_PIPEPIPE:
                case TOKEN_KW_AND:
                case TOKEN_KW_OR:
                    return Sort.SORT_BOOL;
                default:
                    break;
            }
            Sort l = g.sort_of(e.child(0), depth + 1);
            Sort r = g.sort_of(e.child(1), depth + 1);
            // Pointer arithmetic keeps the pointer sort.
            if (l == Sort.SORT_POINTER || r == Sort.SORT_POINTER) { return Sort.SORT_POINTER; }
            return join_sorts(l, r);
        }

        case N_EXPR_UNARY:
        {
            Tk op = (Tk)e.p.op;
            if (op == Tk.TOKEN_BANG || op == Tk.TOKEN_KW_NOT) { return Sort.SORT_BOOL; }
            return g.sort_of(e.child(0), depth + 1);
        }

        case N_EXPR_CALL:
        {
            // The result sort of a call is the callee's return sort when known.
            Node* callee = e.child(0);
            if (callee != null && callee.resolved != null)
            {
                Node* sig = callee.resolved.type_ann;
                if (sig != null && sig.kind == Nk.N_TY_FN)
                {
                    for (usz i = 0; i < sig.child_count; i++)
                    {
                        Node* c = sig.children[i];
                        if (c != null && c.kind == Nk.N_TY_CONSTRAINT)
                        {
                            return sort_of_type(c.child(0), 0);
                        }
                    }
                }
            }
            return Sort.SORT_UNKNOWN;
        }

        case N_EXPR_IF:
        {
            if (e.child_count < 3) { return Sort.SORT_UNIT; }
            return join_sorts(g.sort_of(e.child(1), depth + 1),
                              g.sort_of(e.child(2), depth + 1));
        }

        case N_BLOCK:
        {
            if (e.child_count == 0) { return Sort.SORT_UNIT; }
            return g.sort_of(e.children[e.child_count - 1], depth + 1);
        }

        case N_EXPR_WHILE:
        case N_EXPR_FOR:         return Sort.SORT_UNIT;

        default:
            return Sort.SORT_UNKNOWN;
    }
}

// Check for sort-level contradictions: things wrong under ANY typing.
fn void GradualChecker.walk(GradualChecker* g, Node* n, int depth)
{
    if (n == null || depth > CHECK_MAX_DEPTH) { return; }

    switch (n.kind)
    {
        case N_EXPR_CALL:
        {
            Node* callee = n.child(0);
            if (callee != null)
            {
                Sort cs = g.sort_of(callee, depth + 1);
                g.calls_checked = g.calls_checked + 1;
                // Calling a value that is definitely not callable.
                if (cs != Sort.SORT_UNKNOWN && cs != Sort.SORT_CALLABLE
                    && cs != Sort.SORT_POINTER && cs != Sort.SORT_TYPE
                    && cs != Sort.SORT_EFFECT && cs != Sort.SORT_NEVER)
                {
                    g.sort_errors = g.sort_errors + 1;
                    g.report(n, "this value is called but is not a function", cs);
                }
            }
        }

        case N_EXPR_INDEX:
        {
            Node* base = n.child(0);
            if (base != null)
            {
                Sort bs = g.sort_of(base, depth + 1);
                g.indexes_checked = g.indexes_checked + 1;
                if (bs == Sort.SORT_BOOL || bs == Sort.SORT_CALLABLE
                 || bs == Sort.SORT_UNIT)
                {
                    g.sort_errors = g.sort_errors + 1;
                    g.report(n, "this value is indexed but is not a container", bs);
                }
            }
        }

        case N_EXPR_IF:
        case N_EXPR_WHILE:
        {
            Node* cond = n.child(0);
            if (cond != null)
            {
                Sort cs = g.sort_of(cond, depth + 1);
                g.conditions_checked = g.conditions_checked + 1;
                if (!consistent(cs, Sort.SORT_BOOL))
                {
                    g.sort_errors = g.sort_errors + 1;
                    g.report(cond, "condition is not a boolean", cs);
                }
            }
        }

        case N_EXPR_DEREF:
        {
            Node* p = n.child(0);
            if (p != null)
            {
                Sort ps = g.sort_of(p, depth + 1);
                if (!consistent(ps, Sort.SORT_POINTER))
                {
                    g.sort_errors = g.sort_errors + 1;
                    g.report(n, "this value is dereferenced but is not a pointer", ps);
                }
            }
        }

        default:
            break;
    }
    for (usz i = 0; i < n.child_count; i++) { g.walk(n.children[i], depth + 1); }
}

fn void GradualChecker.report(GradualChecker* g, Node* at, char* msg, Sort found)
{
    if (at == null) { return; }
    if (g.strict)
    {
        g.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3240, at.line, at.col,
                           msg, sort_name(found), g.file);
    }
    else
    {
        g.diags.warn(pfront_core::Phase.PH_RESOLVE, 4060, at.line, at.col, msg, g.file);
    }
}

fn void GradualChecker.summary(GradualChecker* g)
{
    printf("  gradual sorts    : %d exprs, %d contradictions\n",
           (int)g.exprs, (int)g.sort_errors);
    printf("  sort coverage    : %d calls, %d indexes, %d conditions checked\n",
           (int)g.calls_checked, (int)g.indexes_checked, (int)g.conditions_checked);
}

// ════════════════════════════════════════════════════════════════════════════
// PART B — THEORY PIPELINE
// ════════════════════════════════════════════════════════════════════════════
// Runs the theory layer in dependency order:
//   register dialects and effects  →  stage-check  →  rewrite  →  lower  →
//   continuation-normalise  →  UB  →  gradual sorts
//
// Ordering matters. Staging must run before rewriting, because a rewrite that
// moves a term across a quotation boundary would invalidate the stage
// annotations the checker relies on. Lowering runs after rewriting so a
// dialect action can itself be simplified.
struct TheoryPipeline
{
    Arena*                 arena;
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;

    theory_term::HashCons*     hc;
    theory_trs::RuleSet*       rules;
    theory_trs::Rewriter*      rewriter;
    theory_msp::StageChecker*  stages;
    theory_irdl::DialectTable* dialects;
    theory_irdl::PgenCompiler* pgen;
    theory_modal::ScopedRegistry* effects;
    theory_modal::ContTree*    conttree;
    theory_modal::UbTracker*   ub;
    theory_modal::SubtypeCache* subtypes;
    theory_cmtt::JudgmentChecker* cmtt;
    theory_effects::HandlerCheck* handlers;
    theory_effects::RowInference* rows;
    theory_effects::Monomorphiser* mono;
    theory_verify::Verifier*      verifier;
    theory_egraph::Saturator*     saturator;
    theory_stage::PartialEvaluator* peval;
    theory_stage::ComptimeRunner* comptime;
    theory_rowinfer::RowInferencer* rowinfer;
    theory_bidi::BidiChecker*     bidi;
    theory_irdlverify::IrdlVerifier* irdlv;
    theory_pglcert::PglCertifier* pglcert;
    theory_subtype::SemanticSubtyper* semsub;
    theory_subtype::MatchRefiner*     refiner;
    theory_bridge::FeatureScan        features;
    theory_bridge::ConventionAudit    audit;
    theory_absint::AbstractInterpreter* absint;
    theory_opt::Optimizer*     opt;
    theory_live::LivenessAnalysis* live;
    theory_poly::Polymorphism* poly;
    GradualChecker             gradual;

    bool enabled;
    bool strict_sorts;
    usz  passes_run;
    theory_verify::Snapshot before_snap;
    theory_verify::Snapshot after_snap;
    bool has_diff;
    bool use_egraph;
    bool optimize;
    int  opt_level;
    bool timing;              // --time-passes: per-pass wall clock
    bool dump_cfg;            // --dump-cfg: print the last function's CFG
    long[40] pass_ms;
    char*[40] pass_name;
    usz  timed;
}

fn bool TheoryPipeline.init(TheoryPipeline* tp, Arena* a, pfront_core::DiagBag* d,
                            pfront_core::Interner* it, char* file)
{
    tp.arena = a;
    tp.diags = d;
    tp.interner = it;
    tp.file = file;
    tp.enabled = true;
    tp.strict_sorts = false;
    tp.passes_run = 0;
    tp.has_diff = false;
    tp.use_egraph = true;

    tp.hc = (theory_term::HashCons*)malloc(theory_term::HashCons::size);
    tp.rules = (theory_trs::RuleSet*)malloc(theory_trs::RuleSet::size);
    tp.rewriter = (theory_trs::Rewriter*)malloc(theory_trs::Rewriter::size);
    tp.stages = (theory_msp::StageChecker*)malloc(theory_msp::StageChecker::size);
    tp.dialects = (theory_irdl::DialectTable*)malloc(theory_irdl::DialectTable::size);
    tp.pgen = (theory_irdl::PgenCompiler*)malloc(theory_irdl::PgenCompiler::size);
    tp.effects = (theory_modal::ScopedRegistry*)malloc(theory_modal::ScopedRegistry::size);
    tp.conttree = (theory_modal::ContTree*)malloc(theory_modal::ContTree::size);
    tp.ub = (theory_modal::UbTracker*)malloc(theory_modal::UbTracker::size);
    tp.subtypes = (theory_modal::SubtypeCache*)malloc(theory_modal::SubtypeCache::size);
    tp.cmtt = (theory_cmtt::JudgmentChecker*)malloc(theory_cmtt::JudgmentChecker::size);
    tp.handlers = (theory_effects::HandlerCheck*)malloc(theory_effects::HandlerCheck::size);
    tp.rows = (theory_effects::RowInference*)malloc(theory_effects::RowInference::size);
    tp.mono = (theory_effects::Monomorphiser*)malloc(theory_effects::Monomorphiser::size);
    tp.verifier = (theory_verify::Verifier*)malloc(theory_verify::Verifier::size);
    tp.saturator = (theory_egraph::Saturator*)malloc(theory_egraph::Saturator::size);
    tp.peval = (theory_stage::PartialEvaluator*)malloc(theory_stage::PartialEvaluator::size);
    tp.comptime = (theory_stage::ComptimeRunner*)malloc(theory_stage::ComptimeRunner::size);
    tp.rowinfer = (theory_rowinfer::RowInferencer*)malloc(theory_rowinfer::RowInferencer::size);
    tp.bidi = (theory_bidi::BidiChecker*)malloc(theory_bidi::BidiChecker::size);
    tp.irdlv = (theory_irdlverify::IrdlVerifier*)malloc(theory_irdlverify::IrdlVerifier::size);
    tp.pglcert = (theory_pglcert::PglCertifier*)malloc(theory_pglcert::PglCertifier::size);
    tp.semsub = (theory_subtype::SemanticSubtyper*)malloc(theory_subtype::SemanticSubtyper::size);
    tp.refiner = (theory_subtype::MatchRefiner*)malloc(theory_subtype::MatchRefiner::size);
    tp.absint = (theory_absint::AbstractInterpreter*)malloc(theory_absint::AbstractInterpreter::size);
    tp.opt = (theory_opt::Optimizer*)malloc(theory_opt::Optimizer::size);
    tp.live = (theory_live::LivenessAnalysis*)malloc(theory_live::LivenessAnalysis::size);
    tp.poly = (theory_poly::Polymorphism*)malloc(theory_poly::Polymorphism::size);

    if (tp.hc == null || tp.rules == null || tp.rewriter == null || tp.stages == null
     || tp.dialects == null || tp.pgen == null || tp.effects == null
     || tp.conttree == null || tp.ub == null || tp.subtypes == null
     || tp.cmtt == null || tp.handlers == null || tp.rows == null
     || tp.mono == null || tp.verifier == null
     || tp.saturator == null || tp.peval == null || tp.comptime == null
     || tp.rowinfer == null || tp.bidi == null || tp.irdlv == null
     || tp.pglcert == null || tp.semsub == null || tp.refiner == null
     || tp.absint == null)
    {
        return false;
    }

    tp.hc.init();
    tp.rules.init();
    tp.rewriter.init(a, tp.rules, d, it, file, tp.hc);
    tp.stages.init(a, d, it, file);
    tp.dialects.init(a, d, it, file);
    tp.pgen.init(a, d, it, file);
    tp.effects.init(d, it, file);
    tp.conttree.init();
    tp.ub.init(d, it, file);
    tp.subtypes.init();
    tp.cmtt.init(a, d, it, file);
    tp.handlers.init(d, it, file);
    tp.rows.init(tp.handlers, d, it, file);
    tp.mono.init(a, d, it, file);
    tp.verifier.init(d, it, file);
    tp.saturator.init(a, tp.rules, d, file);
    tp.peval.init(a, d, it, file);
    tp.comptime.init(tp.peval, d, file);
    tp.rowinfer.init(a, tp.handlers, d, it, file);
    tp.bidi.init(a, tp.subtypes, d, it, file);
    tp.irdlv.init(d, it, file);
    tp.pglcert.init(d, it, file);
    tp.semsub.init(a, d, it, file);
    tp.refiner.init(tp.semsub, d, file);
    tp.features.init();
    tp.audit.init(d, file);
    tp.absint.init(a, d, it, file);
    if (tp.opt != null) { tp.opt.init(a, d, it, file); }
    if (tp.live != null) { tp.live.init(d, it, file); }
    if (tp.poly != null) { tp.poly.init(a, d, it, file); }
    tp.optimize = true;
    tp.opt_level = 2;
    tp.timing = false;
    tp.dump_cfg = false;
    tp.timed = 0;
    tp.gradual.init(d, it, file);
    return true;
}

fn void TheoryPipeline.destroy(TheoryPipeline* tp)
{
    if (tp.hc != null) { free((void*)tp.hc); }
    if (tp.rules != null) { free((void*)tp.rules); }
    if (tp.rewriter != null) { free((void*)tp.rewriter); }
    if (tp.stages != null) { free((void*)tp.stages); }
    if (tp.dialects != null) { free((void*)tp.dialects); }
    if (tp.pgen != null) { free((void*)tp.pgen); }
    if (tp.effects != null) { free((void*)tp.effects); }
    if (tp.conttree != null) { free((void*)tp.conttree); }
    if (tp.ub != null) { free((void*)tp.ub); }
    if (tp.subtypes != null) { free((void*)tp.subtypes); }
    if (tp.cmtt != null) { free((void*)tp.cmtt); }
    if (tp.handlers != null) { free((void*)tp.handlers); }
    if (tp.rows != null) { free((void*)tp.rows); }
    if (tp.mono != null) { free((void*)tp.mono); }
    if (tp.verifier != null) { free((void*)tp.verifier); }
    if (tp.saturator != null) { tp.saturator.destroy(); free((void*)tp.saturator); }
    if (tp.peval != null) { free((void*)tp.peval); }
    if (tp.comptime != null) { free((void*)tp.comptime); }
    if (tp.rowinfer != null) { free((void*)tp.rowinfer); }
    if (tp.bidi != null) { free((void*)tp.bidi); }
    if (tp.irdlv != null) { tp.irdlv.destroy(); free((void*)tp.irdlv); }
    if (tp.pglcert != null) { free((void*)tp.pglcert); }
    if (tp.semsub != null) { free((void*)tp.semsub); }
    if (tp.refiner != null) { free((void*)tp.refiner); }
    if (tp.absint != null) { tp.absint.destroy(); free((void*)tp.absint); }
    if (tp.opt != null) { tp.opt.destroy(); free((void*)tp.opt); }
    if (tp.live != null) { tp.live.destroy(); free((void*)tp.live); }
    if (tp.poly != null) { tp.poly.destroy(); free((void*)tp.poly); }
}

// Record the elapsed time of one pass. Called only when --time-passes is on,
// so the clock() syscall never costs anything in a normal build.
fn long TheoryPipeline.tick(TheoryPipeline* tp, char* name, long start)
{
    if (!tp.timing) { return 0; }
    long now = clock();
    if (tp.timed < 40)
    {
        tp.pass_name[tp.timed] = name;
        tp.pass_ms[tp.timed] = (now - start) / CLOCKS_PER_MS;
        tp.timed = tp.timed + 1;
    }
    return now;
}

fn Node* TheoryPipeline.run(TheoryPipeline* tp, Node* root)
{
    if (!tp.enabled || root == null) { return root; }
    tp.gradual.strict = tp.strict_sorts;

    // 0. One scan to learn which constructs are present. Passes whose
    //    constructs are absent are skipped: that keeps the report free of rows
    //    of zeroes and avoids walking the tree for nothing.
    long t0 = tp.timing ? clock() : 0;
    tp.features.scan(root, 0);
    tp.audit.walk(root, 0);
    t0 = tp.tick("scan+audit", t0);
    tp.passes_run = tp.passes_run + 1;

    // 1. Registration: dialects and effect operations must exist before any
    //    use of them can be validated.
    tp.dialects.register_dialects(root, 0);
    /*
     Validate dialect USES against the source tree, before any pass
     rewrites it. See the note at the lowering step below.
    */
    tp.dialects.validate_uses(root, 0);
    tp.effects.register_effects(root, 0);
    t0 = tp.tick("register", t0);
    tp.passes_run = tp.passes_run + 2;

    // 2. Staging soundness, BEFORE any rewriting moves terms around.
    tp.stages.walk(root, 0);
    t0 = tp.tick("stages", t0);
    tp.passes_run = tp.passes_run + 1;

    // 2b. The CMTT typing judgment, which subsumes the operational check with
    //     contexts, kinds and levels. Runs alongside rather than instead of
    //     the stage walk: the two catch different failure modes.
    tp.cmtt.run(root);
    t0 = tp.tick("cmtt", t0);
    tp.passes_run = tp.passes_run + 1;

    // 2c. Handler coverage and effect rows.
    tp.handlers.collect(root, 0);
    tp.handlers.walk(root, 0);
    tp.rows.walk(root, 0);
    t0 = tp.tick("handlers+rows", t0);
    tp.passes_run = tp.passes_run + 2;

    // 2d. Generic instantiation census for the middle end.
    tp.mono.scan(root, 0);
    t0 = tp.tick("mono", t0);
    tp.passes_run = tp.passes_run + 1;

    // 2d-bis. POLYMORPHISM. The mono census above counts instantiations;
    //     this pass actually SOLVES them — unifying declared parameter types
    //     against the call's actual arguments to produce a substitution, then
    //     applying it to build a real monomorphic signature per instance.
    //     Runs before rewriting so the types it reads are the ones the user
    //     wrote.
    if (tp.poly != null)
    {
        tp.poly.run(root);
        tp.passes_run = tp.passes_run + 1;
    }

    // 2e. Bidirectional modal typing: box types become inferrable, not just
    //     checkable. Runs before rewriting for the same reason staging does.
    tp.bidi.strict = tp.strict_sorts;
    tp.bidi.run(root);
    t0 = tp.tick("bidi", t0);
    tp.passes_run = tp.passes_run + 1;

    // 2f. Principal-type effect inference over rows.
    tp.rowinfer.strict = tp.strict_sorts;
    tp.rowinfer.run(root);
    t0 = tp.tick("rowinfer", t0);
    tp.passes_run = tp.passes_run + 1;

    // Snapshot before any transformation, so the diff can localise a bug to
    // the pass that caused it.
    theory_verify::Snapshot before = theory_verify::snapshot(root);

    // 3. Term rewriting to a normal form.
    /*
     PGL DECISION TREES, built BEFORE the rewriter runs.

     PgenCompiler was allocated, initialised and reported, and
     build_from_clauses was called from nowhere -- so
     "pgl trees: 0 built, 0 nodes" was printed on every compilation of
     every file in the project and was structurally incapable of
     printing anything else. The pass existed; nothing ran it. Found
     by writing a static graph compiler, the program that is supposed
     to lean on PGL hardest.

     Placement is load-bearing. run_fixpoint REWRITES THE TREE IN
     PLACE, so a rule set's own clause patterns have already been
     rewritten by the time it returns: reading them afterwards gave
     `x * 1 -> x` a pattern column of N_EXPR_IDENT (the rewritten
     result) instead of N_EXPR_BINARY, every row looked like a bare
     variable, and every rule after the first was reported as
     unreachable. The decision tree has to be built from the patterns
     as WRITTEN.
    */
    tp.build_pgen_trees(root, 0);
    t0 = tp.tick("pgen-trees", t0);
    tp.passes_run = tp.passes_run + 1;

    tp.rules.collect(root, 0);
    if (tp.rules.count > 0)
    {
        tp.rules.critical_pairs(tp.diags, tp.file, false);
        root = tp.rewriter.run_fixpoint(root, 8);
        t0 = tp.tick("trs-rewrite", t0);
        tp.passes_run = tp.passes_run + 1;
    }

    // 3b. Compile-time evaluation: `comptime` blocks are forced, static loops
    //     unrolled, and static subexpressions folded away.
    root = tp.comptime.run(root, 0);
    root = tp.peval.specialise(root, 0);
    t0 = tp.tick("comptime+peval", t0);
    tp.passes_run = tp.passes_run + 2;

    // 3c. Equality saturation. Unlike the destructive rewriter this keeps every
    //     equivalent form, so the outcome does not depend on rule order.
    if (tp.rules.count > 0 && tp.use_egraph)
    {
        root = tp.saturator.optimise(root);
        t0 = tp.tick("egraph", t0);
        tp.passes_run = tp.passes_run + 1;
    }

    /*
     4. Dialect LOWERING, after rewriting so the actions it substitutes
        are already simplified.

     Validation does NOT happen here. It moved up to just after
     registration, because by this point the rewriter, comptime folding
     and partial evaluation have all rebuilt parts of the tree and a
     dialect call written in the source may no longer be present in the
     shape validate_uses recognises. On the graph-compiler test that
     showed as "2 dialects, 6 opcodes, 0 uses validated" for a file whose
     every dialect call was still there in the AST dump -- arity checking
     and unknown-opcode diagnosis were simply not reaching them.

     Lowering stays late; diagnosing the user's source stays early.
    */
    if (tp.dialects.opcode_count > 0)
    {
        root = tp.dialects.lower_tree(root, 0);
        tp.passes_run = tp.passes_run + 1;
    }

    // 5. Continuation-tree normalisation for scoped effects.
    tp.conttree.root = tp.conttree.build(root, tp.effects, 0);
    tp.conttree.normalise(16);
    t0 = tp.tick("conttree", t0);
    tp.passes_run = tp.passes_run + 1;

    // 6. Explicit UB accounting.
    tp.ub.walk(root, 0);
    t0 = tp.tick("ub", t0);
    tp.passes_run = tp.passes_run + 1;

    // 7. Gradual sort checking.
    tp.gradual.walk(root, 0);
    t0 = tp.tick("gradual", t0);
    tp.passes_run = tp.passes_run + 1;

    // 7b. IRDL verification traits: SSA form, dominance, purity, termination.
    tp.irdlv.strict = tp.strict_sorts;
    tp.irdlv.run(root);
    t0 = tp.tick("irdlverify", t0);
    tp.passes_run = tp.passes_run + 1;

    // 7c. PGL certificates: exhaustiveness with a named counter-example, and
    //     reachability per clause.
    tp.pglcert.strict = tp.strict_sorts;
    tp.pglcert.walk(root, 0);
    t0 = tp.tick("pglcert", t0);
    tp.passes_run = tp.passes_run + 1;

    // 7d. Set-theoretic subtyping: decide union/intersection/negation by
    //     reduction to emptiness over a DNF, then use it to find match arms
    //     whose pattern type cannot overlap the scrutinee.
    tp.refiner.walk(root, 0);
    t0 = tp.tick("subtype-refine", t0);
    tp.passes_run = tp.passes_run + 1;

    // 7e. Abstract interpretation: intervals, signs and nullness to a
    //     fixpoint with widening. Feeds bounds elision and the range metadata
    //     the LLVM backend can act on.
    tp.absint.strict = tp.strict_sorts;
    tp.absint.run(root);
    t0 = tp.tick("absint", t0);
    tp.passes_run = tp.passes_run + 1;

    // 7e-bis. LIVENESS + SEMI-PRUNED classification. Builds a real CFG per
    //     function, solves backward dataflow to a fixpoint, and splits every
    //     variable into "needs a phi" (live across an edge) and "block-local"
    //     (never crosses one). This is the SP of SP-ERM-e-SSI, and the
    //     optimizer below consumes the dead-definition set it produces.
    if (tp.poly != null) { tp.poly.report(); }
    if (tp.live != null)
    {
        tp.live.run(root);
        tp.passes_run = tp.passes_run + 1;
    }

    // 7f. THE OPTIMIZER. Runs last among the analyses so it consumes every
    //     fact they produced, and before the verifier so a bad rewrite is
    //     caught by the snapshot diff rather than shipped.
    //
    //     Pride is untyped: none of the analyses above can reject a program,
    //     so the only thing they are FOR is this pass. Constant folding,
    //     algebraic identities, branch folding and three kinds of dead code
    //     all run to a fixpoint here.
    if (tp.opt != null && tp.optimize)
    {
        tp.opt.level = tp.opt_level;
        tp.opt.live = tp.live;
        root = tp.opt.run(root);
        t0 = tp.tick("optimizer", t0);
        tp.passes_run = tp.passes_run + 1;
    }

    // 8. Handler-arm linearity for scoped operations.
    tp.check_handlers(root, 0);
    tp.passes_run = tp.passes_run + 1;

    // 9. Verify the transformations did not corrupt the tree. Running this
    //    here means a rewrite bug is reported at the rewrite, not three passes
    //    downstream where the cause is invisible.
    tp.verifier.run(root);
    t0 = tp.tick("verifier", t0);
    tp.after_snap = theory_verify::snapshot(root);
    tp.before_snap = before;
    tp.has_diff = true;
    tp.passes_run = tp.passes_run + 1;

    return root;
}

/*
 Build a PGL decision tree for every clause set in the program.

 The tree is built for its ANALYSIS, not to replace the match: it is what
 the redundancy and exhaustiveness reports are computed from, and a1
 lowers matches independently as a sequential chain. Building it here
 means those reports describe a real structure rather than an empty one.
*/
fn void TheoryPipeline.build_pgen_trees(TheoryPipeline* tp, Node* n, int depth)
{
    if (n == null || depth > CHECK_MAX_DEPTH) { return; }
    /*
     A `pgen` declaration is an N_DECL_FN carrying `p.aux == 2` (see
     parse_pgen_decl), so the N_DECL_FN case already covers it -- there is
     no separate node kind, and assuming one was a guess that did not
     compile.
    */
    if (n.kind == Nk.N_EXPR_MATCH || n.kind == Nk.N_DECL_FN)
    {
        // Only build when there is more than one clause: a single arm has
        // no decision to make, and counting it would inflate the report
        // with trees that discriminate nothing.
        usz clauses = 0;
        for (usz i = 0; i < n.child_count; i++)
        {
            Node* c = n.children[i];
            if (c == null) { continue; }
            if (c.kind == Nk.N_CLAUSE || c.kind == Nk.N_MATCH_ARM)
            {
                clauses = clauses + 1;
            }
        }
        if (clauses > 1)
        {
            tp.pgen.build_from_clauses(n);
            tp.pgen.report_redundant(n);
        }
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        tp.build_pgen_trees(n.children[i], depth + 1);
    }
}

fn void TheoryPipeline.check_handlers(TheoryPipeline* tp, Node* n, int depth)
{
    if (n == null || depth > CHECK_MAX_DEPTH) { return; }
    if (n.kind == Nk.N_HANDLER_ARM) { tp.effects.check_linearity(n, depth); }
    for (usz i = 0; i < n.child_count; i++) { tp.check_handlers(n.children[i], depth + 1); }
}

fn void TheoryPipeline.report(TheoryPipeline* tp)
{
    printf("=== theory layer (%d passes) ===\n", (int)tp.passes_run);
    tp.stages.report();
    tp.rules.report();
    tp.rewriter.report();
    tp.hc.report();
    tp.dialects.report();
    tp.pgen.report();
    tp.effects.report();
    tp.conttree.report();
    tp.ub.report();
    tp.subtypes.report();
    tp.cmtt.report();
    tp.handlers.report();
    tp.rows.report();
    tp.mono.report();
    tp.gradual.summary();
    tp.bidi.report();
    tp.rowinfer.report();
    tp.peval.report();
    tp.comptime.report();
    tp.saturator.report();
    tp.irdlv.report();
    tp.pglcert.report();
    tp.semsub.report();
    tp.refiner.report();
    tp.absint.report();
    if (tp.poly != null) { tp.poly.report(); }
    if (tp.live != null)
    {
        if (tp.dump_cfg) { tp.live.dump_cfg(); }
        tp.live.report();
    }
    if (tp.opt != null && tp.optimize) { tp.opt.report(); }
    if (tp.timing)
    {
        printf("=== pass timing (ms) ===\n");
        long total = 0;
        for (usz i = 0; i < tp.timed; i++) { total = total + tp.pass_ms[i]; }
        for (usz i = 0; i < tp.timed; i++)
        {
            if (tp.pass_ms[i] <= 0) { continue; }
            int pct = total > 0 ? (int)((tp.pass_ms[i] * 100) / total) : 0;
            printf("  %-18s %5d ms  %3d%%\n", tp.pass_name[i], (int)tp.pass_ms[i], pct);
        }
        printf("  %-18s %5d ms\n", "TOTAL", (int)total);
    }
    tp.features.report();
    tp.audit.report();
    tp.verifier.report();
    if (tp.has_diff)
    {
        theory_verify::DiffResult d =
            theory_verify::diff_snapshots(tp.before_snap, tp.after_snap);
        // The optimizer knows exactly how many `let`s it deleted; pass that
        // in so a legitimate DCE removal is not reported as a mystery.
        usz accounted = 0;
        if (tp.opt != null) { accounted = tp.opt.dead_stores; }
        theory_verify::report_diff_accounted(d, tp.before_snap, tp.after_snap,
                                             tp.diags, tp.file, accounted);
    }
}
