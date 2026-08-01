// ============================================================================
// pfront_narrow.c3 — flow-sensitive type narrowing (part 28)
// ----------------------------------------------------------------------------
// The single largest gap between a toy checker and a real one is FLOW
// SENSITIVITY. A declared type is what a variable may hold *somewhere*; what
// it holds *here* is usually more precise, and every practical checker
// exploits that:
//
//     let x : i64 ∪ str = ...
//     if x is i64
//       x + 1            -- x is i64 on this branch, so `+` is legal
//     else
//       str_len(x)       -- x is str on the other branch
//
// Without narrowing the first branch is a type error and the language is
// unusable with union types. TypeScript calls this control-flow analysis; Zig
// gets a weaker version from comptime-known conditions; Rust gets it from
// pattern matching. Pride needs all three shapes.
//
// This module implements:
//
//   1. FACTS            — a proposition about a binding that holds on one edge
//                         of the control-flow graph.
//   2. GUARD ANALYSIS   — reading facts out of a condition, including `&&`,
//                         `||`, `!`, comparisons against null, `is` tests, and
//                         discriminant tests on enums.
//   3. FLOW ENVIRONMENT — a scoped stack of narrowings with proper join at
//                         merge points. Joining is where unsoundness usually
//                         creeps in: the merge of two branches must be the
//                         UNION of their narrowings, never one of them.
//   4. ASSIGNMENT KILL  — writing to a binding invalidates every fact about
//                         it. Missing this is the classic soundness hole.
//   5. UNREACHABILITY   — a branch whose guard contradicts a known fact is
//                         dead, which feeds both diagnostics and codegen.
//
// The lattice is deliberately simple: facts are conjunctions of atomic
// propositions, and the join is set intersection. That is weaker than a full
// abstract domain but it is decidable, fast, and predictable — three
// properties that matter more than precision for a construct programmers must
// reason about in their heads.
// ============================================================================

module pfront_narrow;

import pfront_lex;
import pfront_core;
import pfront_types;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;
alias Types = pfront_types::TypeTable;
alias TyKind = pfront_types::TyKind;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz NR_MAX_FACTS   = 4096;
const usz NR_MAX_FRAMES  = 512;
const usz NR_MAX_BINDERS = 2048;
const int NR_MAX_DEPTH   = 300;

// ── Facts ───────────────────────────────────────────────────────────────────
enum FactKind : int
{
    F_IS_TYPE,        // x has type T on this path
    F_NOT_TYPE,       // x definitely does NOT have type T
    F_IS_NULL,
    F_NOT_NULL,
    F_IS_VARIANT,     // x is enum variant V
    F_NOT_VARIANT,
    F_IS_TRUE,        // a boolean binding is known true
    F_IS_FALSE,
    F_RANGE_LO,       // x >= k
    F_RANGE_HI,       // x <= k
    F_EQ_CONST,       // x == k
    F_NE_CONST
}

struct Fact
{
    FactKind kind;
    Node*    binder;      // the declaration this constrains
    uint     name_id;
    int      type_id;     // for F_IS_TYPE / F_NOT_TYPE
    uint     variant;     // for F_IS_VARIANT
    long     value;       // for range / equality facts
    int      frame;
}

struct FlowEnv
{
    Fact[NR_MAX_FACTS] facts;
    usz                count;
    usz[NR_MAX_FRAMES] frame_base;
    usz                frame_count;

    usz facts_added;
    usz facts_killed;
    usz joins;
    usz contradictions;
}

fn void FlowEnv.init(FlowEnv* e)
{
    e.count = 0;
    e.frame_count = 0;
    e.facts_added = 0;
    e.facts_killed = 0;
    e.joins = 0;
    e.contradictions = 0;
    e.push();
}

fn void FlowEnv.push(FlowEnv* e)
{
    if (e.frame_count >= NR_MAX_FRAMES) { return; }
    e.frame_base[e.frame_count] = e.count;
    e.frame_count = e.frame_count + 1;
}

fn void FlowEnv.pop(FlowEnv* e)
{
    if (e.frame_count == 0) { return; }
    e.frame_count = e.frame_count - 1;
    e.count = e.frame_base[e.frame_count];
}

fn usz FlowEnv.mark(FlowEnv* e) { return e.count; }
fn void FlowEnv.reset(FlowEnv* e, usz m) { if (m <= e.count) { e.count = m; } }

fn bool FlowEnv.add(FlowEnv* e, Fact f)
{
    if (e.count >= NR_MAX_FACTS) { return false; }
    f.frame = (int)e.frame_count - 1;
    e.facts[e.count] = f;
    e.count = e.count + 1;
    e.facts_added = e.facts_added + 1;
    return true;
}

// Writing to a binding invalidates everything known about it. Forgetting this
// is the classic narrowing soundness hole: after `x = something_else`, a fact
// proved before the assignment no longer holds.
fn usz FlowEnv.kill(FlowEnv* e, Node* binder)
{
    if (binder == null) { return 0; }
    usz removed = 0;
    usz w = 0;
    for (usz r = 0; r < e.count; r++)
    {
        if (e.facts[r].binder == binder) { removed = removed + 1; continue; }
        e.facts[w] = e.facts[r];
        w = w + 1;
    }
    e.count = w;
    e.facts_killed = e.facts_killed + removed;
    return removed;
}

// Look up the narrowed type of a binding, or -1 when it is not narrowed.
fn int FlowEnv.narrowed_type(FlowEnv* e, Node* binder)
{
    // The most recent fact wins: later narrowings refine earlier ones.
    usz i = e.count;
    while (i > 0)
    {
        i = i - 1;
        Fact* f = &e.facts[i];
        if (f.binder != binder) { continue; }
        if (f.kind == FactKind.F_IS_TYPE) { return f.type_id; }
    }
    return -1;
}

fn bool FlowEnv.knows_not_null(FlowEnv* e, Node* binder)
{
    usz i = e.count;
    while (i > 0)
    {
        i = i - 1;
        Fact* f = &e.facts[i];
        if (f.binder != binder) { continue; }
        if (f.kind == FactKind.F_NOT_NULL) { return true; }
        if (f.kind == FactKind.F_IS_NULL) { return false; }
    }
    return false;
}

fn bool FlowEnv.knows_variant(FlowEnv* e, Node* binder, uint variant)
{
    usz i = e.count;
    while (i > 0)
    {
        i = i - 1;
        Fact* f = &e.facts[i];
        if (f.binder != binder) { continue; }
        if (f.kind == FactKind.F_IS_VARIANT && f.variant == variant) { return true; }
        if (f.kind == FactKind.F_NOT_VARIANT && f.variant == variant) { return false; }
    }
    return false;
}

// Is this fact contradicted by something already known? A contradiction means
// the branch is unreachable.
fn bool FlowEnv.contradicts(FlowEnv* e, Fact* probe)
{
    for (usz i = 0; i < e.count; i++)
    {
        Fact* f = &e.facts[i];
        if (f.binder != probe.binder) { continue; }

        if (f.kind == FactKind.F_IS_NULL && probe.kind == FactKind.F_NOT_NULL) { return true; }
        if (f.kind == FactKind.F_NOT_NULL && probe.kind == FactKind.F_IS_NULL) { return true; }
        if (f.kind == FactKind.F_IS_TRUE && probe.kind == FactKind.F_IS_FALSE) { return true; }
        if (f.kind == FactKind.F_IS_FALSE && probe.kind == FactKind.F_IS_TRUE) { return true; }

        if (f.kind == FactKind.F_IS_VARIANT && probe.kind == FactKind.F_IS_VARIANT)
        {
            // A value cannot be two different variants at once.
            if (f.variant != probe.variant) { return true; }
        }
        if (f.kind == FactKind.F_IS_VARIANT && probe.kind == FactKind.F_NOT_VARIANT)
        {
            if (f.variant == probe.variant) { return true; }
        }
        if (f.kind == FactKind.F_EQ_CONST && probe.kind == FactKind.F_EQ_CONST)
        {
            if (f.value != probe.value) { return true; }
        }
        if (f.kind == FactKind.F_EQ_CONST && probe.kind == FactKind.F_NE_CONST)
        {
            if (f.value == probe.value) { return true; }
        }
        // Range contradiction: x >= 5 and x <= 3.
        if (f.kind == FactKind.F_RANGE_LO && probe.kind == FactKind.F_RANGE_HI)
        {
            if (f.value > probe.value) { return true; }
        }
        if (f.kind == FactKind.F_RANGE_HI && probe.kind == FactKind.F_RANGE_LO)
        {
            if (probe.value > f.value) { return true; }
        }
    }
    return false;
}

// JOIN two branch environments at a merge point. Only facts present on BOTH
// paths survive — a fact proved on one branch says nothing after the merge.
// Taking the union here instead would be unsound, and it is a mistake that is
// easy to make because the code looks almost identical.
fn void FlowEnv.join(FlowEnv* e, usz base, usz then_end, usz else_end)
{
    e.joins = e.joins + 1;
    // Facts in [base, then_end) came from the then-branch; those in
    // [then_end, else_end) from the else-branch.
    usz w = base;
    for (usz i = base; i < then_end; i++)
    {
        Fact* a = &e.facts[i];
        bool also_in_else = false;
        for (usz k = then_end; k < else_end; k++)
        {
            Fact* b = &e.facts[k];
            if (a.binder != b.binder) { continue; }
            if (a.kind != b.kind) { continue; }
            if (a.kind == FactKind.F_IS_TYPE && a.type_id != b.type_id) { continue; }
            if (a.kind == FactKind.F_IS_VARIANT && a.variant != b.variant) { continue; }
            also_in_else = true;
            break;
        }
        if (!also_in_else) { continue; }
        e.facts[w] = *a;
        w = w + 1;
    }
    e.count = w;
}

// ── Guard analysis ──────────────────────────────────────────────────────────
// Extract the facts implied by a condition being true (or false).
struct GuardAnalyser
{
    FlowEnv*               env;
    Types*                 types;
    pfront_core::Interner* interner;
    pfront_core::DiagBag*  diags;
    char*                  file;

    usz guards_analysed;
    usz facts_derived;
    usz dead_branches;
    usz null_checks;
    usz type_tests;
    usz variant_tests;
    usz range_tests;
}

fn void GuardAnalyser.init(GuardAnalyser* g, FlowEnv* e, Types* t,
                           pfront_core::Interner* it,
                           pfront_core::DiagBag* d, char* file)
{
    g.env = e;
    g.types = t;
    g.interner = it;
    g.diags = d;
    g.file = file;
    g.guards_analysed = 0;
    g.facts_derived = 0;
    g.dead_branches = 0;
    g.null_checks = 0;
    g.type_tests = 0;
    g.variant_tests = 0;
    g.range_tests = 0;
}

fn Node* binder_of(Node* e)
{
    if (e == null) { return null; }
    if (e.kind == Nk.N_EXPR_IDENT) { return e.resolved; }
    return null;
}

fn bool const_int_of(Node* e, long* out)
{
    if (e == null) { return false; }
    if (e.kind == Nk.N_EXPR_INT) { *out = (long)e.p.ival; return true; }
    if (e.kind == Nk.N_EXPR_UNARY && (Tk)e.p.op == Tk.TOKEN_MINUS)
    {
        Node* inner = e.child(0);
        if (inner != null && inner.kind == Nk.N_EXPR_INT)
        {
            *out = -(long)inner.p.ival;
            return true;
        }
    }
    return false;
}

// Derive facts from `cond` assuming it evaluates to `polarity`.
fn void GuardAnalyser.derive(GuardAnalyser* g, Node* cond, bool polarity, int depth)
{
    if (cond == null || depth > NR_MAX_DEPTH) { return; }
    g.guards_analysed = g.guards_analysed + 1;

    switch (cond.kind)
    {
        case N_EXPR_UNARY:
        {
            Tk op = (Tk)cond.p.op;
            // Negation flips the polarity: facts from `!(x == null)` being true
            // are the facts from `x == null` being false.
            if (op == Tk.TOKEN_BANG || op == Tk.TOKEN_KW_NOT)
            {
                g.derive(cond.child(0), !polarity, depth + 1);
            }
            return;
        }

        case N_EXPR_BINARY:
        {
            Tk op = (Tk)cond.p.op;

            // Conjunction: when TRUE both sides hold, so both contribute
            // facts. When FALSE neither side is known, so nothing is derived —
            // deriving from a false `&&` is a classic unsoundness.
            if (op == Tk.TOKEN_AMPAMP || op == Tk.TOKEN_KW_AND)
            {
                if (polarity)
                {
                    g.derive(cond.child(0), true, depth + 1);
                    g.derive(cond.child(1), true, depth + 1);
                }
                return;
            }
            // Disjunction is the dual: facts only when FALSE.
            if (op == Tk.TOKEN_PIPEPIPE || op == Tk.TOKEN_KW_OR)
            {
                if (!polarity)
                {
                    g.derive(cond.child(0), false, depth + 1);
                    g.derive(cond.child(1), false, depth + 1);
                }
                return;
            }

            Node* lhs = cond.child(0);
            Node* rhs = cond.child(1);

            // Null comparison.
            if (op == Tk.TOKEN_EQEQ || op == Tk.TOKEN_NEQ)
            {
                bool eq = op == Tk.TOKEN_EQEQ;
                if (!polarity) { eq = !eq; }

                if (rhs != null && rhs.kind == Nk.N_EXPR_NULL)
                {
                    Node* b = binder_of(lhs);
                    if (b != null)
                    {
                        g.null_checks = g.null_checks + 1;
                        Fact f;
                        f.kind = eq ? FactKind.F_IS_NULL : FactKind.F_NOT_NULL;
                        f.binder = b;
                        f.name_id = lhs.name_id;
                        f.type_id = -1;
                        f.variant = 0;
                        f.value = 0;
                        g.record(f, cond);
                    }
                    return;
                }
                if (lhs != null && lhs.kind == Nk.N_EXPR_NULL)
                {
                    Node* b = binder_of(rhs);
                    if (b != null)
                    {
                        g.null_checks = g.null_checks + 1;
                        Fact f;
                        f.kind = eq ? FactKind.F_IS_NULL : FactKind.F_NOT_NULL;
                        f.binder = b;
                        f.name_id = rhs == null ? 0 : rhs.name_id;
                        f.type_id = -1;
                        f.variant = 0;
                        f.value = 0;
                        g.record(f, cond);
                    }
                    return;
                }

                // Constant equality: `x == 3` narrows x to that value.
                long k = 0;
                Node* b2 = binder_of(lhs);
                if (b2 != null && const_int_of(rhs, &k))
                {
                    Fact f;
                    f.kind = eq ? FactKind.F_EQ_CONST : FactKind.F_NE_CONST;
                    f.binder = b2;
                    f.name_id = lhs.name_id;
                    f.type_id = -1;
                    f.variant = 0;
                    f.value = k;
                    g.record(f, cond);
                }
                return;
            }

            // Ordering comparisons give range facts, which feed both
            // narrowing and (later) bounds-check elimination.
            if (op == Tk.TOKEN_LT || op == Tk.TOKEN_LTEQ
             || op == Tk.TOKEN_GT || op == Tk.TOKEN_GTEQ)
            {
                long k = 0;
                Node* b = binder_of(lhs);
                if (b == null || !const_int_of(rhs, &k)) { return; }
                g.range_tests = g.range_tests + 1;

                Fact f;
                f.binder = b;
                f.name_id = lhs.name_id;
                f.type_id = -1;
                f.variant = 0;

                bool lower = false;
                long bound = k;
                if (op == Tk.TOKEN_LT)   { lower = false; bound = k - 1; }
                if (op == Tk.TOKEN_LTEQ) { lower = false; bound = k; }
                if (op == Tk.TOKEN_GT)   { lower = true;  bound = k + 1; }
                if (op == Tk.TOKEN_GTEQ) { lower = true;  bound = k; }
                // A false comparison gives the complementary bound.
                if (!polarity)
                {
                    if (lower) { lower = false; bound = bound - 1; }
                    else       { lower = true;  bound = bound + 1; }
                }
                f.kind = lower ? FactKind.F_RANGE_LO : FactKind.F_RANGE_HI;
                f.value = bound;
                g.record(f, cond);
                return;
            }
            return;
        }

        // A bare boolean binding used as a condition is itself a fact.
        case N_EXPR_IDENT:
        {
            Node* b = binder_of(cond);
            if (b == null) { return; }
            Fact f;
            f.kind = polarity ? FactKind.F_IS_TRUE : FactKind.F_IS_FALSE;
            f.binder = b;
            f.name_id = cond.name_id;
            f.type_id = -1;
            f.variant = 0;
            f.value = 0;
            g.record(f, cond);
            return;
        }

        // `x is T` — an explicit type test, the primary narrowing construct.
        case N_EXPR_CAST:
        {
            Node* b = binder_of(cond.child(0));
            if (b == null || cond.type_ann == null) { return; }
            g.type_tests = g.type_tests + 1;
            Fact f;
            f.kind = polarity ? FactKind.F_IS_TYPE : FactKind.F_NOT_TYPE;
            f.binder = b;
            f.name_id = 0;
            f.type_id = -1;
            f.variant = 0;
            f.value = 0;
            g.record(f, cond);
            return;
        }

        default:
            return;
    }
}

fn void GuardAnalyser.record(GuardAnalyser* g, Fact f, Node* site)
{
    // A guard contradicting an established fact makes its branch unreachable.
    if (g.env.contradicts(&f))
    {
        g.dead_branches = g.dead_branches + 1;
        g.env.contradictions = g.env.contradictions + 1;
        g.diags.warn(pfront_core::Phase.PH_RESOLVE, 4120,
                     site == null ? 0 : site.line, site == null ? 0 : site.col,
                     "this condition contradicts what is already known here",
                     g.file);
        return;
    }
    if (g.env.add(f)) { g.facts_derived = g.facts_derived + 1; }
}

// ── Pattern narrowing ───────────────────────────────────────────────────────
// Matching `Some(v)` proves the scrutinee is that variant for the arm's extent.
// This is where narrowing and exhaustiveness meet.
fn void GuardAnalyser.narrow_pattern(GuardAnalyser* g, Node* scrutinee, Node* pat)
{
    if (scrutinee == null || pat == null) { return; }
    Node* b = binder_of(scrutinee);
    if (b == null) { return; }

    if (pat.kind == Nk.N_PAT_VARIANT && pat.name_id != 0)
    {
        g.variant_tests = g.variant_tests + 1;
        Fact f;
        f.kind = FactKind.F_IS_VARIANT;
        f.binder = b;
        f.name_id = scrutinee.name_id;
        f.type_id = -1;
        f.variant = pat.name_id;
        f.value = 0;
        g.record(f, pat);
        return;
    }
    if (pat.kind == Nk.N_PAT_LITERAL)
    {
        Node* lit = pat.child(0);
        long k = 0;
        if (lit != null && const_int_of(lit, &k))
        {
            Fact f;
            f.kind = FactKind.F_EQ_CONST;
            f.binder = b;
            f.name_id = scrutinee.name_id;
            f.type_id = -1;
            f.variant = 0;
            f.value = k;
            g.record(f, pat);
        }
    }
}

// After an arm on variant V, later arms know the scrutinee is NOT V. That is
// what makes a final `_` arm narrow to the remaining variants.
fn void GuardAnalyser.exclude_pattern(GuardAnalyser* g, Node* scrutinee, Node* pat)
{
    if (scrutinee == null || pat == null) { return; }
    Node* b = binder_of(scrutinee);
    if (b == null) { return; }
    if (pat.kind != Nk.N_PAT_VARIANT || pat.name_id == 0) { return; }
    Fact f;
    f.kind = FactKind.F_NOT_VARIANT;
    f.binder = b;
    f.name_id = scrutinee.name_id;
    f.type_id = -1;
    f.variant = pat.name_id;
    f.value = 0;
    g.env.add(f);
}

fn void GuardAnalyser.report(GuardAnalyser* g)
{
    printf("  narrowing        : %d guards, %d facts derived, %d dead branches\n",
           (int)g.guards_analysed, (int)g.facts_derived, (int)g.dead_branches);
    printf("  narrowing kinds  : %d null, %d type, %d variant, %d range\n",
           (int)g.null_checks, (int)g.type_tests,
           (int)g.variant_tests, (int)g.range_tests);
    printf("  flow env         : %d added, %d killed by assignment, %d joins\n",
           (int)g.env.facts_added, (int)g.env.facts_killed, (int)g.env.joins);
}

// ── Flow walker ─────────────────────────────────────────────────────────────
// Walks the tree maintaining the flow environment, so a consumer can ask
// "what is known about x here?" at any point.
struct FlowWalker
{
    FlowEnv        env;
    GuardAnalyser  guards;
    Types*         types;
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*          file;

    usz nodes;
    usz narrowed_reads;     // reads that benefited from a narrowing
    usz assignments;
    usz loops_widened;
}

fn void FlowWalker.init(FlowWalker* w, Types* t, pfront_core::DiagBag* d,
                        pfront_core::Interner* it, char* file)
{
    w.env.init();
    w.guards.init(&w.env, t, it, d, file);
    w.types = t;
    w.diags = d;
    w.interner = it;
    w.file = file;
    w.nodes = 0;
    w.narrowed_reads = 0;
    w.assignments = 0;
    w.loops_widened = 0;
}

fn void FlowWalker.walk(FlowWalker* w, Node* n, int depth)
{
    if (n == null || depth > NR_MAX_DEPTH) { return; }
    w.nodes = w.nodes + 1;

    switch (n.kind)
    {
        case N_EXPR_IF:
        {
            Node* cond = n.child(0);
            w.walk(cond, depth + 1);

            usz base = w.env.mark();
            // Then-branch: the condition holds.
            w.guards.derive(cond, true, 0);
            w.walk(n.child(1), depth + 1);
            usz then_end = w.env.count;

            if (n.child_count >= 3)
            {
                // Else-branch: the condition fails.
                w.guards.derive(cond, false, 0);
                w.walk(n.child(2), depth + 1);
                usz else_end = w.env.count;
                // Only facts common to both branches survive the merge.
                w.env.join(base, then_end, else_end);
            }
            else
            {
                w.env.reset(base);
            }
            return;
        }

        case N_EXPR_WHILE:
        {
            Node* cond = n.child(0);
            w.walk(cond, depth + 1);
            usz base = w.env.mark();
            // Inside the loop the guard holds, but any binding assigned in the
            // body must be WIDENED: a fact proved on the first iteration need
            // not hold on the second.
            w.guards.derive(cond, true, 0);
            w.kill_assigned(n.child(1), 0);
            w.loops_widened = w.loops_widened + 1;
            w.walk(n.child(1), depth + 1);
            w.env.reset(base);
            // After the loop the guard is false.
            w.guards.derive(cond, false, 0);
            return;
        }

        case N_EXPR_MATCH:
        {
            Node* scrut = n.child(0);
            w.walk(scrut, depth + 1);
            usz base = w.env.mark();
            for (usz i = 1; i < n.child_count; i++)
            {
                Node* arm = n.children[i];
                if (arm == null) { continue; }
                usz arm_mark = w.env.mark();
                w.guards.narrow_pattern(scrut, arm.child(0));
                for (usz k = 1; k < arm.child_count; k++)
                {
                    w.walk(arm.children[k], depth + 1);
                }
                w.env.reset(arm_mark);
                // Later arms know this pattern did not match.
                w.guards.exclude_pattern(scrut, arm.child(0));
            }
            w.env.reset(base);
            return;
        }

        case N_STMT_ASSIGN:
        case N_STMT_COMPOUND_ASSIGN:
        {
            w.assignments = w.assignments + 1;
            w.walk(n.child(1), depth + 1);
            Node* lhs = n.child(0);
            Node* b = binder_of(lhs);
            if (b != null) { w.env.kill(b); }
            return;
        }

        case N_EXPR_IDENT:
        {
            Node* b = binder_of(n);
            if (b != null && w.env.narrowed_type(b) >= 0)
            {
                w.narrowed_reads = w.narrowed_reads + 1;
            }
            return;
        }

        case N_BLOCK:
        {
            w.env.push();
            for (usz i = 0; i < n.child_count; i++) { w.walk(n.children[i], depth + 1); }
            w.env.pop();
            return;
        }

        default:
        {
            for (usz i = 0; i < n.child_count; i++) { w.walk(n.children[i], depth + 1); }
        }
    }
}

// Kill every binding assigned anywhere in a subtree. Used at loop entry, where
// a fact must survive an arbitrary number of iterations to be valid.
fn void FlowWalker.kill_assigned(FlowWalker* w, Node* n, int depth)
{
    if (n == null || depth > NR_MAX_DEPTH) { return; }
    if (n.kind == Nk.N_STMT_ASSIGN || n.kind == Nk.N_STMT_COMPOUND_ASSIGN)
    {
        Node* b = binder_of(n.child(0));
        if (b != null) { w.env.kill(b); }
    }
    for (usz i = 0; i < n.child_count; i++) { w.kill_assigned(n.children[i], depth + 1); }
}

fn void FlowWalker.run(FlowWalker* w, Node* root)
{
    if (root == null) { return; }
    for (usz i = 0; i < root.child_count; i++)
    {
        Node* d = root.children[i];
        if (d == null) { continue; }
        if (d.kind == Nk.N_DECL_FN)
        {
            w.env.push();
            for (usz k = 0; k < d.child_count; k++)
            {
                Node* c = d.children[k];
                if (c == null) { continue; }
                if (c.kind == Nk.N_CLAUSE)
                {
                    w.env.push();
                    for (usz j = 1; j < c.child_count; j++)
                    {
                        w.walk(c.children[j], 0);
                    }
                    w.env.pop();
                }
                else if (c.kind == Nk.N_BLOCK) { w.walk(c, 0); }
            }
            w.env.pop();
        }
        else if (d.kind == Nk.N_MODULE) { w.run(d); }
    }
}

fn void FlowWalker.report(FlowWalker* w)
{
    w.guards.report();
    printf("  flow analysis    : %d nodes, %d narrowed reads, %d assignments\n",
           (int)w.nodes, (int)w.narrowed_reads, (int)w.assignments);
}
