// ============================================================================
// pfront_flow.c3 — call graph, reachability, control flow (part 10)
// ----------------------------------------------------------------------------
// Analyses that the middle end needs handed to it, computed once here where
// the resolved AST is still available:
//
//   1. CALL GRAPH        — who calls whom, built from resolved identifiers.
//   2. RECURSION         — self-recursive and mutually recursive groups, via
//      the same Tarjan machinery used for the module graph. The SSI builder
//      needs this to decide where φ-nodes and back-edges are required.
//   3. REACHABILITY      — which functions are live from the entry points.
//      Dead functions are reported, not silently emitted.
//   4. DEFINITE RETURN   — does every path through a function produce a value?
//      A missing return on one branch is a real bug that a permissive type
//      checker will not catch.
//   5. UNINITIALISED USE — a `let` read before its initialiser runs.
//   6. LOOP STRUCTURE    — nesting depth and back-edge count, which drives
//      later LICM and the "future" lookahead in FG-e-SSI.
//   7. PURITY            — a conservative side-effect summary per function,
//      refined to a fixpoint over the call graph.
//
// Everything is bounded: no unbounded recursion, no allocation in hot loops.
// ============================================================================

module pfront_flow;

import pfront_lex;
import pfront_core;
import pfront_sema;

alias Tk   = pfront_lex::TokenType;
alias Node = pfront_core::PNode;
alias Nk   = pfront_core::NodeKind;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz MAX_FUNCS      = 4096;
const usz MAX_CALL_EDGES = 16384;
const usz MAX_LOCALS     = 512;

// ════════════════════════════════════════════════════════════════════════════
// 1-3. CALL GRAPH, RECURSION, REACHABILITY
// ════════════════════════════════════════════════════════════════════════════
struct FuncInfo
{
    Node*  decl;
    uint   name_id;
    bool   reachable;
    bool   self_recursive;
    bool   in_recursive_group;
    bool   is_entry;
    bool   is_extern;
    ulong  effects;         // conservative summary, refined to a fixpoint
    int    call_count;      // outgoing calls
    int    caller_count;    // incoming calls
    int    component;       // SCC id
}

struct CallGraph
{
    FuncInfo[MAX_FUNCS] funcs;
    usz                 func_count;

    // Edge list, grouped by caller for CSR conversion.
    int[MAX_CALL_EDGES] edge_from;
    int[MAX_CALL_EDGES] edge_to;
    usz                 edge_count;

    pfront_sema::SccGraph* scc;

    usz recursive_funcs;
    usz mutual_groups;
    usz unreachable_funcs;
    usz max_group_size;
    bool has_real_entry;    // a `main`/extern/pub root was found
    bool library_mode;      // no entry: treat every function as a root
}

fn void CallGraph.init(CallGraph* g)
{
    g.func_count = 0;
    g.edge_count = 0;
    g.scc = null;
    g.recursive_funcs = 0;
    g.mutual_groups = 0;
    g.unreachable_funcs = 0;
    g.max_group_size = 0;
    g.has_real_entry = false;
    g.library_mode = false;
}

fn int CallGraph.index_of(CallGraph* g, Node* decl)
{
    if (decl == null) { return -1; }
    for (usz i = 0; i < g.func_count; i++)
    {
        if (g.funcs[i].decl == decl) { return (int)i; }
    }
    return -1;
}

fn int CallGraph.add_func(CallGraph* g, Node* decl)
{
    int existing = g.index_of(decl);
    if (existing >= 0) { return existing; }
    if (g.func_count >= MAX_FUNCS) { return -1; }
    int id = (int)g.func_count;
    FuncInfo* f = &g.funcs[id];
    f.decl = decl;
    f.name_id = decl.name_id;
    f.reachable = false;
    f.self_recursive = false;
    f.in_recursive_group = false;
    f.is_entry = false;
    f.is_extern = decl.kind == Nk.N_DECL_EXTERN_FN
               || (decl.flags & pfront_core::NF_EXTERN) != 0;
    f.effects = decl.effects;
    f.call_count = 0;
    f.caller_count = 0;
    f.component = -1;
    g.func_count = g.func_count + 1;
    return id;
}

fn bool CallGraph.add_call(CallGraph* g, int from, int to)
{
    if (from < 0 || to < 0) { return false; }
    if (g.edge_count >= MAX_CALL_EDGES) { return false; }
    // Deduplicate: repeated calls to the same target add no information and
    // would inflate the SCC edge arrays.
    for (usz i = 0; i < g.edge_count; i++)
    {
        if (g.edge_from[i] == from && g.edge_to[i] == to) { return true; }
    }
    g.edge_from[g.edge_count] = from;
    g.edge_to[g.edge_count] = to;
    g.edge_count = g.edge_count + 1;
    g.funcs[from].call_count = g.funcs[from].call_count + 1;
    g.funcs[to].caller_count = g.funcs[to].caller_count + 1;
    if (from == to) { g.funcs[from].self_recursive = true; }
    return true;
}

// Collect every function declaration in the tree.
fn void CallGraph.collect_funcs(CallGraph* g, Node* n, int depth)
{
    if (n == null || depth > 200) { return; }
    if (n.kind == Nk.N_DECL_FN || n.kind == Nk.N_DECL_EXTERN_FN)
    {
        g.add_func(n);
    }
    for (usz i = 0; i < n.child_count; i++) { g.collect_funcs(n.children[i], depth + 1); }
}

// Walk a function body recording calls to other known functions.
fn void CallGraph.scan_calls(CallGraph* g, Node* n, int owner, int depth)
{
    if (n == null || depth > 200) { return; }

    // Entering a nested function switches the owner.
    if ((n.kind == Nk.N_DECL_FN || n.kind == Nk.N_DECL_EXTERN_FN) && depth > 0)
    {
        int inner = g.index_of(n);
        if (inner >= 0)
        {
            for (usz i = 0; i < n.child_count; i++)
            {
                g.scan_calls(n.children[i], inner, depth + 1);
            }
            return;
        }
    }

    // Any resolved reference to a function is a potential call. Taking a
    // function's address counts too: it can be invoked indirectly, so treating
    // it as an edge keeps reachability sound (conservative, never unsound).
    if (n.resolved != null)
    {
        Node* t = n.resolved;
        if (t.kind == Nk.N_DECL_FN || t.kind == Nk.N_DECL_EXTERN_FN)
        {
            int callee = g.index_of(t);
            if (callee >= 0 && owner >= 0) { g.add_call(owner, callee); }
        }
    }

    for (usz i = 0; i < n.child_count; i++) { g.scan_calls(n.children[i], owner, depth + 1); }
}

fn void CallGraph.build(CallGraph* g, Node* root, pfront_core::Interner* it)
{
    g.collect_funcs(root, 0);
    for (usz i = 0; i < g.func_count; i++)
    {
        Node* d = g.funcs[i].decl;
        for (usz k = 0; k < d.child_count; k++)
        {
            g.scan_calls(d.children[k], (int)i, 1);
        }
    }
    g.mark_entries(it);
}

// Entry-point selection. `main` is the obvious root, but most files in a
// library have no `main` at all — treating every function there as dead would
// make the analysis useless noise (it reported "625 unreachable of 625" on
// stdlib/os/linux.pie). Rules, in order:
//
//   * `main`            — always an entry.
//   * extern functions  — callable from outside the compilation unit.
//   * `pub` functions   — part of the module's public surface.
//   * address-taken     — reachable indirectly through a function pointer.
//
// If NO entry is found by those rules the unit is a library, and every
// top-level function becomes a root. Dead-code reporting is then meaningless,
// so it is disabled for that unit rather than emitting false warnings.
fn void CallGraph.mark_entries(CallGraph* g, pfront_core::Interner* it)
{
    usz entries = 0;
    for (usz i = 0; i < g.func_count; i++)
    {
        FuncInfo* f = &g.funcs[i];
        char* nm = it.text(f.name_id);
        usz nl = it.text_len(f.name_id);
        if (nm != null && nl == 4
            && nm[0] == 'm' && nm[1] == 'a' && nm[2] == 'i' && nm[3] == 'n')
        {
            f.is_entry = true;
        }
        if (f.is_extern) { f.is_entry = true; }
        if ((f.decl.flags & pfront_core::NF_PUB) != 0) { f.is_entry = true; }
        if ((f.decl.flags & pfront_core::NF_ADDR_TAKEN) != 0) { f.is_entry = true; }
        if (f.is_entry) { entries = entries + 1; }
    }
    g.has_real_entry = entries > 0;
    if (entries > 0) { return; }
    // Library unit: every function is a root, and dead-code analysis is
    // suppressed because it cannot distinguish dead from externally-called.
    g.library_mode = true;
    for (usz i = 0; i < g.func_count; i++) { g.funcs[i].is_entry = true; }
}

// Iterative worklist reachability from the entry set.
fn void CallGraph.compute_reachability(CallGraph* g)
{
    int[MAX_FUNCS] work;
    usz top = 0;
    for (usz i = 0; i < g.func_count; i++)
    {
        if (g.funcs[i].is_entry)
        {
            g.funcs[i].reachable = true;
            if (top < MAX_FUNCS) { work[top] = (int)i; top = top + 1; }
        }
    }
    while (top > 0)
    {
        top = top - 1;
        int v = work[top];
        for (usz e = 0; e < g.edge_count; e++)
        {
            if (g.edge_from[e] != v) { continue; }
            int w = g.edge_to[e];
            if (g.funcs[w].reachable) { continue; }
            g.funcs[w].reachable = true;
            if (top < MAX_FUNCS) { work[top] = w; top = top + 1; }
        }
    }
    g.unreachable_funcs = 0;
    for (usz i = 0; i < g.func_count; i++)
    {
        if (!g.funcs[i].reachable) { g.unreachable_funcs = g.unreachable_funcs + 1; }
    }
}

// Reuse the Tarjan implementation to find mutually recursive groups.
fn void CallGraph.compute_recursion(CallGraph* g, pfront_sema::SccGraph* scc)
{
    g.scc = scc;
    scc.init(g.func_count);
    for (usz v = 0; v < g.func_count; v++)
    {
        scc.begin_node((int)v);
        for (usz e = 0; e < g.edge_count; e++)
        {
            if (g.edge_from[e] == (int)v) { scc.add_edge(g.edge_to[e]); }
        }
    }
    scc.finish();
    scc.run();

    g.recursive_funcs = 0;
    g.mutual_groups = 0;
    g.max_group_size = 0;
    for (usz i = 0; i < g.func_count; i++)
    {
        g.funcs[i].component = scc.component_of[i];
        bool cyc = scc.is_cyclic_member((int)i);
        g.funcs[i].in_recursive_group = cyc;
        if (cyc) { g.recursive_funcs = g.recursive_funcs + 1; }
    }
    for (usz c = 0; c < scc.component_count; c++)
    {
        int csize = scc.component_size[c];
        if (csize > 1)
        {
            g.mutual_groups = g.mutual_groups + 1;
            if ((usz)csize > g.max_group_size) { g.max_group_size = (usz)csize; }
        }
    }
}

// ── 7. PURITY / EFFECT FIXPOINT over the call graph ─────────────────────────
// A function's effects are its own plus every callee's. Iterating to a
// fixpoint handles recursion correctly; the lattice is finite so it converges.
fn int CallGraph.propagate_effects(CallGraph* g)
{
    int rounds = 0;
    bool changed = true;
    while (changed && rounds < 16)
    {
        changed = false;
        rounds = rounds + 1;
        for (usz e = 0; e < g.edge_count; e++)
        {
            int from = g.edge_from[e];
            int to = g.edge_to[e];
            ulong before = g.funcs[from].effects;
            ulong after = before | g.funcs[to].effects;
            if (after != before)
            {
                g.funcs[from].effects = after;
                changed = true;
            }
        }
    }
    // Write the summary back onto the declarations so later passes see it.
    for (usz i = 0; i < g.func_count; i++)
    {
        g.funcs[i].decl.effects = g.funcs[i].effects;
    }
    return rounds;
}

fn void CallGraph.report(CallGraph* g, pfront_core::Interner* it)
{
    printf("  call graph       : %d functions, %d edges\n",
           (int)g.func_count, (int)g.edge_count);
    printf("  recursion        : %d functions in cycles, %d mutual groups (largest %d)\n",
           (int)g.recursive_funcs, (int)g.mutual_groups, (int)g.max_group_size);
    if (g.library_mode)
    {
        printf("  reachability     : library unit (no entry point) - all %d roots\n",
               (int)g.func_count);
    }
    else
    {
        printf("  reachability     : %d unreachable of %d\n",
               (int)g.unreachable_funcs, (int)g.func_count);
    }
}

// Report dead functions as warnings. Skipped for extern/pub, which may be
// called from outside the compilation unit.
fn void CallGraph.report_dead(CallGraph* g, pfront_core::DiagBag* d,
                              pfront_core::Interner* it, char* file)
{
    // Suppressed for library units: "unreachable" there only means "no local
    // caller", which is the normal state of an exported function.
    if (g.library_mode || !g.has_real_entry) { return; }
    for (usz i = 0; i < g.func_count; i++)
    {
        FuncInfo* f = &g.funcs[i];
        if (f.reachable || f.is_entry || f.is_extern) { continue; }
        d.warn(pfront_core::Phase.PH_RESOLVE, 4020, f.decl.line, f.decl.col,
               "function is never called from any entry point", file);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// 4-6. CONTROL FLOW WITHIN A FUNCTION
// ════════════════════════════════════════════════════════════════════════════
// Termination summary for a statement or expression.
enum Flow : int
{
    FLOW_FALLTHROUGH,   // control continues after this construct
    FLOW_RETURNS,       // every path returns
    FLOW_DIVERGES,      // never returns (trap / unreachable / infinite loop)
    FLOW_BREAKS         // exits an enclosing loop
}

struct FlowAnalysis
{
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char* file;

    usz   funcs_checked;
    usz   missing_returns;
    usz   unreachable_stmts;
    usz   infinite_loops;
    int   max_loop_depth;
    int   cur_loop_depth;
    usz   back_edges;
    usz   uninit_reads;
}

fn void FlowAnalysis.init(FlowAnalysis* fa, pfront_core::DiagBag* d,
                          pfront_core::Interner* it, char* file)
{
    fa.diags = d;
    fa.interner = it;
    fa.file = file;
    fa.funcs_checked = 0;
    fa.missing_returns = 0;
    fa.unreachable_stmts = 0;
    fa.infinite_loops = 0;
    fa.max_loop_depth = 0;
    fa.cur_loop_depth = 0;
    fa.back_edges = 0;
    fa.uninit_reads = 0;
}

// Does this construct always transfer control away?
fn Flow FlowAnalysis.flow_of(FlowAnalysis* fa, Node* n, int depth)
{
    if (n == null || depth > 200) { return Flow.FLOW_FALLTHROUGH; }

    switch (n.kind)
    {
        case N_STMT_RETURN:
            return Flow.FLOW_RETURNS;
        case N_STMT_BREAK:
        case N_STMT_CONTINUE:
            return Flow.FLOW_BREAKS;
        case N_EXPR_UNREACHABLE:
        case N_EXPR_TRAP:
            return Flow.FLOW_DIVERGES;

        case N_BLOCK:
        {
            Flow acc = Flow.FLOW_FALLTHROUGH;
            for (usz i = 0; i < n.child_count; i++)
            {
                Node* s = n.children[i];
                if (s == null) { continue; }
                if (acc != Flow.FLOW_FALLTHROUGH)
                {
                    // Everything after a diverging statement is dead.
                    fa.unreachable_stmts = fa.unreachable_stmts + 1;
                    fa.diags.warn(pfront_core::Phase.PH_RESOLVE, 4021, s.line, s.col,
                                  "unreachable statement", fa.file);
                    break;
                }
                acc = fa.flow_of(s, depth + 1);
            }
            return acc;
        }

        case N_EXPR_IF:
        {
            // An `if` only guarantees transfer when BOTH arms do.
            if (n.child_count < 3) { return Flow.FLOW_FALLTHROUGH; }
            Flow a = fa.flow_of(n.child(1), depth + 1);
            Flow b = fa.flow_of(n.child(2), depth + 1);
            if (a == Flow.FLOW_FALLTHROUGH || b == Flow.FLOW_FALLTHROUGH)
            {
                return Flow.FLOW_FALLTHROUGH;
            }
            if (a == Flow.FLOW_RETURNS && b == Flow.FLOW_RETURNS) { return Flow.FLOW_RETURNS; }
            if (a == Flow.FLOW_DIVERGES && b == Flow.FLOW_DIVERGES) { return Flow.FLOW_DIVERGES; }
            return Flow.FLOW_RETURNS;
        }

        case N_EXPR_MATCH:
        {
            // A match transfers only if every arm does AND it is exhaustive.
            bool exhaustive = (n.flags & pfront_core::NF_EXHAUSTIVE) != 0;
            if (!exhaustive) { return Flow.FLOW_FALLTHROUGH; }
            bool all_transfer = n.child_count > 1;
            for (usz i = 1; i < n.child_count; i++)
            {
                Node* arm = n.children[i];
                if (arm == null) { continue; }
                Flow af = Flow.FLOW_FALLTHROUGH;
                for (usz j = 1; j < arm.child_count; j++)
                {
                    Node* b = arm.children[j];
                    if (b == null || b.kind == Nk.N_GUARD) { continue; }
                    af = fa.flow_of(b, depth + 1);
                }
                if (af == Flow.FLOW_FALLTHROUGH) { all_transfer = false; }
            }
            return all_transfer ? Flow.FLOW_RETURNS : Flow.FLOW_FALLTHROUGH;
        }

        case N_EXPR_WHILE:
        {
            fa.cur_loop_depth = fa.cur_loop_depth + 1;
            if (fa.cur_loop_depth > fa.max_loop_depth) { fa.max_loop_depth = fa.cur_loop_depth; }
            fa.back_edges = fa.back_edges + 1;
            Flow body = fa.flow_of(n.child(1), depth + 1);
            fa.cur_loop_depth = fa.cur_loop_depth - 1;

            // `while true` with no break never terminates normally. That is a
            // legitimate pattern (event loops), so it is not a diagnostic, but
            // it DOES mean the code after it is unreachable.
            Node* cond = n.child(0);
            bool always = cond != null && cond.kind == Nk.N_EXPR_BOOL && cond.p.ival != 0;
            if (always && !fa.contains_break(n.child(1), 0))
            {
                fa.infinite_loops = fa.infinite_loops + 1;
                return Flow.FLOW_DIVERGES;
            }
            return Flow.FLOW_FALLTHROUGH;
        }

        case N_EXPR_FOR:
        {
            fa.cur_loop_depth = fa.cur_loop_depth + 1;
            if (fa.cur_loop_depth > fa.max_loop_depth) { fa.max_loop_depth = fa.cur_loop_depth; }
            fa.back_edges = fa.back_edges + 1;
            fa.flow_of(n.child(2), depth + 1);
            fa.cur_loop_depth = fa.cur_loop_depth - 1;
            return Flow.FLOW_FALLTHROUGH;
        }

        case N_EXPR_UNSAFE:
        case N_EXPR_UNCHECKED:
        case N_EXPR_COMPTIME:
        {
            Flow acc = Flow.FLOW_FALLTHROUGH;
            for (usz i = 0; i < n.child_count; i++) { acc = fa.flow_of(n.children[i], depth + 1); }
            return acc;
        }

        default:
        {
            // A call to a diverging function propagates divergence.
            if (n.kind == Nk.N_EXPR_CALL && n.child_count > 0)
            {
                Node* callee = n.children[0];
                if (callee != null && callee.resolved != null
                    && (callee.resolved.effects & pfront_core::EFF_DIVERGE) != 0)
                {
                    return Flow.FLOW_DIVERGES;
                }
            }
            return Flow.FLOW_FALLTHROUGH;
        }
    }
}

// Does a loop body contain a `break` that targets this loop?
fn bool FlowAnalysis.contains_break(FlowAnalysis* fa, Node* n, int depth)
{
    if (n == null || depth > 100) { return false; }
    if (n.kind == Nk.N_STMT_BREAK) { return true; }
    if (n.kind == Nk.N_STMT_RETURN) { return true; }
    // A nested loop captures its own breaks, so do not descend into one.
    if (depth > 0 && (n.kind == Nk.N_EXPR_WHILE || n.kind == Nk.N_EXPR_FOR)) { return false; }
    for (usz i = 0; i < n.child_count; i++)
    {
        if (fa.contains_break(n.children[i], depth + 1)) { return true; }
    }
    return false;
}

// A function whose signature promises a value must produce one on every path.
// Pride's clause bodies are expressions, so the check is: does the body fall
// through WITHOUT yielding a value?
fn void FlowAnalysis.check_fn(FlowAnalysis* fa, Node* f)
{
    if (f == null) { return; }
    if (f.kind == Nk.N_DECL_EXTERN_FN) { return; }
    fa.funcs_checked = fa.funcs_checked + 1;

    for (usz i = 0; i < f.child_count; i++)
    {
        Node* c = f.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.N_CLAUSE)
        {
            for (usz j = 1; j < c.child_count; j++)
            {
                Node* body = c.children[j];
                if (body == null || body.kind == Nk.N_GUARD) { continue; }
                fa.check_body(f, body);
            }
        }
        else if (c.kind == Nk.N_BLOCK) { fa.check_body(f, c); }
    }
}

// Does this function's signature promise a value? `fn f : T -> ()` does not,
// so a trailing assignment is perfectly correct there. Checking this was the
// difference between a useful warning and 14 false positives on the stdlib.
fn bool returns_unit(Node* f)
{
    if (f == null) { return false; }
    Node* sig = f.type_ann;
    if (sig == null) { return true; }   // unannotated: assume no promise
    if (sig.kind != Nk.N_TY_FN) { return false; }
    // The return type lives in the N_TY_CONSTRAINT child.
    for (usz i = 0; i < sig.child_count; i++)
    {
        Node* c = sig.children[i];
        if (c == null || c.kind != Nk.N_TY_CONSTRAINT) { continue; }
        Node* ret = c.child(0);
        if (ret == null) { return true; }
        if (ret.kind == Nk.N_TY_UNIT) { return true; }
        // A named type spelled `unit`/`void` counts as no value.
        if (ret.kind == Nk.N_TY_NAME && ret.p.sptr != null)
        {
            usz n = ret.p.slen;
            char* t = ret.p.sptr;
            if (n == 4 && t[0] == 'u' && t[1] == 'n' && t[2] == 'i' && t[3] == 't') { return true; }
            if (n == 4 && t[0] == 'v' && t[1] == 'o' && t[2] == 'i' && t[3] == 'd') { return true; }
        }
        return false;
    }
    // No constraint child means no declared return type.
    return true;
}

fn void FlowAnalysis.check_body(FlowAnalysis* fa, Node* f, Node* body)
{
    Flow fl = fa.flow_of(body, 0);
    if (fl != Flow.FLOW_FALLTHROUGH) { return; }
    // A function returning () may end with any statement.
    if (returns_unit(f)) { return; }
    if (body.kind != Nk.N_BLOCK) { return; }
    if (body.child_count == 0)
    {
        fa.missing_returns = fa.missing_returns + 1;
        fa.diags.warn(pfront_core::Phase.PH_RESOLVE, 4022, body.line, body.col,
                      "function body is empty but a value is expected", fa.file);
        return;
    }
    Node* last = body.children[body.child_count - 1];
    if (last == null) { return; }
    if (pfront_core::is_expr(last.kind)) { return; }
    if (last.kind == Nk.N_STMT_RETURN) { return; }
    if (last.kind == Nk.N_DECL_LET || last.kind == Nk.N_STMT_ASSIGN
     || last.kind == Nk.N_STMT_COMPOUND_ASSIGN)
    {
        fa.missing_returns = fa.missing_returns + 1;
        fa.diags.warn(pfront_core::Phase.PH_RESOLVE, 4023, last.line, last.col,
                      "function may not return a value on every path", fa.file);
    }
}

// ── 5. USE-BEFORE-INITIALISATION ────────────────────────────────────────────
// `let x = x + 1` and reads of a binding declared later in the same block.
struct InitTracker
{
    Node*[MAX_LOCALS] declared;
    usz               count;
}

fn void InitTracker.reset(InitTracker* t) { t.count = 0; }

fn bool InitTracker.is_declared(InitTracker* t, Node* d)
{
    for (usz i = 0; i < t.count; i++) { if (t.declared[i] == d) { return true; } }
    return false;
}

fn void InitTracker.declare(InitTracker* t, Node* d)
{
    if (t.count >= MAX_LOCALS) { return; }
    t.declared[t.count] = d;
    t.count = t.count + 1;
}

fn void FlowAnalysis.check_init(FlowAnalysis* fa, Node* block, InitTracker* tr, int depth)
{
    if (block == null || depth > 100) { return; }
    if (block.kind != Nk.N_BLOCK)
    {
        for (usz i = 0; i < block.child_count; i++)
        {
            fa.check_init(block.children[i], tr, depth + 1);
        }
        return;
    }
    for (usz i = 0; i < block.child_count; i++)
    {
        Node* s = block.children[i];
        if (s == null) { continue; }
        if (s.kind == Nk.N_DECL_LET)
        {
            // Scan the initialiser BEFORE declaring the binder, so a
            // self-reference is caught.
            for (usz k = 1; k < s.child_count; k++)
            {
                fa.scan_reads(s.children[k], tr, s.child(0), depth + 1);
            }
            Node* pat = s.child(0);
            if (pat != null) { tr.declare(pat); }
            continue;
        }
        fa.scan_reads(s, tr, null, depth + 1);
        fa.check_init(s, tr, depth + 1);
    }
}

fn void FlowAnalysis.scan_reads(FlowAnalysis* fa, Node* n, InitTracker* tr,
                                Node* forbidden, int depth)
{
    if (n == null || depth > 100) { return; }
    if (n.kind == Nk.N_EXPR_IDENT && n.resolved != null)
    {
        if (forbidden != null && n.resolved == forbidden)
        {
            fa.uninit_reads = fa.uninit_reads + 1;
            fa.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3040, n.line, n.col,
                                "binding is used in its own initialiser",
                                "the name is not in scope until the `let` completes",
                                fa.file);
        }
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        fa.scan_reads(n.children[i], tr, forbidden, depth + 1);
    }
}

fn void FlowAnalysis.run(FlowAnalysis* fa, Node* root)
{
    if (root == null) { return; }
    for (usz i = 0; i < root.child_count; i++)
    {
        Node* d = root.children[i];
        if (d == null) { continue; }
        if (d.kind == Nk.N_DECL_FN)
        {
            fa.check_fn(d);
            InitTracker tr;
            tr.reset();
            for (usz k = 0; k < d.child_count; k++)
            {
                Node* c = d.children[k];
                if (c == null) { continue; }
                if (c.kind == Nk.N_CLAUSE)
                {
                    for (usz j = 1; j < c.child_count; j++)
                    {
                        fa.check_init(c.children[j], &tr, 0);
                    }
                }
                else if (c.kind == Nk.N_BLOCK) { fa.check_init(c, &tr, 0); }
            }
        }
        else if (d.kind == Nk.N_MODULE) { fa.run(d); }
    }
}

fn void FlowAnalysis.report(FlowAnalysis* fa)
{
    printf("  control flow     : %d functions, %d possibly missing a value\n",
           (int)fa.funcs_checked, (int)fa.missing_returns);
    printf("  loops            : max nesting %d, %d back edges, %d infinite\n",
           fa.max_loop_depth, (int)fa.back_edges, (int)fa.infinite_loops);
    printf("  dead statements  : %d, self-referential inits: %d\n",
           (int)fa.unreachable_stmts, (int)fa.uninit_reads);
}
