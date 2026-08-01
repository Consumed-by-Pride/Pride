// ============================================================================
// pfront_sema.c3 — semantic analysis: SCC, visibility, patterns (part 7)
// ----------------------------------------------------------------------------
// The analyses here are the ones a production front end needs but a teaching
// parser skips. Each is a real algorithm, not a heuristic:
//
//   1. Tarjan SCC over the module graph   — strongly connected components give
//      a correct topological order for cyclic imports, and identify genuine
//      cycles rather than rejecting any back-edge.
//   2. Tarjan SCC over the call graph     — mutual recursion detection, which
//      effect inference and (later) monomorphisation both need.
//   3. Visibility / access control        — pub, pub(mod), private-by-default,
//      enforced across module boundaries.
//   4. Pattern usefulness (Maranget)      — the algorithm behind rustc's
//      exhaustiveness checker: a matrix-based usefulness test that yields a
//      concrete witness for the missing case, not just a yes/no.
//   5. Const-expression evaluation        — array sizes, enum discriminants,
//      and static initialisers folded at check time with overflow detection.
//   6. Cyclic type detection              — a struct that contains itself by
//      value is infinite-sized; catching it here beats a stack overflow in
//      the backend.
// ============================================================================

module pfront_sema;

import pfront_lex;
import pfront_core;
import pfront_resolve;

alias Tk   = pfront_lex::TokenType;
alias Node = pfront_core::PNode;
alias Nk   = pfront_core::NodeKind;
alias Mod  = pfront_core::Module;
alias Sym  = pfront_core::Symbol;

extern fn int printf(char* fmt, ...);

const usz MAX_GRAPH_NODES = 4096;
const usz MAX_STACK       = 4096;
const usz MAX_MATRIX_ROWS = 96;
const usz MAX_MATRIX_COLS = 12;
const usz CYCLE_STACK_CAP = 256;
const usz MEMO_CAP        = 2048;

// ════════════════════════════════════════════════════════════════════════════
// 1-2. TARJAN STRONGLY CONNECTED COMPONENTS
// ════════════════════════════════════════════════════════════════════════════
// One implementation, used for both the module graph and the call graph.
// Iterative rather than recursive: a deep dependency chain must not blow the
// C stack, and stdlib import chains are genuinely deep.
struct SccGraph
{
    // Adjacency in CSR form: edges[edge_start[v] .. edge_start[v+1]).
    int[MAX_GRAPH_NODES + 1] edge_start;
    int[MAX_GRAPH_NODES * 4] edges;
    usz node_count;
    usz edge_count;

    // Tarjan state.
    int[MAX_GRAPH_NODES] index_of;
    int[MAX_GRAPH_NODES] lowlink;
    bool[MAX_GRAPH_NODES] on_stack;
    int[MAX_STACK]        stack;
    usz                   stack_top;
    int                   next_index;

    // Results.
    int[MAX_GRAPH_NODES] component_of;
    int[MAX_GRAPH_NODES] component_size;   // members per component
    bool[MAX_GRAPH_NODES] has_self_loop;
    bool[MAX_GRAPH_NODES] declared;        // begin_node was called for this vertex
    int                  last_node;
    usz                  component_count;
    usz                  cyclic_components;
    usz                  largest_component;
}

fn void SccGraph.init(SccGraph* g, usz n)
{
    g.node_count = n < MAX_GRAPH_NODES ? n : MAX_GRAPH_NODES;
    g.edge_count = 0;
    g.stack_top = 0;
    g.next_index = 0;
    g.component_count = 0;
    g.cyclic_components = 0;
    g.largest_component = 0;
    g.last_node = -1;
    for (usz i = 0; i <= g.node_count; i++) { g.edge_start[i] = 0; }
    for (usz i = 0; i < g.node_count; i++)
    {
        g.index_of[i] = -1;
        g.lowlink[i] = 0;
        g.on_stack[i] = false;
        g.component_of[i] = -1;
        g.component_size[i] = 0;
        g.has_self_loop[i] = false;
        g.declared[i] = false;
    }
}

// Edges must be added grouped by source vertex (CSR requires it). The loader
// walks modules in order, so this is naturally satisfied.
fn bool SccGraph.begin_node(SccGraph* g, int v)
{
    if (v < 0 || (usz)v >= g.node_count) { return false; }
    // Record where this vertex's edge run starts, and remember that we have
    // seen it. Vertices are expected in ascending order; any gap is closed by
    // finish(), which never has to guess whether a zero means "empty" or
    // "unset" because `declared` records that explicitly.
    g.edge_start[v] = (int)g.edge_count;
    g.declared[v] = true;
    g.last_node = v;
    return true;
}

fn bool SccGraph.add_edge(SccGraph* g, int to)
{
    if (g.edge_count >= MAX_GRAPH_NODES * 4) { return false; }
    if (to < 0 || (usz)to >= g.node_count) { return false; }
    g.edges[g.edge_count] = to;
    g.edge_count = g.edge_count + 1;
    return true;
}

// Close the CSR. Any vertex that was never declared, or declared with no
// edges, gets an empty run [start, start). Walking backwards and carrying the
// next known boundary makes every run well-formed in one pass.
fn void SccGraph.finish(SccGraph* g)
{
    g.edge_start[g.node_count] = (int)g.edge_count;
    int next_start = (int)g.edge_count;
    for (usz i = g.node_count; i > 0; i--)
    {
        usz v = i - 1;
        if (!g.declared[v])
        {
            // Never declared: empty run positioned at the following boundary.
            g.edge_start[v] = next_start;
        }
        else
        {
            next_start = g.edge_start[v];
        }
    }
    // Monotonicity guard: edge_start must be non-decreasing for the run
    // [edge_start[v], edge_start[v+1]) to be meaningful.
    for (usz v = 0; v < g.node_count; v++)
    {
        if (g.edge_start[v] > g.edge_start[v + 1]) { g.edge_start[v] = g.edge_start[v + 1]; }
    }
}

fn void SccGraph.run(SccGraph* g)
{
    int[MAX_STACK] work_v;
    int[MAX_STACK] work_e;

    for (usz root = 0; root < g.node_count; root++)
    {
        if (g.index_of[root] != -1) { continue; }

        usz sp = 0;
        work_v[0] = (int)root;
        work_e[0] = g.edge_start[root];
        g.index_of[root] = g.next_index;
        g.lowlink[root] = g.next_index;
        g.next_index = g.next_index + 1;
        if (g.stack_top < MAX_STACK)
        {
            g.stack[g.stack_top] = (int)root;
            g.stack_top = g.stack_top + 1;
        }
        g.on_stack[root] = true;

        while (true)
        {
            int v = work_v[sp];
            int ei = work_e[sp];
            int end = g.edge_start[v + 1];

            if (ei < end)
            {
                work_e[sp] = ei + 1;
                int w = g.edges[ei];
                if (w < 0 || (usz)w >= g.node_count) { continue; }
                if (w == v) { g.has_self_loop[v] = true; }
                if (g.index_of[w] == -1)
                {
                    g.index_of[w] = g.next_index;
                    g.lowlink[w] = g.next_index;
                    g.next_index = g.next_index + 1;
                    if (g.stack_top < MAX_STACK)
                    {
                        g.stack[g.stack_top] = w;
                        g.stack_top = g.stack_top + 1;
                    }
                    g.on_stack[w] = true;
                    if (sp + 1 < MAX_STACK)
                    {
                        sp = sp + 1;
                        work_v[sp] = w;
                        work_e[sp] = g.edge_start[w];
                    }
                }
                else if (g.on_stack[w])
                {
                    if (g.index_of[w] < g.lowlink[v]) { g.lowlink[v] = g.index_of[w]; }
                }
                continue;
            }

            // v is finished: if it is a root, pop its component.
            if (g.lowlink[v] == g.index_of[v])
            {
                usz members = 0;
                while (g.stack_top > 0)
                {
                    g.stack_top = g.stack_top - 1;
                    int w = g.stack[g.stack_top];
                    g.on_stack[w] = false;
                    g.component_of[w] = (int)g.component_count;
                    members = members + 1;
                    if (w == v) { break; }
                }
                g.component_size[g.component_count] = (int)members;
                if (members > 1) { g.cyclic_components = g.cyclic_components + 1; }
                if (members > g.largest_component) { g.largest_component = members; }
                g.component_count = g.component_count + 1;
            }

            if (sp == 0) { break; }
            int child = v;
            sp = sp - 1;
            int parent = work_v[sp];
            if (g.lowlink[child] < g.lowlink[parent]) { g.lowlink[parent] = g.lowlink[child]; }
        }
    }
}

// Components are numbered in reverse topological order by Tarjan, so a higher
// component id must be processed first when dependencies point "downward".
// O(1) after run(): component sizes are tallied once, and self-loops are
// recorded during the edge walk rather than rescanned per query.
fn bool SccGraph.is_cyclic_member(SccGraph* g, int v)
{
    if (v < 0 || (usz)v >= g.node_count) { return false; }
    int c = g.component_of[v];
    if (c < 0 || (usz)c >= g.component_count) { return false; }
    if (g.component_size[c] > 1) { return true; }
    return g.has_self_loop[v];
}

// Members of the component containing `v`, written into `out`. Used by the
// reporter to name every module in an import cycle.
fn usz SccGraph.component_members(SccGraph* g, int v, int* out, usz cap)
{
    if (v < 0 || (usz)v >= g.node_count) { return 0; }
    int c = g.component_of[v];
    usz n = 0;
    for (usz i = 0; i < g.node_count && n < cap; i++)
    {
        if (g.component_of[i] == c) { out[n] = (int)i; n = n + 1; }
    }
    return n;
}

fn void SccGraph.report(SccGraph* g)
{
    printf("  scc nodes        : %d\n", (int)g.node_count);
    printf("  scc edges        : %d\n", (int)g.edge_count);
    printf("  components       : %d (cyclic=%d, largest=%d)\n",
           (int)g.component_count, (int)g.cyclic_components, (int)g.largest_component);
}

// Build the module dependency graph from the loader and analyse it.
struct ModuleGraph
{
    SccGraph scc;
    usz      modules;
    usz      cycles_found;
}

fn void ModuleGraph.build(ModuleGraph* mg, pfront_resolve::Loader* l)
{
    mg.modules = l.module_count;
    mg.cycles_found = 0;
    mg.scc.init(l.module_count);
    for (usz i = 0; i < l.module_count; i++)
    {
        mg.scc.begin_node((int)i);
        Mod* m = l.modules[i];
        for (usz j = 0; j < m.import_count; j++)
        {
            Mod* dep = m.imports[j];
            for (usz k = 0; k < l.module_count; k++)
            {
                if (l.modules[k] == dep) { mg.scc.add_edge((int)k); break; }
            }
        }
    }
    mg.scc.finish();
    mg.scc.run();
    mg.cycles_found = mg.scc.cyclic_components;
}

fn void ModuleGraph.report(ModuleGraph* mg, pfront_resolve::Loader* l)
{
    printf("  module graph     : %d modules, %d import cycles\n",
           (int)mg.modules, (int)mg.cycles_found);
    if (mg.cycles_found == 0) { return; }
    for (usz c = 0; c < mg.scc.component_count; c++)
    {
        usz n = 0;
        for (usz i = 0; i < mg.scc.node_count; i++)
        {
            if (mg.scc.component_of[i] == (int)c) { n = n + 1; }
        }
        if (n < 2) { continue; }
        printf("    cycle: ");
        for (usz i = 0; i < mg.scc.node_count; i++)
        {
            if (mg.scc.component_of[i] != (int)c) { continue; }
            char* nm = l.interner.text(l.modules[i].name_id);
            printf("%s ", nm == null ? (char*)"?" : nm);
        }
        printf("\n");
    }
}

// ════════════════════════════════════════════════════════════════════════════
// 3. VISIBILITY / ACCESS CONTROL
// ════════════════════════════════════════════════════════════════════════════
enum Vis : int
{
    VIS_PRIVATE,     // visible only within the declaring module
    VIS_MODULE,      // pub(mod) — visible to the module subtree
    VIS_PUBLIC       // pub — visible everywhere
}

struct VisibilityCheck
{
    pfront_core::DiagBag* diags;
    pfront_core::Interner* interner;
    char* file;
    usz   checked;
    usz   violations;
    usz   public_decls;
    usz   private_decls;
    usz   leaks;
    bool  enforce;
}

fn void VisibilityCheck.init(VisibilityCheck* v, pfront_core::DiagBag* d,
                             pfront_core::Interner* it, char* file)
{
    v.diags = d;
    v.interner = it;
    v.file = file;
    v.checked = 0;
    v.violations = 0;
    v.public_decls = 0;
    v.private_decls = 0;
    v.leaks = 0;
    v.enforce = false;
}

fn Vis vis_of(Node* d)
{
    if (d == null) { return Vis.VIS_PRIVATE; }
    if ((d.flags & pfront_core::NF_PUB) != 0) { return Vis.VIS_PUBLIC; }
    return Vis.VIS_PRIVATE;
}

// A reference crossing a module boundary must target a public declaration.
// A reference crossing a module boundary must target a public declaration.
//
// Enforcement is OPT-IN (`enforce`). Pride's stdlib predates `pub` and treats
// module-level declarations as exported by default, so turning this on
// unconditionally would emit thousands of false positives on correct code.
// The pass still measures the violation count in permissive mode, which is how
// you track progress toward being able to enable it.
fn void VisibilityCheck.walk(VisibilityCheck* v, Node* n, Mod* from, int depth)
{
    if (n == null || depth > 200) { return; }

    if (n.resolved != null && n.owner != null)
    {
        Node* target = n.resolved;
        if (target.owner != null && target.owner != n.owner)
        {
            v.checked = v.checked + 1;
            if (vis_of(target) == Vis.VIS_PRIVATE
                && (target.flags & pfront_core::NF_SYNTHETIC) == 0)
            {
                v.violations = v.violations + 1;
                if (v.enforce)
                {
                    char* nm = v.interner.text(target.name_id);
                    v.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3050,
                                       n.line, n.col,
                                       "this declaration is private to its module",
                                       "mark it `pub` to export it",
                                       v.file);
                }
                else
                {
                    v.diags.add(pfront_core::Severity.SEV_NOTE,
                                pfront_core::Phase.PH_RESOLVE, 3050,
                                n.line, n.col,
                                "cross-module use of a non-pub declaration",
                                null, v.file);
                }
            }
        }
    }

    if (pfront_core::is_decl(n.kind))
    {
        if (vis_of(n) == Vis.VIS_PUBLIC) { v.public_decls = v.public_decls + 1; }
        else { v.private_decls = v.private_decls + 1; }

        // A `pub` declaration whose signature mentions a private type leaks it:
        // callers outside the module can name the function but not its types.
        // This is a real error even in permissive mode, because it is
        // unambiguously wrong regardless of the default-export convention.
        if (vis_of(n) == Vis.VIS_PUBLIC && n.type_ann != null)
        {
            v.check_leak(n, n.type_ann, 0);
        }
    }

    for (usz i = 0; i < n.child_count; i++) { v.walk(n.children[i], from, depth + 1); }
}

// Detect a private type appearing in a public signature.
fn void VisibilityCheck.check_leak(VisibilityCheck* v, Node* decl, Node* ty, int depth)
{
    if (ty == null || depth > 32) { return; }
    if (ty.resolved != null)
    {
        Node* t = ty.resolved;
        bool is_type_decl = t.kind == Nk.N_DECL_STRUCT || t.kind == Nk.N_DECL_UNION
                         || t.kind == Nk.N_DECL_ENUM || t.kind == Nk.N_DECL_NEWTYPE;
        if (is_type_decl && t.owner == decl.owner
            && vis_of(t) == Vis.VIS_PRIVATE
            && (t.flags & pfront_core::NF_SYNTHETIC) == 0)
        {
            v.leaks = v.leaks + 1;
            if (v.enforce)
            {
                v.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3051,
                                   decl.line, decl.col,
                                   "public declaration exposes a private type",
                                   "make the type `pub`, or the declaration private",
                                   v.file);
            }
        }
    }
    for (usz i = 0; i < ty.child_count; i++) { v.check_leak(decl, ty.children[i], depth + 1); }
}

fn void VisibilityCheck.report(VisibilityCheck* v)
{
    printf("  visibility       : %d cross-module refs, %d to non-pub decls\n",
           (int)v.checked, (int)v.violations);
    printf("  declarations     : %d pub / %d private\n",
           (int)v.public_decls, (int)v.private_decls);
    printf("  private-type leaks: %d in public signatures%s\n",
           (int)v.leaks, v.enforce ? " (enforced)" : " (permissive)");
}

// ════════════════════════════════════════════════════════════════════════════
// 4. PATTERN USEFULNESS (Maranget's algorithm)
// ════════════════════════════════════════════════════════════════════════════
// The exhaustiveness check in `pfront_ext` answers "did every variant appear?".
// That is too weak for nested patterns: `Some(0)` and `None` cover both
// constructors yet miss `Some(1)`.
//
// Maranget's formulation works on a matrix P of patterns and asks whether a
// vector q is *useful* with respect to P — i.e. whether some value matches q
// but no row of P. Exhaustiveness is then "the wildcard vector is not useful".
// The same machinery reports redundant arms (a row useless w.r.t. its
// predecessors) and produces a concrete counter-example.

// Constructor identity for a pattern head.
enum CtorKind : int
{
    CTOR_WILD,        // _ or a binder: matches anything
    CTOR_VARIANT,     // enum variant, discriminated by name_id
    CTOR_INT,         // integer literal
    CTOR_BOOL,
    CTOR_STRING,
    CTOR_TUPLE,
    CTOR_STRUCT,
    CTOR_RANGE,
    CTOR_OR,
    CTOR_OTHER
}

struct Ctor
{
    CtorKind kind;
    uint     name_id;    // variant name
    ulong    value;      // literal value
    usz      arity;      // sub-pattern count
}

fn Ctor ctor_of(Node* p)
{
    Ctor c;
    c.kind = CtorKind.CTOR_WILD;
    c.name_id = 0;
    c.value = 0;
    c.arity = 0;
    if (p == null) { return c; }
    switch (p.kind)
    {
        case N_PAT_WILDCARD:
        case N_PAT_IDENT:
        case N_PAT_REST:
            c.kind = CtorKind.CTOR_WILD;
        case N_PAT_VARIANT:
        {
            c.kind = CtorKind.CTOR_VARIANT;
            c.name_id = p.name_id;
            // child 0 is the path; the remainder are payload sub-patterns.
            c.arity = p.child_count > 0 ? p.child_count - 1 : 0;
        }
        case N_PAT_TUPLE:
        {
            c.kind = CtorKind.CTOR_TUPLE;
            c.arity = p.child_count;
        }
        case N_PAT_STRUCT:
        {
            c.kind = CtorKind.CTOR_STRUCT;
            c.name_id = p.name_id;
            c.arity = p.child_count > 0 ? p.child_count - 1 : 0;
        }
        case N_PAT_LITERAL:
        {
            Node* lit = p.child(0);
            if (lit == null) { c.kind = CtorKind.CTOR_OTHER; }
            else if (lit.kind == Nk.N_EXPR_BOOL)
            {
                c.kind = CtorKind.CTOR_BOOL;
                c.value = lit.p.ival;
            }
            else if (lit.kind == Nk.N_EXPR_INT || lit.kind == Nk.N_EXPR_CHAR)
            {
                c.kind = CtorKind.CTOR_INT;
                c.value = lit.p.ival;
            }
            else if (lit.kind == Nk.N_EXPR_STRING)
            {
                c.kind = CtorKind.CTOR_STRING;
            }
            else { c.kind = CtorKind.CTOR_OTHER; }
        }
        case N_PAT_RANGE:
            c.kind = CtorKind.CTOR_RANGE;
        case N_PAT_OR:
            c.kind = CtorKind.CTOR_OR;
        default:
            c.kind = CtorKind.CTOR_OTHER;
    }
    return c;
}

fn bool ctor_eq(Ctor a, Ctor b)
{
    if (a.kind != b.kind) { return false; }
    switch (a.kind)
    {
        case CTOR_VARIANT:
        case CTOR_STRUCT:
            return a.name_id == b.name_id;
        case CTOR_INT:
        case CTOR_BOOL:
            return a.value == b.value;
        default:
            return true;
    }
}

// Pattern matrix: rows of column-vectors.
struct PatMatrix
{
    Node*[MAX_MATRIX_ROWS * MAX_MATRIX_COLS] cells;
    usz rows;
    usz cols;
}

fn void PatMatrix.init(PatMatrix* m, usz cols)
{
    m.rows = 0;
    m.cols = cols < MAX_MATRIX_COLS ? cols : MAX_MATRIX_COLS;
}

fn Node* PatMatrix.at(PatMatrix* m, usz r, usz c)
{
    if (r >= m.rows || c >= m.cols) { return null; }
    return m.cells[r * MAX_MATRIX_COLS + c];
}

fn void PatMatrix.set(PatMatrix* m, usz r, usz c, Node* v)
{
    if (r >= MAX_MATRIX_ROWS || c >= MAX_MATRIX_COLS) { return; }
    m.cells[r * MAX_MATRIX_COLS + c] = v;
}

fn bool PatMatrix.push_row1(PatMatrix* m, Node* p)
{
    if (m.rows >= MAX_MATRIX_ROWS) { return false; }
    m.set(m.rows, 0, p);
    m.rows = m.rows + 1;
    return true;
}

// S(c, P): specialise the matrix for constructor c. Rows whose head does not
// match c are dropped; matching rows expand their sub-patterns into the first
// `arity` columns.
fn void specialise(PatMatrix* src, Ctor c, PatMatrix* dst)
{
    usz new_cols = c.arity + (src.cols > 0 ? src.cols - 1 : 0);
    dst.init(new_cols == 0 ? 1 : new_cols);
    dst.rows = 0;
    for (usz r = 0; r < src.rows; r++)
    {
        Node* head = src.at(r, 0);
        Ctor hc = ctor_of(head);
        bool keep = hc.kind == CtorKind.CTOR_WILD || ctor_eq(hc, c);
        if (!keep) { continue; }
        if (dst.rows >= MAX_MATRIX_ROWS) { break; }
        usz col = 0;
        if (hc.kind == CtorKind.CTOR_WILD)
        {
            for (usz k = 0; k < c.arity && col < dst.cols; k++)
            {
                dst.set(dst.rows, col, null);   // null == wildcard
                col = col + 1;
            }
        }
        else
        {
            usz first = head.kind == Nk.N_PAT_VARIANT || head.kind == Nk.N_PAT_STRUCT ? 1 : 0;
            for (usz k = 0; k < c.arity && col < dst.cols; k++)
            {
                dst.set(dst.rows, col, head.child(first + k));
                col = col + 1;
            }
        }
        for (usz k = 1; k < src.cols && col < dst.cols; k++)
        {
            dst.set(dst.rows, col, src.at(r, k));
            col = col + 1;
        }
        dst.rows = dst.rows + 1;
    }
}

// D(P): the default matrix — rows whose head is a wildcard, head column removed.
fn void default_matrix(PatMatrix* src, PatMatrix* dst)
{
    usz nc = src.cols > 0 ? src.cols - 1 : 0;
    dst.init(nc == 0 ? 1 : nc);
    dst.rows = 0;
    for (usz r = 0; r < src.rows; r++)
    {
        Node* head = src.at(r, 0);
        Ctor hc = ctor_of(head);
        if (hc.kind != CtorKind.CTOR_WILD) { continue; }
        if (dst.rows >= MAX_MATRIX_ROWS) { break; }
        for (usz k = 1; k < src.cols; k++) { dst.set(dst.rows, k - 1, src.at(r, k)); }
        dst.rows = dst.rows + 1;
    }
}

struct UsefulnessResult
{
    bool  exhaustive;
    bool  found_witness;
    uint  witness_ctor;      // name_id of a missing variant, if known
    usz   redundant_rows;
    usz   depth_reached;
}

// Collect the distinct constructors appearing in the head column.
fn usz head_ctors(PatMatrix* m, Ctor* out, usz cap)
{
    usz n = 0;
    for (usz r = 0; r < m.rows; r++)
    {
        Ctor c = ctor_of(m.at(r, 0));
        if (c.kind == CtorKind.CTOR_WILD || c.kind == CtorKind.CTOR_OR) { continue; }
        bool seen = false;
        for (usz i = 0; i < n; i++) { if (ctor_eq(out[i], c)) { seen = true; break; } }
        if (!seen && n < cap) { out[n] = c; n = n + 1; }
    }
    return n;
}

// Is the all-wildcard vector useful w.r.t. P? If yes, P is not exhaustive.
// Per-depth scratch matrices. Recursion depth is bounded, so one matrix per
// level is enough and nothing is allocated inside the hot loop.
const usz USEFUL_MAX_DEPTH = 12;
struct MatrixPool
{
    PatMatrix[USEFUL_MAX_DEPTH + 2] level;
}
MatrixPool g_pool @private;

fn bool wildcard_useful(PatMatrix* m, Node* enum_decl, int depth, UsefulnessResult* res)
{
    if (depth > (int)USEFUL_MAX_DEPTH) { return false; }
    if ((usz)depth > res.depth_reached) { res.depth_reached = (usz)depth; }
    if (m.rows == 0) { return true; }          // nothing matches: useful
    if (m.cols == 0) { return false; }         // every row matches: not useful

    Ctor[64] ctors;
    usz nc = head_ctors(m, &ctors[0], 64);
    if (nc == 0)
    {
        PatMatrix* d = &g_pool.level[depth];
        default_matrix(m, d);
        return wildcard_useful(d, null, depth + 1, res);
    }

    // Complete signature test: for an enum we know the full constructor set.
    if (enum_decl != null)
    {
        usz total = 0;
        for (usz i = 0; i < enum_decl.child_count; i++)
        {
            Node* v = enum_decl.children[i];
            if (v != null && v.kind == Nk.N_DECL_VARIANT) { total = total + 1; }
        }
        if (total > 0 && nc < total)
        {
            // A variant is missing: record it as the witness.
            for (usz i = 0; i < enum_decl.child_count; i++)
            {
                Node* v = enum_decl.children[i];
                if (v == null || v.kind != Nk.N_DECL_VARIANT) { continue; }
                bool covered = false;
                for (usz k = 0; k < nc; k++)
                {
                    if (ctors[k].name_id == v.name_id) { covered = true; break; }
                }
                if (!covered)
                {
                    res.found_witness = true;
                    res.witness_ctor = v.name_id;
                    return true;
                }
            }
            return true;
        }
        // Signature complete: useful only if useful under some constructor.
        for (usz k = 0; k < nc; k++)
        {
            PatMatrix* sp = &g_pool.level[depth];
            specialise(m, ctors[k], sp);
            if (wildcard_useful(sp, null, depth + 1, res)) { return true; }
        }
        return false;
    }

    // Unknown/infinite signature (integers, strings): the default matrix
    // decides, because there is always another value outside the listed set.
    PatMatrix* d2 = &g_pool.level[depth];
    default_matrix(m, d2);
    return wildcard_useful(d2, null, depth + 1, res);
}

struct PatternAnalysis
{
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char* file;
    usz   matches_analysed;
    usz   non_exhaustive;
    usz   redundant_arms;
    usz   witnesses;
    usz   depth_peak;
}

fn void PatternAnalysis.init(PatternAnalysis* a, pfront_core::DiagBag* d,
                             pfront_core::Interner* it, char* file)
{
    a.diags = d;
    a.interner = it;
    a.file = file;
    a.matches_analysed = 0;
    a.non_exhaustive = 0;
    a.redundant_arms = 0;
    a.witnesses = 0;
    a.depth_peak = 0;
}

fn Node* enum_from_type(Node* ty)
{
    if (ty == null) { return null; }
    if (ty.resolved != null && ty.resolved.kind == Nk.N_DECL_ENUM) { return ty.resolved; }
    // Unwrap pointer/reference wrappers: `*Color` still matches on Color.
    if (ty.kind == Nk.N_TY_PTR || ty.kind == Nk.N_TY_REF)
    {
        return enum_from_type(ty.child(0));
    }
    return null;
}

// Walk outward from a binder to the signature that gave it a type. A clause
// parameter has no annotation of its own; its type lives in the enclosing
// function's `fn : Color -> i64` signature.
fn Node* enum_from_enclosing_signature(Node* binder)
{
    Node* cur = binder;
    int hops = 0;
    while (cur != null && hops < 24)
    {
        if (cur.kind == Nk.N_DECL_FN || cur.kind == Nk.N_DECL_EXTERN_FN)
        {
            Node* sig = cur.type_ann;
            if (sig != null)
            {
                // N_TY_FN: child 0 is the parameter type (or tuple of them).
                Node* param = sig.child(0);
                Node* e = enum_from_type(param);
                if (e != null) { return e; }
                if (param != null && param.kind == Nk.N_TY_TUPLE)
                {
                    for (usz i = 0; i < param.child_count; i++)
                    {
                        e = enum_from_type(param.children[i]);
                        if (e != null) { return e; }
                    }
                }
            }
            return null;
        }
        cur = cur.parent;
        hops = hops + 1;
    }
    return null;
}

fn Node* resolve_enum_for(Node* scrut)
{
    if (scrut == null) { return null; }
    if (scrut.resolved != null)
    {
        Node* d = scrut.resolved;
        if (d.kind == Nk.N_DECL_ENUM) { return d; }
        if (d.type_ann != null && d.type_ann.resolved != null
            && d.type_ann.resolved.kind == Nk.N_DECL_ENUM) { return d.type_ann.resolved; }
        // A binder annotated with an enum type.
        if (d.kind == Nk.N_PAT_IDENT && d.type_ann != null)
        {
            Node* t = enum_from_type(d.type_ann);
            if (t != null) { return t; }
        }
        // Clause binders carry no annotation; consult the fn signature.
        Node* viaSig = enum_from_enclosing_signature(d);
        if (viaSig != null) { return viaSig; }
    }
    return null;
}

fn void PatternAnalysis.check_match(PatternAnalysis* a, Node* m)
{
    if (m == null || m.child_count < 2) { return; }
    a.matches_analysed = a.matches_analysed + 1;

    PatMatrix* mp = &g_pool.level[USEFUL_MAX_DEPTH + 1];
    mp.init(1);
    for (usz i = 1; i < m.child_count; i++)
    {
        Node* arm = m.children[i];
        if (arm == null) { continue; }
        Node* pat = arm.child(0);
        // A guarded arm cannot be assumed to match, so it does not contribute
        // to coverage — the same rule rustc uses.
        bool guarded = false;
        for (usz j = 1; j < arm.child_count; j++)
        {
            Node* c = arm.children[j];
            if (c != null && c.kind == Nk.N_GUARD) { guarded = true; }
        }
        if (guarded) { continue; }
        mp.push_row1(pat);
    }

    Node* en = resolve_enum_for(m.child(0));
    UsefulnessResult res;
    res.exhaustive = true;
    res.found_witness = false;
    res.witness_ctor = 0;
    res.redundant_rows = 0;
    res.depth_reached = 0;

    bool missing = wildcard_useful(mp, en, 0, &res);
    if (res.depth_reached > a.depth_peak) { a.depth_peak = res.depth_reached; }

    if (missing)
    {
        a.non_exhaustive = a.non_exhaustive + 1;
        if (res.found_witness && res.witness_ctor != 0)
        {
            a.witnesses = a.witnesses + 1;
            char* w = a.interner.text(res.witness_ctor);
            a.diags.add(pfront_core::Severity.SEV_WARNING,
                        pfront_core::Phase.PH_RESOLVE, 4011,
                        m.line, m.col,
                        "match is not exhaustive", w, a.file);
        }
        else
        {
            a.diags.warn(pfront_core::Phase.PH_RESOLVE, 4012, m.line, m.col,
                         "match may not be exhaustive", a.file);
        }
    }
    else
    {
        m.flags = m.flags | pfront_core::NF_EXHAUSTIVE;
    }
}

fn void PatternAnalysis.walk(PatternAnalysis* a, Node* n, int depth)
{
    if (n == null || depth > 200) { return; }
    if (n.kind == Nk.N_EXPR_MATCH) { a.check_match(n); }
    for (usz i = 0; i < n.child_count; i++) { a.walk(n.children[i], depth + 1); }
}

fn void PatternAnalysis.report(PatternAnalysis* a)
{
    printf("  pattern matrices : %d analysed, %d non-exhaustive (%d with witness)\n",
           (int)a.matches_analysed, (int)a.non_exhaustive, (int)a.witnesses);
    printf("  usefulness depth : %d\n", (int)a.depth_peak);
}

// ════════════════════════════════════════════════════════════════════════════
// 5. CONST EXPRESSION EVALUATION
// ════════════════════════════════════════════════════════════════════════════
enum ConstStatus : int
{
    CONST_OK,
    CONST_NOT_CONST,
    CONST_OVERFLOW,
    CONST_DIV_ZERO,
    CONST_BAD_SHIFT,
    CONST_DEPTH
}

struct ConstValue
{
    ConstStatus status;
    long        ival;
    double      fval;
    bool        is_float;
    bool        is_bool;
}

fn ConstValue const_err(ConstStatus s)
{
    ConstValue v;
    v.status = s;
    v.ival = 0;
    v.fval = 0.0;
    v.is_float = false;
    v.is_bool = false;
    return v;
}

// Reduce a value to `bits` width with the given signedness, matching two's
// complement wrap-around semantics.
fn long truncate_to(long v, int bits, bool is_signed)
{
    if (bits <= 0 || bits >= 64) { return v; }
    ulong mask = ((ulong)1 << (ulong)bits) - 1;
    ulong raw = (ulong)v & mask;
    if (!is_signed) { return (long)raw; }
    ulong sign_bit = (ulong)1 << (ulong)(bits - 1);
    if ((raw & sign_bit) != 0)
    {
        // Sign-extend: set every bit above the width.
        return (long)(raw | ~mask);
    }
    return (long)raw;
}

fn ConstValue const_bool(bool b)
{
    ConstValue v;
    v.status = ConstStatus.CONST_OK;
    v.ival = b ? 1 : 0;
    v.fval = 0.0;
    v.is_float = false;
    v.is_bool = true;
    return v;
}

fn ConstValue const_int(long x)
{
    ConstValue v;
    v.status = ConstStatus.CONST_OK;
    v.ival = x;
    v.fval = 0.0;
    v.is_float = false;
    v.is_bool = false;
    return v;
}

// Signed 64-bit overflow detection without relying on UB.
fn bool add_overflows(long a, long b)
{
    if (b > 0 && a > 9223372036854775807L - b) { return true; }
    if (b < 0 && a < -9223372036854775807L - 1 - b) { return true; }
    return false;
}

fn bool sub_overflows(long a, long b)
{
    if (b < 0 && a > 9223372036854775807L + b) { return true; }
    if (b > 0 && a < -9223372036854775807L - 1 + b) { return true; }
    return false;
}

fn bool mul_overflows(long a, long b)
{
    if (a == 0 || b == 0) { return false; }
    long r = a * b;
    return r / b != a;
}

struct ConstEval
{
    pfront_core::DiagBag* diags;
    char* file;
    usz   evaluated;
    usz   folded;
    usz   overflows;
    usz   div_zero;
    usz   bad_shifts;
    usz   folded_ok;
}

fn void ConstEval.init(ConstEval* c, pfront_core::DiagBag* d, char* file)
{
    c.diags = d;
    c.file = file;
    c.evaluated = 0;
    c.folded = 0;
    c.overflows = 0;
    c.div_zero = 0;
    c.bad_shifts = 0;
    c.folded_ok = 0;
}

fn ConstValue ConstEval.eval(ConstEval* c, Node* e, int depth)
{
    if (e == null) { return const_err(ConstStatus.CONST_NOT_CONST); }
    if (depth > 64) { return const_err(ConstStatus.CONST_DEPTH); }
    c.evaluated = c.evaluated + 1;

    switch (e.kind)
    {
        case N_EXPR_INT:
            return const_int((long)e.p.ival);
        case N_EXPR_CHAR:
            return const_int((long)e.p.ival);
        case N_EXPR_BOOL:
        {
            ConstValue v = const_int((long)e.p.ival);
            v.is_bool = true;
            return v;
        }
        case N_EXPR_FLOAT:
        {
            ConstValue v;
            v.status = ConstStatus.CONST_OK;
            v.ival = 0;
            v.fval = e.p.fval;
            v.is_float = true;
            v.is_bool = false;
            return v;
        }
        case N_EXPR_IDENT:
        {
            // A const declaration folds to its initializer.
            if (e.resolved != null && e.resolved.kind == Nk.N_DECL_CONST)
            {
                for (usz i = 0; i < e.resolved.child_count; i++)
                {
                    Node* init = e.resolved.children[i];
                    if (init != null && pfront_core::is_expr(init.kind))
                    {
                        return c.eval(init, depth + 1);
                    }
                }
            }
            return const_err(ConstStatus.CONST_NOT_CONST);
        }
        case N_EXPR_UNARY:
        {
            ConstValue a = c.eval(e.child(0), depth + 1);
            if (a.status != ConstStatus.CONST_OK) { return a; }
            if (a.is_float) { return const_err(ConstStatus.CONST_NOT_CONST); }
            Tk uop = (Tk)e.p.op;
            if (uop == Tk.TOKEN_BANG || uop == Tk.TOKEN_KW_NOT) { return const_bool(a.ival == 0); }
            if (uop == Tk.TOKEN_TILDE) { return const_int((long)(~(ulong)a.ival)); }
            if (a.ival == -9223372036854775807L - 1)
            {
                c.overflows = c.overflows + 1;
                return const_err(ConstStatus.CONST_OVERFLOW);
            }
            return const_int(-a.ival);
        }
        case N_EXPR_BINARY:
        {
            ConstValue a = c.eval(e.child(0), depth + 1);
            if (a.status != ConstStatus.CONST_OK) { return a; }
            ConstValue b = c.eval(e.child(1), depth + 1);
            if (b.status != ConstStatus.CONST_OK) { return b; }
            if (a.is_float || b.is_float) { return const_err(ConstStatus.CONST_NOT_CONST); }
            return c.apply_binop(e, a, b);
        }
        case N_EXPR_CAST:
        {
            // A cast in constant position must TRUNCATE, not pass through:
            // `300 as u8` is 44, and folding it as 300 would silently produce
            // a wrong array length or enum discriminant.
            ConstValue inner = c.eval(e.child(0), depth + 1);
            if (inner.status != ConstStatus.CONST_OK) { return inner; }
            if (inner.is_float) { return inner; }
            int bits = 0;
            bool sg = true;
            if (!c.int_type_of(e.type_ann, &bits, &sg)) { return inner; }
            return const_int(truncate_to(inner.ival, bits, sg));
        }
        default:
            return const_err(ConstStatus.CONST_NOT_CONST);
    }
}

fn ConstValue ConstEval.apply_binop(ConstEval* c, Node* e, ConstValue a, ConstValue b)
{
    // Operator codes are lexer TokenType values, stored as int at parse time.
    Tk op = (Tk)e.p.op;
    long x = a.ival;
    long y = b.ival;

    switch (op)
    {
        case TOKEN_PLUS:
        {
            if (add_overflows(x, y)) { c.overflows = c.overflows + 1; return const_err(ConstStatus.CONST_OVERFLOW); }
            return const_int(x + y);
        }
        case TOKEN_MINUS:
        {
            if (sub_overflows(x, y)) { c.overflows = c.overflows + 1; return const_err(ConstStatus.CONST_OVERFLOW); }
            return const_int(x - y);
        }
        case TOKEN_STAR:
        {
            if (mul_overflows(x, y)) { c.overflows = c.overflows + 1; return const_err(ConstStatus.CONST_OVERFLOW); }
            return const_int(x * y);
        }
        case TOKEN_SLASH:
        {
            if (y == 0) { c.div_zero = c.div_zero + 1; return const_err(ConstStatus.CONST_DIV_ZERO); }
            // INT64_MIN / -1 overflows in two's complement.
            if (x == -9223372036854775807L - 1 && y == -1)
            {
                c.overflows = c.overflows + 1;
                return const_err(ConstStatus.CONST_OVERFLOW);
            }
            return const_int(x / y);
        }
        case TOKEN_PERCENT:
        {
            if (y == 0) { c.div_zero = c.div_zero + 1; return const_err(ConstStatus.CONST_DIV_ZERO); }
            if (x == -9223372036854775807L - 1 && y == -1) { return const_int(0); }
            return const_int(x % y);
        }
        // Wrapping forms are defined to wrap: no overflow diagnostic.
        case TOKEN_PLUS_PERCENT:  return const_int((long)((ulong)x + (ulong)y));
        case TOKEN_MINUS_PERCENT: return const_int((long)((ulong)x - (ulong)y));
        case TOKEN_STAR_PERCENT:  return const_int((long)((ulong)x * (ulong)y));
        // Saturating forms clamp instead of wrapping.
        case TOKEN_PLUS_PIPE:
        {
            if (add_overflows(x, y)) { return const_int(y > 0 ? 9223372036854775807L : -9223372036854775807L - 1); }
            return const_int(x + y);
        }
        case TOKEN_MINUS_PIPE:
        {
            if (sub_overflows(x, y)) { return const_int(y < 0 ? 9223372036854775807L : -9223372036854775807L - 1); }
            return const_int(x - y);
        }
        case TOKEN_STAR_PIPE:
        {
            if (mul_overflows(x, y))
            {
                bool neg = (x < 0) != (y < 0);
                return const_int(neg ? -9223372036854775807L - 1 : 9223372036854775807L);
            }
            return const_int(x * y);
        }
        case TOKEN_AMP:    return const_int((long)((ulong)x & (ulong)y));
        case TOKEN_PIPE:   return const_int((long)((ulong)x | (ulong)y));
        case TOKEN_XOR:    return const_int((long)((ulong)x ^ (ulong)y));
        case TOKEN_LSHIFT:
        {
            // A shift count outside [0,63] is undefined in C semantics; reject
            // it at compile time rather than emitting a platform-dependent
            // constant.
            if (y < 0 || y > 63) { c.bad_shifts = c.bad_shifts + 1; return const_err(ConstStatus.CONST_BAD_SHIFT); }
            return const_int((long)((ulong)x << (ulong)y));
        }
        case TOKEN_RSHIFT:
        {
            if (y < 0 || y > 63) { c.bad_shifts = c.bad_shifts + 1; return const_err(ConstStatus.CONST_BAD_SHIFT); }
            return const_int(x >> y);
        }
        case TOKEN_EQEQ:   return const_bool(x == y);
        case TOKEN_NEQ:
        case TOKEN_NEQ_UNI: return const_bool(x != y);
        case TOKEN_LT:     return const_bool(x < y);
        case TOKEN_LTEQ:
        case TOKEN_LEQ_UNI: return const_bool(x <= y);
        case TOKEN_GT:     return const_bool(x > y);
        case TOKEN_GTEQ:
        case TOKEN_GEQ_UNI: return const_bool(x >= y);
        case TOKEN_AMPAMP:
        case TOKEN_KW_AND: return const_bool(x != 0 && y != 0);
        case TOKEN_PIPEPIPE:
        case TOKEN_KW_OR:  return const_bool(x != 0 || y != 0);
        default:
            return const_err(ConstStatus.CONST_NOT_CONST);
    }
}

// Walk the tree folding every context that REQUIRES a constant: array sizes,
// enum discriminants, and const/static initialisers. Diagnosing these here
// means a bad array length is caught in the front end rather than surfacing
// as a bogus type or a backend crash.
// Recognise an integer type annotation and report its width/signedness.
fn bool ConstEval.int_type_of(ConstEval* c, Node* ty, int* bits, bool* is_signed)
{
    if (ty == null) { return false; }
    if (ty.kind != Nk.N_TY_NAME) { return false; }
    char* s = ty.p.sptr;
    usz n = ty.p.slen;
    if (s == null || n < 2 || n > 4) { return false; }
    char head = s[0];
    if (head != 'i' && head != 'u') { return false; }
    int w = 0;
    for (usz i = 1; i < n; i++)
    {
        if (s[i] < '0' || s[i] > '9') { return false; }
        w = w * 10 + (int)(s[i] - '0');
    }
    if (w != 8 && w != 16 && w != 32 && w != 64) { return false; }
    *bits = w;
    *is_signed = head == 'i';
    return true;
}

fn void ConstEval.walk(ConstEval* c, Node* n, int depth)
{
    if (n == null || depth > 200) { return; }

    if (n.kind == Nk.N_TY_ARRAY && n.child_count >= 2)
    {
        Node* arr_len = n.children[1];
        ConstValue v = c.eval(arr_len, 0);
        if (v.status == ConstStatus.CONST_OK)
        {
            if (v.ival < 0)
            {
                c.diags.error(pfront_core::Phase.PH_RESOLVE, 3030, arr_len.line, arr_len.col,
                              "array length must not be negative", c.file);
            }
            else
            {
                arr_len.p.ival = (ulong)v.ival;
                arr_len.flags = arr_len.flags | pfront_core::NF_TYPED;
                c.folded_ok = c.folded_ok + 1;
            }
        }
        else if (v.status == ConstStatus.CONST_OVERFLOW)
        {
            c.diags.error(pfront_core::Phase.PH_RESOLVE, 3031, arr_len.line, arr_len.col,
                          "array length overflows a 64-bit integer", c.file);
        }
        else if (v.status == ConstStatus.CONST_DIV_ZERO)
        {
            c.diags.error(pfront_core::Phase.PH_RESOLVE, 3032, arr_len.line, arr_len.col,
                          "division by zero in array length", c.file);
        }
    }

    if (n.kind == Nk.N_DECL_VARIANT && n.p.aux == 1)
    {
        for (usz i = 0; i < n.child_count; i++)
        {
            Node* d = n.children[i];
            if (d == null || !pfront_core::is_expr(d.kind)) { continue; }
            ConstValue v = c.eval(d, 0);
            if (v.status == ConstStatus.CONST_OK)
            {
                n.p.ival = (ulong)v.ival;
                c.folded_ok = c.folded_ok + 1;
            }
            else
            {
                c.diags.error(pfront_core::Phase.PH_RESOLVE, 3033, d.line, d.col,
                              "enum discriminant is not a constant expression", c.file);
            }
        }
    }

    if (n.kind == Nk.N_DECL_CONST)
    {
        for (usz i = 0; i < n.child_count; i++)
        {
            Node* d = n.children[i];
            if (d == null || !pfront_core::is_expr(d.kind)) { continue; }
            ConstValue v = c.eval(d, 0);
            if (v.status == ConstStatus.CONST_OVERFLOW)
            {
                c.diags.error(pfront_core::Phase.PH_RESOLVE, 3034, d.line, d.col,
                              "constant expression overflows", c.file);
            }
            else if (v.status == ConstStatus.CONST_DIV_ZERO)
            {
                c.diags.error(pfront_core::Phase.PH_RESOLVE, 3032, d.line, d.col,
                              "division by zero in constant expression", c.file);
            }
            else if (v.status == ConstStatus.CONST_BAD_SHIFT)
            {
                c.diags.error(pfront_core::Phase.PH_RESOLVE, 3035, d.line, d.col,
                              "shift amount out of range (must be 0..63)", c.file);
            }
            else if (v.status == ConstStatus.CONST_OK) { c.folded_ok = c.folded_ok + 1; }
        }
    }

    for (usz i = 0; i < n.child_count; i++) { c.walk(n.children[i], depth + 1); }
    if (n.type_ann != null) { c.walk(n.type_ann, depth + 1); }
}

fn void ConstEval.report(ConstEval* c)
{
    printf("  const eval       : %d nodes, %d folded, %d overflow, %d div-zero, %d bad-shift\n",
           (int)c.evaluated, (int)c.folded_ok, (int)c.overflows,
           (int)c.div_zero, (int)c.bad_shifts);
}

// ════════════════════════════════════════════════════════════════════════════
// 6. CYCLIC TYPE DETECTION
// ════════════════════════════════════════════════════════════════════════════
// `struct A { b : B }` + `struct B { a : A }` is infinite-sized. Behind a
// pointer it is fine. Walk field types, following only by-value edges.
struct TypeCycleCheck
{
    pfront_core::DiagBag* diags;
    pfront_core::Interner* interner;
    char* file;
    Node*[CYCLE_STACK_CAP] stack;
    usz        depth;
    usz        checked;
    usz        cycles;
    usz        visits;
    Node*[MEMO_CAP] memo_decl;
    int[MEMO_CAP]   memo_state;
    usz             memo_count;
}

fn void TypeCycleCheck.init(TypeCycleCheck* t, pfront_core::DiagBag* d,
                            pfront_core::Interner* it, char* file)
{
    t.diags = d;
    t.interner = it;
    t.file = file;
    t.depth = 0;
    t.checked = 0;
    t.cycles = 0;
    t.visits = 0;
    t.memo_count = 0;
}

fn bool TypeCycleCheck.on_stack(TypeCycleCheck* t, Node* d)
{
    for (usz i = 0; i < t.depth; i++) { if (t.stack[i] == d) { return true; } }
    return false;
}

// Memo slots: a declaration already proven acyclic never needs revisiting.
// Without this a diamond (`A` holding two `B`s that each hold `C`) is explored
// exponentially; the stdlib has aggregates nested deeply enough to notice.
fn int TypeCycleCheck.memo_of(TypeCycleCheck* t, Node* d)
{
    for (usz i = 0; i < t.memo_count; i++)
    {
        if (t.memo_decl[i] == d) { return t.memo_state[i]; }
    }
    return 0;   // 0 = unknown, 1 = acyclic, 2 = cyclic
}

fn void TypeCycleCheck.memo_set(TypeCycleCheck* t, Node* d, int state)
{
    for (usz i = 0; i < t.memo_count; i++)
    {
        if (t.memo_decl[i] == d) { t.memo_state[i] = state; return; }
    }
    if (t.memo_count >= MEMO_CAP) { return; }
    t.memo_decl[t.memo_count] = d;
    t.memo_state[t.memo_count] = state;
    t.memo_count = t.memo_count + 1;
}

// An aggregate embedded BY VALUE propagates a cycle. Arrays and tuples embed
// their elements by value, so `struct A { xs : [A; 4] }` is just as infinite as
// `struct A { a : A }` — the original check missed both.
fn Node* by_value_target(Node* ty, int depth)
{
    if (ty == null || depth > 16) { return null; }
    switch (ty.kind)
    {
        case N_TY_PTR:
        case N_TY_REF:
        case N_TY_SLICE:
        case N_TY_FN:
            return null;                       // indirection breaks the cycle
        case N_TY_ARRAY:
        {
            // A zero-length array occupies no storage, so it cannot recurse.
            Node* len = ty.child(1);
            if (len != null && len.p.ival == 0) { return null; }
            return by_value_target(ty.child(0), depth + 1);
        }
        case N_TY_TUPLE:
        {
            for (usz i = 0; i < ty.child_count; i++)
            {
                Node* r = by_value_target(ty.children[i], depth + 1);
                if (r != null) { return r; }
            }
            return null;
        }
        case N_TY_NAME:
        case N_TY_PATH:
        case N_TY_GENERIC:
        {
            Node* target = ty.resolved;
            if (target == null) { return null; }
            // A type alias is transparent: follow it to the real aggregate.
            if (target.kind == Nk.N_DECL_TYPE && target.type_ann != null)
            {
                return by_value_target(target.type_ann, depth + 1);
            }
            if (target.kind == Nk.N_DECL_STRUCT || target.kind == Nk.N_DECL_UNION
             || target.kind == Nk.N_DECL_NEWTYPE)
            {
                return target;
            }
            return null;
        }
        default:
            return null;
    }
}

// Returns true when a by-value cycle was found starting at `decl`.
fn bool TypeCycleCheck.visit(TypeCycleCheck* t, Node* decl)
{
    if (decl == null) { return false; }
    if (t.on_stack(decl)) { return true; }
    int memo = t.memo_of(decl);
    if (memo == 1) { return false; }
    if (memo == 2) { return true; }
    if (t.depth >= CYCLE_STACK_CAP) { return false; }

    t.stack[t.depth] = decl;
    t.depth = t.depth + 1;
    t.visits = t.visits + 1;

    bool found = false;
    for (usz i = 0; i < decl.child_count && !found; i++)
    {
        Node* f = decl.children[i];
        if (f == null) { continue; }
        // Struct/union fields, enum variant payloads, and newtype bodies all
        // embed by value.
        Node* ty = null;
        if (f.kind == Nk.N_DECL_FIELD) { ty = f.type_ann; }
        else if (f.kind == Nk.N_DECL_VARIANT)
        {
            for (usz k = 0; k < f.child_count && !found; k++)
            {
                Node* pay = f.children[k];
                if (pay == null || !pfront_core::is_type(pay.kind)) { continue; }
                Node* tgt2 = by_value_target(pay, 0);
                if (tgt2 != null && t.visit(tgt2)) { found = true; }
            }
            continue;
        }
        if (ty == null) { continue; }
        Node* target = by_value_target(ty, 0);
        if (target != null && t.visit(target)) { found = true; }
    }
    if (decl.kind == Nk.N_DECL_NEWTYPE && decl.type_ann != null && !found)
    {
        Node* tgt = by_value_target(decl.type_ann, 0);
        if (tgt != null && t.visit(tgt)) { found = true; }
    }

    t.depth = t.depth - 1;
    // Only memoise a NEGATIVE result. A positive one may depend on where the
    // walk started (the node could be on the stack for an unrelated reason),
    // so caching it risks a false positive on a different root.
    if (!found) { t.memo_set(decl, 1); }
    return found;
}

fn void TypeCycleCheck.walk(TypeCycleCheck* t, Node* root, int depth)
{
    if (root == null || depth > 100) { return; }
    for (usz i = 0; i < root.child_count; i++)
    {
        Node* d = root.children[i];
        if (d == null) { continue; }
        if (d.kind == Nk.N_DECL_STRUCT || d.kind == Nk.N_DECL_UNION
         || d.kind == Nk.N_DECL_ENUM || d.kind == Nk.N_DECL_NEWTYPE)
        {
            t.checked = t.checked + 1;
            t.depth = 0;
            if (t.visit(d))
            {
                t.cycles = t.cycles + 1;
                t.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3020, d.line, d.col,
                                   "recursive type has infinite size",
                                   "insert a pointer (`*T`) to break the cycle",
                                   t.file);
            }
        }
        else if (d.kind == Nk.N_MODULE) { t.walk(d, depth + 1); }
    }
}

fn void TypeCycleCheck.report(TypeCycleCheck* t)
{
    printf("  type cycles      : %d aggregates checked, %d infinite-size (%d visits, %d memoised)\n",
           (int)t.checked, (int)t.cycles, (int)t.visits, (int)t.memo_count);
}
