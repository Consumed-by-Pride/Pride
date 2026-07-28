// pgen.c3 — Pattern Generation Language → decision trees (MSP step 4)
// Implementation language: C3 (host). Fourth component of the MSP stage.
// PGL  `pgen name<C> → [binds : Types] where [pattern] ↦ action`  generates a
// MATCHER, not a single rewrite. Where rewriting transforms one term, PGL
// builds the matching INFRASTRUCTURE: many clauses compiled into ONE decision
// tree that selects the right action with minimal, shared tests.
// We use Maranget's pattern-match compilation (maximal sharing):
//   1. Collect clauses into a pattern MATRIX (one row per clause).
//   2. At each step, if the first row is all wildcards -> a leaf (that action).
//      Otherwise pick a column (here: column 0 — left-to-right, which is the
//      simple correct strategy; the heuristic is a refinement, not correctness)
//      and SWITCH on the constructors appearing in it. For each constructor,
//      SPECIALIZE the matrix (expand that column into the constructor's args)
//      and recurse; build a DEFAULT edge for the wildcard rows.
//   3. The result is a tree of TEST nodes (switch on node-kind/operator) ending
//      in ACTION leaves — exactly an instruction-selection / rewrite selector.
// AST shape of a pgen (from the parser):
//   Pgen[ name, (GenericParam)?, ArrayLit[binds...], WhereClause[ArrayLit[pat]],
//         action ]
// The `where [pattern]` array holds the match shape; an OR pattern (`a | b`)
// inside it becomes multiple rows. Lowercase idents in the pattern are holes.

module pgen;

import lexer;
import ast;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);

alias Node = ast::AstNode;
alias Nk = ast::NodeKind;
alias Tt = lexer::TokenType;

enum DtKind : int
{
    DT_FAIL,      // no clause matches
    DT_LEAF,      // a clause matched: take its action
    DT_SWITCH,    // test the current subject position's constructor
    DT_DROP,      // consume (pop) the current position unconditionally, recurse
    DT_GUARD      // a `where` condition that must hold (consults SSI later)
}

// A decision-tree node.
struct DtNode
{
    DtKind   kind;
    // DT_LEAF
    Node*    action;       // the pgen action to emit
    int      clause_id;    // which pgen clause this leaf came from
    // DT_SWITCH
    int      probe;        // which subject position (occurrence index) to test
    DtCase*  cases;        // constructor -> child subtree (linked list)
    DtNode*  default_edge; // wildcard fallthrough
    // DT_GUARD
    Node*    guard;        // condition expression
    DtNode*  on_true;
    DtNode*  on_false;
}

struct DtCase
{
    int      ctor_kind;    // NodeKind being matched
    int      ctor_op;      // operator (for binary/unary), else -1
    ulong    ctor_val;     // literal value (LitInt/LitBool), else 0
    bool     has_val;      // whether ctor_val is significant
    int      arity;        // number of sub-positions this ctor exposes
    DtNode*  child;
    DtCase*  next;
}

// Each row is one clause: a list of patterns (one per current "column"/position)
// plus the clause's action and id. Columns correspond to subject positions.
const usz PG_MAX_ROWS = 256;
const usz PG_MAX_COLS = 64;

struct PgRow
{
    Node*[PG_MAX_COLS] pats;   // pattern per column
    usz   ncols;
    Node* action;
    int   clause_id;
    bool  live;
}

struct PgMatrix
{
    PgRow[PG_MAX_ROWS] rows;
    usz   nrows;
}

const usz DT_POOL = 65536;

const usz MX_TRACK = 65536;   // max transient matrices tracked for bulk-free

struct PgenCompiler
{
    DtNode[DT_POOL]  dt_pool;
    usz     dt_count;
    DtCase[DT_POOL]  case_pool;
    usz     case_count;
    int     next_probe;
    bool    overflow;
    int     diag_count;
    // Every transient PgMatrix malloc'd during compilation is recorded here and
    // freed in one sweep when the compile finishes (no per-step leaks).
    void*[MX_TRACK] mx_track;
    usz     mx_count;
}

fn void PgenCompiler.init(PgenCompiler* c)
{
    c.dt_count = 0;
    c.case_count = 0;
    c.next_probe = 0;
    c.overflow = false;
    c.diag_count = 0;
    c.mx_count = 0;
}

// Allocate a transient matrix, tracked for bulk-free at end of compilation.
fn PgMatrix* PgenCompiler.alloc_matrix(PgenCompiler* c)
{
    PgMatrix* m = (PgMatrix*)malloc(PgMatrix::size);
    if (m == null) { c.overflow = true; return null; }
    if (c.mx_count < MX_TRACK)
    {
        c.mx_track[c.mx_count] = (void*)m;
        c.mx_count++;
    }
    m.nrows = 0;
    return m;
}

// Free every transient matrix allocated during compilation.
fn void PgenCompiler.free_matrices(PgenCompiler* c)
{
    for (usz i = 0; i < c.mx_count; i++)
    {
        if (c.mx_track[i] != null) free(c.mx_track[i]);
    }
    c.mx_count = 0;
}

fn DtNode* PgenCompiler.new_dt(PgenCompiler* c, DtKind k)
{
    if (c.dt_count >= DT_POOL) { c.overflow = true; return null; }
    DtNode* n = &c.dt_pool[c.dt_count];
    c.dt_count++;
    n.kind = k;
    n.action = null;
    n.clause_id = -1;
    n.probe = 0;
    n.cases = null;
    n.default_edge = null;
    n.guard = null;
    n.on_true = null;
    n.on_false = null;
    return n;
}

fn DtCase* PgenCompiler.new_case(PgenCompiler* c, int ctor_kind, int ctor_op, ulong ctor_val, bool has_val, int arity, DtNode* child)
{
    if (c.case_count >= DT_POOL) { c.overflow = true; return null; }
    DtCase* cs = &c.case_pool[c.case_count];
    c.case_count++;
    cs.ctor_kind = ctor_kind;
    cs.ctor_op = ctor_op;
    cs.ctor_val = ctor_val;
    cs.has_val = has_val;
    cs.arity = arity;
    cs.child = child;
    cs.next = null;
    return cs;
}

// A pattern is a "hole" (wildcard) if it's a lowercase ident or `_`.
fn bool pat_is_hole(Node* p)
{
    if (p == null) return true;
    if (p.kind != Nk.NODE_IDENT) return false;
    if (p.p.ident.name_len == 0) return true;
    char ch = p.p.ident.name_ptr[0];
    return (ch >= 'a' && ch <= 'z') || ch == '_';
}

// The constructor kind of a non-hole pattern.
fn int pat_ctor_kind(Node* p)
{
    if (p == null) return -1;
    return (int)p.kind;
}

fn int pat_ctor_op(Node* p)
{
    if (p == null) return -1;
    if (p.kind == Nk.NODE_EXPR_BINARY || p.kind == Nk.NODE_EXPR_UNARY) return (int)p.p.op.op;
    return -1;
}

fn int pat_arity(Node* p)
{
    if (p == null) return 0;
    return (int)p.child_count;
}

// A pattern carries a significant literal value (must match exactly).
fn bool pat_has_val(Node* p)
{
    if (p == null) return false;
    return p.kind == Nk.NODE_LIT_INT || p.kind == Nk.NODE_LIT_BOOL;
}

fn ulong pat_val(Node* p)
{
    if (p == null) return 0;
    if (p.kind == Nk.NODE_LIT_INT) return p.p.lit_int.int_val;
    if (p.kind == Nk.NODE_LIT_BOOL) return p.p.lit_bool.bool_val ? 1 : 0;
    return 0;
}

fn bool node_has_val(Node* n)
{
    if (n == null) return false;
    return n.kind == Nk.NODE_LIT_INT || n.kind == Nk.NODE_LIT_BOOL;
}

fn ulong node_val(Node* n)
{
    if (n == null) return 0;
    if (n.kind == Nk.NODE_LIT_INT) return n.p.lit_int.int_val;
    if (n.kind == Nk.NODE_LIT_BOOL) return n.p.lit_bool.bool_val ? 1 : 0;
    return 0;
}

// Compile a pattern matrix to a decision tree. Column 0 is the current probe.
fn DtNode* PgenCompiler.compile(PgenCompiler* c, PgMatrix* m, int depth)
{
    if (c.overflow || depth > 256) return c.new_dt(DtKind.DT_FAIL);

    // Find first live row.
    usz first = PG_MAX_ROWS;
    for (usz i = 0; i < m.nrows; i++)
    {
        if (m.rows[i].live) { first = i; break; }
    }
    if (first == PG_MAX_ROWS) return c.new_dt(DtKind.DT_FAIL);   // empty matrix

    // If the first live row has no columns left, it matches: a leaf.
    if (m.rows[first].ncols == 0)
    {
        DtNode* leaf = c.new_dt(DtKind.DT_LEAF);
        if (leaf == null) return null;
        leaf.action = m.rows[first].action;
        leaf.clause_id = m.rows[first].clause_id;
        return leaf;
    }

    // If column 0 is all holes across live rows, drop column 0 and recurse
    // (nothing to test here; the variable binds unconditionally).
    bool all_holes = true;
    for (usz i = 0; i < m.nrows; i++)
    {
        if (!m.rows[i].live) continue;
        if (!pat_is_hole(m.rows[i].pats[0])) { all_holes = false; break; }
    }
    if (all_holes)
    {
        // Column 0 is an unconditional binder for every row: emit a DROP node
        // so the subject walk pops the matching position, then recurse on the
        // rest. (Without this explicit step the subject stack desyncs.)
        DtNode* drop = c.new_dt(DtKind.DT_DROP);
        if (drop == null) return null;
        PgMatrix* sub = c.drop_col0(m);
        drop.default_edge = c.compile(sub, depth + 1);
        return drop;
    }

    // Otherwise SWITCH on column 0's constructors.
    DtNode* sw = c.new_dt(DtKind.DT_SWITCH);
    if (sw == null) return null;
    sw.probe = c.next_probe;

    // Collect the distinct constructors appearing in column 0.
    // For each, specialize the matrix and recurse.
    DtCase* head = null;
    DtCase* tail = null;

    for (usz i = 0; i < m.nrows; i++)
    {
        if (!m.rows[i].live) continue;
        Node* p = m.rows[i].pats[0];
        if (pat_is_hole(p)) continue;

        int ck = pat_ctor_kind(p);
        int co = pat_ctor_op(p);
        bool hv = pat_has_val(p);
        ulong cv = pat_val(p);

        // Skip if this constructor (kind+op+value) already has a case.
        bool seen = false;
        DtCase* it = head;
        while (it != null)
        {
            if (it.ctor_kind == ck && it.ctor_op == co
                && it.has_val == hv && it.ctor_val == cv) { seen = true; break; }
            it = it.next;
        }
        if (seen) continue;

        int ar = pat_arity(p);
        PgMatrix* spec = c.specialize(m, ck, co, hv, cv, ar);
        DtNode* child = c.compile(spec, depth + 1);
        DtCase* cs = c.new_case(ck, co, cv, hv, ar, child);
        if (cs == null) return null;
        if (head == null) { head = cs; tail = cs; }
        else { tail.next = cs; tail = cs; }
    }
    sw.cases = head;

    // The default edge: rows whose column 0 is a hole (match any constructor).
    PgMatrix* def = c.default_matrix(m);
    if (c.has_live(def))
    {
        sw.default_edge = c.compile(def, depth + 1);
    }
    else
    {
        sw.default_edge = c.new_dt(DtKind.DT_FAIL);
    }

    return sw;
}

fn bool PgenCompiler.has_live(PgenCompiler* c, PgMatrix* m)
{
    for (usz i = 0; i < m.nrows; i++) if (m.rows[i].live) return true;
    return false;
}

// These build NEW matrices in a scratch arena. We allocate them off the heap
// per call and the caller treats them as transient; the engine frees them when
// the whole compile finishes (we keep a free-list-free model: leak into the
// per-compile bump and free at end). For simplicity each is malloc'd and
// tracked for bulk-free.
const usz MX_POOL = 4096;

// Specialize: keep rows whose col0 is a hole (expanded with `arity` wildcards)
// or matches constructor (ck,co) (expanded with that pattern's children).
fn PgMatrix* PgenCompiler.specialize(PgenCompiler* c, PgMatrix* m, int ck, int co, bool hv, ulong cv, int arity)
{
    PgMatrix* out = c.alloc_matrix();
    if (out == null) { return m; }

    for (usz i = 0; i < m.nrows; i++)
    {
        if (!m.rows[i].live) continue;
        Node* p = m.rows[i].pats[0];

        if (pat_is_hole(p))
        {
            // Hole matches any constructor: expand with `arity` fresh holes.
            copy_row_specialized(&m.rows[i], out, null, arity, true);
        }
        else if (pat_ctor_kind(p) == ck && pat_ctor_op(p) == co
                 && pat_has_val(p) == hv && pat_val(p) == cv)
        {
            copy_row_specialized(&m.rows[i], out, p, arity, false);
        }
        // else: row dropped (different constructor or different literal value)
    }
    return out;
}

// Copy a row into `out`, replacing column 0 with either the matched pattern's
// children (when `is_hole`==false) or `arity` wildcard holes (when hole).
fn void copy_row_specialized(PgRow* src, PgMatrix* out, Node* matched, int arity, bool is_hole)
{
    if (out.nrows >= PG_MAX_ROWS) return;
    PgRow* dst = &out.rows[out.nrows];
    out.nrows++;
    dst.live = true;
    dst.action = src.action;
    dst.clause_id = src.clause_id;

    usz k = 0;
    // Expanded sub-columns from column 0.
    if (is_hole)
    {
        for (int a = 0; a < arity && k < PG_MAX_COLS; a++)
        {
            dst.pats[k] = null;   // null pattern == wildcard hole
            k++;
        }
    }
    else
    {
        for (usz a = 0; a < matched.child_count && k < PG_MAX_COLS; a++)
        {
            dst.pats[k] = matched.children[a];
            k++;
        }
    }
    // Remaining original columns (1..).
    for (usz col = 1; col < src.ncols && k < PG_MAX_COLS; col++)
    {
        dst.pats[k] = src.pats[col];
        k++;
    }
    dst.ncols = k;
}

// Default matrix: keep only rows whose col0 is a hole; drop column 0.
fn PgMatrix* PgenCompiler.default_matrix(PgenCompiler* c, PgMatrix* m)
{
    PgMatrix* out = c.alloc_matrix();
    if (out == null) { return m; }
    for (usz i = 0; i < m.nrows; i++)
    {
        if (!m.rows[i].live) continue;
        if (!pat_is_hole(m.rows[i].pats[0])) continue;
        PgRow* dst = &out.rows[out.nrows];
        out.nrows++;
        dst.live = true;
        dst.action = m.rows[i].action;
        dst.clause_id = m.rows[i].clause_id;
        usz k = 0;
        for (usz col = 1; col < m.rows[i].ncols && k < PG_MAX_COLS; col++)
        {
            dst.pats[k] = m.rows[i].pats[col];
            k++;
        }
        dst.ncols = k;
    }
    return out;
}

// Drop column 0 from every live row (used when col0 is all-holes).
fn PgMatrix* PgenCompiler.drop_col0(PgenCompiler* c, PgMatrix* m)
{
    PgMatrix* out = c.alloc_matrix();
    if (out == null) { return m; }
    for (usz i = 0; i < m.nrows; i++)
    {
        if (!m.rows[i].live) continue;
        PgRow* dst = &out.rows[out.nrows];
        out.nrows++;
        dst.live = true;
        dst.action = m.rows[i].action;
        dst.clause_id = m.rows[i].clause_id;
        usz k = 0;
        for (usz col = 1; col < m.rows[i].ncols && k < PG_MAX_COLS; col++)
        {
            dst.pats[k] = m.rows[i].pats[col];
            k++;
        }
        dst.ncols = k;
    }
    return out;
}

// Each Pgen contributes one (or more, via OR) rows: the `where` pattern(s).
fn void PgMatrix.init(PgMatrix* m)
{
    m.nrows = 0;
}

// Extract the match pattern node from a Pgen: the WhereClause's ArrayLit's
// single element (the shape to match).
fn Node* pgen_pattern(Node* pgen)
{
    for (usz i = 0; i < pgen.child_count; i++)
    {
        Node* c = pgen.children[i];
        if (c != null && c.kind == Nk.NODE_WHERE_CLAUSE && c.child_count >= 1)
        {
            Node* arr = c.children[0];
            if (arr != null && arr.child_count >= 1) return arr.children[0];
            return arr;
        }
    }
    return null;
}

// The action is the Pgen's last child.
fn Node* pgen_action(Node* pgen)
{
    if (pgen.child_count == 0) return null;
    return pgen.children[pgen.child_count - 1];
}

// Add a Pgen's clause(s) to the matrix. An OR pattern (`a | b`) at top level
// becomes multiple rows sharing the same action (clause id).
fn void PgMatrix.add_pgen(PgMatrix* m, Node* pgen, int clause_id)
{
    Node* pat = pgen_pattern(pgen);
    Node* action = pgen_action(pgen);
    if (pat == null) return;

    if (pat.kind == Nk.NODE_PATTERN_OR)
    {
        for (usz i = 0; i < pat.child_count; i++)
        {
            m.add_row(pat.children[i], action, clause_id);
        }
    }
    else
    {
        m.add_row(pat, action, clause_id);
    }
}

fn void PgMatrix.add_row(PgMatrix* m, Node* pat, Node* action, int clause_id)
{
    if (m.nrows >= PG_MAX_ROWS) return;
    PgRow* r = &m.rows[m.nrows];
    m.nrows++;
    r.pats[0] = pat;
    r.ncols = 1;
    r.action = action;
    r.clause_id = clause_id;
    r.live = true;
}

// Runs the decision tree against a subject term. Returns the matched action
// (a Pgen action node) or null. This is the executable form of the matcher —
// what backend instruction selection / rewrite selection calls.
// The tree was built treating column 0 as "the current position". We walk the
// subject structurally in lockstep: a SWITCH tests the subject's constructor,
// then descends into its children (which become the new leading columns).
struct SubjStack
{
    Node*[PG_MAX_COLS] items;
    usz count;
}

fn DtNode* run_tree(DtNode* root, Node* subject)
{
    SubjStack st;
    st.count = 0;
    st.items[0] = subject;
    st.count = 1;

    DtNode* cur = root;
    int guard = 0;
    while (cur != null && guard < 100000)
    {
        guard++;
        switch (cur.kind)
        {
            case DtKind.DT_FAIL:
                return null;
            case DtKind.DT_LEAF:
                return cur;
            case DtKind.DT_GUARD:
                // Guards are discharged elsewhere (SSI); assume true here.
                cur = cur.on_true;
            case DtKind.DT_DROP:
                // Consume the current position unconditionally (it bound a hole).
                if (st.count > 0) st.count--;
                cur = cur.default_edge;
            case DtKind.DT_SWITCH:
                if (st.count == 0) { cur = cur.default_edge; break; }
                // Pop the current position.
                Node* subj = st.items[st.count - 1];
                st.count--;
                int sk = subj != null ? (int)subj.kind : -1;
                int so = -1;
                if (subj != null && (subj.kind == Nk.NODE_EXPR_BINARY || subj.kind == Nk.NODE_EXPR_UNARY))
                {
                    so = (int)subj.p.op.op;
                }
                bool shv = node_has_val(subj);
                ulong sval = node_val(subj);
                // Find a matching case (kind + operator + literal value).
                DtCase* cs = cur.cases;
                DtNode* nextn = null;
                while (cs != null)
                {
                    if (cs.ctor_kind == sk && cs.ctor_op == so
                        && cs.has_val == shv && cs.ctor_val == sval)
                    {
                        // Push the subject's children as new positions (reverse
                        // order so the first child is on top).
                        if (subj != null)
                        {
                            for (usz a = 0; a < subj.child_count; a++)
                            {
                                usz idx = subj.child_count - 1 - a;
                                if (st.count < PG_MAX_COLS)
                                {
                                    st.items[st.count] = subj.children[idx];
                                    st.count++;
                                }
                            }
                        }
                        nextn = cs.child;
                        break;
                    }
                    cs = cs.next;
                }
                if (nextn != null) { cur = nextn; }
                else { cur = cur.default_edge; }
            default:
                return null;
        }
    }
    return null;
}

struct PgenSet
{
    PgenCompiler* comp;
    DtNode*       root;
    int           clause_count;
    bool          ok;
}

fn bool PgenSet.build(PgenSet* ps, Node* program)
{
    ps.comp = (PgenCompiler*)malloc(PgenCompiler::size);
    if (ps.comp == null) { ps.ok = false; return false; }
    ps.comp.init();

    PgMatrix* m = (PgMatrix*)malloc(PgMatrix::size);
    if (m == null) { ps.ok = false; return false; }
    m.init();

    int cid = 0;
    cid = collect_pgens(m, program, cid);
    ps.clause_count = cid;

    if (cid == 0)
    {
        ps.root = null;
        ps.ok = true;
        free(m);
        return true;
    }

    ps.root = ps.comp.compile(m, 0);
    ps.ok = !ps.comp.overflow;
    // Free every transient matrix built during compilation (decision-tree
    // nodes live in the compiler's pools, which persist until destroy()).
    ps.comp.free_matrices();
    free(m);
    return ps.ok;
}

fn void PgenSet.destroy(PgenSet* ps)
{
    if (ps.comp != null) free(ps.comp);
    ps.comp = null;
}

// Recursively collect every Pgen into the matrix.
fn int collect_pgens(PgMatrix* m, Node* n, int cid)
{
    if (n == null) return cid;
    if (n.kind == Nk.NODE_PGEN)
    {
        m.add_pgen(n, cid);
        return cid + 1;
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        cid = collect_pgens(m, n.children[i], cid);
    }
    return cid;
}

// Match a subject against the compiled pgen tree; returns the action or null.
fn Node* PgenSet.select(PgenSet* ps, Node* subject)
{
    if (ps.root == null) return null;
    DtNode* leaf = run_tree(ps.root, subject);
    if (leaf == null) return null;
    return leaf.action;
}

// Count decision-tree nodes (for stats / verification).
fn usz PgenSet.node_count(PgenSet* ps)
{
    return ps.comp != null ? ps.comp.dt_count : 0;
}
