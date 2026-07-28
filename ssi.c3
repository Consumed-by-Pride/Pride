// ssi.c3 — Static Single Information (the better-than-SSA form)
// Implementation language: C3 (host). First component of the MSP stage.
// SSA gives each variable ONE definition. SSI (Ananian) additionally SPLITS a
// variable wherever the program *learns something new* about it — i.e. at branch
// conditions — via σ-nodes, in addition to the φ-merges SSA already has. That
// strictly-more information is what later MSP passes (rewrite guards, UB
// exploitation, PGL `where` conditions) consult.
// The parser already plants σ (NODE_SIGMA) and φ (NODE_PHI) MARKERS:
//   if   : [cond, σ(cond), then, (else)?, φ]
//   match: [scrutinee, σ(scrutinee), arm*, φ]
// This pass turns those markers into a real DEF-USE GRAPH with REFINEMENTS:
//   - every binder (let / param / loop var) gets version 0,
//   - each assignment creates a new version (SSA renaming),
//   - a σ on `x < 0.0` refines x to `∩(<0.0)` on the true edge and `∩(≥0.0)`
//     on the false edge,
//   - every resolved Ident *use* is mapped to the SsiVar version it reads,
//     carrying the active refinement at that point.
// Pride has no `goto`; control flow is tree-structured, so construction is a
// single O(n) walk — no dominance-frontier iteration.

module ssi;

import lexer;
import ast;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);

alias Node = ast::AstNode;
alias Nk = ast::NodeKind;
alias Tt = lexer::TokenType;

// A single value-version of a variable.
// How a version came to exist. This is what makes the form a real SSI graph
// rather than just an annotated AST: every version is one of these kinds.
enum SsiKind : int
{
    SSI_DEF,     // an original definition (let / parameter / loop binder v0)
    SSI_ASSIGN,  // produced by an assignment  x = e   (plain SSA renaming)
    SSI_SIGMA,   // a σ-split on a branch edge, carrying a flow refinement
    SSI_PHI      // a φ-merge at a control-flow join, with incoming operands
}

const usz MAX_PHI_OPERANDS = 16;

struct SsiVar
{
    SsiKind  kind;         // how this version was produced
    Node*    binder;       // the PatIdent declaration this is a version of
    Node*    refinement;   // a NODE_TYPE_REFINEMENT (or null): the extra fact
    int      version;      // 0 = definition, +1 per assignment / split / merge
    Node*    def_site;     // node that created this version (let/assign/σ/φ)
    SsiVar*  parent;       // version this was split or merged from

    // φ operands: the incoming versions from each predecessor edge. Each slot i
    // pairs a version (operands[i]) with the edge it arrives on (op_edge[i]:
    // 0 = then/true/fallthrough, 1 = else/false, 2 = loop back-edge, ...).
    SsiVar*[MAX_PHI_OPERANDS] operands;
    int[MAX_PHI_OPERANDS]     op_edge;
    usz      operand_count;
}

// A recorded use:  an Ident node reads a particular SsiVar version.
struct SsiUse
{
    Node*    use_node;     // the NODE_IDENT use
    SsiVar*  ver;          // the version it reads
}

const usz MAX_SSI_VARS = 65536;
const usz MAX_SSI_USES = 262144;
const usz ENV_CAP      = 4096;

// One env entry: a binder mapped to its currently-active version.
struct EnvEntry
{
    Node*    binder;
    SsiVar*  ver;
}

struct SsiDiag { char* msg; int line; int col; }

// The SSI graph plus the construction environment (a scoped binder→version map).
struct SsiGraph
{
    // Arena-style flat pools (heap-allocated; freed in destroy()).
    SsiVar*  vars;
    usz      var_count;
    SsiUse*  uses;
    usz      use_count;

    // Construction environment: a stack of {binder, current-version} entries.
    // Scopes save/restore by remembering the length; a branch overrides an
    // entry then restores the previous one.
    EnvEntry[ENV_CAP] env;
    usz      env_count;

    ast::AstArena* arena;   // for synthesizing refinement type nodes

    SsiDiag[256] diags;
    int      diag_count;
    bool     overflow;

    int      walk_depth;    // recursion guard against deeply-nested trees
}

// Cap on SSI construction recursion depth (degrade gracefully, never overflow).
const int SSI_MAX_DEPTH = 1200;

fn bool SsiGraph.init(SsiGraph* g, ast::AstArena* arena)
{
    g.vars = (SsiVar*)malloc(MAX_SSI_VARS * SsiVar::size);
    if (g.vars == null) return false;
    g.uses = (SsiUse*)malloc(MAX_SSI_USES * SsiUse::size);
    if (g.uses == null) { free(g.vars); g.vars = null; return false; }

    g.var_count = 0;
    g.use_count = 0;
    g.env_count = 0;
    g.arena = arena;
    g.diag_count = 0;
    g.overflow = false;
    g.walk_depth = 0;
    return true;
}

fn void SsiGraph.destroy(SsiGraph* g)
{
    if (g.vars != null) free(g.vars);
    if (g.uses != null) free(g.uses);
    g.vars = null;
    g.uses = null;
}

fn void SsiGraph.diag(SsiGraph* g, char* msg, int line, int col)
{
    if (g.diag_count < 256)
    {
        SsiDiag d;
        d.msg = msg;
        d.line = line;
        d.col = col;
        g.diags[g.diag_count] = d;
        g.diag_count++;
    }
}

fn SsiVar* SsiGraph.new_var_k(SsiGraph* g, SsiKind kind, Node* binder, Node* refinement, int version, Node* def_site, SsiVar* parent)
{
    if (g.var_count >= MAX_SSI_VARS) { g.overflow = true; return null; }
    SsiVar* v = &g.vars[g.var_count];
    g.var_count++;
    v.kind = kind;
    v.binder = binder;
    v.refinement = refinement;
    v.version = version;
    v.def_site = def_site;
    v.parent = parent;
    v.operand_count = 0;
    return v;
}

// Back-compat shim: callers that pass no explicit kind classify by context.
fn SsiVar* SsiGraph.new_var(SsiGraph* g, Node* binder, Node* refinement, int version, Node* def_site, SsiVar* parent)
{
    // Refinement present => a σ-split; version 0 with no parent => a definition;
    // otherwise an assignment-style rename.
    SsiKind k = SSI_ASSIGN;
    if (refinement != null) { k = SSI_SIGMA; }
    else if (parent == null && version == 0) { k = SSI_DEF; }
    return g.new_var_k(k, binder, refinement, version, def_site, parent);
}

// Create a φ-merge version for `binder` at a join, merging the incoming
// versions. The merged refinement is the JOIN (union) of the incoming
// refinements (a value here is "whatever any predecessor could provide").
fn SsiVar* SsiGraph.new_phi(SsiGraph* g, Node* binder, Node* def_site, SsiVar* a, int edge_a, SsiVar* b, int edge_b)
{
    int base = 0;
    if (a != null && a.version > base) base = a.version;
    if (b != null && b.version > base) base = b.version;
    SsiVar* phi = g.new_var_k(SSI_PHI, binder, null, base + 1, def_site, a);
    if (phi == null) return null;
    phi.refinement = g.join_refinement(a, b);
    g.phi_add_operand(phi, a, edge_a);
    g.phi_add_operand(phi, b, edge_b);
    return phi;
}

fn void SsiGraph.phi_add_operand(SsiGraph* g, SsiVar* phi, SsiVar* operand, int edge)
{
    if (phi == null) return;
    if (phi.operand_count >= MAX_PHI_OPERANDS) return;
    phi.operands[phi.operand_count] = operand;
    phi.op_edge[phi.operand_count] = edge;
    phi.operand_count++;
}

// The join of two refinements. If both edges carry the SAME refinement it is
// preserved; otherwise the merge knows nothing more than the base type (null),
// which is the sound union in the value-set lattice.
fn Node* SsiGraph.join_refinement(SsiGraph* g, SsiVar* a, SsiVar* b)
{
    Node* ra = a != null ? a.refinement : null;
    Node* rb = b != null ? b.refinement : null;
    if (ra == null || rb == null) return null;
    if (refinement_eq(ra, rb)) return ra;
    return null;
}

// Structural equality of two refinement nodes (op + identical bound literal).
fn bool refinement_eq(Node* a, Node* b)
{
    if (a == b) return true;
    if (a == null || b == null) return false;
    if (a.kind != b.kind) return false;
    if (a.p.op.op != b.p.op.op) return false;
    if (a.child_count != b.child_count) return false;
    for (usz i = 0; i < a.child_count; i++)
    {
        Node* ca = a.children[i];
        Node* cb = b.children[i];
        if (ca == cb) continue;
        if (ca == null || cb == null) return false;
        if (ca.kind != cb.kind) return false;
        if (ca.kind == Nk.NODE_LIT_INT && ca.p.lit_int.int_val != cb.p.lit_int.int_val) return false;
    }
    return true;
}

fn void SsiGraph.record_use(SsiGraph* g, Node* use_node, SsiVar* ver)
{
    if (ver == null) return;
    if (g.use_count >= MAX_SSI_USES) { g.overflow = true; return; }
    SsiUse* u = &g.uses[g.use_count];
    g.use_count++;
    u.use_node = use_node;
    u.ver = ver;
}

// Public query (used by later MSP passes): which version does this use read?
// Access version `i` from the pool (for tooling / backend iteration).
fn SsiVar* SsiGraph.var_at(SsiGraph* g, usz i)
{
    if (i >= g.var_count) return null;
    return &g.vars[i];
}

// Human-readable name of a version's kind.
fn char* ssi_kind_name(SsiKind k)
{
    switch (k)
    {
        case SSI_DEF:    return "def";
        case SSI_ASSIGN: return "assign";
        case SSI_SIGMA:  return "sigma";
        case SSI_PHI:    return "phi";
        default:         return "?";
    }
}

fn SsiVar* SsiGraph.var_for_use(SsiGraph* g, Node* use_node)
{
    for (usz i = 0; i < g.use_count; i++)
    {
        if (g.uses[i].use_node == use_node) return g.uses[i].ver;
    }
    return null;
}

// The active refinement on a use (or null) — the headline SSI query.
fn Node* SsiGraph.refinement_of(SsiGraph* g, Node* use_node)
{
    SsiVar* v = g.var_for_use(use_node);
    return v != null ? v.refinement : null;
}

fn usz SsiGraph.env_mark(SsiGraph* g)
{
    return g.env_count;
}

fn void SsiGraph.env_reset(SsiGraph* g, usz mark)
{
    g.env_count = mark;
}

// Collapse the env back to `mark` but PRESERVE assignments to outer binders
// (those already bound below `mark`). A `let` introduced inside the scope is
// dropped (it's local); an assignment to an outer variable persists as a new
// override at the parent level. This is what lets a block's reassignments flow
// out to the enclosing if/loop merge logic.
fn void SsiGraph.env_close_block(SsiGraph* g, usz mark)
{
    // Collect, for each binder bound ABOVE mark, its top-most version — but
    // only if that binder ALSO exists below mark (i.e. it's an outer binder).
    usz n_above = g.env_count;
    // First, snapshot the outer overrides we must carry out.
    Node*[256]   carry_b;
    SsiVar*[256] carry_v;
    usz carry = 0;

    usz i = g.env_count;
    while (i > mark)
    {
        i--;
        Node* b = g.env[i].binder;
        SsiVar* v = g.env[i].ver;
        // Already carried? (top-most wins)
        bool seen = false;
        for (usz j = 0; j < carry; j++) { if (carry_b[j] == b) { seen = true; break; } }
        if (seen) continue;
        // Is it an outer binder (bound below mark)?
        bool outer = false;
        for (usz k = 0; k < mark; k++) { if (g.env[k].binder == b) { outer = true; break; } }
        if (outer && carry < 256)
        {
            carry_b[carry] = b;
            carry_v[carry] = v;
            carry++;
        }
    }

    // Drop the scope, then re-apply the carried outer overrides.
    g.env_count = mark;
    for (usz j = 0; j < carry; j++)
    {
        g.env_push(carry_b[j], carry_v[j]);
    }
}

fn SsiVar* SsiGraph.env_lookup(SsiGraph* g, Node* binder)
{
    if (binder == null) return null;
    // Search from the top so the most recent (innermost) binding wins.
    usz i = g.env_count;
    while (i > 0)
    {
        i--;
        if (g.env[i].binder == binder) return g.env[i].ver;
    }
    return null;
}

fn void SsiGraph.env_push(SsiGraph* g, Node* binder, SsiVar* ver)
{
    if (g.env_count >= ENV_CAP) { g.overflow = true; return; }
    g.env[g.env_count].binder = binder;
    g.env[g.env_count].ver = ver;
    g.env_count++;
}

// Override an existing binder's active version, returning the previous version
// so the caller can restore it after a branch.
fn SsiVar* SsiGraph.env_override(SsiGraph* g, Node* binder, SsiVar* ver)
{
    SsiVar* prev = g.env_lookup(binder);
    g.env_push(binder, ver);
    return prev;
}

// A refinement is a NODE_TYPE_REFINEMENT carrying a comparison op and a bound
// expression (reusing the type node the typechecker already understands).
fn Node* SsiGraph.mk_refinement(SsiGraph* g, Tt op, Node* bound, int line, int col)
{
    Node*[1] buf;
    buf[0] = bound;
    return ast::node_op(g.arena, Nk.NODE_TYPE_REFINEMENT, op, &buf[0], 1, line, col);
}

// The boolean negation of a comparison operator (for the false edge).
fn Tt negate_cmp(Tt op)
{
    switch (op)
    {
        case Tt.TOKEN_LT:      return Tt.TOKEN_GTEQ;
        case Tt.TOKEN_GT:      return Tt.TOKEN_LTEQ;
        case Tt.TOKEN_LTEQ:    return Tt.TOKEN_GT;
        case Tt.TOKEN_GTEQ:    return Tt.TOKEN_LT;
        case Tt.TOKEN_EQEQ:    return Tt.TOKEN_NEQ;
        case Tt.TOKEN_NEQ:     return Tt.TOKEN_EQEQ;
        case Tt.TOKEN_LEQ_UNI: return Tt.TOKEN_GT;
        case Tt.TOKEN_GEQ_UNI: return Tt.TOKEN_LT;
        case Tt.TOKEN_NEQ_UNI: return Tt.TOKEN_EQEQ;
        default:               return Tt.TOKEN_INVALID;
    }
}

fn bool is_cmp_op(Tt op)
{
    switch (op)
    {
        case Tt.TOKEN_LT:
        case Tt.TOKEN_GT:
        case Tt.TOKEN_LTEQ:
        case Tt.TOKEN_GTEQ:
        case Tt.TOKEN_EQEQ:
        case Tt.TOKEN_NEQ:
        case Tt.TOKEN_LEQ_UNI:
        case Tt.TOKEN_GEQ_UNI:
        case Tt.TOKEN_NEQ_UNI:
            return true;
        default:
            return false;
    }
}

// From a condition, extract (refined-binder, true-edge-op, bound) when the
// condition has the shape  `ident <cmp> expr`. Returns the binder or null.
struct CondFact { Node* binder; Tt op; Node* bound; bool ok; }

fn CondFact analyze_condition(Node* cond)
{
    CondFact f;
    f.binder = null;
    f.op = Tt.TOKEN_INVALID;
    f.bound = null;
    f.ok = false;

    if (cond == null) return f;
    if (cond.kind != Nk.NODE_EXPR_BINARY) return f;
    if (!is_cmp_op(cond.p.op.op)) return f;
    if (cond.child_count < 2) return f;

    Node* lhs = cond.children[0];
    Node* rhs = cond.children[1];

    // `ident <cmp> bound`
    if (lhs != null && lhs.kind == Nk.NODE_IDENT && lhs.resolved != null)
    {
        f.binder = lhs.resolved;
        f.op = cond.p.op.op;
        f.bound = rhs;
        f.ok = true;
        return f;
    }
    // `bound <cmp> ident`  (flip the operator)
    if (rhs != null && rhs.kind == Nk.NODE_IDENT && rhs.resolved != null)
    {
        f.binder = rhs.resolved;
        f.op = flip_cmp(cond.p.op.op);
        f.bound = lhs;
        f.ok = true;
        return f;
    }
    return f;
}

// Flip a comparison when operands are swapped:  (bound < x)  ⇔  (x > bound).
fn Tt flip_cmp(Tt op)
{
    switch (op)
    {
        case Tt.TOKEN_LT:      return Tt.TOKEN_GT;
        case Tt.TOKEN_GT:      return Tt.TOKEN_LT;
        case Tt.TOKEN_LTEQ:    return Tt.TOKEN_GTEQ;
        case Tt.TOKEN_GTEQ:    return Tt.TOKEN_LTEQ;
        default:               return op;   // == != are symmetric
    }
}

// A single condition can imply MULTIPLE refinements per edge:
//   if a < 10 && b > 0   ⟹  TRUE edge:  a<10  AND  b>0
//   if flag              ⟹  TRUE edge:  flag==true ;  FALSE edge: flag==false
//   if !flag             ⟹  TRUE edge:  flag==false; FALSE edge: flag==true
//   if a || b            ⟹  FALSE edge: a==false AND b==false  (De Morgan)
// `collect_facts` gathers, for a given polarity (true = the taken edge holds),
// every (binder, op, bound) fact the condition implies on that edge.
const usz MAX_EDGE_FACTS = 16;

struct EdgeFact { Node* binder; Tt op; Node* bound; }
struct FactSet  { EdgeFact[MAX_EDGE_FACTS] facts; usz count; }

fn void FactSet.add(FactSet* fs, Node* binder, Tt op, Node* bound)
{
    if (binder == null) return;
    if (fs.count >= MAX_EDGE_FACTS) return;
    fs.facts[fs.count].binder = binder;
    fs.facts[fs.count].op = op;
    fs.facts[fs.count].bound = bound;
    fs.count++;
}

// Recursively collect the refinements `cond` implies when its value equals
// `polarity` (true = condition holds on this edge). For boolean-variable facts
// the bound is left null with op EQEQ (meaning `binder == polarity`); the flag
// `bool_polarity` records which truth value, and a caller with an arena
// synthesizes the literal. This pure form is shared by the SSI tree builder and
// the CFG flattener.
// `arena` may be null (then boolean facts carry a null bound literal — the
// SSI-tree caller passes a real arena so bool facts get a `true`/`false` node).
fn void collect_facts_pure(ast::AstArena* arena, Node* cond, bool polarity, FactSet* out)
{
    if (cond == null) return;
    if (out.count >= MAX_EDGE_FACTS) return;

    // negation: !e / ¬e  flips the polarity
    if (cond.kind == Nk.NODE_EXPR_UNARY
        && (cond.p.op.op == Tt.TOKEN_BANG || cond.p.op.op == Tt.TOKEN_NEGATION || cond.p.op.op == Tt.TOKEN_KW_NOT)
        && cond.child_count >= 1)
    {
        collect_facts_pure(arena, cond.children[0], !polarity, out);
        return;
    }

    if (cond.kind == Nk.NODE_EXPR_BINARY && cond.child_count >= 2)
    {
        Tt op = cond.p.op.op;
        // conjunction: on the TRUE edge BOTH sides hold; on the FALSE edge we
        // learn nothing precise (one side could be false) → no facts.
        if (op == Tt.TOKEN_AMPAMP || op == Tt.TOKEN_KW_AND)
        {
            if (polarity)
            {
                collect_facts_pure(arena, cond.children[0], true, out);
                collect_facts_pure(arena, cond.children[1], true, out);
            }
            return;
        }
        // disjunction: on the FALSE edge BOTH sides are false (De Morgan); on
        // the TRUE edge we learn nothing precise → no facts.
        if (op == Tt.TOKEN_PIPEPIPE || op == Tt.TOKEN_KW_OR)
        {
            if (!polarity)
            {
                collect_facts_pure(arena, cond.children[0], false, out);
                collect_facts_pure(arena, cond.children[1], false, out);
            }
            return;
        }
        // comparison: emit the (possibly negated) fact
        if (is_cmp_op(op))
        {
            CondFact cf = analyze_condition(cond);
            if (cf.ok)
            {
                Tt eff = polarity ? cf.op : negate_cmp(cf.op);
                if (eff != Tt.TOKEN_INVALID) out.add(cf.binder, eff, cf.bound);
            }
            return;
        }
        return;
    }

    // bare boolean variable:  if flag  ⟹  flag == (polarity)
    if (cond.kind == Nk.NODE_IDENT && cond.resolved != null)
    {
        Node* lit = arena != null ? ast::node_bool(arena, polarity, cond.line, cond.col) : null;
        out.add(cond.resolved, Tt.TOKEN_EQEQ, lit);
        return;
    }
}

// Method form used by the SSI-tree builder (has an arena for bool literals).
fn void SsiGraph.collect_facts(SsiGraph* g, Node* cond, bool polarity, FactSet* out)
{
    collect_facts_pure(g.arena, cond, polarity, out);
}

fn void SsiGraph.build(SsiGraph* g, Node* program)
{
    if (program == null) return;
    g.walk(program);
}

fn void SsiGraph.walk(SsiGraph* g, Node* n)
{
    if (n == null) return;
    if (g.overflow) return;
    if (g.walk_depth > SSI_MAX_DEPTH) { g.overflow = true; return; }
    g.walk_depth++;
    g.walk_body(n);
    g.walk_depth--;
}

fn void SsiGraph.walk_body(SsiGraph* g, Node* n)
{
    switch (n.kind)
    {
        case Nk.NODE_DECL_FN:
            g.walk_fn(n);

        case Nk.NODE_DECL_LET:
        case Nk.NODE_DECL_MUT:
        case Nk.NODE_DECL_CONST:
        case Nk.NODE_DECL_STATIC:
            g.walk_let(n);

        case Nk.NODE_EXPR_ASSIGN:
            g.walk_assign(n);

        case Nk.NODE_IDENT:
            // A resolved use reads the binder's current version.
            if (n.resolved != null)
            {
                SsiVar* v = g.env_lookup(n.resolved);
                if (v != null) g.record_use(n, v);
            }

        case Nk.NODE_EXPR_IF:
            g.walk_if(n);

        case Nk.NODE_EXPR_MATCH:
            g.walk_match(n);

        case Nk.NODE_EXPR_WHILE:
            g.walk_while(n);

        case Nk.NODE_EXPR_FOR:
            g.walk_for(n);

        case Nk.NODE_EXPR_BLOCK:
            // A block is a scope: local `let`s are dropped on exit, but
            // assignments to OUTER variables flow out (so if/loop merges see
            // them). env_close_block carries the outer overrides past `mark`.
            usz mark = g.env_mark();
            for (usz i = 0; i < n.child_count; i++) g.walk(n.children[i]);
            g.env_close_block(mark);

        // MSP / metaprogramming bodies are untyped & not flow-analyzed here.
        case Nk.NODE_REWRITE:
        case Nk.NODE_REWRITE_RULE:
        case Nk.NODE_PGEN:
        case Nk.NODE_QUOTE:
        case Nk.NODE_SIGIL_TREE:
        case Nk.NODE_SIGIL_DATA:
        case Nk.NODE_SIGIL_BYTES:
        case Nk.NODE_IRDL:
        case Nk.NODE_DIALECT:
            break;

        default:
            for (usz i = 0; i < n.child_count; i++) g.walk(n.children[i]);
    }
}

// A function: bind its clause parameters as version-0, then walk clause bodies.
fn void SsiGraph.walk_fn(SsiGraph* g, Node* fn_node)
{
    for (usz i = 0; i < fn_node.child_count; i++)
    {
        Node* c = fn_node.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_EXPR_BLOCK)
        {
            for (usz j = 0; j < c.child_count; j++)
            {
                Node* clause = c.children[j];
                if (clause != null && clause.kind == Nk.NODE_CLAUSE)
                {
                    g.walk_clause(clause);
                }
            }
        }
    }
}

fn void SsiGraph.walk_clause(SsiGraph* g, Node* clause)
{
    usz mark = g.env_mark();

    // First child is the parameter pattern; bind its binders as version 0.
    if (clause.child_count >= 1)
    {
        g.bind_pattern_v0(clause.children[0]);
    }
    // Remaining children: guard(s) + body.
    for (usz i = 1; i < clause.child_count; i++)
    {
        g.walk(clause.children[i]);
    }

    g.env_reset(mark);
}

// Create version-0 SsiVars for every binder a pattern introduces.
fn void SsiGraph.bind_pattern_v0(SsiGraph* g, Node* pat)
{
    if (pat == null) return;
    switch (pat.kind)
    {
        case Nk.NODE_PATTERN_IDENT:
            // The binder *is* this PatIdent node (uses resolve to it).
            SsiVar* v0 = g.new_var(pat, null, 0, pat, null);
            g.env_push(pat, v0);

        case Nk.NODE_PATTERN_TUPLE:
        case Nk.NODE_PATTERN_OR:
            for (usz i = 0; i < pat.child_count; i++) g.bind_pattern_v0(pat.children[i]);

        case Nk.NODE_PATTERN_STRUCT:
            for (usz i = 0; i < pat.child_count; i++)
            {
                Node* fld = pat.children[i];
                if (fld == null || fld.kind != Nk.NODE_PATTERN_FIELD) continue;
                // { name : subpattern } binds whatever the subpattern introduces;
                // { name } shorthand: the resolver binds uses to the PatField
                // node itself, so version that node.
                if (fld.child_count >= 2)
                {
                    g.bind_pattern_v0(fld.children[1]);
                }
                else
                {
                    SsiVar* fv = g.new_var(fld, null, 0, fld, null);
                    g.env_push(fld, fv);
                }
            }

        default:
            for (usz i = 0; i < pat.child_count; i++) g.bind_pattern_v0(pat.children[i]);
    }
}

// let/const/static: walk the initializer, then bind the pattern as version 0.
fn void SsiGraph.walk_let(SsiGraph* g, Node* d)
{
    // The initializer must be walked BEFORE the binder is in scope, so
    // `let x = x` reads the outer x.
    for (usz i = 1; i < d.child_count; i++)
    {
        Node* c = d.children[i];
        if (c != null && !is_type_or_row(c)) g.walk(c);
    }
    if (d.child_count >= 1) g.bind_pattern_v0(d.children[0]);
}

fn bool is_type_or_row(Node* n)
{
    if (n == null) return true;
    switch (n.kind)
    {
        case Nk.NODE_TYPE_PRIMITIVE:
        case Nk.NODE_TYPE_PATH:
        case Nk.NODE_TYPE_PTR:
        case Nk.NODE_TYPE_REF:
        case Nk.NODE_TYPE_MUT_REF:
        case Nk.NODE_TYPE_ARRAY:
        case Nk.NODE_TYPE_SLICE:
        case Nk.NODE_TYPE_TUPLE:
        case Nk.NODE_TYPE_FN:
        case Nk.NODE_TYPE_UNION:
        case Nk.NODE_TYPE_INTERSECT:
        case Nk.NODE_TYPE_NEGATION:
        case Nk.NODE_TYPE_BOTTOM:
        case Nk.NODE_TYPE_FORALL:
        case Nk.NODE_TYPE_EXISTS:
        case Nk.NODE_TYPE_GENERIC_APP:
        case Nk.NODE_TYPE_REFINEMENT:
        case Nk.NODE_TYPE_TENSOR:
        case Nk.NODE_EFFECT_ROW:
            return true;
        default:
            return false;
    }
}

// assignment  x = rhs : walk rhs (reads current version), then create a new
// version for the assigned binder (SSA renaming).
fn void SsiGraph.walk_assign(SsiGraph* g, Node* n)
{
    Node* lhs = n.child_count >= 1 ? n.children[0] : null;
    Node* rhs = n.child_count >= 2 ? n.children[1] : null;

    if (rhs != null) g.walk(rhs);

    // Only a bare `ident = ...` renames a tracked variable. (Field/index writes
    // don't create a new whole-variable version in this model.)
    if (lhs != null && lhs.kind == Nk.NODE_IDENT && lhs.resolved != null)
    {
        SsiVar* prev = g.env_lookup(lhs.resolved);
        int nextv = prev != null ? prev.version + 1 : 0;
        SsiVar* nv = g.new_var(lhs.resolved, null, nextv, n, prev);
        g.env_override(lhs.resolved, nv);
    }
    else if (lhs != null)
    {
        g.walk(lhs);   // field/index lvalue: still record its uses
    }
}

// if [cond, σ, then, (else)?, φ] : refine the condition variable on each edge.
// A captured per-binder version assignment from one branch.
const usz MAX_BRANCH_MODS = 1024;

struct BranchSnap
{
    Node*[MAX_BRANCH_MODS]   binders;
    SsiVar*[MAX_BRANCH_MODS] vers;
    usz count;
}

fn void SsiGraph.walk_if(SsiGraph* g, Node* n)
{
    if (n.child_count < 1) return;

    Node* cond = n.children[0];
    g.walk(cond);   // the condition reads current versions

    // Identify the then-branch and an optional else-branch (skip σ/φ markers).
    Node* then_b = null;
    Node* else_b = null;
    for (usz i = 1; i < n.child_count; i++)
    {
        Node* c = n.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_SIGMA || c.kind == Nk.NODE_PHI) continue;
        if (then_b == null) { then_b = c; }
        else { else_b = c; }
    }

    Node* site = n.child_count >= 2 ? n.children[1] : n;

    // Apply EVERY σ-refinement the condition implies on this edge (a condition
    // like `a < 10 && flag` yields two facts), walk the branch, capture the
    // versions of every binder it reassigned, then restore the environment.
    usz mark = g.env_mark();
    FactSet tf;
    tf.count = 0;
    g.collect_facts(cond, true, &tf);
    g.apply_facts(&tf, cond, site);
    if (then_b != null) g.walk(then_b);
    BranchSnap then_snap;
    g.capture_mods(mark, &then_snap);
    g.env_reset(mark);

    BranchSnap else_snap;
    else_snap.count = 0;
    if (else_b != null)
    {
        usz mark2 = g.env_mark();
        FactSet ff;
        ff.count = 0;
        g.collect_facts(cond, false, &ff);
        g.apply_facts(&ff, cond, n);
        g.walk(else_b);
        g.capture_mods(mark2, &else_snap);
        g.env_reset(mark2);
    }

    // For every binder reassigned on EITHER edge, create a φ that merges the
    // value coming from the then-edge (its branch version, or its pre-branch
    // version if the then-branch didn't touch it) with the value from the
    // else-edge (likewise). This is the real SSI join — φ-nodes with operands.
    g.merge_branches(n, &then_snap, &else_snap);
}

// Install one σ-version per fact, chaining so multiple facts on the same binder
// refine progressively. Each σ's `parent` is the binder's prior active version,
// giving step-2 SASI extraction the dominating-σ chain to crawl.
fn void SsiGraph.apply_facts(SsiGraph* g, FactSet* fs, Node* cond, Node* site)
{
    for (usz i = 0; i < fs.count; i++)
    {
        EdgeFact* ef = &fs.facts[i];
        if (ef.binder == null) continue;
        SsiVar* cur = g.env_lookup(ef.binder);
        Node* ref = g.mk_refinement(ef.op, ef.bound, cond.line, cond.col);
        SsiVar* refined = g.new_var_k(SSI_SIGMA, ef.binder, ref,
            cur != null ? cur.version : 0, site, cur);
        g.env_override(ef.binder, refined);
    }
}

// Record every binder whose current env version differs from the version that
// was active at `mark` (i.e. binders the branch reassigned). The branch's
// overrides live above `mark` in the env stack.
fn void SsiGraph.capture_mods(SsiGraph* g, usz mark, BranchSnap* snap)
{
    snap.count = 0;
    // Walk the env entries pushed during the branch (indices >= mark). The
    // top-most entry for a binder is its branch-final version.
    usz i = g.env_count;
    while (i > mark)
    {
        i--;
        Node* b = g.env[i].binder;
        SsiVar* v = g.env[i].ver;
        // Only record the first (top-most) occurrence per binder.
        bool seen = false;
        for (usz j = 0; j < snap.count; j++)
        {
            if (snap.binders[j] == b) { seen = true; break; }
        }
        if (seen) continue;
        // Ignore σ-refinement versions (flow facts) — only real reassignments
        // (SSI_ASSIGN) and binders introduced then mutated count as branch
        // modifications worth merging.
        if (v != null && v.kind == SSI_SIGMA) continue;
        if (snap.count < MAX_BRANCH_MODS)
        {
            snap.binders[snap.count] = b;
            snap.vers[snap.count] = v;
            snap.count++;
        }
    }
}

// Build φ-nodes for binders modified on either edge, installing the merged
// version into the post-if environment.
fn void SsiGraph.merge_branches(SsiGraph* g, Node* site, BranchSnap* then_snap, BranchSnap* else_snap)
{
    // Union of binders touched by either branch.
    for (usz i = 0; i < then_snap.count; i++)
    {
        Node* b = then_snap.binders[i];
        if (!is_outer_binder(g, b)) continue;   // branch-local: nothing to merge
        SsiVar* then_v = then_snap.vers[i];
        SsiVar* else_v = find_snap(else_snap, b);
        SsiVar* pre = g.env_lookup(b);           // pre-branch version (fallthrough)
        if (else_v == null) else_v = pre;
        SsiVar* phi = g.new_phi(b, site, then_v, 0, else_v, 1);
        if (phi != null) g.env_override(b, phi);
    }
    // Binders modified only on the else edge.
    for (usz i = 0; i < else_snap.count; i++)
    {
        Node* b = else_snap.binders[i];
        if (!is_outer_binder(g, b)) continue;
        if (find_snap(then_snap, b) != null) continue;   // already merged above
        SsiVar* else_v = else_snap.vers[i];
        SsiVar* pre = g.env_lookup(b);
        SsiVar* phi = g.new_phi(b, site, pre, 0, else_v, 1);
        if (phi != null) g.env_override(b, phi);
    }
}

fn SsiVar* find_snap(BranchSnap* snap, Node* binder)
{
    for (usz i = 0; i < snap.count; i++)
    {
        if (snap.binders[i] == binder) return snap.vers[i];
    }
    return null;
}

// A binder is "outer" (visible after the if) if it already has a version in the
// current environment — i.e. it was declared before the branch. Binders first
// declared inside a branch are branch-local and don't escape.
fn bool is_outer_binder(SsiGraph* g, Node* binder)
{
    return g.env_lookup(binder) != null;
}

// match [scrutinee, σ, arms.., φ] : each arm scopes its own pattern binders;
// a literal/null arm refines the scrutinee variable inside that arm.
fn void SsiGraph.walk_match(SsiGraph* g, Node* n)
{
    if (n.child_count < 1) return;
    Node* scrut = n.children[0];
    g.walk(scrut);

    // An N-way φ: accumulate, across all arms, the versions each arm produces
    // for outer binders it reassigns. After all arms, one φ per binder merges
    // every arm's contribution (plus the pre-match version as the implicit
    // fallthrough for arms that didn't touch it).
    BranchSnap merged;
    merged.count = 0;

    int arm_edge = 0;
    for (usz i = 1; i < n.child_count; i++)
    {
        Node* arm = n.children[i];
        if (arm == null || arm.kind != Nk.NODE_MATCH_ARM) continue;

        usz mark = g.env_mark();
        if (arm.child_count >= 1) g.bind_pattern_v0(arm.children[0]);
        for (usz j = 1; j < arm.child_count; j++) g.walk(arm.children[j]);

        BranchSnap arm_snap;
        g.capture_mods(mark, &arm_snap);
        g.env_reset(mark);

        // Fold this arm's outer-binder reassignments into the merge accumulator.
        for (usz k = 0; k < arm_snap.count; k++)
        {
            Node* b = arm_snap.binders[k];
            if (!is_outer_binder(g, b)) continue;
            g.accumulate_phi(n, &merged, b, arm_snap.vers[k], arm_edge);
        }
        arm_edge++;
    }

    // Install the accumulated φ-versions into the post-match environment.
    for (usz i = 0; i < merged.count; i++)
    {
        if (merged.vers[i] != null) g.env_override(merged.binders[i], merged.vers[i]);
    }
}

// Add `ver` (from edge `edge`) as a φ operand for `binder`, creating the φ on
// first sighting and extending it on subsequent arms.
fn void SsiGraph.accumulate_phi(SsiGraph* g, Node* site, BranchSnap* merged, Node* binder, SsiVar* ver, int edge)
{
    for (usz i = 0; i < merged.count; i++)
    {
        if (merged.binders[i] == binder)
        {
            SsiVar* phi = merged.vers[i];
            if (phi != null && phi.kind == SSI_PHI)
            {
                g.phi_add_operand(phi, ver, edge);
                phi.refinement = g.join_refinement_node(phi.refinement, ver);
            }
            return;
        }
    }
    // First arm to touch this binder: start a φ merging the pre-match version
    // (edge -1 = fallthrough) with this arm's version.
    SsiVar* pre = g.env_lookup(binder);
    SsiVar* phi = g.new_phi(binder, site, pre, -1, ver, edge);
    if (merged.count < MAX_BRANCH_MODS)
    {
        merged.binders[merged.count] = binder;
        merged.vers[merged.count] = phi;
        merged.count++;
    }
}

// Join an existing refinement node with another version's refinement.
fn Node* SsiGraph.join_refinement_node(SsiGraph* g, Node* existing, SsiVar* v)
{
    Node* other = v != null ? v.refinement : null;
    if (existing == null || other == null) return null;
    if (refinement_eq(existing, other)) return existing;
    return null;
}

// while [cond, body] : the parser does not plant σ/φ for while, so we walk
// conservatively — the condition and body read current versions; any
// assignments in the body are scoped to the loop walk.
// while [cond, body]. A loop-carried variable (reassigned in the body) needs a
// LOOP φ at the header merging its pre-loop version (entry edge) with the value
// from the previous iteration (back-edge). We model this in one pass:
//   1. note the pre-loop versions,
//   2. walk cond + body, capturing the back-edge versions of modified binders,
//   3. create a header φ(entry, back-edge) for each and install it after the
//      loop (the post-loop value is the φ — it could be entry or any iteration).
fn void SsiGraph.walk_while(SsiGraph* g, Node* n)
{
    Node* cond = n.child_count >= 1 ? n.children[0] : null;
    if (cond != null) g.walk(cond);                   // condition reads entry versions
    if (n.child_count >= 2)
    {
        usz mark = g.env_mark();
        // The loop body executes only when the guard held: refine accordingly,
        // so uses inside the body see the guard's σ facts (e.g. `i < n` ⟹ i<n).
        FactSet tf;
        tf.count = 0;
        if (cond != null) g.collect_facts(cond, true, &tf);
        g.apply_facts(&tf, cond != null ? cond : n, n);
        g.walk(n.children[1]);                         // body
        BranchSnap body_snap;
        g.capture_mods(mark, &body_snap);
        g.env_reset(mark);
        g.merge_loop(n, &body_snap);
    }
}

// Install loop-header φ-nodes: for each binder the body reassigned, merge its
// pre-loop (entry) version with the back-edge version on edge 2.
fn void SsiGraph.merge_loop(SsiGraph* g, Node* site, BranchSnap* body_snap)
{
    for (usz i = 0; i < body_snap.count; i++)
    {
        Node* b = body_snap.binders[i];
        if (!is_outer_binder(g, b)) continue;        // body-local: doesn't escape
        SsiVar* entry = g.env_lookup(b);             // pre-loop version
        SsiVar* back = body_snap.vers[i];            // last value in the body
        SsiVar* phi = g.new_phi(b, site, entry, 0, back, 2);   // edge 2 = back-edge
        if (phi != null) g.env_override(b, phi);
    }
}

// for [binder, iter, body] : iterable first, then the loop binder is version 0
// inside the body.
fn void SsiGraph.walk_for(SsiGraph* g, Node* n)
{
    if (n.child_count >= 2) g.walk(n.children[1]);   // iterable (entry versions)

    usz mark = g.env_mark();
    if (n.child_count >= 1) g.bind_pattern_v0(n.children[0]);   // loop binder (fresh each iter)
    if (n.child_count >= 3) g.walk(n.children[2]);              // body
    BranchSnap body_snap;
    g.capture_mods(mark, &body_snap);
    g.env_reset(mark);
    g.merge_loop(n, &body_snap);   // loop-header φ for body-modified outer vars
}
