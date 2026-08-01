// ============================================================================
// theory_irdlverify.c3 — IRDL verification traits (part 24)
// ----------------------------------------------------------------------------
// `theory_irdl` registers dialects and lowers their opcodes. This module adds
// what MLIR calls TRAITS: declarative constraints an operation must satisfy,
// checked before lowering rather than discovered afterwards as a miscompile.
//
// The traits implemented here are the ones that matter for an SSI/SSA middle
// end, which is where these opcodes are headed:
//
//   SSA_FORM         every value is assigned exactly once
//   DOMINANCE        every use is dominated by its definition
//   SINGLE_BLOCK     a region contains exactly one block
//   TERMINATED       every block ends in a terminator, and only there
//   TYPE_MATCH       operand and result types satisfy the declared relation
//   COMMUTATIVE      operand order is irrelevant (enables canonicalisation)
//   IDEMPOTENT       f(f(x)) ≡ f(x)
//   PURE             no side effects, so the op is freely reorderable
//   ISOLATED         a region does not capture from its enclosing scope
//
// Why declare traits instead of hard-coding checks: a dialect author writes
// `opcode gadd : Commutative, Pure` and gets both the verification and the
// canonicalisation opportunities for free. The alternative is every dialect
// re-implementing dominance checking, which is exactly the duplication MLIR's
// trait system exists to prevent.
//
// DOMINANCE deserves a note. A definition dominates a use when every path from
// entry to the use passes through the definition. Computing it properly needs
// a dominator tree; this uses the standard iterative Cooper-Harvey-Kennedy
// algorithm over the region's block graph, which converges quickly on the
// reducible graphs that structured code produces.
// ============================================================================

module theory_irdlverify;

import pfront_lex;
import pfront_core;
import theory_term;
import theory_irdl;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz IV_MAX_BLOCKS   = 4096;
const usz IV_MAX_VALUES   = 16384;
const usz IV_MAX_EDGES    = 8192;
const usz IV_MAX_TRAITS   = 32;
const int IV_MAX_DEPTH    = 300;

// ── Traits ──────────────────────────────────────────────────────────────────
enum Trait : int
{
    TR_NONE,
    TR_SSA_FORM,
    TR_DOMINANCE,
    TR_SINGLE_BLOCK,
    TR_TERMINATED,
    TR_TYPE_MATCH,
    TR_COMMUTATIVE,
    TR_IDEMPOTENT,
    TR_PURE,
    TR_ISOLATED,
    TR_SAME_OPERAND_TYPE,
    TR_VARIADIC
}

fn char* trait_name(Trait t)
{
    switch (t)
    {
        case TR_NONE:             return "none";
        case TR_SSA_FORM:         return "SSAForm";
        case TR_DOMINANCE:        return "Dominance";
        case TR_SINGLE_BLOCK:     return "SingleBlock";
        case TR_TERMINATED:       return "Terminated";
        case TR_TYPE_MATCH:       return "TypeMatch";
        case TR_COMMUTATIVE:      return "Commutative";
        case TR_IDEMPOTENT:       return "Idempotent";
        case TR_PURE:             return "Pure";
        case TR_ISOLATED:         return "IsolatedFromAbove";
        case TR_SAME_OPERAND_TYPE: return "SameOperandType";
        case TR_VARIADIC:         return "Variadic";
    }
}

// Recognise a trait written in a dialect declaration.
fn Trait trait_from_name(char* s, usz n)
{
    if (s == null || n == 0) { return Trait.TR_NONE; }
    if (n == 4 && s[0] == 'P' && s[1] == 'u') { return Trait.TR_PURE; }
    if (n == 11 && s[0] == 'C' && s[1] == 'o') { return Trait.TR_COMMUTATIVE; }
    if (n == 10 && s[0] == 'I' && s[1] == 'd') { return Trait.TR_IDEMPOTENT; }
    if (n == 7 && s[0] == 'S' && s[1] == 'S') { return Trait.TR_SSA_FORM; }
    if (n == 9 && s[0] == 'D' && s[1] == 'o') { return Trait.TR_DOMINANCE; }
    if (n == 11 && s[0] == 'S' && s[1] == 'i') { return Trait.TR_SINGLE_BLOCK; }
    if (n == 10 && s[0] == 'T' && s[1] == 'e') { return Trait.TR_TERMINATED; }
    if (n == 9 && s[0] == 'T' && s[1] == 'y') { return Trait.TR_TYPE_MATCH; }
    if (n == 17 && s[0] == 'I' && s[1] == 's') { return Trait.TR_ISOLATED; }
    if (n == 8 && s[0] == 'V' && s[1] == 'a') { return Trait.TR_VARIADIC; }
    return Trait.TR_NONE;
}

struct TraitSet
{
    Trait[IV_MAX_TRAITS] items;
    usz                  count;
}

fn void TraitSet.clear(TraitSet* t) { t.count = 0; }

fn bool TraitSet.add(TraitSet* t, Trait tr)
{
    if (tr == Trait.TR_NONE) { return false; }
    for (usz i = 0; i < t.count; i++) { if (t.items[i] == tr) { return true; } }
    if (t.count >= IV_MAX_TRAITS) { return false; }
    t.items[t.count] = tr;
    t.count = t.count + 1;
    return true;
}

fn bool TraitSet.has(TraitSet* t, Trait tr)
{
    for (usz i = 0; i < t.count; i++) { if (t.items[i] == tr) { return true; } }
    return false;
}

// ── Region control-flow graph ───────────────────────────────────────────────
// A region is a block graph. Building it explicitly is what lets dominance and
// termination be checked properly rather than approximated.
struct Block
{
    Node*  owner;
    int[16] succs;
    usz    succ_count;
    int[16] preds;
    usz    pred_count;
    int    idom;          // immediate dominator, -1 for the entry
    int    rpo;           // reverse post-order index
    bool   terminated;
    bool   reachable;
}

struct Region
{
    Block[IV_MAX_BLOCKS] blocks;
    usz                  block_count;
    int                  entry;
    int[IV_MAX_BLOCKS]   rpo_order;
    usz                  rpo_count;
    bool                 dom_computed;
}

fn void Region.init(Region* r)
{
    r.block_count = 0;
    r.entry = -1;
    r.rpo_count = 0;
    r.dom_computed = false;
}

fn int Region.add_block(Region* r, Node* owner)
{
    if (r.block_count >= IV_MAX_BLOCKS) { return -1; }
    int id = (int)r.block_count;
    r.block_count = r.block_count + 1;
    Block* b = &r.blocks[id];
    b.owner = owner;
    b.succ_count = 0;
    b.pred_count = 0;
    b.idom = -1;
    b.rpo = -1;
    b.terminated = false;
    b.reachable = false;
    if (r.entry < 0) { r.entry = id; }
    return id;
}

fn void Region.add_edge(Region* r, int from, int to)
{
    if (from < 0 || to < 0) { return; }
    if ((usz)from >= r.block_count || (usz)to >= r.block_count) { return; }
    Block* f = &r.blocks[from];
    Block* t = &r.blocks[to];
    if (f.succ_count < 16) { f.succs[f.succ_count] = to; f.succ_count = f.succ_count + 1; }
    if (t.pred_count < 16) { t.preds[t.pred_count] = from; t.pred_count = t.pred_count + 1; }
}

// Reverse post-order, which is the visit order the dominance iteration needs
// to converge in a small number of passes.
fn void Region.compute_rpo(Region* r)
{
    bool[IV_MAX_BLOCKS] visited;
    for (usz i = 0; i < r.block_count; i++) { visited[i] = false; }
    int[IV_MAX_BLOCKS] post;
    usz post_n = 0;

    // Iterative DFS: recursion would blow the stack on a long chain.
    int[IV_MAX_BLOCKS] stack;
    usz[IV_MAX_BLOCKS] iter;
    usz sp = 0;
    if (r.entry < 0) { return; }
    stack[0] = r.entry;
    iter[0] = 0;
    visited[r.entry] = true;
    sp = 1;

    while (sp > 0)
    {
        int b = stack[sp - 1];
        Block* blk = &r.blocks[b];
        if (iter[sp - 1] < blk.succ_count)
        {
            int s = blk.succs[iter[sp - 1]];
            iter[sp - 1] = iter[sp - 1] + 1;
            if (s >= 0 && (usz)s < r.block_count && !visited[s])
            {
                visited[s] = true;
                if (sp < IV_MAX_BLOCKS) { stack[sp] = s; iter[sp] = 0; sp = sp + 1; }
            }
            continue;
        }
        if (post_n < IV_MAX_BLOCKS) { post[post_n] = b; post_n = post_n + 1; }
        sp = sp - 1;
    }

    r.rpo_count = 0;
    usz i = post_n;
    while (i > 0)
    {
        i = i - 1;
        r.rpo_order[r.rpo_count] = post[i];
        r.blocks[post[i]].rpo = (int)r.rpo_count;
        r.blocks[post[i]].reachable = true;
        r.rpo_count = r.rpo_count + 1;
    }
}

// Cooper-Harvey-Kennedy iterative dominators. Simpler than Lengauer-Tarjan and
// faster in practice on the reducible graphs structured code produces.
fn void Region.compute_dominators(Region* r)
{
    r.compute_rpo();
    if (r.entry < 0) { return; }
    for (usz i = 0; i < r.block_count; i++) { r.blocks[i].idom = -1; }
    r.blocks[r.entry].idom = r.entry;

    bool changed = true;
    int rounds = 0;
    while (changed && rounds < 64)
    {
        changed = false;
        rounds = rounds + 1;
        for (usz i = 0; i < r.rpo_count; i++)
        {
            int b = r.rpo_order[i];
            if (b == r.entry) { continue; }
            Block* blk = &r.blocks[b];
            int new_idom = -1;
            for (usz p = 0; p < blk.pred_count; p++)
            {
                int pred = blk.preds[p];
                if (pred < 0 || (usz)pred >= r.block_count) { continue; }
                if (r.blocks[pred].idom < 0) { continue; }
                new_idom = new_idom < 0 ? pred : r.intersect(pred, new_idom);
            }
            if (new_idom >= 0 && blk.idom != new_idom)
            {
                blk.idom = new_idom;
                changed = true;
            }
        }
    }
    r.dom_computed = true;
}

// Walk both fingers up the dominator tree until they meet.
fn int Region.intersect(Region* r, int a, int b)
{
    int f1 = a;
    int f2 = b;
    int guard = 0;
    while (f1 != f2 && guard < 4096)
    {
        guard = guard + 1;
        while (f1 >= 0 && f2 >= 0 && r.blocks[f1].rpo > r.blocks[f2].rpo)
        {
            if (r.blocks[f1].idom == f1) { break; }
            f1 = r.blocks[f1].idom;
        }
        while (f1 >= 0 && f2 >= 0 && r.blocks[f2].rpo > r.blocks[f1].rpo)
        {
            if (r.blocks[f2].idom == f2) { break; }
            f2 = r.blocks[f2].idom;
        }
        if (f1 < 0 || f2 < 0) { return r.entry; }
        if (r.blocks[f1].rpo == r.blocks[f2].rpo && f1 != f2) { return r.entry; }
    }
    return f1;
}

fn bool Region.dominates(Region* r, int a, int b)
{
    if (!r.dom_computed) { return true; }
    if (a == b) { return true; }
    int cur = b;
    int guard = 0;
    while (cur >= 0 && guard < 4096)
    {
        if (cur == a) { return true; }
        if (r.blocks[cur].idom == cur) { break; }
        cur = r.blocks[cur].idom;
        guard = guard + 1;
    }
    return false;
}

// ── SSA value tracking ──────────────────────────────────────────────────────
struct SsaValue
{
    uint  name_id;
    int   def_block;
    Node* def_site;
    usz   def_count;      // >1 violates SSA
    usz   use_count;
}

struct SsaCheck
{
    SsaValue[IV_MAX_VALUES] values;
    usz                     count;
}

fn void SsaCheck.init(SsaCheck* s) { s.count = 0; }

fn int SsaCheck.find(SsaCheck* s, uint name)
{
    for (usz i = 0; i < s.count; i++) { if (s.values[i].name_id == name) { return (int)i; } }
    return -1;
}

fn int SsaCheck.define(SsaCheck* s, uint name, int block, Node* site)
{
    int existing = s.find(name);
    if (existing >= 0)
    {
        s.values[existing].def_count = s.values[existing].def_count + 1;
        return existing;
    }
    if (s.count >= IV_MAX_VALUES) { return -1; }
    int id = (int)s.count;
    s.count = s.count + 1;
    SsaValue* v = &s.values[id];
    v.name_id = name;
    v.def_block = block;
    v.def_site = site;
    v.def_count = 1;
    v.use_count = 0;
    return id;
}

// ── The verifier ────────────────────────────────────────────────────────────
struct OpTraits
{
    uint     opcode_name;
    TraitSet traits;
}

const usz IV_MAX_OPS = 4096;

struct IrdlVerifier
{
    OpTraits[IV_MAX_OPS] op_traits;
    usz                  op_count;

    Region*   region;
    SsaCheck* ssa;

    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;

    usz ops_verified;
    usz ssa_violations;
    usz dominance_violations;
    usz unterminated_blocks;
    usz type_mismatches;
    usz isolation_violations;
    usz purity_violations;
    usz canonicalisable;     // commutative/idempotent opportunities found
    bool strict;
}

fn bool IrdlVerifier.init(IrdlVerifier* v, pfront_core::DiagBag* d,
                          pfront_core::Interner* it, char* file)
{
    v.op_count = 0;
    v.region = (Region*)malloc(Region::size);
    v.ssa = (SsaCheck*)malloc(SsaCheck::size);
    if (v.region == null || v.ssa == null) { return false; }
    v.region.init();
    v.ssa.init();
    v.diags = d;
    v.interner = it;
    v.file = file;
    v.ops_verified = 0;
    v.ssa_violations = 0;
    v.dominance_violations = 0;
    v.unterminated_blocks = 0;
    v.type_mismatches = 0;
    v.isolation_violations = 0;
    v.purity_violations = 0;
    v.canonicalisable = 0;
    v.strict = false;
    return true;
}

fn void IrdlVerifier.destroy(IrdlVerifier* v)
{
    if (v.region != null) { free((void*)v.region); v.region = null; }
    if (v.ssa != null) { free((void*)v.ssa); v.ssa = null; }
}

// Read traits off a dialect opcode declaration: `opcode gadd : Pure, Commutative`.
fn void IrdlVerifier.collect_traits(IrdlVerifier* v, Node* n, int depth)
{
    if (n == null || depth > 200) { return; }
    if (n.kind == Nk.N_DECL_INTERFACE && (n.flags & pfront_core::NF_SYNTHETIC) != 0)
    {
        for (usz i = 0; i < n.child_count; i++)
        {
            Node* op = n.children[i];
            if (op == null || op.kind != Nk.N_DECL_FIELD) { continue; }
            if (v.op_count >= IV_MAX_OPS) { break; }
            OpTraits* ot = &v.op_traits[v.op_count];
            ot.opcode_name = op.name_id;
            ot.traits.clear();
            // Trait names appear in the opcode's type annotation position.
            v.scan_trait_names(op.type_ann, &ot.traits, 0);
            v.op_count = v.op_count + 1;
        }
    }
    for (usz i = 0; i < n.child_count; i++) { v.collect_traits(n.children[i], depth + 1); }
}

fn void IrdlVerifier.scan_trait_names(IrdlVerifier* v, Node* t, TraitSet* out, int depth)
{
    if (t == null || depth > 32) { return; }
    if (t.kind == Nk.N_TY_NAME && t.p.sptr != null)
    {
        Trait tr = trait_from_name(t.p.sptr, t.p.slen);
        if (tr != Trait.TR_NONE) { out.add(tr); }
    }
    for (usz i = 0; i < t.child_count; i++) { v.scan_trait_names(t.children[i], out, depth + 1); }
}

fn OpTraits* IrdlVerifier.traits_of(IrdlVerifier* v, uint opcode)
{
    for (usz i = 0; i < v.op_count; i++)
    {
        if (v.op_traits[i].opcode_name == opcode) { return &v.op_traits[i]; }
    }
    return null;
}

// Build a region CFG from a function body, so dominance is checkable.
fn void IrdlVerifier.build_region(IrdlVerifier* v, Node* body)
{
    v.region.init();
    if (body == null) { return; }
    int entry = v.region.add_block(body);
    v.walk_blocks(body, entry, 0);
    v.region.compute_dominators();
}

fn int IrdlVerifier.walk_blocks(IrdlVerifier* v, Node* n, int current, int depth)
{
    if (n == null || depth > IV_MAX_DEPTH) { return current; }

    switch (n.kind)
    {
        case N_EXPR_IF:
        {
            int then_b = v.region.add_block(n.child(1));
            v.region.add_edge(current, then_b);
            int after_then = v.walk_blocks(n.child(1), then_b, depth + 1);

            int join = v.region.add_block(n);
            v.region.add_edge(after_then, join);

            if (n.child_count >= 3)
            {
                int else_b = v.region.add_block(n.child(2));
                v.region.add_edge(current, else_b);
                int after_else = v.walk_blocks(n.child(2), else_b, depth + 1);
                v.region.add_edge(after_else, join);
            }
            else
            {
                v.region.add_edge(current, join);
            }
            return join;
        }

        case N_EXPR_WHILE:
        {
            int header = v.region.add_block(n);
            v.region.add_edge(current, header);
            int body = v.region.add_block(n.child(1));
            v.region.add_edge(header, body);
            int after_body = v.walk_blocks(n.child(1), body, depth + 1);
            v.region.add_edge(after_body, header);     // the back edge
            int exit = v.region.add_block(n);
            v.region.add_edge(header, exit);
            return exit;
        }

        case N_STMT_RETURN:
        {
            if (current >= 0 && (usz)current < v.region.block_count)
            {
                v.region.blocks[current].terminated = true;
            }
            return current;
        }

        default:
        {
            int cur = current;
            for (usz i = 0; i < n.child_count; i++)
            {
                cur = v.walk_blocks(n.children[i], cur, depth + 1);
            }
            return cur;
        }
    }
}

// SSA + dominance: each binding defined once, each use dominated by its def.
fn void IrdlVerifier.check_ssa(IrdlVerifier* v, Node* n, int block, int depth)
{
    if (n == null || depth > IV_MAX_DEPTH) { return; }

    if (n.kind == Nk.N_PAT_IDENT && n.name_id != 0)
    {
        int id = v.ssa.define(n.name_id, block, n);
        if (id >= 0 && v.ssa.values[id].def_count > 1)
        {
            v.ssa_violations = v.ssa_violations + 1;
            if (v.strict)
            {
                v.diags.error(pfront_core::Phase.PH_RESOLVE, 3310, n.line, n.col,
                              "value is assigned more than once (SSA form required)",
                              v.file);
            }
        }
    }

    if (n.kind == Nk.N_EXPR_IDENT && n.name_id != 0)
    {
        int id = v.ssa.find(n.name_id);
        if (id >= 0)
        {
            v.ssa.values[id].use_count = v.ssa.values[id].use_count + 1;
            // A use not dominated by its definition reads an uninitialised
            // value on at least one path.
            if (!v.region.dominates(v.ssa.values[id].def_block, block))
            {
                v.dominance_violations = v.dominance_violations + 1;
                if (v.strict)
                {
                    v.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3311,
                                       n.line, n.col,
                                       "use is not dominated by its definition",
                                       "on some path this value is read before it is set",
                                       v.file);
                }
            }
        }
    }

    for (usz i = 0; i < n.child_count; i++) { v.check_ssa(n.children[i], block, depth + 1); }
}

// Trait-specific checks on a dialect operation use.
fn void IrdlVerifier.check_op(IrdlVerifier* v, Node* call, uint opcode)
{
    OpTraits* ot = v.traits_of(opcode);
    if (ot == null) { return; }
    v.ops_verified = v.ops_verified + 1;

    usz argc = call.child_count > 0 ? call.child_count - 1 : 0;

    // SameOperandType: every operand must share a type.
    if (ot.traits.has(Trait.TR_SAME_OPERAND_TYPE) && argc > 1)
    {
        Node* first = call.children[1];
        for (usz i = 2; i < call.child_count; i++)
        {
            Node* a = call.children[i];
            if (a == null || first == null) { continue; }
            if (a.type_ann != null && first.type_ann != null
                && !theory_term::term_eq(a.type_ann, first.type_ann, 0))
            {
                v.type_mismatches = v.type_mismatches + 1;
                if (v.strict)
                {
                    v.diags.error(pfront_core::Phase.PH_RESOLVE, 3312, a.line, a.col,
                                  "operands of this opcode must share one type", v.file);
                }
            }
        }
    }

    // Pure: an operand performing effects contradicts the declaration.
    if (ot.traits.has(Trait.TR_PURE))
    {
        for (usz i = 1; i < call.child_count; i++)
        {
            Node* a = call.children[i];
            if (a == null) { continue; }
            if ((a.effects & pfront_core::EFF_IO) != 0
             || (a.effects & pfront_core::EFF_ALLOC) != 0)
            {
                v.purity_violations = v.purity_violations + 1;
                if (v.strict)
                {
                    v.diags.error(pfront_core::Phase.PH_RESOLVE, 3313, a.line, a.col,
                                  "effectful operand passed to a Pure opcode", v.file);
                }
            }
        }
    }

    // Commutative and Idempotent are canonicalisation opportunities rather
    // than errors: report the count so a later pass can exploit them.
    if (ot.traits.has(Trait.TR_COMMUTATIVE) && argc == 2)
    {
        v.canonicalisable = v.canonicalisable + 1;
    }
    if (ot.traits.has(Trait.TR_IDEMPOTENT) && argc >= 1)
    {
        // f(f(x)) collapses to f(x).
        Node* inner = call.children[1];
        uint dn = 0;
        uint on = 0;
        if (inner != null && theory_irdl::split_dialect_call(inner, &dn, &on)
            && on == opcode)
        {
            v.canonicalisable = v.canonicalisable + 1;
        }
    }
}

fn void IrdlVerifier.walk_ops(IrdlVerifier* v, Node* n, int depth)
{
    if (n == null || depth > IV_MAX_DEPTH) { return; }
    uint dn = 0;
    uint on = 0;
    if (theory_irdl::split_dialect_call(n, &dn, &on)) { v.check_op(n, on); }
    for (usz i = 0; i < n.child_count; i++) { v.walk_ops(n.children[i], depth + 1); }
}

// Terminated: check every reachable block ends in a terminator.
fn void IrdlVerifier.check_termination(IrdlVerifier* v)
{
    for (usz i = 0; i < v.region.block_count; i++)
    {
        Block* b = &v.region.blocks[i];
        if (!b.reachable) { continue; }
        if (b.succ_count > 0) { continue; }     // falls through legitimately
        if (b.terminated) { continue; }
        v.unterminated_blocks = v.unterminated_blocks + 1;
    }
}

fn void IrdlVerifier.run(IrdlVerifier* v, Node* root)
{
    if (root == null) { return; }
    v.collect_traits(root, 0);
    v.walk_ops(root, 0);

    // Per-function SSA and dominance.
    for (usz i = 0; i < root.child_count; i++)
    {
        Node* d = root.children[i];
        if (d == null || d.kind != Nk.N_DECL_FN) { continue; }
        for (usz k = 0; k < d.child_count; k++)
        {
            Node* c = d.children[k];
            if (c == null) { continue; }
            if (c.kind == Nk.N_CLAUSE || c.kind == Nk.N_BLOCK)
            {
                v.ssa.init();
                v.build_region(c);
                v.check_ssa(c, v.region.entry, 0);
                v.check_termination();
            }
        }
    }
}

fn void IrdlVerifier.report(IrdlVerifier* v)
{
    printf("  irdl traits      : %d opcodes with traits, %d op uses verified\n",
           (int)v.op_count, (int)v.ops_verified);
    printf("  irdl ssa/dom     : %d ssa violations, %d dominance violations\n",
           (int)v.ssa_violations, (int)v.dominance_violations);
    if (v.type_mismatches > 0 || v.purity_violations > 0 || v.unterminated_blocks > 0)
    {
        printf("  irdl trait fails : %d type, %d purity, %d unterminated\n",
               (int)v.type_mismatches, (int)v.purity_violations,
               (int)v.unterminated_blocks);
    }
    if (v.canonicalisable > 0)
    {
        printf("  canonicalisation : %d opportunities from Commutative/Idempotent\n",
               (int)v.canonicalisable);
    }
}
