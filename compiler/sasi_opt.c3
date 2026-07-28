// ============================================================================
// sasi_opt.c3 — SASI-driven optimization on the clean SSA CFG (pipeline step 4)
// ----------------------------------------------------------------------------
// Implementation language: C3 (host).
//
// After step 2 (`sasi.c3`) the CFG is clean SSA (σ stripped to a sparse fact
// map). This pass USES that map to delete redundant work:
//
//   1. REDUNDANT-COMPARISON FOLDING. A comparison `v = a <cmp> k` whose truth is
//      already implied by a SASI fact on `a` (crawling the dominating-σ chain)
//      is replaced by a constant bool. E.g. inside `if n>0 { if n>0 ... }` the
//      inner `n>0` is statically true.
//
//   2. BRANCH FOLDING. A `cbr cond` whose `cond` is now a constant bool becomes
//      an unconditional `br` to the taken successor; the untaken edge is removed
//      (predecessor lists + φ operands fixed up).
//
//   3. UNREACHABLE PRUNING. Blocks that lose all predecessors (and aren't the
//      entry) become TERM_UNREACHABLE, their out-edges removed, φ operands of
//      successors dropped — iterated to a fixpoint.
//
//   4. DEAD-CODE ELIMINATION. Pure instructions (and φ) with no remaining users
//      are removed from their block lists.
//
// All edits preserve the SSA-CFG invariants `ssi_ir::verify()` checks
// (succ/pred symmetry, φ operand/predecessor agreement), re-verified after.
//
// The reasoning core is a SOUND integer-implication checker over constant
// bounds: given a known fact `a fop fk` it decides whether `a qop qk` must be
// true, must be false, or is unknown. Only decidable cases fire; everything else
// is left untouched (conservative — never changes program meaning).
// ============================================================================

module sasi_opt;

import lexer;
import ast;
import ssi_ir;
import sasi;

extern fn int printf(char* fmt, ...);

alias Node = ast::AstNode;
alias Nk = ast::NodeKind;
alias Tt = lexer::TokenType;
alias IrVal = ssi_ir::IrVal;
alias IrBlock = ssi_ir::IrBlock;
alias IrOp = ssi_ir::IrOp;
alias TermKind = ssi_ir::TermKind;
alias SsiModule = ssi_ir::SsiModule;
alias SasiMap = sasi::SasiMap;
alias SasiFact = sasi::SasiFact;

const int OPT_FIXPOINT_ROUNDS = 64;   // outer fixpoint cap

struct OptStats
{
    int compares_folded;   // redundant comparisons → const bool
    int branches_folded;   // cbr → br
    int blocks_pruned;     // blocks made unreachable
    int edges_removed;     // CFG edges deleted
    int dead_removed;      // dead instructions/φ removed
    int rounds;            // fixpoint rounds run
}

struct Optimizer
{
    SsiModule* mod;
    SasiMap*   sasi;
    OptStats   st;
}

fn void Optimizer.init(Optimizer* o, SsiModule* mod, SasiMap* sasi)
{
    o.mod = mod;
    o.sasi = sasi;
    o.st.compares_folded = 0;
    o.st.branches_folded = 0;
    o.st.blocks_pruned = 0;
    o.st.edges_removed = 0;
    o.st.dead_removed = 0;
    o.st.rounds = 0;
}

// ── Decidable integer-implication core ───────────────────────────────────────
// A "decision": does a known fact decide a query comparison?
enum Decision : int { D_UNKNOWN, D_TRUE, D_FALSE }

// Canonical comparison kinds (after folding the unicode variants).
enum Cmp : int { C_LT, C_LE, C_GT, C_GE, C_EQ, C_NE, C_NONE }

fn Cmp to_cmp(Tt op)
{
    switch (op)
    {
        case Tt.TOKEN_LT:      return Cmp.C_LT;
        case Tt.TOKEN_LTEQ:    return Cmp.C_LE;
        case Tt.TOKEN_LEQ_UNI: return Cmp.C_LE;
        case Tt.TOKEN_GT:      return Cmp.C_GT;
        case Tt.TOKEN_GTEQ:    return Cmp.C_GE;
        case Tt.TOKEN_GEQ_UNI: return Cmp.C_GE;
        case Tt.TOKEN_EQEQ:    return Cmp.C_EQ;
        case Tt.TOKEN_NEQ:     return Cmp.C_NE;
        case Tt.TOKEN_NEQ_UNI: return Cmp.C_NE;
        default:               return Cmp.C_NONE;
    }
}

// Does `a <fc> fk` (known fact, true) imply `a <qc> qk`?  All over signed ints.
// Returns D_TRUE / D_FALSE / D_UNKNOWN. Sound: only returns a decision when the
// fact's solution set is entirely inside (TRUE) or entirely outside (FALSE) the
// query's solution set.
fn Decision implies(Cmp fc, long fk, Cmp qc, long qk)
{
    if (fc == Cmp.C_NONE || qc == Cmp.C_NONE) return Decision.D_UNKNOWN;

    // Normalize the fact to an interval [lo, hi] over the integers (inclusive).
    // Use sentinels for ±∞.
    long lo_inf = -9223372036854775807L - 1L;   // LONG_MIN
    long hi_inf = 9223372036854775807L;          // LONG_MAX
    long lo = lo_inf;
    long hi = hi_inf;
    bool exact_ne = false;   // fact is `a != fk` (set complement of a point)

    // Guard the interval arithmetic against overflow at the extremes.
    if (fc == Cmp.C_LT && fk == lo_inf) return Decision.D_UNKNOWN;
    if (fc == Cmp.C_GT && fk == hi_inf) return Decision.D_UNKNOWN;

    switch (fc)
    {
        case Cmp.C_LT: hi = fk - 1;
        case Cmp.C_LE: hi = fk;
        case Cmp.C_GT: lo = fk + 1;
        case Cmp.C_GE: lo = fk;
        case Cmp.C_EQ: lo = fk; hi = fk;
        case Cmp.C_NE: exact_ne = true;
        default: return Decision.D_UNKNOWN;
    }

    if (exact_ne)
    {
        // Only a query of the same point is decidable from `a != fk`.
        if (qc == Cmp.C_EQ && qk == fk) return Decision.D_FALSE;
        if (qc == Cmp.C_NE && qk == fk) return Decision.D_TRUE;
        return Decision.D_UNKNOWN;
    }

    // Evaluate the query as true for ALL x in [lo,hi] (→ D_TRUE) or
    // false for ALL x in [lo,hi] (→ D_FALSE); else unknown.
    bool all_true = query_all(lo, hi, qc, qk, true);
    bool all_false = query_all(lo, hi, qc, qk, false);
    if (all_true) return Decision.D_TRUE;
    if (all_false) return Decision.D_FALSE;
    return Decision.D_UNKNOWN;
}

// Is `x <qc> qk` == `want` for EVERY x in [lo,hi]?
fn bool query_all(long lo, long hi, Cmp qc, long qk, bool want)
{
    if (lo > hi) return true;   // empty interval: vacuously
    switch (qc)
    {
        case Cmp.C_LT:
            // x < qk true for all  ⟺ hi < qk ;  false for all ⟺ lo >= qk
            if (want) return hi < qk;
            return lo >= qk;
        case Cmp.C_LE:
            if (want) return hi <= qk;
            return lo > qk;
        case Cmp.C_GT:
            if (want) return lo > qk;
            return hi <= qk;
        case Cmp.C_GE:
            if (want) return lo >= qk;
            return hi < qk;
        case Cmp.C_EQ:
            // all equal ⟺ lo==hi==qk ; all non-equal ⟺ qk outside [lo,hi]
            if (want) return lo == qk && hi == qk;
            return qk < lo || qk > hi;
        case Cmp.C_NE:
            if (want) return qk < lo || qk > hi;
            return lo == qk && hi == qk;
        default:
            return false;
    }
}

// ── Extract a constant integer from a value / refinement-bound node ───────────
fn bool const_int_of_val(IrVal* v, long* out)
{
    if (v == null) return false;
    if (v.op == IrOp.IR_CONST_INT) { *out = (long)v.ival; return true; }
    return false;
}

fn bool const_int_of_node(Node* n, long* out)
{
    if (n == null) return false;
    if (n.kind == Nk.NODE_LIT_INT) { *out = (long)n.p.lit_int.int_val; return true; }
    return false;
}

// A refinement node `a <op> bound`: extract (cmp, const-bound) when the bound is
// an integer literal. Bool refinements (flag==true) are handled separately.
fn bool fact_as_int_cmp(SasiFact* f, Cmp* cmp_out, long* k_out)
{
    if (f == null || f.refinement == null) return false;
    Cmp c = to_cmp(f.refinement.p.op.op);
    if (c == Cmp.C_NONE) return false;
    if (f.refinement.child_count < 1) return false;
    long k;
    if (!const_int_of_node(f.refinement.children[0], &k)) return false;
    *cmp_out = c;
    *k_out = k;
    return true;
}

// ── The query: is comparison value `cmpv` (a = IR_BIN cmp) decided by SASI? ───
// `cmpv` has args[0]=lhs, args[1]=rhs. We look for a SASI fact on lhs (or its
// chain) of the form `lhs <fc> fk`, with rhs a constant qk, and ask `implies`.
// Returns D_TRUE / D_FALSE / D_UNKNOWN.
fn Decision Optimizer.decide_compare(Optimizer* o, IrVal* cmpv)
{
    if (cmpv == null || cmpv.op != IrOp.IR_BIN || cmpv.arg_count < 2) return Decision.D_UNKNOWN;
    Cmp qc = to_cmp(cmpv.bop);
    if (qc == Cmp.C_NONE) return Decision.D_UNKNOWN;

    IrVal* lhs = cmpv.args[0];
    IrVal* rhs = cmpv.args[1];

    // query bound must be a constant int
    long qk;
    if (!const_int_of_val(rhs, &qk)) return Decision.D_UNKNOWN;

    // Walk the dominating-σ chain on lhs: each fact may decide the query.
    SasiFact* f = o.sasi.fact_of(lhs);
    int guard = 0;
    while (f != null)
    {
        Cmp fc;
        long fk;
        if (fact_as_int_cmp(f, &fc, &fk))
        {
            Decision d = implies(fc, fk, qc, qk);
            if (d != Decision.D_UNKNOWN) return d;
        }
        f = f.parent;
        guard++;
        if (guard > 100000) break;
    }
    return Decision.D_UNKNOWN;
}

// A refinement node `a == true/false`: extract the boolean fact value, if the
// refinement is an equality against a bool literal.
fn bool fact_as_bool(SasiFact* f, bool* out)
{
    if (f == null || f.refinement == null) return false;
    if (to_cmp(f.refinement.p.op.op) != Cmp.C_EQ) return false;
    if (f.refinement.child_count < 1) return false;
    Node* b = f.refinement.children[0];
    if (b == null || b.kind != Nk.NODE_LIT_BOOL) return false;
    *out = b.p.lit_bool.bool_val;
    return true;
}

// Decide whether a VALUE used as a boolean (e.g. a `cbr` condition) is
// statically true/false. Handles: a comparison value (via decide_compare); a
// constant bool; and a σ-handle whose SASI fact pins it to a bool (`if flag`
// inside `if flag`). Returns D_TRUE / D_FALSE / D_UNKNOWN.
fn Decision Optimizer.decide_value(Optimizer* o, IrVal* v)
{
    if (v == null) return Decision.D_UNKNOWN;
    if (v.op == IrOp.IR_CONST_BOOL) return v.bval ? Decision.D_TRUE : Decision.D_FALSE;
    if (v.op == IrOp.IR_BIN && to_cmp(v.bop) != Cmp.C_NONE) return o.decide_compare(v);

    // Bare boolean σ-handle: crawl the dominating-σ chain for a bool fact.
    SasiFact* f = o.sasi.fact_of(v);
    int guard = 0;
    while (f != null)
    {
        bool bv;
        if (fact_as_bool(f, &bv)) return bv ? Decision.D_TRUE : Decision.D_FALSE;
        f = f.parent;
        guard++;
        if (guard > 100000) break;
    }
    return Decision.D_UNKNOWN;
}

// ── Pass 1+2: fold redundant comparisons, then fold the branches they feed ───
fn void Optimizer.fold_compares(Optimizer* o)
{
    SsiModule* m = o.mod;
    for (usz bi = 0; bi < m.block_count; bi++)
    {
        IrBlock* b = &m.blocks[bi];
        IrVal* in = b.head;
        while (in != null)
        {
            if (in.op == IrOp.IR_BIN && to_cmp(in.bop) != Cmp.C_NONE)
            {
                Decision d = o.decide_compare(in);
                if (d == Decision.D_TRUE)
                {
                    in.op = IrOp.IR_CONST_BOOL;
                    in.bval = true;
                    in.arg_count = 0;
                    o.st.compares_folded++;
                }
                else if (d == Decision.D_FALSE)
                {
                    in.op = IrOp.IR_CONST_BOOL;
                    in.bval = false;
                    in.arg_count = 0;
                    o.st.compares_folded++;
                }
            }
            in = in.next;
        }
    }
}

// Constant-fold an IR_BIN with two constant-int operands into a constant value
// (int result for arithmetic/bitwise, bool result for comparisons). Signedness-
// correct: signed division/shift/comparison when the source op was signed. This
// catches arithmetic exposed after comparison folding + DCE. Returns true if
// folded.
fn bool Optimizer.fold_const_bin(Optimizer* o, IrVal* v)
{
    if (v == null || v.op != IrOp.IR_BIN || v.arg_count < 2) return false;
    IrVal* a = v.args[0];
    IrVal* b = v.args[1];
    if (a == null || b == null) return false;
    if (a.op != IrOp.IR_CONST_INT || b.op != IrOp.IR_CONST_INT) return false;

    ulong x = a.ival;
    ulong y = b.ival;
    long sx = (long)x;
    long sy = (long)y;
    Cmp c = to_cmp(v.bop);

    // comparison → bool constant
    if (c != Cmp.C_NONE)
    {
        bool res;
        switch (c)
        {
            case Cmp.C_LT: res = sx < sy;
            case Cmp.C_LE: res = sx <= sy;
            case Cmp.C_GT: res = sx > sy;
            case Cmp.C_GE: res = sx >= sy;
            case Cmp.C_EQ: res = x == y;
            case Cmp.C_NE: res = x != y;
            default: return false;
        }
        v.op = IrOp.IR_CONST_BOOL;
        v.bval = res;
        v.arg_count = 0;
        return true;
    }

    // arithmetic / bitwise → int constant
    ulong r;
    switch (v.bop)
    {
        case Tt.TOKEN_PLUS:   r = x + y;
        case Tt.TOKEN_MINUS:  r = x - y;
        case Tt.TOKEN_STAR:   r = x * y;
        case Tt.TOKEN_SLASH:  if (y == 0) return false; r = (ulong)(sx / sy);
        case Tt.TOKEN_PERCENT:if (y == 0) return false; r = (ulong)(sx % sy);
        case Tt.TOKEN_AMP:    r = x & y;
        case Tt.TOKEN_PIPE:   r = x | y;
        case Tt.TOKEN_XOR:    r = x ^ y;
        case Tt.TOKEN_LSHIFT: if (y >= 64) return false; r = x << y;
        case Tt.TOKEN_RSHIFT: if (y >= 64) return false; r = (ulong)(sx >> y);
        default: return false;
    }
    v.op = IrOp.IR_CONST_INT;
    v.ival = r;
    v.arg_count = 0;
    return true;
}

fn void Optimizer.fold_const_arith(Optimizer* o)
{
    SsiModule* m = o.mod;
    for (usz bi = 0; bi < m.block_count; bi++)
    {
        IrBlock* b = &m.blocks[bi];
        IrVal* in = b.head;
        while (in != null)
        {
            if (o.fold_const_bin(in)) o.st.compares_folded++;
            in = in.next;
        }
    }
}

// Fold `cbr cond` where cond is a constant bool → unconditional br to the taken
// successor; remove the untaken edge.
fn void Optimizer.fold_branches(Optimizer* o)
{
    SsiModule* m = o.mod;
    for (usz bi = 0; bi < m.block_count; bi++)
    {
        IrBlock* b = &m.blocks[bi];
        if (b.term != TermKind.TERM_CBR) continue;
        if (b.succ_count < 2) continue;
        // Decide the condition: a folded constant, OR a bool σ-handle whose SASI
        // fact pins it (e.g. `if flag` inside `if flag`).
        Decision d = o.decide_value(b.cond);
        if (d == Decision.D_UNKNOWN) continue;
        bool cond_true = d == Decision.D_TRUE;

        int taken = cond_true ? b.succ[0] : b.succ[1];   // succ[0]=true, succ[1]=false
        int dropped = cond_true ? b.succ[1] : b.succ[0];

        // Rewrite this block to an unconditional branch to `taken`.
        o.detach_edge(b.id, dropped);
        // collapse successors to just `taken`
        b.succ[0] = taken;
        b.succ_count = 1;
        b.case_has[0] = false;
        b.term = TermKind.TERM_BR;
        b.cond = null;
        o.st.branches_folded++;
    }
}

// Remove the CFG edge from→to: drop `to` from from.succ AND from's id from
// to.pred, and DROP the corresponding φ operand in `to` (the operand whose
// predecessor tag is `from`). If `from` had the edge multiple times only one is
// removed (matches one φ operand).
fn void Optimizer.detach_edge(Optimizer* o, int from, int to)
{
    SsiModule* m = o.mod;
    IrBlock* bf = m.blk(from);
    IrBlock* bt = m.blk(to);
    if (bf == null || bt == null) return;

    // remove one occurrence of `to` from bf.succ
    bool removed_succ = false;
    for (usz i = 0; i < bf.succ_count; i++)
    {
        if (!removed_succ && bf.succ[i] == to)
        {
            for (usz j = i + 1; j < bf.succ_count; j++)
            {
                bf.succ[j - 1] = bf.succ[j];
                bf.case_has[j - 1] = bf.case_has[j];
                bf.case_val[j - 1] = bf.case_val[j];
            }
            bf.succ_count--;
            removed_succ = true;
            break;
        }
    }

    // remove one occurrence of `from` from bt.pred AND the matching φ operand
    for (usz i = 0; i < bt.pred_count; i++)
    {
        if (bt.pred[i] == from)
        {
            // drop φ operand whose pred tag == from (first match)
            o.drop_phi_operand(bt, from);
            for (usz j = i + 1; j < bt.pred_count; j++) bt.pred[j - 1] = bt.pred[j];
            bt.pred_count--;
            break;
        }
    }
    o.st.edges_removed++;
}

// Drop the φ operand contributed by predecessor `from` in block `b` (one per φ).
fn void Optimizer.drop_phi_operand(Optimizer* o, IrBlock* b, int from)
{
    IrVal* ph = b.phi_head;
    while (ph != null)
    {
        for (usz k = 0; k < ph.arg_count; k++)
        {
            if (ph.pred[k] == from)
            {
                for (usz j = k + 1; j < ph.arg_count; j++)
                {
                    ph.args[j - 1] = ph.args[j];
                    ph.pred[j - 1] = ph.pred[j];
                }
                ph.arg_count--;
                break;
            }
        }
        ph = ph.next;
    }
}

// ── Pass 3: prune blocks that became unreachable (no preds, not entry) ───────
fn bool Optimizer.is_entry(Optimizer* o, int bid)
{
    SsiModule* m = o.mod;
    for (usz fi = 0; fi < m.func_count; fi++)
    {
        if (m.funcs[fi].entry == bid) return true;
    }
    return false;
}

// Prune by true REACHABILITY (not pred-count). A block is reachable iff it is
// reached from some function entry by following successor edges. Pred-count
// pruning misses unreachable strongly-connected components (e.g. an isolated
// infinite loop after a diverging loop), which would leave dangling operand
// references. We mark from every entry via an explicit worklist DFS, then prune
// every unmarked block.
fn void Optimizer.prune_unreachable(Optimizer* o)
{
    SsiModule* m = o.mod;
    if (m.block_count == 0) return;

    bool* reachable = (bool*)malloc(m.block_count * bool::size);
    int* stack = (int*)malloc(m.block_count * int::size);
    if (reachable == null || stack == null)
    {
        if (reachable != null) free(reachable);
        if (stack != null) free(stack);
        return;
    }
    for (usz i = 0; i < m.block_count; i++) reachable[i] = false;

    // Seed the worklist with every function entry.
    usz sp = 0;
    for (usz fi = 0; fi < m.func_count; fi++)
    {
        int e = m.funcs[fi].entry;
        if (e >= 0 && (usz)e < m.block_count && !reachable[e])
        {
            reachable[e] = true;
            stack[sp] = e;
            sp++;
        }
    }
    // DFS over successor edges.
    while (sp > 0)
    {
        sp--;
        int bid = stack[sp];
        IrBlock* b = m.blk(bid);
        if (b == null) continue;
        for (usz s = 0; s < b.succ_count; s++)
        {
            int to = b.succ[s];
            if (to >= 0 && (usz)to < m.block_count && !reachable[to])
            {
                reachable[to] = true;
                stack[sp] = to;
                sp++;
            }
        }
    }

    // Prune every unmarked block: detach its out-edges (fixing live successors'
    // preds + φ operands), then blank it out as unreachable.
    for (usz bi = 0; bi < m.block_count; bi++)
    {
        if (reachable[bi]) continue;
        IrBlock* b = &m.blocks[bi];
        if (b.term == TermKind.TERM_UNREACHABLE && b.succ_count == 0) continue;
        while (b.succ_count > 0)
        {
            int to = b.succ[0];
            o.detach_edge(b.id, to);
        }
        b.term = TermKind.TERM_UNREACHABLE;
        b.cond = null;
        b.ret_val = null;
        b.head = null;
        b.tail = null;
        b.phi_head = null;
        b.phi_tail = null;
        o.st.blocks_pruned++;
    }

    free(reachable);
    free(stack);
}

// ── Pass 4: dead-instruction elimination (pure values with no users) ─────────
// A value is USED if it appears as an operand of any live instruction/φ, or as a
// block terminator's cond/ret. We mark-sweep: compute the used set, then remove
// unused PURE instructions. Conservative: calls / alloc / free / store-like and
// unknown ops are treated as having side effects and kept.
fn bool is_pure(IrVal* v)
{
    if (v == null) return false;
    switch (v.op)
    {
        case IrOp.IR_CONST_INT:
        case IrOp.IR_CONST_FLOAT:
        case IrOp.IR_CONST_BOOL:
        case IrOp.IR_CONST_STR:
        case IrOp.IR_CONST_NULL:
        case IrOp.IR_CONST_UNIT:
        case IrOp.IR_BIN:
        case IrOp.IR_UN:
        case IrOp.IR_FIELD:
        case IrOp.IR_INDEX:
        case IrOp.IR_CAST:
        case IrOp.IR_TUPLE:
        case IrOp.IR_ARRAY:
        case IrOp.IR_RANGE:
        case IrOp.IR_PHI:
            return true;
        default:
            return false;   // CALL/ALLOC/FREE/STRUCT/PARAM/UNKNOWN/SIGMA: keep
    }
}

fn void Optimizer.dce(Optimizer* o)
{
    SsiModule* m = o.mod;
    if (m.val_count == 0) return;

    // used[id] : value id is referenced somewhere live
    usz n = m.val_count;
    bool* used = (bool*)malloc(n * bool::size);
    if (used == null) return;
    for (usz i = 0; i < n; i++) used[i] = false;

    // Mark from every live block's instructions, φ, and terminator operands.
    for (usz bi = 0; bi < m.block_count; bi++)
    {
        IrBlock* b = &m.blocks[bi];
        mark_list(b.phi_head, used, n);
        mark_list(b.head, used, n);
        if (b.cond != null && valid_id(b.cond, n)) mark_operands(b.cond, used, n);
        if (b.ret_val != null && valid_id(b.ret_val, n)) used[b.ret_val.id] = true;
        if (b.cond != null && valid_id(b.cond, n)) used[b.cond.id] = true;
    }

    // Iteratively: a pure value with no user can be removed; removing it may make
    // its operands unused. Recompute to a fixpoint by repeated sweeps.
    bool changed = true;
    int rounds = 0;
    while (changed && rounds < OPT_FIXPOINT_ROUNDS)
    {
        changed = false;
        rounds++;
        for (usz bi = 0; bi < m.block_count; bi++)
        {
            IrBlock* b = &m.blocks[bi];
            // straight-line instrs
            if (o.sweep_list(b, false, used, n)) changed = true;
            // φ
            if (o.sweep_list(b, true, used, n)) changed = true;
        }
        if (changed)
        {
            // recompute used set
            for (usz i = 0; i < n; i++) used[i] = false;
            for (usz bi = 0; bi < m.block_count; bi++)
            {
                IrBlock* b = &m.blocks[bi];
                mark_list(b.phi_head, used, n);
                mark_list(b.head, used, n);
                if (b.ret_val != null && valid_id(b.ret_val, n)) used[b.ret_val.id] = true;
                if (b.cond != null && valid_id(b.cond, n)) used[b.cond.id] = true;
            }
        }
    }
    free((void*)used);
}

// Remove unused pure values from one of a block's lists. Returns true if any
// removed.
fn bool Optimizer.sweep_list(Optimizer* o, IrBlock* b, bool phi_list, bool* used, usz n)
{
    IrVal* head = phi_list ? b.phi_head : b.head;
    IrVal* new_head = null;
    IrVal* new_tail = null;
    bool removed = false;
    IrVal* in = head;
    while (in != null)
    {
        IrVal* nxt = in.next;
        bool keep = true;
        if (valid_id(in, n) && !used[in.id] && is_pure(in))
        {
            keep = false;
        }
        if (keep)
        {
            in.next = null;
            if (new_tail == null) { new_head = in; new_tail = in; }
            else { new_tail.next = in; new_tail = in; }
        }
        else
        {
            in.next = null;
            o.st.dead_removed++;
            removed = true;
        }
        in = nxt;
    }
    if (phi_list) { b.phi_head = new_head; b.phi_tail = new_tail; }
    else { b.head = new_head; b.tail = new_tail; }
    return removed;
}

fn bool valid_id(IrVal* v, usz n)
{
    return v != null && v.id >= 0 && (usz)v.id < n;
}

fn void mark_operands(IrVal* v, bool* used, usz n)
{
    if (v == null) return;
    for (usz k = 0; k < v.arg_count; k++)
    {
        IrVal* a = v.args[k];
        if (valid_id(a, n)) used[a.id] = true;
    }
}

fn void mark_list(IrVal* head, bool* used, usz n)
{
    IrVal* in = head;
    while (in != null)
    {
        mark_operands(in, used, n);
        in = in.next;
    }
}

// tiny bool-array allocator (avoids pulling a vector type)
extern fn void* malloc(usz size);
extern fn void  free(void* ptr);


// ── Driver: run all passes to a fixpoint ─────────────────────────────────────
fn OptStats Optimizer.run(Optimizer* o)
{
    bool changed = true;
    int rounds = 0;
    while (changed && rounds < OPT_FIXPOINT_ROUNDS)
    {
        rounds++;
        int before = o.st.compares_folded + o.st.branches_folded + o.st.blocks_pruned;
        o.fold_const_arith();     // pass 0: constant arithmetic/compare folding
        o.fold_compares();        // pass 1: SASI redundant-comparison folding
        o.fold_branches();        // pass 2
        o.prune_unreachable();    // pass 3
        int after = o.st.compares_folded + o.st.branches_folded + o.st.blocks_pruned;
        changed = after != before;
    }
    o.dce();                      // pass 4 (once, internally fixpointed)
    o.st.rounds = rounds;
    return o.st;
}

// ── Report ───────────────────────────────────────────────────────────────────
fn void Optimizer.report(Optimizer* o)
{
    printf("\n=== SASI optimization ===\n");
    printf("  redundant compares folded : %d\n", o.st.compares_folded);
    printf("  branches folded (cbr→br)  : %d\n", o.st.branches_folded);
    printf("  blocks pruned             : %d\n", o.st.blocks_pruned);
    printf("  cfg edges removed         : %d\n", o.st.edges_removed);
    printf("  dead instructions removed : %d\n", o.st.dead_removed);
    printf("  fixpoint rounds           : %d\n", o.st.rounds);
}
