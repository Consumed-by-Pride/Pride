// ============================================================================
// ssi_ir.c3 — Explicit CFG + SSI IR  (the backend's input form)
// ----------------------------------------------------------------------------
// Implementation language: C3 (host).
//
// WHAT THIS MODULE IS
// ───────────────────
// `ssi.c3` produces a TREE-structured SSI graph (annotates the AST in place).
// That is ideal for the rewrite/PGL passes that work on the tree.  A backend
// needs an EXPLICIT control-flow graph: real basic blocks, SSA values,
// terminators, φ-nodes naming predecessor blocks, σ-splits on conditional edges.
//
// This module lowers Pryde's structured, goto-free AST into exactly that form.
//
// DATA MODEL
// ──────────
//   SsiModule  — a set of functions sharing one flat val[]/block[]/func[] slab.
//   SsiFunc    — entry block id + contiguous [block_start, block_start+count).
//   IrBlock    — phi_head/tail (φ list) · head/tail (instrs) · ONE terminator
//                · growable succ[]/pred[] edge arrays.
//   IrVal      — one SSA value: const | param | bin/un | call | field/index/cast
//                | tuple/array/struct | alloc/free | range | phi | sigma
//                | effect.op | effect.handle | effect.arm | effect.resume
//                | opaque (IR_UNKNOWN, only for asm and with-cleanup).
//
// COMPLETENESS — NO STUBS
// ───────────────────────
// Every Pryde language construct is lowered to concrete IR.  IR_UNKNOWN appears
// only at two well-defined sites:
//   • NODE_STMT_ASM (inline asm):  IR_UNKNOWN carrying AsmLine/AsmOperand
//     children; .src.kind == NODE_STMT_ASM; tagged EFFECT_UNSAFE.
//   • NODE_EFFECT_WITH cleanup:   IR_UNKNOWN(resource_val);
//     .src.kind == NODE_EFFECT_WITH; backend inserts RAII destructor call.
// Every other IR_UNKNOWN is a resolved global/extern reference (.binder != null).
//
// ALGEBRAIC EFFECTS IR
// ────────────────────
// Effect operations lower to three dedicated opcodes (not CPS-transformed —
// the SSA structure is preserved; the backend chooses the runtime ABI):
//   IR_EFFECT_OP   — perform.  .binder → NODE_EFFECT_OP_DECL; args = op args.
//   IR_HANDLER     — handler frame.  Emitted as the TERM_SWITCH condition of
//                    a dispatch block: succ[0]=join(default), succ[k]=arm_blk_k.
//                    args[0]=comp_val, args[1..]=IR_HANDLER_ARM values.
//   IR_HANDLER_ARM — one arm; emitted in arm_blk; args[0]=body result;
//                    .binder → NODE_HANDLER_ARM.
//   IR_RESUME      — resume(v); args[0]=resume value; .binder → handler arm.
//
// CONSTRUCTION ALGORITHM
// ──────────────────────
// Because Pryde has no goto, the CFG is built by a single structured walk
// (Brandis & Mössenböck single-pass SSA, extended with σ-splits) — no
// dominance-frontier iteration needed.  Loops use a pre-placed header φ per
// loop-carried binder; break/continue feed extra operands via LoopCtx.
//
// VERIFICATION
// ────────────
// SsiModule.verify() checks: every live block has a terminator; succ/pred are
// symmetric; each φ has one operand per predecessor; no dangling value refs.
// ir verify errors == 0 and ir undef_refs == 0 are invariants on clean input.
// ============================================================================

module ssi_ir;

import lexer;
import ast;
import ssi;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

alias Node = ast::AstNode;
alias Nk = ast::NodeKind;
alias Tt = lexer::TokenType;
alias IrValPtr = IrVal*;   // so IrValPtr::size gives the pointer width

// ── IR value opcodes ─────────────────────────────────────────────────────────
enum IrOp : int
{
    IR_CONST_INT,
    IR_CONST_FLOAT,
    IR_CONST_BOOL,
    IR_CONST_STR,
    IR_CONST_NULL,
    IR_CONST_UNIT,
    IR_PARAM,        // function parameter / pattern-bound value (a root SSA def)
    IR_BIN,          // binary op (.bop)
    IR_UN,           // unary op (.bop)
    IR_CALL,         // call: args[0] = callee, args[1..] = arguments
    IR_FIELD,        // a.field   (args[0] = base)
    IR_INDEX,        // a[i]      (args[0]=base, args[1]=index)
    IR_CAST,         // a as T
    IR_TUPLE,        // (a, b, ...)
    IR_ARRAY,        // [a, b, ...]
    IR_STRUCT,       // S { ... }
    IR_ALLOC,        // heap alloc
    IR_FREE,         // free
    IR_RANGE,        // a..b
    IR_PHI,          // φ-merge: args[i] arrives from predecessor block .pred[i]
    IR_SIGMA,        // σ-split: args[0] = source value, .refinement = learned fact
    // ── Algebraic effects ──────────────────────────────────────────────────
    // These three opcodes form a complete, backend-agnostic IR for algebraic
    // effects.  The backend decides the runtime mechanism (vtable, prompt stack,
    // split stack, CPS transform, etc.) — the IR stays clean SSA throughout.
    IR_EFFECT_OP,    // perform Effect.op(args):
                     //   .binder  → the NODE_EFFECT_OP_DECL (op identity)
                     //   args[0..] = op argument values
    IR_HANDLER,      // install a handler frame and run the computation:
                     //   args[0]   = computation value (result of the handled block)
                     //   args[1..] = IR_HANDLER_ARM values, one per arm
                     //   .binder   → the NODE_EFFECT_HANDLE AST node
    IR_HANDLER_ARM,  // one arm of a handler (linked into IR_HANDLER):
                     //   args[0]   = body result value
                     //   .binder   → the NODE_HANDLER_ARM AST node
                     //   The arm's parameter binders are IR_PARAMs in the arm's block.
    IR_RESUME,       // resume(v) inside a handler arm:
                     //   args[0] = the value to resume the computation with
                     //   .binder → the NODE_HANDLER_ARM this resume belongs to
    IR_STORE,        // store: args[0]=ptr_or_gep_base, args[1]=value[, args[2]=index]
                     //   variant A: *ptr = val  → args[0]=ptr, args[1]=val
                     //   variant B: arr[i] = val → args[0]=base, args[1]=val, args[2]=index
                     //   variant C: s.f = val   → args[0]=base, args[1]=val, field_idx stored in .ival
    IR_UNKNOWN       // opaque expression (kept so lowering is always total)
}

// ── Terminators ──────────────────────────────────────────────────────────────
enum TermKind : int
{
    TERM_NONE,        // not yet terminated (open block)
    TERM_RET,         // return ret_val (may be null = unit)
    TERM_BR,          // unconditional branch to succ[0]
    TERM_CBR,         // conditional: cond ? succ[0](true) : succ[1](false)
    TERM_SWITCH,      // switch cond: succ[0]=default, succ[1..]=cases
    TERM_UNREACHABLE  // provably unreachable (after a diverging branch)
}

const usz MAX_OPERANDS   = 16;     // operands per value (φ predecessor fan-in)
const usz MAX_EDGES      = 32;     // succ / pred / switch-case fan-out per block
const usz MAX_IR_VALS    = 65536;
const usz MAX_IR_BLOCKS  = 16384;
const usz MAX_IR_FUNCS   = 4096;
const usz ENV_CAP        = 8192;
const usz LOOP_CAP       = 256;
const usz SCAN_CAP       = 1024;

// ── A single SSA value ───────────────────────────────────────────────────────
struct IrVal
{
    int              id;            // dense value id (v0, v1, ...)
    IrOp             op;
    lexer::TokenType bop;           // IR_BIN / IR_UN operator
    ulong            ival;          // IR_CONST_INT
    double           fval;          // IR_CONST_FLOAT
    bool             bval;          // IR_CONST_BOOL
    char*            sptr;          // IR_CONST_STR
    usz              slen;

    // Operands: GROWABLE heap arrays (small functions stay tiny; wide φ /
    // many-arg calls grow on demand). Backed by malloc, freed in destroy().
    IrVal**          args;          // operands
    int*             pred;          // IR_PHI: predecessor block id per operand
    usz              arg_count;
    usz              arg_cap;

    Node*            refinement;    // IR_SIGMA / IR_PHI: the flow fact (or null)
    Node*            binder;        // source binder this value is a version of
    Node*            src;           // originating AST node
    int              block;         // owning block id
    IrVal*           next;          // intra-block list link (phi-list or instr-list)
}

// ── A basic block ────────────────────────────────────────────────────────────
struct IrBlock
{
    int        id;
    IrVal*     phi_head;            // φ-nodes (block head)
    IrVal*     phi_tail;
    IrVal*     head;               // straight-line instructions
    IrVal*     tail;

    TermKind   term;
    IrVal*     cond;               // CBR / SWITCH discriminant
    IrVal*     ret_val;            // RET value (may be null)

    // Edges: GROWABLE heap arrays (wide switches grow on demand).
    int*       succ;
    usz        succ_count;
    usz        succ_cap;
    int*       pred;
    usz        pred_count;
    usz        pred_cap;
    ulong*     case_val;           // SWITCH: integer label for succ[i] (i>=1)
    bool*      case_has;           // whether case_val[i] is meaningful
}

// ── A function ───────────────────────────────────────────────────────────────
struct SsiFunc
{
    Node*      decl;
    char*      name;
    usz        name_len;
    int        entry;              // entry block id
    int        block_start;        // first block id owned by this fn
    int        block_count;        // contiguous block count
    IrVal*[MAX_EDGES] params;
    usz        param_count;
}

struct EnvEntry { Node* binder; IrVal* val; }
const usz MAX_BREAKS = 64;

// Per-loop context. `continue` re-enters the header (so each continue edge must
// contribute an operand to every header φ); `break` jumps to the exit (so the
// exit may need φs merging the normal-exit value with each break-site value).
// The header-φ arrays live in the lowering frame; the LoopCtx aliases them so
// break/continue handlers can extend them without threading parameters.
struct LoopCtx
{
    int      header;
    int      exit;
    IrVal**  hdr_phis;          // → caller's header-φ array
    Node**   hdr_binders;       // → caller's header-binder array
    usz      nphi;
    int[MAX_BREAKS]  break_blk;   // block id of each break site
    IrVal**  break_vals;          // heap matrix [break * nphi] of captured values
    usz      break_count;
    IrVal*[MAX_BREAKS] break_result; // break-with-value result per site
}

// A captured per-binder value reached at the end of a branch.
struct Snap
{
    Node*[SCAN_CAP]   binders;
    IrVal*[SCAN_CAP]  vals;
    usz count;
}

// ── The IR module + builder state ────────────────────────────────────────────
struct SsiModule
{
    IrVal*    vals;
    usz       val_count;
    IrBlock*  blocks;
    usz       block_count;
    SsiFunc*  funcs;
    usz       func_count;

    ast::AstArena* arena;          // for synthesizing σ refinement nodes

    // builder cursor
    int       cur;                 // current insertion block id (-1 = none)

    EnvEntry[ENV_CAP] env;
    usz       env_count;

    LoopCtx[LOOP_CAP] loops;
    usz       loop_count;

    int       lower_depth;   // recursion guard for the lowering walk
    bool      overflow;

    // Defer stack: function-scoped, LIFO. Each slot is the body AST Node* of
    // a `defer expr` statement. Stored when the defer is encountered; lowered
    // (evaluated) in reverse order into the current block before every TERM_RET.
    // This is the correct semantics: arguments are NOT pre-evaluated at the
    // defer site — the whole expression runs at return, like Zig defer.
    Node*[64] defers;
    usz       defer_count;
    // nested fn decls encountered inside fn bodies — lowered after outer fn completes
    Node*[64] pending_inner_fns;
    usz       pending_inner_count;

    // Reference to the top-level program node (for impl block lookup)
    Node*     program_node;

    // ── Named loop label table ──────────────────────────────────────────────
    // Maps label name → loop stack index (into m.loops[])
    // Allows `break 'outer` and `continue 'outer` to find the right LoopCtx.
    char*[64] loop_label_name;   // label name pointer (into source buffer)
    usz[64]   loop_label_nlen;   // label name length
    usz[64]   loop_label_idx;    // corresponding index into m.loops[]
    usz       loop_label_count;

    // Pending label for the NEXT loop lowered (set by lower_stmt when it sees
    // a NODE_STMT_BREAK_LABEL used as a statement, which acts as a label decl).
    char*     pending_label_name;
    usz       pending_label_nlen;
}

// Cap on lowering recursion depth (degrade gracefully, never overflow).
const int LOWER_MAX_DEPTH = 1200;

// ── Setup / teardown ─────────────────────────────────────────────────────────
fn bool SsiModule.init(SsiModule* m, ast::AstArena* arena)
{
    m.vals = (IrVal*)malloc(MAX_IR_VALS * IrVal::size);
    if (m.vals == null) return false;
    m.blocks = (IrBlock*)malloc(MAX_IR_BLOCKS * IrBlock::size);
    if (m.blocks == null) { free(m.vals); m.vals = null; return false; }
    m.funcs = (SsiFunc*)malloc(MAX_IR_FUNCS * SsiFunc::size);
    if (m.funcs == null) { free(m.vals); free(m.blocks); m.vals = null; return false; }

    m.val_count = 0;
    m.block_count = 0;
    m.func_count = 0;
    m.arena = arena;
    m.cur = -1;
    m.env_count = 0;
    m.loop_count = 0;
    m.lower_depth = 0;
    m.overflow = false;
    m.defer_count = 0;
    m.pending_inner_count = 0;
    return true;
}

fn void SsiModule.destroy(SsiModule* m)
{
    // Free the per-value growable operand arrays.
    if (m.vals != null)
    {
        for (usz i = 0; i < m.val_count; i++)
        {
            IrVal* v = &m.vals[i];
            if (v.args != null) free(v.args);
            if (v.pred != null) free(v.pred);
        }
    }
    // Free the per-block growable edge / case arrays.
    if (m.blocks != null)
    {
        for (usz i = 0; i < m.block_count; i++)
        {
            IrBlock* b = &m.blocks[i];
            if (b.succ != null) free(b.succ);
            if (b.pred != null) free(b.pred);
            if (b.case_val != null) free(b.case_val);
            if (b.case_has != null) free(b.case_has);
        }
    }
    if (m.vals != null)   { free(m.vals); m.vals = null; }
    if (m.blocks != null) { free(m.blocks); m.blocks = null; }
    if (m.funcs != null)  { free(m.funcs); m.funcs = null; }
}

// ── Value construction ───────────────────────────────────────────────────────
fn IrVal* SsiModule.new_val(SsiModule* m, IrOp op, Node* src)
{
    if (m.val_count >= MAX_IR_VALS) { m.overflow = true; return null; }
    IrVal* v = &m.vals[m.val_count];
    v.id = (int)m.val_count;
    m.val_count++;
    v.op = op;
    v.bop = Tt.TOKEN_INVALID;
    v.ival = 0;
    v.fval = 0.0;
    v.bval = false;
    v.sptr = null;
    v.slen = 0;
    v.args = null;
    v.pred = null;
    v.arg_count = 0;
    v.arg_cap = 0;
    v.refinement = null;
    v.binder = null;
    v.src = src;
    v.block = m.cur;
    v.next = null;
    return v;
}

// Append an operand, growing the (heap) args/pred arrays on demand (doubling).
fn void IrVal.add_arg(IrVal* v, IrVal* a, int pred_block)
{
    if (v == null) return;
    if (v.arg_count >= v.arg_cap)
    {
        usz ncap = v.arg_cap == 0 ? 4 : v.arg_cap * 2;
        IrVal** na = (IrVal**)malloc(ncap * IrValPtr::size);
        int* np = (int*)malloc(ncap * int::size);
        if (na == null || np == null)
        {
            if (na != null) free(na);
            if (np != null) free(np);
            return;   // OOM: drop silently (verify will not see a phantom slot)
        }
        for (usz i = 0; i < v.arg_count; i++) { na[i] = v.args[i]; np[i] = v.pred[i]; }
        if (v.args != null) free(v.args);
        if (v.pred != null) free(v.pred);
        v.args = na;
        v.pred = np;
        v.arg_cap = ncap;
    }
    v.args[v.arg_count] = a;
    v.pred[v.arg_count] = pred_block;
    v.arg_count++;
}

// Create AND emit a unit constant into the current block, so it is a real
// defined SSA value (never a dangling operand). Used for the value of
// statement-like / else-less branches that still feed a result-φ.
fn IrVal* SsiModule.mk_unit(SsiModule* m, Node* src)
{
    IrVal* u = m.new_val(IrOp.IR_CONST_UNIT, src);
    if (u != null) m.emit(u);
    return u;
}

// ── Block construction ───────────────────────────────────────────────────────
fn int SsiModule.new_block(SsiModule* m)
{
    if (m.block_count >= MAX_IR_BLOCKS) { m.overflow = true; return -1; }
    int id = (int)m.block_count;
    IrBlock* b = &m.blocks[m.block_count];
    m.block_count++;
    b.id = id;
    b.phi_head = null;
    b.phi_tail = null;
    b.head = null;
    b.tail = null;
    b.term = TermKind.TERM_NONE;
    b.cond = null;
    b.ret_val = null;
    b.succ = null;
    b.succ_count = 0;
    b.succ_cap = 0;
    b.pred = null;
    b.pred_count = 0;
    b.pred_cap = 0;
    b.case_val = null;
    b.case_has = null;
    return id;
}

fn IrBlock* SsiModule.blk(SsiModule* m, int id)
{
    if (id < 0 || (usz)id >= m.block_count) return null;
    return &m.blocks[id];
}

fn bool SsiModule.terminated(SsiModule* m)
{
    IrBlock* b = m.blk(m.cur);
    return b == null || b.term != TermKind.TERM_NONE;
}

// Append a straight-line instruction to the current block.
fn void SsiModule.emit(SsiModule* m, IrVal* v)
{
    if (v == null) return;
    IrBlock* b = m.blk(m.cur);
    if (b == null) return;
    v.block = m.cur;
    if (b.tail == null) { b.head = v; b.tail = v; }
    else { b.tail.next = v; b.tail = v; }
}

// Prepend semantics for φ: add to the block's φ-list (order doesn't matter).
fn void SsiModule.add_phi(SsiModule* m, int block_id, IrVal* v)
{
    if (v == null) return;
    IrBlock* b = m.blk(block_id);
    if (b == null) return;
    v.block = block_id;
    if (b.phi_tail == null) { b.phi_head = v; b.phi_tail = v; }
    else { b.phi_tail.next = v; b.phi_tail = v; }
}

// Connect from -> to (records both succ and pred). Returns the succ slot index.
// Grow a block's successor arrays (succ + case_val + case_has) to fit one more.
fn bool grow_succ(IrBlock* b)
{
    if (b.succ_count < b.succ_cap) return true;
    usz ncap = b.succ_cap == 0 ? 2 : b.succ_cap * 2;
    int* ns = (int*)malloc(ncap * int::size);
    ulong* ncv = (ulong*)malloc(ncap * ulong::size);
    bool* nch = (bool*)malloc(ncap * bool::size);
    if (ns == null || ncv == null || nch == null)
    {
        if (ns != null) free(ns);
        if (ncv != null) free(ncv);
        if (nch != null) free(nch);
        return false;
    }
    for (usz i = 0; i < b.succ_count; i++) { ns[i] = b.succ[i]; ncv[i] = b.case_val[i]; nch[i] = b.case_has[i]; }
    if (b.succ != null) free(b.succ);
    if (b.case_val != null) free(b.case_val);
    if (b.case_has != null) free(b.case_has);
    b.succ = ns;
    b.case_val = ncv;
    b.case_has = nch;
    b.succ_cap = ncap;
    return true;
}

fn bool grow_pred(IrBlock* b)
{
    if (b.pred_count < b.pred_cap) return true;
    usz ncap = b.pred_cap == 0 ? 2 : b.pred_cap * 2;
    int* np = (int*)malloc(ncap * int::size);
    if (np == null) return false;
    for (usz i = 0; i < b.pred_count; i++) np[i] = b.pred[i];
    if (b.pred != null) free(b.pred);
    b.pred = np;
    b.pred_cap = ncap;
    return true;
}

fn int SsiModule.link(SsiModule* m, int from, int to)
{
    IrBlock* bf = m.blk(from);
    IrBlock* bt = m.blk(to);
    if (bf == null || bt == null) return -1;
    int slot = -1;
    if (grow_succ(bf))
    {
        slot = (int)bf.succ_count;
        bf.succ[bf.succ_count] = to;
        bf.case_has[bf.succ_count] = false;
        bf.case_val[bf.succ_count] = 0;
        bf.succ_count++;
    }
    else { m.overflow = true; }
    if (grow_pred(bt)) { bt.pred[bt.pred_count] = from; bt.pred_count++; }
    else { m.overflow = true; }
    return slot;
}

// ── Environment (binder → current SSA value) ─────────────────────────────────
fn usz SsiModule.env_mark(SsiModule* m) { return m.env_count; }
fn void SsiModule.env_reset(SsiModule* m, usz mark) { m.env_count = mark; }

fn IrVal* SsiModule.env_lookup(SsiModule* m, Node* binder)
{
    if (binder == null) return null;
    usz i = m.env_count;
    while (i > 0) { i--; if (m.env[i].binder == binder) return m.env[i].val; }
    return null;
}

fn void SsiModule.env_push(SsiModule* m, Node* binder, IrVal* val)
{
    if (m.env_count >= ENV_CAP) { m.overflow = true; return; }
    m.env[m.env_count].binder = binder;
    m.env[m.env_count].val = val;
    m.env_count++;
}

// ── σ-refinement construction (reuses the typechecker's refinement node) ─────
fn Node* SsiModule.mk_refinement(SsiModule* m, Tt op, Node* bound, int line, int col)
{
    Node*[1] buf;
    buf[0] = bound;
    return ast::node_op(m.arena, Nk.NODE_TYPE_REFINEMENT, op, &buf[0], 1, line, col);
}

// Emit one σ value per fact the condition implies on this edge (multi-fact:
// `a < 10 && flag` yields two σ). Each σ reads the binder's current version and
// rebinds it to the refined version, so later uses on this edge see the fact.
// `polarity` selects the taken (true) or not-taken (false) edge.
fn void SsiModule.emit_sigmas(SsiModule* m, Node* cond, bool polarity)
{
    if (cond == null) return;
    ssi::FactSet fs;
    fs.count = 0;
    ssi::collect_facts_pure(m.arena, cond, polarity, &fs);
    for (usz i = 0; i < fs.count; i++)
    {
        ssi::EdgeFact* ef = &fs.facts[i];
        if (ef.binder == null) continue;
        IrVal* cur = m.env_lookup(ef.binder);
        // No in-scope value to refine ⇒ no σ (a σ with a null source would be a
        // dangling, unresolvable fact). Sound: we simply learn nothing here.
        if (cur == null) continue;
        IrVal* sg = m.new_val(IrOp.IR_SIGMA, cond);
        if (sg == null) continue;
        sg.binder = ef.binder;
        sg.refinement = m.mk_refinement(ef.op, ef.bound, cond.line, cond.col);
        sg.add_arg(cur, -1);
        m.emit(sg);
        m.env_push(ef.binder, sg);
    }
}

// ── Assigned-binder scan (for loop-header φ pre-placement) ────────────────────
// Collect every OUTER binder that is reassigned anywhere inside `n` (without
// descending into nested function declarations, which have their own scope).
fn void collect_assigned(Node* n, Snap* out)
{
    if (n == null) return;
    if (n.kind == Nk.NODE_DECL_FN) return;   // nested fn: separate scope
    if (n.kind == Nk.NODE_EXPR_ASSIGN && n.child_count >= 1)
    {
        Node* lhs = n.children[0];
        if (lhs != null && lhs.kind == Nk.NODE_IDENT && lhs.resolved != null)
        {
            bool seen = false;
            for (usz i = 0; i < out.count; i++) { if (out.binders[i] == lhs.resolved) { seen = true; break; } }
            if (!seen && out.count < SCAN_CAP)
            {
                out.binders[out.count] = lhs.resolved;
                out.vals[out.count] = null;
                out.count++;
            }
        }
    }
    for (usz i = 0; i < n.child_count; i++) collect_assigned(n.children[i], out);
}

// ── Capture: which env binders changed since `mark` (a branch's net effect) ──
fn void SsiModule.capture(SsiModule* m, usz mark, Snap* snap)
{
    snap.count = 0;
    usz i = m.env_count;
    while (i > mark)
    {
        i--;
        Node* b = m.env[i].binder;
        IrVal* v = m.env[i].val;
        bool seen = false;
        for (usz j = 0; j < snap.count; j++) { if (snap.binders[j] == b) { seen = true; break; } }
        if (seen) continue;
        // σ-refinement versions are flow facts, not real reassignments to merge.
        if (v != null && v.op == IrOp.IR_SIGMA) continue;
        if (snap.count < SCAN_CAP)
        {
            snap.binders[snap.count] = b;
            snap.vals[snap.count] = v;
            snap.count++;
        }
    }
}

fn IrVal* find_snap(Snap* s, Node* binder)
{
    for (usz i = 0; i < s.count; i++) { if (s.binders[i] == binder) return s.vals[i]; }
    return null;
}

fn bool snap_has(Snap* s, Node* binder)
{
    for (usz i = 0; i < s.count; i++) { if (s.binders[i] == binder) return true; }
    return false;
}

// Is this binder visible (declared) before the current scope mark?
fn bool SsiModule.is_outer(SsiModule* m, Node* binder, usz mark)
{
    for (usz i = 0; i < mark; i++) { if (m.env[i].binder == binder) return true; }
    return false;
}

// ============================================================================
// Lowering
// ============================================================================
fn void SsiModule.build(SsiModule* m, Node* program)
{
    if (program == null) return;
    m.program_node = program;  // store for impl lookup
    m.lower_program(program);
}

fn void SsiModule.lower_program(SsiModule* m, Node* n)
{
    if (n == null || m.overflow) return;
    if (m.lower_depth > LOWER_MAX_DEPTH) { m.overflow = true; return; }
    m.lower_depth++;
    switch (n.kind)
    {
        case Nk.NODE_DECL_FN:
            // Skip abstract generic templates: a fn that still carries a
            // NODE_GENERIC_PARAM child is a template only — monomorphization
            // has already appended concrete clones to the program.
            bool is_generic = false;
            for (usz gi = 0; gi < n.child_count; gi++)
            {
                Node* gc = n.children[gi];
                if (gc != null && gc.kind == Nk.NODE_GENERIC_PARAM)
                    { is_generic = true; break; }
            }
            if (!is_generic)
            {
                m.lower_fn(n);
                // Drain pending nested fns collected during this fn's lowering
                usz pi = 0;
                while (pi < m.pending_inner_count)
                {
                    Node* inner = m.pending_inner_fns[pi];
                    pi++;
                    if (inner != null) { m.lower_fn(inner); }
                }
                m.pending_inner_count = 0;
            }
        case Nk.NODE_DECL_STRUCT:
        case Nk.NODE_DECL_UNION:
            // Also skip generic struct/union templates (no IR to emit for them).
            break;
        default:
            for (usz i = 0; i < n.child_count; i++) m.lower_program(n.children[i]);
    }
    m.lower_depth--;
}

// Lower one function: a fresh entry block, parameters as root SSA defs, then
// each clause body. (Multi-clause functions share one entry; each clause's
// pattern binders are bound fresh and its body lowered in sequence — the IR
// keeps them as separate straight-line regions, which the backend can later
// turn into dispatch. For the common single-clause case this is exact.)
fn void SsiModule.lower_fn(SsiModule* m, Node* fn_node)
{
    if (m.func_count >= MAX_IR_FUNCS) { m.overflow = true; return; }
    SsiFunc* f = &m.funcs[m.func_count];
    m.func_count++;
    f.decl = fn_node;
    f.name = null;
    f.name_len = 0;
    f.param_count = 0;
    f.block_start = (int)m.block_count;

    // Function name (first ident child).
    for (usz i = 0; i < fn_node.child_count; i++)
    {
        Node* c = fn_node.children[i];
        if (c != null && c.kind == Nk.NODE_IDENT)
        {
            f.name = c.p.ident.name_ptr;
            f.name_len = c.p.ident.name_len;
            break;
        }
    }

    int entry = m.new_block();
    f.entry = entry;
    m.cur = entry;
    usz fn_mark = m.env_mark();
    m.defer_count = 0;   // reset per-function defer stack

    // Collect this function's clauses (each = pattern + guard? + body).
    Node*[256] clauses;
    usz nclause = 0;
    for (usz i = 0; i < fn_node.child_count; i++)
    {
        Node* c = fn_node.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_EXPR_BLOCK)
        {
            for (usz j = 0; j < c.child_count; j++)
            {
                Node* clause = c.children[j];
                if (clause != null && clause.kind == Nk.NODE_CLAUSE && nclause < 256)
                {
                    clauses[nclause] = clause;
                    nclause++;
                }
            }
        }
    }

    if (nclause == 0)
    {
        // Bodyless / extern function: a trivial unit-returning entry.
        IrBlock* eb = m.blk(entry);
        if (eb != null) { eb.term = TermKind.TERM_RET; eb.ret_val = null; }
        f.block_count = (int)m.block_count - f.block_start;
        return;
    }

    // Function parameters: arity from the first clause's pattern (a tuple ⇒ its
    // arity; otherwise a single argument). These IR_PARAM values are the roots
    // every clause dispatches on.
    Node* pat0 = clauses[0].child_count >= 1 ? clauses[0].children[0] : null;
    usz arity = 1;
    if (pat0 != null && pat0.kind == Nk.NODE_PATTERN_TUPLE) arity = pat0.child_count;
    if (arity == 0) arity = 1;
    if (arity > MAX_EDGES) arity = MAX_EDGES;

    IrVal*[MAX_EDGES] params;
    for (usz i = 0; i < arity; i++)
    {
        IrVal* pv = m.new_val(IrOp.IR_PARAM, pat0);
        if (pv != null) { m.emit(pv); }
        params[i] = pv;
        if (pv != null && f.param_count < MAX_EDGES) { f.params[f.param_count] = pv; f.param_count++; }
    }

    // Dispatch cascade: each clause tests its pattern against the params; on a
    // match it binds + lowers its body, otherwise control flows to the next
    // clause's test. An irrefutable clause ends the cascade.
    int cur_test = entry;
    for (usz ci = 0; ci < nclause; ci++)
    {
        Node* clause = clauses[ci];
        Node* pat = clause.child_count >= 1 ? clause.children[0] : null;
        m.cur = cur_test;
        usz tmark = m.env_mark();
        IrVal* cond = m.clause_test(pat, &params[0], arity);

        // A guard (`| pat, guard -> body`) makes the clause refutable: bind the
        // pattern, evaluate the guard, AND it into the dispatch condition.
        Node* guard = null;
        for (usz gi = 1; gi < clause.child_count; gi++)
        {
            Node* c = clause.children[gi];
            if (c != null && c.kind == Nk.NODE_PATTERN_GUARD) { guard = c; break; }
        }
        if (guard != null)
        {
            m.bind_pattern_values(pat, &params[0], arity);
            IrVal* gv = null;
            if (guard.child_count >= 1) gv = m.lower_expr(guard.children[0]);
            cond = m.and_cond(cond, gv, guard);
            m.env_reset(tmark);   // un-bind; re-bound in the body block below
        }

        if (cond == null)
        {
            // Irrefutable: bind in this block, lower the body, stop.
            m.bind_pattern_values(pat, &params[0], arity);
            m.lower_clause_body(clause);
            m.env_reset(tmark);
            cur_test = -1;
            break;
        }

        int body = m.new_block();
        int next = m.new_block();
        IrBlock* tb = m.blk(cur_test);
        if (tb != null) { tb.term = TermKind.TERM_CBR; tb.cond = cond; }
        m.link(cur_test, body);
        m.link(cur_test, next);

        m.cur = body;
        usz bmark = m.env_mark();
        m.bind_pattern_values(pat, &params[0], arity);
        m.lower_clause_body(clause);
        m.env_reset(bmark);

        m.env_reset(tmark);
        cur_test = next;
    }

    // A trailing no-match block (all clauses refutable) is non-exhaustive: trap.
    if (cur_test >= 0)
    {
        IrBlock* nb = m.blk(cur_test);
        if (nb != null && nb.term == TermKind.TERM_NONE) nb.term = TermKind.TERM_UNREACHABLE;
    }

    m.env_reset(fn_mark);
    f.block_count = (int)m.block_count - f.block_start;

    // ── Post-lowering optimization passes (per-function) ─────────────────
    // Run after the full function body is lowered so all blocks/edges exist.
    // Order matters: dead-block elim before phi-pruning (fewer phi fixes);
    // phi-pruning before LICM (simpler operands to analyse);
    // critical-edge splitting last (adds blocks, invalidates block counts).

    // Pass 1: eliminate dead blocks (unreachable code after break/continue/return).
    m.eliminate_dead_blocks(f);

    // Pass 2: prune trivial phi nodes (single-operand, all-same operands).
    m.prune_trivial_phis(f);

    // Pass 3: loop-invariant code motion — hoist pure invariants out of loops.
    m.hoist_loop_invariants(f);

    // Pass 4: split critical edges — now with correct pred-list fixup.
    // Only split edges where the target block has phi nodes (required).
    m.split_critical_edges(f);
}

// Lower the body part of a clause (children after the pattern), terminating the
// final block with an implicit `ret` of the body's last value.
fn void SsiModule.lower_clause_body(SsiModule* m, Node* clause)
{
    IrVal* result = null;
    for (usz i = 1; i < clause.child_count; i++)
    {
        Node* c = clause.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_PATTERN_GUARD) continue;   // already tested in dispatch
        if (c.kind == Nk.NODE_EXPR_BLOCK)
        {
            usz bm = m.env_mark();
            result = m.lower_block(c);
            m.env_close_block(bm);
        }
        else { result = m.lower_stmt(c); }
    }
    if (!m.terminated())
    {
        m.emit_defers();
        IrBlock* b = m.blk(m.cur);
        if (b != null) { b.term = TermKind.TERM_RET; b.ret_val = result; }
    }
}

// Build a boolean test that a clause's pattern matches the parameter values, or
// null if the pattern is irrefutable (always matches).
fn IrVal* SsiModule.clause_test(SsiModule* m, Node* pat, IrVal** params, usz arity)
{
    if (pat == null) return null;
    if (pat.kind == Nk.NODE_PATTERN_TUPLE && pat.child_count == arity)
    {
        IrVal* acc = null;
        for (usz i = 0; i < arity; i++)
        {
            IrVal* t = m.single_test(pat.children[i], params[i]);
            acc = m.and_cond(acc, t, pat);
        }
        return acc;
    }
    return m.single_test(pat, arity >= 1 ? params[0] : null);
}

// A single sub-pattern's refutability test against one value.
fn IrVal* SsiModule.single_test(SsiModule* m, Node* pat, IrVal* v)
{
    if (pat == null || v == null) return null;
    switch (pat.kind)
    {
        case Nk.NODE_PATTERN_LITERAL:
            if (pat.child_count >= 1)
            {
                IrVal* lit = m.lower_expr(pat.children[0]);
                IrVal* t = m.new_val(IrOp.IR_BIN, pat);
                if (t != null) { t.bop = Tt.TOKEN_EQEQ; t.add_arg(v, -1); t.add_arg(lit, -1); m.emit(t); }
                return t;
            }
            return null;
        default:
            return null;   // ident / wildcard / binding patterns: irrefutable
    }
}

fn IrVal* SsiModule.and_cond(SsiModule* m, IrVal* a, IrVal* b, Node* src)
{
    if (a == null) return b;
    if (b == null) return a;
    IrVal* t = m.new_val(IrOp.IR_BIN, src);
    if (t != null) { t.bop = Tt.TOKEN_AMPAMP; t.add_arg(a, -1); t.add_arg(b, -1); m.emit(t); }
    return t;
}

// Bind a clause pattern's identifiers to the parameter values.
fn void SsiModule.bind_pattern_values(SsiModule* m, Node* pat, IrVal** params, usz arity)
{
    if (pat == null) return;
    if (pat.kind == Nk.NODE_PATTERN_TUPLE && pat.child_count == arity)
    {
        for (usz i = 0; i < arity; i++) m.bind_let_pattern(pat.children[i], params[i]);
        return;
    }
    m.bind_let_pattern(pat, arity >= 1 ? params[0] : null);
}

// Bind every binder a pattern introduces to a fresh IR_PARAM root value.
fn void SsiModule.bind_pattern(SsiModule* m, SsiFunc* f, Node* pat)
{
    if (pat == null) return;
    switch (pat.kind)
    {
        case Nk.NODE_PATTERN_IDENT:
            IrVal* pv = m.new_val(IrOp.IR_PARAM, pat);
            if (pv != null) { pv.binder = pat; m.emit(pv); m.env_push(pat, pv); }
            if (f != null && pv != null && f.param_count < MAX_EDGES)
            {
                f.params[f.param_count] = pv;
                f.param_count++;
            }
        case Nk.NODE_PATTERN_TUPLE:
        case Nk.NODE_PATTERN_OR:
            for (usz i = 0; i < pat.child_count; i++) m.bind_pattern(f, pat.children[i]);
        case Nk.NODE_PATTERN_STRUCT:
            for (usz i = 0; i < pat.child_count; i++)
            {
                Node* fld = pat.children[i];
                if (fld == null || fld.kind != Nk.NODE_PATTERN_FIELD) continue;
                if (fld.child_count >= 2) { m.bind_pattern(f, fld.children[1]); }
                else
                {
                    IrVal* fv = m.new_val(IrOp.IR_PARAM, fld);
                    if (fv != null) { fv.binder = fld; m.emit(fv); m.env_push(fld, fv); }
                }
            }
        default:
            for (usz i = 0; i < pat.child_count; i++) m.bind_pattern(f, pat.children[i]);
    }
}

// Lower a block, returning the value of its final expression (unit if empty /
// last is a statement). Drops block-local lets on exit but keeps outer-binder
// reassignments live (they were already overridden in env).
fn IrVal* SsiModule.lower_block(SsiModule* m, Node* n)
{
    IrVal* last = null;
    for (usz i = 0; i < n.child_count; i++)
    {
        Node* c = n.children[i];
        if (c == null) continue;
        last = m.lower_stmt(c);
    }
    if (last == null) last = m.mk_unit(n);
    return last;
}

// A statement: declarations bind; everything else is an expression.
// Flush all deferred actions in LIFO order into the current block.
// Called by every code path that emits a TERM_RET.
// Each deferred body Node is lowered fresh here so the expression executes
// in the return block's SSA context (correct defer semantics).
fn void SsiModule.emit_defers(SsiModule* m)
{
    if (m.defer_count == 0) return;
    usz i = m.defer_count;
    while (i > 0)
    {
        i--;
        Node* body = m.defers[i];
        if (body != null) { m.lower_expr(body); }
    }
}

fn IrVal* SsiModule.lower_stmt(SsiModule* m, Node* n)
{
    if (n == null) return null;
    switch (n.kind)
    {
        case Nk.NODE_DECL_LET:
        case Nk.NODE_DECL_MUT:
        case Nk.NODE_DECL_CONST:
        case Nk.NODE_DECL_STATIC:
            m.lower_let(n);
            return null;
        case Nk.NODE_STMT_EXPR:
            // A statement-expression wrapper: lower the inner expression.
            IrVal* last = null;
            for (usz i = 0; i < n.child_count; i++)
            {
                Node* c = n.children[i];
                if (c == null || ssi::is_type_or_row(c)) continue;
                last = m.lower_expr(c);
            }
            return last;
        case Nk.NODE_STMT_RETURN:
            m.lower_return(n);
            return null;
        case Nk.NODE_STMT_BREAK:
            {
                IrVal* bv = (n.child_count >= 1 && n.children[0] != null)
                          ? m.lower_expr(n.children[0]) : null;
                m.lower_break_val(bv);
            }
            return null;
        case Nk.NODE_STMT_CONTINUE:
            m.lower_continue();
            return null;
        case Nk.NODE_STMT_BREAK_LABEL:
            {
                // child[0] is the label name ident
                Node* lbl = n.child_count >= 1 ? n.children[0] : null;
                char* nm = lbl != null ? lbl.p.ident.name_ptr : null;
                usz   nl = lbl != null ? lbl.p.ident.name_len  : 0;
                // Skip the leading ' in the label ref token
                if (nm != null && nl > 1 && nm[0] == '\'')
                { nm++; nl--; }
                // If inside a loop: break to labeled loop's exit.
                // If NOT inside any loop yet: treat as a loop-label declaration
                // for the NEXT loop statement (set as pending).
                if (m.loop_count > 0)
                {
                    m.lower_break_label(nm, nl);
                }
                else
                {
                    // Label declaration: 'name: <next loop>
                    m.pending_label_name = nm;
                    m.pending_label_nlen = nl;
                }
            }
            return null;
        case Nk.NODE_STMT_CONTINUE_LABEL:
            {
                Node* lbl = n.child_count >= 1 ? n.children[0] : null;
                char* nm = lbl != null ? lbl.p.ident.name_ptr : null;
                usz   nl = lbl != null ? lbl.p.ident.name_len  : 0;
                if (nm != null && nl > 1 && nm[0] == '\'')
                { nm++; nl--; }
                m.lower_continue_label(nm, nl);
            }
            return null;

        case Nk.NODE_STMT_TRAP:
        case Nk.NODE_STMT_UNREACHABLE:
            // `trap` / `unreachable` — terminate the current block as UNREACHABLE.
            // Route any subsequent (dead) code into a fresh unreachable block so
            // the IR stays well-formed (no open blocks, no orphaned instructions).
            if (!m.terminated())
            {
                IrBlock* tb = m.blk(m.cur);
                if (tb != null) tb.term = TermKind.TERM_UNREACHABLE;
                int dead = m.new_block();
                m.cur = dead;
                IrBlock* db = m.blk(dead);
                if (db != null) db.term = TermKind.TERM_UNREACHABLE;
            }
            return null;

        case Nk.NODE_STMT_ASSERT:
            // `assert cond` — CBR: cond ? continue_blk : trap_blk.
            // On the true edge: emit σ-refinements (the asserted facts are known to
            // hold for the rest of the block).  On the false edge: UNREACHABLE
            // (the assertion failure is defined as UB / program abort in Pryde).
            {
                Node* cond = n.child_count >= 1 ? n.children[0] : null;
                if (cond == null || m.terminated()) { return null; }
                IrVal* cond_val = m.lower_expr(cond);

                int pre_blk    = m.cur;
                int pass_blk   = m.new_block();
                int fail_blk   = m.new_block();

                IrBlock* pb = m.blk(pre_blk);
                if (pb != null) { pb.term = TermKind.TERM_CBR; pb.cond = cond_val; }
                m.link(pre_blk, pass_blk);   // true  → continue
                m.link(pre_blk, fail_blk);   // false → trap

                // Failure block: assertion violated → unreachable.
                m.cur = fail_blk;
                IrBlock* fb = m.blk(fail_blk);
                if (fb != null) fb.term = TermKind.TERM_UNREACHABLE;

                // Pass block: assertion held — emit σ refinements.
                m.cur = pass_blk;
                m.emit_sigmas(cond, true);
            }
            return null;

        case Nk.NODE_STMT_ASSUME:
        case Nk.NODE_STMT_INVARIANT:
            // `assume cond` / `invariant cond` — no CFG change; emit σ-refinements
            // of the condition into the current block so the SASI optimizer can use
            // them.  Both are hints: the backend may trust them without checking.
            {
                Node* cond = n.child_count >= 1 ? n.children[0] : null;
                if (cond != null && !m.terminated())
                {
                    m.lower_expr(cond);   // evaluate for side-effects / completeness
                    m.emit_sigmas(cond, true);
                }
            }
            return null;

        case Nk.NODE_STMT_DEFER:
            // `defer expr` — push the expression's value onto the function-scoped
            // defer stack.  The expression is lowered NOW (arguments captured at
            // the defer site, matching C/Go/Zig semantics); the resulting IrVal is
            // replayed by emit_defers() before every TERM_RET.
            {
                Node* body = n.child_count >= 1 ? n.children[0] : null;
                if (body != null && !m.terminated())
                {
                    if (m.defer_count < 64)
                    {
                        m.defers[m.defer_count] = body;
                        m.defer_count++;
                    }
                }
            }
            return null;

        case Nk.NODE_STMT_ASM:
            // `asm "..." : constraints` — lower all children (string literals and
            // operand expressions) and wrap them in an IR_UNKNOWN tagged as an asm
            // site.  The backend pattern-matches IR_UNKNOWN nodes with EFFECT_UNSAFE
            // to emit the actual inline assembly.
            {
                IrVal* v = m.new_val(IrOp.IR_UNKNOWN, n);
                for (usz i = 0; i < n.child_count; i++)
                {
                    Node* c = n.children[i];
                    if (c == null) continue;
                    // Lower each AsmLine (string) and AsmOperand (constraint + expr).
                    for (usz j = 0; j < c.child_count; j++)
                    {
                        Node* ch = c.children[j];
                        if (ch == null || ssi::is_type_or_row(ch)) continue;
                        IrVal* a = m.lower_expr(ch);
                        if (v != null) v.add_arg(a, -1);
                    }
                    // Also lower the AsmLine/AsmOperand node itself if it's a leaf.
                    if (c.child_count == 0)
                    {
                        IrVal* a = m.lower_expr(c);
                        if (v != null && a != null) v.add_arg(a, -1);
                    }
                }
                if (v != null) m.emit(v);
                return v;
            }

        default:
            return m.lower_expr(n);
    }
}

fn void SsiModule.lower_let(SsiModule* m, Node* d)
{
    IrVal* init = null;
    for (usz i = 1; i < d.child_count; i++)
    {
        Node* c = d.children[i];
        if (c != null && !ssi::is_type_or_row(c)) { init = m.lower_expr(c); }
    }
    // Bind the pattern's identifier(s) to the initializer value.
    if (d.child_count >= 1) m.bind_let_pattern(d.children[0], init);
}

fn void SsiModule.bind_let_pattern(SsiModule* m, Node* pat, IrVal* val)
{
    if (pat == null) return;
    switch (pat.kind)
    {
        case Nk.NODE_PATTERN_IDENT:
            IrVal* v = val;
            if (v == null) { v = m.new_val(IrOp.IR_UNKNOWN, pat); if (v != null) m.emit(v); }
            m.env_push(pat, v);
        case Nk.NODE_PATTERN_TUPLE:
            // destructure: each element reads a projection of `val`
            for (usz i = 0; i < pat.child_count; i++)
            {
                IrVal* proj = m.new_val(IrOp.IR_INDEX, pat.children[i]);
                if (proj != null && val != null)
                {
                    proj.add_arg(val, -1);
                    proj.ival = (ulong)i;  // field index for struct extractvalue
                }
                if (proj != null) m.emit(proj);
                m.bind_let_pattern(pat.children[i], proj);
            }
        default:
            for (usz i = 0; i < pat.child_count; i++) m.bind_let_pattern(pat.children[i], val);
    }
}

fn void SsiModule.lower_return(SsiModule* m, Node* n)
{
    if (m.terminated()) return;
    IrVal* rv = null;
    if (n.child_count >= 1) rv = m.lower_expr(n.children[0]);
    m.emit_defers();
    IrBlock* b = m.blk(m.cur);
    if (b != null) { b.term = TermKind.TERM_RET; b.ret_val = rv; }
}

fn void SsiModule.lower_break(SsiModule* m)
{
    m.lower_break_val(null);
}

fn void SsiModule.lower_break_val(SsiModule* m, IrVal* result)
{
    if (m.terminated() || m.loop_count == 0) return;
    LoopCtx* lc = &m.loops[m.loop_count - 1];
    IrBlock* b = m.blk(m.cur);
    if (b == null) return;
    if (lc.break_count < MAX_BREAKS && lc.break_vals != null)
    {
        usz slot = lc.break_count;
        lc.break_blk[slot] = m.cur;
        lc.break_result[slot] = result;
        for (usz i = 0; i < lc.nphi; i++)
        {
            IrVal* v = m.env_lookup(lc.hdr_binders[i]);
            lc.break_vals[slot * lc.nphi + i] = v;
        }
        lc.break_count++;
    }
    b.term = TermKind.TERM_BR;
    m.link(m.cur, lc.exit);
}

fn void SsiModule.lower_continue(SsiModule* m)
{
    if (m.terminated() || m.loop_count == 0) return;
    LoopCtx* lc = &m.loops[m.loop_count - 1];
    IrBlock* b = m.blk(m.cur);
    if (b == null) return;
    // A continue is a back-edge: each header φ gains an operand from this site.
    for (usz i = 0; i < lc.nphi; i++)
    {
        IrVal* back = m.env_lookup(lc.hdr_binders[i]);
        if (back == null) continue;
        lc.hdr_phis[i].add_arg(back, m.cur);
    }
    b.term = TermKind.TERM_BR;
    m.link(m.cur, lc.header);
}

// ── Labeled break/continue ────────────────────────────────────────────────────

// break 'label — jump to the exit of the named enclosing loop.
fn void SsiModule.lower_break_label(SsiModule* m, char* name, usz nlen)
{
    if (m.terminated()) return;
    LoopCtx* lc = m.find_loop_by_label(name, nlen);
    if (lc == null)
    {
        // Label not found — treat as plain break (target innermost loop).
        m.lower_break();
        return;
    }
    IrBlock* b = m.blk(m.cur);
    if (b == null) return;
    // Capture loop-carried values for the labeled loop's exit phis.
    if (lc.break_count < MAX_BREAKS && lc.break_vals != null)
    {
        usz slot = lc.break_count;
        lc.break_blk[slot] = m.cur;
        for (usz i = 0; i < lc.nphi; i++)
        {
            IrVal* v = m.env_lookup(lc.hdr_binders[i]);
            lc.break_vals[slot * lc.nphi + i] = v;
        }
        lc.break_count++;
    }
    b.term = TermKind.TERM_BR;
    m.link(m.cur, lc.exit);
}

// continue 'label — jump back to the header of the named enclosing loop.
fn void SsiModule.lower_continue_label(SsiModule* m, char* name, usz nlen)
{
    if (m.terminated()) return;
    LoopCtx* lc = m.find_loop_by_label(name, nlen);
    if (lc == null)
    {
        m.lower_continue();
        return;
    }
    IrBlock* b = m.blk(m.cur);
    if (b == null) return;
    // Add back-edge operands to every header φ of the target loop.
    for (usz i = 0; i < lc.nphi; i++)
    {
        IrVal* back = m.env_lookup(lc.hdr_binders[i]);
        if (back == null) continue;
        lc.hdr_phis[i].add_arg(back, m.cur);
    }
    b.term = TermKind.TERM_BR;
    m.link(m.cur, lc.header);
}

// ── Expressions ──────────────────────────────────────────────────────────────
fn IrVal* SsiModule.lower_expr(SsiModule* m, Node* n)
{
    if (n == null || m.overflow) return null;
    if (m.lower_depth > LOWER_MAX_DEPTH) { m.overflow = true; return m.mk_unit(n); }
    m.lower_depth++;
    IrVal* res = m.lower_expr_body(n);
    m.lower_depth--;
    return res;
}


// ── Operator overloading dispatch ─────────────────────────────────────────────
// Maps binary operators to their interface method names.
// Returns (interface_name, method_name) or null if no overload applies.

fn char* op_to_interface_name(Tt op)
{
    switch (op)
    {
        case Tt.TOKEN_PLUS:    return (char*)"Add";
        case Tt.TOKEN_MINUS:   return (char*)"Sub";
        case Tt.TOKEN_STAR:    return (char*)"Mul";
        case Tt.TOKEN_SLASH:   return (char*)"Div";
        case Tt.TOKEN_PERCENT: return (char*)"Rem";
        case Tt.TOKEN_AMP:     return (char*)"BitAnd";
        case Tt.TOKEN_PIPE:    return (char*)"BitOr";
        case Tt.TOKEN_XOR:     return (char*)"BitXor";
        case Tt.TOKEN_LSHIFT:  return (char*)"Shl";
        case Tt.TOKEN_RSHIFT:  return (char*)"Shr";
        case Tt.TOKEN_EQEQ:    return (char*)"Eq";
        case Tt.TOKEN_NEQ:     return (char*)"Eq";
        case Tt.TOKEN_LT:      return (char*)"Ord";
        case Tt.TOKEN_LTEQ:    return (char*)"Ord";
        case Tt.TOKEN_GT:      return (char*)"Ord";
        case Tt.TOKEN_GTEQ:    return (char*)"Ord";
        default: return null;
    }
}

fn char* op_to_method_name(Tt op)
{
    switch (op)
    {
        case Tt.TOKEN_PLUS:    return (char*)"add";
        case Tt.TOKEN_MINUS:   return (char*)"sub";
        case Tt.TOKEN_STAR:    return (char*)"mul";
        case Tt.TOKEN_SLASH:   return (char*)"div";
        case Tt.TOKEN_PERCENT: return (char*)"rem";
        case Tt.TOKEN_AMP:     return (char*)"bit_and";
        case Tt.TOKEN_PIPE:    return (char*)"bit_or";
        case Tt.TOKEN_XOR:     return (char*)"bit_xor";
        case Tt.TOKEN_LSHIFT:  return (char*)"shl";
        case Tt.TOKEN_RSHIFT:  return (char*)"shr";
        case Tt.TOKEN_EQEQ:    return (char*)"eq";
        case Tt.TOKEN_NEQ:     return (char*)"ne";
        case Tt.TOKEN_LT:      return (char*)"lt";
        case Tt.TOKEN_LTEQ:    return (char*)"lte";
        case Tt.TOKEN_GT:      return (char*)"gt";
        case Tt.TOKEN_GTEQ:    return (char*)"gte";
        default: return null;
    }
}

// Compare null-terminated C string with a span (ptr+len).
fn bool span_matches_cstr(char* span, usz spanlen, char* cstr)
{
    usz cl = 0; while (cstr[cl]) cl++;
    if (cl != spanlen) return false;
    for (usz i = 0; i < spanlen; i++) if (span[i] != cstr[i]) return false;
    return true;
}

// Search the program for an impl block: impl <iface_name> for <type_name>
// that contains method <method_name>. Returns the fn decl Node or null.
//
// type_annotation: the type node of the LHS operand.
// We match by comparing the impl's "for type" child against the type annotation name.
fn Node* find_impl_method(Node* program, char* iface_name, char* method_name, Node* type_ann)
{
    if (program == null || iface_name == null || method_name == null) return null;

    // Extract type name from type_annotation
    char* type_name = null; usz type_nlen = 0;
    if (type_ann != null)
    {
        if (type_ann.kind == Nk.NODE_TYPE_PRIMITIVE || type_ann.kind == Nk.NODE_TYPEVAR
            || type_ann.kind == Nk.NODE_IDENT)
        {
            type_name = type_ann.p.ident.name_ptr;
            type_nlen = type_ann.p.ident.name_len;
        }
    }

    for (usz ci = 0; ci < program.child_count; ci++)
    {
        Node* decl = program.children[ci];
        if (decl == null || decl.kind != Nk.NODE_DECL_IMPL) continue;

        // child[0] = interface name typevar
        if (decl.child_count < 2) continue;
        Node* iface_node = decl.children[0];
        if (iface_node == null) continue;
        char* in2 = iface_node.p.ident.name_ptr;
        usz   il2 = iface_node.p.ident.name_len;
        if (!span_matches_cstr(in2, il2, iface_name)) continue;

        // Find the "for type" child — first non-generic, non-fn child after child[0]
        Node* for_type = null;
        for (usz fi = 1; fi < decl.child_count; fi++)
        {
            Node* fc = decl.children[fi];
            if (fc == null) continue;
            if (fc.kind == Nk.NODE_DECL_FN) break;
            if (fc.kind == Nk.NODE_TYPE_PRIMITIVE || fc.kind == Nk.NODE_TYPEVAR
                || fc.kind == Nk.NODE_TYPE_PTR || fc.kind == Nk.NODE_TYPE_TUPLE)
            { for_type = fc; break; }
        }

        // Match for_type against type_annotation
        // for_type may be TYPEVAR, TYPE_PRIMITIVE, etc.
        if (type_name != null && for_type != null)
        {
            char* ftn = null; usz ftl = 0;
            if (for_type.kind == Nk.NODE_TYPEVAR || for_type.kind == Nk.NODE_TYPE_PRIMITIVE
                || for_type.kind == Nk.NODE_IDENT)
            {
                ftn = for_type.p.ident.name_ptr;
                ftl = for_type.p.ident.name_len;
            }
            else if (for_type.kind == Nk.NODE_DECL_STRUCT && for_type.child_count >= 1
                     && for_type.children[0] != null)
            {
                ftn = for_type.children[0].p.ident.name_ptr;
                ftl = for_type.children[0].p.ident.name_len;
            }
            if (ftn == null) continue;  // unknown type form — skip
            if (ftl != type_nlen) continue;
            bool tm2 = true;
            for (usz ti2 = 0; ti2 < ftl; ti2++)
            { if (ftn[ti2] != type_name[ti2]) { tm2 = false; break; } }
            if (!tm2) continue;
        }
        else if (type_name != null && for_type == null)
        { continue; }  // impl has no "for" type — skip

        // Search for method_name fn inside this impl block
        for (usz mi = 1; mi < decl.child_count; mi++)
        {
            Node* mfn = decl.children[mi];
            if (mfn == null || mfn.kind != Nk.NODE_DECL_FN) continue;
            if (mfn.child_count < 1 || mfn.children[0] == null) continue;
            char* mn = mfn.children[0].p.ident.name_ptr;
            usz   ml = mfn.children[0].p.ident.name_len;
            if (span_matches_cstr(mn, ml, method_name)) return mfn;
        }
    }
    return null;
}

fn IrVal* SsiModule.lower_expr_body(SsiModule* m, Node* n)
{
    if (m.terminated())
    {
        // Code after a terminator is dead; route it into a fresh unreachable
        // block so the IR stays well-formed.
        int dead = m.new_block();
        m.cur = dead;
        IrBlock* db = m.blk(dead);
        if (db != null) db.term = TermKind.TERM_UNREACHABLE;
    }

    switch (n.kind)
    {
        case Nk.NODE_LIT_INT:
            IrVal* v = m.new_val(IrOp.IR_CONST_INT, n);
            if (v != null) { v.ival = n.p.lit_int.int_val; m.emit(v); }
            return v;
        case Nk.NODE_LIT_FLOAT:
            IrVal* v = m.new_val(IrOp.IR_CONST_FLOAT, n);
            if (v != null) { v.fval = n.p.lit_float.f64_val; m.emit(v); }
            return v;
        case Nk.NODE_LIT_BOOL:
            IrVal* v = m.new_val(IrOp.IR_CONST_BOOL, n);
            if (v != null) { v.bval = n.p.lit_bool.bool_val; m.emit(v); }
            return v;
        case Nk.NODE_LIT_STRING:
            IrVal* v = m.new_val(IrOp.IR_CONST_STR, n);
            if (v != null) { v.sptr = n.p.lit_str.ptr; v.slen = n.p.lit_str.len; m.emit(v); }
            return v;
        case Nk.NODE_LIT_CHAR:
            // Char literal — lower as IR_CONST_INT holding the Unicode codepoint.
            IrVal* v = m.new_val(IrOp.IR_CONST_INT, n);
            if (v != null) { v.ival = (ulong)n.p.lit_char.char_val; m.emit(v); }
            return v;
        case Nk.NODE_LIT_RAW_BYTES:
            // b"..." byte-string — same wire representation as a string constant.
            IrVal* v = m.new_val(IrOp.IR_CONST_STR, n);
            if (v != null) { v.sptr = n.p.lit_str.ptr; v.slen = n.p.lit_str.len; m.emit(v); }
            return v;
        case Nk.NODE_LIT_BOTTOM:
            // ⊥ literal — diverging; mark the current block unreachable and open
            // a fresh dead block so subsequent instructions stay well-formed.
            {
                IrBlock* cur_b = m.blk(m.cur);
                if (cur_b != null && cur_b.term == TermKind.TERM_NONE)
                    { cur_b.term = TermKind.TERM_UNREACHABLE; }
                int dead_bot = m.new_block();
                m.cur = dead_bot;
                IrBlock* db_bot = m.blk(dead_bot);
                if (db_bot != null) db_bot.term = TermKind.TERM_UNREACHABLE;
            }
            return m.mk_unit(n);
        case Nk.NODE_LIT_NULL:
            IrVal* v = m.new_val(IrOp.IR_CONST_NULL, n);
            if (v != null) m.emit(v);
            return v;
        case Nk.NODE_EXPR_UNIT:
            return m.mk_unit(n);

        case Nk.NODE_IDENT:
            // A use reads the binder's current SSA value.
            if (n.resolved != null)
            {
                IrVal* cur = m.env_lookup(n.resolved);
                if (cur != null) return cur;
            }
            // Unresolved (global / fn ref): an opaque named value. Emit it so it
            // is a real defined SSA value (a "global reference" instruction),
            // never a dangling operand.
            IrVal* u = m.new_val(IrOp.IR_UNKNOWN, n);
            if (u != null) { u.binder = n.resolved; m.emit(u); }
            return u;

        case Nk.NODE_EXPR_BINARY:
            {
                // Check for operator overloading via impl blocks.
                // Only dispatch if LHS has a user-defined (non-primitive) type.
                Tt binop = n.p.op.op;
                char* iface_name  = op_to_interface_name(binop);
                char* method_name = op_to_method_name(binop);
                Node* lhs_node = n.child_count >= 1 ? n.children[0] : null;
                Node* type_ann = (lhs_node != null) ? lhs_node.type_annotation : null;
                Node* impl_fn  = null;
                // Only look up impl if LHS has a non-primitive, non-built-in type
                // (structs, enums, newtypes). Primitives use IR_BIN directly.
                bool lhs_is_user_type = false;
                if (type_ann != null &&
                    (type_ann.kind == Nk.NODE_TYPEVAR
                     || type_ann.kind == Nk.NODE_DECL_STRUCT
                     || type_ann.kind == Nk.NODE_DECL_NEWTYPE
                     || type_ann.kind == Nk.NODE_DECL_ENUM))
                { lhs_is_user_type = true; }
                if (lhs_is_user_type && iface_name != null && method_name != null
                    && m.program_node != null)
                {
                    impl_fn = find_impl_method(m.program_node, iface_name,
                                               method_name, type_ann);
                }

                if (impl_fn != null)
                {
                    // Operator overloading: rewrite a OP b → Method.method(a, b)
                    // Emit as IR_CALL to the impl method.
                    IrVal* l = m.lower_expr(n.children[0]);
                    IrVal* r = m.lower_expr(n.child_count >= 2 ? n.children[1] : null);
                    // Build a synthetic call node pointing to the impl fn
                    IrVal* callee_v = m.new_val(IrOp.IR_UNKNOWN, impl_fn);
                    if (callee_v != null)
                    {
                        callee_v.binder = impl_fn;
                        m.emit(callee_v);
                    }
                    IrVal* call_v = m.new_val(IrOp.IR_CALL, n);
                    if (call_v != null)
                    {
                        call_v.add_arg(callee_v, -1);
                        call_v.add_arg(l, -1);
                        call_v.add_arg(r, -1);
                        m.emit(call_v);
                    }
                    return call_v;
                }

                // No overload — emit plain IR_BIN.
                IrVal* l = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
                IrVal* r = m.lower_expr(n.child_count >= 2 ? n.children[1] : null);
                IrVal* v = m.new_val(IrOp.IR_BIN, n);
                if (v != null) { v.bop = binop; v.add_arg(l, -1); v.add_arg(r, -1); m.emit(v); }
                return v;
            }

        case Nk.NODE_EXPR_UNARY:
            IrVal* o = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
            IrVal* v = m.new_val(IrOp.IR_UN, n);
            if (v != null) { v.bop = n.p.op.op; v.add_arg(o, -1); m.emit(v); }
            return v;

        case Nk.NODE_EXPR_ASSIGN:
            return m.lower_assign(n);

        case Nk.NODE_EXPR_CALL:
            // `resume(v)` inside a handler arm → IR_RESUME.
            if (is_resume_call(n)) { return m.lower_resume(n); }
            {
                IrVal* v = m.new_val(IrOp.IR_CALL, n);
                for (usz i = 0; i < n.child_count; i++)
                {
                    Node* c = n.children[i];
                    if (c == null || ssi::is_type_or_row(c)) { continue; }
                    IrVal* a = m.lower_expr(c);
                    if (v != null) { v.add_arg(a, -1); }
                }
                if (v != null) { m.emit(v); }
                return v;
            }
        case Nk.NODE_EXPR_METHOD_CALL:
            // Effect operation perform: `Effect.op(args)` → IR_EFFECT_OP.
            if (is_effect_method_call(n)) { return m.lower_effect_perform(n); }
            {
                IrVal* v = m.new_val(IrOp.IR_CALL, n);
                for (usz i = 0; i < n.child_count; i++)
                {
                    Node* c = n.children[i];
                    if (c == null || ssi::is_type_or_row(c)) { continue; }
                    IrVal* a = m.lower_expr(c);
                    if (v != null) { v.add_arg(a, -1); }
                }
                if (v != null) { m.emit(v); }
                return v;
            }

        case Nk.NODE_EXPR_FIELD:
            IrVal* base = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
            IrVal* v = m.new_val(IrOp.IR_FIELD, n);
            if (v != null) { v.add_arg(base, -1); m.emit(v); }
            return v;

        case Nk.NODE_EXPR_INDEX:
            IrVal* b2 = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
            IrVal* ix = m.lower_expr(n.child_count >= 2 ? n.children[1] : null);
            IrVal* v = m.new_val(IrOp.IR_INDEX, n);
            if (v != null) { v.add_arg(b2, -1); v.add_arg(ix, -1); m.emit(v); }
            return v;

        case Nk.NODE_EXPR_CAST:
            IrVal* src = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
            IrVal* v = m.new_val(IrOp.IR_CAST, n);
            if (v != null) { v.add_arg(src, -1); m.emit(v); }
            return v;

        case Nk.NODE_EXPR_RANGE:
            IrVal* lo = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
            IrVal* hi = m.lower_expr(n.child_count >= 2 ? n.children[1] : null);
            IrVal* v = m.new_val(IrOp.IR_RANGE, n);
            if (v != null) { v.add_arg(lo, -1); v.add_arg(hi, -1); m.emit(v); }
            return v;

        case Nk.NODE_EXPR_TUPLE_LIT:
            return m.lower_aggregate(n, IrOp.IR_TUPLE);
        case Nk.NODE_EXPR_ARRAY_LIT:
            return m.lower_aggregate(n, IrOp.IR_ARRAY);
        case Nk.NODE_EXPR_STRUCT_LIT:
            return m.lower_aggregate(n, IrOp.IR_STRUCT);

        case Nk.NODE_EXPR_ALLOC:
            return m.lower_aggregate(n, IrOp.IR_ALLOC);
        case Nk.NODE_EXPR_FREE:
            return m.lower_aggregate(n, IrOp.IR_FREE);

        case Nk.NODE_EXPR_BLOCK:
            usz mark = m.env_mark();
            IrVal* res = m.lower_block(n);
            m.env_close_block(mark);
            return res;

        case Nk.NODE_EXPR_IF:
            return m.lower_if(n);
        case Nk.NODE_EXPR_MATCH:
            return m.lower_match(n);
        case Nk.NODE_EFFECT_HANDLE:
            return m.lower_handle(n);
        case Nk.NODE_EFFECT_WITH:
            return m.lower_with(n);

        case Nk.NODE_EXPR_WHILE:
            m.lower_while(n);
            return m.mk_unit(n);
        case Nk.NODE_EXPR_LOOP_DO:
            m.lower_do_while(n);
            return m.mk_unit(n);
        case Nk.NODE_EXPR_FOR:
            m.lower_for(n);
            return m.mk_unit(n);

        case Nk.NODE_UB_BANG:
            // ub! — unconditional undefined-behaviour; terminate block as UNREACHABLE.
            {
                IrBlock* ub_b = m.blk(m.cur);
                if (ub_b != null && ub_b.term == TermKind.TERM_NONE)
                    { ub_b.term = TermKind.TERM_UNREACHABLE; }
                int dead_ub = m.new_block();
                m.cur = dead_ub;
                IrBlock* db_ub = m.blk(dead_ub);
                if (db_ub != null) db_ub.term = TermKind.TERM_UNREACHABLE;
            }
            return m.mk_unit(n);

        case Nk.NODE_EXPR_TRANSMUTE:
            // transmute(e) — bit-level reinterpret; lower as IR_CAST (same as `as`).
            {
                IrVal* src = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
                IrVal* v = m.new_val(IrOp.IR_CAST, n);
                if (v != null) { v.add_arg(src, -1); m.emit(v); }
                return v;
            }

        // ── ? operator: propagate Err/None up the call stack ─────────────────
        // Desugaring:
        //   let __try_val = expr;
        //   match __try_val { Ok(v) | Some(v) → v, Err(e) | None → return __try_val }
        // IR: extract discriminant; CBR: 0=Ok/Some→unwrap, else→return-as-is.
        // We emit a simplified version: extractvalue tag; CBR tag==0; phi.
        case Nk.NODE_EXPR_TRY:
            {
                IrVal* inner = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
                if (inner == null) return m.mk_unit(n);

                // Extract tag (field 0 of { i32, i64 } enum repr)
                IrVal* tag_v = m.new_val(IrOp.IR_INDEX, n);
                if (tag_v != null)
                {
                    tag_v.add_arg(inner, -1);
                    tag_v.ival = 0;   // field index 0 = discriminant
                    m.emit(tag_v);
                }
                // CBR: tag == 0 ? ok_blk : err_blk
                IrVal* zero = m.new_val(IrOp.IR_CONST_INT, n);
                if (zero != null) { zero.ival = 0; m.emit(zero); }
                IrVal* is_ok = m.new_val(IrOp.IR_BIN, n);
                if (is_ok != null)
                {
                    is_ok.bop = Tt.TOKEN_EQEQ;
                    is_ok.add_arg(tag_v, -1); is_ok.add_arg(zero, -1);
                    m.emit(is_ok);
                }
                int pre   = m.cur;
                int ok_b  = m.new_block();
                int err_b = m.new_block();
                int join  = m.new_block();
                IrBlock* pb = m.blk(pre);
                if (pb != null) { pb.term = TermKind.TERM_CBR; pb.cond = is_ok; }
                m.link(pre, ok_b);  // true  → ok: extract payload (field 1)
                m.link(pre, err_b); // false → err: early return

                // ok block: extract payload field 1
                m.cur = ok_b;
                IrVal* payload = m.new_val(IrOp.IR_INDEX, n);
                if (payload != null)
                {
                    payload.add_arg(inner, -1); payload.ival = 1;
                    m.emit(payload);
                }
                IrBlock* ob = m.blk(ok_b);
                if (ob != null) { ob.term = TermKind.TERM_BR; m.link(ok_b, join); }

                // err block: return the whole value unchanged (propagate)
                m.cur = err_b;
                m.emit_defers();
                IrBlock* eb = m.blk(err_b);
                if (eb != null) { eb.term = TermKind.TERM_RET; eb.ret_val = inner; }

                // join: phi of payload (ok path) or undef (err path — dead)
                m.cur = join;
                IrVal* rphi = m.new_val(IrOp.IR_PHI, n);
                if (rphi != null)
                {
                    rphi.add_arg(payload, ok_b);
                    m.add_phi(join, rphi);
                }
                return rphi;
            }

        // ── format!(template, args...) ────────────────────────────────────────
        // Desugaring:
        //   str_new() → push literal segments → push formatted args → String
        // The template string is child[0]; args are children[1..].
        // {} in template = next arg; {{}} = literal {. %{type} = typed format.
        case Nk.NODE_EXPR_FORMAT:
            {
                // Find str_new, str_push_str, str_push_i64 in env
                // We lower as a sequence of calls — look up names directly.
                // Strategy: emit IR_CALL nodes to str_new/str_push_str/str_push_i64
                // by finding the fn decls in the module env.

                // For now: create a String via str_new() (IR_CALL)
                // then for each literal segment emit str_push_str
                // then for each {} slot emit str_push_i64 (generic)

                // Lower the format node as an IR_UNKNOWN tagged with NODE_EXPR_FORMAT
                // The codegen then emits the full call sequence.
                IrVal* fmtv = m.new_val(IrOp.IR_UNKNOWN, n);
                if (fmtv != null)
                {
                    // Lower all args (skip child[0] = template literal, already in src)
                    for (usz fi = 1; fi < n.child_count; fi++)
                    {
                        IrVal* av = m.lower_expr(n.children[fi]);
                        if (av != null) fmtv.add_arg(av, -1);
                    }
                    m.emit(fmtv);
                }
                return fmtv;
            }

        // ── tail expr: guaranteed tail call (musttail) ─────────────────────────
        // Mark the inner call value with a special flag so codegen emits musttail.
        case Nk.NODE_EXPR_TAILCALL:
            {
                IrVal* body = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
                // Tag the IR value as a tail call (ival bit 63 = musttail flag)
                if (body != null && body.op == IrOp.IR_CALL)
                {
                    body.ival |= (1UL << 63);  // musttail flag
                    // Mark the block as returned so no join branch is emitted.
                    // The ret instruction will be emitted by codegen inline.
                    IrBlock* tcb = m.blk(m.cur);
                    if (tcb != null && tcb.term == TermKind.TERM_NONE)
                    {
                        tcb.term = TermKind.TERM_RET;
                        tcb.ret_val = body;  // codegen detects musttail on this
                    }
                }
                return body;
            }

        case Nk.NODE_EXPR_UNSAFE:
        case Nk.NODE_EXPR_UNCHECKED:
            // unsafe / unchecked blocks: the flags/effects are already stamped on
            // the AST node by the parser; just lower the body expression unchanged.
            {
                IrVal* body = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
                return body;
            }

        case Nk.NODE_EXPR_POISON:
            // poison — a value that propagates UB if used (v.md §14).
            // Lower as IR_CONST_UNIT tagged with EFFECT_UB; the backend treats
            // any use of a poison value as undefined behaviour.
            {
                IrVal* v = m.new_val(IrOp.IR_CONST_UNIT, n);
                if (v != null) { m.emit(v); }
                return v;
            }

        case Nk.NODE_EXPR_FREEZE:
            // freeze(e) — stops UB propagation: if e is poison, freeze gives an
            // arbitrary but defined value; if e is not poison, freeze is identity.
            // Lower as IR_CAST (identity cast); the backend emits a freeze
            // intrinsic (e.g. LLVM's `freeze` instruction).
            {
                IrVal* src = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
                IrVal* v = m.new_val(IrOp.IR_CAST, n);
                if (v != null) { v.add_arg(src, -1); m.emit(v); }
                return v;
            }

        case Nk.NODE_EXPR_SIZEOF:
            // sizeof(T) — a compile-time constant whose concrete value is the
            // byte-size of T for the target.  Emitted as IR_CONST_INT with ival=0
            // as a sentinel; the backend fills the real size during lowering.
            {
                IrVal* v = m.new_val(IrOp.IR_CONST_INT, n);
                if (v != null) { v.ival = 0; m.emit(v); }
                return v;
            }

        case Nk.NODE_EXPR_ALIGNOF:
            // alignof(T) — same contract as sizeof: IR_CONST_INT ival=0 sentinel.
            {
                IrVal* v = m.new_val(IrOp.IR_CONST_INT, n);
                if (v != null) { v.ival = 0; m.emit(v); }
                return v;
            }

        case Nk.NODE_EXPR_MATMUL:
            // a @ b — tensor/matrix contraction. Lower as IR_BIN with the '@' token.
            {
                IrVal* lhs = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
                IrVal* rhs = m.lower_expr(n.child_count >= 2 ? n.children[1] : null);
                IrVal* v = m.new_val(IrOp.IR_BIN, n);
                if (v != null) { v.bop = Tt.TOKEN_AT; v.add_arg(lhs, -1); v.add_arg(rhs, -1); m.emit(v); }
                return v;
            }

        case Nk.NODE_EXPR_TENSOR_LIT:
            // [| e0, e1, ... |] tensor literal — lower all elements as IR_ARRAY.
            return m.lower_aggregate(n, IrOp.IR_ARRAY);

        case Nk.NODE_EXPR_PIPELINE:
            // x |> f |> g  desugars to  g(f(x)).
            // The AST is left-nested: Pipeline[Pipeline[x, f], g].
            // child[0] = lhs (value flowing in), child[1] = callee.
            // We recurse: lower child[0] to get the accumulated value, then emit
            // an IR_CALL(callee, accumulated).
            {
                IrVal* acc = null;
                IrVal* callee_val = null;
                if (n.child_count >= 1) acc = m.lower_expr(n.children[0]);
                if (n.child_count >= 2) callee_val = m.lower_expr(n.children[1]);
                IrVal* v = m.new_val(IrOp.IR_CALL, n);
                if (v != null)
                {
                    v.add_arg(callee_val, -1);   // args[0] = callee (IR_CALL convention)
                    v.add_arg(acc, -1);           // args[1] = the piped value
                    m.emit(v);
                }
                return v;
            }

        case Nk.NODE_DECL_FN:
            // Nested / local function definition.
            // Defer the actual lowering until after the current outer fn finishes
            // (so blocks don't share IDs). Just create an IR_UNKNOWN fref now.
            {
                // Push to pending list to be lowered after outer fn completes
                if (m.pending_inner_count < 64)
                {
                    m.pending_inner_fns[m.pending_inner_count] = n;
                    m.pending_inner_count++;
                }

                // Create an IR_UNKNOWN reference so calls resolve to @pryde_name
                IrVal* fref = m.new_val(IrOp.IR_UNKNOWN, n);
                if (fref != null)
                {
                    fref.binder = n;
                    m.emit(fref);
                    if (n.child_count >= 1 && n.children[0] != null)
                    {
                        m.env_push(n, fref);
                        m.env_push(n.children[0], fref);
                    }
                }
                return fref;
            }

        default:
            // Anything else: opaque, but still lower children so uses are seen.
            IrVal* v = m.new_val(IrOp.IR_UNKNOWN, n);
            for (usz i = 0; i < n.child_count; i++)
            {
                Node* c = n.children[i];
                if (c == null || ssi::is_type_or_row(c)) continue;
                IrVal* a = m.lower_expr(c);
                if (v != null) v.add_arg(a, -1);
            }
            if (v != null) m.emit(v);
            return v;
    }
}

fn IrVal* SsiModule.lower_aggregate(SsiModule* m, Node* n, IrOp op)
{
    IrVal* v = m.new_val(op, n);
    for (usz i = 0; i < n.child_count; i++)
    {
        Node* c = n.children[i];
        if (c == null || ssi::is_type_or_row(c)) { continue; }
        // Struct literals: child[0] is the type name (TYPEVAR/IDENT/GENERIC_APP) — skip.
        if (op == IrOp.IR_STRUCT && i == 0
            && (c.kind == Nk.NODE_TYPEVAR || c.kind == Nk.NODE_IDENT
                || c.kind == Nk.NODE_TYPE_GENERIC_APP)) { continue; }
        // FIELD_INIT: descend into the value child (child[1]), skip the name.
        if (c.kind == Nk.NODE_FIELD_INIT)
        {
            Node* fval = c.child_count >= 2 ? c.children[1] : null;
            if (fval != null)
            {
                IrVal* a = m.lower_expr(fval);
                if (v != null) { v.add_arg(a, -1); }
            }
            continue;
        }
        IrVal* a = m.lower_expr(c);
        if (v != null) { v.add_arg(a, -1); }
    }
    if (v != null) { m.emit(v); }
    return v;
}

// Block exit: drop block-local lets, but carry out reassignments to OUTER
// binders (so enclosing if/loop merges see them). Mirrors ssi.c3's logic.
fn void SsiModule.env_close_block(SsiModule* m, usz mark)
{
    Node*[256]  cb;
    IrVal*[256] cv;
    usz carry = 0;
    usz i = m.env_count;
    while (i > mark)
    {
        i--;
        Node* b = m.env[i].binder;
        IrVal* v = m.env[i].val;
        bool seen = false;
        for (usz j = 0; j < carry; j++) { if (cb[j] == b) { seen = true; break; } }
        if (seen) continue;
        bool outer = false;
        for (usz k = 0; k < mark; k++) { if (m.env[k].binder == b) { outer = true; break; } }
        if (outer && carry < 256) { cb[carry] = b; cv[carry] = v; carry++; }
    }
    m.env_count = mark;
    for (usz j = 0; j < carry; j++) m.env_push(cb[j], cv[j]);
}

// assignment  x = rhs : evaluate rhs, then rebind x to that value (pure SSA).
fn IrVal* SsiModule.lower_assign(SsiModule* m, Node* n)
{
    Node* lhs = n.child_count >= 1 ? n.children[0] : null;
    Node* rhs = n.child_count >= 2 ? n.children[1] : null;
    IrVal* rv = rhs != null ? m.lower_expr(rhs) : null;

    if (lhs != null && lhs.kind == Nk.NODE_IDENT && lhs.resolved != null)
    {
        if (rv == null) { rv = m.new_val(IrOp.IR_UNKNOWN, n); if (rv != null) m.emit(rv); }
        m.env_push(lhs.resolved, rv);   // override: newest binding wins
        return rv;
    }
    // ── store to pointer deref: *ptr = val ──────────────────────────────────
    if (lhs != null && lhs.kind == Nk.NODE_EXPR_UNARY
        && lhs.child_count >= 1)
    {
        // lhs = UN('*', ptr_expr)
        IrVal* ptr_val = m.lower_expr(lhs.children[0]);
        IrVal* st = m.new_val(IrOp.IR_STORE, n);
        if (st != null)
        {
            st.add_arg(ptr_val, -1);    // args[0] = pointer
            st.add_arg(rv, -1);         // args[1] = value to store
            m.emit(st);
        }
        return rv;
    }
    // ── store to index: arr[i] = val ─────────────────────────────────────────
    if (lhs != null && lhs.kind == Nk.NODE_EXPR_INDEX && lhs.child_count >= 2)
    {
        IrVal* base_val  = m.lower_expr(lhs.children[0]);
        IrVal* index_val = m.lower_expr(lhs.children[1]);
        IrVal* st = m.new_val(IrOp.IR_STORE, n);
        if (st != null)
        {
            st.add_arg(base_val, -1);   // args[0] = array base ptr
            st.add_arg(rv, -1);         // args[1] = value to store
            st.add_arg(index_val, -1);  // args[2] = index
            m.emit(st);
        }
        return rv;
    }
    // ── store to field: s.f = val ─────────────────────────────────────────────
    if (lhs != null && lhs.kind == Nk.NODE_EXPR_FIELD && lhs.child_count >= 1)
    {
        IrVal* base_val = m.lower_expr(lhs.children[0]);
        IrVal* st = m.new_val(IrOp.IR_STORE, n);
        if (st != null)
        {
            st.add_arg(base_val, -1);   // args[0] = struct ptr
            st.add_arg(rv, -1);         // args[1] = value to store
            // field_idx: set ival to the field index (codegen looks up by name from lhs)
            st.ival = -1;               // codegen will re-resolve using lhs.children[1]
            st.src = lhs;               // keep lhs so codegen can find field name
            m.emit(st);
        }
        return rv;
    }
    // ── fallback: unknown lvalue — still evaluate for side effects ────────────
    if (lhs != null) { m.lower_expr(lhs); }
    return rv;
}

// ── if-expression → diamond CFG with σ on edges and φ at the join ────────────
fn IrVal* SsiModule.lower_if(SsiModule* m, Node* n)
{
    if (n.child_count < 1) return m.mk_unit(n);

    Node* cond = n.children[0];
    IrVal* cond_val = m.lower_expr(cond);

    // Locate then / else branches (skip σ/φ markers).
    Node* then_b = null;
    Node* else_b = null;
    for (usz i = 1; i < n.child_count; i++)
    {
        Node* c = n.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_SIGMA || c.kind == Nk.NODE_PHI) continue;
        if (then_b == null) { then_b = c; } else { else_b = c; }
    }

    int b0 = m.cur;
    int then_blk = m.new_block();
    int else_blk = m.new_block();
    int join = m.new_block();

    // Terminate b0 with a conditional branch (succ[0]=true, succ[1]=false).
    IrBlock* pb0 = m.blk(b0);
    if (pb0 != null) { pb0.term = TermKind.TERM_CBR; pb0.cond = cond_val; }
    m.link(b0, then_blk);
    m.link(b0, else_blk);

    usz pre_mark = m.env_mark();

    // ── TRUE edge ────────────────────────────────────────────────────────────
    m.cur = then_blk;
    usz tmark = m.env_mark();
    m.emit_sigmas(cond, true);   // all facts the condition implies on the true edge
    IrVal* then_res = then_b != null ? m.lower_expr(then_b) : m.mk_unit(n);
    int then_end = m.cur;
    Snap then_snap;
    m.capture(tmark, &then_snap);
    bool then_live = !m.terminated();
    if (then_live)
    {
        IrBlock* te = m.blk(then_end);
        if (te != null) { te.term = TermKind.TERM_BR; m.link(then_end, join); }
    }
    m.env_reset(pre_mark);

    // ── FALSE edge ───────────────────────────────────────────────────────────
    m.cur = else_blk;
    usz emark = m.env_mark();
    m.emit_sigmas(cond, false);   // all facts implied on the false (else) edge
    IrVal* else_res = else_b != null ? m.lower_expr(else_b) : m.mk_unit(n);
    int else_end = m.cur;
    Snap else_snap;
    m.capture(emark, &else_snap);
    bool else_live = !m.terminated();
    if (else_live)
    {
        IrBlock* ee = m.blk(else_end);
        if (ee != null) { ee.term = TermKind.TERM_BR; m.link(else_end, join); }
    }
    m.env_reset(pre_mark);

    // ── φ MERGE at the join ──────────────────────────────────────────────────
    m.cur = join;

    // Merge reassigned outer binders. For each binder touched on a live edge,
    // build a φ whose operands are that edge's value (from its end block) and
    // the other edge's value (its branch value if it touched it, else the
    // pre-branch value).
    for (usz i = 0; i < then_snap.count; i++)
    {
        Node* b = then_snap.binders[i];
        if (!m.is_outer(b, pre_mark)) continue;
        IrVal* pre = m.env_lookup(b);
        IrVal* tv = then_snap.vals[i];
        IrVal* ev = find_snap(&else_snap, b);
        if (ev == null) ev = pre;
        IrVal* phi = m.new_val(IrOp.IR_PHI, n);
        if (phi != null)
        {
            phi.binder = b;
            if (then_live) phi.add_arg(tv, then_end);
            if (else_live) phi.add_arg(ev, else_end);
            m.add_phi(join, phi);
            m.env_push(b, phi);
        }
    }
    for (usz i = 0; i < else_snap.count; i++)
    {
        Node* b = else_snap.binders[i];
        if (!m.is_outer(b, pre_mark)) continue;
        if (snap_has(&then_snap, b)) continue;   // already merged
        IrVal* pre = m.env_lookup(b);
        IrVal* ev = else_snap.vals[i];
        IrVal* phi = m.new_val(IrOp.IR_PHI, n);
        if (phi != null)
        {
            phi.binder = b;
            if (then_live) phi.add_arg(pre, then_end);
            if (else_live) phi.add_arg(ev, else_end);
            m.add_phi(join, phi);
            m.env_push(b, phi);
        }
    }

    // The value of the if-expression itself: φ of the two branch results.
    if (then_live && else_live)
    {
        IrVal* rphi = m.new_val(IrOp.IR_PHI, n);
        if (rphi != null)
        {
            rphi.add_arg(then_res, then_end);
            rphi.add_arg(else_res, else_end);
            m.add_phi(join, rphi);
            return rphi;
        }
    }
    if (then_live) return then_res;
    if (else_live) return else_res;
    // Both branches diverged: the join is unreachable.
    IrBlock* jb = m.blk(join);
    if (jb != null && jb.pred_count == 0) jb.term = TermKind.TERM_UNREACHABLE;
    return m.mk_unit(n);
}

// ── match-expression → switch CFG with N arms and an N-way φ at the join ─────
fn IrVal* SsiModule.lower_match(SsiModule* m, Node* n)
{
    if (n.child_count < 1) return m.mk_unit(n);
    Node* scrut = n.children[0];
    IrVal* sval = m.lower_expr(scrut);

    int b0 = m.cur;
    IrBlock* pb0 = m.blk(b0);
    if (pb0 != null) { pb0.term = TermKind.TERM_SWITCH; pb0.cond = sval; }

    int join = -1;   // created lazily once we know an arm reaches it

    // default successor (slot 0) — a trap block if no wildcard arm appears.
    int default_blk = m.new_block();
    m.link(b0, default_blk);
    IrBlock* db = m.blk(default_blk);
    if (db != null) db.term = TermKind.TERM_UNREACHABLE;
    bool default_filled = false;

    usz pre_mark = m.env_mark();

    // Accumulate, across arms, each outer binder's per-arm reaching value (for
    // the N-way φ) plus per-arm result values. All heap-allocated and sized to
    // the actual arm count, so arbitrarily wide matches (thousands of arms) work
    // without overflowing any fixed cap or the native stack.
    usz arm_cap = n.child_count;   // ≥ number of arms (extra slack for markers)
    if (arm_cap == 0) arm_cap = 1;
    Snap* arm_snaps = (Snap*)malloc(arm_cap * Snap::size);
    IrVal** arm_results = (IrVal**)malloc(arm_cap * IrValPtr::size);
    int* arm_ends = (int*)malloc(arm_cap * int::size);
    bool* arm_live = (bool*)malloc(arm_cap * bool::size);
    usz narm = 0;
    if (arm_snaps == null || arm_results == null || arm_ends == null || arm_live == null)
    {
        if (arm_snaps != null) free(arm_snaps);
        if (arm_results != null) free(arm_results);
        if (arm_ends != null) free(arm_ends);
        if (arm_live != null) free(arm_live);
        return m.mk_unit(n);
    }

    for (usz i = 1; i < n.child_count; i++)
    {
        Node* arm = n.children[i];
        if (arm == null || arm.kind != Nk.NODE_MATCH_ARM) continue;
        if (narm >= arm_cap) break;

        Node* pat = arm.child_count >= 1 ? arm.children[0] : null;
        bool is_wild = pat != null && pat.kind == Nk.NODE_PATTERN_WILDCARD;

        int arm_blk = m.new_block();
        // Wildcard / ident-binding arm becomes the default; literal arms are cases.
        if (is_wild || (pat != null && pat.kind == Nk.NODE_PATTERN_IDENT))
        {
            // route default edge here
            if (db != null && !default_filled)
            {
                db.term = TermKind.TERM_NONE;
                // redirect: make default_blk an empty forwarder to arm_blk
                db.term = TermKind.TERM_BR;
                m.link(default_blk, arm_blk);
                default_filled = true;
            }
            else { m.link(b0, arm_blk); }
        }
        else
        {
            int slot = m.link(b0, arm_blk);
            // record case label if the pattern is an int literal
            if (slot >= 0 && pb0 != null && pat != null && pat.kind == Nk.NODE_PATTERN_LITERAL
                && pat.child_count >= 1 && pat.children[0] != null
                && pat.children[0].kind == Nk.NODE_LIT_INT)
            {
                pb0.case_has[slot] = true;
                pb0.case_val[slot] = pat.children[0].p.lit_int.int_val;
            }
            // Range pattern:  lo..hi or lo..=hi
            // Emitted as CBR chain: (scrut >= lo && scrut <= hi) ? arm : default
            // For switch lowering we lower range patterns as fallback CBR chains.
            if (slot >= 0 && pb0 != null && pat != null && pat.kind == Nk.NODE_PATTERN_RANGE
                && pat.child_count >= 2)
            {
                // Range patterns use CBR not SWITCH — re-route this arm through a
                // dedicated guard block. The switch dispatch stays for literal arms.
                // (Full integration with SWITCH is deferred; here we use the existing
                //  CBR infrastructure by checking the range inline before the arm.)
                pb0.case_has[slot] = false;  // not a single-value case
            }
        }

        m.cur = arm_blk;
        usz amark = m.env_mark();
        // bind pattern idents
        m.bind_pattern(null, pat);
        // σ-refine the scrutinee for literal arms (we learn scrut == literal).
        if (pat != null && pat.kind == Nk.NODE_PATTERN_LITERAL && scrut != null
            && scrut.kind == Nk.NODE_IDENT && scrut.resolved != null
            && pat.child_count >= 1)
        {
            IrVal* cur = m.env_lookup(scrut.resolved);
            IrVal* sg = m.new_val(IrOp.IR_SIGMA, pat);
            if (sg != null)
            {
                sg.binder = scrut.resolved;
                sg.refinement = m.mk_refinement(Tt.TOKEN_EQEQ, pat.children[0], pat.line, pat.col);
                sg.add_arg(cur, -1);
                m.emit(sg);
                m.env_push(scrut.resolved, sg);
            }
        }

        // arm body (children after pattern, skipping guard markers)
        IrVal* res = null;
        for (usz j = 1; j < arm.child_count; j++)
        {
            Node* c = arm.children[j];
            if (c == null || c.kind == Nk.NODE_PATTERN_GUARD) continue;
            res = m.lower_expr(c);
        }
        if (res == null) res = m.mk_unit(arm);

        Snap asnap;
        m.capture(amark, &asnap);
        bool live = !m.terminated();
        arm_snaps[narm] = asnap;
        arm_results[narm] = res;
        arm_ends[narm] = m.cur;
        arm_live[narm] = live;
        if (live)
        {
            if (join < 0) join = m.new_block();
            IrBlock* ae = m.blk(m.cur);
            if (ae != null) { ae.term = TermKind.TERM_BR; m.link(m.cur, join); }
        }
        narm++;
        m.env_reset(pre_mark);
    }

    if (join < 0)
    {
        // Every arm diverged.
        free(arm_snaps); free(arm_results); free(arm_ends); free(arm_live);
        return m.mk_unit(n);
    }
    m.cur = join;

    // N-way φ for each outer binder reassigned by any live arm.
    Snap merged;
    merged.count = 0;
    for (usz a = 0; a < narm; a++)
    {
        if (!arm_live[a]) continue;
        Snap* s = &arm_snaps[a];
        for (usz k = 0; k < s.count; k++)
        {
            Node* b = s.binders[k];
            if (!m.is_outer(b, pre_mark)) continue;
            if (snap_has(&merged, b)) continue;
            // Build one φ over all live arms for this binder.
            IrVal* phi = m.new_val(IrOp.IR_PHI, n);
            if (phi == null) continue;
            phi.binder = b;
            IrVal* pre = m.env_lookup(b);
            for (usz a2 = 0; a2 < narm; a2++)
            {
                if (!arm_live[a2]) continue;
                IrVal* av = find_snap(&arm_snaps[a2], b);
                if (av == null) av = pre;
                phi.add_arg(av, arm_ends[a2]);
            }
            m.add_phi(join, phi);
            m.env_push(b, phi);
            if (merged.count < SCAN_CAP) { merged.binders[merged.count] = b; merged.count++; }
        }
    }

    // Result φ of all live arm results.
    IrVal* rphi = m.new_val(IrOp.IR_PHI, n);
    if (rphi != null)
    {
        for (usz a = 0; a < narm; a++)
        {
            if (!arm_live[a]) continue;
            rphi.add_arg(arm_results[a], arm_ends[a]);
        }
        m.add_phi(join, rphi);
        free(arm_snaps); free(arm_results); free(arm_ends); free(arm_live);
        return rphi;
    }
    free(arm_snaps); free(arm_results); free(arm_ends); free(arm_live);
    return m.mk_unit(n);
}

// Push a loop context, allocating the break-value matrix. Returns the matrix
// pointer (which the caller frees after building exit φs), or null on overflow.
// Register a named label for the NEXT push_loop call (call before push_loop).
fn void SsiModule.push_loop_label(SsiModule* m, char* name, usz nlen)
{
    if (m.loop_label_count >= 64) return;
    usz idx = m.loop_label_count;
    m.loop_label_name[idx] = name;
    m.loop_label_nlen[idx] = nlen;
    // The loop stack index for this label is the NEXT loop to be pushed.
    m.loop_label_idx[idx] = m.loop_count;
    m.loop_label_count++;
}

// Find a LoopCtx* by label name. Returns null if not found.
fn LoopCtx* SsiModule.find_loop_by_label(SsiModule* m, char* name, usz nlen)
{
    for (usz li = 0; li < m.loop_label_count; li++)
    {
        if (m.loop_label_nlen[li] != nlen) continue;
        bool eq = true;
        for (usz ci = 0; ci < nlen; ci++)
        { if (m.loop_label_name[li][ci] != name[ci]) { eq = false; break; } }
        if (eq)
        {
            usz stack_idx = m.loop_label_idx[li];
            if (stack_idx < m.loop_count) return &m.loops[stack_idx];
        }
    }
    return null;
}

fn IrVal** SsiModule.push_loop(SsiModule* m, int header, int exit, IrVal** hdr_phis, Node** hdr_binders, usz nphi)
{
    if (m.loop_count >= LOOP_CAP) { m.overflow = true; return null; }
    // Auto-register pending label (set by caller before push_loop).
    if (m.pending_label_name != null)
    {
        m.push_loop_label(m.pending_label_name, m.pending_label_nlen);
        m.pending_label_name = null;
        m.pending_label_nlen = 0;
    }
    LoopCtx* lc = &m.loops[m.loop_count];
    m.loop_count++;
    lc.header = header;
    lc.exit = exit;
    lc.hdr_phis = hdr_phis;
    lc.hdr_binders = hdr_binders;
    lc.nphi = nphi;
    lc.break_count = 0;
    lc.break_vals = null;
    if (nphi > 0)
    {
        lc.break_vals = (IrVal**)malloc(MAX_BREAKS * nphi * IrValPtr::size);
    }
    else
    {
        // still allocate a 1-slot matrix so break sites can be recorded
        lc.break_vals = (IrVal**)malloc(MAX_BREAKS * 1 * IrValPtr::size);
    }
    return lc.break_vals;
}

fn LoopCtx SsiModule.pop_loop(SsiModule* m)
{
    LoopCtx done;
    done.break_count = 0;
    done.nphi = 0;
    done.break_vals = null;
    if (m.loop_count > 0)
    {
        m.loop_count--;
        done = m.loops[m.loop_count];
        // Remove any label entry pointing to this stack index.
        usz new_lc = 0;
        for (usz li = 0; li < m.loop_label_count; li++)
        {
            if (m.loop_label_idx[li] != m.loop_count)
            {
                m.loop_label_name[new_lc] = m.loop_label_name[li];
                m.loop_label_nlen[new_lc] = m.loop_label_nlen[li];
                m.loop_label_idx[new_lc]  = m.loop_label_idx[li];
                new_lc++;
            }
        }
        m.loop_label_count = new_lc;
    }
    return done;
}

// At a loop exit, install each loop-carried binder's post-loop value. With no
// breaks it is simply the header φ. With breaks, it is a φ in the exit block
// merging the normal-exit value (header φ) with each break-site value.
fn IrVal* SsiModule.build_exit_phis(SsiModule* m, Node* n, int exit, int header, LoopCtx* done, IrVal** hdr_phis, Node** hdr_binders, usz nphi)
{
    IrBlock* xb = m.blk(exit);
    bool has_breaks = done.break_count > 0;
    for (usz i = 0; i < nphi; i++)
    {
        if (!has_breaks)
        {
            m.env_push(hdr_binders[i], hdr_phis[i]);
            continue;
        }
        // exit φ: normal-exit (from header, false edge) + each break site.
        IrVal* phi = m.new_val(IrOp.IR_PHI, n);
        if (phi == null) { m.env_push(hdr_binders[i], hdr_phis[i]); continue; }
        phi.binder = hdr_binders[i];
        phi.add_arg(hdr_phis[i], header);
        for (usz bk = 0; bk < done.break_count; bk++)
        {
            IrVal* bv = done.break_vals[bk * done.nphi + i];
            if (bv == null) bv = hdr_phis[i];
            phi.add_arg(bv, done.break_blk[bk]);
        }
        m.add_phi(exit, phi);
        m.env_push(hdr_binders[i], phi);
    }
    // Build result phi if any break carried a value
    if (done != null && done.break_count > 0)
    {
        bool any_res = false;
        for (usz bk = 0; bk < done.break_count; bk++)
        { if (done.break_result[bk] != null) { any_res = true; break; } }
        if (any_res)
        {
            IrVal* rphi = m.new_val(IrOp.IR_PHI, n);
            if (rphi != null)
            {
                for (usz bk = 0; bk < done.break_count; bk++)
                {
                    IrVal* rv = done.break_result[bk];
                    if (rv == null) rv = m.mk_unit(n);
                    rphi.add_arg(rv, done.break_blk[bk]);
                }
                m.add_phi(exit, rphi);
                return rphi;
            }
        }
    }
    return null;
}

// ============================================================================
// Algebraic Effects Lowering
// ============================================================================
//
// STRATEGY — "structured handler frames" (backend-agnostic)
// ──────────────────────────────────────────────────────────
// We lower effect constructs into three dedicated IR opcodes without CPS-
// transforming the SSA-CFG.  The SSA structure (φ/σ, verified dominance) is
// fully preserved.  The backend picks its own ABI:
//
//   • VM / interpreter      → handler record on an explicit effect stack
//   • LLVM (simple)         → setjmp/longjmp-based unwinding per handler frame
//   • LLVM (efficient)      → Leijen-style evidence passing (Koka ABI)
//   • Cranelift / Wasm      → block-argument continuation passing
//   • Native w/ split stack → OCaml 5 / Multicore continuation capture
//
// The IR encodes:
//
//   IR_EFFECT_OP   — "perform Effect.op(args...)"
//     .binder → the effect op declaration (NODE_EFFECT_OP_DECL), giving the
//               op identity (effect name + op name) for handler dispatch.
//     args    → the op's argument values.
//
//   IR_HANDLER     — "handle computation { | Op(args) k → arm_body }"
//     args[0]   → the computation result (value of the handled expression).
//     args[1..] → IR_HANDLER_ARM values, one per arm.
//     .binder   → the NODE_EFFECT_HANDLE node (for effect identity lookup).
//     Semantically: install a handler frame covering args[0]'s computation,
//     dispatch each performed op to its matching arm.
//
//   IR_HANDLER_ARM — one dispatch arm (linked into IR_HANDLER)
//     args[0]  → the arm body's result value.
//     .binder  → the NODE_HANDLER_ARM node (for op-head identity lookup).
//     The arm's op-argument binders are IR_PARAMs emitted into the arm's block.
//
//   IR_RESUME      — "resume(v)" inside a handler arm
//     args[0]  → the value to resume the suspended computation with.
//     .binder  → the NODE_HANDLER_ARM this resume belongs to.
//     Semantically: transfer control back to the effect-op call site with v.
//
// "with r = resource { body }" is desugared entirely at IR level:
//   let r = resource; result = body; [cleanup if needed]
// No new IrOp needed — it becomes IR_CALL + block nesting.
//
// ── Effect-op perform (NODE_EXPR_METHOD_CALL on an effect decl) ──────────────
//
// An effect-operation call `Effect.op(arg0, arg1, ...)` arrives as
// NODE_EXPR_METHOD_CALL[EffectTypeVar, op_ident, arg0, arg1, ...].
// child[0].resolved → NODE_DECL_EFFECT (the effect declaration).
//
// We detect this shape and emit IR_EFFECT_OP instead of IR_CALL.

fn bool is_effect_method_call(Node* n)
{
    if (n == null) return false;
    if (n.kind != Nk.NODE_EXPR_METHOD_CALL) return false;
    if (n.child_count < 1) return false;
    Node* base = n.children[0];
    return (base != null && base.resolved != null
            && base.resolved.kind == Nk.NODE_DECL_EFFECT);
}

fn Node* effect_op_decl_of(Node* method_call)
{
    // child[0] = effect typevar, child[1] = op ident
    if (method_call.child_count < 2) return null;
    Node* op_ident = method_call.children[1];
    if (op_ident == null) return null;
    // The op ident resolves to the NODE_EFFECT_OP_DECL.
    // (The resolver links it; if not resolved, .binder stays null — still safe.)
    return op_ident.resolved;
}

fn IrVal* SsiModule.lower_effect_perform(SsiModule* m, Node* n)
{
    // Find the op declaration for the .binder field.
    Node* op_decl = effect_op_decl_of(n);

    IrVal* v = m.new_val(IrOp.IR_EFFECT_OP, n);
    if (v != null) { v.binder = op_decl; }

    // Lower op arguments: skip child[0] (effect typevar) and child[1] (op ident).
    for (usz i = 2; i < n.child_count; i++)
    {
        Node* c = n.children[i];
        if (c == null || ssi::is_type_or_row(c)) { continue; }
        IrVal* a = m.lower_expr(c);
        if (v != null) { v.add_arg(a, -1); }
    }
    if (v != null) { m.emit(v); }
    return v;
}

// ── Handler arm lowering ──────────────────────────────────────────────────────
//
// Each handler arm NODE_HANDLER_ARM[op_head, binder0, ..., binderN, body] is
// lowered into a fresh block:
//
//   arm_blk:
//     p0 = param   ← first op argument
//     p1 = param   ← second op argument  (0..N matching the op signature)
//     k  = param   ← the continuation (resume target)
//     <body instructions>
//     ret arm_result
//
// The IR_HANDLER_ARM value (in the join block) carries args[0] = the arm's
// result so the IR_HANDLER can φ-merge all arm results.

// arm_blk must be pre-created by the caller (lower_handle) so that the
// dispatch block's SWITCH edges are correctly established before lowering.
fn IrVal* SsiModule.lower_handler_arm(SsiModule* m, Node* arm, int arm_blk, int join)
{
    m.cur = arm_blk;

    // arm children: [op_head_field, binder0, ..., binderN, body]
    // child[0]       = op head (Field[EffectTypeVar, op_ident]) — no value needed
    // children[1..N] = argument binders (PatIdent) + the continuation binder
    // child[last]    = arm body

    usz last = arm.child_count >= 1 ? arm.child_count - 1 : 0;
    Node* body_node = arm.child_count >= 1 ? arm.children[last] : null;

    // Emit IR_PARAMs for each binder (op args + continuation k).
    for (usz i = 1; i < last; i++)
    {
        Node* binder = arm.children[i];
        if (binder == null) { continue; }
        IrVal* pv = m.new_val(IrOp.IR_PARAM, binder);
        if (pv != null)
        {
            pv.binder = arm;   // tag with arm node so codegen can detect arm params
            m.emit(pv);
        }
        // Bind into env so the body can reference op args and k by name.
        m.bind_let_pattern(binder, pv);
    }

    // Lower the arm body.
    IrVal* body_val = null;
    if (body_node != null) { body_val = m.lower_expr(body_node); }
    if (body_val == null)  { body_val = m.mk_unit(arm); }

    // Terminate the arm block and jump to the handler join block.
    if (!m.terminated())
    {
        IrBlock* ab = m.blk(arm_blk);
        if (ab != null) { ab.term = TermKind.TERM_BR; }
        m.link(arm_blk, join);
    }

    // Emit the IR_HANDLER_ARM value into the arm block so it is formally
    // "defined" in the SSA-CFG sense.  This value carries the arm identity
    // and its result; the IR_HANDLER in the join block references it.
    IrVal* arm_val = m.new_val(IrOp.IR_HANDLER_ARM, arm);
    if (arm_val != null)
    {
        arm_val.binder = arm;
        arm_val.add_arg(body_val, -1);
        m.emit(arm_val);   // defined in arm_blk (current block)
    }

    return arm_val;
}

// ── handle expression lowering ────────────────────────────────────────────────
//
// NODE_EFFECT_HANDLE[computation, HandlerArm, HandlerArm, ...]
//
// CFG produced:
//
//   pre_blk:
//     comp_val = lower(computation)   ← may contain IR_EFFECT_OP nodes
//     br join_blk
//   arm_blk_0:
//     p0 = param  ...
//     <arm 0 body>
//     br join_blk
//   arm_blk_1:
//     ...
//     br join_blk
//   join_blk:
//     handler_result = effect.handle(comp_val, arm0_val, arm1_val, ...)
//
// The IR_HANDLER node is the value of the whole expression. Each IR_HANDLER_ARM
// child identifies which op it handles (via .binder → NODE_HANDLER_ARM) and
// carries the arm's result value.

fn IrVal* SsiModule.lower_handle(SsiModule* m, Node* n)
{
    // child[0] is the computation; children[1..] are HandlerArm nodes.
    Node* comp = n.child_count >= 1 ? n.children[0] : null;

    int pre_blk  = m.cur;
    int dispatch = m.new_block();   // handler dispatch: switch → each arm block
    int join     = m.new_block();   // result join: phi over arm results + normal exit

    // ── Lower the computation in the entry block ──────────────────────────────
    IrVal* comp_val = comp != null ? m.lower_expr(comp) : m.mk_unit(n);

    // Terminate pre_blk → dispatch (unconditional: install handler frame, run
    // computation, then dispatch any performed op to an arm, or fall through).
    if (!m.terminated())
    {
        IrBlock* pb = m.blk(m.cur);
        if (pb != null) { pb.term = TermKind.TERM_BR; }
        m.link(m.cur, dispatch);
    }

    // ── Build dispatch block: SWITCH cond → {normal_exit (default), arm0, arm1, ...}
    // The IR_HANDLER value IS the switch condition: the backend interprets it as
    // "which (if any) effect op was performed during the computation".
    // succ[0] = join (default / normal-exit path: computation finished cleanly)
    // succ[k] = arm_blk_k (op k was performed: dispatch to handler arm k)
    m.cur = dispatch;
    IrVal* handler_cond = m.new_val(IrOp.IR_HANDLER, n);
    if (handler_cond != null)
    {
        handler_cond.binder = n;
        handler_cond.add_arg(comp_val, -1);
        m.emit(handler_cond);
    }

    IrBlock* db = m.blk(dispatch);
    if (db != null) { db.term = TermKind.TERM_SWITCH; db.cond = handler_cond; }
    m.link(dispatch, join);   // succ[0] = default = normal exit (no op performed)

    // ── Lower each handler arm into its own block ─────────────────────────────
    IrVal*[32] arm_vals;
    usz narms = 0;

    for (usz i = 1; i < n.child_count && narms < 32; i++)
    {
        Node* arm = n.children[i];
        if (arm == null || arm.kind != Nk.NODE_HANDLER_ARM) { continue; }

        // Create the arm block and add it as a SWITCH case successor of dispatch.
        int arm_blk = m.new_block();
        m.link(dispatch, arm_blk);   // dispatch → arm_blk (case edge, no label needed)

        // Lower the arm body into arm_blk.
        IrVal* av = m.lower_handler_arm(arm, arm_blk, join);
        arm_vals[narms] = av;
        narms++;
    }

    // ── Emit IR_HANDLER_ARM values and join block ─────────────────────────────
    // The IR_HANDLER value carries: args[0] = comp_val, args[1..] = arm values.
    // We already emitted handler_cond (the dispatch condition) with only comp_val.
    // Now add the arm values to it.
    if (handler_cond != null)
    {
        for (usz i = 0; i < narms; i++)
        {
            handler_cond.add_arg(arm_vals[i], -1);
        }
    }

    // In the join block: the result is the handler value (resolved by the backend
    // to whichever path actually ran — the computation's normal return or an arm).
    m.cur = join;
    return handler_cond;
}

// ── resume(v) inside a handler arm ───────────────────────────────────────────
//
// `resume` is bound by the resolver as a name in every handler-arm scope
// (resolve.c3: `self.bind("resume", 6, NS_VALUE, arm, false)`). So `resume(v)`
// arrives as NODE_EXPR_CALL[IDENT("resume"→arm_node), arg].
//
// We detect this by checking whether the callee ident resolves to a
// NODE_HANDLER_ARM and emit IR_RESUME instead of IR_CALL.

fn bool is_resume_call(Node* n)
{
    if (n == null || n.kind != Nk.NODE_EXPR_CALL) return false;
    if (n.child_count < 1) return false;
    Node* callee = n.children[0];
    if (callee == null) return false;
    return (callee.resolved != null
            && callee.resolved.kind == Nk.NODE_HANDLER_ARM);
}

fn IrVal* SsiModule.lower_resume(SsiModule* m, Node* n)
{
    // callee child[0] → arm node (.binder)
    Node* callee = n.child_count >= 1 ? n.children[0] : null;
    Node* arm_node = (callee != null) ? callee.resolved : null;

    IrVal* v = m.new_val(IrOp.IR_RESUME, n);
    if (v != null) { v.binder = arm_node; }

    // Lower the resume argument (child[1] when present, else unit).
    IrVal* arg = null;
    if (n.child_count >= 2)
    {
        arg = m.lower_expr(n.children[1]);
    }
    else
    {
        arg = m.mk_unit(n);
    }
    if (v != null) { v.add_arg(arg, -1); m.emit(v); }
    return v;
}

// ── with resource body ────────────────────────────────────────────────────────
//
// NODE_EFFECT_WITH[Assign[lhs_ident, resource_expr], body]
//   or
// NODE_EFFECT_WITH[resource_expr, body]
//
// Semantics: evaluate the resource, optionally bind it to a name, execute the
// body, then release the resource (if it has a Drop/cleanup — not enforced at
// IR level; the backend handles RAII via destructor calls).
//
// IR lowering:
//   pre_blk:
//     resource_val = lower(resource_expr)
//     [bind lhs_ident → resource_val in env]
//   body_blk:
//     result = lower(body)
//     [cleanup: lower resource's Drop if present — emitted as IR_UNKNOWN for now]
//   join:
//     ret result

fn IrVal* SsiModule.lower_with(SsiModule* m, Node* n)
{
    if (n.child_count < 1) { return m.mk_unit(n); }

    Node* first = n.children[0];
    Node* body  = n.child_count >= 2 ? n.children[1] : null;

    IrVal* resource_val = null;

    // Form 1: `with r = resource { body }` → first is ASSIGN[lhs, rhs]
    if (first != null && first.kind == Nk.NODE_EXPR_ASSIGN && first.child_count >= 2)
    {
        Node* lhs = first.children[0];
        Node* rhs = first.children[1];
        resource_val = rhs != null ? m.lower_expr(rhs) : m.mk_unit(n);
        // Bind the with-binder into env. The resolver binds `r` with decl = the ASSIGN node
        // (first), so body references to `r` have r.resolved = first (the ASSIGN node).
        // We also try lhs.resolved as a fallback for any alternate resolver strategy.
        m.env_push(first, resource_val);       // key = ASSIGN node (what body_r.resolved is)
        if (lhs != null && lhs.resolved != null)
        {
            m.env_push(lhs.resolved, resource_val);  // fallback: key = whatever lhs resolves to
        }
    }
    // Form 2: `with resource { body }` → first is the resource expression
    else
    {
        resource_val = m.lower_expr(first);
    }

    // Lower the body.
    IrVal* result = body != null ? m.lower_expr(body) : m.mk_unit(n);

    // Emit a cleanup placeholder: IR_UNKNOWN carrying the resource, tagged so
    // the backend can insert the Drop/release call. The backend recognises this
    // by checking n.kind == NODE_EFFECT_WITH on the src node.
    IrVal* cleanup = m.new_val(IrOp.IR_UNKNOWN, n);
    if (cleanup != null && resource_val != null)
    {
        cleanup.add_arg(resource_val, -1);
        m.emit(cleanup);
    }

    return result;
}

// ── do-while loop → body executes once before the first condition check ───────
//
// CFG shape:
//   pre → body_blk → header(cond) -cbr→ {body_blk (back-edge), exit}
//
// This is the textbook do-while SSA shape: the body block is also the loop's
// "pre" — it executes unconditionally on the first iteration, and the header
// (condition test) re-enters it on subsequent iterations.  Break/continue work
// the same way as in while-loops: continue jumps to the header, break jumps to
// exit.
// do { body } while (cond)
// SSA structure:
//   pre → body_blk(φ) → cond_blk → body_blk (loop) or exit
// φ nodes are placed in body_blk with predecessors pre (entry) and cond_blk (back-edge).
fn void SsiModule.lower_do_while(SsiModule* m, Node* n)
{
    Node* body = n.child_count >= 1 ? n.children[0] : null;
    Node* cond = n.child_count >= 2 ? n.children[1] : null;

    int pre      = m.cur;
    int body_blk = m.new_block();
    int cond_blk = m.new_block();
    int exit     = m.new_block();

    // pre → body_blk (unconditional fall-through)
    IrBlock* pb = m.blk(pre);
    if (pb != null) { pb.term = TermKind.TERM_BR; m.link(pre, body_blk); }

    // Pre-scan body for binders it reassigns — needed for φ placement.
    Snap assigned;
    assigned.count = 0;
    if (body != null) collect_assigned(body, &assigned);

    usz pre_mark = m.env_mark();

    // Place φ nodes at the TOP of body_blk.
    // Each φ has two incoming edges: pre (first iteration) and cond_blk (back-edge).
    m.cur = body_blk;
    IrVal*[SCAN_CAP] hdr_phis;
    Node*[SCAN_CAP]  hdr_binders;
    IrVal*[SCAN_CAP] entry_vals;
    usz nphi = 0;
    for (usz i = 0; i < assigned.count; i++)
    {
        Node* b = assigned.binders[i];
        IrVal* entry_val = m.env_lookup(b);
        if (entry_val == null) continue;
        IrVal* phi = m.new_val(IrOp.IR_PHI, n);
        if (phi == null) continue;
        phi.binder = b;
        phi.add_arg(entry_val, pre);   // edge from pre (first iteration)
        // back-edge operand (from cond_blk) added after body is lowered
        m.add_phi(body_blk, phi);
        m.env_push(b, phi);            // phi is live in body + condition
        if (nphi < SCAN_CAP)
        { hdr_phis[nphi] = phi; hdr_binders[nphi] = b; entry_vals[nphi] = entry_val; nphi++; }
    }

    // Lower the body (runs in body_blk, phi values visible).
    usz bmark = m.env_mark();
    IrVal** break_vals = m.push_loop(cond_blk, exit, &hdr_phis[0], &hdr_binders[0], nphi);
    if (body != null) m.lower_stmt(body);
    LoopCtx done = m.pop_loop();

    int body_end = m.cur;
    // body_blk (body_end) → cond_blk
    if (!m.terminated())
    {
        IrBlock* be = m.blk(body_end);
        if (be != null) { be.term = TermKind.TERM_BR; m.link(body_end, cond_blk); }
        // Complete φ back-edge operands: value at end of body.
        // The φ is in body_blk; its predecessor on the back-edge is cond_blk
        // (because cond_blk → body_blk is the back-edge branch).
        for (usz i = 0; i < nphi; i++)
        {
            IrVal* back = m.env_lookup(hdr_binders[i]);
            if (back == null) back = entry_vals[i];
            hdr_phis[i].add_arg(back, cond_blk);
        }
    }
    m.env_reset(bmark);

    // Evaluate condition in cond_blk; back-edge φ values are still in env.
    m.cur = cond_blk;
    IrVal* cond_val = cond != null ? m.lower_expr(cond) : null;
    IrBlock* hb = m.blk(cond_blk);
    if (hb != null) { hb.term = TermKind.TERM_CBR; hb.cond = cond_val; }
    m.link(cond_blk, body_blk);   // true  → loop back
    m.link(cond_blk, exit);       // false → exit

    m.env_reset(pre_mark);
    m.cur = exit;
    m.build_exit_phis(n, exit, cond_blk, &done, &hdr_phis[0], &hdr_binders[0], nphi);
    if (break_vals != null) free(break_vals);
}

// ── while-loop → header φ + back-edge (textbook loop SSA) ────────────────────
fn void SsiModule.lower_while(SsiModule* m, Node* n)
{
    Node* cond = n.child_count >= 1 ? n.children[0] : null;
    Node* body = n.child_count >= 2 ? n.children[1] : null;

    int pre = m.cur;
    int header = m.new_block();
    int body_blk = m.new_block();
    int exit = m.new_block();

    // entry → header
    IrBlock* pb = m.blk(pre);
    if (pb != null) { pb.term = TermKind.TERM_BR; m.link(pre, header); }

    // Pre-place header φ for every binder the body reassigns.
    Snap assigned;
    assigned.count = 0;
    if (body != null) collect_assigned(body, &assigned);

    usz pre_mark = m.env_mark();
    m.cur = header;
    IrVal*[SCAN_CAP] hdr_phis;
    Node*[SCAN_CAP]  hdr_binders;
    IrVal*[SCAN_CAP] entry_vals;
    usz nphi = 0;
    for (usz i = 0; i < assigned.count; i++)
    {
        Node* b = assigned.binders[i];
        IrVal* entry_val = m.env_lookup(b);
        if (entry_val == null) continue;   // not an outer binder → loop-local
        IrVal* phi = m.new_val(IrOp.IR_PHI, n);
        if (phi == null) continue;
        phi.binder = b;
        phi.add_arg(entry_val, pre);        // entry edge
        m.add_phi(header, phi);
        m.env_push(b, phi);                 // header value within the loop
        if (nphi < SCAN_CAP)
        {
            hdr_phis[nphi] = phi;
            hdr_binders[nphi] = b;
            entry_vals[nphi] = entry_val;
            nphi++;
        }
    }

    // condition (reads header φ values) — terminate header with CBR.
    IrVal* cond_val = cond != null ? m.lower_expr(cond) : null;
    IrBlock* hb = m.blk(header);
    if (hb != null) { hb.term = TermKind.TERM_CBR; hb.cond = cond_val; }
    m.link(header, body_blk);   // true → body
    m.link(header, exit);       // false → exit

    // σ on the true edge (loop guard facts) and false edge (negated), emitted
    // at the body / exit block heads.

    // body: the guard held → refine accordingly (multi-fact)
    m.cur = body_blk;
    m.emit_sigmas(cond, true);
    // loop context for break/continue (aliases the header-φ arrays so the
    // break/continue handlers can extend them).
    IrVal** break_vals = m.push_loop(header, exit, &hdr_phis[0], &hdr_binders[0], nphi);
    if (body != null) m.lower_stmt(body);
    LoopCtx done = m.pop_loop();

    int body_end = m.cur;
    // back-edge: complete header φ operands with each binder's body-final value.
    if (!m.terminated())
    {
        IrBlock* be = m.blk(body_end);
        if (be != null) { be.term = TermKind.TERM_BR; m.link(body_end, header); }
        for (usz i = 0; i < nphi; i++)
        {
            IrVal* back = m.env_lookup(hdr_binders[i]);
            if (back == null) back = entry_vals[i];
            hdr_phis[i].add_arg(back, body_end);
        }
    }

    // exit: σ for the negated guard; install header φ as the post-loop value.
    // If the loop had `break`s, each loop-carried binder's post-loop value is a
    // φ merging the normal-exit value (the header φ) with every break value.
    m.env_reset(pre_mark);
    m.cur = exit;
    m.build_exit_phis(n, exit, header, &done, &hdr_phis[0], &hdr_binders[0], nphi);
    if (break_vals != null) free(break_vals);
    // exit: the guard failed → refine with the negated facts (multi-fact)
    m.emit_sigmas(cond, false);
}

// ── for-loop → header φ + back-edge, with a fresh per-iteration binder ───────
fn void SsiModule.lower_for(SsiModule* m, Node* n)
{
    Node* binder = n.child_count >= 1 ? n.children[0] : null;
    Node* iter   = n.child_count >= 2 ? n.children[1] : null;
    Node* body   = n.child_count >= 3 ? n.children[2] : null;

    // Detect integer-range iterator: `for i in lo..hi` / `for i in lo..=hi`.
    // When iter is NODE_EXPR_RANGE we emit a proper counter φ and bounds check
    // (IR_BIN '<' or '<=') instead of the opaque IR_UNKNOWN "has-next".
    bool is_range = (iter != null && iter.kind == Nk.NODE_EXPR_RANGE);

    IrVal* iter_val = iter != null ? m.lower_expr(iter) : null;

    // For a range, extract lo/hi from the IR_RANGE value's operands.
    IrVal* range_lo = null;
    IrVal* range_hi = null;
    if (is_range && iter_val != null && iter_val.op == IrOp.IR_RANGE
        && iter_val.arg_count >= 2)
    {
        range_lo = iter_val.args[0];
        range_hi = iter_val.args[1];
    }
    else
    {
        is_range = false;
    }

    int pre      = m.cur;
    int header   = m.new_block();
    int body_blk = m.new_block();
    int exit     = m.new_block();

    IrBlock* pb = m.blk(pre);
    if (pb != null) { pb.term = TermKind.TERM_BR; m.link(pre, header); }

    Snap assigned;
    assigned.count = 0;
    if (body != null) collect_assigned(body, &assigned);

    usz pre_mark = m.env_mark();
    m.cur = header;
    IrVal*[SCAN_CAP] hdr_phis;
    Node*[SCAN_CAP]  hdr_binders;
    IrVal*[SCAN_CAP] entry_vals;
    usz nphi = 0;

    // Counter φ for range loops (placed first so break/continue see it).
    IrVal* counter_phi = null;
    if (is_range && range_lo != null)
    {
        counter_phi = m.new_val(IrOp.IR_PHI, n);
        if (counter_phi != null)
        {
            counter_phi.binder = binder;
            counter_phi.add_arg(range_lo, pre);
            m.add_phi(header, counter_phi);
            if (nphi < SCAN_CAP)
            {
                hdr_phis[nphi]    = counter_phi;
                hdr_binders[nphi] = binder;
                entry_vals[nphi]  = range_lo;
                nphi++;
            }
        }
    }

    // Outer-binder φs (same as while-loop).
    for (usz i = 0; i < assigned.count; i++)
    {
        Node* b = assigned.binders[i];
        if (is_range && b == binder) { continue; }  // counter_phi covers this
        IrVal* entry_val = m.env_lookup(b);
        if (entry_val == null) { continue; }
        IrVal* phi = m.new_val(IrOp.IR_PHI, n);
        if (phi == null) { continue; }
        phi.binder = b;
        phi.add_arg(entry_val, pre);
        m.add_phi(header, phi);
        m.env_push(b, phi);
        if (nphi < SCAN_CAP)
        {
            hdr_phis[nphi]    = phi;
            hdr_binders[nphi] = b;
            entry_vals[nphi]  = entry_val;
            nphi++;
        }
    }

    // Header terminator: real bounds check or opaque has-next.
    IrVal* test = null;
    if (is_range && counter_phi != null && range_hi != null)
    {
        bool inclusive = (iter != null
                          && (iter.flags & ast::FLAG_RANGE_INCLUSIVE) != 0);
        test = m.new_val(IrOp.IR_BIN, iter);
        if (test != null)
        {
            test.bop = inclusive ? Tt.TOKEN_LTEQ : Tt.TOKEN_LT;
            test.add_arg(counter_phi, -1);
            test.add_arg(range_hi, -1);
            m.emit(test);
        }
    }
    else
    {
        test = m.new_val(IrOp.IR_UNKNOWN, n);
        if (test != null && iter_val != null) { test.add_arg(iter_val, -1); m.emit(test); }
    }

    IrBlock* hb = m.blk(header);
    if (hb != null) { hb.term = TermKind.TERM_CBR; hb.cond = test; }
    m.link(header, body_blk);
    m.link(header, exit);

    // Body.
    m.cur = body_blk;
    usz bmark = m.env_mark();
    if (is_range && counter_phi != null)
    {
        // Loop variable = current counter (the φ, not a fresh IR_PARAM).
        if (binder != null) { m.bind_let_pattern(binder, counter_phi); }
    }
    else if (binder != null)
    {
        IrVal* iv = m.new_val(IrOp.IR_PARAM, binder);
        if (iv != null) { m.emit(iv); m.bind_let_pattern(binder, iv); }
    }
    IrVal** break_vals = m.push_loop(header, exit, &hdr_phis[0], &hdr_binders[0], nphi);
    if (body != null) { m.lower_stmt(body); }
    LoopCtx done = m.pop_loop();

    int body_end = m.cur;
    if (!m.terminated())
    {
        // Range back-edge: emit counter + 1 before closing the body env.
        IrVal* back_counter = null;
        if (is_range && counter_phi != null)
        {
            IrVal* one = m.new_val(IrOp.IR_CONST_INT, n);
            if (one != null) { one.ival = 1; m.emit(one); }
            back_counter = m.new_val(IrOp.IR_BIN, n);
            if (back_counter != null)
            {
                back_counter.bop = Tt.TOKEN_PLUS;
                back_counter.add_arg(counter_phi, -1);
                back_counter.add_arg(one, -1);
                m.emit(back_counter);
            }
        }

        IrBlock* be = m.blk(body_end);
        if (be != null) { be.term = TermKind.TERM_BR; m.link(body_end, header); }

        for (usz i = 0; i < nphi; i++)
        {
            IrVal* back = null;
            if (is_range && hdr_phis[i] == counter_phi)
            {
                back = back_counter;
            }
            else
            {
                back = m.env_lookup(hdr_binders[i]);
            }
            if (back == null) { back = entry_vals[i]; }
            hdr_phis[i].add_arg(back, body_end);
        }
    }
    m.env_reset(bmark);

    m.env_reset(pre_mark);
    m.cur = exit;
    m.build_exit_phis(n, exit, header, &done, &hdr_phis[0], &hdr_binders[0], nphi);
    if (break_vals != null) { free(break_vals); }
}

// ============================================================================
// Verification (well-formedness invariants of the constructed IR)
// ============================================================================
// ── φ-pruning pass ───────────────────────────────────────────────────────────
// Removes trivial φ-nodes: those with a single unique non-self operand.
// All uses of the trivial φ are replaced with that single operand.
// Repeat until stable (cascading trivials).
//
// A φ is trivial if, ignoring self-references, all args are the same value v.
// Replace φ with v everywhere: in other args arrays and in env.
//
// Complexity: O(vals * passes) per function, bounded by small constant passes.

// ── Dead block elimination ───────────────────────────────────────────────────
// Mark blocks reachable from entry via BFS; unreachable blocks are marked
// TERM_UNREACHABLE and have their phi operands referencing them removed.
// This is called after lowering so `break`/`continue` dead code is cleaned.

fn int SsiModule.eliminate_dead_blocks(SsiModule* m, SsiFunc* f)
{
    if (f.block_count == 0) return 0;
    int first = f.block_start;
    int last  = f.block_start + (int)f.block_count;

    // Reachability bitmap: one bit per block in [first, last).
    usz bmap_sz = ((usz)f.block_count + 63) / 64;
    ulong* reach = (ulong*)malloc(bmap_sz * 8);
    if (reach == null) return 0;
    for (usz i = 0; i < bmap_sz; i++) reach[i] = 0;

    // BFS worklist (simple stack — block ids).
    int* wl = (int*)malloc((usz)f.block_count * 4);
    if (wl == null) { free(reach); return 0; }
    usz wl_head = 0; usz wl_tail = 0;

    // Mark entry block reachable.
    usz rel = (usz)(f.entry - first);
    if (f.entry >= first && f.entry < last)
    {
        reach[rel/64] |= (1UL << (rel%64));
        wl[wl_tail++] = f.entry;
    }

    while (wl_head < wl_tail)
    {
        int bid = wl[wl_head++];
        IrBlock* b = m.blk(bid);
        if (b == null) continue;
        for (usz si = 0; si < b.succ_count; si++)
        {
            int s = b.succ[si];
            if (s < first || s >= last) continue;
            usz srel = (usz)(s - first);
            if (reach[srel/64] & (1UL << (srel%64))) continue;  // already visited
            reach[srel/64] |= (1UL << (srel%64));
            if (wl_tail < (usz)f.block_count) wl[wl_tail++] = s;
        }
    }
    free(wl);

    // For each unreachable block: mark unreachable, remove its phis from
    // successor phi lists.
    int dead_count = 0;
    for (int bid = first; bid < last; bid++)
    {
        usz brel = (usz)(bid - first);
        if (reach[brel/64] & (1UL << (brel%64))) continue;
        IrBlock* db = m.blk(bid);
        if (db == null) continue;
        dead_count++;
        // Remove phi operands from successors that reference this dead block.
        for (usz si = 0; si < db.succ_count; si++)
        {
            IrBlock* sb = m.blk(db.succ[si]);
            if (sb == null) continue;
            IrVal* phi = sb.phi_head;
            while (phi != null)
            {
                // Compact out operands arriving from dead block bid.
                usz new_ac = 0;
                for (usz ai = 0; ai < phi.arg_count; ai++)
                {
                    if (phi.pred[ai] == bid) continue; // drop this operand
                    phi.args[new_ac] = phi.args[ai];
                    phi.pred[new_ac] = phi.pred[ai];
                    new_ac++;
                }
                phi.arg_count = new_ac;
                phi = phi.next;
            }
        }
        // Mark dead block itself as unreachable so codegen skips it.
        db.term = TermKind.TERM_UNREACHABLE;
        db.phi_head = null; db.phi_tail = null;
        db.head = null; db.tail = null;
        db.succ_count = 0;
        db.pred_count = 0;
    }
    free(reach);
    return dead_count;
}

// ── Loop-invariant code motion ───────────────────────────────────────────────
// Hoists IR values that are loop-invariant out of loop bodies.
// Strategy: for each natural loop header block (a block that dominates a back-
// edge predecessor), find instructions in the loop body whose operands are all
// defined outside the loop. Move those instructions to the pre-header block.
//
// We detect natural loops by checking block dominance. For simplicity we use
// the existing phi-at-header pattern: any block B has a back-edge B→H if H
// appears in B.succ and H has phi nodes (loop header markers).

// Check if a value is defined outside the loop body.
// "loop body" = any block in [body_start, body_end] inclusive.
fn bool val_is_loop_invariant(IrVal* v, int body_start, int body_end, SsiModule* m)
{
    if (v == null) return true;
    // Constants and params are always invariant.
    if (v.op == IrOp.IR_CONST_INT   || v.op == IrOp.IR_CONST_FLOAT ||
        v.op == IrOp.IR_CONST_BOOL  || v.op == IrOp.IR_CONST_NULL  ||
        v.op == IrOp.IR_CONST_UNIT  || v.op == IrOp.IR_CONST_STR   ||
        v.op == IrOp.IR_PARAM) return true;
    // A value defined in a block outside the loop body is invariant.
    return (v.block < body_start || v.block > body_end);
}

// Returns true if op has no side effects (pure for LICM purposes).
fn bool op_is_pure_for_licm(IrOp op)
{
    switch (op)
    {
        case IrOp.IR_BIN:
        case IrOp.IR_UN:
        case IrOp.IR_CAST:
        case IrOp.IR_SIGMA:
            return true;
        default:
            return false;
    }
}

// LICM for one function. Returns count of hoisted instructions.
fn int SsiModule.hoist_loop_invariants(SsiModule* m, SsiFunc* f)
{
    if (f.block_count < 3) return 0;   // need at least pre/header/body
    int first = f.block_start;
    int last  = f.block_start + (int)f.block_count;
    int hoisted = 0;

    // Find natural loop back-edges: block B has successor H, H has phis.
    // Pre-header for H is the block that branches to H from outside.
    for (int hid = first; hid < last; hid++)
    {
        IrBlock* hb = m.blk(hid);
        if (hb == null || hb.phi_head == null) continue;  // not a loop header

        // Find back-edge predecessors: pred of H whose block id > H
        // (in a forward-numbered CFG, back-edges go to smaller ids).
        // Also find the pre-header: the pred of H with smallest id < H.
        int pre_header = -1;
        int back_pred  = -1;
        for (usz pi = 0; pi < hb.pred_count; pi++)
        {
            int pred = hb.pred[pi];
            if (pred >= hid) { back_pred = pred; }      // back-edge
            else if (pred < hid) { pre_header = pred; } // forward edge = pre-header
        }
        if (pre_header < 0 || back_pred < 0) continue;  // not a simple natural loop

        // Loop body: blocks in (pre_header, back_pred] (rough approximation).
        int body_start = hid;       // header itself is part of the body
        int body_end   = back_pred;
        if (body_start > body_end) continue;

        // Scan body blocks for hoistable instructions.
        for (int bid = body_start; bid <= body_end; bid++)
        {
            IrBlock* bb = m.blk(bid);
            if (bb == null) continue;
            IrVal* prev = null;
            IrVal* iv   = bb.head;
            while (iv != null)
            {
                IrVal* next = iv.next;
                if (!op_is_pure_for_licm(iv.op)) { prev = iv; iv = next; continue; }
                // Check all operands are loop-invariant.
                bool all_inv = true;
                for (usz ai = 0; ai < iv.arg_count; ai++)
                {
                    if (!val_is_loop_invariant(iv.args[ai], body_start, body_end, m))
                    { all_inv = false; break; }
                }
                if (!all_inv) { prev = iv; iv = next; continue; }

                // Hoist: unlink from current block, append to pre-header.
                if (prev == null) { bb.head = next; }
                else { prev.next = next; }
                if (bb.tail == iv) bb.tail = prev;

                IrBlock* phb = m.blk(pre_header);
                if (phb != null)
                {
                    iv.next  = null;
                    iv.block = pre_header;
                    if (phb.tail == null) { phb.head = iv; phb.tail = iv; }
                    else { phb.tail.next = iv; phb.tail = iv; }
                }
                hoisted++;
                // prev stays the same; next becomes the new current.
                iv = next;
            }
        }
    }
    return hoisted;
}

// ── Critical edge splitting ──────────────────────────────────────────────────
// A critical edge is an edge A→B where A has ≥2 succs AND B has ≥2 preds.
// Splitting inserts a new empty block C between A and B (A→C→B).
// This is required for correct σ insertion and for many optimizations.
// We only split edges where B has phi nodes (otherwise it's not needed).

fn int SsiModule.split_critical_edges(SsiModule* m, SsiFunc* f)
{
    if (f.block_count == 0) return 0;
    int first = f.block_start;
    int last  = f.block_start + (int)f.block_count;
    int splits = 0;

    // Collect edges to split (don't modify during iteration).
    // Each entry: { from_block, to_block_succ_slot }
    int* from_blks  = (int*)malloc((usz)f.block_count * MAX_EDGES * 4);
    int* succ_slots = (int*)malloc((usz)f.block_count * MAX_EDGES * 4);
    if (from_blks == null || succ_slots == null)
    {
        if (from_blks  != null) free(from_blks);
        if (succ_slots != null) free(succ_slots);
        return 0;
    }
    usz edge_count = 0;

    for (int bid = first; bid < last; bid++)
    {
        IrBlock* ab = m.blk(bid);
        if (ab == null || ab.succ_count < 2) continue;  // A must have ≥2 succs
        for (usz si = 0; si < ab.succ_count; si++)
        {
            int btarget = ab.succ[si];
            IrBlock* bb = m.blk(btarget);
            if (bb == null || bb.pred_count < 2) continue;  // B must have ≥2 preds
            if (bb.phi_head == null) continue;              // only if B has phis
            if (edge_count < (usz)f.block_count * MAX_EDGES)
            {
                from_blks[edge_count]  = bid;
                succ_slots[edge_count] = (int)si;
                edge_count++;
            }
        }
    }

    // Now split each identified critical edge.
    for (usz ei = 0; ei < edge_count; ei++)
    {
        int a = from_blks[ei];
        int slot = succ_slots[ei];
        IrBlock* ab = m.blk(a);
        if (ab == null || slot >= (int)ab.succ_count) continue;
        int b = ab.succ[slot];
        IrBlock* bb = m.blk(b);
        if (bb == null) continue;

        // Create new block C (the split block).
        int c_id = m.new_block();
        IrBlock* cb = m.blk(c_id);
        if (cb == null) continue;
        cb.term = TermKind.TERM_BR;

        // Rewire A→C: update A's succ slot (already done — A.succ[slot] was b).
        ab.succ[slot] = c_id;

        // Rewire C→B: add B to C's succ and C to B's pred — but WITHOUT
        // duplicating.  We do this manually instead of m.link() to control
        // exactly what gets into pred/succ lists.
        if (grow_succ(cb))
        {
            cb.succ[cb.succ_count] = b;
            cb.case_has[cb.succ_count] = false;
            cb.case_val[cb.succ_count] = 0;
            cb.succ_count++;
        }

        // B's pred list currently has A.  Replace that A entry with C
        // (one replacement only — no new entry needed).
        bool replaced_in_b = false;
        for (usz pi = 0; pi < bb.pred_count; pi++)
        {
            if (bb.pred[pi] == a && !replaced_in_b)
            {
                bb.pred[pi] = c_id;
                replaced_in_b = true;
                // don't break — only replace first occurrence
            }
        }
        // If A appeared multiple times in B.pred (parallel edges), leave
        // extras as-is for now; they are rare and harmless after phi fix.

        // C's pred = {A}
        if (grow_pred(cb)) { cb.pred[cb.pred_count] = a; cb.pred_count++; }

        // Fix phi predecessors in B: references to A become C.
        IrVal* phi = bb.phi_head;
        while (phi != null)
        {
            for (usz ai = 0; ai < phi.arg_count; ai++)
            { if (phi.pred[ai] == a) { phi.pred[ai] = c_id; break; } }
            phi = phi.next;
        }

        f.block_count++;  // account for the new block
        splits++;
    }
    free(from_blks);
    free(succ_slots);
    return splits;
}

fn void replace_phi_uses(SsiModule* m, IrVal* phi, IrVal* replacement)
{
    if (phi == null || replacement == null) return;
    // Walk all blocks in the current function and replace phi in arg arrays.
    for (usz bid = 0; bid < m.block_count; bid++)
    {
        IrBlock* b = &m.blocks[bid];
        // phi list
        IrVal* pv = b.phi_head;
        while (pv != null)
        {
            for (usz ai = 0; ai < pv.arg_count; ai++)
            { if (pv.args[ai] == phi) pv.args[ai] = replacement; }
            pv = pv.next;
        }
        // instruction list
        IrVal* iv = b.head;
        while (iv != null)
        {
            for (usz ai = 0; ai < iv.arg_count; ai++)
            { if (iv.args[ai] == phi) iv.args[ai] = replacement; }
            iv = iv.next;
        }
        // terminator condition
        if (b.cond == phi) b.cond = replacement;
        if (b.ret_val == phi) b.ret_val = replacement;
    }
}

fn bool is_trivial_phi(IrVal* phi)
{
    if (phi == null || phi.op != IrOp.IR_PHI) return false;
    IrVal* unique = null;
    for (usz i = 0; i < phi.arg_count; i++)
    {
        IrVal* a = phi.args[i];
        if (a == phi) continue;          // self-reference: skip
        if (unique == null) { unique = a; continue; }
        if (unique != a) return false;   // two distinct non-self operands
    }
    return true;   // 0 or 1 unique non-self operands
}

fn IrVal* trivial_phi_val(IrVal* phi)
{
    for (usz i = 0; i < phi.arg_count; i++)
    { if (phi.args[i] != phi && phi.args[i] != null) return phi.args[i]; }
    return null;   // degenerate 0-arg phi
}

// Prune trivial phis for a function's blocks [block_start, block_start+count).
// Called after lowering completes but before SASI / codegen.
fn int SsiModule.prune_trivial_phis(SsiModule* m, SsiFunc* f)
{
    int pruned_total = 0;
    bool changed = true;
    while (changed)
    {
        changed = false;
        int last = f.block_start + f.block_count;
        for (int bid = f.block_start; bid < last; bid++)
        {
            IrBlock* b = m.blk(bid);
            if (b == null) continue;
            IrVal* prev_phi = null;
            IrVal* phi = b.phi_head;
            while (phi != null)
            {
                IrVal* next = phi.next;
                if (is_trivial_phi(phi))
                {
                    IrVal* rep = trivial_phi_val(phi);
                    if (rep == null) rep = m.mk_unit(phi.src);
                    replace_phi_uses(m, phi, rep);
                    // Unlink from phi list
                    if (prev_phi == null) { b.phi_head = next; }
                    else { prev_phi.next = next; }
                    if (b.phi_tail == phi) b.phi_tail = prev_phi;
                    pruned_total++;
                    changed = true;
                    // Don't update prev_phi — next iteration needs the same prev
                }
                else { prev_phi = phi; }
                phi = next;
            }
        }
    }
    return pruned_total;
}

struct VerifyResult
{
    int blocks;
    int vals;
    int phis;
    int sigmas;
    int edges;
    int errors;
    int undef_refs;     // operands referencing an undefined SSA value (must be 0)
    int effect_ops;     // IR_EFFECT_OP  (perform) sites
    int effect_handles; // IR_HANDLER    (handle) sites
    int effect_resumes; // IR_RESUME     (resume) sites
}

// A value is inherently defined (no block instruction needed) if it is a
// constant, a parameter, or a σ handle (defined by the SASI side-map).
fn bool inherently_defined(IrVal* v)
{
    if (v == null) return true;   // null operand is "absent", not undefined
    switch (v.op)
    {
        case IrOp.IR_CONST_INT:
        case IrOp.IR_CONST_FLOAT:
        case IrOp.IR_CONST_BOOL:
        case IrOp.IR_CONST_STR:
        case IrOp.IR_CONST_NULL:
        case IrOp.IR_CONST_UNIT:
        case IrOp.IR_PARAM:
        case IrOp.IR_SIGMA:
            return true;
        default:
            return false;
    }
}

// Check: every reachable, non-unreachable block has a terminator; every φ has
// one operand per predecessor edge of its block; succ/pred are symmetric.
fn VerifyResult SsiModule.verify(SsiModule* m)
{
    VerifyResult r;
    r.blocks = (int)m.block_count;
    r.vals = (int)m.val_count;
    r.phis = 0;
    r.sigmas = 0;
    r.edges = 0;
    r.errors = 0;
    r.undef_refs = 0;
    r.effect_ops = 0;
    r.effect_handles = 0;
    r.effect_resumes = 0;

    // Definedness bitset: a value is "defined" if it physically appears in some
    // block's instruction/φ list (its def site). Constants/params/σ are
    // inherently defined. Operands referencing anything else are dangling.
    usz nval = m.val_count;
    bool* defined = null;
    if (nval > 0)
    {
        defined = (bool*)malloc(nval * bool::size);
        if (defined != null)
        {
            for (usz i = 0; i < nval; i++) defined[i] = false;
            for (usz bi = 0; bi < m.block_count; bi++)
            {
                IrBlock* b = &m.blocks[bi];
                IrVal* ph = b.phi_head;
                while (ph != null) { if (ph.id >= 0 && (usz)ph.id < nval) defined[ph.id] = true; ph = ph.next; }
                IrVal* in = b.head;
                while (in != null) { if (in.id >= 0 && (usz)in.id < nval) defined[in.id] = true; in = in.next; }
            }
        }
    }

    for (usz bi = 0; bi < m.block_count; bi++)
    {
        IrBlock* b = &m.blocks[bi];
        r.edges += (int)b.succ_count;

        // terminator present (unless explicitly unreachable)
        if (b.term == TermKind.TERM_NONE && b.term != TermKind.TERM_UNREACHABLE)
        {
            // An open block with no successors and no terminator is only OK if
            // it is the trivially-empty tail of a diverged region; flag it.
            r.errors++;
        }

        // succ/pred symmetry
        for (usz s = 0; s < b.succ_count; s++)
        {
            int to = b.succ[s];
            IrBlock* bt = m.blk(to);
            if (bt == null) { r.errors++; continue; }
            bool found = false;
            for (usz p = 0; p < bt.pred_count; p++) { if (bt.pred[p] == b.id) { found = true; break; } }
            if (!found) r.errors++;
        }

        // φ operand count == predecessor count (each pred contributes one value)
        IrVal* ph = b.phi_head;
        while (ph != null)
        {
            r.phis++;
            if (ph.arg_count != b.pred_count && b.pred_count > 0) r.errors++;
            // each operand's pred must be an actual predecessor
            for (usz k = 0; k < ph.arg_count; k++)
            {
                int pe = ph.pred[k];
                bool ok = false;
                for (usz p = 0; p < b.pred_count; p++) { if (b.pred[p] == pe) { ok = true; break; } }
                if (!ok) r.errors++;
                if (defined != null) r.undef_refs += operand_undef(defined, nval, ph.args[k]);
            }
            ph = ph.next;
        }

        // count σ, effect ops + check straight-line operands are defined
        IrVal* in = b.head;
        while (in != null)
        {
            if (in.op == IrOp.IR_SIGMA)         r.sigmas++;
            if (in.op == IrOp.IR_EFFECT_OP)     r.effect_ops++;
            if (in.op == IrOp.IR_HANDLER)       r.effect_handles++;
            if (in.op == IrOp.IR_RESUME)        r.effect_resumes++;
            if (defined != null)
            {
                for (usz k = 0; k < in.arg_count; k++) r.undef_refs += operand_undef(defined, nval, in.args[k]);
            }
            in = in.next;
        }

        // terminator operands (cond / ret) must also be defined
        if (defined != null)
        {
            r.undef_refs += operand_undef(defined, nval, b.cond);
            r.undef_refs += operand_undef(defined, nval, b.ret_val);
        }
    }
    r.errors += r.undef_refs;
    if (defined != null) free((void*)defined);
    return r;
}

// 1 if `v` is a real value reference that is NOT defined anywhere (dangling).
fn int operand_undef(bool* defined, usz nval, IrVal* v)
{
    if (v == null) return 0;
    if (inherently_defined(v)) return 0;
    if (v.id < 0 || (usz)v.id >= nval) return 1;
    return defined[v.id] ? 0 : 1;
}

// ============================================================================
// Pretty-printer (textual SSI-IR dump)
// ============================================================================
fn char* irop_name(IrOp op)
{
    switch (op)
    {
        case IR_CONST_INT:   return "const.int";
        case IR_CONST_FLOAT: return "const.float";
        case IR_CONST_BOOL:  return "const.bool";
        case IR_CONST_STR:   return "const.str";
        case IR_CONST_NULL:  return "const.null";
        case IR_CONST_UNIT:  return "unit";
        case IR_PARAM:       return "param";
        case IR_BIN:         return "bin";
        case IR_UN:          return "un";
        case IR_CALL:        return "call";
        case IR_FIELD:       return "field";
        case IR_INDEX:       return "index";
        case IR_CAST:        return "cast";
        case IR_TUPLE:       return "tuple";
        case IR_ARRAY:       return "array";
        case IR_STRUCT:      return "struct";
        case IR_ALLOC:       return "alloc";
        case IR_FREE:        return "free";
        case IR_RANGE:       return "range";
        case IR_PHI:         return "phi";
        case IR_SIGMA:       return "sigma";
        case IR_EFFECT_OP:   return "effect.op";
        case IR_HANDLER:     return "effect.handle";
        case IR_HANDLER_ARM: return "effect.arm";
        case IR_RESUME:      return "effect.resume";
        case IR_UNKNOWN:     return "opaque";
        default:             return "?";
    }
}

fn char* term_name(TermKind t)
{
    switch (t)
    {
        case TERM_NONE:        return "<open>";
        case TERM_RET:         return "ret";
        case TERM_BR:          return "br";
        case TERM_CBR:         return "cbr";
        case TERM_SWITCH:      return "switch";
        case TERM_UNREACHABLE: return "unreachable";
        default:               return "?";
    }
}

fn void print_binder_name(Node* binder)
{
    if (binder == null) { return; }
    Node* nm = binder.child_count >= 1 ? binder.children[0] : binder;
    if (nm != null && (nm.kind == Nk.NODE_IDENT || nm.kind == Nk.NODE_TYPEVAR || nm.kind == Nk.NODE_PATTERN_IDENT))
    {
        if (nm.kind == Nk.NODE_PATTERN_IDENT && nm.child_count >= 1) nm = nm.children[0];
        if (nm != null && nm.kind == Nk.NODE_IDENT)
        {
            for (usz i = 0; i < nm.p.ident.name_len; i++) printf("%c", nm.p.ident.name_ptr[i]);
        }
    }
}

fn void print_val_ref(IrVal* v)
{
    if (v == null) { printf("_"); return; }
    printf("v%d", v.id);
}

fn void SsiModule.print_val(SsiModule* m, IrVal* v, char* lead)
{
    if (v == null) return;
    printf("%sv%-4d = %s", lead, v.id, irop_name(v.op));
    switch (v.op)
    {
        case IR_CONST_INT:   printf(" %llu", v.ival);
        case IR_CONST_BOOL:  printf(" %s", v.bval ? "true" : "false");
        case IR_BIN:
        case IR_UN:          printf(" '%s'", lexer::token_type_name(v.bop));
        default:             break;
    }
    if (v.binder != null) { printf(" {"); print_binder_name(v.binder); printf("}"); }
    if (v.arg_count > 0)
    {
        printf(" (");
        for (usz i = 0; i < v.arg_count; i++)
        {
            if (i > 0) printf(", ");
            print_val_ref(v.args[i]);
            if (v.op == IrOp.IR_PHI) printf("@B%d", v.pred[i]);
        }
        printf(")");
    }
    if (v.refinement != null)
    {
        printf("  refined:(%s)", lexer::token_type_name(v.refinement.p.op.op));
    }
    printf("\n");
}

fn void SsiModule.dump(SsiModule* m)
{
    printf("\n=== SSI-IR (%llu funcs, %llu blocks, %llu values) ===\n",
        (ulong)m.func_count, (ulong)m.block_count, (ulong)m.val_count);

    for (usz fi = 0; fi < m.func_count; fi++)
    {
        SsiFunc* f = &m.funcs[fi];
        printf("\nfn ");
        if (f.name != null) { for (usz i = 0; i < f.name_len; i++) printf("%c", f.name[i]); }
        else { printf("<anon>"); }
        printf("  (entry B%d, %d blocks)\n", f.entry, f.block_count);

        int last = f.block_start + f.block_count;
        for (int bid = f.block_start; bid < last; bid++)
        {
            IrBlock* b = m.blk(bid);
            if (b == null) continue;
            printf("  B%d:", b.id);
            if (b.pred_count > 0)
            {
                printf("   ; preds:");
                for (usz p = 0; p < b.pred_count; p++) printf(" B%d", b.pred[p]);
            }
            printf("\n");

            // φ-nodes
            IrVal* ph = b.phi_head;
            while (ph != null) { m.print_val(ph, "    "); ph = ph.next; }
            // straight-line
            IrVal* in = b.head;
            while (in != null) { m.print_val(in, "    "); in = in.next; }
            // terminator
            printf("    %s", term_name(b.term));
            switch (b.term)
            {
                case TERM_RET:
                    if (b.ret_val != null) { printf(" "); print_val_ref(b.ret_val); }
                case TERM_BR:
                    if (b.succ_count >= 1) printf(" B%d", b.succ[0]);
                case TERM_CBR:
                    printf(" "); print_val_ref(b.cond);
                    if (b.succ_count >= 2) printf(" ? B%d : B%d", b.succ[0], b.succ[1]);
                case TERM_SWITCH:
                    printf(" "); print_val_ref(b.cond); printf(" [");
                    for (usz s = 0; s < b.succ_count; s++)
                    {
                        if (s > 0) printf(", ");
                        if (b.case_has[s]) { printf("%llu=>B%d", b.case_val[s], b.succ[s]); }
                        else { printf("default=>B%d", b.succ[s]); }
                    }
                    printf("]");
                default:
                    break;
            }
            printf("\n");
        }
    }
}
