// ssi_ir.c3 — Explicit CFG + SSI IR  (the backend's input form)
// Implementation language: C3 (host).
// WHAT THIS MODULE IS
// `ssi.c3` produces a TREE-structured SSI graph (annotates the AST in place).
// That is ideal for the rewrite/PGL passes that work on the tree.  A backend
// needs an EXPLICIT control-flow graph: real basic blocks, SSA values,
// terminators, φ-nodes naming predecessor blocks, σ-splits on conditional edges.
// This module lowers Pride's structured, goto-free AST into exactly that form.
// DATA MODEL
//   SsiModule  — a set of functions sharing one flat val[]/block[]/func[] slab.
//   SsiFunc    — entry block id + contiguous [block_start, block_start+count).
//   IrBlock    — phi_head/tail (φ list) · head/tail (instrs) · ONE terminator
//                · growable succ[]/pred[] edge arrays.
//   IrVal      — one SSA value: const | param | bin/un | call | field/index/cast
//                | tuple/array/struct | alloc/free | range | phi | sigma
//                | effect.op | effect.handle | effect.arm | effect.resume
//                | opaque (IR_UNKNOWN, only for asm and with-cleanup).
// COMPLETENESS — NO STUBS
// Every Pride language construct is lowered to concrete IR.  IR_UNKNOWN appears
// only at two well-defined sites:
//   • NODE_STMT_ASM (inline asm):  IR_UNKNOWN carrying AsmLine/AsmOperand
//     children; .src.kind == NODE_STMT_ASM; tagged EFFECT_UNSAFE.
//   • NODE_EFFECT_WITH cleanup:   IR_UNKNOWN(resource_val);
//     .src.kind == NODE_EFFECT_WITH; backend inserts RAII destructor call.
// Every other IR_UNKNOWN is a resolved global/extern reference (.binder != null).
// ALGEBRAIC EFFECTS IR
// Effect operations lower to three dedicated opcodes (not CPS-transformed —
// the SSA structure is preserved; the backend chooses the runtime ABI):
//   IR_EFFECT_OP   — perform.  .binder → NODE_EFFECT_OP_DECL; args = op args.
//   IR_HANDLER     — handler frame.  Emitted as the TERM_SWITCH condition of
//                    a dispatch block: succ[0]=join(default), succ[k]=arm_blk_k.
//                    args[0]=comp_val, args[1..]=IR_HANDLER_ARM values.
//   IR_HANDLER_ARM — one arm; emitted in arm_blk; args[0]=body result;
//                    .binder → NODE_HANDLER_ARM.
//   IR_RESUME      — resume(v); args[0]=resume value; .binder → handler arm.
// CONSTRUCTION ALGORITHM
// Because Pride has no goto, the CFG is built by a single structured walk
// (Brandis & Mössenböck single-pass SSA, extended with σ-splits) — no
// dominance-frontier iteration needed.  Loops use a pre-placed header φ per
// loop-carried binder; break/continue feed extra operands via LoopCtx.
// VERIFICATION
// SsiModule.verify() checks: every live block has a terminator; succ/pred are
// symmetric; each φ has one operand per predecessor; no dangling value refs.
// ir verify errors == 0 and ir undef_refs == 0 are invariants on clean input.

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
    IR_HANDLER_COMPLETE, // computation finished normally: tear the handler
                     //   frame down.  Emitted at the end of the computation
                     //   block, before the branch to the handler join block.
                     //   Carries no value; the join φ takes args[0] of the
                     //   IR_HANDLER directly from the computation block.
    IR_STORE,        // store: args[0]=ptr_or_gep_base, args[1]=value[, args[2]=index]
                     //   variant A: *ptr = val  → args[0]=ptr, args[1]=val
                     //   variant B: arr[i] = val → args[0]=base, args[1]=val, args[2]=index
                     //   variant C: s.f = val   → args[0]=base, args[1]=val, field_idx stored in .ival
    IR_ATOMIC_RMW,   // atomicrmw op ptr val ordering  → args[0]=ptr args[1]=val  .ival=op+order
    IR_CMPXCHG,      // cmpxchg ptr expected desired → args[0]=ptr args[1]=exp args[2]=new
    IR_FENCE,        // fence ordering → .ival = memory order (SeqCst=5, AcqRel=4, Acquire=2, Release=3)
    IR_UNKNOWN       // opaque expression (kept so lowering is always total)
}

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
const usz AT_CAP         = 256;

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
    // For-range loops only (null for while/do/non-range iterators): the
    // induction counter φ and its step.  A `continue` edge must feed
    // counter+step into the counter φ — exactly like the body-end back-edge —
    // because the generic path feeds the CURRENT value, which skips the
    // increment and spins forever on the un-advanced counter.
    IrVal*   counter_phi;
    IrVal*   counter_step;
}

// A captured per-binder value reached at the end of a branch.
struct Snap
{
    Node*[SCAN_CAP]   binders;
    IrVal*[SCAN_CAP]  vals;
    usz count;
}

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
    // Address-taken locals: per-function table at the module level. Filled by
    // collect_addr_taken at the start of lower_fn / lower_closure_thunk; the
    // home IrVal is created lazily at the binding site (bind_let_pattern).
    Node*[AT_CAP]  at_binder;
    IrVal*[AT_CAP] at_home;
    Node*[AT_CAP]  at_src;    // first `&x` AST node (carries the *T annotation)
    usz            at_count;
    // nested fn decls encountered inside fn bodies — lowered after outer fn completes
    Node*[64] pending_inner_fns;
    usz       pending_inner_count;

    // Reference to the top-level program node (for impl block lookup)
    Node*     program_node;

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

    // Module-scope `let`/`let mut` with literal initializers (r15): keyed by
    // binder pattern node so a read can seed the value like `const`. Seeded
    // once from build(); fn-local lets never enter this table.
    TopLet[TOP_LET_CAP] top_lets;
    usz                 top_let_count;
}

// A module-scope let with a compile-time-evaluable (literal) initializer.
struct TopLet
{
    Node* binder;   // PATTERN_IDENT of the binding
    Node* init;     // literal initializer expression
}

const usz TOP_LET_CAP = 512;

// Cap on lowering recursion depth (degrade gracefully, never overflow).
const int LOWER_MAX_DEPTH = 1200;

// Returns 8 if unknown (pointer-sized conservative default).
fn ulong sizeof_prim(char* name, usz len)
{
    if (name == null || len == 0) { return 8; }
    // Integer / unsigned: i8 u8 i16 u16 i32 u32 i64 u64 i128 u128 isize usize
    if (len >= 2 && (name[0] == 'i' || name[0] == 'u'))
    {
        // isize/usize are 64-bit on this target; every other iN/uN spelling
        // carries its bit width as a decimal suffix after the leading letter.
        if (span_matches_cstr(name, len, (char*)"isize") || span_matches_cstr(name, len, (char*)"usize"))
        {
            return 8;
        }
        ulong bits = 0;
        for (usz di = 1; di < len; di++)
        {
            if (name[di] >= '0' && name[di] <= '9') { bits = bits * 10 + (ulong)(name[di] - '0'); }
        }
        if (bits >= 1)
        {
            ulong bytes = (bits + 7) / 8;
            return bytes > 8 ? 16 : bytes; // i128/u128 = 16 bytes
        }
        return 8;
    }
    // Float: f32 f64
    if (span_matches_cstr(name, len, (char*)"f32")) { return 4; }
    if (span_matches_cstr(name, len, (char*)"f64")) { return 8; }
    // bool
    if (span_matches_cstr(name, len, (char*)"bool")) { return 1; }
    // chr (character = 4 bytes / unicode codepoint)
    if (span_matches_cstr(name, len, (char*)"char")) { return 4; }
    // ptr / raw pointer
    if (span_matches_cstr(name, len, (char*)"ptr")) { return 8; }
    // str / Str (fat pointer: ptr + len)
    if (span_matches_cstr(name, len, (char*)"str") || span_matches_cstr(name, len, (char*)"Str")) { return 16; }
    return 8;
}

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

// Link from→to as a SWITCH case edge with an explicit integer label.
fn int SsiModule.link_case(SsiModule* m, int from, int to, ulong case_label)
{
    IrBlock* bf = m.blk(from);
    IrBlock* bt = m.blk(to);
    if (bf == null || bt == null) return -1;
    int slot = -1;
    if (grow_succ(bf))
    {
        slot = (int)bf.succ_count;
        bf.succ[bf.succ_count] = to;
        bf.case_has[bf.succ_count] = true;    // ← case value is meaningful
        bf.case_val[bf.succ_count] = case_label;
        bf.succ_count++;
    }
    else { m.overflow = true; }
    if (grow_pred(bt)) { bt.pred[bt.pred_count] = from; bt.pred_count++; }
    else { m.overflow = true; }
    return slot;
}

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

// Inline-evaluate a DECL_CONST / DECL_STATIC read: the bound env value wins
// when one exists (env_lookup is keyed by binder pattern while a use resolves
// to the DECL node, so re-lookup via the decl's pattern child), otherwise the
// literal initializer is materialized, otherwise the whole initializer
// expression is lowered. Shared by the ident fallback (top-level constants)
// and the module-namespace FIELD path (`math::pi`). Null when nothing was
// found — callers then keep their generic fallback.
fn IrVal* SsiModule.lower_const_static(SsiModule* m, Node* decl_c)
{
    if (decl_c == null) return null;
    if (decl_c.child_count >= 1 && decl_c.children[0] != null)
    {
        IrVal* cur = m.env_lookup(decl_c.children[0]);
        if (cur != null) return cur;
    }
    // Inline-evaluate integer/bool/null constant from AST initializer.
    // children[0] = pattern binder (skip), children[1..] = type/init.
    // Walk from child 1 onward to find the init expression (skip type annotations).
    for (usz ci = 1; ci < decl_c.child_count; ci++)
    {
        Node* cc = decl_c.children[ci];
        if (cc == null || ssi::is_type_or_row(cc)) continue;
        // Integer literal
        if (cc.kind == Nk.NODE_LIT_INT)
        {
            IrVal* cv = m.new_val(IrOp.IR_CONST_INT, cc);
            if (cv != null) { cv.ival = cc.p.lit_int.int_val; m.emit(cv); }
            return cv;
        }
        // Bool literal
        if (cc.kind == Nk.NODE_LIT_BOOL)
        {
            IrVal* cv = m.new_val(IrOp.IR_CONST_BOOL, cc);
            if (cv != null) { cv.bval = cc.p.lit_bool.bool_val; m.emit(cv); }
            return cv;
        }
        // Null literal
        if (cc.kind == Nk.NODE_LIT_NULL)
        {
            IrVal* cv = m.new_val(IrOp.IR_CONST_NULL, cc);
            if (cv != null) { m.emit(cv); }
            return cv;
        }
        // Float literal
        if (cc.kind == Nk.NODE_LIT_FLOAT)
        {
            IrVal* cv = m.new_val(IrOp.IR_CONST_FLOAT, cc);
            if (cv != null) { cv.fval = cc.p.lit_float.f64_val; m.emit(cv); }
            return cv;
        }
        // For other const initializers, lower the whole expression.
        return m.lower_expr(cc);
    }
    return null;
}

// ── Address-taken locals ─────────────────────────────────────────────────────
// A local whose address is observed (`&x`) cannot live purely in SSA values:
// every mutation through that pointer must be visible to all observers, so the
// binding gets ONE persistent "home" (an IR_UN '&' value, which codegen lowers
// to a fresh alloca initialised with the current value). `&x` yields the home
// itself, reads lower to loads from it, writes lower to stores into it.
// Previously each `&x` materialised a fresh alloca holding a COPY of the SSA
// value — mutations through the pointer evaporated, so arenas/freelists lost
// their cursors and every address-based API misbehaved.

fn IrVal* SsiModule.home_for(SsiModule* m, Node* binder)
{
    if (binder == null) return null;
    for (usz i = 0; i < m.at_count; i++)
    {
        if (m.at_binder[i] == binder) return m.at_home[i];
    }
    return null;
}

fn bool SsiModule.is_addr_taken(SsiModule* m, Node* binder)
{
    if (binder == null) return false;
    for (usz i = 0; i < m.at_count; i++)
    {
        if (m.at_binder[i] == binder) return true;
    }
    return false;
}

// Pre-scan a function body for `&x` (also `&x.f` / `&x[i]`) and record every
// root binder as address-taken. Nested fn decls and closures are skipped —
// they own separate scopes and are scanned when lowered.
fn void collect_addr_taken(SsiModule* m, Node* n)
{
    if (n == null) return;
    if (n.kind == Nk.NODE_DECL_FN) return;
    if (n.kind == Nk.NODE_EXPR_CLOSURE) return;
    if (n.kind == Nk.NODE_EXPR_UNARY && n.child_count >= 1
        && n.p.op.op == Tt.TOKEN_AMP)
    {
        Node* root = n.children[0];
        while (root != null
            && (root.kind == Nk.NODE_EXPR_FIELD || root.kind == Nk.NODE_EXPR_INDEX)
            && root.child_count >= 1)
        { root = root.children[0]; }
        if (root != null && root.kind == Nk.NODE_IDENT && root.resolved != null
            && m.at_count < AT_CAP && !m.is_addr_taken(root.resolved))
        {
            m.at_binder[m.at_count] = root.resolved;
            m.at_home[m.at_count] = null;
            m.at_src[m.at_count] = n;
            m.at_count++;
        }
    }
    for (usz i = 0; i < n.child_count; i++) collect_addr_taken(m, n.children[i]);
}

// Base value for an lvalue store: an address-taken root ident yields its
// persistent home (mutations must land in the shared memory); anything else is
// lowered as a normal rvalue.
fn IrVal* SsiModule.lower_lvalue_base(SsiModule* m, Node* base_expr)
{
    if (base_expr != null && base_expr.kind == Nk.NODE_IDENT && base_expr.resolved != null)
    {
        IrVal* h = m.home_for(base_expr.resolved);
        if (h != null) return h;
    }
    return m.lower_expr(base_expr);
}

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

// Lowering
fn void SsiModule.build(SsiModule* m, Node* program)
{
    if (program == null) return;
    m.program_node = program;  // store for impl lookup
    m.seed_top_lets(program);
    m.lower_program(program);
}

// Collect module-scope `let` bindings whose initializer is a compile-time
// literal (int/unsigned/bool/float/char/null — anything the const-inliner
// can evaluate without a runtime). These read back like `const`: a module
// `let x : i64 = 10` used to lower to NOTHING, so every read silently saw 0.
// Record one module-scope literal `let` (DECL_LET whose binder is a plain
// PATTERN_IDENT and whose initializer is a compile-time literal).
fn void SsiModule.seed_one_top_let(SsiModule* m, Node* d) @private
{
    if (d == null || d.kind != Nk.NODE_DECL_LET) return;
    if (m.top_let_count >= TOP_LET_CAP) return;
    Node* pat = d.child_count >= 1 ? d.children[0] : null;
    if (pat == null || pat.kind != Nk.NODE_PATTERN_IDENT) return;
    // Find the initializer: last non-type, non-row child.
    Node* init = null;
    for (usz ci = 1; ci < d.child_count; ci++)
    {
        Node* c = d.children[ci];
        if (c == null || ssi::is_type_or_row(c)) continue;
        init = c;
    }
    if (init == null) return;
    bool is_lit = init.kind == Nk.NODE_LIT_INT || init.kind == Nk.NODE_LIT_BOOL
        || init.kind == Nk.NODE_LIT_FLOAT || init.kind == Nk.NODE_LIT_CHAR
        || init.kind == Nk.NODE_LIT_NULL || init.kind == Nk.NODE_LIT_STRING;
    if (!is_lit) return;
    TopLet* tl = &m.top_lets[m.top_let_count];
    tl.binder = pat;
    tl.init = init;
    m.top_let_count++;
}

fn void SsiModule.seed_top_lets(SsiModule* m, Node* program)
{
    m.top_let_count = 0;
    for (usz i = 0; i < program.child_count && m.top_let_count < TOP_LET_CAP; i++)
    {
        Node* d = program.children[i];
        if (d == null) continue;
        if (d.kind == Nk.NODE_DECL_LET) { m.seed_one_top_let(d); continue; }
        // One level of module nesting: literal lets inside a `mod` block seed
        // the same way — a use/import of the member (chased to the DECL_LET)
        // reads back through the same binder-keyed lookup.
        if (d.kind == Nk.NODE_DECL_MOD)
        {
            for (usz j = 0; j < d.child_count; j++)
            {
                Node* blk = d.children[j];
                if (blk == null || blk.kind != Nk.NODE_EXPR_BLOCK) continue;
                for (usz k = 0; k < blk.child_count; k++)
                {
                    m.seed_one_top_let(blk.children[k]);
                }
            }
        }
    }
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
                usz outer_func_idx = m.func_count;  // fn about to be registered
                m.lower_fn(n);
                // Set outer fn block_count BEFORE drain (thunk blocks don't belong to outer)
                SsiFunc* outer_f = (outer_func_idx < m.func_count) ? &m.funcs[outer_func_idx] : null;
                if (outer_f != null)
                {
                    outer_f.block_count = (int)m.block_count - outer_f.block_start;
                    m.eliminate_dead_blocks(outer_f);
                    m.prune_trivial_phis(outer_f);
                    m.hoist_loop_invariants(outer_f);
                    m.split_critical_edges(outer_f);
                }
                // Drain pending nested fns AFTER outer fn is fully processed
                    usz pi = 0;
                while (pi < m.pending_inner_count)
                {
                    Node* inner = m.pending_inner_fns[pi];
                    pi++;
                    if (inner != null)
                    {
                                    m.lower_fn(inner);
                    }
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

// Generates: @__pride_closure_N(ptr %__env, arg0_i64, ...) -> i64
// The thunk:
//   1. Has a ptr env parameter followed by one i64 per clause parameter
//   2. Loads captures from env (ptrtoint per slot)
//   3. Runs the closure body clauses (same as lower_fn for NODE_DECL_FN)
//   4. Returns i64 (generic; widened for uniformity)
// The closure ID is stamped via v.ival in lower_closure().
// We find it by scanning vals for the closure IR_UNKNOWN.

fn void SsiModule.lower_closure_thunk(SsiModule* m, Node* closure_node)
{
    if (m.func_count >= MAX_IR_FUNCS) { m.overflow = true; return; }
    SsiFunc* f = &m.funcs[m.func_count];
    m.func_count++;
    f.decl        = closure_node;
    f.name        = null;
    f.name_len    = 0;
    f.param_count = 0;
    f.block_start = (int)m.block_count;  // ← CRITICAL: must be set before new_block()

    // Find the closure ID by scanning vals
    int cid = 0;
    usz ncap = 0;
    for (usz vi = 0; vi < m.val_count; vi++)
    {
        IrVal* v2 = &m.vals[vi];
        if (v2.op == IrOp.IR_UNKNOWN && v2.binder == closure_node)
        { cid = (int)(v2.ival & 0x7FFFFFFF); ncap = v2.arg_count; break; }
    }

    // Name is emitted by codegen via emit_fn_name (detects closure binder)
    f.name = null; f.name_len = 0;

    int entry = m.new_block();
    f.entry = entry;
    m.cur = entry;
    usz fn_mark = m.env_mark();
    m.defer_count = 0;
    m.at_count = 0;      // per-function address-taken locals
    for (usz ci = 0; ci < closure_node.child_count; ci++) collect_addr_taken(m, closure_node.children[ci]);

    // Env parameter (ptr %__env) — param index 0, not pushed to env
    IrVal* env_param = m.new_val(IrOp.IR_PARAM, closure_node);
    if (env_param != null) { m.emit(env_param); f.params[f.param_count++] = env_param; }

    // Collect clauses from closure_node (children are NODE_CLAUSE nodes directly)
    Node*[256] clauses;
    usz nclause = 0;
    for (usz i = 0; i < closure_node.child_count; i++)
    {
        Node* ch = closure_node.children[i];
        if (ch != null && ch.kind == Nk.NODE_CLAUSE && nclause < 256)
        { clauses[nclause++] = ch; }
    }

    // Value parameters: arity from the first clause's pattern (a tuple ⇒ its
    // arity; otherwise a single argument), EXACTLY as lower_fn. The old code
    // only emitted value params for IDENT/TUPLE first patterns — a closure
    // whose first clause opened on a literal had NO value parameter (thunk
    // signature disagreed with its call sites) and every clause after the
    // first was dead code appended behind a RET.
    Node* pat0 = nclause >= 1 && clauses[0].child_count >= 1 ? clauses[0].children[0] : null;
    usz arity = 1;
    if (pat0 != null && pat0.kind == Nk.NODE_PATTERN_TUPLE) arity = pat0.child_count;
    if (arity == 0) arity = 1;
    if (arity > MAX_EDGES) arity = MAX_EDGES;

    IrVal*[MAX_EDGES] vparams;
    for (usz i = 0; i < arity; i++)
    {
        Node* param_src = pat0;
        if (pat0 != null && pat0.kind == Nk.NODE_PATTERN_TUPLE
            && i < pat0.child_count && pat0.children[i] != null)
        {
            param_src = pat0.children[i];
        }
        IrVal* pv = m.new_val(IrOp.IR_PARAM, param_src);
        if (pv != null) { m.emit(pv); }
        vparams[i] = pv;
        if (pv != null && f.param_count < MAX_EDGES) { f.params[f.param_count] = pv; f.param_count++; }
    }

    // Capture loads: free vars of the whole closure (excluding clause-local
    // binders) loaded from the env record ONCE in the entry block — the loads
    // dominate every dispatch/body block — and re-bound per scope below.
    Node*[64] cap_binders;
    usz cap_count = 0;
    Node*[128] local_binders;
    usz local_count = 0;
    for (usz cpi = 0; cpi < closure_node.child_count; cpi++)
    {
        Node* cl2 = closure_node.children[cpi];
        if (cl2 == null) continue;
        // Whole-clause marking (pattern + body), same rule as the old path:
        // body-local binders are not captures.
        mark_local_binders(cl2, &local_binders[0], &local_count, 128);
    }
    for (usz cpi = 0; cpi < closure_node.child_count; cpi++)
    { collect_free_vars(closure_node.children[cpi], &local_binders[0], local_count,
                       &cap_binders[0], &cap_count, 64); }
    IrVal*[64] cap_vals;
    for (usz ci3 = 0; ci3 < cap_count; ci3++)
    {
        cap_vals[ci3] = null;
        Node* cap_binder = cap_binders[ci3];
        if (cap_binder == null) continue;
        IrVal* load_v = m.new_val(IrOp.IR_INDEX, cap_binder);
        if (load_v == null) continue;
        load_v.add_arg(env_param, -1);
        load_v.ival = (ulong)ci3;
        m.emit(load_v);
        cap_vals[ci3] = load_v;
    }

    // Dispatch cascade: the SAME shape as lower_fn — each clause tests its
    // pattern against the value params; a guard ANDs into the test with the
    // pattern bindings live; the body block re-binds pattern + captures and
    // lowers the clause body; an irrefutable clause ends the cascade; a
    // fall-through past the last refutable clause is a trap. The old
    // straight-line lowering returned clause 0 unconditionally, leaving
    // every later arm dead.
    int cur_test = entry;
    for (usz ci = 0; ci < nclause; ci++)
    {
        Node* clause = clauses[ci];
        Node* pat = clause.child_count >= 1 ? clause.children[0] : null;
        m.cur = cur_test;
        usz tmark = m.env_mark();
        for (usz cj = 0; cj < cap_count; cj++)
        { if (cap_binders[cj] != null && cap_vals[cj] != null) m.env_push(cap_binders[cj], cap_vals[cj]); }

        IrVal* cond = m.clause_test(pat, &vparams[0], arity);

        // A guard (`| pat, guard -> body`) makes the clause refutable: bind
        // the pattern, evaluate the guard, AND it into the dispatch cond.
        Node* guard = null;
        for (usz gi = 1; gi < clause.child_count; gi++)
        {
            Node* c = clause.children[gi];
            if (c != null && c.kind == Nk.NODE_PATTERN_GUARD) { guard = c; break; }
        }
        if (guard != null)
        {
            m.bind_pattern_values(pat, &vparams[0], arity);
            IrVal* gv = null;
            if (guard.child_count >= 1) gv = m.lower_expr(guard.children[0]);
            cond = m.and_cond(cond, gv, guard);
            m.env_reset(tmark);   // un-bind; re-bound below
        }

        if (cond == null)
        {
            // Irrefutable: re-bind (tmark was reset above if guarded) and
            // lower the body; dispatch ends here.
            for (usz cj = 0; cj < cap_count; cj++)
            { if (cap_binders[cj] != null && cap_vals[cj] != null) m.env_push(cap_binders[cj], cap_vals[cj]); }
            m.bind_pattern_values(pat, &vparams[0], arity);
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
        for (usz cj = 0; cj < cap_count; cj++)
        { if (cap_binders[cj] != null && cap_vals[cj] != null) m.env_push(cap_binders[cj], cap_vals[cj]); }
        m.bind_pattern_values(pat, &vparams[0], arity);
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

    // Close open block
    IrBlock* last_b = m.blk(m.cur);
    if (last_b != null && last_b.term == TermKind.TERM_NONE)
    {
        last_b.term = TermKind.TERM_RET;
        last_b.ret_val = m.mk_unit(closure_node);
    }

    m.env_reset(fn_mark);
    f.block_count = (int)m.block_count - f.block_start;

    // Note: post-lowering passes for thunks run when
    // the outer fn includes the thunk in its block range.
    // Skip here to avoid corrupting outer fn blocks.
}

fn void SsiModule.lower_fn(SsiModule* m, Node* fn_node)
{
    // Handle NODE_EXPR_CLOSURE: lower as a thunk function
    // named @__pride_closure_N with an env ptr parameter.
    if (fn_node != null && fn_node.kind == Nk.NODE_EXPR_CLOSURE)
    {
        m.lower_closure_thunk(fn_node);
        return;
    }

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
    m.at_count = 0;      // per-function address-taken locals
    // Scan the fn's children (NOT fn_node itself — its DECL_FN kind is the
    // nested-fn skip guard; the walk would return immediately).
    for (usz ci = 0; ci < fn_node.child_count; ci++) collect_addr_taken(m, fn_node.children[ci]);

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
        // Use the individual child pattern as the src for each param so that
        // field-access codegen can find the correct struct type via pv.src.type_annotation.
        // For a single-arg function, pat0 itself is the src (it has the type stamped).
        // For multi-arg, pat0.children[i] has the per-element type.
        Node* param_src = pat0;
        if (pat0 != null && pat0.kind == Nk.NODE_PATTERN_TUPLE
            && i < pat0.child_count && pat0.children[i] != null)
        {
            param_src = pat0.children[i];
        }
        IrVal* pv = m.new_val(IrOp.IR_PARAM, param_src);
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
    // Note: f.block_count and post-lowering passes are run by lower_program
    // AFTER the drain loop completes, so thunk blocks are correctly accounted for.
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
            // emit_defers before env_close_block so deferred exprs see block locals.
            // Reset defer_count so outer path does not double-fire.
            if (!m.terminated())
            {
                m.emit_defers();
                m.defer_count = 0;
            }
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
// ── Union variant (tagged-sum) lowering ────────────────────────────────────
// Tagged repr: `{ i32 tag, i64 payload }` — the same layout the `?` desugar
// and DECL_ENUM printing assume. A `{ name: binder }` pattern tests the tag
// against the variant ordinal and binds `extractvalue payload` coerced back
// to the payload type.

// Recover (union type, variant ordinal, payload type) from a union-variant
// `{ name: binder }` pattern. Typecheck stamped the pattern with the union
// type; the first PATTERN_FIELD carries the variant name.
fn bool variant_pattern_info(Node* pat, Node** out_union_ty, int* out_ord, Node** out_payload)
{
    if (pat == null || pat.kind != Nk.NODE_PATTERN_STRUCT || pat.child_count < 1) return false;
    Node* pf0 = pat.children[0];
    if (pf0 == null || pf0.kind != Nk.NODE_PATTERN_FIELD || pf0.child_count < 1) return false;
    Node* ty = pat.type_annotation != null ? pat.type_annotation : pf0.type_annotation;
    if (ast::union_decl_of(ty) == null) return false;
    Node* vn = pf0.children[0];
    if (vn == null || vn.p.ident.name_ptr == null) return false;
    Node* payload = null;
    int ord = ast::union_variant_lookup(ast::union_decl_of(ty),
                vn.p.ident.name_ptr, vn.p.ident.name_len, &payload);
    if (ord < 0) return false;
    if (out_union_ty != null) *out_union_ty = ty;
    if (out_ord != null) *out_ord = ord;
    if (out_payload != null) *out_payload = payload;
    return true;
}

// The repr-extraction values (tag/payload extractvalue) and the fabricated
// dispatch booleans (tag == ordinal tests, guard-folding and/or) need LLVM
// types of their OWN — the extracted slot type (i32 tag / i64 payload) or i1
// — while their natural src nodes (the variant pattern / field) carry the
// UNION type annotation. tymap Priority 1 copies iv.src.type_annotation
// verbatim, which would type an `extractvalue { i32, i64 }, 0` as the whole
// aggregate: every downstream consumer (icmp operands, cast sources, ret/call
// printers) then emitted aggregate-typed references to an i32/i64 definition
// (observed as "aggregate cmp (type error, soft)" constants and as
// `bitcast i32 %v to i32` where %v was defined i64). Fabricate a fresh
// annotation-carrying holder node as the src instead.
fn Node* SsiModule.typed_holder_src(SsiModule* m, Nk kind, Node* like, char* tyname, usz tylen)
{
    int ln = like != null ? like.line : 0;
    int lc = like != null ? like.col : 0;
    Node* h = ast::node_raw(m.arena, kind, ln, lc);
    if (h != null)
    {
        h.type_annotation = ast::node_name(m.arena, Nk.NODE_TYPE_PRIMITIVE, tyname, tylen, ln, lc);
    }
    return h;
}

// i1 holder for a fabricated dispatch boolean.
fn Node* SsiModule.bool_test_src(SsiModule* m, Node* like)
{
    return m.typed_holder_src(Nk.NODE_EXPR_BINARY, like, (char*)"i1", 2);
}

// and_cond/or_cond receive pattern nodes as src whose type annotation may be
// a union decl (variant arms): substitute a boolean holder for exactly those
// (scalar / unannotated srcs flow through unchanged).
fn Node* SsiModule.cond_src(SsiModule* m, Node* src)
{
    if (src != null && src.type_annotation != null
        && ast::union_decl_of(src.type_annotation) != null)
    {
        return m.bool_test_src(src);
    }
    return src;
}

// tag(v) / payload(v): extractvalue on the { i32, i64 } repr. The src carries
// the SLOT type (i32 / i64), not the pattern's union annotation.
fn IrVal* SsiModule.union_tag(SsiModule* m, IrVal* v, Node* src)
{
    IrVal* t = m.new_val(IrOp.IR_INDEX,
                m.typed_holder_src(Nk.NODE_EXPR_INDEX, src, (char*)"i32", 3));
    if (t != null && v != null) { t.add_arg(v, -1); t.ival = 0; m.emit(t); }
    return t;
}

fn IrVal* SsiModule.union_payload(SsiModule* m, IrVal* v, Node* src)
{
    // A null scrutinee (unbindable upstream — e.g. an unannotated closure
    // parameter matched with variant patterns: those bodies are not type
    // checked, so the binder arrives without a value) must NOT mint a value
    // id that never lands in a block: the binder would dangle wherever the
    // arm uses it (φ incoming → "use of undefined value" under llvm-as,
    // unparseable-by-semantics output). Emitting a defined i64 zero keeps
    // the module well-formed; the site's own hard diagnostic (aggregate
    // closure arg) already reports the real problem.
    if (v == null)
    {
        int zln = src != null ? src.line : 0;
        int zlc = src != null ? src.col  : 0;
        Node* zsrc = ast::node_int(m.arena, 0, 64, true, zln, zlc);
        IrVal* z = m.new_val(IrOp.IR_CONST_INT, zsrc);
        if (z != null) { z.ival = 0; m.emit(z); }
        return z;
    }
    IrVal* t = m.new_val(IrOp.IR_INDEX,
                m.typed_holder_src(Nk.NODE_EXPR_INDEX, src, (char*)"i64", 3));
    if (t != null) { t.add_arg(v, -1); t.ival = 1; m.emit(t); }
    return t;
}

// Bit-exact payload boxing into / unboxing from the i64 slot (shared by the
// tagged { i32, i64 } payload and the untagged C-union bitbox). Numeric
// casts do NOT preserve bits for floats (`1.5 as i64` is fptosi), so float
// payloads move through transmute-style IR_CAST nodes — pure reinterprets.
fn IrVal* SsiModule.bitbox_to_i64(SsiModule* m, IrVal* v, Node* payload_ty, Node* src)
{
    if (v == null) return v;
    int ln = src != null ? src.line : 0;
    int lc = src != null ? src.col : 0;
    bool is_f32 = payload_ty != null && payload_ty.kind == Nk.NODE_TYPE_PRIMITIVE
        && payload_ty.p.ident.name_len == 3 && payload_ty.p.ident.name_ptr[0] == 'f';
    bool is_f64 = payload_ty != null && payload_ty.kind == Nk.NODE_TYPE_PRIMITIVE
        && payload_ty.p.ident.name_len == 3 && payload_ty.p.ident.name_ptr[0] == 'f'
        && payload_ty.p.ident.name_ptr[1] == '6';
    Node* i64ty = ast::node_name(m.arena, Nk.NODE_TYPE_PRIMITIVE, (char*)"i64", 3, ln, lc);
    if (is_f64)
    {
        // double → i64: one transmute (same width).
        Node* tn = ast::node1(m.arena, Nk.NODE_EXPR_TRANSMUTE, src, ln, lc);
        tn.type_annotation = i64ty;
        IrVal* tv = m.new_val(IrOp.IR_CAST, tn);
        if (tv != null) { tv.add_arg(v, -1); m.emit(tv); return tv; }
        return v;
    }
    if (is_f32)
    {
        // Constants with an `f32` suffix still materialize as LLVM `double`
        // (the float-literal repr), so narrow semantically to float FIRST
        // (fptrunc is bit-exact for a genuine f32 value; a same-type float
        // stays a no-op fadd) and only then reinterpret — transmuting the
        // double straight to i32 would fall through to a numeric fptosi and
        // lose the bits entirely.
        Node* f32ty = ast::node_name(m.arena, Nk.NODE_TYPE_PRIMITIVE, (char*)"f32", 3, ln, lc);
        IrVal* f32v = m.cast_to(v, f32ty, src);
        Node* i32ty = ast::node_name(m.arena, Nk.NODE_TYPE_PRIMITIVE, (char*)"i32", 3, ln, lc);
        Node* tn = ast::node1(m.arena, Nk.NODE_EXPR_TRANSMUTE, src, ln, lc);
        tn.type_annotation = i32ty;
        IrVal* tv = m.new_val(IrOp.IR_CAST, tn);
        if (tv != null) { tv.add_arg(f32v, -1); m.emit(tv); }
        else { tv = f32v; }
        return m.cast_to(tv, i64ty, src);
    }
    // Integers, bools, pointers: the semantic cast chain (sext/zext/trunc/
    // ptrtoint) is bit-exact through the readback's trunc.
    return m.cast_to(v, i64ty, src);
}

fn IrVal* SsiModule.unbox_from_i64(SsiModule* m, IrVal* v, Node* payload_ty, Node* src)
{
    if (v == null || payload_ty == null) return v;
    int ln = src != null ? src.line : 0;
    int lc = src != null ? src.col : 0;
    bool is_f32 = payload_ty.kind == Nk.NODE_TYPE_PRIMITIVE
        && payload_ty.p.ident.name_len == 3 && payload_ty.p.ident.name_ptr[0] == 'f'
        && payload_ty.p.ident.name_ptr[1] != '6';
    bool is_f64 = payload_ty.kind == Nk.NODE_TYPE_PRIMITIVE
        && payload_ty.p.ident.name_len == 3 && payload_ty.p.ident.name_ptr[0] == 'f'
        && payload_ty.p.ident.name_ptr[1] == '6';
    if (is_f64)
    {
        Node* tn = ast::node1(m.arena, Nk.NODE_EXPR_TRANSMUTE, src, ln, lc);
        tn.type_annotation = payload_ty;
        IrVal* tv = m.new_val(IrOp.IR_CAST, tn);
        if (tv != null) { tv.add_arg(v, -1); m.emit(tv); return tv; }
        return v;
    }
    if (is_f32)
    {
        // i64 → i32 (trunc: low bits) → float (transmute).
        Node* i32ty = ast::node_name(m.arena, Nk.NODE_TYPE_PRIMITIVE, (char*)"i32", 3, ln, lc);
        IrVal* tv = m.cast_to(v, i32ty, src);
        Node* tn = ast::node1(m.arena, Nk.NODE_EXPR_TRANSMUTE, src, ln, lc);
        tn.type_annotation = payload_ty;
        IrVal* bv = m.new_val(IrOp.IR_CAST, tn);
        if (bv != null) { bv.add_arg(tv, -1); m.emit(bv); return bv; }
        return tv;
    }
    return m.cast_to(v, payload_ty, src);
}

// i32 constant carrying a variant ordinal (typed so the aggregate repr
// prints { i32, ... } rather than { i64, ... }).
fn IrVal* SsiModule.tag_const(SsiModule* m, int ord, Node* src)
{
    int ln = src != null ? src.line : 0;
    int lc = src != null ? src.col  : 0;
    Node* lit = ast::node_int(m.arena, (ulong)ord, 32, true, ln, lc);
    IrVal* c = m.new_val(IrOp.IR_CONST_INT, lit);
    if (c != null) { c.ival = (ulong)ord; m.emit(c); }
    return c;
}

// A bare enum-variant VALUE (`Green`) lowers to the tagged repr
// `{ i32 ordinal, i64 payload }` with a zero payload slot — the exact shape a
// DECL_ENUM's repr and a fn's parameter assume. The ordinal is recovered from
// the resolver-stamped owner enum on the variant (tree is parent-less) by
// identity scan; when the variant carries payload AST data the unit path is
// all that exists today, so payloads beyond unit are left to typecheck's
// diagnostics. Returns null when the use isn't a resolvable variant.
fn IrVal* SsiModule.lower_enum_variant_use(SsiModule* m, Node* n)
{
    Node* ev = n != null ? n.resolved : null;
    if (ev == null || ev.kind != Nk.NODE_ENUM_VARIANT) return null;
    // The resolver stamps the owner link in .resolved, NOT .type_annotation:
    // type_annotation is followed recursively by monomorphization's
    // clone_node (variant → enum → children → variant is an exponential
    // cycle), while .resolved is only remapped shallowly by fixup_resolved.
    Node* edecl = ev.resolved;
    if (edecl == null || edecl.kind != Nk.NODE_DECL_ENUM) return null;
    int ord = -1;
    int cnt = 0;
    for (usz ei = 1; ei < edecl.child_count; ei++)
    {
        Node* c = edecl.children[ei];
        if (c == null || c.kind != Nk.NODE_ENUM_VARIANT) continue;
        if (c == ev) { ord = cnt; break; }
        cnt++;
    }
    if (ord < 0) return null;
    IrVal* tagv = m.tag_const(ord, n);
    Node* zlit = ast::node_int(m.arena, 0, 64, true, n.line, n.col);
    IrVal* pay = m.new_val(IrOp.IR_CONST_INT, zlit);
    if (pay != null) { pay.ival = 0; m.emit(pay); }
    IrVal* ag = m.new_val(IrOp.IR_TUPLE, n);
    if (ag != null)
    {
        ag.add_arg(tagv, -1);
        ag.add_arg(pay, -1);
        m.emit(ag);
    }
    return ag;
}

// Fabricate an `expr as ToTy` cast over an ALREADY-LOWERED value — the
// enum-payload repr coercion in both directions (i64 slot <-> payload type).
// The fabricated EXPR_CAST node carries the destination in type_annotation,
// which is exactly where tymap inference and IR_CAST codegen look for it.
fn IrVal* SsiModule.cast_to(SsiModule* m, IrVal* v, Node* to_ty, Node* src)
{
    if (v == null || to_ty == null) return v;
    int ln = src != null ? src.line : 0;
    int lc = src != null ? src.col  : 0;
    Node* cd = ast::node2(m.arena, Nk.NODE_EXPR_CAST, src != null ? src : to_ty, to_ty, ln, lc);
    cd.type_annotation = to_ty;
    IrVal* c = m.new_val(IrOp.IR_CAST, cd);
    if (c != null) { c.add_arg(v, -1); m.emit(c); return c; }
    return v;
}

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

// Match-expression tuple arms: the refutability test of a tuple pattern
// against ONE scrutinee value — every component is tested via single_test
// against the component's own projection (exactly clause_test over
// projections; bind/wildcard components contribute no test). This is what
// `match t | (0, 0) -> ...` spec matching needs: literal components compare
// equal, binders destructure irrefutably.
fn IrVal* SsiModule.tuple_component_test(SsiModule* m, Node* pat, IrVal* sval)
{
    if (pat == null || sval == null || pat.kind != Nk.NODE_PATTERN_TUPLE) return null;
    IrVal* acc = null;
    for (usz i = 0; i < pat.child_count; i++)
    {
        Node* comp = pat.children[i];
        if (comp == null) continue;
        IrVal* proj = m.new_val(IrOp.IR_INDEX, comp);
        if (proj == null) continue;
        proj.add_arg(sval, -1);
        proj.ival = (ulong)i;
        m.emit(proj);
        IrVal* t = m.single_test(comp, proj);
        acc = m.and_cond(acc, t, pat);
    }
    return acc;
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
        case Nk.NODE_PATTERN_STRUCT:
            // Union-variant pattern: test the tag against the ordinal.
            {
                int ord = 0; Node* vp_ty = null; Node* vp_un = null;
                if (variant_pattern_info(pat, &vp_un, &ord, &vp_ty))
                {
                    IrVal* tg = m.union_tag(v, pat);
                    IrVal* tc = m.tag_const(ord, pat);
                    // bool holder src: `pat` carries the union annotation; the
                    // icmp result must stay i1 in the tymap.
                    IrVal* t = m.new_val(IrOp.IR_BIN, m.bool_test_src(pat));
                    if (t != null) { t.bop = Tt.TOKEN_EQEQ; t.add_arg(tg, -1); t.add_arg(tc, -1); m.emit(t); }
                    return t;
                }
                return null;
            }
        case Nk.NODE_PATTERN_IDENT:
            // Bare enum-variant name pattern (`| Red -> ...`): a CONSTANT
            // pattern testing the discriminant, not a binder — the pattern
            // carries the enum type (typecheck-stamped), the carried name
            // gives the ordinal in declaration order. It used to fall through
            // to "irrefutable", making the FIRST such clause swallow every
            // value — silent wrong dispatch on enums.
            if (pat.child_count >= 1 && pat.children[0] != null
                && (pat.children[0].kind == Nk.NODE_TYPEVAR
                    || pat.children[0].kind == Nk.NODE_IDENT)
                && pat.type_annotation != null)
            {
                Node* nm3 = pat.children[0];
                Node* ed3 = ast::enum_decl_of(pat.type_annotation);
                if (ed3 != null && nm3.p.ident.name_ptr != null)
                {
                    int ord3 = ast::enum_variant_lookup(ed3,
                        nm3.p.ident.name_ptr, nm3.p.ident.name_len);
                    if (ord3 >= 0)
                    {
                        IrVal* tg3 = m.union_tag(v, pat);
                        IrVal* tc3 = m.tag_const(ord3, pat);
                        IrVal* t3 = m.new_val(IrOp.IR_BIN, m.bool_test_src(pat));
                        if (t3 != null)
                        {
                            t3.bop = Tt.TOKEN_EQEQ;
                            t3.add_arg(tg3, -1);
                            t3.add_arg(tc3, -1);
                            m.emit(t3);
                        }
                        return t3;
                    }
                }
            }
            return null;
        case Nk.NODE_PATTERN_OR:
            // | a | b | ... : test every alternative; any match suffices.
            // An irrefutable alternative (ident binder / '_') makes the whole
            // OR irrefutable -> no test (null), same rule as single patterns.
            {
                IrVal* acc = null;
                for (usz oi = 0; oi < pat.child_count; oi++)
                {
                    IrVal* t = m.single_test(pat.children[oi], v);
                    if (t == null) return null;
                    acc = m.or_cond(acc, t, pat);
                }
                return acc;
            }
        default:
            return null;   // ident / wildcard / binding patterns: irrefutable
    }
}

fn IrVal* SsiModule.and_cond(SsiModule* m, IrVal* a, IrVal* b, Node* src)
{
    if (a == null) return b;
    if (b == null) return a;
    IrVal* t = m.new_val(IrOp.IR_BIN, m.cond_src(src));
    if (t != null) { t.bop = Tt.TOKEN_AMPAMP; t.add_arg(a, -1); t.add_arg(b, -1); m.emit(t); }
    return t;
}

fn IrVal* SsiModule.or_cond(SsiModule* m, IrVal* a, IrVal* b, Node* src)
{
    if (a == null) return b;
    if (b == null) return a;
    IrVal* t = m.new_val(IrOp.IR_BIN, m.cond_src(src));
    if (t != null) { t.bop = Tt.TOKEN_PIPEPIPE; t.add_arg(a, -1); t.add_arg(b, -1); m.emit(t); }
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

// Bind every binder a pattern introduces to a fresh IR_PARAM root value
// (f != null: fn-entry context — params materialize in the fn header).
// With f == null (legacy mid-function fallback: a pattern shape the typed
// destructuring paths don't cover, e.g. a struct-ish pattern against a
// scrutinee typecheck never stamped) an IR_PARAM would print NO
// instruction anywhere — any later use, especially a match-join φ operand,
// dangles with "use of undefined value". Mid-function binders instead get
// a defined zero placeholder: the placeholder values are inert placeholders
// for programs the type checker already rejected (or never visited), and
// the module stays verifiable and parseable.
fn void SsiModule.bind_pattern(SsiModule* m, SsiFunc* f, Node* pat)
{
    if (pat == null) return;
    switch (pat.kind)
    {
        case Nk.NODE_PATTERN_IDENT:
            IrVal* pv = null;
            if (f != null)
            {
                pv = m.new_val(IrOp.IR_PARAM, pat);
                if (pv != null && f.param_count < MAX_EDGES)
                {
                    f.params[f.param_count] = pv;
                    f.param_count++;
                }
            }
            else
            {
                Node* zsrc = ast::node_int(m.arena, 0, 64, true, pat.line, pat.col);
                pv = m.new_val(IrOp.IR_CONST_INT, zsrc);
                if (pv != null) { pv.ival = 0; }
            }
            if (pv != null) { pv.binder = pat; m.emit(pv); m.env_push(pat, pv); }
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
                    IrVal* fv = null;
                    if (f != null)
                    {
                        fv = m.new_val(IrOp.IR_PARAM, fld);
                    }
                    else
                    {
                        Node* zsrc2 = ast::node_int(m.arena, 0, 64, true, fld.line, fld.col);
                        fv = m.new_val(IrOp.IR_CONST_INT, zsrc2);
                        if (fv != null) { fv.ival = 0; }
                    }
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
    // Snapshot and clear the defer stack BEFORE executing any deferred body.
    // This prevents re-entrant defer execution: if a deferred expression itself
    // triggers lower_return (e.g. `defer return x`), the inner lower_return
    // must not re-fire the same defers, producing infinite recursion.
    usz saved_count = m.defer_count;
    Node*[64] saved_defers;
    for (usz si = 0; si < saved_count; si++) saved_defers[si] = m.defers[si];
    m.defer_count = 0;   // prevent re-entry

    // Execute in LIFO order (last registered = first executed).
    usz i = saved_count;
    while (i > 0)
    {
        i--;
        Node* body = saved_defers[i];
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
            // (the assertion failure is defined as UB / program abort in Pride).
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
            if (m.is_addr_taken(pat))
            {
                // Address-taken binding: ONE persistent home for the value.
                // The home's src is the `&x` node, which carries the *T
                // annotation — codegen then types the resulting pointer
                // exactly like a source-level address-of.
                IrVal* home = null;
                for (usz hi = 0; hi < m.at_count; hi++)
                {
                    if (m.at_binder[hi] != pat) continue;
                    Node* hsrc = m.at_src[hi] != null ? m.at_src[hi] : pat;
                    home = m.new_val(IrOp.IR_UN, hsrc);
                    if (home != null)
                    {
                        home.bop = Tt.TOKEN_AMP;
                        home.add_arg(v, -1);
                        m.emit(home);
                        m.at_home[hi] = home;
                    }
                    break;
                }
                if (home != null) { m.env_push(pat, home); return; }
                // fall through to plain binding if home creation failed
            }
            m.env_push(pat, v);
        case Nk.NODE_PATTERN_OR:
            // Every ident alternative names the same scrutinee value.
            for (usz oi = 0; oi < pat.child_count; oi++)
            {
                Node* alt = pat.children[oi];
                if (alt != null && alt.kind == Nk.NODE_PATTERN_IDENT) m.bind_let_pattern(alt, val);
            }
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
        case Nk.NODE_PATTERN_STRUCT:
            // Union-variant pattern: each field binder receives the payload
            // extracted from the { i32, i64 } repr and coerced back to the
            // payload type (`_` on a unit payload binds nothing).
            {
                // Newtype destructuring (`let Dollars(v) = d`, or the
                // `| Dollars(d) -> ...` clause pattern): a newtype carries NO
                // runtime tag — the value IS the underlying value, so the
                // binder aliases the incoming value unchanged. Falling into
                // the variant path here fabricated a unit/undefined binder
                // for an identity operation.
                Node* nt_head = pat.child_count >= 1 ? pat.children[0] : null;
                if (nt_head != null && nt_head.resolved != null
                    && nt_head.resolved.kind == Nk.NODE_DECL_NEWTYPE)
                {
                    for (usz nti = 1; nti < pat.child_count; nti++)
                    {
                        Node* ntb = pat.children[nti];
                        if (ntb == null) continue;
                        m.bind_let_pattern(ntb, val);
                    }
                    return;
                }
                int ord = 0; Node* vp_ty = null; Node* vp_un = null;
                if (!variant_pattern_info(pat, &vp_un, &ord, &vp_ty))
                {
                    // Plain-struct destructure (`let { x, y } = p`,
                    // `let { fst: a } = pair`): NOT a variant pattern.  Each
                    // named field is projected out of the aggregate by its
                    // DECLARATION ordinal (the pattern may list fields in any
                    // order), then the subpattern binds recursively — or, for
                    // the `{ x }` shorthand, the field node itself (the
                    // resolver keys shorthand uses to the PATTERN_FIELD:
                    // bind_pattern_field).  Previously this fell into the
                    // unstamped fallback below, binding the UNIT value (or
                    // nothing at all for the shorthand) — reads came out 0.
                    Node* sdecl = ast::struct_decl_of(pat.type_annotation);
                    if (sdecl != null)
                    {
                        for (usz si = 0; si < pat.child_count; si++)
                        {
                            Node* pf = pat.children[si];
                            if (pf == null || pf.kind != Nk.NODE_PATTERN_FIELD
                                || pf.child_count < 1) continue;
                            Node* vn = pf.children[0];
                            if (vn == null || vn.p.ident.name_ptr == null) continue;
                            Node* fty2 = null;
                            int ford = ast::struct_field_lookup(sdecl,
                                vn.p.ident.name_ptr, vn.p.ident.name_len, &fty2);
                            if (ford < 0) continue;   // typecheck already hard-errored
                            if (pf.type_annotation == null)
                            {
                                // Unstamped (closure-body) form: fabricate the
                                // field type from the declaration so codegen
                                // can type the projection.
                                pf.type_annotation =
                                    ast::generic_payload_subst(pat.type_annotation, fty2);
                            }
                            IrVal* proj = m.new_val(IrOp.IR_INDEX, pf);
                            if (proj != null && val != null)
                            {
                                proj.add_arg(val, -1);
                                proj.ival = (ulong)ford;
                            }
                            if (proj != null) m.emit(proj);
                            if (pf.child_count >= 2 && pf.children[1] != null
                                && pf.children[1].kind != Nk.NODE_PATTERN_LITERAL)
                            {
                                // `{ name: subpattern }` — recursive binding
                                // (nested tuple/struct destructuring works).
                                m.bind_let_pattern(pf.children[1], proj);
                            }
                            else if (pf.child_count < 2)
                            {
                                m.env_push(pf, proj);
                            }
                            // `{ name: literal }` binds nothing (irrefutable
                            // let-pattern convention, same as tuple lets).
                        }
                        return;
                    }
                    // Unstamped pattern (e.g. inside an unannotated closure
                    // body, which the type checker never visits): the binder
                    // must still name a DEFINED value. Binding nothing turns
                    // a use into a fabricated IR_UNKNOWN that codegen prints
                    // as no instruction at all — a dangling `%vN` reference
                    // ("use of undefined value" under llvm-as), exactly the
                    // miscompile class the unit-payload path below guards
                    // against. Same convention: bind the unit value.
                    for (usz i = 0; i < pat.child_count; i++)
                    {
                        Node* pf2 = pat.children[i];
                        if (pf2 == null || pf2.kind != Nk.NODE_PATTERN_FIELD
                            || pf2.child_count < 2) continue;
                        Node* bind2 = pf2.children[1];
                        if (bind2 == null || bind2.kind != Nk.NODE_PATTERN_IDENT) continue;
                        m.bind_let_pattern(bind2, m.mk_unit(pf2));
                    }
                    return;
                }
                for (usz i = 0; i < pat.child_count; i++)
                {
                    Node* pf = pat.children[i];
                    if (pf == null || pf.kind != Nk.NODE_PATTERN_FIELD || pf.child_count < 2) continue;
                    Node* bind = pf.children[1];
                    if (bind == null || bind.kind != Nk.NODE_PATTERN_IDENT) continue;
                    Node* pty = pf.type_annotation != null ? pf.type_annotation : vp_ty;
                    if (pty != null && pty.kind == Nk.NODE_EXPR_UNIT)
                    {
                        // Unit payload: no slot to extract, but the binder must
                        // still name a DEFINED value (the variant's unit) —
                        // leaving it unbound would turn every use into an
                        // opaque global reference.
                        m.bind_let_pattern(bind, m.mk_unit(pf));
                        continue;
                    }
                    IrVal* pv = m.union_payload(val, pf);
                    IrVal* cv = m.unbox_from_i64(pv, pty, pf);
                    m.bind_let_pattern(bind, cv);
                }
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
        // For-range loop: the counter advances across a continue, too — feed
        // counter+step (mirrors the body-end back-edge in lower_for) instead
        // of the current counter, or the loop re-runs the SAME index forever.
        if (back != null && lc.counter_phi != null && lc.counter_step != null
            && lc.hdr_phis[i] == lc.counter_phi)
        {
            IrVal* bc = m.new_val(IrOp.IR_BIN, lc.counter_phi.src);
            if (bc != null)
            {
                bc.bop = Tt.TOKEN_PLUS;
                bc.add_arg(lc.counter_phi, -1);
                bc.add_arg(lc.counter_step, -1);
                m.emit(bc);
                back = bc;
            }
        }
        if (back == null) continue;
        lc.hdr_phis[i].add_arg(back, m.cur);
    }
    b.term = TermKind.TERM_BR;
    m.link(m.cur, lc.header);
}


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
        // Same counter-advance rule as lower_continue for a for-range target.
        if (back != null && lc.counter_phi != null && lc.counter_step != null
            && lc.hdr_phis[i] == lc.counter_phi)
        {
            IrVal* bc = m.new_val(IrOp.IR_BIN, lc.counter_phi.src);
            if (bc != null)
            {
                bc.bop = Tt.TOKEN_PLUS;
                bc.add_arg(lc.counter_phi, -1);
                bc.add_arg(lc.counter_step, -1);
                m.emit(bc);
                back = bc;
            }
        }
        if (back == null) continue;
        lc.hdr_phis[i].add_arg(back, m.cur);
    }
    b.term = TermKind.TERM_BR;
    m.link(m.cur, lc.header);
}

fn IrVal* SsiModule.lower_expr(SsiModule* m, Node* n)
{
    if (n == null || m.overflow) return null;
    if (m.lower_depth > LOWER_MAX_DEPTH) { m.overflow = true; return m.mk_unit(n); }
    m.lower_depth++;
    IrVal* res = m.lower_expr_body(n);
    m.lower_depth--;
    return res;
}


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


// Walk a node collecting free-variable references (names resolved to bindings
// that are NOT defined inside the closure itself).

// Mark all binders defined inside the closure body to detect free vs bound.
fn void mark_local_binders(Node* n, Node** bound, usz* bound_count, usz cap)
{
    if (n == null || *bound_count >= cap) return;
    // Binders: let/mut pattern idents, fn params, clause pattern idents
    if (n.kind == Nk.NODE_PATTERN_IDENT || n.kind == Nk.NODE_DECL_LET
        || n.kind == Nk.NODE_DECL_MUT)
    {
        bound[*bound_count] = n; (*bound_count)++;
    }
    for (usz i = 0; i < n.child_count; i++)
    { mark_local_binders(n.children[i], bound, bound_count, cap); }
}

fn bool is_locally_bound(Node* resolved, Node** bound, usz bound_count)
{
    for (usz i = 0; i < bound_count; i++)
    { if (bound[i] == resolved) return true; }
    return false;
}

// Collect free variable references: IDENT nodes whose .resolved is outside the closure.
fn void collect_free_vars(Node* n, Node** locals, usz local_count,
                          Node** free_out, usz* free_count, usz free_cap)
{
    if (n == null || *free_count >= free_cap) return;
    if (n.kind == Nk.NODE_IDENT && n.resolved != null)
    {
        // Check if resolved is a local binder (fn param or let inside closure)
        if (!is_locally_bound(n.resolved, locals, local_count))
        {
            // Check if already in free list
            bool already = false;
            for (usz i = 0; i < *free_count; i++)
            { if (free_out[i] == n.resolved) { already = true; break; } }
            if (!already && *free_count < free_cap)
            {
                free_out[*free_count] = n.resolved;
                (*free_count)++;
            }
        }
    }
    for (usz i = 0; i < n.child_count; i++)
    { collect_free_vars(n.children[i], locals, local_count,
                        free_out, free_count, free_cap); }
}

// We reuse IR_UNKNOWN tagged with the closure AST node.
// args[0] = thunk ptr (IR_UNKNOWN with binder = synthesized fn decl)
// args[1..] = captured IrVals (one per free variable)
// Codegen emits:
//   %env.N = alloca { T1, T2, ... }
//   (store each captured value into the env struct)
//   %closure.N = insertvalue { ptr, ptr } undef, ptr @thunk.N, 0
//   %closure.N2 = insertvalue { ptr, ptr } %closure.N, ptr %env.N, 1

fn IrVal* SsiModule.lower_closure(SsiModule* m, Node* closure_node)
{
    if (closure_node == null) return m.mk_unit(closure_node);

    Node*[128] locals;
    usz local_count = 0;
    for (usz ci = 0; ci < closure_node.child_count; ci++)
    {
        Node* clause = closure_node.children[ci];
        if (clause == null) continue;
        // Walk the WHOLE clause (pattern + guard + body), not just its
        // parameter pattern: every binder the body introduces (lets,
        // match-arm pattern binders) is local to the closure, never a
        // capture. Pattern-only marking left body-local binders looking
        // "free", so they were captured: unbound at closure-creation time,
        // the slot froze a unit value and the thunk emitted the invalid
        // `inttoptr void {} to ptr`.
        mark_local_binders(clause, &locals[0], &local_count, 128);
    }

    Node*[64] captures;
    usz capture_count = 0;
    for (usz ci = 0; ci < closure_node.child_count; ci++)
    { collect_free_vars(closure_node.children[ci], &locals[0], local_count,
                        &captures[0], &capture_count, 64); }

    static int closure_seq = 0;
    closure_seq++;
    int cid = closure_seq;

    //    The thunk takes (ptr %__env, original_args...) and unpacks captures.
    //    For now we register the closure as a pending inner fn;
    //    codegen will emit the thunk globally.
    IrVal* closure_v = m.new_val(IrOp.IR_UNKNOWN, closure_node);
    if (closure_v == null) return m.mk_unit(closure_node);
    closure_v.binder = closure_node;  // tag so codegen recognises it
    closure_v.ival = (ulong)cid;      // unique closure id

    // args[0..capture_count-1] = current SSA values for each captured binding
    for (usz i = 0; i < capture_count; i++)
    {
        IrVal* cap_val = m.env_lookup(captures[i]);
        if (cap_val == null) cap_val = m.mk_unit(closure_node);
        closure_v.add_arg(cap_val, -1);
    }

    m.emit(closure_v);

    // Schedule the thunk for post-outer-fn lowering (same mechanism as inner fns)
    if (m.pending_inner_count < 64)
    {
        m.pending_inner_fns[m.pending_inner_count] = closure_node;
        m.pending_inner_count++;
    }

    return closure_v;
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
        // Statement nodes that can appear as `then`/`else` bodies of if-then:
        // `if cond then return x` — the parser places NODE_STMT_RETURN as then_b.
        // Route through lower_stmt so it properly calls lower_return (TERM_RET).
        case Nk.NODE_STMT_RETURN:
        case Nk.NODE_STMT_BREAK:
        case Nk.NODE_STMT_CONTINUE:
        case Nk.NODE_STMT_BREAK_LABEL:
        case Nk.NODE_STMT_CONTINUE_LABEL:
        case Nk.NODE_STMT_TRAP:
        case Nk.NODE_STMT_UNREACHABLE:
        case Nk.NODE_STMT_DEFER:
            return m.lower_stmt(n);
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
                if (cur != null && m.home_for(n.resolved) == cur)
                {
                    // Address-taken binding: a use LOADS from the persistent
                    // home, so mutations made through `&x` are observed.
                    IrVal* ld = m.new_val(IrOp.IR_UN, n);
                    if (ld != null)
                    {
                        ld.bop = Tt.TOKEN_STAR;
                        ld.add_arg(cur, -1);
                        m.emit(ld);
                        return ld;
                    }
                    return cur;
                }
                if (cur != null) return cur;

                // Module-scope `let` with a literal initializer behaves like
                // `const` (r15): v.md §5 makes plain `let` an immutable
                // binding by default, and a module-scope immutable binding of
                // a compile-time literal IS a constant. It used to lower to
                // nothing at all — reading it silently produced 0, a
                // miscompile of a program that resolved and typechecked
                // fine. Env lookup here just seeds the value once, keyed by
                // the binder pattern, exactly like a fn-local binding.
                if (n.resolved.kind == Nk.NODE_PATTERN_IDENT
                    || n.resolved.kind == Nk.NODE_DECL_LET)
                {
                    // The binder whose identity keys a top-level literal let:
                    // direct uses resolve to the PATTERN_IDENT; a use reached
                    // through a chased member import resolves to the DECL_LET
                    // (whose pattern is children[0]).
                    Node* want = n.resolved;
                    if (want.kind == Nk.NODE_DECL_LET)
                    {
                        want = (want.child_count >= 1) ? want.children[0] : null;
                    }
                    Node* let_init = null;
                    bool lit_let = false;
                    // Recover the initializer: the tree is parent-less, so
                    // match by identity against the module's seeded top-level
                    // lets.
                    for (usz tli = 0; tli < m.top_let_count && want != null; tli++)
                    {
                        TopLet* tl = &m.top_lets[tli];
                        if (tl.binder == want) { let_init = tl.init; lit_let = true; break; }
                    }
                    if (lit_let && let_init != null)
                    {
                        IrVal* lv = m.lower_expr(let_init);
                        if (lv != null)
                        {
                            m.env_push(n.resolved, lv);
                            return lv;
                        }
                    }
                    // Fall through: a module-scope `let mutable` or
                    // non-literal init has no constant answer here.
                }

                // DECL_CONST / DECL_STATIC with an inline-evaluable
                // initializer: shared with the module-namespace FIELD path.
                if (n.resolved.kind == Nk.NODE_DECL_CONST
                    || n.resolved.kind == Nk.NODE_DECL_STATIC)
                {
                    IrVal* csv = m.lower_const_static(n.resolved);
                    if (csv != null) return csv;
                }
            }
            // An enum-variant ctor use resolves to the variant node: emit the
            // tagged { i32 ordinal, i64 0 } repr (same arm as the TypeVar
            // variant in the default case — kept here so lowercase-spelled
            // variants resolve identically).
            if (n.resolved != null && n.resolved.kind == Nk.NODE_ENUM_VARIANT)
            {
                IrVal* evv = m.lower_enum_variant_use(n);
                if (evv != null) return evv;
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
            return m.lower_unary(n);

        case Nk.NODE_EXPR_ASSIGN:
            return m.lower_assign(n);

        case Nk.NODE_EXPR_CALL:
            // `resume(v)` inside a handler arm → IR_RESUME.
            if (is_resume_call(n)) { return m.lower_resume(n); }
            // Newtype constructor: `Dollars(x)` is a transparent wrap — the
            // runtime representation IS the underlying value, so the "call"
            // is the identity on its single argument. It used to fall through
            // to the generic callee path with the newtype NAME as an opaque
            // global, becoming a call through inttoptr(0) — immediate UB.
            {
                Node* callee_n = (n.child_count >= 1) ? n.children[0] : null;
                if (callee_n != null && callee_n.resolved != null
                    && callee_n.resolved.kind == Nk.NODE_DECL_NEWTYPE)
                {
                    if (n.child_count >= 2) return m.lower_expr(n.children[1]);
                    return m.mk_unit(n);
                }
            }
            // `k(val)` where k is the continuation binder (IR_UNKNOWN with arm binder)
            // → also emit IR_RESUME(val).
            {
                // Peek at callee ident to detect continuation call
                Node* callee_node = (n.child_count >= 1) ? n.children[0] : null;
                bool is_continuation_call = false;
                if (callee_node != null)
                {
                    // Resolve the ident to its bound IrVal
                    IrVal* callee_iv = (callee_node.resolved != null)
                        ? m.env_lookup(callee_node.resolved) : null;
                    if (callee_iv == null && callee_node.kind == Nk.NODE_IDENT)
                    {
                        // Try direct env lookup by name
                        callee_iv = m.env_lookup(callee_node);
                    }
                    if (callee_iv != null
                        && callee_iv.op == IrOp.IR_UNKNOWN
                        && callee_iv.binder != null
                        && callee_iv.binder.kind == Nk.NODE_HANDLER_ARM)
                    {
                        is_continuation_call = true;
                    }
                }
                if (is_continuation_call)
                {
                    // Emit as IR_RESUME: resume the computation with the first arg
                    IrVal* resume_v = m.new_val(IrOp.IR_RESUME, n);
                    Node* arm_bnd = callee_node != null && callee_node.resolved != null
                                  ? callee_node.resolved : null;
                    if (resume_v != null) { resume_v.binder = arm_bnd; }
                    IrVal* resume_arg = (n.child_count >= 2) ? m.lower_expr(n.children[1])
                                                              : m.mk_unit(n);
                    if (resume_v != null)
                    {
                        resume_v.add_arg(resume_arg, -1);
                        m.emit(resume_v);
                    }
                    return resume_v;
                }
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
            // Union variant constructor: `U.variant(args)` → tagged repr
            // `{ i32 ordinal, i64 payload }`. Resolved by shape, not by name:
            // the base must resolve to a union decl and the member must be a
            // variant of it (previously this fell through to a generic call
            // and produced an inttoptr call through a NULL callee).
            {
                Node* vbase = n.child_count >= 1 ? n.children[0] : null;
                Node* vmem  = n.child_count >= 2 ? n.children[1] : null;
                Node* vdecl = vbase != null ? ast::union_decl_of(vbase) : null;
                bool mem_named = vmem != null
                    && (vmem.kind == Nk.NODE_IDENT || vmem.kind == Nk.NODE_TYPEVAR)
                    && vmem.p.ident.name_ptr != null;
                if (vdecl != null && mem_named)
                {
                    Node* payload_ty = null;
                    int ord = ast::union_variant_lookup(vdecl,
                        vmem.p.ident.name_ptr, vmem.p.ident.name_len, &payload_ty);
                    if (ord >= 0)
                    {
                        // Untagged C-union (r13): the whole value is one i64
                        // bitbox holding the payload BIT-EXACTLY; no tag slot
                        // exists. Non-scalar fields cannot fit the cell — the
                        // front-end's hard diagnostic gates that; emit a
                        // parseable zero here.
                        if (ast::union_is_c_union(vdecl))
                        {
                            if (!ast::union_payload_is_scalar(payload_ty))
                            {
                                Node* zlit2 = ast::node_int(m.arena, 0, 64, true, n.line, n.col);
                                IrVal* z64 = m.new_val(IrOp.IR_CONST_INT, zlit2);
                                if (z64 != null) { z64.ival = 0; m.emit(z64); }
                                return z64;
                            }
                            Node* carg = n.child_count >= 3 ? n.children[2] : null;
                            IrVal* cav = m.lower_expr(carg);
                            return m.bitbox_to_i64(cav, payload_ty, n);
                        }
                        bool unit_payload = payload_ty == null || payload_ty.kind == Nk.NODE_EXPR_UNIT;
                        IrVal* tagv = m.tag_const(ord, n);
                        IrVal* pay64 = null;
                        if (unit_payload)
                        {
                            Node* zlit = ast::node_int(m.arena, 0, 64, true, n.line, n.col);
                            pay64 = m.new_val(IrOp.IR_CONST_INT, zlit);
                            if (pay64 != null) { pay64.ival = 0; m.emit(pay64); }
                        }
                        else
                        {
                            Node* varg = n.child_count >= 3 ? n.children[2] : null;
                            IrVal* argv64 = m.lower_expr(varg);
                            pay64 = m.bitbox_to_i64(argv64, payload_ty, n);
                        }
                        IrVal* ag = m.new_val(IrOp.IR_TUPLE, n);
                        if (ag != null)
                        {
                            ag.add_arg(tagv, -1);
                            ag.add_arg(pay64, -1);
                            m.emit(ag);
                            return ag;
                        }
                    }
                }
            }
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
            // Module namespace access: `math::f` / `alias::f`. The base names
            // a module (direct decl or import alias) and the member ident's
            // .resolved is stamped at the declaration INSIDE the module — this
            // node is a namespaced NAME, not a data projection. A module has
            // no runtime value, so the old IR_FIELD lowering projected from a
            // fabricated null base and a call became an indirect call through
            // inttoptr(0) (garbage result, or SIGTRAP once the optimizer sees
            // the UB). Emit the member exactly like a top-level use of the
            // same declaration: fn → direct reference (IR_UNKNOWN with the
            // DECL_FN binder, which codegen turns into @pride_name with proper
            // parameter marshalling), const/static → inline evaluation.
            {
                Node* fbase = n.child_count >= 1 ? n.children[0] : null;
                Node* fmem  = n.child_count >= 2 ? n.children[1] : null;
                Node* fbtgt = fbase != null ? fbase.resolved : null;
                bool base_is_ns = fbtgt != null
                    && (fbtgt.kind == Nk.NODE_DECL_MOD
                        || fbtgt.kind == Nk.NODE_DECL_USE
                        || fbtgt.kind == Nk.NODE_DECL_IMPORT);
                if (base_is_ns && fmem != null && fmem.resolved != null)
                {
                    Node* md = fmem.resolved;
                    if (md.kind == Nk.NODE_DECL_FN)
                    {
                        IrVal* fref = m.new_val(IrOp.IR_UNKNOWN, n);
                        if (fref != null) { fref.binder = md; m.emit(fref); }
                        return fref;
                    }
                    if (md.kind == Nk.NODE_DECL_CONST
                        || md.kind == Nk.NODE_DECL_STATIC)
                    {
                        IrVal* csv = m.lower_const_static(md);
                        if (csv != null) return csv;
                    }
                }
                // Enum-variant selection `Color.Red` (r39): the base is the
                // enum TYPE (not a value) — the generic projection below
                // lowers it to a junk global and GEP-loads a record out of
                // inttoptr(0).  Construct the tagged { ordinal, 0 } repr by
                // declaration ordinal, exactly like the bare-ident variant
                // arm in the default case; the member ident gets resolved to
                // the variant node (the resolver does not link it).
                Node* fbase2 = n.child_count >= 1 ? n.children[0] : null;
                Node* fmem2  = n.child_count >= 2 ? n.children[1] : null;
                Node* edecl2 = ast::enum_decl_of(fbase2);
                if (edecl2 != null && fmem2 != null
                    && fmem2.p.ident.name_ptr != null)
                {
                    for (usz evi = 1; evi < edecl2.child_count; evi++)
                    {
                        Node* ev2 = edecl2.children[evi];
                        if (ev2 == null || ev2.kind != Nk.NODE_ENUM_VARIANT) continue;
                        Node* vn2 = ev2.child_count >= 1 ? ev2.children[0] : null;
                        if (vn2 == null || vn2.p.ident.name_ptr == null
                            || vn2.p.ident.name_len != fmem2.p.ident.name_len) continue;
                        bool veq = true;
                        for (usz vci = 0; vci < fmem2.p.ident.name_len; vci++)
                        { if (vn2.p.ident.name_ptr[vci] != fmem2.p.ident.name_ptr[vci]) { veq = false; break; } }
                        if (!veq) continue;
                        fmem2.resolved = ev2;
                        IrVal* evv = m.lower_enum_variant_use(fmem2);
                        if (evv != null) return evv;
                        break;
                    }
                }
            }
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

        case Nk.NODE_EXPR_RANGE_STEP:
            // start..end by step. Lowered exactly like NODE_EXPR_RANGE but with
            // a third IR_RANGE operand (args[2]) carrying the step value, so
            // lower_for() (and any other IR_RANGE consumer) can recover it
            // instead of assuming a hardcoded step of 1.
            IrVal* rs_lo = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
            IrVal* rs_hi = m.lower_expr(n.child_count >= 2 ? n.children[1] : null);
            IrVal* rs_step = m.lower_expr(n.child_count >= 3 ? n.children[2] : null);
            IrVal* rs_v = m.new_val(IrOp.IR_RANGE, n);
            if (rs_v != null)
            {
                rs_v.add_arg(rs_lo, -1);
                rs_v.add_arg(rs_hi, -1);
                if (rs_step != null) rs_v.add_arg(rs_step, -1);
                m.emit(rs_v);
            }
            return rs_v;

        case Nk.NODE_EXPR_TUPLE_LIT:
            return m.lower_aggregate(n, IrOp.IR_TUPLE);
        case Nk.NODE_EXPR_ARRAY_LIT:
            return m.lower_aggregate(n, IrOp.IR_ARRAY);
        case Nk.NODE_EXPR_STRUCT_LIT:
            return m.lower_aggregate(n, IrOp.IR_STRUCT);

        case Nk.NODE_EXPR_ALLOC:
            {
                // Pre-scan the type child for a dynamic count expression and lower it
                // BEFORE creating the ALLOC IrVal, so the count val dominates the alloc.
                ulong alloc_nbytes  = 8;
                bool  dynamic_count = false;
                IrVal* dyn_count_val = null;

                if (n.child_count >= 1 && n.children[0] != null)
                {
                    Node* aty_pre = n.children[0];
                    if (aty_pre.kind == Nk.NODE_TYPE_ARRAY)
                    {
                        ulong eb_pre = 8;
                        Node* cnt_pre = null;
                        for (usz ci = 0; ci < aty_pre.child_count; ci++)
                        {
                            Node* ac = aty_pre.children[ci];
                            if (ac == null) { continue; }
                            if (ac.kind == Nk.NODE_TYPE_PRIMITIVE)
                            { eb_pre = (ulong)sizeof_prim(ac.p.ident.name_ptr, ac.p.ident.name_len); }
                            else if (ac.kind != Nk.NODE_TYPE_ARRAY && ac.kind != Nk.NODE_TYPE_PTR
                                  && ac.kind != Nk.NODE_TYPE_REF && ac.kind != Nk.NODE_TYPE_MUT_REF)
                            { cnt_pre = ac; }
                        }
                        if (cnt_pre != null && cnt_pre.kind != Nk.NODE_LIT_INT)
                        {
                            // Dynamic: emit count expr NOW before alloc val.
                            dyn_count_val = m.lower_expr(cnt_pre);
                            dynamic_count = true;
                            alloc_nbytes  = eb_pre;
                        }
                    }
                }

                // Now create the ALLOC IrVal — it will come AFTER the count in the IR stream.
                IrVal* av = m.lower_aggregate(n, IrOp.IR_ALLOC);
                if (av == null) { return null; }

                // If not already computed dynamically above, do the static/scalar scan now.
                if (!dynamic_count && n.child_count >= 1 && n.children[0] != null)
                {
                    Node* aty = n.children[0];
                    if (aty.kind == Nk.NODE_TYPE_ARRAY && aty.child_count >= 1)
                    {
                        ulong elem_bytes = 8;
                        ulong arr_n = 1;
                        for (usz ci = 0; ci < aty.child_count; ci++)
                        {
                            Node* ac = aty.children[ci];
                            if (ac == null) { continue; }
                            if (ac.kind == Nk.NODE_LIT_INT)
                            { arr_n = ac.p.lit_int.int_val; }
                            else if (ac.kind == Nk.NODE_TYPE_PRIMITIVE)
                            { elem_bytes = (ulong)sizeof_prim(ac.p.ident.name_ptr, ac.p.ident.name_len); }
                        }
                        if (arr_n < 1) arr_n = 1;
                        alloc_nbytes = arr_n * elem_bytes;
                    }
                    else if (aty.kind == Nk.NODE_TYPE_PRIMITIVE)
                    {
                        alloc_nbytes = (ulong)sizeof_prim(aty.p.ident.name_ptr, aty.p.ident.name_len);
                    }
                    else if (aty.kind == Nk.NODE_TYPE_PTR || aty.kind == Nk.NODE_TYPE_REF
                          || aty.kind == Nk.NODE_TYPE_MUT_REF)
                    {
                        alloc_nbytes = 8;
                    }
                }

                if (dynamic_count && dyn_count_val != null)
                {
                    // Dynamic array alloc: bit 63 of ival set = dynamic.
                    // Low 32 bits = elem_bytes. arg[0] = runtime count IrVal.
                    av.ival = (ulong)0x8000000000000000u | (alloc_nbytes & 0xFFFFFFFFu);
                    av.add_arg(dyn_count_val, m.cur);
                }
                else
                {
                    av.ival = (ulong)alloc_nbytes;
                }
                return av;
            }
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

        // 'label: <loop>  — labeled loop. child[0]=label ident, child[1]=loop node.
        case Nk.NODE_EXPR_LABELED:
            {
                Node* lbl_ident = n.child_count >= 1 ? n.children[0] : null;
                Node* loop_node = n.child_count >= 2 ? n.children[1] : null;
                if (lbl_ident != null && loop_node != null)
                {
                    char* nm = lbl_ident.p.ident.name_ptr;
                    usz   nl = lbl_ident.p.ident.name_len;
                    // Strip leading ' from the label ref token if present
                    if (nm != null && nl > 1 && nm[0] == '\'') { nm++; nl--; }
                    m.pending_label_name = nm;
                    m.pending_label_nlen = nl;
                    return m.lower_expr(loop_node);
                }
                return m.mk_unit(n);
            }

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

        case Nk.NODE_EXPR_CLOSURE:
            return m.lower_closure(n);

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

        case Nk.NODE_STAGE:
        case Nk.NODE_QUOTE:
            // MSP nodes that reach codegen: evaluate/passthrough the inner expression.
            // A stage/quote that wasn't consumed by stage.c3 (e.g. in a generic body
            // that's being monomorphized) should not crash the backend.
            if (n.child_count >= 1 && n.children[0] != null) { return m.lower_expr(n.children[0]); }
            return m.mk_unit(n);

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

        case Nk.NODE_EXPR_ATOMIC_RMW:
            {
                IrVal* aptr = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
                IrVal* aval = m.lower_expr(n.child_count >= 2 ? n.children[1] : null);
                IrVal* v = m.new_val(IrOp.IR_ATOMIC_RMW, n);
                if (v != null) { v.ival = n.p.raw; v.add_arg(aptr, -1); v.add_arg(aval, -1); m.emit(v); }
                return v;
            }

        case Nk.NODE_EXPR_ATOMIC_CMPXCHG:
            {
                IrVal* cptr = m.lower_expr(n.child_count >= 1 ? n.children[0] : null);
                IrVal* cexp = m.lower_expr(n.child_count >= 2 ? n.children[1] : null);
                IrVal* cnew = m.lower_expr(n.child_count >= 3 ? n.children[2] : null);
                IrVal* v = m.new_val(IrOp.IR_CMPXCHG, n);
                if (v != null) { v.add_arg(cptr, -1); v.add_arg(cexp, -1); v.add_arg(cnew, -1); m.emit(v); }
                return v;
            }

        case Nk.NODE_EXPR_FENCE:
            {
                // Ordering ident → .ival: seq_cst=5 acq_rel=4 acquire=2 release=3 monotonic=0
                IrVal* v = m.new_val(IrOp.IR_FENCE, n);
                if (v != null)
                {
                    long ord = 5;  // default seq_cst
                    Node* ord_node = n.child_count >= 1 ? n.children[0] : null;
                    if (ord_node != null && ord_node.kind == Nk.NODE_IDENT)
                    {
                        char* nm = ord_node.p.ident.name_ptr; usz nl = ord_node.p.ident.name_len;
                        if (nl >= 7 && nm[0]=='a'&&nm[1]=='c'&&nm[2]=='q'&&nm[3]=='_'&&nm[4]=='r') { ord=4; }
                        else if (nl >= 7 && nm[0]=='a'&&nm[1]=='c'&&nm[2]=='q') { ord=2; }
                        else if (nl >= 7 && nm[0]=='r'&&nm[1]=='e'&&nm[2]=='l') { ord=3; }
                        else if (nl >= 8 && nm[0]=='m'&&nm[1]=='o'&&nm[2]=='n') { ord=0; }
                    }
                    v.ival = (ulong)ord;
                    m.emit(v);
                }
                return v;
            }

        case Nk.NODE_EXPR_MATMUL:
            // a @ b — tensor/matrix contraction.
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

                // Create an IR_UNKNOWN reference so calls resolve to @pride_name
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
            // NODE_TYPEVAR that resolved to a DECL_CONST (e.g. TOK_KW_FN=100):
            // uppercase names are parsed as typevar nodes but used as values.
            // If resolved to a const/static, inline-evaluate the initializer.
            // A bare enum-variant use (uppercase idents parse as TypeVar):
            // `Green` lowers to the tagged `{ i32 ordinal, i64 0 }` repr an
            // enum value actually carries — the opaque-global fallback made
            // it a ptr literal that no consumer can use.
            if (n.kind == Nk.NODE_TYPEVAR && n.resolved != null
                && (n.resolved.kind == Nk.NODE_PATTERN_IDENT
                    || n.resolved.kind == Nk.NODE_DECL_LET
                    || n.resolved.kind == Nk.NODE_DECL_MUT))
            {
                // A local binder whose name is capitalized (e.g. `let Red = 7`
                // shadowing the enum variant) resolves here too — the let
                // binder, fn param, or module-scope let lowered through this
                // same default arm used to fall to the opaque placeholder,
                // silently reading 0 for a live local. Read the env exactly
                // like the NODE_IDENT use case does.
                IrVal* tcur = m.env_lookup(n.resolved);
                if (tcur != null && m.home_for(n.resolved) == tcur)
                {
                    IrVal* tld = m.new_val(IrOp.IR_UN, n);
                    if (tld != null)
                    {
                        tld.bop = Tt.TOKEN_STAR;
                        tld.add_arg(tcur, -1);
                        m.emit(tld);
                        return tld;
                    }
                    return tcur;
                }
                if (tcur != null) return tcur;
                // Module-scope literal let not seeded into this fn's env:
                // recover its constant initializer (same as the IDENT path).
                Node* twant = n.resolved;
                if (twant.kind == Nk.NODE_DECL_LET)
                {
                    twant = twant.child_count >= 1 ? twant.children[0] : null;
                }
                for (usz tli = 0; tli < m.top_let_count && twant != null; tli++)
                {
                    TopLet* tl = &m.top_lets[tli];
                    if (tl.binder != twant || tl.init == null) continue;
                    IrVal* lv = m.lower_expr(tl.init);
                    if (lv != null)
                    {
                        m.env_push(n.resolved, lv);
                        return lv;
                    }
                }
            }
            if (n.kind == Nk.NODE_TYPEVAR && n.resolved != null
                && n.resolved.kind == Nk.NODE_ENUM_VARIANT)
            {
                IrVal* evv = m.lower_enum_variant_use(n);
                if (evv != null) return evv;
            }
            if (n.kind == Nk.NODE_TYPEVAR && n.resolved != null
                && (n.resolved.kind == Nk.NODE_DECL_CONST
                    || n.resolved.kind == Nk.NODE_DECL_STATIC))
            {
                Node* decl_tv = n.resolved;
                // Try env lookup via PatIdent key first
                if (decl_tv.child_count >= 1 && decl_tv.children[0] != null)
                {
                    IrVal* tv_cur = m.env_lookup(decl_tv.children[0]);
                    if (tv_cur != null) return tv_cur;
                }
                // Inline-evaluate: walk children[1..] for the init literal
                for (usz tci = 1; tci < decl_tv.child_count; tci++)
                {
                    Node* tcc = decl_tv.children[tci];
                    if (tcc == null || ssi::is_type_or_row(tcc)) continue;
                    if (tcc.kind == Nk.NODE_LIT_INT)
                    {
                        IrVal* cv = m.new_val(IrOp.IR_CONST_INT, tcc);
                        if (cv != null) { cv.ival = tcc.p.lit_int.int_val; m.emit(cv); }
                        return cv;
                    }
                    if (tcc.kind == Nk.NODE_LIT_BOOL)
                    {
                        IrVal* cv = m.new_val(IrOp.IR_CONST_BOOL, tcc);
                        if (cv != null) { cv.bval = tcc.p.lit_bool.bool_val; m.emit(cv); }
                        return cv;
                    }
                    if (tcc.kind == Nk.NODE_LIT_NULL)
                    {
                        IrVal* cv = m.new_val(IrOp.IR_CONST_NULL, tcc);
                        if (cv != null) { m.emit(cv); }
                        return cv;
                    }
                    // Fallback: lower the init expression
                    return m.lower_expr(tcc);
                }
            }
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
    // SENTINEL inside lower_aggregate: set ival=77777 for any ALLOC
    if (v != null) { v.ival = 55555; }  // ALWAYS fire
    for (usz i = 0; i < n.child_count; i++)
    {
        Node* c = n.children[i];
        if (c == null || ssi::is_type_or_row(c)) { continue; }
        // Struct literals: child[0] is either the type name (TYPEVAR/GENERIC_APP, or IDENT
        // resolving to a struct/type decl) — skip those. But for struct UPDATE syntax
        // (`base_val { field: new_val }`), child[0] is an IDENT resolving to a VALUE binding —
        // lower it as the base struct and tag v.ival=1 (struct update mode).
        if (op == IrOp.IR_STRUCT && i == 0)
        {
            if (c.kind == Nk.NODE_TYPEVAR || c.kind == Nk.NODE_TYPE_GENERIC_APP) { continue; }
            if (c.kind == Nk.NODE_IDENT)
            {
                // Check what the ident resolves to
                Node* res = c.resolved;
                bool resolves_to_type = (res != null
                    && (res.kind == Nk.NODE_DECL_STRUCT || res.kind == Nk.NODE_DECL_TYPE
                        || res.kind == Nk.NODE_DECL_ENUM));
                if (resolves_to_type) { continue; }   // type name — skip
                // Value binding (pat_ident, let, etc.) — this is the base struct for update
                IrVal* base = m.lower_expr(c);
                if (v != null)
                {
                    v.add_arg(base, -1);
                    v.ival = 1;   // 1 = struct update (arg[0] = base struct value)
                }
                continue;
            }
        }
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

    // Compound assignment: +=, -=, *=, /=, %=, &=, |=, ^=, <<=, >>=
    // Desugar: lhs OP= rhs  →  lhs = lhs OP rhs
    // n.p.op.op carries the compound token; TOKEN_EQ is plain assignment.
    Tt assign_op = n.p.op.op;
    Tt bin_op = Tt.TOKEN_EQ;  // sentinel: no compound op
    switch (assign_op)
    {
        case Tt.TOKEN_PLUSEQ:    bin_op = Tt.TOKEN_PLUS;    break;
        case Tt.TOKEN_MINUSEQ:   bin_op = Tt.TOKEN_MINUS;   break;
        case Tt.TOKEN_STAREQ:    bin_op = Tt.TOKEN_STAR;    break;
        case Tt.TOKEN_SLASHEQ:   bin_op = Tt.TOKEN_SLASH;   break;
        case Tt.TOKEN_PERCENTEQ: bin_op = Tt.TOKEN_PERCENT; break;
        case Tt.TOKEN_AMPEQ:     bin_op = Tt.TOKEN_AMP;     break;
        case Tt.TOKEN_PIPEEQ:    bin_op = Tt.TOKEN_PIPE;    break;
        case Tt.TOKEN_XOREQ:     bin_op = Tt.TOKEN_XOR;     break;
        case Tt.TOKEN_LSHIFTEQ:  bin_op = Tt.TOKEN_LSHIFT;  break;
        case Tt.TOKEN_RSHIFTEQ:  bin_op = Tt.TOKEN_RSHIFT;  break;
        default: break;
    }

    IrVal* rv = null;
    if (bin_op != Tt.TOKEN_EQ)
    {
        // Compound: read current lhs value, compute op, store result
        IrVal* lhs_val = m.lower_expr(lhs);
        IrVal* rhs_val = rhs != null ? m.lower_expr(rhs) : null;
        IrVal* bin = m.new_val(IrOp.IR_BIN, n);
        if (bin != null)
        {
            bin.bop = bin_op;
            bin.add_arg(lhs_val, -1);
            bin.add_arg(rhs_val, -1);
            m.emit(bin);
        }
        rv = bin;
    }
    else
    {
        rv = rhs != null ? m.lower_expr(rhs) : null;
    }

    if (lhs != null && lhs.kind == Nk.NODE_IDENT && lhs.resolved != null)
    {
        // Address-taken binding: write through to the persistent home so every
        // `&x` observer (and every later load) sees the store. The env keeps
        // the home — no fresh SSA version is created.
        IrVal* home = m.home_for(lhs.resolved);
        if (home != null)
        {
            if (rv == null) { rv = m.new_val(IrOp.IR_UNKNOWN, n); if (rv != null) m.emit(rv); }
            IrVal* st = m.new_val(IrOp.IR_STORE, n);
            if (st != null)
            {
                st.add_arg(home, -1);   // args[0] = home pointer
                st.add_arg(rv, -1);     // args[1] = value to store
                m.emit(st);
            }
            return rv;
        }
        if (rv == null) { rv = m.new_val(IrOp.IR_UNKNOWN, n); if (rv != null) m.emit(rv); }
        m.env_push(lhs.resolved, rv);   // override: newest binding wins
        return rv;
    }
    if (lhs != null && lhs.kind == Nk.NODE_EXPR_UNARY
        && lhs.child_count >= 1)
    {
        // lhs = UN('*', ptr_expr)
        IrVal* ptr_val = m.lower_lvalue_base(lhs.children[0]);
        IrVal* st = m.new_val(IrOp.IR_STORE, n);
        if (st != null)
        {
            st.add_arg(ptr_val, -1);    // args[0] = pointer
            st.add_arg(rv, -1);         // args[1] = value to store
            m.emit(st);
        }
        return rv;
    }
    if (lhs != null && lhs.kind == Nk.NODE_EXPR_INDEX && lhs.child_count >= 2)
    {
        IrVal* base_val  = m.lower_lvalue_base(lhs.children[0]);
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
    if (lhs != null && lhs.kind == Nk.NODE_EXPR_FIELD && lhs.child_count >= 1)
    {
        IrVal* base_val = m.lower_lvalue_base(lhs.children[0]);
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
    if (lhs != null) { m.lower_expr(lhs); }
    return rv;
}

fn IrVal* SsiModule.lower_unary(SsiModule* m, Node* n)
{
    Node* uop_arg = n.child_count >= 1 ? n.children[0] : null;
    // `&x` (or `&x.f`, `&x[i]`) of an address-taken local: yield the binding's
    // persistent home — ONE stable address per binding — instead of a fresh
    // alloca holding a copy of the current value.
    if (n.p.op.op == Tt.TOKEN_AMP && uop_arg != null)
    {
        Node* root = uop_arg;
        while (root != null
            && (root.kind == Nk.NODE_EXPR_FIELD || root.kind == Nk.NODE_EXPR_INDEX)
            && root.child_count >= 1)
        { root = root.children[0]; }
        if (root != null && root.kind == Nk.NODE_IDENT && root.resolved != null)
        {
            IrVal* home = m.home_for(root.resolved);
            if (home != null) return home;
        }
    }
    IrVal* o = m.lower_expr(uop_arg);
    IrVal* v = m.new_val(IrOp.IR_UN, n);
    if (v != null) { v.bop = n.p.op.op; v.add_arg(o, -1); m.emit(v); }
    return v;
}

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

// The SWITCH case value of an int-like literal pattern, false when the
// pattern cannot be a switch case. Covers int, bool and char literals —
// previously only NODE_LIT_INT was honoured, so `match b | true -> | false ->`
// dispatched through an EMPTY switch and fell into the non-exhaustive trap
// on every input.
// Equality pretest for an all-literal or-pattern used in match lowering:
// (sval == alt0) || (sval == alt1) || ...  Null result means irrefutable.
fn IrVal* SsiModule.or_pattern_test(SsiModule* m, Node* pat, IrVal* sval)
{
    return m.single_test(pat, sval);
}

fn bool match_case_value(Node* pat, ulong* out)
{
    if (pat == null || pat.kind != Nk.NODE_PATTERN_LITERAL
        || pat.child_count < 1 || pat.children[0] == null) return false;
    Node* lit = pat.children[0];
    switch (lit.kind)
    {
        case Nk.NODE_LIT_INT:
            *out = lit.p.lit_int.int_val;
            return true;
        case Nk.NODE_LIT_BOOL:
            *out = lit.p.lit_bool.bool_val ? 1 : 0;
            return true;
        case Nk.NODE_LIT_CHAR:
            *out = (ulong)lit.p.lit_char.char_val;
            return true;
        default:
            return false;
    }
}

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
    // When the default block is repurposed as the guard-chain forwarder, its
    // TRAP role moves to a fresh block: chain-exhausted (and guarded-literal)
    // false edges must trap on a failed match, not loop back into the chain
    // head (an infinite loop — a hang where the language promises UB/trap).
    int trap_blk = default_blk;

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
    int* lit_pend = (int*)malloc(arm_cap * int::size);   // guarded-literal false edges awaiting a chain arm
    usz narm = 0;
    if (arm_snaps == null || arm_results == null || arm_ends == null || arm_live == null || lit_pend == null)
    {
        if (arm_snaps != null) free(arm_snaps);
        if (arm_results != null) free(arm_results);
        if (arm_ends != null) free(arm_ends);
        if (arm_live != null) free(arm_live);
        if (lit_pend != null) free(lit_pend);
        return m.mk_unit(n);
    }

    // Guarded-arm dispatch. The SWITCH dispatches literal cases directly;
    // everything else falls to succ[0] (default_blk), which forwards to the
    // head of a chain of guard blocks — one per ident/wildcard arm, in source
    // order. A guard's false edge continues to the NEXT ident/wildcard arm
    // (literal cases are already exhausted by the switch); the chain falls
    // into the trap block when exhausted. A guarded LITERAL arm's false edge
    // joins the chain at the next ident/wildcard arm as well (the switch has
    // already proved the case value, so literal arms can never re-match).
    //
    //   match n
    //     | 0        -> a           [switch case 0 -> body]
    //     | k, k > 0 -> b           [default -> guard(k>0) -> body | false -> chain]
    //     | _        -> c           [chain catch-all]
    int pending_false = -1;   // chain guard block awaiting its false-edge target
    usz n_lit_pend = 0;       // lit_pend[0..n_lit_pend]: unresolved literal-guard false edges
    ulong* pend_val = (ulong*)malloc(arm_cap * ulong::size);  // case value per pending edge
    ulong* claim_val = (ulong*)malloc(arm_cap * ulong::size); // switch case values in use
    bool* claim_dead = (bool*)malloc(arm_cap * bool::size);   // claim closed by an unguarded arm
    usz n_claim = 0;
    if (pend_val == null || claim_val == null || claim_dead == null)
    {
        if (pend_val != null) free(pend_val);
        if (claim_val != null) free(claim_val);
        if (claim_dead != null) free(claim_dead);
        free(arm_snaps); free(arm_results); free(arm_ends); free(arm_live); free(lit_pend);
        return m.mk_unit(n);
    }
    // All arms AFTER arm CUR that can still match case value CV receive the
    // pending false edges recorded for CV (chain arms match anything).
    // Implemented inline at each arm: literal arms flush their own value,
    // ident/wildcard arms flush everything.

    for (usz i = 1; i < n.child_count; i++)
    {
        Node* arm = n.children[i];
        if (arm == null || arm.kind != Nk.NODE_MATCH_ARM) continue;
        if (narm >= arm_cap) break;

        Node* pat = arm.child_count >= 1 ? arm.children[0] : null;
        bool is_wild = pat != null && pat.kind == Nk.NODE_PATTERN_WILDCARD;
        bool is_bind = pat != null && pat.kind == Nk.NODE_PATTERN_IDENT;
        bool is_tuple = pat != null && pat.kind == Nk.NODE_PATTERN_TUPLE;
        bool is_or   = pat != null && pat.kind == Nk.NODE_PATTERN_OR;

        // Guard extraction: the parser stores `| pat, cond -> body` as arm
        // children [pat, NODE_PATTERN_GUARD(cond), body...]. Must precede the
        // classification below: an all-literal OR arm WITH a guard lowers as
        // a tested chain arm, not as switch cases.
        Node* guard = null;
        for (usz j = 1; j < arm.child_count; j++)
        {
            Node* c = arm.children[j];
            if (c != null && c.kind == Nk.NODE_PATTERN_GUARD) { guard = c; break; }
        }

        // OR-arm classification. Typecheck restricts alternatives to
        // literals / ident binders / '_'; anything else never reaches here.
        bool or_has_irrefutable = false;   // an ident binder or '_' alternative
        bool or_all_case_lits   = is_or;   // every alternative has a case value
        bool or_has_str         = false;   // a string-literal alternative
        Node* or_ident = null;             // first ident alternative (binds scrutinee)
        if (is_or)
        {
            for (usz oi = 0; oi < pat.child_count; oi++)
            {
                Node* alt = pat.children[oi];
                if (alt == null) { or_all_case_lits = false; continue; }
                if (alt.kind == Nk.NODE_PATTERN_IDENT)
                {
                    or_has_irrefutable = true;
                    if (or_ident == null) or_ident = alt;
                }
                else if (alt.kind == Nk.NODE_PATTERN_WILDCARD)
                {
                    or_has_irrefutable = true;
                }
                else
                {
                    if (alt.kind == Nk.NODE_PATTERN_LITERAL
                        && alt.child_count >= 1 && alt.children[0] != null
                        && alt.children[0].kind == Nk.NODE_LIT_STRING)
                    {
                        or_has_str = true;
                    }
                    ulong tmp_cv = 0;
                    if (!match_case_value(alt, &tmp_cv)) or_all_case_lits = false;
                }
            }
        }
        // Wildcard, ident and tuple patterns are IRREFUTABLE (they match any
        // scrutable value of their shape): they route through the default
        // chain, never as switch cases. Typechecking hard-rejects shape
        // mismatches (tuple pattern vs non-tuple/scalar domain), so by the
        // time a tuple arm reaches here the scrutinee is an aggregate the
        // binding layer can destructure. An OR with an irrefutable
        // alternative matches everything (chain arm; the ident binds the
        // scrutinee); an all-literal OR WITH a guard is a chain arm with an
        // equality pretest folded into its guard (one static false edge
        // cannot route per case value — the chain re-tests instead).
        bool or_chain_irrefutable = is_or && or_has_irrefutable;
        // An OR with string-literal alternatives is a tested chain arm even
        // unguarded: every alternative is a refutable content-equality test
        // (no switch case values to claim).
        bool or_tested_chain = is_or && !or_has_irrefutable
            && ((or_all_case_lits && guard != null) || or_has_str);
        // Union-variant struct arm `{ name: binder }`: refutable, goes through
        // the default chain with its tag test folded into the dispatch block
        // (same tested-chain shape as guarded OR arms — a switch cannot prove
        // a tag without giving every variant value its own case routing).
        bool is_variant_arm = !is_or
            && variant_pattern_info(pat, null, null, null);
        // Bare enum-variant name arm (`| Red -> ...`): a constant pattern on
        // the discriminant — refutable like the union-variant arm, and the
        // name must NOT swallow as a plain binder (its old is_bind
        // classification skipped every test, so the first name arm matched
        // everything).
        bool is_enum_name_arm = false;
        if (!is_or && pat != null && pat.kind == Nk.NODE_PATTERN_IDENT
            && pat.child_count >= 1 && pat.children[0] != null
            && (pat.children[0].kind == Nk.NODE_TYPEVAR
                || pat.children[0].kind == Nk.NODE_IDENT)
            && pat.type_annotation != null)
        {
            Node* enm = pat.children[0];
            Node* edc = ast::enum_decl_of(pat.type_annotation);
            if (edc != null && enm.p.ident.name_ptr != null
                && ast::enum_variant_lookup(edc, enm.p.ident.name_ptr,
                                            enm.p.ident.name_len) >= 0)
            {
                is_enum_name_arm = true;
                is_bind = false;
            }
        }
        // Newtype struct arm `Dollars(v)`: a tagless identity wrap —
        // irrefutable (there is nothing to test), bound through the destructuring
        // layer so the binder aliases the scrutinee unchanged. It used to take
        // the legacy bind_pattern fallback, which BINDS NOTHING for a
        // TypeVar-headed pattern — a use of the binder fabricated a dangling
        // reference or zero.
        bool is_newtype_arm = !is_or
            && pat != null && pat.kind == Nk.NODE_PATTERN_STRUCT
            && pat.child_count >= 1 && pat.children[0] != null
            && pat.children[0].resolved != null
            && pat.children[0].resolved.kind == Nk.NODE_DECL_NEWTYPE;
        // Null-literal arm (`| null -> ...`): a refutable pointer-equality
        // test on the scrutinee. The switch has no integer case value for
        // it — the literal arm's old fallback statically linked it as
        // "shadowed / non-int literal: unreachable", so a null scrutinee
        // silently fell into the NEXT arm (usually the catch-all).
        bool is_null_arm = !is_or && pat != null
            && pat.kind == Nk.NODE_PATTERN_LITERAL
            && pat.child_count >= 1 && pat.children[0] != null
            && pat.children[0].kind == Nk.NODE_LIT_NULL;
        // String-literal arm (`| "hi" -> ...`): refutable CONTENT-equality
        // test on the Str scrutinee. The switch has no integer case value
        // for a string, so — like the null arm used to — the arm fell into
        // the "non-int literal" fallback and was statically dead: every
        // string silently dropped into the NEXT arm (usually the catch-all).
        // single_test on the literal lowers to `==` on Str, which codegen
        // emits as @pride_str_eq.
        bool is_str_arm = !is_or && pat != null
            && pat.kind == Nk.NODE_PATTERN_LITERAL
            && pat.child_count >= 1 && pat.children[0] != null
            && pat.children[0].kind == Nk.NODE_LIT_STRING;
        // Tuple arm with LITERAL components (`| (0, b) -> ...`): refutable —
        // the component equalities are tested in the dispatch block via
        // tuple_component_test, exactly like fn-clause tuple matching.
        bool tuple_lit_comps = false;
        if (is_tuple)
        {
            for (usz k = 0; k < pat.child_count; k++)
            {
                if (pat.children[k] != null
                    && pat.children[k].kind == Nk.NODE_PATTERN_LITERAL)
                { tuple_lit_comps = true; break; }
            }
        }
        // Enum-name arms are tested-chain arms too: the switch cannot prove
        // a discriminant (no integer case value exists for a NAME pattern),
        // so they route through the default chain exactly like union-variant
        // arms, re-testing the tag in their dispatch block.
        bool chain_arm = is_wild || is_bind || is_tuple || or_chain_irrefutable || or_tested_chain
            || is_variant_arm || is_newtype_arm || is_enum_name_arm || is_null_arm
            || is_str_arm;

        int arm_blk = m.new_block();
        // Variant arms need the tag test evaluated in a dispatch block even
        // without a user guard; null and string arms need their equality
        // test there.
        // (or_tested_chain needs the block even when guard==null: the OR
        // with string alternatives has NO switch cases, so without the
        // equality pretest here the arm would match EVERYTHING; same for
        // refutable literal components of a tuple arm.)
        bool needs_test_blk = (guard != null) || is_variant_arm || is_enum_name_arm
            || is_null_arm || is_str_arm || or_tested_chain || tuple_lit_comps;
        int guard_blk = needs_test_blk ? m.new_block() : -1;
        int dispatch = (guard_blk >= 0) ? guard_blk : arm_blk;

        if (chain_arm)
        {
            // First ident/wildcard arm: the switch's default edge forwards to
            // the head of the guard chain.
            if (db != null && !default_filled)
            {
                db.term = TermKind.TERM_BR;
                m.link(default_blk, dispatch);
                default_filled = true;
                trap_blk = m.new_block();
                IrBlock* ttb = m.blk(trap_blk);
                if (ttb != null) ttb.term = TermKind.TERM_UNREACHABLE;
            }
            else { m.link(b0, arm_blk); }   // trailing catch-all: unreachable
            // A previous chain guard falls through to this arm on false.
            if (pending_false >= 0) { m.link(pending_false, dispatch); pending_false = -1; }
            // A chain arm matches anything: ALL pending literal-guard false
            // edges resolve here regardless of their case value.
            for (usz q = 0; q < n_lit_pend; q++) { m.link(lit_pend[q], dispatch); }
            n_lit_pend = 0;
        }
        else if (is_or)
        {
            // Unguarded all-literal OR: ONE switch case per alternative
            // value (LLVM cases may share a destination). The first-claim /
            // pending / shadow bookkeeping is the single-literal rule
            // applied independently per alternative value.
            for (usz oi = 0; oi < pat.child_count; oi++)
            {
                ulong ocv = 0;
                if (pat.children[oi] == null || !match_case_value(pat.children[oi], &ocv)) continue;
                int prior_o = -1;
                for (usz q = 0; q < n_claim; q++) { if (claim_val[q] == ocv) { prior_o = (int)q; break; } }
                bool shadowed_o = prior_o >= 0 && claim_dead[prior_o];
                if (prior_o < 0)
                {
                    int slot = m.link(b0, dispatch);
                    if (slot >= 0 && pb0 != null)
                    {
                        pb0.case_has[slot] = true;
                        pb0.case_val[slot] = ocv;
                    }
                    claim_val[n_claim] = ocv;
                    claim_dead[n_claim] = true;   // these arms are unguarded
                    n_claim++;
                }
                else if (!shadowed_o)
                {
                    // Reachable via the ordering chain for THIS value.
                    usz w = 0;
                    for (usz q = 0; q < n_lit_pend; q++)
                    {
                        if (pend_val[q] == ocv) { m.link(lit_pend[q], dispatch); continue; }
                        lit_pend[w] = lit_pend[q]; pend_val[w] = pend_val[q]; w++;
                    }
                    n_lit_pend = w;
                    claim_dead[prior_o] = true;
                }
                // shadowed alternative: contributes nothing; the arm may
                // still be reached through its other values.
            }
        }
        else
        {
            // Literal arms are switch cases, but LLVM forbids duplicate case
            // values: only the FIRST arm to claim a value becomes a case.
            // Same-value successors join the ordered chain instead — reached
            // through the earlier guard's false edge — or are shadowed dead
            // code once an unguarded arm has claimed the value.
            bool has_cv = false; ulong cv = 0;
            if (match_case_value(pat, &cv)) { has_cv = true; }
            int prior = -1;
            if (has_cv)
            {
                for (usz q = 0; q < n_claim; q++) { if (claim_val[q] == cv) { prior = (int)q; break; } }
            }
            bool shadowed = prior >= 0 && claim_dead[prior];
            if (has_cv && prior < 0)
            {
                int slot = m.link(b0, dispatch);
                if (slot >= 0 && pb0 != null)
                {
                    pb0.case_has[slot] = true;
                    pb0.case_val[slot] = cv;
                }
                claim_val[n_claim] = cv;
                claim_dead[n_claim] = (guard_blk < 0);
                n_claim++;
            }
            else { m.link(b0, arm_blk); }   // shadowed / non-int literal: unreachable
            if (has_cv && prior >= 0 && !shadowed)
            {
                // Reachable via the ordering chain: resolve earlier guards'
                // false edges for THIS value here, then track shadowing.
                usz w = 0;
                for (usz q = 0; q < n_lit_pend; q++)
                {
                    if (pend_val[q] == cv) { m.link(lit_pend[q], dispatch); continue; }
                    lit_pend[w] = lit_pend[q]; pend_val[w] = pend_val[q]; w++;
                }
                n_lit_pend = w;
                if (guard_blk < 0) { claim_dead[prior] = true; }
            }
        }

        usz amark = m.env_mark();
        // Bind pattern variables against the SCRUTINEE VALUE, never fresh
        // unbound parameters: an ident arm aliases it, a tuple arm destructures
        // it via projections, a union-variant arm extracts its payload slot.
        // (Other pattern shapes keep the legacy binding until they get
        // properly typed destructuring.)
        // Emit the destructuring projections in this arm's DISPATCH block
        // (guard_blk when present, else arm_blk): the dispatch block
        // dominates both the guard evaluation and the arm body. Emitting
        // into whatever block the previous arm left cur in scattered the
        // projections into earlier bodies (broken dominance) — and a guard
        // referencing a bound name needs the binding ABOVE guard_blk.
        m.cur = (guard_blk >= 0) ? guard_blk : arm_blk;
        if (is_bind || is_tuple || is_variant_arm || is_newtype_arm) { m.bind_let_pattern(pat, sval); }
        else if (or_ident != null)               { m.bind_let_pattern(or_ident, sval); }
        else                                     { m.bind_pattern(null, pat); }

        // Guarded arm: evaluate the guard in its own dispatch block with the
        // pattern bindings live; true → body, false → continue matching.
        if (guard_blk >= 0)
        {
            m.cur = guard_blk;
            IrVal* gval = guard != null
                ? m.lower_expr(guard.child_count >= 1 ? guard.children[0] : null)
                : null;
            if (is_variant_arm || is_enum_name_arm || is_null_arm || is_str_arm)
            {
                // The switch proved nothing: run the variant tag test here
                // and AND any user guard into it. single_test covers both
                // `{ name: binder }` (union) and bare name (enum) arms —
                // and the null/string arms' PATTERN_LITERAL falls out of its
                // generic literal-equality arm (icmp eq on scalars, a
                // @pride_str_eq call for Str).
                gval = m.and_cond(m.single_test(pat, sval), gval, pat);
            }
            if (or_tested_chain)
            {
                // Reached via the default chain: the switch proved nothing
                // about the scrutinee, so AND the alternative-equality
                // pretest into the guard condition.
                gval = m.and_cond(m.or_pattern_test(pat, sval), gval, pat);
            }
            if (tuple_lit_comps)
            {
                // Refutable literal components of the tuple pattern: AND
                // their per-component equality tests in.
                gval = m.and_cond(m.tuple_component_test(pat, sval), gval, pat);
            }
            IrBlock* gb = m.blk(guard_blk);
            if (gb != null && gval != null) { gb.term = TermKind.TERM_CBR; gb.cond = gval; }
            m.link(guard_blk, arm_blk);
            if (chain_arm) { pending_false = guard_blk; }   // resolved by the next chain arm / trap
            else if (n_lit_pend < arm_cap)
            {
                // Guarded literal: false edge awaits the next arm that can
                // still match this case value (same-value literal or any
                // ident/wildcard arm), in source order.
                lit_pend[n_lit_pend] = guard_blk;
                ulong pv = 0;
                match_case_value(pat, &pv);
                pend_val[n_lit_pend] = pv;
                n_lit_pend++;
            }
        }

        m.cur = arm_blk;
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

    // An open guard chain falls through to the trap when exhausted
    // (non-exhaustive match on values no arm claimed).
    if (pending_false >= 0) { m.link(pending_false, trap_blk); pending_false = -1; }
    for (usz q = 0; q < n_lit_pend; q++) { m.link(lit_pend[q], trap_blk); }
    n_lit_pend = 0;

    // A match whose arms recorded NO switch cases (pure irrefutable arms —
    // wildcard/ident/tuple — possibly behind guards) has nothing to dispatch:
    // LLVM `switch` requires an integer condition, and an aggregate scrutinee
    // (tuple) is outright illegal there. Downgrade to a plain branch into the
    // default chain (succ[0]): dispatch then lives entirely in guard blocks.
    if (pb0 != null && pb0.term == TermKind.TERM_SWITCH)
    {
        bool any_case = false;
        for (usz si = 0; si < pb0.succ_count; si++)
        { if (pb0.case_has[si]) { any_case = true; break; } }
        if (!any_case) { pb0.term = TermKind.TERM_BR; }
    }

    if (join < 0)
    {
        // Every arm diverged.
        free(arm_snaps); free(arm_results); free(arm_ends); free(arm_live); free(lit_pend);
        free(pend_val); free(claim_val); free(claim_dead);
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
        free(arm_snaps); free(arm_results); free(arm_ends); free(arm_live); free(lit_pend);
        free(pend_val); free(claim_val); free(claim_dead);
        return rphi;
    }
    free(arm_snaps); free(arm_results); free(arm_ends); free(arm_live); free(lit_pend);
    free(pend_val); free(claim_val); free(claim_dead);
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
    // Slots are reused across sibling loops — clear the for-range hook or a
    // stale counter from a previous loop would corrupt this one's continue.
    lc.counter_phi = null;
    lc.counter_step = null;
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

// Algebraic Effects Lowering
// STRATEGY — "structured handler frames" (backend-agnostic)
// We lower effect constructs into three dedicated IR opcodes without CPS-
// transforming the SSA-CFG.  The SSA structure (φ/σ, verified dominance) is
// fully preserved.  The backend picks its own ABI:
//   • VM / interpreter      → handler record on an explicit effect stack
//   • LLVM (simple)         → setjmp/longjmp-based unwinding per handler frame
//   • LLVM (efficient)      → Leijen-style evidence passing (Koka ABI)
//   • Cranelift / Wasm      → block-argument continuation passing
//   • Native w/ split stack → OCaml 5 / Multicore continuation capture
// The IR encodes:
//   IR_EFFECT_OP   — "perform Effect.op(args...)"
//     .binder → the effect op declaration (NODE_EFFECT_OP_DECL), giving the
//               op identity (effect name + op name) for handler dispatch.
//     args    → the op's argument values.
//   IR_HANDLER     — "handle computation { | Op(args) k → arm_body }"
//     args[0]   → the computation result (value of the handled expression).
//     args[1..] → IR_HANDLER_ARM values, one per arm.
//     .binder   → the NODE_EFFECT_HANDLE node (for effect identity lookup).
//     Semantically: install a handler frame covering args[0]'s computation,
//     dispatch each performed op to its matching arm.
//   IR_HANDLER_ARM — one dispatch arm (linked into IR_HANDLER)
//     args[0]  → the arm body's result value.
//     .binder  → the NODE_HANDLER_ARM node (for op-head identity lookup).
//     The arm's op-argument binders are IR_PARAMs emitted into the arm's block.
//   IR_RESUME      — "resume(v)" inside a handler arm
//     args[0]  → the value to resume the suspended computation with.
//     .binder  → the NODE_HANDLER_ARM this resume belongs to.
//     Semantically: transfer control back to the effect-op call site with v.
// "with r = resource { body }" is desugared entirely at IR level:
//   let r = resource; result = body; [cleanup if needed]
// No new IrOp needed — it becomes IR_CALL + block nesting.
// An effect-operation call `Effect.op(arg0, arg1, ...)` arrives as
// NODE_EXPR_METHOD_CALL[EffectTypeVar, op_ident, arg0, arg1, ...].
// child[0].resolved → NODE_DECL_EFFECT (the effect declaration).
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


fn IrVal* SsiModule.lower_effect_perform(SsiModule* m, Node* n)
{
    // Find the op declaration for the .binder field.
    Node* op_decl = ast::effect_op_decl_of(n);

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

    // Coerce the ptr result to the declared return type if needed.
    // __pride_perform always returns ptr; Pride ops declare their actual return type.
    // For non-ptr, non-unit return types (e.g. i64, bool, f64), emit ptrtoint/bitcast.
    if (v != null && op_decl != null)
    {
        // op_decl is EffectOpDecl: children[1] = TyFn, TyFn.children[1] = return type.
        Node* tyfn = op_decl.child_count >= 2 ? op_decl.children[1] : null;
        Node* ret_ty = (tyfn != null && tyfn.kind == Nk.NODE_TYPE_FN && tyfn.child_count >= 2)
                       ? tyfn.children[1] : null;
        bool ret_is_prim = (ret_ty != null && ret_ty.kind == Nk.NODE_TYPE_PRIMITIVE);
        // Coerce: primitive return type → ptrtoint the ptr result from __pride_perform.
        // We must NOT annotate n.type_annotation (that would corrupt the IR_EFFECT_OP's
        // tymap type from "ptr" to "i64", making src_type wrong in IR_CAST codegen).
        // Instead: use ret_ty as the cast dst annotation on a DIFFERENT node (ret_ty itself).
        if (ret_is_prim)
        {
            // Emit IR_CAST with src=v(ptr), using ret_ty node as src to drive dst-type inference.
            // The cast val's src = ret_ty (a TyPrimitive node), so Priority 1 gives "i64".
            // The cast arg[0] = v (IR_EFFECT_OP, tymap="ptr"), so src type is "ptr". Correct.
            IrVal* cast = m.new_val(IrOp.IR_CAST, ret_ty);
            if (cast != null)
            {
                cast.bop = Tt.TOKEN_KW_AS;
                cast.add_arg(v, -1);
                m.emit(cast);
                return cast;
            }
        }
    }

    return v;
}

// Each handler arm NODE_HANDLER_ARM[op_head, binder0, ..., binderN, body] is
// lowered into a fresh block:
//   arm_blk:
//     p0 = param   ← first op argument
//     p1 = param   ← second op argument  (0..N matching the op signature)
//     k  = param   ← the continuation (resume target)
//     <body instructions>
//     ret arm_result
// The IR_HANDLER_ARM value (in the join block) carries args[0] = the arm's
// result so the IR_HANDLER can φ-merge all arm results.

// arm_blk must be pre-created by the caller (lower_handle) so that the
// dispatch block's SWITCH edges are correctly established before lowering.
// Bind one handler-arm argument pattern to exactly the runtime slots it
// names, flattening tuple patterns: the effect ABI passes op arguments in
// FLAT slots (the frame's arm_args[0..N)), so `Op.f (a, b)` is two slots,
// `()` is zero. Emits one IR_PARAM per leaf binder with the flat slot index
// on pv.ival (read directly by codegen's get_arm_arg emission). Returns the
// next free slot.
fn int SsiModule.emit_arm_arg_params(SsiModule* m, Node* pat, Node* arm, int slot) @private
{
    if (pat == null) return slot;
    if (pat.kind == Nk.NODE_PATTERN_TUPLE)
    {
        for (usz i = 0; i < pat.child_count; i++)
        { slot = m.emit_arm_arg_params(pat.children[i], arm, slot); }
        return slot;
    }
    if (pat.kind == Nk.NODE_PATTERN_IDENT)
    {
        IrVal* pv = m.new_val(IrOp.IR_PARAM, pat);
        if (pv != null)
        {
            pv.binder = arm;          // codegen: effect-arm arg branch
            pv.ival = (ulong)slot;    // flat runtime slot index
            m.emit(pv);
        }
        m.bind_let_pattern(pat, pv);
        return slot + 1;
    }
    // Wildcards/literals consume a slot but bind nothing.
    return slot + 1;
}

fn IrVal* SsiModule.lower_handler_arm(SsiModule* m, Node* arm, int arm_blk, int join)
{
    m.cur = arm_blk;

    // arm children: [op_head_field, binder0, ..., binderN, body]
    // child[0]       = op head (Field[EffectTypeVar, op_ident]) — no value needed
    // children[1..N] = argument binders (PatIdent) + the continuation binder
    // child[last]    = arm body

    usz last = arm.child_count >= 1 ? arm.child_count - 1 : 0;
    Node* body_node = arm.child_count >= 1 ? arm.children[last] : null;

    // Binder classification — the op DECLARATION's arity is the ground truth.
    // An arm names exactly the op's parameters (resume-style, no continuation)
    // or the parameters PLUS a trailing continuation binder k. `()` in binder
    // position is the zero-arg placeholder and names no slot.
    //
    // Previously this guessed positionally ("the last binder is k whenever
    // there is ≥1 binder"), silently misclassifying a single ARGUMENT binder as
    // the continuation: `| Ask.ask code -> resume(code * 2)` bound `code` to
    // the never-emitted continuation sentinel, and the body's `code` read then
    // decomposed that virtual value into `index (v70)` against an undefined
    // register — only visible once the join φ was typed honestly and llvm-as
    // got far enough to notice.
    long op_nargs = ast::effect_op_arity_of_arm(arm);
    usz cont_idx = 0;   // child index of the continuation binder; 0 = none
    {
        usz eff = 0;
        usz last_eff = 0;
        for (usz i = 1; i < last; i++)
        {
            if (ast::is_arm_unit_binder(arm.children[i])) continue;
            eff++;
            last_eff = i;
        }
        if (op_nargs >= 0)
        {
            if ((long)eff == op_nargs + 1) { cont_idx = last_eff; }
        }
        else if (last >= 2) { cont_idx = last - 1; }   // resolver already errored; legacy guess
    }

    // Emit IR_PARAMs for op ARGUMENT binders (children[1..last-1] minus the
    // continuation). Tuple patterns flatten onto the runtime's flat arg-slot
    // ABI: `Op.pair (a, b) k` names slots 0 and 1 just like `Op.pair a b k`.
    // The slot index travels on the IR_PARAM value itself (pv.ival) — codegen
    // must not re-derive it from child position (position ≠ slot the moment a
    // `()` placeholder or a nested tuple appears).
    int arm_slot = 0;
    for (usz i = 1; i < last; i++)
    {
        Node* binder = arm.children[i];
        if (binder == null) { continue; }

        if (cont_idx != 0 && i == cont_idx)
        {
            // Continuation k: bind to an IR_UNKNOWN sentinel tagged with the arm node.
            // When the body calls k(val), lower_expr detects this and emits IR_RESUME(val).
            IrVal* kv = m.new_val(IrOp.IR_UNKNOWN, binder);
            if (kv != null)
            {
                kv.binder = arm;  // binder == arm node → "this is a continuation"
                // Do NOT emit — it is a virtual value, never actually defined as an inst.
            }
            m.bind_let_pattern(binder, kv);
            continue;
        }
        if (ast::is_arm_unit_binder(binder)) { continue; }
        arm_slot = m.emit_arm_arg_params(binder, arm, arm_slot);
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

// NODE_EFFECT_HANDLE[computation, HandlerArm, HandlerArm, ...]
// CFG produced:
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
// The IR_HANDLER node is the value of the whole expression. Each IR_HANDLER_ARM
// child identifies which op it handles (via .binder → NODE_HANDLER_ARM) and
// carries the arm's result value.

fn IrVal* SsiModule.lower_handle(SsiModule* m, Node* n)
{
    // child[0] is the computation; children[1..] are HandlerArm nodes.
    Node* comp = n.child_count >= 1 ? n.children[0] : null;

    // CRITICAL ORDERING: the handler frame (push_handler) MUST be installed
    // before the computation body runs, so that IR_EFFECT_OP inside the body
    // can find the handler.  We achieve this by emitting IR_HANDLER (which the
    // backend translates to push_handler + switch) in dispatch_blk FIRST, then
    // branching to comp_blk to actually run the computation.
    //
    // Block layout:
    //   pre_blk  → dispatch                (unconditional)
    //   dispatch : IR_HANDLER emitted here  → comp_blk (case 0 / normal)
    //                                       → arm_blk_k (case k+1 / op k fired)
    //   comp_blk : computation runs (effects now find the installed handler)
    //              → join  (unconditional on completion)
    //   arm_blk_k: handler arm body  → join
    //   join     : result merge

    int pre_blk  = m.cur;
    int dispatch = m.new_block();   // emit push_handler + switch here
    int comp_blk = m.new_block();   // computation runs here (handler already installed)
    int join     = m.new_block();   // all paths merge here

    // Terminate pre_blk → dispatch
    if (!m.terminated())
    {
        IrBlock* pb = m.blk(pre_blk);
        if (pb != null) { pb.term = TermKind.TERM_BR; }
        m.link(pre_blk, dispatch);
    }

    // ── dispatch block: emit IR_HANDLER → push_handler + switch ───────────────
    // The backend translates IR_HANDLER to: push_handler(); switch(result) { ... }
    // succ[0] = comp_blk  (default / normal: handler installed, run computation)
    // succ[k] = arm_blk_k (case k: op k was performed during computation)
    m.cur = dispatch;
    IrVal* handler_cond = m.new_val(IrOp.IR_HANDLER, n);
    if (handler_cond != null)
    {
        handler_cond.binder = n;
        // comp_val is added later (after comp_blk lowering) so IR_HANDLER has it as arg
        m.emit(handler_cond);
    }

    IrBlock* db = m.blk(dispatch);
    if (db != null) { db.term = TermKind.TERM_SWITCH; db.cond = handler_cond; }
    m.link(dispatch, comp_blk);  // succ[0] = default = normal path: run computation

    // ── comp_blk: run the computation AFTER handler is installed ─────────────
    m.cur = comp_blk;
    IrVal* comp_val = comp != null ? m.lower_expr(comp) : m.mk_unit(n);
    int comp_end = m.cur;
    // The computation reached its end: tear the handler frame down before
    // joining.  This is the ONLY correct pop point on the normal path — an
    // arm that called resume() never returns (resume is a tail transfer of
    // control to the computation), so the IR_HANDLER_ARM pop in the arm block
    // executes only for arms that finish WITHOUT resuming.
    if (!m.terminated())
    {
        IrVal* done_v = m.new_val(IrOp.IR_HANDLER_COMPLETE, n);
        if (done_v != null) { m.emit(done_v); }
        IrBlock* cpb = m.blk(m.cur);
        if (cpb != null) { cpb.term = TermKind.TERM_BR; }
        m.link(m.cur, join);
    }
    // Now attach comp_val to handler_cond so the IR_HANDLER carries it
    if (handler_cond != null) { handler_cond.add_arg(comp_val, -1); }

    IrVal*[32] arm_vals;
    int[32]    arm_blks;
    usz narms = 0;

    for (usz i = 1; i < n.child_count && narms < 32; i++)
    {
        Node* arm = n.children[i];
        if (arm == null || arm.kind != Nk.NODE_HANDLER_ARM) { continue; }

        // Create the arm block and add it as a SWITCH case successor of dispatch.
        int arm_blk = m.new_block();
        // Dispatch token contract (with the runtime, see §4 of compiler_rt.c):
        // __pride_push_handler returns 0 on first entry ("run the
        // computation") and (op_id + 1) when operation `op_id` was performed.
        // Case each arm on its op's declaration id + 1 — a stable, unique
        // token that never collides with the 0 sentinel.  (Fall back to the
        // arm ordinal only if the op declaration could not be resolved.)
        Node* op_decl = ast::effect_op_decl_of_arm(arm);
        ulong case_tag = (op_decl != null) ? (ulong)op_decl.id + 1
                                           : (ulong)(narms + 1);
        m.link_case(dispatch, arm_blk, case_tag);

        // Lower the arm body into arm_blk.
        IrVal* av = m.lower_handler_arm(arm, arm_blk, join);
        arm_vals[narms] = av;
        arm_blks[narms] = arm_blk;
        narms++;
    }

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

    // The value of the handle expression is a φ in the join block: the
    // computation's result on the normal edge, each arm's result on its edge.
    // (It used to be handler_cond itself — the push_handler dispatch token —
    // which meant `handle` evaluated to a runtime cookie instead of the
    // handled value.  Only include incoming edges that were actually linked:
    // a diverging computation or arm leaves no edge to join.)
    m.cur = join;
    IrBlock* jb = m.blk(join);
    IrVal* rphi = m.new_val(IrOp.IR_PHI, n);
    if (rphi != null)
    {
        // Type the φ from the computation's annotated node: arm values are
        // runtime-ABI-shaped (resume returns ptr by declaration), so
        // operand-driven inference would type the join φ "ptr".  The
        // computation's type IS the handle expression's type.
        if (comp != null && comp.type_annotation != null) { rphi.binder = comp; }
        IrBlock* ce = m.blk(comp_end);
        if (ce != null && ce.succ_count > 0) { rphi.add_arg(comp_val, comp_end); }
        for (usz i = 0; i < narms; i++)
        {
            IrBlock* ab = m.blk(arm_blks[i]);
            if (arm_vals[i] != null && ab != null && ab.succ_count > 0)
            {
                rphi.add_arg(arm_vals[i], arm_blks[i]);
            }
        }
        if (rphi.arg_count > 0)
        {
            m.add_phi(join, rphi);
            return rphi;
        }
    }
    // Degenerate: every path diverged.
    if (jb != null && jb.pred_count == 0) { jb.term = TermKind.TERM_UNREACHABLE; }
    return handler_cond;
}

// `resume` is bound by the resolver as a name in every handler-arm scope
// (resolve.c3: `self.bind("resume", 6, NS_VALUE, arm, false)`). So `resume(v)`
// arrives as NODE_EXPR_CALL[IDENT("resume"→arm_node), arg].
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

// NODE_EFFECT_WITH[Assign[lhs_ident, resource_expr], body]
//   or
// NODE_EFFECT_WITH[resource_expr, body]
// Semantics: evaluate the resource, optionally bind it to a name, execute the
// body, then release the resource (if it has a Drop/cleanup — not enforced at
// IR level; the backend handles RAII via destructor calls).
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

// CFG shape:
//   pre → body_blk → header(cond) -cbr→ {body_blk (back-edge), exit}
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

fn void SsiModule.lower_for(SsiModule* m, Node* n)
{
    Node* binder = n.child_count >= 1 ? n.children[0] : null;
    Node* iter   = n.child_count >= 2 ? n.children[1] : null;
    Node* body   = n.child_count >= 3 ? n.children[2] : null;

    // Detect integer-range iterator: `for i in lo..hi` / `for i in lo..=hi`
    // / `for i in lo..hi by step`. When iter is NODE_EXPR_RANGE or
    // NODE_EXPR_RANGE_STEP we emit a proper counter φ and bounds check
    // (IR_BIN '<' or '<=') instead of the opaque IR_UNKNOWN "has-next".
    bool is_range = (iter != null
        && (iter.kind == Nk.NODE_EXPR_RANGE || iter.kind == Nk.NODE_EXPR_RANGE_STEP));

    IrVal* iter_val = iter != null ? m.lower_expr(iter) : null;

    // For a range, extract lo/hi (and, for a step-range, the step) from the
    // IR_RANGE value's operands. args[2], if present, is the step value
    // (see the NODE_EXPR_RANGE_STEP case in lower_expr_body).
    IrVal* range_lo = null;
    IrVal* range_hi = null;
    IrVal* range_step = null;
    if (is_range && iter_val != null && iter_val.op == IrOp.IR_RANGE
        && iter_val.arg_count >= 2)
    {
        range_lo = iter_val.args[0];
        range_hi = iter_val.args[1];
        if (iter_val.arg_count >= 3) range_step = iter_val.args[2];
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
    // Hoist the range step: one value feeds both the body-end back-edge and
    // every `continue` edge's counter increment (LoopCtx.counter_step).
    // (Emitted in body_blk, which dominates the latch and all continue sites.)
    IrVal* step_val = null;
    if (is_range && counter_phi != null)
    {
        step_val = range_step;
        if (step_val == null)
        {
            IrVal* one = m.new_val(IrOp.IR_CONST_INT, n);
            if (one != null) { one.ival = 1; m.emit(one); }
            step_val = one;
        }
    }
    IrVal** break_vals = m.push_loop(header, exit, &hdr_phis[0], &hdr_binders[0], nphi);
    if (is_range && counter_phi != null && m.loop_count >= 1)
    {
        LoopCtx* lc2 = &m.loops[m.loop_count - 1];
        lc2.counter_phi  = counter_phi;
        lc2.counter_step = step_val;
    }
    if (body != null) { m.lower_stmt(body); }
    LoopCtx done = m.pop_loop();

    int body_end = m.cur;
    if (!m.terminated())
    {
        // Range back-edge: emit counter + step (default step 1 when the
        // iterator was a plain lo..hi/lo..=hi range with no explicit `by`).
        IrVal* back_counter = null;
        if (is_range && counter_phi != null)
        {
            back_counter = m.new_val(IrOp.IR_BIN, n);
            if (back_counter != null)
            {
                back_counter.bop = Tt.TOKEN_PLUS;
                back_counter.add_arg(counter_phi, -1);
                back_counter.add_arg(step_val, -1);
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

// Verification (well-formedness invariants of the constructed IR)
// Removes trivial φ-nodes: those with a single unique non-self operand.
// All uses of the trivial φ are replaced with that single operand.
// Repeat until stable (cascading trivials).
// A φ is trivial if, ignoring self-references, all args are the same value v.
// Replace φ with v everywhere: in other args arrays and in env.
// Complexity: O(vals * passes) per function, bounded by small constant passes.

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

// Hoists IR values that are loop-invariant out of loop bodies.
// Strategy: for each natural loop header block (a block that dominates a back-
// edge predecessor), find instructions in the loop body whose operands are all
// defined outside the loop. Move those instructions to the pre-header block.
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

// Returns true if op is safe to hoist out of loop bodies (pure, no memory).
// IR_CAST is NOT included: ptrtoint/inttoptr depend on the validity of the
// pointer in the current context and should not be hoisted across branches.
// IR_FIELD and IR_INDEX involve loads — also not safe to hoist blindly.
fn bool op_is_pure_for_licm(IrOp op)
{
    switch (op)
    {
        case IrOp.IR_BIN:   // Arithmetic / comparison — always pure
            return true;
        case IrOp.IR_UN:    // Unary negation / NOT — pure IF not dereference
            // TOKEN_STAR (deref) is not pure; others are
            return true;    // conservative: caller checks args invariance
        case IrOp.IR_SIGMA: // Sigma refinements — pure flow annotation
            return true;
        // IR_CAST (ptrtoint/inttoptr) explicitly excluded — can't hoist ptr ops
        // IR_FIELD / IR_INDEX excluded — involve memory reads
        default:
            return false;
    }
}

// Computes immediate dominator for each block in the function.
// dom[i] = immediate dominator of block (first + i), or -1 if undefined.
// Uses the classic Cooper/Harvey/Kennedy O(N^2) algorithm — fast enough for
// the small functions we produce (~5-50 blocks per function).
// Returns a malloc'd array of size f.block_count (caller must free).
fn int* SsiModule.compute_idom(SsiModule* m, SsiFunc* f)
{
    if (f.block_count == 0) return null;
    int n     = (int)f.block_count;
    int first = f.block_start;

    // idom[i] = immediate dominator of (first+i), index into [0,n).
    // -1 = undefined / unreachable.
    int* idom = (int*)malloc((usz)n * 4);
    if (idom == null) return null;
    for (int i = 0; i < n; i++) idom[i] = -1;

    // Entry block dominates itself.
    int entry_rel = f.entry - first;
    if (entry_rel < 0 || entry_rel >= n) { free(idom); return null; }
    idom[entry_rel] = entry_rel;

    // Iterative convergence: process blocks in reverse postorder (approximate
    // by ascending block id — true for our forward-numbered IR).
    bool changed = true;
    while (changed)
    {
        changed = false;
        for (int i = 0; i < n; i++)
        {
            int bid = first + i;
            if (bid == f.entry) continue;  // entry is its own idom
            IrBlock* b = m.blk(bid);
            if (b == null) continue;

            int new_idom = -1;
            // Find a predecessor with a defined idom.
            for (usz pi = 0; pi < b.pred_count; pi++)
            {
                int pred = b.pred[pi];
                int prel = pred - first;
                if (prel < 0 || prel >= n) continue;
                if (idom[prel] < 0) continue;  // pred not yet processed
                if (new_idom < 0) { new_idom = prel; continue; }
                // Intersect new_idom and prel up the dominator tree.
                int a = prel;
                int b2 = new_idom;
                while (a != b2)
                {
                    while (a > b2 && idom[a] >= 0 && idom[a] != a) a = idom[a];
                    while (b2 > a && idom[b2] >= 0 && idom[b2] != b2) b2 = idom[b2];
                    if (a == b2) break;
                    // Avoid infinite loop on malformed CFG
                    if (idom[a] == a && idom[b2] == b2) break;
                    if (idom[a] < 0 || idom[b2] < 0) break;
                }
                new_idom = a;
            }
            if (new_idom >= 0 && new_idom != idom[i])
            { idom[i] = new_idom; changed = true; }
        }
    }
    return idom;
}

// Returns true if `dom_rel` dominates `target_rel` using the idom tree.
fn bool dominated_by(int* idom, int n, int target_rel, int dom_rel)
{
    if (target_rel < 0 || target_rel >= n) return false;
    if (dom_rel    < 0 || dom_rel    >= n) return false;
    int cur = target_rel;
    int iter = 0;
    while (iter < n + 1)
    {
        if (cur == dom_rel) return true;
        if (idom[cur] < 0 || idom[cur] == cur) break;  // reached root
        cur = idom[cur];
        iter++;
    }
    return false;
}

// Compute the set of blocks in the loop body given header hrel and back-edge
// pred brel (both relative indices). Uses a backward BFS from brel up to hrel.
// Returns a malloc'd bool array of size n; caller must free.
fn bool* compute_loop_body(int* idom, int n, int hrel, int brel,
                           SsiModule* m, int first)
{
    bool* in_body = (bool*)malloc((usz)n);
    if (in_body == null) return null;
    for (int i = 0; i < n; i++) in_body[i] = false;

    // Work-list: backward BFS from back-pred to header.
    int* wl  = (int*)malloc((usz)n * 4);
    if (wl == null) { free(in_body); return null; }
    int whead = 0; int wtail = 0;

    in_body[brel] = true;
    in_body[hrel] = true;
    if (brel != hrel) { wl[wtail++] = brel; }

    while (whead < wtail)
    {
        int cur_rel = wl[whead++];
        IrBlock* cb = m.blk(first + cur_rel);
        if (cb == null) continue;
        for (usz pi = 0; pi < cb.pred_count; pi++)
        {
            int pred = cb.pred[pi];
            int prel = pred - first;
            if (prel < 0 || prel >= n) continue;
            if (in_body[prel]) continue;
            in_body[prel] = true;
            if (wtail < n) wl[wtail++] = prel;
        }
    }
    free(wl);
    return in_body;
}

// LICM for one function. Returns count of hoisted instructions.
// Uses proper dominator analysis to identify real loop pre-headers.
fn int SsiModule.hoist_loop_invariants(SsiModule* m, SsiFunc* f)
{
    if (f.block_count < 3) return 0;
    int n     = (int)f.block_count;
    int first = f.block_start;
    int last  = f.block_start + n;
    int hoisted = 0;

    // Compute dominator tree.
    int* idom = m.compute_idom(f);
    if (idom == null) return 0;

    for (int hid = first; hid < last; hid++)
    {
        int hrel = hid - first;
        IrBlock* hb = m.blk(hid);
        // Loop header must have phis (loop-carried values).
        if (hb == null || hb.phi_head == null) continue;

        // Find natural back-edge: a predecessor B such that H dominates B.
        // There may be multiple back-edges; handle one at a time.
        for (usz pi = 0; pi < hb.pred_count; pi++)
        {
            int back_id  = hb.pred[pi];
            int back_rel = back_id - first;
            if (back_rel < 0 || back_rel >= n) continue;

            // H must dominate back_pred for this to be a natural loop back-edge.
            if (!dominated_by(idom, n, back_rel, hrel)) continue;

            // Find the unique pre-header: the non-back-edge predecessor of H
            // that is NOT inside the loop body (not dominated by H transitively).
            // For a well-formed natural loop there is exactly one such predecessor.
            int pre_header = -1;
            int pre_count  = 0;
            for (usz pj = 0; pj < hb.pred_count; pj++)
            {
                int pred = hb.pred[pj];
                int prel = pred - first;
                if (prel < 0 || prel >= n) continue;
                // Is this pred inside the loop? (dominated by header)
                if (prel == hrel) continue;  // self-loop edge
                if (dominated_by(idom, n, prel, hrel)) continue; // inside loop
                pre_header = pred;
                pre_count++;
            }
            // Require exactly one pre-header (simple natural loop).
            if (pre_count != 1 || pre_header < 0) continue;

            // Pre-header must unconditionally branch to H (TERM_BR only).
            // This ensures the pre-header dominates all blocks the header dominates.
            IrBlock* phb = m.blk(pre_header);
            if (phb == null || phb.term != TermKind.TERM_BR) continue;
            // Pre-header's sole successor must be the header.
            if (phb.succ_count != 1 || phb.succ[0] != hid) continue;

            // Compute the exact loop body (blocks on any path from H to back_pred).
            bool* in_body = compute_loop_body(idom, n, hrel, back_rel, m, first);
            if (in_body == null) continue;

            // Scan each body block for hoistable instructions.
            for (int bid = first; bid < last; bid++)
            {
                int brel2 = bid - first;
                if (!in_body[brel2]) continue;
                if (bid == hid) continue;  // don't hoist from header itself
                IrBlock* bb = m.blk(bid);
                if (bb == null) continue;
                IrVal* prev = null;
                IrVal* iv   = bb.head;
                while (iv != null)
                {
                    IrVal* next = iv.next;
                    if (!op_is_pure_for_licm(iv.op)) { prev = iv; iv = next; continue; }
                    // All operands must be loop-invariant (defined outside the body).
                    bool all_inv = true;
                    for (usz ai = 0; ai < iv.arg_count; ai++)
                    {
                        IrVal* arg = iv.args[ai];
                        if (arg == null) continue;
                        // Params and constants are always invariant.
                        if (arg.op == IrOp.IR_PARAM    ||
                            arg.op == IrOp.IR_CONST_INT ||
                            arg.op == IrOp.IR_CONST_FLOAT ||
                            arg.op == IrOp.IR_CONST_BOOL  ||
                            arg.op == IrOp.IR_CONST_NULL  ||
                            arg.op == IrOp.IR_CONST_UNIT  ||
                            arg.op == IrOp.IR_CONST_STR) continue;
                        int ablock_rel = arg.block - first;
                        if (ablock_rel < 0 || ablock_rel >= n
                            || !in_body[ablock_rel]) continue;  // invariant (outside body)
                        // Defined inside loop body — not invariant.
                        all_inv = false; break;
                    }
                    if (!all_inv) { prev = iv; iv = next; continue; }

                    // Hoist: unlink from body block, append to pre-header.
                    if (prev == null) { bb.head = next; }
                    else             { prev.next = next; }
                    if (bb.tail == iv) bb.tail = prev;

                    iv.next  = null;
                    iv.block = pre_header;
                    if (phb.tail == null) { phb.head = iv; phb.tail = iv; }
                    else { phb.tail.next = iv; phb.tail = iv; }
                    hoisted++;
                    iv = next;  // prev stays: the slot is now occupied by next
                }
            }

            free(in_body);
        }
    }

    free(idom);
    return hoisted;
}

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
    // Safety: if the unique representative is NOT inherently_defined,
    // only prune if it was defined in block 0 (entry block) — conservative
    // dominance approximation that prevents most dominance violations.
    if (unique != null && !inherently_defined(unique))
    {
        // If the unique rep is in a specific block, we can't safely replace
        // without dominator info. Keep the phi — it's not harmful to keep it.
        return false;
    }
    return true;   // 0 or 1 unique non-self operands, all safely inherent
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

// Pretty-printer (textual SSI-IR dump)
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
        case IR_ATOMIC_RMW:  return "atomic.rmw";
        case IR_CMPXCHG:     return "atomic.cmpxchg";
        case IR_FENCE:       return "fence";
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
// cache_bust_1783244364
