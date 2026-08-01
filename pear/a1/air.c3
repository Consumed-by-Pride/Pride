/*
 AIR — the SP-ERM-e-SSI datatype.

 Semi-Pruned, Exceptional, Range-bounded, Memory-aware, extended Static
 Single Information. This module owns the in-memory form only; the textual
 writer is air_print.c3 and the reader is air_parse.c3 (PEAR.md D3).

 ── Shape ────────────────────────────────────────────────────────────────
   AirModule  owns every function and the value/block arenas
     AirFunc    owns a block list and a parameter list
       AirBlock   an ordered list of value ids + one terminator
         AirValue one SSA definition (an opcode plus operands)

 Values are referred to by `uint` id, never by pointer. Ids are stable
 across growth, pointers are not: the storage is a growable array that
 reallocates (D6). Every `AirValue*` obtained from `AirModule.val()` must be
 treated as invalid the moment another value is added.

 ── Design rules this file exists to enforce ─────────────────────────────

 D2, no sentinel overloading. `ssi_ir.c3` packed six meanings into one
 `.ival` field (-1, -2, -3, 0, 1 and the magic 55555) covering address-of
 mode, array-element update, atomic ordering, field index and sizeof. Its
 r43–r46 bug markers cluster on exactly that. Here every distinct meaning
 is a distinct opcode or a named field. Nothing is a mode flag.

 D6, growable storage. `ssi_ir.c3` caps MAX_OPERANDS at 16 and MAX_IR_VALS
 at 65536 and truncates silently past them. Here operands live in one
 shared arena-backed pool addressed by (offset, count), so an operand list
 has no fixed ceiling. Where a real limit exists it sets `overflowed`,
 which is reported rather than swallowed.

 D1, origin threading. Every value carries `origin`, the AIR value id it
 descends from, so that range and memory facts computed in a2 can still be
 attributed after four conversions. In a1 a freshly built value is its own
 origin; a synthesised value with no antecedent uses AIR_NO_ORIGIN.
*/

module pear_air;

import pfront_core;
import pear_erm;

alias Arena = pfront_core::Arena;

extern fn int   printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn void* realloc(void* p, usz size);
extern fn void  free(void* p);
extern fn void* memcpy(void* dst, void* src, usz n);

// ════════════════════════════════════════════════════════════════════════
// IDS
// ════════════════════════════════════════════════════════════════════════

/*
 Id 0 is reserved as "no value" for every id space. A real value, block or
 function always has an id >= 1. This is the one reserved encoding in AIR
 and it means exactly one thing everywhere it appears, which is the point
 of D2: `0` is never also "the first element" or "unset flag" or "unit".
*/
const uint AIR_NO_VALUE  = 0;
const uint AIR_NO_BLOCK  = 0;
const uint AIR_NO_FUNC   = 0;

/*
 D1. A value that descends from no earlier value — a constant materialised
 by a lowering rule, a φ inserted by SSA construction — records this rather
 than pointing at an unrelated id. `--verify-facts` counts these, so an
 origin that is merely *forgotten* shows up as a measurement, not as a
 silently wrong attribution.
*/
const uint AIR_NO_ORIGIN = 0;

// ════════════════════════════════════════════════════════════════════════
// OPCODES
// ════════════════════════════════════════════════════════════════════════

/*
 One opcode per distinct operation. Where ssi_ir.c3 used one opcode plus a
 mode field, AIR uses separate opcodes — AIR_STORE_PTR / AIR_STORE_FIELD /
 AIR_STORE_INDEX rather than one AIR_STORE with three operand conventions.
 The operand contract for each is stated in its comment and is checked by
 verify.c3.
*/
enum AirOp : int (String mnemonic)
{
    // ── constants ───────────────────────────────────────────────────────
    AIR_CONST_INT { "const.int" },     // payload.ival
    AIR_CONST_FLOAT { "const.float" },   // payload.fval
    AIR_CONST_BOOL { "const.bool" },    // payload.ival, 0 or 1
    AIR_CONST_STR { "const.str" },     // payload.name = interned text
    AIR_CONST_NULL { "const.null" },    // no payload
    AIR_CONST_UNIT { "const.unit" },    // no payload

    // ── roots ───────────────────────────────────────────────────────────
    AIR_PARAM { "param" },         // function or block parameter; payload.name

    // ── pure arithmetic ─────────────────────────────────────────────────
    AIR_BIN { "bin" },           // operands[0], operands[1]; payload.op
    AIR_UN { "un" },            // operands[0];              payload.op
    AIR_CAST { "cast" },          // operands[0];              payload.name = target type

    // ── aggregates ──────────────────────────────────────────────────────
    AIR_TUPLE { "tuple" },         // operands[0..n]
    AIR_ARRAY { "array" },         // operands[0..n]
    AIR_STRUCT { "struct" },        // operands[0..n]; payload.name = type name

    /*
     Reads. Three opcodes, not one with a mode flag.
       LOAD_FIELD  operands[0] = base aggregate, payload.index = field slot
       LOAD_INDEX  operands[0] = base, operands[1] = index value
       LOAD_PTR    operands[0] = pointer
     ssi_ir.c3 distinguished these by sign-encoding the field index, which
     is the r43–r46 bug cluster.
    */
    AIR_LOAD_FIELD { "load.field" },
    AIR_LOAD_INDEX { "load.index" },
    AIR_LOAD_PTR { "load.ptr" },

    /*
     Address-of, kept separate from the loads. In ssi_ir.c3 "give me the
     address instead of the value" was `.ival = -2` on the same opcode.
    */
    AIR_ADDR_FIELD { "addr.field" },    // operands[0] = base; payload.index
    AIR_ADDR_INDEX { "addr.index" },    // operands[0] = base, operands[1] = index
    AIR_ADDR_OF { "addr.of" },       // operands[0] = a place

    // ── writes (effectful; never deleted by DCE without a purity proof) ──
    AIR_STORE_PTR { "store.ptr" },     // operands[0] = ptr,  operands[1] = value
    AIR_STORE_FIELD { "store.field" },   // operands[0] = base, operands[1] = value; payload.index
    AIR_STORE_INDEX { "store.index" },   // operands[0] = base, operands[1] = value, operands[2] = index

    // ── calls ───────────────────────────────────────────────────────────
    AIR_CALL { "call" },          // operands[0] = callee, operands[1..] = args
    AIR_CALL_DIRECT { "call.direct" },   // payload.name = callee; operands[0..] = args

    // ── memory ──────────────────────────────────────────────────────────
    AIR_ALLOC { "alloc" },         // operands[0] = size
    AIR_FREE { "free" },          // operands[0] = ptr

    /*
     Globals are ordinary M-tracked memory from the start. ssi_ir.c3 bolted
     IR_GLOAD / IR_GSTORE on late (marker r56d) because globals had not been
     considered until they were needed.
    */
    AIR_GLOBAL_ADDR { "global.addr" },   // payload.name

    // ── SSI: the merge and the split ────────────────────────────────────
    /*
     φ, a merge. operands[i] is the value arriving from incoming_block[i].
     The two arrays are parallel and verify.c3 checks that they are the same
     length and that the block list matches the CFG's predecessor list as a
     set. ssi_ir.c3 kept the predecessor list in a side array that could
     drift out of sync (marker r44, stale φ slots reused across sibling
     loops); here they are allocated together and grow together.
    */
    AIR_PHI { "phi" },

    /*
     σ, a split. The `e` of e-SSI. One σ per outgoing edge of a splitting
     point, so each successor sees a distinct name carrying the fact that
     reaching *that* edge implies. operands[0] is the value being split;
     payload.fact names the refinement.
    */
    AIR_SIGMA { "sigma" },

    /*
     π, the `E` of SP-ERM-e-SSI (Choi/Cytron/Ferrante). A σ splits on a
     CONDITIONAL; a π splits across a POTENTIALLY-DIVERGING OPERATION.

     `%p2 = pi %p1` after a dereference names "the pointer, on the path
     where the dereference did not fault", carrying nonnull. After a
     checked index it carries inbounds; after a division, nonzero.

     LLVM has no equivalent. A faulting operation there is an ordinary
     instruction, so "this was already checked" is a property of a program
     POINT that every consumer must re-derive, rather than a property of a
     NAME that travels with the value. That is the main reason a redundant
     bounds check survives in .ll and can be renamed away here.

     operands[0] is the guarded value, operands[1] the operation that
     guarded it, so DCE cannot float the π above its own justification.
    */
    AIR_PI { "pi" },

    /*
     M. Memory as an explicitly versioned resource, in the IR rather than
     in a side analysis. See pear_erm for why this differs from LLVM's
     MemorySSA, which is rebuilt on demand and never serialised.

     MEM_ENTRY defines version 0; MEM_PHI joins versions at a control-flow
     join exactly as a scalar φ does, with a parallel incoming-block list.
    */
    AIR_MEM_ENTRY { "mem.entry" },
    AIR_MEM_PHI { "mem.phi" },

    // ── effects (backend-agnostic, as in ssi_ir.c3 — that part was right) ─
    AIR_PERFORM { "perform" },       // payload.name = Effect.op; operands = args
    AIR_HANDLE { "handle" },        // operands[0] = computation, operands[1..] = arms
    AIR_HANDLE_ARM { "handle.arm" },    // operands[0] = body
    /*
     resume is a re-entry edge, not a call. PEAR.md section 3 calls this out:
     it has no exception-language analogue and is closer to a coroutine
     yield, so it gets its own construct rather than being modelled as a
     call that happens to return twice.
    */
    AIR_RESUME { "resume" },        // operands[0] = value to resume with

    // ── escape hatch ────────────────────────────────────────────────────
    /*
     Lowering must be TOTAL. A construct a1 cannot yet translate becomes
     AIR_UNKNOWN with its operands preserved, so the IR stays well-formed
     and the gap is visible in the dump and countable in the stats, rather
     than crashing or silently dropping code.
    */
    AIR_UNKNOWN { "unknown" }
}

/*
 Binary and unary operators live in their own enum rather than being raw
 token ids. a2 pattern-matches on these; a raw token id would couple the
 middle end to the lexer's numbering (D5).
*/
enum AirBinOp : int (String mnemonic)
{
    ABO_ADD { "add" },   ABO_SUB { "sub" },   ABO_MUL { "mul" },
    ABO_DIV { "div" },   ABO_MOD { "mod" },
    ABO_AND { "and" },   ABO_OR { "or" },    ABO_XOR { "xor" },
    ABO_SHL { "shl" },   ABO_SHR { "shr" },
    ABO_EQ { "eq" },    ABO_NE { "ne" },
    ABO_LT { "lt" },    ABO_LE { "le" },    ABO_GT { "gt" },  ABO_GE { "ge" },
    ABO_LAND { "land" },  ABO_LOR { "lor" },

    /*
     Pride distinguishes three overflow behaviours per arithmetic operator
     (spec: `+?` checked, `+%` wrapping, `+|` saturating). They are NOT
     interchangeable and must not collapse onto the plain operator:

       add   overflow is undefined; a2 may assume it does not happen
       addc  checked; yields a value and an overflow flag (C23 ckd_add)
       addw  wrapping; defined two's-complement, a2 may NOT assume no
             overflow, and the range transfer function must go to top
       adds  saturating; clamps at the type bound, so the result range is
             bounded by the type even when the inputs are unbounded

     Collapsing them onto `add` would let a2 delete an overflow check the
     programmer explicitly asked for, which is a miscompile.
    */
    ABO_ADDC { "addc" },  ABO_SUBC { "subc" },  ABO_MULC { "mulc" },
    ABO_ADDW { "addw" },  ABO_SUBW { "subw" },  ABO_MULW { "mulw" },
    ABO_ADDS { "adds" },  ABO_SUBS { "subs" },  ABO_MULS { "muls" },

    ABO_NONE { "?" }
}

enum AirUnOp : int (String mnemonic)
{
    AUO_NEG { "neg" },  AUO_NOT { "not" },  AUO_BNOT { "bnot" },
    AUO_NONE { "?" }
}

// ════════════════════════════════════════════════════════════════════════
// TERMINATORS
// ════════════════════════════════════════════════════════════════════════

/*
 A block ends in exactly one terminator. `TERM_OPEN` means the block is
 still being built; verify.c3 rejects any reachable block still open, which
 is the check that catches a lowering path that forgot to close a branch.
*/
enum AirTerm : int (String mnemonic)
{
    TERM_OPEN { "open" },
    TERM_RET { "ret" },         // ret_value (may be AIR_NO_VALUE for unit)
    TERM_JUMP { "jump" },        // succ[0]
    TERM_BRANCH { "branch" },      // cond, succ[0] = then, succ[1] = else
    TERM_SWITCH { "switch" },      // cond, succ[0..n]; case values in the block
    /*
     Divergent terminators. `ub!`, `trap` and `unreachable` are ⊥-typed:
     control does not leave the block by any edge. They are distinct
     opcodes because a2 treats them differently — `trap` is a real runtime
     call, `unreachable` is a promise to the optimiser, `ub!` is the
     programmer asserting the same thing explicitly (and it requires an
     enclosing `unsafe`, which pfront already checks).
    */
    TERM_UNREACHABLE { "unreachable" },
    TERM_TRAP { "trap" },
    TERM_UB { "ub" }
}

// ════════════════════════════════════════════════════════════════════════
// REFINEMENTS — what a σ records
// ════════════════════════════════════════════════════════════════════════

/*
 The fact that holds on the edge a σ guards. This is the seed for `R`
 (ranges) and part of the seed for `E` (the fault twin). Kept as a small
 named enum rather than a pointer to an AST node: a2 must be able to read
 it without reaching back into pfront (D5), and the AST node it came from
 is already recoverable through `origin`.
*/
enum AirFact : int (String mnemonic)
{
    FACT_NONE { "none" },
    // from `if x < e` and friends — the e-SSA facts
    FACT_LT { "lt" },
    FACT_LE { "le" },
    FACT_GT { "gt" },
    FACT_GE { "ge" },
    FACT_EQ { "eq" },
    FACT_NE { "ne" },
    // from a null test, and from the non-fault edge of a dereference
    FACT_NONNULL { "nonnull" },
    FACT_NULL { "null" },
    // from the non-fault edge of `/`, `%`
    FACT_NONZERO { "nonzero" },
    // from the non-fault edge of `a[i]`
    FACT_INBOUNDS { "inbounds" },
    // from a match arm
    FACT_VARIANT { "variant" },
    // the fault twin itself: this edge is taken only when the op faults
    FACT_FAULT { "fault" }
}

// ════════════════════════════════════════════════════════════════════════
// PAYLOAD
// ════════════════════════════════════════════════════════════════════════

/*
 D2 in structural form. Rather than one integer field reinterpreted per
 opcode, each meaning has its own named field. The cost is a few bytes per
 value; the benefit is that reading a dump never requires knowing which
 interpretation is live.

 Which fields an opcode uses is documented on the opcode above and checked
 by verify.c3.
*/
struct AirPayload
{
    long      ival;      // CONST_INT, CONST_BOOL
    double    fval;      // CONST_FLOAT
    uint      name;      // interned: CONST_STR, PARAM, CAST, STRUCT, CALL_DIRECT,
                         //           GLOBAL_ADDR, PERFORM
    uint      index;     // field slot: LOAD_FIELD, ADDR_FIELD, STORE_FIELD
    AirBinOp  op;        // BIN
    AirUnOp   uop;       // UN
    AirFact   fact;      // SIGMA
}

fn void AirPayload.clear(AirPayload* p)
{
    p.ival  = 0;
    p.fval  = 0.0;
    p.name  = 0;
    p.index = 0;
    p.op    = AirBinOp.ABO_NONE;
    p.uop   = AirUnOp.AUO_NONE;
    p.fact  = AirFact.FACT_NONE;
}

// ════════════════════════════════════════════════════════════════════════
// VALUE
// ════════════════════════════════════════════════════════════════════════

/*
 One SSA definition.

 Operands are NOT stored inline. They live in the module's shared operand
 pool as a (op_off, op_count) slice, which is what removes ssi_ir.c3's
 MAX_OPERANDS 16 ceiling (D6). A φ additionally owns a parallel slice of
 incoming block ids at the same offset in the module's block-operand pool,
 so the two can never drift apart in length.
*/
struct AirValue
{
    uint     id;
    AirOp    op;
    uint     block;        // the block this value is defined in

    usz      op_off;       // slice into AirModule.operands
    usz      op_count;
    usz      inc_off;      // PHI only: slice into AirModule.phi_blocks
    usz      inc_count;    // PHI only: must equal op_count

    AirPayload p;

    /*
     D1. The AIR value this descends from. In a1 a value built directly
     from the AST is its own origin. A conversion in a later stage copies
     this field forward; it never invents one.
    */
    uint     origin;

    /*
     ERM. The R (range, known bits, nullness, width), the M (memory
     version and alias scope) and the SP classification, carried on EVERY
     version rather than as optional metadata.

     This is the substance of "denser than .ll". LLVM carries `!range` on
     a few instruction kinds, recomputes known-bits from scratch in
     ValueTracking every time it is asked, and cannot serialise MemorySSA
     at all. Here all three are part of the value, printed in the text and
     round-tripped, so a fact established in a2 is still readable at a5.
    */
    pear_erm::Facts facts;

    /*
     This slot HELD a φ that was proven trivial and neutralised in place.
     It is a hole, not an instruction.

     The slot is kept rather than deleted because removing an element from
     the middle of a block invalidates every position other code holds.
     But a hole must not count as a "non-φ value" when the next φ looks
     for its insertion point, or the all-φ-come-first invariant breaks.
     Pattern-matching on CONST_UNIT instead would wrongly skip a genuine
     unit the user wrote.
    */
    bool     is_phi_hole;

    // Source position, carried purely for diagnostics. Never semantic.
    int      line;
    int      col;
}

// ════════════════════════════════════════════════════════════════════════
// BLOCK
// ════════════════════════════════════════════════════════════════════════

/*
 A basic block: an ordered list of value ids, then one terminator.

 `values`, `succ` and `pred` are all growable arrays owned by the block.
 ssi_ir.c3 capped edges at 32; a `match` over a wide enum exceeds that, and
 it truncated silently.
*/
struct AirBlock
{
    uint   id;
    uint   func;
    uint   name;          // interned label, 0 for an anonymous block

    uint*  values;        // value ids, in order
    usz    value_count;
    usz    value_cap;

    AirTerm term;
    uint    term_value;   // RET: the returned value. BRANCH/SWITCH: the scrutinee.

    uint*  succ;
    usz    succ_count;
    usz    succ_cap;

    uint*  pred;
    usz    pred_count;
    usz    pred_cap;

    /*
     SWITCH only: one case value per successor, parallel to `succ`. The
     final successor is the default arm when `has_default` is set.
    */
    long*  case_vals;
    usz    case_count;
    usz    case_cap;
    bool   has_default;

    bool   reachable;     // filled in by verify.c3
}

// ════════════════════════════════════════════════════════════════════════
// FUNCTION
// ════════════════════════════════════════════════════════════════════════

struct AirFunc
{
    uint   id;
    uint   name;          // interned
    uint   entry;         // block id
    bool   is_pub;

    uint*  blocks;        // block ids, in creation order
    usz    block_count;
    usz    block_cap;

    uint*  params;        // AIR_PARAM value ids, in declaration order
    usz    param_count;
    usz    param_cap;

    int    line;
    int    col;
}

// ════════════════════════════════════════════════════════════════════════
// MODULE
// ════════════════════════════════════════════════════════════════════════

/*
 Owns every value, block and function, plus the two shared operand pools.

 Everything is indexed from 1 so that 0 can mean "none" in every id space
 (see AIR_NO_VALUE). Slot 0 of each array is a reserved dummy and is never
 handed out.

 `overflowed` is set if any growth request failed. It is REPORTED rather
 than being allowed to silently truncate a list (D6). A pass seeing it set
 must degrade to "unknown", never to "wrong".
*/
struct AirModule
{
    uint        name;
    Arena*      arena;
    pfront_core::Interner* interner;

    AirValue*   values;
    usz         value_count;
    usz         value_cap;

    AirBlock*   blocks;
    usz         block_count;
    usz         block_cap;

    AirFunc*    funcs;
    usz         func_count;
    usz         func_cap;

    // Shared operand pool. A value's operands are operands[op_off .. +op_count].
    uint*       operands;
    usz         operand_count;
    usz         operand_cap;

    // Parallel pool for φ incoming-block ids.
    uint*       phi_blocks;
    usz         phi_block_count;
    usz         phi_block_cap;

    bool        overflowed;
}

// ── growth helpers ──────────────────────────────────────────────────────

/*
 These use malloc/realloc rather than the arena because they must be able
 to GROW. The arena is a bump allocator with no free and no resize, which
 is right for AST nodes (write once, never resized) and wrong for a value
 array that doubles. The arena is still used for anything write-once.
*/
fn bool grow_u32(uint** arr, usz* cap, usz need)
{
    if (need <= *cap) { return true; }
    usz nc = *cap == 0 ? 8 : *cap;
    while (nc < need) { nc = nc * 2; }
    uint* p = (uint*)realloc((void*)*arr, nc * uint::size);
    if (p == null) { return false; }
    *arr = p;
    *cap = nc;
    return true;
}

fn bool grow_i64(long** arr, usz* cap, usz need)
{
    if (need <= *cap) { return true; }
    usz nc = *cap == 0 ? 8 : *cap;
    while (nc < need) { nc = nc * 2; }
    long* p = (long*)realloc((void*)*arr, nc * long::size);
    if (p == null) { return false; }
    *arr = p;
    *cap = nc;
    return true;
}

fn bool AirModule.init(AirModule* m, Arena* a, pfront_core::Interner* it, uint name)
{
    m.name = name;
    m.arena = a;
    m.interner = it;
    m.values = null;   m.value_count = 0;   m.value_cap = 0;
    m.blocks = null;   m.block_count = 0;   m.block_cap = 0;
    m.funcs  = null;   m.func_count  = 0;   m.func_cap  = 0;
    m.operands = null; m.operand_count = 0; m.operand_cap = 0;
    m.phi_blocks = null; m.phi_block_count = 0; m.phi_block_cap = 0;
    m.overflowed = false;

    // Reserve slot 0 in each id space so 0 always means "none".
    if (!m.reserve_values(1) || !m.reserve_blocks(1) || !m.reserve_funcs(1))
    {
        return false;
    }
    m.value_count = 1;
    m.block_count = 1;
    m.func_count  = 1;
    return true;
}

fn bool AirModule.reserve_values(AirModule* m, usz need)
{
    if (need <= m.value_cap) { return true; }
    usz nc = m.value_cap == 0 ? 64 : m.value_cap;
    while (nc < need) { nc = nc * 2; }
    AirValue* p = (AirValue*)realloc((void*)m.values, nc * AirValue::size);
    if (p == null) { m.overflowed = true; return false; }
    m.values = p;
    m.value_cap = nc;
    return true;
}

fn bool AirModule.reserve_blocks(AirModule* m, usz need)
{
    if (need <= m.block_cap) { return true; }
    usz nc = m.block_cap == 0 ? 32 : m.block_cap;
    while (nc < need) { nc = nc * 2; }
    AirBlock* p = (AirBlock*)realloc((void*)m.blocks, nc * AirBlock::size);
    if (p == null) { m.overflowed = true; return false; }
    m.blocks = p;
    m.block_cap = nc;
    return true;
}

fn bool AirModule.reserve_funcs(AirModule* m, usz need)
{
    if (need <= m.func_cap) { return true; }
    usz nc = m.func_cap == 0 ? 16 : m.func_cap;
    while (nc < need) { nc = nc * 2; }
    AirFunc* p = (AirFunc*)realloc((void*)m.funcs, nc * AirFunc::size);
    if (p == null) { m.overflowed = true; return false; }
    m.funcs = p;
    m.func_cap = nc;
    return true;
}

fn void AirModule.destroy(AirModule* m)
{
    /*
     Start at 1, not 0. Slot 0 of each array is the reserved "none" dummy
     that init() never writes to: it is raw malloc memory, so its pointer
     fields hold garbage and freeing them aborts the process.

     This crashed the very first multi-block fixture with `free(): invalid
     pointer`, and it crashed AFTER all the test output had been buffered,
     so the visible symptom was a silent abort with no diagnostics at all.
     Slot 0 is skipped everywhere else in this file (val/blk/fun all reject
     id 0); destroy was the one loop that forgot.
    */
    for (usz i = 1; i < m.block_count; i++)
    {
        AirBlock* b = &m.blocks[i];
        if (b.values != null)    { free((void*)b.values); }
        if (b.succ != null)      { free((void*)b.succ); }
        if (b.pred != null)      { free((void*)b.pred); }
        if (b.case_vals != null) { free((void*)b.case_vals); }
    }
    for (usz i = 1; i < m.func_count; i++)
    {
        AirFunc* f = &m.funcs[i];
        if (f.blocks != null) { free((void*)f.blocks); }
        if (f.params != null) { free((void*)f.params); }
    }
    if (m.values != null)     { free((void*)m.values); }
    if (m.blocks != null)     { free((void*)m.blocks); }
    if (m.funcs != null)      { free((void*)m.funcs); }
    if (m.operands != null)   { free((void*)m.operands); }
    if (m.phi_blocks != null) { free((void*)m.phi_blocks); }
    m.values = null; m.blocks = null; m.funcs = null;
    m.operands = null; m.phi_blocks = null;
    m.value_count = 0; m.block_count = 0; m.func_count = 0;
    m.operand_count = 0; m.phi_block_count = 0;
    m.value_cap = 0; m.block_cap = 0; m.func_cap = 0;
    m.operand_cap = 0; m.phi_block_cap = 0;
}

// ── accessors ───────────────────────────────────────────────────────────

/*
 Return the value/block/func with this id, or null.

 The returned pointer is invalidated by the next add_* call, because the
 backing array may reallocate. Callers hold ids across mutation, never
 pointers. This is stated here because it is the single easiest way to
 introduce a use-after-free in this design.
*/
fn AirValue* AirModule.val(AirModule* m, uint id)
{
    if (id == AIR_NO_VALUE || (usz)id >= m.value_count) { return null; }
    return &m.values[id];
}

fn AirBlock* AirModule.blk(AirModule* m, uint id)
{
    if (id == AIR_NO_BLOCK || (usz)id >= m.block_count) { return null; }
    return &m.blocks[id];
}

fn AirFunc* AirModule.fun(AirModule* m, uint id)
{
    if (id == AIR_NO_FUNC || (usz)id >= m.func_count) { return null; }
    return &m.funcs[id];
}

// Operand i of a value, or AIR_NO_VALUE if out of range.
fn uint AirModule.operand(AirModule* m, uint vid, usz i)
{
    AirValue* v = m.val(vid);
    if (v == null || i >= v.op_count) { return AIR_NO_VALUE; }
    return m.operands[v.op_off + i];
}

// The block operand i of a φ arrives from.
fn uint AirModule.phi_incoming(AirModule* m, uint vid, usz i)
{
    AirValue* v = m.val(vid);
    if (v == null || v.op != AirOp.AIR_PHI || i >= v.inc_count) { return AIR_NO_BLOCK; }
    return m.phi_blocks[v.inc_off + i];
}

// ── construction ────────────────────────────────────────────────────────

fn uint AirModule.new_func(AirModule* m, uint name, int line, int col)
{
    if (!m.reserve_funcs(m.func_count + 1)) { return AIR_NO_FUNC; }
    uint id = (uint)m.func_count;
    m.func_count = m.func_count + 1;
    AirFunc* f = &m.funcs[id];
    f.id = id;
    f.name = name;
    f.entry = AIR_NO_BLOCK;
    f.is_pub = false;
    f.blocks = null; f.block_count = 0; f.block_cap = 0;
    f.params = null; f.param_count = 0; f.param_cap = 0;
    f.line = line;
    f.col = col;
    return id;
}

fn uint AirModule.new_block(AirModule* m, uint func, uint name)
{
    if (!m.reserve_blocks(m.block_count + 1)) { return AIR_NO_BLOCK; }
    uint id = (uint)m.block_count;
    m.block_count = m.block_count + 1;
    AirBlock* b = &m.blocks[id];
    b.id = id;
    b.func = func;
    b.name = name;
    b.values = null; b.value_count = 0; b.value_cap = 0;
    b.term = AirTerm.TERM_OPEN;
    b.term_value = AIR_NO_VALUE;
    b.succ = null; b.succ_count = 0; b.succ_cap = 0;
    b.pred = null; b.pred_count = 0; b.pred_cap = 0;
    b.case_vals = null; b.case_count = 0; b.case_cap = 0;
    b.has_default = false;
    b.reachable = false;

    AirFunc* f = m.fun(func);
    if (f != null)
    {
        if (!grow_u32(&f.blocks, &f.block_cap, f.block_count + 1))
        {
            m.overflowed = true;
        }
        else
        {
            f.blocks[f.block_count] = id;
            f.block_count = f.block_count + 1;
        }
    }
    return id;
}

/*
 Copy `n` operands into the shared pool and return the offset.

 Taking the operands as an array up front, rather than appending one at a
 time, is what keeps a value's slice contiguous. An "add one operand later"
 API would either fragment the pool or force a copy on every append, and
 the fragmenting version is how a φ's operand list gets out of step with
 its incoming-block list.
*/
fn usz AirModule.push_operands(AirModule* m, uint* ops, usz n)
{
    if (n == 0) { return 0; }
    if (!grow_u32(&m.operands, &m.operand_cap, m.operand_count + n))
    {
        m.overflowed = true;
        return 0;
    }
    usz off = m.operand_count;
    for (usz i = 0; i < n; i++) { m.operands[off + i] = ops[i]; }
    m.operand_count = m.operand_count + n;
    return off;
}

fn usz AirModule.push_phi_blocks(AirModule* m, uint* bs, usz n)
{
    if (n == 0) { return 0; }
    if (!grow_u32(&m.phi_blocks, &m.phi_block_cap, m.phi_block_count + n))
    {
        m.overflowed = true;
        return 0;
    }
    usz off = m.phi_block_count;
    for (usz i = 0; i < n; i++) { m.phi_blocks[off + i] = bs[i]; }
    m.phi_block_count = m.phi_block_count + n;
    return off;
}

/*
 Create a value and append it to `block`.

 `origin` follows D1: pass AIR_NO_ORIGIN for a genuinely new construct and
 the value becomes its own origin; pass an existing id to record descent.
*/
fn uint AirModule.new_value(AirModule* m, uint block, AirOp op,
                            uint* ops, usz n_ops, uint origin,
                            int line, int col)
{
    if (!m.reserve_values(m.value_count + 1)) { return AIR_NO_VALUE; }
    usz off = m.push_operands(ops, n_ops);
    if (n_ops > 0 && off == 0 && m.overflowed) { return AIR_NO_VALUE; }

    uint id = (uint)m.value_count;
    m.value_count = m.value_count + 1;
    AirValue* v = &m.values[id];
    v.id = id;
    v.op = op;
    v.block = block;
    v.op_off = off;
    v.op_count = n_ops;
    v.inc_off = 0;
    v.inc_count = 0;
    v.p.clear();
    // realloc'd storage is raw memory: an uninitialised Facts would make
    // every new value claim whatever ranges happened to be in the heap.
    v.facts = pear_erm::facts_unknown();
    v.is_phi_hole = false;
    v.origin = origin == AIR_NO_ORIGIN ? id : origin;
    v.line = line;
    v.col = col;

    AirBlock* b = m.blk(block);
    if (b != null)
    {
        if (!grow_u32(&b.values, &b.value_cap, b.value_count + 1))
        {
            m.overflowed = true;
        }
        else
        {
            b.values[b.value_count] = id;
            b.value_count = b.value_count + 1;
        }
    }
    return id;
}

/*
 A φ. The operand list and the incoming-block list are pushed together and
 their lengths are equal by construction — the failure ssi_ir.c3 hit at
 marker r44 (a stale φ slot counter reused across sibling loops) is not
 expressible here.
*/
fn uint AirModule.new_phi(AirModule* m, uint block, uint* ops, uint* incoming,
                          usz n, uint origin, int line, int col)
{
    uint id = m.new_value(block, AirOp.AIR_PHI, ops, n, origin, line, col);
    if (id == AIR_NO_VALUE) { return id; }
    usz off = m.push_phi_blocks(incoming, n);
    if (n > 0 && off == 0 && m.overflowed) { return AIR_NO_VALUE; }
    AirValue* v = &m.values[id];
    v.inc_off = off;
    v.inc_count = n;
    return id;
}

// A σ split: one name per outgoing edge, carrying the fact that edge implies.
/*
 Seed R for a constant. Every other range in the function is derived from
 these by the transfer functions, so getting the base case right is what
 makes the whole lattice non-trivial.
*/
fn void AirModule.set_const_int(AirModule* m, uint vid, long v, int width, bool is_signed)
{
    AirValue* av = m.val(vid);
    if (av == null) { return; }
    av.p.ival = v;
    av.facts.range = pear_erm::r_const(v);
    av.facts.bits = pear_erm::kb_const(v);
    av.facts.width = width;
    av.facts.is_signed = is_signed;
}

fn uint AirModule.new_sigma(AirModule* m, uint block, uint src, AirFact fact,
                            int line, int col)
{
    uint[1] ops;
    ops[0] = src;
    // D1: a σ is a RENAME of an existing value, so it inherits that value's
    // origin rather than starting a new lineage. Without this, every range
    // fact learned about `x` would be lost the moment `x` was split.
    uint org = AIR_NO_ORIGIN;
    AirValue* s = m.val(src);
    if (s != null) { org = s.origin; }
    uint id = m.new_value(block, AirOp.AIR_SIGMA, &ops[0], 1, org, line, col);
    if (id == AIR_NO_VALUE) { return id; }
    m.values[id].p.fact = fact;
    // Inherit the source's facts; the caller narrows them with
    // refine_sigma once the comparison bound is known.
    AirValue* sv2 = m.val(src);
    if (sv2 != null) { m.values[id].facts = sv2.facts; }
    return id;
}

/*
 Narrow a σ's range using the bound it was split on.

 Split from new_sigma because the bound is not always a literal: `if x < n`
 gives a symbolic bound that only a2 can resolve, and a σ created now may
 be refined later. Keeping the two apart means neither has to guess.
*/
fn void AirModule.refine_sigma(AirModule* m, uint vid, long bound)
{
    AirValue* v = m.val(vid);
    if (v == null || v.op != AirOp.AIR_SIGMA) { return; }
    switch (v.p.fact)
    {
        case FACT_LT: v.facts.range = pear_erm::r_refine_lt(v.facts.range, bound);
        case FACT_LE: v.facts.range = pear_erm::r_refine_le(v.facts.range, bound);
        case FACT_GT: v.facts.range = pear_erm::r_refine_gt(v.facts.range, bound);
        case FACT_GE: v.facts.range = pear_erm::r_refine_ge(v.facts.range, bound);
        case FACT_EQ: v.facts.range = pear_erm::r_refine_eq(v.facts.range, bound);
        case FACT_NE: v.facts.range = pear_erm::r_refine_ne(v.facts.range, bound);
        case FACT_NONNULL: v.facts.nullness = pear_erm::Nullness.NULL_NEVER;
        case FACT_NULL:    v.facts.nullness = pear_erm::Nullness.NULL_ALWAYS;
        default: break;
    }
}

/*
 A π: the value on the NON-FAULTING path of a diverging operation.

 `guard` is the operation that can fault (the load, the index, the
 division). Naming it as operand 1 makes the dependence explicit, so no
 pass can hoist the π above the check that justifies its fact.

 D1: like σ, a π is a RENAME, so it inherits the guarded value's origin.
 A π that started a fresh lineage would strand every range fact learned
 about the original the moment the first bounds check was crossed.
*/
fn uint AirModule.new_pi(AirModule* m, uint block, uint guarded, uint guard,
                         AirFact fact, int line, int col)
{
    uint[2] ops;
    ops[0] = guarded;
    ops[1] = guard;
    uint org = AIR_NO_ORIGIN;
    AirValue* g = m.val(guarded);
    if (g != null) { org = g.origin; }
    uint id = m.new_value(block, AirOp.AIR_PI, &ops[0], 2, org, line, col);
    if (id == AIR_NO_VALUE) { return id; }
    m.values[id].p.fact = fact;

    /*
     RE-FETCH. `g` was taken before new_value, which grows the value array
     and therefore may realloc it — so the earlier pointer now dangles.
     This is the exact hazard documented on AirModule.val ("the returned
     pointer is invalidated by the next add_* call"), and I violated it
     three lines after writing it down.

     It survived every hand-written fixture and crashed on stdlib/io.pie,
     which is large enough to force a reallocation mid-function. Holding
     an id across mutation is safe; holding a pointer is not.
    */
    g = m.val(guarded);

    /*
     Seed R from the fact the π establishes. This is where the `E` feeds
     the `R`: surviving a dereference PROVES nonnull, surviving a division
     proves the divisor nonzero, surviving a checked index proves inbounds.
     Recording it here rather than leaving it for a2 means the fact exists
     from the moment the π does.
    */
    AirValue* v = &m.values[id];
    if (g != null) { v.facts = g.facts; }
    switch (fact)
    {
        case FACT_NONNULL:
            v.facts.nullness = pear_erm::Nullness.NULL_NEVER;
        case FACT_NONZERO:
            v.facts.range = pear_erm::r_refine_ne(v.facts.range, 0);
        case FACT_INBOUNDS:
            // Lower bound only: the upper bound needs the length, which
            // a2 supplies once it knows the allocation. Claiming a bogus
            // upper bound here would be worse than claiming nothing.
            v.facts.range = pear_erm::r_refine_ge(v.facts.range, 0);
        default:
            break;
    }
    return id;
}

/*
 The memory-entry token: version 0, the state of memory on entry to a
 function. Every load that no store dominates reads this.
*/
fn uint AirModule.new_mem_entry(AirModule* m, uint block, int line, int col)
{
    uint[1] ops;
    uint id = m.new_value(block, AirOp.AIR_MEM_ENTRY, &ops[0], 0, AIR_NO_ORIGIN, line, col);
    if (id == AIR_NO_VALUE) { return id; }
    AirValue* v = &m.values[id];
    v.facts.mem.kind = pear_erm::MemKind.MEM_LIVE_ON_ENTRY;
    v.facts.mem.version = 0;
    return id;
}

/*
 A memory φ. Memory joins at a control-flow join exactly as a scalar does,
 and giving it a real node — rather than recomputing reaching definitions
 on demand — is what lets the answer survive serialisation.
*/
fn uint AirModule.new_mem_phi(AirModule* m, uint block, uint* ops, uint* incoming,
                              usz n, uint version, int line, int col)
{
    uint id = m.new_value(block, AirOp.AIR_MEM_PHI, ops, n, AIR_NO_ORIGIN, line, col);
    if (id == AIR_NO_VALUE) { return id; }
    usz off = m.push_phi_blocks(incoming, n);
    AirValue* v = &m.values[id];
    v.inc_off = off;
    v.inc_count = n;
    v.facts.mem.kind = pear_erm::MemKind.MEM_PHI;
    v.facts.mem.version = version;
    return id;
}

// Record that this value reads memory version `reaching`.
fn void AirModule.set_mem_use(AirModule* m, uint vid, uint reaching,
                              pear_erm::AliasScope scope)
{
    AirValue* v = m.val(vid);
    if (v == null) { return; }
    v.facts.mem.kind = pear_erm::MemKind.MEM_USE;
    v.facts.mem.reaching = reaching;
    v.facts.mem.scope = scope;
}

// Record that this value writes memory, producing `version` from `reaching`.
fn void AirModule.set_mem_def(AirModule* m, uint vid, uint version, uint reaching,
                              pear_erm::AliasScope scope)
{
    AirValue* v = m.val(vid);
    if (v == null) { return; }
    v.facts.mem.kind = pear_erm::MemKind.MEM_DEF;
    v.facts.mem.version = version;
    v.facts.mem.reaching = reaching;
    v.facts.mem.scope = scope;
}

// ── ERM queries, the reason the facts are carried at all ────────────────

/*
 Can this value be proven to fit in `bits`? A true answer is what lets a2
 narrow a 64-bit operation, delete an overflow check, or drop a bounds
 test. In LLVM the same question costs a fresh ValueTracking walk at every
 call site.
*/
fn bool AirModule.value_fits(AirModule* m, uint vid, int bits, bool is_signed)
{
    AirValue* v = m.val(vid);
    if (v == null) { return false; }
    return pear_erm::r_fits(&v.facts.range, bits, is_signed);
}

fn bool AirModule.value_nonnull(AirModule* m, uint vid)
{
    AirValue* v = m.val(vid);
    if (v == null) { return false; }
    return v.facts.nullness == pear_erm::Nullness.NULL_NEVER;
}

/*
 Alignment implied by the known trailing zeros. This is what becomes an
 `align` attribute at emission; LLVM would rediscover it from scratch.
*/
fn int AirModule.value_alignment(AirModule* m, uint vid)
{
    AirValue* v = m.val(vid);
    if (v == null) { return 1; }
    int tz = pear_erm::kb_trailing_zeros(&v.facts.bits);
    if (tz >= 31) { return 1 << 30; }
    return 1 << tz;
}

/*
 Do two memory accesses provably not alias? Distinct non-zero scopes, or
 either side flagged no_alias, is enough. Unknown scope answers false,
 which is the conservative direction.
*/
fn bool AirModule.no_alias(AirModule* m, uint a, uint b)
{
    AirValue* va = m.val(a);
    AirValue* vb = m.val(b);
    if (va == null || vb == null) { return false; }
    if (va.facts.mem.no_alias || vb.facts.mem.no_alias) { return true; }
    if (va.facts.mem.scope == pear_erm::ALIAS_UNKNOWN) { return false; }
    if (vb.facts.mem.scope == pear_erm::ALIAS_UNKNOWN) { return false; }
    return va.facts.mem.scope != vb.facts.mem.scope;
}

// ── edges ───────────────────────────────────────────────────────────────

/*
 Add a CFG edge. Duplicate edges are permitted here, unlike theory_live's
 Cfg.add_edge which deduplicates: a φ needs one operand per INCOMING EDGE,
 so `if c then x else x` genuinely has two edges to the join and the φ
 genuinely has two operands. Collapsing them would leave the φ's operand
 count disagreeing with the predecessor count, which verify.c3 checks.
*/
fn void AirModule.add_edge(AirModule* m, uint from, uint to)
{
    AirBlock* f = m.blk(from);
    AirBlock* t = m.blk(to);
    if (f == null || t == null) { return; }
    if (!grow_u32(&f.succ, &f.succ_cap, f.succ_count + 1)) { m.overflowed = true; return; }
    f.succ[f.succ_count] = to;
    f.succ_count = f.succ_count + 1;
    if (!grow_u32(&t.pred, &t.pred_cap, t.pred_count + 1)) { m.overflowed = true; return; }
    t.pred[t.pred_count] = from;
    t.pred_count = t.pred_count + 1;
}

fn void AirModule.set_term(AirModule* m, uint block, AirTerm term, uint value)
{
    AirBlock* b = m.blk(block);
    if (b == null) { return; }
    b.term = term;
    b.term_value = value;
}

fn void AirModule.add_case(AirModule* m, uint block, long v)
{
    AirBlock* b = m.blk(block);
    if (b == null) { return; }
    if (!grow_i64(&b.case_vals, &b.case_cap, b.case_count + 1)) { m.overflowed = true; return; }
    b.case_vals[b.case_count] = v;
    b.case_count = b.case_count + 1;
}

fn void AirModule.add_param(AirModule* m, uint func, uint value)
{
    AirFunc* f = m.fun(func);
    if (f == null) { return; }
    if (!grow_u32(&f.params, &f.param_cap, f.param_count + 1)) { m.overflowed = true; return; }
    f.params[f.param_count] = value;
    f.param_count = f.param_count + 1;
}

// ── classification, used by verify.c3 and by a2's DCE ───────────────────

/*
 "Definitely has a side effect." The polarity matters and is deliberately
 the same as pfront's `is_pure` interlock: this answers a question DCE is
 allowed to act on. An opcode not listed here is not thereby proven pure —
 AIR_UNKNOWN is treated as effectful precisely because it is unknown.
*/
fn bool op_has_effect(AirOp op)
{
    switch (op)
    {
        case AIR_STORE_PTR:
        case AIR_STORE_FIELD:
        case AIR_STORE_INDEX:
        case AIR_CALL:
        case AIR_CALL_DIRECT:
        case AIR_ALLOC:
        case AIR_FREE:
        case AIR_PERFORM:
        case AIR_HANDLE:
        case AIR_HANDLE_ARM:
        case AIR_RESUME:
        case AIR_UNKNOWN:
            return true;
        default:
            return false;
    }
}

// Does this opcode produce a value other code can name?
fn bool op_yields_value(AirOp op)
{
    switch (op)
    {
        case AIR_STORE_PTR:
        case AIR_STORE_FIELD:
        case AIR_STORE_INDEX:
        case AIR_FREE:
            return false;
        default:
            return true;
    }
}

// Does this terminator leave the block by a CFG edge?
fn bool term_has_successors(AirTerm t)
{
    switch (t)
    {
        case TERM_JUMP:
        case TERM_BRANCH:
        case TERM_SWITCH:
            return true;
        default:
            return false;
    }
}

// ⊥-typed: control never leaves the block at all.
fn bool term_is_divergent(AirTerm t)
{
    switch (t)
    {
        case TERM_UNREACHABLE:
        case TERM_TRAP:
        case TERM_UB:
            return true;
        default:
            return false;
    }
}

/*
 How many successors this terminator REQUIRES. -1 means variable (switch).
 verify.c3 uses this rather than hardcoding the arities at the check site,
 so adding a terminator cannot leave a stale check behind.
*/
fn int term_arity(AirTerm t)
{
    switch (t)
    {
        case TERM_JUMP:   return 1;
        case TERM_BRANCH: return 2;
        case TERM_SWITCH: return -1;
        default:          return 0;
    }
}

// ── mnemonics, shared by the printer and the parser ─────────────────────

fn String op_name(AirOp o)      { return o.mnemonic; }
fn String term_name(AirTerm t)  { return t.mnemonic; }
fn String binop_name(AirBinOp b){ return b.mnemonic; }
fn String unop_name(AirUnOp u)  { return u.mnemonic; }
fn String fact_name(AirFact f)  { return f.mnemonic; }

/*
 Reverse lookups. The printer and the parser MUST agree, so both go through
 the same mnemonic table on the enum rather than keeping two hand-written
 switch statements that can drift. Round-trip tests would catch a drift,
 but not having two tables is better than catching it.
*/
fn bool str_eq_n(char* a, usz alen, String b)
{
    if (alen != b.len) { return false; }
    for (usz i = 0; i < alen; i++) { if (a[i] != b[i]) { return false; } }
    return true;
}

fn AirOp op_from_name(char* s, usz len, bool* ok)
{
    *ok = true;
    foreach (o : AirOp::values) { if (str_eq_n(s, len, o.mnemonic)) { return o; } }
    *ok = false;
    return AirOp.AIR_UNKNOWN;
}

fn AirTerm term_from_name(char* s, usz len, bool* ok)
{
    *ok = true;
    foreach (t : AirTerm::values) { if (str_eq_n(s, len, t.mnemonic)) { return t; } }
    *ok = false;
    return AirTerm.TERM_OPEN;
}

fn AirBinOp binop_from_name(char* s, usz len, bool* ok)
{
    *ok = true;
    foreach (b : AirBinOp::values) { if (str_eq_n(s, len, b.mnemonic)) { return b; } }
    *ok = false;
    return AirBinOp.ABO_NONE;
}

fn AirUnOp unop_from_name(char* s, usz len, bool* ok)
{
    *ok = true;
    foreach (u : AirUnOp::values) { if (str_eq_n(s, len, u.mnemonic)) { return u; } }
    *ok = false;
    return AirUnOp.AUO_NONE;
}

fn AirFact fact_from_name(char* s, usz len, bool* ok)
{
    *ok = true;
    foreach (f : AirFact::values) { if (str_eq_n(s, len, f.mnemonic)) { return f; } }
    *ok = false;
    return AirFact.FACT_NONE;
}
