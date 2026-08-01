/*
 build.c3 — PNode → AIR. Build order step 3.

 This is the only module in PEAR that reads an AST (PEAR.md D5). It reads
 the AST and never Pride source: pfront owns the grammar, and there is no
 second lexer or parser anywhere in PEAR.

 ── SSA construction: Braun et al., not dominance frontiers ─────────────

 "Simple and Efficient Construction of Static Single Assignment Form"
 (CC 2013). Variables are renamed on the fly during a single structured
 walk; φ are created lazily when a read cannot be satisfied locally, and
 trivial φ are removed as soon as they are seen to be trivial.

 This is the right fit for Pride and it is what PEAR.md section 8 means by
 keeping ssi_ir.c3's "structured single-pass CFG walk (Brandis-Mössenböck,
 no dominance-frontier iteration needed since Pride has no goto)". Pride
 has `if`/`while`/`match` and no arbitrary jumps, so every block's
 predecessor set is known by the time the construct that owns it closes.
 Computing dominance frontiers to place φ we can place directly would be
 work done twice.

   write_var(binder, block, value)   record the current definition
   read_var(binder, block)           find it, inserting φ if needed
   seal_block(block)                 all predecessors are now known

 A block is SEALED once no further predecessor can appear. A loop header
 is created unsealed — its back edge does not exist yet — and sealed after
 the body is built. Reading a variable in an unsealed block parks an
 incomplete φ that is filled in at seal time. That single mechanism is what
 makes loop-carried variables work without a second pass.

 ── SP: the semi-pruned filter ──────────────────────────────────────────
 Braun's algorithm is already close to pruned form: a φ is only created
 when a read actually needs one, so a variable never read across an edge
 never gets one. `remove_trivial_phi` then deletes φ whose operands all
 agree. air_infer.c3's classify_sp records the result per value so the
 outcome is auditable in the text.

 ── e and E: where σ and π are placed ───────────────────────────────────
 σ on the operands of a branch condition, one per outgoing edge, carrying
 that edge's fact (PEAR.md section 3, the e-SSA table). π across an
 operation that can diverge. Both are RENAMES, so both inherit origin (D1)
 and both make a fact a property of a NAME rather than of a program point.

 ── Totality ────────────────────────────────────────────────────────────
 Lowering must never fail. A construct with no rule yet becomes AIR_UNKNOWN
 with its operands preserved, counted in `unsupported`, and reported. A
 lowering pass that aborts on the first unhandled node cannot be run
 against a real 258-module standard library to find out what is missing.
*/

module pear_build;

import pear_air;
import pear_erm;
import pear_infer;
import pfront_core;
import pfront_lex;

alias Air   = pear_air::AirModule;
alias Op    = pear_air::AirOp;
alias Term  = pear_air::AirTerm;
alias Fact  = pear_air::AirFact;
alias BOp   = pear_air::AirBinOp;
alias AirBinOpAlias = pear_air::AirBinOp;
alias UOp   = pear_air::AirUnOp;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;

extern fn int   printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn void* realloc(void* p, usz size);
extern fn void  free(void* p);

/*
 Operator token ids.

 pfront stores the operator as `p.op`, a plain int, precisely so PEAR does
 not have to depend on the lexer (D5). But the VALUES have to agree, and
 hardcoding them by eye does not work: my first attempt guessed
 TOKEN_PLUS = 233 from its source line number when the enum ordinal is
 actually 155, so every binary operator lowered to AIR_UNKNOWN.

 So they are derived from the enum itself. This still imports pfront_lex,
 which looks like a D5 violation, but is not: D5 forbids a stage READING A
 PNode or Pride source. a1 is explicitly allowed to read the AST, and
 reading a compile-time constant from the same front end it already parses
 with is strictly safer than duplicating the numbers. Stages a2-a5 import
 neither, and pear_tests/run.sh greps to prove it.
*/
const int TK_PIPE      = (int)pfront_lex::TokenType.TOKEN_PIPE.ordinal;
const int TK_PLUS      = (int)pfront_lex::TokenType.TOKEN_PLUS.ordinal;
const int TK_MINUS     = (int)pfront_lex::TokenType.TOKEN_MINUS.ordinal;
const int TK_STAR      = (int)pfront_lex::TokenType.TOKEN_STAR.ordinal;
const int TK_SLASH     = (int)pfront_lex::TokenType.TOKEN_SLASH.ordinal;
const int TK_PERCENT   = (int)pfront_lex::TokenType.TOKEN_PERCENT.ordinal;
const int TK_AMP       = (int)pfront_lex::TokenType.TOKEN_AMP.ordinal;
const int TK_AMPAMP    = (int)pfront_lex::TokenType.TOKEN_AMPAMP.ordinal;
const int TK_PIPEPIPE  = (int)pfront_lex::TokenType.TOKEN_PIPEPIPE.ordinal;
const int TK_XOR       = (int)pfront_lex::TokenType.TOKEN_XOR.ordinal;
const int TK_BANG      = (int)pfront_lex::TokenType.TOKEN_BANG.ordinal;
const int TK_EQEQ      = (int)pfront_lex::TokenType.TOKEN_EQEQ.ordinal;
const int TK_NEQ       = (int)pfront_lex::TokenType.TOKEN_NEQ.ordinal;
const int TK_LT        = (int)pfront_lex::TokenType.TOKEN_LT.ordinal;
const int TK_LTEQ      = (int)pfront_lex::TokenType.TOKEN_LTEQ.ordinal;
const int TK_GT        = (int)pfront_lex::TokenType.TOKEN_GT.ordinal;
const int TK_GTEQ      = (int)pfront_lex::TokenType.TOKEN_GTEQ.ordinal;
const int TK_LSHIFT    = (int)pfront_lex::TokenType.TOKEN_LSHIFT.ordinal;
const int TK_RSHIFT    = (int)pfront_lex::TokenType.TOKEN_RSHIFT.ordinal;
// Unicode spellings are distinct tokens; the spec lists them as equal.
const int TK_GEQ_UNI   = (int)pfront_lex::TokenType.TOKEN_GEQ_UNI.ordinal;
const int TK_LEQ_UNI   = (int)pfront_lex::TokenType.TOKEN_LEQ_UNI.ordinal;
const int TK_NEQ_UNI   = (int)pfront_lex::TokenType.TOKEN_NEQ_UNI.ordinal;
// Overflow-qualified arithmetic: distinct semantics, distinct opcodes.
const int TK_PLUS_Q    = (int)pfront_lex::TokenType.TOKEN_PLUS_QUESTION.ordinal;
const int TK_MINUS_Q   = (int)pfront_lex::TokenType.TOKEN_MINUS_QUESTION.ordinal;
const int TK_STAR_Q    = (int)pfront_lex::TokenType.TOKEN_STAR_QUESTION.ordinal;
const int TK_PLUS_PCT  = (int)pfront_lex::TokenType.TOKEN_PLUS_PERCENT.ordinal;
const int TK_MINUS_PCT = (int)pfront_lex::TokenType.TOKEN_MINUS_PERCENT.ordinal;
const int TK_STAR_PCT  = (int)pfront_lex::TokenType.TOKEN_STAR_PERCENT.ordinal;
const int TK_PLUS_PIPE = (int)pfront_lex::TokenType.TOKEN_PLUS_PIPE.ordinal;
const int TK_MINUS_PIP = (int)pfront_lex::TokenType.TOKEN_MINUS_PIPE.ordinal;
const int TK_STAR_PIPE = (int)pfront_lex::TokenType.TOKEN_STAR_PIPE.ordinal;
/*
 Compound-assignment tokens. `x += e` keeps the `+=` token, not `+`, so
 binop_of would return NONE and the whole statement fell through to
 AIR_UNKNOWN. Mapped separately rather than by munging the token, because
 the two are genuinely different tokens and pretending otherwise is how
 an off-by-one in an enum turns into silently wrong code.
*/
const int TK_PLUSEQ    = (int)pfront_lex::TokenType.TOKEN_PLUSEQ.ordinal;
const int TK_MINUSEQ   = (int)pfront_lex::TokenType.TOKEN_MINUSEQ.ordinal;
const int TK_STAREQ    = (int)pfront_lex::TokenType.TOKEN_STAREQ.ordinal;
const int TK_SLASHEQ   = (int)pfront_lex::TokenType.TOKEN_SLASHEQ.ordinal;
const int TK_PERCENTEQ = (int)pfront_lex::TokenType.TOKEN_PERCENTEQ.ordinal;
const int TK_AMPEQ     = (int)pfront_lex::TokenType.TOKEN_AMPEQ.ordinal;
const int TK_PIPEEQ    = (int)pfront_lex::TokenType.TOKEN_PIPEEQ.ordinal;
const int TK_XOREQ     = (int)pfront_lex::TokenType.TOKEN_XOREQ.ordinal;
const int TK_LSHIFTEQ  = (int)pfront_lex::TokenType.TOKEN_LSHIFTEQ.ordinal;
const int TK_RSHIFTEQ  = (int)pfront_lex::TokenType.TOKEN_RSHIFTEQ.ordinal;

// The binary operator a compound assignment applies. Separate from
// binop_of so neither table has to know about the other's tokens.
fn AirBinOpAlias compound_binop_of(int tok)
{
    switch (tok)
    {
        case TK_PLUSEQ:    return AirBinOpAlias.ABO_ADD;
        case TK_MINUSEQ:   return AirBinOpAlias.ABO_SUB;
        case TK_STAREQ:    return AirBinOpAlias.ABO_MUL;
        case TK_SLASHEQ:   return AirBinOpAlias.ABO_DIV;
        case TK_PERCENTEQ: return AirBinOpAlias.ABO_MOD;
        case TK_AMPEQ:     return AirBinOpAlias.ABO_AND;
        case TK_PIPEEQ:    return AirBinOpAlias.ABO_OR;
        case TK_XOREQ:     return AirBinOpAlias.ABO_XOR;
        case TK_LSHIFTEQ:  return AirBinOpAlias.ABO_SHL;
        case TK_RSHIFTEQ:  return AirBinOpAlias.ABO_SHR;
        default:           return AirBinOpAlias.ABO_NONE;
    }
}

// ════════════════════════════════════════════════════════════════════════
// VARIABLE MAP
// ════════════════════════════════════════════════════════════════════════

/*
 Current definition of a variable in a block.

 A variable is identified by its BINDER POINTER, not by its name. Two
 distinct `let x` in sibling scopes are different variables that happen to
 share a spelling, and keying on the name would merge them — the same
 mistake theory_poly.c3 had to fix by keying substitution on binder
 pointer rather than name.
*/
struct VarDef
{
    Node* binder;
    uint  block;
    uint  value;
}

struct IncompletePhi
{
    Node* binder;
    uint  block;
    uint  phi;
}

struct Builder
{
    Air*   m;
    pfront_core::Interner* interner;

    VarDef* defs;
    usz     def_count;
    usz     def_cap;

    IncompletePhi* incomplete;
    usz            inc_count;
    usz            inc_cap;

    bool*  sealed;          // indexed by block id
    usz    sealed_cap;

    uint   cur_func;
    uint   cur_block;

    // Innermost loop, for `break` / `continue`. -1 when not in a loop.
    uint   loop_header;
    uint   loop_exit;
    bool   in_loop;

    // Honest counters, reported whether flattering or not.
    usz    unsupported;     // constructs with no lowering rule yet
    usz    phis_created;
    usz    phis_removed;    // trivial φ eliminated
    usz    sigmas;
    usz    pis;

    // Which AST node kinds hit the fallback, so the gap can be reported
    // by construct instead of as one opaque number.
    usz[256] miss_kind;
    usz      miss_undef_read;
}

fn void Builder.init(Builder* b, Air* m, pfront_core::Interner* it)
{
    b.m = m;
    b.interner = it;
    b.defs = null; b.def_count = 0; b.def_cap = 0;
    b.incomplete = null; b.inc_count = 0; b.inc_cap = 0;
    b.sealed = null; b.sealed_cap = 0;
    b.cur_func = pear_air::AIR_NO_FUNC;
    b.cur_block = pear_air::AIR_NO_BLOCK;
    b.loop_header = 0; b.loop_exit = 0; b.in_loop = false;
    b.unsupported = 0; b.phis_created = 0; b.phis_removed = 0;
    b.sigmas = 0; b.pis = 0;
    for (usz i = 0; i < 256; i++) { b.miss_kind[i] = 0; }
    b.miss_undef_read = 0;
}

fn void Builder.note_unsupported(Builder* b, Nk k)
{
    usz i = (usz)k;
    if (i < 256) { b.miss_kind[i] = b.miss_kind[i] + 1; }
}

fn void Builder.destroy(Builder* b)
{
    if (b.defs != null) { free((void*)b.defs); b.defs = null; }
    if (b.incomplete != null) { free((void*)b.incomplete); b.incomplete = null; }
    if (b.sealed != null) { free((void*)b.sealed); b.sealed = null; }
}

fn void Builder.write_var(Builder* b, Node* binder, uint block, uint value)
{
    if (binder == null) { return; }
    for (usz i = 0; i < b.def_count; i++)
    {
        if (b.defs[i].binder == binder && b.defs[i].block == block)
        {
            b.defs[i].value = value;
            return;
        }
    }
    if (b.def_count + 1 > b.def_cap)
    {
        usz nc = b.def_cap == 0 ? 64 : b.def_cap * 2;
        VarDef* p = (VarDef*)realloc((void*)b.defs, nc * VarDef::size);
        if (p == null) { return; }
        b.defs = p; b.def_cap = nc;
    }
    b.defs[b.def_count].binder = binder;
    b.defs[b.def_count].block = block;
    b.defs[b.def_count].value = value;
    b.def_count = b.def_count + 1;
}

fn uint Builder.local_var(Builder* b, Node* binder, uint block)
{
    for (usz i = 0; i < b.def_count; i++)
    {
        if (b.defs[i].binder == binder && b.defs[i].block == block)
        {
            return b.defs[i].value;
        }
    }
    return pear_air::AIR_NO_VALUE;
}

fn bool Builder.is_sealed(Builder* b, uint block)
{
    if ((usz)block >= b.sealed_cap) { return false; }
    return b.sealed[block];
}

fn void Builder.mark_sealed(Builder* b, uint block, bool v)
{
    if ((usz)block >= b.sealed_cap)
    {
        usz nc = b.sealed_cap == 0 ? 64 : b.sealed_cap;
        while (nc <= (usz)block) { nc = nc * 2; }
        bool* p = (bool*)realloc((void*)b.sealed, nc);
        if (p == null) { return; }
        for (usz i = b.sealed_cap; i < nc; i++) { p[i] = false; }
        b.sealed = p; b.sealed_cap = nc;
    }
    b.sealed[block] = v;
}

fn void Builder.add_incomplete(Builder* b, Node* binder, uint block, uint phi)
{
    if (b.inc_count + 1 > b.inc_cap)
    {
        usz nc = b.inc_cap == 0 ? 32 : b.inc_cap * 2;
        IncompletePhi* p = (IncompletePhi*)realloc((void*)b.incomplete,
                                                   nc * IncompletePhi::size);
        if (p == null) { return; }
        b.incomplete = p; b.inc_cap = nc;
    }
    b.incomplete[b.inc_count].binder = binder;
    b.incomplete[b.inc_count].block = block;
    b.incomplete[b.inc_count].phi = phi;
    b.inc_count = b.inc_count + 1;
}

/*
 Read a variable, inserting φ as needed. The heart of Braun et al.

 Three cases:
   unsealed block   park an incomplete φ; its operands are filled at seal
                    time, once every predecessor exists. This is what makes
                    a loop-carried variable work in one pass.
   one predecessor  no φ can be needed; recurse into it. This is the case
                    that keeps straight-line code φ-free, and it is most of
                    real code — theory_live measured 53% of stdlib
                    variables never crossing a block boundary.
   many predecessors  create the φ, RECORD IT FIRST, then fill operands.
                    Recording before filling is what terminates the
                    recursion on a cycle.
*/
fn uint Builder.read_var(Builder* b, Node* binder, uint block)
{
    if (binder == null) { return pear_air::AIR_NO_VALUE; }

    uint local = b.local_var(binder, block);
    if (local != pear_air::AIR_NO_VALUE) { return local; }

    pear_air::AirBlock* blk = b.m.blk(block);
    if (blk == null) { return pear_air::AIR_NO_VALUE; }

    uint val;
    if (!b.is_sealed(block))
    {
        val = b.new_empty_phi(block, binder);
        b.add_incomplete(binder, block, val);
    }
    else if (blk.pred_count == 1)
    {
        return b.read_var(binder, blk.pred[0]);
    }
    else if (blk.pred_count == 0)
    {
        /*
         No predecessors, and not the entry block: this block is
         UNREACHABLE. A `while` whose body always breaks, or an arm after
         an irrefutable pattern, leaves one behind; a2's DCE removes them.

         A variable read here has no reaching definition and never can,
         because no path arrives. That is not a lowering gap — there is
         nothing to lower — so it must not be counted as one. Emitting
         AIR_UNKNOWN and calling it "unsupported" inflated the gap with
         code that will be deleted before it is ever examined.

         `poison` says exactly the right thing: any value is acceptable
         because control cannot get here. It is distinct from AIR_UNKNOWN,
         which means "a1 could not translate this" — conflating the two is
         how a coverage number stops meaning anything.
        */
        uint[1] none;
        val = b.m.new_value(block, Op.AIR_POISON, &none[0], 0,
                            pear_air::AIR_NO_ORIGIN, 0, 0);
        b.write_var(binder, block, val);
        return val;
    }
    else
    {
        val = b.new_empty_phi(block, binder);
        // Record BEFORE filling operands: a cyclic read must find this φ
        // rather than recursing forever.
        b.write_var(binder, block, val);
        val = b.fill_phi(val, binder, block);
    }
    b.write_var(binder, block, val);
    return val;
}

fn uint Builder.new_empty_phi(Builder* b, uint block, Node* binder)
{
    uint[1] none;
    uint phi = b.m.new_value(block, Op.AIR_PHI, &none[0], 0,
                             pear_air::AIR_NO_ORIGIN, 0, 0);
    if (phi == pear_air::AIR_NO_VALUE) { return phi; }
    if (binder != null) { b.m.values[phi].p.name = binder.name_id; }
    b.phis_created = b.phis_created + 1;

    /*
     A φ must precede every non-φ in its block. Braun's algorithm creates
     φ lazily, i.e. potentially after ordinary values already exist, so the
     new φ has to be moved to the front. Appending and leaving it would
     violate the invariant verify.c3 checks.
    */
    pear_air::AirBlock* blk = b.m.blk(block);
    if (blk != null && blk.value_count > 1)
    {
        usz last = blk.value_count - 1;
        usz insert = 0;
        while (insert < last)
        {
            pear_air::AirValue* v = b.m.val(blk.values[insert]);
            if (v == null) { break; }
            // Skip live φ AND the holes left by removed ones: a hole is
            // not an instruction, and treating it as one pushes this φ
            // past it and breaks the all-φ-first invariant.
            if (v.op != Op.AIR_PHI && !v.is_phi_hole) { break; }
            insert = insert + 1;
        }
        for (usz i = last; i > insert; i--) { blk.values[i] = blk.values[i - 1]; }
        blk.values[insert] = phi;
    }
    return phi;
}

/*
 Fill a φ's operands, one per predecessor, then try to remove it.
*/
fn uint Builder.fill_phi(Builder* b, uint phi, Node* binder, uint block)
{
    pear_air::AirBlock* blk = b.m.blk(block);
    if (blk == null) { return phi; }

    uint[64] ops;
    uint[64] incs;
    usz n = 0;
    for (usz i = 0; i < blk.pred_count && n < 64; i++)
    {
        uint pv = b.read_var(binder, blk.pred[i]);
        if (pv == pear_air::AIR_NO_VALUE) { continue; }
        ops[n] = pv;
        incs[n] = blk.pred[i];
        n = n + 1;
    }

    usz ooff = b.m.push_operands(&ops[0], n);
    usz ioff = b.m.push_phi_blocks(&incs[0], n);
    pear_air::AirValue* pv2 = b.m.val(phi);
    if (pv2 == null) { return phi; }
    pv2.op_off = ooff;
    pv2.op_count = n;
    pv2.inc_off = ioff;
    pv2.inc_count = n;

    return b.remove_trivial_phi(phi);
}

/*
 A φ is TRIVIAL when every operand is either the φ itself or one single
 other value: it merges nothing. Replace it with that value.

 This is what keeps Braun's output close to pruned form without a separate
 pruning pass, and it is why the SP in SP-ERM-e-SSI does not need a
 liveness pre-pass here.

 The φ is not deleted from the block — removing an element from the middle
 of a block invalidates positions other code may hold. It is turned into a
 copy of the surviving value by rewriting every USE, and the now-dead φ is
 left for a2's DCE, which is the pass that owns deletion.
*/
fn uint Builder.remove_trivial_phi(Builder* b, uint phi)
{
    pear_air::AirValue* p = b.m.val(phi);
    if (p == null || p.op != Op.AIR_PHI) { return phi; }

    uint same = pear_air::AIR_NO_VALUE;
    for (usz i = 0; i < p.op_count; i++)
    {
        uint o = b.m.operands[p.op_off + i];
        if (o == phi || o == same) { continue; }
        if (same != pear_air::AIR_NO_VALUE) { return phi; }   // merges >1 value
        same = o;
    }
    if (same == pear_air::AIR_NO_VALUE) { return phi; }        // no operands

    /*
     Rewrite every use of the φ to the surviving value — AND every
     `origin` that named it.

     Missing the origin rewrite left a σ built over this φ pointing at a
     slot that is about to become a hole, so its origin no longer matched
     its source's. verify.c3 caught it as a D1 violation on
     stdlib/pride/msp.pie, and the check was right: D1 keys every fact by
     origin, so an origin pointing at a dead slot makes every fact about
     that lineage unreachable — the precise "ERM ends up decorative"
     failure D1 exists to prevent.
    */
    uint same_origin = same;
    pear_air::AirValue* sv = b.m.val(same);
    if (sv != null) { same_origin = sv.origin; }

    for (usz i = 1; i < b.m.value_count; i++)
    {
        pear_air::AirValue* v = &b.m.values[i];
        for (usz oi = 0; oi < v.op_count; oi++)
        {
            if (b.m.operands[v.op_off + oi] == phi)
            {
                b.m.operands[v.op_off + oi] = same;
            }
        }
        if (v.origin == phi && v.id != phi) { v.origin = same_origin; }
    }
    for (usz i = 1; i < b.m.block_count; i++)
    {
        if (b.m.blocks[i].term_value == phi) { b.m.blocks[i].term_value = same; }
    }
    for (usz i = 0; i < b.def_count; i++)
    {
        if (b.defs[i].value == phi) { b.defs[i].value = same; }
    }

    /*
     Neutralise the φ in place. It keeps its slot (positions stay valid)
     but becomes a no-operand const.unit that nothing references, which
     a2's DCE removes. Leaving it as a zero-operand PHI would fail
     verify.c3's "one operand per predecessor" check.
    */
    p = b.m.val(phi);
    p.op = Op.AIR_CONST_UNIT;
    p.op_count = 0;
    p.inc_count = 0;
    p.is_phi_hole = true;
    b.phis_removed = b.phis_removed + 1;
    return same;
}

/*
 Seal a block: no further predecessor can appear, so every parked φ can be
 completed.
*/
fn void Builder.seal_block(Builder* b, uint block)
{
    if (b.is_sealed(block)) { return; }
    b.mark_sealed(block, true);

    usz i = 0;
    while (i < b.inc_count)
    {
        if (b.incomplete[i].block != block) { i = i + 1; continue; }
        Node* binder = b.incomplete[i].binder;
        uint phi = b.incomplete[i].phi;
        // Remove before filling: fill_phi recurses and could otherwise see
        // this entry again.
        b.incomplete[i] = b.incomplete[b.inc_count - 1];
        b.inc_count = b.inc_count - 1;
        b.fill_phi(phi, binder, block);
    }
}

// ════════════════════════════════════════════════════════════════════════
// HELPERS
// ════════════════════════════════════════════════════════════════════════

/*
 Is this binder declared at MODULE scope rather than inside a function?

 Walks the parent chain: reaching a function or a clause means local,
 reaching the program or module node means global. Checking the node kind
 alone cannot tell them apart — a module-level `let` and a function-body
 `let` are both N_DECL_LET with an N_PAT_IDENT child.
*/
fn bool is_module_level(Node* binder)
{
    Node* cur = binder;
    usz guard = 0;
    while (cur != null && guard < 64)
    {
        guard = guard + 1;
        if (cur.kind == Nk.N_DECL_FN || cur.kind == Nk.N_CLAUSE
            || cur.kind == Nk.N_EXPR_LAMBDA || cur.kind == Nk.N_MATCH_ARM
            || cur.kind == Nk.N_HANDLER_ARM)
        {
            return false;
        }
        if (cur.kind == Nk.N_PROGRAM || cur.kind == Nk.N_MODULE) { return true; }
        cur = cur.parent;
    }
    // No parent chain at all: treat as local, which keeps the old
    // behaviour for a synthesised binder rather than inventing a global.
    return false;
}

fn uint Builder.emit(Builder* b, Op op, uint* ops, usz n, Node* src)
{
    int line = src == null ? 0 : src.line;
    int col  = src == null ? 0 : src.col;
    return b.m.new_value(b.cur_block, op, ops, n, pear_air::AIR_NO_ORIGIN, line, col);
}

/*
 Lower a sub-expression that MUST yield an operand.

 lower_expr can legitimately return AIR_NO_VALUE: `unreachable`, `trap`
 and `ub!` set a terminator and produce nothing, and an `if` whose arms
 both diverge has no join value. Storing that into an operand list writes
 the reserved "none" id 0 into a position that must name a real value,
 which verify.c3 rightly rejects as "operand is the null value id".

 There are ~20 operand positions, so guarding each one would be twenty
 chances to forget. This is the chokepoint: a missing operand becomes an
 explicit AIR_UNKNOWN, which keeps lowering TOTAL, keeps the module
 well-formed, and makes the gap countable instead of malformed.

 Found by the stdlib sweep on os/linux/tls.pie, which produced
 `%233 = bin %0 %232 op=sub`.
*/
fn uint Builder.lower_operand(Builder* b, Node* n)
{
    uint v = b.lower_expr(n);
    if (v != pear_air::AIR_NO_VALUE) { return v; }
    uint[1] none;
    b.unsupported = b.unsupported + 1;
    if (n != null) { b.note_unsupported(n.kind); }
    return b.emit(Op.AIR_UNKNOWN, &none[0], 0, n);
}

fn uint Builder.const_int(Builder* b, long v, Node* src)
{
    uint[1] none;
    uint id = b.emit(Op.AIR_CONST_INT, &none[0], 0, src);
    if (id == pear_air::AIR_NO_VALUE) { return id; }
    int w = src != null && src.p.width != 0 ? (int)src.p.width : 64;
    bool sg = src == null ? true : src.p.is_signed;
    b.m.set_const_int(id, v, w, sg);
    return id;
}

fn bool Builder.block_open(Builder* b)
{
    pear_air::AirBlock* blk = b.m.blk(b.cur_block);
    return blk != null && blk.term == Term.TERM_OPEN;
}

/*
 Map a pfront operator token to an AIR operator.

 Checked arithmetic (`+?`), wrapping (`+%`) and saturating (`+|`) all
 collapse to the base operation here and are NOT distinguished yet. That is
 a real gap: they have different overflow semantics and a2 must not assume
 they wrap. Counted as unsupported so the number is visible rather than
 silently wrong.
*/
fn BOp binop_of(int tok)
{
    switch (tok)
    {
        case TK_PLUS:     return BOp.ABO_ADD;
        case TK_MINUS:    return BOp.ABO_SUB;
        case TK_STAR:     return BOp.ABO_MUL;
        case TK_SLASH:    return BOp.ABO_DIV;
        case TK_PERCENT:  return BOp.ABO_MOD;
        case TK_AMP:      return BOp.ABO_AND;
        case TK_PIPE:     return BOp.ABO_OR;
        case TK_XOR:      return BOp.ABO_XOR;
        case TK_LSHIFT:   return BOp.ABO_SHL;
        case TK_RSHIFT:   return BOp.ABO_SHR;
        case TK_EQEQ:     return BOp.ABO_EQ;
        case TK_NEQ:      return BOp.ABO_NE;
        case TK_LT:       return BOp.ABO_LT;
        case TK_LTEQ:     return BOp.ABO_LE;
        case TK_GT:       return BOp.ABO_GT;
        case TK_GTEQ:     return BOp.ABO_GE;
        case TK_AMPAMP:   return BOp.ABO_LAND;
        case TK_PIPEPIPE: return BOp.ABO_LOR;
        case TK_GEQ_UNI:  return BOp.ABO_GE;
        case TK_LEQ_UNI:  return BOp.ABO_LE;
        case TK_NEQ_UNI:  return BOp.ABO_NE;
        case TK_PLUS_Q:   return BOp.ABO_ADDC;
        case TK_MINUS_Q:  return BOp.ABO_SUBC;
        case TK_STAR_Q:   return BOp.ABO_MULC;
        case TK_PLUS_PCT: return BOp.ABO_ADDW;
        case TK_MINUS_PCT:return BOp.ABO_SUBW;
        case TK_STAR_PCT: return BOp.ABO_MULW;
        case TK_PLUS_PIPE:return BOp.ABO_ADDS;
        case TK_MINUS_PIP:return BOp.ABO_SUBS;
        case TK_STAR_PIPE:return BOp.ABO_MULS;
        default:          return BOp.ABO_NONE;
    }
}

// The fact a comparison establishes on its TRUE edge, and its negation.
fn Fact fact_true_of(BOp op)
{
    switch (op)
    {
        case ABO_LT: return Fact.FACT_LT;
        case ABO_LE: return Fact.FACT_LE;
        case ABO_GT: return Fact.FACT_GT;
        case ABO_GE: return Fact.FACT_GE;
        case ABO_EQ: return Fact.FACT_EQ;
        case ABO_NE: return Fact.FACT_NE;
        default:     return Fact.FACT_NONE;
    }
}

fn Fact fact_false_of(BOp op)
{
    switch (op)
    {
        case ABO_LT: return Fact.FACT_GE;
        case ABO_LE: return Fact.FACT_GT;
        case ABO_GT: return Fact.FACT_LE;
        case ABO_GE: return Fact.FACT_LT;
        case ABO_EQ: return Fact.FACT_NE;
        case ABO_NE: return Fact.FACT_EQ;
        default:     return Fact.FACT_NONE;
    }
}

// ════════════════════════════════════════════════════════════════════════
// σ PLACEMENT — the `e` of e-SSI
// ════════════════════════════════════════════════════════════════════════

/*
 Place σ for a branch, in the SUCCESSOR block.

 The σ belongs at the top of the target block rather than in the branching
 block: it names the value as it is on THAT edge, and putting both edges'
 σ in the predecessor would leave two names for the same variable live at
 the same point — which is precisely what verify.c3's SSI property 4 check
 rejects.

 Only a comparison against something produces a useful fact, and only a
 variable operand is worth splitting: splitting a constant renames a value
 whose range is already exact.
*/
fn void Builder.place_sigma(Builder* b, Node* cond, uint cond_val,
                            uint target, bool on_true)
{
    if (cond == null || cond.kind != Nk.N_EXPR_BINARY) { return; }
    pear_air::AirValue* cv = b.m.val(cond_val);
    if (cv == null || cv.op != Op.AIR_BIN || cv.op_count < 2) { return; }

    BOp op = cv.p.op;
    Fact f = on_true ? fact_true_of(op) : fact_false_of(op);
    if (f == Fact.FACT_NONE) { return; }

    uint lhs = b.m.operands[cv.op_off];
    uint rhs = b.m.operands[cv.op_off + 1];

    // The binder behind the left operand, if it is a plain variable read.
    Node* lb = cond.child_count > 0 ? cond.children[0] : null;
    if (lb != null && lb.kind == Nk.N_EXPR_IDENT && lb.resolved != null)
    {
        uint saved = b.cur_block;
        b.cur_block = target;
        uint s = b.m.new_sigma(target, lhs, f, cond.line, cond.col);
        if (s != pear_air::AIR_NO_VALUE)
        {
            b.sigmas = b.sigmas + 1;
            // Narrow immediately when the bound is a known constant; a
            // symbolic bound is left for a2.
            pear_air::AirValue* rv = b.m.val(rhs);
            if (rv != null && pear_erm::r_is_const(&rv.facts.range))
            {
                b.m.refine_sigma(s, rv.facts.range.lo);
            }
            // Rebind the variable in the target block so every use there
            // sees the REFINED name. Without this the σ is dead and the
            // whole e-SSI apparatus is decorative.
            b.write_var(lb.resolved, target, s);
        }
        b.cur_block = saved;
    }
}

// ════════════════════════════════════════════════════════════════════════
// EXPRESSIONS
// ════════════════════════════════════════════════════════════════════════

fn uint Builder.lower_expr(Builder* b, Node* n)
{
    if (n == null) { return pear_air::AIR_NO_VALUE; }
    uint[16] ops;

    switch (n.kind)
    {
        case N_EXPR_INT:
            return b.const_int((long)n.p.ival, n);

        case N_EXPR_BOOL:
        {
            uint id = b.emit(Op.AIR_CONST_BOOL, &ops[0], 0, n);
            if (id != pear_air::AIR_NO_VALUE)
            {
                b.m.values[id].p.ival = (long)n.p.ival;
                b.m.values[id].facts.range = pear_erm::r_range(0, 1);
                b.m.values[id].facts.width = 1;
            }
            return id;
        }

        case N_EXPR_FLOAT:
        {
            uint id = b.emit(Op.AIR_CONST_FLOAT, &ops[0], 0, n);
            if (id != pear_air::AIR_NO_VALUE) { b.m.values[id].p.fval = n.p.fval; }
            return id;
        }

        case N_EXPR_CHAR:
            return b.const_int((long)n.p.ival, n);

        case N_EXPR_STRING:
        case N_EXPR_BYTES:
        {
            uint id = b.emit(Op.AIR_CONST_STR, &ops[0], 0, n);
            if (id != pear_air::AIR_NO_VALUE && n.p.sptr != null)
            {
                b.m.values[id].p.name = b.interner.intern(n.p.sptr, n.p.slen);
            }
            return id;
        }

        case N_EXPR_NULL:
        {
            uint id = b.emit(Op.AIR_CONST_NULL, &ops[0], 0, n);
            if (id != pear_air::AIR_NO_VALUE)
            {
                b.m.values[id].facts.nullness = pear_erm::Nullness.NULL_ALWAYS;
            }
            return id;
        }

        case N_EXPR_UNIT:
            return b.emit(Op.AIR_CONST_UNIT, &ops[0], 0, n);

        case N_EXPR_IDENT:
        case N_EXPR_PATH:
        {
            /*
             Route by WHAT THE NAME RESOLVES TO, not by assuming it is a
             local.

             The original code sent every resolved identifier through
             read_var. That is only correct for a LOCAL BINDER — a
             parameter, a `let`, a pattern binder. A reference to a
             top-level function, a `const`, a `static` or an enum variant
             is not in the SSA variable map, so read_var fell through to
             its undefined-variable arm and produced AIR_UNKNOWN.

             That single mistake accounted for 3,104 of 3,466 unknowns
             across the stdlib: every `f(x)` where `f` is an ordinary
             top-level function. It is why `align_up(p as i64, a)` lowered
             with an unknown callee.
            */
            Node* d = n.resolved;
            if (d == null)
            {
                // Genuinely unbound. Pride is untyped and pfront leaves
                // module-path segments unresolved on purpose, so this is
                // a named external reference, not an error.
                uint id = b.emit(Op.AIR_GLOBAL_ADDR, &ops[0], 0, n);
                if (id != pear_air::AIR_NO_VALUE) { b.m.values[id].p.name = n.name_id; }
                return id;
            }

            switch (d.kind)
            {
                case N_PAT_IDENT:
                case N_DECL_PARAM:
                case N_DECL_LET:
                {
                    /*
                     A binder — but not necessarily a LOCAL one.

                     `let x = ...` at module scope is a mutable global and
                     resolves to exactly the same N_PAT_IDENT as a function
                     local. Sending it to read_var found nothing (it was
                     never written in any block) and produced AIR_UNKNOWN.
                     That was 291 of the remaining 315 holes, all of them
                     module-level state like `crc32_table_ready`.

                     Tell them apart by SCOPE, not by node kind: a binder
                     whose enclosing declaration chain reaches the program
                     root without passing a function is a global, and a
                     global is memory.
                    */
                    if (is_module_level(d))
                    {
                        uint a = b.emit(Op.AIR_GLOBAL_ADDR, &ops[0], 0, n);
                        if (a == pear_air::AIR_NO_VALUE) { return a; }
                        b.m.values[a].p.name = d.name_id != 0 ? d.name_id : n.name_id;
                        b.m.values[a].facts.nullness = pear_erm::Nullness.NULL_NEVER;
                        ops[0] = a;
                        return b.emit(Op.AIR_LOAD_PTR, &ops[0], 1, n);
                    }

                    uint v = b.read_var(d, b.cur_block);
                    if (v != pear_air::AIR_NO_VALUE) { return v; }

                    /*
                     A genuine local read on a path where it was never
                     written. Pride is untyped and never rejects, so this
                     stays an explicit hole rather than an error — but it
                     is a REAL one, so keep it countable.
                    */
                    b.unsupported = b.unsupported + 1;
                    b.miss_undef_read = b.miss_undef_read + 1;
                    return b.emit(Op.AIR_UNKNOWN, &ops[0], 0, n);
                }

                case N_DECL_FN:
                case N_DECL_EXTERN_FN:
                {
                    uint id = b.emit(Op.AIR_FUNC_REF, &ops[0], 0, n);
                    if (id != pear_air::AIR_NO_VALUE)
                    {
                        b.m.values[id].p.name = d.name_id != 0 ? d.name_id : n.name_id;
                        // A function address is never null.
                        b.m.values[id].facts.nullness = pear_erm::Nullness.NULL_NEVER;
                    }
                    return id;
                }

                case N_DECL_CONST:
                {
                    /*
                     A `const` with a literal initialiser is FOLDED here.
                     Emitting a const.ref and leaving the value for a2
                     would mean the range lattice starts from nothing on
                     every constant in the program — and R's whole value
                     comes from constants being the base case.
                    */
                    Node* init = null;
                    for (usz ci = 0; ci < d.child_count; ci++)
                    {
                        Node* c = d.children[ci];
                        if (c != null && pfront_core::is_expr(c.kind)) { init = c; }
                    }
                    if (init != null && init.kind == Nk.N_EXPR_INT)
                    {
                        return b.const_int((long)init.p.ival, init);
                    }
                    if (init != null && init.kind == Nk.N_EXPR_BOOL)
                    {
                        uint id = b.emit(Op.AIR_CONST_BOOL, &ops[0], 0, n);
                        if (id != pear_air::AIR_NO_VALUE)
                        {
                            b.m.values[id].p.ival = (long)init.p.ival;
                            b.m.values[id].facts.range = pear_erm::r_range(0, 1);
                            b.m.values[id].facts.width = 1;
                        }
                        return id;
                    }
                    // Non-literal initialiser (an expression over other
                    // consts): name it, and let a2 fold it once it has the
                    // whole module.
                    uint id = b.emit(Op.AIR_CONST_REF, &ops[0], 0, n);
                    if (id != pear_air::AIR_NO_VALUE)
                    {
                        b.m.values[id].p.name = d.name_id != 0 ? d.name_id : n.name_id;
                    }
                    return id;
                }

                case N_DECL_STATIC:
                {
                    // A mutable module global IS memory, so it gets an
                    // address and a load rather than a value (marker r56d
                    // in ssi_ir.c3 was this being bolted on late).
                    uint a = b.emit(Op.AIR_GLOBAL_ADDR, &ops[0], 0, n);
                    if (a == pear_air::AIR_NO_VALUE) { return a; }
                    b.m.values[a].p.name = d.name_id != 0 ? d.name_id : n.name_id;
                    b.m.values[a].facts.nullness = pear_erm::Nullness.NULL_NEVER;
                    ops[0] = a;
                    return b.emit(Op.AIR_LOAD_PTR, &ops[0], 1, n);
                }

                case N_DECL_VARIANT:
                {
                    // A nullary enum variant used as a value.
                    uint id = b.emit(Op.AIR_VARIANT_REF, &ops[0], 0, n);
                    if (id != pear_air::AIR_NO_VALUE)
                    {
                        b.m.values[id].p.name = d.name_id != 0 ? d.name_id : n.name_id;
                        b.m.values[id].p.index = (uint)d.p.ival;
                        b.m.values[id].facts.range = pear_erm::r_const((long)d.p.ival);
                    }
                    return id;
                }

                default:
                {
                    /*
                     Resolves to something with no runtime value: a struct
                     or type declaration used in value position, an effect,
                     an interface. Name it rather than dropping it.
                    */
                    uint id = b.emit(Op.AIR_GLOBAL_ADDR, &ops[0], 0, n);
                    if (id != pear_air::AIR_NO_VALUE)
                    {
                        b.m.values[id].p.name = d.name_id != 0 ? d.name_id : n.name_id;
                    }
                    return id;
                }
            }
        }

        case N_EXPR_BINARY:
        {
            if (n.child_count < 2) { break; }
            uint l = b.lower_operand(n.children[0]);
            uint r = b.lower_operand(n.children[1]);
            BOp op = binop_of(n.p.op);
            if (op == BOp.ABO_NONE) { break; }
            ops[0] = l; ops[1] = r;
            uint id = b.emit(Op.AIR_BIN, &ops[0], 2, n);
            if (id == pear_air::AIR_NO_VALUE) { return id; }
            b.m.values[id].p.op = op;
            pear_infer::infer_value(b.m, id);

            /*
             E. A division by a value not proven non-zero can fault, so the
             quotient is marked may-fault and the DIVISOR gets a π naming
             it on the surviving path. That π is what lets a second
             division by the same divisor skip its check.
            */
            if (op == BOp.ABO_DIV || op == BOp.ABO_MOD)
            {
                b.m.values[id].facts.may_fault = true;
                pear_air::AirValue* rv = b.m.val(r);
                if (rv != null && rv.facts.range.is_top)
                {
                    uint pi = b.m.new_pi(b.cur_block, r, id, Fact.FACT_NONZERO,
                                         n.line, n.col);
                    if (pi != pear_air::AIR_NO_VALUE)
                    {
                        b.pis = b.pis + 1;
                        Node* rn = n.children[1];
                        if (rn != null && rn.kind == Nk.N_EXPR_IDENT && rn.resolved != null)
                        {
                            b.write_var(rn.resolved, b.cur_block, pi);
                        }
                    }
                }
            }
            return id;
        }

        case N_EXPR_UNARY:
        {
            if (n.child_count < 1) { break; }
            uint v = b.lower_operand(n.children[0]);
            ops[0] = v;
            uint id = b.emit(Op.AIR_UN, &ops[0], 1, n);
            if (id == pear_air::AIR_NO_VALUE) { return id; }
            switch (n.p.op)
            {
                case TK_MINUS: b.m.values[id].p.uop = UOp.AUO_NEG;
                case TK_BANG:  b.m.values[id].p.uop = UOp.AUO_NOT;
                default:       b.m.values[id].p.uop = UOp.AUO_BNOT;
            }
            return id;
        }

        case N_EXPR_CAST:
        {
            if (n.child_count < 1) { break; }
            uint v = b.lower_operand(n.children[0]);
            ops[0] = v;
            uint id = b.emit(Op.AIR_CAST, &ops[0], 1, n);
            if (id != pear_air::AIR_NO_VALUE)
            {
                if (n.type_ann != null) { b.m.values[id].p.name = n.type_ann.name_id; }
                pear_infer::infer_value(b.m, id);
            }
            return id;
        }

        case N_EXPR_METHOD:
        {
            /*
             `a.b.f(args)` — the single most common unlowered construct in
             the stdlib (3,123 sites). The parser cannot tell a METHOD call
             on a value from a call to `f` exported by MODULE `a.b`, so it
             always builds N_EXPR_METHOD and the RESOLVER decides. By the
             time a1 runs, `resolved` already says which it was:

               resolved != null  a module-qualified call. The receiver is a
                                 module PATH, not a value, so it must NOT
                                 be lowered — doing so is what produced the
                                 spurious `global.addr name=os` noise.
               resolved == null  an ordinary method call on a value.

             Reading `resolved` rather than re-deciding is the whole point
             of a1 consuming the AST instead of the source.
            */
            usz k = 0;
            usz first_arg = 0;
            if (n.resolved != null)
            {
                // Module-qualified: children[0] is the module path.
                first_arg = 1;
            }
            for (usz i = first_arg; i < n.child_count && k < 16; i++)
            {
                ops[k] = b.lower_operand(n.children[i]);
                k = k + 1;
            }
            uint id = b.emit(n.resolved != null ? Op.AIR_CALL_DIRECT : Op.AIR_CALL,
                             &ops[0], k, n);
            if (id != pear_air::AIR_NO_VALUE) { b.m.values[id].p.name = n.name_id; }
            return id;
        }

        case N_EXPR_STRUCT_LIT:
        {
            /*
             `S { f: v, ... }`. The children are N_EXPR_FIELD_INIT, each
             wrapping one value. Lowering the INITS as operands directly —
             rather than recursing into them as expressions — is what
             removes both this (399) and N_EXPR_FIELD_INIT (1,194) from the
             unsupported list: the field-init node is a syntactic wrapper
             with no runtime content of its own.
            */
            usz k = 0;
            for (usz i = 0; i < n.child_count && k < 16; i++)
            {
                Node* c = n.children[i];
                if (c == null) { continue; }
                if (c.kind == Nk.N_EXPR_FIELD_INIT)
                {
                    // The init's value is its last child; a shorthand
                    // `S { x }` has none, and reads the variable instead.
                    if (c.child_count > 0)
                    {
                        ops[k] = b.lower_operand(c.children[c.child_count - 1]);
                    }
                    else
                    {
                        ops[k] = b.lower_operand(c);
                    }
                }
                else
                {
                    ops[k] = b.lower_operand(c);
                }
                k = k + 1;
            }
            uint id = b.emit(Op.AIR_STRUCT, &ops[0], k, n);
            if (id != pear_air::AIR_NO_VALUE) { b.m.values[id].p.name = n.name_id; }
            return id;
        }

        case N_EXPR_FIELD_INIT:
            // Reached only when a field init is visited outside a struct
            // literal. Transparent: its value is the value.
            if (n.child_count > 0) { return b.lower_expr(n.children[n.child_count - 1]); }
            return pear_air::AIR_NO_VALUE;

        case N_EXPR_FREE:
        {
            usz k = 0;
            for (usz i = 0; i < n.child_count && k < 16; i++)
            {
                ops[k] = b.lower_operand(n.children[i]);
                k = k + 1;
            }
            return b.emit(Op.AIR_FREE, &ops[0], k, n);
        }

        case N_EXPR_CALL:
        {
            /*
             A call CLOBBERS memory unless proven otherwise, which a1 never
             is. Marking it a memory def here rather than leaving it
             transparent is the conservative direction; the other way round
             is a miscompile.
            */
            usz n_args = 0;
            for (usz i = 0; i < n.child_count && n_args < 16; i++)
            {
                ops[n_args] = b.lower_operand(n.children[i]);
                n_args = n_args + 1;
            }
            uint id = b.emit(Op.AIR_CALL, &ops[0], n_args, n);
            return id;
        }

        case N_EXPR_FIELD:
        {
            if (n.child_count < 1) { break; }
            ops[0] = b.lower_operand(n.children[0]);
            uint id = b.emit(Op.AIR_LOAD_FIELD, &ops[0], 1, n);
            if (id != pear_air::AIR_NO_VALUE) { b.m.values[id].p.name = n.name_id; }
            return id;
        }

        case N_EXPR_INDEX:
        {
            if (n.child_count < 2) { break; }
            ops[0] = b.lower_operand(n.children[0]);
            ops[1] = b.lower_operand(n.children[1]);
            uint id = b.emit(Op.AIR_LOAD_INDEX, &ops[0], 2, n);
            if (id == pear_air::AIR_NO_VALUE) { return id; }
            /*
             E. An index can fault, so π the INDEX on the surviving path
             with inbounds. A second access at the same index then needs no
             check — the fact rides on the name.
            */
            b.m.values[id].facts.may_fault = true;
            uint pi = b.m.new_pi(b.cur_block, ops[1], id, Fact.FACT_INBOUNDS,
                                 n.line, n.col);
            if (pi != pear_air::AIR_NO_VALUE)
            {
                b.pis = b.pis + 1;
                Node* ix = n.children[1];
                if (ix != null && ix.kind == Nk.N_EXPR_IDENT && ix.resolved != null)
                {
                    b.write_var(ix.resolved, b.cur_block, pi);
                }
            }
            return id;
        }

        case N_EXPR_DEREF:
        {
            if (n.child_count < 1) { break; }
            ops[0] = b.lower_operand(n.children[0]);
            uint id = b.emit(Op.AIR_LOAD_PTR, &ops[0], 1, n);
            if (id == pear_air::AIR_NO_VALUE) { return id; }
            b.m.values[id].facts.may_fault = true;
            // E. Surviving a dereference proves the pointer non-null.
            uint pi = b.m.new_pi(b.cur_block, ops[0], id, Fact.FACT_NONNULL,
                                 n.line, n.col);
            if (pi != pear_air::AIR_NO_VALUE)
            {
                b.pis = b.pis + 1;
                Node* pn = n.children[0];
                if (pn != null && pn.kind == Nk.N_EXPR_IDENT && pn.resolved != null)
                {
                    b.write_var(pn.resolved, b.cur_block, pi);
                }
            }
            return id;
        }

        case N_EXPR_REF:
        {
            if (n.child_count < 1) { break; }
            Node* tgt = n.children[0];

            /*
             `&place` must compute an ADDRESS, never load and then take the
             address of the loaded value.

             `&p[i]` was lowering to `load.index` followed by `addr.of`,
             which is wrong twice: it performs a memory read the source
             never asked for (observable if the slot is uninitialised or
             volatile), and the address it yields is of a temporary rather
             than of the element.

             AIR_ADDR_INDEX and AIR_ADDR_FIELD exist for exactly this and
             were unreachable — nothing produced them, which is how the
             bug survived: the opcodes looked implemented.
            */
            if (tgt != null && tgt.kind == Nk.N_EXPR_INDEX && tgt.child_count > 1)
            {
                ops[0] = b.lower_operand(tgt.children[0]);
                ops[1] = b.lower_operand(tgt.children[1]);
                uint ai = b.emit(Op.AIR_ADDR_INDEX, &ops[0], 2, n);
                if (ai != pear_air::AIR_NO_VALUE)
                {
                    b.m.values[ai].facts.nullness = pear_erm::Nullness.NULL_NEVER;
                }
                return ai;
            }
            if (tgt != null && tgt.kind == Nk.N_EXPR_FIELD && tgt.child_count > 0)
            {
                ops[0] = b.lower_operand(tgt.children[0]);
                uint af = b.emit(Op.AIR_ADDR_FIELD, &ops[0], 1, n);
                if (af != pear_air::AIR_NO_VALUE)
                {
                    b.m.values[af].p.name = tgt.name_id;
                    b.m.values[af].facts.nullness = pear_erm::Nullness.NULL_NEVER;
                }
                return af;
            }

            ops[0] = b.lower_operand(tgt);
            uint id = b.emit(Op.AIR_ADDR_OF, &ops[0], 1, n);
            if (id != pear_air::AIR_NO_VALUE)
            {
                b.m.values[id].facts.nullness = pear_erm::Nullness.NULL_NEVER;
            }
            return id;
        }

        case N_EXPR_TUPLE:
        {
            usz k = 0;
            for (usz i = 0; i < n.child_count && k < 16; i++)
            {
                ops[k] = b.lower_operand(n.children[i]);
                k = k + 1;
            }
            return b.emit(Op.AIR_TUPLE, &ops[0], k, n);
        }

        case N_EXPR_ARRAY:
        {
            usz k = 0;
            for (usz i = 0; i < n.child_count && k < 16; i++)
            {
                ops[k] = b.lower_operand(n.children[i]);
                k = k + 1;
            }
            return b.emit(Op.AIR_ARRAY, &ops[0], k, n);
        }

        case N_EXPR_ALLOC:
        {
            usz k = 0;
            for (usz i = 0; i < n.child_count && k < 16; i++)
            {
                ops[k] = b.lower_operand(n.children[i]);
                k = k + 1;
            }
            uint id = b.emit(Op.AIR_ALLOC, &ops[0], k, n);
            if (id != pear_air::AIR_NO_VALUE)
            {
                // A fresh allocation cannot alias anything existing: the
                // strongest alias fact available, and what escape analysis
                // is built on.
                b.m.values[id].facts.nullness = pear_erm::Nullness.NULL_NEVER;
                b.m.values[id].facts.mem.no_alias = true;
            }
            return id;
        }

        case N_EXPR_ASM:
        {
            /*
             Inline assembly. Opaque to every analysis by definition, but
             it is NOT a lowering hole: the operands are real and must be
             kept live, and it must be treated as clobbering memory.

             AIR_UNKNOWN would be wrong here in a subtle way — it would say
             "a1 could not translate this", when in fact this IS the
             translation. Conflating "opaque" with "unimplemented" is how a
             coverage number stops meaning anything.
            */
            usz k = 0;
            for (usz i = 0; i < n.child_count && k < 16; i++)
            {
                Node* c = n.children[i];
                if (c == null || !pfront_core::is_expr(c.kind)) { continue; }
                ops[k] = b.lower_operand(c);
                k = k + 1;
            }
            uint id = b.emit(Op.AIR_ASM, &ops[0], k, n);
            if (id != pear_air::AIR_NO_VALUE)
            {
                b.m.values[id].p.name = n.name_id;
                b.m.values[id].facts.may_fault = true;
            }
            return id;
        }

        case N_EXPR_PERFORM:
        {
            /*
             `perform Effect.op(args)`.

             children[0] is the MODULE PATH naming the operation, not an
             argument. Lowering it as one produced two `unknown` values per
             perform (the path segments have no runtime value) and buried
             the real arguments behind them.

             The operation's identity is already in `name_id`, put there by
             the resolver, so the path is dropped and only the arguments
             become operands.
            */
            usz k = 0;
            for (usz i = 0; i < n.child_count && k < 16; i++)
            {
                Node* c = n.children[i];
                if (c == null) { continue; }
                if (c.kind == Nk.N_MODULE_PATH || c.kind == Nk.N_PATH_SEG) { continue; }
                ops[k] = b.lower_operand(c);
                k = k + 1;
            }
            uint id = b.emit(Op.AIR_PERFORM, &ops[0], k, n);
            if (id != pear_air::AIR_NO_VALUE) { b.m.values[id].p.name = n.name_id; }
            return id;
        }

        case N_EXPR_HANDLE:
            return b.lower_handle(n);

        case N_HANDLER_ARM:
            // Reached only if an arm is visited outside its handler; the
            // handler lowers its own arms.
            return b.lower_handler_arm(n);

        case N_EXPR_RESUME:
        {
            usz k = 0;
            for (usz i = 0; i < n.child_count && k < 16; i++)
            {
                ops[k] = b.lower_operand(n.children[i]);
                k = k + 1;
            }
            return b.emit(Op.AIR_RESUME, &ops[0], k, n);
        }

        /*
         Statement-shaped nodes reachable from EXPRESSION position.

         `x = e` and `x += e` are N_STMT_ASSIGN / N_STMT_COMPOUND_ASSIGN
         even when they appear inside an expression (a semicolon chain in
         a clause body, an `if` branch used as a value). lower_stmt has the
         rules; lower_expr had no case and fell through to AIR_UNKNOWN.

         Delegating rather than duplicating: two copies of the assignment
         lowering would be two places to fix a store-shape bug.
        */
        case N_STMT_ASSIGN:
        case N_EXPR_ASSIGN:
        case N_STMT_COMPOUND_ASSIGN:
        case N_STMT_RETURN:
        case N_STMT_BREAK:
        case N_STMT_CONTINUE:
        case N_STMT_EXPR:
        case N_DECL_LET:
            return b.lower_stmt(n);

        case N_EXPR_IF:
            return b.lower_if(n);

        case N_EXPR_MATCH:
            return b.lower_match(n);

        case N_EXPR_WHILE:
            return b.lower_while(n);

        case N_BLOCK:
            return b.lower_block(n);

        case N_EXPR_UNSAFE:
        case N_EXPR_UNCHECKED:
        case N_EXPR_COMPTIME:
            // Transparent wrappers: lower the body, keep no node. The
            // safety obligation was already checked by pfront.
            if (n.child_count > 0) { return b.lower_expr(n.children[0]); }
            return pear_air::AIR_NO_VALUE;

        case N_EXPR_UNREACHABLE:
            b.m.set_term(b.cur_block, Term.TERM_UNREACHABLE, pear_air::AIR_NO_VALUE);
            return pear_air::AIR_NO_VALUE;

        case N_EXPR_TRAP:
            b.m.set_term(b.cur_block, Term.TERM_TRAP, pear_air::AIR_NO_VALUE);
            return pear_air::AIR_NO_VALUE;

        case N_EXPR_UB:
            b.m.set_term(b.cur_block, Term.TERM_UB, pear_air::AIR_NO_VALUE);
            return pear_air::AIR_NO_VALUE;

        default:
            break;
    }

    /*
     No rule yet. Preserve the operands so the IR stays well-formed and the
     value is still referenceable, and COUNT it. This is what makes it
     possible to run the lowering over the whole stdlib and get a real
     answer about coverage instead of a crash.
    */
    usz k = 0;
    for (usz i = 0; i < n.child_count && k < 16; i++)
    {
        uint c = b.lower_expr(n.children[i]);
        if (c != pear_air::AIR_NO_VALUE) { ops[k] = c; k = k + 1; }
    }
    b.unsupported = b.unsupported + 1;
    b.note_unsupported(n.kind);
    return b.emit(Op.AIR_UNKNOWN, &ops[0], k, n);
}

// ════════════════════════════════════════════════════════════════════════
// CONTROL FLOW
// ════════════════════════════════════════════════════════════════════════

fn uint Builder.lower_if(Builder* b, Node* n)
{
    if (n.child_count < 2) { return pear_air::AIR_NO_VALUE; }

    Node* cond_n = n.children[0];
    uint cond = b.lower_expr(cond_n);

    uint entry = b.cur_block;
    uint bt = b.m.new_block(b.cur_func, 0);
    uint be = n.child_count > 2 ? b.m.new_block(b.cur_func, 0) : 0;
    uint bj = b.m.new_block(b.cur_func, 0);

    // Both arms have exactly one predecessor and can be sealed at once.
    b.mark_sealed(bt, true);
    if (be != 0) { b.mark_sealed(be, true); }

    b.m.set_term(entry, Term.TERM_BRANCH, cond);
    b.m.add_edge(entry, bt);
    b.m.add_edge(entry, be != 0 ? be : bj);

    // e-SSI: one σ per outgoing edge, in the successor.
    b.place_sigma(cond_n, cond, bt, true);
    b.place_sigma(cond_n, cond, be != 0 ? be : bj, false);

    b.cur_block = bt;
    uint tv = b.lower_expr(n.children[1]);
    bool t_open = b.block_open();
    if (t_open)
    {
        b.m.set_term(b.cur_block, Term.TERM_JUMP, pear_air::AIR_NO_VALUE);
        b.m.add_edge(b.cur_block, bj);
    }
    uint t_end = b.cur_block;

    uint ev = pear_air::AIR_NO_VALUE;
    uint e_end = 0;
    bool e_open = false;
    if (be != 0)
    {
        b.cur_block = be;
        ev = b.lower_expr(n.children[2]);
        e_open = b.block_open();
        if (e_open)
        {
            b.m.set_term(b.cur_block, Term.TERM_JUMP, pear_air::AIR_NO_VALUE);
            b.m.add_edge(b.cur_block, bj);
        }
        e_end = b.cur_block;
    }

    // The join's predecessors are complete only now.
    b.mark_sealed(bj, true);
    b.seal_block(bj);
    b.cur_block = bj;

    /*
     An `if` used as a VALUE needs a φ at the join. Only build one when
     both arms actually reach it — an arm ending in `return` contributes no
     edge, and a φ with an operand from a non-predecessor is exactly what
     verify.c3 rejects.
    */
    if (be != 0 && t_open && e_open
        && tv != pear_air::AIR_NO_VALUE && ev != pear_air::AIR_NO_VALUE)
    {
        uint[2] ops;
        uint[2] incs;
        ops[0] = tv;   incs[0] = t_end;
        ops[1] = ev;   incs[1] = e_end;
        uint phi = b.m.new_phi(bj, &ops[0], &incs[0], 2,
                               pear_air::AIR_NO_ORIGIN, n.line, n.col);
        if (phi != pear_air::AIR_NO_VALUE)
        {
            b.phis_created = b.phis_created + 1;
            pear_infer::infer_value(b.m, phi);
        }
        return phi;
    }
    if (t_open && !e_open && be != 0) { return tv; }
    if (!t_open && e_open) { return ev; }
    return pear_air::AIR_NO_VALUE;
}

fn uint Builder.lower_while(Builder* b, Node* n)
{
    if (n.child_count < 2) { return pear_air::AIR_NO_VALUE; }

    uint pre = b.cur_block;
    uint head = b.m.new_block(b.cur_func, 0);
    uint body = b.m.new_block(b.cur_func, 0);
    uint exit = b.m.new_block(b.cur_func, 0);

    b.m.set_term(pre, Term.TERM_JUMP, pear_air::AIR_NO_VALUE);
    b.m.add_edge(pre, head);

    /*
     The header is created UNSEALED: its back edge does not exist until the
     body has been built. Any variable read in the condition parks an
     incomplete φ, which seal_block completes once the back edge is added.
     This is the whole reason Braun's algorithm needs sealing, and it is
     what makes a loop-carried variable work in a single pass.
    */
    b.mark_sealed(head, false);
    b.mark_sealed(body, true);
    b.mark_sealed(exit, true);

    b.cur_block = head;
    Node* cond_n = n.children[0];
    uint cond = b.lower_expr(cond_n);
    uint head_end = b.cur_block;
    b.m.set_term(head_end, Term.TERM_BRANCH, cond);
    b.m.add_edge(head_end, body);
    b.m.add_edge(head_end, exit);

    b.place_sigma(cond_n, cond, body, true);
    b.place_sigma(cond_n, cond, exit, false);

    bool saved_in = b.in_loop;
    uint saved_h = b.loop_header;
    uint saved_e = b.loop_exit;
    b.in_loop = true;
    b.loop_header = head;
    b.loop_exit = exit;

    b.cur_block = body;
    b.lower_expr(n.children[1]);
    if (b.block_open())
    {
        b.m.set_term(b.cur_block, Term.TERM_JUMP, pear_air::AIR_NO_VALUE);
        b.m.add_edge(b.cur_block, head);      // the back edge
    }

    b.in_loop = saved_in;
    b.loop_header = saved_h;
    b.loop_exit = saved_e;

    // The back edge exists now, so the header's predecessors are complete.
    b.seal_block(head);

    b.cur_block = exit;
    /*
     A `while` has no value, but it can appear in a position that needs
     one (the last expression of a clause body, an operand of a chain).
     Returning NO_VALUE there forced the caller into lower_operand's hole
     path. Unit is the honest answer and keeps the IR total.
    */
    uint[1] none;
    return b.emit(Op.AIR_CONST_UNIT, &none[0], 0, n);
}



// ════════════════════════════════════════════════════════════════════════
// EFFECT HANDLERS
// ════════════════════════════════════════════════════════════════════════

/*
 `handle comp | E.op params k -> body ...` (spec §10).

 Lowered to the three backend-agnostic opcodes ssi_ir.c3 got right and
 PEAR.md section 8 says to keep: AIR_HANDLE installs a handler frame over
 a computation, AIR_HANDLE_ARM is one operation's body, AIR_RESUME re-enters
 the delimited continuation.

 Deliberately NOT lowered to a concrete mechanism here. Whether a handler
 becomes a vtable, a prompt stack, a split stack or a CPS transform is a
 backend choice, and a3 is where the double-barrelled CPS conversion
 happens. Committing to one now would make that stage a rewrite instead of
 a translation.

 Operand layout, checked by verify.c3:
   AIR_HANDLE      operands[0] = the computation's value
                   operands[1..] = one AIR_HANDLE_ARM per operation
   AIR_HANDLE_ARM  operands[0] = the arm body's value
                   payload.name = the operation it handles

 Each arm gets its OWN BLOCK. An arm body is entered by a non-local jump
 from wherever the effect was performed, not by falling through the
 computation, so giving arms their own blocks is what keeps the CFG honest
 — putting them inline would claim the computation reaches them by an edge
 that does not exist.
*/
fn uint Builder.lower_handler_arm(Builder* b, Node* arm)
{
    uint[4] ops;

    /*
     An arm binds its operation's PARAMETERS and its CONTINUATION `k`:

         | State.get () k -> resume cell

     Both are pattern children. They must be bound before the body is
     lowered, or every use of `k` inside it is an undefined read.
    */
    Node* body = null;
    for (usz i = 0; i < arm.child_count; i++)
    {
        Node* c = arm.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.N_MODULE_PATH || c.kind == Nk.N_PATH_SEG) { continue; }
        if (pfront_core::is_pattern(c.kind))
        {
            // A parameter of the operation, or the continuation binder.
            uint[1] none;
            uint pv = b.m.new_value(b.cur_block, Op.AIR_PARAM, &none[0], 0,
                                    pear_air::AIR_NO_ORIGIN, c.line, c.col);
            if (pv != pear_air::AIR_NO_VALUE)
            {
                b.m.values[pv].p.name = c.name_id;
                b.bind_pattern_vars(c, pv);
            }
            continue;
        }
        body = c;
    }

    uint bv = body != null ? b.lower_operand(body)
                           : b.emit(Op.AIR_CONST_UNIT, &ops[0], 0, arm);
    ops[0] = bv;
    uint id = b.emit(Op.AIR_HANDLE_ARM, &ops[0], 1, arm);
    if (id != pear_air::AIR_NO_VALUE) { b.m.values[id].p.name = arm.name_id; }
    return id;
}

fn uint Builder.lower_handle(Builder* b, Node* n)
{
    uint[32] ops;
    usz nops = 0;

    // The computation is the first non-arm child.
    Node* comp = null;
    for (usz i = 0; i < n.child_count; i++)
    {
        Node* c = n.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.N_HANDLER_ARM) { continue; }
        if (comp == null) { comp = c; }
    }

    /*
     No new blocks. The computation and the arm bodies are ordinary values
     in the current block; the handler node ties them together.

     Splitting them across blocks would need edges that do not exist (see
     the comment on the arm loop below), and a1's job is to record the
     structure faithfully, not to invent a control-flow shape that a3 will
     have to undo.
    */
    uint cv = comp != null ? b.lower_operand(comp)
                           : b.emit(Op.AIR_CONST_UNIT, &ops[0], 0, n);
    ops[0] = cv;
    nops = 1;

    /*
     Arms are lowered INLINE in the computation's block, not as separate
     CFG blocks.

     My first attempt gave each arm its own block with an edge from the
     handler's entry. That is wrong twice over, and the verifier caught
     both: the entry's terminator is a `jump` (arity 1) so a second
     successor is malformed, and an arm's values then failed dominance
     because the edge licensing them does not really exist.

     The deeper point is that an arm is entered by a NON-LOCAL transfer
     from wherever the effect was performed — that is what makes it a
     delimited continuation. It is NOT a successor of the block that
     installs the frame, and inventing that edge tells every downstream
     analysis something false about control flow.

     So the arms are simply OPERANDS of AIR_HANDLE. The handler node is
     what says "these bodies may run"; making the transfer explicit is
     a3's job, where the double-barrelled CPS conversion turns each arm
     into a real continuation. a1 records the structure without lying
     about the edges.
    */
    for (usz i = 0; i < n.child_count && nops < 32; i++)
    {
        Node* c = n.children[i];
        if (c == null || c.kind != Nk.N_HANDLER_ARM) { continue; }
        ops[nops] = b.lower_handler_arm(c);
        nops = nops + 1;
    }

    uint id = b.emit(Op.AIR_HANDLE, &ops[0], nops, n);
    if (id != pear_air::AIR_NO_VALUE) { b.m.values[id].p.name = n.name_id; }
    return id;
}

// ════════════════════════════════════════════════════════════════════════
// MATCH
// ════════════════════════════════════════════════════════════════════════

/*
 Pattern matching, lowered as a SEQUENTIAL DECISION CHAIN.

 One test block per arm, falling through to the next on failure:

     test0 --fail--> test1 --fail--> test2 --fail--> nomatch
       |               |               |
      body0          body1           body2
       \_______________\_______________\____________> join

 Not a switch, and not a balanced decision tree, for three reasons that
 are specific to Pride rather than to convenience:

   1. Arm order is SEMANTIC. Pride arms are tried top to bottom and the
      first match wins, so two arms can overlap and the earlier one must
      shadow the later. A switch reorders by key and loses that.
   2. Patterns are heterogeneous. A single match can mix a literal, a
      variant, a range, an or-pattern and a binder. Only the literal and
      variant cases are switch-able at all.
   3. A chain is CORRECT for every pattern kind, and a switch is an
      optimisation of one special case. a2 has the CFG and the range facts
      to recognise "all arms are disjoint integer literals" and rebuild it
      as a switch, with better information than a1 has.

 So a1 emits the form that is always right, and leaves the specialisation
 to the stage that can prove it is safe. Correct first, fast second.

 Every arm's body jumps to a shared join, where a φ merges the results —
 which is what makes `match` usable as an expression.
*/

/*
 Emit the boolean test for one pattern against the scrutinee.

 Returns AIR_NO_VALUE for an IRREFUTABLE pattern (a wildcard or a bare
 binder), which always matches and therefore needs no test at all. The
 caller uses that to end the chain rather than emitting `if (true)`.
*/
fn uint Builder.pattern_test(Builder* b, Node* pat, uint scrut)
{
    if (pat == null) { return pear_air::AIR_NO_VALUE; }
    uint[2] ops;

    switch (pat.kind)
    {
        case N_PAT_WILDCARD:
        case N_PAT_IDENT:
            // Irrefutable: matches anything. No test.
            return pear_air::AIR_NO_VALUE;

        case N_PAT_LITERAL:
        {
            // `| 3i64 ->` : scrutinee == literal
            Node* lit = pat.child_count > 0 ? pat.children[0] : pat;
            uint lv = b.lower_operand(lit);
            ops[0] = scrut; ops[1] = lv;
            uint t = b.emit(Op.AIR_BIN, &ops[0], 2, pat);
            if (t != pear_air::AIR_NO_VALUE)
            {
                b.m.values[t].p.op = BOp.ABO_EQ;
                pear_infer::infer_value(b.m, t);
            }
            return t;
        }

        case N_PAT_VARIANT:
        {
            /*
             `| Color.Red ->` : compare the scrutinee's discriminant.

             The variant's tag comes from its DECLARATION, which the
             resolver already attached. Re-deriving it from the pattern's
             spelling would mean re-implementing enum numbering in a1.
            */
            Node* d = pat.resolved;
            long tag = 0;
            if (d != null) { tag = (long)d.p.ival; }
            uint tv = b.const_int(tag, pat);
            ops[0] = scrut; ops[1] = tv;
            uint t = b.emit(Op.AIR_BIN, &ops[0], 2, pat);
            if (t != pear_air::AIR_NO_VALUE)
            {
                b.m.values[t].p.op = BOp.ABO_EQ;
                pear_infer::infer_value(b.m, t);
            }
            return t;
        }

        case N_PAT_RANGE:
        {
            // `| 1i64..9i64 ->` : lo <= s && s <= hi
            if (pat.child_count < 2) { return pear_air::AIR_NO_VALUE; }
            uint lo = b.lower_operand(pat.children[0]);
            uint hi = b.lower_operand(pat.children[1]);
            ops[0] = scrut; ops[1] = lo;
            uint ge = b.emit(Op.AIR_BIN, &ops[0], 2, pat);
            if (ge != pear_air::AIR_NO_VALUE) { b.m.values[ge].p.op = BOp.ABO_GE; }
            ops[0] = scrut; ops[1] = hi;
            uint le = b.emit(Op.AIR_BIN, &ops[0], 2, pat);
            if (le != pear_air::AIR_NO_VALUE) { b.m.values[le].p.op = BOp.ABO_LE; }
            ops[0] = ge; ops[1] = le;
            uint both = b.emit(Op.AIR_BIN, &ops[0], 2, pat);
            if (both != pear_air::AIR_NO_VALUE)
            {
                b.m.values[both].p.op = BOp.ABO_LAND;
                pear_infer::infer_value(b.m, both);
            }
            return both;
        }

        case N_PAT_OR:
        {
            /*
             `| a | b ->` : any alternative matching is a match.

             An alternative that is itself irrefutable makes the WHOLE
             or-pattern irrefutable, so the chain must stop there rather
             than emitting a test that can never fail.
            */
            uint acc = pear_air::AIR_NO_VALUE;
            for (usz i = 0; i < pat.child_count; i++)
            {
                uint t = b.pattern_test(pat.children[i], scrut);
                if (t == pear_air::AIR_NO_VALUE) { return pear_air::AIR_NO_VALUE; }
                if (acc == pear_air::AIR_NO_VALUE) { acc = t; continue; }
                ops[0] = acc; ops[1] = t;
                uint o = b.emit(Op.AIR_BIN, &ops[0], 2, pat);
                if (o != pear_air::AIR_NO_VALUE) { b.m.values[o].p.op = BOp.ABO_LOR; }
                acc = o;
            }
            return acc;
        }

        case N_PAT_TUPLE:
        case N_PAT_STRUCT:
        case N_PAT_ARRAY:
        {
            /*
             A destructuring pattern tests each SUB-pattern against the
             corresponding field, and matches only if all of them do. A
             sub-pattern that is a plain binder contributes no test, which
             is why a tuple of binders is irrefutable and correctly
             produces no branch at all.
            */
            uint acc = pear_air::AIR_NO_VALUE;
            for (usz i = 0; i < pat.child_count; i++)
            {
                Node* sub = pat.children[i];
                if (sub == null) { continue; }
                ops[0] = scrut;
                uint fld = b.emit(Op.AIR_LOAD_FIELD, &ops[0], 1, sub);
                if (fld != pear_air::AIR_NO_VALUE) { b.m.values[fld].p.index = (uint)i; }
                uint t = b.pattern_test(sub, fld);
                if (t == pear_air::AIR_NO_VALUE) { continue; }
                if (acc == pear_air::AIR_NO_VALUE) { acc = t; continue; }
                ops[0] = acc; ops[1] = t;
                uint a2 = b.emit(Op.AIR_BIN, &ops[0], 2, pat);
                if (a2 != pear_air::AIR_NO_VALUE) { b.m.values[a2].p.op = BOp.ABO_LAND; }
                acc = a2;
            }
            return acc;
        }

        case N_PAT_REF:
            // `| &p ->` : the reference itself imposes no test; recurse.
            if (pat.child_count > 0) { return b.pattern_test(pat.children[0], scrut); }
            return pear_air::AIR_NO_VALUE;

        case N_PAT_REST:
            // `..` matches any remainder.
            return pear_air::AIR_NO_VALUE;

        default:
            /*
             An unknown pattern kind must be treated as IRREFUTABLE, not as
             a failing test. Emitting a test that can never succeed would
             silently skip the arm and change program behaviour; treating
             it as always-matching preserves the arm and merely loses
             precision. Wrong-but-safe over wrong-and-silent.
            */
            b.unsupported = b.unsupported + 1;
            b.note_unsupported(pat.kind);
            return pear_air::AIR_NO_VALUE;
    }
}

/*
 Bind every binder in a pattern to the corresponding piece of the
 scrutinee. Runs in the arm's BODY block, after the test has passed, so a
 binding is only in scope where it is valid.
*/
fn void Builder.bind_pattern_vars(Builder* b, Node* pat, uint scrut)
{
    if (pat == null) { return; }
    uint[1] ops;
    switch (pat.kind)
    {
        case N_PAT_IDENT:
            b.write_var(pat, b.cur_block, scrut);

        case N_PAT_VARIANT:
        {
            // A variant's PAYLOAD binders: `| Some(x) ->` binds x.
            for (usz i = 0; i < pat.child_count; i++)
            {
                Node* sub = pat.children[i];
                if (sub == null || !pfront_core::is_pattern(sub.kind)) { continue; }
                ops[0] = scrut;
                uint fld = b.emit(Op.AIR_LOAD_FIELD, &ops[0], 1, sub);
                if (fld != pear_air::AIR_NO_VALUE) { b.m.values[fld].p.index = (uint)i; }
                b.bind_pattern_vars(sub, fld);
            }
        }

        case N_PAT_TUPLE:
        case N_PAT_STRUCT:
        case N_PAT_ARRAY:
        {
            for (usz i = 0; i < pat.child_count; i++)
            {
                Node* sub = pat.children[i];
                if (sub == null) { continue; }
                ops[0] = scrut;
                uint fld = b.emit(Op.AIR_LOAD_FIELD, &ops[0], 1, sub);
                if (fld != pear_air::AIR_NO_VALUE) { b.m.values[fld].p.index = (uint)i; }
                b.bind_pattern_vars(sub, fld);
            }
        }

        case N_PAT_REF:
            if (pat.child_count > 0) { b.bind_pattern_vars(pat.children[0], scrut); }

        default:
            break;
    }
}

/*
 Lower a `match` expression, or the multi-clause body of a function.

 `arms` are N_MATCH_ARM or N_CLAUSE nodes; both hold a pattern followed by
 a body, so one routine serves both and multi-clause dispatch stops being
 a separate unimplemented feature.
*/
fn uint Builder.lower_match_arms(Builder* b, Node* owner, uint scrut,
                                 Node** arms, usz arm_count)
{
    if (arm_count == 0) { return pear_air::AIR_NO_VALUE; }

    uint join = b.m.new_block(b.cur_func, 0);
    b.mark_sealed(join, false);   // predecessors accumulate as arms close

    // One result/incoming pair per arm that reaches the join.
    uint[64] res;
    uint[64] from;
    usz nres = 0;

    for (usz i = 0; i < arm_count; i++)
    {
        Node* arm = arms[i];
        if (arm == null) { continue; }

        // An arm is `pattern [guard] body...`.
        Node* pat = null;
        usz body_at = arm.child_count;
        for (usz k = 0; k < arm.child_count; k++)
        {
            Node* c = arm.children[k];
            if (c == null) { continue; }
            if (pat == null && pfront_core::is_pattern(c.kind)) { pat = c; continue; }
            if (body_at == arm.child_count) { body_at = k; }
        }

        uint test = b.pattern_test(pat, scrut);

        uint body_blk;
        uint next_blk = pear_air::AIR_NO_BLOCK;
        if (test == pear_air::AIR_NO_VALUE)
        {
            /*
             IRREFUTABLE arm: no branch, and everything after it is dead.
             Emitting a test would be `if (true)`, and continuing the chain
             would build blocks no path reaches.
            */
            body_blk = b.cur_block;
        }
        else
        {
            body_blk = b.m.new_block(b.cur_func, 0);
            next_blk = b.m.new_block(b.cur_func, 0);
            b.mark_sealed(body_blk, true);
            b.mark_sealed(next_blk, true);
            b.m.set_term(b.cur_block, Term.TERM_BRANCH, test);
            b.m.add_edge(b.cur_block, body_blk);
            b.m.add_edge(b.cur_block, next_blk);
            b.cur_block = body_blk;
        }

        // Bindings live in the body, after the test succeeded.
        b.bind_pattern_vars(pat, scrut);

        uint v = pear_air::AIR_NO_VALUE;
        for (usz k = body_at; k < arm.child_count; k++)
        {
            if (!b.block_open()) { break; }
            v = b.lower_stmt(arm.children[k]);
        }
        if (b.block_open())
        {
            b.m.set_term(b.cur_block, Term.TERM_JUMP, pear_air::AIR_NO_VALUE);
            b.m.add_edge(b.cur_block, join);
            if (nres < 64)
            {
                res[nres] = v == pear_air::AIR_NO_VALUE
                          ? b.emit(Op.AIR_CONST_UNIT, &res[0], 0, arm)
                          : v;
                from[nres] = b.cur_block;
                nres = nres + 1;
            }
        }

        if (test == pear_air::AIR_NO_VALUE) { break; }   // chain ends here
        b.cur_block = next_blk;
    }

    /*
     The fall-through end of the chain: every pattern failed.

     Pride is untyped and pfront does NOT reject a non-exhaustive match
     (it warns). So this must produce something rather than being assumed
     unreachable — asserting unreachable and being wrong is a miscompile.
     `trap` is the honest lowering: reaching it is a real runtime error.
    */
    if (b.block_open())
    {
        b.m.set_term(b.cur_block, Term.TERM_TRAP, pear_air::AIR_NO_VALUE);
    }

    b.mark_sealed(join, true);
    b.seal_block(join);
    b.cur_block = join;

    if (nres == 0) { return pear_air::AIR_NO_VALUE; }
    if (nres == 1) { return res[0]; }

    uint phi = b.m.new_phi(join, &res[0], &from[0], nres,
                           pear_air::AIR_NO_ORIGIN, owner.line, owner.col);
    if (phi != pear_air::AIR_NO_VALUE)
    {
        b.phis_created = b.phis_created + 1;
        pear_infer::infer_value(b.m, phi);
    }
    return phi;
}

fn uint Builder.lower_match(Builder* b, Node* n)
{
    if (n.child_count < 1) { return pear_air::AIR_NO_VALUE; }
    uint scrut = b.lower_operand(n.children[0]);

    Node*[64] arms;
    usz na = 0;
    for (usz i = 1; i < n.child_count && na < 64; i++)
    {
        Node* c = n.children[i];
        if (c != null && c.kind == Nk.N_MATCH_ARM) { arms[na] = c; na = na + 1; }
    }
    return b.lower_match_arms(n, scrut, &arms[0], na);
}

// ════════════════════════════════════════════════════════════════════════
// STATEMENTS
// ════════════════════════════════════════════════════════════════════════

fn uint Builder.lower_block(Builder* b, Node* n)
{
    uint last = pear_air::AIR_NO_VALUE;
    for (usz i = 0; i < n.child_count; i++)
    {
        if (!b.block_open()) { break; }   // unreachable tail
        last = b.lower_stmt(n.children[i]);
    }
    return last;
}

fn uint Builder.lower_stmt(Builder* b, Node* n)
{
    if (n == null) { return pear_air::AIR_NO_VALUE; }
    uint[4] ops;

    switch (n.kind)
    {
        case N_DECL_LET:
        {
            /*
             A `let` is not a memory operation: it BINDS a name to a value.
             Recording it in the variable map rather than emitting a store
             is what keeps scalars in SSA registers instead of forcing a
             mem2reg pass later.
            */
            /*
             Accept ANY pattern, not just a bare identifier.

             `let (v0, v1, v2, v3) = sip_round(...)` is routine in this
             stdlib. Matching only N_PAT_IDENT left the tuple's binders
             unwritten, so every later use fell into read_var's
             undefined-variable arm — 104 holes in siphash.pie alone from
             this one omission.

             bind_pattern_vars already destructures, so reuse it rather
             than writing a second, subtly different, version.
            */
            Node* pat = null;
            Node* init = null;
            for (usz i = 0; i < n.child_count; i++)
            {
                Node* c = n.children[i];
                if (c == null) { continue; }
                if (pat == null && pfront_core::is_pattern(c.kind)) { pat = c; continue; }
                if (pfront_core::is_expr(c.kind) || c.kind == Nk.N_BLOCK) { init = c; }
            }
            uint v = init != null ? b.lower_expr(init) : pear_air::AIR_NO_VALUE;
            if (v == pear_air::AIR_NO_VALUE) { v = b.emit(Op.AIR_CONST_UNIT, &ops[0], 0, n); }
            if (pat != null) { b.bind_pattern_vars(pat, v); }
            return v;
        }

        case N_STMT_RETURN:
        {
            uint v = pear_air::AIR_NO_VALUE;
            if (n.child_count > 0) { v = b.lower_expr(n.children[0]); }
            b.m.set_term(b.cur_block, Term.TERM_RET, v);
            return v;
        }

        case N_STMT_BREAK:
            if (b.in_loop)
            {
                b.m.set_term(b.cur_block, Term.TERM_JUMP, pear_air::AIR_NO_VALUE);
                b.m.add_edge(b.cur_block, b.loop_exit);
            }
            return pear_air::AIR_NO_VALUE;

        case N_STMT_CONTINUE:
            if (b.in_loop)
            {
                b.m.set_term(b.cur_block, Term.TERM_JUMP, pear_air::AIR_NO_VALUE);
                b.m.add_edge(b.cur_block, b.loop_header);
            }
            return pear_air::AIR_NO_VALUE;

        case N_STMT_COMPOUND_ASSIGN:
        {
            /*
             `x += e` is `x = x + e`, desugared here rather than in the
             parser so the AST keeps the source shape and a1 owns the
             expansion. The READ of x must happen before the write, and
             must go through read_var so it sees the current SSA version.
            */
            if (n.child_count < 2) { break; }
            Node* lhs = n.children[0];
            uint cur = b.lower_operand(lhs);
            uint rhs = b.lower_operand(n.children[1]);
            BOp op = compound_binop_of(n.p.op);
            if (op == BOp.ABO_NONE) { break; }
            ops[0] = cur; ops[1] = rhs;
            uint combined = b.emit(Op.AIR_BIN, &ops[0], 2, n);
            if (combined == pear_air::AIR_NO_VALUE) { break; }
            b.m.values[combined].p.op = op;
            pear_infer::infer_value(b.m, combined);

            if (lhs != null && lhs.kind == Nk.N_EXPR_IDENT && lhs.resolved != null)
            {
                b.write_var(lhs.resolved, b.cur_block, combined);
                return combined;
            }
            if (lhs != null && lhs.kind == Nk.N_EXPR_DEREF && lhs.child_count > 0)
            {
                ops[0] = b.lower_operand(lhs.children[0]);
                ops[1] = combined;
                return b.emit(Op.AIR_STORE_PTR, &ops[0], 2, n);
            }
            if (lhs != null && lhs.kind == Nk.N_EXPR_FIELD && lhs.child_count > 0)
            {
                ops[0] = b.lower_operand(lhs.children[0]);
                ops[1] = combined;
                uint id = b.emit(Op.AIR_STORE_FIELD, &ops[0], 2, n);
                if (id != pear_air::AIR_NO_VALUE) { b.m.values[id].p.name = lhs.name_id; }
                return id;
            }
            if (lhs != null && lhs.kind == Nk.N_EXPR_INDEX && lhs.child_count > 1)
            {
                ops[0] = b.lower_operand(lhs.children[0]);
                ops[1] = combined;
                ops[2] = b.lower_operand(lhs.children[1]);
                return b.emit(Op.AIR_STORE_INDEX, &ops[0], 3, n);
            }
            return combined;
        }

        case N_STMT_ASSIGN:
        case N_EXPR_ASSIGN:
        {
            if (n.child_count < 2) { break; }
            Node* lhs = n.children[0];
            uint rv = b.lower_operand(n.children[1]);

            /*
             Assigning to a LOCAL is a rebind (SSA rename). Assigning to a
             module-level binder is a real STORE to memory — rebinding it
             would make the write invisible to every other function.
            */
            if (lhs != null && lhs.kind == Nk.N_EXPR_IDENT && lhs.resolved != null)
            {
                if (is_module_level(lhs.resolved))
                {
                    uint a = b.emit(Op.AIR_GLOBAL_ADDR, &ops[0], 0, lhs);
                    if (a != pear_air::AIR_NO_VALUE)
                    {
                        b.m.values[a].p.name = lhs.resolved.name_id != 0
                                             ? lhs.resolved.name_id : lhs.name_id;
                        b.m.values[a].facts.nullness = pear_erm::Nullness.NULL_NEVER;
                        ops[0] = a; ops[1] = rv;
                        return b.emit(Op.AIR_STORE_PTR, &ops[0], 2, n);
                    }
                }
                b.write_var(lhs.resolved, b.cur_block, rv);
                return rv;
            }
            // Through a pointer, a field or an index: a real memory write.
            if (lhs != null && lhs.kind == Nk.N_EXPR_DEREF && lhs.child_count > 0)
            {
                ops[0] = b.lower_operand(lhs.children[0]);
                ops[1] = rv;
                return b.emit(Op.AIR_STORE_PTR, &ops[0], 2, n);
            }
            if (lhs != null && lhs.kind == Nk.N_EXPR_FIELD && lhs.child_count > 0)
            {
                ops[0] = b.lower_operand(lhs.children[0]);
                ops[1] = rv;
                uint id = b.emit(Op.AIR_STORE_FIELD, &ops[0], 2, n);
                if (id != pear_air::AIR_NO_VALUE) { b.m.values[id].p.name = lhs.name_id; }
                return id;
            }
            if (lhs != null && lhs.kind == Nk.N_EXPR_INDEX && lhs.child_count > 1)
            {
                ops[0] = b.lower_operand(lhs.children[0]);
                ops[1] = rv;
                ops[2] = b.lower_operand(lhs.children[1]);
                return b.emit(Op.AIR_STORE_INDEX, &ops[0], 3, n);
            }

            /*
             Any other left-hand side. Reached when the LHS is an
             arbitrary address-valued expression — in this stdlib, from a
             parenthesised cast chain (`*(((p as i64) + n) as *u8) = b`)
             that pfront folds into a binary node.

             Lower it as a STORE THROUGH THE COMPUTED ADDRESS rather than
             giving up. That is the correct semantics for every
             address-valued LHS, and it keeps the write visible to the
             memory versioning instead of vanishing into a hole — a
             dropped store is a miscompile, an imprecise one is not.
            */
            if (lhs != null)
            {
                ops[0] = b.lower_operand(lhs);
                ops[1] = rv;
                return b.emit(Op.AIR_STORE_PTR, &ops[0], 2, n);
            }
            break;
        }

        case N_STMT_EXPR:
            if (n.child_count > 0) { return b.lower_expr(n.children[0]); }
            return pear_air::AIR_NO_VALUE;

        case N_BLOCK:
            return b.lower_block(n);

        case N_DECL_FN:
        {
            /*
             A function declared inside another function's body.

             Pride has no closures over a nested `fn` (the spec has no
             lambda form and generics are monomorphised), so a nested fn is
             an ordinary top-level function that merely happens to be
             written inside another. Lower it as one, restoring the outer
             function's cursor afterwards.

             Emitting a hole here would have been the easy path and would
             have silently dropped 18 real functions from the stdlib.
            */
            uint saved_f = b.cur_func;
            uint saved_b = b.cur_block;
            bool saved_loop = b.in_loop;
            uint saved_h = b.loop_header;
            uint saved_e = b.loop_exit;

            b.lower_function(n);

            b.cur_func = saved_f;
            b.cur_block = saved_b;
            b.in_loop = saved_loop;
            b.loop_header = saved_h;
            b.loop_exit = saved_e;
            // A declaration has no value; the enclosing block continues.
            return b.emit(Op.AIR_CONST_UNIT, &ops[0], 0, n);
        }

        case N_DECL_CONST:
        case N_DECL_STATIC:
        case N_DECL_TYPE:
        case N_DECL_STRUCT:
        case N_DECL_ENUM:
        case N_DECL_UNION:
        case N_DECL_EFFECT:
        case N_DECL_NEWTYPE:
            /*
             A declaration inside a body. It contributes no runtime value
             and its contents are handled where they are USED (a const is
             folded at the reference, a type has no code), so this is a
             no-op rather than a hole.
            */
            return b.emit(Op.AIR_CONST_UNIT, &ops[0], 0, n);

        default:
            break;
    }

    if (pfront_core::is_expr(n.kind)) { return b.lower_expr(n); }

    b.unsupported = b.unsupported + 1;
    b.note_unsupported(n.kind);
    return b.emit(Op.AIR_UNKNOWN, &ops[0], 0, n);
}

// ════════════════════════════════════════════════════════════════════════
// FUNCTIONS
// ════════════════════════════════════════════════════════════════════════

/*
 Bind a pattern to an incoming parameter value.

 A tuple pattern destructures: `| (a, b) ->` binds each component to a
 field of the incoming value rather than to the value itself. Getting this
 wrong would bind both names to the whole tuple, which resolves and
 verifies but is silently wrong — the kind of failure that only shows up as
 a wrong answer at runtime.
*/
fn void Builder.bind_pattern(Builder* b, Node* pat, uint val)
{
    if (pat == null) { return; }
    switch (pat.kind)
    {
        case N_PAT_IDENT:
            b.write_var(pat, b.cur_block, val);

        case N_PAT_TUPLE:
        {
            for (usz i = 0; i < pat.child_count; i++)
            {
                uint[1] ops;
                ops[0] = val;
                uint f = b.emit(Op.AIR_LOAD_FIELD, &ops[0], 1, pat.children[i]);
                if (f != pear_air::AIR_NO_VALUE) { b.m.values[f].p.index = (uint)i; }
                b.bind_pattern(pat.children[i], f);
            }
        }

        case N_PAT_WILDCARD:
            break;

        default:
            // A literal or variant pattern is a TEST, not a binding, and
            // testing needs a match lowering that does not exist yet.
            b.unsupported = b.unsupported + 1;
    }
}

fn void Builder.lower_function(Builder* b, Node* fn_node)
{
    uint f = b.m.new_func(fn_node.name_id, fn_node.line, fn_node.col);
    if (f == pear_air::AIR_NO_FUNC) { return; }
    b.cur_func = f;
    if ((fn_node.flags & pfront_core::NF_PUB) != 0) { b.m.fun(f).is_pub = true; }

    uint entry = b.m.new_block(f, 0);
    b.m.fun(f).entry = entry;
    b.mark_sealed(entry, true);
    b.cur_block = entry;

    // Memory version 0 exists from the first instruction.
    b.m.new_mem_entry(entry, fn_node.line, fn_node.col);

    /*
     Only the FIRST clause is lowered. Multi-clause functions need pattern
     dispatch, which is a match lowering that does not exist yet; lowering
     every clause into one block would silently run them all. Counted, and
     stated plainly rather than implied to work.
    */
    Node* clause = null;
    usz clause_count = 0;
    for (usz i = 0; i < fn_node.child_count; i++)
    {
        Node* c = fn_node.children[i];
        if (c != null && c.kind == Nk.N_CLAUSE)
        {
            clause_count = clause_count + 1;
            if (clause == null) { clause = c; }
        }
    }
    if (clause_count > 1) { b.unsupported = b.unsupported + (clause_count - 1); }

    if (clause == null)
    {
        // A declaration with no body (extern, interface method).
        b.m.set_term(entry, Term.TERM_RET, pear_air::AIR_NO_VALUE);
        return;
    }

    // Parameters, then the body.
    usz body_at = clause.child_count;
    for (usz i = 0; i < clause.child_count; i++)
    {
        Node* c = clause.children[i];
        if (c == null) { continue; }
        if (pfront_core::is_pattern(c.kind))
        {
            uint[1] none;
            uint pv = b.m.new_value(entry, Op.AIR_PARAM, &none[0], 0,
                                    pear_air::AIR_NO_ORIGIN, c.line, c.col);
            if (pv != pear_air::AIR_NO_VALUE)
            {
                b.m.values[pv].p.name = c.name_id;
                b.m.add_param(f, pv);
                b.bind_pattern(c, pv);
            }
            continue;
        }
        if (body_at == clause.child_count) { body_at = i; }
    }

    uint result = pear_air::AIR_NO_VALUE;
    for (usz i = body_at; i < clause.child_count; i++)
    {
        if (!b.block_open()) { break; }
        result = b.lower_stmt(clause.children[i]);
    }

    /*
     Close every block still open. A clause body is an EXPRESSION whose
     value is the return value, so an open block returns it; blocks left
     open by a construct that never joined return unit. verify.c3 rejects
     any reachable open block, so this must be total.
    */
    if (b.block_open())
    {
        b.m.set_term(b.cur_block, Term.TERM_RET, result);
    }
    pear_air::AirFunc* af = b.m.fun(f);
    for (usz i = 0; i < af.block_count; i++)
    {
        pear_air::AirBlock* blk = b.m.blk(af.blocks[i]);
        if (blk != null && blk.term == Term.TERM_OPEN)
        {
            b.m.set_term(blk.id, Term.TERM_RET, pear_air::AIR_NO_VALUE);
        }
        b.seal_block(af.blocks[i]);
    }
}

// ════════════════════════════════════════════════════════════════════════
// ENTRY POINT
// ════════════════════════════════════════════════════════════════════════

struct BuildStats
{
    usz functions;
    usz blocks;
    usz values;
    usz unsupported;
    usz phis_created;
    usz phis_removed;
    usz sigmas;
    usz pis;
    usz[256] miss_kind;
    usz      miss_undef_read;
}

/*
 Lower a whole program AST into an AIR module.

 Walks only top-level function declarations. Types, effects, interfaces and
 module headers carry no executable code and are skipped — a1's job is the
 executable form, and layout metadata belongs to a4.
*/
fn void build_module(Air* m, Node* program, pfront_core::Interner* it, BuildStats* st)
{
    st.functions = 0; st.blocks = 0; st.values = 0; st.unsupported = 0;
    st.phis_created = 0; st.phis_removed = 0; st.sigmas = 0; st.pis = 0;
    if (program == null) { return; }

    Builder b;
    b.init(m, it);

    walk_decls(&b, program, st);

    st.unsupported = b.unsupported;
    st.phis_created = b.phis_created;
    st.phis_removed = b.phis_removed;
    st.sigmas = b.sigmas;
    st.pis = b.pis;
    for (usz i = 0; i < 256; i++) { st.miss_kind[i] = b.miss_kind[i]; }
    st.miss_undef_read = b.miss_undef_read;
    st.blocks = m.block_count > 0 ? m.block_count - 1 : 0;
    st.values = m.value_count > 0 ? m.value_count - 1 : 0;
    b.destroy();
}

fn void walk_decls(Builder* b, Node* n, BuildStats* st)
{
    if (n == null) { return; }
    if (n.kind == Nk.N_DECL_FN)
    {
        b.lower_function(n);
        st.functions = st.functions + 1;
        return;
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        walk_decls(b, n.children[i], st);
    }
}

fn void print_build_stats(BuildStats* s)
{
    printf("  functions        : %d\n", (int)s.functions);
    printf("  blocks / values  : %d / %d\n", (int)s.blocks, (int)s.values);
    printf("  phi created/removed: %d / %d\n",
           (int)s.phis_created, (int)s.phis_removed);
    printf("  sigma / pi       : %d / %d\n", (int)s.sigmas, (int)s.pis);
    printf("  unsupported      : %d\n", (int)s.unsupported);
}

/*
 Per-construct breakdown of what did NOT lower.

 Kept behind a flag rather than deleted: one aggregate number cannot tell
 you whether the gap is one missing construct or fifty, and the answer
 drives what to build next. This is what showed N_EXPR_METHOD alone was
 3,123 of 8,935 -- a single construct worth 35% of the gap.
*/
fn void print_miss_histogram(BuildStats* s)
{
    if (s.miss_undef_read > 0)
    {
        printf("    miss undef-read : %d\n", (int)s.miss_undef_read);
    }
    for (usz i = 0; i < 256; i++)
    {
        if (s.miss_kind[i] > 0)
        {
            printf("    miss kind %d : %d\n", (int)i, (int)s.miss_kind[i]);
        }
    }
}
