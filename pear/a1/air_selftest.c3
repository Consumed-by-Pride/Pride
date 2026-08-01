/*
 a1 self-test driver.

 Runs the round-trip property (PEAR.md D3 / testing table row 1) and the
 verifier (row 2) against both programmatically-built modules and
 hand-written .air fixtures.

 Usage:
   pear_a1_test                 run the built-in suite
   pear_a1_test <file.air>...   parse, verify and re-print each file

 Exit code: 0 all passed, 1 something failed. The harness in
 pear_tests/run.sh reads the printed PASS/FAIL lines, not just the code, so
 a silent early exit cannot masquerade as success.
*/

module pear_a1_test;

import pear_air;
import pear_air_print;
import pear_air_parse;
import pear_verify;
import pear_infer;
import pear_erm;
import pfront_core;

alias Air  = pear_air::AirModule;
alias Op   = pear_air::AirOp;
alias Term = pear_air::AirTerm;
alias Fact = pear_air::AirFact;
alias BOp  = pear_air::AirBinOp;

extern fn int    printf(char* fmt, ...);
extern fn void*  malloc(usz size);
extern fn void   free(void* p);
extern fn void*  fopen(char* path, char* mode);
extern fn usz    fread(void* buf, usz esize, usz n, void* f);
extern fn int    fclose(void* f);
extern fn int    fflush(void* f);


/*
 C3 caps a stack object at 64 KB and `Interner` is ~1.4 MB, so every test
 context is heap-allocated. Bundling the three together keeps each test
 body to one alloc and one free, and makes it impossible to free the arena
 while the interner still points into it.
*/
struct Ctx
{
    pfront_core::Arena     arena;
    pfront_core::Interner  interner;
    Air                    mod;
}

fn Ctx* ctx_new()
{
    Ctx* c = (Ctx*)malloc(Ctx::size);
    if (c == null) { return null; }
    c.arena.init();
    c.interner.init(&c.arena);
    c.mod.init(&c.arena, &c.interner, c.interner.intern("t", 1));
    return c;
}

fn void ctx_free(Ctx* c)
{
    if (c == null) { return; }
    c.mod.destroy();
    c.arena.destroy();
    free((void*)c);
}

alias Builder = fn void(Air*, pfront_core::Interner*);

int g_pass = 0;
int g_fail = 0;

fn void ok(bool cond, char* what)
{
    if (cond) { g_pass = g_pass + 1; printf("  PASS  %s\n", what); }
    else      { g_fail = g_fail + 1; printf("  FAIL  %s\n", what); }
}

// ════════════════════════════════════════════════════════════════════════
// FIXTURE BUILDERS
// ════════════════════════════════════════════════════════════════════════

/*
 A straight-line function:

   func straight entry=b1
     %1 = const.int ival=2
     %2 = const.int ival=40
     %3 = bin %1 %2 op=add
     ret %3

 Exercises: constants, a binary op, a return with a value.
*/
fn void build_straight(Air* m, pfront_core::Interner* it)
{
    uint fname = it.intern("straight", 8);
    uint f = m.new_func(fname, 1, 1);
    uint b = m.new_block(f, 0);
    m.fun(f).entry = b;

    uint[2] ops;
    uint c1 = m.new_value(b, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 1, 1);
    m.val(c1).p.ival = 2;
    uint c2 = m.new_value(b, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 2, 1);
    m.val(c2).p.ival = 40;

    ops[0] = c1; ops[1] = c2;
    uint add = m.new_value(b, Op.AIR_BIN, &ops[0], 2, pear_air::AIR_NO_ORIGIN, 3, 1);
    m.val(add).p.op = BOp.ABO_ADD;

    m.set_term(b, Term.TERM_RET, add);
}

/*
 A diamond with a φ at the join, and σ splits on the condition's operand —
 the shape that makes this SSI rather than SSA.

   func diamond entry=entry
     entry:  %1 = param name=n
             %2 = const.int ival=0
             %3 = bin %1 %2 op=gt
             %4 = sigma %1 fact=gt     ; the then-edge name
             %5 = sigma %1 fact=le     ; the else-edge name
             branch %3 then else
     then:   %6 = const.int ival=1
             jump join
     else:   %7 = const.int ival=2
             jump join
     join:   %8 = phi %6@then %7@else
             ret %8

 Exercises: params, σ on both edges, a two-operand φ with labels, branch,
 multiple predecessors.
*/
fn void build_diamond(Air* m, pfront_core::Interner* it)
{
    uint fname = it.intern("diamond", 7);
    uint f = m.new_func(fname, 10, 1);

    uint b_entry = m.new_block(f, it.intern("entry", 5));
    uint b_then  = m.new_block(f, it.intern("then", 4));
    uint b_else  = m.new_block(f, it.intern("else_", 5));
    uint b_join  = m.new_block(f, it.intern("join", 4));
    m.fun(f).entry = b_entry;

    uint[4] ops;
    uint[4] incs;

    uint prm = m.new_value(b_entry, Op.AIR_PARAM, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 10, 1);
    m.val(prm).p.name = it.intern("n", 1);
    m.add_param(f, prm);

    uint zero = m.new_value(b_entry, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 11, 1);
    m.val(zero).p.ival = 0;

    ops[0] = prm; ops[1] = zero;
    uint cmp = m.new_value(b_entry, Op.AIR_BIN, &ops[0], 2, pear_air::AIR_NO_ORIGIN, 11, 1);
    m.val(cmp).p.op = BOp.ABO_GT;

    // The e of e-SSI: one σ per outgoing edge, each carrying that edge's fact.
    m.new_sigma(b_entry, prm, Fact.FACT_GT, 11, 1);
    m.new_sigma(b_entry, prm, Fact.FACT_LE, 11, 1);

    m.set_term(b_entry, Term.TERM_BRANCH, cmp);
    m.add_edge(b_entry, b_then);
    m.add_edge(b_entry, b_else);

    uint one = m.new_value(b_then, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 12, 1);
    m.val(one).p.ival = 1;
    m.set_term(b_then, Term.TERM_JUMP, pear_air::AIR_NO_VALUE);
    m.add_edge(b_then, b_join);

    uint two = m.new_value(b_else, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 13, 1);
    m.val(two).p.ival = 2;
    m.set_term(b_else, Term.TERM_JUMP, pear_air::AIR_NO_VALUE);
    m.add_edge(b_else, b_join);

    ops[0] = one;    ops[1] = two;
    incs[0] = b_then; incs[1] = b_else;
    uint phi = m.new_phi(b_join, &ops[0], &incs[0], 2, pear_air::AIR_NO_ORIGIN, 14, 1);
    m.set_term(b_join, Term.TERM_RET, phi);
}

/*
 A loop, so the φ has a genuine BACK EDGE and the reader has to resolve a
 forward reference (the φ names a value defined below it).

   func loop entry=pre
     pre:    %1 = const.int ival=0
             jump head
     head:   %2 = phi %1@pre %5@body
             %3 = const.int ival=10
             %4 = bin %2 %3 op=lt
             branch %4 body exit
     body:   %5 = bin %2 %6 op=add
             jump head
     exit:   ret %2
*/
fn void build_loop(Air* m, pfront_core::Interner* it)
{
    uint fname = it.intern("loop", 4);
    uint f = m.new_func(fname, 20, 1);

    uint b_pre  = m.new_block(f, it.intern("pre", 3));
    uint b_head = m.new_block(f, it.intern("head", 4));
    uint b_body = m.new_block(f, it.intern("body", 4));
    uint b_exit = m.new_block(f, it.intern("exit", 4));
    m.fun(f).entry = b_pre;

    uint[4] ops;
    uint[4] incs;

    uint init = m.new_value(b_pre, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 20, 1);
    m.val(init).p.ival = 0;
    m.set_term(b_pre, Term.TERM_JUMP, pear_air::AIR_NO_VALUE);
    m.add_edge(b_pre, b_head);

    // The φ is created before its second operand exists, exactly as a real
    // SSA construction would: patch it after building the body.
    ops[0] = init; ops[1] = pear_air::AIR_NO_VALUE;
    incs[0] = b_pre; incs[1] = b_body;
    uint phi = m.new_phi(b_head, &ops[0], &incs[0], 2, pear_air::AIR_NO_ORIGIN, 21, 1);

    uint lim = m.new_value(b_head, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 21, 1);
    m.val(lim).p.ival = 10;
    ops[0] = phi; ops[1] = lim;
    uint cmp = m.new_value(b_head, Op.AIR_BIN, &ops[0], 2, pear_air::AIR_NO_ORIGIN, 21, 1);
    m.val(cmp).p.op = BOp.ABO_LT;
    m.set_term(b_head, Term.TERM_BRANCH, cmp);
    m.add_edge(b_head, b_body);
    m.add_edge(b_head, b_exit);

    uint step = m.new_value(b_body, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 22, 1);
    m.val(step).p.ival = 1;
    ops[0] = phi; ops[1] = step;
    uint next = m.new_value(b_body, Op.AIR_BIN, &ops[0], 2, pear_air::AIR_NO_ORIGIN, 22, 1);
    m.val(next).p.op = BOp.ABO_ADD;
    m.set_term(b_body, Term.TERM_JUMP, pear_air::AIR_NO_VALUE);
    m.add_edge(b_body, b_head);

    // Patch the back-edge operand now that `next` exists.
    m.operands[m.val(phi).op_off + 1] = next;

    m.set_term(b_exit, Term.TERM_RET, phi);
}

/*
 A switch with a default arm, plus the three divergent terminators. These
 are the cases most likely to be got wrong in the text form, because they
 have variable arity and because a divergent block legitimately has no
 successors.
*/
fn void build_switch(Air* m, pfront_core::Interner* it)
{
    uint fname = it.intern("sw", 2);
    uint f = m.new_func(fname, 30, 1);
    uint b0 = m.new_block(f, it.intern("head", 4));
    uint b1 = m.new_block(f, it.intern("c1", 2));
    uint b2 = m.new_block(f, it.intern("c2", 2));
    uint bd = m.new_block(f, it.intern("dflt", 4));
    m.fun(f).entry = b0;

    uint[2] ops;
    uint prm = m.new_value(b0, Op.AIR_PARAM, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 30, 1);
    m.val(prm).p.name = it.intern("x", 1);
    m.add_param(f, prm);

    m.set_term(b0, Term.TERM_SWITCH, prm);
    m.add_case(b0, 1);
    m.add_edge(b0, b1);
    m.add_case(b0, 7);
    m.add_edge(b0, b2);
    m.blk(b0).has_default = true;
    m.add_edge(b0, bd);

    uint r1 = m.new_value(b1, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 31, 1);
    m.val(r1).p.ival = 100;
    m.set_term(b1, Term.TERM_RET, r1);

    // Divergent: control never leaves.
    m.set_term(b2, Term.TERM_TRAP, pear_air::AIR_NO_VALUE);
    m.set_term(bd, Term.TERM_UNREACHABLE, pear_air::AIR_NO_VALUE);
}

/*
 Every payload-carrying opcode at least once, so the printer/parser
 attribute paths are all exercised. Without this, an opcode whose payload
 the printer forgets would round-trip "successfully" by printing nothing
 and parsing nothing.
*/
fn void build_payloads(Air* m, pfront_core::Interner* it)
{
    uint fname = it.intern("payloads", 8);
    uint f = m.new_func(fname, 40, 1);
    uint b = m.new_block(f, 0);          // deliberately anonymous
    m.fun(f).entry = b;
    m.fun(f).is_pub = true;

    uint[3] ops;

    uint ci = m.new_value(b, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 40, 1);
    m.val(ci).p.ival = -9223372036854775807;      // near INT64_MIN

    uint cf = m.new_value(b, Op.AIR_CONST_FLOAT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 40, 1);
    m.val(cf).p.fval = 0.1;                        // does NOT survive decimal round-trip

    uint cb = m.new_value(b, Op.AIR_CONST_BOOL, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 40, 1);
    m.val(cb).p.ival = 1;

    uint cs = m.new_value(b, Op.AIR_CONST_STR, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 40, 1);
    m.val(cs).p.name = it.intern("hello", 5);

    m.new_value(b, Op.AIR_CONST_NULL, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 40, 1);
    m.new_value(b, Op.AIR_CONST_UNIT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 40, 1);

    ops[0] = ci;
    uint cast = m.new_value(b, Op.AIR_CAST, &ops[0], 1, pear_air::AIR_NO_ORIGIN, 41, 1);
    m.val(cast).p.name = it.intern("u8", 2);

    uint un = m.new_value(b, Op.AIR_UN, &ops[0], 1, pear_air::AIR_NO_ORIGIN, 41, 1);
    m.val(un).p.uop = pear_air::AirUnOp.AUO_NEG;

    uint lf = m.new_value(b, Op.AIR_LOAD_FIELD, &ops[0], 1, pear_air::AIR_NO_ORIGIN, 42, 1);
    m.val(lf).p.index = 3;

    uint af = m.new_value(b, Op.AIR_ADDR_FIELD, &ops[0], 1, pear_air::AIR_NO_ORIGIN, 42, 1);
    m.val(af).p.index = 5;

    ops[0] = ci; ops[1] = cb;
    uint sf = m.new_value(b, Op.AIR_STORE_FIELD, &ops[0], 2, pear_air::AIR_NO_ORIGIN, 43, 1);
    m.val(sf).p.index = 7;

    ops[0] = ci; ops[1] = cb; ops[2] = ci;
    m.new_value(b, Op.AIR_STORE_INDEX, &ops[0], 3, pear_air::AIR_NO_ORIGIN, 43, 1);

    ops[0] = ci;
    uint cd = m.new_value(b, Op.AIR_CALL_DIRECT, &ops[0], 1, pear_air::AIR_NO_ORIGIN, 44, 1);
    m.val(cd).p.name = it.intern("printf", 6);

    uint ga = m.new_value(b, Op.AIR_GLOBAL_ADDR, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 44, 1);
    m.val(ga).p.name = it.intern("g_counter", 9);

    uint pf = m.new_value(b, Op.AIR_PERFORM, &ops[0], 1, pear_air::AIR_NO_ORIGIN, 45, 1);
    m.val(pf).p.name = it.intern("State.get", 9);

    m.new_value(b, Op.AIR_RESUME, &ops[0], 1, pear_air::AIR_NO_ORIGIN, 45, 1);

    // A σ inherits its source's origin (D1) — asserted separately below.
    m.new_sigma(b, ci, Fact.FACT_NONNULL, 46, 1);

    m.set_term(b, Term.TERM_RET, pear_air::AIR_NO_VALUE);
}

// ════════════════════════════════════════════════════════════════════════
// ROUND-TRIP HARNESS
// ════════════════════════════════════════════════════════════════════════

/*
 print -> parse -> print, and assert:
   1. the two modules are structurally equal (air_eq)
   2. the two RENDERINGS are byte-identical

 Check 2 is what catches a printer that is not deterministic and a parser
 that silently normalises something away. Check 1 is what catches a printer
 and parser that agree on a wrong shape. Neither alone is sufficient.
*/
fn bool roundtrip(Air* m, char* label)
{
    usz len1 = 0;
    char* txt1 = pear_air_print::render(m, true, &len1);
    if (txt1 == null) { printf("  FAIL  %s (render returned null)\n", label); g_fail++; return false; }

    Ctx* c2 = ctx_new();
    if (c2 == null) { printf("  FAIL  %s (oom)\n", label); g_fail++; free((void*)txt1); return false; }
    Air* m2p = &c2.mod;

    usz errs = 0;
    bool parsed = pear_air_parse::parse_into(m2p, txt1, len1, &errs);
    if (!parsed || errs > 0)
    {
        printf("  FAIL  %s (parse reported %d errors)\n", label, (int)errs);
        g_fail++;
        free((void*)txt1);
        ctx_free(c2);
        return false;
    }

    char* why = "";
    bool same = pear_air_parse::air_eq(m, m2p, &why);
    if (!same)
    {
        printf("  FAIL  %s (structural mismatch: %s)\n", label, why);
        g_fail++;
        free((void*)txt1);
        ctx_free(c2);
        return false;
    }

    usz len2 = 0;
    char* txt2 = pear_air_print::render(m2p, true, &len2);
    bool text_same = txt2 != null && len1 == len2;
    if (text_same)
    {
        for (usz i = 0; i < len1; i++)
        {
            if (txt1[i] != txt2[i]) { text_same = false; break; }
        }
    }
    if (!text_same)
    {
        printf("  FAIL  %s (text differs after reprint)\n", label);
        printf("---- first ----\n%s\n---- second ----\n%s\n", txt1, txt2);
        g_fail++;
    }
    else
    {
        printf("  PASS  %s (round-trip, %d bytes)\n", label, (int)len1);
        g_pass++;
    }

    free((void*)txt1);
    if (txt2 != null) { free((void*)txt2); }
    ctx_free(c2);
    return text_same;
}


// ════════════════════════════════════════════════════════════════════════
// NEGATIVE TESTS — the verifier must actually REJECT bad IR
// ════════════════════════════════════════════════════════════════════════

/*
 A verifier that returns "0 errors" on everything passes every positive
 test while checking nothing. Each case below builds IR that violates ONE
 stated property and asserts a non-zero error count, so the checks are
 known to fire rather than assumed to.
*/
fn void expect_rejected(char* what, Builder build)
{
    Ctx* c = ctx_new();
    if (c == null) { printf("  FAIL  %s (oom)\n", what); g_fail++; return; }
    build(&c.mod, &c.interner);
    pear_verify::Report rep;
    pear_verify::verify(&c.mod, &rep);
    if (rep.errors > 0)
    {
        printf("  PASS  reject: %s (%d errors)\n", what, (int)rep.errors);
        g_pass++;
    }
    else
    {
        printf("  FAIL  reject: %s -- verifier accepted malformed IR\n", what);
        g_fail++;
    }
    ctx_free(c);
}

// A reachable block with no terminator.
fn void bad_open_block(Air* m, pfront_core::Interner* it)
{
    uint f = m.new_func(it.intern("f", 1), 1, 1);
    uint b = m.new_block(f, 0);
    m.fun(f).entry = b;
    uint[1] ops;
    m.new_value(b, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 1, 1);
    // deliberately no set_term
}

// A phi with fewer operands than the block has predecessors.
fn void bad_phi_arity(Air* m, pfront_core::Interner* it)
{
    uint f = m.new_func(it.intern("f", 1), 1, 1);
    uint e = m.new_block(f, it.intern("e", 1));
    uint l = m.new_block(f, it.intern("l", 1));
    uint r = m.new_block(f, it.intern("r", 1));
    uint j = m.new_block(f, it.intern("j", 1));
    m.fun(f).entry = e;
    uint[2] ops;
    uint[2] incs;
    uint c0 = m.new_value(e, Op.AIR_CONST_BOOL, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 1, 1);
    m.set_term(e, Term.TERM_BRANCH, c0);
    m.add_edge(e, l); m.add_edge(e, r);
    uint a = m.new_value(l, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 2, 1);
    m.set_term(l, Term.TERM_JUMP, pear_air::AIR_NO_VALUE); m.add_edge(l, j);
    m.set_term(r, Term.TERM_JUMP, pear_air::AIR_NO_VALUE); m.add_edge(r, j);
    // j has TWO predecessors but the phi is given only ONE operand.
    ops[0] = a; incs[0] = l;
    uint phi = m.new_phi(j, &ops[0], &incs[0], 1, pear_air::AIR_NO_ORIGIN, 3, 1);
    m.set_term(j, Term.TERM_RET, phi);
}

// An operand whose definition does not dominate its use.
fn void bad_dominance(Air* m, pfront_core::Interner* it)
{
    uint f = m.new_func(it.intern("f", 1), 1, 1);
    uint e = m.new_block(f, it.intern("e", 1));
    uint l = m.new_block(f, it.intern("l", 1));
    uint r = m.new_block(f, it.intern("r", 1));
    m.fun(f).entry = e;
    uint[2] ops;
    uint c0 = m.new_value(e, Op.AIR_CONST_BOOL, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 1, 1);
    m.set_term(e, Term.TERM_BRANCH, c0);
    m.add_edge(e, l); m.add_edge(e, r);
    // Defined only on the left arm...
    uint only_left = m.new_value(l, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 2, 1);
    m.set_term(l, Term.TERM_RET, only_left);
    // ...but used on the right arm, which it does not dominate.
    ops[0] = only_left; ops[1] = only_left;
    uint use = m.new_value(r, Op.AIR_BIN, &ops[0], 2, pear_air::AIR_NO_ORIGIN, 3, 1);
    m.val(use).p.op = BOp.ABO_ADD;
    m.set_term(r, Term.TERM_RET, use);
}

// A value used before it is defined within the same block.
fn void bad_use_before_def(Air* m, pfront_core::Interner* it)
{
    uint f = m.new_func(it.intern("f", 1), 1, 1);
    uint b = m.new_block(f, 0);
    m.fun(f).entry = b;
    uint[2] ops;
    uint later = m.new_value(b, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 2, 1);
    ops[0] = later; ops[1] = later;
    uint user = m.new_value(b, Op.AIR_BIN, &ops[0], 2, pear_air::AIR_NO_ORIGIN, 3, 1);
    m.val(user).p.op = BOp.ABO_ADD;
    // Reorder the block so the use physically precedes the definition.
    pear_air::AirBlock* bb = m.blk(b);
    uint tmp = bb.values[0];
    bb.values[0] = bb.values[1];
    bb.values[1] = tmp;
    m.set_term(b, Term.TERM_RET, user);
}

// A branch whose successor count does not match its arity.
fn void bad_branch_arity(Air* m, pfront_core::Interner* it)
{
    uint f = m.new_func(it.intern("f", 1), 1, 1);
    uint e = m.new_block(f, it.intern("e", 1));
    uint t = m.new_block(f, it.intern("t", 1));
    m.fun(f).entry = e;
    uint[1] ops;
    uint c0 = m.new_value(e, Op.AIR_CONST_BOOL, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 1, 1);
    m.set_term(e, Term.TERM_BRANCH, c0);
    m.add_edge(e, t);        // only ONE successor for a two-way branch
    m.set_term(t, Term.TERM_RET, pear_air::AIR_NO_VALUE);
}

// A sigma that does not inherit its source's origin -- the D1 violation
// that would make range facts unattributable after a split.
fn void bad_sigma_origin(Air* m, pfront_core::Interner* it)
{
    uint f = m.new_func(it.intern("f", 1), 1, 1);
    uint b = m.new_block(f, 0);
    m.fun(f).entry = b;
    uint[1] ops;
    uint src = m.new_value(b, Op.AIR_PARAM, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 1, 1);
    m.add_param(f, src);
    uint s = m.new_sigma(b, src, Fact.FACT_GT, 1, 1);
    m.val(s).origin = s;                 // break D1 on purpose
    m.set_term(b, Term.TERM_RET, s);
}

// A phi placed after a non-phi value.
fn void bad_phi_position(Air* m, pfront_core::Interner* it)
{
    uint f = m.new_func(it.intern("f", 1), 1, 1);
    uint e = m.new_block(f, it.intern("e", 1));
    uint j = m.new_block(f, it.intern("j", 1));
    m.fun(f).entry = e;
    uint[1] ops;
    uint a = m.new_value(e, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 1, 1);
    m.set_term(e, Term.TERM_JUMP, pear_air::AIR_NO_VALUE);
    m.add_edge(e, j);
    // A real instruction first...
    uint junk = m.new_value(j, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 2, 1);
    // ...then a phi, which must come first.
    uint[1] incs;
    ops[0] = a; incs[0] = e;
    uint phi = m.new_phi(j, &ops[0], &incs[0], 1, pear_air::AIR_NO_ORIGIN, 3, 1);
    m.set_term(j, Term.TERM_RET, phi);
}

// ════════════════════════════════════════════════════════════════════════
// MAIN
// ════════════════════════════════════════════════════════════════════════

fn void run_case(char* name, Builder build, bool expect_verify_clean)
{
    Ctx* c = ctx_new();
    if (c == null) { printf("  FAIL  %s (oom)\n", name); g_fail++; return; }
    Air* m = &c.mod;

    build(m, &c.interner);
    // Run ERM inference BEFORE the round trip: the facts must be in the
    // printed text, or the round trip proves nothing about them.
    pear_infer::ErmStats est;
    pear_infer::run(m, &est);
    roundtrip(m, name);

    pear_verify::Report rep;
    pear_verify::verify(m, &rep);
    bool clean = rep.errors == 0;
    if (clean == expect_verify_clean)
    {
        printf("  PASS  %s (verify: %d errors, as expected)\n", name, (int)rep.errors);
        g_pass++;
    }
    else
    {
        printf("  FAIL  %s (verify: %d errors, expected %s)\n",
               name, (int)rep.errors, expect_verify_clean ? "clean" : "dirty");
        pear_verify::print_report(&rep);
        g_fail++;
    }

    ctx_free(c);
}

fn int main(String[] args)
{
    // File mode: parse, verify and print each named .air file.
    if (args.len > 1)
    {
        int rc = 0;
        for (usz ai = 1; ai < args.len; ai++)
        {
            void* fh = fopen((char*)args[ai].ptr, "rb");
            if (fh == null) { printf("cannot open %s\n", (char*)args[ai].ptr); rc = 1; continue; }
            char* buf = (char*)malloc(1 << 20);
            usz n = fread((void*)buf, 1, (1 << 20) - 1, fh);
            fclose(fh);
            buf[n] = 0;

            Ctx* c = ctx_new();
            if (c == null) { printf("oom\n"); rc = 1; free((void*)buf); continue; }
            Air* m = &c.mod;

            usz errs = 0;
            bool okp = pear_air_parse::parse_into(m, buf, n, &errs);
            printf("=== %s: parse %s (%d errors) ===\n",
                   (char*)args[ai].ptr, okp ? "ok" : "FAILED", (int)errs);

            // Seed ERM before verifying and printing, so a hand-written
            // file shows the facts a1 derives rather than only the ones
            // the author typed.
            pear_infer::ErmStats est;
            pear_infer::run(m, &est);

            pear_verify::Report rep;
            pear_verify::verify(m, &rep);
            pear_verify::print_report(&rep);
            printf("  --- ERM ---\n");
            pear_infer::print_stats(&est);
            pear_air_print::dump(m, true);

            if (!okp || rep.errors > 0) { rc = 1; }
            ctx_free(c);
            free((void*)buf);
        }
        return rc;
    }

    printf("=== pear/a1 self-test ===\n");
    run_case("straight", &build_straight, true);
    run_case("diamond",  &build_diamond,  true);
    run_case("loop",     &build_loop,     true);
    run_case("switch",   &build_switch,   true);
    run_case("payloads", &build_payloads, true);

    // The verifier must REJECT each of these. Without this block, "0
    // errors" on the positive cases would be equally consistent with a
    // verifier that checks nothing at all.
    expect_rejected("reachable block with no terminator", &bad_open_block);
    expect_rejected("phi operand count != predecessor count", &bad_phi_arity);
    expect_rejected("definition does not dominate use", &bad_dominance);
    expect_rejected("use before def in the same block", &bad_use_before_def);
    expect_rejected("branch with one successor", &bad_branch_arity);
    expect_rejected("sigma breaks origin inheritance (D1)", &bad_sigma_origin);
    expect_rejected("phi after a non-phi value", &bad_phi_position);

    // ── D1: a σ must inherit its source's origin ───────────────────────
    // If it did not, every range fact learned about a variable would be
    // lost the instant e-SSI split it, which would make the whole `R` of
    // SP-ERM-e-SSI decorative. Asserted directly rather than trusted.
    {
        Ctx* c = ctx_new();
        Air* mp = &c.mod;
        uint f = mp.new_func(c.interner.intern("f", 1), 1, 1);
        uint b = mp.new_block(f, 0);
        mp.fun(f).entry = b;
        uint[1] ops;
        uint src = mp.new_value(b, Op.AIR_PARAM, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 1, 1);
        uint s1 = mp.new_sigma(b, src, Fact.FACT_GT, 1, 1);
        uint s2 = mp.new_sigma(b, s1, Fact.FACT_NONNULL, 1, 1);
        mp.set_term(b, Term.TERM_RET, s2);
        // A chain of two σ over the same variable must still name the
        // ORIGINAL value, not the intermediate split.
        ok(mp.val(s1).origin == src && mp.val(s2).origin == src,
           "D1: sigma chain preserves the root origin");
        ok(mp.val(src).origin == src, "D1: a root value is its own origin");
        ctx_free(c);
    }

    // ── D6: overflow is reported, never silent ─────────────────────────
    // A value with more operands than any fixed cap must still be stored
    // in full. ssi_ir.c3 capped at 16 and truncated.
    {
        Ctx* c = ctx_new();
        Air* mp = &c.mod;
        uint f = mp.new_func(c.interner.intern("wide", 4), 1, 1);
        uint b = mp.new_block(f, 0);
        mp.fun(f).entry = b;
        uint[64] ops;
        uint base = mp.new_value(b, Op.AIR_CONST_INT, &ops[0], 0, pear_air::AIR_NO_ORIGIN, 1, 1);
        for (usz i = 0; i < 64; i++) { ops[i] = base; }
        uint wide = mp.new_value(b, Op.AIR_TUPLE, &ops[0], 64, pear_air::AIR_NO_ORIGIN, 1, 1);
        mp.set_term(b, Term.TERM_RET, wide);
        ok(mp.val(wide).op_count == 64 && !mp.overflowed,
           "D6: 64 operands stored without truncation (ssi_ir capped at 16)");
        ctx_free(c);
    }

    printf("---\npear/a1 self-test: pass=%d fail=%d\n", g_pass, g_fail);
    return g_fail == 0 ? 0 : 1;
}
