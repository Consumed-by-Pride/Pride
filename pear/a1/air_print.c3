/*
 AIR textual writer — one half of PEAR.md D3.

 The other half is air_parse.c3, and the contract between them is
 `parse(print(x)) == x`. Everything printed here must be re-readable there;
 anything that is only a comment must be marked so the reader can skip it.

 D3 is called "the single highest-leverage decision in the document" in
 PEAR.md, for a concrete reason: ssi_ir.c3 has a dump but no reader, so
 every backend test has to run the whole front end first. With a reader,
 a3/a4/a5 can be developed and tested against hand-written .air files
 before a1's build path is finished.

 ── Grammar produced ────────────────────────────────────────────────────
   module <name>
   func <name> [pub] entry=<label> {
     block <label> [pred=<l>,...] {
       %<id> = <opcode> [operands] [attrs]
       ...
       <terminator>
     }
   }

 A value id printed as `%7` is the module-global AirValue id, not a
 per-function counter. Keeping them global means a printed operand
 reference is unambiguous without tracking scope, and the reader can
 resolve references in one pass.
*/

module pear_air_print;

import pear_air;
import pear_erm;
import pfront_core;

alias Air   = pear_air::AirModule;
alias Val   = pear_air::AirValue;
alias Blk   = pear_air::AirBlock;
alias Fn    = pear_air::AirFunc;
alias Op    = pear_air::AirOp;
alias Term  = pear_air::AirTerm;

extern fn int printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn void* realloc(void* p, usz size);
extern fn void free(void* p);

/*
 Output sink. Printing to a growable buffer rather than straight to stdout
 is what makes the round-trip test possible in-process: print to a buffer,
 hand the buffer to the parser, compare. A stdout-only printer would force
 the test through a temporary file.
*/
struct Out
{
    char* buf;
    usz   len;
    usz   cap;
    bool  to_stdout;
    bool  oom;
}

fn void Out.init_buffer(Out* o)
{
    o.buf = null; o.len = 0; o.cap = 0; o.to_stdout = false; o.oom = false;
}

fn void Out.init_stdout(Out* o)
{
    o.buf = null; o.len = 0; o.cap = 0; o.to_stdout = true; o.oom = false;
}

fn void Out.destroy(Out* o)
{
    if (o.buf != null) { free((void*)o.buf); o.buf = null; }
    o.len = 0; o.cap = 0;
}

fn void Out.ch(Out* o, char c)
{
    if (o.to_stdout) { printf("%c", c); return; }
    if (o.len + 2 > o.cap)
    {
        usz nc = o.cap == 0 ? 256 : o.cap * 2;
        char* p = (char*)realloc((void*)o.buf, nc);
        if (p == null) { o.oom = true; return; }
        o.buf = p; o.cap = nc;
    }
    o.buf[o.len] = c;
    o.len = o.len + 1;
    o.buf[o.len] = 0;
}

fn void Out.raw(Out* o, char* s, usz n)
{
    for (usz i = 0; i < n; i++) { o.ch(s[i]); }
}

fn void Out.str(Out* o, String s)
{
    for (usz i = 0; i < s.len; i++) { o.ch(s[i]); }
}

fn void Out.cstr(Out* o, char* s)
{
    if (s == null) { return; }
    usz i = 0;
    while (s[i] != 0) { o.ch(s[i]); i = i + 1; }
}

fn void Out.num(Out* o, long v)
{
    if (v < 0) { o.ch('-'); }
    // Build digits backwards. Written out rather than using snprintf so the
    // printer has no dependency on a C format buffer size.
    char[24] tmp;
    usz n = 0;
    ulong u = v < 0 ? (ulong)(-(v + 1)) + 1 : (ulong)v;
    if (u == 0) { o.ch('0'); return; }
    while (u > 0 && n < 24) { tmp[n] = (char)('0' + (char)(u % 10)); u = u / 10; n = n + 1; }
    while (n > 0) { n = n - 1; o.ch(tmp[n]); }
}

/*
 UNSIGNED printing, not a cast through `long`.

 The cast was wrong for any value above INT64_MAX, which is routine here:
 known-bits `zeros` is the complement of the value, so the constant 2 has
 zeros = 0xFFFFFFFFFFFFFFFD and printed as `-3`. The reader then failed on
 it, which is how the round-trip test caught this — the printer alone
 looked fine. Float bit patterns have the same exposure.
*/
fn void Out.unum(Out* o, ulong v)
{
    if (v == 0) { o.ch('0'); return; }
    char[24] tmp;
    usz n = 0;
    while (v > 0 && n < 24) { tmp[n] = (char)('0' + (char)(v % 10)); v = v / 10; n = n + 1; }
    while (n > 0) { n = n - 1; o.ch(tmp[n]); }
}

// ════════════════════════════════════════════════════════════════════════
// CANONICAL NUMBERING
// ════════════════════════════════════════════════════════════════════════

/*
 Printed value ids are assigned in TRAVERSAL order (function, then block,
 then position within block), not from the internal AirValue id.

 This is what makes D3's diff property real. Internal ids reflect the
 order values happened to be CONSTRUCTED, which is an implementation
 detail: a loop header's phi is built before the body value it references,
 so it gets a lower id, while a reader that resolves the forward reference
 first assigns them the other way round. Both graphs are identical; only
 the numbering differs.

 If the text exposed that, then (a) print/parse/print would not be stable,
 and (b) every unrelated optimiser change would renumber the whole file and
 bury the real change in renumbering noise. Canonical order removes both.

 A value referenced but never defined in any block -- which a well-formed
 module should not contain, but a partially-built or hand-written one can
 -- keeps a slot so the reference still prints as a valid id rather than
 silently becoming something else.
*/
struct Numbering
{
    uint* to_print;    // internal id -> printed id
    usz   cap;
    uint  next;
}

fn void Numbering.init(Numbering* nb, usz n)
{
    nb.cap = n;
    nb.next = 1;
    nb.to_print = (uint*)malloc(n * uint::size);
    if (nb.to_print == null) { nb.cap = 0; return; }
    for (usz i = 0; i < n; i++) { nb.to_print[i] = 0; }
}

fn void Numbering.destroy(Numbering* nb)
{
    if (nb.to_print != null) { free((void*)nb.to_print); nb.to_print = null; }
    nb.cap = 0;
}

fn void Numbering.assign(Numbering* nb, uint internal_id)
{
    if ((usz)internal_id >= nb.cap) { return; }
    if (nb.to_print[internal_id] != 0) { return; }
    nb.to_print[internal_id] = nb.next;
    nb.next = nb.next + 1;
}

fn uint Numbering.get(Numbering* nb, uint internal_id)
{
    if ((usz)internal_id >= nb.cap) { return internal_id; }
    uint p = nb.to_print[internal_id];
    return p == 0 ? internal_id : p;
}

/*
 Walk the module in print order and assign every defined value a number.
 Done as a separate pass BEFORE printing so a forward reference (a loop
 header phi naming a body value) already has its number when it is printed.
*/
fn void Numbering.build(Numbering* nb, Air* m)
{
    for (usz fi = 1; fi < m.func_count; fi++)
    {
        Fn* f = m.fun((uint)fi);
        if (f == null) { continue; }
        for (usz bi = 0; bi < f.block_count; bi++)
        {
            Blk* b = m.blk(f.blocks[bi]);
            if (b == null) { continue; }
            for (usz vi = 0; vi < b.value_count; vi++)
            {
                // Skip holes here as well, so printed ids stay contiguous
                // and the numbering matches what is actually emitted.
                Val* hv = m.val(b.values[vi]);
                if (hv != null && hv.is_phi_hole) { continue; }
                nb.assign(b.values[vi]);
            }
        }
    }
    // Anything referenced but never listed in a block still needs a number,
    // or its references would print as a raw internal id and collide.
    for (usz i = 1; i < m.value_count; i++)
    {
        nb.assign((uint)i);
    }
}

// ── name printing ───────────────────────────────────────────────────────

/*
 An interned name, or a placeholder if it is unset or the interner is
 missing. Never prints nothing: an empty token would desynchronise the
 reader, which is exactly the kind of round-trip failure D3 exists to make
 impossible.
*/
/*
 Is this byte safe to emit RAW inside a name?

 Deliberately wider than air_parse.c3's `is_word`, and the difference is
 the point. Two separate questions were being conflated:

   1. which bytes can the SCANNER read back as one token, and
   2. which bytes would corrupt the STRUCTURE of the line.

 Only (2) needs escaping. A name is a whitespace-delimited field followed
 by `key=value` attributes, so the bytes that actually break parsing are
 whitespace (ends the field early), `=` (starts an attribute), `;` (starts
 a comment) and control characters. Everything else -- `~`, `/`, `"`,
 `-`, `[`, `:` -- is inert in this position.

 The first version escaped anything outside `is_word` and produced
 `name=$22a$20b$20c$22` for the string "a b c" and `$7eTree` for the
 `~Tree` sigil: correct, round-trippable, and unreadable. 1,500 escapes
 across the standard library where 80 were needed. Since the IR is meant
 to be read by a person -- that is half of why D3 exists -- an encoding
 that obscures every string literal in the program is the wrong trade.
*/
fn bool name_char_ok(char c)
{
    if (c == (char)' ' || c == (char)9 || c == (char)10 || c == (char)13)
    {
        return false;
    }
    if (c == '=' || c == ';' || c == '$') { return false; }
    // Control bytes have no business in a single-line field.
    if ((uint)c < 32u) { return false; }
    return true;
}

/*
 Print an interned name, ESCAPING anything the reader could not read back.

 Pride is untyped and permissive, and pfront will happily hand a1 a
 declaration whose name is an operator: error recovery on hostile input
 produced `func => entry=b1`. The printer emitted those bytes verbatim,
 and then the reader's `word()` -- which stops at any non-word character
 -- consumed NOTHING for the name, so the `=` of `entry=` was taken as
 the `=` of a `name=value` attribute and `entry=b1` was swallowed as the
 name's value. The function came back with no entry block, which
 verify.c3 reports as "function has no entry block", and the parse still
 claimed "0 errors".

 Nine of 508 fuzzed files hit this. It is a D3 failure of the worst kind:
 not a crash, not a diagnostic, just a silently different program on the
 far side of a round trip.

 The escape is `$xx` hex per offending byte, chosen because `$` is not in
 `is_word` so the encoding is unambiguous, and the result is still a
 single whitespace-free token. A name that is entirely unprintable still
 prints as something, so no name can ever collapse to nothing and shift
 the fields after it.
*/
fn void print_name(Out* o, Air* m, uint id)
{
    if (id == 0 || m.interner == null) { o.str("_"); return; }
    char* t = m.interner.text(id);
    usz   n = m.interner.text_len(id);
    if (t == null || n == 0) { o.str("_"); return; }

    bool clean = true;
    for (usz i = 0; i < n; i++)
    {
        if (!name_char_ok(t[i])) { clean = false; break; }
    }
    if (clean) { o.raw(t, n); return; }

    // `$` prefix marks an escaped name; each bad byte becomes $xx.
    for (usz i = 0; i < n; i++)
    {
        char c = t[i];
        if (name_char_ok(c)) { o.raw(&t[i], 1); continue; }
        char[3] esc;
        esc[0] = '$';
        esc[1] = hex_digit((int)(((uint)c >> 4) & 0xF));
        esc[2] = hex_digit((int)((uint)c & 0xF));
        o.raw(&esc[0], 3);
    }
}

fn char hex_digit(int v)
{
    if (v < 10) { return (char)('0' + v); }
    return (char)('a' + (v - 10));
}

// A block label. Named blocks print their name; anonymous ones print `b<id>`.
fn void print_label(Out* o, Air* m, uint bid)
{
    Blk* b = m.blk(bid);
    if (b == null) { o.str("b?"); return; }
    if (b.name != 0 && m.interner != null)
    {
        print_name(o, m, b.name);
        return;
    }
    o.ch('b');
    o.unum((ulong)bid);
}

// ── values ──────────────────────────────────────────────────────────────

/*
 One value, one line.

   %<id> = <mnemonic> <operands...> <attributes...>

 Attributes are `key=value` and always come after operands, so the reader
 can shift operands until it sees an `=`. Order within the attribute list
 is fixed by this function, which keeps printed output diffable across
 runs.
*/
fn void print_value(Out* o, Air* m, Numbering* nb, uint vid, bool with_origin)
{
    Val* v = m.val(vid);
    if (v == null) { return; }

    o.str("    %");
    o.unum((ulong)nb.get(v.id));
    o.str(" = ");
    o.str(pear_air::op_name(v.op));

    // Operands.
    for (usz i = 0; i < v.op_count; i++)
    {
        o.str(" %");
        o.unum((ulong)nb.get(m.operands[v.op_off + i]));
        /*
         A φ names the block each operand arrives from, inline, so the
         pairing is visible in the text and cannot be misread.

         MEM_PHI too. It was omitted here, so a memory φ printed as
         `mem.phi %30 %54` with no `@label` at all -- the incoming blocks
         simply were not in the text. Reading that back gave op_count 2
         and inc_count 0, which is exactly what verify.c3 rejects as
         "phi operand count differs from its incoming-block count": 75
         errors on io.pie alone, and 1,585 across the standard library,
         every one of them appearing only AFTER a round trip. a2 places
         the memory φ, so a1's own output never showed it and the printer
         and the verifier disagreed in a direction nothing tested.
        */
        bool any_phi_here = v.op == Op.AIR_PHI || v.op == Op.AIR_MEM_PHI;
        if (any_phi_here && i < v.inc_count)
        {
            o.str("@");
            print_label(o, m, m.phi_blocks[v.inc_off + i]);
        }
    }

    // Payload attributes, printed only when the opcode actually uses them.
    // Printing every field for every opcode would round-trip fine but would
    // make the output unreadable and the diffs noisy.
    switch (v.op)
    {
        case AIR_CONST_INT:
        case AIR_CONST_BOOL:
            o.str(" ival=");
            o.num(v.p.ival);
        case AIR_CONST_FLOAT:
            // Floats print through their exact bit pattern. A decimal
            // rendering would not round-trip: 0.1 does not survive
            // decimal -> binary -> decimal at fixed precision, and a
            // near-miss here would silently change program semantics.
            o.str(" fbits=");
            o.unum(*(ulong*)&v.p.fval);
        case AIR_CONST_STR:
        case AIR_PARAM:
        case AIR_CAST:
        case AIR_STRUCT:
        case AIR_CALL_DIRECT:
        case AIR_GLOBAL_ADDR:
        case AIR_FUNC_REF:
        case AIR_CONST_REF:
        case AIR_ASM:
        case AIR_PERFORM:
        case AIR_SIZEOF:      // names a TYPE, which a4 needs for layout
        case AIR_ALIGNOF:
        case AIR_TRANSMUTE:
            o.str(" name=");
            print_name(o, m, v.p.name);
        case AIR_VARIANT_REF:
        case AIR_OFFSETOF:      // type name plus the field slot
            o.str(" name=");
            print_name(o, m, v.p.name);
            o.str(" index=");
            o.unum((ulong)v.p.index);
        case AIR_LOAD_FIELD:
        case AIR_ADDR_FIELD:
        case AIR_STORE_FIELD:
            o.str(" index=");
            o.unum((ulong)v.p.index);
            /*
             The field NAME as well as its slot.

             build.c3 has always set p.name on a field access, and this
             printed only p.index -- so `p.x` and `p.y` were
             indistinguishable in serialised AIR, and the name was
             silently dropped on every round trip. That is a D3 violation:
             the text has to carry everything the in-memory form does, or
             a stage reading the file sees less than the stage that wrote
             it.

             It matters concretely at a4, where a struct pattern's fields
             are resolved by NAME -- `{ y, x }` is legal and its written
             order is not the declaration order, so the slot index alone
             cannot recover which field was meant.
            */
            if (v.p.name != 0)
            {
                o.str(" field=");
                print_name(o, m, v.p.name);
            }
        case AIR_BIN:
            o.str(" op=");
            o.str(pear_air::binop_name(v.p.op));
        case AIR_UN:
            o.str(" op=");
            o.str(pear_air::unop_name(v.p.uop));
        case AIR_SIGMA:
        case AIR_PI:
            // Both carry a refinement; a π that lost its fact on a round
            // trip would silently degrade to an opaque copy.
            o.str(" fact=");
            o.str(pear_air::fact_name(v.p.fact));
        default:
            break;
    }

    /*
     ERM, printed inline in brackets.

     This is what makes .air denser than .ll as a FILE, not just as an
     in-memory structure. LLVM's equivalent facts are either absent from
     the text (known-bits, MemorySSA) or attached as optional metadata a
     pass may drop (`!range`). Here they are part of the value's syntax and
     survive a round trip, so a fact established in a2 is readable at a5.

     Only non-trivial facts print; a wall of `[range=top]` on every line
     would destroy the diff property D3 exists for.
    */
    if (pear_erm::facts_known(&v.facts))
    {
        o.str("  [");
        bool first = true;

        if (!v.facts.range.is_top)
        {
            if (v.facts.range.is_bottom) { o.str("range=bottom"); }
            else
            {
                o.str("range=");
                o.num(v.facts.range.lo);
                o.str("..");
                o.num(v.facts.range.hi);
            }
            first = false;
        }
        if (v.facts.width != 0)
        {
            if (!first) { o.ch(' '); }
            o.str("w=");
            o.num((long)v.facts.width);
            first = false;
        }
        if (!pear_erm::kb_is_unknown(&v.facts.bits))
        {
            if (!first) { o.ch(' '); }
            o.str("kb=");
            o.unum(v.facts.bits.zeros);
            o.ch('/');
            o.unum(v.facts.bits.ones);
            first = false;
        }
        if (v.facts.nullness != pear_erm::Nullness.NULL_UNKNOWN)
        {
            if (!first) { o.ch(' '); }
            o.str("null=");
            o.str(v.facts.nullness.mnemonic);
            first = false;
        }
        if (v.facts.mem.kind != pear_erm::MemKind.MEM_NONE)
        {
            if (!first) { o.ch(' '); }
            o.str("mem=");
            o.str(v.facts.mem.kind.mnemonic);
            o.ch(':');
            o.unum((ulong)v.facts.mem.version);
            o.str("<-");
            o.unum((ulong)v.facts.mem.reaching);
            if (v.facts.mem.scope != pear_erm::ALIAS_UNKNOWN)
            {
                o.str(" scope=");
                o.unum((ulong)v.facts.mem.scope);
            }
            if (v.facts.mem.no_alias) { o.str(" noalias"); }
            if (v.facts.mem.volatile_) { o.str(" volatile"); }
            first = false;
        }
        if (v.facts.crosses_block)
        {
            if (!first) { o.ch(' '); }
            o.str("nonlocal");
            first = false;
        }
        if (v.facts.may_fault)
        {
            if (!first) { o.ch(' '); }
            o.str("mayfault");
            first = false;
        }
        o.ch(']');
    }

    /*
     D1. The origin is printed only when it differs from the value's own id,
     i.e. only when the value actually descends from another. Printing
     `origin=7` on value %7 would be noise on every line. The reader treats
     an absent origin as self-origin, which is the same rule new_value uses.
    */
    if (with_origin && v.origin != v.id && v.origin != pear_air::AIR_NO_ORIGIN)
    {
        o.str(" origin=%");
        o.unum((ulong)nb.get(v.origin));
    }

    o.ch('\n');
}

// ── terminators ─────────────────────────────────────────────────────────

fn void print_term(Out* o, Air* m, Numbering* nb, uint bid)
{
    Blk* b = m.blk(bid);
    if (b == null) { return; }

    o.str("    ");
    o.str(pear_air::term_name(b.term));

    switch (b.term)
    {
        case TERM_RET:
            if (b.term_value != pear_air::AIR_NO_VALUE)
            {
                o.str(" %");
                o.unum((ulong)nb.get(b.term_value));
            }
        case TERM_JUMP:
            o.ch(' ');
            if (b.succ_count > 0) { print_label(o, m, b.succ[0]); } else { o.str("b?"); }
        case TERM_BRANCH:
            o.str(" %");
            o.unum((ulong)nb.get(b.term_value));
            o.ch(' ');
            if (b.succ_count > 0) { print_label(o, m, b.succ[0]); } else { o.str("b?"); }
            o.ch(' ');
            if (b.succ_count > 1) { print_label(o, m, b.succ[1]); } else { o.str("b?"); }
        case TERM_SWITCH:
            o.str(" %");
            o.unum((ulong)nb.get(b.term_value));
            // `case <v> -> <label>` per arm, then an optional `default -> <label>`.
            for (usz i = 0; i < b.succ_count; i++)
            {
                bool is_default = b.has_default && i + 1 == b.succ_count;
                o.str(is_default ? " default->" : " case ");
                if (!is_default)
                {
                    if (i < b.case_count) { o.num(b.case_vals[i]); } else { o.num(0); }
                    o.str("->");
                }
                print_label(o, m, b.succ[i]);
            }
        default:
            break;
    }
    o.ch('\n');
}

// ── blocks and functions ────────────────────────────────────────────────

fn void print_block(Out* o, Air* m, Numbering* nb, uint bid, bool with_origin)
{
    Blk* b = m.blk(bid);
    if (b == null) { return; }

    o.str("  block ");
    print_label(o, m, bid);

    /*
     Predecessors are printed as a COMMENT-like attribute the reader
     ignores: they are derived from the successor edges, so re-reading them
     would let a hand-edited file declare an inconsistent CFG. Printing them
     is still worth it because they are what a human needs when reading a
     φ. The reader rebuilds preds from succs.
    */
    if (b.pred_count > 0)
    {
        o.str("  ; pred=");
        for (usz i = 0; i < b.pred_count; i++)
        {
            if (i > 0) { o.ch(','); }
            print_label(o, m, b.pred[i]);
        }
    }
    o.str("\n");

    for (usz i = 0; i < b.value_count; i++)
    {
        /*
         PHI HOLES ARE NOT SERIALISED.

         remove_trivial_phi neutralises a trivial φ in place and marks the
         slot, because deleting from the middle of a block invalidates
         every position other code holds DURING construction. Nothing
         references the slot afterwards.

         That constraint does not apply to the text form, and emitting the
         hole was actively harmful: `is_phi_hole` is not printable, so
         after a round trip the hole became an ordinary const.unit sitting
         between two φ and verification failed with "phi appears after a
         non-phi value". 85 of 258 stdlib modules could not survive their
         own round trip.

         That breaks D3's promise directly — a2 reading a .air file would
         see a different module than a2 reading a1's memory. Omitting the
         holes removes the concept from the serialised form entirely.
        */
        pear_air::AirValue* hv = m.val(b.values[i]);
        if (hv != null && hv.is_phi_hole) { continue; }
        print_value(o, m, nb, b.values[i], with_origin);
    }
    print_term(o, m, nb, bid);
    o.str("  end\n");
}

fn void print_func(Out* o, Air* m, Numbering* nb, uint fid, bool with_origin)
{
    Fn* f = m.fun(fid);
    if (f == null) { return; }

    o.str("func ");
    print_name(o, m, f.name);
    if (f.is_pub) { o.str(" pub"); }
    o.str(" entry=");
    print_label(o, m, f.entry);
    o.ch('\n');

    for (usz i = 0; i < f.block_count; i++)
    {
        print_block(o, m, nb, f.blocks[i], with_origin);
    }
    o.str("endfunc\n");
}

fn void print_module(Out* o, Air* m, bool with_origin)
{
    Numbering nb;
    nb.init(m.value_count);
    nb.build(m);

    o.str("module ");
    print_name(o, m, m.name);
    o.ch('\n');
    /*
     Overflow is REPORTED, never silent (D6). If a growth request failed the
     printed IR is incomplete, and a reader that silently accepted it would
     turn a resource failure into a wrong-code bug.
    */
    if (m.overflowed) { o.str("; WARNING: module overflowed, IR is incomplete\n"); }
    for (usz i = 1; i < m.func_count; i++)
    {
        print_func(o, m, &nb, (uint)i, with_origin);
    }
    nb.destroy();
}

// Convenience: render a whole module to a fresh heap buffer.
fn char* render(Air* m, bool with_origin, usz* out_len)
{
    Out o;
    o.init_buffer();
    print_module(&o, m, with_origin);
    if (out_len != null) { *out_len = o.len; }
    return o.buf;   // caller frees
}

fn void dump(Air* m, bool with_origin)
{
    Out o;
    o.init_stdout();
    print_module(&o, m, with_origin);
}
