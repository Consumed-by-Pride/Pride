/*
 AIR textual reader — the other half of PEAR.md D3.

 Contract with air_print.c3: `parse(print(x)) == x`. The round-trip test in
 pear_tests/run.sh asserts it on every fixture, and the equality used is
 structural (air_eq below), not a text comparison — comparing text would
 pass trivially and prove nothing about the datatype.

 ── Two-pass, because forward references are normal ──────────────────────
 A φ at the top of a loop header names values defined later in the loop
 body, and a `jump` names a block that has not been read yet. So:

   pass 1  create every block, record its label
   pass 2  create values and resolve every %id and label reference

 Value ids in the text are the writer's global ids. They are NOT reused
 directly as the new module's ids — the reader builds its own id space and
 keeps a text-id -> new-id map, so a hand-written file with sparse or
 out-of-order ids still loads. Trusting the text's numbering would make the
 reader reject anything a human wrote by hand, which defeats the purpose.

 ── Error handling ───────────────────────────────────────────────────────
 Parsing is total: an unrecognised line is recorded as an error with its
 line number and skipped, rather than aborting. `ok` reports whether
 anything failed. A reader that dies on the first bad line is painful to
 use against hand-written fixtures.
*/

module pear_air_parse;

import pear_air;
import pear_erm;
import pfront_core;

alias Air  = pear_air::AirModule;
alias Op   = pear_air::AirOp;
alias Term = pear_air::AirTerm;

extern fn int   printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn void* realloc(void* p, usz size);
extern fn void  free(void* p);

const usz MAX_PARSE_ERRORS = 32;

// ════════════════════════════════════════════════════════════════════════
// LABEL AND ID MAPS
// ════════════════════════════════════════════════════════════════════════

/*
 Text label -> new block id. Linear scan: an AIR function has tens of
 blocks, not thousands, and a hash table here would be more code than it
 saves. If a2 ever produces functions with block counts where this matters,
 the fix is to swap the lookup, not to have guessed early.
*/
struct LabelMap
{
    char** names;
    usz*   lens;
    uint*  ids;
    usz    count;
    usz    cap;
}

fn void LabelMap.init(LabelMap* lm)
{
    lm.names = null; lm.lens = null; lm.ids = null; lm.count = 0; lm.cap = 0;
}

fn void LabelMap.destroy(LabelMap* lm)
{
    if (lm.names != null) { free((void*)lm.names); }
    if (lm.lens != null)  { free((void*)lm.lens); }
    if (lm.ids != null)   { free((void*)lm.ids); }
    lm.names = null; lm.lens = null; lm.ids = null; lm.count = 0; lm.cap = 0;
}

fn bool LabelMap.grow(LabelMap* lm, usz need)
{
    if (need <= lm.cap) { return true; }
    usz nc = lm.cap == 0 ? 16 : lm.cap;
    while (nc < need) { nc = nc * 2; }
    char** nn = (char**)realloc((void*)lm.names, nc * (usz)8);
    if (nn == null) { return false; }
    lm.names = nn;
    usz* nl = (usz*)realloc((void*)lm.lens, nc * usz::size);
    if (nl == null) { return false; }
    lm.lens = nl;
    uint* ni = (uint*)realloc((void*)lm.ids, nc * uint::size);
    if (ni == null) { return false; }
    lm.ids = ni;
    lm.cap = nc;
    return true;
}

fn void LabelMap.put(LabelMap* lm, char* name, usz len, uint id)
{
    if (!lm.grow(lm.count + 1)) { return; }
    lm.names[lm.count] = name;
    lm.lens[lm.count] = len;
    lm.ids[lm.count] = id;
    lm.count = lm.count + 1;
}

fn uint LabelMap.get(LabelMap* lm, char* name, usz len)
{
    for (usz i = 0; i < lm.count; i++)
    {
        if (lm.lens[i] != len) { continue; }
        bool same = true;
        for (usz j = 0; j < len; j++)
        {
            if (lm.names[i][j] != name[j]) { same = false; break; }
        }
        if (same) { return lm.ids[i]; }
    }
    return pear_air::AIR_NO_BLOCK;
}

/*
 Text value id -> new value id. Indexed directly by the text id, grown on
 demand, so lookup is O(1) and a sparse file just leaves holes.
*/
struct IdMap
{
    uint* to_new;
    usz   cap;
}

fn void IdMap.init(IdMap* im) { im.to_new = null; im.cap = 0; }
fn void IdMap.destroy(IdMap* im)
{
    if (im.to_new != null) { free((void*)im.to_new); im.to_new = null; }
    im.cap = 0;
}

fn bool IdMap.ensure(IdMap* im, usz idx)
{
    if (idx < im.cap) { return true; }
    usz nc = im.cap == 0 ? 64 : im.cap;
    while (nc <= idx) { nc = nc * 2; }
    uint* p = (uint*)realloc((void*)im.to_new, nc * uint::size);
    if (p == null) { return false; }
    for (usz i = im.cap; i < nc; i++) { p[i] = pear_air::AIR_NO_VALUE; }
    im.to_new = p;
    im.cap = nc;
    return true;
}

fn void IdMap.put(IdMap* im, uint text_id, uint new_id)
{
    if (!im.ensure((usz)text_id)) { return; }
    im.to_new[text_id] = new_id;
}

fn uint IdMap.get(IdMap* im, uint text_id)
{
    if ((usz)text_id >= im.cap) { return pear_air::AIR_NO_VALUE; }
    return im.to_new[text_id];
}

// ════════════════════════════════════════════════════════════════════════
// SCANNER
// ════════════════════════════════════════════════════════════════════════

/*
 Whitespace-and-newline oriented. AIR's text form is line-based: one value
 or one terminator per line, with `;` starting a comment that runs to the
 end of the line. There is no nesting to track and no string escapes to
 handle, which is deliberate — a format that needs a real lexer needs a
 real grammar, and this one should stay small enough to read in one sitting.
*/
struct Scan
{
    char* src;
    usz   len;
    usz   pos;
    int   line;
}

fn void Scan.init(Scan* s, char* src, usz len)
{
    s.src = src; s.len = len; s.pos = 0; s.line = 1;
}

fn bool Scan.at_end(Scan* s) { return s.pos >= s.len; }
fn char Scan.cur(Scan* s)    { return s.pos < s.len ? s.src[s.pos] : (char)0; }

fn bool is_space(char c) { return c == ' ' || c == '\t' || c == '\r'; }

/*
 Characters that may appear inside a NAME token.

 `$` is here because the printer escapes any byte it cannot emit safely
 as `$xx` (see print_name in air_print.c3). Without `$` in this set the
 escape would split the name in two and the field after it would be
 misread -- which is the exact failure the escape exists to prevent.

 Must stay in lock-step with `name_char_ok` in air_print.c3.
*/
fn bool is_word(char c)
{
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
        || (c >= '0' && c <= '9') || c == '_' || c == '.' || c == '?'
        || c == '$';
}

/*
 Characters that may appear inside a NAME field specifically.

 Wider than is_word, and matched to `name_char_ok` in air_print.c3: a
 name runs to whitespace, `=` or `;`, so a `~` or a quote or a slash in
 the middle of one is unambiguous and is read verbatim. `$` introduces a
 hex escape for the handful of bytes that are not safe.

 Keeping this separate from is_word matters: is_word also governs
 keywords and attribute KEYS, where the narrow set is correct.
*/
fn bool is_name_char(char c)
{
    if (c == (char)' ' || c == (char)9 || c == (char)10 || c == (char)13)
    {
        return false;
    }
    if (c == '=' || c == ';') { return false; }
    if ((uint)c < 32u) { return false; }
    return true;
}

// Read a NAME field: everything up to whitespace, `=` or `;`.
fn usz Scan.name_word(Scan* s, char** start)
{
    s.skip_inline();
    *start = s.src + s.pos;
    usz n = 0;
    while (!s.at_end() && is_name_char(s.cur())) { s.pos = s.pos + 1; n = n + 1; }
    return n;
}

// Skip spaces and a trailing comment, but never a newline.
fn void Scan.skip_inline(Scan* s)
{
    while (!s.at_end())
    {
        char c = s.cur();
        if (is_space(c)) { s.pos = s.pos + 1; continue; }
        if (c == ';')
        {
            while (!s.at_end() && s.cur() != '\n') { s.pos = s.pos + 1; }
            continue;
        }
        break;
    }
}

fn bool Scan.at_eol(Scan* s)
{
    s.skip_inline();
    return s.at_end() || s.cur() == '\n';
}

fn void Scan.next_line(Scan* s)
{
    while (!s.at_end() && s.cur() != '\n') { s.pos = s.pos + 1; }
    if (!s.at_end()) { s.pos = s.pos + 1; s.line = s.line + 1; }
}

// Advance to the next line that has content. Returns false at end of input.
fn bool Scan.next_content_line(Scan* s)
{
    while (!s.at_end())
    {
        s.skip_inline();
        if (s.at_end()) { return false; }
        if (s.cur() == '\n') { s.pos = s.pos + 1; s.line = s.line + 1; continue; }
        return true;
    }
    return false;
}

// Read a bare word. Returns length; sets *start.
fn usz Scan.word(Scan* s, char** start)
{
    s.skip_inline();
    *start = s.src + s.pos;
    usz n = 0;
    while (!s.at_end() && is_word(s.cur())) { s.pos = s.pos + 1; n = n + 1; }
    return n;
}

fn bool Scan.eat_char(Scan* s, char c)
{
    s.skip_inline();
    if (!s.at_end() && s.cur() == c) { s.pos = s.pos + 1; return true; }
    return false;
}

// Match a keyword without consuming it unless it matches exactly.
fn bool Scan.peek_word_is(Scan* s, String kw)
{
    usz save = s.pos;
    char* w;
    usz n = s.word(&w);
    s.pos = save;
    if (n != kw.len) { return false; }
    for (usz i = 0; i < n; i++) { if (w[i] != kw[i]) { return false; } }
    return true;
}

fn bool Scan.eat_word(Scan* s, String kw)
{
    if (!s.peek_word_is(kw)) { return false; }
    char* w;
    s.word(&w);
    return true;
}

// `%<digits>`, the text form of a value reference.
fn bool Scan.value_ref(Scan* s, uint* out)
{
    s.skip_inline();
    if (s.at_end() || s.cur() != '%') { return false; }
    s.pos = s.pos + 1;
    ulong v = 0;
    bool saw = false;
    while (!s.at_end() && s.cur() >= '0' && s.cur() <= '9')
    {
        v = v * 10 + (ulong)(s.cur() - '0');
        s.pos = s.pos + 1;
        saw = true;
    }
    if (!saw) { return false; }
    *out = (uint)v;
    return true;
}

fn bool Scan.signed_int(Scan* s, long* out)
{
    s.skip_inline();
    bool neg = false;
    if (!s.at_end() && (s.cur() == '-' || s.cur() == '+'))
    {
        neg = s.cur() == '-';
        s.pos = s.pos + 1;
    }
    ulong v = 0;
    bool saw = false;
    while (!s.at_end() && s.cur() >= '0' && s.cur() <= '9')
    {
        v = v * 10 + (ulong)(s.cur() - '0');
        s.pos = s.pos + 1;
        saw = true;
    }
    if (!saw) { return false; }
    *out = neg ? -(long)v : (long)v;
    return true;
}

fn bool Scan.unsigned_int(Scan* s, ulong* out)
{
    s.skip_inline();
    ulong v = 0;
    bool saw = false;
    while (!s.at_end() && s.cur() >= '0' && s.cur() <= '9')
    {
        v = v * 10 + (ulong)(s.cur() - '0');
        s.pos = s.pos + 1;
        saw = true;
    }
    if (!saw) { return false; }
    *out = v;
    return true;
}

// ════════════════════════════════════════════════════════════════════════
// PARSER
// ════════════════════════════════════════════════════════════════════════

struct Parse
{
    Scan     sc;
    Air*     m;
    LabelMap labels;
    IdMap    ids;
    usz      errors;
    int[MAX_PARSE_ERRORS] err_lines;
    bool     ok;
}

fn void Parse.err(Parse* p, char* what)
{
    if (p.errors < MAX_PARSE_ERRORS) { p.err_lines[p.errors] = p.sc.line; }
    p.errors = p.errors + 1;
    p.ok = false;
    printf("air_parse: line %d: %s\n", p.sc.line, what);
}

fn int hex_val(char c)
{
    if (c >= '0' && c <= '9') { return (int)(c - '0'); }
    if (c >= 'a' && c <= 'f') { return 10 + (int)(c - 'a'); }
    if (c >= 'A' && c <= 'F') { return 10 + (int)(c - 'A'); }
    return -1;
}

/*
 Intern a name read from the text, DECODING the printer's `$xx` escapes.

 The printer escapes any byte that is not a legal name character, because
 a raw `=` or `"` or space in a name breaks the field structure of the
 line (see print_name). Decoding here, at the single point where every
 name the reader stores passes through, is what makes the escape a
 TRANSPORT encoding rather than a change to the name itself.

 Without the decode the escape is not idempotent and that is worse than
 the bug it fixes: `"a b c"` printed as `$22a$20b$20c$22`, which read
 back as the literal 18-character name `$22a$20b$20c$22` and then
 re-printed as `$2422a$2420b$2420c$2422`, growing on every pass. D3 asks
 for print/parse to be the identity, not merely to survive.

 A malformed escape -- `$` not followed by two hex digits -- is kept
 verbatim. It cannot come from this printer, and silently dropping bytes
 from a name a human wrote by hand would be its own small betrayal.
*/
fn uint Parse.intern(Parse* p, char* s, usz n)
{
    if (p.m.interner == null || n == 0) { return 0; }
    // `_` is the writer's placeholder for "no name"; map it back to 0 so a
    // round trip does not turn an absent name into a literal underscore.
    if (n == 1 && s[0] == '_') { return 0; }

    bool has_esc = false;
    for (usz i = 0; i < n; i++) { if (s[i] == '$') { has_esc = true; break; } }
    if (!has_esc) { return p.m.interner.intern(s, n); }

    char* buf = (char*)malloc(n + 1);
    if (buf == null) { return p.m.interner.intern(s, n); }
    usz w = 0;
    usz i2 = 0;
    while (i2 < n)
    {
        if (s[i2] == '$' && i2 + 2 < n)
        {
            int hi = hex_val(s[i2 + 1]);
            int lo = hex_val(s[i2 + 2]);
            if (hi >= 0 && lo >= 0)
            {
                buf[w] = (char)((hi << 4) | lo);
                w = w + 1;
                i2 = i2 + 3;
                continue;
            }
        }
        buf[w] = s[i2];
        w = w + 1;
        i2 = i2 + 1;
    }
    uint id = w == 0 ? 0 : p.m.interner.intern(buf, w);
    free((void*)buf);
    return id;
}

/*
 Resolve a text value id to a new one, creating a placeholder if the value
 has not been seen yet.

 Forward references are legitimate: a loop-header φ names values defined in
 the body below it. Rather than a separate patch list, an unseen id gets a
 placeholder AIR_UNKNOWN value now, and the real definition OVERWRITES that
 same slot when it is read. That keeps every operand a valid id at all
 times, so the module is never transiently malformed.
*/
fn uint Parse.resolve_value(Parse* p, uint text_id)
{
    uint got = p.ids.get(text_id);
    if (got != pear_air::AIR_NO_VALUE) { return got; }
    uint[1] none;
    uint nid = p.m.new_value(pear_air::AIR_NO_BLOCK, Op.AIR_UNKNOWN,
                             &none[0], 0, pear_air::AIR_NO_ORIGIN, 0, 0);
    p.ids.put(text_id, nid);
    return nid;
}

// ── pass 1: collect block labels ────────────────────────────────────────

/*
 Walk the whole text creating a block per `block <label>` line, so that
 pass 2 can resolve any forward jump. Functions are created here too, since
 a block belongs to one.
*/
fn void Parse.pass1(Parse* p)
{
    p.sc.pos = 0;
    p.sc.line = 1;
    uint cur_func = pear_air::AIR_NO_FUNC;

    while (p.sc.next_content_line() || !p.sc.at_end())
    {
        if (p.sc.at_end()) { break; }

        if (p.sc.eat_word("module"))
        {
            char* w; usz n = p.sc.name_word(&w);
            p.m.name = p.intern(w, n);
            p.sc.next_line();
            continue;
        }

        if (p.sc.eat_word("func"))
        {
            // name_word, not word: a function name comes straight from
            // Pride source and error recovery can make it an operator.
            // `func => entry=b1` read the name as EMPTY with word(), then
            // took the `=` of `entry=` as an attribute separator and
            // swallowed `entry=b1` as its value -- the function came back
            // with no entry block and the parse still said "0 errors".
            char* w; usz n = p.sc.name_word(&w);
            uint nm = p.intern(w, n);
            cur_func = p.m.new_func(nm, p.sc.line, 1);
            // `pub` and `entry=` are read in pass 2, once labels exist.
            p.sc.next_line();
            continue;
        }

        if (p.sc.eat_word("block"))
        {
            char* w; usz n = p.sc.word(&w);
            uint bid = p.m.new_block(cur_func, 0);
            /*
             A label that is literally `b<digits>` is the writer's ANONYMOUS
             form, so it must not become a real name — otherwise a
             round trip turns every anonymous block into a named one and the
             second print differs from the first.
            */
            bool anon = n >= 2 && w[0] == 'b';
            if (anon)
            {
                for (usz i = 1; i < n; i++)
                {
                    if (w[i] < '0' || w[i] > '9') { anon = false; break; }
                }
            }
            if (!anon)
            {
                pear_air::AirBlock* b = p.m.blk(bid);
                if (b != null) { b.name = p.intern(w, n); }
            }
            p.labels.put(w, n, bid);
            p.sc.next_line();
            continue;
        }

        p.sc.next_line();
    }
}

// ── pass 2: values, terminators, edges ──────────────────────────────────

/*
 Read the `[range=.. w=.. kb=../.. null=.. mem=..:n<-m ...]` bracket the
 printer emits. Without this the ERM facts would print but not survive a
 round trip, which would make them decorative in exactly the way D1 warns
 about.
*/
fn void Parse.parse_facts(Parse* p, uint vid)
{
    if (!p.sc.eat_char('[')) { return; }
    pear_air::AirValue* v = p.m.val(vid);
    if (v == null) { return; }

    while (!p.sc.at_eol())
    {
        if (p.sc.eat_char(']')) { return; }

        usz save = p.sc.pos;
        char* k; usz kn = p.sc.word(&k);
        if (kn == 0) { p.sc.pos = save; break; }

        if (pear_air::str_eq_n(k, kn, "nonlocal"))
        {
            p.m.val(vid).facts.crosses_block = true;
            continue;
        }
        if (pear_air::str_eq_n(k, kn, "mayfault"))
        {
            p.m.val(vid).facts.may_fault = true;
            continue;
        }
        if (pear_air::str_eq_n(k, kn, "noalias"))
        {
            p.m.val(vid).facts.mem.no_alias = true;
            continue;
        }
        if (pear_air::str_eq_n(k, kn, "volatile"))
        {
            p.m.val(vid).facts.mem.volatile_ = true;
            continue;
        }

        if (!p.sc.eat_char('=')) { p.sc.pos = save; break; }

        if (pear_air::str_eq_n(k, kn, "range"))
        {
            if (p.sc.peek_word_is("bottom"))
            {
                char* w; p.sc.word(&w);
                p.m.val(vid).facts.range = pear_erm::r_bottom();
            }
            else
            {
                long lo; long hi;
                if (!p.sc.signed_int(&lo)) { p.err("bad range lo"); break; }
                if (!p.sc.eat_char('.') || !p.sc.eat_char('.'))
                {
                    p.err("expected '..' in range"); break;
                }
                if (!p.sc.signed_int(&hi)) { p.err("bad range hi"); break; }
                p.m.val(vid).facts.range = pear_erm::r_range(lo, hi);
            }
        }
        else if (pear_air::str_eq_n(k, kn, "w"))
        {
            long w;
            if (p.sc.signed_int(&w)) { p.m.val(vid).facts.width = (int)w; }
            else { p.err("bad width"); }
        }
        else if (pear_air::str_eq_n(k, kn, "kb"))
        {
            ulong z; ulong on;
            if (!p.sc.unsigned_int(&z)) { p.err("bad known-bits zeros"); break; }
            if (!p.sc.eat_char('/')) { p.err("expected '/' in kb"); break; }
            if (!p.sc.unsigned_int(&on)) { p.err("bad known-bits ones"); break; }
            p.m.val(vid).facts.bits.zeros = z;
            p.m.val(vid).facts.bits.ones = on;
        }
        else if (pear_air::str_eq_n(k, kn, "null"))
        {
            char* w; usz n = p.sc.word(&w);
            bool got = false;
            foreach (nn : pear_erm::Nullness::values)
            {
                if (pear_air::str_eq_n(w, n, nn.mnemonic))
                {
                    p.m.val(vid).facts.nullness = nn;
                    got = true;
                    break;
                }
            }
            if (!got) { p.err("unknown nullness"); }
        }
        else if (pear_air::str_eq_n(k, kn, "mem"))
        {
            char* w; usz n = p.sc.word(&w);
            bool got = false;
            foreach (mk : pear_erm::MemKind::values)
            {
                if (pear_air::str_eq_n(w, n, mk.mnemonic))
                {
                    p.m.val(vid).facts.mem.kind = mk;
                    got = true;
                    break;
                }
            }
            if (!got) { p.err("unknown memory kind"); }
            if (p.sc.eat_char(':'))
            {
                ulong ver;
                if (p.sc.unsigned_int(&ver)) { p.m.val(vid).facts.mem.version = (uint)ver; }
                if (p.sc.eat_char('<') && p.sc.eat_char('-'))
                {
                    ulong re;
                    if (p.sc.unsigned_int(&re)) { p.m.val(vid).facts.mem.reaching = (uint)re; }
                }
            }
        }
        else if (pear_air::str_eq_n(k, kn, "scope"))
        {
            ulong sc;
            if (p.sc.unsigned_int(&sc)) { p.m.val(vid).facts.mem.scope = (uint)sc; }
            else { p.err("bad alias scope"); }
        }
        else
        {
            p.err("unknown fact");
            char* w; p.sc.word(&w);
        }
    }
    p.sc.eat_char(']');
}

fn void Parse.parse_attrs(Parse* p, uint vid)
{
    pear_air::AirValue* v = p.m.val(vid);
    if (v == null) { return; }

    while (!p.sc.at_eol())
    {
        usz save = p.sc.pos;
        char* k; usz kn = p.sc.word(&k);
        if (kn == 0) { p.sc.pos = save; break; }
        if (!p.sc.eat_char('='))
        {
            // Not an attribute; leave it for the caller.
            p.sc.pos = save;
            break;
        }

        if (pear_air::str_eq_n(k, kn, "ival"))
        {
            long iv;
            if (p.sc.signed_int(&iv)) { p.m.val(vid).p.ival = iv; }
            else { p.err("bad ival"); }
        }
        else if (pear_air::str_eq_n(k, kn, "fbits"))
        {
            ulong bits;
            if (p.sc.unsigned_int(&bits))
            {
                // Reconstruct the double from its exact bit pattern.
                p.m.val(vid).p.fval = *(double*)&bits;
            }
            else { p.err("bad fbits"); }
        }
        else if (pear_air::str_eq_n(k, kn, "name"))
        {
            char* w; usz n = p.sc.name_word(&w);
            p.m.val(vid).p.name = p.intern(w, n);
        }
        else if (pear_air::str_eq_n(k, kn, "index"))
        {
            ulong ix;
            if (p.sc.unsigned_int(&ix)) { p.m.val(vid).p.index = (uint)ix; }
            else { p.err("bad index"); }
        }
        else if (pear_air::str_eq_n(k, kn, "field"))
        {
            // The field NAME on a load/store/addr of a struct field. See
            // the note in air_print.c3: printing only the slot index lost
            // it on every round trip.
            char* w; usz n = p.sc.name_word(&w);
            p.m.val(vid).p.name = p.intern(w, n);
        }
        else if (pear_air::str_eq_n(k, kn, "op"))
        {
            char* w; usz n = p.sc.word(&w);
            bool ok1 = false;
            // `op=` is a binary operator on AIR_BIN and a unary one on
            // AIR_UN. The opcode has already been read, so there is no
            // ambiguity — this is the one place the two share a key name.
            if (p.m.val(vid).op == Op.AIR_UN)
            {
                pear_air::AirUnOp u = pear_air::unop_from_name(w, n, &ok1);
                if (ok1) { p.m.val(vid).p.uop = u; }
            }
            else
            {
                pear_air::AirBinOp b = pear_air::binop_from_name(w, n, &ok1);
                if (ok1) { p.m.val(vid).p.op = b; }
            }
            if (!ok1) { p.err("unknown operator"); }
        }
        else if (pear_air::str_eq_n(k, kn, "fact"))
        {
            char* w; usz n = p.sc.word(&w);
            bool ok1 = false;
            pear_air::AirFact f = pear_air::fact_from_name(w, n, &ok1);
            if (ok1) { p.m.val(vid).p.fact = f; } else { p.err("unknown fact"); }
        }
        else if (pear_air::str_eq_n(k, kn, "origin"))
        {
            uint oref;
            if (p.sc.value_ref(&oref))
            {
                p.m.val(vid).origin = p.resolve_value(oref);
            }
            else { p.err("bad origin"); }
        }
        else
        {
            p.err("unknown attribute");
            // Consume the value so the scanner stays in sync.
            char* w; p.sc.word(&w);
        }
    }
}

fn void Parse.parse_value_line(Parse* p, uint block)
{
    uint text_id;
    if (!p.sc.value_ref(&text_id)) { p.err("expected %id"); p.sc.next_line(); return; }
    if (!p.sc.eat_char('=')) { p.err("expected '='"); p.sc.next_line(); return; }

    char* w; usz n = p.sc.word(&w);
    bool ok1 = false;
    Op op = pear_air::op_from_name(w, n, &ok1);
    if (!ok1) { p.err("unknown opcode"); }

    /*
     Operands, plus the `@label` suffix a φ uses.

     GROWABLE. These were `uint[64]` with an explicit "operand list
     exceeds reader capacity" error, which is honest but still refuses
     the input -- and D3 says every IR must be printable AND re-readable.
     Once a1 stopped capping phi operands at 64 it began EMITTING
     81-operand phis that its own reader rejected, and a2 could not load
     the file at all. A printer and a parser that disagree about the
     maximum arity make the round-trip property untestable exactly where
     it matters most.
    */
    uint* ops = null;
    uint* incs = null;
    usz ocap = 0;
    usz nops = 0;
    // MEM_PHI carries `@label` suffixes exactly like a value φ; the
    // printer emits them for both, so the reader must accept both.
    bool is_phi = op == Op.AIR_PHI || op == Op.AIR_MEM_PHI;

    while (!p.sc.at_eol())
    {
        usz save = p.sc.pos;
        uint r;
        if (!p.sc.value_ref(&r)) { p.sc.pos = save; break; }
        if (nops == ocap)
        {
            usz nc = ocap == 0 ? 16 : ocap * 2;
            uint* o2 = (uint*)realloc((void*)ops, nc * uint::size);
            uint* i2 = (uint*)realloc((void*)incs, nc * uint::size);
            if (o2 != null) { ops = o2; }
            if (i2 != null) { incs = i2; }
            if (o2 == null || i2 == null)
            {
                p.err("out of memory reading operand list");
                break;
            }
            ocap = nc;
        }
        ops[nops] = p.resolve_value(r);
        incs[nops] = pear_air::AIR_NO_BLOCK;
        if (is_phi && p.sc.eat_char('@'))
        {
            char* lw; usz ln = p.sc.word(&lw);
            incs[nops] = p.labels.get(lw, ln);
            if (incs[nops] == pear_air::AIR_NO_BLOCK) { p.err("unknown phi label"); }
        }
        nops = nops + 1;
    }

    /*
     Reuse the placeholder slot if this id was forward-referenced, so every
     operand that already points at it stays valid. Otherwise create fresh.
    */
    uint existing = p.ids.get(text_id);
    uint vid;
    if (existing != pear_air::AIR_NO_VALUE)
    {
        vid = existing;
        pear_air::AirValue* v = p.m.val(vid);
        usz off = nops == 0 ? 0 : p.m.push_operands(&ops[0], nops);
        v = p.m.val(vid);              // push_operands may realloc
        v.op = op;
        v.block = block;
        v.op_off = off;
        v.op_count = nops;
        v.origin = vid;
        pear_air::AirBlock* b = p.m.blk(block);
        if (b != null)
        {
            if (pear_air::grow_u32(&b.values, &b.value_cap, b.value_count + 1))
            {
                b.values[b.value_count] = vid;
                b.value_count = b.value_count + 1;
            }
            else { p.m.overflowed = true; }
        }
    }
    else
    {
        uint[1] empty;
        vid = p.m.new_value(block, op, nops == 0 ? &empty[0] : &ops[0], nops,
                            pear_air::AIR_NO_ORIGIN, p.sc.line, 1);
        p.ids.put(text_id, vid);
    }

    if (is_phi && nops > 0)
    {
        usz ioff = p.m.push_phi_blocks(&incs[0], nops);
        pear_air::AirValue* v = p.m.val(vid);
        v.inc_off = ioff;
        v.inc_count = nops;
    }

    if (ops != null)  { free((void*)ops); }
    if (incs != null) { free((void*)incs); }

    p.parse_attrs(vid);
    p.parse_facts(vid);
    p.parse_attrs(vid);   // `origin=` may follow the fact bracket
    p.sc.next_line();
}

fn uint Parse.read_label(Parse* p)
{
    char* w; usz n = p.sc.word(&w);
    uint id = p.labels.get(w, n);
    if (id == pear_air::AIR_NO_BLOCK) { p.err("unknown label"); }
    return id;
}

fn void Parse.parse_term_line(Parse* p, uint block, Term t)
{
    switch (t)
    {
        case TERM_RET:
        {
            uint r;
            if (p.sc.value_ref(&r))
            {
                p.m.set_term(block, t, p.resolve_value(r));
            }
            else
            {
                p.m.set_term(block, t, pear_air::AIR_NO_VALUE);
            }
        }
        case TERM_JUMP:
        {
            uint tgt = p.read_label();
            p.m.set_term(block, t, pear_air::AIR_NO_VALUE);
            if (tgt != pear_air::AIR_NO_BLOCK) { p.m.add_edge(block, tgt); }
        }
        case TERM_BRANCH:
        {
            uint c;
            if (!p.sc.value_ref(&c)) { p.err("branch needs a condition"); break; }
            uint tt = p.read_label();
            uint ff = p.read_label();
            p.m.set_term(block, t, p.resolve_value(c));
            if (tt != pear_air::AIR_NO_BLOCK) { p.m.add_edge(block, tt); }
            if (ff != pear_air::AIR_NO_BLOCK) { p.m.add_edge(block, ff); }
        }
        case TERM_SWITCH:
        {
            uint c;
            if (!p.sc.value_ref(&c)) { p.err("switch needs a scrutinee"); break; }
            p.m.set_term(block, t, p.resolve_value(c));
            while (!p.sc.at_eol())
            {
                if (p.sc.eat_word("case"))
                {
                    long cv;
                    if (!p.sc.signed_int(&cv)) { p.err("bad case value"); break; }
                    if (!p.sc.eat_char('-') || !p.sc.eat_char('>'))
                    {
                        p.err("expected '->' after case value");
                        break;
                    }
                    uint tgt = p.read_label();
                    p.m.add_case(block, cv);
                    if (tgt != pear_air::AIR_NO_BLOCK) { p.m.add_edge(block, tgt); }
                    continue;
                }
                if (p.sc.eat_word("default"))
                {
                    if (!p.sc.eat_char('-') || !p.sc.eat_char('>'))
                    {
                        p.err("expected '->' after default");
                        break;
                    }
                    uint tgt = p.read_label();
                    pear_air::AirBlock* b = p.m.blk(block);
                    if (b != null) { b.has_default = true; }
                    if (tgt != pear_air::AIR_NO_BLOCK) { p.m.add_edge(block, tgt); }
                    continue;
                }
                break;
            }
        }
        default:
            p.m.set_term(block, t, pear_air::AIR_NO_VALUE);
    }
    p.sc.next_line();
}

fn void Parse.pass2(Parse* p)
{
    p.sc.pos = 0;
    p.sc.line = 1;
    uint cur_func = pear_air::AIR_NO_FUNC;
    uint cur_block = pear_air::AIR_NO_BLOCK;
    uint func_seq = 0;
    uint block_seq = 0;

    while (!p.sc.at_end())
    {
        if (!p.sc.next_content_line()) { break; }

        if (p.sc.eat_word("module")) { p.sc.next_line(); continue; }

        if (p.sc.eat_word("endfunc"))
        {
            cur_func = pear_air::AIR_NO_FUNC;
            p.sc.next_line();
            continue;
        }

        if (p.sc.eat_word("end"))
        {
            cur_block = pear_air::AIR_NO_BLOCK;
            p.sc.next_line();
            continue;
        }

        if (p.sc.eat_word("func"))
        {
            // Pass 1 created these in order, so walking the same order pairs
            // each header with the function it made.
            func_seq = func_seq + 1;
            cur_func = func_seq;
            char* w; p.sc.name_word(&w); // name, already interned in pass 1
            pear_air::AirFunc* f = p.m.fun(cur_func);
            while (!p.sc.at_eol())
            {
                if (p.sc.eat_word("pub")) { if (f != null) { f.is_pub = true; } continue; }
                usz save = p.sc.pos;
                char* k; usz kn = p.sc.word(&k);
                if (kn > 0 && p.sc.eat_char('='))
                {
                    if (pear_air::str_eq_n(k, kn, "entry"))
                    {
                        uint e = p.read_label();
                        if (f != null) { f.entry = e; }
                        continue;
                    }
                    char* dummy; p.sc.word(&dummy);
                    continue;
                }
                p.sc.pos = save;
                break;
            }
            p.sc.next_line();
            continue;
        }

        if (p.sc.eat_word("block"))
        {
            block_seq = block_seq + 1;
            cur_block = block_seq;
            p.sc.next_line();
            continue;
        }

        // A value line starts with `%`.
        p.sc.skip_inline();
        if (!p.sc.at_end() && p.sc.cur() == '%')
        {
            if (cur_block == pear_air::AIR_NO_BLOCK)
            {
                p.err("value outside a block");
                p.sc.next_line();
                continue;
            }
            p.parse_value_line(cur_block);
            continue;
        }

        // Otherwise it must be a terminator.
        usz save = p.sc.pos;
        char* w; usz n = p.sc.word(&w);
        bool ok1 = false;
        Term t = pear_air::term_from_name(w, n, &ok1);
        if (ok1 && cur_block != pear_air::AIR_NO_BLOCK)
        {
            p.parse_term_line(cur_block, t);
            continue;
        }
        p.sc.pos = save;
        p.err("unrecognised line");
        p.sc.next_line();
    }
}

/*
 Parse `src` into `m`, which must already be initialised. Returns true when
 nothing failed.

 The module keeps its own id numbering; text ids are a naming convention in
 the file, not a contract about internal layout.
*/
fn bool parse_into(Air* m, char* src, usz len, usz* out_errors)
{
    Parse p;
    p.sc.init(src, len);
    p.m = m;
    p.labels.init();
    p.ids.init();
    p.errors = 0;
    p.ok = true;

    p.pass1();
    p.pass2();
    p.rebuild_params();

    if (out_errors != null) { *out_errors = p.errors; }
    p.labels.destroy();
    p.ids.destroy();
    return p.ok;
}

/*
 Rebuild each function's PARAMETER LIST from the values just read.

 The list was never reconstructed at all. a1 builds it with add_param
 while lowering, but nothing wrote it to the text and nothing rebuilt it
 on the way back in, so `param_count` was 1 before a round trip and 0
 after -- measured directly, not inferred. Everything downstream of a
 round trip therefore saw functions with no arity:

   * every parameter check in verify.c3 iterates `f.param_count` and so
     became silently INERT the moment the IR had been re-read. The whole
     block was dead code on any file loaded from disk, which is every
     file a2 has ever seen;
   * a2's DCE treats AIR_PARAM as a root because a parameter is part of
     the interface -- but with the list empty, nothing could check that
     it had honoured it. Injecting a bug that let DCE delete parameters
     removed a live argument from a two-argument function and the entire
     74-test suite stayed green;
   * a3 would inherit functions whose arity is unknown, which is not a
     recoverable position for a CPS conversion.

 Rebuilding from the ORDER of AIR_PARAM values in the entry block, rather
 than adding an arity to the header, is deliberate: the parameters are
 already in the text as values, so a separate count in the header would
 be a second source of truth that can disagree with the first. This
 derives the list from the values that are actually there.

 Order is the entry block's value order, which is the order a1 emitted
 them in, so the list round-trips identically rather than merely having
 the right length.
*/
fn void Parse.rebuild_params(Parse* p)
{
    for (usz fi = 1; fi < p.m.func_count; fi++)
    {
        pear_air::AirFunc* f = p.m.fun((uint)fi);
        if (f == null) { continue; }
        if (f.param_count != 0) { continue; }   // already known
        /*
         Scan EVERY block, not just the entry.

         Scanning only the entry block looks right -- SSI property 1 says
         a parameter is defined at CFG entry -- but it makes the verifier
         unable to report the violation: a parameter placed in some other
         block simply would not be found, param_count would stay 0, and
         the check that exists to catch exactly that would iterate zero
         times. The fixture bad_param_detached.air was ACCEPTED for this
         reason.

         Collecting them wherever they are, and letting verify.c3 judge
         whether the placement is legal, keeps the reader honest and the
         rule enforceable. Entry-block parameters still come first and in
         order, so a well-formed module round-trips unchanged.
        */
        pear_air::AirBlock* e = p.m.blk(f.entry);
        if (e != null)
        {
            for (usz i = 0; i < e.value_count; i++)
            {
                pear_air::AirValue* v = p.m.val(e.values[i]);
                if (v == null || v.is_phi_hole) { continue; }
                if (v.op != pear_air::AirOp.AIR_PARAM) { continue; }
                p.m.add_param(f.id, v.id);
            }
        }
        for (usz bi = 0; bi < f.block_count; bi++)
        {
            if (f.blocks[bi] == f.entry) { continue; }
            pear_air::AirBlock* b2 = p.m.blk(f.blocks[bi]);
            if (b2 == null) { continue; }
            for (usz i = 0; i < b2.value_count; i++)
            {
                pear_air::AirValue* v = p.m.val(b2.values[i]);
                if (v == null || v.is_phi_hole) { continue; }
                if (v.op != pear_air::AirOp.AIR_PARAM) { continue; }
                p.m.add_param(f.id, v.id);
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════
// STRUCTURAL EQUALITY — what the round-trip test actually asserts
// ════════════════════════════════════════════════════════════════════════

/*
 Compare two modules by SHAPE, not by text and not by id.

 Comparing rendered text would make the round-trip test tautological: it
 would pass whenever the printer is deterministic, whether or not the
 parser understood anything. Comparing ids would fail spuriously, since
 the reader assigns its own.

 So: same function count, same block structure per function, same opcode
 and operand shape per value, with operand references compared by POSITION
 in the traversal rather than by id.
*/
fn bool air_eq(Air* a, Air* b, char** why)
{
    if (a.func_count != b.func_count) { *why = "function count"; return false; }

    for (usz fi = 1; fi < a.func_count; fi++)
    {
        pear_air::AirFunc* fa = a.fun((uint)fi);
        pear_air::AirFunc* fb = b.fun((uint)fi);
        if (fa == null || fb == null) { *why = "missing function"; return false; }
        if (fa.block_count != fb.block_count) { *why = "block count"; return false; }
        if (fa.is_pub != fb.is_pub) { *why = "pub flag"; return false; }

        for (usz bi = 0; bi < fa.block_count; bi++)
        {
            pear_air::AirBlock* ba = a.blk(fa.blocks[bi]);
            pear_air::AirBlock* bb = b.blk(fb.blocks[bi]);
            if (ba == null || bb == null) { *why = "missing block"; return false; }
            if (ba.value_count != bb.value_count) { *why = "value count"; return false; }
            if (ba.term != bb.term) { *why = "terminator kind"; return false; }
            if (ba.succ_count != bb.succ_count) { *why = "successor count"; return false; }
            if (ba.case_count != bb.case_count) { *why = "case count"; return false; }
            if (ba.has_default != bb.has_default) { *why = "default arm"; return false; }
            for (usz ci = 0; ci < ba.case_count; ci++)
            {
                if (ba.case_vals[ci] != bb.case_vals[ci]) { *why = "case value"; return false; }
            }

            for (usz vi = 0; vi < ba.value_count; vi++)
            {
                pear_air::AirValue* va = a.val(ba.values[vi]);
                pear_air::AirValue* vb = b.val(bb.values[vi]);
                if (va == null || vb == null) { *why = "missing value"; return false; }
                if (va.op != vb.op)             { *why = "opcode"; return false; }
                if (va.op_count != vb.op_count) { *why = "operand count"; return false; }
                if (va.inc_count != vb.inc_count) { *why = "phi incoming count"; return false; }
                if (va.p.ival != vb.p.ival)     { *why = "ival"; return false; }
                if (va.p.index != vb.p.index)   { *why = "index"; return false; }
                /*
                 Compare the field name by PRESENCE, not by id: the two
                 modules have separate interners, so the same text has
                 different ids in each. A name that vanished on the round
                 trip shows up as one side being 0.
                */
                if ((va.p.name == 0) != (vb.p.name == 0))
                {
                    *why = "field name presence"; return false;
                }
                if (va.p.op != vb.p.op)         { *why = "binop"; return false; }
                if (va.p.uop != vb.p.uop)       { *why = "unop"; return false; }
                if (va.p.fact != vb.p.fact)     { *why = "fact"; return false; }
                // Float compared by bits: NaN != NaN would otherwise make a
                // round trip of a NaN constant report a false difference.
                if (*(ulong*)&va.p.fval != *(ulong*)&vb.p.fval)
                {
                    *why = "fval"; return false;
                }
                // Names compared by TEXT, since the two modules may use
                // different interners with different id numbering.
                if ((va.p.name == 0) != (vb.p.name == 0)) { *why = "name presence"; return false; }
                if (va.p.name != 0 && a.interner != null && b.interner != null)
                {
                    char* ta = a.interner.text(va.p.name);
                    usz   na = a.interner.text_len(va.p.name);
                    char* tb = b.interner.text(vb.p.name);
                    usz   nb = b.interner.text_len(vb.p.name);
                    if (na != nb) { *why = "name length"; return false; }
                    for (usz k = 0; k < na; k++)
                    {
                        if (ta[k] != tb[k]) { *why = "name text"; return false; }
                    }
                }
                /*
                 D1: origin is compared as a RELATION — "is this value its
                 own origin?" — rather than as a raw id, because the two
                 modules number values differently. A value that descends
                 from another must still descend from another after a round
                 trip, or fact attribution has been lost in the text form.
                */
                bool self_a = va.origin == va.id;
                bool self_b = vb.origin == vb.id;
                if (self_a != self_b) { *why = "origin self-reference"; return false; }

                /*
                 ERM must survive the round trip too. Without comparing
                 these, a printer that emitted facts and a parser that
                 ignored them would still "round-trip successfully" — the
                 exact failure mode D1 exists to prevent.
                */
                if (!pear_erm::r_eq(va.facts.range, vb.facts.range))
                {
                    *why = "range"; return false;
                }
                if (va.facts.bits.zeros != vb.facts.bits.zeros
                 || va.facts.bits.ones  != vb.facts.bits.ones)
                {
                    *why = "known bits"; return false;
                }
                if (va.facts.nullness != vb.facts.nullness) { *why = "nullness"; return false; }
                if (va.facts.width != vb.facts.width)       { *why = "width"; return false; }
                if (va.facts.mem.kind != vb.facts.mem.kind) { *why = "memory kind"; return false; }
                if (va.facts.mem.version != vb.facts.mem.version)
                {
                    *why = "memory version"; return false;
                }
                if (va.facts.mem.reaching != vb.facts.mem.reaching)
                {
                    *why = "reaching memory version"; return false;
                }
                if (va.facts.mem.scope != vb.facts.mem.scope) { *why = "alias scope"; return false; }
                if (va.facts.mem.no_alias != vb.facts.mem.no_alias) { *why = "noalias"; return false; }
                if (va.facts.crosses_block != vb.facts.crosses_block)
                {
                    *why = "SP classification"; return false;
                }
                if (va.facts.may_fault != vb.facts.may_fault) { *why = "may-fault"; return false; }
            }
        }
    }
    *why = "";
    return true;
}
