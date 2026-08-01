// ============================================================================
// pfront_parse.c3 — Pride front-end: recursive-descent parser (part 2)
// ----------------------------------------------------------------------------
// Consumes pfront_lex::Token stream, produces pfront_core::PNode trees.
//
// Structure of this file:
//   1.  Parser state, token ring, error recovery
//   2.  Layout handling (INDENT / DEDENT / NEWLINE)
//   3.  Types            — parse_type and friends
//   4.  Patterns         — parse_pattern
//   5.  Expressions      — Pratt parser with a real precedence table
//   6.  Statements       — blocks, control flow
//   7.  Declarations     — fn/struct/enum/effect/impl/use/mod
//   8.  Program driver
//
// Two things this parser does that the old one did not:
//   * It interns every identifier as it is created, so the resolver never
//     does string comparison.
//   * It records `use` declarations as first-class nodes with a resolved
//     module path, so the module loader can walk them without re-parsing.
// ============================================================================

module pfront_parse;

import pfront_lex;
import pfront_core;

alias Tk   = pfront_lex::TokenType;
alias Tok  = pfront_lex::Token;
alias Node = pfront_core::PNode;
alias Nk   = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn int printf(char* fmt, ...);

const int MAX_DEPTH = 400;
const usz LA_SIZE   = 12;
// Depth of the synthesised-token pushback stack. Two is the most any
// construct needs (`type V = struct` reorders name and keyword).
const usz PUSHBACK_MAX = 4;

// `p.aux` marker on an N_PAT_IDENT that the parser could not distinguish from
// a nullary enum variant (a bare uppercase name: `| M -> ...` vs `| Red ->`).
// The resolver promotes it back to N_PAT_VARIANT when the name resolves to a
// variant, and binds it otherwise. See parse_pattern_atom's TOKEN_TYPEVAR arm.
const int PAT_MAYBE_VARIANT = 7;

// `p.aux` marker on an N_EXPR_ARRAY built from the REPEAT form `[v; n]`.
// Children are [value, count] rather than a list of elements, so any pass
// that walks array literals must check this before treating child_count as
// the element count.
const int ARRAY_REPEAT = 8;

// ── Parser ──────────────────────────────────────────────────────────────────
struct Parser
{
    pfront_lex::Lexer*        lx;
    Arena*               arena;
    pfront_core::Interner*  interner;
    pfront_core::DiagBag*   diags;
    pfront_core::Module*    module_ctx;
    char*                filename;

    Tok[LA_SIZE]  ring;
    usz           ring_fill;

    int   depth;
    bool  panicking;
    bool  depth_reported;

    // `|` is ambiguous: type-union in a signature vs. clause head. Set while
    // parsing a function signature so parse_type stops at a clause boundary.
    bool  in_fn_sig;
    // Struct literals `Name { ... }` are ambiguous with `if cond { }`. Suppress
    // them while parsing a control-flow condition.
    bool  no_struct_lit;

    // INDENTs absorbed by line-continuation. Each one has a matching DEDENT
    // that must be dropped when the continued expression finishes, otherwise
    // the enclosing block sees a spurious close.
    int   cont_indents;

    // DEDENTs an indented block declined to consume because an `else` followed.
    // parse_if settles exactly its own, so a conditional nested in an
    // initializer never steals the enclosing block's close.
    int   deferred_dedents;

    // Indent of the statement currently being parsed, and of the block opened
    // by a `let ... =` initializer (0 when none). Together these bound how far
    // an inline conditional may close layout levels.
    int   stmt_indent;
    int   init_block_level;

    // Set when a line continuation consumed the layout that would otherwise
    // have introduced the following block. See settle_continuation.
    bool  implicit_block;

    // One-slot pushback buffer, for splitting `>>` at a generic close.
    // See Parser.push_back: without it the ring silently drops a real
    // token when a synthesised one is inserted.
    Tok[PUSHBACK_MAX] pending;
    usz   pending_count;

    // Source line of the most recently consumed token. A layout block always
    // begins on a line AFTER the construct that introduces it, so this is how
    // an inline body (`else 3i64`) is told apart from a lexer-folded block.
    int   prev_line;
}

fn void Parser.init(Parser* p, pfront_lex::Lexer* lx, Arena* a,
                    pfront_core::Interner* it, pfront_core::DiagBag* d,
                    pfront_core::Module* mod, char* filename)
{
    p.lx = lx;
    p.arena = a;
    p.interner = it;
    p.diags = d;
    p.module_ctx = mod;
    p.filename = filename;
    p.ring_fill = 0;
    p.depth = 0;
    p.panicking = false;
    p.depth_reported = false;
    p.in_fn_sig = false;
    p.no_struct_lit = false;
    p.cont_indents = 0;
    p.deferred_dedents = 0;
    p.stmt_indent = 0;
    p.init_block_level = 0;
    p.implicit_block = false;
    p.prev_line = 0;
    p.pending_count = 0;
    p.fill();
}

fn void Parser.fill(Parser* p)
{
    while (p.ring_fill < LA_SIZE)
    {
        p.ring[p.ring_fill] = p.lx.next();
        p.ring_fill = p.ring_fill + 1;
    }
}

fn Tok Parser.cur(Parser* p)  { return p.ring[0]; }
fn Tok Parser.peek(Parser* p, usz n)
{
    if (n >= LA_SIZE) { n = LA_SIZE - 1; }
    return p.ring[n];
}

fn Tk Parser.ct(Parser* p) { return p.ring[0].type; }

fn Tok Parser.advance(Parser* p)
{
    Tok t = p.ring[0];
    // Layout tokens carry the line of the token that FOLLOWS them, so they
    // would defeat the same-line test in parse_block_or_expr. Only real
    // tokens update the watermark.
    if (t.type != Tk.TOKEN_NEWLINE && t.type != Tk.TOKEN_INDENT
        && t.type != Tk.TOKEN_DEDENT)
    {
        p.prev_line = t.line;
    }
    for (usz i = 0; i + 1 < LA_SIZE; i++) { p.ring[i] = p.ring[i + 1]; }
    p.ring[LA_SIZE - 1] = p.next_raw();
    return t;
}

fn bool Parser.check(Parser* p, Tk t) { return p.ring[0].type == t; }

fn bool Parser.at_end(Parser* p) { return p.ring[0].type == Tk.TOKEN_EOF; }

fn bool Parser.accept(Parser* p, Tk t)
{
    if (p.ring[0].type == t) { p.advance(); return true; }
    return false;
}

fn void Parser.err(Parser* p, int code, char* msg)
{
    if (p.panicking) { return; }
    Tok c = p.cur();
    p.diags.error(pfront_core::Phase.PH_PARSE, code, c.line, c.col, msg, p.filename);
    p.panicking = true;
}

fn void Parser.err_hint(Parser* p, int code, char* msg, char* hint)
{
    if (p.panicking) { return; }
    Tok c = p.cur();
    p.diags.error_hint(pfront_core::Phase.PH_PARSE, code, c.line, c.col, msg, hint, p.filename);
    p.panicking = true;
}

fn void Parser.err_at(Parser* p, int code, int line, int col, char* msg)
{
    if (p.panicking) { return; }
    p.diags.error(pfront_core::Phase.PH_PARSE, code, line, col, msg, p.filename);
    p.panicking = true;
}

/*
 Close a generic argument list, splitting a `>>` token when necessary.

 `Foo<Bar<T>>` lexes the trailing `>>` as ONE right-shift token, so the
 inner list found no `>` and reported "expected '>' to close generic type
 arguments". Writing `Foo<Bar<T> >` worked, which is the classic C++
 problem and the same fix C++11 adopted.

 Rather than re-lexing (the parser has a token ring buffer with no
 position index and cannot rewind), the `>>` is CONSUMED and replaced in
 place by a single `>`: the inner list takes the first half, and the outer
 list finds the remaining `>` where it expects it. `>>=` gets the same
 treatment, leaving `>=`.
*/
fn bool Parser.expect_generic_close(Parser* p)
{
    if (p.check(Tk.TOKEN_GT)) { p.advance(); return true; }

    if (p.check(Tk.TOKEN_RSHIFT))
    {
        Tok sh = p.cur();
        p.advance();
        // Put back the second `>`, positioned one column further along so
        // diagnostics still point at the right character.
        Tok rest = sh;
        rest.type = Tk.TOKEN_GT;
        rest.len = 1;
        rest.col = sh.col + 1;
        p.push_back(rest);
        return true;
    }
    if (p.check(Tk.TOKEN_RSHIFTEQ))
    {
        Tok sh = p.cur();
        p.advance();
        Tok rest = sh;
        rest.type = Tk.TOKEN_GTEQ;
        rest.len = 2;
        rest.col = sh.col + 1;
        p.push_back(rest);
        return true;
    }
    p.err(1010, "expected '>' to close generic type arguments");
    return false;
}

/*
 Push a synthesised token onto the front of the lookahead ring.

 Used only to split a `>>` into two `>` when closing nested generics.

 The obvious implementation — shift every slot right and drop the last —
 is WRONG and was the first thing I tried: the ring is full of tokens the
 lexer has already produced, so the dropped slot loses a real token. It
 worked for `A<B<T>>` and silently lost the `type` keyword that began the
 next declaration in `A<B<C<A<T>>>>`, which then parsed as a continuation
 of the previous one.

 Instead the displaced token goes into a one-slot PENDING buffer that
 `refill` consults before asking the lexer. Nothing is discarded, and the
 ring stays exactly as deep as it was.
*/
fn void Parser.push_back(Parser* p, Tok t)
{
    /*
     The token about to fall off the end is PRESERVED, not dropped.

     A small stack rather than one slot: `type V = struct` needs two
     consecutive pushes (the name, then the keyword back on top of it) to
     reorder the ring into the shape parse_struct_decl expects. A
     single-slot buffer rejected the second push and left the ring
     scrambled.
    */
    if (p.pending_count >= PUSHBACK_MAX)
    {
        p.err(1010, "internal: token pushback overflow");
        return;
    }
    p.pending[p.pending_count] = p.ring[LA_SIZE - 1];
    p.pending_count = p.pending_count + 1;
    for (usz i = LA_SIZE - 1; i > 0; i--) { p.ring[i] = p.ring[i - 1]; }
    p.ring[0] = t;
}

// The next token for the ring: the pending one if there is one, else the
// lexer's. Keeps push_back lossless.
fn Tok Parser.next_raw(Parser* p)
{
    if (p.pending_count > 0)
    {
        p.pending_count = p.pending_count - 1;
        return p.pending[p.pending_count];
    }
    return p.lx.next();
}

fn bool Parser.expect(Parser* p, Tk t, int code, char* msg)
{
    if (p.ring[0].type == t) { p.advance(); return true; }
    p.err(code, msg);
    return false;
}

// Error recovery: skip to something that plausibly starts a new statement or
// declaration, so one syntax error does not cascade into fifty.
fn void Parser.sync(Parser* p)
{
    p.panicking = false;
    while (!p.at_end())
    {
        switch (p.ct())
        {
            case TOKEN_NEWLINE:
            case TOKEN_DEDENT:
            case TOKEN_SEMI:
                p.advance();
                return;
            case TOKEN_KW_FN:
            case TOKEN_KW_LET:
            case TOKEN_KW_CONST:
            case TOKEN_KW_STATIC:
            case TOKEN_KW_TYPE:
            case TOKEN_KW_STRUCT:
            case TOKEN_KW_UNION:
            case TOKEN_KW_ENUM:
            case TOKEN_KW_EFFECT:
            case TOKEN_KW_INTERFACE:
            case TOKEN_KW_IMPL:
            case TOKEN_KW_USE:
            case TOKEN_KW_MOD:
            case TOKEN_KW_NEWTYPE:
            case TOKEN_KW_RETURN:
            case TOKEN_KW_IF:
            case TOKEN_KW_WHILE:
            case TOKEN_KW_FOR:
            case TOKEN_KW_MATCH:
                return;
            default:
                p.advance();
        }
    }
}

fn bool Parser.enter(Parser* p)
{
    p.depth = p.depth + 1;
    if (p.depth > MAX_DEPTH)
    {
        if (!p.depth_reported)
        {
            Tok c = p.cur();
            p.diags.error(pfront_core::Phase.PH_PARSE, 1001, c.line, c.col,
                          "expression nests too deeply", p.filename);
            p.depth_reported = true;
        }
        return false;
    }
    return true;
}

fn void Parser.leave(Parser* p) { p.depth = p.depth - 1; }

// ── Node helpers ────────────────────────────────────────────────────────────
fn Node* Parser.mk(Parser* p, Nk k, int line, int col)
{
    Node* n = p.arena.node(k, line, col);
    if (n != null) { n.owner = p.module_ctx; }
    return n;
}

fn Node* Parser.mk_at(Parser* p, Nk k, Tok t)
{
    Node* n = p.arena.node(k, t.line, t.col);
    if (n != null)
    {
        n.owner = p.module_ctx;
        n.span_start = (uint)0;
        n.span_end = (uint)t.len;
    }
    return n;
}

fn void Parser.add(Parser* p, Node* parent, Node* child)
{
    p.arena.add_child(parent, child);
}

fn Node* Parser.mk_error(Parser* p, Tok t)
{
    Node* n = p.mk_at(Nk.N_INVALID, t);
    if (n != null) { n.flags = n.flags | pfront_core::NF_ERROR; }
    return n;
}

fn uint Parser.intern_tok(Parser* p, Tok t)
{
    return p.interner.intern(t.start, t.len);
}

// ── Layout helpers ──────────────────────────────────────────────────────────
// The lexer emits NEWLINE / INDENT / DEDENT and suppresses them inside
// brackets. These helpers keep that handling in one place.
fn void Parser.skip_newlines(Parser* p)
{
    while (p.check(Tk.TOKEN_NEWLINE)) { p.advance(); }
}

fn void Parser.skip_layout(Parser* p)
{
    while (p.check(Tk.TOKEN_NEWLINE) || p.check(Tk.TOKEN_INDENT) || p.check(Tk.TOKEN_DEDENT))
    {
        p.advance();
    }
}

fn void Parser.end_stmt(Parser* p)
{
    // A trailing binary operator makes the lexer open an INDENT for the
    // continuation line:
    //
    //     h = (a << 1) +          <- INDENT opens here
    //         (b << 7)            <- DEDENT closes it before the next stmt
    //     h                       <- but the enclosing block never sees a
    //                                DEDENT of its own
    //
    // skip_continuation_layout counted that INDENT into `cont_indents`.
    // Closing it here — at the one place every statement ends — keeps the
    // layout stack balanced. Without it the DEDENT was mistaken for the end
    // of the enclosing block, so the statement AFTER the continuation was
    // ejected from the function and reported as an unresolved name.
    //
    // parse_if and parse_while already did this via settle_continuation for
    // their conditions; a plain assignment had no equivalent.
    while (p.cont_indents > 0 && p.check(Tk.TOKEN_DEDENT))
    {
        p.advance();
        p.cont_indents = p.cont_indents - 1;
    }
    if (p.cont_indents > 0 && !p.check(Tk.TOKEN_DEDENT)) { p.cont_indents = 0; }

    if (p.accept(Tk.TOKEN_SEMI)) { p.skip_newlines(); return; }
    while (p.check(Tk.TOKEN_NEWLINE)) { p.advance(); }
}

fn bool Parser.at_block_end(Parser* p)
{
    return p.at_end() || p.check(Tk.TOKEN_DEDENT) || p.check(Tk.TOKEN_RBRACE);
}

// After a binary operator that ended a line, the operand lives on the next
// physical line. Consume NEWLINE/INDENT so the operand parses normally.
//
// DEDENT is deliberately NOT consumed: it closes the enclosing block, and
// eating it would splice the following statement into the sub-expression.
// (`let a = x ||\n  x` followed by `a` — swallowing the DEDENT moved `a`
// out of the clause body and made it unresolvable.) An INDENT opened purely
// by a continuation is balanced by the matching DEDENT, which the block
// parser tolerates as an extra.
fn void Parser.skip_continuation_layout(Parser* p)
{
    int budget = 0;
    int opened = 0;
    while (budget < 8)
    {
        Tk t = p.ct();
        if (t == Tk.TOKEN_NEWLINE) { p.advance(); budget = budget + 1; continue; }
        if (t == Tk.TOKEN_INDENT)
        {
            p.advance();
            budget = budget + 1;
            opened = opened + 1;
            continue;
        }
        break;
    }
    p.cont_indents = p.cont_indents + opened;
}

// Drop DEDENTs that merely close INDENTs absorbed by line continuation.
// A wrapped condition such as
//     if (a) ||
//        (b)
//       body
// makes the lexer open a level for the continuation line; its DEDENT arrives
// just before `body` and would otherwise be mistaken for the end of the
// enclosing block, so the body parsed as "expected an expression".
fn void Parser.settle_continuation(Parser* p)
{
    // A continuation line indented to the SAME column the body will use makes
    // the lexer reuse that level: the DEDENT closes the continuation and no
    // INDENT is emitted for the body. Record that so parse_block_or_expr
    // reads a layout block anyway instead of failing on the bare statement.
    while (p.cont_indents > 0 && p.check(Tk.TOKEN_DEDENT))
    {
        p.advance();
        p.cont_indents = p.cont_indents - 1;
        p.implicit_block = true;
    }
    if (p.cont_indents > 0 && !p.check(Tk.TOKEN_DEDENT)) { p.cont_indents = 0; }

    // The wrapped-condition case, where the lexer REALIGNED its indent stack
    // to the continuation line instead of opening a fresh level:
    //     if (a) ||
    //        (b)
    //       body
    // No INDENT is ever emitted for `body`; a single DEDENT closes the
    // continuation. Recognise it structurally: a DEDENT followed by a
    // statement deeper than the statement that owns this construct.
    if (p.check(Tk.TOKEN_DEDENT))
    {
        // The lexer emits DEDENT then NEWLINE then the statement, so looking
        // only at peek(1) saw the NEWLINE and the guard never fired. Skip the
        // layout run to reach the token that actually starts the body.
        //
        // Verified against the real token stream for
        //     if x <= 1 &&
        //        x >= 2 &&
        //        x == hi
        //       x = x & 4
        // which lexes as: ... IDENT(hi) DEDENT NEWLINE IDENT(x) '=' ...
        // Only the NEWLINE separates the DEDENT from the body, so peek past
        // it — looking at peek(1) alone saw the NEWLINE and never fired.
        Tok after = p.peek(1);
        if (after.type == Tk.TOKEN_NEWLINE) { after = p.peek(2); }

        // The DEDENT closes the continuation level, NOT the enclosing block,
        // exactly when the statement that follows is still indented deeper
        // than the construct that owns it. Consume just that one DEDENT and
        // leave the NEWLINE: the block reader needs it, and the block's real
        // closing DEDENT arrives later and must reach the enclosing parser.
        if (tok_starts_stmt(after.type) && after.col - 1 > p.stmt_indent)
        {
            p.advance();
            p.implicit_block = true;
            // The lexer opened ONE level for the continuation and closes it
            // with this DEDENT. But the enclosing block also opened a level
            // and is still waiting for its own DEDENT — and the lexer will
            // not emit a second one, because it realigned rather than
            // nesting. Record the debt so parse_virtual_block knows the
            // DEDENT it eventually meets belongs to the enclosing block and
            // must be left alone. Without this the virtual block ate it and
            // the construct's next sibling was reparented out of the
            // function entirely.
            p.deferred_dedents = p.deferred_dedents + 1;
        }
    }
    // NOTE: implicit_block is deliberately NOT cleared here. It is consumed by
    // parse_block_or_expr, which may run several tokens later.
}

// Decide whether the `|` under the cursor introduces a new clause/match arm
// or is an infix bitwise-or.
//
// An arm head has the shape `| <pattern> ->` (optionally `| <pattern> if g ->`).
// Scanning for the arrow is the reliable signal; a bitwise-or's right operand
// will not produce a top-level arrow inside the lookahead window.
//
// Two cheap structural cues decide most cases without deep scanning:
//   * `|` at the start of a physical line is overwhelmingly an arm head.
//   * `|` followed by an uppercase constructor and then `(` or `->` is an arm.
fn bool Parser.pipe_starts_arm(Parser* p)
{
    Tk n1 = p.peek(1).type;

    // `| ->` is malformed as an operator; assume arm and let the arm parser
    // produce the better error message.
    if (n1 == Tk.TOKEN_ARROW || n1 == Tk.TOKEN_ARROW_ASCII) { return true; }

    // A wildcard or rest pattern only makes sense as an arm head.
    if (n1 == Tk.TOKEN_WILDCARD)
    {
        Tk n2 = p.peek(2).type;
        return n2 == Tk.TOKEN_ARROW || n2 == Tk.TOKEN_ARROW_ASCII;
    }

    // Constructor pattern: `| Some(x) ->` / `| None ->`.
    if (n1 == Tk.TOKEN_TYPEVAR)
    {
        Tk n2 = p.peek(2).type;
        if (n2 == Tk.TOKEN_LPAREN) { return true; }
        if (n2 == Tk.TOKEN_ARROW || n2 == Tk.TOKEN_ARROW_ASCII) { return true; }
        if (n2 == Tk.TOKEN_DOT) { return true; }
        return false;
    }

    // Tuple pattern head: `| (a, b) ->`. A parenthesised expression can also
    // follow bitwise-or, so require the arrow to appear after the group.
    if (n1 == Tk.TOKEN_LPAREN) { return p.arrow_follows_group(1); }

    // Simple binder: `| x ->`.
    if (n1 == Tk.TOKEN_IDENT || tok_is_member_name(n1))
    {
        Tk n2 = p.peek(2).type;
        return n2 == Tk.TOKEN_ARROW || n2 == Tk.TOKEN_ARROW_ASCII;
    }

    // Literal pattern: `| 0 ->`.
    if (n1 == Tk.TOKEN_LIT_INT || n1 == Tk.TOKEN_LIT_STRING
     || n1 == Tk.TOKEN_LIT_CHAR || n1 == Tk.TOKEN_LIT_BOOL)
    {
        Tk n2 = p.peek(2).type;
        return n2 == Tk.TOKEN_ARROW || n2 == Tk.TOKEN_ARROW_ASCII;
    }

    return false;
}

// Peek past a balanced parenthesised group starting at lookahead index `from`
// and report whether an arrow immediately follows. Limited to the lookahead
// ring, so deeply nested heads fall back to "not an arm" — the conservative
// choice, since misreading an arm as bitwise-or yields a precise parse error
// while the reverse silently truncates a function body.
fn bool Parser.arrow_follows_group(Parser* p, usz from)
{
    usz i = from;
    int depth = 0;
    while (i < LA_SIZE)
    {
        Tk t = p.peek(i).type;
        if (t == Tk.TOKEN_LPAREN) { depth = depth + 1; }
        else if (t == Tk.TOKEN_RPAREN)
        {
            depth = depth - 1;
            if (depth == 0)
            {
                if (i + 1 < LA_SIZE)
                {
                    Tk nx = p.peek(i + 1).type;
                    return nx == Tk.TOKEN_ARROW || nx == Tk.TOKEN_ARROW_ASCII;
                }
                return false;
            }
        }
        else if (t == Tk.TOKEN_EOF) { return false; }
        i = i + 1;
    }
    return false;
}

// True when the token run starting at `from` is only layout before `want`.
// Used for lookahead across line breaks without mutating parser state.
fn bool Parser.layout_then(Parser* p, Tk want)
{
    usz look = 0;
    while (look + 1 < LA_SIZE)
    {
        Tk t = p.peek(look).type;
        if (t == Tk.TOKEN_NEWLINE || t == Tk.TOKEN_INDENT || t == Tk.TOKEN_DEDENT)
        {
            look = look + 1;
            continue;
        }
        break;
    }
    return p.peek(look).type == want;
}

// Consume a layout run and return how many tokens were eaten, so a caller can
// decide to proceed or (conceptually) back off.
fn usz Parser.eat_layout_run(Parser* p)
{
    usz n = 0;
    while (p.check(Tk.TOKEN_NEWLINE) || p.check(Tk.TOKEN_INDENT) || p.check(Tk.TOKEN_DEDENT))
    {
        p.advance();
        n = n + 1;
    }
    return n;
}

// ════════════════════════════════════════════════════════════════════════════
// 3. TYPES
// ════════════════════════════════════════════════════════════════════════════

/*
 Does this token begin a refinement predicate inside parentheses?
 Only comparison operators can: `(> 0)`, `(<= 1.0)`, `(!= 0)`.
*/
fn bool tok_is_refine_op(Tk t)
{
    switch (t)
    {
        case TOKEN_LT:
        case TOKEN_LTEQ:
        case TOKEN_GT:
        case TOKEN_GTEQ:
        case TOKEN_EQEQ:
        case TOKEN_NEQ:
        case TOKEN_LEQ_UNI:
        case TOKEN_GEQ_UNI:
        case TOKEN_NEQ_UNI:
            return true;
        default:
            return false;
    }
}

fn bool tok_starts_type(Tk t)
{
    switch (t)
    {
        case TOKEN_IDENT:
        case TOKEN_TYPEVAR:
        case TOKEN_WILDCARD:
        case TOKEN_LPAREN:
        case TOKEN_LBRACK:
        case TOKEN_STAR:
        case TOKEN_AMP:
        case TOKEN_KW_FN:
        case TOKEN_KW_SELF:
        case TOKEN_BOTTOM:
        case TOKEN_NEGATION:
        case TOKEN_LIT_NULL:
        case TOKEN_KW_NULLPTR:
        case TOKEN_FORALL:
        case TOKEN_EXISTS:
        case TOKEN_KW_TYPEOF:
        case TOKEN_KW_TYPEOF_UNQUAL:
        case TOKEN_EMPTYSET:
            return true;
        default:
            return false;
    }
}

/*
 Parse a type, then absorb any following arrow chain into an N_TY_FN.

 `parse_type` deliberately stops before `->`, because in a `fn` signature
 the arrow belongs to parse_fn_decl. Three other places need the arrow
 anyway — a `type` alias, a parenthesised type, and a quantifier body —
 and each had its own copy of the absorption, which is how they drifted:
 all three absorbed exactly ONE arrow.

 Arrows are RIGHT-associative (`X -> Y -> Z` is `X -> (Y -> Z)`), so one
 absorption is not enough. `∀ A . ∀ B . (A -> B) -> A -> B` left the final
 `B` outside the inner binder and reported it as an unknown type name.

 Recursing on the return type gives the right shape and, being one
 function, keeps the three call sites from diverging again.
*/
fn Node* Parser.parse_type_with_arrow(Parser* p)
{
    Node* lhs = p.parse_type();
    if (!p.check(Tk.TOKEN_ARROW) && !p.check(Tk.TOKEN_ARROW_ASCII)) { return lhs; }

    Tok ar = p.advance();
    // Right-associative: the return type may itself be an arrow chain.
    Node* ret = p.parse_type_with_arrow();
    Node* fnty = p.mk_at(Nk.N_TY_FN, ar);
    p.add(fnty, lhs);
    if (ret != null)
    {
        Node* rw = p.mk_at(Nk.N_TY_CONSTRAINT, ar);
        p.add(rw, ret);
        p.add(fnty, rw);
    }
    if (p.check(Tk.TOKEN_BANG))
    {
        Node* row = p.parse_effect_row();
        if (row != null) { p.add(fnty, row); }
    }
    return fnty;
}

fn Node* Parser.parse_type(Parser* p)
{
    return p.parse_type_ops(0);
}

// Type-level operators: ∪ (union), ∩ (intersect). Left-associative, with
// intersect binding tighter than union.
fn Node* Parser.parse_type_ops(Parser* p, int min_prec)
{
    if (!p.enter()) { Tok c = p.cur(); return p.mk_error(c); }
    Node* left = p.parse_type_prefix();
    while (true)
    {
        Tk t = p.ct();
        int prec = 0;
        Nk kind = Nk.N_TY_UNION;
        if (t == Tk.TOKEN_UNION_SYM) { prec = 1; kind = Nk.N_TY_UNION; }
        else if (t == Tk.TOKEN_INTERSECT) { prec = 2; kind = Nk.N_TY_INTERSECT; }
        else if (t == Tk.TOKEN_PIPE && !p.in_fn_sig) { prec = 1; kind = Nk.N_TY_UNION; }
        else { break; }
        if (prec < min_prec) { break; }
        Tok op = p.advance();
        Node* right = p.parse_type_ops(prec + 1);
        Node* n = p.mk(kind, op.line, op.col);
        p.add(n, left);
        p.add(n, right);
        left = n;
    }
    p.leave();
    return left;
}

fn Node* Parser.parse_type_prefix(Parser* p)
{
    Tok t = p.cur();
    switch (t.type)
    {
        case TOKEN_STAR:
        {
            p.advance();
            bool is_mut = p.accept(Tk.TOKEN_KW_MUT);
            Node* inner = p.parse_type_prefix();
            Node* n = p.mk(Nk.N_TY_PTR, t.line, t.col);
            if (is_mut) { n.flags = n.flags | pfront_core::NF_MUT; }
            p.add(n, inner);
            return n;
        }
        case TOKEN_AMP:
        {
            p.advance();
            bool is_mut = p.accept(Tk.TOKEN_KW_MUT);
            Node* inner = p.parse_type_prefix();
            Node* n = p.mk(Nk.N_TY_REF, t.line, t.col);
            if (is_mut) { n.flags = n.flags | pfront_core::NF_MUT; }
            p.add(n, inner);
            return n;
        }
        case TOKEN_NEGATION:
        {
            p.advance();
            Node* inner = p.parse_type_prefix();
            return p.arena.node1(Nk.N_TY_NEGATION, inner, t.line, t.col);
        }
        case TOKEN_FORALL:
        case TOKEN_EXISTS:
        {
            /*
             Quantified types, spec §13.4:
                 ∀ A . A -> A
                 ∃ T . T ∩ ¬null
                 ∀ A . ∀ B . (A -> B) -> A -> B

             The binder scopes over EVERYTHING to its right, so the body is
             parsed with the full type grammar rather than as a prefix
             operand — `∀ A . A -> A` must bind the whole arrow type, not
             just `A`.

             Neither quantifier had any parse rule at all; both are in the
             spec and neither appears in the stdlib, so nothing caught it.
            */
            p.advance();
            Nk qk = t.type == Tk.TOKEN_FORALL ? Nk.N_TY_FORALL : Nk.N_TY_EXISTS;
            Node* q = p.mk_at(qk, t);

            // One or more bound variables, comma-separated.
            while (true)
            {
                Tok v = p.cur();
                if (v.type != Tk.TOKEN_TYPEVAR && v.type != Tk.TOKEN_IDENT)
                {
                    p.err(1016, "expected a type variable after a quantifier");
                    break;
                }
                p.advance();
                Node* tv = p.mk_at(Nk.N_DECL_TYPEPARAM, v);
                tv.name_id = p.intern_tok(v);
                tv.p.sptr = v.start;
                tv.p.slen = v.len;
                p.add(q, tv);
                if (!p.accept(Tk.TOKEN_COMMA)) { break; }
            }

            // The separator is `.`; accept `,` too since the spec writes
            // both spellings in different examples.
            if (!p.accept(Tk.TOKEN_DOT)) { p.accept(Tk.TOKEN_COMMA); }

            /*
             The body must absorb a following ARROW.

             `parse_type` deliberately stops before `->`, because in a `fn`
             signature the arrow is consumed by parse_fn_decl, which builds
             the N_TY_FN itself. But a quantifier scopes over the WHOLE
             type, so `∀ A . A -> A` must bind both sides. Without this the
             body was just the parameter `A`, the arrow was assembled one
             level up, and the return `A` resolved outside the binder's
             scope — reported as an unknown type name.

             Build the same N_TY_FN shape parse_fn_decl and the alias path
             produce, so downstream passes see one representation.
            */
            p.add(q, p.parse_type_with_arrow());
            return q;
        }
        default:
            return p.parse_type_postfix();
    }
}

fn Node* Parser.parse_type_postfix(Parser* p)
{
    Node* base = p.parse_type_atom();
    while (true)
    {
        Tk t = p.ct();
        if (t == Tk.TOKEN_LT)
        {
            // Generic application: Name<A, B>
            if (base == null) { break; }
            if (base.kind != Nk.N_TY_NAME && base.kind != Nk.N_TY_PATH) { break; }
            Tok lt = p.advance();
            Node* g = p.mk(Nk.N_TY_GENERIC, lt.line, lt.col);
            p.add(g, base);
            if (!p.check(Tk.TOKEN_GT))
            {
                while (true)
                {
                    Node* arg = p.parse_type();
                    p.add(g, arg);
                    if (!p.accept(Tk.TOKEN_COMMA)) { break; }
                    if (p.check(Tk.TOKEN_GT)) { break; }
                }
            }
            p.expect_generic_close();
            base = g;
        }
        else if (t == Tk.TOKEN_DOT || t == Tk.TOKEN_COLONCOLON)
        {
            // Qualified type: mod.Type
            Tok dot = p.advance();
            Tok nm = p.cur();
            if (!tok_is_member_name(nm.type))
            {
                p.err(1011, "expected a type name after '.' in a qualified type");
                break;
            }
            p.advance();
            Node* path = p.mk(Nk.N_TY_PATH, dot.line, dot.col);
            p.add(path, base);
            Node* seg = p.mk_at(Nk.N_PATH_SEG, nm);
            seg.name_id = p.intern_tok(nm);
            seg.p.sptr = nm.start;
            seg.p.slen = nm.len;
            p.add(path, seg);
            base = path;
        }
        else { break; }
    }
    return base;
}

fn Node* Parser.parse_type_atom(Parser* p)
{
    Tok t = p.cur();
    switch (t.type)
    {
        case TOKEN_IDENT:
        case TOKEN_TYPEVAR:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_TY_NAME, t);
            n.name_id = p.intern_tok(t);
            n.p.sptr = t.start;
            n.p.slen = t.len;
            return n;
        }
        case TOKEN_WILDCARD:
            p.advance();
            return p.mk_at(Nk.N_TY_INFER, t);
        case TOKEN_KW_SELF:
            p.advance();
            return p.mk_at(Nk.N_TY_SELF, t);
        case TOKEN_BOTTOM:
        case TOKEN_EMPTYSET:
            p.advance();
            return p.mk_at(Nk.N_TY_BOTTOM, t);
        case TOKEN_LIT_NULL:
        {
            /*
             `null` as a TYPE — the singleton set containing only the null
             pointer. The spec's canonical semantic-subtyping example is
             `type NonNull<T> = T ∩ ¬null` (§13.1), and it did not parse:
             the lexer classifies `null` as TOKEN_LIT_NULL (a literal), so
             the type atom parser rejected it as "expected a type".

             It is a named type here, not a literal: `¬null` must denote
             the complement of that singleton for the disjointness relation
             to mean anything.
            */
            p.advance();
            Node* n = p.mk_at(Nk.N_TY_NAME, t);
            n.name_id = p.interner.intern("null", 4);
            n.p.sptr = t.start;
            n.p.slen = t.len;
            return n;
        }
        case TOKEN_KW_NULLPTR:
        {
            // C23 spelling of the same singleton.
            p.advance();
            Node* n = p.mk_at(Nk.N_TY_NAME, t);
            n.name_id = p.interner.intern("null", 4);
            n.p.sptr = t.start;
            n.p.slen = t.len;
            return n;
        }
        case TOKEN_LPAREN:
        {
            p.advance();
            if (p.accept(Tk.TOKEN_RPAREN)) { return p.mk_at(Nk.N_TY_UNIT, t); }

            /*
             A REFINEMENT PREDICATE, spec §13.1:
                 type Positive    = i32 ∩ (> 0)
                 type Normalized  = f32 ∩ (>= 0.0) ∩ (<= 1.0)

             A parenthesised type never starts with a comparison operator,
             so seeing one here is unambiguous. Without this the whole
             refinement half of semantic subtyping was unparseable — every
             example in §13.1 failed with "expected a type".
            */
            if (tok_is_refine_op(p.ct()))
            {
                Tok op = p.advance();
                Node* rf = p.mk_at(Nk.N_TY_REFINE, op);
                rf.p.op = (int)op.type;
                p.add(rf, p.parse_expr());
                p.expect(Tk.TOKEN_RPAREN, 1014, "expected ')' to close a refinement predicate");
                return rf;
            }

            Node* first = p.parse_type();
            if (p.check(Tk.TOKEN_COMMA))
            {
                Node* tup = p.mk_at(Nk.N_TY_TUPLE, t);
                p.add(tup, first);
                while (p.accept(Tk.TOKEN_COMMA))
                {
                    if (p.check(Tk.TOKEN_RPAREN)) { break; }
                    // C-style variadic tail: `(ptr, ptr, ...) -> i32`
                    if (p.check(Tk.TOKEN_ELLIPSIS))
                    {
                        Tok el = p.advance();
                        tup.flags = tup.flags | pfront_core::NF_VARIADIC;
                        p.add(tup, p.mk_at(Nk.N_TY_INFER, el));
                        break;
                    }
                    p.add(tup, p.parse_type());
                }
                p.expect(Tk.TOKEN_RPAREN, 1012, "expected ')' to close tuple type");
                return tup;
            }
            /*
             A PARENTHESISED FUNCTION TYPE: `(A -> B)`.

             parse_type stops before an arrow, because in a `fn` signature
             the arrow belongs to parse_fn_decl. Inside parentheses there
             is no such wrapper, so the arrow was left sitting where a `)`
             was expected — `(i64 -> i64)` did not parse at all, and nor
             did any higher-order signature written that way.

             Build the same N_TY_FN shape as parse_fn_decl and the alias
             path, so downstream sees one representation of a function
             type rather than three.
            */
            if (p.check(Tk.TOKEN_ARROW) || p.check(Tk.TOKEN_ARROW_ASCII))
            {
                Tok ar = p.advance();
                Node* ret = p.parse_type_with_arrow();
                Node* fnty = p.mk_at(Nk.N_TY_FN, ar);
                p.add(fnty, first);
                if (ret != null)
                {
                    Node* rw = p.mk_at(Nk.N_TY_CONSTRAINT, ar);
                    p.add(rw, ret);
                    p.add(fnty, rw);
                }
                if (p.check(Tk.TOKEN_BANG))
                {
                    Node* row = p.parse_effect_row();
                    if (row != null) { p.add(fnty, row); }
                }
                p.expect(Tk.TOKEN_RPAREN, 1012, "expected ')' after parenthesised function type");
                return fnty;
            }
            p.expect(Tk.TOKEN_RPAREN, 1012, "expected ')' after parenthesised type");
            return first;
        }
        case TOKEN_LBRACK:
        {
            // [T] slice, or [T; N] array
            p.advance();
            Node* elem = p.parse_type();
            if (p.accept(Tk.TOKEN_SEMI))
            {
                Node* arr = p.mk_at(Nk.N_TY_ARRAY, t);
                p.add(arr, elem);
                Node* count = p.parse_expr();
                p.add(arr, count);
                p.expect(Tk.TOKEN_RBRACK, 1013, "expected ']' to close array type");
                return arr;
            }
            p.expect(Tk.TOKEN_RBRACK, 1013, "expected ']' to close slice type");
            return p.arena.node1(Nk.N_TY_SLICE, elem, t.line, t.col);
        }
        case TOKEN_KW_FN:
        {
            // fn(A, B) -> C
            p.advance();
            Node* fnty = p.mk_at(Nk.N_TY_FN, t);
            if (p.accept(Tk.TOKEN_LPAREN))
            {
                if (!p.check(Tk.TOKEN_RPAREN))
                {
                    while (true)
                    {
                        p.add(fnty, p.parse_type());
                        if (!p.accept(Tk.TOKEN_COMMA)) { break; }
                        if (p.check(Tk.TOKEN_RPAREN)) { break; }
                    }
                }
                p.expect(Tk.TOKEN_RPAREN, 1014, "expected ')' in function type");
            }
            if (p.accept(Tk.TOKEN_ARROW) || p.accept(Tk.TOKEN_ARROW_ASCII))
            {
                Node* ret = p.parse_type();
                Node* rw = p.mk(Nk.N_TY_CONSTRAINT, t.line, t.col);
                p.add(rw, ret);
                p.add(fnty, rw);
            }
            return fnty;
        }
        case TOKEN_KW_TYPEOF:
        case TOKEN_KW_TYPEOF_UNQUAL:
        {
            p.advance();
            p.expect(Tk.TOKEN_LPAREN, 1015, "expected '(' after typeof");
            Node* e = p.parse_expr();
            p.expect(Tk.TOKEN_RPAREN, 1015, "expected ')' after typeof operand");
            // N_TY_TYPEOF, not N_TY_NAME: the child is an EXPRESSION and
            // must be resolved as one. As an unnamed N_TY_NAME the operand
            // was never visited and came out unresolved.
            Node* n = p.mk_at(Nk.N_TY_TYPEOF, t);
            p.add(n, e);
            return n;
        }
        default:
        {
            // Keywordised names are legal type/module identifiers: `meta`,
            // `region`, `block`, `node`, `graph`, `stage`. They appear as real
            // module names in the stdlib (`meta.Metadata`), so rejecting them
            // here made every qualified reference to such a module fail.
            if (tok_is_member_name(t.type))
            {
                p.advance();
                Node* n = p.mk_at(Nk.N_TY_NAME, t);
                n.name_id = p.intern_tok(t);
                n.p.sptr = t.start;
                n.p.slen = t.len;
                return n;
            }
            p.err(1016, "expected a type");
            p.advance();
            return p.mk_error(t);
        }
    }
}

// Effect row:  ! [IO, Alloc, ..r]
fn Node* Parser.parse_effect_row(Parser* p)
{
    Tok bang = p.cur();
    if (!p.accept(Tk.TOKEN_BANG)) { return null; }
    Node* row = p.mk_at(Nk.N_TY_EFFECT_ROW, bang);
    if (!p.accept(Tk.TOKEN_LBRACK))
    {
        // `! E` single-effect shorthand
        if (p.check(Tk.TOKEN_IDENT) || p.check(Tk.TOKEN_TYPEVAR))
        {
            Tok e = p.advance();
            Node* el = p.mk_at(Nk.N_TY_EFFECT_ELEM, e);
            el.name_id = p.intern_tok(e);
            el.p.sptr = e.start;
            el.p.slen = e.len;
            p.add(row, el);
        }
        return row;
    }
    while (!p.check(Tk.TOKEN_RBRACK) && !p.at_end())
    {
        if (p.accept(Tk.TOKEN_DOTDOT))
        {
            row.flags = row.flags | pfront_core::NF_OPEN_ROW;
            if (p.check(Tk.TOKEN_IDENT) || p.check(Tk.TOKEN_TYPEVAR))
            {
                Tok tail = p.advance();
                Node* el = p.mk_at(Nk.N_TY_EFFECT_ELEM, tail);
                el.name_id = p.intern_tok(tail);
                el.p.sptr = tail.start;
                el.p.slen = tail.len;
                el.p.aux = 1;   // marks the row tail variable
                p.add(row, el);
            }
        }
        else if (p.check(Tk.TOKEN_IDENT) || p.check(Tk.TOKEN_TYPEVAR))
        {
            Tok e = p.advance();
            Node* el = p.mk_at(Nk.N_TY_EFFECT_ELEM, e);
            el.name_id = p.intern_tok(e);
            el.p.sptr = e.start;
            el.p.slen = e.len;
            p.add(row, el);
        }
        else
        {
            p.err(1017, "expected an effect name in effect row");
            break;
        }
        if (!p.accept(Tk.TOKEN_COMMA)) { break; }
    }
    p.expect(Tk.TOKEN_RBRACK, 1018, "expected ']' to close effect row");
    return row;
}

// ════════════════════════════════════════════════════════════════════════════
// 4. PATTERNS
// ════════════════════════════════════════════════════════════════════════════

fn Node* Parser.parse_pattern(Parser* p)
{
    if (!p.enter()) { Tok c = p.cur(); return p.mk_error(c); }
    Node* first = p.parse_pattern_range();
    // or-patterns: p1 | p2 | p3
    if (p.check(Tk.TOKEN_PIPE) && !p.in_fn_sig)
    {
        Node* orp = p.mk(Nk.N_PAT_OR, first.line, first.col);
        p.add(orp, first);
        orp.flags = orp.flags | pfront_core::NF_REFUTABLE;
        while (p.accept(Tk.TOKEN_PIPE))
        {
            p.add(orp, p.parse_pattern_range());
        }
        p.leave();
        return orp;
    }
    p.leave();
    return first;
}

fn Node* Parser.parse_pattern_range(Parser* p)
{
    Node* lo = p.parse_pattern_atom();
    if (p.check(Tk.TOKEN_DOTDOT) || p.check(Tk.TOKEN_DOTDOTEQ))
    {
        Tok op = p.advance();
        Node* rng = p.mk(Nk.N_PAT_RANGE, op.line, op.col);
        if (op.type == Tk.TOKEN_DOTDOTEQ) { rng.flags = rng.flags | pfront_core::NF_INCLUSIVE; }
        rng.flags = rng.flags | pfront_core::NF_REFUTABLE;
        p.add(rng, lo);
        Node* hi = p.parse_pattern_atom();
        p.add(rng, hi);
        return rng;
    }
    return lo;
}

fn Node* Parser.parse_pattern_atom(Parser* p)
{
    Tok t = p.cur();

    // A `mut` prefix is legal on any binder, not just behind `&`. Tuple
    // destructuring uses it per-element:
    //     let (mut v0, mut v1) = city_weak_hash(...)
    // Handling `mut` only in the `&mut` and `let mut` positions made every
    // such destructuring a parse error at the comma.
    if (t.type == Tk.TOKEN_KW_MUT)
    {
        p.advance();
        Node* inner = p.parse_pattern_atom();
        if (inner != null) { inner.flags = inner.flags | pfront_core::NF_MUT; }
        return inner;
    }

    switch (t.type)
    {
        case TOKEN_WILDCARD:
            p.advance();
            return p.mk_at(Nk.N_PAT_WILDCARD, t);

        case TOKEN_LBRACE:
        {
            /*
             An ANONYMOUS struct pattern, spec §8:

                 match point
                   | { x: 0, y: 0 } → "origin"
                   | { x: 0, y }    → "on y-axis"
                   | { x, y }       → "general"

             and the tagged-sum form from §9, `| ({ some: v }, _) -> v`.

             Only the NAMED form (`Point { x, y }`) had a rule, because
             that is the only one the stdlib writes. The anonymous form —
             which is what the spec uses for every example, since the type
             is already known from the scrutinee — failed with "expected a
             pattern".

             Same node shape as the named form, minus the path child, so
             exhaustiveness checking and lowering need no new case.
            */
            p.advance();
            Node* sp = p.mk_at(Nk.N_PAT_STRUCT, t);
            sp.flags = sp.flags | pfront_core::NF_REFUTABLE;
            p.skip_layout();
            while (!p.check(Tk.TOKEN_RBRACE) && !p.at_end())
            {
                Tok fname = p.cur();
                if (fname.type == Tk.TOKEN_DOTDOT)
                {
                    p.advance();
                    p.add(sp, p.mk_at(Nk.N_PAT_REST, fname));
                    p.skip_layout();
                    break;
                }
                if (!tok_is_member_name(fname.type))
                {
                    p.err(1023, "expected a field name in struct pattern");
                    break;
                }
                p.advance();
                Node* fld = p.mk_at(Nk.N_PAT_FIELD, fname);
                fld.name_id = p.intern_tok(fname);
                fld.p.sptr = fname.start;
                fld.p.slen = fname.len;
                if (p.accept(Tk.TOKEN_COLON))
                {
                    p.add(fld, p.parse_pattern());
                }
                else
                {
                    // Shorthand `{ x }` binds a variable of the same name.
                    Node* bind = p.mk_at(Nk.N_PAT_IDENT, fname);
                    bind.name_id = fld.name_id;
                    bind.p.sptr = fname.start;
                    bind.p.slen = fname.len;
                    p.add(fld, bind);
                }
                p.add(sp, fld);
                p.skip_layout();
                if (!p.accept(Tk.TOKEN_COMMA)) { break; }
                p.skip_layout();
            }
            p.skip_layout();
            p.expect(Tk.TOKEN_RBRACE, 1024, "expected '}' to close struct pattern");
            return sp;
        }

        case TOKEN_DOTDOT:
            p.advance();
            return p.mk_at(Nk.N_PAT_REST, t);

        case TOKEN_LIT_INT:
        case TOKEN_LIT_FLOAT:
        case TOKEN_LIT_BOOL:
        case TOKEN_LIT_CHAR:
        case TOKEN_LIT_STRING:
        case TOKEN_LIT_NULL:
        {
            Node* lit = p.parse_literal();
            Node* n = p.mk_at(Nk.N_PAT_LITERAL, t);
            n.flags = n.flags | pfront_core::NF_REFUTABLE;
            p.add(n, lit);
            return n;
        }

        case TOKEN_MINUS:
        {
            // negative integer literal pattern
            p.advance();
            Node* lit = p.parse_literal();
            Node* neg = p.mk_at(Nk.N_EXPR_UNARY, t);
            neg.p.op = (int)Tk.TOKEN_MINUS;
            p.add(neg, lit);
            Node* n = p.mk_at(Nk.N_PAT_LITERAL, t);
            n.flags = n.flags | pfront_core::NF_REFUTABLE;
            p.add(n, neg);
            return n;
        }

        case TOKEN_AMP:
        {
            p.advance();
            bool is_mut = p.accept(Tk.TOKEN_KW_MUT);
            Node* inner = p.parse_pattern_atom();
            Node* n = p.mk_at(Nk.N_PAT_REF, t);
            if (is_mut) { n.flags = n.flags | pfront_core::NF_MUT; }
            p.add(n, inner);
            return n;
        }

        case TOKEN_LPAREN:
        {
            p.advance();
            if (p.accept(Tk.TOKEN_RPAREN))
            {
                // () unit pattern — irrefutable
                return p.mk_at(Nk.N_PAT_TUPLE, t);
            }
            Node* first = p.parse_pattern();
            if (p.check(Tk.TOKEN_COMMA))
            {
                Node* tup = p.mk_at(Nk.N_PAT_TUPLE, t);
                p.add(tup, first);
                while (p.accept(Tk.TOKEN_COMMA))
                {
                    if (p.check(Tk.TOKEN_RPAREN)) { break; }
                    p.add(tup, p.parse_pattern());
                }
                p.expect(Tk.TOKEN_RPAREN, 1020, "expected ')' to close tuple pattern");
                return tup;
            }
            p.expect(Tk.TOKEN_RPAREN, 1020, "expected ')' after pattern");
            return first;
        }

        case TOKEN_LBRACK:
        {
            p.advance();
            Node* arr = p.mk_at(Nk.N_PAT_ARRAY, t);
            arr.flags = arr.flags | pfront_core::NF_REFUTABLE;
            while (!p.check(Tk.TOKEN_RBRACK) && !p.at_end())
            {
                p.add(arr, p.parse_pattern());
                if (!p.accept(Tk.TOKEN_COMMA)) { break; }
            }
            p.expect(Tk.TOKEN_RBRACK, 1021, "expected ']' to close array pattern");
            return arr;
        }

        case TOKEN_TYPEVAR:
        {
            // Enum variant, possibly qualified and/or with a payload.
            Node* path = p.parse_pattern_path();
            if (p.check(Tk.TOKEN_LPAREN))
            {
                p.advance();
                Node* v = p.mk_at(Nk.N_PAT_VARIANT, t);
                v.flags = v.flags | pfront_core::NF_REFUTABLE;
                v.name_id = path.name_id;
                p.add(v, path);
                while (!p.check(Tk.TOKEN_RPAREN) && !p.at_end())
                {
                    p.add(v, p.parse_pattern());
                    if (!p.accept(Tk.TOKEN_COMMA)) { break; }
                }
                p.expect(Tk.TOKEN_RPAREN, 1022, "expected ')' to close variant pattern");
                return v;
            }
            if (p.check(Tk.TOKEN_LBRACE) && !p.no_struct_lit)
            {
                p.advance();
                Node* sp = p.mk_at(Nk.N_PAT_STRUCT, t);
                sp.flags = sp.flags | pfront_core::NF_REFUTABLE;
                sp.name_id = path.name_id;
                p.add(sp, path);
                p.skip_layout();
                while (!p.check(Tk.TOKEN_RBRACE) && !p.at_end())
                {
                    Tok fname = p.cur();
                    if (fname.type == Tk.TOKEN_DOTDOT)
                    {
                        p.advance();
                        p.add(sp, p.mk_at(Nk.N_PAT_REST, fname));
                        p.skip_layout();
                        break;
                    }
                    if (!p.expect(Tk.TOKEN_IDENT, 1023, "expected a field name in struct pattern")) { break; }
                    Node* fld = p.mk_at(Nk.N_PAT_FIELD, fname);
                    fld.name_id = p.intern_tok(fname);
                    fld.p.sptr = fname.start;
                    fld.p.slen = fname.len;
                    if (p.accept(Tk.TOKEN_COLON))
                    {
                        p.add(fld, p.parse_pattern());
                    }
                    else
                    {
                        // shorthand `{ x }` binds x
                        Node* bind = p.mk_at(Nk.N_PAT_IDENT, fname);
                        bind.name_id = fld.name_id;
                        bind.p.sptr = fname.start;
                        bind.p.slen = fname.len;
                        p.add(fld, bind);
                    }
                    p.add(sp, fld);
                    p.skip_layout();
                    if (!p.accept(Tk.TOKEN_COMMA)) { break; }
                    p.skip_layout();
                }
                p.skip_layout();
                p.expect(Tk.TOKEN_RBRACE, 1024, "expected '}' to close struct pattern");
                return sp;
            }
            // A BARE uppercase name with no payload, no braces and no dotted
            // qualification is genuinely ambiguous in surface syntax:
            //
            //     | Red      -> ...     -- nullary enum variant (refutable)
            //     | M        -> ...     -- a binder that happens to be caps
            //
            // The parser cannot tell them apart; only the resolver knows
            // whether `M` names a variant in scope. Committing to
            // N_PAT_VARIANT here made every uppercase parameter name — the
            // `(a, b, c, M, N, K)` matrix-dimension convention used across
            // the numeric stdlib — an unresolvable pattern.
            //
            // Emit a BINDER carrying the path as a child. The resolver
            // promotes it back to a variant when the name resolves to one
            // (see bind_pattern / N_PAT_IDENT with NF_REFUTABLE), and
            // otherwise binds it. Qualified names (`Color.Red`) and payload
            // forms are unambiguous and were already handled above.
            if (path != null && path.child_count <= 1)
            {
                Node* amb = p.mk_at(Nk.N_PAT_IDENT, t);
                amb.name_id = path.name_id;
                amb.p.sptr = t.start;
                amb.p.slen = t.len;
                // Remember the variant reading so the resolver can restore it.
                amb.p.aux = PAT_MAYBE_VARIANT;
                p.add(amb, path);
                return amb;
            }
            Node* v2 = p.mk_at(Nk.N_PAT_VARIANT, t);
            v2.flags = v2.flags | pfront_core::NF_REFUTABLE;
            v2.name_id = path.name_id;
            p.add(v2, path);
            return v2;
        }

        case TOKEN_IDENT:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_PAT_IDENT, t);
            n.name_id = p.intern_tok(t);
            n.p.sptr = t.start;
            n.p.slen = t.len;
            // `name : Type` annotated binder
            if (p.check(Tk.TOKEN_COLON))
            {
                p.advance();
                n.type_ann = p.parse_type();
            }
            return n;
        }

        default:
        {
            // Metaprogramming/IRDL keywords (`node`, `opcode`, `block`, ...)
            // are frequently used as ordinary binder names in real code. In
            // pattern position they are plain identifiers.
            if (tok_is_member_name(t.type))
            {
                p.advance();
                Node* n = p.mk_at(Nk.N_PAT_IDENT, t);
                n.name_id = p.intern_tok(t);
                n.p.sptr = t.start;
                n.p.slen = t.len;
                if (p.check(Tk.TOKEN_COLON))
                {
                    p.advance();
                    n.type_ann = p.parse_type();
                }
                return n;
            }
            p.err(1025, "expected a pattern");
            p.advance();
            return p.mk_error(t);
        }
    }
}

fn Node* Parser.parse_pattern_path(Parser* p)
{
    Tok first = p.advance();
    Node* path = p.mk_at(Nk.N_MODULE_PATH, first);
    Node* seg = p.mk_at(Nk.N_PATH_SEG, first);
    seg.name_id = p.intern_tok(first);
    seg.p.sptr = first.start;
    seg.p.slen = first.len;
    p.add(path, seg);
    path.name_id = seg.name_id;
    while ((p.check(Tk.TOKEN_DOT) || p.check(Tk.TOKEN_COLONCOLON))
        && tok_is_member_name(p.peek(1).type))
    {
        p.advance();
        Tok nx = p.advance();
        Node* s2 = p.mk_at(Nk.N_PATH_SEG, nx);
        s2.name_id = p.intern_tok(nx);
        s2.p.sptr = nx.start;
        s2.p.slen = nx.len;
        p.add(path, s2);
        path.name_id = s2.name_id;   // the last segment names the variant
    }
    return path;
}

// ════════════════════════════════════════════════════════════════════════════
// 5. EXPRESSIONS  (Pratt / precedence climbing)
// ════════════════════════════════════════════════════════════════════════════

// Binding powers. Higher binds tighter. Mirrors the documented Pride table.
fn int infix_prec(Tk t)
{
    switch (t)
    {
        /*
         `++` is REWRITE-RULE COMPOSITION (spec §24, precedence level 16 —
         below pipeline, above assignment). It had no entry here at all, so
         `let full : Rewrite = arith ++ strength` — the documented way to
         build a rule set — reported "expected an expression".

         Level 1 here matches the spec's relative ordering: composition
         binds looser than everything except assignment, so `a ++ b |> c`
         groups as `a ++ (b |> c)`... no: pipeline is level 14 and compose
         is 16, i.e. compose binds LOOSER. Giving pipeline 1 and compose 0
         would put compose below assignment. The table here is inverted
         relative to the spec's numbering (higher binds tighter), so
         compose gets the lowest non-zero precedence and pipeline sits
         just above it.
        */
        case TOKEN_PLUSPLUS:      return 1;
        case TOKEN_PIPELINE:      return 2;
        case TOKEN_KW_OR:
        case TOKEN_PIPEPIPE:      return 3;
        case TOKEN_KW_AND:
        case TOKEN_AMPAMP:        return 4;
        case TOKEN_EQEQ:
        case TOKEN_NEQ:
        case TOKEN_NEQ_UNI:       return 5;
        case TOKEN_LT:
        case TOKEN_LTEQ:
        case TOKEN_GT:
        case TOKEN_GTEQ:
        case TOKEN_GEQ_UNI:
        case TOKEN_LEQ_UNI:
        case TOKEN_ELEMENT:       return 6;   // ∈ — relational (spec §24)
        case TOKEN_PIPE:          return 7;
        case TOKEN_XOR:           return 8;
        case TOKEN_AMP:           return 9;
        case TOKEN_LSHIFT:
        case TOKEN_RSHIFT:        return 10;
        case TOKEN_DOTDOT:
        case TOKEN_DOTDOTEQ:      return 11;
        case TOKEN_PLUS:
        case TOKEN_MINUS:
        case TOKEN_PLUS_QUESTION:
        case TOKEN_MINUS_QUESTION:
        case TOKEN_PLUS_PERCENT:
        case TOKEN_MINUS_PERCENT:
        case TOKEN_PLUS_PIPE:
        case TOKEN_MINUS_PIPE:    return 12;
        case TOKEN_STAR:
        case TOKEN_SLASH:
        case TOKEN_PERCENT:
        case TOKEN_STAR_QUESTION:
        case TOKEN_STAR_PERCENT:
        case TOKEN_STAR_PIPE:     return 13;
        case TOKEN_KW_AS:         return 14;
        /*
         0 means "not an infix operator" and is load-bearing: callers loop
         `while (infix_prec(t) > 0)`. A blanket renumber caught this too
         and returned 1, which made EVERY token look like an operator —
         31 regression tests failed instantly. Left explicit so the next
         renumber does not repeat it.
        */
        default:                  return 0;
    }
}

fn bool is_right_assoc(Tk t)
{
    // No right-associative binary operators today; kept as a hook so adding
    // `**` or `<|` later is a one-line change rather than a restructure.
    return false;
}

fn Node* Parser.parse_expr(Parser* p)
{
    return p.parse_expr_prec(1);
}

// Assignment is parsed at statement level, not here, so `a = b` inside an
// expression context is a deliberate error rather than a silent success.
fn Node* Parser.parse_expr_prec(Parser* p, int min_prec)
{
    if (!p.enter()) { Tok c = p.cur(); p.advance(); return p.mk_error(c); }
    Node* left = p.parse_unary();
    while (true)
    {
        Tk t = p.ct();
        // Inside a clause/match/handler arm body, a bare `|` starts the NEXT
        // arm and must terminate this expression rather than parse as
        // bitwise-or. `match o | Some(_) -> true | None -> false` depends on
        // this, and it is the single most common shape in the stdlib.
        // `|` is genuinely ambiguous inside an arm body:
        //     | w -> a | b            -- bitwise-or, ONE arm
        //     | Some(x) -> a | None -> b   -- TWO arms
        // Disambiguate on shape rather than position: a `|` that introduces
        // an arm is followed by a pattern and then an arrow. If we cannot see
        // an arrow within the lookahead window, treat it as bitwise-or.
        if (t == Tk.TOKEN_PIPE && p.in_fn_sig)
        {
            if (!p.pipe_starts_arm()) { /* fall through: bitwise or */ }
            else { break; }
        }

        // Line continuation. A layout token here may be cosmetic: real Pride
        // wraps long boolean chains as
        //     (a && b) ||
        //     (c && d)
        // The lexer emits NEWLINE/INDENT after the trailing operator, but the
        // expression is unfinished. Look past the layout run; if an infix
        // operator continues the expression, absorb the layout and carry on.
        if (t == Tk.TOKEN_NEWLINE || t == Tk.TOKEN_INDENT)
        {
            usz look = 0;
            while (look + 1 < LA_SIZE)
            {
                Tk lt = p.peek(look).type;
                if (lt == Tk.TOKEN_NEWLINE || lt == Tk.TOKEN_INDENT) { look = look + 1; continue; }
                break;
            }
            Tk after = p.peek(look).type;
            int cont_prec = infix_prec(after);
            bool continues = cont_prec != 0 && cont_prec >= min_prec;
            if (after == Tk.TOKEN_PIPE && p.in_fn_sig) { continues = false; }

            /*
             AMBIGUOUS PREFIX/INFIX OPERATORS AT LINE START.

             `*` and `&` are both infix (multiply, bitwise-and) and prefix
             (dereference, address-of). At the start of a NEW LINE the
             prefix reading is meant:

                 let a = &n
                 *a            <- dereference, not `&n * a`

             Treating them as a continuation silently merged the two
             statements and the second's binder came out unresolved. The
             same applies to `-` (negate) and `+`.

             A genuine continuation puts the operator at the END of the
             previous line, which this branch does not see — that case is
             handled by skip_continuation_layout after the operator is
             consumed. So an ambiguous operator appearing FIRST on a line
             is always the prefix form.
            */
            if (after == Tk.TOKEN_STAR || after == Tk.TOKEN_AMP
                || after == Tk.TOKEN_MINUS || after == Tk.TOKEN_PLUS)
            {
                /*
                 ...but a CONTINUATION line is indented deeper than the
                 statement that owns it:

                     (n + 0) + (n + 0)
                       + (n * 1)          <- indented: infix continuation
                 vs
                     let a = &n
                     *a                   <- same column: prefix deref

                 Only the second is a new statement. Using the token kind
                 alone broke every leading-operator continuation in
                 experiments/test_irdl_trs.pie, which is exactly what that
                 file exists to check.
                */
                if (p.peek(look).col - 1 <= p.stmt_indent) { continues = false; }
            }
            if (!continues) { break; }
            for (usz k = 0; k < look; k++) { p.advance(); }
            t = p.ct();
        }

        int prec = infix_prec(t);
        if (prec == 0 || prec < min_prec) { break; }
        Tok op = p.advance();
        // Symmetric case: the operator is at END of line and the operand is on
        // the next. `x ||\n  y` — skip the layout run before the right side.
        p.skip_continuation_layout();

        if (op.type == Tk.TOKEN_KW_AS)
        {
            // The type after `as` must NOT swallow a following `|` as a
            // type-union operator:
            //     p[0] as i64 | ((p[1] as i64) << 32)
            // is a bitwise-or of two casts, not a cast to the union type
            // `i64 | ...`. A union in cast position would be written with
            // the explicit `∪` symbol.
            //
            // `in_fn_sig` already means exactly "a bare `|` here is not a
            // type union" (it exists for clause bars in signatures), so
            // reuse it rather than adding a second near-identical flag.
            bool saved_sig = p.in_fn_sig;
            p.in_fn_sig = true;
            Node* ty = p.parse_type();
            p.in_fn_sig = saved_sig;
            Node* cast = p.mk_at(Nk.N_EXPR_CAST, op);
            p.add(cast, left);
            cast.type_ann = ty;
            left = cast;
            continue;
        }

        if (op.type == Tk.TOKEN_DOTDOT || op.type == Tk.TOKEN_DOTDOTEQ)
        {
            Node* rng = p.mk_at(Nk.N_EXPR_RANGE, op);
            if (op.type == Tk.TOKEN_DOTDOTEQ) { rng.flags = rng.flags | pfront_core::NF_INCLUSIVE; }
            p.add(rng, left);
            if (tok_starts_expr(p.ct()))
            {
                p.add(rng, p.parse_expr_prec(prec + 1));
            }
            // `0..n by 2`
            if (p.check(Tk.TOKEN_KW_BY))
            {
                p.advance();
                Node* step = p.parse_expr_prec(prec + 1);
                p.add(rng, step);
                rng.p.aux = 1;
            }
            left = rng;
            continue;
        }

        int next_min = is_right_assoc(op.type) ? prec : prec + 1;

        /*
         `expr |> rules*` — apply a rule set to a FIXPOINT (spec §16, §20).

         The trailing `*` is a SUFFIX on the pipeline's right operand, not a
         multiplication. It has to be handled before the operand is parsed:
         `parse_expr_prec` would otherwise read `a * <whatever follows>` as
         a product and consume the next line's first token, reporting
         "expected an expression" at end of file.

         So the right operand of a pipeline is parsed at UNARY precedence —
         high enough to take a name or a call, low enough to leave a
         following `*` alone — and the `*` is then claimed here.

         Recorded in `aux` rather than as a distinct node kind, so both
         spellings stay one N_EXPR_BINARY that existing consumers handle;
         aux == 1 means fixpoint.
        */
        int pipe_fix = 0;
        Node* right;
        if (op.type == Tk.TOKEN_PIPELINE)
        {
            right = p.parse_unary();
            if (p.check(Tk.TOKEN_STAR)) { p.advance(); pipe_fix = 1; }
        }
        else
        {
            right = p.parse_expr_prec(next_min);
        }

        Node* bin = p.mk_at(Nk.N_EXPR_BINARY, op);
        bin.p.aux = pipe_fix;
        bin.p.op = (int)op.type;
        p.add(bin, left);
        p.add(bin, right);
        left = bin;
    }
    p.leave();
    // Discard DEDENTs that merely close continuation INDENTs we absorbed.
    //
    // A wrapped condition is often indented DEEPER than the block it guards:
    //     else if a ||
    //             b ||
    //             c
    //       let x = ...
    // The lexer opens an INDENT for the continuation and then, at `let`,
    // dedents to a level that never appeared on its stack ("inconsistent
    // dedent"). Balancing our absorbed INDENTs here — and only ours — keeps
    // the lexer's indent stack and the parser's view in agreement.
    while (p.cont_indents > 0 && p.check(Tk.TOKEN_DEDENT))
    {
        p.advance();
        p.cont_indents = p.cont_indents - 1;
        // A continuation line indented to the SAME column the body will use
        // makes the lexer reuse that level: this DEDENT closes the
        // continuation, and no INDENT is emitted for the body that follows.
        //     if (a) ||
        //        (b)
        //       body        <- no INDENT here
        // Record it so parse_block_or_expr still reads a block.
        p.implicit_block = true;
    }
    // If the run ended without the matching DEDENTs (the next line dedents
    // past them in one step), drop the debt so a later block does not eat a
    // DEDENT that belongs to it.
    //
    // The DEDENT does not always come first: after a continuation whose last
    // token ends a line, the lexer emits DEDENT only once it has seen the
    // next line, so the immediate token is a NEWLINE. Dropping the debt on
    // sight of that NEWLINE left the continuation's INDENT unclosed, and the
    // statement after it was ejected from the enclosing block. Look past a
    // single NEWLINE before deciding the debt is unpayable.
    // If the run ended without the matching DEDENTs (the next line dedents
    // past them in one step), drop the debt so a later block does not eat a
    // DEDENT that belongs to it.
    //
    // This routine is RE-ENTRANT: a parenthesised operand runs it again from
    // inside the outer expression. Clearing the debt on that inner exit threw
    // away a continuation the OUTER expression had opened, so
    //     h = (a) +
    //         (b)
    // left its INDENT unclosed and the following statement was ejected from
    // the block. Only settle the debt when the parser is back at a position
    // where a statement could legally end: a closing bracket, an operator or
    // an `=` means an expression is still in progress.
    // A BINARY OPERATOR here means the chain continues onto yet another
    // line (`a +` / `b +` / `a`), so the statement has not ended and the
    // debt is still owed.
    Tk exit_tok = p.ct();
    bool mid_expr = exit_tok == Tk.TOKEN_RPAREN || exit_tok == Tk.TOKEN_RBRACK
                 || exit_tok == Tk.TOKEN_COMMA  || exit_tok == Tk.TOKEN_EQ
                 || infix_prec(exit_tok) > 0;
    if (!mid_expr && p.cont_indents > 0 && !p.check(Tk.TOKEN_DEDENT))
    {
        bool dedent_follows = p.check(Tk.TOKEN_NEWLINE)
                           && p.peek(1).type == Tk.TOKEN_DEDENT;
        if (!dedent_follows) { p.cont_indents = 0; }
    }
    return left;
}

fn bool tok_starts_expr(Tk t)
{
    switch (t)
    {
        case TOKEN_IDENT:
        case TOKEN_TYPEVAR:
        case TOKEN_WILDCARD:
        case TOKEN_LIT_INT:
        case TOKEN_LIT_FLOAT:
        case TOKEN_LIT_BOOL:
        case TOKEN_LIT_CHAR:
        case TOKEN_LIT_STRING:
        case TOKEN_LIT_RAW_BYTES:
        case TOKEN_LIT_NULL:
        case TOKEN_LPAREN:
        case TOKEN_LBRACK:
        case TOKEN_LBRACE:
        case TOKEN_MINUS:
        case TOKEN_BANG:
        case TOKEN_KW_NOT:
        case TOKEN_TILDE:
        case TOKEN_STAR:
        case TOKEN_AMP:
        case TOKEN_KW_IF:
        case TOKEN_KW_MATCH:
        case TOKEN_KW_WHILE:
        case TOKEN_KW_FOR:
        case TOKEN_KW_FN:
        case TOKEN_KW_ALLOC:
        case TOKEN_KW_FREE:
        case TOKEN_KW_SIZEOF:
        case TOKEN_KW_ALIGNOF:
        case TOKEN_KW_OFFSETOF:
        case TOKEN_KW_POISON:
        case TOKEN_KW_FREEZE:
        case TOKEN_KW_INVARIANT:
        case TOKEN_KW_TRANSMUTE:
        case TOKEN_KW_SYSCALL:
        case TOKEN_KW_UNSAFE:
        case TOKEN_KW_UNCHECKED:
        case TOKEN_KW_COMPTIME:
        case TOKEN_KW_HANDLE:
        case TOKEN_KW_SELF:
        case TOKEN_KW_ASSERT:
        case TOKEN_KW_ASSUME:
        case TOKEN_KW_UB_BANG:
        case TOKEN_KW_UNREACHABLE:
        case TOKEN_KW_TRAP:
        case TOKEN_KW_QUOTE:
        case TOKEN_KW_SPLICE:
        case TOKEN_KW_VOLATILE:
        case TOKEN_KW_FENCE:
        case TOKEN_KW_ATOMIC_ADD:
        case TOKEN_KW_ATOMIC_SUB:
        case TOKEN_KW_ATOMIC_AND:
        case TOKEN_KW_ATOMIC_OR:
        case TOKEN_KW_ATOMIC_XOR:
        case TOKEN_KW_ATOMIC_XCHG:
        case TOKEN_KW_ATOMIC_CMPXCHG:
        case TOKEN_KW_TAIL:
            return true;
        default:
            return false;
    }
}

/*
 Prefix operators (spec section 24, level 2).

 `¬` is the unicode spelling of `not`. The lexer has produced
 TOKEN_NEGATION since it was written, but the parser accepted it only in
 TYPE position (set-theoretic negation, `¬null`). In expression position
 it fell through to parse_postfix and reported "expected an expression",
 so `¬ p` was a parse error while `not p` worked. The spec lists both
 spellings of every unicode operator as equal; ≤ ≥ ≠ were wired up and
 this one was missed.
*/
fn Node* Parser.parse_unary(Parser* p)
{
    Tok t = p.cur();
    switch (t.type)
    {
        case TOKEN_MINUS:
        case TOKEN_BANG:
        case TOKEN_KW_NOT:
        case TOKEN_NEGATION:   // ¬ — the unicode spelling of `not`
        case TOKEN_TILDE:      // bitwise complement: ~(al - 1)
        {
            p.advance();
            Node* operand = p.parse_unary();
            Node* n = p.mk_at(Nk.N_EXPR_UNARY, t);
            n.p.op = (int)t.type;
            p.add(n, operand);
            return n;
        }
        case TOKEN_STAR:
        {
            p.advance();
            Node* operand = p.parse_unary();
            return p.arena.node1(Nk.N_EXPR_DEREF, operand, t.line, t.col);
        }
        case TOKEN_AMP:
        {
            p.advance();
            bool is_mut = p.accept(Tk.TOKEN_KW_MUT);
            Node* operand = p.parse_unary();
            Node* n = p.mk_at(Nk.N_EXPR_REF, t);
            if (is_mut) { n.flags = n.flags | pfront_core::NF_MUT; }
            p.add(n, operand);
            return n;
        }
        default:
            return p.parse_postfix();
    }
}

// A member name after `.` may be spelled with a token the lexer keywordised
// (`free`, `alloc`, `type`, `match`, ...). In member position those are plain
// identifiers, so the whole keyword range is admissible here.
fn bool tok_is_member_name(Tk t)
{
    if (t == Tk.TOKEN_IDENT || t == Tk.TOKEN_TYPEVAR) { return true; }
    if (t == Tk.TOKEN_KW_BY) { return true; }
    // The contiguous keyword block runs from TOKEN_KW_FN through the IRDL
    // group ending at TOKEN_KW_GRAPH (`node`, `opcode`, `block`, `edge`, ...).
    int v = (int)t;
    int lo = (int)Tk.TOKEN_KW_FN;
    int hi = (int)Tk.TOKEN_KW_GRAPH;
    return v >= lo && v <= hi;
}

fn Node* Parser.parse_postfix(Parser* p)
{
    Node* e = p.parse_primary();
    while (true)
    {
        Tk t = p.ct();
        if (t == Tk.TOKEN_LPAREN)
        {
            Tok lp = p.advance();
            Node* call = p.mk_at(Nk.N_EXPR_CALL, lp);
            p.add(call, e);
            p.skip_layout();
            while (!p.check(Tk.TOKEN_RPAREN) && !p.at_end())
            {
                p.add(call, p.parse_expr());
                p.skip_layout();
                if (!p.accept(Tk.TOKEN_COMMA)) { break; }
                p.skip_layout();
            }
            p.expect(Tk.TOKEN_RPAREN, 1030, "expected ')' to close call arguments");
            // A call is potentially effectful; the real effect set is computed
            // after resolution, but mark it so pure-expression checks are sound.
            call.effects = call.effects | pfront_core::EFF_IO;
            e = call;
        }
        else if (t == Tk.TOKEN_LBRACK)
        {
            Tok lb = p.advance();
            Node* idx = p.parse_expr();
            if (p.check(Tk.TOKEN_DOTDOT) || p.check(Tk.TOKEN_DOTDOTEQ))
            {
                Tok dd = p.advance();
                Node* sl = p.mk_at(Nk.N_EXPR_SLICE, lb);
                if (dd.type == Tk.TOKEN_DOTDOTEQ) { sl.flags = sl.flags | pfront_core::NF_INCLUSIVE; }
                p.add(sl, e);
                p.add(sl, idx);
                if (!p.check(Tk.TOKEN_RBRACK)) { p.add(sl, p.parse_expr()); }
                p.expect(Tk.TOKEN_RBRACK, 1031, "expected ']' to close slice");
                e = sl;
            }
            else
            {
                p.expect(Tk.TOKEN_RBRACK, 1031, "expected ']' to close index");
                Node* ix = p.mk_at(Nk.N_EXPR_INDEX, lb);
                p.add(ix, e);
                p.add(ix, idx);
                e = ix;
            }
        }
        else if (t == Tk.TOKEN_DOT || t == Tk.TOKEN_COLONCOLON)
        {
            Tok dot = p.advance();
            Tok nm = p.cur();
            if (nm.type == Tk.TOKEN_LIT_INT)
            {
                // tuple index: t.0
                p.advance();
                Node* fld = p.mk_at(Nk.N_EXPR_FIELD, dot);
                p.add(fld, e);
                fld.p.ival = parse_uint_literal(nm.start, nm.len);
                fld.p.aux = 1;   // numeric field
                e = fld;
                continue;
            }
            // After a dot, a keyword is just a member name: `os.linux.free`,
            // `mod.type`, `x.match`. Accept any word-shaped token here.
            if (!tok_is_member_name(nm.type))
            {
                p.err(1032, "expected a field or method name after '.'");
                break;
            }
            p.advance();
            if (p.check(Tk.TOKEN_LPAREN))
            {
                Tok lp = p.advance();
                Node* m = p.mk_at(Nk.N_EXPR_METHOD, dot);
                m.name_id = p.intern_tok(nm);
                m.p.sptr = nm.start;
                m.p.slen = nm.len;
                p.add(m, e);
                p.skip_layout();
                while (!p.check(Tk.TOKEN_RPAREN) && !p.at_end())
                {
                    p.add(m, p.parse_expr());
                    p.skip_layout();
                    if (!p.accept(Tk.TOKEN_COMMA)) { break; }
                    p.skip_layout();
                }
                p.expect(Tk.TOKEN_RPAREN, 1030, "expected ')' to close method arguments");
                m.effects = m.effects | pfront_core::EFF_IO;
                e = m;
            }
            else if (nm.type == Tk.TOKEN_TYPEVAR && p.check(Tk.TOKEN_LBRACE)
                     && !p.no_struct_lit)
            {
                // Qualified struct literal: `mmap.MmapRegion { ... }`.
                // A bare `Type { ... }` was handled in parse_primary, but a
                // dotted path arrives here instead, so the `{` was read as a
                // block and the whole initializer was lost.
                Node* tyname = p.mk_at(Nk.N_EXPR_IDENT, nm);
                tyname.name_id = p.intern_tok(nm);
                tyname.p.sptr = nm.start;
                tyname.p.slen = nm.len;
                Node* qual = p.mk_at(Nk.N_EXPR_FIELD, dot);
                qual.name_id = tyname.name_id;
                p.add(qual, e);
                Node* lit = p.parse_struct_literal(tyname, nm);
                // Remember the module qualifier so resolution can find the type.
                if (lit != null) { lit.type_slot = qual; }
                e = lit;
            }
            else
            {
                Node* fld = p.mk_at(Nk.N_EXPR_FIELD, dot);
                fld.name_id = p.intern_tok(nm);
                fld.p.sptr = nm.start;
                fld.p.slen = nm.len;
                p.add(fld, e);
                e = fld;
            }
        }
        else if (t == Tk.TOKEN_QUESTION)
        {
            Tok q = p.advance();
            Node* tr = p.mk_at(Nk.N_EXPR_TRY, q);
            p.add(tr, e);
            e = tr;
        }
        else { break; }
    }
    return e;
}

fn ulong parse_uint_literal(char* s, usz len)
{
    ulong v = 0;
    usz i = 0;
    int base = 10;
    if (len >= 2 && s[0] == '0')
    {
        char c = s[1];
        if (c == 'x' || c == 'X') { base = 16; i = 2; }
        else if (c == 'b' || c == 'B') { base = 2; i = 2; }
        else if (c == 'o' || c == 'O') { base = 8; i = 2; }
    }
    while (i < len)
    {
        char c = s[i];
        if (c == '_') { i = i + 1; continue; }
        int d = -1;
        if (c >= '0' && c <= '9') { d = (int)(c - '0'); }
        else if (c >= 'a' && c <= 'f') { d = (int)(c - 'a') + 10; }
        else if (c >= 'A' && c <= 'F') { d = (int)(c - 'A') + 10; }
        else { break; }   // a type suffix like i64/u8 begins here
        if (d >= base) { break; }
        v = v * (ulong)base + (ulong)d;
        i = i + 1;
    }
    return v;
}

fn double parse_float_literal(char* s, usz len)
{
    double whole = 0.0;
    usz i = 0;
    while (i < len && s[i] >= '0' && s[i] <= '9')
    {
        whole = whole * 10.0 + (double)(int)(s[i] - '0');
        i = i + 1;
    }
    if (i < len && s[i] == '.')
    {
        i = i + 1;
        double scale = 0.1;
        while (i < len && s[i] >= '0' && s[i] <= '9')
        {
            whole = whole + (double)(int)(s[i] - '0') * scale;
            scale = scale * 0.1;
            i = i + 1;
        }
    }
    if (i < len && (s[i] == 'e' || s[i] == 'E'))
    {
        i = i + 1;
        bool neg = false;
        if (i < len && (s[i] == '+' || s[i] == '-')) { neg = s[i] == '-'; i = i + 1; }
        int ex = 0;
        while (i < len && s[i] >= '0' && s[i] <= '9')
        {
            ex = ex * 10 + (int)(s[i] - '0');
            i = i + 1;
        }
        for (int k = 0; k < ex; k++)
        {
            if (neg) { whole = whole / 10.0; } else { whole = whole * 10.0; }
        }
    }
    return whole;
}

// Reads a trailing width suffix (i8/i16/i32/i64/u8/.../f32/f64) if present.
fn void read_num_suffix(char* s, usz len, char* out_width, bool* out_signed)
{
    *out_width = 0;
    *out_signed = true;
    usz i = 0;
    while (i < len)
    {
        char c = s[i];
        if (c == 'i' || c == 'u' || c == 'f')
        {
            // Only treat as a suffix when digits follow and we are past the mantissa.
            if (i + 1 < len && s[i + 1] >= '0' && s[i + 1] <= '9')
            {
                *out_signed = c != 'u';
                int w = 0;
                usz j = i + 1;
                while (j < len && s[j] >= '0' && s[j] <= '9')
                {
                    w = w * 10 + (int)(s[j] - '0');
                    j = j + 1;
                }
                *out_width = (char)w;
                return;
            }
        }
        i = i + 1;
    }
}

fn Node* Parser.parse_literal(Parser* p)
{
    Tok t = p.advance();
    switch (t.type)
    {
        case TOKEN_LIT_INT:
        {
            Node* n = p.mk_at(Nk.N_EXPR_INT, t);
            n.p.ival = parse_uint_literal(t.start, t.len);
            char w; bool sg;
            read_num_suffix(t.start, t.len, &w, &sg);
            n.p.width = w;
            n.p.is_signed = sg;
            n.p.sptr = t.start;
            n.p.slen = t.len;
            return n;
        }
        case TOKEN_LIT_FLOAT:
        {
            Node* n = p.mk_at(Nk.N_EXPR_FLOAT, t);
            n.p.fval = parse_float_literal(t.start, t.len);
            char w; bool sg;
            read_num_suffix(t.start, t.len, &w, &sg);
            n.p.width = w == 0 ? (char)64 : w;
            n.p.sptr = t.start;
            n.p.slen = t.len;
            return n;
        }
        case TOKEN_LIT_BOOL:
        {
            Node* n = p.mk_at(Nk.N_EXPR_BOOL, t);
            n.p.ival = (t.len == 4) ? 1 : 0;   // "true" is 4 chars, "false" is 5
            return n;
        }
        case TOKEN_LIT_CHAR:
        {
            Node* n = p.mk_at(Nk.N_EXPR_CHAR, t);
            n.p.sptr = t.start;
            n.p.slen = t.len;
            n.p.ival = t.len >= 3 ? (ulong)(char)t.start[1] : 0;
            return n;
        }
        case TOKEN_LIT_STRING:
        {
            Node* n = p.mk_at(Nk.N_EXPR_STRING, t);
            n.p.sptr = t.start;
            n.p.slen = t.len;
            return n;
        }
        case TOKEN_LIT_RAW_BYTES:
        {
            Node* n = p.mk_at(Nk.N_EXPR_BYTES, t);
            n.p.sptr = t.start;
            n.p.slen = t.len;
            return n;
        }
        case TOKEN_LIT_NULL:
            return p.mk_at(Nk.N_EXPR_NULL, t);
        default:
            p.err_at(1040, t.line, t.col, "expected a literal");
            return p.mk_error(t);
    }
}

fn Node* Parser.parse_primary(Parser* p)
{
    Tok t = p.cur();
    switch (t.type)
    {
        case TOKEN_LIT_INT:
        case TOKEN_LIT_FLOAT:
        case TOKEN_LIT_BOOL:
        case TOKEN_LIT_CHAR:
        case TOKEN_LIT_STRING:
        case TOKEN_LIT_RAW_BYTES:
        case TOKEN_LIT_NULL:
            return p.parse_literal();

        case TOKEN_KW_SELF:
            p.advance();
            return p.mk_at(Nk.N_EXPR_SELF, t);

        case TOKEN_WILDCARD:
            p.advance();
            return p.mk_at(Nk.N_EXPR_IDENT, t);

        case TOKEN_IDENT:
        {
            // Contextual effect keywords, recognised by shape rather than by
            // the lexer so `perform`/`resume` stay usable as variable names.
            if (p.at_perform()) { return p.parse_perform(); }
            if (p.at_resume())  { return p.parse_resume(); }
            p.advance();
            Node* id = p.mk_at(Nk.N_EXPR_IDENT, t);
            id.name_id = p.intern_tok(t);
            id.p.sptr = t.start;
            id.p.slen = t.len;
            /*
             STRUCT UPDATE SYNTAX, spec §9: `let v2 = v { x: 99.0 }`.

             Only the uppercase TOKEN_TYPEVAR arm checked for a following
             `{`, because a struct LITERAL is written with a type name.
             But an UPDATE is written with a lowercase VALUE, and it has
             the identical shape — so `v { x: 99.0 }` stopped at the brace
             and reported "expected an expression".

             Same node kind: an update is a literal whose base is a value
             rather than a type, and the resolver already tells them apart
             by what the head resolves to.
            */
            if (p.check(Tk.TOKEN_LBRACE) && !p.no_struct_lit)
            {
                return p.parse_struct_literal(id, t);
            }
            return id;
        }

        case TOKEN_TYPEVAR:
        {
            // Could be: Type { .. } literal, Enum.Variant, or a bare type name.
            p.advance();
            Node* id = p.mk_at(Nk.N_EXPR_IDENT, t);
            id.name_id = p.intern_tok(t);
            id.p.sptr = t.start;
            id.p.slen = t.len;
            if (p.check(Tk.TOKEN_LBRACE) && !p.no_struct_lit)
            {
                return p.parse_struct_literal(id, t);
            }
            return id;
        }

        case TOKEN_LPAREN:
        {
            p.advance();
            if (p.accept(Tk.TOKEN_RPAREN)) { return p.mk_at(Nk.N_EXPR_UNIT, t); }
            bool saved = p.no_struct_lit;
            p.no_struct_lit = false;
            p.skip_layout();
            Node* first = p.parse_expr();
            p.skip_layout();
            if (p.check(Tk.TOKEN_COMMA))
            {
                Node* tup = p.mk_at(Nk.N_EXPR_TUPLE, t);
                p.add(tup, first);
                while (p.accept(Tk.TOKEN_COMMA))
                {
                    p.skip_layout();
                    if (p.check(Tk.TOKEN_RPAREN)) { break; }
                    p.add(tup, p.parse_expr());
                    p.skip_layout();
                }
                p.expect(Tk.TOKEN_RPAREN, 1041, "expected ')' to close tuple");
                p.no_struct_lit = saved;
                return tup;
            }
            p.expect(Tk.TOKEN_RPAREN, 1041, "expected ')' after expression");
            p.no_struct_lit = saved;
            return first;
        }

        case TOKEN_LBRACK:
        {
            p.advance();
            Node* arr = p.mk_at(Nk.N_EXPR_ARRAY, t);
            bool saved = p.no_struct_lit;
            p.no_struct_lit = false;
            p.skip_layout();
            bool first_elem = true;
            while (!p.check(Tk.TOKEN_RBRACK) && !p.at_end())
            {
                Node* el = p.parse_expr();
                p.add(arr, el);
                p.skip_layout();
                // `[value; count]` — the array REPEAT form. `[0i64; 32]` is
                // thirty-two zeroes, not a one-element array. It is used
                // throughout the stdlib for fixed-size table initialisers,
                // and `alloc [C; n]` in v.md 6 is the same syntax.
                //
                // Only valid immediately after the first element; a second
                // `;` would be meaningless.
                if (first_elem && p.check(Tk.TOKEN_SEMI))
                {
                    p.advance();
                    p.skip_layout();
                    Node* count = p.parse_expr();
                    arr.kind = Nk.N_EXPR_ARRAY;
                    arr.p.aux = ARRAY_REPEAT;
                    if (count != null) { p.add(arr, count); }
                    p.skip_layout();
                    break;
                }
                first_elem = false;
                if (!p.accept(Tk.TOKEN_COMMA)) { break; }
                p.skip_layout();
            }
            p.expect(Tk.TOKEN_RBRACK, 1042, "expected ']' to close array literal");
            p.no_struct_lit = saved;
            return arr;
        }

        case TOKEN_KW_IF:      return p.parse_if();
        case TOKEN_KW_MATCH:   return p.parse_match();
        case TOKEN_KW_WHILE:   return p.parse_while();
        case TOKEN_KW_FOR:     return p.parse_for();
        case TOKEN_KW_REWRITE:
        {
            // `let arith : Rewrite = rewrite | x + 0 ↦ x` — a rule set as a
            // VALUE, per v.md §16. The declaration form (`rewrite name ...`)
            // was already handled at top level, but the expression form was
            // not, so every documented `let r : Rewrite = rewrite` example
            // failed with "expected an expression".
            //
            // Reuse the declaration parser: it already accepts both `↦` and
            // `->`, both braced and indented bodies, and the optional leading
            // bar. The result is an anonymous rule set.
            //
            // But `rewrite` is ALSO a module name in this stdlib
            // (`stdlib/pride/rewrite.pie`), so `rewrite.rule_new(l, r, p)`
            // is a qualified call, not a rule set. A following `.` or `(`
            // means it is being used as an ordinary name — the same
            // soft-keyword disambiguation `tail`, `handle` and `stage`
            // already do.
            //
            // Without this the receiver parsed as a bare `fn` node and
            // every call through the facade lowered to an unknown callee.
            Tk nxt = p.peek(1).type;
            if (nxt == Tk.TOKEN_DOT || nxt == Tk.TOKEN_LPAREN
                || nxt == Tk.TOKEN_COMMA || nxt == Tk.TOKEN_RPAREN)
            {
                Tok id_tok = p.advance();
                Node* id = p.mk_at(Nk.N_EXPR_IDENT, id_tok);
                id.name_id = p.intern_tok(id_tok);
                id.p.sptr = id_tok.start;
                id.p.slen = id_tok.len;
                return id;
            }
            return p.parse_rewrite_decl();
        }

        case TOKEN_KW_HANDLE:
        {
            // `handle` introduces an effect handler (`handle comp | E.op ...`)
            // but is also a common variable name — UEFI code passes `handle`
            // as an ordinary argument everywhere.
            //
            // A handler is always followed by something that starts a
            // computation. If the next token closes or separates the current
            // expression, `handle` is being used as a plain identifier.
            // Same disambiguation as TOKEN_KW_TAIL below.
            // An INFIX OPERATOR after `handle` means it was an operand, not a
            // handler head: `if handle == n then ...` is a comparison. The
            // original list enumerated only closers/separators, so a `handle`
            // on the LEFT of an operator still opened a handler and the rest
            // of the condition was consumed as its computation.
            Tk nx = p.peek(1).type;
            bool is_value = nx == Tk.TOKEN_RPAREN || nx == Tk.TOKEN_COMMA
                         || nx == Tk.TOKEN_RBRACK || nx == Tk.TOKEN_RBRACE
                         || nx == Tk.TOKEN_SEMI   || nx == Tk.TOKEN_NEWLINE
                         || nx == Tk.TOKEN_DEDENT || nx == Tk.TOKEN_EOF
                         || nx == Tk.TOKEN_COLON
                         || nx == Tk.TOKEN_EQ
                         || infix_prec(nx) > 0
                         // `if h == handle then ...` -- soft keyword, see tok_is_then.
                         || tok_is_then(p.peek(1));
            if (is_value)
            {
                p.advance();
                Node* id = p.mk_at(Nk.N_EXPR_IDENT, t);
                id.name_id = p.intern_tok(t);
                id.p.sptr = t.start;
                id.p.slen = t.len;
                return id;
            }
            return p.parse_handle();
        }
        case TOKEN_KW_ASM:     return p.parse_asm();
        case TOKEN_KW_STAGE:
        {
            // `stage N { ... }` is a staging block, but `stage` is also an
            // ordinary field and variable name — `CmttBox { stage: stage }`
            // uses it as both in one line. Disambiguate by lookahead, the
            // same rule as TOKEN_KW_TAIL and TOKEN_KW_HANDLE: a staging
            // block is followed by a level or a body, never by a token that
            // closes or separates the enclosing expression.
            if (!tok_starts_stage_body(p.peek(1).type))
            {
                p.advance();
                Node* id = p.mk_at(Nk.N_EXPR_IDENT, t);
                id.name_id = p.intern_tok(t);
                id.p.sptr = t.start;
                id.p.slen = t.len;
                return id;
            }
            // A bare `stage N` block: everything inside runs at that level.
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_QUOTE, t);
            if (p.check(Tk.TOKEN_LIT_INT))
            {
                Tok lv = p.advance();
                n.p.aux = (int)parse_uint_literal(lv.start, lv.len);
            }
            p.add(n, p.parse_block_or_expr());
            return n;
        }

        case TOKEN_KW_FN:      return p.parse_lambda();

        case TOKEN_KW_ALLOC:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_ALLOC, t);
            n.effects = n.effects | pfront_core::EFF_ALLOC;
            if (p.check(Tk.TOKEN_LBRACK))
            {
                n.type_ann = p.parse_type();
            }
            else
            {
                p.add(n, p.parse_unary());
            }
            return n;
        }

        case TOKEN_KW_FREE:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_FREE, t);
            n.effects = n.effects | pfront_core::EFF_ALLOC;
            p.add(n, p.parse_unary());
            return n;
        }

        case TOKEN_KW_SIZEOF:
        case TOKEN_KW_ALIGNOF:
        {
            p.advance();
            Nk k = t.type == Tk.TOKEN_KW_SIZEOF ? Nk.N_EXPR_SIZEOF : Nk.N_EXPR_ALIGNOF;
            Node* n = p.mk_at(k, t);
            bool paren = p.accept(Tk.TOKEN_LPAREN);
            n.type_ann = p.parse_type();
            if (paren) { p.expect(Tk.TOKEN_RPAREN, 1043, "expected ')' after type operand"); }
            return n;
        }

        case TOKEN_KW_POISON:
        {
            /*
             `poison` — a value that propagates UB if used (spec §14).
             No parse rule existed, so it fell through to the identifier
             path and came out as an unresolved name.

             Nullary: it takes no operand. NOT N_EXPR_UB — that is `ub!`,
             which requires an enclosing `unsafe`; `poison` does not.
            */
            p.advance();
            return p.mk_at(Nk.N_EXPR_POISON, t);
        }

        case TOKEN_KW_FREEZE:
        {
            // `freeze n` — stops UB propagation from a poison value (§14).
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_ASSUME, t);
            n.p.aux = 1;          // 1 = freeze, distinct from a bare assume
            p.add(n, p.parse_unary());
            return n;
        }

        case TOKEN_KW_INVARIANT:
        {
            // `invariant cond` — an optimiser hint like `assume`, but
            // asserted to hold at every iteration rather than once (§14).
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_ASSUME, t);
            n.p.aux = 2;          // 2 = invariant
            p.add(n, p.parse_expr());
            return n;
        }

        case TOKEN_KW_OFFSETOF:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_OFFSETOF, t);
            p.expect(Tk.TOKEN_LPAREN, 1043, "expected '(' after offset_of");
            n.type_ann = p.parse_type();
            p.expect(Tk.TOKEN_COMMA, 1043, "expected ',' in offset_of");
            Tok f = p.cur();
            if (p.expect(Tk.TOKEN_IDENT, 1043, "expected a field name in offset_of"))
            {
                n.name_id = p.interner.intern(f.start, f.len);
                n.p.sptr = f.start;
                n.p.slen = f.len;
            }
            p.expect(Tk.TOKEN_RPAREN, 1043, "expected ')' after offset_of");
            return n;
        }

        case TOKEN_KW_TRANSMUTE:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_TRANSMUTE, t);
            n.effects = n.effects | pfront_core::EFF_UNSAFE;
            p.expect(Tk.TOKEN_LPAREN, 1044, "expected '(' after transmute");
            p.add(n, p.parse_expr());
            if (p.accept(Tk.TOKEN_COMMA)) { n.type_ann = p.parse_type(); }
            p.expect(Tk.TOKEN_RPAREN, 1044, "expected ')' after transmute");
            return n;
        }

        case TOKEN_KW_SYSCALL:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_SYSCALL, t);
            n.effects = n.effects | pfront_core::EFF_UNSAFE | pfront_core::EFF_IO;
            p.expect(Tk.TOKEN_LPAREN, 1045, "expected '(' after syscall");
            while (!p.check(Tk.TOKEN_RPAREN) && !p.at_end())
            {
                p.add(n, p.parse_expr());
                if (!p.accept(Tk.TOKEN_COMMA)) { break; }
            }
            p.expect(Tk.TOKEN_RPAREN, 1045, "expected ')' to close syscall");
            return n;
        }

        case TOKEN_KW_UNSAFE:
        case TOKEN_KW_UNCHECKED:
        {
            p.advance();
            Nk k = t.type == Tk.TOKEN_KW_UNSAFE ? Nk.N_EXPR_UNSAFE : Nk.N_EXPR_UNCHECKED;
            Node* n = p.mk_at(k, t);
            if (t.type == Tk.TOKEN_KW_UNSAFE) { n.effects = n.effects | pfront_core::EFF_UNSAFE; }
            p.add(n, p.parse_block_or_expr());
            return n;
        }

        case TOKEN_KW_COMPTIME:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_COMPTIME, t);
            // An inline `comptime e` takes a single expression. Routing it
            // through parse_block_or_expr let the virtual-block heuristic
            // absorb the FOLLOWING statement, so `let x = comptime 3 * 4`
            // swallowed the next line and then failed to evaluate.
            if (p.check(Tk.TOKEN_INDENT) || p.check(Tk.TOKEN_LBRACE))
            {
                p.add(n, p.parse_block_or_expr());
            }
            else
            {
                bool sv = p.in_fn_sig;
                p.in_fn_sig = true;
                p.add(n, p.parse_expr());
                p.in_fn_sig = sv;
            }
            return n;
        }

        case TOKEN_KW_ASSERT:
        case TOKEN_KW_ASSUME:
        {
            p.advance();
            Nk k = t.type == Tk.TOKEN_KW_ASSERT ? Nk.N_EXPR_ASSERT : Nk.N_EXPR_ASSUME;
            Node* n = p.mk_at(k, t);
            if (k == Nk.N_EXPR_ASSERT) { n.effects = n.effects | pfront_core::EFF_PANIC; }
            bool paren = p.accept(Tk.TOKEN_LPAREN);
            p.add(n, p.parse_expr());
            if (paren)
            {
                if (p.accept(Tk.TOKEN_COMMA)) { p.add(n, p.parse_expr()); }
                p.expect(Tk.TOKEN_RPAREN, 1046, "expected ')' after assertion");
            }
            return n;
        }

        case TOKEN_KW_UB_BANG:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_UB, t);
            n.effects = n.effects | pfront_core::EFF_UB;
            if (p.check(Tk.TOKEN_LIT_STRING)) { p.add(n, p.parse_literal()); }
            return n;
        }

        case TOKEN_KW_UNREACHABLE:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_UNREACHABLE, t);
            n.effects = n.effects | pfront_core::EFF_DIVERGE;
            if (p.accept(Tk.TOKEN_LPAREN)) { p.expect(Tk.TOKEN_RPAREN, 1047, "expected ')'"); }
            return n;
        }

        case TOKEN_KW_TRAP:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_TRAP, t);
            n.effects = n.effects | pfront_core::EFF_DIVERGE;
            if (p.accept(Tk.TOKEN_LPAREN)) { p.expect(Tk.TOKEN_RPAREN, 1047, "expected ')'"); }
            return n;
        }

        case TOKEN_KW_VOLATILE:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_VOLATILE, t);
            n.effects = n.effects | pfront_core::EFF_IO;
            p.add(n, p.parse_unary());
            return n;
        }

        case TOKEN_KW_FENCE:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_FENCE, t);
            n.effects = n.effects | pfront_core::EFF_IO;
            if (p.accept(Tk.TOKEN_LPAREN))
            {
                if (!p.check(Tk.TOKEN_RPAREN)) { p.add(n, p.parse_expr()); }
                p.expect(Tk.TOKEN_RPAREN, 1048, "expected ')' after fence");
            }
            return n;
        }

        case TOKEN_KW_ATOMIC_ADD:
        case TOKEN_KW_ATOMIC_SUB:
        case TOKEN_KW_ATOMIC_AND:
        case TOKEN_KW_ATOMIC_OR:
        case TOKEN_KW_ATOMIC_XOR:
        case TOKEN_KW_ATOMIC_XCHG:
        case TOKEN_KW_ATOMIC_CMPXCHG:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_ATOMIC, t);
            n.p.op = (int)t.type;
            n.effects = n.effects | pfront_core::EFF_IO;
            p.expect(Tk.TOKEN_LPAREN, 1049, "expected '(' after atomic operation");
            while (!p.check(Tk.TOKEN_RPAREN) && !p.at_end())
            {
                p.add(n, p.parse_expr());
                if (!p.accept(Tk.TOKEN_COMMA)) { break; }
            }
            p.expect(Tk.TOKEN_RPAREN, 1049, "expected ')' to close atomic operation");
            return n;
        }

        case TOKEN_KW_REIFY:
        case TOKEN_KW_EVAL:
        {
            /*
             `reify e` and `eval e` — MSP operators (spec §20's keyword
             list) with no parse rule at all. They fell through to the
             identifier path, so `let r = reify x` bound `r` to a bare name
             `reify` and left `x` dangling as a separate statement. The
             error surfaced as "unresolved name" on a keyword, which is
             about as misleading as a diagnostic gets.

             They are prefix operators over one expression, like `splice`
             and `unquote` beside them. Both are stage-neutral: `reify`
             turns a value into its representation, `eval` runs a
             representation — neither defers to a later stage, so they must
             NOT be modelled as quotation.
            */
            p.advance();
            Node* n = p.mk_at(t.type == Tk.TOKEN_KW_REIFY
                              ? Nk.N_EXPR_REIFY : Nk.N_EXPR_EVAL, t);
            p.add(n, p.parse_unary());
            return n;
        }

        case TOKEN_KW_QUOTE:
        case TOKEN_SIGIL_TREE:
        case TOKEN_SIGIL_DATA:
        case TOKEN_SIGIL_BYTES:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_QUOTE, t);
            n.p.op = (int)t.type;
            // `box[Γ] e` — the contextual environment that makes a cross-stage
            // reference sound. Recording it is what distinguishes CMTT from
            // plain quotation.
            if (p.check(Tk.TOKEN_LBRACK))
            {
                p.advance();
                Node* env = p.mk_at(Nk.N_TY_EFFECT_ROW, t);
                env.p.aux = 2;   // marks a box environment rather than an effect row
                while (!p.check(Tk.TOKEN_RBRACK) && !p.at_end())
                {
                    Tok v = p.cur();
                    if (!tok_is_member_name(v.type)) { break; }
                    p.advance();
                    Node* b = p.mk_at(Nk.N_EXPR_IDENT, v);
                    b.name_id = p.intern_tok(v);
                    b.p.sptr = v.start;
                    b.p.slen = v.len;
                    p.add(env, b);
                    if (!p.accept(Tk.TOKEN_COMMA)) { break; }
                }
                p.expect(Tk.TOKEN_RBRACK, 1250, "expected ']' to close a box environment");
                p.add(n, env);
            }
            p.add(n, p.parse_block_or_expr());
            // A trailing `at Stage L` fixes the fragment's target stage.
            if (p.at_stage_keyword()) { n.p.aux = p.parse_stage_offset(); }
            return n;
        }

        case TOKEN_KW_SPLICE:
        case TOKEN_KW_UNQUOTE:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_EXPR_SPLICE, t);
            p.add(n, p.parse_unary());
            return n;
        }

        case TOKEN_KW_TAIL:
        {
            // `tail` is BOTH a tail-call annotation (`tail f(x)`) and one of
            // the most common variable names in real code (`let tail = ...`
            // appears in every ring buffer and deque in the stdlib).
            //
            // Disambiguate by lookahead rather than by reserving the word.
            // As an ANNOTATION it must be followed by something that can
            // start a call expression. Anything else — an operator, a
            // closing bracket, a comma, a line break — means it is being
            // used as an ordinary identifier.
            //
            // Getting this wrong swallowed the following token and produced
            // "expected an expression" at a completely unrelated position,
            // which then cascaded into a wave of bogus "unresolved name"
            // errors for every later binding in the file.
            // `then` is a SOFT keyword lexed as an ordinary identifier, so it
            // must NOT count as the start of a callee. `if head == tail then
            // ...` otherwise reads `tail then` as a tail call and steals the
            // `then` that ends the condition.
            Tk nx = p.peek(1).type;
            bool annotation = ((nx == Tk.TOKEN_IDENT && !tok_is_then(p.peek(1)))
                               || nx == Tk.TOKEN_KW_SELF);
            if (annotation)
            {
                p.advance();
                Node* inner = p.parse_postfix();
                if (inner != null) { inner.flags = inner.flags | pfront_core::NF_TAIL; }
                return inner;
            }
            p.advance();
            Node* id = p.mk_at(Nk.N_EXPR_IDENT, t);
            id.name_id = p.intern_tok(t);
            id.p.sptr = t.start;
            id.p.slen = t.len;
            return id;
        }

        case TOKEN_LBRACE:
            return p.parse_brace_block();

        default:
        {
            // Same contextual-keyword rule as patterns: `node`, `opcode`,
            // `block` etc. are ordinary variable names in most real code.
            if (tok_is_member_name(t.type))
            {
                p.advance();
                Node* id = p.mk_at(Nk.N_EXPR_IDENT, t);
                id.name_id = p.intern_tok(t);
                id.p.sptr = t.start;
                id.p.slen = t.len;
                return id;
            }
            p.err(1050, "expected an expression");
            p.advance();
            return p.mk_error(t);
        }
    }
}

fn Node* Parser.parse_struct_literal(Parser* p, Node* name, Tok t)
{
    p.advance();   // consume '{'
    Node* lit = p.mk_at(Nk.N_EXPR_STRUCT_LIT, t);
    lit.name_id = name.name_id;
    p.add(lit, name);
    p.skip_layout();
    while (!p.check(Tk.TOKEN_RBRACE) && !p.at_end())
    {
        Tok fname = p.cur();
        // Field names may be spelled with a keywordised token (`region`,
        // `block`, `node`, `type` ...). In field position they are plain
        // identifiers, exactly as in struct DECLARATIONS and member access.
        if (!tok_is_member_name(fname.type))
        {
            p.err(1051, "expected a field name in struct literal");
            break;
        }
        p.advance();
        Node* fi = p.mk_at(Nk.N_EXPR_FIELD_INIT, fname);
        fi.name_id = p.intern_tok(fname);
        fi.p.sptr = fname.start;
        fi.p.slen = fname.len;
        if (p.accept(Tk.TOKEN_COLON) || p.accept(Tk.TOKEN_EQ))
        {
            p.add(fi, p.parse_expr());
        }
        else
        {
            // shorthand `{ x }`
            Node* id = p.mk_at(Nk.N_EXPR_IDENT, fname);
            id.name_id = fi.name_id;
            id.p.sptr = fname.start;
            id.p.slen = fname.len;
            p.add(fi, id);
        }
        p.add(lit, fi);
        p.skip_layout();
        if (!p.accept(Tk.TOKEN_COMMA)) { break; }
        p.skip_layout();
    }
    p.skip_layout();
    p.expect(Tk.TOKEN_RBRACE, 1052, "expected '}' to close struct literal");
    return lit;
}

// ── Control-flow expressions ────────────────────────────────────────────────
fn Node* Parser.parse_if(Parser* p)
{
    Tok t = p.advance();   // if
    Node* n = p.mk_at(Nk.N_EXPR_IF, t);
    bool saved = p.no_struct_lit;
    p.no_struct_lit = true;
    Node* cond = p.parse_expr();
    p.no_struct_lit = saved;
    p.settle_continuation();
    p.add(n, cond);
    // Pride supports both the layout form (`if c` + indented block) and the
    // inline ML form (`if c then a else b`). `then` is lexed as an identifier.
    bool has_then = false;
    if (p.at_then()) { p.advance(); has_then = true; }
    if (has_then)
    {
        // `then` may be followed inline by the value, or by a line break and
        // an indented block:
        //     let t = if flag then
        //               "a"
        //             else
        //               "b"
        // Count the INDENTs each branch opens so exactly those, and no more,
        // are closed at the end. `cont_indents` is the parser-wide tally that
        // parse_arm_body feeds through parse_indented_block.
        int before_then = p.deferred_dedents;
        p.add(n, p.parse_arm_body());
        // `else` may sit at a shallower indent than the then-value, leaving a
        // run of DEDENT/NEWLINE before it. Only consume that run when an `else`
        // actually follows, so we never eat an enclosing block's close.
        if (p.layout_then(Tk.TOKEN_KW_ELSE)) { p.eat_layout_run(); }
        if (p.accept(Tk.TOKEN_KW_ELSE))
        {
            if (p.check(Tk.TOKEN_KW_IF)) { p.add(n, p.parse_if()); }
            else { p.add(n, p.parse_arm_body()); }
        }
        p.deferred_dedents = before_then;
        // Close every level this conditional's branches left open, and no
        // more. The rule is columnar: a DEDENT landing at a column still
        // DEEPER than the `if` keyword closes a branch block; the first one at
        // or above `if`'s own column belongs to the enclosing construct.
        //
        // Getting this wrong is silent and severe in BOTH directions:
        // over-consuming nests the following statement inside the initializer,
        // under-consuming ejects it from the enclosing block. Both were
        // observed with the earlier count-based heuristics, and both surface
        // only as "unresolved name" far from the real cause.
        // Each DEDENT carries (in `len`) the indent level it closes; every
        // DEDENT in a run reports the same target column, so the level is the
        // only usable discriminator.
        //
        // Close levels strictly DEEPER than the statement this conditional
        // belongs to. `stmt_indent` is the indent of the enclosing block, so
        // its own level survives for the block to consume:
        //
        //   let t = if c then      stmt_indent=4  if at col 13
        //             1            branch level 14  -> close
        //           else
        //             2            branch level 12  -> close (12 > 4)
        //   t                      level 4 belongs to the block -> keep
        //
        //   let q : i64 =          stmt_indent=4  if at col 7
        //     if c then            branch level 8  -> close
        //       1
        //     else
        //       2                  level 6 is the initializer block
        //   let vr = ...           -> keep, else `vr` nests inside `q`
        //
        // Using the `if` column instead was wrong in the second case; using a
        // fixed count was wrong in the first. Both failures are silent and
        // surface only as "unresolved name" far from the cause.
        int keep_level = p.stmt_indent;
        while (p.check(Tk.TOKEN_DEDENT) && (int)p.cur().len > keep_level)
        {
            // Never close past the initializer block that owns this statement.
            if (p.init_block_level > 0 && (int)p.cur().len <= p.init_block_level) { break; }
            p.advance();
        }
        return n;
    }
    p.add(n, p.parse_block_or_expr());
    // `else` normally sits on its own line, so an arbitrary run of DEDENT and
    // NEWLINE separates it from the then-branch. A fixed 2-token peek missed
    // deeply nested cases (`if` inside `if` inside a clause), which showed up
    // as "expected an expression" on the `else` line. Scan the whole run.
    if (p.check(Tk.TOKEN_NEWLINE) || p.check(Tk.TOKEN_DEDENT))
    {
        if (p.layout_then(Tk.TOKEN_KW_ELSE))
        {
            while (p.check(Tk.TOKEN_NEWLINE) || p.check(Tk.TOKEN_DEDENT))
            {
                if (p.check(Tk.TOKEN_DEDENT) && p.peek(1).type == Tk.TOKEN_KW_ELSE)
                {
                    p.advance();
                    break;
                }
                p.advance();
            }
        }
    }
    if (p.accept(Tk.TOKEN_KW_ELSE))
    {
        // An INLINE else body leaves this branch's DEDENT unconsumed; a
        // block body consumes its own. Track which happened so only the
        // inline case tries to close the leftover levels.
        bool inline_else = !p.check(Tk.TOKEN_INDENT) && !p.check(Tk.TOKEN_LBRACE)
                        && !p.check(Tk.TOKEN_NEWLINE);
        if (p.check(Tk.TOKEN_KW_IF))
        {
            p.add(n, p.parse_if());
            inline_else = false;
        }
        else
        {
            p.add(n, p.parse_block_or_expr());
        }

        // Close the layout levels this `else` branch opened, but only down to
        // the level of the statement that owns this `if`.
        //
        // An INLINE else body (`else 2i64`) leaves the branch's DEDENT
        // unconsumed, because parse_block_or_expr took the single-expression
        // path and never entered a block. For a NESTED if that is fatal:
        //
        //     if p > 1
        //       if p > 2
        //         1
        //       else 2      <- inline; DEDENT for the inner block still queued
        //     else 3        <- outer else never seen; parsed as an IDENT
        //                      inside the inner if's block
        //
        // The symptom is a bogus "unresolved name 'else'" far from the cause.
        //
        // Close only levels strictly DEEPER than this `if`'s own column, and
        // only when an `else` is what follows — otherwise a DEDENT that ends
        // the enclosing block would be eaten and the block's next sibling
        // would nest inside it.
        //
        // `t.col - 1` is this `if`'s level; `DEDENT.len` is the column the
        // DEDENT closes to. For the case above the inner `if` sits at col 7
        // (level 6) and the queued DEDENT has len 6, so it closes exactly to
        // the outer `else` — which is why comparing against `stmt_indent`
        // (also 6) was one level too shallow to fire.
        if (inline_else)
        {
            int if_level = t.col - 1;
            while ((p.check(Tk.TOKEN_DEDENT) || p.check(Tk.TOKEN_NEWLINE))
                   && p.layout_then(Tk.TOKEN_KW_ELSE))
            {
                if (p.check(Tk.TOKEN_DEDENT))
                {
                    if ((int)p.cur().len < if_level) { break; }
                    if (p.init_block_level > 0
                        && (int)p.cur().len <= p.init_block_level) { break; }
                }
                p.advance();
            }
        }
    }
    return n;
}

// `then` is not a lexer keyword — it arrives as an ordinary identifier so it
// stays usable as a variable name. Both `if c then a` and
// `while c then body` need to recognise it, so the spelling check lives here
// rather than being duplicated at each site.
// Does this token begin the body of a `stage` block? A staging block is
// `stage <level> <body>` or `stage <body>`; anything that closes or separates
// an expression means `stage` was being used as an ordinary name.
fn bool tok_starts_stage_body(Tk t)
{
    return t == Tk.TOKEN_LIT_INT
        || t == Tk.TOKEN_LBRACE
        || t == Tk.TOKEN_INDENT;
}

fn bool Parser.at_then(Parser* p)
{
    return tok_is_then(p.cur());
}

// `then` is a SOFT keyword: the lexer hands it over as a plain TOKEN_IDENT so
// it stays usable as a variable name. Every lookahead that asks "does an
// identifier follow?" must therefore exclude it, or a soft-keyword construct
// will swallow the `then` that ends its own head.
//
// This bit the `tail` disambiguation in stdlib/os/linux/io_uring.pie:300:
//     if head == tail then 0 as *IoUringCqe
// `tail` saw IDENT(`then`) next, concluded it was a tail-call annotation
// (`tail f(x)`), consumed `then` as the callee, and the `if` lost its body.
// The error surfaced as "unresolved name 'then'" with no hint of the cause.
fn bool tok_is_then(Tok c)
{
    if (c.type != Tk.TOKEN_IDENT) { return false; }
    if (c.len != 4) { return false; }
    return c.start[0] == 't' && c.start[1] == 'h'
        && c.start[2] == 'e' && c.start[3] == 'n';
}

fn Node* Parser.parse_while(Parser* p)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_EXPR_WHILE, t);
    bool saved = p.no_struct_lit;
    p.no_struct_lit = true;
    p.add(n, p.parse_expr());
    p.no_struct_lit = saved;
    p.settle_continuation();
    // `while cond do { ... }` — the optional `do` keyword introduces the body.
    // Without consuming it the condition parser stopped at `do` and the body
    // was dropped, which silently truncated every such loop in the stdlib.
    //
    // `then` is accepted in the same position. The stdlib writes both, and a
    // single-line loop reads naturally either way:
    //     while (path as *u16)[n as i64] != 0u16 then n = n + 1u16
    if (!p.accept(Tk.TOKEN_KW_DO)) { if (p.at_then()) { p.advance(); } }
    p.add(n, p.parse_block_or_expr());
    return n;
}

fn Node* Parser.parse_for(Parser* p)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_EXPR_FOR, t);
    Node* pat = p.parse_pattern();
    p.add(n, pat);
    if (!p.expect(Tk.TOKEN_KW_IN, 1060, "expected 'in' in a for loop")) { return n; }
    bool saved = p.no_struct_lit;
    p.no_struct_lit = true;
    p.add(n, p.parse_expr());
    p.no_struct_lit = saved;
    p.accept(Tk.TOKEN_KW_DO);
    p.add(n, p.parse_block_or_expr());
    return n;
}


/*
 Does this token begin a DECLARATION? Used to stop constructs that scan
 forward (match arms, clause lists) from running past the end of the
 enclosing item into the next one.
*/
fn bool tok_starts_decl(Tk t)
{
    switch (t)
    {
        case TOKEN_KW_FN:
        case TOKEN_KW_TYPE:
        case TOKEN_KW_STRUCT:
        case TOKEN_KW_UNION:
        case TOKEN_KW_ENUM:
        case TOKEN_KW_EFFECT:
        case TOKEN_KW_INTERFACE:
        case TOKEN_KW_IMPL:
        case TOKEN_KW_EXTERN:
        case TOKEN_KW_CONST:
        case TOKEN_KW_STATIC:
        case TOKEN_KW_USE:
        case TOKEN_KW_MOD:
            return true;
        default:
            return false;
    }
}

fn Node* Parser.parse_match(Parser* p)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_EXPR_MATCH, t);
    bool saved = p.no_struct_lit;
    bool saved_sig = p.in_fn_sig;
    p.no_struct_lit = true;
    // `match o | Some(_) -> ...` puts the scrutinee immediately before a `|`
    // that introduces an arm, not a bitwise-or. Parsing the scrutinee at a
    // precedence above `|` stops the Pratt loop from swallowing the arm bar.
    p.in_fn_sig = true;
    p.add(n, p.parse_expr_prec(7));
    // Clear the guard for the ARMS: a `match` nested in a clause body inherits
    // in_fn_sig=true from parse_arm_body, which would block its own arm bars.
    p.in_fn_sig = false;
    p.no_struct_lit = saved;
    p.skip_layout();
    bool braced = p.accept(Tk.TOKEN_LBRACE);
    p.skip_layout();
    bool indented = p.accept(Tk.TOKEN_INDENT);
    p.skip_newlines();
    while (true)
    {
        // Arms may be separated by layout: allow NEWLINE/INDENT before a bar.
        if (!p.check(Tk.TOKEN_PIPE))
        {
            usz look = 0;
            bool found = false;
            while (look < 3)
            {
                Tk lt = p.peek(look).type;
                /*
                 DEDENT is NOT skipped here. It closes the block the match
                 lives in, so a `|` found past it belongs to something
                 else — and the scan below would walk out of the match to
                 reach it.

                 Without this, a top-level `fn g` written after a match
                 was swallowed INTO the match's last arm: the scan crossed
                 the DEDENT looking for the next bar, found the `|` of
                 `g`'s own clause, and kept going. `fn g` then appeared
                 nested inside `fn f` in the AST, with no diagnostic.
                 Reproduced with two functions where the first ends in a
                 match; verified by the AST dump showing `fn 'g'` at depth
                 8 instead of depth 2.
                */
                if (lt == Tk.TOKEN_NEWLINE || lt == Tk.TOKEN_INDENT) { look = look + 1; continue; }
                if (lt == Tk.TOKEN_PIPE) { found = true; }
                break;
            }
            if (!found) { break; }
            /*
             Advance to that bar, but never across a DEDENT or a
             declaration keyword: both mean the match has ended and the
             bar belongs to the next construct.
            */
            while (!p.check(Tk.TOKEN_PIPE) && !p.at_end())
            {
                if (p.check(Tk.TOKEN_DEDENT)) { break; }
                if (tok_starts_decl(p.ct())) { break; }
                p.advance();
            }
            if (!p.check(Tk.TOKEN_PIPE)) { break; }
        }
        Tok bar = p.advance();
        Node* arm = p.mk_at(Nk.N_MATCH_ARM, bar);
        bool sv = p.in_fn_sig;
        p.in_fn_sig = false;
        p.add(arm, p.parse_pattern());
        p.in_fn_sig = sv;
        if (p.check(Tk.TOKEN_KW_IF))
        {
            Tok g = p.advance();
            Node* guard = p.mk_at(Nk.N_GUARD, g);
            p.add(guard, p.parse_expr());
            p.add(arm, guard);
        }
        if (!p.accept(Tk.TOKEN_ARROW) && !p.accept(Tk.TOKEN_ARROW_ASCII))
        {
            p.err(1061, "expected '->' after a match pattern");
            p.sync();
            p.add(n, arm);
            continue;
        }
        p.add(arm, p.parse_arm_body());
        p.add(n, arm);
        /*
         Skip only NEWLINEs between arms, never a DEDENT.

         skip_layout() here ate the DEDENT that closes the match's own
         block, so the arm loop carried on into whatever followed. A
         top-level `fn g` written after a match ended up nested inside the
         previous function, silently and with no diagnostic — the AST dump
         showed `fn 'g'` at depth 8 instead of 2.

         The closing DEDENT is consumed below, once, by the `indented`
         branch that owns it.
        */
        p.skip_newlines();
    }
    if (indented) { while (p.accept(Tk.TOKEN_DEDENT)) {} }
    if (braced) { p.skip_layout(); p.expect(Tk.TOKEN_RBRACE, 1062, "expected '}' to close match"); }
    if (n.child_count < 2)
    {
        p.err_at(1063, t.line, t.col, "match expression has no arms");
    }
    // Restore the caller's bar-handling mode now that our arms are consumed.
    p.in_fn_sig = saved_sig;
    return n;
}

fn Node* Parser.parse_handle(Parser* p)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_EXPR_HANDLE, t);
    p.add(n, p.parse_block_or_expr());
    p.skip_layout();
    while (p.check(Tk.TOKEN_PIPE))
    {
        Tok bar = p.advance();
        Node* arm = p.mk_at(Nk.N_HANDLER_ARM, bar);
        // Effect.op args -> body
        Tok en = p.cur();
        if (en.type == Tk.TOKEN_IDENT || en.type == Tk.TOKEN_TYPEVAR)
        {
            Node* path = p.parse_pattern_path();
            arm.name_id = path.name_id;
            p.add(arm, path);
        }
        // argument binders up to the arrow
        while (!p.check(Tk.TOKEN_ARROW) && !p.check(Tk.TOKEN_ARROW_ASCII)
            && !p.at_end() && !p.check(Tk.TOKEN_NEWLINE))
        {
            p.add(arm, p.parse_pattern_atom());
        }
        if (!p.accept(Tk.TOKEN_ARROW) && !p.accept(Tk.TOKEN_ARROW_ASCII))
        {
            p.err(1064, "expected '->' in a handler arm");
            p.sync();
            p.add(n, arm);
            continue;
        }
        p.add(arm, p.parse_arm_body());
        p.add(n, arm);

        // Look for the next arm WITHOUT consuming the layout that ends the
        // handler.
        //
        // `skip_layout` eats DEDENTs, so after the final arm it walked out of
        // the handler's block and kept scanning for `|`. Any following
        // top-level declaration was then parsed as part of this expression:
        //
        //     handle ...
        //     | A.g () k -> resume s
        //
        //     effect B              <- swallowed; "expected an expression"
        //       h : i64 -> i64
        //
        // Only advance if a `|` really is next in the layout run, and require
        // it to be indented at least as far as the first arm — a bar at a
        // shallower column belongs to an enclosing construct.
        if (!p.layout_then(Tk.TOKEN_PIPE)) { break; }
        usz look = 0;
        while (look + 1 < LA_SIZE)
        {
            Tk lt = p.peek(look).type;
            if (lt == Tk.TOKEN_NEWLINE || lt == Tk.TOKEN_INDENT
                || lt == Tk.TOKEN_DEDENT)
            {
                look = look + 1;
                continue;
            }
            break;
        }
        if (p.peek(look).col < bar.col) { break; }
        p.skip_layout();
    }
    return n;
}

fn Node* Parser.parse_lambda(Parser* p)
{
    Tok t = p.advance();   // fn
    Node* n = p.mk_at(Nk.N_EXPR_LAMBDA, t);
    if (p.accept(Tk.TOKEN_LPAREN))
    {
        while (!p.check(Tk.TOKEN_RPAREN) && !p.at_end())
        {
            Node* prm = p.parse_param();
            p.add(n, prm);
            if (!p.accept(Tk.TOKEN_COMMA)) { break; }
        }
        p.expect(Tk.TOKEN_RPAREN, 1065, "expected ')' to close lambda parameters");
    }
    if (p.accept(Tk.TOKEN_ARROW) || p.accept(Tk.TOKEN_ARROW_ASCII))
    {
        n.type_ann = p.parse_type();
    }
    // Multi-clause lambda: fn | p -> e | q -> f
    if (p.check(Tk.TOKEN_PIPE))
    {
        while (p.check(Tk.TOKEN_PIPE))
        {
            Tok bar = p.advance();
            Node* cl = p.mk_at(Nk.N_CLAUSE, bar);
            bool sv = p.in_fn_sig;
            p.in_fn_sig = true;
            p.add(cl, p.parse_pattern());
            p.in_fn_sig = sv;
            if (!p.accept(Tk.TOKEN_ARROW) && !p.accept(Tk.TOKEN_ARROW_ASCII))
            {
                p.err(1066, "expected '->' in lambda clause");
                p.sync();
                p.add(n, cl);
                continue;
            }
            p.add(cl, p.parse_arm_body());
            p.add(n, cl);
            p.skip_layout();
        }
        return n;
    }
    p.add(n, p.parse_block_or_expr());
    return n;
}

// ── Blocks ──────────────────────────────────────────────────────────────────
// A block is either brace-delimited or layout-delimited (INDENT ... DEDENT).
fn Node* Parser.parse_brace_block(Parser* p)
{
    Tok t = p.advance();   // {
    Node* b = p.mk_at(Nk.N_BLOCK, t);
    p.skip_layout();
    while (!p.check(Tk.TOKEN_RBRACE) && !p.at_end())
    {
        Node* s = p.parse_stmt();
        if (s != null) { p.add(b, s); }
        if (p.panicking) { p.sync(); }
        p.skip_layout();
    }
    p.expect(Tk.TOKEN_RBRACE, 1070, "expected '}' to close block");
    return b;
}

fn Node* Parser.parse_indented_block(Parser* p)
{
    Tok t = p.cur();
    Node* b = p.mk_at(Nk.N_BLOCK, t);
    if (!p.expect(Tk.TOKEN_INDENT, 1071, "expected an indented block")) { return b; }
    p.skip_newlines();
    int saved_stmt_indent = p.stmt_indent;
    while (!p.check(Tk.TOKEN_DEDENT) && !p.at_end())
    {
        // An `else` here belongs to an enclosing `if`, never to this block.
        //
        // A nested `if` whose else-branch is INLINE (`else 2i64`) returns
        // with the cursor already past the layout run, sitting on the OUTER
        // `else`. Looping only on DEDENT then parsed that keyword as a
        // statement, and the error surfaced as "unresolved name 'else'"
        // rather than anywhere near the real cause. Stop and let the
        // enclosing parse_if claim it.
        if (p.check(Tk.TOKEN_KW_ELSE)) { break; }
        // Each statement records its own column so a nested conditional knows
        // which layout levels belong to it.
        p.stmt_indent = p.cur().col - 1;
        Node* s = p.parse_stmt();
        if (s != null) { p.add(b, s); }
        if (p.panicking) { p.sync(); }
        p.skip_newlines();
    }
    // Do not consume the block-closing DEDENT when an `else` follows it: the
    // enclosing `if` needs to see that `else`, and an inline `if/then` puts
    // its value in a deeper block than the `else` keyword.
    if (p.check(Tk.TOKEN_DEDENT) && p.peek(1).type == Tk.TOKEN_KW_ELSE)
    {
        // Deferred: the enclosing `if` must see this `else`. Record the debt so
        // parse_if closes exactly this one DEDENT and no other.
        p.deferred_dedents = p.deferred_dedents + 1;
        p.stmt_indent = saved_stmt_indent;
        return b;
    }
    p.accept(Tk.TOKEN_DEDENT);
    p.stmt_indent = saved_stmt_indent;
    return b;
}

// Does this token plausibly begin a statement? Used to recognise a block whose
// INDENT the lexer folded into a preceding continuation line.
fn bool tok_starts_stmt(Tk t)
{
    switch (t)
    {
        case TOKEN_KW_LET:
        case TOKEN_KW_CONST:
        case TOKEN_KW_STATIC:
        case TOKEN_KW_RETURN:
        case TOKEN_KW_BREAK:
        case TOKEN_KW_CONTINUE:
        case TOKEN_KW_DEFER:
        case TOKEN_KW_IF:
        case TOKEN_KW_WHILE:
        case TOKEN_KW_FOR:
        case TOKEN_KW_MATCH:
            return true;
        default:
            return tok_starts_expr(t);
    }
}

// A block whose opening INDENT was consumed by a line continuation. Reads
// statements until the enclosing DEDENT, exactly like parse_indented_block but
// without expecting the INDENT that never arrived.
fn Node* Parser.parse_virtual_block(Parser* p)
{
    Tok t = p.cur();
    Node* b = p.mk_at(Nk.N_BLOCK, t);
    int saved_stmt_indent = p.stmt_indent;
    p.skip_newlines();

    // The block's own column. Because no INDENT was emitted for this block,
    // there is no DEDENT to close it either: the next sibling of the
    // ENCLOSING construct simply appears at a shallower column, separated by
    // a bare NEWLINE.
    //
    //     if a &&
    //        b            <- continuation, col 8 (INDENT opened here)
    //       body          <- this block,   col 7 (no INDENT)
    //     tail            <- sibling,      col 5 (no DEDENT before it)
    //
    // Stopping only on DEDENT therefore ran past `body` and swallowed
    // `tail`, reparenting it out of the function entirely. Track the column
    // and stop when a statement is no longer indented past it.
    int block_col = p.cur().col;

    if (p.deferred_dedents > 0) { p.deferred_dedents = p.deferred_dedents - 1; }

    while (!p.at_end())
    {
        if (p.check(Tk.TOKEN_KW_ELSE)) { break; }
        if (p.check(Tk.TOKEN_DEDENT)) { break; }
        if (p.cur().col < block_col) { break; }
        p.stmt_indent = p.cur().col - 1;
        Node* s = p.parse_stmt();
        if (s != null) { p.add(b, s); }
        if (p.panicking) { p.sync(); }
        p.skip_newlines();
    }

    // This block DOES own a closing DEDENT, despite never having been opened
    // by an INDENT. When the body is shallower than the continuation the
    // lexer does not nest a new level — it REALIGNS the existing one, so the
    // level it later pops is the body's, not the enclosing block's:
    //
    //     if a &&
    //        b        <- INDENT to col 8
    //       body      <- DEDENT(closes 8), stack realigned 8 -> 7
    //     tail        <- DEDENT(closes 7)   <-- belongs to THIS block
    //
    // `DEDENT.len` is the closed level's column minus one, which is how the
    // two were told apart. Leaving this DEDENT for the enclosing block made
    // that block close one statement early, so the construct's next sibling
    // was reparented out of the function.
    //
    // The `else` case is the exception: parse_if must see the `else`, so the
    // DEDENT is deferred exactly as parse_indented_block does.
    if (p.check(Tk.TOKEN_DEDENT) && p.peek(1).type == Tk.TOKEN_KW_ELSE)
    {
        p.deferred_dedents = p.deferred_dedents + 1;
    }
    else
    {
        p.accept(Tk.TOKEN_DEDENT);
    }
    p.stmt_indent = saved_stmt_indent;
    return b;
}

// Arm bodies (match / clause / handler) must not swallow a following `|`,
// because that bar introduces the NEXT arm rather than a bitwise-or. Setting
// in_fn_sig makes parse_expr_prec treat `|` as a terminator.
fn Node* Parser.parse_arm_body(Parser* p)
{
    p.skip_newlines();
    if (p.check(Tk.TOKEN_INDENT)) { return p.parse_indented_block(); }
    // A brace block is explicitly delimited, so `|` inside it is unambiguous
    // bitwise-or, never an arm separator. Clear the guard for its extent.
    if (p.check(Tk.TOKEN_LBRACE))
    {
        bool sv = p.in_fn_sig;
        p.in_fn_sig = false;
        Node* b = p.parse_brace_block();
        p.in_fn_sig = sv;
        return b;
    }
    bool saved = p.in_fn_sig;
    p.in_fn_sig = true;
    Node* e = p.parse_stmt_expr_only();
    // A semicolon chains further statements on the same line:
    //   `| code -> syscall1(NR_EXIT_GROUP, code); unreachable`
    // Collect them into a block so the arm yields the LAST value.
    if (p.check(Tk.TOKEN_SEMI))
    {
        Node* blk = p.mk(Nk.N_BLOCK, e == null ? 0 : e.line, e == null ? 0 : e.col);
        p.add(blk, e);
        while (p.accept(Tk.TOKEN_SEMI))
        {
            if (p.check(Tk.TOKEN_NEWLINE) || p.check(Tk.TOKEN_DEDENT) || p.at_end()) { break; }
            if (p.check(Tk.TOKEN_PIPE)) { break; }
            // A closing brace ends the ENCLOSING block, so the semicolon we
            // just consumed was a terminator, not a separator:
            //     if c then { a = 1; if d then x else (); } else { () }
            //                                            ^ this `;` then `}`
            // Without this the loop tried to parse `}` as a statement and
            // reported "expected an expression", then "expected '}'" at EOF.
            if (p.check(Tk.TOKEN_RBRACE)) { break; }
            p.add(blk, p.parse_stmt_expr_only());
        }
        p.in_fn_sig = saved;
        return blk;
    }
    p.in_fn_sig = saved;
    return e;
}

// The workhorse: after `if cond`, `-> `, `while c` etc., the body may be
// (a) an indented block, (b) a braced block, or (c) a single inline expression.
fn Node* Parser.parse_block_or_expr(Parser* p)
{
    p.skip_newlines();
    if (p.check(Tk.TOKEN_INDENT)) { p.implicit_block = false; return p.parse_indented_block(); }
    if (p.check(Tk.TOKEN_LBRACE)) { p.implicit_block = false; return p.parse_brace_block(); }
    // `implicit_block` is a ONE-SHOT hint left by a line continuation that
    // absorbed the layout which would have opened this block. It is set at a
    // distance (settle_continuation, and the debt-drop in the binary-operator
    // parser) and was never invalidated, so it could survive to a LATER
    // construct and turn an inline body into a spurious block.
    //
    //     let (a, b) =
    //       if ilen >= 4          <- initializer block, level 8
    //         ...
    //       else if ilen > 0
    //         let av = ilen |     <- continuation sets implicit_block
    //                  ilen
    //         (av, 0)
    //       else (0, 0)           <- INLINE body, but implicit_block still set
    //     let s = ilen            <- swallowed: parse_virtual_block accepted
    //                                the DEDENT (len=8) closing the initializer
    //
    // Same guard as the column path below: a block the lexer folded away
    // still BEGINS ON A LATER LINE than the construct introducing it, whereas
    // an inline body sits on the same line. Verified on the real token
    // stream -- the stolen DEDENT is at L17 while the `else` body is at L16.
    // Clear the flag either way; it has been answered.
    if (p.implicit_block)
    {
        p.implicit_block = false;
        if (p.cur().line > p.prev_line) { return p.parse_virtual_block(); }
    }
    // A wrapped condition can consume the layout that would have introduced
    // the body:
    //     if (a) ||
    //        (b)
    //       body          <- deeper than the `if`, but no INDENT was emitted
    // The lexer realigned its indent stack to the continuation line, so the
    // body is structurally a block even though no INDENT arrived. Detect it
    // by column: deeper than the owning statement means "block".
    if (p.check(Tk.TOKEN_DEDENT))
    {
        // The DEDENT closes the continuation level, not the enclosing block:
        // look past it. If a statement follows at a column deeper than the
        // statement that owns this construct, that statement is our body.
        Tok after = p.peek(1);
        if (tok_starts_stmt(after.type) && after.col - 1 > p.stmt_indent)
        {
            p.advance();
            return p.parse_virtual_block();
        }
    }
    // A body the lexer folded into a continuation is still a BLOCK: it begins
    // on a later line than the keyword that introduced it. An INLINE body
    // (`else 3i64`) sits on the SAME line and is a bare expression.
    //
    // Without the line test, `else 3i64` inside a `let` initializer took the
    // virtual-block path, and parse_virtual_block then consumed the DEDENT
    // that closes the INITIALIZER — so the initializer's own block never saw
    // its close and swallowed the following statement. That is the whole of
    // the long-standing `let x = if/else if/else` bug; it was never in
    // parse_if's recursion. Verified on the token stream: the `else` body
    // `3i64` is at L10 C14 while the stolen DEDENT (len=8, the initializer
    // level) is at L11.
    if (!p.at_end() && p.cur().col - 1 > p.stmt_indent
        && p.cur().line > p.prev_line
        && tok_starts_stmt(p.ct()))
    {
        return p.parse_virtual_block();
    }
    // Single inline statement/expression.
    Node* e = p.parse_stmt_expr_only();
    return e;
}

// ════════════════════════════════════════════════════════════════════════════
// 6. STATEMENTS
// ════════════════════════════════════════════════════════════════════════════

fn bool is_assign_op(Tk t)
{
    switch (t)
    {
        case TOKEN_PLUSEQ:
        case TOKEN_MINUSEQ:
        case TOKEN_STAREQ:
        case TOKEN_SLASHEQ:
        case TOKEN_PERCENTEQ:
        case TOKEN_AMPEQ:
        case TOKEN_PIPEEQ:
        case TOKEN_XOREQ:
        case TOKEN_LSHIFTEQ:
        case TOKEN_RSHIFTEQ:
            return true;
        default:
            return false;
    }
}

fn Node* Parser.parse_stmt_expr_only(Parser* p)
{
    // Control-transfer keywords are STATEMENTS, not expressions, but they are
    // legal wherever an inline body is:
    //
    //     if at_end then break
    //     | 0i64 -> return 1i64
    //     while c do continue
    //
    // parse_expr has no case for them, so they fell through to the
    // contextual-identifier rule and became `ident 'break' [UNRESOLVED]`.
    // That produced 25 bogus "unresolved name" errors across the stdlib, all
    // reported at the keyword rather than anywhere near a real mistake.
    //
    // Handle them here, at the single entry point every inline body shares,
    // rather than at each of the four call sites.
    Tk k = p.ct();
    if (k == Tk.TOKEN_KW_BREAK || k == Tk.TOKEN_KW_CONTINUE
        || k == Tk.TOKEN_KW_RETURN)
    {
        return p.parse_stmt();
    }

    // A binding is also a statement, and a semicolon chain in an inline body
    // routinely starts with one:
    //
    //     | s -> let n = strlen(s); write(1, s, n); ()
    //
    // Without this the `let` parsed as an identifier and every later use of
    // the bound name reported "unresolved name" -- 4 sites in fmt.pie alone,
    // all blamed on the USE rather than on the binding that never happened.
    //
    // parse_let ends with end_stmt, which CONSUMES the semicolon. The caller's
    // chain loop would therefore never see it, so the rest of the line was
    // dropped. Collect the whole chain here instead, and hand back a block
    // whose value is the last element.
    if (k == Tk.TOKEN_KW_LET)
    {
        Node* first = p.parse_let();
        if (!p.at_block_end() && !p.check(Tk.TOKEN_NEWLINE)
            && tok_starts_stmt(p.ct()))
        {
            Node* blk = p.mk(Nk.N_BLOCK, first == null ? 0 : first.line,
                                          first == null ? 0 : first.col);
            p.add(blk, first);
            while (!p.at_block_end() && !p.check(Tk.TOKEN_NEWLINE)
                   && tok_starts_stmt(p.ct()))
            {
                // parse_let swallows its own trailing `;` via end_stmt, an
                // expression does not. Track which happened so the loop does
                // not demand a semicolon that was already consumed — two
                // chained `let`s hit exactly that and dropped the tail.
                bool was_let = p.ct() == Tk.TOKEN_KW_LET;
                Node* nxt = was_let ? p.parse_let() : p.parse_stmt_expr_only();
                if (nxt == null) { break; }
                p.add(blk, nxt);
                if (!was_let && !p.accept(Tk.TOKEN_SEMI)) { break; }
            }
            return blk;
        }
        return first;
    }

    Node* e = p.parse_expr();
    if (p.check(Tk.TOKEN_EQ))
    {
        Tok eq = p.advance();
        Node* rhs = p.parse_expr();
        Node* asn = p.mk_at(Nk.N_STMT_ASSIGN, eq);
        p.add(asn, e);
        p.add(asn, rhs);
        return asn;
    }
    if (is_assign_op(p.ct()))
    {
        Tok op = p.advance();
        Node* rhs = p.parse_expr();
        Node* asn = p.mk_at(Nk.N_STMT_COMPOUND_ASSIGN, op);
        asn.p.op = (int)op.type;
        p.add(asn, e);
        p.add(asn, rhs);
        return asn;
    }
    return e;
}

fn Node* Parser.parse_stmt(Parser* p)
{
    p.skip_newlines();
    Tok t = p.cur();
    switch (t.type)
    {
        case TOKEN_KW_LET:      return p.parse_let();
        case TOKEN_KW_CONST:    return p.parse_const(false);
        case TOKEN_KW_STATIC:   return p.parse_const(true);
        case TOKEN_KW_RETURN:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_STMT_RETURN, t);
            if (tok_starts_expr(p.ct())) { p.add(n, p.parse_expr()); }
            p.end_stmt();
            return n;
        }
        case TOKEN_KW_BREAK:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_STMT_BREAK, t);
            if (p.check(Tk.TOKEN_LABEL_REF))
            {
                Tok lb = p.advance();
                n.name_id = p.interner.intern(lb.start, lb.len);
                n.p.sptr = lb.start;
                n.p.slen = lb.len;
            }
            if (tok_starts_expr(p.ct())) { p.add(n, p.parse_expr()); }
            p.end_stmt();
            return n;
        }
        case TOKEN_KW_CONTINUE:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_STMT_CONTINUE, t);
            if (p.check(Tk.TOKEN_LABEL_REF))
            {
                Tok lb = p.advance();
                n.name_id = p.interner.intern(lb.start, lb.len);
                n.p.sptr = lb.start;
                n.p.slen = lb.len;
            }
            p.end_stmt();
            return n;
        }
        case TOKEN_KW_DEFER:
        {
            p.advance();
            Node* n = p.mk_at(Nk.N_STMT_DEFER, t);
            p.add(n, p.parse_block_or_expr());
            p.end_stmt();
            return n;
        }
        case TOKEN_KW_FN:
        {
            // A nested named fn is a declaration; an anonymous one is a lambda.
            Tk nx = p.peek(1).type;
            if (nx == Tk.TOKEN_IDENT) { return p.parse_fn_decl(false); }
            Node* e = p.parse_stmt_expr_only();
            p.end_stmt();
            return e;
        }
        case TOKEN_KW_STRUCT:   return p.parse_struct_decl(false, Nk.N_DECL_STRUCT);
        case TOKEN_KW_UNION:    return p.parse_struct_decl(false, Nk.N_DECL_UNION);
        case TOKEN_KW_ENUM:     return p.parse_enum_decl(false);
        case TOKEN_KW_TYPE:     return p.parse_type_alias(false);
        case TOKEN_KW_USE:      return p.parse_use();
        default:
        {
            Node* e = p.parse_stmt_expr_only();
            p.end_stmt();
            return e;
        }
    }
}

fn Node* Parser.parse_let(Parser* p)
{
    Tok t = p.advance();   // let
    Node* n = p.mk_at(Nk.N_DECL_LET, t);
    if (p.accept(Tk.TOKEN_KW_MUT)) { n.flags = n.flags | pfront_core::NF_MUT; }
    Node* pat = p.parse_pattern();
    p.add(n, pat);
    if (pat != null && pat.kind == Nk.N_PAT_IDENT) { n.name_id = pat.name_id; }
    if (p.accept(Tk.TOKEN_COLON)) { n.type_ann = p.parse_type(); }
    if (p.accept(Tk.TOKEN_EQ))
    {
        // The initializer may be an indented block on the following line:
        //     let n =
        //       if ty == 'f'
        //         a
        //       else
        //         b
        // parse_block_or_expr handles the inline case identically, so route
        // both through it rather than special-casing.
        p.add(n, p.parse_initializer());
    }
    p.end_stmt();
    return n;
}



// An initializer / RHS value: inline expression, or a layout block introduced
// by a line break. Kept separate from parse_block_or_expr because an RHS must
// not consume a `|` that belongs to an enclosing clause.
fn Node* Parser.parse_initializer(Parser* p)
{
    if (p.layout_then(Tk.TOKEN_INDENT) && !p.check(Tk.TOKEN_INDENT))
    {
        // Nothing to do: fall through, the INDENT is next after newlines.
    }
    usz eaten = 0;
    while (p.check(Tk.TOKEN_NEWLINE)) { p.advance(); eaten = eaten + 1; }
    if (p.check(Tk.TOKEN_INDENT))
    {
        // Record the level this initializer block opens so a conditional
        // inside it never closes past it and swallows the next statement.
        int saved = p.init_block_level;
        int my_level = p.cur().col - 1;
        p.init_block_level = my_level;
        Node* v = p.parse_indented_block_value();

        // An `else if` chain inside the initializer opens one layout level per
        // link, and parse_indented_block only ever consumes the single DEDENT
        // that closes its own. The surplus then leaked out and the statement
        // AFTER the initializer was parsed as part of it:
        //
        //     let a =
        //       if n > 0        <- initializer block, level 6
        //         1
        //       else if n < 0   <- second level
        //         2
        //       else 3
        //     a                 <- was nested inside `a`'s own initializer
        //
        // Close the DEDENT that ends the initializer itself, plus any the
        // else-if chain left behind.
        //
        // `DEDENT.len` is the column the DEDENT closes TO, not the level it
        // closes FROM: the run above ends with len 6 (back to the statement)
        // while the initializer sat at level 8. Comparing `len > my_level`
        // therefore never fired. The correct test is that the DEDENT lands
        // at or above the initializer — those are the ones it owns — while
        // anything landing shallower than the enclosing STATEMENT belongs to
        // the outer block and must be left alone.
        while (p.check(Tk.TOKEN_DEDENT)
               && (int)p.cur().len >= p.stmt_indent
               && (int)p.cur().len <= my_level)
        {
            p.advance();
        }

        p.init_block_level = saved;
        return v;
    }
    if (p.check(Tk.TOKEN_LBRACE)) { return p.parse_brace_block(); }
    return p.parse_expr();
}

// Like parse_indented_block, but when the block holds exactly one expression
// the expression itself is returned. `let n =` + an indented `if` should bind
// the if-expression, not a block wrapping it — that keeps the AST shape the
// same as the inline spelling and avoids a pointless N_BLOCK for consumers.
fn Node* Parser.parse_indented_block_value(Parser* p)
{
    Node* b = p.parse_indented_block();
    if (b != null && b.child_count == 1)
    {
        Node* only = b.children[0];
        if (only != null && is_value_node(only.kind))
        {
            only.parent = b.parent;
            return only;
        }
    }
    return b;
}

fn bool is_value_node(Nk k)
{
    if (pfront_core::is_expr(k)) { return true; }
    return k == Nk.N_BLOCK;
}

fn Node* Parser.parse_const(Parser* p, bool is_static)
{
    Tok t = p.advance();
    Node* n = p.mk_at(is_static ? Nk.N_DECL_STATIC : Nk.N_DECL_CONST, t);
    if (p.accept(Tk.TOKEN_KW_MUT)) { n.flags = n.flags | pfront_core::NF_MUT; }
    // Constants are conventionally SCREAMING_CASE, which the lexer classifies
    // as TOKEN_TYPEVAR (uppercase-initial), so both spellings are accepted.
    Tok nm = p.cur();
    if (nm.type == Tk.TOKEN_IDENT || nm.type == Tk.TOKEN_TYPEVAR)
    {
        p.advance();
        n.name_id = p.interner.intern(nm.start, nm.len);
        n.p.sptr = nm.start;
        n.p.slen = nm.len;
    }
    else
    {
        p.err(1080, "expected a name after const/static");
    }
    if (p.accept(Tk.TOKEN_COLON)) { n.type_ann = p.parse_type(); }
    if (p.accept(Tk.TOKEN_EQ)) { p.add(n, p.parse_expr()); }
    p.end_stmt();
    return n;
}

// ════════════════════════════════════════════════════════════════════════════
// 7. DECLARATIONS
// ════════════════════════════════════════════════════════════════════════════

fn Node* Parser.parse_param(Parser* p)
{
    Tok t = p.cur();
    Node* prm = p.mk_at(Nk.N_DECL_PARAM, t);
    if (p.accept(Tk.TOKEN_ELLIPSIS))
    {
        prm.flags = prm.flags | pfront_core::NF_VARIADIC;
        return prm;
    }
    if (p.accept(Tk.TOKEN_KW_MUT)) { prm.flags = prm.flags | pfront_core::NF_MUT; }
    Node* pat = p.parse_pattern_atom();
    p.add(prm, pat);
    if (pat != null) { prm.name_id = pat.name_id; }
    if (p.accept(Tk.TOKEN_COLON)) { prm.type_ann = p.parse_type(); }
    return prm;
}

fn void Parser.parse_typarams(Parser* p, Node* owner)
{
    if (!p.check(Tk.TOKEN_LT)) { return; }
    p.advance();
    while (!p.check(Tk.TOKEN_GT) && !p.at_end())
    {
        Tok tv = p.cur();
        if (tv.type != Tk.TOKEN_TYPEVAR && tv.type != Tk.TOKEN_IDENT)
        {
            p.err(1081, "expected a type parameter name");
            break;
        }
        p.advance();
        Node* tp = p.mk_at(Nk.N_DECL_TYPEPARAM, tv);
        tp.name_id = p.interner.intern(tv.start, tv.len);
        tp.p.sptr = tv.start;
        tp.p.slen = tv.len;
        if (p.accept(Tk.TOKEN_COLON))
        {
            // bound: T : Interface
            tp.type_ann = p.parse_type();
        }
        p.add(owner, tp);
        if (!p.accept(Tk.TOKEN_COMMA)) { break; }
    }
    p.expect(Tk.TOKEN_GT, 1082, "expected '>' to close type parameters");
}

// Pride functions come in two shapes:
//   (a)  fn name : Type -> Type
//          | pattern -> body
//          | pattern -> body
//   (b)  fn name(a: T, b: U) -> V { ... }
fn Node* Parser.parse_fn_decl(Parser* p, bool is_pub)
{
    Tok t = p.advance();   // fn
    Node* n = p.mk_at(Nk.N_DECL_FN, t);
    if (is_pub) { n.flags = n.flags | pfront_core::NF_PUB; }
    Tok nm = p.cur();
    if (!tok_is_member_name(nm.type))
    {
        p.err(1083, "expected a function name");
        p.sync();
        return n;
    }
    p.advance();
    n.name_id = p.interner.intern(nm.start, nm.len);
    n.p.sptr = nm.start;
    n.p.slen = nm.len;

    p.parse_typarams(n);

    if (p.check(Tk.TOKEN_COLON))
    {
        // Signature form.
        p.advance();
        bool sv = p.in_fn_sig;
        p.in_fn_sig = true;
        Node* sig = p.parse_type();
        Node* ret = null;
        if (p.accept(Tk.TOKEN_ARROW) || p.accept(Tk.TOKEN_ARROW_ASCII))
        {
            ret = p.parse_type();
        }
        Node* fnty = p.mk(Nk.N_TY_FN, t.line, t.col);
        p.add(fnty, sig);
        if (ret != null)
        {
            Node* rw = p.mk(Nk.N_TY_CONSTRAINT, t.line, t.col);
            p.add(rw, ret);
            p.add(fnty, rw);
        }
        n.type_ann = fnty;
        if (p.check(Tk.TOKEN_BANG))
        {
            Node* row = p.parse_effect_row();
            if (row != null) { p.add(fnty, row); }
        }
        p.in_fn_sig = sv;

        // `fn NAME : T = <expr>` — a nullary constant written with `fn`
        // rather than `const`. There are no clauses; the initializer follows
        // the signature directly:
        //     fn F64_NAN_BITS : u64 = 0x7FF8000000000000u64
        // Treat it as a zero-argument definition so the value is reachable
        // and the name resolves like any other module member.
        if (p.check(Tk.TOKEN_EQ))
        {
            p.advance();
            Node* init = p.parse_expr();
            Node* cl = p.mk(Nk.N_CLAUSE, t.line, t.col);
            cl.flags = cl.flags | pfront_core::NF_SYNTHETIC;
            if (init != null) { p.add(cl, init); }
            p.add(n, cl);
            p.skip_trailing_attrs();
            p.skip_newlines();
            return n;
        }

        p.skip_trailing_attrs();
        p.skip_newlines();
        bool indented = p.accept(Tk.TOKEN_INDENT);
        p.skip_newlines();

        /*
         WHERE CLAUSES, spec §12:

             fn zip<A, B, C> : (*A, *B, u64) -> *C
               where C = Pair<A, B>
               | (xs, ys, n) -> ...

         A `where` binds a type equation that applies while checking the
         body. There was no rule for it at all: the parser reached the
         `where` keyword expecting a clause bar, reported "expected an
         expression", and then reported the equation's own identifiers as
         unresolved names — three cascading errors from one missing
         construct.

         Several equations may be given, one per line or comma-separated.
         They attach to the function as N_TY_WHERE children so the type
         checker can apply them; each is `Name = Type`.
        */
        while (p.check(Tk.TOKEN_KW_WHERE))
        {
            Tok w = p.advance();
            while (true)
            {
                Tok wnm = p.cur();
                if (wnm.type != Tk.TOKEN_TYPEVAR && wnm.type != Tk.TOKEN_IDENT)
                {
                    p.err(1085, "expected a type name in a where clause");
                    break;
                }
                p.advance();
                Node* wh = p.mk_at(Nk.N_TY_WHERE, w);
                wh.name_id = p.intern_tok(wnm);
                wh.p.sptr = wnm.start;
                wh.p.slen = wnm.len;

                /*
                 Two forms are in the spec: an EQUALITY (`where C = Pair<A,B>`)
                 and a CONSTRAINT (`where T : Ord`). Both bind the name; the
                 discriminator is recorded in `aux` so the checker can tell
                 an equation from a bound without re-reading the source.
                */
                if (p.accept(Tk.TOKEN_EQ))      { wh.p.aux = 0; }
                else if (p.accept(Tk.TOKEN_COLON)) { wh.p.aux = 1; }
                else
                {
                    p.err(1086, "expected '=' or ':' in a where clause");
                    break;
                }
                p.add(wh, p.parse_type_with_arrow());
                p.add(n, wh);

                if (!p.accept(Tk.TOKEN_COMMA)) { break; }
                p.skip_newlines();
            }
            p.skip_newlines();
            // A `where` on its own line opens a layout level the clause
            // bars then close; absorb it so the bar loop below still sees
            // them at the expected depth.
            if (!indented) { indented = p.accept(Tk.TOKEN_INDENT); }
            p.skip_newlines();
        }

        while (p.check(Tk.TOKEN_PIPE))
        {
            Tok bar = p.advance();
            Node* cl = p.mk_at(Nk.N_CLAUSE, bar);
            bool sv2 = p.in_fn_sig;
            p.in_fn_sig = true;
            Node* cpat = p.parse_pattern();

            /*
             OR-PATTERNS in a function clause, spec §8:

                 | 'a' | 'e' | 'i' | 'o' | 'u' → "vowel"

             The clause loop treats `|` as the ARM separator, so an
             alternative inside one arm looked like the start of the next
             and the parser demanded an arrow. Collect them: after the
             first pattern, a `|` that is NOT followed by another arm's
             worth of pattern-then-arrow is an alternative.

             Distinguishing them needs no lookahead trick — an alternative
             is simply a pattern followed eventually by the SAME arrow, so
             keep absorbing `| pattern` until the arrow appears.
            */
            while (p.check(Tk.TOKEN_PIPE))
            {
                p.advance();
                Node* alt = p.parse_pattern();
                if (alt == null) { break; }
                Node* orp = p.mk_at(Nk.N_PAT_OR, bar);
                orp.flags = orp.flags | pfront_core::NF_REFUTABLE;
                p.add(orp, cpat);
                p.add(orp, alt);
                cpat = orp;
            }
            p.add(cl, cpat);
            p.in_fn_sig = sv2;

            /*
             GUARDS, spec §8: `| pattern, guard → body`.

             Only the `if` spelling was accepted. The spec's own examples
             use a comma (`| n, n < 0 → "negative"`), which left the comma
             where the arrow was expected.
            */
            if (p.check(Tk.TOKEN_KW_IF) || p.check(Tk.TOKEN_COMMA))
            {
                Tok g = p.advance();
                Node* guard = p.mk_at(Nk.N_GUARD, g);
                bool sv_g = p.in_fn_sig;
                p.in_fn_sig = true;
                p.add(guard, p.parse_expr());
                p.in_fn_sig = sv_g;
                p.add(cl, guard);
            }
            if (!p.accept(Tk.TOKEN_ARROW) && !p.accept(Tk.TOKEN_ARROW_ASCII))
            {
                p.err(1084, "expected '->' after a function clause pattern");
                p.sync();
                p.add(n, cl);
                continue;
            }
            p.add(cl, p.parse_arm_body());
            p.add(n, cl);
            p.skip_newlines();
        }
        if (indented) { while (p.accept(Tk.TOKEN_DEDENT)) {} }
        return n;
    }

    // Parameter-list form.
    if (p.accept(Tk.TOKEN_LPAREN))
    {
        while (!p.check(Tk.TOKEN_RPAREN) && !p.at_end())
        {
            p.add(n, p.parse_param());
            if (!p.accept(Tk.TOKEN_COMMA)) { break; }
        }
        p.expect(Tk.TOKEN_RPAREN, 1085, "expected ')' to close parameter list");
    }
    if (p.accept(Tk.TOKEN_ARROW) || p.accept(Tk.TOKEN_ARROW_ASCII))
    {
        n.type_ann = p.parse_type();
    }
    if (p.check(Tk.TOKEN_BANG))
    {
        Node* row = p.parse_effect_row();
        if (row != null) { p.add(n, row); }
    }
    p.skip_trailing_attrs();
    if (p.check(Tk.TOKEN_KW_WHERE))
    {
        p.advance();
        Node* w = p.mk(Nk.N_TY_WHERE, t.line, t.col);
        while (tok_starts_type(p.ct()))
        {
            p.add(w, p.parse_type());
            if (!p.accept(Tk.TOKEN_COMMA)) { break; }
        }
        p.add(n, w);
    }
    p.skip_newlines();
    if (p.check(Tk.TOKEN_INDENT) || p.check(Tk.TOKEN_LBRACE))
    {
        p.add(n, p.parse_block_or_expr());
    }
    return n;
}

fn Node* Parser.parse_struct_decl(Parser* p, bool is_pub, Nk kind)
{
    Tok t = p.advance();
    Node* n = p.mk_at(kind, t);
    if (is_pub) { n.flags = n.flags | pfront_core::NF_PUB; }
    Tok nm = p.cur();
    if (!tok_is_member_name(nm.type))
    {
        p.err(1086, "expected a struct name");
        p.sync();
        return n;
    }
    p.advance();
    n.name_id = p.interner.intern(nm.start, nm.len);
    n.p.sptr = nm.start;
    n.p.slen = nm.len;
    p.parse_typarams(n);

    /*
     Struct ATTRIBUTES, spec §9: `struct CacheLine #align(64)`,
     `struct PackedHdr #packed`. Nothing consumed them, so the `#` sat
     where the field list was expected and every field then failed with
     "expected an expression".

     skip_trailing_attrs already existed and was already used for
     functions; the struct parser simply never called it. Layout and ABI
     attributes are exactly the ones a systems language cannot do without.
    */
    p.skip_trailing_attrs();
    p.skip_newlines();

    bool braced = p.accept(Tk.TOKEN_LBRACE);
    bool indented = false;
    if (!braced) { indented = p.accept(Tk.TOKEN_INDENT); }
    p.skip_newlines();

    while (!p.at_end())
    {
        if (braced && p.check(Tk.TOKEN_RBRACE)) { break; }
        if (indented && p.check(Tk.TOKEN_DEDENT)) { break; }
        if (!braced && !indented) { break; }
        Tok fname = p.cur();
        if (!tok_is_member_name(fname.type))
        {
            if (p.check(Tk.TOKEN_NEWLINE)) { p.advance(); continue; }
            break;
        }
        p.advance();
        Node* f = p.mk_at(Nk.N_DECL_FIELD, fname);
        f.name_id = p.interner.intern(fname.start, fname.len);
        f.p.sptr = fname.start;
        f.p.slen = fname.len;
        if (p.accept(Tk.TOKEN_COLON)) { f.type_ann = p.parse_type(); }
        else { p.err(1087, "expected ':' and a type in a field declaration"); }
        if (p.accept(Tk.TOKEN_EQ)) { p.add(f, p.parse_expr()); }
        p.add(n, f);
        // Fields separate with a comma, a semicolon, or just a newline. The
        // semicolon form packs several onto one line and is used throughout
        // the stdlib for state records:
        //     v0 : u64; v1 : u64; v2 : u64; v3 : u64
        // Accepting only ',' made the second field on such a line look like
        // the start of a new declaration.
        if (!p.accept(Tk.TOKEN_COMMA)) { p.accept(Tk.TOKEN_SEMI); }
        p.skip_newlines();
    }
    if (indented) { while (p.accept(Tk.TOKEN_DEDENT)) {} }
    if (braced) { p.expect(Tk.TOKEN_RBRACE, 1088, "expected '}' to close struct body"); }
    return n;
}

fn Node* Parser.parse_enum_decl(Parser* p, bool is_pub)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_DECL_ENUM, t);
    if (is_pub) { n.flags = n.flags | pfront_core::NF_PUB; }
    Tok nm = p.cur();
    if (!tok_is_member_name(nm.type))
    {
        p.err(1089, "expected an enum name");
        p.sync();
        return n;
    }
    p.advance();
    n.name_id = p.interner.intern(nm.start, nm.len);
    n.p.sptr = nm.start;
    n.p.slen = nm.len;
    p.parse_typarams(n);
    p.skip_newlines();

    bool braced = p.accept(Tk.TOKEN_LBRACE);
    bool indented = false;
    if (!braced) { indented = p.accept(Tk.TOKEN_INDENT); }
    p.skip_newlines();

    int ordinal = 0;
    while (!p.at_end())
    {
        if (braced && p.check(Tk.TOKEN_RBRACE)) { break; }
        if (indented && p.check(Tk.TOKEN_DEDENT)) { break; }
        if (!braced && !indented) { break; }
        p.accept(Tk.TOKEN_PIPE);
        Tok vn = p.cur();
        if (!tok_is_member_name(vn.type))
        {
            if (p.check(Tk.TOKEN_NEWLINE)) { p.advance(); continue; }
            break;
        }
        p.advance();
        Node* v = p.mk_at(Nk.N_DECL_VARIANT, vn);
        v.name_id = p.interner.intern(vn.start, vn.len);
        v.p.sptr = vn.start;
        v.p.slen = vn.len;
        v.p.ival = (ulong)ordinal;
        ordinal = ordinal + 1;
        if (p.accept(Tk.TOKEN_LPAREN))
        {
            while (!p.check(Tk.TOKEN_RPAREN) && !p.at_end())
            {
                Node* pt = p.parse_type();
                p.add(v, pt);
                if (!p.accept(Tk.TOKEN_COMMA)) { break; }
            }
            p.expect(Tk.TOKEN_RPAREN, 1090, "expected ')' to close variant payload");
        }
        if (p.accept(Tk.TOKEN_EQ))
        {
            Node* disc = p.parse_expr();
            p.add(v, disc);
            v.p.aux = 1;
        }
        p.add(n, v);
        p.accept(Tk.TOKEN_COMMA);
        p.skip_newlines();
    }
    if (indented) { while (p.accept(Tk.TOKEN_DEDENT)) {} }
    if (braced) { p.expect(Tk.TOKEN_RBRACE, 1091, "expected '}' to close enum body"); }
    return n;
}

fn Node* Parser.parse_type_alias(Parser* p, bool is_pub)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_DECL_TYPE, t);
    if (is_pub) { n.flags = n.flags | pfront_core::NF_PUB; }
    Tok nm = p.cur();
    if (!tok_is_member_name(nm.type))
    {
        p.err(1092, "expected a type alias name");
        p.sync();
        return n;
    }
    p.advance();
    n.name_id = p.interner.intern(nm.start, nm.len);
    n.p.sptr = nm.start;
    n.p.slen = nm.len;
    p.parse_typarams(n);

    /*
     `type Name = struct` / `= union` / `= enum` — the spec's PRIMARY
     spelling for these (§9 writes every struct that way), and it did not
     parse at all: the alias read `struct` as a type name and then choked
     on the field list.

     The stdlib only ever writes the bare `struct Name` form, which is why
     nothing caught this. Both spellings must produce the SAME declaration
     node, or downstream passes would see two shapes for one concept.

     Delegating to the real declaration parser gives that for free; it
     needs the name and type parameters transplanted, since it expects to
     read them itself.
    */
    if (p.check(Tk.TOKEN_EQ))
    {
        Tk after = p.peek(1).type;
        if (after == Tk.TOKEN_KW_STRUCT || after == Tk.TOKEN_KW_UNION
            || after == Tk.TOKEN_KW_ENUM)
        {
            p.advance();                       // '='
            /*
             The declaration parsers do `advance()` for their own keyword
             and THEN read the name. Here the name came before the keyword,
             so consume the keyword now and push the name into its place:
             the parser's advance() eats a copy of the name token, and the
             real one is what it reads next.

             Pushing the name without consuming the keyword named every
             such struct `struct`, because advance() ate the pushed name
             and the keyword became the identifier.
            */
            /*
             Order matters: the declaration parser calls advance() for its
             own keyword and only then reads the name. So the ring must be

                 [ keyword, NAME, ... ]

             Consume the keyword, push the name, then push the keyword back
             on top of it. Pushing only the name left the ring as
             [ NAME, keyword, ... ] — advance() ate the name and every
             such struct came out called `struct`.
            */
            Tok kw = p.advance();
            p.push_back(nm);
            p.push_back(kw);
            Node* d = after == Tk.TOKEN_KW_STRUCT
                        ? p.parse_struct_decl(is_pub, Nk.N_DECL_STRUCT)
                    : after == Tk.TOKEN_KW_UNION
                        ? p.parse_struct_decl(is_pub, Nk.N_DECL_UNION)
                    :     p.parse_enum_decl(is_pub);
            if (d != null)
            {
                for (usz i = 0; i < n.child_count; i++)
                {
                    Node* c = n.children[i];
                    if (c != null && c.kind == Nk.N_DECL_TYPEPARAM) { p.add(d, c); }
                }
            }
            return d;
        }
    }

    if (p.accept(Tk.TOKEN_EQ))
    {
        Node* ty = p.parse_type();
        // `type F = A -> B` — a function type on the right of an alias.
        //
        // `parse_type` stops before the arrow because in a `fn` signature the
        // arrow is consumed by parse_fn_decl, which builds the N_TY_FN itself.
        // An alias has no such wrapper, so the arrow was left dangling and the
        // statement terminator saw `->` and reported "expected an expression"
        // two lines away from the real cause.
        //
        // Build the same N_TY_FN shape parse_fn_decl produces, so downstream
        // passes see one representation of a function type, not two.
        if (p.check(Tk.TOKEN_ARROW) || p.check(Tk.TOKEN_ARROW_ASCII))
        {
            p.advance();
            Node* ret = p.parse_type();
            Node* fnty = p.mk(Nk.N_TY_FN, t.line, t.col);
            p.add(fnty, ty);
            if (ret != null)
            {
                Node* rw = p.mk(Nk.N_TY_CONSTRAINT, t.line, t.col);
                p.add(rw, ret);
                p.add(fnty, rw);
            }
            // An effect row may follow: `type H = A -> B ! [IO]`.
            if (p.check(Tk.TOKEN_BANG))
            {
                Node* row = p.parse_effect_row();
                if (row != null) { p.add(fnty, row); }
            }
            ty = fnty;
        }
        n.type_ann = ty;
    }
    p.end_stmt();
    return n;
}

fn Node* Parser.parse_newtype(Parser* p, bool is_pub)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_DECL_NEWTYPE, t);
    if (is_pub) { n.flags = n.flags | pfront_core::NF_PUB; }
    Tok nm = p.cur();
    if (!tok_is_member_name(nm.type))
    {
        p.err(1093, "expected a newtype name");
        p.sync();
        return n;
    }
    p.advance();
    n.name_id = p.interner.intern(nm.start, nm.len);
    n.p.sptr = nm.start;
    n.p.slen = nm.len;
    p.parse_typarams(n);
    if (p.accept(Tk.TOKEN_EQ)) { n.type_ann = p.parse_type(); }
    p.end_stmt();
    return n;
}

fn Node* Parser.parse_effect_decl(Parser* p, bool is_pub)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_DECL_EFFECT, t);
    if (is_pub) { n.flags = n.flags | pfront_core::NF_PUB; }
    Tok nm = p.cur();
    if (!tok_is_member_name(nm.type))
    {
        p.err(1094, "expected an effect name");
        p.sync();
        return n;
    }
    p.advance();
    n.name_id = p.interner.intern(nm.start, nm.len);
    n.p.sptr = nm.start;
    n.p.slen = nm.len;
    p.parse_typarams(n);
    p.skip_newlines();

    bool braced = p.accept(Tk.TOKEN_LBRACE);
    bool indented = false;
    if (!braced) { indented = p.accept(Tk.TOKEN_INDENT); }
    p.skip_newlines();

    while (!p.at_end())
    {
        if (braced && p.check(Tk.TOKEN_RBRACE)) { break; }
        if (indented && p.check(Tk.TOKEN_DEDENT)) { break; }
        if (!braced && !indented) { break; }
        Tok on = p.cur();
        if (!tok_is_member_name(on.type))
        {
            if (p.check(Tk.TOKEN_NEWLINE)) { p.advance(); continue; }
            break;
        }
        p.advance();
        Node* op = p.mk_at(Nk.N_DECL_EFFECT_OP, on);
        op.name_id = p.interner.intern(on.start, on.len);
        op.p.sptr = on.start;
        op.p.slen = on.len;
        if (p.accept(Tk.TOKEN_COLON))
        {
            bool sv = p.in_fn_sig;
            p.in_fn_sig = true;
            Node* arg = p.parse_type();
            p.add(op, arg);
            if (p.accept(Tk.TOKEN_ARROW) || p.accept(Tk.TOKEN_ARROW_ASCII))
            {
                Node* ret = p.parse_type();
                Node* rw = p.mk(Nk.N_TY_CONSTRAINT, on.line, on.col);
                p.add(rw, ret);
                p.add(op, rw);
            }
            p.in_fn_sig = sv;
        }
        p.add(n, op);
        p.skip_newlines();
    }
    if (indented) { while (p.accept(Tk.TOKEN_DEDENT)) {} }
    if (braced) { p.expect(Tk.TOKEN_RBRACE, 1095, "expected '}' to close effect body"); }
    return n;
}

fn Node* Parser.parse_interface_decl(Parser* p, bool is_pub)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_DECL_INTERFACE, t);
    if (is_pub) { n.flags = n.flags | pfront_core::NF_PUB; }
    Tok nm = p.cur();
    if (!tok_is_member_name(nm.type))
    {
        p.err(1096, "expected an interface name");
        p.sync();
        return n;
    }
    p.advance();
    n.name_id = p.interner.intern(nm.start, nm.len);
    n.p.sptr = nm.start;
    n.p.slen = nm.len;
    p.parse_typarams(n);

    // A single-method interface is often written on ONE line:
    //     interface Add   fn add : (Self, Self) -> Self
    // Skipping newlines first and then demanding an INDENT or `{` missed
    // that form entirely, so the method was left to be parsed as a
    // top-level declaration and `Self` escaped the interface's scope.
    if (p.check(Tk.TOKEN_KW_FN))
    {
        Node* m = p.parse_fn_decl(false);
        if (m != null) { p.add(n, m); }
        p.skip_newlines();
        return n;
    }

    p.skip_newlines();
    bool indented = p.accept(Tk.TOKEN_INDENT);
    bool braced = false;
    if (!indented) { braced = p.accept(Tk.TOKEN_LBRACE); }
    p.skip_newlines();
    while (!p.at_end())
    {
        if (braced && p.check(Tk.TOKEN_RBRACE)) { break; }
        if (indented && p.check(Tk.TOKEN_DEDENT)) { break; }
        if (!braced && !indented) { break; }
        if (p.check(Tk.TOKEN_KW_FN))
        {
            p.add(n, p.parse_fn_decl(false));
        }
        else if (p.check(Tk.TOKEN_NEWLINE)) { p.advance(); }
        else { break; }
        p.skip_newlines();
    }
    if (indented) { while (p.accept(Tk.TOKEN_DEDENT)) {} }
    if (braced) { p.expect(Tk.TOKEN_RBRACE, 1097, "expected '}' to close interface"); }
    return n;
}

fn Node* Parser.parse_impl_decl(Parser* p, bool is_pub)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_DECL_IMPL, t);
    if (is_pub) { n.flags = n.flags | pfront_core::NF_PUB; }
    p.parse_typarams(n);
    Node* first = p.parse_type();
    /*
     `impl Iface for Type` — `for` is a KEYWORD (TOKEN_KW_FOR), not an
     identifier.

     The check looked for a three-character IDENT, which `for` never is,
     so the interface/target split never happened and the `for` was then
     parsed as a for-LOOP: "expected 'in' in a for loop", on a declaration.

     `impl ... for` has ZERO uses in the stdlib, which is exactly why this
     survived. The IDENT branch is kept in case a soft spelling appears.
    */
    if (p.check(Tk.TOKEN_KW_FOR)
        || (p.check(Tk.TOKEN_IDENT) && p.cur().len == 3))
    {
        // `impl Iface for Type`
        p.advance();
        Node* target = p.parse_type();
        p.add(n, first);
        p.add(n, target);
        n.name_id = first == null ? 0 : first.name_id;
    }
    else
    {
        p.add(n, first);
        n.name_id = first == null ? 0 : first.name_id;
    }
    p.skip_newlines();
    bool indented = p.accept(Tk.TOKEN_INDENT);
    bool braced = false;
    if (!indented) { braced = p.accept(Tk.TOKEN_LBRACE); }
    p.skip_newlines();
    while (!p.at_end())
    {
        if (braced && p.check(Tk.TOKEN_RBRACE)) { break; }
        if (indented && p.check(Tk.TOKEN_DEDENT)) { break; }
        if (!braced && !indented) { break; }
        if (p.check(Tk.TOKEN_KW_FN)) { p.add(n, p.parse_fn_decl(false)); }
        else if (p.check(Tk.TOKEN_NEWLINE)) { p.advance(); }
        else { break; }
        /*
         Only NEWLINEs between members, never a DEDENT.

         skip_newlines is right; skip_layout would eat the DEDENT that
         closes the impl block, and the loop would then keep taking `fn`
         declarations from the rest of the file. Every function after an
         `impl` ended up nested inside it — silently, with the only symptom
         an "unresolved name" at the first use.

         Same failure as the match-arm loop, and for the same reason: a
         member loop must not consume its own terminator.
        */
        p.skip_newlines();
        // A DEDENT here ends the block even if the member parser already
        // consumed the one it was expecting.
        if (indented && p.check(Tk.TOKEN_DEDENT)) { break; }
        // A top-level declaration keyword also ends it: the impl's own
        // DEDENT may have been absorbed by the last member's body.
        if (indented && tok_starts_decl(p.ct()) && p.cur().col == 1) { break; }
    }
    if (indented) { while (p.accept(Tk.TOKEN_DEDENT)) {} }
    if (braced) { p.expect(Tk.TOKEN_RBRACE, 1098, "expected '}' to close impl"); }
    return n;
}

fn Node* Parser.parse_extern_decl(Parser* p, bool is_pub)
{
    Tok t = p.advance();   // extern
    if (p.check(Tk.TOKEN_LIT_STRING)) { p.advance(); }   // extern "C"
    if (p.check(Tk.TOKEN_KW_FN))
    {
        Node* f = p.parse_fn_decl(is_pub);
        if (f != null)
        {
            f.kind = Nk.N_DECL_EXTERN_FN;
            f.flags = f.flags | pfront_core::NF_EXTERN;
        }
        return f;
    }
    Node* n = p.mk_at(Nk.N_DECL_EXTERN_FN, t);
    n.flags = n.flags | pfront_core::NF_EXTERN;
    p.err(1099, "expected 'fn' after 'extern'");
    p.sync();
    return n;
}

// ── Module path / use / mod ─────────────────────────────────────────────────
fn Node* Parser.parse_module_path(Parser* p)
{
    Tok first = p.cur();
    Node* path = p.mk_at(Nk.N_MODULE_PATH, first);
    if (!tok_is_member_name(first.type))
    {
        p.err(1100, "expected a module path");
        return path;
    }
    p.advance();
    Node* seg = p.mk_at(Nk.N_PATH_SEG, first);
    seg.name_id = p.interner.intern(first.start, first.len);
    seg.p.sptr = first.start;
    seg.p.slen = first.len;
    p.add(path, seg);
    while ((p.check(Tk.TOKEN_DOT) || p.check(Tk.TOKEN_COLONCOLON))
        && tok_is_member_name(p.peek(1).type))
    {
        p.advance();
        Tok nx = p.advance();
        Node* s = p.mk_at(Nk.N_PATH_SEG, nx);
        s.name_id = p.interner.intern(nx.start, nx.len);
        s.p.sptr = nx.start;
        s.p.slen = nx.len;
        p.add(path, s);
    }
    return path;
}

fn Node* Parser.parse_use(Parser* p)
{
    Tok t = p.advance();   // use
    Node* n = p.mk_at(Nk.N_USE, t);
    Node* path = p.parse_module_path();
    p.add(n, path);
    // Build the dotted name so the loader can map it to a file without
    // re-walking the segment list.
    n.name_id = p.dotted_name_of(path);

    if (p.check(Tk.TOKEN_DOT) && p.peek(1).type == Tk.TOKEN_STAR)
    {
        p.advance();
        p.advance();
        n.flags = n.flags | pfront_core::NF_GLOB;
    }
    else if (p.accept(Tk.TOKEN_STAR))
    {
        n.flags = n.flags | pfront_core::NF_GLOB;
    }
    else if (p.check(Tk.TOKEN_DOT) && p.peek(1).type == Tk.TOKEN_LBRACE)
    {
        p.advance();
        p.advance();
        p.skip_layout();
        while (!p.check(Tk.TOKEN_RBRACE) && !p.at_end())
        {
            Tok item = p.cur();
            if (item.type != Tk.TOKEN_IDENT && item.type != Tk.TOKEN_TYPEVAR)
            {
                p.err(1101, "expected an imported name");
                break;
            }
            p.advance();
            Node* it = p.mk_at(Nk.N_USE_ITEM, item);
            it.name_id = p.interner.intern(item.start, item.len);
            it.p.sptr = item.start;
            it.p.slen = item.len;
            if (p.check(Tk.TOKEN_KW_AS))
            {
                p.advance();
                Tok al = p.cur();
                if (al.type == Tk.TOKEN_IDENT || al.type == Tk.TOKEN_TYPEVAR)
                {
                    p.advance();
                    it.p.aux = (int)p.interner.intern(al.start, al.len);
                }
            }
            p.add(n, it);
            p.skip_layout();
            if (!p.accept(Tk.TOKEN_COMMA)) { break; }
            p.skip_layout();
        }
        p.expect(Tk.TOKEN_RBRACE, 1102, "expected '}' to close import list");
    }
    else if (p.check(Tk.TOKEN_KW_AS))
    {
        p.advance();
        Tok al = p.cur();
        if (al.type == Tk.TOKEN_IDENT || al.type == Tk.TOKEN_TYPEVAR)
        {
            p.advance();
            n.p.aux = (int)p.interner.intern(al.start, al.len);
        }
        else { p.err(1103, "expected an alias name after 'as'"); }
    }
    p.end_stmt();
    return n;
}

// Joins path segments with '.' and interns the result: "pride.core.mem".
fn uint Parser.dotted_name_of(Parser* p, Node* path)
{
    if (path == null || path.child_count == 0) { return 0; }
    char[512] buf;
    usz pos = 0;
    for (usz i = 0; i < path.child_count; i++)
    {
        Node* seg = path.children[i];
        if (seg == null) { continue; }
        if (i > 0 && pos < 511) { buf[pos] = '.'; pos = pos + 1; }
        for (usz j = 0; j < seg.p.slen && pos < 511; j++)
        {
            buf[pos] = seg.p.sptr[j];
            pos = pos + 1;
        }
    }
    buf[pos] = 0;
    return p.interner.intern(&buf[0], pos);
}

fn Node* Parser.parse_mod(Parser* p)
{
    Tok t = p.advance();   // mod
    Node* n = p.mk_at(Nk.N_MODULE, t);
    Node* path = p.parse_module_path();
    p.add(n, path);
    n.name_id = p.dotted_name_of(path);
    // `mod name` as a header line, or `mod name <block>` as a nested module.
    p.skip_newlines();
    if (p.check(Tk.TOKEN_INDENT))
    {
        p.advance();
        p.skip_newlines();
        while (!p.check(Tk.TOKEN_DEDENT) && !p.at_end())
        {
            Node* d = p.parse_decl();
            if (d != null) { p.add(n, d); }
            if (p.panicking) { p.sync(); }
            p.skip_newlines();
        }
        p.accept(Tk.TOKEN_DEDENT);
    }
    return n;
}

// ── Stage annotations (MSP / CMTT) ──────────────────────────────────────────
// `at Stage L`, `at Stage L+1`, `at Stage 0`. The offset is stored on the node
// so theory_msp can renumber a fragment when it is spliced elsewhere.
fn bool Parser.at_stage_keyword(Parser* p)
{
    // `at` is lexed as an identifier; `Stage` as a TYPEVAR.
    if (!p.check(Tk.TOKEN_IDENT)) { return false; }
    Tok t = p.cur();
    if (t.len != 2 || t.start[0] != 'a' || t.start[1] != 't') { return false; }
    Tok nx = p.peek(1);
    if (nx.type != Tk.TOKEN_TYPEVAR && nx.type != Tk.TOKEN_IDENT) { return false; }
    return nx.len == 5 && nx.start[0] == 'S' && nx.start[1] == 't'
        && nx.start[2] == 'a' && nx.start[3] == 'g' && nx.start[4] == 'e';
}

fn int Parser.parse_stage_offset(Parser* p)
{
    p.advance();   // at
    p.advance();   // Stage
    int base = 0;
    bool relative = false;
    if (p.check(Tk.TOKEN_LIT_INT))
    {
        Tok n = p.advance();
        base = (int)parse_uint_literal(n.start, n.len);
    }
    else if (p.check(Tk.TOKEN_IDENT) || p.check(Tk.TOKEN_TYPEVAR))
    {
        // A symbolic level such as `L` means "relative to the current stage".
        p.advance();
        relative = true;
    }
    if (p.accept(Tk.TOKEN_PLUS))
    {
        if (p.check(Tk.TOKEN_LIT_INT))
        {
            Tok d = p.advance();
            base = base + (int)parse_uint_literal(d.start, d.len);
        }
    }
    else if (p.accept(Tk.TOKEN_MINUS))
    {
        if (p.check(Tk.TOKEN_LIT_INT))
        {
            Tok d = p.advance();
            base = base - (int)parse_uint_literal(d.start, d.len);
        }
    }
    return relative ? base : base;
}

// ── Attributes ──────────────────────────────────────────────────────────────
// #[attr] / #[attr(args)] and #attr forms. Attributes are attached to the
// following declaration as trailing metadata children.
fn void Parser.skip_attributes(Parser* p)
{
    while (p.check(Tk.TOKEN_HASH) || p.check(Tk.TOKEN_AT))
    {
        p.advance();
        if (p.accept(Tk.TOKEN_LBRACK))
        {
            int depth = 1;
            while (depth > 0 && !p.at_end())
            {
                if (p.check(Tk.TOKEN_LBRACK)) { depth = depth + 1; }
                if (p.check(Tk.TOKEN_RBRACK)) { depth = depth - 1; }
                p.advance();
            }
        }
        else
        {
            if (p.check(Tk.TOKEN_IDENT) || p.check(Tk.TOKEN_TYPEVAR)) { p.advance(); }
            if (p.accept(Tk.TOKEN_LPAREN))
            {
                int depth = 1;
                while (depth > 0 && !p.at_end())
                {
                    if (p.check(Tk.TOKEN_LPAREN)) { depth = depth + 1; }
                    if (p.check(Tk.TOKEN_RPAREN)) { depth = depth - 1; }
                    p.advance();
                }
            }
        }
        p.skip_newlines();
    }
}

// Trailing attributes: `fn f : T -> U   #extern("name") #cc(c)`. These sit at
// the END of a signature line, so every declaration parser must tolerate them
// before the layout terminator. Skipping them here keeps that in one place.
fn void Parser.skip_trailing_attrs(Parser* p)
{
    while (p.check(Tk.TOKEN_HASH) || p.check(Tk.TOKEN_AT))
    {
        p.advance();
        if (p.check(Tk.TOKEN_LBRACK))
        {
            p.advance();
            int depth = 1;
            while (depth > 0 && !p.at_end())
            {
                if (p.check(Tk.TOKEN_LBRACK)) { depth = depth + 1; }
                if (p.check(Tk.TOKEN_RBRACK)) { depth = depth - 1; }
                p.advance();
            }
            continue;
        }
        // #name or #name(args) — also accept keyword-valued attribute names
        // such as #extern / #inline / #packed, which the lexer keywordises.
        if (!p.check(Tk.TOKEN_NEWLINE) && !p.at_end()) { p.advance(); }
        if (p.check(Tk.TOKEN_LPAREN))
        {
            p.advance();
            int depth = 1;
            while (depth > 0 && !p.at_end())
            {
                if (p.check(Tk.TOKEN_LPAREN)) { depth = depth + 1; }
                if (p.check(Tk.TOKEN_RPAREN)) { depth = depth - 1; }
                p.advance();
            }
        }
    }
}

fn Node* Parser.parse_decl(Parser* p)
{
    p.skip_newlines();
    p.skip_attributes();
    p.skip_newlines();
    if (p.at_end()) { return null; }

    // Doc comments attach to the next declaration.
    Node* doc = null;
    while (p.check(Tk.TOKEN_DOC_COMMENT))
    {
        Tok d = p.advance();
        if (doc == null)
        {
            doc = p.mk_at(Nk.N_DOC, d);
            doc.p.sptr = d.start;
            doc.p.slen = d.len;
        }
        p.skip_newlines();
    }

    bool is_pub = false;
    // `pub` is lexed as an identifier; treat it as a modifier when it precedes
    // a declaration keyword.
    if (p.check(Tk.TOKEN_IDENT) && p.cur().len == 3
        && p.cur().start[0] == 'p' && p.cur().start[1] == 'u' && p.cur().start[2] == 'b')
    {
        Tk nx = p.peek(1).type;
        if (nx == Tk.TOKEN_KW_FN || nx == Tk.TOKEN_KW_STRUCT || nx == Tk.TOKEN_KW_ENUM
         || nx == Tk.TOKEN_KW_UNION || nx == Tk.TOKEN_KW_TYPE || nx == Tk.TOKEN_KW_CONST
         || nx == Tk.TOKEN_KW_STATIC || nx == Tk.TOKEN_KW_EFFECT || nx == Tk.TOKEN_KW_LET
         || nx == Tk.TOKEN_KW_NEWTYPE || nx == Tk.TOKEN_KW_INTERFACE || nx == Tk.TOKEN_KW_USE
         || nx == Tk.TOKEN_KW_IMPL || nx == Tk.TOKEN_KW_EXTERN)
        {
            p.advance();
            is_pub = true;
        }
    }

    Node* d = null;
    switch (p.ct())
    {
        case TOKEN_KW_MOD:       d = p.parse_mod();
        case TOKEN_KW_USE:       d = p.parse_use();
        case TOKEN_KW_FN:        d = p.parse_fn_decl(is_pub);
        case TOKEN_KW_STRUCT:    d = p.parse_struct_decl(is_pub, Nk.N_DECL_STRUCT);
        case TOKEN_KW_UNION:     d = p.parse_struct_decl(is_pub, Nk.N_DECL_UNION);
        case TOKEN_KW_ENUM:      d = p.parse_enum_decl(is_pub);
        case TOKEN_KW_TYPE:      d = p.parse_type_alias(is_pub);
        case TOKEN_KW_NEWTYPE:   d = p.parse_newtype(is_pub);
        case TOKEN_KW_EFFECT:    d = p.parse_effect_decl(is_pub);
        case TOKEN_KW_INTERFACE: d = p.parse_interface_decl(is_pub);
        case TOKEN_KW_IMPL:      d = p.parse_impl_decl(is_pub);
        case TOKEN_KW_EXTERN:    d = p.parse_extern_decl(is_pub);
        case TOKEN_KW_MACRO:     d = p.parse_macro_decl();
        case TOKEN_KW_REWRITE:   d = p.parse_rewrite_decl();
        case TOKEN_KW_DIALECT:   d = p.parse_dialect_decl();
        case TOKEN_KW_PGEN:      d = p.parse_pgen_decl();
        case TOKEN_KW_IRDL:      d = p.parse_irdl_decl();
        case TOKEN_KW_LET:       d = p.parse_let();
        case TOKEN_KW_CONST:     d = p.parse_const(false);
        case TOKEN_KW_STATIC:    d = p.parse_const(true);
        case TOKEN_NEWLINE:
        case TOKEN_INDENT:
        case TOKEN_DEDENT:
            p.advance();
            return null;
        default:
        {
            // Top-level expression statement (scripts / REPL-style files).
            d = p.parse_stmt();
        }
    }
    if (d != null)
    {
        if (is_pub) { d.flags = d.flags | pfront_core::NF_PUB; }
        if (doc != null) { d.type_slot = null; p.add(d, doc); }
    }
    return d;
}

// ════════════════════════════════════════════════════════════════════════════
// 8. PROGRAM DRIVER
// ════════════════════════════════════════════════════════════════════════════

fn Node* Parser.parse_program(Parser* p)
{
    Tok start = p.cur();
    Node* prog = p.mk_at(Nk.N_PROGRAM, start);
    p.skip_layout();
    int guard = 0;
    while (!p.at_end())
    {
        usz before_line = (usz)p.cur().line;
        char* before_ptr = p.cur().start;
        Node* d = p.parse_decl();
        if (d != null) { p.add(prog, d); }
        if (p.panicking) { p.sync(); }
        p.skip_layout();
        // Guarantee forward progress: if a production consumed nothing and did
        // not report, force one token forward so we can never spin.
        if (p.cur().start == before_ptr && !p.at_end())
        {
            guard = guard + 1;
            if (guard > 3)
            {
                p.advance();
                guard = 0;
            }
        }
        else { guard = 0; }
    }
    return prog;
}
