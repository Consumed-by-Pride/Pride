/*
 Pride lexer
 Implementation language: C3  (NOT a compilation target, just what the compiler is written in)
 Pipeline: Pride source -> tokens -> Parser -> AST -> ClangIR/LLVM -> native

 This file turns a raw source buffer into a flat token stream.
 The parser (parser.c3) drives this by calling Lexer.next() in a loop.

 Key design notes for whoever writes the parser:
   - Indentation is significant. INDENT/DEDENT/NEWLINE are real tokens.
     Inside (), [] or {} they are suppressed entirely (layout-free regions).
   - Comments use -- for line comments and --[ ... ]-- for nestable block comments.
   - Unicode operators (→ ↦ ∩ ∪ ⊥ ≥ ≤ ≠ ∀ ∃ ∈ ∅ σ φ) are first-class tokens.
   - ~Tree ~Data ~Bytes are single sigil tokens, not ~ followed by an ident.
   - ub! is a single keyword token (the ! is consumed as part of it).
   - Uppercase-starting idents are TOKEN_TYPEVAR. A lone _ is TOKEN_WILDCARD.
   - The token queue can hold up to 256 pending tokens. BOL processing can
     push multiple DEDENT tokens at once, which is why we need the queue.
   - All tokens point into the original source buffer (zero-copy). Don't free
     the source while tokens are still in use.

 Public API:
   Lexer.init(source, length)  -- set up a fresh lexer
   Lexer.next()                -- pull the next token
   Lexer.had_error()           -- true if any lex errors occurred
   Lexer.diag_count()          -- number of diagnostics collected
   Lexer.get_diag(i)           -- fetch diagnostic i
*/

module pfront_lex;

/*
 Every token kind the lexer can produce.
 The parser pattern-matches on these to drive its recursive descent.
*/
enum TokenType : int
{
    // Structural / control tokens
    TOKEN_EOF,       // end of input; always the last token
    TOKEN_INVALID,   // something the lexer couldn't recognise; lex error already recorded

    /*
     Layout tokens (indentation-sensitive, Python-style)
     Suppressed inside (), [] and {}  see: in_layout_suppressed_region
    */
    TOKEN_NEWLINE,   // same indent level, new statement
    TOKEN_INDENT,    // indent increased
    TOKEN_DEDENT,    // indent decreased (may emit several in a row via the queue)

    // Identifiers
    TOKEN_IDENT,     // regular lowercase-starting identifier
    TOKEN_TYPEVAR,   // uppercase-starting identifier  e.g. T, MyType
    TOKEN_WILDCARD,  // lone underscore _  (pattern wildcard / unused binding)

    // Literals
    TOKEN_LIT_INT,
    TOKEN_LIT_FLOAT,
    TOKEN_LIT_BOOL,      // "true" or "false" (resolved at lex time)
    TOKEN_LIT_CHAR,
    TOKEN_LIT_STRING,
    TOKEN_LIT_RAW_BYTES, // b"..." prefix; raw byte sequence, no escape processing
    TOKEN_LIT_NULL,

    // Core language keywords
    TOKEN_KW_FN,
    TOKEN_KW_LET,
    TOKEN_KW_MUT,
    TOKEN_KW_TYPE,
    TOKEN_KW_STRUCT,
    TOKEN_KW_UNION,
    TOKEN_KW_ENUM,
    TOKEN_KW_EFFECT,
    TOKEN_KW_INTERFACE,  // interface declaration
    TOKEN_KW_IMPL,       // impl Interface for Type
    TOKEN_KW_SELF,       // Self type keyword
    TOKEN_KW_VOLATILE,   // volatile read/write
    TOKEN_KW_OFFSETOF,   // offset_of(Type, field)
    TOKEN_KW_SYSCALL,    // syscall(num, ...) — direct kernel syscall
    TOKEN_KW_NAKED,      // #[naked] function attribute
    TOKEN_LABEL_REF,     // 'name — reference to a loop label (for break/continue)
    TOKEN_KW_NEWTYPE,    // newtype — distinct nominal type wrapper
    TOKEN_KW_THREAD_LOCAL, // thread_local — TLS variable declaration
    TOKEN_KW_MACRO,      // macro — declarative macro declaration
    TOKEN_FATARROW,      // => — macro rule separator / fat arrow
    TOKEN_KW_TAIL,       // tail — tail call guarantee
    TOKEN_QUESTION,      // ? — try/propagate operator
    TOKEN_KW_HANDLE,
    TOKEN_KW_MATCH,
    TOKEN_KW_IF,
    TOKEN_KW_ELSE,
    TOKEN_KW_WHILE,
    TOKEN_KW_FOR,
    TOKEN_KW_DO,
    TOKEN_KW_IN,
    TOKEN_KW_AS,
    TOKEN_KW_AND,
    TOKEN_KW_OR,
    TOKEN_KW_NOT,
    TOKEN_KW_RETURN,
    TOKEN_KW_CONTINUE,
    TOKEN_KW_BREAK,
    TOKEN_KW_USE,
    TOKEN_KW_MOD,
    TOKEN_KW_WHERE,
    TOKEN_KW_WITH,
    TOKEN_KW_ALLOC,
    TOKEN_KW_FREE,
    TOKEN_KW_DEFER,
    TOKEN_KW_ASM,

    // Low-level / ABI keywords
    TOKEN_KW_EXTERN,
    TOKEN_KW_EXPORT,
    TOKEN_KW_INLINE,
    TOKEN_KW_NOINLINE,
    TOKEN_KW_PACKED,
    TOKEN_KW_ALIGN,
    TOKEN_KW_ATOMIC,
    TOKEN_KW_STATIC,
    TOKEN_KW_CONST,
    TOKEN_KW_TYPEOF,        // typeof(expr) — C23
    TOKEN_KW_TYPEOF_UNQUAL, // typeof_unqual(expr) — C23
    TOKEN_KW_NULLPTR,       // nullptr — C23 null pointer constant
    TOKEN_KW_CONSTEXPR,     // constexpr — C23 compile-time constant
    TOKEN_KW_DEPRECATED,    // deprecated — for [[deprecated]] attr keyword
    TOKEN_KW_UNSAFE,
    TOKEN_KW_PURE,
    TOKEN_KW_SIZEOF,
    TOKEN_KW_ALIGNOF,
    TOKEN_KW_TRANSMUTE,

    /*
     Explicit UB and safety annotations
     ub! is a single token (not "ub" + "!") — see lex_ident for why
    */
    TOKEN_KW_UB_BANG,    // ub! "message"  marks intentional undefined behaviour
    TOKEN_KW_ASSUME,
    TOKEN_KW_ASSERT,
    TOKEN_KW_INVARIANT,
    TOKEN_KW_UNREACHABLE,
    TOKEN_KW_TRAP,
    TOKEN_KW_POISON,
    TOKEN_KW_FREEZE,
    TOKEN_KW_UNCHECKED,
    TOKEN_KW_FENCE,          // memory fence
    TOKEN_KW_ATOMIC_ADD,     // atomic fetch-add
    TOKEN_KW_ATOMIC_SUB,
    TOKEN_KW_ATOMIC_AND,
    TOKEN_KW_ATOMIC_OR,
    TOKEN_KW_ATOMIC_XOR,
    TOKEN_KW_ATOMIC_XCHG,
    TOKEN_KW_ATOMIC_CMPXCHG,

    /*
     Metaprogramming keywords
     These operate on the compile-time AST, not on runtime values.
    */
    TOKEN_KW_REWRITE,    // first-class term rewriting rule
    TOKEN_KW_PGEN,       // Pattern Generation Language block
    TOKEN_KW_STAGE,
    TOKEN_KW_QUOTE,
    TOKEN_KW_SPLICE,
    TOKEN_KW_UNQUOTE,
    TOKEN_KW_REIFY,
    TOKEN_KW_EVAL,
    TOKEN_KW_COMPTIME,
    TOKEN_KW_RUNTIME,
    TOKEN_KW_PATTERN,
    TOKEN_KW_RULE,
    TOKEN_KW_FIXPOINT,
    TOKEN_KW_META,
    TOKEN_KW_GENERATE,
    TOKEN_KW_LOWER,

    // IRDL / graph IR keywords (used in dialect/backend definition blocks)
    TOKEN_KW_IRDL,
    TOKEN_KW_DIALECT,
    TOKEN_KW_OPCODE,
    TOKEN_KW_REGION,
    TOKEN_KW_BLOCK,
    TOKEN_KW_NODE,
    TOKEN_KW_EDGE,
    TOKEN_KW_HYPEREDGE,
    TOKEN_KW_GRAPH,

    /*
     Code-as-data sigils (AST quotation)
     These are single tokens, NOT a bare ~ followed by an identifier.
     ~Tree  = quote as AST node tree
     ~Data  = quote as raw data
     ~Bytes = quote as byte sequence
    */
    TOKEN_SIGIL_TREE,
    TOKEN_SIGIL_DATA,
    TOKEN_SIGIL_BYTES,

    // Delimiters
    TOKEN_LPAREN,
    TOKEN_RPAREN,
    TOKEN_LBRACK,
    TOKEN_RBRACK,
    TOKEN_LBRACE,
    TOKEN_RBRACE,

    // Punctuation
    TOKEN_COMMA,
    TOKEN_SEMI,
    TOKEN_COLON,
    TOKEN_COLONCOLON,  // ::  module path separator
    TOKEN_DOT,
    TOKEN_DOTDOT,      // ..  range
    TOKEN_DOTDOTEQ,    // ..= inclusive range
    TOKEN_ELLIPSIS,    // ... variadic / spread
    TOKEN_AT,
    TOKEN_HASH,
    TOKEN_TILDE,       // bare ~ (not a sigil; rare, but kept for completeness)
    TOKEN_PLUS_QUESTION,    // +? checked add (C23: ckd_add)
    TOKEN_MINUS_QUESTION,   // -? checked sub (C23: ckd_sub) 
    TOKEN_STAR_QUESTION,    // *? checked mul (C23: ckd_mul)
    TOKEN_PLUS_PERCENT,     // +% wrapping add (defined two's-complement)
    TOKEN_MINUS_PERCENT,    // -% wrapping sub
    TOKEN_STAR_PERCENT,     // *% wrapping mul
    TOKEN_PLUS_PIPE,        // +| saturating add (clamp at INT_MAX/INT_MIN)
    TOKEN_MINUS_PIPE,       // -| saturating sub
    TOKEN_STAR_PIPE,        // *| saturating mul
    TOKEN_BACKTICK,
    TOKEN_DOLLAR,

    // ASCII operators
    TOKEN_ARROW_ASCII,  // ->  (ASCII fallback for →)
    TOKEN_PIPE,         // |
    TOKEN_PIPELINE,     // |>  pipe operator
    TOKEN_PLUS,
    TOKEN_PLUSPLUS,     // ++  rewrite rule composition
    TOKEN_PLUSEQ,
    TOKEN_MINUS,
    TOKEN_MINUSEQ,
    TOKEN_STAR,
    TOKEN_STAREQ,
    TOKEN_SLASH,
    TOKEN_SLASHEQ,
    TOKEN_PERCENT,
    TOKEN_PERCENTEQ,
    TOKEN_AMP,
    TOKEN_AMPEQ,
    TOKEN_AMPAMP,
    TOKEN_PIPEEQ,
    TOKEN_PIPEPIPE,
    TOKEN_XOR,
    TOKEN_XOREQ,
    TOKEN_BANG,
    TOKEN_EQ,
    TOKEN_EQEQ,
    TOKEN_NEQ,
    TOKEN_LT,
    TOKEN_LTEQ,
    TOKEN_GT,
    TOKEN_GTEQ,
    TOKEN_LSHIFT,
    TOKEN_LSHIFTEQ,
    TOKEN_RSHIFT,
    TOKEN_RSHIFTEQ,

    // Unicode operators (matched by raw UTF-8 byte sequence in unicode_operator_at)
    TOKEN_ARROW,       // →  function return type / clause arrow
    TOKEN_MAPSTO,      // ↦  rewrite rule arrow
    TOKEN_INTERSECT,   // ∩  type intersection
    TOKEN_UNION_SYM,   // ∪  type union
    TOKEN_NEGATION,    // ¬  type negation
    TOKEN_BOTTOM,      // ⊥  uninhabited type (ub! has this type)
    TOKEN_GEQ_UNI,     // ≥
    TOKEN_LEQ_UNI,     // ≤
    TOKEN_NEQ_UNI,     // ≠
    TOKEN_FORALL,      // ∀
    TOKEN_EXISTS,      // ∃
    TOKEN_ELEMENT,     // ∈
    TOKEN_EMPTYSET,    // ∅
    TOKEN_SIGMA,       // σ  SSI sigma node (used in metaprogramming, not normal source)
    TOKEN_PHI,         // φ  SSI phi node   (same as above)
    TOKEN_KW_BY,       // by  — step keyword in range literals: 0..n by 2
    TOKEN_DOC_COMMENT  // --- doc comment line (emitted instead of discarding when --- prefix detected)
}

/*
 A single token. Points directly into the source buffer — zero-copy.
 The parser holds onto these; don't free the source while they're live.
*/
struct Token
{
    TokenType type;
    char* start;  // pointer into the original source buffer
    usz len;      // byte length (NOT codepoints for unicode operators)
    int line;     // 1-based line number
    int col;      // 1-based column number
}

// A lex-time error. We collect all of them rather than aborting on the first.
struct Diagnostic
{
    char* msg;
    int line;
    int col;
}

/*
 The full lexer state. Stack-allocate one of these; it owns nothing on the heap.
 Caller owns the source buffer and keeps it alive for the lifetime of the lexer.
*/
struct Lexer
{
    char* source;   // pointer to the source bytes (not null-terminated, use len)
    usz len;        // total byte count of source
    usz pos;        // current read position in source

    int line;       // current line (1-based)
    int col;        // current column (1-based)

    bool bol;          // true when we're at the start of a new line and haven't processed indentation yet
    bool eof_checked;  // guards against running the EOF bracket-balance check more than once

    /*
     Indentation stack. indents[0] is always 0 (the base level).
     Each INDENT push stores the new column count; DEDENTs pop back down.
     Max nesting depth is 255 (indents[1..255]).
    */
    int[256] indents;
    int indent_idx;

    /*
     Bracket depth counters. While any of these are > 0, layout (INDENT/DEDENT/NEWLINE)
     is suppressed. Mismatched brackets are recorded as diagnostics but don't abort.
    */
    int paren_depth;
    int brack_depth;
    int brace_depth;

    /*
     Circular token queue. handle_bol can emit multiple DEDENT tokens at once
     (one per indent level popped), so we buffer them here and drain on next calls.
     Size 256 is plenty — you'd need 255 nested indent levels to fill it.
    */
    Token[256] queue;
    int q_head;
    int q_tail;

    /*
     Diagnostics. We cap at 256; anything beyond that is silently dropped.
     Check had_error first, then iterate diags[0..diag_count-1].
    */
    Diagnostic[256] diags;
    int diag_count;
    bool had_error;
}

// ── Public API ──────────────────────────────────────────────────────────────

<*
 Set up a fresh lexer over a source buffer. Call this before anything else.
 source must stay alive until you're done consuming tokens.
*>
fn void Lexer.init(Lexer* self, char* source, usz length)
{
    self.source = source;
    self.len = length;
    self.pos = 0;
    self.line = 1;
    self.col = 1;
    self.bol = true;
    self.eof_checked = false;
    self.indent_idx = 0;
    self.indents[0] = 0;
    self.paren_depth = 0;
    self.brack_depth = 0;
    self.brace_depth = 0;
    self.q_head = 0;
    self.q_tail = 0;
    self.diag_count = 0;
    self.had_error = false;
}

// ── Internals ────────────────────────────────────────────────────────────────

<*
 Build a token from its parts. All the lex_* functions go through this.
*>
fn Token make_token(TokenType type, char* start, usz len, int line, int col) @private
{
    Token t;
    t.type = type;
    t.start = start;
    t.len = len;
    t.line = line;
    t.col = col;
    return t;
}

<*
 Record a lex error. We never hard-abort — always keep going so we can
 report as many problems as possible in one pass.
*>
fn void emit_error(Lexer* self, char* msg, int line, int col) @private
{
    self.had_error = true;

    if (self.diag_count < 256)
    {
        Diagnostic d;
        d.msg = msg;
        d.line = line;
        d.col = col;
        self.diags[self.diag_count] = d;
        self.diag_count++;
    }
}

<*
 Circular token queue. Used to buffer multiple tokens produced in one shot
 (e.g. several DEDENTs at once during BOL processing).
*>
fn bool q_has(Lexer* self) @private
{
    return self.q_head != self.q_tail;
}

fn bool q_push(Lexer* self, Token t) @private
{
    int next = (self.q_tail + 1) % 256;

    if (next == self.q_head)
    {
        emit_error(self, "lexer token queue overflow", t.line, t.col);
        return false;
    }

    self.queue[self.q_tail] = t;
    self.q_tail = next;
    return true;
}

fn Token q_pop(Lexer* self) @private
{
    Token t = self.queue[self.q_head];
    self.q_head = (self.q_head + 1) % 256;
    return t;
}

<*
 Low-level cursor helpers. peek/peek_at never move pos; advance does.
 Returns 0 (null byte) past end of input — safe to call without bounds checks.
*>
fn bool at_end(Lexer* self) @private
{
    return self.pos >= self.len;
}

fn char peek(Lexer* self) @private
{
    if (self.pos >= self.len) return 0;
    return self.source[self.pos];
}

fn char peek_at(Lexer* self, usz off) @private
{
    usz p = self.pos + off;
    if (p >= self.len) return 0;
    return self.source[p];
}

fn char advance(Lexer* self) @private
{
    if (self.pos >= self.len) return 0;

    char c = self.source[self.pos];
    self.pos++;

    if (c == '\n')
    {
        self.line++;
        self.col = 1;
    }
    else
    {
        self.col++;
    }

    return c;
}

/*
 ── Character classifiers ─────────────────────────────────────────────────
 Plain char predicates — no Lexer state needed.
*/

fn bool is_digit(char c) @private
{
    return c >= '0' && c <= '9';
}

fn bool is_hex(char c) @private
{
    if (c >= '0' && c <= '9') return true;
    if (c >= 'a' && c <= 'f') return true;
    if (c >= 'A' && c <= 'F') return true;
    return false;
}

fn bool is_oct(char c) @private
{
    return c >= '0' && c <= '7';
}

fn bool is_bin(char c) @private
{
    return c == '0' || c == '1';
}

fn bool is_alpha(char c) @private
{
    if (c >= 'a' && c <= 'z') return true;
    if (c >= 'A' && c <= 'Z') return true;
    return false;
}

fn bool is_upper(char c) @private
{
    return c >= 'A' && c <= 'Z';
}

<*
 An ident can start with a letter, underscore, or any high byte (unicode).
 Unicode idents are allowed; the classifier just checks the leading byte.
*>
fn bool is_ident_start(char c) @private
{
    if (is_alpha(c)) return true;
    if (c == '_') return true;
    if ((c & 0x80) != 0) return true;
    return false;
}

fn bool is_ident_cont(char c) @private
{
    if (is_ident_start(c)) return true;
    if (is_digit(c)) return true;
    return false;
}

<*
 When we're inside brackets of any kind, INDENT/DEDENT/NEWLINE are not emitted.
 This lets multi-line expressions flow naturally inside argument lists etc.
*>
fn bool in_layout_suppressed_region(Lexer* self) @private
{
    if (self.paren_depth > 0) return true;
    if (self.brack_depth > 0) return true;
    if (self.brace_depth > 0) return true;
    return false;
}

<*
 Byte-level string comparison used by keyword_type.
 No null terminator assumed on either side.
*>
fn bool span_eq(char* s, usz len, char* lit, usz lit_len) @private
{
    if (len != lit_len) return false;

    for (usz i = 0; i < len; i++)
    {
        if (s[i] != lit[i]) return false;
    }

    return true;
}

<*
 Pride comments:
   line comment:  -- text until end of line
   block comment: --[ ... ]--  (nestable, so --[ --[ ]-- ]-- works fine)
*>
fn bool consume_block_comment(Lexer* self) @private
{
    int start_line = self.line;
    int start_col = self.col;

    advance(self);
    advance(self);
    advance(self);

    int depth = 1;

    while (!at_end(self) && depth > 0)
    {
        if (peek(self) == '-' && peek_at(self, 1) == '-' && peek_at(self, 2) == '[')
        {
            advance(self);
            advance(self);
            advance(self);
            depth++;
        }
        else if (peek(self) == ']' && peek_at(self, 1) == '-' && peek_at(self, 2) == '-')
        {
            advance(self);
            advance(self);
            advance(self);
            depth--;
        }
        else
        {
            advance(self);
        }
    }

    if (depth != 0)
    {
        emit_error(self, "unterminated block comment", start_line, start_col);
        return false;
    }

    return true;
}

fn void consume_line_comment(Lexer* self) @private
{
    // A triple-dash comment  ---  is a doc-comment and gets emitted as a token
    // so the parser can attach it to the following declaration as a NODE_DOC_COMMENT.
    // At this point self.pos is at the first '-' of the '--' sequence.
    // peek_at(self, 2) is the third character — a '-' makes it '---'.
    bool is_doc = peek_at(self, 2) == '-'
               && peek_at(self, 3) != '-';  // avoid '----' being treated as doc
    char* start = self.source + self.pos;
    int   dline = self.line;
    int   dcol  = self.col;

    advance(self);
    advance(self);

    while (!at_end(self) && peek(self) != '\n')
    {
        advance(self);
    }

    // Emit doc-comment token so the parser can attach it to the next decl.
    if (is_doc)
    {
        usz doc_len = (usz)(self.pos - (usz)(start - self.source));
        q_push(self, make_token(TokenType.TOKEN_DOC_COMMENT, start, doc_len, dline, dcol));
    }
}

fn void push_invalid_at(Lexer* self, char* msg, char* start, usz len, int line, int col) @private
{
    emit_error(self, msg, line, col);
    q_push(self, make_token(TokenType.TOKEN_INVALID, start, len, line, col));
}

<*
 Beginning-of-line handler. Called at the start of every new line before
 the first real token. Counts leading spaces, compares to the indent stack,
 and queues the appropriate INDENT / DEDENT / NEWLINE tokens.

 Layout suppression: if we're inside (), [] or {} we just eat whitespace
 and clear bol — no layout tokens are emitted at all.

 Tabs in indentation are a hard error; spaces only.
 Blank lines and comment-only lines are skipped (bol stays active).
*>
fn void handle_bol(Lexer* self) @private
{
    if (!self.bol) return;

    if (in_layout_suppressed_region(self))
    {
        // Inside (), [] or {} there is no INDENT/DEDENT to compute, so this
        // path only had to skip horizontal whitespace. But it runs AFTER
        // skip_trivia has already consumed the newline, which means it is the
        // first thing to look at the new line's leading characters — and it
        // never checked for a comment.
        //
        // A `--` opening a line inside a brace block therefore lexed as two
        // MINUS tokens followed by the comment's words as identifiers:
        //
        //     } else if p < 0 then {
        //         -- Negative tags are placeholders     <- became `- - IDENT...`
        //         unifier_bind(u, pat.tag, target.tag)
        //
        // Every name on the following lines then failed to resolve, and the
        // reported position was the comment rather than the real code.
        while (!at_end(self))
        {
            char c = peek(self);

            if (c == ' ' || c == '\t' || c == '\r')
            {
                advance(self);
                continue;
            }

            if (c == '-' && peek_at(self, 1) == '-')
            {
                if (peek_at(self, 2) == '[')
                {
                    if (!consume_block_comment(self)) { self.bol = false; return; }
                }
                else
                {
                    consume_line_comment(self);
                }
                // A comment-only line leaves us at the newline; consume it and
                // keep scanning, exactly as the unsuppressed path does.
                if (!at_end(self) && peek(self) == '\n') { advance(self); }
                continue;
            }

            if (c == '\n')
            {
                advance(self);
                continue;
            }

            break;
        }

        self.bol = false;
        return;
    }

    int indent = 0;
    int first_line = self.line;
    int first_col = self.col;

    while (!at_end(self))
    {
        char c = peek(self);

        if (c == ' ')
        {
            indent++;
            advance(self);
        }
        else if (c == '\t')
        {
            char* s = self.source + self.pos;
            int l = self.line;
            int col = self.col;
            advance(self);
            push_invalid_at(self, "tabs are not allowed in indentation", s, 1, l, col);
            self.bol = false;
            return;
        }
        else if (c == '\r')
        {
            advance(self);
        }
        else if (c == '\n')
        {
            advance(self);
            indent = 0;
            first_line = self.line;
            first_col = self.col;
        }
        else if (peek(self) == '-' && peek_at(self, 1) == '-')
        {
            if (peek_at(self, 2) == '[')
            {
                if (!consume_block_comment(self))
                {
                    self.bol = false;
                    return;
                }
            }
            else
            {
                consume_line_comment(self);

                if (!at_end(self) && peek(self) == '\n')
                {
                    advance(self);
                    indent = 0;
                    first_line = self.line;
                    first_col = self.col;
                }
                else
                {
                    break;
                }
            }
        }
        else
        {
            break;
        }
    }

    if (at_end(self))
    {
        self.bol = false;
        return;
    }

    int top = self.indents[self.indent_idx];

    if (indent > top)
    {
        if (self.indent_idx >= 255)
        {
            push_invalid_at(self, "indentation nesting too deep", self.source + self.pos, 0, first_line, first_col);
            self.bol = false;
            return;
        }

        self.indent_idx++;
        self.indents[self.indent_idx] = indent;
        q_push(self, make_token(TokenType.TOKEN_INDENT, self.source + self.pos, 0, self.line, self.col));
    }
    else if (indent < top)
    {
        while (self.indent_idx > 0 && indent < self.indents[self.indent_idx])
        {
            // Carry the indent level being CLOSED in the token's `len` field.
            // Every DEDENT in a run otherwise shares the target column, so a
            // parser cannot tell which nesting level each one ends. The parser
            // uses this to close exactly its own blocks.
            Token dd = make_token(TokenType.TOKEN_DEDENT, self.source + self.pos, 0, self.line, self.col);
            dd.len = (usz)self.indents[self.indent_idx];
            q_push(self, dd);
            self.indent_idx--;
        }

        if (indent != self.indents[self.indent_idx])
        {
            // Hanging indent. Real Pride uses continuation lines aligned to a
            // column that was never pushed as a block level:
            //
            //     let t = if flag then
            //               1
            //             else            <-- lands between two levels
            //               2
            //
            // Rejecting this outright made every such file unparseable. The
            // dedent loop above has already popped to the nearest level that
            // is <= indent, so the structure is unambiguous.
            //
            // It is NOT safe to simply overwrite the top of the stack. When
            // the observed column is DEEPER than that enclosing level, the
            // level being written over is a REAL block that has not ended,
            // and destroying it means its closing DEDENT is never emitted:
            //
            //     fn a : (i64, i64) -> i64
            //       | (m, e) ->
            //         if m == 0i64          <- clause body, level 4
            //           1i64
            //         else if e >= 0i64 &&
            //                 m <= 9i64     <- continuation, level 12
            //           2i64                <- pops 12, lands at 6 > 4
            //                                  overwriting made level 4 vanish
            //         else if e >= 1i64 &&
            //                 m <= 8i64
            //           3i64
            //         else 0i64
            //     fn b : ...                <- silently parsed INSIDE fn a
            //
            // Each wrapped `else if` consumed one stack slot this way. Two of
            // them walked the stack to index 0 and clobbered the FILE level,
            // after which no DEDENT could ever be emitted (the pop loop is
            // guarded on `indent_idx > 0`). `fn b` was reparented into `fn a`
            // with ZERO diagnostics. Verified on the real indent stack:
            //   L8  REALIGN idx=2  4 -> 6
            //   L9  REALIGN idx=1  2 -> 4
            //   L12 REALIGN idx=0  0 -> 4   <- file level destroyed
            //   L14 REALIGN idx=0  4 -> 0   <- no DEDENT, block never closes
            //
            // So: PUSH a new level when the column is deeper than the
            // enclosing one (it is a genuine hanging level that will get its
            // own DEDENT later), and only overwrite when it is not -- which
            // can only happen at index 0, where there is nothing left to pop.
            if (indent > self.indents[self.indent_idx] && self.indent_idx < 255)
            {
                self.indent_idx++;
                self.indents[self.indent_idx] = indent;
            }
            else
            {
                self.indents[self.indent_idx] = indent;
            }
        }

        q_push(self, make_token(TokenType.TOKEN_NEWLINE, self.source + self.pos, 0, self.line, self.col));
    }
    else
    {
        if (self.line > 1)
        {
            q_push(self, make_token(TokenType.TOKEN_NEWLINE, self.source + self.pos, 0, self.line, self.col));
        }
    }

    self.bol = false;
}

<*
 Skip horizontal whitespace and comments on the current line.
 Stops and sets bol=true when it hits a newline (handled next call).
*>
fn void skip_trivia(Lexer* self) @private
{
    while (!at_end(self))
    {
        char c = peek(self);

        if (c == ' ' || c == '\t' || c == '\r')
        {
            advance(self);
        }
        else if (c == '\n')
        {
            advance(self);
            self.bol = true;
            return;
        }
        else if (peek(self) == '-' && peek_at(self, 1) == '-')
        {
            if (peek_at(self, 2) == '[')
            {
                if (!consume_block_comment(self)) return;
            }
            else
            {
                consume_line_comment(self);

                if (!at_end(self) && peek(self) == '\n')
                {
                    advance(self);
                    self.bol = true;
                }

                return;
            }
        }
        else
        {
            return;
        }
    }
}

fn bool valid_escape_head(char c) @private
{
    if (c == 'n') return true;
    if (c == 'r') return true;
    if (c == 't') return true;
    if (c == '0') return true;
    if (c == '\\') return true;
    if (c == '\'') return true;
    if (c == '"') return true;
    if (c == 'x') return true;
    if (c == 'u') return true;
    return false;
}

<*
 Lex a string literal. prefix=1 for regular strings, prefix=2 for b"..." raw bytes.
 Handles \n \r \t \0 \\ \' \" \xHH \u{HHHH} escape sequences.
 Single-line only — a newline before the closing quote is a hard error.
*>
fn Token lex_string(Lexer* self, TokenType kind, int prefix) @private
{
    char* start = self.source + self.pos;
    int start_line = self.line;
    int start_col = self.col;

    for (int i = 0; i < prefix; i++)
    {
        advance(self);
    }

    bool terminated = false;

    while (!at_end(self))
    {
        char c = peek(self);

        if (c == '"')
        {
            advance(self);
            terminated = true;
            break;
        }

        if (c == '\n')
        {
            break;
        }

        if (c == '\\')
        {
            advance(self);

            if (at_end(self)) break;
            if (peek(self) == '\n') break;

            char esc = peek(self);

            if (!valid_escape_head(esc))
            {
                emit_error(self, "invalid escape sequence", self.line, self.col);
            }

            advance(self);

            if (esc == 'x')
            {
                if (!is_hex(peek(self)) || !is_hex(peek_at(self, 1)))
                {
                    emit_error(self, "invalid hex escape", self.line, self.col);
                }
                else
                {
                    advance(self);
                    advance(self);
                }
            }
            else if (esc == 'u')
            {
                if (peek(self) != '{')
                {
                    emit_error(self, "invalid unicode escape", self.line, self.col);
                }
                else
                {
                    advance(self);

                    bool saw = false;

                    while (!at_end(self) && peek(self) != '}')
                    {
                        if (!is_hex(peek(self)))
                        {
                            emit_error(self, "invalid unicode escape digit", self.line, self.col);
                            break;
                        }

                        saw = true;
                        advance(self);
                    }

                    if (peek(self) == '}') { advance(self); }
                    else { emit_error(self, "unterminated unicode escape", self.line, self.col); }

                    if (!saw) emit_error(self, "empty unicode escape", self.line, self.col);
                }
            }
        }
        else
        {
            advance(self);
        }
    }

    if (!terminated)
    {
        emit_error(self, "unterminated string literal", start_line, start_col);
        return make_token(TokenType.TOKEN_INVALID, start, (usz)(self.source + self.pos - start), start_line, start_col);
    }

    return make_token(kind, start, (usz)(self.source + self.pos - start), start_line, start_col);
}

fn Token lex_char(Lexer* self) @private
{
    char* start = self.source + self.pos;
    int start_line = self.line;
    int start_col = self.col;

    advance(self);

    bool terminated = false;
    int units = 0;

    while (!at_end(self))
    {
        char c = peek(self);

        if (c == '\'')
        {
            advance(self);
            terminated = true;
            break;
        }

        if (c == '\n')
        {
            break;
        }

        if (c == '\\')
        {
            advance(self);

            if (at_end(self)) break;
            if (peek(self) == '\n') break;

            char esc = peek(self);

            if (!valid_escape_head(esc))
            {
                emit_error(self, "invalid escape sequence", self.line, self.col);
            }

            advance(self);
            units++;

            if (esc == 'x')
            {
                if (!is_hex(peek(self)) || !is_hex(peek_at(self, 1)))
                {
                    emit_error(self, "invalid hex escape", self.line, self.col);
                }
                else
                {
                    advance(self);
                    advance(self);
                }
            }
        }
        else
        {
            advance(self);
            units++;
        }
    }

    if (!terminated)
    {
        emit_error(self, "unterminated character literal", start_line, start_col);
        return make_token(TokenType.TOKEN_INVALID, start, (usz)(self.source + self.pos - start), start_line, start_col);
    }

    if (units == 0)
    {
        emit_error(self, "empty character literal", start_line, start_col);
    }

    return make_token(TokenType.TOKEN_LIT_CHAR, start, (usz)(self.source + self.pos - start), start_line, start_col);
}

fn bool digit_valid_for_base(char c, int base) @private
{
    if (base == 2) return is_bin(c);
    if (base == 8) return is_oct(c);
    if (base == 10) return is_digit(c);
    if (base == 16) return is_hex(c);
    return false;
}

<*
 Scan a run of digits in the given base. Underscores are allowed as separators
 (e.g. 1_000_000) but a trailing underscore is a lex error.
*>
fn bool scan_digits(Lexer* self, int base) @private
{
    bool saw_digit = false;
    bool last_us = false;

    while (!at_end(self))
    {
        char c = peek(self);

        if (c == '_')
        {
            last_us = true;
            advance(self);
            continue;
        }

        if (!digit_valid_for_base(c, base))
        {
            break;
        }

        saw_digit = true;
        last_us = false;
        advance(self);
    }

    return saw_digit && !last_us;
}

<*
 Consume a type suffix after a numeric literal (e.g. i32, u64, f32).
*>
fn void scan_suffix(Lexer* self) @private
{
    while (!at_end(self) && is_ident_cont(peek(self)))
    {
        advance(self);
    }
}

<*
 Lex a numeric literal. Handles:
   decimal     42  3.14  1e10  1.5e-3
   hex         0xFF  0xDEAD_BEEF
   binary      0b1010_1100
   octal       0o755
 All forms accept an optional type suffix (i32, f64, etc.) after the digits.
*>
fn Token lex_number(Lexer* self) @private
{
    char* start = self.source + self.pos;
    int start_line = self.line;
    int start_col = self.col;

    bool is_float = false;
    bool valid_digits = true;

    if (peek(self) == '0' && self.pos + 1 < self.len)
    {
        char n = peek_at(self, 1);

        if (n == 'x' || n == 'X')
        {
            advance(self);
            advance(self);

            valid_digits = scan_digits(self, 16);

            if (is_alpha(peek(self)) || peek(self) == '_')
            {
                scan_suffix(self);
            }
            else if (is_digit(peek(self)))
            {
                emit_error(self, "invalid hexadecimal digit", self.line, self.col);
                scan_suffix(self);
            }

            if (!valid_digits) emit_error(self, "invalid hexadecimal literal", start_line, start_col);

            return make_token(TokenType.TOKEN_LIT_INT, start, (usz)(self.source + self.pos - start), start_line, start_col);
        }

        if (n == 'b' || n == 'B')
        {
            advance(self);
            advance(self);

            valid_digits = scan_digits(self, 2);

            if (is_digit(peek(self)) && !is_bin(peek(self)))
            {
                emit_error(self, "invalid binary digit", self.line, self.col);
                scan_suffix(self);
            }
            else
            {
                scan_suffix(self);
            }

            if (!valid_digits) emit_error(self, "invalid binary literal", start_line, start_col);

            return make_token(TokenType.TOKEN_LIT_INT, start, (usz)(self.source + self.pos - start), start_line, start_col);
        }

        if (n == 'o' || n == 'O')
        {
            advance(self);
            advance(self);

            valid_digits = scan_digits(self, 8);

            if (is_digit(peek(self)) && !is_oct(peek(self)))
            {
                emit_error(self, "invalid octal digit", self.line, self.col);
                scan_suffix(self);
            }
            else
            {
                scan_suffix(self);
            }

            if (!valid_digits) emit_error(self, "invalid octal literal", start_line, start_col);

            return make_token(TokenType.TOKEN_LIT_INT, start, (usz)(self.source + self.pos - start), start_line, start_col);
        }
    }

    scan_digits(self, 10);

    if (peek(self) == '.' && peek_at(self, 1) != '.' && is_digit(peek_at(self, 1)))
    {
        is_float = true;
        advance(self);
        scan_digits(self, 10);
    }

    char e = peek(self);

    if (e == 'e' || e == 'E')
    {
        char p1 = peek_at(self, 1);
        char p2 = peek_at(self, 2);

        if (is_digit(p1) || ((p1 == '+' || p1 == '-') && is_digit(p2)))
        {
            is_float = true;
            advance(self);

            if (peek(self) == '+' || peek(self) == '-')
            {
                advance(self);
            }

            scan_digits(self, 10);
        }
    }

    scan_suffix(self);

    return make_token(is_float ? TokenType.TOKEN_LIT_FLOAT : TokenType.TOKEN_LIT_INT, start, (usz)(self.source + self.pos - start), start_line, start_col);
}

<*
 Map an identifier span to its keyword token type (or TOKEN_IDENT if it's not a keyword).
 Dispatches on length first, then does byte comparisons — no hash table needed.
 Also handles TOKEN_TYPEVAR (uppercase start) and TOKEN_WILDCARD (lone _).
*>
fn TokenType keyword_type(char* p, usz len) @private
{
    switch (len)
    {
        case 2:
            if (span_eq(p, len, "fn", 2)) return TokenType.TOKEN_KW_FN;
            if (span_eq(p, len, "if", 2)) return TokenType.TOKEN_KW_IF;
            if (span_eq(p, len, "as", 2)) return TokenType.TOKEN_KW_AS;
            if (span_eq(p, len, "or", 2)) return TokenType.TOKEN_KW_OR;
            if (span_eq(p, len, "in", 2)) return TokenType.TOKEN_KW_IN;
            if (span_eq(p, len, "by", 2)) return TokenType.TOKEN_KW_BY;
            if (span_eq(p, len, "do", 2)) return TokenType.TOKEN_KW_DO;
            break;

        case 3:
            if (span_eq(p, len, "let", 3)) return TokenType.TOKEN_KW_LET;
            if (span_eq(p, len, "mut", 3)) return TokenType.TOKEN_KW_MUT;
            if (span_eq(p, len, "for", 3)) return TokenType.TOKEN_KW_FOR;
            if (span_eq(p, len, "use", 3)) return TokenType.TOKEN_KW_USE;
            if (span_eq(p, len, "mod", 3)) return TokenType.TOKEN_KW_MOD;
            if (span_eq(p, len, "asm", 3)) return TokenType.TOKEN_KW_ASM;
            if (span_eq(p, len, "and", 3)) return TokenType.TOKEN_KW_AND;
            if (span_eq(p, len, "not", 3)) return TokenType.TOKEN_KW_NOT;
            break;

        case 4:
            if (span_eq(p, len, "type", 4)) return TokenType.TOKEN_KW_TYPE;
            if (span_eq(p, len, "else", 4)) return TokenType.TOKEN_KW_ELSE;
            if (span_eq(p, len, "free", 4)) return TokenType.TOKEN_KW_FREE;
            if (span_eq(p, len, "with", 4)) return TokenType.TOKEN_KW_WITH;
            if (span_eq(p, len, "true", 4)) return TokenType.TOKEN_LIT_BOOL;
            if (span_eq(p, len, "null", 4)) return TokenType.TOKEN_LIT_NULL;
            if (span_eq(p, len, "pure", 4)) return TokenType.TOKEN_KW_PURE;
            if (span_eq(p, len, "trap", 4)) return TokenType.TOKEN_KW_TRAP;
            if (span_eq(p, len, "pgen", 4)) return TokenType.TOKEN_KW_PGEN;
            if (span_eq(p, len, "eval", 4)) return TokenType.TOKEN_KW_EVAL;
            if (span_eq(p, len, "rule", 4)) return TokenType.TOKEN_KW_RULE;
            if (span_eq(p, len, "meta", 4)) return TokenType.TOKEN_KW_META;
            if (span_eq(p, len, "irdl", 4)) return TokenType.TOKEN_KW_IRDL;
            if (span_eq(p, len, "node", 4)) return TokenType.TOKEN_KW_NODE;
            if (span_eq(p, len, "edge", 4)) return TokenType.TOKEN_KW_EDGE;
            if (span_eq(p, len, "enum", 4)) return TokenType.TOKEN_KW_ENUM;
            if (span_eq(p, len, "self", 4)) return TokenType.TOKEN_KW_SELF;
            if (span_eq(p, len, "impl", 4)) return TokenType.TOKEN_KW_IMPL;
            if (span_eq(p, len, "tail", 4)) return TokenType.TOKEN_KW_TAIL;
            break;

        case 5:
            if (span_eq(p, len, "macro", 5)) return TokenType.TOKEN_KW_MACRO;
            if (span_eq(p, len, "union", 5)) return TokenType.TOKEN_KW_UNION;
            if (span_eq(p, len, "naked", 5)) return TokenType.TOKEN_KW_NAKED;
            if (span_eq(p, len, "match", 5)) return TokenType.TOKEN_KW_MATCH;
            if (span_eq(p, len, "while", 5)) return TokenType.TOKEN_KW_WHILE;
            if (span_eq(p, len, "alloc", 5)) return TokenType.TOKEN_KW_ALLOC;
            if (span_eq(p, len, "where", 5)) return TokenType.TOKEN_KW_WHERE;
            if (span_eq(p, len, "break", 5)) return TokenType.TOKEN_KW_BREAK;
            if (span_eq(p, len, "false", 5)) return TokenType.TOKEN_LIT_BOOL;
            if (span_eq(p, len, "align", 5)) return TokenType.TOKEN_KW_ALIGN;
            if (span_eq(p, len, "const", 5)) return TokenType.TOKEN_KW_CONST;
            if (span_eq(p, len, "stage", 5)) return TokenType.TOKEN_KW_STAGE;
            if (span_eq(p, len, "quote", 5)) return TokenType.TOKEN_KW_QUOTE;
            if (span_eq(p, len, "reify", 5)) return TokenType.TOKEN_KW_REIFY;
            if (span_eq(p, len, "lower", 5)) return TokenType.TOKEN_KW_LOWER;
            if (span_eq(p, len, "block", 5)) return TokenType.TOKEN_KW_BLOCK;
            if (span_eq(p, len, "graph", 5)) return TokenType.TOKEN_KW_GRAPH;
            if (span_eq(p, len, "defer", 5)) return TokenType.TOKEN_KW_DEFER;
            if (span_eq(p, len, "fence", 5)) return TokenType.TOKEN_KW_FENCE;
            break;

        case 6:
            if (span_eq(p, len, "struct", 6)) return TokenType.TOKEN_KW_STRUCT;
            if (span_eq(p, len, "effect", 6)) return TokenType.TOKEN_KW_EFFECT;
            if (span_eq(p, len, "handle", 6)) return TokenType.TOKEN_KW_HANDLE;
            if (span_eq(p, len, "return", 6)) return TokenType.TOKEN_KW_RETURN;
            if (span_eq(p, len, "extern", 6)) return TokenType.TOKEN_KW_EXTERN;
            if (span_eq(p, len, "export", 6)) return TokenType.TOKEN_KW_EXPORT;
            if (span_eq(p, len, "inline", 6)) return TokenType.TOKEN_KW_INLINE;
            if (span_eq(p, len, "packed", 6)) return TokenType.TOKEN_KW_PACKED;
            if (span_eq(p, len, "sizeof", 6)) return TokenType.TOKEN_KW_SIZEOF;
            if (span_eq(p, len, "static", 6)) return TokenType.TOKEN_KW_STATIC;
            if (span_eq(p, len, "unsafe", 6)) return TokenType.TOKEN_KW_UNSAFE;
            if (span_eq(p, len, "atomic", 6)) return TokenType.TOKEN_KW_ATOMIC;
            if (span_eq(p, len, "assume", 6)) return TokenType.TOKEN_KW_ASSUME;
            if (span_eq(p, len, "assert", 6)) return TokenType.TOKEN_KW_ASSERT;
            if (span_eq(p, len, "poison", 6)) return TokenType.TOKEN_KW_POISON;
            if (span_eq(p, len, "freeze", 6)) return TokenType.TOKEN_KW_FREEZE;
            if (span_eq(p, len, "splice", 6)) return TokenType.TOKEN_KW_SPLICE;
            if (span_eq(p, len, "region", 6)) return TokenType.TOKEN_KW_REGION;
            if (span_eq(p, len, "opcode", 6)) return TokenType.TOKEN_KW_OPCODE;
            if (span_eq(p, len, "typeof", 6)) return TokenType.TOKEN_KW_TYPEOF;
            break;

        case 7:
            if (span_eq(p, len, "newtype", 7)) return TokenType.TOKEN_KW_NEWTYPE;
            if (span_eq(p, len, "syscall", 7)) return TokenType.TOKEN_KW_SYSCALL;
            if (span_eq(p, len, "rewrite", 7)) return TokenType.TOKEN_KW_REWRITE;
            if (span_eq(p, len, "alignof", 7)) return TokenType.TOKEN_KW_ALIGNOF;
            if (span_eq(p, len, "runtime", 7)) return TokenType.TOKEN_KW_RUNTIME;
            if (span_eq(p, len, "pattern", 7)) return TokenType.TOKEN_KW_PATTERN;
            if (span_eq(p, len, "unquote", 7)) return TokenType.TOKEN_KW_UNQUOTE;
            if (span_eq(p, len, "dialect", 7)) return TokenType.TOKEN_KW_DIALECT;
            if (span_eq(p, len, "nullptr", 7)) return TokenType.TOKEN_KW_NULLPTR;
            break;

        case 8:
            if (span_eq(p, len, "volatile", 8)) return TokenType.TOKEN_KW_VOLATILE;
            if (span_eq(p, len, "continue", 8)) return TokenType.TOKEN_KW_CONTINUE;
            if (span_eq(p, len, "noinline", 8)) return TokenType.TOKEN_KW_NOINLINE;
            if (span_eq(p, len, "comptime", 8)) return TokenType.TOKEN_KW_COMPTIME;
            if (span_eq(p, len, "fixpoint", 8)) return TokenType.TOKEN_KW_FIXPOINT;
            if (span_eq(p, len, "generate", 8)) return TokenType.TOKEN_KW_GENERATE;
            // The spec (§14) writes `offsetof`; only `offset_of` was
            // recognised, so the spec spelling lexed as an identifier and
            // `offsetof(V, y)` parsed as a call to an undefined function.
            if (span_eq(p, len, "offsetof", 8)) return TokenType.TOKEN_KW_OFFSETOF;
            break;

        case 9:
            if (span_eq(p, len, "offset_of", 9)) return TokenType.TOKEN_KW_OFFSETOF;
            if (span_eq(p, len, "atomic_or", 9)) return TokenType.TOKEN_KW_ATOMIC_OR;
            if (span_eq(p, len, "interface", 9)) return TokenType.TOKEN_KW_INTERFACE;
            if (span_eq(p, len, "transmute", 9)) return TokenType.TOKEN_KW_TRANSMUTE;
            if (span_eq(p, len, "unchecked", 9)) return TokenType.TOKEN_KW_UNCHECKED;
            if (span_eq(p, len, "invariant", 9)) return TokenType.TOKEN_KW_INVARIANT;
            if (span_eq(p, len, "hyperedge", 9)) return TokenType.TOKEN_KW_HYPEREDGE;
            if (span_eq(p, len, "constexpr", 9)) return TokenType.TOKEN_KW_CONSTEXPR;
            break;

        case 10:
            if (span_eq(p, len, "atomic_add", 10)) return TokenType.TOKEN_KW_ATOMIC_ADD;
            if (span_eq(p, len, "atomic_sub", 10)) return TokenType.TOKEN_KW_ATOMIC_SUB;
            if (span_eq(p, len, "atomic_and", 10)) return TokenType.TOKEN_KW_ATOMIC_AND;
            if (span_eq(p, len, "atomic_xor", 10)) return TokenType.TOKEN_KW_ATOMIC_XOR;
            break;

        case 11:
            if (span_eq(p, len, "unreachable", 11)) return TokenType.TOKEN_KW_UNREACHABLE;
            if (span_eq(p, len, "atomic_xchg", 11)) return TokenType.TOKEN_KW_ATOMIC_XCHG;
            break;

        case 12:
            if (span_eq(p, len, "thread_local", 12)) return TokenType.TOKEN_KW_THREAD_LOCAL;
            break;

        case 13:
            if (span_eq(p, len, "typeof_unqual", 13)) return TokenType.TOKEN_KW_TYPEOF_UNQUAL;
            break;

        case 14:
            if (span_eq(p, len, "atomic_cmpxchg", 14)) return TokenType.TOKEN_KW_ATOMIC_CMPXCHG;
            break;
    }

    if (len == 1 && p[0] == '_') return TokenType.TOKEN_WILDCARD;
    if (len > 0 && is_upper(p[0])) return TokenType.TOKEN_TYPEVAR;

    return TokenType.TOKEN_IDENT;
}

<*
 Lex an identifier or keyword. Unicode idents are allowed (high bytes pass through).
 Special case: "ub" immediately followed by '!' is consumed as a single TOKEN_KW_UB_BANG.
 This avoids the parser having to glue two tokens together for what is a single concept.
*>
fn Token lex_ident(Lexer* self) @private
{
    char* start = self.source + self.pos;
    int start_line = self.line;
    int start_col = self.col;

    advance(self);

    while (!at_end(self) && is_ident_cont(peek(self)))
    {
        advance(self);
    }

    usz len = (usz)(self.source + self.pos - start);

    if (len == 2 && start[0] == 'u' && start[1] == 'b' && peek(self) == '!')
    {
        advance(self);
        return make_token(TokenType.TOKEN_KW_UB_BANG, start, 3, start_line, start_col);
    }

    TokenType type = keyword_type(start, len);
    return make_token(type, start, len, start_line, start_col);
}

fn bool match_word_after_tilde(Lexer* self, char* word, int word_len) @private
{
    for (int i = 0; i < word_len; i++)
    {
        if (peek_at(self, 1 + (usz)i) != word[i]) return false;
    }

    char after = peek_at(self, 1 + (usz)word_len);

    if (after != 0 && is_ident_cont(after)) return false;

    return true;
}

<*
 Lex a ~ token. If it's immediately followed by Tree/Data/Bytes (no space,
 not continued as a longer ident) we produce the sigil token directly.
 Otherwise we fall back to a bare TOKEN_TILDE.

 Parser note: TOKEN_SIGIL_TREE / _DATA / _BYTES are used to quote expressions
 as AST nodes. The parser should treat them as unary prefix operators that
 wrap their operand in a CodeTree/CodeData/CodeBytes AST node.
*>
fn Token lex_tilde(Lexer* self) @private
{
    char* start = self.source + self.pos;
    int start_line = self.line;
    int start_col = self.col;

    char[4] tree = { 'T', 'r', 'e', 'e' };
    char[4] data = { 'D', 'a', 't', 'a' };
    char[5] bytes = { 'B', 'y', 't', 'e', 's' };

    if (match_word_after_tilde(self, &tree[0], 4))
    {
        for (int i = 0; i < 5; i++) advance(self);
        return make_token(TokenType.TOKEN_SIGIL_TREE, start, 5, start_line, start_col);
    }

    if (match_word_after_tilde(self, &data[0], 4))
    {
        for (int i = 0; i < 5; i++) advance(self);
        return make_token(TokenType.TOKEN_SIGIL_DATA, start, 5, start_line, start_col);
    }

    if (match_word_after_tilde(self, &bytes[0], 5))
    {
        for (int i = 0; i < 6; i++) advance(self);
        return make_token(TokenType.TOKEN_SIGIL_BYTES, start, 6, start_line, start_col);
    }

    advance(self);
    return make_token(TokenType.TOKEN_TILDE, start, 1, start_line, start_col);
}

<*
 Probe the current position for a known Unicode operator sequence.
 We match by raw UTF-8 bytes — no full Unicode decode needed since we only
 care about a fixed set of codepoints. All recognised operators are 2 or 3 bytes.

 Recognised sequences:
   E2 86 92 → TOKEN_ARROW      (→  U+2192)
   E2 86 A6 → TOKEN_MAPSTO     (↦  U+21A6)
   E2 88 A9 → TOKEN_INTERSECT  (∩  U+2229)
   E2 88 AA → TOKEN_UNION_SYM  (∪  U+222A)
   E2 8A A5 → TOKEN_BOTTOM     (⊥  U+22A5)
   E2 89 A5 → TOKEN_GEQ_UNI   (≥  U+2265)
   E2 89 A4 → TOKEN_LEQ_UNI   (≤  U+2264)
   E2 89 A0 → TOKEN_NEQ_UNI   (≠  U+2260)
   E2 88 80 → TOKEN_FORALL     (∀  U+2200)
   E2 88 83 → TOKEN_EXISTS     (∃  U+2203)
   E2 88 88 → TOKEN_ELEMENT    (∈  U+2208)
   E2 88 85 → TOKEN_EMPTYSET   (∅  U+2205)
   CF 83    → TOKEN_SIGMA      (σ  U+03C3 — 2-byte sequence, not 0xE2-prefixed)
   CF 86    → TOKEN_PHI        (φ  U+03C6 — 2-byte sequence, not 0xE2-prefixed)
   C2 AC    → TOKEN_NEGATION   (¬  U+00AC)
*>
fn bool unicode_operator_at(Lexer* self, TokenType* out_type, usz* out_len) @private
{
    char b0 = peek(self);

    if (b0 == (char)0xE2 && self.pos + 2 < self.len)
    {
        char b1 = peek_at(self, 1);
        char b2 = peek_at(self, 2);

        if (b1 == (char)0x86 && b2 == (char)0x92) { *out_type = TokenType.TOKEN_ARROW; *out_len = 3; return true; }
        if (b1 == (char)0x86 && b2 == (char)0xA6) { *out_type = TokenType.TOKEN_MAPSTO; *out_len = 3; return true; }
        if (b1 == (char)0x88 && b2 == (char)0xA9) { *out_type = TokenType.TOKEN_INTERSECT; *out_len = 3; return true; }
        if (b1 == (char)0x88 && b2 == (char)0xAA) { *out_type = TokenType.TOKEN_UNION_SYM; *out_len = 3; return true; }
        if (b1 == (char)0x8A && b2 == (char)0xA5) { *out_type = TokenType.TOKEN_BOTTOM; *out_len = 3; return true; }
        if (b1 == (char)0x89 && b2 == (char)0xA5) { *out_type = TokenType.TOKEN_GEQ_UNI; *out_len = 3; return true; }
        if (b1 == (char)0x89 && b2 == (char)0xA4) { *out_type = TokenType.TOKEN_LEQ_UNI; *out_len = 3; return true; }
        if (b1 == (char)0x89 && b2 == (char)0xA0) { *out_type = TokenType.TOKEN_NEQ_UNI; *out_len = 3; return true; }
        if (b1 == (char)0x88 && b2 == (char)0x80) { *out_type = TokenType.TOKEN_FORALL; *out_len = 3; return true; }
        if (b1 == (char)0x88 && b2 == (char)0x83) { *out_type = TokenType.TOKEN_EXISTS; *out_len = 3; return true; }
        if (b1 == (char)0x88 && b2 == (char)0x88) { *out_type = TokenType.TOKEN_ELEMENT; *out_len = 3; return true; }
        if (b1 == (char)0x88 && b2 == (char)0x85) { *out_type = TokenType.TOKEN_EMPTYSET; *out_len = 3; return true; }
    }

    // σ (U+03C3) and φ (U+03C6) are 2-byte UTF-8 sequences (lead byte 0xCF),
    // NOT part of the 0xE2-prefixed 3-byte block above.
    if (b0 == (char)0xCF && self.pos + 1 < self.len)
    {
        char b1 = peek_at(self, 1);

        if (b1 == (char)0x83) { *out_type = TokenType.TOKEN_SIGMA; *out_len = 2; return true; }
        if (b1 == (char)0x86) { *out_type = TokenType.TOKEN_PHI; *out_len = 2; return true; }
    }

    if (b0 == (char)0xC2 && self.pos + 1 < self.len)
    {
        char b1 = peek_at(self, 1);

        if (b1 == (char)0xAC)
        {
            *out_type = TokenType.TOKEN_NEGATION;
            *out_len = 2;
            return true;
        }
    }

    return false;
}

fn Token lex_unicode_operator(Lexer* self) @private
{
    char* start = self.source + self.pos;
    int start_line = self.line;
    int start_col = self.col;

    TokenType type = TokenType.TOKEN_INVALID;
    usz len = 0;

    if (unicode_operator_at(self, &type, &len))
    {
        for (usz i = 0; i < len; i++)
        {
            advance(self);
        }

        return make_token(type, start, len, start_line, start_col);
    }

    advance(self);
    emit_error(self, "invalid unicode sequence", start_line, start_col);
    return make_token(TokenType.TOKEN_INVALID, start, 1, start_line, start_col);
}

<*
 Lex punctuation and operator tokens. Multi-character operators are checked
 longest-match first (e.g. >>= before >> before >).
*>
fn Token lex_punct(Lexer* self) @private
{
    char* start = self.source + self.pos;
    int start_line = self.line;
    int start_col = self.col;
    char c = peek(self);

    if (c == '.' && peek_at(self, 1) == '.' && peek_at(self, 2) == '=')
    {
        advance(self); advance(self); advance(self);
        return make_token(TokenType.TOKEN_DOTDOTEQ, start, 3, start_line, start_col);
    }

    if (c == '<' && peek_at(self, 1) == '<' && peek_at(self, 2) == '=')
    {
        advance(self); advance(self); advance(self);
        return make_token(TokenType.TOKEN_LSHIFTEQ, start, 3, start_line, start_col);
    }

    if (c == '>' && peek_at(self, 1) == '>' && peek_at(self, 2) == '=')
    {
        advance(self); advance(self); advance(self);
        return make_token(TokenType.TOKEN_RSHIFTEQ, start, 3, start_line, start_col);
    }

    if (c == '.' && peek_at(self, 1) == '.')
    {
        advance(self); advance(self);
        if (self.pos < self.len && self.source[self.pos] == '.')
        {
            self.pos++;
            return make_token(TokenType.TOKEN_ELLIPSIS, start, 3, start_line, start_col);
        }
        return make_token(TokenType.TOKEN_DOTDOT, start, 2, start_line, start_col);
    }

    if (c == ':' && peek_at(self, 1) == ':')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_COLONCOLON, start, 2, start_line, start_col);
    }

    if (c == '-' && peek_at(self, 1) == '>')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_ARROW_ASCII, start, 2, start_line, start_col);
    }

    if (c == '=' && peek_at(self, 1) == '>')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_FATARROW, start, 2, start_line, start_col);
    }

    if (c == '|' && peek_at(self, 1) == '>')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_PIPELINE, start, 2, start_line, start_col);
    }

    if (c == '+' && peek_at(self, 1) == '+')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_PLUSPLUS, start, 2, start_line, start_col);
    }

    if (c == '+' && peek_at(self, 1) == '=')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_PLUSEQ, start, 2, start_line, start_col);
    }

    // Wrapping arithmetic: +%  -%  *%
    if (c == '+' && peek_at(self, 1) == '%')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_PLUS_PERCENT, start, 2, start_line, start_col);
    }
    if (c == '-' && peek_at(self, 1) == '%')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_MINUS_PERCENT, start, 2, start_line, start_col);
    }
    if (c == '*' && peek_at(self, 1) == '%')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_STAR_PERCENT, start, 2, start_line, start_col);
    }

    // Checked arithmetic: +?  -?  *?  (returns {T, bool}; see codegen's
    // llvm.sadd/ssub/smul.with.overflow lowering)
    if (c == '+' && peek_at(self, 1) == '?')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_PLUS_QUESTION, start, 2, start_line, start_col);
    }
    if (c == '-' && peek_at(self, 1) == '?')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_MINUS_QUESTION, start, 2, start_line, start_col);
    }
    if (c == '*' && peek_at(self, 1) == '?')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_STAR_QUESTION, start, 2, start_line, start_col);
    }

    // Saturating arithmetic: +|  -|  *|
    if (c == '+' && peek_at(self, 1) == '|')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_PLUS_PIPE, start, 2, start_line, start_col);
    }
    if (c == '-' && peek_at(self, 1) == '|')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_MINUS_PIPE, start, 2, start_line, start_col);
    }
    if (c == '*' && peek_at(self, 1) == '|')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_STAR_PIPE, start, 2, start_line, start_col);
    }

    if (c == '-' && peek_at(self, 1) == '=')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_MINUSEQ, start, 2, start_line, start_col);
    }

    if (c == '*' && peek_at(self, 1) == '=')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_STAREQ, start, 2, start_line, start_col);
    }

    if (c == '/' && peek_at(self, 1) == '=')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_SLASHEQ, start, 2, start_line, start_col);
    }

    if (c == '%' && peek_at(self, 1) == '=')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_PERCENTEQ, start, 2, start_line, start_col);
    }

    if (c == '&' && peek_at(self, 1) == '=')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_AMPEQ, start, 2, start_line, start_col);
    }

    if (c == '&' && peek_at(self, 1) == '&')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_AMPAMP, start, 2, start_line, start_col);
    }

    if (c == '|' && peek_at(self, 1) == '=')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_PIPEEQ, start, 2, start_line, start_col);
    }

    if (c == '|' && peek_at(self, 1) == '|')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_PIPEPIPE, start, 2, start_line, start_col);
    }

    if (c == '^' && peek_at(self, 1) == '=')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_XOREQ, start, 2, start_line, start_col);
    }

    if (c == '=' && peek_at(self, 1) == '=')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_EQEQ, start, 2, start_line, start_col);
    }

    if (c == '!' && peek_at(self, 1) == '=')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_NEQ, start, 2, start_line, start_col);
    }

    if (c == '<' && peek_at(self, 1) == '<')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_LSHIFT, start, 2, start_line, start_col);
    }

    if (c == '>' && peek_at(self, 1) == '>')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_RSHIFT, start, 2, start_line, start_col);
    }

    if (c == '<' && peek_at(self, 1) == '=')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_LTEQ, start, 2, start_line, start_col);
    }

    if (c == '>' && peek_at(self, 1) == '=')
    {
        advance(self); advance(self);
        return make_token(TokenType.TOKEN_GTEQ, start, 2, start_line, start_col);
    }

    advance(self);

    switch (c)
    {
        case '(':
            self.paren_depth++;
            return make_token(TokenType.TOKEN_LPAREN, start, 1, start_line, start_col);

        case ')':
            if (self.paren_depth == 0) { emit_error(self, "unmatched closing parenthesis", start_line, start_col); }
            else { self.paren_depth--; }
            return make_token(TokenType.TOKEN_RPAREN, start, 1, start_line, start_col);

        case '[':
            self.brack_depth++;
            return make_token(TokenType.TOKEN_LBRACK, start, 1, start_line, start_col);

        case ']':
            if (self.brack_depth == 0) { emit_error(self, "unmatched closing bracket", start_line, start_col); }
            else { self.brack_depth--; }
            return make_token(TokenType.TOKEN_RBRACK, start, 1, start_line, start_col);

        case '{':
            self.brace_depth++;
            return make_token(TokenType.TOKEN_LBRACE, start, 1, start_line, start_col);

        case '}':
            if (self.brace_depth == 0) { emit_error(self, "unmatched closing brace", start_line, start_col); }
            else { self.brace_depth--; }
            return make_token(TokenType.TOKEN_RBRACE, start, 1, start_line, start_col);

        case ',':
            return make_token(TokenType.TOKEN_COMMA, start, 1, start_line, start_col);

        case ';':
            return make_token(TokenType.TOKEN_SEMI, start, 1, start_line, start_col);

        case ':':
            return make_token(TokenType.TOKEN_COLON, start, 1, start_line, start_col);

        case '.':
            return make_token(TokenType.TOKEN_DOT, start, 1, start_line, start_col);

        case '@':
            return make_token(TokenType.TOKEN_AT, start, 1, start_line, start_col);

        case '#':
            return make_token(TokenType.TOKEN_HASH, start, 1, start_line, start_col);

        case '?':
            return make_token(TokenType.TOKEN_QUESTION, start, 1, start_line, start_col);

        case '`':
            return make_token(TokenType.TOKEN_BACKTICK, start, 1, start_line, start_col);

        case '$':
            return make_token(TokenType.TOKEN_DOLLAR, start, 1, start_line, start_col);

        case '|':
            return make_token(TokenType.TOKEN_PIPE, start, 1, start_line, start_col);

        case '&':
            return make_token(TokenType.TOKEN_AMP, start, 1, start_line, start_col);

        case '!':
            return make_token(TokenType.TOKEN_BANG, start, 1, start_line, start_col);

        case '*':
return make_token(TokenType.TOKEN_STAR, start, 1, start_line, start_col);

        case '+':
return make_token(TokenType.TOKEN_PLUS, start, 1, start_line, start_col);

        case '-':
return make_token(TokenType.TOKEN_MINUS, start, 1, start_line, start_col);

        case '/':
            return make_token(TokenType.TOKEN_SLASH, start, 1, start_line, start_col);

        case '%':
            return make_token(TokenType.TOKEN_PERCENT, start, 1, start_line, start_col);

        case '^':
            return make_token(TokenType.TOKEN_XOR, start, 1, start_line, start_col);

        case '=':
            return make_token(TokenType.TOKEN_EQ, start, 1, start_line, start_col);

        case '<':
            return make_token(TokenType.TOKEN_LT, start, 1, start_line, start_col);

        case '>':
            return make_token(TokenType.TOKEN_GT, start, 1, start_line, start_col);
    }

    emit_error(self, "invalid character", start_line, start_col);
    return make_token(TokenType.TOKEN_INVALID, start, 1, start_line, start_col);
}

<*
 Run once at EOF to validate bracket balance. Records an error for each
 unclosed (, [ or { that's still open. The eof_checked flag prevents
 running this more than once if the parser keeps asking for tokens.
*>
fn void check_eof_once(Lexer* self) @private
{
    if (self.eof_checked) return;

    self.eof_checked = true;

    if (self.paren_depth > 0) emit_error(self, "unclosed parenthesis at end of file", self.line, self.col);
    if (self.brack_depth > 0) emit_error(self, "unclosed bracket at end of file", self.line, self.col);
    if (self.brace_depth > 0) emit_error(self, "unclosed brace at end of file", self.line, self.col);
}

<*
 Flush any remaining DEDENT tokens for open indent levels, then emit EOF.
 The parser may call Lexer.next() past EOF — it will keep getting TOKEN_EOF.
*>
fn Token emit_eof(Lexer* self) @private
{
    check_eof_once(self);

    while (self.indent_idx > 0)
    {
        q_push(self, make_token(TokenType.TOKEN_DEDENT, self.source + self.pos, 0, self.line, self.col));
        self.indent_idx--;
    }

    if (q_has(self))
    {
        return q_pop(self);
    }

    return make_token(TokenType.TOKEN_EOF, self.source + self.pos, 0, self.line, self.col);
}

<*
 Pull the next token from the stream. The parser calls this in a loop.
 Returns TOKEN_EOF once the source is exhausted (and keeps returning it after that).
*>
fn Token Lexer.next(Lexer* self)
{
    if (q_has(self))
    {
        return q_pop(self);
    }

    if (self.bol)
    {
        handle_bol(self);
        if (q_has(self)) return q_pop(self);
    }

    skip_trivia(self);

    if (self.bol)
    {
        handle_bol(self);
        if (q_has(self)) return q_pop(self);
    }

    if (at_end(self))
    {
        return emit_eof(self);
    }

    char c = peek(self);

    if (c == 'b' && peek_at(self, 1) == '"')
    {
        return lex_string(self, TokenType.TOKEN_LIT_RAW_BYTES, 2);
    }

    if (c == '"')
    {
        return lex_string(self, TokenType.TOKEN_LIT_STRING, 1);
    }

    if (c == '\'')
    {
        // ' followed by an identifier = label reference ('label_name)
        // ' followed by anything else = character literal
        // Use peek_at(self, 1) because peek(self) still returns the '\'' itself
        // (the quote is at self.pos, not yet consumed).
        //
        // Ambiguity: 'x' (a single-letter/underscore char literal) LOOKS like
        // the start of a label ref ('x_loop) under a naive one-token-of-
        // lookahead check. Disambiguate with one more character of lookahead:
        // if the character immediately after the would-be label start is a
        // closing quote, this is unambiguously a char literal (a label
        // reference is never immediately followed by a closing quote, since
        // it has no closing quote at all), so fall through to lex_char.
        char nc = peek_at(self, 1);
        bool nc_ident_start = (nc >= 'a' && nc <= 'z') || (nc >= 'A' && nc <= 'Z') || nc == '_';
        bool looks_like_char_lit = peek_at(self, 2) == '\'';
        if (nc_ident_start && !looks_like_char_lit)
        {
            // Lex as label ref: consume the ' then read the identifier
            advance(self);  // consume '
            char* ident_start = self.source + self.pos;
            int i_line = self.line; int i_col = self.col;
            while (self.pos < self.len)
            {
                char ic = peek(self);
                if (!((ic>='a'&&ic<='z')||(ic>='A'&&ic<='Z')||(ic>='0'&&ic<='9')||ic=='_')) break;
                advance(self);
            }
            return make_token(TokenType.TOKEN_LABEL_REF, ident_start - 1,
                              (usz)(self.source + self.pos - ident_start + 1), i_line, i_col);
        }
        return lex_char(self);
    }

    if (c == '~')
    {
        return lex_tilde(self);
    }

    if (is_digit(c))
    {
        return lex_number(self);
    }

    if ((c & 0x80) != 0)
    {
        TokenType unicode_type = TokenType.TOKEN_INVALID;
        usz unicode_len = 0;

        if (unicode_operator_at(self, &unicode_type, &unicode_len))
        {
            return lex_unicode_operator(self);
        }

        return lex_ident(self);
    }

    if (is_ident_start(c))
    {
        return lex_ident(self);
    }

    return lex_punct(self);
}

fn bool Lexer.had_errors(Lexer* self)
{
    return self.had_error;
}

fn int Lexer.get_diag_count(Lexer* self)
{
    return self.diag_count;
}

fn Diagnostic Lexer.get_diag(Lexer* self, int i)
{
    return self.diags[i];
}

// ── Display helper (additive; does NOT affect lexing/tokenizing) ─────────────
// Maps a TokenType to a short human-readable name. Used by tooling such as the
// AST printer in pride.c3. Pure presentation — no lexer state is touched.
fn char* token_type_name(TokenType t)
{
    switch (t)
    {
        case TOKEN_EOF:           return "EOF";
        case TOKEN_INVALID:       return "INVALID";
        case TOKEN_NEWLINE:       return "NEWLINE";
        case TOKEN_INDENT:        return "INDENT";
        case TOKEN_DEDENT:        return "DEDENT";
        case TOKEN_IDENT:         return "IDENT";
        case TOKEN_TYPEVAR:       return "TYPEVAR";
        case TOKEN_WILDCARD:      return "_";
        case TOKEN_LIT_INT:       return "INT";
        case TOKEN_LIT_FLOAT:     return "FLOAT";
        case TOKEN_LIT_BOOL:      return "BOOL";
        case TOKEN_LIT_CHAR:      return "CHAR";
        case TOKEN_LIT_STRING:    return "STRING";
        case TOKEN_LIT_RAW_BYTES: return "RAW_BYTES";
        case TOKEN_LIT_NULL:      return "null";
        case TOKEN_KW_FN:         return "fn";
        case TOKEN_KW_LET:        return "let";
        case TOKEN_KW_MUT:        return "mut";
        case TOKEN_KW_TYPE:       return "type";
        case TOKEN_KW_STRUCT:     return "struct";
        case TOKEN_KW_UNION:      return "union";
        case TOKEN_KW_ENUM:       return "enum";
        case TOKEN_KW_EFFECT:     return "effect";
        case TOKEN_KW_INTERFACE:  return "interface";
        case TOKEN_KW_IMPL:       return "impl";
        case TOKEN_KW_SELF:       return "Self";
        case TOKEN_KW_VOLATILE:   return "volatile";
        case TOKEN_KW_OFFSETOF:   return "offset_of";
        case TOKEN_KW_SYSCALL:    return "syscall";
        case TOKEN_KW_NAKED:      return "naked";
        case TOKEN_LABEL_REF:     return "LABEL_REF";
        case TOKEN_KW_NEWTYPE:    return "newtype";
        case TOKEN_KW_THREAD_LOCAL: return "thread_local";
        case TOKEN_KW_MACRO:      return "macro";
        case TOKEN_FATARROW:      return "=>";
        case TOKEN_KW_TAIL:       return "tail";
        case TOKEN_QUESTION:      return "?";
        case TOKEN_KW_HANDLE:     return "handle";
        case TOKEN_KW_MATCH:      return "match";
        case TOKEN_KW_IF:         return "if";
        case TOKEN_KW_ELSE:       return "else";
        case TOKEN_KW_WHILE:      return "while";
        case TOKEN_KW_FOR:        return "for";
        case TOKEN_KW_DO:         return "do";
        case TOKEN_KW_IN:         return "in";
        case TOKEN_KW_AS:         return "as";
        case TOKEN_KW_AND:        return "and";
        case TOKEN_KW_OR:         return "or";
        case TOKEN_KW_NOT:        return "not";
        case TOKEN_KW_RETURN:     return "return";
        case TOKEN_KW_CONTINUE:   return "continue";
        case TOKEN_KW_BREAK:      return "break";
        case TOKEN_KW_USE:        return "use";
        case TOKEN_KW_MOD:        return "mod";
        case TOKEN_KW_WHERE:      return "where";
        case TOKEN_KW_WITH:       return "with";
        case TOKEN_KW_ALLOC:      return "alloc";
        case TOKEN_KW_FREE:       return "free";
        case TOKEN_KW_DEFER:      return "defer";
        case TOKEN_KW_ASM:        return "asm";
        case TOKEN_KW_EXTERN:     return "extern";
        case TOKEN_KW_EXPORT:     return "export";
        case TOKEN_KW_INLINE:     return "inline";
        case TOKEN_KW_NOINLINE:   return "noinline";
        case TOKEN_KW_PACKED:     return "packed";
        case TOKEN_KW_ALIGN:      return "align";
        case TOKEN_KW_ATOMIC:     return "atomic";
        case TOKEN_KW_STATIC:     return "static";
        case TOKEN_KW_CONST:      return "const";
        case TOKEN_KW_TYPEOF:     return "typeof";
        case TOKEN_KW_TYPEOF_UNQUAL: return "typeof_unqual";
        case TOKEN_KW_NULLPTR:    return "nullptr";
        case TOKEN_KW_CONSTEXPR:  return "constexpr";
        case TOKEN_KW_DEPRECATED: return "deprecated";
        case TOKEN_KW_UNSAFE:     return "unsafe";
        case TOKEN_KW_PURE:       return "pure";
        case TOKEN_KW_SIZEOF:     return "sizeof";
        case TOKEN_KW_ALIGNOF:    return "alignof";
        case TOKEN_KW_TRANSMUTE:  return "transmute";
        case TOKEN_KW_UB_BANG:    return "ub!";
        case TOKEN_KW_ASSUME:         return "assume";
        case TOKEN_KW_FENCE:          return "fence";
        case TOKEN_KW_ATOMIC_ADD:     return "atomic_add";
        case TOKEN_KW_ATOMIC_SUB:     return "atomic_sub";
        case TOKEN_KW_ATOMIC_AND:     return "atomic_and";
        case TOKEN_KW_ATOMIC_OR:      return "atomic_or";
        case TOKEN_KW_ATOMIC_XOR:     return "atomic_xor";
        case TOKEN_KW_ATOMIC_XCHG:    return "atomic_xchg";
        case TOKEN_KW_ATOMIC_CMPXCHG: return "atomic_cmpxchg";
        case TOKEN_KW_ASSERT:     return "assert";
        case TOKEN_KW_INVARIANT:  return "invariant";
        case TOKEN_KW_UNREACHABLE:return "unreachable";
        case TOKEN_KW_TRAP:       return "trap";
        case TOKEN_KW_POISON:     return "poison";
        case TOKEN_KW_FREEZE:     return "freeze";
        case TOKEN_KW_UNCHECKED:  return "unchecked";
        case TOKEN_KW_REWRITE:    return "rewrite";
        case TOKEN_KW_PGEN:       return "pgen";
        case TOKEN_KW_STAGE:      return "stage";
        case TOKEN_KW_QUOTE:      return "quote";
        case TOKEN_KW_SPLICE:     return "splice";
        case TOKEN_KW_UNQUOTE:    return "unquote";
        case TOKEN_KW_REIFY:      return "reify";
        case TOKEN_KW_EVAL:       return "eval";
        case TOKEN_KW_COMPTIME:   return "comptime";
        case TOKEN_KW_RUNTIME:    return "runtime";
        case TOKEN_KW_PATTERN:    return "pattern";
        case TOKEN_KW_RULE:       return "rule";
        case TOKEN_KW_FIXPOINT:   return "fixpoint";
        case TOKEN_KW_META:       return "meta";
        case TOKEN_KW_GENERATE:   return "generate";
        case TOKEN_KW_LOWER:      return "lower";
        case TOKEN_KW_IRDL:       return "irdl";
        case TOKEN_KW_DIALECT:    return "dialect";
        case TOKEN_KW_OPCODE:     return "opcode";
        case TOKEN_KW_REGION:     return "region";
        case TOKEN_KW_BLOCK:      return "block";
        case TOKEN_KW_NODE:       return "node";
        case TOKEN_KW_EDGE:       return "edge";
        case TOKEN_KW_HYPEREDGE:  return "hyperedge";
        case TOKEN_KW_GRAPH:      return "graph";
        case TOKEN_SIGIL_TREE:    return "~Tree";
        case TOKEN_SIGIL_DATA:    return "~Data";
        case TOKEN_SIGIL_BYTES:   return "~Bytes";
        case TOKEN_LPAREN:        return "(";
        case TOKEN_RPAREN:        return ")";
        case TOKEN_LBRACK:        return "[";
        case TOKEN_RBRACK:        return "]";
        case TOKEN_LBRACE:        return "{";
        case TOKEN_RBRACE:        return "}";
        case TOKEN_COMMA:         return ",";
        case TOKEN_SEMI:          return ";";
        case TOKEN_COLON:         return ":";
        case TOKEN_COLONCOLON:    return "::";
        case TOKEN_DOT:           return ".";
        case TOKEN_DOTDOT:        return "..";
        case TOKEN_DOTDOTEQ:      return "..=";
        case TOKEN_ELLIPSIS:       return "...";
        case TOKEN_AT:            return "@";
        case TOKEN_HASH:          return "#";
        case TOKEN_TILDE:         return "~";
        case TOKEN_PLUS_QUESTION:   return "+?";
        case TOKEN_MINUS_QUESTION:  return "-?";
        case TOKEN_STAR_QUESTION:   return "*?";
        case TOKEN_PLUS_PERCENT:    return "+%";
        case TOKEN_MINUS_PERCENT:   return "-%";
        case TOKEN_STAR_PERCENT:    return "*%";
        case TOKEN_PLUS_PIPE:       return "+|";
        case TOKEN_MINUS_PIPE:      return "-|";
        case TOKEN_STAR_PIPE:       return "*|";
        case TOKEN_BACKTICK:      return "`";
        case TOKEN_DOLLAR:        return "$";
        case TOKEN_ARROW_ASCII:   return "->";
        case TOKEN_PIPE:          return "|";
        case TOKEN_PIPELINE:      return "|>";
        case TOKEN_PLUS:          return "+";
        case TOKEN_PLUSPLUS:      return "++";
        case TOKEN_PLUSEQ:        return "+=";
        case TOKEN_MINUS:         return "-";
        case TOKEN_MINUSEQ:       return "-=";
        case TOKEN_STAR:          return "*";
        case TOKEN_STAREQ:        return "*=";
        case TOKEN_SLASH:         return "/";
        case TOKEN_SLASHEQ:       return "/=";
        case TOKEN_PERCENT:       return "%";
        case TOKEN_PERCENTEQ:     return "%=";
        case TOKEN_AMP:           return "&";
        case TOKEN_AMPEQ:         return "&=";
        case TOKEN_AMPAMP:        return "&&";
        case TOKEN_PIPEEQ:        return "|=";
        case TOKEN_PIPEPIPE:      return "||";
        case TOKEN_XOR:           return "^";
        case TOKEN_XOREQ:         return "^=";
        case TOKEN_BANG:          return "!";
        case TOKEN_EQ:            return "=";
        case TOKEN_EQEQ:          return "==";
        case TOKEN_NEQ:           return "!=";
        case TOKEN_LT:            return "<";
        case TOKEN_LTEQ:          return "<=";
        case TOKEN_GT:            return ">";
        case TOKEN_GTEQ:          return ">=";
        case TOKEN_LSHIFT:        return "<<";
        case TOKEN_LSHIFTEQ:      return "<<=";
        case TOKEN_RSHIFT:        return ">>";
        case TOKEN_RSHIFTEQ:      return ">>=";
        case TOKEN_ARROW:         return "->";
        case TOKEN_MAPSTO:        return "|->";
        case TOKEN_INTERSECT:     return "&cap;";
        case TOKEN_UNION_SYM:     return "&cup;";
        case TOKEN_NEGATION:      return "~not";
        case TOKEN_BOTTOM:        return "_|_";
        case TOKEN_GEQ_UNI:       return ">=";
        case TOKEN_LEQ_UNI:       return "<=";
        case TOKEN_NEQ_UNI:       return "!=";
        case TOKEN_FORALL:        return "forall";
        case TOKEN_EXISTS:        return "exists";
        case TOKEN_ELEMENT:       return "in-set";
        case TOKEN_EMPTYSET:      return "empty";
        case TOKEN_SIGMA:         return "sigma";
        case TOKEN_PHI:           return "phi";
        case TOKEN_KW_BY:         return "by";
        case TOKEN_DOC_COMMENT:   return "doc_comment";
        default:                  return "?";
    }
}
