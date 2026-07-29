// parser.c3 — Pride recursive-descent parser
// Implementation language: C3 (host).
// Drives lexer.c3's Lexer.next() and produces an ast.c3 AST.
// Layout-aware: INDENT / DEDENT / NEWLINE tokens delimit blocks Python-style.
// Pipeline:  Pride source -> Lexer (tokens) -> Parser (this) -> AST
// Coverage (v.md): modules/use, fn clause syntax + attributes + asm + effect
// rows + generics + where, type/struct/union/effect decls, let/const/static,
// full expression precedence (v.md §23), pattern matching, control flow,
// memory ops, UB/safety, metaprogramming (rewrite/pgen/quote/comptime/stage/
// reify/eval/fixpoint/...), code quotation sigils, and IRDL/dialect blocks.

module parser;

import lexer;
import ast;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn double strtod(char* str, char** endptr);

alias Tt  = lexer::TokenType;
alias Tok = lexer::Token;
alias Node = ast::AstNode;
alias Nk  = ast::NodeKind;

// Bounded scratch buffer for collecting child lists before committing them to
// the arena. 4096 slots is far beyond any realistic single node arity.
const usz SCRATCH = 4096;

// One pending parse diagnostic.
struct ParseError
{
    char* msg;
    int   line;
    int   col;
}

struct Parser
{
    lexer::Lexer* lx;
    ast::AstArena* arena;

    // Two-token lookahead ring. cur is the token under inspection.
    Tok cur;
    Tok la1;            // lookahead 1
    Tok la2;            // lookahead 2
    bool has_la1;
    bool has_la2;

    // Collected diagnostics (independent of the lexer's own).
    ParseError[256] errors;
    int error_count;
    bool had_error;

    // Panic flag: once set, the current production unwinds to a sync point.
    bool panicking;

    // Recursion-depth guard. Recursive-descent over deeply nested input (e.g.
    // thousands of nested parens or indents) would otherwise overflow the C
    // stack and crash. We cap nesting and report a diagnostic instead.
    int depth;
    bool depth_exceeded;

    // True while parsing an fn signature's type (through effect row / where
    // clause). In that context a same-line ASCII `|` is ambiguous between
    // the type-union infix and a one-line clause head
    // (`fn f : (i32, i32) -> i32 | (a, b) -> a + b`) — parse_type_ops uses
    // fn_sig_pipe_is_clause to disambiguate. Outside fn signatures the
    // historical peek heuristic applies (type aliases etc.).
    bool in_fn_sig;
}

// Maximum recursive-descent nesting before we bail out. Each logical nesting
// level (one paren / one block) descends through the ~16-deep precedence chain,
// so native stack frames ≈ depth × 16. Empirically the 8 MB stack overflows
// around 250 paren levels, so we cap well below that.
const int MAX_PARSE_DEPTH = 150;

fn void Parser.init(Parser* self, lexer::Lexer* lx, ast::AstArena* arena)
{
    self.lx = lx;
    self.arena = arena;
    self.has_la1 = false;
    self.has_la2 = false;
    self.error_count = 0;
    self.had_error = false;
    self.in_fn_sig = false;
    self.panicking = false;
    self.depth = 0;
    self.depth_exceeded = false;
    self.cur = lx.next();
}

// Enter one level of recursive descent. Returns false if the depth cap is hit,
// in which case the caller should bail out to avoid a native stack overflow.
fn bool Parser.enter(Parser* self)
{
    self.depth++;
    if (self.depth > MAX_PARSE_DEPTH)
    {
        if (!self.depth_exceeded)
        {
            self.depth_exceeded = true;
            self.error("nesting too deep; input rejected to avoid stack overflow");
        }
        return false;
    }
    return true;
}

fn void Parser.leave(Parser* self)
{
    if (self.depth > 0) self.depth--;
}

fn Tok Parser.peek(Parser* self)
{
    return self.cur;
}

fn Tok Parser.peek1(Parser* self)
{
    if (!self.has_la1)
    {
        self.la1 = self.lx.next();
        self.has_la1 = true;
    }
    return self.la1;
}

fn Tok Parser.peek2(Parser* self)
{
    if (!self.has_la1)
    {
        self.la1 = self.lx.next();
        self.has_la1 = true;
    }
    if (!self.has_la2)
    {
        self.la2 = self.lx.next();
        self.has_la2 = true;
    }
    return self.la2;
}

fn Tok Parser.advance(Parser* self)
{
    Tok prev = self.cur;
    if (self.has_la1)
    {
        self.cur = self.la1;
        if (self.has_la2)
        {
            self.la1 = self.la2;
            self.has_la2 = false;
        }
        else
        {
            self.has_la1 = false;
        }
    }
    else
    {
        self.cur = self.lx.next();
    }
    return prev;
}

fn bool Parser.check(Parser* self, Tt t)
{
    return self.cur.type == t;
}

fn bool Parser.accept(Parser* self, Tt t)
{
    if (self.cur.type == t)
    {
        self.advance();
        return true;
    }
    return false;
}

fn bool Parser.at_end(Parser* self)
{
    return self.cur.type == Tt.TOKEN_EOF;
}

fn void Parser.error(Parser* self, char* msg)
{
    self.had_error = true;
    if (self.panicking) return;   // suppress cascades until we resync
    self.panicking = true;

    if (self.error_count < 256)
    {
        ParseError e;
        e.msg = msg;
        e.line = self.cur.line;
        e.col = self.cur.col;
        self.errors[self.error_count] = e;
        self.error_count++;
    }
}

// Require a token; on mismatch, record an error but keep going.
fn void Parser.expect(Parser* self, Tt t, char* msg)
{
    if (self.cur.type == t)
    {
        self.advance();
        return;
    }
    self.error(msg);
}

// Skip zero or more standalone NEWLINE tokens (blank separators).
fn void Parser.skip_newlines(Parser* self)
{
    // Skip newlines AND doc-comment tokens that appear between declarations.
    // Doc-comment tokens are only meaningful at the top-decl level where
    // parse_top_decl explicitly collects them; everywhere else they're noise.
    while (self.cur.type == Tt.TOKEN_NEWLINE
        || self.cur.type == Tt.TOKEN_DOC_COMMENT)
    {
        self.advance();
    }
}

fn bool Parser.at_block_start(Parser* self)
{
    return self.cur.type == Tt.TOKEN_INDENT;
}

// A node-building helper: a small stack-local scratch list manager.
// A node-building scratch list. Keeps a SMALL inline array on the stack (so
// deeply-recursive parse frames stay tiny) and spills to a heap buffer only for
// the rare wide node (e.g. a match with thousands of arms). This avoids putting
// a multi-KB array on every recursive frame, which previously let ~140 levels of
// nesting overflow the native stack. `items()` returns the active backing store.
const usz SCRATCH_INLINE = 64;

struct Scratch
{
    Node*[SCRATCH_INLINE] inl;   // inline fast path (covers the vast majority)
    Node** heap;                 // overflow buffer (null until needed)
    usz    heap_cap;
    usz    count;
}

extern fn void* realloc(void* p, usz size);

fn void Scratch.reset(Scratch* s)
{
    if (s.heap != null) { free((void*)s.heap); s.heap = null; }
    s.heap_cap = 0;
    s.count = 0;
}

fn void Scratch.push(Scratch* s, Node* n)
{
    if (s.count < SCRATCH_INLINE)
    {
        s.inl[s.count] = n;
        s.count++;
        return;
    }
    // spill to / grow the heap buffer, copying the inline prefix on first spill
    if (s.heap == null)
    {
        usz cap = SCRATCH_INLINE * 4;
        s.heap = (Node**)malloc(cap * ast::NodePtr::size);
        if (s.heap == null) return;   // OOM: drop extra children (bounded, safe)
        s.heap_cap = cap;
        for (usz i = 0; i < SCRATCH_INLINE; i++) s.heap[i] = s.inl[i];
    }
    else if (s.count >= s.heap_cap)
    {
        usz cap = s.heap_cap * 2;
        Node** grown = (Node**)realloc((void*)s.heap, cap * ast::NodePtr::size);
        if (grown == null) return;
        s.heap = grown;
        s.heap_cap = cap;
    }
    s.heap[s.count] = n;
    s.count++;
}

// The active backing array (heap once spilled, else inline).
fn Node** Scratch.items(Scratch* s)
{
    return s.heap != null ? s.heap : &s.inl[0];
}

fn Node* Parser.finish(Parser* self, Nk kind, Scratch* s, int line, int col)
{
    Node* r = ast::node_n(self.arena, kind, s.items(), s.count, line, col);
    s.reset();   // release any heap-spilled buffer (node_n copied the data)
    return r;
}

fn bool tok_text_eq(Tok t, char* lit, usz lit_len) @private
{
    if (t.len != lit_len) return false;
    for (usz i = 0; i < t.len; i++)
    {
        if (t.start[i] != lit[i]) return false;
    }
    return true;
}

// Build a name node (ident/typevar) directly from the current token's span.
fn Node* Parser.name_from(Parser* self, Tok t, Nk kind)
{
    return ast::node_name(self.arena, kind, t.start, t.len, t.line, t.col);
}

// True if the current token can serve as a *member name* after '.' or '::',
// or as an effect-operation name. This is any identifier, type variable, OR
// any keyword — Pride lets keywords be member/operation names (e.g.
// `Mem.alloc`, `IO.read`, `obj.match`). The lexer reports keywords as their
// own token kinds, so we accept the whole keyword range here.
fn bool Parser.at_member_name(Parser* self)
{
    Tt t = self.cur.type;
    if (t == Tt.TOKEN_IDENT) return true;
    if (t == Tt.TOKEN_TYPEVAR) return true;
    // Keyword tokens occupy a contiguous range in the enum, from TOKEN_KW_FN
    // through TOKEN_KW_GRAPH. Accept any of them as a member name.
    if ((int)t >= (int)Tt.TOKEN_KW_FN && (int)t <= (int)Tt.TOKEN_KW_GRAPH) return true;
    if (t == Tt.TOKEN_KW_UB_BANG) return true;
    return false;
}

// Top level

// program ::= { top_decl }
fn Node* Parser.parse_program(Parser* self)
{
    Scratch s;
    s.reset();

    self.skip_newlines();
    while (!self.at_end())
    {
        Node* d = self.parse_top_decl();
        if (d != null) s.push(d);
        self.panicking = false;
        self.depth = 0;
        self.depth_exceeded = false;
        self.skip_newlines();

        // Defensive: ensure forward progress even on an unrecognised token.
        if (d == null && !self.at_end())
        {
            self.advance();
        }
    }

    return self.finish(Nk.NODE_PROGRAM, &s, 1, 1);
}

fn Node* Parser.parse_top_decl(Parser* self)
{
    // Collect any leading doc-comment lines (--- text).
    // skip_newlines() consumes doc-comment tokens too (outside top-decl context),
    // so here we use a bare newline-only skip between lines.
    Node* pending_doc = null;
    while (self.check(Tt.TOKEN_DOC_COMMENT))
    {
        Tok dc = self.advance();
        if (pending_doc == null)
        {
            pending_doc = ast::node_doc_comment(self.arena, dc.start, dc.len, dc.line, dc.col);
        }
        // Skip only newlines between consecutive doc lines, NOT doc-comments.
        while (self.cur.type == Tt.TOKEN_NEWLINE) { self.advance(); }
    }

    // Leading attribute block: #[section("...")] #[packed] #[interrupt] etc.
    // Consume attrs, parse the following declaration, graft attrs onto it.
    if (self.check(Tt.TOKEN_HASH))
    {
        Node* attrs = self.parse_attr_block();
        self.skip_newlines();
        Node* inner = self.parse_top_decl();
        if (inner == null) return attrs;
        // Attach attr list as the first child of the decl node so emit_function
        // and emit_struct_decls can find it via NODE_ATTRIBUTE_LIST child scan.
        if (attrs != null)
        {
            // Prepend: shift existing children and insert attrs at front
            ast::add_child(self.arena, inner, attrs);
            // Rotate: move last child (just added) to front
            if (inner.child_count >= 2)
            {
                Node* tmp = inner.children[inner.child_count - 1];
                for (usz ri = inner.child_count - 1; ri > 0; ri--)
                    { inner.children[ri] = inner.children[ri - 1]; }
                inner.children[0] = tmp;
            }
        }
        // Attach any collected doc-comment to the declaration.
        if (pending_doc != null) { ast::node_attach_doc(inner, pending_doc); }
        return inner;
    }

    switch (self.cur.type)
    {
        case Tt.TOKEN_KW_MOD:     return self.parse_mod();
        case Tt.TOKEN_KW_USE:     return self.parse_use();
        case Tt.TOKEN_KW_FN:
            {
                // Peek: is the next token a name/IDENT (named fn decl)
                // or | / ( (anonymous closure)?
                Tt next = self.peek1().type;
                bool is_closure = (next == Tt.TOKEN_PIPE
                                || next == Tt.TOKEN_LPAREN
                                || next == Tt.TOKEN_ARROW
                                || next == Tt.TOKEN_ARROW_ASCII);
                if (is_closure)
                { return self.parse_closure_expr(); }
                return self.parse_fn();
            }
        case Tt.TOKEN_KW_TYPE:    return self.parse_type_decl();
        case Tt.TOKEN_KW_STRUCT:  return self.parse_struct(false);
        case Tt.TOKEN_KW_UNION:   return self.parse_union(false);
        case Tt.TOKEN_KW_ENUM:    return self.parse_enum();
        case Tt.TOKEN_KW_NEWTYPE: return self.parse_newtype();
        case Tt.TOKEN_KW_MACRO:   return self.parse_macro_decl();
        case Tt.TOKEN_KW_THREAD_LOCAL:
            {
                self.advance(); // thread_local
                Node* inner = self.parse_let();
                return inner != null ? ast::node1(self.arena, Nk.NODE_DECL_TLS, inner, inner.line, inner.col) : null;
            }
        case Tt.TOKEN_KW_INTERFACE: return self.parse_interface();
        case Tt.TOKEN_KW_IMPL:      return self.parse_impl();
        case Tt.TOKEN_KW_EFFECT:  return self.parse_effect_decl();
        case Tt.TOKEN_KW_CONSTEXPR: return self.parse_constexpr_decl();
        case Tt.TOKEN_KW_LET:     return self.parse_let();
        case Tt.TOKEN_KW_CONST:   return self.parse_const_static(Nk.NODE_DECL_CONST);
        case Tt.TOKEN_KW_STATIC:  return self.parse_const_static(Nk.NODE_DECL_STATIC);
        case Tt.TOKEN_KW_IRDL:    return self.parse_irdl();
        case Tt.TOKEN_KW_DIALECT: return self.parse_dialect();
        // Standalone graph-IR declarations (v.md §19 keywords): a `graph`,
        // `node`, `edge`, `hyperedge`, or `block` may appear at the top level,
        // not only nested inside a `dialect`. Reuse the IRDL member parser.
        case Tt.TOKEN_KW_GRAPH:
        case Tt.TOKEN_KW_NODE:
        case Tt.TOKEN_KW_EDGE:
        case Tt.TOKEN_KW_HYPEREDGE:
            return self.parse_irdl_member();
        case Tt.TOKEN_KW_PGEN:    return self.parse_pgen();
        case Tt.TOKEN_KW_HANDLE:  return self.parse_handle();
        case Tt.TOKEN_KW_PATTERN: return self.parse_pattern_decl();
        case Tt.TOKEN_KW_RULE:    return self.parse_named_rule();
        case Tt.TOKEN_KW_REWRITE: return self.parse_rewrite();
        // `operator` is a contextual keyword — checked via IDENT text below.
        default:
            // Friendly guidance for constructs Pride deliberately lacks: a bare
            // `enum`/`class`/`interface`/`trait` at the top level is almost
            // certainly someone reaching for a feature from another language.
            // Point them at the Pride idiom instead of emitting cryptic cascades.
            if (self.cur.type == Tt.TOKEN_IDENT)
            {
                if (tok_text_eq(self.cur, "class", 5) || tok_text_eq(self.cur, "interface", 9))
                {
                    self.error("Pride has no `class`/`interface`; use `struct` for data and free functions for behavior");
                    return self.recover_decl();
                }
                if (tok_text_eq(self.cur, "trait", 5))
                {
                    self.advance();
                    return self.parse_interface();
                }
                // `operator` as a contextual keyword:
                //   operator (+) : (T, T) -> T  | (a, b) -> ...
                if (tok_text_eq(self.cur, "operator", 8))
                {
                    return self.parse_operator_decl();
                }
            }
            // Any other top-level token: parse as an expression statement so
            // standalone metaprogramming/test snippets still produce a graph.
            {
                Node* stmt_node = self.parse_stmt();
                if (pending_doc != null) { ast::node_attach_doc(stmt_node, pending_doc); }
                return stmt_node;
            }
    }
}

// Helper: attach pending_doc to a freshly-parsed decl node (used in the switch
// arms that return directly rather than through the bottom path).
fn Node* Parser.with_doc(Parser* self, Node* decl, Node* doc)
{
    if (doc != null && decl != null) { ast::node_attach_doc(decl, doc); }
    return decl;
}

// Skip tokens until the next plausible top-level declaration boundary, so a
// guidance error above doesn't cascade into dozens of follow-on errors.
fn Node* Parser.recover_decl(Parser* self)
{
    Tok t = self.cur;
    // consume the offending line and any indented block that follows it
    while (!self.at_end() && !self.check(Tt.TOKEN_NEWLINE) && !self.check(Tt.TOKEN_INDENT)) self.advance();
    self.skip_newlines();
    if (self.check(Tt.TOKEN_INDENT))
    {
        int depth = 0;
        self.advance();   // INDENT
        depth++;
        while (depth > 0 && !self.at_end())
        {
            if (self.check(Tt.TOKEN_INDENT)) { depth++; self.advance(); }
            else if (self.check(Tt.TOKEN_DEDENT)) { depth--; self.advance(); }
            else { self.advance(); }
        }
    }
    self.panicking = false;
    return ast::node0(self.arena, Nk.NODE_INVALID, t.line, t.col);
}

// mod NAME <block-of-decls>
fn Node* Parser.parse_mod(Parser* self)
{
    Tok kw = self.advance();   // mod
    Scratch s;
    s.reset();

    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
    {
        Tok name = self.advance();
        s.push(self.name_from(name, Nk.NODE_IDENT));
    }
    else
    {
        self.error("expected module name after 'mod'");
    }

    // Optional indented body of declarations.
    if (self.accept(Tt.TOKEN_NEWLINE)) { /* allow newline before block */ }
    if (self.at_block_start())
    {
        Node* body = self.parse_decl_block();
        s.push(body);
    }

    return self.finish(Nk.NODE_DECL_MOD, &s, kw.line, kw.col);
}

// use path::seg::... (as alias)?
fn Node* Parser.parse_use(Parser* self)
{
    Tok kw = self.advance();   // use
    Scratch s;
    s.reset();

    bool is_pub = false;
    // `pub use` is handled by the caller already setting a pub flag, but
    // support it here for symmetry: `use pub foo.bar` is not valid Pride,
    // but `pub use` preceding tokens may have been consumed.

    Node* path_node = self.parse_module_path();
    s.push(path_node);

    // Detect kind: glob (*), named ({...}), aliased (as Name), plain.
    // parse_module_path stops before `{` and `*` so we check them here directly.
    // Also handle a trailing `::` or `.` that parse_module_path left unconsumed.
    ast::ImportKind kind = ast::ImportKind.IMPORT_MODULE;
    char* alias_ptr = null;
    usz   alias_len = 0;

    // Consume a trailing separator if present (e.g. `use std::` before `{`).
    if (!self.check(Tt.TOKEN_LBRACE) && !self.check(Tt.TOKEN_STAR))
    {
        // no-op: separator was already consumed by parse_module_path
    }

    if (self.accept(Tt.TOKEN_STAR))
    {
        kind = ast::ImportKind.IMPORT_GLOB;
    }
    else if (self.check(Tt.TOKEN_LBRACE))
    {
        kind = ast::ImportKind.IMPORT_NAMED;
        self.advance();  // {
        while (!self.check(Tt.TOKEN_RBRACE) && !self.at_end())
        {
            if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
            {
                Tok nm = self.advance();
                Node* nm_node = self.name_from(nm, Nk.NODE_IDENT);
                // Support `Name as Alias` inside brace list.
                if (self.accept(Tt.TOKEN_KW_AS))
                {
                    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
                    {
                        Tok an = self.advance();
                        s.push(self.name_from(an, Nk.NODE_IDENT));
                    }
                }
                s.push(nm_node);
            }
            else
            {
                self.error("expected name in import list");
                break;
            }
            if (!self.accept(Tt.TOKEN_COMMA)) { break; }
        }
        self.expect(Tt.TOKEN_RBRACE, "expected '}' to close import list");
    }

    if (self.accept(Tt.TOKEN_KW_AS))
    {
        if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
        {
            Tok alias_tok = self.advance();
            alias_ptr = alias_tok.start;
            alias_len = alias_tok.len;
            kind = ast::ImportKind.IMPORT_ALIASED;
            s.push(self.name_from(alias_tok, Nk.NODE_IDENT));
        }
        else
        {
            self.error("expected alias name after 'as'");
        }
    }

    // Build the flat path string from the path_node's children identifiers.
    // For now we use the source text span of the path node directly.
    char* path_ptr = null;
    usz   path_len = 0;
    if (path_node != null && path_node.child_count >= 1)
    {
        // First child is first ident — the path spans from there.
        Node* first = path_node.children[0];
        if (first != null)
        {
            path_ptr = first.p.ident.name_ptr;
            path_len = first.p.ident.name_len;
        }
    }

    Node* n = ast::node_decl_import(self.arena,
                                     path_ptr, path_len,
                                     alias_ptr, alias_len,
                                     is_pub, kind,
                                     s.items(), s.count,
                                     kw.line, kw.col);
    return n;
}

// ── Operator overloading declaration ────────────────────────────────────────
// operator (TOKEN) [#prec(N)] [#assoc(left|right|none)] : Type
//   | (a, b) -> body
//
// The operator token inside the parens can be any binary operator symbol.
// #prec and #assoc attributes are optional; defaults: prec=PREC_MUL, assoc=left.
// After the body, the operator is registered in the arena's PrecTable so that
// subsequent expressions can parse it with the declared precedence.
fn Node* Parser.parse_operator_decl(Parser* self)
{
    int line = self.cur.line;
    int col  = self.cur.col;
    self.advance();   // consume "operator" (contextual keyword as IDENT)

    // Expect the operator token in parens: operator (+)
    self.expect(Tt.TOKEN_LPAREN, "expected '(' after 'operator'");

    Tok op_tok = self.cur;
    if (self.at_end() || self.check(Tt.TOKEN_RPAREN))
    {
        self.error("expected operator token inside 'operator (...)'");
        return ast::node0(self.arena, Nk.NODE_INVALID, line, col);
    }
    self.advance();   // consume the operator token itself

    self.expect(Tt.TOKEN_RPAREN, "expected ')' after operator token");

    // Optional precedence and associativity attributes.
    int   prec  = ast::PREC_MUL;
    ast::Assoc assoc = ast::Assoc.ASSOC_LEFT;

    // #prec(N) — integer literal precedence
    if (self.check(Tt.TOKEN_HASH))
    {
        Tok h = self.advance();   // #
        if (self.check(Tt.TOKEN_IDENT) && tok_text_eq(self.cur, "prec", 4))
        {
            self.advance();
            self.expect(Tt.TOKEN_LPAREN, "expected '(' after #prec");
            if (self.check(Tt.TOKEN_LIT_INT))
            {
                Tok pv = self.advance();
                // Parse integer from token text (Token has no int_val field).
                int pval = 0;
                for (usz pi = 0; pi < pv.len; pi++)
                {
                    char pc = pv.start[pi];
                    if (pc >= '0' && pc <= '9') { pval = pval * 10 + (int)(pc - '0'); }
                }
                prec = (pval > 0 && pval < 99) ? pval : ast::PREC_MUL;
            }
            self.expect(Tt.TOKEN_RPAREN, "expected ')' after precedence value");
        }
        (void)h;
    }

    // #assoc(left|right|none)
    if (self.check(Tt.TOKEN_HASH))
    {
        self.advance();   // #
        if (self.check(Tt.TOKEN_IDENT) && tok_text_eq(self.cur, "assoc", 5))
        {
            self.advance();
            self.expect(Tt.TOKEN_LPAREN, "expected '(' after #assoc");
            if (self.check(Tt.TOKEN_IDENT))
            {
                Tok av = self.advance();
                if (tok_text_eq(av, "right", 5)) { assoc = ast::Assoc.ASSOC_RIGHT; }
                else if (tok_text_eq(av, "none", 4)) { assoc = ast::Assoc.ASSOC_NONE; }
                // else: "left" or anything else → ASSOC_LEFT (default)
            }
            self.expect(Tt.TOKEN_RPAREN, "expected ')' after assoc value");
        }
    }

    // Signature: : Type
    self.expect(Tt.TOKEN_COLON, "expected ':' before operator type signature");
    Node* sig = self.parse_type();

    // Optional effect row
    Node* eff = null;
    if (self.check(Tt.TOKEN_BANG)) { eff = self.parse_effect_row(); }

    // Clause bodies — same as a function.
    self.skip_newlines();
    Node* clauses = self.parse_clauses();

    // Build child list: [sig, (eff), (clauses)]
    Scratch s;
    s.reset();
    s.push(sig);
    if (eff    != null) s.push(eff);
    if (clauses != null) s.push(clauses);

    Node* n = ast::node_decl_operator(self.arena,
                                       op_tok.type, prec, assoc,
                                       s.items(), s.count,
                                       line, col);
    return n;
}

// module_path ::= ident ( :: ident )*
// module_path ::= ident ( ('::' | '.') ident )*
// Pride supports both `std::mem` and `os.linux` notation interchangeably.
// The `{name, name}` grouping is handled by parse_use; this only parses
// the base path before any brace group.
fn Node* Parser.parse_module_path(Parser* self)
{
    Scratch s;
    s.reset();
    int line = self.cur.line;
    int col  = self.cur.col;

    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
    {
        Tok t = self.advance();
        s.push(self.name_from(t, Nk.NODE_IDENT));
    }
    else
    {
        self.error("expected identifier in module path");
    }

    // Accept both `::` and `.` as path separators, stopping before `{` or `*`.
    bool more = true;
    while (more)
    {
        bool got_sep = self.accept(Tt.TOKEN_COLONCOLON) || self.accept(Tt.TOKEN_DOT);
        if (!got_sep) { break; }

        // Stop if the next token is `{` (brace group) or `*` (glob) —
        // parse_use will handle those.
        if (self.check(Tt.TOKEN_LBRACE) || self.check(Tt.TOKEN_STAR)) { break; }

        if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
        {
            Tok t = self.advance();
            s.push(self.name_from(t, Nk.NODE_IDENT));
        }
        else
        {
            self.error("expected identifier in module path");
            break;
        }
    }

    return self.finish(Nk.NODE_MODULE_PATH, &s, line, col);
}

// A generic indented block of declarations (used by mod / irdl / dialect).
fn Node* Parser.parse_decl_block(Parser* self)
{
    Scratch s;
    s.reset();
    int line = self.cur.line;
    int col = self.cur.col;

    self.expect(Tt.TOKEN_INDENT, "expected indented block");
    self.skip_newlines();

    while (!self.check(Tt.TOKEN_DEDENT) && !self.at_end())
    {
        Node* d = self.parse_top_decl();
        if (d != null) s.push(d);
        self.panicking = false;
        self.depth = 0;
        self.depth_exceeded = false;
        self.skip_newlines();
        if (d == null && !self.check(Tt.TOKEN_DEDENT) && !self.at_end())
        {
            self.advance();
        }
    }

    self.accept(Tt.TOKEN_DEDENT);
    return self.finish(Nk.NODE_EXPR_BLOCK, &s, line, col);
}

// Functions (v.md §6)
// fn NAME <Generics>? : Type ! [Effects]?  <attrs>?  <clauses>

// Anonymous closure:  fn | (args) -> body   or  fn (args) -> body
// Creates a NODE_EXPR_CLOSURE node.
// children:  [clause1, clause2, ...]  (one per | pattern -> body arm)
fn Node* Parser.parse_closure_expr(Parser* self)
{
    Tok kw = self.advance();   // fn
    Scratch s;
    s.reset();

    // Optional -> ReturnType annotation
    // Parse clause arms: | (args) -> body
    self.skip_newlines();
    bool indented = self.accept(Tt.TOKEN_INDENT);
    self.skip_newlines();

    while (self.check(Tt.TOKEN_PIPE) || self.check(Tt.TOKEN_LPAREN)
           || self.check(Tt.TOKEN_ARROW) || self.check(Tt.TOKEN_ARROW_ASCII))
    {
        // Each arm: | pattern -> body   (reuse parse_clause machinery)
        Node* clause = self.parse_clause();
        if (clause != null) s.push(clause);
        self.skip_newlines();
        if (!self.check(Tt.TOKEN_PIPE)) break;
    }

    if (indented) self.accept(Tt.TOKEN_DEDENT);

    return self.finish(Nk.NODE_EXPR_CLOSURE, &s, kw.line, kw.col);
}

fn Node* Parser.parse_fn(Parser* self)
{
    Tok kw = self.advance();   // fn
    Scratch s;
    s.reset();

    // Name — also accept keywords that are valid extern/intrinsic names (free, malloc, etc.)
    Node* name = null;
    bool is_keyword_name = (self.cur.type == Tt.TOKEN_KW_FREE      ||
                            self.cur.type == Tt.TOKEN_KW_ALLOC     ||
                            self.cur.type == Tt.TOKEN_KW_DEFER     ||
                            self.cur.type == Tt.TOKEN_KW_WITH      ||
                            self.cur.type == Tt.TOKEN_KW_EXTERN    ||
                            self.cur.type == Tt.TOKEN_KW_IN        ||
                            self.cur.type == Tt.TOKEN_KW_GENERATE  ||
                            self.cur.type == Tt.TOKEN_KW_LOWER     ||
                            self.cur.type == Tt.TOKEN_KW_REIFY     ||
                            self.cur.type == Tt.TOKEN_KW_STAGE     ||
                            self.cur.type == Tt.TOKEN_KW_META      ||
                            self.cur.type == Tt.TOKEN_KW_FIXPOINT  ||
                            self.cur.type == Tt.TOKEN_KW_RUNTIME   ||
                            self.cur.type == Tt.TOKEN_KW_PATTERN   ||
                            self.cur.type == Tt.TOKEN_KW_GRAPH     ||
                            self.cur.type == Tt.TOKEN_KW_BLOCK     ||
                            self.cur.type == Tt.TOKEN_KW_NODE      ||
                            self.cur.type == Tt.TOKEN_KW_REGION);
    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR) || is_keyword_name)
    {
        Tok nt = self.advance();
        name = self.name_from(nt, Nk.NODE_IDENT);
    }
    else
    {
        self.error("expected function name after 'fn'");
        name = ast::node0(self.arena, Nk.NODE_INVALID, kw.line, kw.col);
    }
    s.push(name);

    // Optional generic parameters <A, B : Constraint, ...>
    if (self.check(Tt.TOKEN_LT))
    {
        s.push(self.parse_generics());
    }

    // Pre-signature attributes: fn name #[attr] #[attr] : Type
    // Attributes may appear between the name/generics and the colon.
    if (self.check(Tt.TOKEN_HASH))
    {
        Node* pre_attrs = self.parse_attr_block();
        if (pre_attrs != null) s.push(pre_attrs);
    }

    // Signature ':'  Type (! [Effects])?
    self.expect(Tt.TOKEN_COLON, "expected ':' before function type");
    bool saved_fn_sig = self.in_fn_sig;
    self.in_fn_sig = true;
    Node* sig = self.parse_type();
    s.push(sig);

    // Effect row attached at signature level.
    if (self.check(Tt.TOKEN_BANG))
    {
        s.push(self.parse_effect_row());
    }

    // Common user error: `fn f : T -> U = | p -> body`. Pride has NO `=`
    // between the signature and the clauses (v.md §6.1) — be loud about it
    // instead of letting the `=` cascade into top-level Invalid-node garbage
    // that previously compiled through with only soft warnings and emitted
    // `ret <ty> undef`. Consume the `=` and parse the clauses as usual so
    // this stays a single, precise diagnostic.
    if (self.check(Tt.TOKEN_EQ))
    {
        self.error("unexpected '=' after function signature (clauses follow the signature directly: `| pattern -> body`)");
        self.advance();   // consume '='; clauses still parse → single clean diagnostic
    }

    // The function body region (where clause, attributes, and clauses) usually
    // sits under a single INDENT. We open it here once and close it once, so
    // the where/attr/clause sub-parsers all work at the current level without
    // fighting over the same INDENT/DEDENT pair.
    self.skip_newlines();
    bool body_indented = false;
    if (self.check(Tt.TOKEN_INDENT))
    {
        // Only claim the INDENT as the body region if what's inside is a
        // where/attr/clause head (not, say, a stray nested construct).
        Tt inner = self.peek1().type;
        if (inner == Tt.TOKEN_KW_WHERE || inner == Tt.TOKEN_HASH
            || inner == Tt.TOKEN_PIPE || inner == Tt.TOKEN_ARROW
            || inner == Tt.TOKEN_ARROW_ASCII || inner == Tt.TOKEN_KW_ASM)
        {
            self.advance();
            body_indented = true;
        }
    }
    self.skip_newlines();

    // where clause (now always at the current level).
    if (self.check(Tt.TOKEN_KW_WHERE))
    {
        s.push(self.parse_where());
    }

    // Attributes:  #inline #export(...)  — at the current level.
    self.skip_newlines();
    if (self.check(Tt.TOKEN_HASH))
    {
        Node* attrs = self.parse_attr_block();
        if (attrs != null) s.push(attrs);
    }

    // Clause bodies: `| pat -> body` lines, a single `-> body`, or asm.
    // The fn-signature type context ends here — clause `|`s are patterns now.
    self.in_fn_sig = saved_fn_sig;
    self.skip_newlines();
    Node* clauses = self.parse_clauses();
    if (clauses != null) s.push(clauses);

    self.skip_newlines();
    if (body_indented) self.accept(Tt.TOKEN_DEDENT);

    Node* fn_node = self.finish(Nk.NODE_DECL_FN, &s, kw.line, kw.col);

    // Populate FnData metadata now that we have scanned all clauses.
    // Walk children to count clauses and detect extern/vararg attributes.
    if (fn_node != null)
    {
        uint clause_count = 0;
        uint arity        = 0;
        bool is_extern    = false;
        bool is_variadic  = false;
        bool arity_set    = false;
        for (usz ci = 0; ci < fn_node.child_count; ci++)
        {
            Node* ch = fn_node.children[ci];
            if (ch == null) continue;
            if (ch.kind == ast::NodeKind.NODE_CLAUSE)
            {
                clause_count++;
                // Arity = number of pattern children of the first clause.
                if (!arity_set && ch.child_count >= 1)
                {
                    // Pattern is child[0]; count its fields for tuple patterns,
                    // or 1 for a single-param pattern.
                    Node* pat = ch.children[0];
                    if (pat != null && pat.kind == ast::NodeKind.NODE_PATTERN_TUPLE)
                    {
                        arity = (uint)pat.child_count;
                    }
                    else
                    {
                        arity = (pat != null) ? 1u : 0u;
                    }
                    arity_set = true;
                }
            }
            if (ch.kind == ast::NodeKind.NODE_ATTR_EXTERN)  { is_extern   = true; }
            if (ch.kind == ast::NodeKind.NODE_ATTR_VARARG)   { is_variadic = true; }
        }
        // Intern the function name (child[0] should be NODE_IDENT).
        uint intern_name_id = 0;
        if (fn_node.child_count >= 1 && fn_node.children[0] != null
            && fn_node.children[0].kind == ast::NodeKind.NODE_IDENT)
        {
            Node* nm = fn_node.children[0];
            intern_name_id = self.arena.intern_str(nm.p.ident.name_ptr, nm.p.ident.name_len);
        }
        ast::node_fn_set_meta(fn_node, arity, clause_count,
                              false, false,   // recursion detected later
                              is_extern, is_variadic, intern_name_id);
    }
    return fn_node;
}

// generics ::= '<' generic_param (',' generic_param)* '>'
fn Node* Parser.parse_generics(Parser* self)
{
    Tok lt = self.advance();   // <
    Scratch s;
    s.reset();

    if (!self.check(Tt.TOKEN_GT))
    {
        s.push(self.parse_generic_param());
        while (self.accept(Tt.TOKEN_COMMA))
        {
            s.push(self.parse_generic_param());
        }
    }
    self.expect(Tt.TOKEN_GT, "expected '>' to close generic parameters");
    return self.finish(Nk.NODE_GENERIC_PARAM, &s, lt.line, lt.col);
}

// generic_param ::= TypeVar (':' Type)?
fn Node* Parser.parse_generic_param(Parser* self)
{
    Scratch s;
    s.reset();
    int line = self.cur.line;
    int col = self.cur.col;

    if (self.check(Tt.TOKEN_TYPEVAR) || self.check(Tt.TOKEN_IDENT))
    {
        Tok t = self.advance();
        s.push(self.name_from(t, Nk.NODE_TYPEVAR));
    }
    else
    {
        self.error("expected type parameter name");
    }

    if (self.accept(Tt.TOKEN_COLON))
    {
        s.push(self.parse_type());
    }

    return self.finish(Nk.NODE_PARAM, &s, line, col);
}

// where ::= 'where' constraint ( (',' | NEWLINE) constraint )*
// constraint ::= Type '=' Type   |   Type ':' Type   |   Type
// Constraints may be comma-separated on one line, or one per indented line.
fn Node* Parser.parse_where(Parser* self)
{
    Tok kw = self.advance();   // where
    Scratch s;
    s.reset();

    // The body may be inline (same line) or an indented block of constraints.
    self.skip_newlines();
    bool indented = self.accept(Tt.TOKEN_INDENT);
    self.skip_newlines();

    bool more = true;
    while (more)
    {
        Node* c = self.parse_where_constraint();
        if (c != null) s.push(c);

        // Either a comma on the same line, or a newline starting the next.
        if (self.accept(Tt.TOKEN_COMMA))
        {
            self.skip_newlines();
            more = !self.check(Tt.TOKEN_DEDENT) && !self.at_end();
        }
        else if (self.check(Tt.TOKEN_NEWLINE))
        {
            self.skip_newlines();
            // Continue only if another constraint plausibly follows (a type
            // atom), i.e. we are still inside the indented where-block.
            more = indented
                && (self.check(Tt.TOKEN_TYPEVAR) || self.check(Tt.TOKEN_IDENT));
        }
        else
        {
            more = false;
        }
    }

    if (indented) self.accept(Tt.TOKEN_DEDENT);
    return self.finish(Nk.NODE_WHERE_CLAUSE, &s, kw.line, kw.col);
}

fn Node* Parser.parse_where_constraint(Parser* self)
{
    int line = self.cur.line;
    int col = self.cur.col;
    Node* lhs = self.parse_type();

    // Equality constraint:  C = Pair<A, B>
    if (self.accept(Tt.TOKEN_EQ))
    {
        Node* rhs = self.parse_type();
        return ast::node2(self.arena, Nk.NODE_WHERE_CLAUSE, lhs, rhs, line, col);
    }

    // Bound constraint:  T : Ord
    if (self.accept(Tt.TOKEN_COLON))
    {
        Node* bound = self.parse_type();
        return ast::node2(self.arena, Nk.NODE_PARAM, lhs, bound, line, col);
    }

    return ast::node1(self.arena, Nk.NODE_WHERE_CLAUSE, lhs, line, col);
}

// Attributes: a run of #name or #name(args), possibly across indented lines.
// Parse a single C23-style [[attr]] attribute
fn Node* Parser.parse_one_c23_attr(Parser* self) @private
{
    // Consume first [ already done by caller; consume second [
    if (!self.check(Tt.TOKEN_LBRACK)) { return null; }
    self.advance(); // second [
    Scratch as2; as2.reset();
    int ln = self.cur.line; int cl = self.cur.col;
    // Parse comma-separated attribute names
    while (!self.check(Tt.TOKEN_RBRACK) && !self.check(Tt.TOKEN_EOF))
    {
        if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_KW_DEPRECATED))
        {
            Tok nm = self.advance();
            Nk kind = attr_kind_for(nm);
            Scratch inner; inner.reset();
            inner.push(self.name_from(nm, Nk.NODE_IDENT));
            // Optional (args) or ("message")
            if (self.accept(Tt.TOKEN_LPAREN))
            {
                if (!self.check(Tt.TOKEN_RPAREN)) { inner.push(self.parse_expr()); }
                self.expect(Tt.TOKEN_RPAREN, "expected ')' in [[attr(...)]]");
            }
            as2.push(self.finish(kind, &inner, nm.line, nm.col));
        }
        if (!self.accept(Tt.TOKEN_COMMA)) { break; }
    }
    self.expect(Tt.TOKEN_RBRACK, "expected ']]' — first ']'");
    self.expect(Tt.TOKEN_RBRACK, "expected ']]' — second ']'");
    return self.finish(Nk.NODE_ATTRIBUTE_LIST, &as2, ln, cl);
}

fn Node* Parser.parse_attr_block(Parser* self)
{
    Scratch s;
    s.reset();
    int line = self.cur.line;
    int col = self.cur.col;

    bool indented = self.accept(Tt.TOKEN_INDENT);
    self.skip_newlines();

    // Accept any mix of #[...] and [[...]] attributes
    while (self.check(Tt.TOKEN_HASH) || self.check(Tt.TOKEN_LBRACK))
    {
        if (self.check(Tt.TOKEN_LBRACK))
        {
            // Peek: is it [[? (two consecutive [ means C23 attribute)
            self.advance(); // consume first [
            if (self.check(Tt.TOKEN_LBRACK))
            {
                Node* ca = self.parse_one_c23_attr();
                if (ca != null)
                {
                    // Merge children of the returned LIST into s
                    for (usz ci = 0; ci < ca.child_count; ci++)
                    {
                        if (ca.children[ci] != null) s.push(ca.children[ci]);
                    }
                }
            }
            // else: it was a standalone [ (not an attribute) — bail
            // (we already consumed the [, but can't un-consume; accept mismatch)
        }
        else
        {
            Node* a = self.parse_attribute();
            if (a != null) s.push(a);
        }
        self.skip_newlines();
    }

    if (indented) self.accept(Tt.TOKEN_DEDENT);

    if (s.count == 0) return null;
    return self.finish(Nk.NODE_ATTRIBUTE_LIST, &s, line, col);
}

fn Node* Parser.parse_attribute(Parser* self)
{
    Tok hash = self.advance();   // #
    Scratch s;
    s.reset();

    // Support #[name(args)] syntax as well as #name(args)
    bool bracket_form = false;
    if (self.check(Tt.TOKEN_LBRACK))
    {
        self.advance();  // consume [
        bracket_form = true;
    }

    Nk kind = Nk.NODE_ATTR_GENERIC;
    if (self.check(Tt.TOKEN_IDENT) || is_attr_keyword(self.cur.type))
    {
        Tok name = self.advance();
        kind = attr_kind_for(name);
        s.push(self.name_from(name, Nk.NODE_IDENT));
    }
    else
    {
        self.error("expected attribute name after '#'");
    }

    // Optional (args)
    if (self.accept(Tt.TOKEN_LPAREN))
    {
        if (!self.check(Tt.TOKEN_RPAREN))
        {
            s.push(self.parse_expr());
            while (self.accept(Tt.TOKEN_COMMA))
            {
                s.push(self.parse_expr());
            }
        }
        self.expect(Tt.TOKEN_RPAREN, "expected ')' to close attribute args");
    }

    if (bracket_form) self.accept(Tt.TOKEN_RBRACK);
    return self.finish(kind, &s, hash.line, hash.col);
}

fn bool is_attr_keyword(Tt t) @private
{
    switch (t)
    {
        case Tt.TOKEN_KW_EXTERN:
        case Tt.TOKEN_KW_EXPORT:
        case Tt.TOKEN_KW_INLINE:
        case Tt.TOKEN_KW_NOINLINE:
        case Tt.TOKEN_KW_PACKED:
        case Tt.TOKEN_KW_ALIGN:
        case Tt.TOKEN_KW_VOLATILE:
        case Tt.TOKEN_KW_ATOMIC:
        case Tt.TOKEN_KW_UNSAFE:
        case Tt.TOKEN_KW_PURE:
        case Tt.TOKEN_KW_NAKED:
        case Tt.TOKEN_KW_DEPRECATED:
        case Tt.TOKEN_KW_STATIC:
        case Tt.TOKEN_KW_CONST:
            return true;
        default:
            return false;
    }
}

fn Nk attr_kind_for(Tok name) @private
{
    if (tok_text_eq(name, "extern", 6))   return Nk.NODE_ATTR_EXTERN;
    if (tok_text_eq(name, "export", 6))   return Nk.NODE_ATTR_EXPORT;
    if (tok_text_eq(name, "inline", 6))   return Nk.NODE_ATTR_INLINE;
    if (tok_text_eq(name, "noinline", 8)) return Nk.NODE_ATTR_NOINLINE;
    if (tok_text_eq(name, "packed", 6))   return Nk.NODE_ATTR_PACKED;
    if (tok_text_eq(name, "align", 5))    return Nk.NODE_ATTR_ALIGN;
    if (tok_text_eq(name, "volatile", 8)) return Nk.NODE_ATTR_VOLATILE;
    if (tok_text_eq(name, "atomic", 6))   return Nk.NODE_ATTR_ATOMIC;
    if (tok_text_eq(name, "unsafe", 6))   return Nk.NODE_ATTR_UNSAFE;
    if (tok_text_eq(name, "pure", 4))          return Nk.NODE_ATTR_PURE;
    // C23 standard attributes — parsed as NODE_ATTR_GENERIC with their name preserved
    if (tok_text_eq(name, "nodiscard", 9))     return Nk.NODE_ATTR_GENERIC;  // [[nodiscard]]
    if (tok_text_eq(name, "deprecated", 10))   return Nk.NODE_ATTR_GENERIC;  // [[deprecated]]
    if (tok_text_eq(name, "maybe_unused", 12)) return Nk.NODE_ATTR_GENERIC;  // [[maybe_unused]]
    if (tok_text_eq(name, "noreturn", 8))      return Nk.NODE_ATTR_GENERIC;  // [[noreturn]]
    if (tok_text_eq(name, "fallthrough", 11))  return Nk.NODE_ATTR_GENERIC;  // [[fallthrough]]
    if (tok_text_eq(name, "reproducible", 12)) return Nk.NODE_ATTR_GENERIC;  // [[reproducible]] C23
    if (tok_text_eq(name, "unsequenced", 11))  return Nk.NODE_ATTR_GENERIC;  // [[unsequenced]] C23
    if (tok_text_eq(name, "noinit", 6))        return Nk.NODE_ATTR_GENERIC;  // [[noinit]]
    if (tok_text_eq(name, "clang_builtin_alias", 20)) return Nk.NODE_ATTR_GENERIC;
    return Nk.NODE_ATTR_GENERIC;
}

// clauses ::= ('|' pattern (',' guard)? '->' body)+   |   '->' body   |   block
fn Node* Parser.parse_clauses(Parser* self)
{
    Scratch s;
    s.reset();
    int line = self.cur.line;
    int col = self.cur.col;

    // Allow newline/indent before the clause list.
    self.skip_newlines();
    bool indented = self.accept(Tt.TOKEN_INDENT);
    self.skip_newlines();

    if (self.check(Tt.TOKEN_PIPE))
    {
        uint clause_idx = 0;
        while (self.check(Tt.TOKEN_PIPE))
        {
            Node* clause = self.parse_clause();
            if (clause != null)
            {
                // Tag clause with its index; total_clauses patched below.
                bool chas_guard = (clause.flags & ast::FLAG_REFUTABLE) != 0;
                ast::node_clause_set_meta(clause, clause_idx, 0, chas_guard);
                s.push(clause);
                clause_idx++;
            }
            self.skip_newlines();
        }
        // Back-patch total_clauses on every clause we just collected.
        for (usz ci = 0; ci < s.count; ci++)
        {
            if (s.items()[ci] != null && s.items()[ci].kind == Nk.NODE_CLAUSE)
            {
                s.items()[ci].p.clause_data.total_clauses = (uint)s.count;
                // Mark last clause so tail-call detection has a fast check.
                if (ci == s.count - 1) s.items()[ci].flags |= ast::FLAG_CLAUSE_LAST;
            }
        }
    }
    else if (self.check(Tt.TOKEN_ARROW) || self.check(Tt.TOKEN_ARROW_ASCII))
    {
        // Single anonymous clause: -> body
        self.advance();
        Node* body = self.parse_clause_body();
        Node* clause = ast::node1(self.arena, Nk.NODE_CLAUSE, body, line, col);
        ast::node_clause_set_meta(clause, 0, 1, false);
        clause.flags |= ast::FLAG_CLAUSE_LAST;
        s.push(clause);
    }
    else if (self.check(Tt.TOKEN_KW_ASM))
    {
        // fn f : ... | () -> asm  was the common case, but allow bare asm body
        Node* body = self.parse_asm();
        s.push(ast::node1(self.arena, Nk.NODE_CLAUSE, body, line, col));
    }

    if (indented) self.accept(Tt.TOKEN_DEDENT);

    if (s.count == 0) return null;
    return self.finish(Nk.NODE_EXPR_BLOCK, &s, line, col);
}

// clause ::= '|' pattern (',' guard_expr)? ('->' body)?
fn Node* Parser.parse_clause(Parser* self)
{
    Tok bar = self.advance();   // |
    Scratch s;
    s.reset();

    Node* pat = self.parse_pattern();
    s.push(pat);

    // Optional guard after a comma.
    if (self.accept(Tt.TOKEN_COMMA))
    {
        Node* guard = self.parse_expr();
        Node* gnode = ast::node1(self.arena, Nk.NODE_PATTERN_GUARD, guard, bar.line, bar.col);
        s.push(gnode);
    }

    if (self.accept(Tt.TOKEN_ARROW) || self.accept_ascii_arrow())
    {
        Node* body = self.parse_clause_body();
        s.push(body);
    }
    else
    {
        self.error("expected '->' in clause");
    }

    return self.finish(Nk.NODE_CLAUSE, &s, bar.line, bar.col);
}

fn bool Parser.accept_ascii_arrow(Parser* self)
{
    return self.accept(Tt.TOKEN_ARROW_ASCII);
}

// A clause body is either an inline expression or an indented block.
fn Node* Parser.parse_clause_body(Parser* self)
{
    self.skip_newlines();
    if (self.at_block_start())
    {
        return self.parse_block();
    }
    // Allow statement-like constructs as inline bodies after `then`:
    // break / continue / return / let / let mut
    // e.g. `if cond then break`, `if cond then let _ = expr`
    if (self.check(Tt.TOKEN_KW_BREAK) || self.check(Tt.TOKEN_KW_CONTINUE)
     || self.check(Tt.TOKEN_KW_RETURN) || self.check(Tt.TOKEN_KW_LET)
     || self.check(Tt.TOKEN_KW_CONST) || self.check(Tt.TOKEN_KW_STATIC))
    {
        return self.parse_stmt();
    }
    // A bare `|` as the first token of a clause body means an anonymous closure:
    //   fn f : i64 -> (i64 -> i64)  | n -> | x -> x + n
    // Parse the `| pat -> body` chain as a closure — WITHOUT consuming a leading `fn`.
    if (self.check(Tt.TOKEN_PIPE))
    {
        Tok t2 = self.cur;
        Scratch sc2;
        sc2.reset();
        while (self.check(Tt.TOKEN_PIPE))
        {
            Node* cl = self.parse_clause();
            if (cl != null) sc2.push(cl);
            self.skip_newlines();
        }
        return self.finish(Nk.NODE_EXPR_CLOSURE, &sc2, t2.line, t2.col);
    }
    return self.parse_expr();
}

// effect_row ::= '!' '[' (effect_ref (',' effect_ref)*)? (',' '..' ident)? ']'
fn Node* Parser.parse_effect_row(Parser* self)
{
    Tok bang = self.advance();   // !
    Scratch s;
    s.reset();

    self.expect(Tt.TOKEN_LBRACK, "expected '[' to open effect row");

    bool open = false;
    if (!self.check(Tt.TOKEN_RBRACK))
    {
        bool more = true;
        while (more)
        {
            if (self.check(Tt.TOKEN_DOTDOT))
            {
                // open tail ..r
                self.advance();
                Node* tail = null;
                if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
                {
                    Tok r = self.advance();
                    tail = self.name_from(r, Nk.NODE_IDENT);
                }
                Node* o = (tail != null)
                    ? ast::node1(self.arena, Nk.NODE_EFFECT_OPEN, tail, bang.line, bang.col)
                    : ast::node0(self.arena, Nk.NODE_EFFECT_OPEN, bang.line, bang.col);
                s.push(o);
                open = true;
            }
            else if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
            {
                Tok e = self.advance();
                Node* ref = self.name_from(e, Nk.NODE_IDENT);
                s.push(ast::node1(self.arena, Nk.NODE_EFFECT_REF, ref, e.line, e.col));
            }
            else if (self.check(Tt.TOKEN_EMPTYSET))
            {
                self.advance();   // ∅ empty row
            }
            else
            {
                self.error("expected effect name in effect row");
                break;
            }

            more = self.accept(Tt.TOKEN_COMMA);
        }
    }

    self.expect(Tt.TOKEN_RBRACK, "expected ']' to close effect row");

    Node* row = self.finish(Nk.NODE_EFFECT_ROW, &s, bang.line, bang.col);
    if (open && row != null) row.flags |= ast::FLAG_OPEN_ROW;
    return row;
}

// asm ( "line" )+  (: operand-spec)?      — lines may be indented.
fn Node* Parser.parse_asm(Parser* self)
{
    Tok kw = self.advance();   // asm
    Scratch s;
    s.reset();

    self.skip_newlines();
    bool indented = self.accept(Tt.TOKEN_INDENT);
    self.skip_newlines();

    while (self.check(Tt.TOKEN_LIT_STRING))
    {
        Tok line = self.advance();
        Node* str = ast::node_str(self.arena, Nk.NODE_LIT_STRING, line.start, line.len, line.line, line.col);
        s.push(ast::node1(self.arena, Nk.NODE_ASM_LINE, str, line.line, line.col));
        self.skip_newlines();
    }

    // Operand specifications:
    //   : out rax            : in (p)           : clobber "rax", "rdx"
    //   : out "=r" (result)  : in "r" (x), "r" (y)
    // Each ':' introduces one operand group: an optional direction keyword
    // (out/in/clobber as plain idents), then a comma-separated list of items,
    // where an item is a register/constraint name, a string constraint, or a
    // parenthesised binding expression.
    while (self.check(Tt.TOKEN_COLON))
    {
        Tok colon = self.advance();
        Scratch ops;
        ops.reset();

        // Optional direction keyword (out / in / clobber / =r etc.) as an ident.
        if (self.check(Tt.TOKEN_IDENT) && self.peek1().type != Tt.TOKEN_LPAREN)
        {
            // Only treat a leading ident as the direction if another operand
            // item plausibly follows (string, ident, or '(').
            Tt nxt = self.peek1().type;
            if (nxt == Tt.TOKEN_IDENT || nxt == Tt.TOKEN_LIT_STRING
                || nxt == Tt.TOKEN_LPAREN || nxt == Tt.TOKEN_COMMA)
            {
                Tok dir = self.advance();
                ops.push(self.name_from(dir, Nk.NODE_IDENT));
            }
        }

        // Operand item list.
        bool first = true;
        while (!self.check(Tt.TOKEN_COLON)
            && !self.check(Tt.TOKEN_DEDENT)
            && !self.check(Tt.TOKEN_NEWLINE)
            && !self.at_end())
        {
            if (!first)
            {
                if (!self.accept(Tt.TOKEN_COMMA)) break;
            }
            first = false;

            if (self.check(Tt.TOKEN_LIT_STRING))
            {
                Tok str = self.advance();
                ops.push(ast::node_str(self.arena, Nk.NODE_LIT_STRING, str.start, str.len, str.line, str.col));
            }
            if (self.check(Tt.TOKEN_LPAREN))
            {
                ops.push(self.parse_paren_expr());
            }
            else if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
            {
                Tok id = self.advance();
                ops.push(self.name_from(id, Nk.NODE_IDENT));
            }
        }

        Node* op = self.finish(Nk.NODE_ASM_OPERAND, &ops, colon.line, colon.col);
        s.push(op);
        self.skip_newlines();
    }

    if (indented) self.accept(Tt.TOKEN_DEDENT);

    Node* node = self.finish(Nk.NODE_STMT_ASM, &s, kw.line, kw.col);
    ast::node_add_effect(node, ast::EFFECT_UNSAFE);
    return node;
}

// Types (v.md §4, §20)
// type ::= fn_type
// The arrow is right-associative; effect rows bind to the function type.
fn Node* Parser.parse_type(Parser* self)
{
    if (!self.enter())
    {
        Tok t = self.cur;
        if (!self.at_end()) self.advance();
        self.leave();
        return ast::node0(self.arena, Nk.NODE_INVALID, t.line, t.col);
    }
    Node* r = self.parse_type_inner();
    self.leave();
    return r;
}

fn Node* Parser.parse_type_inner(Parser* self)
{
    Node* left = self.parse_type_ops();

    if (self.check(Tt.TOKEN_ARROW) || self.check(Tt.TOKEN_ARROW_ASCII))
    {
        Tok arr = self.advance();
        Node* ret = self.parse_type();   // right-assoc
        Node* fn_ty = ast::node2(self.arena, Nk.NODE_TYPE_FN, left, ret, arr.line, arr.col);

        // A function type may carry an effect row, even nested inside a tuple:
        //   (A -> B ! [..r])
        if (self.check(Tt.TOKEN_BANG))
        {
            Node* row = self.parse_effect_row();
            fn_ty = ast::node2(self.arena, Nk.NODE_TYPE_FN, fn_ty, row, arr.line, arr.col);
        }
        return fn_ty;
    }
    return left;
}

// fn-signature context disambiguation for ASCII `|` (used only when
// Parser.in_fn_sig is set): scans the token stream AFTER a `|` and answers
// "does this form a clause head `pattern ->` / `pattern , guard ->`?".
//
// The old two-token heuristic could only see `| ident ->` — a tuple clause
// head `| (a, b) -> body` or struct-variant head `| { some: x } -> body`
// slipped past it, the type parser ate `| (a, b) -> a` as a TYPE UNION
// (TyUnion with a TyTuple arm!), and the leftover `+ b` became a unary-plus
// statement — corrupting every declaration after a one-line fn.
//
// Method: snapshot the lexer (a flat value struct) and walk tokens with a
// paren/brace/bracket depth counter. A top-level ARROW or COMMA means
// clause; a NEWLINE, INDENT, second top-level `|`, EOF, or any
// non-pattern-continuing token at depth 0 means type union. Parser/lexer
// state (including the la1/la2 ring) is left untouched.
fn bool Parser.fn_sig_pipe_is_clause(Parser* self)
{
    self.peek1();
    self.peek2();
    lexer::Lexer probe = *self.lx;
    int depth = 0;
    int step = 0;
    for (int guard = 0; guard < 512; guard++)
    {
        Tok t;
        if (step == 0)       { t = self.has_la1 ? self.la1 : probe.next(); step = 1; }
        else if (step == 1)  { t = self.has_la2 ? self.la2 : probe.next(); step = 2; }
        else                 { t = probe.next(); }
        switch (t.type)
        {
            case Tt.TOKEN_NEWLINE:
            case Tt.TOKEN_INDENT:
            case Tt.TOKEN_DEDENT:
            case Tt.TOKEN_EOF:
            case Tt.TOKEN_PIPE:
                return false;
            case Tt.TOKEN_LPAREN:
            case Tt.TOKEN_LBRACE:
            case Tt.TOKEN_LBRACK:
                depth++;
            case Tt.TOKEN_RPAREN:
            case Tt.TOKEN_RBRACE:
            case Tt.TOKEN_RBRACK:
                if (depth == 0) { return false; }
                depth--;
            case Tt.TOKEN_ARROW:
            case Tt.TOKEN_ARROW_ASCII:
            case Tt.TOKEN_COMMA:
                if (depth == 0) { return true; }
            default:
            {
                if (depth == 0)
                {
                    // Only pattern-continuing tokens keep the clause reading alive.
                    bool cont = (t.type == Tt.TOKEN_IDENT
                        || t.type == Tt.TOKEN_TYPEVAR
                        || t.type == Tt.TOKEN_WILDCARD
                        || t.type == Tt.TOKEN_LIT_INT
                        || t.type == Tt.TOKEN_LIT_FLOAT
                        || t.type == Tt.TOKEN_LIT_BOOL
                        || t.type == Tt.TOKEN_LIT_CHAR
                        || t.type == Tt.TOKEN_LIT_STRING
                        || t.type == Tt.TOKEN_COLON
                        || t.type == Tt.TOKEN_MINUS
                        || t.type == Tt.TOKEN_DOT
                        || t.type == Tt.TOKEN_KW_IF);
                    if (!cont) { return false; }
                }
            }
        }
    }
    return false;
}

// type_ops ::= type_postfix ( (∩|∪) type_postfix )*    (and ¬ as prefix)
fn Node* Parser.parse_type_ops(Parser* self)
{
    Node* left = self.parse_type_prefix();

    while (self.check(Tt.TOKEN_INTERSECT) || self.check(Tt.TOKEN_UNION_SYM))
    {
        Tok op = self.advance();
        Node* right = self.parse_type_prefix();
        Nk k = (op.type == Tt.TOKEN_INTERSECT) ? Nk.NODE_TYPE_INTERSECT : Nk.NODE_TYPE_UNION;
        left = ast::node2(self.arena, k, left, right, op.line, op.col);
    }

    // ASCII `|` in type position is accepted as type union (same as ∪).
    // Disambiguation from clause-starting `|`:
    //   A clause pipe is always at the start of an indented line — the token
    //   after it is a pattern/ident, the token after THAT is `->` or `,`.
    //   A type union `|` is always followed by a type-starting token, and
    //   is never preceded by a NEWLINE/INDENT at column ≤ 3.
    //   Heuristic: if `|` is followed by IDENT then `->`, it's a clause — stop.
    //   Otherwise treat as type union and loop.
    // ASCII `|` in type position = type union (same as ∪).
    // Disambiguation from clause-starting `|`:
    //   Clause pipe: `| pat -> body`  or  `| pat, guard -> body`
    //   Type union:  `T1 | T2`  or  `type X = A | B`
    // Strategy: look ahead past the `|`.
    //   If peek1 is a type-starting token (primitive, typevar, *, (, !, etc.) → type union
    //   If peek1 is IDENT/WILDCARD followed by `->` or `,` or `if` → clause pipe (stop)
    //   Col ≤ 4 → always clause (freshly indented line)
    while (self.check(Tt.TOKEN_PIPE))
    {
        if (self.cur.col <= 4) { break; }   // indented clause pipe
        // Also stop if p1 is a NEWLINE (blank | line = clause)
        Tt p1 = self.peek1().type;
        if (p1 == Tt.TOKEN_NEWLINE || p1 == Tt.TOKEN_INDENT) { break; }
        if (self.in_fn_sig)
        {
            // fn-signature context: full balanced pattern scan (tuple and
            // struct clause heads included) — see fn_sig_pipe_is_clause.
            if (self.fn_sig_pipe_is_clause()) { break; }
        }
        else
        {
            // Lookahead: what follows the `|`?
            Tt p2 = self.peek2().type;
            // Pattern-like after |: ident/wildcard/tuple start followed by arrow, comma, or guard keyword
            bool after_is_clause_start =
                (p1 == Tt.TOKEN_IDENT || p1 == Tt.TOKEN_WILDCARD || p1 == Tt.TOKEN_LPAREN
                 || p1 == Tt.TOKEN_LIT_INT || p1 == Tt.TOKEN_LIT_BOOL || p1 == Tt.TOKEN_LIT_CHAR)
                && (p2 == Tt.TOKEN_ARROW || p2 == Tt.TOKEN_ARROW_ASCII
                    || p2 == Tt.TOKEN_COMMA || p2 == Tt.TOKEN_KW_IF);
            if (after_is_clause_start) { break; }
        }
        Tok op = self.advance();
        Node* right = self.parse_type_prefix();
        left = ast::node2(self.arena, Nk.NODE_TYPE_UNION, left, right, op.line, op.col);
    }
    return left;
}

fn Node* Parser.parse_type_prefix(Parser* self)
{
    // Depth-guard the prefix recursion (*T / &T / ¬T chains and, via postfix,
    // generic application) so pathological nesting is rejected, not crashed.
    if (!self.enter())
    {
        Tok t = self.cur;
        if (!self.at_end()) self.advance();
        self.leave();
        return ast::node0(self.arena, Nk.NODE_INVALID, t.line, t.col);
    }
    Node* r = self.parse_type_prefix_inner();
    self.leave();
    return r;
}

fn Node* Parser.parse_type_prefix_inner(Parser* self)
{
    // ¬T negation
    if (self.check(Tt.TOKEN_NEGATION))
    {
        Tok op = self.advance();
        Node* t = self.parse_type_prefix();
        return ast::node1(self.arena, Nk.NODE_TYPE_NEGATION, t, op.line, op.col);
    }

    // *T pointer
    if (self.check(Tt.TOKEN_STAR))
    {
        Tok op = self.advance();
        Node* t = self.parse_type_prefix();
        return ast::node1(self.arena, Nk.NODE_TYPE_PTR, t, op.line, op.col);
    }

    // &T reference / &mut T
    if (self.check(Tt.TOKEN_AMP))
    {
        Tok op = self.advance();
        if (self.accept(Tt.TOKEN_KW_MUT))
        {
            Node* t = self.parse_type_prefix();
            return ast::node1(self.arena, Nk.NODE_TYPE_MUT_REF, t, op.line, op.col);
        }
        Node* t = self.parse_type_prefix();
        return ast::node1(self.arena, Nk.NODE_TYPE_REF, t, op.line, op.col);
    }

    // ∀ A . T   /   ∃ T . body
    if (self.check(Tt.TOKEN_FORALL) || self.check(Tt.TOKEN_EXISTS))
    {
        Tok q = self.advance();
        Scratch s;
        s.reset();
        if (self.check(Tt.TOKEN_TYPEVAR) || self.check(Tt.TOKEN_IDENT))
        {
            Tok v = self.advance();
            s.push(self.name_from(v, Nk.NODE_TYPEVAR));
        }
        self.accept(Tt.TOKEN_DOT);
        s.push(self.parse_type());
        Nk k = (q.type == Tt.TOKEN_FORALL) ? Nk.NODE_TYPE_FORALL : Nk.NODE_TYPE_EXISTS;
        return self.finish(k, &s, q.line, q.col);
    }

    return self.parse_type_postfix();
}

// type_postfix ::= type_atom ( generic-app | nothing )
fn Node* Parser.parse_type_postfix(Parser* self)
{
    Node* base = self.parse_type_atom();

    // Generic application:  Name<T, U>
    if (self.check(Tt.TOKEN_LT) && base != null && is_typevarish(base))
    {
        Tok lt = self.advance();
        Scratch s;
        s.reset();
        s.push(base);
        if (!self.check(Tt.TOKEN_GT))
        {
            s.push(self.parse_type());
            while (self.accept(Tt.TOKEN_COMMA))
            {
                s.push(self.parse_type());
            }
        }
        self.expect(Tt.TOKEN_GT, "expected '>' to close generic application");
        return self.finish(Nk.NODE_TYPE_GENERIC_APP, &s, lt.line, lt.col);
    }

    return base;
}

fn bool is_typevarish(Node* n) @private
{
    return n != null && (n.kind == Nk.NODE_TYPEVAR
        || n.kind == Nk.NODE_TYPE_PATH
        || n.kind == Nk.NODE_TYPE_PRIMITIVE);
}

// type_atom ::= primitive | typevar | path | ⊥ | () | (T, ...) | [T; N] | refinement
fn Node* Parser.parse_type_atom(Parser* self)
{
    Tok t = self.cur;

    switch (t.type)
    {
        case Tt.TOKEN_BOTTOM:
            self.advance();
            return ast::node_bottom(self.arena, t.line, t.col);

        case Tt.TOKEN_TYPEVAR:
            // Tensor<T; D0, D1, ...> is a built-in shaped type.
            if (tok_text_eq(t, "Tensor", 6) && self.peek1().type == Tt.TOKEN_LT)
            {
                return self.parse_tensor_type();
            }
            // Capitalised primitive names (e.g. `Str`) lex as TYPEVARs but are
            // built-in primitive types, not type variables. Recognise them so
            // the resolver treats them as defined (a single `Str` with no `::`
            // following is the primitive; `Str::x` would be a module path).
            if (is_primitive_name(t) && self.peek1().type != Tt.TOKEN_COLONCOLON)
            {
                self.advance();
                return ast::node_name(self.arena, Nk.NODE_TYPE_PRIMITIVE, t.start, t.len, t.line, t.col);
            }
            self.advance();
            return self.name_from(t, Nk.NODE_TYPEVAR);

        case Tt.TOKEN_IDENT:
            return self.parse_type_path();

        case Tt.TOKEN_LPAREN:
            return self.parse_type_paren();

        case Tt.TOKEN_LBRACK:
            return self.parse_type_array();

        case Tt.TOKEN_KW_TYPEOF:
        case Tt.TOKEN_KW_TYPEOF_UNQUAL:
            // typeof(expr) and typeof_unqual(expr) — C23 type operators
            // Return a NODE_TYPEOF node wrapping the expression.
            {
                bool unqual = (t.type == Tt.TOKEN_KW_TYPEOF_UNQUAL);
                self.advance();  // consume typeof / typeof_unqual
                self.expect(Tt.TOKEN_LPAREN, "expected '(' after typeof");
                Node* inner = self.parse_expr();
                self.expect(Tt.TOKEN_RPAREN, "expected ')' after typeof(expr)");
                Scratch ts; ts.reset(); ts.push(inner);
                Nk tok = unqual ? Nk.NODE_TYPEOF_UNQUAL : Nk.NODE_TYPEOF;
                return self.finish(tok, &ts, t.line, t.col);
            }

        default:
            self.error("expected a type");
            self.advance();
            return ast::node0(self.arena, Nk.NODE_INVALID, t.line, t.col);
    }
}

// Tensor<ElemType; Dim0, Dim1, ...> — a shaped numeric tensor type.
// Children: [elem-type, dim-expr*]. Dimensions are expressions (usually int
// literals or generic size params).
fn Node* Parser.parse_tensor_type(Parser* self)
{
    Tok kw = self.advance();   // Tensor
    self.expect(Tt.TOKEN_LT, "expected '<' after Tensor");

    Scratch s;
    s.reset();

    // Element type.
    s.push(self.parse_type());

    // Shape dimensions after ';'. Dimensions are additive expressions (no
    // comparison/shift), so the closing '>' is never mistaken for `greater-than`.
    if (self.accept(Tt.TOKEN_SEMI))
    {
        if (!self.check(Tt.TOKEN_GT))
        {
            s.push(self.parse_add());
            while (self.accept(Tt.TOKEN_COMMA))
            {
                if (self.check(Tt.TOKEN_GT)) break;
                s.push(self.parse_add());
            }
        }
    }

    self.expect(Tt.TOKEN_GT, "expected '>' to close Tensor type");
    return self.finish(Nk.NODE_TYPE_TENSOR, &s, kw.line, kw.col);
}

// path type: lowercase primitive (i32, ...) OR a module path a::B::C
fn Node* Parser.parse_type_path(Parser* self)
{
    Tok first = self.advance();

    // Primitive names are lowercase idents from a fixed set.
    if (is_primitive_name(first) && !self.check(Tt.TOKEN_COLONCOLON))
    {
        return ast::node_name(self.arena, Nk.NODE_TYPE_PRIMITIVE, first.start, first.len, first.line, first.col);
    }

    Scratch s;
    s.reset();
    s.push(self.name_from(first, Nk.NODE_IDENT));
    while (self.accept(Tt.TOKEN_COLONCOLON))
    {
        if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
        {
            Tok seg = self.advance();
            s.push(self.name_from(seg, Nk.NODE_IDENT));
        }
        else
        {
            self.error("expected path segment after '::'");
            break;
        }
    }

    if (s.count == 1)
    {
        // Single ident type — keep as a primitive-ish path leaf.
        return ast::node_name(self.arena, Nk.NODE_TYPE_PRIMITIVE, first.start, first.len, first.line, first.col);
    }
    return self.finish(Nk.NODE_TYPE_PATH, &s, first.line, first.col);
}

fn bool is_primitive_name(Tok t) @private
{
    if (tok_text_eq(t, "i8", 2))   return true;
    if (tok_text_eq(t, "i16", 3))  return true;
    if (tok_text_eq(t, "i32", 3))  return true;
    if (tok_text_eq(t, "i64", 3))  return true;
    if (tok_text_eq(t, "u8", 2))   return true;
    if (tok_text_eq(t, "u16", 3))  return true;
    if (tok_text_eq(t, "u32", 3))  return true;
    if (tok_text_eq(t, "u64", 3))  return true;
    if (tok_text_eq(t, "f32", 3))  return true;
    if (tok_text_eq(t, "f64", 3))  return true;
    if (tok_text_eq(t, "bool", 4)) return true;
    if (tok_text_eq(t, "ptr", 3))  return true;
    if (tok_text_eq(t, "Str", 3))  return true;
    return false;
}

// ( ) unit | ( T ) group | ( T , ... ) tuple   — also handles refinements (> 0)
fn Node* Parser.parse_type_paren(Parser* self)
{
    Tok lp = self.advance();   // (

    if (self.accept(Tt.TOKEN_RPAREN))
    {
        // unit type ()
        return ast::node0(self.arena, Nk.NODE_EXPR_UNIT, lp.line, lp.col);
    }

    // Refinement predicate, e.g. (> 0), (<= 1.0), (>= 0.0)
    if (is_compare_op(self.cur.type))
    {
        Tok op = self.advance();
        Node* bound = self.parse_expr();
        self.expect(Tt.TOKEN_RPAREN, "expected ')' to close refinement");
        return ast::node_op(self.arena, Nk.NODE_TYPE_REFINEMENT, op.type, &bound, 1, op.line, op.col);
    }

    Scratch s;
    s.reset();
    s.push(self.parse_type());
    bool is_tuple = false;
    while (self.accept(Tt.TOKEN_COMMA))
    {
        is_tuple = true;
        if (self.check(Tt.TOKEN_RPAREN)) break;
        s.push(self.parse_type());
    }
    self.expect(Tt.TOKEN_RPAREN, "expected ')' to close type");

    if (is_tuple)
    {
        return self.finish(Nk.NODE_TYPE_TUPLE, &s, lp.line, lp.col);
    }
    Node* only = s.items()[0]; s.reset(); return only;
}

// [T; N] fixed array  |  [T] slice
fn Node* Parser.parse_type_array(Parser* self)
{
    Tok lb = self.advance();   // [
    Node* elem = self.parse_type();

    if (self.accept(Tt.TOKEN_SEMI))
    {
        Node* len = self.parse_expr();
        self.expect(Tt.TOKEN_RBRACK, "expected ']' to close array type");
        return ast::node2(self.arena, Nk.NODE_TYPE_ARRAY, elem, len, lb.line, lb.col);
    }

    self.expect(Tt.TOKEN_RBRACK, "expected ']' to close slice type");
    return ast::node1(self.arena, Nk.NODE_TYPE_SLICE, elem, lb.line, lb.col);
}

fn bool is_compare_op(Tt t) @private
{
    switch (t)
    {
        case Tt.TOKEN_LT:
        case Tt.TOKEN_GT:
        case Tt.TOKEN_LTEQ:
        case Tt.TOKEN_GTEQ:
        case Tt.TOKEN_EQEQ:
        case Tt.TOKEN_NEQ:
        case Tt.TOKEN_LEQ_UNI:
        case Tt.TOKEN_GEQ_UNI:
        case Tt.TOKEN_NEQ_UNI:
        case Tt.TOKEN_ELEMENT:    // ∈  set membership
            return true;
        default:
            return false;
    }
}

// Type / struct / union / effect declarations (v.md §9, §10)
// type NAME <Generics>? = ( struct | union | type-expr )
fn Node* Parser.parse_type_decl(Parser* self)
{
    Tok kw = self.advance();   // type
    Scratch s;
    s.reset();

    if (self.check(Tt.TOKEN_TYPEVAR) || self.check(Tt.TOKEN_IDENT))
    {
        Tok name = self.advance();
        s.push(self.name_from(name, Nk.NODE_TYPEVAR));
    }
    else
    {
        self.error("expected type name after 'type'");
    }

    if (self.check(Tt.TOKEN_LT))
    {
        s.push(self.parse_generics());
    }

    self.expect(Tt.TOKEN_EQ, "expected '=' in type declaration");

    if (self.check(Tt.TOKEN_KW_STRUCT))
    {
        s.push(self.parse_struct(true));
    }
    else if (self.check(Tt.TOKEN_KW_UNION))
    {
        s.push(self.parse_union(true));
    }
    else
    {
        s.push(self.parse_type());
    }

    return self.finish(Nk.NODE_DECL_TYPE, &s, kw.line, kw.col);
}

// struct (#attrs)? <indented fields>
fn Node* Parser.parse_struct(Parser* self, bool anonymous)
{
    Tok kw = self.advance();   // struct
    Scratch s;
    s.reset();

    // Optional NAME (named form `struct Point`); absent in the anonymous form
    // used as a type-alias body (`type Vec3 = struct`). When a name is present
    // it is child 0 so the resolver hoists it like any other type declaration.
    if (!anonymous && (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR)))
    {
        Tok name = self.advance();
        s.push(self.name_from(name, Nk.NODE_TYPEVAR));
    }

    // Optional generic parameter list:  struct Stack<T>  /  struct Map<K, V>
    if (!anonymous && self.check(Tt.TOKEN_LT))
    {
        s.push(self.parse_generics());
    }

    if (self.check(Tt.TOKEN_HASH))
    {
        Node* attrs = self.parse_attr_block();
        if (attrs != null) s.push(attrs);
    }

    self.skip_newlines();
    if (self.at_block_start())
    {
        Node* fields = self.parse_field_block();
        s.push(fields);
    }

    return self.finish(Nk.NODE_DECL_STRUCT, &s, kw.line, kw.col);
}

fn Node* Parser.parse_union(Parser* self, bool anonymous)
{
    Tok kw = self.advance();   // union
    Scratch s;
    s.reset();

    if (!anonymous && (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR)))
    {
        Tok name = self.advance();
        s.push(self.name_from(name, Nk.NODE_TYPEVAR));
    }

    // Optional generic parameter list:  union Either<L, R>
    if (!anonymous && self.check(Tt.TOKEN_LT))
    {
        s.push(self.parse_generics());
    }

    if (self.check(Tt.TOKEN_HASH))
    {
        Node* attrs = self.parse_attr_block();
        if (attrs != null) s.push(attrs);
    }

    self.skip_newlines();
    if (self.at_block_start())
    {
        Node* fields = self.parse_field_block();
        s.push(fields);
    }

    return self.finish(Nk.NODE_DECL_UNION, &s, kw.line, kw.col);
}


fn Node* Parser.parse_enum(Parser* self)
{
    Tok kw = self.advance();   // enum
    Scratch s;
    s.reset();

    // Optional name:  enum Foo  or  enum Foo<T, E>
    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
    {
        Tok name = self.advance();
        s.push(self.name_from(name, Nk.NODE_TYPEVAR));
    }

    // Optional generic parameter list
    if (self.check(Tt.TOKEN_LT))
    {
        s.push(self.parse_generics());
    }

    // Body: indented block of comma/newline separated variants
    self.skip_newlines();
    if (self.at_block_start())
    {
        self.advance();   // consume INDENT or {
        self.skip_newlines();
        while (!self.check(Tt.TOKEN_DEDENT) && !self.check(Tt.TOKEN_RBRACE)
               && !self.check(Tt.TOKEN_EOF))
        {
            Node* variant = self.parse_enum_variant();
            if (variant != null) s.push(variant);
            // Allow trailing comma or newline between variants
            if (self.check(Tt.TOKEN_COMMA)) self.advance();
            self.skip_newlines();
        }
        if (!self.check(Tt.TOKEN_EOF)) self.advance(); // consume DEDENT / }
    }

    return self.finish(Nk.NODE_DECL_ENUM, &s, kw.line, kw.col);
}

// Parse one enum variant:  Name  or  Name(T)  or  Name(A, B)
fn Node* Parser.parse_enum_variant(Parser* self)
{
    if (!self.check(Tt.TOKEN_IDENT) && !self.check(Tt.TOKEN_TYPEVAR)) return null;
    Tok name = self.advance();
    Scratch s;
    s.reset();
    s.push(self.name_from(name, Nk.NODE_IDENT));

    // Payload: (T)  or  (A, B)  or  { field: T, ... }
    if (self.check(Tt.TOKEN_LPAREN))
    {
        self.advance();  // (
        int idx = 0;
        while (!self.check(Tt.TOKEN_RPAREN) && !self.check(Tt.TOKEN_EOF))
        {
            Node* ty = self.parse_type();
            if (ty != null)
            {
                // Create an anonymous field: _0, _1, ...
                char[8] fname;
                fname[0] = '_';
                int n2 = idx; int di = 1;
                if (n2 == 0) { fname[di++] = '0'; }
                else { char[4] tmp; int ti = 0; while(n2>0){tmp[ti++]=(char)('0'+(n2%10));n2/=10;} while(ti>0){fname[di++]=tmp[--ti];} }
                fname[di] = 0;
                // Build a FIELD_DECL node for this positional payload field
                // Name: use node_str which handles arena allocation
                Node* fname_node = ast::node_str(self.arena, Nk.NODE_IDENT, &fname[0], (usz)di, name.line, name.col);
                Node* field = ast::node2(self.arena, Nk.NODE_FIELD_DECL, fname_node, ty, name.line, name.col);
                if (field != null)
                {
                    // Copy name into field.p.ident for resolver
                    if (fname_node != null)
                    {
                        field.p.ident.name_ptr = fname_node.p.ident.name_ptr;
                        field.p.ident.name_len = fname_node.p.ident.name_len;
                    }
                    s.push(field);
                }
                idx++;
            }
            if (self.check(Tt.TOKEN_COMMA)) self.advance();
        }
        if (self.check(Tt.TOKEN_RPAREN)) self.advance();
    }

    return self.finish(Nk.NODE_ENUM_VARIANT, &s, name.line, name.col);
}

// interface Foo<T> {
//   fn method : Self -> T
//   fn other  : (Self, i64) -> bool
// }
// newtype Foo = UnderlyingType
// macro Name { | pattern => expansion, ... }
fn Node* Parser.parse_macro_decl(Parser* self)
{
    Tok kw = self.advance();  // macro
    Scratch s;
    s.reset();
    // Name
    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
    { s.push(self.name_from(self.advance(), Nk.NODE_TYPEVAR)); }
    // Body: indented block of | pat => expr rules
    self.skip_newlines();
    if (self.at_block_start())
    {
        self.advance();  // INDENT
        self.skip_newlines();
        while (!self.check(Tt.TOKEN_DEDENT) && !self.check(Tt.TOKEN_EOF))
        {
            if (self.accept(Tt.TOKEN_PIPE))
            {
                Scratch rs;
                rs.reset();
                Node* pat = self.parse_pattern();
                rs.push(pat);
                if (self.accept(Tt.TOKEN_FATARROW))
                { rs.push(self.parse_expr()); }
                s.push(self.finish(Nk.NODE_MACRO_RULE, &rs, kw.line, kw.col));
            }
            if (self.check(Tt.TOKEN_COMMA)) self.advance();
            self.skip_newlines();
        }
        if (!self.check(Tt.TOKEN_EOF)) self.advance();  // DEDENT
    }
    return self.finish(Nk.NODE_DECL_MACRO, &s, kw.line, kw.col);
}


fn Node* Parser.parse_newtype(Parser* self)
{
    Tok kw = self.advance();  // newtype
    Scratch s;
    s.reset();
    // Name
    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
    { s.push(self.name_from(self.advance(), Nk.NODE_TYPEVAR)); }
    // Optional generics
    if (self.check(Tt.TOKEN_LT)) { s.push(self.parse_generics()); }
    // : UnderlyingType  OR  = UnderlyingType
    if (self.accept(Tt.TOKEN_COLON) || self.accept(Tt.TOKEN_EQ)) { s.push(self.parse_type()); }
    return self.finish(Nk.NODE_DECL_NEWTYPE, &s, kw.line, kw.col);
}


fn Node* Parser.parse_interface(Parser* self)
{
    Tok kw = self.cur.type == Tt.TOKEN_KW_INTERFACE ? self.advance()
           : self.advance();  // also accept 'trait' forwarded here
    Scratch s;
    s.reset();

    // Name
    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
    {
        s.push(self.name_from(self.advance(), Nk.NODE_TYPEVAR));
    }

    // Optional generics
    if (self.check(Tt.TOKEN_LT)) { s.push(self.parse_generics()); }

    // Optional where clause
    if (self.check(Tt.TOKEN_KW_WHERE)) { s.push(self.parse_where()); }

    // Body: indented block of fn signatures
    self.skip_newlines();
    if (self.at_block_start())
    {
        self.advance();  // INDENT
        self.skip_newlines();
        while (!self.check(Tt.TOKEN_DEDENT) && !self.check(Tt.TOKEN_EOF))
        {
            Node* method = self.parse_fn();
            if (method != null) s.push(method);
            self.skip_newlines();
        }
        if (!self.check(Tt.TOKEN_EOF)) self.advance();  // DEDENT
    }

    return self.finish(Nk.NODE_DECL_INTERFACE, &s, kw.line, kw.col);
}

// impl Foo for Bar { ... }  or  impl Foo<T> for Bar<T> where T : Baz { ... }
fn Node* Parser.parse_impl(Parser* self)
{
    Tok kw = self.advance();  // impl
    Scratch s;
    s.reset();

    // Interface name
    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
    {
        s.push(self.name_from(self.advance(), Nk.NODE_TYPEVAR));
    }

    // Optional generics on interface
    if (self.check(Tt.TOKEN_LT)) { s.push(self.parse_generics()); }

    // "for" keyword
    if (self.check(Tt.TOKEN_KW_FOR)) { self.advance(); }

    // Implementing type
    Node* for_ty = self.parse_type();
    if (for_ty != null) s.push(for_ty);

    // Optional where clause
    if (self.check(Tt.TOKEN_KW_WHERE)) { s.push(self.parse_where()); }

    // Body: indented block of fn definitions
    self.skip_newlines();
    if (self.at_block_start())
    {
        self.advance();  // INDENT
        self.skip_newlines();
        while (!self.check(Tt.TOKEN_DEDENT) && !self.check(Tt.TOKEN_EOF))
        {
            Node* method = self.parse_fn();
            if (method != null) s.push(method);
            self.skip_newlines();
        }
        if (!self.check(Tt.TOKEN_EOF)) self.advance();  // DEDENT
    }

    return self.finish(Nk.NODE_DECL_IMPL, &s, kw.line, kw.col);
}


// indented list of `name : Type` field declarations
fn Node* Parser.parse_field_block(Parser* self)
{
    Scratch s;
    s.reset();
    int line = self.cur.line;
    int col = self.cur.col;

    self.expect(Tt.TOKEN_INDENT, "expected indented field list");
    self.skip_newlines();

    while (!self.check(Tt.TOKEN_DEDENT) && !self.at_end())
    {
        // A top-level keyword at column 1 means the struct body is over
        // (lexer should emit DEDENT but be defensive here)
        if (self.cur.col <= 1 &&
            (self.check(Tt.TOKEN_KW_FN)     || self.check(Tt.TOKEN_KW_STRUCT)  ||
             self.check(Tt.TOKEN_KW_UNION)  || self.check(Tt.TOKEN_KW_ENUM)    ||
             self.check(Tt.TOKEN_KW_EFFECT) || self.check(Tt.TOKEN_KW_TYPE)    ||
             self.check(Tt.TOKEN_KW_LET)    || self.check(Tt.TOKEN_KW_CONST)   ||
             self.check(Tt.TOKEN_KW_STATIC) || self.check(Tt.TOKEN_KW_INTERFACE)||
             self.check(Tt.TOKEN_KW_IMPL)   || self.check(Tt.TOKEN_KW_MOD)))
        { break; }
        if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR)
            || self.at_member_name())  // keywords are valid field names
        {
            Tok name = self.advance();
            self.expect(Tt.TOKEN_COLON, "expected ':' after field name");
            Node* ty = self.parse_type();
            Node* nm = self.name_from(name, Nk.NODE_IDENT);
            Node* field = ast::node2(self.arena, Nk.NODE_FIELD_DECL, nm, ty, name.line, name.col);
            s.push(field);
        }
        else
        {
            self.error("expected field name");
            self.advance();
        }
        self.panicking = false;
        self.skip_newlines();
    }

    self.accept(Tt.TOKEN_DEDENT);
    return self.finish(Nk.NODE_EXPR_BLOCK, &s, line, col);
}

// effect NAME <Generics>? <indented op decls>
fn Node* Parser.parse_effect_decl(Parser* self)
{
    Tok kw = self.advance();   // effect
    Scratch s;
    s.reset();

    if (self.check(Tt.TOKEN_TYPEVAR) || self.check(Tt.TOKEN_IDENT))
    {
        Tok name = self.advance();
        s.push(self.name_from(name, Nk.NODE_TYPEVAR));
    }
    else
    {
        self.error("expected effect name after 'effect'");
    }

    if (self.check(Tt.TOKEN_LT))
    {
        s.push(self.parse_generics());
    }

    self.skip_newlines();
    if (self.at_block_start())
    {
        Scratch ops;
        ops.reset();
        int line = self.cur.line;
        int col = self.cur.col;

        self.advance();   // INDENT
        self.skip_newlines();
        while (!self.check(Tt.TOKEN_DEDENT) && !self.at_end())
        {
            if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
            {
                Tok opname = self.advance();
                self.expect(Tt.TOKEN_COLON, "expected ':' after effect operation name");
                Node* ty = self.parse_type();
                Node* nm = self.name_from(opname, Nk.NODE_IDENT);
                Node* op = ast::node2(self.arena, Nk.NODE_EFFECT_OP_DECL, nm, ty, opname.line, opname.col);
                ops.push(op);
            }
            else
            {
                self.error("expected effect operation name");
                self.advance();
            }
            self.panicking = false;
            self.skip_newlines();
        }
        self.accept(Tt.TOKEN_DEDENT);
        s.push(self.finish(Nk.NODE_EXPR_BLOCK, &ops, line, col));
    }

    return self.finish(Nk.NODE_DECL_EFFECT, &s, kw.line, kw.col);
}

// Bindings (v.md §5)
// let (mut)? pattern (: Type)? (! [Effects])? (= expr)?
// Recursively flag every binder in a pattern as mutable (for `let mut`).
fn void mark_pattern_mut(Node* pat) @private
{
    if (pat == null) return;
    pat.flags |= ast::FLAG_MUT;
    for (usz i = 0; i < pat.child_count; i++)
    {
        mark_pattern_mut(pat.children[i]);
    }
}

// C23 constexpr: `constexpr name : T = expr`
// Treated as a compile-time-evaluated constant (equivalent to stage { expr }).
fn Node* Parser.parse_constexpr_decl(Parser* self)
{
    Tok kw = self.advance();  // consume 'constexpr'
    Scratch s; s.reset();

    // Require an ident name
    if (!self.check(Tt.TOKEN_IDENT))
    {
        self.error("expected identifier after 'constexpr'");
        return ast::node0(self.arena, Nk.NODE_INVALID, kw.line, kw.col);
    }
    Tok nm = self.advance();
    Node* pat = ast::node_name(self.arena, Nk.NODE_IDENT, nm.start, nm.len, nm.line, nm.col);
    s.push(pat);

    // Optional type annotation
    if (self.accept(Tt.TOKEN_COLON))
    {
        s.push(self.parse_type());
    }

    // Initialiser
    if (self.accept(Tt.TOKEN_EQ))
    {
        // Wrap the expr in a stage{} node for compile-time evaluation
        Node* init = self.parse_expr();
        Scratch stg; stg.reset(); stg.push(init);
        Node* staged = self.finish(Nk.NODE_STAGE, &stg, kw.line, kw.col);
        s.push(staged);
    }
    return self.finish(Nk.NODE_DECL_LET, &s, kw.line, kw.col);
}

fn Node* Parser.parse_let(Parser* self)
{
    Tok kw = self.advance();   // let
    Scratch s;
    s.reset();

    bool is_mut = self.accept(Tt.TOKEN_KW_MUT);

    Node* pat = self.parse_pattern();
    // Mark the binder(s) mutable so assignment checking can permit writes.
    if (is_mut) mark_pattern_mut(pat);
    s.push(pat);

    if (self.accept(Tt.TOKEN_COLON))
    {
        Node* ty = self.parse_type();
        s.push(ty);
        if (self.check(Tt.TOKEN_BANG))
        {
            s.push(self.parse_effect_row());
        }
    }

    if (self.accept(Tt.TOKEN_EQ))
    {
        Node* init = self.parse_clause_body();
        s.push(init);
    }

    Nk kind = is_mut ? Nk.NODE_DECL_MUT : Nk.NODE_DECL_LET;
    Node* node = self.finish(kind, &s, kw.line, kw.col);
    if (is_mut && node != null) node.flags |= ast::FLAG_MUT;
    return node;
}

fn Node* Parser.parse_const_static(Parser* self, Nk kind)
{
    Tok kw = self.advance();   // const / static
    Scratch s;
    s.reset();

    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
    {
        Tok name = self.advance();
        s.push(self.name_from(name, Nk.NODE_IDENT));
    }
    else
    {
        self.error("expected name in const/static declaration");
    }

    if (self.accept(Tt.TOKEN_COLON))
    {
        s.push(self.parse_type());
    }
    if (self.accept(Tt.TOKEN_EQ))
    {
        s.push(self.parse_clause_body());
    }

    return self.finish(kind, &s, kw.line, kw.col);
}

// Statements & blocks (v.md §7)
// block ::= INDENT (stmt NEWLINE?)* DEDENT
fn Node* Parser.parse_block(Parser* self)
{
    if (!self.enter())
    {
        Tok t = self.cur;
        if (!self.at_end()) self.advance();
        self.leave();
        return ast::node0(self.arena, Nk.NODE_INVALID, t.line, t.col);
    }
    Node* r = self.parse_block_inner();
    self.leave();
    return r;
}

fn Node* Parser.parse_block_inner(Parser* self)
{
    Scratch s;
    s.reset();
    int line = self.cur.line;
    int col = self.cur.col;

    self.expect(Tt.TOKEN_INDENT, "expected indented block");
    self.skip_newlines();

    while (!self.check(Tt.TOKEN_DEDENT) && !self.at_end())
    {
        Node* st = self.parse_stmt();
        if (st != null) s.push(st);
        self.panicking = false;
        self.skip_newlines();
        if (st == null && !self.check(Tt.TOKEN_DEDENT) && !self.at_end())
        {
            self.advance();
        }
    }

    self.accept(Tt.TOKEN_DEDENT);
    return self.finish(Nk.NODE_EXPR_BLOCK, &s, line, col);
}

fn Node* Parser.parse_stmt(Parser* self)
{
    Tok t = self.cur;

    switch (t.type)
    {
        case Tt.TOKEN_KW_CONSTEXPR: return self.parse_constexpr_decl();
        case Tt.TOKEN_KW_LET:     return self.parse_let();
        case Tt.TOKEN_KW_CONST:   return self.parse_const_static(Nk.NODE_DECL_CONST);
        case Tt.TOKEN_KW_STATIC:  return self.parse_const_static(Nk.NODE_DECL_STATIC);
        case Tt.TOKEN_KW_RETURN:  return self.parse_return();
        case Tt.TOKEN_KW_BREAK:
            {
                self.advance();
                // A label may sit on the next line (break\n  'label), but a
                // break VALUE must be on the SAME line as `break` — otherwise
                // the following statement is silently swallowed as break's
                // result expression (that was the root of the 'unreachable
                // code after break' lint gap: the dead statement became a
                // child of the Break node, so it never appeared as a block
                // statement and no warning could fire).
                bool at_line_end = self.check(Tt.TOKEN_NEWLINE) || self.check(Tt.TOKEN_DEDENT)
                                || self.check(Tt.TOKEN_EOF) || self.at_end();
                if (!at_line_end)
                {
                    // Same line: label reference, or break-with-value.
                    bool is_label_tok = self.check(Tt.TOKEN_LABEL_REF) || self.check(Tt.TOKEN_LIT_CHAR);
                    if (!is_label_tok && self.cur.start != null && self.cur.len >= 2)
                    {
                        char c0 = self.cur.start[0];
                        char c1 = self.cur.start[1];
                        if (c0 == '\'' && ((c1 >= 'a' && c1 <= 'z') || (c1 >= 'A' && c1 <= 'Z') || c1 == '_')) { is_label_tok = true; }
                    }
                    if (is_label_tok)
                    {
                        Tok lbl = self.advance();
                        Node* lbl_node = self.name_from(lbl, Nk.NODE_IDENT);
                        return ast::node1(self.arena, Nk.NODE_STMT_BREAK_LABEL, lbl_node, t.line, t.col);
                    }
                    Node* bval = self.parse_expr();
                    if (bval != null)
                    { return ast::node1(self.arena, Nk.NODE_STMT_BREAK, bval, t.line, t.col); }
                    return ast::node0(self.arena, Nk.NODE_STMT_BREAK, t.line, t.col);
                }
                // End of line: only a label may still follow (next line).
                self.skip_newlines();
                bool is_label_nl = self.check(Tt.TOKEN_LABEL_REF) || self.check(Tt.TOKEN_LIT_CHAR);
                if (!is_label_nl && self.cur.start != null && self.cur.len >= 2)
                {
                    char c0 = self.cur.start[0];
                    char c1 = self.cur.start[1];
                    if (c0 == '\'' && ((c1 >= 'a' && c1 <= 'z') || (c1 >= 'A' && c1 <= 'Z') || c1 == '_')) { is_label_nl = true; }
                }
                if (is_label_nl)
                {
                    Tok lbl = self.advance();
                    Node* lbl_node = self.name_from(lbl, Nk.NODE_IDENT);
                    return ast::node1(self.arena, Nk.NODE_STMT_BREAK_LABEL, lbl_node, t.line, t.col);
                }
                return ast::node0(self.arena, Nk.NODE_STMT_BREAK, t.line, t.col);
            }
        case Tt.TOKEN_KW_CONTINUE:
            {
                self.advance();
                self.skip_newlines();
                bool is_lbl3 = self.check(Tt.TOKEN_LABEL_REF) || self.check(Tt.TOKEN_LIT_CHAR);
                if (!is_lbl3 && self.cur.start != null && self.cur.len >= 2)
                {
                    char c0b = self.cur.start[0];
                    char c1b = self.cur.start[1];
                    if (c0b == '\'' && ((c1b >= 'a' && c1b <= 'z') || (c1b >= 'A' && c1b <= 'Z') || c1b == '_')) { is_lbl3 = true; }
                }
                if (is_lbl3)
                {
                    Tok lbl3 = self.advance();
                    Node* lbl_node3 = self.name_from(lbl3, Nk.NODE_IDENT);
                    return ast::node1(self.arena, Nk.NODE_STMT_CONTINUE_LABEL, lbl_node3, t.line, t.col);
                }
                return ast::node0(self.arena, Nk.NODE_STMT_CONTINUE, t.line, t.col);
            }
        case Tt.TOKEN_KW_DEFER:   return self.parse_defer();
        case Tt.TOKEN_KW_ASM:     return self.parse_asm();
        case Tt.TOKEN_KW_ASSUME:  return self.parse_unary_stmt(Nk.NODE_STMT_ASSUME);
        case Tt.TOKEN_KW_ASSERT:  return self.parse_unary_stmt(Nk.NODE_STMT_ASSERT);
        case Tt.TOKEN_KW_INVARIANT: return self.parse_unary_stmt(Nk.NODE_STMT_INVARIANT);
        case Tt.TOKEN_KW_UNREACHABLE: self.advance(); return ast::node0(self.arena, Nk.NODE_STMT_UNREACHABLE, t.line, t.col);
        case Tt.TOKEN_KW_TRAP:    self.advance(); return ast::node0(self.arena, Nk.NODE_STMT_TRAP, t.line, t.col);
        case Tt.TOKEN_KW_UNSAFE:  return self.parse_safety_block(Nk.NODE_EXPR_UNSAFE);
        case Tt.TOKEN_KW_UNCHECKED: return self.parse_safety_block(Nk.NODE_EXPR_UNCHECKED);
        case Tt.TOKEN_KW_FN:      return self.parse_fn();
        case Tt.TOKEN_KW_TYPE:    return self.parse_type_decl();
        case Tt.TOKEN_KW_USE:     return self.parse_use();
        default:
            return self.parse_expr_stmt();
    }
}

fn Node* Parser.parse_return(Parser* self)
{
    Tok kw = self.advance();   // return
    // `return` with no value is allowed (next is a layout/EOF token).
    if (self.check(Tt.TOKEN_NEWLINE) || self.check(Tt.TOKEN_DEDENT) || self.at_end())
    {
        return ast::node0(self.arena, Nk.NODE_STMT_RETURN, kw.line, kw.col);
    }
    Node* val = self.parse_expr();
    return ast::node1(self.arena, Nk.NODE_STMT_RETURN, val, kw.line, kw.col);
}

fn Node* Parser.parse_defer(Parser* self)
{
    Tok kw = self.advance();   // defer
    Node* body = self.parse_clause_body();
    return ast::node1(self.arena, Nk.NODE_STMT_DEFER, body, kw.line, kw.col);
}

fn Node* Parser.parse_unary_stmt(Parser* self, Nk kind)
{
    Tok kw = self.advance();
    Node* e = self.parse_expr();
    return ast::node1(self.arena, kind, e, kw.line, kw.col);
}

fn Node* Parser.parse_expr_stmt(Parser* self)
{
    int line = self.cur.line;
    int col = self.cur.col;
    Node* e = self.parse_expr();
    return ast::node1(self.arena, Nk.NODE_STMT_EXPR, e, line, col);
}

// Expressions — precedence climbing (v.md §23)
// Entry point. Assignment is the lowest precedence we treat as an expression.
fn Node* Parser.parse_expr(Parser* self)
{
    if (!self.enter())
    {
        Tok t = self.cur;
        if (!self.at_end()) self.advance();   // ensure progress
        self.leave();
        return ast::node0(self.arena, Nk.NODE_INVALID, t.line, t.col);
    }
    Node* r = self.parse_assign();
    self.leave();
    return r;
}

// 15. Assignment (right-assoc): =  +=  -=  *=  /=  %=  &=  |=  ^=  <<=  >>=
fn Node* Parser.parse_assign(Parser* self)
{
    Node* lhs = self.parse_compose();

    if (is_assign_op(self.cur.type))
    {
        Tok op = self.advance();
        Node* rhs = self.parse_assign();   // right-assoc
        return ast::node_op(self.arena, Nk.NODE_EXPR_ASSIGN, op.type, &make2(lhs, rhs)[0], 2, op.line, op.col);
    }
    return lhs;
}

fn bool is_assign_op(Tt t) @private
{
    switch (t)
    {
        case Tt.TOKEN_EQ:
        case Tt.TOKEN_PLUSEQ:
        case Tt.TOKEN_MINUSEQ:
        case Tt.TOKEN_STAREQ:
        case Tt.TOKEN_SLASHEQ:
        case Tt.TOKEN_PERCENTEQ:
        case Tt.TOKEN_AMPEQ:
        case Tt.TOKEN_PIPEEQ:
        case Tt.TOKEN_XOREQ:
        case Tt.TOKEN_LSHIFTEQ:
        case Tt.TOKEN_RSHIFTEQ:
            return true;
        default:
            return false;
    }
}

// 20. Rewrite-rule composition:  ++  (left-assoc, looser than range/pipeline)
// Per v.md §11/§23, rule sets compose with `++`:  arith ++ strength_reduce
fn Node* Parser.parse_compose(Parser* self)
{
    Node* lhs = self.parse_range();
    while (self.check(Tt.TOKEN_PLUSPLUS))
    {
        Tok op = self.advance();
        Node* rhs = self.parse_range();
        lhs = ast::node_binary(self.arena, op.type, lhs, rhs, op.line, op.col);
    }
    return lhs;
}

// 14. Range:  start..end  |  start..=end  |  start..end by step  |  start..=end by step
fn Node* Parser.parse_range(Parser* self)
{
    Node* lhs = self.parse_pipeline();

    if (self.check(Tt.TOKEN_DOTDOT) || self.check(Tt.TOKEN_DOTDOTEQ))
    {
        Tok op        = self.advance();
        bool inclusive = (op.type == Tt.TOKEN_DOTDOTEQ);
        Node* rhs     = self.parse_pipeline();

        // Optional step:  start..end by step   (e.g. 0..100 by 2)
        // "by" is a proper keyword (TOKEN_KW_BY) so no text-matching needed.
        if (self.check(Tt.TOKEN_KW_BY))
        {
            self.advance();   // consume "by"
            Node* step = self.parse_pipeline();
            return ast::node_range_step(self.arena, lhs, rhs, step, inclusive, op.line, op.col);
        }

        // Plain range without step.
        Node* node = ast::node2(self.arena, Nk.NODE_EXPR_RANGE, lhs, rhs, op.line, op.col);
        if (inclusive && node != null) node.flags |= ast::FLAG_RANGE_INCLUSIVE;
        return node;
    }
    return lhs;
}

// 13. Pipeline:  |>   (left-assoc).  `rules*` fixpoint handled in postfix.
fn Node* Parser.parse_pipeline(Parser* self)
{
    Node* lhs = self.parse_logic_or();

    while (self.check(Tt.TOKEN_PIPELINE))
    {
        Tok op = self.advance();
        Node* rhs = self.parse_logic_or();

        // A trailing '*' marks fixpoint application:  expr |> rules*
        bool fixpoint = false;
        if (self.check(Tt.TOKEN_STAR))
        {
            self.advance();
            fixpoint = true;
        }

        Node* node = ast::node2(self.arena, Nk.NODE_EXPR_PIPELINE, lhs, rhs, op.line, op.col);
        if (fixpoint && node != null)
        {
            node.flags |= ast::FLAG_FIXPOINT;
            node = ast::node1(self.arena, Nk.NODE_FIXPOINT, node, op.line, op.col);
        }
        lhs = node;
    }
    return lhs;
}

// 12. Logical OR:  or  ||
fn Node* Parser.parse_logic_or(Parser* self)
{
    Node* lhs = self.parse_logic_and();
    while (self.check(Tt.TOKEN_KW_OR) || self.check(Tt.TOKEN_PIPEPIPE))
    {
        Tok op = self.advance();
        Node* rhs = self.parse_logic_and();
        lhs = ast::node_binary(self.arena, op.type, lhs, rhs, op.line, op.col);
    }
    return lhs;
}

// 11. Logical AND:  and  &&
fn Node* Parser.parse_logic_and(Parser* self)
{
    Node* lhs = self.parse_compare();
    while (self.check(Tt.TOKEN_KW_AND) || self.check(Tt.TOKEN_AMPAMP))
    {
        Tok op = self.advance();
        Node* rhs = self.parse_compare();
        lhs = ast::node_binary(self.arena, op.type, lhs, rhs, op.line, op.col);
    }
    return lhs;
}

// 10. Comparison:  <  >  <=  >=  ==  !=  ≤  ≥  ≠   (non-assoc, but we chain)
fn Node* Parser.parse_compare(Parser* self)
{
    Node* lhs = self.parse_bit_or();
    while (is_compare_op(self.cur.type))
    {
        Tok op = self.advance();
        Node* rhs = self.parse_bit_or();
        lhs = ast::node_binary(self.arena, op.type, lhs, rhs, op.line, op.col);
    }
    return lhs;
}

// 9. Bitwise OR:  |
fn Node* Parser.parse_bit_or(Parser* self)
{
    Node* lhs = self.parse_bit_xor();
    // Don't consume a `|` that closes a tensor literal (`|]`) as bitwise-or.
    while (self.check(Tt.TOKEN_PIPE) && self.peek1().type != Tt.TOKEN_RBRACK)
    {
        Tok op = self.advance();
        Node* rhs = self.parse_bit_xor();
        lhs = ast::node_binary(self.arena, op.type, lhs, rhs, op.line, op.col);
    }
    return lhs;
}

// 8. Bitwise XOR:  ^
fn Node* Parser.parse_bit_xor(Parser* self)
{
    Node* lhs = self.parse_bit_and();
    while (self.check(Tt.TOKEN_XOR))
    {
        Tok op = self.advance();
        Node* rhs = self.parse_bit_and();
        lhs = ast::node_binary(self.arena, op.type, lhs, rhs, op.line, op.col);
    }
    return lhs;
}

// 7. Bitwise AND:  &
fn Node* Parser.parse_bit_and(Parser* self)
{
    Node* lhs = self.parse_shift();
    while (self.check(Tt.TOKEN_AMP))
    {
        Tok op = self.advance();
        Node* rhs = self.parse_shift();
        lhs = ast::node_binary(self.arena, op.type, lhs, rhs, op.line, op.col);
    }
    return lhs;
}

// 6. Shift:  <<  >>
fn Node* Parser.parse_shift(Parser* self)
{
    Node* lhs = self.parse_add();
    while (self.check(Tt.TOKEN_LSHIFT) || self.check(Tt.TOKEN_RSHIFT))
    {
        Tok op = self.advance();
        Node* rhs = self.parse_add();
        lhs = ast::node_binary(self.arena, op.type, lhs, rhs, op.line, op.col);
    }
    return lhs;
}

// 5. Additive:  +  -
fn Node* Parser.parse_add(Parser* self)
{
    Node* lhs = self.parse_mul();
    while (self.check(Tt.TOKEN_PLUS) || self.check(Tt.TOKEN_MINUS)
        || self.check(Tt.TOKEN_PLUS_QUESTION) || self.check(Tt.TOKEN_MINUS_QUESTION)
        || self.check(Tt.TOKEN_PLUS_PERCENT)  || self.check(Tt.TOKEN_MINUS_PERCENT)
        || self.check(Tt.TOKEN_PLUS_PIPE)     || self.check(Tt.TOKEN_MINUS_PIPE))
    {
        Tok op = self.advance();
        Node* rhs = self.parse_mul();
        lhs = ast::node_binary(self.arena, op.type, lhs, rhs, op.line, op.col);
    }
    return lhs;
}

// 4. Multiplicative:  *  /  %
// A '*' is only binary multiplication when a real operand follows. A trailing
// '*' (e.g. `rules*` for fixpoint application, v.md §11/§17) is left for the
// pipeline layer to pick up.
fn Node* Parser.parse_mul(Parser* self)
{
    Node* lhs = self.parse_matmul();
    while (self.check(Tt.TOKEN_SLASH) || self.check(Tt.TOKEN_PERCENT)
        || self.check(Tt.TOKEN_STAR_QUESTION)
        || self.check(Tt.TOKEN_STAR_PERCENT) || self.check(Tt.TOKEN_STAR_PIPE)
        || (self.check(Tt.TOKEN_STAR) && can_start_expr(self.peek1().type)))
    {
        Tok op = self.advance();
        Node* rhs = self.parse_matmul();
        lhs = ast::node_binary(self.arena, op.type, lhs, rhs, op.line, op.col);
    }
    return lhs;
}

// 4b. Tensor contraction:  a @ b  (matmul). Binds tighter than * / %, so
// `A @ B * s` is `(A @ B) * s`. Left-associative.
fn Node* Parser.parse_matmul(Parser* self)
{
    Node* lhs = self.parse_cast();
    while (self.check(Tt.TOKEN_AT))
    {
        Tok op = self.advance();
        Node* rhs = self.parse_cast();
        lhs = ast::node2(self.arena, Nk.NODE_EXPR_MATMUL, lhs, rhs, op.line, op.col);
    }
    return lhs;
}

// True if a token can begin an expression (used to disambiguate trailing '*').
fn bool can_start_expr(Tt t)
{
    switch (t)
    {
        case Tt.TOKEN_LIT_INT:
        case Tt.TOKEN_LIT_FLOAT:
        case Tt.TOKEN_LIT_BOOL:
        case Tt.TOKEN_LIT_CHAR:
        case Tt.TOKEN_LIT_STRING:
        case Tt.TOKEN_LIT_RAW_BYTES:
        case Tt.TOKEN_LIT_NULL:
        case Tt.TOKEN_KW_NULLPTR:
        case Tt.TOKEN_IDENT:
        case Tt.TOKEN_TYPEVAR:
        case Tt.TOKEN_WILDCARD:
        case Tt.TOKEN_LPAREN:
        case Tt.TOKEN_LBRACK:
        case Tt.TOKEN_STAR:
        case Tt.TOKEN_AMP:
        case Tt.TOKEN_MINUS:
        case Tt.TOKEN_PLUS:
        case Tt.TOKEN_BANG:
        case Tt.TOKEN_KW_NOT:
        case Tt.TOKEN_NEGATION:
        case Tt.TOKEN_BOTTOM:
        case Tt.TOKEN_SIGIL_TREE:
        case Tt.TOKEN_SIGIL_DATA:
        case Tt.TOKEN_SIGIL_BYTES:
        case Tt.TOKEN_KW_IF:
        case Tt.TOKEN_KW_MATCH:
        case Tt.TOKEN_KW_ALLOC:
        case Tt.TOKEN_KW_UB_BANG:
            return true;
        default:
            return false;
    }
}

// 3. Cast:  expr as Type
fn Node* Parser.parse_cast(Parser* self)
{
    Node* e = self.parse_prefix();
    while (self.check(Tt.TOKEN_KW_AS))
    {
        Tok op = self.advance();
        Node* ty = self.parse_type_prefix();
        e = ast::node2(self.arena, Nk.NODE_EXPR_CAST, e, ty, op.line, op.col);
    }
    return e;
}

// 2. Prefix:  *p  &x  -x  not x  ¬  ~Tree ~Data ~Bytes  and meta prefixes
fn Node* Parser.parse_prefix(Parser* self)
{
    // Depth-guard the unary-prefix recursion (*x / -x / !x / sigils / …) so a
    // long prefix chain is rejected, not crashed.
    if (!self.enter())
    {
        Tok t = self.cur;
        if (!self.at_end()) self.advance();
        self.leave();
        return ast::node0(self.arena, Nk.NODE_INVALID, t.line, t.col);
    }
    Node* r = self.parse_prefix_inner();
    self.leave();
    return r;
}

fn Node* Parser.parse_prefix_inner(Parser* self)
{
    Tok t = self.cur;

    switch (t.type)
    {
        case Tt.TOKEN_STAR:      // *p   dereference
        case Tt.TOKEN_AMP:       // &x   address-of
        case Tt.TOKEN_MINUS:     // -x   negate
        case Tt.TOKEN_BANG:      // !x   logical not
        case Tt.TOKEN_KW_NOT:    // not x
        case Tt.TOKEN_NEGATION:  // ¬x   type/logical negation
        case Tt.TOKEN_PLUS:      // +x   unary plus
        case Tt.TOKEN_TILDE:     // ~x   bare tilde (non-sigil)
        case Tt.TOKEN_DOLLAR:    // $x   compile-time / meta marker
        case Tt.TOKEN_BACKTICK:  // `x   quasiquote marker
            self.advance();
            Node* operand = self.parse_prefix();
            return ast::node_unary(self.arena, t.type, operand, t.line, t.col);

        case Tt.TOKEN_SIGIL_TREE:
            self.advance();
            return ast::node1(self.arena, Nk.NODE_SIGIL_TREE, self.parse_prefix(), t.line, t.col);
        case Tt.TOKEN_SIGIL_DATA:
            self.advance();
            return ast::node1(self.arena, Nk.NODE_SIGIL_DATA, self.parse_prefix(), t.line, t.col);
        case Tt.TOKEN_SIGIL_BYTES:
            self.advance();
            return ast::node1(self.arena, Nk.NODE_SIGIL_BYTES, self.parse_prefix(), t.line, t.col);

        case Tt.TOKEN_KW_ALLOC:
            return self.parse_alloc();
        case Tt.TOKEN_KW_FREE:
            self.advance();
            Node* fop = self.parse_prefix();
            Node* fn_node = ast::node1(self.arena, Nk.NODE_EXPR_FREE, fop, t.line, t.col);
            ast::node_add_effect(fn_node, ast::EFFECT_ALLOC);
            return fn_node;

        case Tt.TOKEN_KW_UNCHECKED:
            self.advance();
            Node* uop = self.parse_prefix();
            Node* un = ast::node1(self.arena, Nk.NODE_EXPR_UNCHECKED, uop, t.line, t.col);
            if (un != null) un.flags |= ast::FLAG_UNCHECKED;
            return un;

        default:
            return self.parse_apply();
    }
}

// Juxtaposition application (ML-style):  f x,  k s,  k sys_read(),  k arena(n)
// Used for continuation resumption in effect handlers and curried calls.
// We absorb a following expression as an argument only when it unambiguously
// begins a new atom (ident / literal / '(' / sigil / etc.) AND the callee is
// something callable (a name, field access, or another application). Operator
// tokens like '+' '*' '|>' are NOT argument starters, so arithmetic is safe.
fn Node* Parser.parse_apply(Parser* self)
{
    Node* e = self.parse_postfix();

    while (self.callee_is_applicable(e) && can_start_atom(self.cur.type)
        && !self.at_soft_keyword())
    {
        int line = self.cur.line;
        int col = self.cur.col;
        Node* arg = self.parse_postfix();
        e = ast::node2(self.arena, Nk.NODE_EXPR_CALL, e, arg, line, col);
    }
    return e;
}

// True when the current token is a contextual soft keyword (`then`, `else`)
// that must terminate juxtaposition application rather than be absorbed as an
// argument. (These are not reserved tokens, so the lexer returns them as idents
// — except `else`, which IS a real keyword and is excluded by can_start_atom.)
fn bool Parser.at_soft_keyword(Parser* self)
{
    if (self.cur.type != Tt.TOKEN_IDENT) return false;
    if (tok_text_eq(self.cur, "then", 4)) return true;
    return false;
}

fn bool Parser.callee_is_applicable(Parser* self, Node* e)
{
    if (e == null) return false;
    switch (e.kind)
    {
        case Nk.NODE_IDENT:
        case Nk.NODE_TYPEVAR:
        case Nk.NODE_EXPR_FIELD:
        case Nk.NODE_EXPR_CALL:
        case Nk.NODE_EXPR_METHOD_CALL:
        case Nk.NODE_EXPR_INDEX:
            return true;
        default:
            return false;
    }
}

// A token that can begin an *atomic* argument for juxtaposition application.
// Deliberately excludes '-' '*' '&' (ambiguous binary/unary) so that
// `a - b`, `a * b`, `p & q` keep their binary reading.
fn bool can_start_atom(Tt t)
{
    switch (t)
    {
        case Tt.TOKEN_LIT_INT:
        case Tt.TOKEN_LIT_FLOAT:
        case Tt.TOKEN_LIT_BOOL:
        case Tt.TOKEN_LIT_CHAR:
        case Tt.TOKEN_LIT_STRING:
        case Tt.TOKEN_LIT_RAW_BYTES:
        case Tt.TOKEN_LIT_NULL:
        case Tt.TOKEN_KW_NULLPTR:
        case Tt.TOKEN_IDENT:
        case Tt.TOKEN_TYPEVAR:
        case Tt.TOKEN_WILDCARD:
        case Tt.TOKEN_LPAREN:
            return true;
        // IRDL/graph soft keywords used freely as identifiers in expression position:
        // node, edge, block, graph, lower, region, opcode, hyperedge
        case Tt.TOKEN_KW_LOWER:
        case Tt.TOKEN_KW_OPCODE:
        case Tt.TOKEN_KW_REGION:
        case Tt.TOKEN_KW_BLOCK:
        case Tt.TOKEN_KW_NODE:
        case Tt.TOKEN_KW_EDGE:
        case Tt.TOKEN_KW_HYPEREDGE:
        case Tt.TOKEN_KW_GRAPH:
            return true;
        default:
            return false;
    }
}

// alloc Type   |   alloc [T; N]
fn Node* Parser.parse_alloc(Parser* self)
{
    Tok kw = self.advance();   // alloc
    Node* what = self.parse_type_prefix();
    Node* node = ast::node1(self.arena, Nk.NODE_EXPR_ALLOC, what, kw.line, kw.col);
    ast::node_add_effect(node, ast::EFFECT_ALLOC);
    return node;
}

// 1. Postfix:  f(args)  obj.field  obj.method(args)  arr[i]
fn Node* Parser.parse_postfix(Parser* self)
{
    Node* e = self.parse_primary();

    bool more = true;
    while (more)
    {
        switch (self.cur.type)
        {
            case Tt.TOKEN_LPAREN:
                e = self.parse_call(e);
            case Tt.TOKEN_LBRACK:
                e = self.parse_index(e);
            case Tt.TOKEN_DOT:
                e = self.parse_field_or_method(e);
            case Tt.TOKEN_COLONCOLON:
                e = self.parse_path_access(e);
            case Tt.TOKEN_QUESTION:
                // postfix '?' — try / optional-propagation operator
                Tok q = self.advance();
                e = ast::node_unary(self.arena, Tt.TOKEN_QUESTION, e, q.line, q.col);
            case Tt.TOKEN_LBRACE:
                // struct literal update / construction:  Name { ... }
                if (e != null && (e.kind == Nk.NODE_IDENT || e.kind == Nk.NODE_TYPEVAR
                    || e.kind == Nk.NODE_EXPR_FIELD || e.kind == Nk.NODE_TYPE_PATH))
                {
                    e = self.parse_struct_lit(e);
                }
                else
                {
                    more = false;
                }
            default:
                more = false;
        }
    }
    return e;
}

fn Node* Parser.parse_call(Parser* self, Node* callee)
{
    Tok lp = self.advance();   // (
    Scratch s;
    s.reset();
    s.push(callee);

    if (!self.check(Tt.TOKEN_RPAREN))
    {
        s.push(self.parse_arg());
        while (self.accept(Tt.TOKEN_COMMA))
        {
            if (self.check(Tt.TOKEN_RPAREN)) break;
            s.push(self.parse_arg());
        }
    }
    self.expect(Tt.TOKEN_RPAREN, "expected ')' to close call");
    return self.finish(Nk.NODE_EXPR_CALL, &s, lp.line, lp.col);
}

fn Node* Parser.parse_arg(Parser* self)
{
    return self.parse_expr();
}

fn Node* Parser.parse_index(Parser* self, Node* base)
{
    Tok lb = self.advance();   // [
    Node* idx = self.parse_expr();
    self.expect(Tt.TOKEN_RBRACK, "expected ']' to close index");
    return ast::node2(self.arena, Nk.NODE_EXPR_INDEX, base, idx, lb.line, lb.col);
}

fn Node* Parser.parse_field_or_method(Parser* self, Node* base)
{
    Tok dot = self.advance();   // .
    if (!self.at_member_name())
    {
        self.error("expected field or method name after '.'");
        return base;
    }
    Tok name = self.advance();
    Node* nm = self.name_from(name, Nk.NODE_IDENT);

    if (self.check(Tt.TOKEN_LPAREN))
    {
        // method call
        Tok lp = self.advance();
        Scratch s;
        s.reset();
        s.push(base);
        s.push(nm);
        if (!self.check(Tt.TOKEN_RPAREN))
        {
            s.push(self.parse_arg());
            while (self.accept(Tt.TOKEN_COMMA))
            {
                if (self.check(Tt.TOKEN_RPAREN)) break;
                s.push(self.parse_arg());
            }
        }
        self.expect(Tt.TOKEN_RPAREN, "expected ')' to close method call");
        return self.finish(Nk.NODE_EXPR_METHOD_CALL, &s, lp.line, lp.col);
    }

    return ast::node2(self.arena, Nk.NODE_EXPR_FIELD, base, nm, dot.line, dot.col);
}

fn Node* Parser.parse_path_access(Parser* self, Node* base)
{
    Tok cc = self.advance();   // ::
    if (!self.at_member_name())
    {
        self.error("expected name after '::'");
        return base;
    }
    Tok name = self.advance();
    Node* nm = self.name_from(name, Nk.NODE_IDENT);
    return ast::node2(self.arena, Nk.NODE_EXPR_FIELD, base, nm, cc.line, cc.col);
}

// Name { field: val, ... }
fn Node* Parser.parse_struct_lit(Parser* self, Node* name)
{
    Tok lb = self.advance();   // {
    Scratch s;
    s.reset();
    s.push(name);

    self.skip_newlines();
    if (!self.check(Tt.TOKEN_RBRACE))
    {
        s.push(self.parse_field_init());
        while (self.accept(Tt.TOKEN_COMMA))
        {
            self.skip_newlines();
            if (self.check(Tt.TOKEN_RBRACE)) break;
            s.push(self.parse_field_init());
        }
    }
    self.skip_newlines();
    self.expect(Tt.TOKEN_RBRACE, "expected '}' to close struct literal");
    return self.finish(Nk.NODE_EXPR_STRUCT_LIT, &s, lb.line, lb.col);
}

// field_init ::= name (: expr)?   (shorthand allowed:  { x, y })
fn Node* Parser.parse_field_init(Parser* self)
{
    if (!(self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR) || self.at_member_name()))
    {
        self.error("expected field name in struct literal");
        self.advance();
        return ast::node0(self.arena, Nk.NODE_INVALID, self.cur.line, self.cur.col);
    }
    Tok name = self.advance();
    Node* nm = self.name_from(name, Nk.NODE_IDENT);

    // Accept both `field: expr` and `field = expr` styles.
    if (self.accept(Tt.TOKEN_COLON) || self.accept(Tt.TOKEN_EQ))
    {
        Node* val = self.parse_expr();
        return ast::node2(self.arena, Nk.NODE_FIELD_INIT, nm, val, name.line, name.col);
    }
    return ast::node1(self.arena, Nk.NODE_FIELD_INIT, nm, name.line, name.col);
}

// Primary expressions: literals, names, grouped/tuple, array literals,
// control-flow-as-expression, metaprogramming, UB/safety, etc.
fn Node* Parser.parse_primary(Parser* self)
{
    Tok t = self.cur;

    switch (t.type)
    {
        case Tt.TOKEN_LIT_INT:        return self.parse_int_lit();
        case Tt.TOKEN_LIT_FLOAT:      return self.parse_float_lit();
        case Tt.TOKEN_LIT_BOOL:
            self.advance();
            return ast::node_bool(self.arena, tok_text_eq(t, "true", 4), t.line, t.col);
        case Tt.TOKEN_LIT_CHAR:
            self.advance();
            return ast::node_char(self.arena, parse_char_value(t.start, t.len), t.line, t.col);
        case Tt.TOKEN_LIT_STRING:
            {
                self.advance();
                // Interpolated string detection:  "hello {name}, age {age}"
                // We scan the raw bytes for '{' ... '}' holes.  If any are found
                // we split into alternating segments and parse the hole contents
                // as sub-expressions.  Otherwise it's a plain string literal.
                char* src    = t.start;
                usz   src_len = t.len;
                // Quick check: any NON-EMPTY '{' hole in the string body?
                // `{name}` is (unimplemented) interpolation; `{}` is a
                // positional format! template hole (fine inside format!) and
                // `{{` is an escaped literal brace — neither is an error.
                bool has_holes = false;
                for (usz si = 0; si + 1 < src_len; si++)
                {
                    if (src[si] == '{')
                    {
                        if (src[si+1] == '{') { si++; continue; }   // escaped '{'
                        if (src[si+1] != '}') { has_holes = true; break; }
                    }
                }
                if (!has_holes)
                {
                    return ast::node_str(self.arena, Nk.NODE_LIT_STRING, t.start, t.len, t.line, t.col);
                }
                // Interpolation holes in a plain string literal have NO working
                // lowering: holes were collected as raw source bytes for a
                // nested-lexer re-parse that was never implemented, so the
                // program compiled cleanly and then printed nothing/garbage —
                // a silent miscompile. Fail loudly instead and point at the
                // supported path. Recovery: degrade to the plain literal text
                // (a single diagnostic, downstream still sees a normal string).
                self.error("named interpolation holes `{name}` are not supported; use format! with positional holes: format!(\"value: {}\", x)");
                return ast::node_str(self.arena, Nk.NODE_LIT_STRING, t.start, t.len, t.line, t.col);
            }
        case Tt.TOKEN_LIT_RAW_BYTES:
            self.advance();
            return ast::node_str(self.arena, Nk.NODE_LIT_RAW_BYTES, t.start, t.len, t.line, t.col);
        case Tt.TOKEN_LIT_NULL:
        case Tt.TOKEN_KW_NULLPTR:
            self.advance();
            return ast::node_null(self.arena, t.line, t.col);
        case Tt.TOKEN_BOTTOM:
            self.advance();
            return ast::node0(self.arena, Nk.NODE_LIT_BOTTOM, t.line, t.col);
        case Tt.TOKEN_EMPTYSET:
            // ∅  empty set value / empty effect row literal
            self.advance();
            return ast::node0(self.arena, Nk.NODE_LIT_BOTTOM, t.line, t.col);

        case Tt.TOKEN_FORALL:
            // ∀ A . body   universal quantifier in value/type position
            self.advance();
            return self.parse_quantifier_expr(Nk.NODE_TYPE_FORALL, t);
        case Tt.TOKEN_EXISTS:
            // ∃ T . body   existential quantifier
            self.advance();
            return self.parse_quantifier_expr(Nk.NODE_TYPE_EXISTS, t);

        case Tt.TOKEN_IDENT:
            {
                // Compile-time macro calls: include_bytes!(...), env!(...),
                // concat!(...), format!(...). The BANG IS MANDATORY:
                // `name!(...)` is a macro invocation, a bare `name(...)` is
                // ALWAYS an ordinary function call. Treating the bare form as
                // a macro hijacked any user-declared function with one of these
                // exact names — silently rewriting its call sites into
                // format-string construction (a real observed miscompile:
                // `fn format : i32 -> i32` + `format(41)` produced a
                // { ptr, i64, i64 } format record instead of a call).
                // NOTE: these MUST stay exact full-name comparisons
                // (tok_text_eq checks every byte), never partial byte sniffing.
                bool ib = tok_text_eq(t, "include_bytes", 13);
                bool ev = tok_text_eq(t, "env", 3);
                bool cc = tok_text_eq(t, "concat", 6);
                bool fm = tok_text_eq(t, "format", 6);
                bool macro_head = (ib||ev||cc||fm)
                    && self.peek1().type == Tt.TOKEN_BANG
                    && self.peek2().type == Tt.TOKEN_LPAREN;
                if (macro_head)
                {
                    self.advance();  // consume IDENT
                    self.advance();  // consume !
                    self.advance();  // consume (
                    if (fm)
                    {
                        // format!("template", arg0, arg1, ...) — collect all args
                        Scratch fs;
                        fs.reset();
                        while (!self.check(Tt.TOKEN_RPAREN) && !self.check(Tt.TOKEN_EOF))
                        {
                            fs.push(self.parse_expr());
                            if (self.check(Tt.TOKEN_COMMA)) self.advance();
                        }
                        self.accept(Tt.TOKEN_RPAREN);
                        return self.finish(Nk.NODE_EXPR_FORMAT, &fs, t.line, t.col);
                    }
                    Node* arg2 = null;
                    if (!self.check(Tt.TOKEN_RPAREN)) arg2 = self.parse_expr();
                    self.accept(Tt.TOKEN_RPAREN);
                    Nk mk = ib ? Nk.NODE_EXPR_INCLUDE_BYTES
                             : ev ? Nk.NODE_EXPR_ENV_VAR
                             :      Nk.NODE_EXPR_CONCAT;
                    return ast::node1(self.arena, mk, arg2, t.line, t.col);
                }
                self.advance();
                return self.name_from(t, Nk.NODE_IDENT);
            }
        case Tt.TOKEN_TYPEVAR:
            self.advance();
            return self.name_from(t, Nk.NODE_TYPEVAR);
        case Tt.TOKEN_WILDCARD:
            self.advance();
            return ast::node_wildcard(self.arena, t.line, t.col);

        case Tt.TOKEN_LPAREN:
            return self.parse_paren_expr();
        case Tt.TOKEN_LBRACK:
            // [| ... |]  is a tensor literal; plain [ ... ] is an array literal.
            if (self.peek1().type == Tt.TOKEN_PIPE)
            {
                return self.parse_tensor_lit();
            }
            return self.parse_array_lit();

        case Tt.TOKEN_KW_IF:        return self.parse_if();
        case Tt.TOKEN_KW_MATCH:     return self.parse_match();
        case Tt.TOKEN_KW_WHILE:     return self.parse_while();
        case Tt.TOKEN_KW_FOR:       return self.parse_for();
        case Tt.TOKEN_KW_DO:        return self.parse_do_while();

        // 'label: while / 'label: for / 'label: do
        // A TOKEN_LABEL_REF followed by ':' followed by a loop keyword
        // introduces a labeled loop. We attach the label name to the loop node.
        case Tt.TOKEN_LABEL_REF:
            {
                // Peek: next token after label_ref should be ':' or COLON
                Tok lbl_tok = self.cur;
                self.advance(); // consume label ref
                self.skip_newlines();
                if (self.check(Tt.TOKEN_COLON))
                {
                    self.advance(); // consume ':'
                    self.skip_newlines();
                    // Parse the loop
                    Node* loop_node = null;
                    if (self.check(Tt.TOKEN_KW_WHILE)) { loop_node = self.parse_while(); }
                    else if (self.check(Tt.TOKEN_KW_FOR)) { loop_node = self.parse_for(); }
                    else if (self.check(Tt.TOKEN_KW_DO)) { loop_node = self.parse_do_while(); }
                    else { self.error("expected while/for/do after loop label"); return null; }
                    if (loop_node != null)
                    {
                        // Attach label node as first child of the loop
                        Node* lbl_node = self.name_from(lbl_tok, Nk.NODE_IDENT);
                        Node* labeled = ast::node2(self.arena, Nk.NODE_EXPR_LABELED,
                                                   lbl_node, loop_node, lbl_tok.line, lbl_tok.col);
                        return labeled;
                    }
                }
                // Not a labeled loop: treat as a standalone label ref expression (error context)
                return self.name_from(lbl_tok, Nk.NODE_IDENT);
            }

        case Tt.TOKEN_KW_RETURN:    return self.parse_return();

        case Tt.TOKEN_KW_UB_BANG:   return self.parse_ub_bang();
        case Tt.TOKEN_KW_POISON:    self.advance(); return effecting(ast::node0(self.arena, Nk.NODE_EXPR_POISON, t.line, t.col), ast::EFFECT_UB);
        case Tt.TOKEN_KW_FREEZE:    self.advance(); return ast::node1(self.arena, Nk.NODE_EXPR_FREEZE, self.parse_prefix(), t.line, t.col);
        case Tt.TOKEN_KW_TRAP:      self.advance(); return ast::node0(self.arena, Nk.NODE_STMT_TRAP, t.line, t.col);
        case Tt.TOKEN_KW_UNREACHABLE: self.advance(); return ast::node0(self.arena, Nk.NODE_STMT_UNREACHABLE, t.line, t.col);

        case Tt.TOKEN_KW_SIZEOF:    self.advance(); return ast::node1(self.arena, Nk.NODE_EXPR_SIZEOF, self.parse_paren_or_type(), t.line, t.col);
        case Tt.TOKEN_KW_TAIL:
            // tail expr — mark a call as a tail call (musttail in LLVM)
            { self.advance(); return ast::node1(self.arena, Nk.NODE_EXPR_TAILCALL, self.parse_expr(), t.line, t.col); }

        // Detected when primary sees an IDENT "include_bytes" / "env" / "concat"
        // followed by "!" "(". We parse them here via the IDENT check fallthrough.

        case Tt.TOKEN_KW_OFFSETOF:
            {
                self.advance();
                self.expect(Tt.TOKEN_LPAREN, "expected '(' after offset_of");
                Node* ty2 = self.parse_type();
                self.expect(Tt.TOKEN_COMMA, "expected ',' in offset_of(Type, field)");
                Node* fld = self.parse_primary();
                self.expect(Tt.TOKEN_RPAREN, "expected ')' after offset_of");
                return ast::node2(self.arena, Nk.NODE_EXPR_OFFSETOF, ty2, fld, t.line, t.col);
            }
        case Tt.TOKEN_KW_VOLATILE:
            {
                self.advance();
                // volatile load(ptr) or volatile store(ptr, val)
                self.skip_newlines();
                // Check for "store" keyword (TOKEN_IDENT with text "store")
                bool is_store_kw = self.check(Tt.TOKEN_IDENT) && self.cur.len == 5
                    && self.cur.start[0]=='s'&&self.cur.start[1]=='t'&&self.cur.start[2]=='o'
                    &&self.cur.start[3]=='r'&&self.cur.start[4]=='e';
                if (is_store_kw)
                {
                    // volatile store(ptr, val)
                    self.advance();
                    self.expect(Tt.TOKEN_LPAREN, "expected '(' after volatile store");
                    Node* ptr2 = self.parse_expr();
                    self.expect(Tt.TOKEN_COMMA, "expected ','");
                    Node* val2 = self.parse_expr();
                    self.expect(Tt.TOKEN_RPAREN, "expected ')'");
                    return ast::node2(self.arena, Nk.NODE_EXPR_VOLATILE_STORE, ptr2, val2, t.line, t.col);
                }
                else
                {
                    // volatile(ptr) = volatile load
                    self.expect(Tt.TOKEN_LPAREN, "expected '(' after volatile");
                    Node* ptr3 = self.parse_expr();
                    self.expect(Tt.TOKEN_RPAREN, "expected ')'");
                    return ast::node1(self.arena, Nk.NODE_EXPR_VOLATILE_LOAD, ptr3, t.line, t.col);
                }
            }
        case Tt.TOKEN_KW_FENCE:
            {
                // fence(acquire|release|acq_rel|seq_cst)
                self.advance();
                self.expect(Tt.TOKEN_LPAREN, "expected '(' after fence");
                Node* ord = self.parse_expr();
                self.expect(Tt.TOKEN_RPAREN, "expected ')' after fence ordering");
                return ast::node1(self.arena, Nk.NODE_EXPR_FENCE, ord, t.line, t.col);
            }
        case Tt.TOKEN_KW_ATOMIC_ADD:
        case Tt.TOKEN_KW_ATOMIC_SUB:
        case Tt.TOKEN_KW_ATOMIC_AND:
        case Tt.TOKEN_KW_ATOMIC_OR:
        case Tt.TOKEN_KW_ATOMIC_XOR:
        case Tt.TOKEN_KW_ATOMIC_XCHG:
            {
                // atomic_op(ptr, val) — fetch-and-op, returns old value
                self.advance();
                self.expect(Tt.TOKEN_LPAREN, "expected '(' after atomic op");
                Node* aptr = self.parse_expr();
                self.expect(Tt.TOKEN_COMMA, "expected ','");
                Node* aval = self.parse_expr();
                self.expect(Tt.TOKEN_RPAREN, "expected ')'");
                Node* nd = ast::node2(self.arena, Nk.NODE_EXPR_ATOMIC_RMW, aptr, aval, t.line, t.col);
                // Encode which op in the payload: 0=add 1=sub 2=and 3=or 4=xor 5=xchg
                if (nd != null)
                {
                    int aop = 0;
                    if (t.type == Tt.TOKEN_KW_ATOMIC_SUB)       { aop = 1; }
                    else if (t.type == Tt.TOKEN_KW_ATOMIC_AND)  { aop = 2; }
                    else if (t.type == Tt.TOKEN_KW_ATOMIC_OR)   { aop = 3; }
                    else if (t.type == Tt.TOKEN_KW_ATOMIC_XOR)  { aop = 4; }
                    else if (t.type == Tt.TOKEN_KW_ATOMIC_XCHG) { aop = 5; }
                    nd.p.raw = (ulong)aop;
                }
                return nd;
            }
        case Tt.TOKEN_KW_ATOMIC_CMPXCHG:
            {
                // atomic_cmpxchg(ptr, expected, desired) → (old, success)
                self.advance();
                self.expect(Tt.TOKEN_LPAREN, "expected '(' after atomic_cmpxchg");
                Node* cptr = self.parse_expr();
                self.expect(Tt.TOKEN_COMMA, "expected ','");
                Node* cexp = self.parse_expr();
                self.expect(Tt.TOKEN_COMMA, "expected ','");
                Node* cnew = self.parse_expr();
                self.expect(Tt.TOKEN_RPAREN, "expected ')'");
                return ast::node3(self.arena, Nk.NODE_EXPR_ATOMIC_CMPXCHG, cptr, cexp, cnew, t.line, t.col);
            }
        case Tt.TOKEN_KW_SYSCALL:
            {
                self.advance();
                // syscall(num, arg0, arg1, ...) — up to 6 args
                self.expect(Tt.TOKEN_LPAREN, "expected '(' after syscall");
                Scratch sc2;
                sc2.reset();
                while (!self.check(Tt.TOKEN_RPAREN) && !self.check(Tt.TOKEN_EOF))
                {
                    sc2.push(self.parse_expr());
                    if (self.check(Tt.TOKEN_COMMA)) self.advance();
                }
                self.expect(Tt.TOKEN_RPAREN, "expected ')'");
                Node* syscall_node = self.finish(Nk.NODE_EXPR_SYSCALL, &sc2, t.line, t.col);
                // A raw kernel syscall is the project's own idiomatic way to
                // do I/O (see examples/*.pie, tests/exec/*.pie) — tag it with
                // EFFECT_IO so the effect checker's "no hidden behavior"
                // guarantee actually covers it, matching every other
                // effectful primitive built here (alloc/free/asm/ub!/handle
                // all call node_add_effect on themselves). Kept consistent
                // with alloc/free, which likewise only require ! [Alloc] and
                // not also ! [Unsafe] despite being similarly low-level.
                ast::node_add_effect(syscall_node, ast::EFFECT_IO);
                return syscall_node;
            }
        case Tt.TOKEN_KW_ALIGNOF:   self.advance(); return ast::node1(self.arena, Nk.NODE_EXPR_ALIGNOF, self.parse_paren_or_type(), t.line, t.col);
        case Tt.TOKEN_KW_TRANSMUTE: return self.parse_transmute();

        case Tt.TOKEN_KW_REWRITE:   return self.parse_rewrite();
        case Tt.TOKEN_KW_HANDLE:    return self.parse_handle();
        case Tt.TOKEN_KW_COMPTIME:  return self.parse_meta_block(Nk.NODE_COMPTIME);
        case Tt.TOKEN_KW_RUNTIME:   return self.parse_meta_block(Nk.NODE_RUNTIME);
        case Tt.TOKEN_KW_STAGE:     return self.parse_meta_block(Nk.NODE_STAGE);
        case Tt.TOKEN_KW_META:      return self.parse_meta_block(Nk.NODE_META);
        case Tt.TOKEN_KW_QUOTE:     self.advance(); return ast::node1(self.arena, Nk.NODE_QUOTE, self.parse_prefix(), t.line, t.col);
        case Tt.TOKEN_KW_SPLICE:    return self.parse_call_like(Nk.NODE_SPLICE);
        case Tt.TOKEN_KW_UNQUOTE:   return self.parse_call_like(Nk.NODE_UNQUOTE);
        case Tt.TOKEN_KW_REIFY:     return self.parse_call_like(Nk.NODE_REIFY);
        case Tt.TOKEN_KW_EVAL:      return self.parse_call_like(Nk.NODE_EVAL);
        case Tt.TOKEN_KW_GENERATE:  return self.parse_call_like(Nk.NODE_GENERATE);
        case Tt.TOKEN_KW_LOWER:     return self.parse_call_like(Nk.NODE_LOWER);
        case Tt.TOKEN_KW_PGEN:      return self.parse_pgen();
        case Tt.TOKEN_KW_FIXPOINT:  return self.parse_call_like(Nk.NODE_FIXPOINT);
        case Tt.TOKEN_KW_WITH:      return self.parse_with();
        case Tt.TOKEN_KW_RULE:      return self.parse_named_rule();

        case Tt.TOKEN_KW_FN:
            {
                // fn in expression position: closure if followed by | or (
                Tt fnext = self.peek1().type;
                bool fn_is_closure = (fnext == Tt.TOKEN_PIPE
                                   || fnext == Tt.TOKEN_LPAREN
                                   || fnext == Tt.TOKEN_ARROW
                                   || fnext == Tt.TOKEN_ARROW_ASCII);
                if (fn_is_closure) { return self.parse_closure_expr(); }
                // Named fn in expression: treat as nested fn decl
                return self.parse_fn();
            }

        default:
            // Soft keywords (node, edge, block, graph, lower, region, opcode, etc.)
            // used as plain identifiers in expression position.
            if (self.at_member_name())
            {
                self.advance();
                Node* nd = self.name_from(t, Nk.NODE_IDENT);
                // May be followed by a struct literal: Name { ... }
                if (self.check(Tt.TOKEN_LBRACE))
                {
                    return self.parse_struct_lit(nd);
                }
                return nd;
            }
            self.error("expected an expression");
            self.advance();
            return ast::node0(self.arena, Nk.NODE_INVALID, t.line, t.col);
    }
}

fn Node* effecting(Node* n, ulong eff) @private
{
    ast::node_add_effect(n, eff);
    return n;
}

// ∀ A . body   /   ∃ T . body   — quantifier in expression position.
// Children: [bound-var, body].  `q` is the quantifier token (for location).
fn Node* Parser.parse_quantifier_expr(Parser* self, Nk kind, Tok q)
{
    Scratch s;
    s.reset();

    if (self.check(Tt.TOKEN_TYPEVAR) || self.check(Tt.TOKEN_IDENT))
    {
        Tok v = self.advance();
        s.push(self.name_from(v, Nk.NODE_TYPEVAR));
    }
    else
    {
        self.error("expected a variable after quantifier");
    }

    self.accept(Tt.TOKEN_DOT);
    // The body of a quantifier is a type (e.g. ∀ A . A → A).
    s.push(self.parse_type());
    return self.finish(kind, &s, q.line, q.col);
}

fn Node* Parser.parse_int_lit(Parser* self)
{
    Tok t = self.advance();
    ulong v = parse_int_value(t.start, t.len);
    // Extract type suffix from the literal token: i8/u8/i16/u16/i32/u32/i64/u64/i128/u128/isize/usize
    // Scan past the numeric part to find any suffix.
    char bits = 64;
    bool is_signed = true;
    char* p = t.start;
    usz len = t.len;
    // Skip leading 0x/0b/0o prefix and digits/underscores to find suffix start
    usz si = 0;
    if (len >= 2 && p[0] == '0' && (p[1]=='x'||p[1]=='X'||p[1]=='b'||p[1]=='B'||p[1]=='o'||p[1]=='O')) { si = 2; }
    while (si < len && ((p[si] >= '0' && p[si] <= '9') || (p[si] >= 'a' && p[si] <= 'f')
           || (p[si] >= 'A' && p[si] <= 'F') || p[si] == '_')) { si++; }
    // si now points to suffix (or end)
    if (si < len) {
        char* suf = p + si;
        usz slen = len - si;
        bool u_prefix = (suf[0] == 'u');
        bool i_prefix = (suf[0] == 'i');
        if (u_prefix || i_prefix) {
            is_signed = i_prefix;
            if (slen >= 4 && suf[1]=='1' && suf[2]=='2' && suf[3]=='8') { bits = 128; }
            else if (slen >= 5 && suf[1]=='s' && suf[2]=='i' && suf[3]=='z' && suf[4]=='e') { bits = 64; } // isize/usize = 64 on x86_64
            else if (slen >= 3 && suf[1]=='6' && suf[2]=='4') { bits = 64; }
            else if (slen >= 3 && suf[1]=='3' && suf[2]=='2') { bits = 32; }
            else if (slen >= 3 && suf[1]=='1' && suf[2]=='6') { bits = 16; }
            else if (slen >= 2 && suf[1]=='8')                  { bits = 8; }
        }
    }
    return ast::node_int(self.arena, v, bits, is_signed, t.line, t.col);
}

fn Node* Parser.parse_float_lit(Parser* self)
{
    Tok t = self.advance();
    // Parse the floating-point value from the token text.
    // Handles: 3.14, 1.5e10, 1.5E-3, 3.14f32 (suffix stripped).
    // We use strtod via a temporary null-terminated copy.
    double fval = 0.0;
    char bits = 64;
    bool is_f32 = false;
    // Check for f32/f64 suffix
    if (t.len >= 3) {
        char* end = t.start + t.len;
        if (end[-1] == '2' && end[-2] == '3' && end[-3] == 'f') { is_f32 = true; bits = 32; }
        else if (end[-1] == '4' && end[-2] == '6' && end[-3] == 'f') { bits = 64; }
    }
    // Copy token to null-terminated buffer for strtod
    char[64] buf;
    usz copy_len = (t.len < 63) ? t.len : 63;
    // Strip suffix if present
    usz parse_len = copy_len;
    if (is_f32 && parse_len >= 3) { parse_len -= 3; }
    else if (bits == 64 && parse_len >= 3 && t.start[parse_len-3] == 'f') { parse_len -= 3; }
    for (usz fi = 0; fi < parse_len; fi++) buf[fi] = t.start[fi];
    buf[parse_len] = 0;
    // Parse: use C's strtod
    fval = (double)strtod(&buf[0], null);
    return ast::node_float(self.arena, fval, bits, t.line, t.col);
}

// Minimal integer value decoder for the common bases. Underscores skipped.
// Suffixes (i32, u64, ...) are ignored for the numeric value here.
fn ulong parse_int_value(char* p, usz len) @private
{
    ulong v = 0;

    if (len >= 2 && p[0] == '0' && (p[1] == 'x' || p[1] == 'X'))
    {
        for (usz i = 2; i < len; i++)
        {
            char c = p[i];
            if (c == '_') continue;
            if (c >= '0' && c <= '9') { v = v * 16 + (ulong)(uint)(c - '0'); }
            else if (c >= 'a' && c <= 'f') { v = v * 16 + (ulong)(uint)(c - 'a' + 10); }
            else if (c >= 'A' && c <= 'F') { v = v * 16 + (ulong)(uint)(c - 'A' + 10); }
            else { break; }
        }
        return v;
    }
    if (len >= 2 && p[0] == '0' && (p[1] == 'b' || p[1] == 'B'))
    {
        for (usz i = 2; i < len; i++)
        {
            char c = p[i];
            if (c == '_') continue;
            if (c == '0' || c == '1') { v = v * 2 + (ulong)(uint)(c - '0'); }
            else { break; }
        }
        return v;
    }
    if (len >= 2 && p[0] == '0' && (p[1] == 'o' || p[1] == 'O'))
    {
        for (usz i = 2; i < len; i++)
        {
            char c = p[i];
            if (c == '_') continue;
            if (c >= '0' && c <= '7') { v = v * 8 + (ulong)(uint)(c - '0'); }
            else { break; }
        }
        return v;
    }

    for (usz i = 0; i < len; i++)
    {
        char c = p[i];
        if (c == '_') continue;
        if (c >= '0' && c <= '9') { v = v * 10 + (ulong)(uint)(c - '0'); }
        else { break; }   // hit a type suffix
    }
    return v;
}

fn bool is_hex_digit(char c) @private
{
    if (c >= '0' && c <= '9') return true;
    if (c >= 'a' && c <= 'f') return true;
    if (c >= 'A' && c <= 'F') return true;
    return false;
}

fn uint hex_digit_value(char c) @private
{
    if (c >= '0' && c <= '9') return (uint)(c - '0');
    if (c >= 'a' && c <= 'f') return (uint)(c - 'a' + 10);
    if (c >= 'A' && c <= 'F') return (uint)(c - 'A' + 10);
    return 0;
}

// Decode a TOKEN_LIT_CHAR token's source span (including the surrounding
// single quotes, e.g. 'a' 'x41' '\n' '\x41' '\u{1F600}') into its codepoint.
// Mirrors the escape grammar already VALIDATED (but not decoded) by
// lexer.c3::lex_char. On any malformed input (which the lexer should already
// have flagged as a diagnostic) this returns 0 rather than crashing.
fn uint parse_char_value(char* p, usz len) @private
{
    if (p == null || len < 2 || p[0] != '\'') return 0;
    usz i = 1;                       // skip opening quote
    usz end = len - 1;               // index of closing quote (if well-formed)
    if (end > len || end <= i) return 0;

    if (p[i] != '\\')
    {
        // Plain (non-escaped) character. Decode as UTF-8 if it's a
        // multi-byte sequence; otherwise it's a single ASCII byte.
        uint b0 = (uint)(int)p[i] & 0xFF;
        if ((b0 & 0x80) == 0) return b0;

        // Minimal UTF-8 decode (2/3/4-byte sequences).
        if ((b0 & 0xE0) == 0xC0 && i + 1 < end)
        {
            uint cp = b0 & 0x1F;
            cp = (cp << 6) | ((uint)(int)p[i+1] & 0x3F);
            return cp;
        }
        if ((b0 & 0xF0) == 0xE0 && i + 2 < end)
        {
            uint cp = b0 & 0x0F;
            cp = (cp << 6) | ((uint)(int)p[i+1] & 0x3F);
            cp = (cp << 6) | ((uint)(int)p[i+2] & 0x3F);
            return cp;
        }
        if ((b0 & 0xF8) == 0xF0 && i + 3 < end)
        {
            uint cp = b0 & 0x07;
            cp = (cp << 6) | ((uint)(int)p[i+1] & 0x3F);
            cp = (cp << 6) | ((uint)(int)p[i+2] & 0x3F);
            cp = (cp << 6) | ((uint)(int)p[i+3] & 0x3F);
            return cp;
        }
        return b0;
    }

    // Escape sequence: p[i] == '\\'
    if (i + 1 >= end) return 0;
    char esc = p[i + 1];
    switch (esc)
    {
        case 'n': return (uint)'\n';
        case 'r': return (uint)'\r';
        case 't': return (uint)'\t';
        case '0': return 0;
        case '\\': return (uint)'\\';
        case '\'': return (uint)'\'';
        case '"': return (uint)'"';
        case 'x':
            {
                // \xHH — exactly two hex digits.
                if (i + 3 < len && is_hex_digit(p[i+2]) && is_hex_digit(p[i+3]))
                {
                    return (hex_digit_value(p[i+2]) << 4) | hex_digit_value(p[i+3]);
                }
                return 0;
            }
        case 'u':
            {
                // \u{HHHH...} — one or more hex digits inside braces.
                usz j = i + 2;
                if (j >= len || p[j] != '{') return 0;
                j++;
                uint cp = 0;
                bool saw = false;
                while (j < end && p[j] != '}')
                {
                    if (!is_hex_digit(p[j])) return 0;
                    cp = (cp << 4) | hex_digit_value(p[j]);
                    saw = true;
                    j++;
                }
                return saw ? cp : 0;
            }
        default:
            return 0;
    }
}

// ( ) unit | ( expr ) group | ( e, e, ... ) tuple
fn Node* Parser.parse_paren_expr(Parser* self)
{
    Tok lp = self.advance();   // (

    if (self.accept(Tt.TOKEN_RPAREN))
    {
        return ast::node0(self.arena, Nk.NODE_EXPR_UNIT, lp.line, lp.col);
    }

    Scratch s;
    s.reset();
    s.push(self.parse_expr());

    // ';' separates a parenthesised sequence:  (s = v; k ())  -> a block whose
    // value is the last expression. This is distinct from ',' tuples.
    if (self.check(Tt.TOKEN_SEMI))
    {
        while (self.accept(Tt.TOKEN_SEMI))
        {
            if (self.check(Tt.TOKEN_RPAREN)) break;
            s.push(self.parse_expr());
        }
        self.expect(Tt.TOKEN_RPAREN, "expected ')' to close sequence");
        return self.finish(Nk.NODE_EXPR_BLOCK, &s, lp.line, lp.col);
    }

    bool is_tuple = false;
    while (self.accept(Tt.TOKEN_COMMA))
    {
        is_tuple = true;
        if (self.check(Tt.TOKEN_RPAREN)) break;
        s.push(self.parse_expr());
    }
    self.expect(Tt.TOKEN_RPAREN, "expected ')'");

    if (is_tuple)
    {
        return self.finish(Nk.NODE_EXPR_TUPLE_LIT, &s, lp.line, lp.col);
    }
    Node* only = s.items()[0]; s.reset(); return only;
}

// [ e, e, ... ]   |   [ value ; count ]
// Tensor literal:  [| e, e, ... |]   (rows may nest: [| [|1,2|], [|3,4|] |]).
// Children are the row/element expressions; nesting encodes rank.
fn Node* Parser.parse_tensor_lit(Parser* self)
{
    Tok lb = self.advance();   // [
    self.advance();            // |  (the opening bar)
    Scratch s;
    s.reset();

    self.skip_newlines();
    // Closing is `|]` — a PIPE immediately followed by RBRACK.
    if (!(self.check(Tt.TOKEN_PIPE) && self.peek1().type == Tt.TOKEN_RBRACK))
    {
        s.push(self.parse_expr());
        while (self.accept(Tt.TOKEN_COMMA))
        {
            self.skip_newlines();
            if (self.check(Tt.TOKEN_PIPE) && self.peek1().type == Tt.TOKEN_RBRACK) break;
            s.push(self.parse_expr());
        }
    }
    self.skip_newlines();
    self.expect(Tt.TOKEN_PIPE, "expected '|]' to close tensor literal");
    self.expect(Tt.TOKEN_RBRACK, "expected ']' to close tensor literal");
    return self.finish(Nk.NODE_EXPR_TENSOR_LIT, &s, lb.line, lb.col);
}

fn Node* Parser.parse_array_lit(Parser* self)
{
    Tok lb = self.advance();   // [
    Scratch s;
    s.reset();

    if (!self.check(Tt.TOKEN_RBRACK))
    {
        Node* first = self.parse_expr();
        s.push(first);

        if (self.accept(Tt.TOKEN_SEMI))
        {
            // [value; count] repeat form
            Node* count = self.parse_expr();
            s.push(count);
            self.expect(Tt.TOKEN_RBRACK, "expected ']' to close array");
            Node* node = self.finish(Nk.NODE_EXPR_ARRAY_LIT, &s, lb.line, lb.col);
            return node;
        }

        while (self.accept(Tt.TOKEN_COMMA))
        {
            if (self.check(Tt.TOKEN_RBRACK)) break;
            s.push(self.parse_expr());
        }
    }
    self.expect(Tt.TOKEN_RBRACK, "expected ']' to close array");
    return self.finish(Nk.NODE_EXPR_ARRAY_LIT, &s, lb.line, lb.col);
}

// sizeof/alignof take either (expr) or a bare type.
// Operand of `sizeof` / `alignof`: a TYPE, optionally parenthesised. Both
// `sizeof i32` and `sizeof(i32)` (and `sizeof(*T)`, `sizeof([i32;4])`) name a
// type, never a value — so we parse the inside of the parens as a type.
fn Node* Parser.parse_paren_or_type(Parser* self)
{
    if (self.accept(Tt.TOKEN_LPAREN))
    {
        Node* ty = self.parse_type();
        self.expect(Tt.TOKEN_RPAREN, "expected ')' after type");
        return ty;
    }
    return self.parse_type_prefix();
}

// transmute(expr)
fn Node* Parser.parse_transmute(Parser* self)
{
    Tok kw = self.advance();   // transmute
    self.expect(Tt.TOKEN_LPAREN, "expected '(' after transmute");
    Node* e = self.parse_expr();
    self.expect(Tt.TOKEN_RPAREN, "expected ')' after transmute argument");
    return ast::node1(self.arena, Nk.NODE_EXPR_TRANSMUTE, e, kw.line, kw.col);
}

// keyword(args) style meta operators: splice/unquote/reify/eval/generate/lower
fn Node* Parser.parse_call_like(Parser* self, Nk kind)
{
    Tok kw = self.advance();
    Scratch s;
    s.reset();
    if (self.accept(Tt.TOKEN_LPAREN))
    {
        if (!self.check(Tt.TOKEN_RPAREN))
        {
            s.push(self.parse_expr());
            while (self.accept(Tt.TOKEN_COMMA))
            {
                s.push(self.parse_expr());
            }
        }
        self.expect(Tt.TOKEN_RPAREN, "expected ')'");
    }
    else
    {
        s.push(self.parse_prefix());
    }
    return self.finish(kind, &s, kw.line, kw.col);
}

// ub! "message"
fn Node* Parser.parse_ub_bang(Parser* self)
{
    Tok kw = self.advance();   // ub!
    Scratch s;
    s.reset();
    if (self.check(Tt.TOKEN_LIT_STRING))
    {
        Tok msg = self.advance();
        s.push(ast::node_str(self.arena, Nk.NODE_LIT_STRING, msg.start, msg.len, msg.line, msg.col));
    }
    Node* node = self.finish(Nk.NODE_UB_BANG, &s, kw.line, kw.col);
    ast::node_add_effect(node, ast::EFFECT_UB);
    if (node != null) node.type_annotation = ast::node_bottom(self.arena, kw.line, kw.col);
    return node;
}

// Control flow as expressions (v.md §7)
// if cond <block> (else if cond <block>)* (else <block>)?
// Consume an optional `then` soft keyword (a plain ident whose text is "then").
fn void Parser.accept_soft_then(Parser* self)
{
    if (self.check(Tt.TOKEN_IDENT) && tok_text_eq(self.cur, "then", 4))
    {
        self.advance();
    }
}

fn Node* Parser.parse_if(Parser* self)
{
    Tok kw = self.advance();   // if
    Scratch s;
    s.reset();

    Node* cond = self.parse_expr();
    s.push(cond);

    // SSI: the parser inserts a σ-node split at the condition (v.md §20.3).
    Node* sigma = ast::node1(self.arena, Nk.NODE_SIGMA, cond, kw.line, kw.col);
    s.push(sigma);

    // Optional soft keyword `then` for inline if-expressions:
    //   if a > b then a else b
    // `then` is not a reserved keyword, so the lexer hands it back as an ident.
    self.accept_soft_then();

    Node* then_blk = self.parse_clause_body();
    s.push(then_blk);

    self.skip_newlines();
    if (self.accept(Tt.TOKEN_KW_ELSE))
    {
        if (self.check(Tt.TOKEN_KW_IF))
        {
            Node* elif = self.parse_if();
            s.push(elif);
        }
        else
        {
            Node* else_blk = self.parse_clause_body();
            s.push(else_blk);
        }
    }

    // φ-node merge at the join.
    Node* phi = ast::node0(self.arena, Nk.NODE_PHI, kw.line, kw.col);
    s.push(phi);

    return self.finish(Nk.NODE_EXPR_IF, &s, kw.line, kw.col);
}

// match expr <arms>
fn Node* Parser.parse_match(Parser* self)
{
    Tok kw = self.advance();   // match
    Scratch s;
    s.reset();

    Node* scrutinee = self.parse_expr();
    s.push(scrutinee);
    s.push(ast::node1(self.arena, Nk.NODE_SIGMA, scrutinee, kw.line, kw.col));

    self.skip_newlines();
    bool indented = self.accept(Tt.TOKEN_INDENT);
    self.skip_newlines();

    while (self.check(Tt.TOKEN_PIPE))
    {
        Node* arm = self.parse_match_arm();
        if (arm != null) s.push(arm);
        self.skip_newlines();
    }

    if (indented) self.accept(Tt.TOKEN_DEDENT);

    s.push(ast::node0(self.arena, Nk.NODE_PHI, kw.line, kw.col));
    return self.finish(Nk.NODE_EXPR_MATCH, &s, kw.line, kw.col);
}

// arm ::= '|' pattern (',' guard)? '->' body
fn Node* Parser.parse_match_arm(Parser* self)
{
    Tok bar = self.advance();   // |
    Scratch s;
    s.reset();

    Node* pat = self.parse_pattern();
    s.push(pat);

    if (self.accept(Tt.TOKEN_COMMA))
    {
        Node* guard = self.parse_expr();
        s.push(ast::node1(self.arena, Nk.NODE_PATTERN_GUARD, guard, bar.line, bar.col));
    }

    if (self.accept(Tt.TOKEN_ARROW) || self.accept(Tt.TOKEN_ARROW_ASCII))
    {
        Node* body = self.parse_clause_body();
        s.push(body);
    }
    else
    {
        self.error("expected '->' in match arm");
    }

    return self.finish(Nk.NODE_MATCH_ARM, &s, bar.line, bar.col);
}

fn Node* Parser.parse_while(Parser* self)
{
    Tok kw = self.advance();   // while
    Node* cond = self.parse_expr();
    Node* body = self.parse_clause_body();
    return ast::node2(self.arena, Nk.NODE_EXPR_WHILE, cond, body, kw.line, kw.col);
}

fn Node* Parser.parse_do_while(Parser* self)
{
    Tok kw = self.advance();   // do
    Node* body = self.parse_clause_body();
    self.skip_newlines();
    self.expect(Tt.TOKEN_KW_WHILE, "expected 'while' after do-body");
    Node* cond = self.parse_expr();
    return ast::node2(self.arena, Nk.NODE_EXPR_LOOP_DO, body, cond, kw.line, kw.col);
}

// for ident in range <block>
fn Node* Parser.parse_for(Parser* self)
{
    Tok kw = self.advance();   // for
    Scratch s;
    s.reset();

    Node* binder = self.parse_pattern();
    s.push(binder);

    self.expect(Tt.TOKEN_KW_IN, "expected 'in' in for loop");
    Node* iter = self.parse_expr();
    s.push(iter);

    Node* body = self.parse_clause_body();
    s.push(body);

    return self.finish(Nk.NODE_EXPR_FOR, &s, kw.line, kw.col);
}

// Patterns (v.md §8)
// pattern ::= or_pattern   ('|' alternatives folded into NODE_PATTERN_OR)
fn Node* Parser.parse_pattern(Parser* self)
{
    if (!self.enter())
    {
        Tok t = self.cur;
        if (!self.at_end()) self.advance();
        self.leave();
        return ast::node0(self.arena, Nk.NODE_INVALID, t.line, t.col);
    }
    Node* r = self.parse_pattern_inner();
    self.leave();
    return r;
}

fn Node* Parser.parse_pattern_inner(Parser* self)
{
    Node* first = self.parse_pattern_atom();

    if (self.check(Tt.TOKEN_PIPE))
    {
        Scratch s;
        s.reset();
        s.push(first);
        int line = first != null ? first.line : self.cur.line;
        int col = first != null ? first.col : self.cur.col;
        while (self.accept(Tt.TOKEN_PIPE))
        {
            s.push(self.parse_pattern_atom());
        }
        return self.finish(Nk.NODE_PATTERN_OR, &s, line, col);
    }
    return first;
}

fn Node* Parser.parse_pattern_atom(Parser* self)
{
    Tok t = self.cur;

    switch (t.type)
    {
        case Tt.TOKEN_WILDCARD:
            self.advance();
            return ast::node0(self.arena, Nk.NODE_PATTERN_WILDCARD, t.line, t.col);

        case Tt.TOKEN_LIT_INT:
            {
                self.advance();
                Node* lit = ast::node_int(self.arena, parse_int_value(t.start, t.len), 64, true, t.line, t.col);
                // Check for range pattern:  LIT..LIT  or  LIT..=LIT
                if (self.check(Tt.TOKEN_DOTDOT) || self.check(Tt.TOKEN_DOTDOTEQ))
                {
                    bool inclusive = self.check(Tt.TOKEN_DOTDOTEQ);
                    self.advance();
                    Tok hi_tok = self.cur;
                    Node* hi_lit = null;
                    if (self.check(Tt.TOKEN_LIT_INT))
                    {
                        self.advance();
                        hi_lit = ast::node_int(self.arena, parse_int_value(hi_tok.start, hi_tok.len), 64, true, hi_tok.line, hi_tok.col);
                    }
                    Node* rp = ast::node2(self.arena, Nk.NODE_PATTERN_RANGE, lit, hi_lit, t.line, t.col);
                    if (rp != null && inclusive) rp.flags |= ast::FLAG_RANGE_INCLUSIVE;
                    return rp;
                }
                return ast::node1(self.arena, Nk.NODE_PATTERN_LITERAL, lit, t.line, t.col);
            }

        case Tt.TOKEN_LIT_FLOAT:
            self.advance();
            return ast::node1(self.arena, Nk.NODE_PATTERN_LITERAL,
                ast::node_float(self.arena, 0.0, 64, t.line, t.col), t.line, t.col);

        case Tt.TOKEN_LIT_CHAR:
            self.advance();
            return ast::node1(self.arena, Nk.NODE_PATTERN_LITERAL,
                ast::node_char(self.arena, parse_char_value(t.start, t.len), t.line, t.col), t.line, t.col);

        case Tt.TOKEN_LIT_STRING:
            self.advance();
            return ast::node1(self.arena, Nk.NODE_PATTERN_LITERAL,
                ast::node_str(self.arena, Nk.NODE_LIT_STRING, t.start, t.len, t.line, t.col), t.line, t.col);

        case Tt.TOKEN_LIT_BOOL:
            self.advance();
            return ast::node1(self.arena, Nk.NODE_PATTERN_LITERAL,
                ast::node_bool(self.arena, tok_text_eq(t, "true", 4), t.line, t.col), t.line, t.col);

        case Tt.TOKEN_LIT_NULL:
        case Tt.TOKEN_KW_NULLPTR:
            self.advance();
            return ast::node1(self.arena, Nk.NODE_PATTERN_LITERAL,
                ast::node_null(self.arena, t.line, t.col), t.line, t.col);

        case Tt.TOKEN_IDENT:
            self.advance();
            return ast::node1(self.arena, Nk.NODE_PATTERN_IDENT, self.name_from(t, Nk.NODE_IDENT), t.line, t.col);

        // Soft keywords used as variable names in patterns: node, edge, block, graph, etc.
        // These are IRDL/graph keywords that are extremely common as variable names.
        default:
            if (self.at_member_name())
            {
                self.advance();
                return ast::node1(self.arena, Nk.NODE_PATTERN_IDENT, self.name_from(t, Nk.NODE_IDENT), t.line, t.col);
            }
            self.error("expected a pattern");
            if (!self.at_end()) self.advance();
            return ast::node0(self.arena, Nk.NODE_INVALID, t.line, t.col);

        case Tt.TOKEN_TYPEVAR:
            {
                self.advance();
                Node* tvar_name = self.name_from(t, Nk.NODE_TYPEVAR);
                // Constructor pattern: Some(pat) or Ok(pat) or Err(pat) etc.
                if (self.check(Tt.TOKEN_LPAREN))
                {
                    self.advance();  // consume (
                    Scratch cs;
                    cs.reset();
                    cs.push(tvar_name);
                    while (!self.check(Tt.TOKEN_RPAREN) && !self.check(Tt.TOKEN_EOF))
                    {
                        cs.push(self.parse_pattern());
                        if (self.check(Tt.TOKEN_COMMA)) self.advance();
                    }
                    self.accept(Tt.TOKEN_RPAREN);
                    return self.finish(Nk.NODE_PATTERN_STRUCT, &cs, t.line, t.col);
                }
                return ast::node1(self.arena, Nk.NODE_PATTERN_IDENT, tvar_name, t.line, t.col);
            }

        case Tt.TOKEN_LPAREN:
            return self.parse_tuple_pattern();

        case Tt.TOKEN_LBRACE:
            return self.parse_struct_pattern();
    }
}

fn Node* Parser.parse_tuple_pattern(Parser* self)
{
    Tok lp = self.advance();   // (
    Scratch s;
    s.reset();

    if (self.accept(Tt.TOKEN_RPAREN))
    {
        // () unit pattern
        return ast::node0(self.arena, Nk.NODE_PATTERN_TUPLE, lp.line, lp.col);
    }

    s.push(self.parse_pattern());
    while (self.accept(Tt.TOKEN_COMMA))
    {
        if (self.check(Tt.TOKEN_RPAREN)) break;
        s.push(self.parse_pattern());
    }
    self.expect(Tt.TOKEN_RPAREN, "expected ')' to close tuple pattern");
    return self.finish(Nk.NODE_PATTERN_TUPLE, &s, lp.line, lp.col);
}

// { field (: subpattern)? , ... }
fn Node* Parser.parse_struct_pattern(Parser* self)
{
    Tok lb = self.advance();   // {
    Scratch s;
    s.reset();

    self.skip_newlines();
    if (!self.check(Tt.TOKEN_RBRACE))
    {
        s.push(self.parse_struct_pattern_field());
        while (self.accept(Tt.TOKEN_COMMA))
        {
            self.skip_newlines();
            if (self.check(Tt.TOKEN_RBRACE)) break;
            s.push(self.parse_struct_pattern_field());
        }
    }
    self.skip_newlines();
    self.expect(Tt.TOKEN_RBRACE, "expected '}' to close struct pattern");
    return self.finish(Nk.NODE_PATTERN_STRUCT, &s, lb.line, lb.col);
}

fn Node* Parser.parse_struct_pattern_field(Parser* self)
{
    if (!(self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR)))
    {
        self.error("expected field name in struct pattern");
        self.advance();
        return ast::node0(self.arena, Nk.NODE_INVALID, self.cur.line, self.cur.col);
    }
    Tok name = self.advance();
    Node* nm = self.name_from(name, Nk.NODE_IDENT);

    if (self.accept(Tt.TOKEN_COLON))
    {
        Node* sub = self.parse_pattern();
        return ast::node2(self.arena, Nk.NODE_PATTERN_FIELD, nm, sub, name.line, name.col);
    }
    return ast::node1(self.arena, Nk.NODE_PATTERN_FIELD, nm, name.line, name.col);
}

// Algebraic effects: handlers (v.md §10.3)
// handle computation <arms>   (arms: '| Effect.op args k -> body')
fn Node* Parser.parse_handle(Parser* self)
{
    Tok kw = self.advance();   // handle
    Scratch s;
    s.reset();

    // The computation: either an inline expression, or an indented body.
    self.skip_newlines();
    if (!self.at_block_start() && !self.check(Tt.TOKEN_PIPE))
    {
        Node* comp = self.parse_expr();
        s.push(comp);
    }

    self.skip_newlines();
    bool indented = self.accept(Tt.TOKEN_INDENT);
    self.skip_newlines();

    // Nested handle as the computation (stacked handlers, v.md §10.4)
    if (self.check(Tt.TOKEN_KW_HANDLE))
    {
        s.push(self.parse_handle());
        self.skip_newlines();
    }

    while (self.check(Tt.TOKEN_PIPE))
    {
        Node* arm = self.parse_handler_arm();
        if (arm != null) s.push(arm);
        self.skip_newlines();
    }

    if (indented) self.accept(Tt.TOKEN_DEDENT);

    Node* node = self.finish(Nk.NODE_EFFECT_HANDLE, &s, kw.line, kw.col);
    ast::node_add_effect(node, ast::EFFECT_IO);  // handlers are effectful by nature
    return node;
}

// handler_arm ::= '|' Effect '.' op  binder*  k  '->' body
// e.g.  | IO.write_byte byte k -> (sys_write(byte); k ())
//       | State.get () k       -> k s
//       | Err.raise _ _        -> default_value
// Child layout: [ op-head, binder-pattern*, body ]. The op-head is a
// NODE_EXPR_FIELD (Effect.op) when qualified, else a bare ident. Every binder
// (arguments and the continuation) is parsed as a real pattern.
fn Node* Parser.parse_handler_arm(Parser* self)
{
    Tok bar = self.advance();   // |
    Scratch s;
    s.reset();

    // Operation head: Effect '.' op  (or a bare name).
    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
    {
        Tok id = self.advance();
        Node* head = self.name_from(id, id.type == Tt.TOKEN_TYPEVAR ? Nk.NODE_TYPEVAR : Nk.NODE_IDENT);
        if (self.accept(Tt.TOKEN_DOT))
        {
            if (self.at_member_name())
            {
                Tok op = self.advance();
                head = ast::node2(self.arena, Nk.NODE_EXPR_FIELD, head,
                    self.name_from(op, Nk.NODE_IDENT), id.line, id.col);
            }
            else
            {
                self.error("expected operation name after '.' in handler arm");
            }
        }
        s.push(head);
    }
    else
    {
        self.error("expected effect operation in handler arm");
    }

    // Binder patterns (arguments + the trailing continuation), up to '->'.
    while (!self.check(Tt.TOKEN_ARROW)
        && !self.check(Tt.TOKEN_ARROW_ASCII)
        && !self.check(Tt.TOKEN_NEWLINE)
        && !self.check(Tt.TOKEN_DEDENT)
        && !self.at_end())
    {
        s.push(self.parse_pattern_atom());
    }

    if (self.accept(Tt.TOKEN_ARROW) || self.accept(Tt.TOKEN_ARROW_ASCII))
    {
        Node* body = self.parse_clause_body();
        s.push(body);
    }
    else
    {
        self.error("expected '->' in handler arm");
    }

    return self.finish(Nk.NODE_HANDLER_ARM, &s, bar.line, bar.col);
}

// Term rewriting (v.md §11)
// rewrite <arms>   (arms: '| lhs ↦ rhs' or '| lhs, guard ↦ rhs')
fn Node* Parser.parse_rewrite(Parser* self)
{
    Tok kw = self.advance();   // rewrite
    Scratch s;
    s.reset();

    self.skip_newlines();
    bool indented = self.accept(Tt.TOKEN_INDENT);
    self.skip_newlines();

    while (self.check(Tt.TOKEN_PIPE))
    {
        Node* rule = self.parse_rewrite_rule();
        if (rule != null) s.push(rule);
        self.skip_newlines();
    }

    if (indented) self.accept(Tt.TOKEN_DEDENT);
    return self.finish(Nk.NODE_REWRITE, &s, kw.line, kw.col);
}

// rule ::= '|' expr (',' guard)? '↦' expr
fn Node* Parser.parse_rewrite_rule(Parser* self)
{
    Tok bar = self.advance();   // |
    Scratch s;
    s.reset();

    Node* lhs = self.parse_expr();
    s.push(lhs);

    if (self.accept(Tt.TOKEN_COMMA))
    {
        Node* guard = self.parse_expr();
        s.push(ast::node1(self.arena, Nk.NODE_PATTERN_GUARD, guard, bar.line, bar.col));
    }

    self.expect(Tt.TOKEN_MAPSTO, "expected '↦' in rewrite rule");
    Node* rhs = self.parse_expr();
    s.push(rhs);

    return self.finish(Nk.NODE_REWRITE_RULE, &s, bar.line, bar.col);
}

// Pattern Generation Language (v.md §12)
// pgen name<Generics>? -> [bindings] where [conditions] ↦ action
fn Node* Parser.parse_pgen(Parser* self)
{
    Tok kw = self.advance();   // pgen
    Scratch s;
    s.reset();

    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
    {
        Tok name = self.advance();
        s.push(self.name_from(name, Nk.NODE_IDENT));
    }

    if (self.check(Tt.TOKEN_LT))
    {
        s.push(self.parse_generics());
    }

    // Arrow into the body (→ in the spec).
    self.skip_newlines();
    self.accept(Tt.TOKEN_ARROW);
    self.accept(Tt.TOKEN_ARROW_ASCII);
    self.skip_newlines();
    bool indented = self.accept(Tt.TOKEN_INDENT);
    self.skip_newlines();

    // [bindings : Types]
    if (self.check(Tt.TOKEN_LBRACK))
    {
        s.push(self.parse_bracket_group());
    }

    self.skip_newlines();

    // where [conditions]
    if (self.accept(Tt.TOKEN_KW_WHERE))
    {
        self.skip_newlines();
        if (self.check(Tt.TOKEN_LBRACK))
        {
            Node* conds = self.parse_bracket_group();
            s.push(ast::node1(self.arena, Nk.NODE_WHERE_CLAUSE, conds, kw.line, kw.col));
        }
    }

    self.skip_newlines();

    // ↦ action
    if (self.accept(Tt.TOKEN_MAPSTO))
    {
        Node* action = self.parse_clause_body();
        s.push(action);
    }

    if (indented) self.accept(Tt.TOKEN_DEDENT);
    return self.finish(Nk.NODE_PGEN, &s, kw.line, kw.col);
}

// A bracket group [a : T, b, c] used by PGL binding lists and IRDL rules.
// Each entry is a binding `expr : Type` (-> NODE_PARAM) or a bare expression.
// Layout is suppressed inside [] by the lexer, so entries may span lines.
fn Node* Parser.parse_bracket_group(Parser* self)
{
    Tok lb = self.advance();   // [
    Scratch s;
    s.reset();

    if (!self.check(Tt.TOKEN_RBRACK))
    {
        s.push(self.parse_pgen_binding());
        while (self.accept(Tt.TOKEN_COMMA))
        {
            if (self.check(Tt.TOKEN_RBRACK)) break;
            s.push(self.parse_pgen_binding());
        }
    }
    self.expect(Tt.TOKEN_RBRACK, "expected ']' to close bracket group");
    return self.finish(Nk.NODE_EXPR_ARRAY_LIT, &s, lb.line, lb.col);
}

// binding ::= expr (: Type)?    (also matches the where-condition form)
fn Node* Parser.parse_pgen_binding(Parser* self)
{
    int line = self.cur.line;
    int col = self.cur.col;

    // Rest / spread binder:  `..name`  — binds the remaining (variadic) args.
    // Used by flexible/untyped IRDL opcodes: `[a : i32, ..rest] ↦ ...`.
    if (self.accept(Tt.TOKEN_DOTDOT))
    {
        Node* nm = null;
        if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
        {
            Tok n = self.advance();
            nm = self.name_from(n, Nk.NODE_IDENT);
        }
        return ast::node1(self.arena, Nk.NODE_EXPR_RANGE, nm, line, col);
    }

    Node* e = self.parse_expr();
    if (self.accept(Tt.TOKEN_COLON))
    {
        Node* ty = self.parse_type();
        return ast::node2(self.arena, Nk.NODE_PARAM, e, ty, line, col);
    }
    return e;
}

// pattern NAME = expr     (named pattern declaration)
fn Node* Parser.parse_pattern_decl(Parser* self)
{
    Tok kw = self.advance();   // pattern
    Scratch s;
    s.reset();

    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
    {
        Tok name = self.advance();
        s.push(self.name_from(name, Nk.NODE_IDENT));
    }
    if (self.accept(Tt.TOKEN_EQ))
    {
        s.push(self.parse_clause_body());
    }
    return self.finish(Nk.NODE_PATTERN_DECL, &s, kw.line, kw.col);
}

// meta block: comptime / runtime / stage / meta  followed by a block or expr
fn Node* Parser.parse_meta_block(Parser* self, Nk kind)
{
    Tok kw = self.advance();
    Node* body = self.parse_clause_body();
    return ast::node1(self.arena, kind, body, kw.line, kw.col);
}

// `unsafe`/`unchecked` introduce a region carrying a safety relaxation. Both
// accept either an indented block (`unsafe\n  <stmts>`) or a single inline
// expression (`unsafe expr`). `unsafe` additionally carries the Unsafe effect.
fn Node* Parser.parse_safety_block(Parser* self, Nk kind)
{
    Tok kw = self.advance();   // unsafe / unchecked
    Node* body = self.parse_clause_body();
    Node* n = ast::node1(self.arena, kind, body, kw.line, kw.col);
    if (n != null)
    {
        if (kind == Nk.NODE_EXPR_UNSAFE) ast::node_add_effect(n, ast::EFFECT_UNSAFE);
        if (kind == Nk.NODE_EXPR_UNCHECKED) n.flags |= ast::FLAG_UNCHECKED;
    }
    return n;
}

// with handler_expr <block>   — install a handler/resource over a scope.
// Children: [handler-expr, body-block].
fn Node* Parser.parse_with(Parser* self)
{
    Tok kw = self.advance();   // with
    Scratch s;
    s.reset();

    // The handler/resource expression on the same logical line.
    if (!self.at_block_start()
        && !self.check(Tt.TOKEN_NEWLINE)
        && !self.check(Tt.TOKEN_DEDENT)
        && !self.at_end())
    {
        s.push(self.parse_expr());
    }

    // The governed body: an indented block or an inline expression.
    Node* body = self.parse_clause_body();
    if (body != null) s.push(body);

    return self.finish(Nk.NODE_EFFECT_WITH, &s, kw.line, kw.col);
}

// rule NAME = lhs ↦ rhs   — a single first-class named rewrite rule.
// Children: [name, lhs, (guard)?, rhs].
fn Node* Parser.parse_named_rule(Parser* self)
{
    Tok kw = self.advance();   // rule
    Scratch s;
    s.reset();

    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
    {
        Tok name = self.advance();
        s.push(self.name_from(name, Nk.NODE_IDENT));
    }
    else
    {
        self.error("expected name after 'rule'");
    }

    self.expect(Tt.TOKEN_EQ, "expected '=' in rule declaration");

    Node* lhs = self.parse_expr();
    s.push(lhs);

    if (self.accept(Tt.TOKEN_COMMA))
    {
        Node* guard = self.parse_expr();
        s.push(ast::node1(self.arena, Nk.NODE_PATTERN_GUARD, guard, kw.line, kw.col));
    }

    self.expect(Tt.TOKEN_MAPSTO, "expected '↦' in rule declaration");
    Node* rhs = self.parse_expr();
    s.push(rhs);

    return self.finish(Nk.NODE_REWRITE_RULE, &s, kw.line, kw.col);
}

// IRDL — IR Dialect Language (v.md §14)
// dialect NAME <indented opcode/region/... decls>
fn Node* Parser.parse_dialect(Parser* self)
{
    Tok kw = self.advance();   // dialect
    Scratch s;
    s.reset();

    if (self.check(Tt.TOKEN_TYPEVAR) || self.check(Tt.TOKEN_IDENT))
    {
        Tok name = self.advance();
        s.push(self.name_from(name, Nk.NODE_TYPEVAR));
    }

    self.skip_newlines();
    if (self.at_block_start())
    {
        Scratch body;
        body.reset();
        int line = self.cur.line;
        int col = self.cur.col;
        self.advance();   // INDENT
        self.skip_newlines();
        while (!self.check(Tt.TOKEN_DEDENT) && !self.at_end())
        {
            Node* d = self.parse_irdl_member();
            if (d != null) body.push(d);
            self.panicking = false;
            self.skip_newlines();
            if (d == null && !self.check(Tt.TOKEN_DEDENT) && !self.at_end()) self.advance();
        }
        self.accept(Tt.TOKEN_DEDENT);
        s.push(self.finish(Nk.NODE_EXPR_BLOCK, &body, line, col));
    }

    return self.finish(Nk.NODE_DIALECT, &s, kw.line, kw.col);
}

// opcode NAME | region NAME | block NAME | node NAME | edge NAME | hyperedge NAME | graph NAME
fn Node* Parser.parse_irdl_member(Parser* self)
{
    Tok t = self.cur;
    Nk kind;

    switch (t.type)
    {
        case Tt.TOKEN_KW_OPCODE:    kind = Nk.NODE_OPCODE;
        case Tt.TOKEN_KW_REGION:    kind = Nk.NODE_REGION;
        case Tt.TOKEN_KW_BLOCK:     kind = Nk.NODE_BLOCK_IR;
        case Tt.TOKEN_KW_NODE:      kind = Nk.NODE_NODE_DECL;
        case Tt.TOKEN_KW_EDGE:      kind = Nk.NODE_EDGE_DECL;
        case Tt.TOKEN_KW_HYPEREDGE: kind = Nk.NODE_HYPEREDGE_DECL;
        case Tt.TOKEN_KW_GRAPH:     kind = Nk.NODE_GRAPH;
        default:
            // Unknown member: parse as a statement so we still consume it.
            return self.parse_stmt();
    }

    self.advance();   // the member keyword
    Scratch s;
    s.reset();
    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
    {
        Tok name = self.advance();
        s.push(self.name_from(name, Nk.NODE_IDENT));
    }

    // edge / hyperedge connect named endpoints:  edge from to   /
    // hyperedge a b c — consume the remaining operand names on the line so they
    // are recorded (and resolved as references to existing node names).
    if (kind == Nk.NODE_EDGE_DECL || kind == Nk.NODE_HYPEREDGE_DECL)
    {
        while (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
        {
            Tok ep = self.advance();
            s.push(self.name_from(ep, Nk.NODE_IDENT));
        }
    }

    // Optional opcode SIGNATURE:  opcode gadd : (i32, i32) -> i32
    // The type's parameter/result kinds are validated against uses (IRDL §c).
    if (kind == Nk.NODE_OPCODE && self.accept(Tt.TOKEN_COLON))
    {
        s.push(self.parse_type());
    }

    // Optional REGION / BLOCK body:  region body <indented ops...>
    // A region groups nested IRDL members (its own opcodes/blocks).
    if ((kind == Nk.NODE_REGION || kind == Nk.NODE_BLOCK_IR || kind == Nk.NODE_GRAPH))
    {
        self.skip_newlines();
        if (self.at_block_start())
        {
            Scratch body;
            body.reset();
            int bline = self.cur.line;
            int bcol = self.cur.col;
            self.advance();   // INDENT
            self.skip_newlines();
            while (!self.check(Tt.TOKEN_DEDENT) && !self.at_end())
            {
                Node* m = self.parse_irdl_member();
                if (m != null) body.push(m);
                self.panicking = false;
                self.skip_newlines();
                if (m == null && !self.check(Tt.TOKEN_DEDENT) && !self.at_end()) self.advance();
            }
            self.accept(Tt.TOKEN_DEDENT);
            s.push(self.finish(Nk.NODE_EXPR_BLOCK, &body, bline, bcol));
        }
    }

    return self.finish(kind, &s, t.line, t.col);
}

// irdl <indented lowering rules>   (rules: 'Dialect.op [binds] ↦ action')
fn Node* Parser.parse_irdl(Parser* self)
{
    Tok kw = self.advance();   // irdl
    Scratch s;
    s.reset();

    self.skip_newlines();
    bool indented = self.accept(Tt.TOKEN_INDENT);
    self.skip_newlines();

    while (!self.check(Tt.TOKEN_DEDENT) && !self.at_end())
    {
        Node* rule = self.parse_irdl_rule();
        if (rule != null) s.push(rule);
        self.panicking = false;
        self.skip_newlines();
        if (rule == null && !self.check(Tt.TOKEN_DEDENT) && !self.at_end()) self.advance();
    }

    if (indented) self.accept(Tt.TOKEN_DEDENT);
    return self.finish(Nk.NODE_IRDL, &s, kw.line, kw.col);
}

// irdl rule ::= dotted_path [binding (',' binding)*] ↦ action
//   e.g.  MyDialect.add_i32 [a : i32, b : i32] ↦ emit_asm("addl ...")
// Children: [ head-path, binding-group?, action ].
fn Node* Parser.parse_irdl_rule(Parser* self)
{
    int line = self.cur.line;
    int col = self.cur.col;
    Scratch s;
    s.reset();

    // Head: Dialect.opcode (a dotted path), built explicitly so the following
    // '[' is treated as a binding group rather than an index expression.
    Node* head = self.parse_dotted_path();
    s.push(head);

    // Optional [binding : Type, ...] group (PGL-style binding list).
    if (self.check(Tt.TOKEN_LBRACK))
    {
        s.push(self.parse_bracket_group());
    }

    // Optional guard:  Dialect.op [bindings], <guard-expr> ↦ action
    // Enables conditional / optimizing lowering rules (e.g. fold when b == 0).
    if (self.accept(Tt.TOKEN_COMMA))
    {
        Node* guard = self.parse_expr();
        s.push(ast::node1(self.arena, Nk.NODE_PATTERN_GUARD, guard, line, col));
    }

    self.expect(Tt.TOKEN_MAPSTO, "expected '↦' in irdl lowering rule");
    Node* action = self.parse_clause_body();
    s.push(action);

    return self.finish(Nk.NODE_LOWER, &s, line, col);
}

// A dotted path used as an opcode reference:  Name ('.' Name)*
fn Node* Parser.parse_dotted_path(Parser* self)
{
    int line = self.cur.line;
    int col = self.cur.col;

    Node* head;
    if (self.check(Tt.TOKEN_IDENT) || self.check(Tt.TOKEN_TYPEVAR))
    {
        Tok first = self.advance();
        head = self.name_from(first, first.type == Tt.TOKEN_TYPEVAR ? Nk.NODE_TYPEVAR : Nk.NODE_IDENT);
    }
    else
    {
        self.error("expected an opcode path");
        return ast::node0(self.arena, Nk.NODE_INVALID, line, col);
    }

    while (self.accept(Tt.TOKEN_DOT))
    {
        if (self.at_member_name())
        {
            Tok seg = self.advance();
            head = ast::node2(self.arena, Nk.NODE_EXPR_FIELD, head,
                self.name_from(seg, Nk.NODE_IDENT), line, col);
        }
        else
        {
            self.error("expected name after '.' in opcode path");
            break;
        }
    }
    return head;
}

fn Node*[2] make2(Node* a, Node* b) @private
{
    Node*[2] buf;
    buf[0] = a;
    buf[1] = b;
    return buf;
}
