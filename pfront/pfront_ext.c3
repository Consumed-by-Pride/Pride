// ============================================================================
// pfront_ext.c3 — Pride front-end: extended surface + analyses (part 5)
// ----------------------------------------------------------------------------
// Everything here operates on the AST that pfront_parse builds and
// pfront_resolve binds. It is split out so the core parser stays readable.
//
//   1. Effect surface      — perform / resume / handler sugar
//   2. Inline assembly     — asm blocks with operand constraints
//   3. Metaprogramming     — macro / rewrite / pgen / dialect declarations
//   4. Effect inference    — propagate the EFF_* lattice bottom-up
//   5. Reachability + lint — unused bindings, dead code, unreachable arms
//   6. Exhaustiveness      — match/clause coverage over enum variants
//   7. Statistics          — the numbers the driver reports
// ============================================================================

module pfront_ext;

import pfront_lex;
import pfront_core;
import pfront_parse;

alias Tk    = pfront_lex::TokenType;
alias Tok   = pfront_lex::Token;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;
alias Parser = pfront_parse::Parser;

extern fn int printf(char* fmt, ...);

// Does this token begin a top-level declaration? Used to terminate un-braced
// theory blocks whose closing DEDENT has already been consumed.
fn bool starts_declaration(Tk t)
{
    switch (t)
    {
        case TOKEN_KW_FN:
        case TOKEN_KW_STRUCT:
        case TOKEN_KW_UNION:
        case TOKEN_KW_ENUM:
        case TOKEN_KW_TYPE:
        case TOKEN_KW_NEWTYPE:
        case TOKEN_KW_EFFECT:
        case TOKEN_KW_INTERFACE:
        case TOKEN_KW_IMPL:
        case TOKEN_KW_EXTERN:
        case TOKEN_KW_USE:
        case TOKEN_KW_MOD:
        case TOKEN_KW_CONST:
        case TOKEN_KW_STATIC:
        case TOKEN_KW_MACRO:
        case TOKEN_KW_REWRITE:
        case TOKEN_KW_DIALECT:
        case TOKEN_KW_PGEN:
        case TOKEN_KW_IRDL:
            return true;
        default:
            return false;
    }
}

// ════════════════════════════════════════════════════════════════════════════
// 1. EFFECT SURFACE
// ════════════════════════════════════════════════════════════════════════════

// `perform` and `resume` are lexed as ordinary identifiers, so they are
// recognised contextually: `perform` followed by a path, `resume` followed by
// `(` or an expression. Treating them as keywords in the lexer would break
// every program that uses either word as a variable.
fn bool Parser.at_perform(Parser* p)
{
    if (!p.check(Tk.TOKEN_IDENT)) { return false; }
    Tok t = p.cur();
    if (t.len != 7) { return false; }
    if (t.start[0] != 'p' || t.start[1] != 'e' || t.start[2] != 'r') { return false; }
    Tk nx = p.peek(1).type;
    return nx == Tk.TOKEN_IDENT || nx == Tk.TOKEN_TYPEVAR;
}

fn bool Parser.at_resume(Parser* p)
{
    if (!p.check(Tk.TOKEN_IDENT)) { return false; }
    Tok t = p.cur();
    if (t.len != 6) { return false; }
    if (t.start[0] != 'r' || t.start[1] != 'e' || t.start[2] != 's') { return false; }
    if (t.start[3] != 'u' || t.start[4] != 'm' || t.start[5] != 'e') { return false; }
    // Continuations are invoked by JUXTAPOSITION, not just by call syntax:
    // v.md §10.3 — "Continuations resume by juxtaposition application: `k v`".
    // So `resume 2` and `resume x` are as valid as `resume(2)`, and the
    // stdlib writes the juxtaposed form 4x more often. Requiring '(' left
    // `resume v` parsed as a bare identifier, which then failed to resolve.
    //
    // Only a token that can BEGIN an expression counts. Anything else means
    // `resume` is being used as an ordinary variable name, which the
    // contextual treatment exists to allow.
    Tk nx = p.peek(1).type;
    return nx == Tk.TOKEN_LPAREN
        || nx == Tk.TOKEN_IDENT
        || nx == Tk.TOKEN_TYPEVAR
        || nx == Tk.TOKEN_LIT_INT
        || nx == Tk.TOKEN_LIT_FLOAT
        || nx == Tk.TOKEN_LIT_BOOL
        || nx == Tk.TOKEN_LIT_CHAR
        || nx == Tk.TOKEN_LIT_STRING
        || nx == Tk.TOKEN_LIT_NULL
        || nx == Tk.TOKEN_KW_SELF
        || nx == Tk.TOKEN_LBRACK;
}

// `perform Effect.op(a, b)` — invoke an algebraic effect operation.
fn Node* Parser.parse_perform(Parser* p)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_EXPR_PERFORM, t);
    n.effects = n.effects | pfront_core::EFF_IO;
    Node* path = p.parse_module_path();
    p.add(n, path);
    if (path != null && path.child_count > 0)
    {
        n.name_id = path.children[path.child_count - 1].name_id;
    }
    if (p.accept(Tk.TOKEN_LPAREN))
    {
        while (!p.check(Tk.TOKEN_RPAREN) && !p.at_end())
        {
            p.add(n, p.parse_expr());
            if (!p.accept(Tk.TOKEN_COMMA)) { break; }
        }
        p.expect(Tk.TOKEN_RPAREN, 1200, "expected ')' to close perform arguments");
    }
    return n;
}

// `resume(v)` / `resume v` — continue a captured continuation.
fn Node* Parser.parse_resume(Parser* p)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_EXPR_RESUME, t);
    n.effects = n.effects | pfront_core::EFF_IO;
    if (p.accept(Tk.TOKEN_LPAREN))
    {
        if (!p.check(Tk.TOKEN_RPAREN)) { p.add(n, p.parse_expr()); }
        p.expect(Tk.TOKEN_RPAREN, 1201, "expected ')' after resume value");
        return n;
    }
    if (pfront_parse::tok_starts_expr(p.ct())) { p.add(n, p.parse_expr()); }
    return n;
}

// ════════════════════════════════════════════════════════════════════════════
// 2. INLINE ASSEMBLY
// ════════════════════════════════════════════════════════════════════════════
// asm { "mov rax, 1" : "=r"(out) : "r"(in) : "memory" }
fn Node* Parser.parse_asm(Parser* p)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_EXPR_ASM, t);
    n.effects = n.effects | pfront_core::EFF_UNSAFE | pfront_core::EFF_IO;

    // Optional qualifiers: asm volatile / asm intel
    while (p.check(Tk.TOKEN_IDENT))
    {
        Tok q = p.cur();
        if (q.len == 8 && q.start[0] == 'v') { p.advance(); n.p.aux = n.p.aux | 1; continue; }
        if (q.len == 5 && q.start[0] == 'i') { p.advance(); n.p.aux = n.p.aux | 2; continue; }
        break;
    }

    bool braced = p.accept(Tk.TOKEN_LBRACE);
    p.skip_layout();

    // Template strings.
    while (p.check(Tk.TOKEN_LIT_STRING))
    {
        p.add(n, p.parse_literal());
        p.skip_layout();
    }

    // Up to three colon-separated operand groups: outputs, inputs, clobbers.
    int group = 0;
    while (p.check(Tk.TOKEN_COLON) && group < 3)
    {
        p.advance();
        group = group + 1;
        p.skip_layout();
        while (!p.check(Tk.TOKEN_COLON) && !p.check(Tk.TOKEN_RBRACE)
            && !p.at_end() && !p.check(Tk.TOKEN_NEWLINE))
        {
            if (p.check(Tk.TOKEN_LIT_STRING))
            {
                Node* cons = p.parse_literal();
                cons.p.aux = group;
                p.add(n, cons);
                if (p.accept(Tk.TOKEN_LPAREN))
                {
                    p.add(n, p.parse_expr());
                    p.expect(Tk.TOKEN_RPAREN, 1210, "expected ')' after asm operand");
                }
            }
            else { break; }
            if (!p.accept(Tk.TOKEN_COMMA)) { break; }
            p.skip_layout();
        }
        p.skip_layout();
    }
    if (braced)
    {
        p.skip_layout();
        p.expect(Tk.TOKEN_RBRACE, 1211, "expected '}' to close asm block");
    }
    return n;
}

// ════════════════════════════════════════════════════════════════════════════
// 3. METAPROGRAMMING DECLARATIONS
// ════════════════════════════════════════════════════════════════════════════

// macro name(args) => expansion
fn Node* Parser.parse_macro_decl(Parser* p)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_DECL_FN, t);
    n.flags = n.flags | pfront_core::NF_SYNTHETIC;
    Tok nm = p.cur();
    if (pfront_parse::tok_is_member_name(nm.type))
    {
        p.advance();
        n.name_id = p.interner.intern(nm.start, nm.len);
        n.p.sptr = nm.start;
        n.p.slen = nm.len;
    }
    else
    {
        p.err(1220, "expected a macro name");
        return n;
    }
    if (p.accept(Tk.TOKEN_LPAREN))
    {
        while (!p.check(Tk.TOKEN_RPAREN) && !p.at_end())
        {
            p.add(n, p.parse_param());
            if (!p.accept(Tk.TOKEN_COMMA)) { break; }
        }
        p.expect(Tk.TOKEN_RPAREN, 1221, "expected ')' to close macro parameters");
    }
    if (p.accept(Tk.TOKEN_FATARROW) || p.accept(Tk.TOKEN_EQ))
    {
        p.add(n, p.parse_block_or_expr());
    }
    else
    {
        p.skip_newlines();
        if (p.check(Tk.TOKEN_INDENT) || p.check(Tk.TOKEN_LBRACE))
        {
            p.add(n, p.parse_block_or_expr());
        }
    }
    return n;
}

// rewrite { lhs ↦ rhs, ... }
fn Node* Parser.parse_rewrite_decl(Parser* p)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_DECL_FN, t);
    n.flags = n.flags | pfront_core::NF_SYNTHETIC;
    if (pfront_parse::tok_is_member_name(p.ct()))
    {
        Tok nm = p.advance();
        n.name_id = p.interner.intern(nm.start, nm.len);
        n.p.sptr = nm.start;
        n.p.slen = nm.len;
    }
    p.skip_newlines();
    bool braced = p.accept(Tk.TOKEN_LBRACE);
    bool indented = false;
    if (!braced) { indented = p.accept(Tk.TOKEN_INDENT); }
    p.skip_layout();
    while (!p.at_end())
    {
        if (braced && p.check(Tk.TOKEN_RBRACE)) { break; }
        if (indented && p.check(Tk.TOKEN_DEDENT)) { break; }
        if (!braced && !indented) { break; }
        // Rules may be written `| lhs -> rhs` (matching clause syntax) or bare
        // `lhs ↦ rhs`. Accept both; the leading bar is purely visual.
        p.accept(Tk.TOKEN_PIPE);
        if (p.check(Tk.TOKEN_RBRACE) || p.check(Tk.TOKEN_DEDENT) || p.at_end()) { break; }
        // A declaration keyword ends the block: an un-braced `rewrite` is
        // closed by dedent, and if that DEDENT was already consumed the next
        // `fn`/`struct`/... would otherwise be swallowed as a rule.
        if (starts_declaration(p.ct())) { break; }
        bool sv_bar = p.in_fn_sig;
        p.in_fn_sig = true;
        Node* lhs = p.parse_expr();
        p.in_fn_sig = sv_bar;
        if (p.accept(Tk.TOKEN_MAPSTO) || p.accept(Tk.TOKEN_ARROW)
         || p.accept(Tk.TOKEN_ARROW_ASCII) || p.accept(Tk.TOKEN_FATARROW))
        {
            Node* rhs = p.parse_arm_body();
            Node* rule = p.mk(Nk.N_CLAUSE, lhs == null ? 0 : lhs.line,
                                            lhs == null ? 0 : lhs.col);
            p.add(rule, lhs);
            p.add(rule, rhs);
            p.add(n, rule);
        }
        else { p.add(n, lhs); }
        p.accept(Tk.TOKEN_COMMA);
        p.skip_layout();
    }
    if (indented) { while (p.accept(Tk.TOKEN_DEDENT)) {} }
    if (braced) { p.expect(Tk.TOKEN_RBRACE, 1230, "expected '}' to close rewrite block"); }
    return n;
}

// `pgen name where [pattern] ↦ action` — a pattern-generation clause set that
// theory_irdl compiles into one decision tree.
fn Node* Parser.parse_pgen_decl(Parser* p)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_DECL_FN, t);
    n.flags = n.flags | pfront_core::NF_SYNTHETIC;
    n.p.aux = 2;   // marks a pgen rather than a rewrite block
    if (pfront_parse::tok_is_member_name(p.ct()))
    {
        Tok nm = p.advance();
        n.name_id = p.interner.intern(nm.start, nm.len);
        n.p.sptr = nm.start;
        n.p.slen = nm.len;
    }
    p.parse_typarams(n);
    p.skip_newlines();
    bool braced = p.accept(Tk.TOKEN_LBRACE);
    bool indented = false;
    if (!braced) { indented = p.accept(Tk.TOKEN_INDENT); }
    p.skip_layout();
    while (!p.at_end())
    {
        if (braced && p.check(Tk.TOKEN_RBRACE)) { break; }
        if (indented && p.check(Tk.TOKEN_DEDENT)) { break; }
        if (!braced && !indented) { break; }
        p.accept(Tk.TOKEN_KW_WHERE);
        p.accept(Tk.TOKEN_PIPE);
        Node* pat = p.parse_pattern();
        Node* rule = p.mk(Nk.N_CLAUSE, pat == null ? t.line : pat.line,
                                        pat == null ? t.col : pat.col);
        p.add(rule, pat);
        if (p.accept(Tk.TOKEN_MAPSTO) || p.accept(Tk.TOKEN_ARROW)
         || p.accept(Tk.TOKEN_ARROW_ASCII) || p.accept(Tk.TOKEN_FATARROW))
        {
            p.add(rule, p.parse_arm_body());
        }
        p.add(n, rule);
        p.accept(Tk.TOKEN_COMMA);
        p.skip_layout();
    }
    if (indented) { while (p.accept(Tk.TOKEN_DEDENT)) {} }
    if (braced) { p.expect(Tk.TOKEN_RBRACE, 1260, "expected '}' to close pgen"); }
    return n;
}

// `irdl` block: lowering rules of the form `Dialect.op [a, b] ↦ action`.
fn Node* Parser.parse_irdl_decl(Parser* p)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_DECL_INTERFACE, t);
    n.flags = n.flags | pfront_core::NF_SYNTHETIC;
    n.p.aux = 3;   // marks an irdl lowering block
    p.skip_newlines();
    bool braced = p.accept(Tk.TOKEN_LBRACE);
    bool indented = false;
    if (!braced) { indented = p.accept(Tk.TOKEN_INDENT); }
    p.skip_layout();
    while (!p.at_end())
    {
        if (braced && p.check(Tk.TOKEN_RBRACE)) { break; }
        if (indented && p.check(Tk.TOKEN_DEDENT)) { break; }
        if (!braced && !indented) { break; }
        if (!pfront_parse::tok_is_member_name(p.ct())) { break; }
        Node* head = p.parse_module_path();
        Node* rule = p.mk(Nk.N_CLAUSE, head == null ? t.line : head.line,
                                        head == null ? t.col : head.col);
        p.add(rule, head);
        if (p.check(Tk.TOKEN_LBRACK))
        {
            p.advance();
            Node* binds = p.mk_at(Nk.N_EXPR_ARRAY, t);
            while (!p.check(Tk.TOKEN_RBRACK) && !p.at_end())
            {
                Tok b = p.cur();
                if (!pfront_parse::tok_is_member_name(b.type)) { break; }
                p.advance();
                Node* bn = p.mk_at(Nk.N_EXPR_IDENT, b);
                bn.name_id = p.interner.intern(b.start, b.len);
                bn.p.sptr = b.start;
                bn.p.slen = b.len;
                p.add(binds, bn);
                if (!p.accept(Tk.TOKEN_COMMA)) { break; }
            }
            p.expect(Tk.TOKEN_RBRACK, 1261, "expected ']' after IRDL operand list");
            p.add(rule, binds);
        }
        if (p.accept(Tk.TOKEN_MAPSTO) || p.accept(Tk.TOKEN_ARROW)
         || p.accept(Tk.TOKEN_ARROW_ASCII))
        {
            p.add(rule, p.parse_arm_body());
        }
        p.add(n, rule);
        p.skip_layout();
    }
    if (indented) { while (p.accept(Tk.TOKEN_DEDENT)) {} }
    if (braced) { p.expect(Tk.TOKEN_RBRACE, 1262, "expected '}' to close irdl block"); }
    return n;
}

// dialect Name { opcode ... }
fn Node* Parser.parse_dialect_decl(Parser* p)
{
    Tok t = p.advance();
    Node* n = p.mk_at(Nk.N_DECL_INTERFACE, t);
    n.flags = n.flags | pfront_core::NF_SYNTHETIC;
    if (pfront_parse::tok_is_member_name(p.ct()))
    {
        Tok nm = p.advance();
        n.name_id = p.interner.intern(nm.start, nm.len);
        n.p.sptr = nm.start;
        n.p.slen = nm.len;
    }
    p.skip_newlines();
    bool braced = p.accept(Tk.TOKEN_LBRACE);
    bool indented = false;
    if (!braced) { indented = p.accept(Tk.TOKEN_INDENT); }
    p.skip_layout();
    while (!p.at_end())
    {
        if (braced && p.check(Tk.TOKEN_RBRACE)) { break; }
        if (indented && p.check(Tk.TOKEN_DEDENT)) { break; }
        if (!braced && !indented) { break; }
        // v.md 19 lists the IRDL vocabulary as
        //   `irdl dialect opcode region block node edge hyperedge graph`
        // but only four of the member forms were accepted here. `region`,
        // `hyperedge` and `graph` fell through to the generic path, where the
        // member NAME was parsed as an expression and reported "unresolved
        // name" -- so a dialect declaring a region could not compile.
        if (p.check(Tk.TOKEN_KW_OPCODE) || p.check(Tk.TOKEN_KW_NODE)
         || p.check(Tk.TOKEN_KW_EDGE) || p.check(Tk.TOKEN_KW_BLOCK)
         || p.check(Tk.TOKEN_KW_REGION) || p.check(Tk.TOKEN_KW_HYPEREDGE)
         || p.check(Tk.TOKEN_KW_GRAPH))
        {
            Tok ok = p.advance();
            Node* op = p.mk_at(Nk.N_DECL_FIELD, ok);
            if (pfront_parse::tok_is_member_name(p.ct()))
            {
                Tok nm2 = p.advance();
                op.name_id = p.interner.intern(nm2.start, nm2.len);
                op.p.sptr = nm2.start;
                op.p.slen = nm2.len;
            }
            if (p.accept(Tk.TOKEN_COLON)) { op.type_ann = p.parse_type(); }
            p.add(n, op);
        }
        else if (p.check(Tk.TOKEN_NEWLINE)) { p.advance(); continue; }
        else { break; }
        p.skip_layout();
    }
    if (indented) { while (p.accept(Tk.TOKEN_DEDENT)) {} }
    if (braced) { p.expect(Tk.TOKEN_RBRACE, 1240, "expected '}' to close dialect"); }
    return n;
}

// ════════════════════════════════════════════════════════════════════════════
// 4. EFFECT INFERENCE
// ════════════════════════════════════════════════════════════════════════════
// The parser seeds leaf effects (a call is EFF_IO, alloc is EFF_ALLOC, ...).
// This pass pushes them up through the tree and, once names are resolved,
// pulls a callee's declared effects into the caller.
struct EffectPass
{
    usz nodes_visited;
    usz fns_analysed;
    usz effectful_fns;
    usz pure_fns;
    int rounds;
    bool changed;
}

fn void EffectPass.init(EffectPass* e)
{
    e.nodes_visited = 0;
    e.fns_analysed = 0;
    e.effectful_fns = 0;
    e.pure_fns = 0;
    e.rounds = 0;
    e.changed = false;
}

fn ulong EffectPass.infer(EffectPass* e, Node* n, int depth)
{
    if (n == null || depth > 200) { return pfront_core::EFF_PURE; }
    e.nodes_visited = e.nodes_visited + 1;
    ulong acc = n.effects;

    for (usz i = 0; i < n.child_count; i++)
    {
        acc = acc | e.infer(n.children[i], depth + 1);
    }

    // A resolved call inherits the callee's inferred effect set.
    if (n.kind == Nk.N_EXPR_CALL && n.child_count > 0)
    {
        Node* callee = n.children[0];
        if (callee != null && callee.resolved != null)
        {
            acc = acc | callee.resolved.effects;
        }
    }
    if (n.kind == Nk.N_EXPR_IDENT && n.resolved != null)
    {
        if (n.resolved.kind == Nk.N_DECL_EFFECT_OP)
        {
            acc = acc | pfront_core::EFF_IO;
        }
    }
    // An explicit effect row on a signature is authoritative: honour it.
    if (n.type_ann != null)
    {
        ulong declared = collect_row_effects(n.type_ann, 0);
        acc = acc | declared;
    }

    if (acc != n.effects) { e.changed = true; }
    n.effects = acc;
    return acc;
}

fn ulong collect_row_effects(Node* t, int depth)
{
    if (t == null || depth > 40) { return pfront_core::EFF_PURE; }
    ulong acc = pfront_core::EFF_PURE;
    if (t.kind == Nk.N_TY_EFFECT_ROW)
    {
        for (usz i = 0; i < t.child_count; i++)
        {
            Node* el = t.children[i];
            if (el == null) { continue; }
            acc = acc | effect_name_bit(el.p.sptr, el.p.slen);
        }
    }
    for (usz i = 0; i < t.child_count; i++)
    {
        acc = acc | collect_row_effects(t.children[i], depth + 1);
    }
    return acc;
}

fn ulong effect_name_bit(char* s, usz len)
{
    if (s == null || len == 0) { return pfront_core::EFF_PURE; }
    if (len == 2 && s[0] == 'I' && s[1] == 'O') { return pfront_core::EFF_IO; }
    if (len == 5 && s[0] == 'A') { return pfront_core::EFF_ALLOC; }
    if (len == 5 && s[0] == 'P') { return pfront_core::EFF_PANIC; }
    if (len == 6 && s[0] == 'U') { return pfront_core::EFF_UNSAFE; }
    if (len == 3 && s[0] == 'D') { return pfront_core::EFF_DIVERGE; }
    return pfront_core::EFF_IO;
}

// Run to a fixpoint so mutual recursion converges.
fn void EffectPass.run(EffectPass* e, Node* root)
{
    for (int i = 0; i < 8; i++)
    {
        e.changed = false;
        e.rounds = i + 1;
        e.infer(root, 0);
        if (!e.changed) { break; }
    }
    e.tally(root, 0);
}

fn void EffectPass.tally(EffectPass* e, Node* n, int depth)
{
    if (n == null || depth > 200) { return; }
    if (n.kind == Nk.N_DECL_FN || n.kind == Nk.N_DECL_EXTERN_FN)
    {
        e.fns_analysed = e.fns_analysed + 1;
        if (n.effects == pfront_core::EFF_PURE) { e.pure_fns = e.pure_fns + 1; }
        else { e.effectful_fns = e.effectful_fns + 1; }
    }
    for (usz i = 0; i < n.child_count; i++) { e.tally(n.children[i], depth + 1); }
}

fn void EffectPass.report(EffectPass* e)
{
    printf("  effect rounds    : %d\n", e.rounds);
    printf("  functions        : %d (pure=%d effectful=%d)\n",
           (int)e.fns_analysed, (int)e.pure_fns, (int)e.effectful_fns);
}

// ════════════════════════════════════════════════════════════════════════════
// 5. LINTS
// ════════════════════════════════════════════════════════════════════════════
struct Linter
{
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;
    usz  unused_bindings;
    usz  dead_after_return;
    usz  empty_blocks;
    usz  shadowed;
    usz  checked;
}

fn void Linter.init(Linter* l, pfront_core::DiagBag* d,
                    pfront_core::Interner* it, char* file)
{
    l.diags = d;
    l.interner = it;
    l.file = file;
    l.unused_bindings = 0;
    l.dead_after_return = 0;
    l.empty_blocks = 0;
    l.shadowed = 0;
    l.checked = 0;
}

// A binding whose name starts with '_' is intentionally unused.
fn bool name_is_ignored(Node* n)
{
    if (n == null || n.p.sptr == null || n.p.slen == 0) { return false; }
    return n.p.sptr[0] == '_';
}

fn void Linter.walk(Linter* l, Node* n, int depth)
{
    if (n == null || depth > 200) { return; }
    l.checked = l.checked + 1;

    // Unused let-bindings and parameters.
    if (n.kind == Nk.N_PAT_IDENT)
    {
        bool used = (n.flags & pfront_core::NF_USED) != 0;
        if (n.sym != null && n.sym.used) { used = true; }
        if (!used && !name_is_ignored(n))
        {
            l.unused_bindings = l.unused_bindings + 1;
            l.diags.warn(pfront_core::Phase.PH_RESOLVE, 4001, n.line, n.col,
                         "unused binding (prefix with '_' if intentional)", l.file);
        }
    }

    // Statements after a diverging statement are unreachable.
    if (n.kind == Nk.N_BLOCK)
    {
        if (n.child_count == 0) { l.empty_blocks = l.empty_blocks + 1; }
        bool diverged = false;
        for (usz i = 0; i < n.child_count; i++)
        {
            Node* s = n.children[i];
            if (s == null) { continue; }
            if (diverged)
            {
                l.dead_after_return = l.dead_after_return + 1;
                l.diags.warn(pfront_core::Phase.PH_RESOLVE, 4002, s.line, s.col,
                             "unreachable code (a previous statement always diverges)",
                             l.file);
                break;
            }
            if (stmt_diverges(s)) { diverged = true; }
        }
    }

    for (usz i = 0; i < n.child_count; i++) { l.walk(n.children[i], depth + 1); }
}

fn bool stmt_diverges(Node* s)
{
    if (s == null) { return false; }
    switch (s.kind)
    {
        case N_STMT_RETURN:
        case N_STMT_BREAK:
        case N_STMT_CONTINUE:
        case N_EXPR_UNREACHABLE:
        case N_EXPR_TRAP:
            return true;
        default:
            return (s.effects & pfront_core::EFF_DIVERGE) != 0;
    }
}

fn void Linter.report(Linter* l)
{
    printf("  unused bindings  : %d\n", (int)l.unused_bindings);
    printf("  unreachable stmts: %d\n", (int)l.dead_after_return);
    printf("  empty blocks     : %d\n", (int)l.empty_blocks);
}

// ════════════════════════════════════════════════════════════════════════════
// 6. EXHAUSTIVENESS
// ════════════════════════════════════════════════════════════════════════════
// For a match on an enum, check every variant is covered (or a wildcard is).
struct ExhaustCheck
{
    pfront_core::DiagBag* diags;
    char* file;
    usz matches_checked;
    usz non_exhaustive;
    usz has_wildcard;
}

fn void ExhaustCheck.init(ExhaustCheck* x, pfront_core::DiagBag* d, char* file)
{
    x.diags = d;
    x.file = file;
    x.matches_checked = 0;
    x.non_exhaustive = 0;
    x.has_wildcard = 0;
}

fn bool pattern_is_irrefutable(Node* p)
{
    if (p == null) { return false; }
    switch (p.kind)
    {
        case N_PAT_WILDCARD:
        case N_PAT_IDENT:
            return true;
        case N_PAT_TUPLE:
        {
            for (usz i = 0; i < p.child_count; i++)
            {
                if (!pattern_is_irrefutable(p.children[i])) { return false; }
            }
            return true;
        }
        default:
            return false;
    }
}

// Find the enum decl a scrutinee resolves to, if any.
fn Node* enum_of_scrutinee(Node* scrut)
{
    if (scrut == null || scrut.resolved == null) { return null; }
    Node* d = scrut.resolved;
    if (d.kind == Nk.N_DECL_ENUM) { return d; }
    if (d.type_ann != null && d.type_ann.resolved != null
        && d.type_ann.resolved.kind == Nk.N_DECL_ENUM)
    {
        return d.type_ann.resolved;
    }
    return null;
}

fn void ExhaustCheck.walk(ExhaustCheck* x, Node* n, int depth)
{
    if (n == null || depth > 200) { return; }
    if (n.kind == Nk.N_EXPR_MATCH && n.child_count >= 2)
    {
        x.matches_checked = x.matches_checked + 1;
        bool wildcard = false;
        for (usz i = 1; i < n.child_count; i++)
        {
            Node* arm = n.children[i];
            if (arm == null) { continue; }
            if (pattern_is_irrefutable(arm.child(0))) { wildcard = true; }
        }
        if (wildcard)
        {
            x.has_wildcard = x.has_wildcard + 1;
            n.flags = n.flags | pfront_core::NF_EXHAUSTIVE;
        }
        else
        {
            Node* en = enum_of_scrutinee(n.child(0));
            if (en != null)
            {
                usz total = 0;
                usz covered = 0;
                for (usz v = 0; v < en.child_count; v++)
                {
                    Node* variant = en.children[v];
                    if (variant == null || variant.kind != Nk.N_DECL_VARIANT) { continue; }
                    total = total + 1;
                    for (usz i = 1; i < n.child_count; i++)
                    {
                        Node* arm = n.children[i];
                        if (arm == null) { continue; }
                        Node* pt = arm.child(0);
                        if (pt != null && pt.kind == Nk.N_PAT_VARIANT
                            && pt.name_id == variant.name_id)
                        {
                            covered = covered + 1;
                            break;
                        }
                    }
                }
                if (total > 0 && covered < total)
                {
                    x.non_exhaustive = x.non_exhaustive + 1;
                    x.diags.warn(pfront_core::Phase.PH_RESOLVE, 4010, n.line, n.col,
                                 "match may not cover every variant of this enum",
                                 x.file);
                }
                else if (total > 0)
                {
                    n.flags = n.flags | pfront_core::NF_EXHAUSTIVE;
                }
            }
        }
    }
    for (usz i = 0; i < n.child_count; i++) { x.walk(n.children[i], depth + 1); }
}

fn void ExhaustCheck.report(ExhaustCheck* x)
{
    printf("  matches checked  : %d (wildcard=%d, possibly-partial=%d)\n",
           (int)x.matches_checked, (int)x.has_wildcard, (int)x.non_exhaustive);
}

// ════════════════════════════════════════════════════════════════════════════
// 6b. DID-YOU-MEAN SUGGESTIONS
// ════════════════════════════════════════════════════════════════════════════
// Bounded Levenshtein distance over interned names. Used to turn a bare
// "unresolved name" into "unresolved name; did you mean `foo`?", which is the
// difference between a usable and an infuriating error message.
const usz EDIT_MAX_LEN = 64;

fn usz edit_distance(char* a, usz alen, char* b, usz blen, usz cutoff)
{
    if (alen > EDIT_MAX_LEN || blen > EDIT_MAX_LEN) { return cutoff + 1; }
    // Quick reject on length difference alone.
    usz diff = alen > blen ? alen - blen : blen - alen;
    if (diff > cutoff) { return cutoff + 1; }

    usz[EDIT_MAX_LEN + 1] prev;
    usz[EDIT_MAX_LEN + 1] cur;
    for (usz j = 0; j <= blen; j++) { prev[j] = j; }

    for (usz i = 1; i <= alen; i++)
    {
        cur[0] = i;
        usz row_best = cur[0];
        for (usz j = 1; j <= blen; j++)
        {
            usz cost = lower_eq(a[i - 1], b[j - 1]) ? 0 : 1;
            usz del = prev[j] + 1;
            usz ins = cur[j - 1] + 1;
            usz sub = prev[j - 1] + cost;
            usz best = del;
            if (ins < best) { best = ins; }
            if (sub < best) { best = sub; }
            cur[j] = best;
            if (best < row_best) { row_best = best; }
        }
        // Whole row already exceeds the cutoff: no path can recover.
        if (row_best > cutoff) { return cutoff + 1; }
        for (usz j = 0; j <= blen; j++) { prev[j] = cur[j]; }
    }
    return prev[blen];
}

fn bool lower_eq(char x, char y)
{
    char lx = x;
    char ly = y;
    if (lx >= 'A' && lx <= 'Z') { lx = (char)(lx + 32); }
    if (ly >= 'A' && ly <= 'Z') { ly = (char)(ly + 32); }
    return lx == ly;
}

// Scan every interned name for the closest match to `name`.
struct Suggester
{
    pfront_core::Interner* interner;
    usz  queries;
    usz  hits;
}

fn void Suggester.init(Suggester* s, pfront_core::Interner* it)
{
    s.interner = it;
    s.queries = 0;
    s.hits = 0;
}

fn uint Suggester.best_match(Suggester* s, uint name_id, uint* candidates, usz cand_count)
{
    s.queries = s.queries + 1;
    char* target = s.interner.text(name_id);
    usz tlen = s.interner.text_len(name_id);
    if (target == null || tlen == 0) { return 0; }

    // Allow roughly one edit per three characters, capped at 3.
    usz cutoff = tlen / 3;
    if (cutoff < 1) { cutoff = 1; }
    if (cutoff > 3) { cutoff = 3; }

    uint best_id = 0;
    usz  best_d = cutoff + 1;
    for (usz i = 0; i < cand_count; i++)
    {
        uint cid = candidates[i];
        if (cid == 0 || cid == name_id) { continue; }
        char* c = s.interner.text(cid);
        usz clen = s.interner.text_len(cid);
        if (c == null || clen == 0) { continue; }
        usz d = edit_distance(target, tlen, c, clen, cutoff);
        if (d < best_d) { best_d = d; best_id = cid; }
    }
    if (best_id != 0) { s.hits = s.hits + 1; }
    return best_id;
}

fn void Suggester.report(Suggester* s)
{
    printf("  suggestions      : %d hits / %d queries\n", (int)s.hits, (int)s.queries);
}

// ════════════════════════════════════════════════════════════════════════════
// 7. AST STATISTICS
// ════════════════════════════════════════════════════════════════════════════
struct Stats
{
    usz[pfront_core::NodeKind.N_KIND_COUNT.ordinal] by_kind;
    usz total;
    usz decls;
    usz exprs;
    usz patterns;
    usz types;
    usz resolved;
    usz unresolved;
    int max_depth;
    usz max_children;
}

fn void Stats.init(Stats* s)
{
    for (usz i = 0; i < pfront_core::NodeKind.N_KIND_COUNT.ordinal; i++) { s.by_kind[i] = 0; }
    s.total = 0;
    s.decls = 0;
    s.exprs = 0;
    s.patterns = 0;
    s.types = 0;
    s.resolved = 0;
    s.unresolved = 0;
    s.max_depth = 0;
    s.max_children = 0;
}

fn void Stats.walk(Stats* s, Node* n, int depth)
{
    if (n == null || depth > 300) { return; }
    s.total = s.total + 1;
    int k = (int)n.kind;
    if (k >= 0 && k < (int)pfront_core::NodeKind.N_KIND_COUNT.ordinal)
    {
        s.by_kind[k] = s.by_kind[k] + 1;
    }
    if (pfront_core::is_decl(n.kind)) { s.decls = s.decls + 1; }
    if (pfront_core::is_expr(n.kind)) { s.exprs = s.exprs + 1; }
    if (pfront_core::is_pattern(n.kind)) { s.patterns = s.patterns + 1; }
    if (pfront_core::is_type(n.kind)) { s.types = s.types + 1; }
    if (n.resolved != null) { s.resolved = s.resolved + 1; }
    if (depth > s.max_depth) { s.max_depth = depth; }
    if (n.child_count > s.max_children) { s.max_children = n.child_count; }
    for (usz i = 0; i < n.child_count; i++) { s.walk(n.children[i], depth + 1); }
    if (n.type_ann != null) { s.walk(n.type_ann, depth + 1); }
}

fn void Stats.report(Stats* s, pfront_core::Interner* it)
{
    printf("  total nodes      : %d\n", (int)s.total);
    printf("    declarations   : %d\n", (int)s.decls);
    printf("    expressions    : %d\n", (int)s.exprs);
    printf("    patterns       : %d\n", (int)s.patterns);
    printf("    types          : %d\n", (int)s.types);
    printf("  resolved refs    : %d\n", (int)s.resolved);
    printf("  max depth        : %d\n", s.max_depth);
    printf("  widest node      : %d children\n", (int)s.max_children);
}

// Print the most common node kinds — useful when tuning the parser.
fn void Stats.report_histogram(Stats* s, int top_n)
{
    printf("  --- node kind histogram (top %d) ---\n", top_n);
    for (int rank = 0; rank < top_n; rank++)
    {
        usz best = 0;
        int best_k = -1;
        for (int k = 0; k < (int)pfront_core::NodeKind.N_KIND_COUNT.ordinal; k++)
        {
            if (s.by_kind[k] > best)
            {
                bool already = false;
                best = s.by_kind[k];
                best_k = k;
            }
        }
        if (best_k < 0 || best == 0) { break; }
        printf("    %-18s %d\n",
               pfront_core::kind_name((pfront_core::NodeKind)best_k), (int)best);
        s.by_kind[best_k] = 0;
    }
}
