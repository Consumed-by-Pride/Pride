// ============================================================================
// pfront_dump.c3 — the final AST renderer
// ----------------------------------------------------------------------------
// `--dump-ast` prints the tree as the PARSER built it, which is the right
// thing when debugging the parser and the wrong thing for everything else.
// By the time the front end is done the tree has been rewritten by the
// partial evaluator, the term rewriter, the e-graph and the optimizer, and
// every one of those passes attached information that the plain dump throws
// away.
//
// `--emit-ast` prints the FINAL tree with everything the front end learned:
//
//   * resolution      — which declaration each identifier binds to
//   * effects         — the inferred effect row, as symbols
//   * provenance      — SYN marks a node the compiler synthesised, so a
//                       folded constant is visibly not what the user typed
//   * literal values  — after folding, so `2*3+4` shows as `7`
//   * flags           — mut / pub / exhaustive / tail
//
// Two output shapes, because they serve different readers:
//
//   TREE  — indented, for a human reading the structure.
//   SEXP  — a fully parenthesised S-expression on one line per top-level
//           declaration, for a machine. This is the form the middle end
//           will consume, and it is stable enough to diff between builds,
//           which is what makes an optimization regression visible.
//
// The renderer is deliberately total: every NodeKind has a case, and unknown
// kinds print their numeric id rather than silently rendering as nothing. A
// dump that quietly omits a node is worse than no dump, because it makes a
// tree look correct when it is not.
// ============================================================================

module pfront_dump;

import pfront_core;
import pfront_lex;

alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Tk    = pfront_lex::TokenType;

extern fn int printf(char* fmt, ...);

const int DUMP_MAX_DEPTH = 200;

// ── Operator spelling ───────────────────────────────────────────────────────
// The parser stores the operator as a raw token id. Printing the id would
// make the dump unreadable, so map it back to source syntax.
fn char* op_text(int op)
{
    switch ((Tk)op)
    {
        case TOKEN_PLUS:          return "+";
        case TOKEN_MINUS:         return "-";
        case TOKEN_STAR:          return "*";
        case TOKEN_SLASH:         return "/";
        case TOKEN_PERCENT:       return "%";
        case TOKEN_AMP:           return "&";
        case TOKEN_PIPE:          return "|";
        case TOKEN_XOR:           return "^";
        case TOKEN_LSHIFT:        return "<<";
        case TOKEN_RSHIFT:        return ">>";
        case TOKEN_AMPAMP:        return "&&";
        case TOKEN_PIPEPIPE:      return "||";
        case TOKEN_BANG:          return "!";
        case TOKEN_EQEQ:          return "==";
        case TOKEN_NEQ:           return "!=";
        case TOKEN_NEQ_UNI:       return "≠";
        case TOKEN_LT:            return "<";
        case TOKEN_GT:            return ">";
        case TOKEN_LTEQ:          return "<=";
        case TOKEN_GTEQ:          return ">=";
        case TOKEN_LEQ_UNI:       return "≤";
        case TOKEN_GEQ_UNI:       return "≥";
        case TOKEN_EQ:            return "=";
        case TOKEN_PLUSEQ:        return "+=";
        case TOKEN_MINUSEQ:       return "-=";
        case TOKEN_STAREQ:        return "*=";
        case TOKEN_SLASHEQ:       return "/=";
        case TOKEN_PERCENTEQ:     return "%=";
        case TOKEN_AMPEQ:         return "&=";
        case TOKEN_PIPEEQ:        return "|=";
        case TOKEN_XOREQ:         return "^=";
        case TOKEN_LSHIFTEQ:      return "<<=";
        case TOKEN_RSHIFTEQ:      return ">>=";
        case TOKEN_PLUS_PERCENT:  return "+%";
        case TOKEN_MINUS_PERCENT: return "-%";
        case TOKEN_STAR_PERCENT:  return "*%";
        case TOKEN_PLUS_PIPE:     return "+|";
        case TOKEN_MINUS_PIPE:    return "-|";
        case TOKEN_STAR_PIPE:     return "*|";
        case TOKEN_PLUS_QUESTION: return "+?";
        case TOKEN_MINUS_QUESTION:return "-?";
        case TOKEN_STAR_QUESTION: return "*?";
        case TOKEN_PIPELINE:      return "|>";
        default:                  return "?";
    }
}

// ── Effect row ──────────────────────────────────────────────────────────────
fn void print_effects(ulong e)
{
    if (e == pfront_core::EFF_PURE) { return; }
    printf(" ![");
    bool first = true;
    if ((e & pfront_core::EFF_IO) != 0)      { printf("IO");                first = false; }
    if ((e & pfront_core::EFF_ALLOC) != 0)   { if (!first) { printf(","); } printf("Alloc");  first = false; }
    if ((e & pfront_core::EFF_UNSAFE) != 0)  { if (!first) { printf(","); } printf("Unsafe"); first = false; }
    if ((e & pfront_core::EFF_UB) != 0)      { if (!first) { printf(","); } printf("UB");     first = false; }
    if ((e & pfront_core::EFF_PANIC) != 0)   { if (!first) { printf(","); } printf("Panic");  first = false; }
    if ((e & pfront_core::EFF_DIVERGE) != 0) { if (!first) { printf(","); } printf("Diverge"); }
    printf("]");
}

fn void indent_by(int n)
{
    for (int i = 0; i < n; i++) { printf("  "); }
}

// ── Literal payload ─────────────────────────────────────────────────────────
// Printed for the kinds that carry one. After the optimizer has run this is
// where a folded constant becomes visible: the node prints its VALUE, and the
// SYN marker says the compiler put it there.
fn void print_payload(Node* n, pfront_core::Interner* it)
{
    switch (n.kind)
    {
        case N_EXPR_INT:
            printf(" %lld", (long)n.p.ival);
            if (n.p.width != 0) { printf("%s%d", n.p.is_signed ? "i" : "u", (int)n.p.width); }
        case N_EXPR_FLOAT:
            printf(" %f", n.p.fval);
        case N_EXPR_BOOL:
            printf(" %s", n.p.ival != 0 ? "true" : "false");
        case N_EXPR_CHAR:
            printf(" '\\u%04x'", (int)n.p.ival);
        case N_EXPR_STRING:
            printf(" \"");
            if (n.p.sptr != null)
            {
                // Cap the echo: a long string literal would drown the dump.
                usz cap = n.p.slen > 32 ? (usz)32 : n.p.slen;
                for (usz i = 0; i < cap; i++)
                {
                    char c = n.p.sptr[i];
                    if (c == '\n') { printf("\\n"); }
                    else if (c == '\t') { printf("\\t"); }
                    else if (c == '"') { printf("\\\""); }
                    else { printf("%c", c); }
                }
                if (n.p.slen > 32) { printf("..."); }
            }
            printf("\"");
        case N_EXPR_BINARY:
        case N_EXPR_UNARY:
        case N_STMT_ASSIGN:
        case N_STMT_COMPOUND_ASSIGN:
        case N_EXPR_ASSIGN:
            printf(" %s", op_text(n.p.op));
        default:
            break;
    }
}

// ── Flags ───────────────────────────────────────────────────────────────────
fn void print_flags(Node* n)
{
    uint f = n.flags;
    if ((f & pfront_core::NF_PUB) != 0)        { printf(" pub"); }
    if ((f & pfront_core::NF_MUT) != 0)        { printf(" mut"); }
    if ((f & pfront_core::NF_SYNTHETIC) != 0)  { printf(" SYN"); }
    if ((f & pfront_core::NF_EXHAUSTIVE) != 0) { printf(" exh"); }
    if ((f & pfront_core::NF_VARIADIC) != 0)   { printf(" ..."); }
    if ((f & pfront_core::NF_EXTERN) != 0)     { printf(" extern"); }
    if ((f & pfront_core::NF_TAIL) != 0)       { printf(" tail"); }
    if ((f & pfront_core::NF_ERROR) != 0)      { printf(" ERR"); }
}

// ════════════════════════════════════════════════════════════════════════════
// TREE FORM
// ════════════════════════════════════════════════════════════════════════════

struct DumpStats
{
    usz nodes;
    usz synthetic;
    usz resolved;
    usz unresolved;
    usz max_depth;
}

fn void DumpStats.init(DumpStats* s)
{
    s.nodes = 0; s.synthetic = 0; s.resolved = 0;
    s.unresolved = 0; s.max_depth = 0;
}

fn void dump_tree(Node* n, pfront_core::Interner* it, int depth, DumpStats* st)
{
    if (n == null) { return; }
    if (depth > DUMP_MAX_DEPTH)
    {
        indent_by(depth);
        printf("... (depth limit)\n");
        return;
    }

    st.nodes = st.nodes + 1;
    if ((usz)depth > st.max_depth) { st.max_depth = (usz)depth; }
    if ((n.flags & pfront_core::NF_SYNTHETIC) != 0) { st.synthetic = st.synthetic + 1; }

    indent_by(depth);
    printf("%s", pfront_core::kind_name(n.kind));

    if (n.name_id != 0 && it != null)
    {
        char* nm = it.text(n.name_id);
        if (nm != null) { printf(" '%s'", nm); }
    }

    print_payload(n, it);
    print_flags(n);
    print_effects(n.effects);

    // Resolution: the single most useful thing to see, because an
    // accidentally-unresolved name is the most common front-end bug.
    if (n.kind == Nk.N_EXPR_IDENT)
    {
        if (n.resolved != null)
        {
            st.resolved = st.resolved + 1;
            printf(" -> %s", pfront_core::kind_name(n.resolved.kind));
            if (n.resolved.name_id != 0 && it != null)
            {
                char* rn = it.text(n.resolved.name_id);
                if (rn != null) { printf(" '%s'", rn); }
            }
            printf("#%d", (int)n.resolved.id);
        }
        else if ((n.flags & pfront_core::NF_RESOLVED) != 0)
        {
            // Module-path segment: resolved, but to a module rather than a
            // declaration. Not an error, and not counted as unresolved.
            st.resolved = st.resolved + 1;
            printf(" -> module");
        }
        else
        {
            st.unresolved = st.unresolved + 1;
            printf(" -> UNRESOLVED");
        }
    }

    printf("  @%d:%d\n", n.line, n.col);

    if (n.type_ann != null)
    {
        indent_by(depth + 1);
        printf(": ");
        printf("%s\n", pfront_core::kind_name(n.type_ann.kind));
        dump_tree(n.type_ann, it, depth + 2, st);
    }

    for (usz i = 0; i < n.child_count; i++)
    {
        dump_tree(n.children[i], it, depth + 1, st);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// S-EXPRESSION FORM
// ════════════════════════════════════════════════════════════════════════════
// Machine-readable and diffable. One top-level declaration per line means a
// change to one function shows as a one-line diff instead of reflowing the
// whole file, which is what makes this usable as an optimization regression
// baseline.

fn void dump_sexp(Node* n, pfront_core::Interner* it, int depth)
{
    if (n == null) { printf("()"); return; }
    if (depth > DUMP_MAX_DEPTH) { printf("(...)"); return; }

    printf("(%s", pfront_core::kind_name(n.kind));

    if (n.name_id != 0 && it != null)
    {
        char* nm = it.text(n.name_id);
        if (nm != null) { printf(" %s", nm); }
    }

    switch (n.kind)
    {
        case N_EXPR_INT:   printf(" %lld", (long)n.p.ival);
        case N_EXPR_BOOL:  printf(" %s", n.p.ival != 0 ? "true" : "false");
        case N_EXPR_FLOAT: printf(" %f", n.p.fval);
        case N_EXPR_BINARY:
        case N_EXPR_UNARY: printf(" %s", op_text(n.p.op));
        default: break;
    }

    if ((n.flags & pfront_core::NF_SYNTHETIC) != 0) { printf(" :syn"); }
    if (n.effects != pfront_core::EFF_PURE) { print_effects(n.effects); }

    for (usz i = 0; i < n.child_count; i++)
    {
        printf(" ");
        dump_sexp(n.children[i], it, depth + 1);
    }
    printf(")");
}

// ── Entry point ─────────────────────────────────────────────────────────────
fn void emit_ast(Node* root, pfront_core::Interner* it, char* path, bool sexp)
{
    if (root == null) { return; }

    if (sexp)
    {
        printf("=== final AST, s-expression (%s) ===\n", path);
        for (usz i = 0; i < root.child_count; i++)
        {
            dump_sexp(root.children[i], it, 0);
            printf("\n");
        }
        return;
    }

    printf("=== final AST, post-optimization (%s) ===\n", path);
    printf("--- legend: SYN = compiler-synthesised   -> = resolves to   ![] = effects\n");

    DumpStats st;
    st.init();
    dump_tree(root, it, 0, &st);

    printf("--- %d nodes, depth %d, %d synthetic, %d resolved, %d unresolved\n",
           (int)st.nodes, (int)st.max_depth, (int)st.synthetic,
           (int)st.resolved, (int)st.unresolved);
}
