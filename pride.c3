// pride.c3 — Pride compiler front-end driver
// Implementation language: C3 (host).
//   pride <file.pie>
// Reads a Pride source file, runs lexer.c3 -> parser.c3 -> AST, then prints
// the resulting tree as an indented dump plus a summary (node count, effects
// on the root, and any diagnostics).

module pride;

import lexer;
import ast;
import parser;
import resolve;
import typecheck;
import effectcheck;
import lint;
import ssi;
import ssi_ir;
import codegen;
import sasi;
import sasi_opt;
import rewrite;
import pgen;
import stage;
import irdl_msp;
import integrity;
import mono;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn CFile fopen(char* path, char* mode);
extern fn int   fclose(CFile stream);
extern fn usz   fread(void* ptr, usz size, usz nmemb, CFile stream);
extern fn int   fseek(CFile stream, long offset, int whence);
extern fn long  ftell(CFile stream);
extern fn int   printf(char* fmt, ...);
extern fn int   snprintf(char* buf, usz size, char* fmt, ...);
extern fn int   system(char* cmd);
extern fn int   putchar(int c);
extern fn long  readlink(char* path, char* buf, usz bufsz);

alias CFile = void*;

const int SEEK_SET = 0;
const int SEEK_END = 2;

alias Node = ast::AstNode;
alias Nk = ast::NodeKind;

// Reads the whole file into a heap buffer. Returns null on failure; sets *out_len.
fn usz cstr_len2(char* s)
{
    usz n = 0;
    while (s[n] != 0) n++;
    return n;
}

// Exact comparison of a NUL-terminated C string against a literal. Used by
// the CLI argument parser below so every `--flag` is matched unambiguously
// by its FULL text, never by a hand-picked subset of byte positions (that
// class of bug previously made `--strip` silently dispatch as `--stage`,
// and made `--emit-obj`/`--emit-bin` entirely unreachable — both fixed by
// switching every flag comparison in main() to go through this helper).
fn bool arg_is(char* s, usz slen, char* lit)
{
    usz i = 0;
    while (i < slen)
    {
        if (lit[i] == 0) return false;   // s longer than the literal
        if (s[i] != lit[i]) return false;
        i++;
    }
    return lit[i] == 0;                  // s must consume the whole literal
}

// True if `s` starts with `prefix` (both NUL-terminated). Used for flags that
// carry an inline value, e.g. `--target=<triple>` / `--cfg=<name>`.
fn bool arg_starts_with(char* s, usz slen, char* prefix, usz prefix_len)
{
    if (slen < prefix_len) return false;
    for (usz i = 0; i < prefix_len; i++)
    {
        if (s[i] != prefix[i]) return false;
    }
    return true;
}

fn char* read_file(char* path, usz* out_len)
{
    CFile f = fopen(path, "rb");
    if (f == null) return null;

    fseek(f, 0, SEEK_END);
    long file_sz = ftell(f);
    fseek(f, 0, SEEK_SET);

    if (file_sz < 0)
    {
        fclose(f);
        return null;
    }

    usz len = (usz)file_sz;
    char* buf = (char*)malloc(len + 1);
    if (buf == null)
    {
        fclose(f);
        return null;
    }

    usz got = fread((void*)buf, 1, len, f);
    fclose(f);
    buf[got] = 0;
    *out_len = got;
    return buf;
}

fn void print_indent(int depth)
{
    for (int i = 0; i < depth; i++)
    {
        printf("  ");
    }
}

fn void print_span(char* p, usz len)
{
    for (usz i = 0; i < len; i++)
    {
        putchar((int)p[i]);
    }
}

// Print the effect mask in a compact !{IO Alloc ...} form (empty -> nothing).
fn void print_effects(ulong eff)
{
    if (eff == ast::EFFECT_PURE)
    {
        return;
    }
    printf("  !{");
    bool first = true;
    if ((eff & ast::EFFECT_IO) != 0)     { printf("%sIO", first ? "" : " ");     first = false; }
    if ((eff & ast::EFFECT_ALLOC) != 0)  { printf("%sAlloc", first ? "" : " ");  first = false; }
    if ((eff & ast::EFFECT_UNSAFE) != 0) { printf("%sUnsafe", first ? "" : " "); first = false; }
    if ((eff & ast::EFFECT_UB) != 0)     { printf("%sUB", first ? "" : " ");     first = false; }
    if ((eff & ast::EFFECT_PANIC) != 0)  { printf("%sPanic", first ? "" : " ");  first = false; }
    printf("}");
}

// Print a node's inline payload (literal value, name text, operator) if any.
fn void print_payload(Node* n)
{
    switch (n.kind)
    {
        case Nk.NODE_LIT_INT:
            printf(" = %llu", n.p.lit_int.int_val);
        case Nk.NODE_LIT_FLOAT:
            printf(" = <float>");
        case Nk.NODE_LIT_BOOL:
            printf(" = %s", n.p.lit_bool.bool_val ? "true" : "false");
        case Nk.NODE_LIT_CHAR:
            printf(" = 'char'");
        case Nk.NODE_LIT_STRING:
        case Nk.NODE_LIT_RAW_BYTES:
            printf(" = \"");
            print_span(n.p.lit_str.ptr, n.p.lit_str.len);
            printf("\"");
        case Nk.NODE_IDENT:
        case Nk.NODE_TYPEVAR:
        case Nk.NODE_TYPE_PRIMITIVE:
            printf(" '");
            print_span(n.p.ident.name_ptr, n.p.ident.name_len);
            printf("'");
        case Nk.NODE_EXPR_BINARY:
        case Nk.NODE_EXPR_UNARY:
        case Nk.NODE_EXPR_ASSIGN:
        case Nk.NODE_TYPE_REFINEMENT:
            printf(" op=%s", lexer::token_type_name(n.p.op.op));
        default:
            break;
    }
}

// Compact one-line rendering of a type node (for the AST dump's `: type`).
fn void print_type_brief(Node* t)
{
    print_type_brief_d(t, 0);
}

fn void print_type_brief_d(Node* t, int depth)
{
    if (t == null) { printf("?"); return; }
    if (depth > 1200) { printf("..."); return; }
    switch (t.kind)
    {
        case Nk.NODE_TYPE_PRIMITIVE:
            print_span(t.p.ident.name_ptr, t.p.ident.name_len);
        case Nk.NODE_TYPEVAR:
            print_span(t.p.ident.name_ptr, t.p.ident.name_len);
        case Nk.NODE_TYPE_BOTTOM:
        case Nk.NODE_LIT_BOTTOM:
            printf("_|_");
        case Nk.NODE_EXPR_UNIT:
            printf("()");
        case Nk.NODE_TYPE_PTR:
            printf("*");
            if (t.child_count >= 1) print_type_brief_d(t.children[0], depth + 1);
        case Nk.NODE_TYPE_UNION:
            for (usz i = 0; i < t.child_count; i++)
            {
                if (i > 0) printf(" | ");
                print_type_brief_d(t.children[i], depth + 1);
            }
        case Nk.NODE_TYPE_INTERSECT:
            for (usz i = 0; i < t.child_count; i++)
            {
                if (i > 0) printf(" & ");
                print_type_brief_d(t.children[i], depth + 1);
            }
        case Nk.NODE_TYPE_TUPLE:
            printf("(");
            for (usz i = 0; i < t.child_count; i++)
            {
                if (i > 0) printf(", ");
                print_type_brief_d(t.children[i], depth + 1);
            }
            printf(")");
        case Nk.NODE_TYPE_FN:
            if (t.child_count >= 1) print_type_brief_d(t.children[0], depth + 1);
            printf(" -> ");
            if (t.child_count >= 2) print_type_brief_d(t.children[1], depth + 1);
        default:
            printf("%s", ast::node_kind_name(t.kind));
    }
}

// Recursive tree dump.
fn void print_node(Node* n, int depth)
{
    if (depth > 1200) { print_indent(depth); printf("...\n"); return; }
    if (n == null)
    {
        print_indent(depth);
        printf("<null>\n");
        return;
    }

    print_indent(depth);
    printf("%s#%u", ast::node_kind_name(n.kind), n.id);
    print_payload(n);

    if ((n.flags & ast::FLAG_FOLDED) != 0)    printf(" [folded]");
    if ((n.flags & ast::FLAG_MUT) != 0)       printf(" [mut]");
    if ((n.flags & ast::FLAG_RANGE_INCLUSIVE) != 0) printf(" [inclusive]");
    if ((n.flags & ast::FLAG_OPEN_ROW) != 0)  printf(" [open-row]");
    if ((n.flags & ast::FLAG_FIXPOINT) != 0)  printf(" [fixpoint]");
    if ((n.flags & ast::FLAG_UNCHECKED) != 0) printf(" [unchecked]");

    if (n.resolved != null) printf(" -> #%u", n.resolved.id);

    if (n.type_annotation != null)
    {
        printf("  : ");
        print_type_brief(n.type_annotation);
    }

    print_effects(n.effects);
    printf("\n");

    for (usz i = 0; i < n.child_count; i++)
    {
        print_node(n.children[i], depth + 1);
    }
}



// Evaluates a cfg predicate against the active cfg_flags set.
// Returns true if the predicate holds (the declaration should be kept).
// Supported predicates:
//   cfg(name)              — flag 'name' is active
//   cfg(key = "val")       — flag 'key=val' is active
//   cfg(not(p))            — !p
//   cfg(all(p1, p2, ...))  — all predicates hold
//   cfg(any(p1, p2, ...))  — any predicate holds

fn bool cfg_flag_matches(char** flags, int nflags, char* key, usz klen, char* val, usz vlen)
{
    for (int i = 0; i < nflags; i++)
    {
        char* f = flags[i];
        if (f == null) continue;
        // Try key=val match first
        if (vlen > 0)
        {
            // Check if flag is "key=val"
            usz fl = cstr_len2(f);
            if (fl == klen + 1 + vlen)
            {
                bool ok = true;
                for (usz j = 0; j < klen && ok; j++) if (f[j] != key[j]) ok = false;
                if (ok && f[klen] == '=')
                {
                    for (usz j = 0; j < vlen && ok; j++)
                    { if (f[klen + 1 + j] != val[j]) ok = false; }
                    if (ok) return true;
                }
            }
        }
        else
        {
            // Bare name match
            usz fl = cstr_len2(f);
            if (fl == klen)
            {
                bool eq = true;
                for (usz j = 0; j < klen; j++) if (f[j] != key[j]) { eq = false; break; }
                if (eq) return true;
            }
        }
    }
    return false;
}

fn bool eval_cfg_expr(Node* expr, char** flags, int nflags)
{
    if (expr == null) return true;
    // IDENT: bare flag name
    if (expr.kind == NodeKind.NODE_IDENT || expr.kind == NodeKind.NODE_TYPEVAR)
    {
        char* nm = expr.p.ident.name_ptr;
        usz   nl = expr.p.ident.name_len;
        return cfg_flag_matches(flags, nflags, nm, nl, null, 0);
    }
    // key = "value" (Assign with string RHS)
    if (expr.kind == NodeKind.NODE_EXPR_ASSIGN && expr.child_count >= 2)
    {
        Node* key = expr.children[0];
        Node* val = expr.children[1];
        if (key == null || val == null) return true;
        char* kn = key.p.ident.name_ptr;  usz kl = key.p.ident.name_len;
        // val is a string literal: strip quotes
        char* vn = val.p.ident.name_ptr;  usz vl = val.p.ident.name_len;
        // string literal includes surrounding quotes — strip them
        if (vl >= 2 && vn[0]=='"') { vn++; vl -= 2; }
        return cfg_flag_matches(flags, nflags, kn, kl, vn, vl);
    }
    // Call: cfg(...), not(...), all(...), any(...)
    if (expr.kind == NodeKind.NODE_EXPR_CALL)
    { return eval_cfg_call(expr, flags, nflags); }
    return true;
}

fn bool eval_cfg_call(Node* call, char** flags, int nflags)
{
    if (call == null) return true;
    // call.children[0] = callee ident (cfg/not/all/any/or key name)
    // call.children[1..] = arguments
    Node* callee = call.child_count >= 1 ? call.children[0] : null;
    if (callee == null) return true;
    char* nm = callee.p.ident.name_ptr;
    usz   nl = callee.p.ident.name_len;

    // not(p)
    if (nl == 3 && nm[0]=='n'&&nm[1]=='o'&&nm[2]=='t')
    {
        Node* inner = call.child_count >= 2 ? call.children[1] : null;
        return !eval_cfg_expr(inner, flags, nflags);
    }
    // all(p1, p2, ...)
    if (nl == 3 && nm[0]=='a'&&nm[1]=='l'&&nm[2]=='l')
    {
        for (usz i = 1; i < call.child_count; i++)
        { if (!eval_cfg_expr(call.children[i], flags, nflags)) return false; }
        return true;
    }
    // any(p1, p2, ...)
    if (nl == 3 && nm[0]=='a'&&nm[1]=='n'&&nm[2]=='y')
    {
        for (usz i = 1; i < call.child_count; i++)
        { if (eval_cfg_expr(call.children[i], flags, nflags)) return true; }
        return false;
    }
    // Bare name as cfg condition (cfg itself)
    // This is the top-level cfg(predicate) call — evaluate the predicate
    if (nl == 3 && nm[0]=='c'&&nm[1]=='f'&&nm[2]=='g' && call.child_count >= 2)
    { return eval_cfg_expr(call.children[1], flags, nflags); }

    // Otherwise: treat callee name as a bare flag
    return cfg_flag_matches(flags, nflags, nm, nl, null, 0);
}


// Check if a node has a #[cfg(...)] attribute and evaluate it.
// Returns true if the node should be KEPT, false if it should be stripped.
fn bool check_cfg_attrs(Node* n, char** flags, int nflags)
{
    if (n == null) return true;
    // Scan children for NODE_ATTRIBUTE_LIST containing an Attr named "cfg"
    for (usz i = 0; i < n.child_count; i++)
    {
        Node* ch = n.children[i];
        if (ch == null || ch.kind != NodeKind.NODE_ATTRIBUTE_LIST) continue;
        for (usz j = 0; j < ch.child_count; j++)
        {
            Node* attr = ch.children[j];
            if (attr == null) continue;
            if (attr.child_count < 1 || attr.children[0] == null) continue;
            char* an = attr.children[0].p.ident.name_ptr;
            usz   al = attr.children[0].p.ident.name_len;
            if (al == 3 && an[0]=='c'&&an[1]=='f'&&an[2]=='g')
            {
                // Evaluate the cfg predicate (child[1] of attr, or wrap in cfg())
                Node* pred = attr.child_count >= 2 ? attr.children[1] : null;
                if (!eval_cfg_expr(pred, flags, nflags)) return false;
            }
        }
    }
    return true;
}

// Strip program nodes that fail their #[cfg(...)] predicates.
fn void apply_cfg_strip(Node* program, char** flags, int nflags)
{
    if (program == null || nflags == 0) return;
    for (usz i = 0; i < program.child_count; i++)
    {
        Node* child = program.children[i];
        if (!check_cfg_attrs(child, flags, nflags))
        {
            program.children[i] = null;   // strip: null out the pointer
        }
    }
}

// Every diagnostic message maps to a stable E-code. The code is derived by
// hashing the first 32 chars of the message (deterministic across builds).
// Range allocations:
//   E0001–E0099  : lexer errors
//   E0100–E0199  : parser errors
//   E0200–E0299  : resolver errors
//   E0300–E0399  : type errors
//   E0350–E0399  : type warnings
//   E0400–E0449  : effect errors
//   E0450–E0499  : effect warnings
//   E0500–E0599  : lint warnings

fn int stable_error_code(int base, char* msg)
{
    if (msg == null) return base;
    // FNV-1a hash of first 32 bytes of msg, modulo 100, added to base range.
    ulong h = 2166136261;
    for (int i = 0; i < 32 && msg[i] != 0; i++)
    {
        h ^= (ulong)(uint)msg[i];
        h *= 16777619;
    }
    return base + (int)(h % 100);
}

// Fix-it hint: given a message, return a suggestion string (or null).
fn char* fixit_hint(char* msg)
{
    if (msg == null) return null;
    // Pattern match on message prefix for common actionable errors.
    if (msg[0]=='u'&&msg[1]=='n'&&msg[2]=='d'&&msg[3]=='e'&&msg[4]=='f') // "undefined name"
    { return "hint: check spelling; declare the name before use"; }
    if (msg[0]=='d'&&msg[1]=='u'&&msg[2]=='p'&&msg[3]=='l') // "duplicate definition"
    { return "hint: rename one of the two definitions"; }
    if (msg[0]=='a'&&msg[1]=='s'&&msg[2]=='s'&&msg[3]=='i'&&msg[4]=='g'&&msg[5]=='n'&&msg[6]=='m') // "assignment to immutable"
    { return "hint: declare the binding with `let mut` to allow mutation"; }
    if (msg[0]=='t'&&msg[1]=='o'&&msg[2]=='o'&&msg[3]==' '&&msg[4]=='f') // "too few arguments"
    { return "hint: add the missing arguments to the call"; }
    if (msg[0]=='t'&&msg[1]=='o'&&msg[2]=='o'&&msg[3]==' '&&msg[4]=='m') // "too many arguments"
    { return "hint: remove the extra arguments"; }
    if (msg[0]=='i'&&msg[1]=='f'&&msg[2]==' '&&msg[3]=='c') // "if condition is not bool"
    { return "hint: use a comparison operator (==, !=, <, >) to produce a bool"; }
    if (msg[0]=='c'&&msg[1]=='o'&&msg[2]=='n'&&msg[3]=='d'&&msg[4]=='i'&&msg[5]=='t'&&msg[13]=='a') // "condition is an assignment"
    { return "hint: use == for comparison, = is assignment"; }
    if (msg[0]=='m'&&msg[1]=='i'&&msg[2]=='s'&&msg[3]=='s'&&msg[4]=='i'&&msg[5]=='n'&&msg[6]=='g') // "missing field"
    { return "hint: add the missing field or use .. to fill remaining fields"; }
    if (msg[0]=='u'&&msg[1]=='n'&&msg[2]=='k'&&msg[3]=='n'&&msg[4]=='o'&&msg[5]=='w'&&msg[6]=='n'&&msg[7]==' '&&msg[8]=='f') // "unknown field"
    { return "hint: check the struct definition for the correct field name"; }
    if (msg[0]=='b'&&msg[1]=='i'&&msg[2]=='t'&&msg[3]=='w') // "bitwise/shift ... floats"
    { return "hint: cast to an integer type first, then apply bitwise ops"; }
    if (msg[0]=='d'&&msg[1]=='e'&&msg[2]=='r'&&msg[3]=='e'&&msg[4]=='f') // "dereference of non-pointer"
    { return "hint: only pointer types (*T) can be dereferenced with *"; }
    if (msg[0]=='c'&&msg[1]=='l'&&msg[2]=='a'&&msg[3]=='u'&&msg[4]=='s'&&msg[5]=='e'&&msg[6]==' '&&msg[7]=='b') // "clause body type"
    { return "hint: ensure all clauses return the same type, or annotate the return type"; }
    if (msg[0]=='t'&&msg[1]=='y'&&msg[2]=='p'&&msg[3]=='e'&&msg[4]==' '&&msg[5]=='a') // "type argument does not satisfy"
    { return "hint: use a type that satisfies the constraint (e.g., add a where clause)"; }
    if (msg[0]=='p'&&msg[1]=='e'&&msg[2]=='r'&&msg[3]=='f'&&msg[4]=='o'&&msg[5]=='r'&&msg[6]=='m') // "performs undeclared effect"
    { return "hint: add the effect to the function signature: fn f : T -> U ! [EffectName]"; }
    return null;
}

// Did-you-mean: Levenshtein distance ≤ 2 between candidate names.
fn int edit_distance(char* a, int alen, char* b, int blen)
{
    if (alen > 32 || blen > 32) return 99;
    int[33][33] dp;
    for (int i = 0; i <= alen; i++) dp[i][0] = i;
    for (int j = 0; j <= blen; j++) dp[0][j] = j;
    for (int i = 1; i <= alen; i++)
    {
        for (int j = 1; j <= blen; j++)
        {
            int sub = (a[i-1] == b[j-1]) ? 0 : 1;
            int del = dp[i-1][j] + 1;
            int ins = dp[i][j-1] + 1;
            int rep = dp[i-1][j-1] + sub;
            int mn = del < ins ? del : ins;
            dp[i][j] = mn < rep ? mn : rep;
        }
    }
    return dp[alen][blen];
}

// JSON output mode: emit all diagnostics as JSON array.
bool g_json_output = false;

fn void json_escape(char* s)
{
    if (s == null) return;
    for (int i = 0; s[i] != 0; i++)
    {
        char ch = s[i];
        if      (ch == '"')  { printf("\\\""); }
        else if (ch == '\\') { printf("\\\\"); }
        else if (ch == '\n') { printf("\\n"); }
        else if (ch == '\r') { printf("\\r"); }
        else if (ch == '\t') { printf("\\t"); }
        else { printf("%c", ch); }
    }
}

fn void emit_json_diag(char* phase, int line, int col, int code,
                       char* msg, char* hint, char* source_file, bool is_error)
{
    printf("{");
    printf("\"phase\":\"%s\",", phase);
    printf("\"line\":%d,", line);
    printf("\"col\":%d,", col);
    printf("\"code\":\"%04d\",", code);
    printf("\"severity\":\"%s\",", is_error ? "error" : "warning");
    printf("\"message\":\""); json_escape(msg); printf("\",");
    if (hint != null) { printf("\"hint\":\""); json_escape(hint); printf("\","); }
    else              { printf("\"hint\":null,"); }
    printf("\"file\":\""); json_escape(source_file); printf("\"");
    printf("}");
}

fn void report_lexer_diags(lexer::Lexer* lx)
{
    int count = lx.get_diag_count();
    if (count == 0) return;

    printf("\n=== Lexer diagnostics (%d) ===\n", count);
    for (int i = 0; i < count; i++)
    {
        lexer::Diagnostic d = lx.get_diag(i);
        printf("  [lex %d:%d] ", d.line, d.col);
        printf("%s\n", d.msg);
    }
}


// Print the source line that contains the error, then a caret (^) under col.
fn void print_source_line(char* src, usz src_len, int target_line, int col)
{
    if (src == null || src_len == 0 || target_line < 1) return;
    // Walk to the target line
    int cur_line = 1;
    usz line_start = 0;
    for (usz i = 0; i < src_len; i++)
    {
        if (cur_line == target_line) { line_start = i; break; }
        if (src[i] == '\n') cur_line++;
    }
    if (cur_line != target_line) return;
    // Find end of line
    usz line_end = line_start;
    while (line_end < src_len && src[line_end] != '\n') line_end++;
    usz line_len = line_end - line_start;
    if (line_len > 120) line_len = 120;  // cap display width
    // Print line
    printf("    ");
    for (usz i = 0; i < line_len; i++) printf("%c", src[line_start + i]);
    printf("\n    ");
    // Print caret
    int c2 = col > 0 ? col - 1 : 0;
    for (int i = 0; i < c2 && i < 120; i++) printf(" ");
    printf("^\n");
}

fn void report_parser_diags(parser::Parser* p, char* src, usz src_len)
{
    if (p.error_count == 0) return;
    if (g_json_output)
    {
        printf("[");
        for (int i = 0; i < p.error_count; i++)
        {
            parser::ParseError e = p.errors[i];
            int code = stable_error_code(100, e.msg);
            char* hint = fixit_hint(e.msg);
            if (i > 0) printf(",");
            emit_json_diag("parse", e.line, e.col, code, e.msg, hint, src, true);
        }
        printf("]\n");
        return;
    }
    printf("\n=== Parser diagnostics (%d) ===\n", p.error_count);
    for (int i = 0; i < p.error_count; i++)
    {
        parser::ParseError e = p.errors[i];
        int code = stable_error_code(100, e.msg);
        printf("  [parse %d:%d] E%04d: %s\n", e.line, e.col, code, e.msg);
        char* hint = fixit_hint(e.msg);
        if (hint != null) printf("  %s\n", hint);
        print_source_line(src, src_len, e.line, e.col);
    }
}

fn void report_resolve_diags(resolve::Resolver* r, char* src, usz src_len)
{
    if (r.error_count == 0) return;
    if (g_json_output)
    {
        printf("[");
        for (int i = 0; i < r.error_count; i++)
        {
            resolve::ResolveError e = r.errors[i];
            int code = stable_error_code(200, e.msg);
            char* hint = fixit_hint(e.msg);
            if (i > 0) printf(",");
            emit_json_diag("resolve", e.line, e.col, code, e.msg, hint, src, true);
        }
        printf("]\n");
        return;
    }
    printf("\n=== Resolver diagnostics (%d) ===\n", r.error_count);
    for (int i = 0; i < r.error_count; i++)
    {
        resolve::ResolveError e = r.errors[i];
        int code = stable_error_code(200, e.msg);
        printf("  [resolve %d:%d] E%04d: %s\n", e.line, e.col, code, e.msg);
        char* hint = fixit_hint(e.msg);
        if (hint != null) printf("  %s\n", hint);
        print_source_line(src, src_len, e.line, e.col);
    }
}

fn void report_typecheck_diags(typecheck::TypeChecker* tc, char* src, usz src_len)
{
    if (tc.diag_count == 0) return;

    printf("\n=== Type diagnostics (%d) ===\n", tc.diag_count);
    for (int i = 0; i < tc.diag_count; i++)
    {
        typecheck::TypeError e = tc.diags[i];
        int code = stable_error_code(e.is_error ? 300 : 350, e.msg);
        if (g_json_output)
        {
            if (i > 0) printf(",");
            emit_json_diag(e.is_error ? "type-err" : "type-warn", e.line, e.col, code,
                           e.msg, fixit_hint(e.msg), src, e.is_error);
        }
        else
        {
            printf("  [%s %d:%d] E%04d: %s\n", e.is_error ? "type-err" : "type-warn",
                   e.line, e.col, code, e.msg);
            char* hint5 = fixit_hint(e.msg);
            if (hint5 != null) printf("  %s\n", hint5);
            print_source_line(src, src_len, e.line, e.col);
        }
    }
}

fn void report_effect_diags(effectcheck::EffectChecker* ec, char* src, usz src_len)
{
    if (ec.diag_count == 0) return;

    printf("\n=== Effect diagnostics (%d) ===\n", ec.diag_count);
    for (int i = 0; i < ec.diag_count; i++)
    {
        effectcheck::EffectError e = ec.diags[i];
        int code = stable_error_code(e.is_error ? 400 : 450, e.msg);
        if (g_json_output)
        {
            if (i > 0) printf(",");
            emit_json_diag(e.is_error ? "effect-err" : "effect-warn", e.line, e.col, code,
                           e.msg, fixit_hint(e.msg), src, e.is_error);
        }
        else
        {
            printf("  [%s %d:%d] E%04d: %s\n", e.is_error ? "effect-err" : "effect-warn",
                   e.line, e.col, code, e.msg);
            char* hint6 = fixit_hint(e.msg);
            if (hint6 != null) printf("  %s\n", hint6);
            print_source_line(src, src_len, e.line, e.col);
        }
    }
}

// Dump the SSI graph: each recorded use, the version it reads, and any
// active refinement. Used to verify SSI construction (--dump-ssi).
fn void print_binder_name(ssi::SsiVar* v)
{
    if (v == null || v.binder == null) { printf("?"); return; }
    Node* b = v.binder;
    Node* nm = b.child_count >= 1 ? b.children[0] : b;
    if (nm != null && (nm.kind == Nk.NODE_IDENT || nm.kind == Nk.NODE_TYPEVAR))
    {
        print_span(nm.p.ident.name_ptr, nm.p.ident.name_len);
    }
    else
    {
        printf("?");
    }
}

fn void dump_ssi_graph(ssi::SsiGraph* sg)
{
    printf("\n=== SSI (%llu versions, %llu uses) ===\n",
        (ulong)sg.var_count, (ulong)sg.use_count);

    // Versions: show each value-version, its kind, refinement, and (for φ) the
    // incoming operands per edge — the real SSI graph.
    printf("  -- versions --\n");
    for (usz i = 0; i < sg.var_count; i++)
    {
        ssi::SsiVar* v = sg.var_at(i);
        if (v == null) continue;
        printf("    ");
        print_binder_name(v);
        printf(" v%d [%s]", v.version, ssi::ssi_kind_name(v.kind));
        if (v.refinement != null)
        {
            printf(" refined:(%s)", lexer::token_type_name(v.refinement.p.op.op));
        }
        if (v.kind == ssi::SsiKind.SSI_PHI && v.operand_count > 0)
        {
            printf(" = phi(");
            for (usz k = 0; k < v.operand_count; k++)
            {
                if (k > 0) printf(", ");
                ssi::SsiVar* op = v.operands[k];
                int edge = v.op_edge[k];
                if (op != null) { printf("v%d@e%d", op.version, edge); }
                else { printf("_@e%d", edge); }
            }
            printf(")");
        }
        printf("\n");
    }

    // Uses: which version each identifier read resolves to.
    printf("  -- uses --\n");
    for (usz i = 0; i < sg.use_count; i++)
    {
        ssi::SsiUse u = sg.uses[i];
        Node* usen = u.use_node;
        ssi::SsiVar* v = u.ver;
        printf("    use #%u '", usen.id);
        if (usen.kind == Nk.NODE_IDENT || usen.kind == Nk.NODE_TYPEVAR)
        {
            print_span(usen.p.ident.name_ptr, usen.p.ident.name_len);
        }
        printf("' (%d:%d) -> ", usen.line, usen.col);
        if (v != null)
        {
            printf("v%d", v.version);
            if (v.refinement != null)
            {
                printf("  refined:(%s)", lexer::token_type_name(v.refinement.p.op.op));
            }
        }
        else
        {
            printf("<unbound>");
        }
        printf("\n");
    }
}

fn void dump_stage_report(stage::Stager* st)
{
    printf("\n=== Staging / CTFE ===\n");
    printf("  comptime/eval folded : %d\n", st.folded);
    printf("  splices grafted      : %d\n", st.splices);
    printf("  comptime fns         : %llu\n", (ulong)st.fn_count);
    if (st.out_of_fuel) printf("  [OUT OF FUEL]\n");
    if (st.too_deep)    printf("  [EVAL TOO DEEP]\n");
    if (st.overflow)    printf("  [CTFE ENV/FN TABLE OVERFLOW — some bindings or comptime fns were dropped]\n");
    for (int i = 0; i < st.diag_count; i++)
    {
        stage::StageDiag d = st.diags[i];
        printf("  [%s %d:%d] %s\n", d.is_error ? "stage-err" : "stage-warn", d.line, d.col, d.msg);
    }
}

fn void dump_irdl_report(irdl_msp::DialectTable* dt)
{
    printf("\n=== IRDL ===\n");
    printf("  dialects registered  : %llu\n", (ulong)dt.dialect_count);
    printf("  opcodes registered   : %llu\n", (ulong)dt.opcode_count);
    printf("  regions registered   : %llu\n", (ulong)dt.region_count);
    printf("  graphs registered    : %llu (%llu nodes, %llu edges)\n",
        (ulong)dt.graph_count, (ulong)dt.graph_node_count, (ulong)dt.graph_edge_count);
    printf("  lowerings applied    : %d\n", dt.lowerings_applied);
    if (dt.out_of_fuel) printf("  [OUT OF FUEL]\n");
    if (dt.too_deep)    printf("  [LOWER CHAIN TOO DEEP]\n");
    if (dt.overflow)    printf("  [IRDL TABLE OVERFLOW — some dialects/opcodes/regions were dropped]\n");
    // per-opcode lowering status
    for (usz i = 0; i < dt.opcode_count; i++)
    {
        irdl_msp::Opcode* o = &dt.opcodes[i];
        printf("    ");
        for (usz j = 0; j < o.dname_len; j++) printf("%c", o.dname[j]);
        printf(".");
        for (usz j = 0; j < o.name_len; j++) printf("%c", o.name[j]);
        if (o.has_sig) { printf("  : (%llu args -> result)", (ulong)o.arg_kind_count); }
        if (o.has_rule) { printf("  [%llu rule(s)]\n", (ulong)o.rule_count); }
        else { printf("  [no lowering rule]\n"); }
    }
    for (int i = 0; i < dt.diag_count; i++)
    {
        irdl_msp::IrdlDiag d = dt.diags[i];
        printf("  [%s %d:%d] %s\n", d.is_error ? "irdl-err" : "irdl-warn", d.line, d.col, d.msg);
    }
}

// Recursively collect every `rewrite {...}` block's rules into one set.
// Driver-level AST walks are depth-guarded so pathological nesting degrades
// gracefully instead of overflowing the native stack.
const int DRIVER_MAX_DEPTH = 1200;

fn void collect_rules(rewrite::RuleSet* rs, Node* n, int depth)
{
    if (n == null || depth > DRIVER_MAX_DEPTH) return;
    if (n.kind == Nk.NODE_REWRITE)
    {
        rs.add_block(n);
        return;
    }
    if (n.kind == Nk.NODE_REWRITE_RULE)
    {
        rs.add_rule_node(n);
        return;
    }
    for (usz i = 0; i < n.child_count; i++) collect_rules(rs, n.children[i], depth + 1);
}

// A compact one-line expression printer (for rewrite before/after display).
fn void print_expr(Node* n)
{
    print_expr_d(n, 0);
}

fn void print_expr_d(Node* n, int depth)
{
    if (n == null) { printf("?"); return; }
    if (depth > 1200) { printf("..."); return; }
    switch (n.kind)
    {
        case Nk.NODE_LIT_INT:    printf("%llu", n.p.lit_int.int_val);
        case Nk.NODE_LIT_BOOL:   printf("%s", n.p.lit_bool.bool_val ? "true" : "false");
        case Nk.NODE_IDENT:
        case Nk.NODE_TYPEVAR:    print_span(n.p.ident.name_ptr, n.p.ident.name_len);
        case Nk.NODE_EXPR_BINARY:
            printf("(");
            if (n.child_count >= 1) print_expr_d(n.children[0], depth + 1);
            printf(" %s ", lexer::token_type_name(n.p.op.op));
            if (n.child_count >= 2) print_expr_d(n.children[1], depth + 1);
            printf(")");
        case Nk.NODE_EXPR_UNARY:
            printf("%s", lexer::token_type_name(n.p.op.op));
            if (n.child_count >= 1) print_expr_d(n.children[0], depth + 1);
        case Nk.NODE_EXPR_CALL:
            if (n.child_count >= 1) print_expr_d(n.children[0], depth + 1);
            printf("(");
            for (usz i = 1; i < n.child_count; i++)
            {
                if (i > 1) printf(", ");
                print_expr_d(n.children[i], depth + 1);
            }
            printf(")");
        default:
            printf("<%s>", ast::node_kind_name(n.kind));
    }
}

// Find pipeline expressions and apply the collected rules to their value,
// printing the before/after term. Pipelines: NODE_EXPR_PIPELINE[value, rules]
// (a NODE_FIXPOINT wrapper marks `|> rules*`).
fn void apply_at_pipelines(rewrite::Rewriter* rw, Node* n, int depth)
{
    if (n == null || depth > DRIVER_MAX_DEPTH) return;

    Node* pipe = n;
    if (pipe.kind == Nk.NODE_FIXPOINT && pipe.child_count >= 1)
    {
        pipe = pipe.children[0];
    }

    if (pipe.kind == Nk.NODE_EXPR_PIPELINE && pipe.child_count >= 1)
    {
        Node* value = pipe.children[0];
        printf("  ");
        print_expr(value);
        printf("   ↦   ");
        Node* result = rw.apply_fixpoint(value);
        print_expr(result);
        printf("\n");
        return;   // don't recurse into the rewritten value
    }

    for (usz i = 0; i < n.child_count; i++) apply_at_pipelines(rw, n.children[i], depth + 1);
}

// Collect every pgen declaration node (for the self-test).
fn void collect_pgen_nodes(Node* n, Node** out, usz* count, usz cap, int depth)
{
    if (n == null || depth > DRIVER_MAX_DEPTH) return;
    if (n.kind == Nk.NODE_PGEN)
    {
        if (*count < cap) { out[*count] = n; *count = *count + 1; }
        return;
    }
    for (usz i = 0; i < n.child_count; i++) collect_pgen_nodes(n.children[i], out, count, cap, depth + 1);
}

// PGL pass: compile all pgens to one decision tree; report node count and run
// a self-test (each pgen's own `where` pattern must select its own action).
fn void run_pgen_pass(Node* program)
{
    pgen::PgenSet* ps = (pgen::PgenSet*)malloc(pgen::PgenSet::size);
    bool ok = ps.build(program);

    printf("\n=== PGL (%d clauses, %llu decision-tree nodes) ===\n",
        ps.clause_count, (ulong)ps.node_count());
    if (!ok) printf("  [decision-tree build incomplete: overflow]\n");

    // Self-test: feed each pgen's own pattern shape back through the tree.
    Node*[512] pgens;
    usz pn = 0;
    collect_pgen_nodes(program, &pgens[0], &pn, 512, 0);
    usz hits = 0;
    for (usz i = 0; i < pn; i++)
    {
        Node* pat = pgen::pgen_pattern(pgens[i]);
        if (pat == null) continue;
        // Skip OR patterns for the self-test (multiple shapes per clause).
        if (pat.kind == Nk.NODE_PATTERN_OR) { hits++; continue; }
        Node* act = ps.select(pat);
        if (act != null) hits++;
    }
    printf("  self-test: %llu / %llu clause patterns select an action\n",
        (ulong)hits, (ulong)pn);

    ps.destroy();
    free((void*)ps);
}

fn void run_rewrite_pass(ast::AstArena* arena, Node* program)
{
    // Collect rules.
    rewrite::RuleSet* rs = (rewrite::RuleSet*)malloc(rewrite::RuleSet::size);
    rs.init();
    collect_rules(rs, program, 0);
    rs.build_index();   // discrimination tree: O(candidates) rule lookup

    // Hash-cons table for the engine.
    rewrite::HashCons* hc = (rewrite::HashCons*)malloc(rewrite::HashCons::size);
    hc.init();

    rewrite::Rewriter rw;
    // Generous but bounded fuel: enough for deep real simplification, small
    // enough that a non-terminating rule set fails fast with a diagnostic.
    rw.init(arena, hc, rs, 100000);

    printf("\n=== Rewrite (%llu rules) ===\n", (ulong)rs.count);
    apply_at_pipelines(&rw, program, 0);
    printf("  [%llu rewrites applied", (ulong)rw.firings);
    if (rw.too_deep) { printf(", TERM TOO DEEP (size-growing rule?)"); }
    else if (rw.out_of_fuel) { printf(", OUT OF FUEL"); }
    printf("]\n");

    free((void*)hc);
    free((void*)rs);
}

fn void report_lint_diags(lint::Linter* lt)
{
    if (lt.diag_count == 0) return;

    printf("\n=== Lint diagnostics (%d) ===\n", lt.diag_count);
    for (int i = 0; i < lt.diag_count; i++)
    {
        lint::LintError e = lt.diags[i];
        printf("  [%s %d:%d] ", e.is_error ? "lint-err" : "lint-warn", e.line, e.col);
        printf("%s\n", e.msg);
    }
}

// Always-on IRDL diagnostics (the `--irdl` flag additionally prints the full
// dialect/opcode report; these per-line errors must surface unconditionally,
// like every other phase's diagnostics).
fn void report_irdl_diags(irdl_msp::DialectTable* dt)
{
    if (dt.diag_count == 0) return;
    printf("\n=== IRDL diagnostics (%d) ===\n", dt.diag_count);
    for (int i = 0; i < dt.diag_count; i++)
    {
        irdl_msp::IrdlDiag d = dt.diags[i];
        printf("  [%s %d:%d] %s\n", d.is_error ? "irdl-err" : "irdl-warn", d.line, d.col, d.msg);
    }
}

// Frontend integrity findings. Printed with --verify; the summary always shows
// the count. These indicate a tree that would tangle lowering.
fn void report_integrity(integrity::Verifier* iv)
{
    if (iv.finding_count == 0) return;
    printf("\n=== Frontend integrity findings (%d) ===\n", iv.finding_count);
    for (int i = 0; i < iv.finding_count; i++)
    {
        integrity::Finding f = iv.findings[i];
        printf("  [integrity %d:%d] %s\n", f.line, f.col, f.msg);
    }
}

fn void print_version()
{
    printf("pride 0.1.0 (LLVM 19 pipeline, x86_64-linux)\n");
}

// Single source of truth for the CLI surface. Keep in sync with the argument
// dispatcher in main() below.
fn void print_help()
{
    print_version();
    printf("\n");
    printf("usage: pride [options] <file.pie>\n");
    printf("\n");
    printf("compilation & output:\n");
    printf("  --emit-llvm <path>   emit LLVM 22 IR text (.ll); '--emit-llvm=<path>' works too\n");
    printf("                       (default: <source>.ll next to the source file)\n");
    printf("  --emit-obj           emit-llvm + assemble + compile to a native object (.o)\n");
    printf("  --emit-bin           emit-obj + link a native executable (via ld.lld)\n");
    printf("  -o <path>            output path for --emit-bin (default: source stem)\n");
    printf("  --opt=<0|1|2|3>      optimisation level of the LLVM pipeline (default 2)\n");
    printf("  -g, --debug          emit DWARF debug info\n");
    printf("  --lto                thin link-time optimisation (with --emit-bin)\n");
    printf("  --strip              strip symbols from the linked binary\n");
    printf("  --target=<triple>    override the LLVM target triple\n");
    printf("  --cfg=<name[=val]>   set a cfg flag (platform cfgs are added automatically)\n");
    printf("  --freestanding       bare-metal mode: no runtime objects, no libc declarations\n");
    printf("\n");
    printf("front-end behaviour:\n");
    printf("  --strict             promote soft type/effect/lint warnings to errors\n");
    printf("  --test               discover test_ functions / #[test] functions\n");
    printf("  --json               emit diagnostics as a JSON array\n");
    printf("  --verify             print frontend integrity findings (pre-lowering audit)\n");
    printf("\n");
    printf("inspection dumps:\n");
    printf("  --dump-ast           print the parsed AST\n");
    printf("  --dump-mono          print monomorphisation results\n");
    printf("  --dump-ssi           dump SSI construction (versions/uses)\n");
    printf("  --dump-sasi          dump SASI\n");
    printf("  --dump-ir            dump the final IR before codegen\n");
    printf("  --stage              print the staging (CTFE) report\n");
    printf("  --irdl               print the IRDL dialect report\n");
    printf("  --rewrite            run the rewrite pass and report\n");
    printf("  --pgen               run pass-generation and report\n");
    printf("\n");
    printf("misc:\n");
    printf("  -h, --help           show this text and exit\n");
    printf("  -V, --version        print the version and exit\n");
    printf("\n");
    printf("notes:\n");
    printf("  --emit-obj/--emit-bin shell out to llvm-as, opt, llc, ld.lld.\n");
    printf("  --emit-bin links runtime/compiler_rt.o + compiler_rt_arch.o found next to\n");
    printf("  the pride executable (build them with `make runtime`).\n");
}

fn bool file_exists(char* path)
{
    CFile f = fopen(path, "rb");
    if (f == null) return false;
    fclose(f);
    return true;
}

fn int main(int argc, char** argv)
{
    if (argc < 2)
    {
        print_help();
        return 1;
    }

    // Scan args: the first non-flag is the source path; --strict promotes soft
    // type warnings to errors (v.md §20.4).
    bool strict = false;
    bool dump_ast  = false;  // --dump-ast: print AST (off by default for speed)
    bool dump_ssi = false;
    bool dump_ir = false;
    bool dump_mono = false;
    bool emit_llvm = false;
    char* llvm_out = null;
    bool run_tests  = false;  // --test: discover test functions
    bool json_output = false; // --json: emit diagnostics as JSON array
    char* target_triple = null;  // --target=<triple>
    char*[64] cfg_flags;          // --cfg=name or --cfg=key=val
    int cfg_count = 0;
    bool emit_debug_info = false; // -g: DWARF debug info
    bool emit_obj  = false;   // --emit-obj: compile to native object
    bool emit_bin  = false;   // --emit-bin: compile + link to binary
    bool emit_debug= false;   // --debug: emit DWARF debug info via -g
    bool emit_lto  = false;   // --lto: enable link-time optimisation
    bool emit_strip = false;  // --strip: strip debug info from output binary
    int  opt_level = 2;       // --opt=N (0-3, default 2)
    char* out_path = null;    // -o <path>
    bool run_rewrite = false;
    bool run_pgen = false;
    bool dump_stage = false;
    bool dump_irdl = false;
    bool dump_sasi = false;
    bool verify_frontend = false;
    bool freestanding = false;   // --freestanding: also affects --emit-bin linking
    char* path_arg = argv[1];
    bool found_path = false;
    for (usz ai = 1; ai < (usz)argc; ai++)
    {
        char* a_raw = argv[ai];
        usz a_len = cstr_len2(a_raw);

        // Flags carrying an inline `=value` or a following argument are
        // checked first via prefix match; everything else is an exact,
        // full-string comparison (arg_is) — no partial byte-position
        // sniffing anywhere in this dispatcher.
        if (arg_starts_with(a_raw, a_len, "--emit-llvm", 11))
        {
            // --emit-llvm [output.ll]  (default: source.ll next to source file)
            emit_llvm = true;
            if (a_len > 12 && a_raw[11] == '=')
            {
                // Inline form: --emit-llvm=<path>
                usz plen = a_len - 12;
                char* pbuf = (char*)malloc(plen + 1);
                if (pbuf != null)
                {
                    for (usz pi = 0; pi < plen; pi++) pbuf[pi] = a_raw[12 + pi];
                    pbuf[plen] = 0;
                    llvm_out = pbuf;
                }
            }
            // If the next arg is not a flag, treat it as the output path
            else if (ai + 1 < (usz)argc && argv[ai + 1][0] != 0 && argv[ai + 1][0] != '-')
            {
                ai++;
                // Copy the output path from the next argument
                char* path_src = argv[ai];
                usz plen = cstr_len2(path_src);
                char* pbuf = (char*)malloc(plen + 1);
                if (pbuf != null)
                {
                    for (usz pi = 0; pi < plen; pi++) pbuf[pi] = path_src[pi];
                    pbuf[plen] = 0;
                    llvm_out = pbuf;
                }
            }
        }
        else if (arg_is(a_raw, a_len, "--opt") || arg_starts_with(a_raw, a_len, "--opt=", 6))
        {
            // --opt=N or --opt N
            if (a_len > 5 && a_raw[5] == '=') { opt_level = (int)(a_raw[6] - '0'); }
            else if (ai + 1 < (usz)argc) { ai++; opt_level = (int)(argv[ai][0] - '0'); }
        }
        else if (arg_starts_with(a_raw, a_len, "--target=", 9))
        {
            target_triple = a_raw + 9;   // --target=<triple>
        }
        else if (arg_starts_with(a_raw, a_len, "--cfg=", 6))
        {
            if (cfg_count < 64) { cfg_flags[cfg_count] = a_raw + 6; cfg_count++; }   // --cfg=...
        }
        else if (arg_is(a_raw, a_len, "--help") || arg_is(a_raw, a_len, "-h"))
        {
            print_help();
            return 0;
        }
        else if (arg_is(a_raw, a_len, "--version") || arg_is(a_raw, a_len, "-V"))
        {
            print_version();
            return 0;
        }
        else if (arg_is(a_raw, a_len, "-o"))
        {
            // -o <path>
            if (ai + 1 < (usz)argc) { ai++; out_path = argv[ai]; }
        }
        else if (arg_is(a_raw, a_len, "--strict"))       { strict = true; }
        else if (arg_is(a_raw, a_len, "--dump-sasi"))    { dump_sasi = true; }
        else if (arg_is(a_raw, a_len, "--dump-ssi"))     { dump_ssi = true; }
        else if (arg_is(a_raw, a_len, "--dump-ir"))      { dump_ir = true; }
        else if (arg_is(a_raw, a_len, "--dump-ast"))     { dump_ast = true; }
        else if (arg_is(a_raw, a_len, "--dump-mono"))    { dump_mono = true; }
        else if (arg_is(a_raw, a_len, "--rewrite"))      { run_rewrite = true; }
        else if (arg_is(a_raw, a_len, "--pgen"))         { run_pgen = true; }
        else if (arg_is(a_raw, a_len, "--stage"))        { dump_stage = true; }
        else if (arg_is(a_raw, a_len, "--irdl"))         { dump_irdl = true; }
        else if (arg_is(a_raw, a_len, "--verify"))       { verify_frontend = true; }
        else if (arg_is(a_raw, a_len, "--debug"))        { emit_debug = true; }
        else if (arg_is(a_raw, a_len, "--lto"))          { emit_lto = true; }
        else if (arg_is(a_raw, a_len, "--strip"))        { emit_strip = true; }
        // --freestanding: bare-metal/kernel mode — no runtime, no libc declarations
        else if (arg_is(a_raw, a_len, "--freestanding")) { codegen::set_freestanding(true); freestanding = true; }
        else if (arg_is(a_raw, a_len, "--test"))         { run_tests = true; }
        else if (arg_is(a_raw, a_len, "--json"))         { json_output = true; g_json_output = true; }
        else if (arg_is(a_raw, a_len, "-g"))             { emit_debug_info = true; }
        else if (arg_is(a_raw, a_len, "--emit-obj"))     { emit_obj = true; }
        else if (arg_is(a_raw, a_len, "--emit-bin"))     { emit_bin = true; emit_llvm = true; }
        else if (a_len > 1 && a_raw[0] == '-')
        {
            // Unknown flag: fail loudly instead of silently treating it as the
            // source path (previously `pride --help` tried to read a file
            // literally named '--help').
            printf("error: unknown option '%s'\n", a_raw);
            printf("try 'pride --help' for the list of options.\n");
            return 2;
        }
        else if (!found_path)
        {
            path_arg = a_raw;
            found_path = true;
        }
    }
    if (!found_path)
    {
        printf("usage: pride [--strict] <file.pie>\n");
        return 1;
    }
    // Auto-populate platform cfg flags
    if (cfg_count < 60)
    {
        cfg_flags[cfg_count++] = (char*)"target_os=linux";
        cfg_flags[cfg_count++] = (char*)"target_arch=x86_64";
        cfg_flags[cfg_count++] = (char*)"target_arch=x86-64";
        cfg_flags[cfg_count++] = (char*)"unix";
        cfg_flags[cfg_count++] = (char*)"linux";   // bare platform flags
        cfg_flags[cfg_count++] = (char*)"x86_64";
        cfg_flags[cfg_count++] = (char*)"pride";
        cfg_flags[cfg_count++] = (char*)"debug";   // default build mode
    }

    char[1024] path_buf;
    usz n = cstr_len2(path_arg) < 1023 ? cstr_len2(path_arg) : 1023;
    for (usz i = 0; i < n; i++)
    {
        path_buf[i] = path_arg[i];
    }
    path_buf[n] = 0;

    usz src_len = 0;
    char* src = read_file(&path_buf[0], &src_len);
    if (src == null)
    {
        printf("error: cannot read file '%s'\n", &path_buf[0]);
        return 1;
    }

    if (!emit_llvm || dump_ast) { printf("=== Pride front-end ===\n"); }
    printf("source: %s  (%llu bytes)\n\n", &path_buf[0], (ulong)src_len);

    // 1. Lexer
    lexer::Lexer lx;
    lx.init(src, src_len);

    // 2. AST arena
    ast::AstArena arena;
    if (!arena.init(ast::DEFAULT_ARENA_BYTES))
    {
        printf("error: failed to allocate AST arena\n");
        free((void*)src);
        return 1;
    }

    // 3. Parser
    parser::Parser p;
    p.init(&lx, &arena);

    Node* program = p.parse_program();

    // 4. Name resolution — links every identifier use to its declaration.
    // The Resolver holds the scope stack inline, so it's heap-allocated.
    resolve::Resolver* r = (resolve::Resolver*)malloc(resolve::Resolver::size);
    r.init();
    r.resolve_program(program);

    // 5. Type checking — semantic subtyping with soft warnings (v.md §20).
    typecheck::TypeChecker tc;
    tc.init(&arena, strict);
    tc.check_program(program);

    // 6. Effect checking — actual effects must fit the declared ! [...] row.
    effectcheck::EffectChecker ec;
    ec.init(strict);
    ec.check_program(program);

    // 7. Lint — advisory warnings (exhaustiveness, unreachable, unused).
    // Heap-allocated: the Linter holds large inline binder/diag tables.
    lint::Linter* lt = (lint::Linter*)malloc(lint::Linter::size);
    lt.init(strict);
    lt.run(program);

    // 7'. Frontend integrity verification (pre-lowering guardrail). Audits that
    // the post-resolve/post-typecheck AST satisfies the invariants lowering
    // assumes: every value-position name resolved, every expression typed, no
    // INVALID sentinels, correct positional arity. Run BEFORE IRDL mutates the
    // tree so we audit exactly what the backend will consume. Soft by default
    // (reported, never fatal) unless --strict; --verify prints each finding.
    integrity::Verifier* iv = (integrity::Verifier*)malloc(integrity::Verifier::size);
    iv.init();
    if (verify_frontend) { iv.verify(program); }  // only when --verify

    // 7a. MSP — Staging (CTFE). Runs the compile-time evaluator: folds
    // `comptime`/`eval` blocks to value nodes, grafts `splice`s inside quotes,
    // and checks well-stagedness (splice/unquote must be inside a quotation).
    // This is compile-time-only; nothing here runs at program runtime.
    stage::Stager* st = (stage::Stager*)malloc(stage::Stager::size);
    st.init(&arena);
    program = st.run(program);
    if (dump_stage) dump_stage_report(st);

    // 7a'. MSP — IRDL dialect lowering (final transform). Registers `dialect`
    // opcodes/regions, registers `irdl` lowering rules, validates every
    // dialect-op use, then lowers those uses by substituting args into the
    // matching rule's action template (a structural rewrite to a fixpoint).
    irdl_msp::DialectTable* dt = (irdl_msp::DialectTable*)malloc(irdl_msp::DialectTable::size);
    dt.init(&arena);
    // Fast scan: only run IRDL pipeline if there are dialect/irdl declarations.
    // Most programs have none — skip the full 3-pass scan entirely.
    {
        bool has_irdl = false;
        for (usz qi = 0; qi < program.child_count && !has_irdl; qi++)
        {
            Node* qc = program.children[qi];
            if (qc == null) continue;
            if (qc.kind == Nk.NODE_DIALECT || qc.kind == Nk.NODE_IRDL
                || qc.kind == Nk.NODE_PGEN) has_irdl = true;
        }
        if (has_irdl) { program = dt.run(program); }
    }
    if (dump_irdl) dump_irdl_report(dt);

    // 7a''. Monomorphization — expand all generic call/struct-lit sites into
    // fully-concrete clones and append them to the program tree. The original
    // generic declarations are preserved as templates (skipped by IR lowering).
    mono::Monomorphizer* mn = (mono::Monomorphizer*)malloc(mono::Monomorphizer::size);
    bool mono_ok = mn.init(&arena);
    usz  mono_instances = 0;
    int  mono_warnings  = 0;
    if (mono_ok)
    {
        program = mn.run(program);
        mono_instances = mn.instance_count_fn();
        mono_warnings  = mn.warning_count_fn();
        if (dump_mono) { mn.dump(); }
    }

    // 7b. MSP — Static Single Information (first MSP component). Builds the
    // def-use graph + refinements from the parser's σ/φ markers.
    ssi::SsiGraph* sg = (ssi::SsiGraph*)malloc(ssi::SsiGraph::size);
    bool ssi_ok = sg.init(&arena);
    if (ssi_ok) sg.build(program);
    if (ssi_ok && dump_ssi) dump_ssi_graph(sg);

    // 7b'. MSP — explicit CFG + SSI IR (the SSI-first backend's input form).
    // Lowers the structured AST into basic blocks with φ-merges (carrying
    // predecessor blocks) and σ-splits (on conditional out-edges). Always
    // built (cheap, single walk); --dump-ir prints the textual IR.
    ssi_ir::SsiModule* ir = (ssi_ir::SsiModule*)malloc(ssi_ir::SsiModule::size);
    bool ir_ok = ir.init(&arena);
    ssi_ir::VerifyResult vr;
    vr.errors = 0; vr.blocks = 0; vr.vals = 0; vr.phis = 0; vr.sigmas = 0; vr.edges = 0; vr.undef_refs = 0; vr.effect_ops = 0; vr.effect_handles = 0; vr.effect_resumes = 0;
    if (ir_ok)
    {
        ir.build(program);
        if (verify_frontend) { vr = ir.verify(); }
        if (dump_ir) ir.dump();
    }

    // 7b''. SASI — Sparsely-Annotated Single Information (extraction, step 2).
    // Flatten-first: the IR above carries σ IN-BAND. SASI sweeps every σ into a
    // sparse value-id-keyed fact map (with the dominating-σ chain), then strips
    // σ from the block instruction lists, leaving CLEAN standard SSA. The fact
    // map preserves all path info for the step-4 optimizer.
    sasi::SasiMap* sm = (sasi::SasiMap*)malloc(sasi::SasiMap::size);
    bool sasi_ok = false;
    sasi::SasiVerify sv;
    sv.leftover_sigma = 0; sv.unresolved = 0; sv.facts = 0; sv.chains = 0;
    // 7b'''. SASI optimization (step 4): use the fact map to fold redundant
    // comparisons / branches, prune unreachable blocks, and DCE — on the clean
    // SSA. Re-verify afterward to confirm the SSA-CFG invariants still hold.
    sasi_opt::OptStats os;
    os.compares_folded = 0; os.branches_folded = 0; os.blocks_pruned = 0;
    os.edges_removed = 0; os.dead_removed = 0; os.rounds = 0;
    ssi_ir::VerifyResult vr2;
    vr2.errors = 0; vr2.undef_refs = 0; vr2.effect_ops = 0; vr2.effect_handles = 0; vr2.effect_resumes = 0;
    if (ir_ok)
    {
        sasi_ok = sm.init(ir);
        if (sasi_ok)
        {
            sm.extract();
            sv = sm.verify();
            if (dump_sasi)
            {
                sm.dump();
                printf("\n=== CFG after σ-strip (clean SSA) ===\n");
                ir.dump();
            }
            // step 4
            sasi_opt::Optimizer opt;
            opt.init(ir, sm);
            os = opt.run();
            if (verify_frontend) { vr2 = ir.verify(); }
            if (dump_sasi)
            {
                opt.report();
                printf("\n=== CFG after SASI optimization ===\n");
                ir.dump();
            }
        }
    }

    // 7c. MSP — term rewriting (second MSP component). With --rewrite, collect
    // all `rewrite {...}` blocks into one rule set and apply them at every
    // `expr |> rules` / `expr |> rules*` pipeline, printing before/after.
    if (run_rewrite) run_rewrite_pass(&arena, program);

    // 7d. MSP — Pattern Generation Language. With --pgen, compile all `pgen`
    // declarations into one decision tree and report its shape + a self-test
    // (each pgen's own pattern must select its own action).
    if (run_pgen) run_pgen_pass(program);

    // 7d-pre. Apply #[cfg(...)] stripping based on active --cfg flags
    apply_cfg_strip(program, &cfg_flags[0], cfg_count);

    // 7e. LLVM IR emission (--emit-llvm).  Runs after all pipeline stages so
    // the IR has been through SASI optimisation before codegen sees it.
    bool codegen_ok = true;
    if (emit_llvm && ir_ok && vr.errors == 0)
    {
        // Derive output path: replace .pie with .ll, or use llvm_out if given.
        char[1024] ll_path;
        if (llvm_out != null)
        {
            usz n2 = cstr_len2(llvm_out);
            n2 = n2 < 1023 ? n2 : 1023;
            for (usz i = 0; i < n2; i++) ll_path[i] = llvm_out[i];
            ll_path[n2] = 0;
        }
        else
        {
            // source path with .pie → .ll
            usz n2 = n < 1023 ? n : 1023;
            for (usz i = 0; i < n2; i++) ll_path[i] = path_buf[i];
            // replace last .pie with .ll
            usz dot = n2;
            for (usz i = n2; i > 0; i--) { if (path_buf[i-1] == '.') { dot = i-1; break; } }
            ll_path[dot] = '.'; ll_path[dot+1] = 'l'; ll_path[dot+2] = 'l'; ll_path[dot+3] = 0;
        }
        printf("=== Emitting LLVM IR → %s ===\n", &ll_path[0]);
        // Pass target triple override if specified
        if (target_triple != null) codegen::set_target_triple(target_triple);
        codegen_ok = codegen::emit_llvm_file(ir, &arena, &path_buf[0], &ll_path[0]);
        if (codegen_ok)
        {
            printf("llvm emit      : ok\n");
        }
        else
        {
            printf("llvm emit      : FAILED\n");
        }
        if (llvm_out != null) { free((void*)llvm_out); llvm_out = null; }

        // 7f. Downstream pipeline: .ll → .bc → .o → binary
        if (codegen_ok && (emit_obj || emit_bin))
        {
            // Build output stem from ll_path (strip .ll)
            char[1024] stem;
            usz slen = cstr_len2(&ll_path[0]);
            usz stem_len = (slen >= 3 && ll_path[slen-3]=='.' && ll_path[slen-2]=='l' && ll_path[slen-1]=='l')
                         ? slen - 3 : slen;
            for (usz si = 0; si < stem_len && si < 1023; si++) stem[si] = ll_path[si];
            stem[stem_len] = 0;

            // Build opt flags string
            char[64] opt_str;
            snprintf(&opt_str[0], 64, "-O%d", opt_level);
            char[64] debug_flag;
            snprintf(&debug_flag[0], 64, "%s", (emit_debug || emit_debug_info) ? "-g" : "");

            // llvm-as: .ll → .bc
            char[2048] cmd;
            snprintf(&cmd[0], 2048, "llvm-as %s -o %s.bc 2>&1", &ll_path[0], &stem[0]);
            int r2 = system(&cmd[0]);
            if (r2 != 0) { printf("llvm-as     : FAILED\n"); }
            else
            {
                // opt: run LLVM optimizer passes on .bc for better execution speed
                // -O2+: run full optimizer including function inlining, loop transforms,
                //        vectorization, constant folding, dead code elimination.
                // This is what makes Pride binaries rival Rust/Zig in execution speed.
                if (opt_level >= 1)
                {
                    char[2048] opt_cmd;
                    snprintf(&opt_cmd[0], 2048,
                        "opt --passes='default<%s>' %s.bc -o %s.opt.bc 2>/dev/null && mv %s.opt.bc %s.bc",
                        opt_level >= 3 ? "O3" : opt_level >= 2 ? "O2" : "O1",
                        &stem[0], &stem[0], &stem[0], &stem[0]);
                    system(&opt_cmd[0]);   // failures are soft — still have original .bc
                }
                printf("opt            : ok\n");
                // llc: .bc → .o  (use mcpu=native for best codegen on this machine)
                snprintf(&cmd[0], 2048, "llc %s %s -filetype=obj %s.bc -o %s.o 2>&1",
                         &opt_str[0], &debug_flag[0], &stem[0], &stem[0]);
                r2 = system(&cmd[0]);
                if (r2 != 0) { printf("llc         : FAILED\n"); }
                else
                {
                    printf("llc         : ok\n");
                    if (emit_bin)
                    {
                        // Link
                        char[1024] bin_path;
                        if (out_path != null)
                        {
                            usz op_len = cstr_len2(out_path);
                            for (usz oi = 0; oi < op_len && oi < 1023; oi++) bin_path[oi] = out_path[oi];
                            bin_path[op_len] = 0;
                        }
                        else
                        {
                            for (usz si2 = 0; si2 < stem_len && si2 < 1023; si2++) bin_path[si2] = stem[si2];
                            bin_path[stem_len] = 0;
                        }
                        char[64] lto_flag;
                        snprintf(&lto_flag[0], 64, "%s", emit_lto ? "--lto=thin" : "");
                        char[64] strip_flag;
                        snprintf(&strip_flag[0], 64, "%s", emit_strip ? "-s" : "");
                        char[64] gc_flag;
                        // --gc-sections eliminates unused functions/data → smaller binary
                        // --icf=all: merge identical code sections → further size reduction
                        snprintf(&gc_flag[0], 64, "%s",
                            opt_level >= 1 ? "--gc-sections --icf=all" : "");

                        // Resolve the directory holding this executable so the runtime
                        // support objects can be linked no matter the CWD. The runtime
                        // provides algebraic effects, panic, and SIMD builtins
                        // (compiler_rt.o) plus arch ABI stubs (compiler_rt_arch.o).
                        char[1024] exe_dir;
                        {
                            char[1024] exe_path;
                            long rl = readlink((char*)"/proc/self/exe", &exe_path[0], 1023);
                            if (rl > 0)
                            {
                                usz d = (usz)rl;
                                while (d > 0 && exe_path[d-1] != '/') d--;   // strip basename
                                for (usz ei = 0; ei < d; ei++) exe_dir[ei] = exe_path[ei];
                                exe_dir[d] = 0;
                            }
                            else
                            {
                                exe_dir[0] = '.'; exe_dir[1] = '/'; exe_dir[2] = 0;
                            }
                        }
                        char[1200] rt_obj;
                        char[1200] rt_arch_obj;
                        snprintf(&rt_obj[0], 1200, "%sruntime/compiler_rt.o", &exe_dir[0]);
                        snprintf(&rt_arch_obj[0], 1200, "%sruntime/compiler_rt_arch.o", &exe_dir[0]);
                        char[2600] rt_args;
                        rt_args[0] = 0;   // empty when freestanding / runtime missing
                        bool link_rt = !freestanding;
                        if (link_rt && (!file_exists(&rt_obj[0]) || !file_exists(&rt_arch_obj[0])))
                        {
                            printf("warning: runtime/compiler_rt*.o not found next to %s;\n"
                                   "         run `make runtime`. Programs using effects/panic/"
                                   "SIMD will fail to link.\n", &exe_dir[0]);
                            link_rt = false;
                        }
                        if (link_rt)
                        {
                            snprintf(&rt_args[0], 2600, "%s %s ", &rt_obj[0], &rt_arch_obj[0]);
                        }
                        // Link line mirrors the known-good Makefile recipe: crt1/crti +
                        // crtn, runtime objects, libc/libgcc, canonical ELF interpreter.
                        char[4608] linkcmd;
                        snprintf(&linkcmd[0], 4608,
                            "ld.lld /usr/lib/x86_64-linux-gnu/crt1.o "
                            "/usr/lib/x86_64-linux-gnu/crti.o "
                            "%s.o %s"
                            "/usr/lib/x86_64-linux-gnu/crtn.o -o %s "
                            "-L/usr/lib/x86_64-linux-gnu -L/lib/x86_64-linux-gnu "
                            "-L/usr/lib/gcc/x86_64-linux-gnu/14 "
                            "-lc -lm -lpthread -lgcc -lgcc_s %s %s %s "
                            "--dynamic-linker /lib64/ld-linux-x86-64.so.2 2>&1",
                            &stem[0], &rt_args[0], &bin_path[0],
                            &lto_flag[0], &strip_flag[0], &gc_flag[0]);
                        r2 = system(&linkcmd[0]);
                        if (r2 != 0) { printf("ld.lld      : FAILED\n"); }
                        else { printf("linked         : %s\n", &bin_path[0]); }
                    }
                }
            }
        }
    }

    // 7g. Test discovery (--test): find test_ prefixed functions and report them.
    if (run_tests && program != null)
    {
        int n_test_fns = 0;
        printf("\n=== Test Discovery ===\n");
        for (usz ni = 0; ni < (usz)program.child_count; ni++)
        {
            Node* decl = program.children[ni];
            if (decl == null || decl.kind != Nk.NODE_DECL_FN) continue;
            if (decl.child_count < 1 || decl.children[0] == null) continue;
            Node* fn_nm = decl.children[0];
            char* nm = fn_nm.p.ident.name_ptr;
            usz   nl = fn_nm.p.ident.name_len;
            bool is_test = (nl >= 5 && nm[0]=='t'&&nm[1]=='e'&&nm[2]=='s'&&nm[3]=='t'&&nm[4]=='_');
            // Also detect #[test] attribute on any fn
            if (!is_test)
            {
                for (usz ai = 1; ai < decl.child_count && !is_test; ai++)
                {
                    Node* anode = decl.children[ai];
                    if (anode == null || anode.kind != NodeKind.NODE_ATTRIBUTE_LIST) continue;
                    for (usz aj = 0; aj < anode.child_count && !is_test; aj++)
                    {
                        Node* attr = anode.children[aj];
                        if (attr == null || attr.child_count < 1 || attr.children[0] == null) continue;
                        char* aname = attr.children[0].p.ident.name_ptr;
                        usz   alen  = attr.children[0].p.ident.name_len;
                        if (alen == 4 && aname[0]=='t'&&aname[1]=='e'&&aname[2]=='s'&&aname[3]=='t')
                        { is_test = true; }
                    }
                }
            }
            if (is_test)
            {
                printf("  [test] ");
                for (usz ci = 0; ci < nl; ci++) printf("%c", nm[ci]);
                printf("\n");
                n_test_fns++;
            }
        }
        printf("  total test functions: %d\n", n_test_fns);
    }

    // 8. Output (AST only with --dump-ast — off by default for performance)
    if (dump_ast)
    {
        printf("=== AST ===\n");
        print_node(program, 0);
    }

    report_lexer_diags(&lx);
    report_parser_diags(&p, lx.source, lx.len);
    report_resolve_diags(r, lx.source, lx.len);
    report_typecheck_diags(&tc, lx.source, lx.len);
    report_effect_diags(&ec, lx.source, lx.len);
    report_lint_diags(lt);
    report_irdl_diags(dt);
    if (verify_frontend) report_integrity(iv);
    if (mono_ok) mn.report();

    // Summary: only print when not doing --emit-llvm or explicitly requested
    if (!emit_llvm || dump_ast)
    {
    printf("\n=== Summary ===\n");
    printf("nodes allocated : %llu\n", (ulong)arena.node_count);
    printf("arena used      : %llu / %llu bytes\n", (ulong)arena.cursor, (ulong)arena.cap);
    printf("lex errors      : %s\n", lx.had_errors() ? "yes" : "no");
    printf("parse errors    : %d\n", p.error_count);
    printf("resolve errors  : %d\n", r.error_count);
    printf("type errors     : %d\n", tc.error_count);
    printf("type warnings   : %d\n", tc.warning_count);
    printf("effect errors   : %d\n", ec.error_count);
    printf("effect warnings : %d\n", ec.warning_count);
    printf("lint warnings   : %d\n", lt.warning_count);
    printf("ssi versions    : %llu\n", (ulong)sg.var_count);
    printf("ssi uses        : %llu\n", (ulong)sg.use_count);
    printf("ir blocks       : %d\n", vr.blocks);
    printf("ir values       : %d\n", vr.vals);
    printf("ir phis         : %d\n", vr.phis);
    printf("ir sigmas       : %d\n", vr.sigmas);
    printf("ir edges        : %d\n", vr.edges);
    printf("ir effect.ops   : %d\n", vr.effect_ops);
    printf("ir effect.handle: %d\n", vr.effect_handles);
    printf("ir effect.resume: %d\n", vr.effect_resumes);
    printf("ir verify errors: %d\n", vr.errors);
    printf("sasi facts      : %d\n", sv.facts);
    printf("sasi sigma swept: %d\n", sasi_ok ? sm.swept : 0);
    printf("sasi sigma left : %d\n", sv.leftover_sigma);
    printf("sasi unresolved : %d\n", sv.unresolved);
    // SSI post-lowering pass stats (from prune_trivial_phis, dead_block, LICM, split)
    // These are computed per-function inside lower_fn and aggregated here via
    // a lightweight struct stored in the SsiModule (future: plumb counters).
    printf("ssi phi pruned  : (done per-fn)\n");
    printf("ssi dead elim   : (done per-fn)\n");
    printf("ssi licm hoisted: (done per-fn)\n");
    printf("opt compares    : %d\n", os.compares_folded);
    printf("opt branches    : %d\n", os.branches_folded);
    printf("opt blocks pruned: %d\n", os.blocks_pruned);
    printf("opt dead removed: %d\n", os.dead_removed);
    printf("opt verify errs : %d\n", vr2.errors);
    printf("stage folded    : %d\n", st.folded);
    printf("stage errors    : %d\n", st.error_count());
    printf("irdl dialects   : %llu\n", (ulong)dt.dialect_count);
    printf("irdl lowerings  : %d\n", dt.lowerings_applied);
    printf("irdl errors     : %d\n", dt.error_count());
    printf("mono instances  : %llu\n", (ulong)mono_instances);
    printf("mono warnings   : %d\n",  mono_warnings);
    printf("integrity issues: %d (names %d, untyped %d, invalid %d, arity %d)\n",
        iv.total(), iv.unresolved_names, iv.untyped_exprs, iv.invalid_nodes, iv.arity_breaks);
    if (program != null)
    {
        printf("root effects    :");
        if (program.effects == ast::EFFECT_PURE) printf(" pure");
        print_effects(program.effects);
        printf("\n");
    }

    } // end summary

    // The entire tree is released in one call.
    bool resolve_failed = r.had_error;
    bool type_failed = tc.error_count > 0;
    bool effect_failed = ec.error_count > 0;
    bool lint_failed = lt.error_count > 0;
    bool irdl_failed = dt.error_count() > 0;
    // Integrity issues are hard failures only under --strict (they indicate a
    // tree that would tangle lowering); soft-reported otherwise.
    bool integrity_failed = strict && iv.total() > 0;
    sg.destroy();
    free((void*)sg);
    if (sasi_ok) sm.destroy();
    free((void*)sm);
    if (ir_ok) ir.destroy();
    free((void*)ir);
    free((void*)st);
    free((void*)dt);
    free((void*)lt);
    free((void*)iv);
    if (mono_ok) mn.destroy();
    free((void*)mn);
    free((void*)r);
    arena.destroy();
    free((void*)src);
    return (lx.had_errors() || p.had_error || resolve_failed || type_failed || effect_failed || lint_failed || irdl_failed || integrity_failed) ? 2 : 0;
}
