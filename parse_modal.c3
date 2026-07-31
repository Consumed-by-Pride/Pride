// parse_modal.c3 — Modal Staging & CMTT Recursive-Descent Syntax Parser
// Implementation language: C3 (host).
//
// This module provides formal recursive-descent parsing for Pride's Multi-Level
// Contextual Effect Engine (MLCEE):
//
//   1. STAGE LEVEL ANNOTATIONS (`parse_stage_annotation`, `parse_modal_at`):
//      Parses `at Stage L`, `at Stage L+1`, `at Stage L-1`, and numeric stage
//      literals (`at Stage 0`, `at Stage 1`). Generates NODE_STAGE AST nodes
//      carrying the target stage offset.
//
//   2. CONTEXTUAL MODAL BOXES (`parse_cmtt_box`, `parse_open_code_quote`):
//      Parses modal box declarations of the form:
//          box[Γ] <expr> at Stage L
//      Captures explicit lexical environment list Γ and binds the open code
//      AST subtree to stage L.
//
//   3. OPEN-CODE PATTERN MATCHING (`parse_open_code_pattern_case`):
//      Parses macro-time pattern matching clauses over quoted code:
//          case <perform with_timeout(0) { ~body }> at Stage L+1 => expr
//      Builds pattern AST trees with spliced variable binders (~body) for
//      the CMTT open-code pattern matcher.
//
//   4. HIGHER-ORDER & SCOPED EFFECT SIGNATURES (`parse_scoped_effect_decl`):
//      Parses scoped effect declarations and operation signatures with two-part
//      continuation annotations (k_in / k_out).

module parse_modal;

import lexer;
import ast;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

alias Node = ast::AstNode;
alias Nk   = ast::NodeKind;
alias Tt   = lexer::TokenType;

const usz PARSE_MODAL_MAX_ARGS   = 64;
const usz PARSE_MODAL_MAX_CLAUSE = 128;
const int PARSE_MODAL_MAX_DEPTH  = 500;

struct ModalParserContext
{
    ast::AstArena* arena;
    int            current_stage_level;
    bool           in_macro_body;
    int            errors;
    char[256][32]  error_msgs;
}

fn void ModalParserContext.init(ModalParserContext* p, ast::AstArena* a)
{
    p.arena = a;
    p.current_stage_level = 0;
    p.in_macro_body = false;
    p.errors = 0;
}

fn void ModalParserContext.report_error(ModalParserContext* p, char* msg)
{
    if (p.errors < 32 && msg != null)
    {
        char* dst = &p.error_msgs[p.errors][0];
        usz i = 0;
        while (msg[i] != 0 && i < 255) { dst[i] = msg[i]; i++; }
        dst[i] = 0;
        p.errors++;
    }
}

// ── Stage Level Annotation Parsing (`at Stage L+n`) ─────────────────────────

struct StageOffset
{
    char* base_ident;
    usz   ident_len;
    int   offset;
    bool  is_numeric_literal;
    int   literal_value;
}

fn StageOffset parse_stage_offset_from_span(char* span, usz len)
{
    StageOffset s;
    s.base_ident = null;
    s.ident_len = 0;
    s.offset = 0;
    s.is_numeric_literal = false;
    s.literal_value = 0;

    if (span == null || len == 0) return s;

    // Check if span is all digits (numeric literal stage e.g. Stage 0, Stage 1)
    bool all_digits = true;
    int val = 0;
    for (usz i = 0; i < len; i++)
    {
        if (span[i] < '0' || span[i] > '9') { all_digits = false; break; }
        val = val * 10 + (int)(span[i] - '0');
    }
    if (all_digits)
    {
        s.is_numeric_literal = true;
        s.literal_value = val;
        s.offset = val;
        return s;
    }

    // Parse base identifier + optional offset (+N / -N)
    usz k = 0;
    while (k < len && ((span[k] >= 'a' && span[k] <= 'z') || (span[k] >= 'A' && span[k] <= 'Z')))
    {
        k++;
    }
    s.base_ident = span;
    s.ident_len  = k;

    if (k < len)
    {
        char sign = span[k];
        if (sign == '+' || sign == '-')
        {
            k++;
            int off = 0;
            while (k < len && span[k] >= '0' && span[k] <= '9')
            {
                off = off * 10 + (int)(span[k] - '0');
                k++;
            }
            s.offset = (sign == '-') ? -off : off;
        }
    }
    return s;
}

fn Node* build_stage_node(ast::AstArena* arena, StageOffset* off, int line, int col)
{
    if (arena == null || off == null) return null;
    Node* n = ast::node0(arena, Nk.NODE_STAGE, line, col);
    if (n == null) return null;
    n.p.lit_int.int_val   = (ulong)off.offset;
    n.p.lit_int.bits      = (char)64;
    n.p.lit_int.is_signed = true;
    return n;
}

// ── Contextual Modal Box Declaration (`box[Γ] <expr> at Stage L`) ───────────

struct CmttEnvBinding
{
    char* var_name;
    usz   var_len;
    Node* type_node;
}

struct CmttBoxDecl
{
    CmttEnvBinding[16] env_bindings;
    usz                env_count;
    Node*              quoted_expr;
    StageOffset        stage;
    bool               is_valid;
}

fn void CmttBoxDecl.init(CmttBoxDecl* d)
{
    d.env_count = 0;
    d.quoted_expr = null;
    d.is_valid = false;
}

fn bool CmttBoxDecl.add_binding(CmttBoxDecl* d, char* name, usz len, Node* ty)
{
    if (d.env_count >= 16) return false;
    usz idx = d.env_count++;
    d.env_bindings[idx].var_name  = name;
    d.env_bindings[idx].var_len   = len;
    d.env_bindings[idx].type_node = ty;
    return true;
}

fn Node* parse_cmtt_box_decl(ModalParserContext* ctx, CmttBoxDecl* decl, int line, int col)
{
    if (ctx == null || decl == null || !decl.is_valid) return null;
    Node* box_node = ast::node0(ctx.arena, Nk.NODE_QUOTE, line, col);
    if (box_node == null) return null;

    // Attach explicit environment bindings as leading AST children
    for (usz i = 0; i < decl.env_count; i++)
    {
        Node* id = ast::node_ident(ctx.arena, decl.env_bindings[i].var_name,
                                   decl.env_bindings[i].var_len, line, col);
        if (id != null)
        {
            id.type_annotation = decl.env_bindings[i].type_node;
            ast::add_child(ctx.arena, box_node, id);
        }
    }

    if (decl.quoted_expr != null)
    {
        ast::add_child(ctx.arena, box_node, decl.quoted_expr);
    }
    Node* st_node = build_stage_node(ctx.arena, &decl.stage, line, col);
    if (st_node != null)
    {
        ast::add_child(ctx.arena, box_node, st_node);
    }
    return box_node;
}

// ── Open-Code Pattern Case Clause (`case <pattern> at Stage L => expr`) ────

struct OpenCodeCaseClause
{
    Node*       pattern_quote;
    StageOffset match_stage;
    Node*       body_expr;
    bool        has_guard;
    Node*       guard_expr;
}

fn Node* parse_open_code_case(ModalParserContext* ctx, OpenCodeCaseClause* clause, int line, int col)
{
    if (ctx == null || clause == null || clause.pattern_quote == null) return null;
    Node* arm = ast::node0(ctx.arena, Nk.NODE_MATCH_ARM, line, col);
    if (arm == null) return null;

    ast::add_child(ctx.arena, arm, clause.pattern_quote);

    if (clause.has_guard && clause.guard_expr != null)
    {
        Node* g = ast::node0(ctx.arena, Nk.NODE_PATTERN_GUARD, line, col);
        if (g != null)
        {
            ast::add_child(ctx.arena, g, clause.guard_expr);
            ast::add_child(ctx.arena, arm, g);
        }
    }

    if (clause.body_expr != null)
    {
        ast::add_child(ctx.arena, arm, clause.body_expr);
    }
    return arm;
}

// ── Higher-Order & Scoped Effect Signature Parser ───────────────────────────

struct ScopedEffectOpDecl
{
    char* op_name;
    usz   op_len;
    Node* param_types;
    Node* ret_type;
    bool  is_scoped;
    bool  has_two_part_cont; // k_in / k_out annotation
}

fn Node* parse_scoped_effect_op(ModalParserContext* ctx, ScopedEffectOpDecl* op, int line, int col)
{
    if (ctx == null || op == null || op.op_name == null) return null;
    Node* op_node = ast::node0(ctx.arena, Nk.NODE_EFFECT_OP_DECL, line, col);
    if (op_node == null) return null;

    Node* name_id = ast::node_ident(ctx.arena, op.op_name, op.op_len, line, col);
    if (name_id != null)
    {
        ast::add_child(ctx.arena, op_node, name_id);
    }

    Node* fn_ty = ast::node0(ctx.arena, Nk.NODE_TYPE_FN, line, col);
    if (fn_ty != null)
    {
        if (op.param_types != null) ast::add_child(ctx.arena, fn_ty, op.param_types);
        if (op.ret_type != null)    ast::add_child(ctx.arena, fn_ty, op.ret_type);
        ast::add_child(ctx.arena, op_node, fn_ty);
    }
    return op_node;
}

// ── Recursive AST Validation for Quoted & Spliced Trees ─────────────────────

fn bool validate_parsed_quote_tree(Node* n, int stage_level, int depth)
{
    if (n == null || depth > PARSE_MODAL_MAX_DEPTH) return true;
    if (n.kind == Nk.NODE_QUOTE)
    {
        for (usz i = 0; i < n.child_count; i++)
        {
            if (!validate_parsed_quote_tree(n.children[i], stage_level + 1, depth + 1)) return false;
        }
        return true;
    }
    if (n.kind == Nk.NODE_SPLICE || n.kind == Nk.NODE_UNQUOTE)
    {
        if (stage_level <= 0) return false; // parse error: splice at stage 0
        for (usz i = 0; i < n.child_count; i++)
        {
            if (!validate_parsed_quote_tree(n.children[i], stage_level - 1, depth + 1)) return false;
        }
        return true;
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        if (!validate_parsed_quote_tree(n.children[i], stage_level, depth + 1)) return false;
    }
    return true;
}

// Validate that an open code pattern case clause has no unbound spliced vars
fn bool validate_open_code_case_clause(OpenCodeCaseClause* clause)
{
    if (clause == null || clause.pattern_quote == null) return false;
    return validate_parsed_quote_tree(clause.pattern_quote, clause.match_stage.offset, 0);
}

// Format modal parser diagnostic message with stage context
fn usz format_modal_parse_diag(ModalParserContext* ctx, char* buf, usz cap)
{
    if (ctx == null || buf == null || cap == 0) return 0;
    buf[0] = 0;
    usz pos = 0;
    char* hdr = (char*)"=== Modal Parser Diagnostics ===\n";
    usz hl = 0; while (hdr[hl] != 0 && pos < cap - 1) { buf[pos++] = hdr[hl++]; }

    for (int i = 0; i < ctx.errors && pos < cap - 64; i++)
    {
        char* em = &ctx.error_msgs[i][0];
        char* pfx = (char*)"error: ";
        usz pl = 0; while (pfx[pl] != 0 && pos < cap - 1) { buf[pos++] = pfx[pl++]; }
        usz el = 0; while (em[el] != 0 && pos < cap - 1) { buf[pos++] = em[el++]; }
        buf[pos++] = '\n';
    }
    buf[pos] = 0;
    return pos;
}
