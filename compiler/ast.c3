// ============================================================================
// ast.c3 — Abstract Syntax Tree for the Pryde compiler
// ----------------------------------------------------------------------------
// Implementation language: C3 (host). Pryde is written in C3; it does NOT
// compile to C3.
//
// A plain, standard AST: every node has exactly one parent (a tree). This
// module defines:
//   - NodeKind   : every node kind the parser can build
//   - AstNode    : a single tree node, with inline metadata + a payload union
//   - AstArena   : a bump-allocated slab so we never free nodes individually
//   - effects    : a u64 bitmask per node, OR-propagated child -> parent
//   - folding    : LitInt op LitInt etc. fold immediately at build time
//
// The parser (parser.c3) calls the node_* constructors here. The driver
// (pryde.c3) walks the resulting tree and prints it.
// ============================================================================

module ast;

import lexer;

// ── libc bindings ────────────────────────────────────────────────────────────
// The arena is heap-backed so the slab size is configurable at runtime.
extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn void* memset(void* dst, int value, usz n);

// ── Effect flags ─────────────────────────────────────────────────────────────
// Effects propagate upward: a parent's mask is the union of its children's.
const ulong EFFECT_PURE   = 0;
const ulong EFFECT_IO     = 1;   // bit 0 — performs I/O
const ulong EFFECT_ALLOC  = 2;   // bit 1 — allocates or frees memory
const ulong EFFECT_UNSAFE = 4;   // bit 2 — unsafe op or inline asm
const ulong EFFECT_UB     = 8;   // bit 3 — may trigger declared UB
const ulong EFFECT_PANIC  = 16;  // bit 4 — may panic

// ── Node flags ───────────────────────────────────────────────────────────────
const uint FLAG_NONE             = 0;
const uint FLAG_MUT              = 1;   // mutable binding / mut ref
const uint FLAG_RANGE_INCLUSIVE  = 2;   // ..= rather than ..
const uint FLAG_FOLDED           = 4;   // produced by constant folding
const uint FLAG_UNCHECKED        = 8;   // inside an `unchecked` region
const uint FLAG_FIXPOINT         = 16;  // pipeline applied to fixpoint (rules*)
const uint FLAG_OPEN_ROW         = 32;  // effect row carries an open tail ..r
const uint FLAG_TYPED            = 64;  // type checker has visited this node
const uint FLAG_USED             = 128; // a binding that is referenced (lint)
const uint FLAG_NORMAL           = 256; // rewrite: this term is in normal form
const uint FLAG_REFUTABLE        = 512; // pattern that may fail to match (e.g. a
                                        // struct pattern over a union variant)
const uint FLAG_EXHAUSTIVE       = 1024;// match/clause-set the type checker has
                                        // proven total (e.g. all union variants)

// ── Node kinds ───────────────────────────────────────────────────────────────
enum NodeKind : int
{
    // Root / structural
    NODE_PROGRAM,
    NODE_INVALID,
    NODE_PARAM,
    NODE_GENERIC_PARAM,
    NODE_WHERE_CLAUSE,
    NODE_ATTRIBUTE_LIST,
    NODE_MODULE_PATH,
    NODE_MATCH_ARM,
    NODE_CLAUSE,            // one Prolog-style fn clause: pattern (,guard) -> body
    NODE_FIELD_DECL,        // a struct/union field:  name : Type
    NODE_FIELD_INIT,        // a struct-literal field: name : value
    NODE_HANDLER_ARM,       // one arm of a handle block
    NODE_EFFECT_ROW,        // ! [ ... ] row attached to a fn type
    NODE_EFFECT_REF,        // a single effect name inside a row
    NODE_EFFECT_OPEN,       // the ..r open tail of a row
    NODE_ARG,               // call argument (named or positional)
    NODE_ASM_LINE,          // one "..." line of an asm block
    NODE_ASM_OPERAND,       // one  : in/out (..)  operand binding

    // Literals
    NODE_LIT_INT,
    NODE_LIT_FLOAT,
    NODE_LIT_BOOL,
    NODE_LIT_CHAR,
    NODE_LIT_STRING,
    NODE_LIT_RAW_BYTES,
    NODE_LIT_NULL,
    NODE_LIT_BOTTOM,

    // Names
    NODE_IDENT,
    NODE_TYPEVAR,
    NODE_WILDCARD,

    // Types
    NODE_TYPE_PRIMITIVE,
    NODE_TYPE_PATH,
    NODE_TYPE_PTR,
    NODE_TYPE_REF,
    NODE_TYPE_MUT_REF,
    NODE_TYPE_ARRAY,
    NODE_TYPE_SLICE,
    NODE_TYPE_TUPLE,
    NODE_TYPE_FN,
    NODE_TYPE_UNION,
    NODE_TYPE_INTERSECT,
    NODE_TYPE_NEGATION,
    NODE_TYPE_BOTTOM,
    NODE_TYPE_FORALL,
    NODE_TYPE_EXISTS,
    NODE_TYPE_GENERIC_APP,
    NODE_TYPE_REFINEMENT,   // e.g. (> 0), (<= 1.0) used in semantic subtyping
    NODE_TYPE_TENSOR,       // Tensor<T; D0, D1, ...> — element type + shape dims
    NODE_EXPR_TENSOR_LIT,   // [| ... |] tensor literal
    NODE_EXPR_MATMUL,       // a @ b  matrix / tensor contraction

    // Declarations
    NODE_DECL_LET,
    NODE_DECL_MUT,
    NODE_DECL_FN,
    NODE_DECL_TYPE,
    NODE_DECL_STRUCT,
    NODE_DECL_UNION,
    NODE_DECL_NEWTYPE,      // newtype Foo = T  — distinct wrapper type
    NODE_DECL_TLS,          // thread_local let x : T = init — thread-local storage
    NODE_DECL_MACRO,        // macro Foo { | pat => expr, ... }
    NODE_MACRO_RULE,        // one rule: | pat => expansion
    NODE_MACRO_CALL,        // Foo!(args) — macro invocation
    NODE_DECL_ENUM,         // enum Foo { Variant(T), Bar, Baz(A,B) }
    NODE_ENUM_VARIANT,      // one variant: name + optional payload fields
    NODE_DECL_INTERFACE,    // interface Foo { fn method : Self -> T }
    NODE_DECL_IMPL,         // impl Foo for Bar { fn method ... }
    NODE_DECL_EFFECT,
    NODE_DECL_MOD,
    NODE_DECL_USE,
    NODE_DECL_CONST,
    NODE_DECL_STATIC,

    // Statements
    NODE_STMT_RETURN,
    NODE_STMT_BREAK,          // break (optional 'label)
    NODE_STMT_BREAK_LABEL,    // break 'label — labeled break
    NODE_STMT_CONTINUE_LABEL, // continue 'label
    NODE_STMT_CONTINUE,
    NODE_STMT_DEFER,
    NODE_STMT_ASM,
    NODE_STMT_EXPR,
    NODE_STMT_ASSUME,
    NODE_STMT_ASSERT,
    NODE_STMT_INVARIANT,
    NODE_STMT_UNREACHABLE,
    NODE_STMT_TRAP,

    // Expressions
    NODE_EXPR_IF,
    NODE_EXPR_MATCH,
    NODE_EXPR_WHILE,
    NODE_EXPR_FOR,
    NODE_EXPR_LOOP_DO,
    NODE_EXPR_BLOCK,
    NODE_EXPR_ASSIGN,
    NODE_EXPR_BINARY,
    NODE_EXPR_UNARY,
    NODE_EXPR_CALL,
    NODE_EXPR_METHOD_CALL,
    NODE_EXPR_FIELD,
    NODE_EXPR_INDEX,
    NODE_EXPR_CAST,
    NODE_EXPR_TUPLE_LIT,
    NODE_EXPR_ARRAY_LIT,
    NODE_EXPR_STRUCT_LIT,
    NODE_EXPR_CLOSURE,
    NODE_EXPR_ALLOC,
    NODE_EXPR_FREE,
    NODE_EXPR_RANGE,
    NODE_EXPR_PIPELINE,
    NODE_EXPR_SIZEOF,
    NODE_EXPR_ALIGNOF,
    NODE_EXPR_OFFSETOF,
    NODE_EXPR_VOLATILE_LOAD,
    NODE_EXPR_VOLATILE_STORE,
    NODE_EXPR_SYSCALL,
    NODE_EXPR_TRANSMUTE,
    NODE_EXPR_TRY,
    NODE_EXPR_TAILCALL,
    NODE_PATTERN_RANGE,
    NODE_EXPR_FORMAT,         // format!("template", args...) — string interpolation
    NODE_EXPR_INCLUDE_BYTES,  // include_bytes!("file") — embed file at compile time
    NODE_EXPR_ENV_VAR,        // env!("VAR") — read env var at compile time
    NODE_EXPR_CONCAT,         // concat!("a", "b", ...) — string concat at compile time
    NODE_EXPR_UNCHECKED,
    NODE_EXPR_UNSAFE,       // unsafe <block/expr> — carries the Unsafe effect
    NODE_EXPR_UNIT,         // ()

    // Patterns
    NODE_PATTERN_WILDCARD,
    NODE_PATTERN_LITERAL,
    NODE_PATTERN_IDENT,
    NODE_PATTERN_TUPLE,
    NODE_PATTERN_STRUCT,
    NODE_PATTERN_UNION,
    NODE_PATTERN_OR,
    NODE_PATTERN_GUARD,
    NODE_PATTERN_FIELD,     // name or name: subpattern inside a struct pattern

    // Effects
    NODE_EFFECT_HANDLE,
    NODE_EFFECT_WITH,
    NODE_EFFECT_PERFORM,
    NODE_EFFECT_OP_DECL,

    // Attributes
    NODE_ATTR_EXTERN,
    NODE_ATTR_EXPORT,
    NODE_ATTR_INLINE,
    NODE_ATTR_NOINLINE,
    NODE_ATTR_PACKED,
    NODE_ATTR_ALIGN,
    NODE_ATTR_VOLATILE,
    NODE_ATTR_ATOMIC,
    NODE_ATTR_UNSAFE,
    NODE_ATTR_PURE,
    NODE_ATTR_GENERIC,      // any other #name(args) attribute (vectorize, etc.)

    // Safety / UB
    NODE_UB_BANG,
    NODE_EXPR_POISON,
    NODE_EXPR_FREEZE,

    // Metaprogramming
    NODE_REWRITE,
    NODE_REWRITE_RULE,
    NODE_PGEN,
    NODE_STAGE,
    NODE_TYPEOF,           // typeof(expr) — C23 type query
    NODE_TYPEOF_UNQUAL,    // typeof_unqual(expr) — C23
    NODE_QUOTE,
    NODE_SPLICE,
    NODE_UNQUOTE,
    NODE_REIFY,
    NODE_EVAL,
    NODE_COMPTIME,
    NODE_RUNTIME,
    NODE_PATTERN_DECL,
    NODE_FIXPOINT,
    NODE_META,
    NODE_GENERATE,
    NODE_LOWER,

    // Code quotation sigils
    NODE_SIGIL_TREE,
    NODE_SIGIL_DATA,
    NODE_SIGIL_BYTES,

    // IRDL / graph IR
    NODE_IRDL,
    NODE_DIALECT,
    NODE_OPCODE,
    NODE_REGION,
    NODE_BLOCK_IR,
    NODE_NODE_DECL,
    NODE_EDGE_DECL,
    NODE_HYPEREDGE_DECL,
    NODE_GRAPH,

    // SSI markers (inserted by the parser at control-flow joins/splits)
    NODE_SIGMA,
    NODE_PHI
}

// ── Payload structs ──────────────────────────────────────────────────────────
// Only leaves and operator nodes carry a payload; everything else uses children.
struct LitIntData    { ulong int_val; char bits; bool is_signed; }
struct LitFloatData  { double f64_val; char bits; }
struct LitBoolData   { bool bool_val; }
struct LitCharData   { uint char_val; }
struct LitStrData    { char* ptr; usz len; }
struct OpData        { lexer::TokenType op; }
struct IdentData     { char* name_ptr; usz name_len; }
struct AlignData     { ulong value; }   // #align(N), [T; N], etc.

union AstPayload
{
    LitIntData   lit_int;
    LitFloatData lit_float;
    LitBoolData  lit_bool;
    LitCharData  lit_char;
    LitStrData   lit_str;
    OpData       op;
    IdentData    ident;
    AlignData    align;
    ulong        raw;
}

// ── The node ─────────────────────────────────────────────────────────────────
// A standard tree node. `children` is an arena-allocated array of pointers.
struct AstNode
{
    NodeKind     kind;
    uint         id;              // monotonically increasing
    int          line;           // 1-based source location
    int          col;
    AstNode*     type_annotation; // attached type, if any
    ulong        effects;         // EFFECT_* bitmask (union of children)
    uint         flags;           // FLAG_* bitmask
    usz          child_count;
    AstNode**    children;        // arena-allocated array
    AstNode*     resolved;        // name resolution: declaration this refers to
    AstPayload   p;
}

alias NodePtr = AstNode*;

// ── Arena ────────────────────────────────────────────────────────────────────
// A single contiguous slab. All nodes are bump-allocated; the whole tree is
// released in one free() after we are done with it. No GC, no per-node frees.
struct AstArena
{
    char*       base;            // slab start
    usz         cursor;          // next free byte
    usz         cap;             // slab size in bytes
    uint        next_id;
    usz         node_count;
    bool        oom;             // set if the slab filled up
}

// Default slab: 64 MB.
const usz DEFAULT_ARENA_BYTES = 64 * 1024 * 1024;

// Stand up a fresh arena. Returns false if the OS allocation failed.
fn bool AstArena.init(AstArena* a, usz bytes)
{
    a.base = (char*)malloc(bytes);
    if (a.base == null) return false;

    a.cursor = 0;
    a.cap = bytes;
    a.next_id = 1;
    a.node_count = 0;
    a.oom = false;
    return true;
}

// Release the whole tree in a single call.
fn void AstArena.destroy(AstArena* a)
{
    if (a.base != null) free(a.base);
    a.base = null;
    a.cursor = 0;
    a.cap = 0;
}

// Bump allocate `size` bytes aligned to `align`. Returns null on OOM.
fn void* arena_alloc(AstArena* a, usz size, usz align)
{
    usz cur = a.cursor;
    usz aligned = (cur + (align - 1)) & ~(align - 1);

    if (aligned + size > a.cap)
    {
        a.oom = true;
        return null;
    }

    a.cursor = aligned + size;
    return (void*)(a.base + aligned);
}

// ── Node construction ────────────────────────────────────────────────────────
fn AstNode* node_raw(AstArena* a, NodeKind kind, int line, int col)
{
    AstNode* n = (AstNode*)arena_alloc(a, AstNode::size, AstNode::alignment);
    if (n == null) return null;

    n.kind = kind;
    n.id = a.next_id;
    a.next_id++;
    a.node_count++;
    n.line = line;
    n.col = col;
    n.type_annotation = null;
    n.effects = EFFECT_PURE;
    n.flags = FLAG_NONE;
    n.child_count = 0;
    n.children = null;
    n.resolved = null;
    n.p.raw = 0;
    return n;
}

// Copy a child list into the arena and OR child effects up into the parent.
fn void node_attach(AstArena* a, AstNode* n, AstNode** kids, usz count)
{
    if (count == 0)
    {
        n.children = null;
        n.child_count = 0;
        return;
    }

    AstNode** arr = (AstNode**)arena_alloc(a, count * NodePtr::size, NodePtr::alignment);
    if (arr == null)
    {
        n.children = null;
        n.child_count = 0;
        return;
    }

    for (usz i = 0; i < count; i++)
    {
        arr[i] = kids[i];
        if (kids[i] != null) n.effects |= kids[i].effects;
    }

    n.children = arr;
    n.child_count = count;
}

// ── Public leaf constructors ─────────────────────────────────────────────────
fn AstNode* node_int(AstArena* a, ulong v, char bits, bool is_signed, int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_LIT_INT, line, col);
    if (n == null) return null;
    n.p.lit_int.int_val = v;
    n.p.lit_int.bits = bits;
    n.p.lit_int.is_signed = is_signed;
    return n;
}

fn AstNode* node_float(AstArena* a, double v, char bits, int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_LIT_FLOAT, line, col);
    if (n == null) return null;
    n.p.lit_float.f64_val = v;
    n.p.lit_float.bits = bits;
    return n;
}

fn AstNode* node_bool(AstArena* a, bool v, int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_LIT_BOOL, line, col);
    if (n == null) return null;
    n.p.lit_bool.bool_val = v;
    return n;
}

fn AstNode* node_char(AstArena* a, uint v, int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_LIT_CHAR, line, col);
    if (n == null) return null;
    n.p.lit_char.char_val = v;
    return n;
}

fn AstNode* node_str(AstArena* a, NodeKind kind, char* ptr, usz len, int line, int col)
{
    AstNode* n = node_raw(a, kind, line, col);
    if (n == null) return null;
    n.p.lit_str.ptr = ptr;
    n.p.lit_str.len = len;
    return n;
}

fn AstNode* node_null(AstArena* a, int line, int col)
{
    return node_raw(a, NodeKind.NODE_LIT_NULL, line, col);
}

fn AstNode* node_bottom(AstArena* a, int line, int col)
{
    return node_raw(a, NodeKind.NODE_TYPE_BOTTOM, line, col);
}

fn AstNode* node_name(AstArena* a, NodeKind kind, char* ptr, usz len, int line, int col)
{
    AstNode* n = node_raw(a, kind, line, col);
    if (n == null) return null;
    n.p.ident.name_ptr = ptr;
    n.p.ident.name_len = len;
    return n;
}

fn AstNode* node_wildcard(AstArena* a, int line, int col)
{
    return node_raw(a, NodeKind.NODE_WILDCARD, line, col);
}

// A generic 0..N children node, finalized from a temporary buffer.
fn AstNode* node_n(AstArena* a, NodeKind kind, AstNode** kids, usz count, int line, int col)
{
    AstNode* n = node_raw(a, kind, line, col);
    if (n == null) return null;
    node_attach(a, n, kids, count);
    return n;
}

fn AstNode* node0(AstArena* a, NodeKind kind, int line, int col)
{
    return node_n(a, kind, null, 0, line, col);
}

fn AstNode* node1(AstArena* a, NodeKind kind, AstNode* c0, int line, int col)
{
    AstNode*[1] buf;
    buf[0] = c0;
    return node_n(a, kind, &buf[0], 1, line, col);
}

fn AstNode* node2(AstArena* a, NodeKind kind, AstNode* c0, AstNode* c1, int line, int col)
{
    AstNode*[2] buf;
    buf[0] = c0;
    buf[1] = c1;
    return node_n(a, kind, &buf[0], 2, line, col);
}

fn AstNode* node3(AstArena* a, NodeKind kind, AstNode* c0, AstNode* c1, AstNode* c2, int line, int col)
{
    AstNode*[3] buf;
    buf[0] = c0;
    buf[1] = c1;
    buf[2] = c2;
    return node_n(a, kind, &buf[0], 3, line, col);
}

fn AstNode* node_op(AstArena* a, NodeKind kind, lexer::TokenType op, AstNode** kids, usz count, int line, int col)
{
    AstNode* n = node_raw(a, kind, line, col);
    if (n == null) return null;
    n.p.op.op = op;
    node_attach(a, n, kids, count);
    return n;
}

// Tag a node (and, transitively for the parser, its parents) with an effect.
fn void node_add_effect(AstNode* n, ulong eff)
{
    if (n != null) n.effects |= eff;
}

// ── Constant folding ─────────────────────────────────────────────────────────
fn bool both_int(AstNode* l, AstNode* r)
{
    return l != null && r != null
        && l.kind == NodeKind.NODE_LIT_INT
        && r.kind == NodeKind.NODE_LIT_INT;
}

fn bool both_bool(AstNode* l, AstNode* r)
{
    return l != null && r != null
        && l.kind == NodeKind.NODE_LIT_BOOL
        && r.kind == NodeKind.NODE_LIT_BOOL;
}

fn AstNode* mark_folded(AstNode* n)
{
    if (n != null) n.flags |= FLAG_FOLDED;
    return n;
}

// Try to fold `lhs op rhs`. Returns the folded literal, or null if not foldable.
// Division/modulo by zero is intentionally NOT folded (the error propagates).
fn AstNode* fold_binary(AstArena* a, lexer::TokenType op, AstNode* lhs, AstNode* rhs, int line, int col)
{
    if (both_int(lhs, rhs))
    {
        ulong x = lhs.p.lit_int.int_val;
        ulong y = rhs.p.lit_int.int_val;
        char bits = lhs.p.lit_int.bits;
        // A result/comparison is signed if EITHER operand is signed.
        bool sg = lhs.p.lit_int.is_signed || rhs.p.lit_int.is_signed;
        // Signed views for division/modulo/shift/comparison.
        long sx = (long)x;
        long sy = (long)y;

        switch (op)
        {
            case lexer::TokenType.TOKEN_PLUS:    return mark_folded(node_int(a, x + y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_MINUS:   return mark_folded(node_int(a, x - y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_STAR:    return mark_folded(node_int(a, x * y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_SLASH:
                if (y == 0) return null;
                if (sg) return mark_folded(node_int(a, (ulong)(sx / sy), bits, sg, line, col));
                return mark_folded(node_int(a, x / y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_PERCENT:
                if (y == 0) return null;
                if (sg) return mark_folded(node_int(a, (ulong)(sx % sy), bits, sg, line, col));
                return mark_folded(node_int(a, x % y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_AMP:     return mark_folded(node_int(a, x & y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_PIPE:    return mark_folded(node_int(a, x | y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_XOR:     return mark_folded(node_int(a, x ^ y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_LSHIFT:  return mark_folded(node_int(a, x << y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_RSHIFT:
                // arithmetic shift for signed, logical for unsigned
                if (sg) return mark_folded(node_int(a, (ulong)(sx >> y), bits, sg, line, col));
                return mark_folded(node_int(a, x >> y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_EQEQ:    return mark_folded(node_bool(a, x == y, line, col));
            case lexer::TokenType.TOKEN_NEQ:
            case lexer::TokenType.TOKEN_NEQ_UNI: return mark_folded(node_bool(a, x != y, line, col));
            case lexer::TokenType.TOKEN_LT:      return mark_folded(node_bool(a, sg ? sx < sy : x < y, line, col));
            case lexer::TokenType.TOKEN_GT:      return mark_folded(node_bool(a, sg ? sx > sy : x > y, line, col));
            case lexer::TokenType.TOKEN_LTEQ:
            case lexer::TokenType.TOKEN_LEQ_UNI: return mark_folded(node_bool(a, sg ? sx <= sy : x <= y, line, col));
            case lexer::TokenType.TOKEN_GTEQ:
            case lexer::TokenType.TOKEN_GEQ_UNI: return mark_folded(node_bool(a, sg ? sx >= sy : x >= y, line, col));
            default:
                return null;
        }
    }

    if (both_bool(lhs, rhs))
    {
        bool x = lhs.p.lit_bool.bool_val;
        bool y = rhs.p.lit_bool.bool_val;

        switch (op)
        {
            case lexer::TokenType.TOKEN_KW_AND:
            case lexer::TokenType.TOKEN_AMPAMP:   return mark_folded(node_bool(a, x && y, line, col));
            case lexer::TokenType.TOKEN_KW_OR:
            case lexer::TokenType.TOKEN_PIPEPIPE: return mark_folded(node_bool(a, x || y, line, col));
            case lexer::TokenType.TOKEN_EQEQ:     return mark_folded(node_bool(a, x == y, line, col));
            case lexer::TokenType.TOKEN_NEQ:      return mark_folded(node_bool(a, x != y, line, col));
            default:
                return null;
        }
    }

    return null;
}

// Build a binary expression, folding it first if both operands are literals.
fn AstNode* node_binary(AstArena* a, lexer::TokenType op, AstNode* lhs, AstNode* rhs, int line, int col)
{
    AstNode* folded = fold_binary(a, op, lhs, rhs, line, col);
    if (folded != null) return folded;

    AstNode*[2] buf;
    buf[0] = lhs;
    buf[1] = rhs;
    return node_op(a, NodeKind.NODE_EXPR_BINARY, op, &buf[0], 2, line, col);
}

fn AstNode* node_unary(AstArena* a, lexer::TokenType op, AstNode* operand, int line, int col)
{
    AstNode*[1] buf;
    buf[0] = operand;
    return node_op(a, NodeKind.NODE_EXPR_UNARY, op, &buf[0], 1, line, col);
}

// ── Display helper for the driver ────────────────────────────────────────────
fn char* node_kind_name(NodeKind k)
{
    switch (k)
    {
        case NODE_PROGRAM:           return "Program";
        case NODE_INVALID:           return "Invalid";
        case NODE_PARAM:             return "Param";
        case NODE_GENERIC_PARAM:     return "GenericParam";
        case NODE_WHERE_CLAUSE:      return "WhereClause";
        case NODE_ATTRIBUTE_LIST:    return "AttributeList";
        case NODE_MODULE_PATH:       return "ModulePath";
        case NODE_MATCH_ARM:         return "MatchArm";
        case NODE_CLAUSE:            return "Clause";
        case NODE_FIELD_DECL:        return "FieldDecl";
        case NODE_FIELD_INIT:        return "FieldInit";
        case NODE_HANDLER_ARM:       return "HandlerArm";
        case NODE_EFFECT_ROW:        return "EffectRow";
        case NODE_EFFECT_REF:        return "EffectRef";
        case NODE_EFFECT_OPEN:       return "EffectOpen";
        case NODE_ARG:               return "Arg";
        case NODE_ASM_LINE:          return "AsmLine";
        case NODE_ASM_OPERAND:       return "AsmOperand";
        case NODE_LIT_INT:           return "LitInt";
        case NODE_LIT_FLOAT:         return "LitFloat";
        case NODE_LIT_BOOL:          return "LitBool";
        case NODE_LIT_CHAR:          return "LitChar";
        case NODE_LIT_STRING:        return "LitString";
        case NODE_LIT_RAW_BYTES:     return "LitRawBytes";
        case NODE_LIT_NULL:          return "LitNull";
        case NODE_LIT_BOTTOM:        return "LitBottom";
        case NODE_IDENT:             return "Ident";
        case NODE_TYPEVAR:           return "TypeVar";
        case NODE_WILDCARD:          return "Wildcard";
        case NODE_TYPE_PRIMITIVE:    return "TyPrimitive";
        case NODE_TYPE_PATH:         return "TyPath";
        case NODE_TYPE_PTR:          return "TyPtr";
        case NODE_TYPE_REF:          return "TyRef";
        case NODE_TYPE_MUT_REF:      return "TyMutRef";
        case NODE_TYPE_ARRAY:        return "TyArray";
        case NODE_TYPE_SLICE:        return "TySlice";
        case NODE_TYPE_TUPLE:        return "TyTuple";
        case NODE_TYPE_FN:           return "TyFn";
        case NODE_TYPE_UNION:        return "TyUnion";
        case NODE_TYPE_INTERSECT:    return "TyIntersect";
        case NODE_TYPE_NEGATION:     return "TyNegation";
        case NODE_TYPE_BOTTOM:       return "TyBottom";
        case NODE_TYPE_FORALL:       return "TyForall";
        case NODE_TYPE_EXISTS:       return "TyExists";
        case NODE_TYPE_GENERIC_APP:  return "TyGenericApp";
        case NODE_TYPE_REFINEMENT:   return "TyRefinement";
        case NODE_TYPE_TENSOR:       return "TyTensor";
        case NODE_EXPR_TENSOR_LIT:   return "TensorLit";
        case NODE_EXPR_MATMUL:       return "MatMul";
        case NODE_DECL_LET:          return "Let";
        case NODE_DECL_MUT:          return "LetMut";
        case NODE_DECL_FN:           return "Fn";
        case NODE_DECL_TYPE:         return "TypeDecl";
        case NODE_DECL_STRUCT:       return "Struct";
        case NODE_DECL_UNION:        return "Union";
        case NODE_DECL_NEWTYPE:      return "Newtype";
        case NODE_DECL_TLS:          return "ThreadLocal";
        case NODE_DECL_MACRO:        return "Macro";
        case NODE_MACRO_RULE:        return "MacroRule";
        case NODE_MACRO_CALL:        return "MacroCall";
        case NODE_DECL_ENUM:         return "Enum";
        case NODE_ENUM_VARIANT:      return "EnumVariant";
        case NODE_DECL_INTERFACE:    return "Interface";
        case NODE_DECL_IMPL:         return "Impl";
        case NODE_DECL_EFFECT:       return "Effect";
        case NODE_DECL_MOD:          return "Mod";
        case NODE_DECL_USE:          return "Use";
        case NODE_DECL_CONST:        return "Const";
        case NODE_DECL_STATIC:       return "Static";
        case NODE_STMT_RETURN:       return "Return";
        case NODE_STMT_BREAK:        return "Break";
        case NODE_STMT_BREAK_LABEL:  return "BreakLabel";
        case NODE_STMT_CONTINUE_LABEL:return "ContinueLabel";
        case NODE_STMT_CONTINUE:     return "Continue";
        case NODE_STMT_DEFER:        return "Defer";
        case NODE_STMT_ASM:          return "Asm";
        case NODE_STMT_EXPR:         return "ExprStmt";
        case NODE_STMT_ASSUME:       return "Assume";
        case NODE_STMT_ASSERT:       return "Assert";
        case NODE_STMT_INVARIANT:    return "Invariant";
        case NODE_STMT_UNREACHABLE:  return "Unreachable";
        case NODE_STMT_TRAP:         return "Trap";
        case NODE_EXPR_IF:           return "If";
        case NODE_EXPR_MATCH:        return "Match";
        case NODE_EXPR_WHILE:        return "While";
        case NODE_EXPR_FOR:          return "For";
        case NODE_EXPR_LOOP_DO:      return "DoWhile";
        case NODE_EXPR_BLOCK:        return "Block";
        case NODE_EXPR_ASSIGN:       return "Assign";
        case NODE_EXPR_BINARY:       return "Binary";
        case NODE_EXPR_UNARY:        return "Unary";
        case NODE_EXPR_CALL:         return "Call";
        case NODE_EXPR_METHOD_CALL:  return "MethodCall";
        case NODE_EXPR_FIELD:        return "Field";
        case NODE_EXPR_INDEX:        return "Index";
        case NODE_EXPR_CAST:         return "Cast";
        case NODE_EXPR_TUPLE_LIT:    return "TupleLit";
        case NODE_EXPR_ARRAY_LIT:    return "ArrayLit";
        case NODE_EXPR_STRUCT_LIT:   return "StructLit";
        case NODE_EXPR_CLOSURE:      return "Closure";
        case NODE_EXPR_ALLOC:        return "Alloc";
        case NODE_EXPR_FREE:         return "Free";
        case NODE_EXPR_RANGE:        return "Range";
        case NODE_EXPR_PIPELINE:     return "Pipeline";
        case NODE_EXPR_SIZEOF:        return "SizeOf";
        case NODE_EXPR_OFFSETOF:      return "Offsetof";
        case NODE_EXPR_VOLATILE_LOAD: return "VolLoad";
        case NODE_EXPR_VOLATILE_STORE:return "VolStore";
        case NODE_EXPR_SYSCALL:       return "Syscall";
        case NODE_EXPR_ALIGNOF:      return "AlignOf";
        case NODE_EXPR_TRANSMUTE:    return "Transmute";
        case NODE_EXPR_TRY:          return "Try";
        case NODE_EXPR_TAILCALL:     return "TailCall";
        case NODE_PATTERN_RANGE:     return "PatRange";
        case NODE_EXPR_FORMAT:        return "Format";
        case NODE_EXPR_INCLUDE_BYTES: return "IncludeBytes";
        case NODE_EXPR_ENV_VAR:       return "EnvVar";
        case NODE_EXPR_CONCAT:        return "Concat";
        case NODE_EXPR_UNCHECKED:    return "Unchecked";
        case NODE_EXPR_UNSAFE:       return "Unsafe";
        case NODE_EXPR_UNIT:         return "Unit";
        case NODE_PATTERN_WILDCARD:  return "PatWildcard";
        case NODE_PATTERN_LITERAL:   return "PatLiteral";
        case NODE_PATTERN_IDENT:     return "PatIdent";
        case NODE_PATTERN_TUPLE:     return "PatTuple";
        case NODE_PATTERN_STRUCT:    return "PatStruct";
        case NODE_PATTERN_UNION:     return "PatUnion";
        case NODE_PATTERN_OR:        return "PatOr";
        case NODE_PATTERN_GUARD:     return "PatGuard";
        case NODE_PATTERN_FIELD:     return "PatField";
        case NODE_EFFECT_HANDLE:     return "Handle";
        case NODE_EFFECT_WITH:       return "With";
        case NODE_EFFECT_PERFORM:    return "Perform";
        case NODE_EFFECT_OP_DECL:    return "EffectOpDecl";
        case NODE_ATTR_EXTERN:       return "AttrExtern";
        case NODE_ATTR_EXPORT:       return "AttrExport";
        case NODE_ATTR_INLINE:       return "AttrInline";
        case NODE_ATTR_NOINLINE:     return "AttrNoinline";
        case NODE_ATTR_PACKED:       return "AttrPacked";
        case NODE_ATTR_ALIGN:        return "AttrAlign";
        case NODE_ATTR_VOLATILE:     return "AttrVolatile";
        case NODE_ATTR_ATOMIC:       return "AttrAtomic";
        case NODE_ATTR_UNSAFE:       return "AttrUnsafe";
        case NODE_ATTR_PURE:         return "AttrPure";
        case NODE_ATTR_GENERIC:      return "Attr";
        case NODE_UB_BANG:           return "UbBang";
        case NODE_EXPR_POISON:       return "Poison";
        case NODE_EXPR_FREEZE:       return "Freeze";
        case NODE_REWRITE:           return "Rewrite";
        case NODE_REWRITE_RULE:      return "RewriteRule";
        case NODE_PGEN:              return "Pgen";
        case NODE_STAGE:             return "Stage";
        case NODE_TYPEOF:            return "Typeof";
        case NODE_TYPEOF_UNQUAL:     return "TypeofUnqual";
        case NODE_QUOTE:             return "Quote";
        case NODE_SPLICE:            return "Splice";
        case NODE_UNQUOTE:           return "Unquote";
        case NODE_REIFY:             return "Reify";
        case NODE_EVAL:              return "Eval";
        case NODE_COMPTIME:          return "Comptime";
        case NODE_RUNTIME:           return "Runtime";
        case NODE_PATTERN_DECL:      return "PatternDecl";
        case NODE_FIXPOINT:          return "Fixpoint";
        case NODE_META:              return "Meta";
        case NODE_GENERATE:          return "Generate";
        case NODE_LOWER:             return "Lower";
        case NODE_SIGIL_TREE:        return "SigilTree";
        case NODE_SIGIL_DATA:        return "SigilData";
        case NODE_SIGIL_BYTES:       return "SigilBytes";
        case NODE_IRDL:              return "Irdl";
        case NODE_DIALECT:           return "Dialect";
        case NODE_OPCODE:            return "Opcode";
        case NODE_REGION:            return "Region";
        case NODE_BLOCK_IR:          return "BlockIR";
        case NODE_NODE_DECL:         return "NodeDecl";
        case NODE_EDGE_DECL:         return "EdgeDecl";
        case NODE_HYPEREDGE_DECL:    return "HyperedgeDecl";
        case NODE_GRAPH:             return "Graph";
        case NODE_SIGMA:             return "Sigma";
        case NODE_PHI:               return "Phi";
        default:                     return "?";
    }
}
