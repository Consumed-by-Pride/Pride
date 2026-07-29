// ast.c3 — Abstract Syntax Tree for the Pride compiler
// Implementation language: C3 (host). Pride is written in C3; it does NOT
// compile to C3.
// A plain, standard AST: every node has exactly one parent (a tree). This
// module defines:
//   - NodeKind   : every node kind the parser can build
//   - AstNode    : a single tree node, with inline metadata + a payload union
//   - AstArena   : a bump-allocated slab so we never free nodes individually
//   - effects    : a u64 bitmask per node, OR-propagated child -> parent
//   - folding    : LitInt op LitInt etc. fold immediately at build time
// The parser (parser.c3) calls the node_* constructors here. The driver
// (pride.c3) walks the resulting tree and prints it.

module ast;

import lexer;

// The arena is heap-backed so the slab size is configurable at runtime.
extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn void* memset(void* dst, int value, usz n);

// Effects propagate upward: a parent's mask is the union of its children's.
const ulong EFFECT_PURE   = 0;
const ulong EFFECT_IO     = 1;   // bit 0 — performs I/O
const ulong EFFECT_ALLOC  = 2;   // bit 1 — allocates or frees memory
const ulong EFFECT_UNSAFE = 4;   // bit 2 — unsafe op or inline asm
const ulong EFFECT_UB     = 8;   // bit 3 — may trigger declared UB
const ulong EFFECT_PANIC  = 16;  // bit 4 — may panic

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
    NODE_EXPR_LABELED,        // 'label: while/for/do — labeled loop
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
    NODE_EXPR_ATOMIC_RMW,       // atomic_add/sub/and/or/xor/xchg(ptr, val)
    NODE_EXPR_ATOMIC_CMPXCHG,   // atomic_cmpxchg(ptr, expected, new)
    NODE_EXPR_FENCE,            // fence(ordering)
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
    NODE_ATTR_SECTION,      // #[section("name")] — linker section
    NODE_ATTR_USED,         // #[used] — prevent dead-code elimination
    NODE_ATTR_WEAK,         // #[weak] — weak symbol linkage
    NODE_ATTR_VARARG,       // #[vararg] / ... — variadic C function
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
    NODE_PHI,

    // ── New nodes ──────────────────────────────────────────────────────────

    // Error recovery: a partial parse subtree with a diagnosis attached.
    // Downstream passes skip these silently; the type checker does not enter them.
    // children[0] = partial subtree (may be null), payload = ErrorRecoveryData.
    NODE_ERROR_RECOVERY,

    // Operator overloading declaration:
    //   operator (+) : (T, T) -> T | (a, b) -> ...
    // children = param list + clause list.  payload = OperatorData.
    NODE_DECL_OPERATOR,

    // Structured interpolated string: "hello {name}, you are {age} years old"
    // children = [seg0, expr0, seg1, expr1, ..., segN]  (alternating)
    // payload = InterpStrData.
    NODE_INTERPOLATED_STRING,

    // Comptime block with cached evaluation result.
    // children[0] = body.  payload = ComptimeBlockData.
    NODE_COMPTIME_BLOCK,

    // Step range:  start..end by step   (e.g. 0..100 by 2)
    // children[0]=start, children[1]=end, children[2]=step.
    // payload = RangeStepData.
    NODE_EXPR_RANGE_STEP,

    // Inline asm block with dialect tag (AT&T / Intel / custom).
    // children = asm lines + operand bindings.  payload = AsmBlockData.
    NODE_STMT_ASM_BLOCK,

    // Import with structured path data for fast resolution.
    // payload = ImportData.
    NODE_DECL_IMPORT,

    // Pattern matrix node attached to a fn's first clause during typecheck.
    // Not emitted by the parser; inserted by the pattern exhaustiveness checker.
    NODE_PATTERN_MATRIX,

    // Trivia-preserving wrapper: holds a whitespace/comment token sequence
    // before a real node.  Used by the CST shadow layer.
    // children[0] = real node.  payload = TriviaData.
    NODE_TRIVIA,

    // Doc-comment attached to a declaration.
    // payload.lit_str = the raw comment text (after stripping -- / ---).
    NODE_DOC_COMMENT
}

// Only leaves and operator nodes carry a payload; everything else uses children.
struct LitIntData    { ulong int_val; char bits; bool is_signed; }
struct LitFloatData  { double f64_val; char bits; }
struct LitBoolData   { bool bool_val; }
struct LitCharData   { uint char_val; }
struct LitStrData    { char* ptr; usz len; }
struct OpData        { lexer::TokenType op; }
struct IdentData     { char* name_ptr; usz name_len; uint intern_id; }  // intern_id = 0 means not yet interned
struct AlignData     { ulong value; }   // #align(N), [T; N], etc.

// ── New payload variants ────────────────────────────────────────────────────

// Identifies the synchronisation token and a diagnostic id for error recovery.
struct ErrorRecoveryData
{
    lexer::TokenType sync_tok;   // token kind at which the parser re-synced
    uint             diag_id;    // index into the parser's error table
    bool             partial;    // true = children[0] is a partial valid subtree
}

// User-defined operator declaration metadata.
enum Assoc : int { ASSOC_NONE, ASSOC_LEFT, ASSOC_RIGHT }
struct OperatorData
{
    lexer::TokenType op_tok;   // the operator token (TOKEN_PLUS, TOKEN_STAR, etc.)
    int              prec;     // precedence level (0..99, same scale as built-ins)
    Assoc            assoc;    // associativity
}

// Interpolated string: segment count is number of literal string pieces.
// The node has 2*segment_count - 1 children (segments interleaved with exprs).
struct InterpStrData
{
    uint segment_count;    // number of string literal segments
    bool has_raw_prefix;   // r"..." raw interpolation — backslash not interpreted
}

// Comptime block with evaluation cache.
enum ComptimeKind : int
{
    COMPTIME_EXPR,   // comptime expression — produces a value
    COMPTIME_TYPE,   // comptime expression — produces a type
    COMPTIME_DECL    // comptime block — produces declarations
}
struct ComptimeBlockData
{
    ComptimeKind kind;
    bool         evaluated;       // true once the comptime evaluator has run
    AstNode*     cached_result;   // non-null after evaluation; avoids re-eval
}

// Step range: start..end by step.
struct RangeStepData
{
    bool inclusive;   // ..= vs ..
    bool has_step;    // whether children[2] is present
}

// Inline asm block with dialect selection and option flags.
enum AsmDialect : int { ASM_DIALECT_ATT, ASM_DIALECT_INTEL, ASM_DIALECT_CUSTOM }
const uint ASM_OPT_VOLATILE   = 1;   // asm block has observable side-effects
const uint ASM_OPT_INLINE     = 2;   // hint: prefer inline (no call)
const uint ASM_OPT_ALIGNSTACK = 4;   // ensure stack is aligned before the asm
struct AsmBlockData
{
    AsmDialect dialect;
    uint       options;     // ASM_OPT_* bitmask
    uint       n_outputs;   // number of output operand bindings
    uint       n_inputs;    // number of input operand bindings
    uint       n_clobbers;  // number of clobber strings
}

// Structured import — avoids string-walking children to resolve paths.
enum ImportKind : int
{
    IMPORT_MODULE,    // use foo.bar
    IMPORT_GLOB,      // use foo.*
    IMPORT_NAMED,     // use foo.{A, B, C}
    IMPORT_ALIASED    // use foo.Bar as Baz
}
struct ImportData
{
    char*      path;        // dotted path as a flat string "foo.bar.baz"
    usz        path_len;
    char*      alias_name;  // non-null for IMPORT_ALIASED
    usz        alias_len;
    bool       is_pub;      // pub use ...
    ImportKind kind;
}

// Trivia (whitespace + comments) preceding a real node.
struct TriviaData
{
    char* text;        // raw source bytes of the trivia
    usz   text_len;
    bool  has_doc;     // true if any trivia line starts with ---
}

// Function declaration metadata cached at parse time.
struct FnData
{
    uint arity;               // number of parameters in the first clause
    uint clause_count;        // total number of | clauses
    bool is_recursive;        // parser-detected self-reference (conservative)
    bool is_tail_recursive;   // all recursive calls are in tail position
    bool is_extern;           // #extern attribute present
    bool is_variadic;         // #vararg attribute present
    uint intern_name_id;      // interned function name (0 = not interned yet)
}

// Match expression metadata cached at parse time.
struct MatchData
{
    uint arm_count;             // number of match arms
    bool is_exhaustive_proven;  // set by the exhaustiveness checker
    bool has_guard;             // at least one arm has a guard
    bool is_stmt;               // match used as a statement (result discarded)
}

// Clause metadata — attached to each fn clause node.
struct ClauseData
{
    uint clause_idx;     // 0-based index of this clause in the function
    uint total_clauses;  // total clauses in the enclosing fn (set at parse end)
    bool has_guard;      // this clause has a comma-separated guard condition
    AstNode* pattern_matrix_cache;  // null until the exhaustiveness checker runs
}

union AstPayload
{
    LitIntData      lit_int;
    LitFloatData    lit_float;
    LitBoolData     lit_bool;
    LitCharData     lit_char;
    LitStrData      lit_str;
    OpData          op;
    IdentData       ident;
    AlignData       align;

    // New variants
    ErrorRecoveryData  error_recovery;
    OperatorData       operator_decl;
    InterpStrData      interp_str;
    ComptimeBlockData  comptime_block;
    RangeStepData      range_step;
    AsmBlockData       asm_block;
    ImportData         import_decl;
    TriviaData         trivia;
    FnData             fn_data;
    MatchData          match_data;
    ClauseData         clause_data;

    ulong           raw;
}

// ── Additional flags ────────────────────────────────────────────────────────
// Extends FLAG_* constants defined above.
const uint FLAG_TAIL_POS       = 2048;   // expression is in tail position
const uint FLAG_COMPTIME       = 4096;   // value is known at compile time
const uint FLAG_INTERNED       = 8192;   // identifier/string is in the intern table
const uint FLAG_POISONED       = 16384;  // node is inside an error-recovery subtree
const uint FLAG_DOC_ATTACHED   = 32768;  // a doc-comment has been attached
const uint FLAG_CLAUSE_LAST    = 65536;  // this is the last clause of a fn (for tail detection)

// A standard tree node. `children` is an arena-allocated array of pointers.
//
// Span layout (byte offsets into the original source buffer):
//   span_start — first byte of the first token of this node (inclusive)
//   span_end   — first byte AFTER the last token of this node (exclusive)
//   tok_idx    — index of this node's primary token in the flat token array
//                (enables O(1) re-serialisation and incremental reparsing)
//
// Intern id:
//   For NODE_IDENT, NODE_LIT_STRING, and NODE_TYPE_PRIMITIVE, intern_id is a
//   key into the module-level StrInternTable.  0 means "not yet interned".
//   Once interned, identifier equality is O(1): compare intern_id, not bytes.
//
// doc_comment:
//   Non-null on any declaration node that had a preceding --- doc block.
//   Points to a NODE_DOC_COMMENT in the same arena.
struct AstNode
{
    NodeKind     kind;
    uint         id;              // monotonically increasing, unique per arena
    int          line;            // 1-based source location (redundant with span for diagnostics)
    int          col;
    uint         span_start;      // byte offset of first token (into source buffer)
    uint         span_end;        // byte offset past last token (exclusive)
    uint         tok_idx;         // index into the flat token array (0 if unavailable)
    uint         intern_id;       // interned name id (0 = not interned)
    AstNode*     type_annotation; // attached type, if any
    AstNode*     doc_comment;     // NODE_DOC_COMMENT, or null
    ulong        effects;         // EFFECT_* bitmask (union of children)
    uint         flags;           // FLAG_* bitmask (extended set above)
    usz          child_count;
    AstNode**    children;        // arena-allocated array
    AstNode*     resolved;        // name resolution: declaration this refers to
    AstPayload   p;
}

alias NodePtr = AstNode*;

// ── String intern table ─────────────────────────────────────────────────────
// Maps (char*, len) → uint intern_id.  All identifier and string-literal bytes
// are deduplicated through this table so equality checks become O(1) integer
// comparisons rather than O(n) memcmp.
//
// Design:
//   Open-addressing hash table with linear probing.
//   Bucket count is always a power of two; load factor stays below 0.75.
//   The id 0 is reserved for "not interned".  Ids start at 1.
//   Strings themselves are stored in the AstArena (no separate allocation).
const usz INTERN_INITIAL_CAP = 1024;
const usz INTERN_ID_NONE     = 0;

struct InternBucket
{
    char*  ptr;    // pointer into arena storage; null = empty bucket
    usz    len;
    uint   id;
}

struct StrInternTable
{
    InternBucket*  buckets;
    usz            bucket_count;   // always a power of two
    usz            entry_count;
    uint           next_id;        // next id to assign; starts at 1
}

fn bool StrInternTable.init(StrInternTable* t)
{
    t.buckets = (InternBucket*)malloc(INTERN_INITIAL_CAP * InternBucket::size);
    if (t.buckets == null) return false;
    for (usz i = 0; i < INTERN_INITIAL_CAP; i++)
    {
        t.buckets[i].ptr = null;
        t.buckets[i].len = 0;
        t.buckets[i].id  = 0;
    }
    t.bucket_count = INTERN_INITIAL_CAP;
    t.entry_count  = 0;
    t.next_id      = 1;
    return true;
}

fn void StrInternTable.destroy(StrInternTable* t)
{
    if (t.buckets != null) free(t.buckets);
    t.buckets = null;
}

// FNV-1a 64-bit hash over (ptr, len).
fn ulong intern_hash(char* ptr, usz len)
{
    ulong h = 14695981039346656037u;
    for (usz i = 0; i < len; i++)
    {
        h ^= (ulong)(uint)(char)ptr[i];
        h *= 1099511628211u;
    }
    return h;
}

fn bool intern_str_eq(char* a, usz al, char* b, usz bl)
{
    if (al != bl) return false;
    for (usz i = 0; i < al; i++) if (a[i] != b[i]) return false;
    return true;
}

// Grow the table when load > 0.75.
fn bool StrInternTable.grow(StrInternTable* t)
{
    usz new_cap = t.bucket_count * 2;
    InternBucket* nb = (InternBucket*)malloc(new_cap * InternBucket::size);
    if (nb == null) return false;
    for (usz i = 0; i < new_cap; i++) { nb[i].ptr = null; nb[i].len = 0; nb[i].id = 0; }
    for (usz i = 0; i < t.bucket_count; i++)
    {
        if (t.buckets[i].ptr == null) continue;
        ulong h = intern_hash(t.buckets[i].ptr, t.buckets[i].len);
        usz slot = (usz)(h & (ulong)(new_cap - 1));
        while (nb[slot].ptr != null) slot = (slot + 1) & (new_cap - 1);
        nb[slot] = t.buckets[i];
    }
    free(t.buckets);
    t.buckets      = nb;
    t.bucket_count = new_cap;
    return true;
}

// Intern a string.  Returns 0 on allocation failure.
// If already present, returns the existing id.  Otherwise assigns a new one.
// NOTE: the string bytes must already be in stable storage (arena or literal).
fn uint StrInternTable.intern(StrInternTable* t, char* ptr, usz len)
{
    if (t.entry_count * 4 >= t.bucket_count * 3)
    {
        if (!t.grow()) return 0;
    }
    ulong h    = intern_hash(ptr, len);
    usz   slot = (usz)(h & (ulong)(t.bucket_count - 1));
    while (t.buckets[slot].ptr != null)
    {
        if (intern_str_eq(t.buckets[slot].ptr, t.buckets[slot].len, ptr, len))
        {
            return t.buckets[slot].id;
        }
        slot = (slot + 1) & (t.bucket_count - 1);
    }
    uint id = t.next_id++;
    t.buckets[slot].ptr = ptr;
    t.buckets[slot].len = len;
    t.buckets[slot].id  = id;
    t.entry_count++;
    return id;
}

// Look up without inserting.  Returns INTERN_ID_NONE if not found.
fn uint StrInternTable.lookup(StrInternTable* t, char* ptr, usz len)
{
    ulong h    = intern_hash(ptr, len);
    usz   slot = (usz)(h & (ulong)(t.bucket_count - 1));
    while (t.buckets[slot].ptr != null)
    {
        if (intern_str_eq(t.buckets[slot].ptr, t.buckets[slot].len, ptr, len))
        {
            return t.buckets[slot].id;
        }
        slot = (slot + 1) & (t.bucket_count - 1);
    }
    return INTERN_ID_NONE;
}

// ── Operator precedence table ───────────────────────────────────────────────
// The Pratt parser uses this table rather than hardcoded if-chains, so that
// user-defined operators (NODE_DECL_OPERATOR) can register entries at parse
// time and participate in expression parsing with custom precedence.
//
// Built-in operators are pre-populated by prec_table_init().
// The table is a flat sorted array; lookup is O(1) via a small hash table
// keyed on the TokenType integer value.
//
// Precedence levels (matching Pride's spec §23):
//   1  = lowest: pipeline |>
//   2  = effect-perform
//   3  = or / ||
//   4  = and / &&
//   5  = comparison == != < <= > >=
//   6  = bitwise | ^ &
//   7  = shift << >>
//   8  = additive + -
//   9  = multiplicative * / %
//   10 = wrapping/saturating +% -% *% +| -| *|
//   11 = cast as
//   12 = unary prefix (!, -, ~, *)
//   13 = postfix (call, index, field, ?)
//   99 = comptime-only (tightly binding)

const int PREC_NONE       = 0;
const int PREC_PIPELINE   = 1;
const int PREC_OR         = 3;
const int PREC_AND        = 4;
const int PREC_CMP        = 5;
const int PREC_BITWISE    = 6;
const int PREC_SHIFT      = 7;
const int PREC_ADD        = 8;
const int PREC_MUL        = 9;
const int PREC_WRAP       = 10;
const int PREC_CAST       = 11;
const int PREC_UNARY      = 12;
const int PREC_POSTFIX    = 13;

const usz PREC_TABLE_MAX  = 256;
const usz PREC_SLOT_COUNT = 512;

struct PrecEntry
{
    lexer::TokenType  op;
    int               prec;
    Assoc             assoc;
    bool              is_binary;
    bool              is_unary_prefix;
    bool              is_user_defined;  // true = registered by NODE_DECL_OPERATOR
}

struct PrecTable
{
    PrecEntry[256]  entries;
    usz             count;
    // Small hash map for O(1) lookup: token_type -> entry index.
    // Slots store (entry_index + 1) so 0 = empty.
    uint[512]       slots;
    usz             slot_mask;    // = 511
}

fn void PrecTable.insert(PrecTable* t, PrecEntry e)
{
    if (t.count >= PREC_TABLE_MAX) return;
    usz idx = t.count;
    t.entries[idx] = e;
    t.count++;
    // Hash into slots
    uint key  = (uint)e.op;
    usz  slot = (usz)(key * 2654435761u) & t.slot_mask;
    while (t.slots[slot] != 0) slot = (slot + 1) & t.slot_mask;
    t.slots[slot] = (uint)(idx + 1);
}

fn PrecEntry* PrecTable.find(PrecTable* t, lexer::TokenType op)
{
    uint key  = (uint)op;
    usz  slot = (usz)(key * 2654435761u) & t.slot_mask;
    while (t.slots[slot] != 0)
    {
        usz idx = (usz)(t.slots[slot] - 1);
        if (t.entries[idx].op == op) return &t.entries[idx];
        slot = (slot + 1) & t.slot_mask;
    }
    return null;
}

// Register a user-defined operator at runtime (called from the parser when it
// sees NODE_DECL_OPERATOR).  Returns false if the table is full.
fn bool PrecTable.register_user_op(PrecTable* t, lexer::TokenType op, int prec, Assoc assoc)
{
    PrecEntry e;
    e.op              = op;
    e.prec            = prec;
    e.assoc           = assoc;
    e.is_binary       = true;
    e.is_unary_prefix = false;
    e.is_user_defined = true;
    t.insert(e);
    return true;
}

fn void PrecTable.init(PrecTable* t)
{
    t.count     = 0;
    t.slot_mask = 511;
    for (usz i = 0; i < 512; i++) t.slots[i] = 0;

    // Helper macro-style: we declare a local to reuse
    PrecEntry e;

    // Pipeline
    e.is_user_defined = false;
    e.is_unary_prefix = false;
    e.is_binary = true;

    e.op = lexer::TokenType.TOKEN_PIPELINE;   e.prec = PREC_PIPELINE; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);

    // Logical
    e.op = lexer::TokenType.TOKEN_PIPEPIPE;   e.prec = PREC_OR;  e.assoc = Assoc.ASSOC_LEFT; t.insert(e);
    e.op = lexer::TokenType.TOKEN_KW_OR;      e.prec = PREC_OR;  e.assoc = Assoc.ASSOC_LEFT; t.insert(e);
    e.op = lexer::TokenType.TOKEN_AMPAMP;     e.prec = PREC_AND; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);
    e.op = lexer::TokenType.TOKEN_KW_AND;     e.prec = PREC_AND; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);

    // Comparison
    e.op = lexer::TokenType.TOKEN_EQEQ;      e.prec = PREC_CMP; e.assoc = Assoc.ASSOC_NONE; t.insert(e);
    e.op = lexer::TokenType.TOKEN_NEQ;        e.prec = PREC_CMP; e.assoc = Assoc.ASSOC_NONE; t.insert(e);
    e.op = lexer::TokenType.TOKEN_NEQ_UNI;    e.prec = PREC_CMP; e.assoc = Assoc.ASSOC_NONE; t.insert(e);
    e.op = lexer::TokenType.TOKEN_LT;         e.prec = PREC_CMP; e.assoc = Assoc.ASSOC_NONE; t.insert(e);
    e.op = lexer::TokenType.TOKEN_LTEQ;       e.prec = PREC_CMP; e.assoc = Assoc.ASSOC_NONE; t.insert(e);
    e.op = lexer::TokenType.TOKEN_LEQ_UNI;    e.prec = PREC_CMP; e.assoc = Assoc.ASSOC_NONE; t.insert(e);
    e.op = lexer::TokenType.TOKEN_GT;         e.prec = PREC_CMP; e.assoc = Assoc.ASSOC_NONE; t.insert(e);
    e.op = lexer::TokenType.TOKEN_GTEQ;       e.prec = PREC_CMP; e.assoc = Assoc.ASSOC_NONE; t.insert(e);
    e.op = lexer::TokenType.TOKEN_GEQ_UNI;    e.prec = PREC_CMP; e.assoc = Assoc.ASSOC_NONE; t.insert(e);

    // Bitwise
    e.op = lexer::TokenType.TOKEN_PIPE;       e.prec = PREC_BITWISE; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);
    e.op = lexer::TokenType.TOKEN_XOR;        e.prec = PREC_BITWISE; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);
    e.op = lexer::TokenType.TOKEN_AMP;        e.prec = PREC_BITWISE; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);

    // Shift
    e.op = lexer::TokenType.TOKEN_LSHIFT;     e.prec = PREC_SHIFT; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);
    e.op = lexer::TokenType.TOKEN_RSHIFT;     e.prec = PREC_SHIFT; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);

    // Additive
    e.op = lexer::TokenType.TOKEN_PLUS;       e.prec = PREC_ADD; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);
    e.op = lexer::TokenType.TOKEN_MINUS;      e.prec = PREC_ADD; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);

    // Multiplicative
    e.op = lexer::TokenType.TOKEN_STAR;       e.prec = PREC_MUL; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);
    e.op = lexer::TokenType.TOKEN_SLASH;      e.prec = PREC_MUL; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);
    e.op = lexer::TokenType.TOKEN_PERCENT;    e.prec = PREC_MUL; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);

    // Wrapping / saturating  (+% -% *%  +| -| *|)
    e.op = lexer::TokenType.TOKEN_PLUS_PERCENT;  e.prec = PREC_WRAP; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);
    e.op = lexer::TokenType.TOKEN_MINUS_PERCENT; e.prec = PREC_WRAP; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);
    e.op = lexer::TokenType.TOKEN_STAR_PERCENT;  e.prec = PREC_WRAP; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);
    e.op = lexer::TokenType.TOKEN_PLUS_PIPE;     e.prec = PREC_WRAP; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);
    e.op = lexer::TokenType.TOKEN_MINUS_PIPE;    e.prec = PREC_WRAP; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);
    e.op = lexer::TokenType.TOKEN_STAR_PIPE;     e.prec = PREC_WRAP; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);

    // Matmul
    e.op = lexer::TokenType.TOKEN_AT;         e.prec = PREC_MUL; e.assoc = Assoc.ASSOC_LEFT; t.insert(e);

    // Set-membership (∈)
    e.op = lexer::TokenType.TOKEN_ELEMENT;    e.prec = PREC_CMP; e.assoc = Assoc.ASSOC_NONE; t.insert(e);
    e.op = lexer::TokenType.TOKEN_KW_IN;      e.prec = PREC_CMP; e.assoc = Assoc.ASSOC_NONE; t.insert(e);
}

// ── A single contiguous slab ─────────────────────────────────────────────────
// All nodes are bump-allocated; the whole tree is released in one free() after
// we are done with it.  No GC, no per-node frees.
struct AstArena
{
    char*       base;            // slab start
    usz         cursor;          // next free byte
    usz         cap;             // slab size in bytes
    uint        next_id;
    usz         node_count;
    bool        oom;             // set if the slab filled up
    StrInternTable intern;       // string intern table (shares arena allocation for keys)
    PrecTable   prec;            // operator precedence table (populated by the parser)
}

// Default slab: 64 MB.
const usz DEFAULT_ARENA_BYTES = 64 * 1024 * 1024;

// Stand up a fresh arena.  Returns false if any OS allocation failed.
fn bool AstArena.init(AstArena* a, usz bytes)
{
    a.base = (char*)malloc(bytes);
    if (a.base == null) return false;

    a.cursor    = 0;
    a.cap       = bytes;
    a.next_id   = 1;
    a.node_count = 0;
    a.oom       = false;

    // Initialise the string intern table.
    if (!a.intern.init())
    {
        free(a.base);
        a.base = null;
        return false;
    }

    // Initialise the operator precedence table with all built-in operators.
    a.prec.init();

    return true;
}

// Release the whole tree in a single call.
fn void AstArena.destroy(AstArena* a)
{
    a.intern.destroy();
    if (a.base != null) free(a.base);
    a.base   = null;
    a.cursor = 0;
    a.cap    = 0;
}

// Convenience: intern an identifier into this arena's intern table.
// The string bytes must reside in stable storage (the arena slab or a literal).
fn uint AstArena.intern_str(AstArena* a, char* ptr, usz len)
{
    return a.intern.intern(ptr, len);
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

fn AstNode* node_raw(AstArena* a, NodeKind kind, int line, int col)
{
    AstNode* n = (AstNode*)arena_alloc(a, AstNode::size, AstNode::alignment);
    if (n == null) return null;

    n.kind            = kind;
    n.id              = a.next_id;
    a.next_id++;
    a.node_count++;
    n.line            = line;
    n.col             = col;
    n.span_start      = 0;
    n.span_end        = 0;
    n.tok_idx         = 0;
    n.intern_id       = 0;
    n.type_annotation = null;
    n.doc_comment     = null;
    n.effects         = EFFECT_PURE;
    n.flags           = FLAG_NONE;
    n.child_count     = 0;
    n.children        = null;
    n.resolved        = null;
    n.p.raw           = 0;
    return n;
}

// Attach byte-precise source span to a node (called by the parser after it
// knows the extent of the construct).
fn void node_set_span(AstNode* n, uint start, uint end, uint tok_idx)
{
    if (n == null) return;
    n.span_start = start;
    n.span_end   = end;
    n.tok_idx    = tok_idx;
}

// Attach a doc-comment node to a declaration node.
fn void node_attach_doc(AstNode* decl, AstNode* doc)
{
    if (decl == null || doc == null) return;
    decl.doc_comment = doc;
    decl.flags |= FLAG_DOC_ATTACHED;
}

// ── Error recovery node ─────────────────────────────────────────────────────
fn AstNode* node_error_recovery(AstArena* a, AstNode* partial,
                                 lexer::TokenType sync_tok, uint diag_id,
                                 int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_ERROR_RECOVERY, line, col);
    if (n == null) return null;
    n.p.error_recovery.sync_tok = sync_tok;
    n.p.error_recovery.diag_id  = diag_id;
    n.p.error_recovery.partial  = (partial != null);
    n.flags |= FLAG_POISONED;
    if (partial != null)
    {
        AstNode*[1] buf;
        buf[0] = partial;
        node_attach(a, n, &buf[0], 1);
    }
    return n;
}

// ── Operator overloading declaration ────────────────────────────────────────
fn AstNode* node_decl_operator(AstArena* a,
                                 lexer::TokenType op_tok, int prec, Assoc assoc,
                                 AstNode** kids, usz count,
                                 int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_DECL_OPERATOR, line, col);
    if (n == null) return null;
    n.p.operator_decl.op_tok = op_tok;
    n.p.operator_decl.prec   = prec;
    n.p.operator_decl.assoc  = assoc;
    node_attach(a, n, kids, count);
    // Register the operator in the arena's prec table so future parses see it.
    a.prec.register_user_op(op_tok, prec, assoc);
    return n;
}

// ── Interpolated string node ────────────────────────────────────────────────
// segments and exprs must be interleaved: [seg0, expr0, seg1, expr1, ..., segN]
// `segment_count` is the number of literal string pieces (always one more
// than the number of interpolation holes).
fn AstNode* node_interp_string(AstArena* a,
                                 AstNode** parts, usz part_count,
                                 uint segment_count, bool raw_prefix,
                                 int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_INTERPOLATED_STRING, line, col);
    if (n == null) return null;
    n.p.interp_str.segment_count = segment_count;
    n.p.interp_str.has_raw_prefix = raw_prefix;
    node_attach(a, n, parts, part_count);
    return n;
}

// ── Comptime block ───────────────────────────────────────────────────────────
fn AstNode* node_comptime_block(AstArena* a, AstNode* body,
                                  ComptimeKind kind, int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_COMPTIME_BLOCK, line, col);
    if (n == null) return null;
    n.p.comptime_block.kind           = kind;
    n.p.comptime_block.evaluated      = false;
    n.p.comptime_block.cached_result  = null;
    if (body != null)
    {
        AstNode*[1] buf;
        buf[0] = body;
        node_attach(a, n, &buf[0], 1);
    }
    return n;
}

// Called by the comptime evaluator to cache a result — avoids re-evaluation
// on subsequent passes (type checker, codegen).
fn void node_comptime_set_result(AstNode* n, AstNode* result)
{
    if (n == null || n.kind != NodeKind.NODE_COMPTIME_BLOCK) return;
    n.p.comptime_block.evaluated     = true;
    n.p.comptime_block.cached_result = result;
    n.flags |= FLAG_COMPTIME;
}

// ── Step range   start..end by step ─────────────────────────────────────────
fn AstNode* node_range_step(AstArena* a,
                              AstNode* start, AstNode* end, AstNode* step,
                              bool inclusive, int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_EXPR_RANGE_STEP, line, col);
    if (n == null) return null;
    n.p.range_step.inclusive = inclusive;
    n.p.range_step.has_step  = (step != null);
    // Also mirror `inclusive` into the shared FLAG_RANGE_INCLUSIVE bit so
    // downstream passes (e.g. ssi_ir.c3's lower_for) that check
    // `node.flags & FLAG_RANGE_INCLUSIVE` — the same check used for a plain
    // NODE_EXPR_RANGE — work uniformly for step-ranges too, without needing
    // to know about the range_step payload variant.
    if (inclusive) n.flags |= FLAG_RANGE_INCLUSIVE;
    AstNode*[3] buf;
    buf[0] = start;
    buf[1] = end;
    buf[2] = step;   // may be null; node_attach skips null only if we check
    usz cnt = (step != null) ? 3u : 2u;
    node_attach(a, n, &buf[0], cnt);
    return n;
}

// ── Inline asm block ─────────────────────────────────────────────────────────
fn AstNode* node_asm_block(AstArena* a,
                             AsmDialect dialect, uint options,
                             uint n_outputs, uint n_inputs, uint n_clobbers,
                             AstNode** kids, usz count, int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_STMT_ASM_BLOCK, line, col);
    if (n == null) return null;
    n.p.asm_block.dialect   = dialect;
    n.p.asm_block.options   = options;
    n.p.asm_block.n_outputs  = n_outputs;
    n.p.asm_block.n_inputs   = n_inputs;
    n.p.asm_block.n_clobbers = n_clobbers;
    node_attach(a, n, kids, count);
    if (options & ASM_OPT_VOLATILE) n.effects |= EFFECT_UNSAFE;
    return n;
}

// ── Structured import ────────────────────────────────────────────────────────
fn AstNode* node_decl_import(AstArena* a,
                               char* path, usz path_len,
                               char* alias_name, usz alias_len,
                               bool is_pub, ImportKind kind,
                               AstNode** kids, usz count, int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_DECL_IMPORT, line, col);
    if (n == null) return null;
    n.p.import_decl.path       = path;
    n.p.import_decl.path_len   = path_len;
    n.p.import_decl.alias_name = alias_name;
    n.p.import_decl.alias_len  = alias_len;
    n.p.import_decl.is_pub     = is_pub;
    n.p.import_decl.kind       = kind;
    node_attach(a, n, kids, count);
    return n;
}

// ── Trivia wrapper ───────────────────────────────────────────────────────────
fn AstNode* node_trivia(AstArena* a, AstNode* real_node,
                          char* text, usz text_len, bool has_doc,
                          int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_TRIVIA, line, col);
    if (n == null) return null;
    n.p.trivia.text     = text;
    n.p.trivia.text_len = text_len;
    n.p.trivia.has_doc  = has_doc;
    if (real_node != null)
    {
        AstNode*[1] buf;
        buf[0] = real_node;
        node_attach(a, n, &buf[0], 1);
    }
    return n;
}

// ── Doc-comment node ─────────────────────────────────────────────────────────
fn AstNode* node_doc_comment(AstArena* a, char* text, usz len, int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_DOC_COMMENT, line, col);
    if (n == null) return null;
    n.p.lit_str.ptr = text;
    n.p.lit_str.len = len;
    return n;
}

// ── FnData helpers ───────────────────────────────────────────────────────────
// Set function metadata on a NODE_DECL_FN node (called by the parser once it
// has scanned all clauses of a function declaration).
fn void node_fn_set_meta(AstNode* fn_node, uint arity, uint clause_count,
                           bool is_recursive, bool is_tail_recursive,
                           bool is_extern, bool is_variadic, uint intern_name_id)
{
    if (fn_node == null || fn_node.kind != NodeKind.NODE_DECL_FN) return;
    fn_node.p.fn_data.arity             = arity;
    fn_node.p.fn_data.clause_count      = clause_count;
    fn_node.p.fn_data.is_recursive      = is_recursive;
    fn_node.p.fn_data.is_tail_recursive = is_tail_recursive;
    fn_node.p.fn_data.is_extern         = is_extern;
    fn_node.p.fn_data.is_variadic       = is_variadic;
    fn_node.p.fn_data.intern_name_id    = intern_name_id;
}

// ── ClauseData helpers ───────────────────────────────────────────────────────
fn void node_clause_set_meta(AstNode* clause, uint idx, uint total, bool has_guard)
{
    if (clause == null || clause.kind != NodeKind.NODE_CLAUSE) return;
    clause.p.clause_data.clause_idx    = idx;
    clause.p.clause_data.total_clauses = total;
    clause.p.clause_data.has_guard     = has_guard;
    clause.p.clause_data.pattern_matrix_cache = null;
    if (has_guard) clause.flags |= FLAG_REFUTABLE;
}

// ── MatchData helpers ────────────────────────────────────────────────────────
fn void node_match_set_meta(AstNode* match, uint arm_count, bool has_guard, bool is_stmt)
{
    if (match == null || match.kind != NodeKind.NODE_EXPR_MATCH) return;
    match.p.match_data.arm_count            = arm_count;
    match.p.match_data.is_exhaustive_proven = false;
    match.p.match_data.has_guard            = has_guard;
    match.p.match_data.is_stmt              = is_stmt;
}

fn void node_match_mark_exhaustive(AstNode* match)
{
    if (match == null || match.kind != NodeKind.NODE_EXPR_MATCH) return;
    match.p.match_data.is_exhaustive_proven = true;
    match.flags |= FLAG_EXHAUSTIVE;
}

// ── Intern-aware identifier builder ─────────────────────────────────────────
// Like node_ident but also interns the name, setting intern_id on the node.
fn AstNode* node_ident_interned(AstArena* a, char* name_ptr, usz name_len, int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_IDENT, line, col);
    if (n == null) return null;
    n.p.ident.name_ptr = name_ptr;
    n.p.ident.name_len = name_len;
    uint id = a.intern.intern(name_ptr, name_len);
    n.p.ident.intern_id = id;
    n.intern_id         = id;
    n.flags |= FLAG_INTERNED;
    return n;
}

// Append a single child to an already-built node (used by MSP code generation).
// Allocates a new arena array one slot larger.  O(n) but rare.
fn void add_child(AstArena* a, AstNode* parent, AstNode* child)
{
    if (parent == null || child == null) return;
    usz new_count = parent.child_count + 1;
    AstNode** arr = (AstNode**)arena_alloc(a, new_count * NodePtr::size, NodePtr::alignment);
    if (arr == null) return;
    for (usz i = 0; i < parent.child_count; i++) arr[i] = parent.children[i];
    arr[parent.child_count] = child;
    parent.children   = arr;
    parent.child_count = new_count;
    parent.effects |= child.effects;
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

// Helper: build an identifier node (NODE_IDENT or NODE_TYPEVAR).
fn AstNode* node_ident(AstArena* a, char* name_ptr, usz name_len, int line, int col)
{
    AstNode* n = node_raw(a, NodeKind.NODE_IDENT, line, col);
    if (n == null) return null;
    n.p.ident.name_ptr = name_ptr;
    n.p.ident.name_len = name_len;
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
                // INT64_MIN / -1 overflows (result doesn't fit in i64) and is
                // undefined behavior for the HOST's signed division — don't
                // fold it at compile time; let it become a runtime operation
                // instead (whose UB policy, if any, is the codegen's concern).
                if (sg && x == 0x8000000000000000u && sy == -1) return null;
                if (sg) return mark_folded(node_int(a, (ulong)(sx / sy), bits, sg, line, col));
                return mark_folded(node_int(a, x / y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_PERCENT:
                if (y == 0) return null;
                if (sg && x == 0x8000000000000000u && sy == -1) return null;
                if (sg) return mark_folded(node_int(a, (ulong)(sx % sy), bits, sg, line, col));
                return mark_folded(node_int(a, x % y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_AMP:     return mark_folded(node_int(a, x & y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_PIPE:    return mark_folded(node_int(a, x | y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_XOR:     return mark_folded(node_int(a, x ^ y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_LSHIFT:
                // A shift count >= 64 (or negative, read as signed) is
                // undefined behavior for the HOST's shift operator too — do
                // not fold; let the runtime operation (and its own overflow/
                // UB policy) handle it instead of invoking host UB here.
                if (y >= 64 || sy < 0) return null;
                return mark_folded(node_int(a, x << y, bits, sg, line, col));
            case lexer::TokenType.TOKEN_RSHIFT:
                // arithmetic shift for signed, logical for unsigned
                if (y >= 64 || sy < 0) return null;
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
        case NODE_EXPR_LABELED:      return "Labeled";
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
        case NODE_EXPR_VOLATILE_LOAD:   return "VolLoad";
        case NODE_EXPR_VOLATILE_STORE:  return "VolStore";
        case NODE_EXPR_ATOMIC_RMW:      return "AtomicRmw";
        case NODE_EXPR_ATOMIC_CMPXCHG:  return "AtomicCmpxchg";
        case NODE_EXPR_FENCE:           return "Fence";
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
        case NODE_SIGMA:                return "Sigma";
        case NODE_PHI:                  return "Phi";
        case NODE_ERROR_RECOVERY:       return "ErrorRecovery";
        case NODE_DECL_OPERATOR:        return "DeclOperator";
        case NODE_INTERPOLATED_STRING:  return "InterpString";
        case NODE_COMPTIME_BLOCK:       return "ComptimeBlock";
        case NODE_EXPR_RANGE_STEP:      return "RangeStep";
        case NODE_STMT_ASM_BLOCK:       return "AsmBlock";
        case NODE_DECL_IMPORT:          return "DeclImport";
        case NODE_PATTERN_MATRIX:       return "PatternMatrix";
        case NODE_TRIVIA:               return "Trivia";
        case NODE_DOC_COMMENT:          return "DocComment";
        default:                        return "?";
    }
}

// ── Union variant helpers (tagged-sum support) ─────────────────────────────
// A union type node resolves (through TypeVar/TypeDecl) to a NODE_DECL_UNION
// whose EXPR_BLOCK child lists variant NODE_FIELD_DECLs: [name, payloadType].
// The tagged repr is `{ i32, i64 }` (variant ordinal + 64-bit payload slot),
// the same shape the `?` desugar and DECL_ENUM printing already assume.

// Return the NODE_DECL_UNION behind a type node, or null.
fn AstNode* union_decl_of(AstNode* ty)
{
    if (ty == null) return null;
    AstNode* r = null;
    if (ty.kind == NodeKind.NODE_TYPEVAR && ty.resolved != null) r = ty.resolved;
    if (r == null && ty.kind == NodeKind.NODE_DECL_UNION) r = ty;
    if (r != null)
    {
        if (r.kind == NodeKind.NODE_DECL_UNION) return r;
        if (r.kind == NodeKind.NODE_DECL_TYPE && r.child_count >= 1)
        {
            AstNode* body = r.children[r.child_count - 1];
            if (body != null && body.kind == NodeKind.NODE_DECL_UNION) return body;
        }
    }
    return null;
}

// Return the NODE_DECL_ENUM behind a type node, or null. Mirrors
// union_decl_of for the enum repr — same tagged { i32, i64 } shape.
fn AstNode* enum_decl_of(AstNode* ty)
{
    if (ty == null) return null;
    AstNode* r = null;
    if (ty.kind == NodeKind.NODE_TYPEVAR && ty.resolved != null) r = ty.resolved;
    if (r == null && ty.kind == NodeKind.NODE_DECL_ENUM) r = ty;
    if (r != null)
    {
        if (r.kind == NodeKind.NODE_DECL_ENUM) return r;
        if (r.kind == NodeKind.NODE_DECL_TYPE && r.child_count >= 1)
        {
            AstNode* body = r.children[r.child_count - 1];
            if (body != null && body.kind == NodeKind.NODE_DECL_ENUM) return body;
        }
    }
    return null;
}

// Find an enum's variant ordinal (0-based discriminant, declaration order of
// the variant nodes) for `name`, or -1. Variant decls whose head ident is
// pre-resolved to the variant node are matched by IDENT NODE — the
// declaration-order child — so aliases can't spoof a name.
fn int enum_variant_lookup(AstNode* edecl, char* name, usz name_len)
{
    if (edecl == null || edecl.kind != NodeKind.NODE_DECL_ENUM || name == null) return -1;
    int ord = 0;
    for (usz evi = 1; evi < edecl.child_count; evi++)
    {
        AstNode* ev = edecl.children[evi];
        if (ev == null || ev.kind != NodeKind.NODE_ENUM_VARIANT) continue;
        AstNode* vn = ev.child_count >= 1 ? ev.children[0] : null;
        if (vn != null
            && vn.p.ident.name_ptr != null
            && vn.p.ident.name_len == name_len)
        {
            bool eq = true;
            for (usz ci = 0; ci < name_len; ci++)
            {
                if (vn.p.ident.name_ptr[ci] != name[ci]) { eq = false; break; }
            }
            if (eq) return ord;
        }
        ord++;
    }
    return -1;
}

// Find a union's variant field-decl index + payload type for `name`.
// Returns the 0-based variant ordinal (the discriminant), or -1.
// `out_payload` receives the payload type node (NODE_EXPR_UNIT for none).
fn int union_variant_lookup(AstNode* udecl, char* name, usz name_len, AstNode** out_payload)
{
    if (out_payload != null) *out_payload = null;
    if (udecl == null || udecl.kind != NodeKind.NODE_DECL_UNION || name == null) return -1;
    AstNode* blk = null;
    for (usz i = 0; i < udecl.child_count; i++)
    {
        AstNode* c = udecl.children[i];
        if (c != null && c.kind == NodeKind.NODE_EXPR_BLOCK) { blk = c; break; }
    }
    if (blk == null) return -1;
    int ord = 0;
    for (usz i = 0; i < blk.child_count; i++)
    {
        AstNode* fd = blk.children[i];
        if (fd == null || fd.kind != NodeKind.NODE_FIELD_DECL || fd.child_count < 1) continue;
        AstNode* fn_node = fd.children[0];
        if (fn_node != null && fn_node.p.ident.name_len == name_len)
        {
            bool eq = true;
            for (usz k = 0; k < name_len; k++)
            {
                if (fn_node.p.ident.name_ptr[k] != name[k]) { eq = false; break; }
            }
            if (eq)
            {
                if (out_payload != null && fd.child_count >= 2) *out_payload = fd.children[1];
                return ord;
            }
        }
        ord++;
    }
    return -1;
}

// True when a payload type fits the 64-bit repr slot: iN/uN, bool, ptr,
// float/double, or unit (no payload). Everything else (tuples, structs,
// unions, arrays, slices) is not lowered yet.
fn bool union_payload_is_scalar(AstNode* ty)
{
    if (ty == null) return true;
    if (ty.kind == NodeKind.NODE_EXPR_UNIT) return true;
    if (ty.kind == NodeKind.NODE_TYPE_PTR) return true;
    if (ty.kind != NodeKind.NODE_TYPE_PRIMITIVE) return false;
    char* n = ty.p.ident.name_ptr;
    usz   l = ty.p.ident.name_len;
    if (l == 0) return false;
    if (n[0] == 'i' || n[0] == 'u')
    {
        // iN/uN with digits, width must be ≤ 64
        long w = 0;
        for (usz k = 1; k < l; k++)
        {
            if (n[k] < '0' || n[k] > '9') return false;
            w = w * 10 + (long)(n[k] - '0');
        }
        return w >= 1 && w <= 64;
    }
    if (l == 4 && n[0]=='b' && n[1]=='o' && n[2]=='o' && n[3]=='l') return true;
    if (l == 3 && n[0]=='p' && n[1]=='t' && n[2]=='r')             return true;
    if (l == 3 && n[0]=='f' && n[1]=='3' && n[2]=='2')             return true;
    if (l == 3 && n[0]=='f' && n[1]=='6' && n[2]=='4')             return true;
    return false;
}

// Representation rule for union declarations (r13) — v.md §9 ordains the
// untagged C-union ("same bytes, different interpretation", accessed by
// field name) and the implementation also has the r7 discriminated union
// ({ i32 tag, i64 payload }, dispatched by `{ variant: binder }` patterns /
// `Make.v(...)` constructors). Both use the surface keyword `union`; the
// shapes are distinguished by payload kinds:
//
//   * ANY unit-payload variant (`none : ()`)  → tagged discriminated union.
//     the unit variant only has meaning as a discriminant marker.
//   * ALL variants carry data payloads        → untagged C-union: every
//     field overlaps one 64-bit bitbox. `union Res ok : i32 / err : i32`
//     therefore picks the C-union (it has no meaningful discriminant), and
//     matching such a value by variant pattern is a hard type error — the
//     repr holds no tag to test.
fn bool union_is_c_union(AstNode* udecl)
{
    if (udecl == null || udecl.kind != NodeKind.NODE_DECL_UNION) return false;
    AstNode* blk = null;
    for (usz i = 0; i < udecl.child_count; i++)
    {
        AstNode* c = udecl.children[i];
        if (c != null && c.kind == NodeKind.NODE_EXPR_BLOCK) { blk = c; break; }
    }
    if (blk == null) return false;
    int nfields = 0;
    for (usz i = 0; i < blk.child_count; i++)
    {
        AstNode* fd = blk.children[i];
        if (fd == null || fd.kind != NodeKind.NODE_FIELD_DECL) continue;
        nfields++;
        AstNode* pt = fd.child_count >= 2 ? fd.children[1] : null;
        if (pt == null || pt.kind == NodeKind.NODE_EXPR_UNIT) return false;
    }
    return nfields >= 1;
}

// ── Algebraic-effect operation queries ───────────────────────────────────────
// Pure AST queries over effect declarations (resolver .resolved links), shared
// by typecheck, ssi lowering and codegen. Previously lived in ssi_ir.c3 where
// the typechecker could not reach them — arm binder typing needs exactly the
// same ground truth (op arity, param types) as the runtime lowering.

// Find the EffectOpDecl for an effect method call/nodepair.
// child[0] = effect typevar, child[1] = op ident
fn AstNode* effect_op_decl_of(AstNode* method_call)
{
    if (method_call == null || method_call.child_count < 2) return null;
    AstNode* op_ident = method_call.children[1];
    if (op_ident == null) return null;
    // Fast path: resolver already linked the op ident to its EffectOpDecl.
    if (op_ident.resolved != null && op_ident.resolved.kind == NodeKind.NODE_EFFECT_OP_DECL)
    {
        return op_ident.resolved;
    }
    // Slow path: search the effect declaration manually (resolver did not link it).
    AstNode* effect_tyvar = method_call.children[0];
    AstNode* effect_decl = (effect_tyvar != null) ? effect_tyvar.resolved : null;
    if (effect_decl == null || effect_decl.kind != NodeKind.NODE_DECL_EFFECT) { return null; }
    // Effect decl: children[0]=TypeVar(name), children[1]=Block(op decls)
    AstNode* body = null;
    for (usz bi = 0; bi < effect_decl.child_count; bi++)
    {
        AstNode* bc = effect_decl.children[bi];
        if (bc != null && bc.kind == NodeKind.NODE_EXPR_BLOCK) { body = bc; break; }
    }
    if (body == null) { return null; }
    char* want_name = op_ident.p.ident.name_ptr;
    usz   want_len  = op_ident.p.ident.name_len;
    for (usz oi = 0; oi < body.child_count; oi++)
    {
        AstNode* op = body.children[oi];
        if (op == null || op.kind != NodeKind.NODE_EFFECT_OP_DECL || op.child_count < 1) { continue; }
        AstNode* op_name = op.children[0];
        if (op_name == null) { continue; }
        char* nm = op_name.p.ident.name_ptr;
        usz   nl = op_name.p.ident.name_len;
        if (nl == want_len && nm != null)
        {
            bool match = true;
            for (usz k = 0; k < nl; k++) { if (nm[k] != want_name[k]) { match = false; break; } }
            if (match) { return op; }
        }
    }
    return null;
}

// The op head of a handler arm (children[0]) has the same
// [EffectTypeVar, op_ident] shape as an effect method call's first two
// children, so it resolves through effect_op_decl_of directly.
fn AstNode* effect_op_decl_of_arm(AstNode* arm)
{
    if (arm == null || arm.kind != NodeKind.NODE_HANDLER_ARM || arm.child_count < 1)
    {
        return null;
    }
    AstNode* head = arm.children[0];
    if (head == null || head.child_count < 2) { return null; }
    return effect_op_decl_of(head);
}

// Declared parameter count of the op a handler arm dispatches, or -1 when the
// op declaration can't be found (the resolver has already errored; the caller
// then falls back to a positional guess so lowering can still finish).
fn long effect_op_arity_of_arm(AstNode* arm)
{
    AstNode* op_decl = effect_op_decl_of_arm(arm);
    if (op_decl == null || op_decl.child_count < 2) return -1;
    AstNode* tyfn = op_decl.children[1];   // EffectOpDecl[name, TyFn]
    if (tyfn == null || tyfn.kind != NodeKind.NODE_TYPE_FN || tyfn.child_count < 2) return -1;
    AstNode* params = tyfn.children[0];    // TyFn[params, ret]
    if (params == null) return -1;
    if (params.kind == NodeKind.NODE_EXPR_UNIT || params.kind == NodeKind.NODE_LIT_BOTTOM) return 0;
    if (params.kind == NodeKind.NODE_TYPE_TUPLE) return (long)params.child_count;
    return 1;
}

// Declared parameter type at flat index `idx` for an EffectOpDecl's TyFn, or
// null when unknown/out of range. Mirrors the flattening view of the runtime
// arg-slot ABI exactly.
fn AstNode* effect_op_param_type(AstNode* op_decl, int idx)
{
    if (op_decl == null || idx < 0 || op_decl.child_count < 2) return null;
    AstNode* tyfn = op_decl.children[1];
    if (tyfn == null || tyfn.kind != NodeKind.NODE_TYPE_FN || tyfn.child_count < 2) return null;
    AstNode* params = tyfn.children[0];
    if (params == null) return null;
    if (params.kind == NodeKind.NODE_EXPR_UNIT || params.kind == NodeKind.NODE_LIT_BOTTOM) return null;
    if (params.kind == NodeKind.NODE_TYPE_TUPLE)
    {
        return idx < (int)params.child_count ? params.children[idx] : null;
    }
    return idx == 0 ? params : null;
}

// `()` in handler-arm binder position: the zero-arg placeholder pattern
// (`State.get () k -> ...`). It names NO op argument and consumes no slot.
fn bool is_arm_unit_binder(AstNode* b)
{
    if (b == null) return false;
    if (b.kind == NodeKind.NODE_EXPR_UNIT) return true;
    return b.kind == NodeKind.NODE_PATTERN_TUPLE && b.child_count == 0;
}
