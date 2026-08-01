// ============================================================================
// pfront_core.c3 — Pride front-end: AST substrate, arena, interner, diagnostics
// ----------------------------------------------------------------------------
// Part 1 of the from-scratch front end (`pfront`). This module owns:
//   * NodeKind        — the AST vocabulary (self-contained, not ast.c3's)
//   * PNode           — the AST node, with resolution + type slots built in
//   * Arena           — bump allocator for nodes / child arrays / strings
//   * Interner        — string interning with FNV-1a, used by the resolver
//   * DiagBag         — unified diagnostic sink (parse + resolve share it)
//   * SymTab / Scope  — lexical scope chain (hash-bucketed, arena-backed)
//   * Module registry — the load-once cache that makes `use` real
//
// Design notes that matter downstream:
//   1. Every PNode carries `resolved` (decl it refers to) and `sym` (symbol
//      slot). The parser fills structure; the resolver fills these. There is
//      no separate "resolve pass over a stub AST" — see pfront_resolve.c3.
//   2. Names are interned at PARSE time, so resolution compares uint ids
//      rather than doing memcmp per lookup. This is what makes cross-module
//      resolution cheap enough to run over a 257-module stdlib.
//   3. The arena never frees individual nodes. One `destroy` frees all slabs.
//      Slabs are chained, so we never realloc-and-invalidate live pointers.
// ============================================================================

module pfront_core;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn void* memset(void* dst, int value, usz n);
extern fn void* memcpy(void* dst, void* src, usz n);
extern fn int   printf(char* fmt, ...);

// ── Effect bitmask ──────────────────────────────────────────────────────────
const ulong EFF_PURE   = 0;
const ulong EFF_IO     = 1;
const ulong EFF_ALLOC  = 2;
const ulong EFF_UNSAFE = 4;
const ulong EFF_UB     = 8;
const ulong EFF_PANIC  = 16;
const ulong EFF_DIVERGE = 32;

// ── Node flags ──────────────────────────────────────────────────────────────
const uint NF_NONE        = 0;
const uint NF_MUT         = 1;      // `let mut`, `&mut T`
const uint NF_INCLUSIVE   = 2;      // ..= range
const uint NF_PUB         = 4;      // exported from its module
const uint NF_RESOLVED    = 8;      // resolver has visited and bound this node
const uint NF_TYPED       = 16;     // type slot is populated
const uint NF_USED        = 32;     // referenced at least once (unused-binding lint)
const uint NF_REFUTABLE   = 64;     // pattern may fail to match
const uint NF_EXHAUSTIVE  = 128;    // match/clause set proven exhaustive
const uint NF_OPEN_ROW    = 256;    // effect row has open tail `..r`
const uint NF_VARIADIC    = 512;    // `...` in a parameter list
const uint NF_EXTERN      = 1024;   // extern linkage
const uint NF_GLOB        = 2048;   // `use m.*`
const uint NF_ERROR       = 4096;   // error-recovery placeholder
const uint NF_SYNTHETIC   = 8192;   // compiler-generated, not from source
const uint NF_ADDR_TAKEN  = 16384;  // `&x` appears somewhere
const uint NF_TAIL        = 32768;  // tail-call annotated
/*
 A `do ... while cond` loop: the body runs BEFORE the first test.

 Carried as a flag on N_EXPR_WHILE rather than as its own node kind
 because everything else about the two is identical -- one condition, one
 body, the same break/continue targets -- and a separate kind would mean
 every consumer needs a second case that does the same thing. The flag is
 the difference, and it is exactly one bit of difference.
*/
const uint NF_POSTTEST    = 65536;  // do { body } while cond

// ── AST vocabulary ──────────────────────────────────────────────────────────
// Grouped so range checks (is_decl / is_expr / is_pattern / is_type) are
// simple bounds tests rather than long switch chains.
enum NodeKind : int
{
    // -- structural -----------------------------------------------------
    N_INVALID,
    N_PROGRAM,
    N_MODULE,           // `mod name` + its declarations
    N_MODULE_PATH,      // a.b.c  (children = N_PATH_SEG)
    N_PATH_SEG,
    N_USE,              // `use path` / `use path.*` / `use path as x`
    N_USE_ITEM,         // one entry of `use path.{a, b as c}`
    N_DOC,

    // -- declarations (N_DECL_FIRST .. N_DECL_LAST) ----------------------
    N_DECL_FN,
    N_DECL_LET,
    N_DECL_CONST,
    N_DECL_STATIC,
    N_DECL_TYPE,        // type alias
    N_DECL_STRUCT,
    N_DECL_UNION,
    N_DECL_ENUM,
    N_DECL_NEWTYPE,
    N_DECL_EFFECT,
    N_DECL_INTERFACE,
    N_DECL_IMPL,
    N_DECL_EXTERN_FN,
    N_DECL_FIELD,       // struct/union field
    N_DECL_VARIANT,     // enum variant
    N_DECL_EFFECT_OP,   // one `op : T -> U` inside an effect
    N_DECL_PARAM,       // a function parameter (binder + type)
    N_DECL_TYPEPARAM,   // generic type parameter

    // -- clauses / arms --------------------------------------------------
    N_CLAUSE,           // `| pattern -> body` of a multi-arm fn
    N_MATCH_ARM,
    N_HANDLER_ARM,
    N_GUARD,

    // -- statements ------------------------------------------------------
    N_STMT_EXPR,
    N_STMT_RETURN,
    N_STMT_BREAK,
    N_STMT_CONTINUE,
    N_STMT_DEFER,
    N_STMT_ASSIGN,
    N_STMT_COMPOUND_ASSIGN,
    N_BLOCK,

    // -- expressions -----------------------------------------------------
    N_EXPR_INT,
    N_EXPR_FLOAT,
    N_EXPR_BOOL,
    N_EXPR_CHAR,
    N_EXPR_STRING,
    N_EXPR_BYTES,
    N_EXPR_NULL,
    N_EXPR_UNIT,
    N_EXPR_IDENT,
    N_EXPR_PATH,        // a.b.c used as a value
    N_EXPR_SELF,
    N_EXPR_BINARY,
    N_EXPR_UNARY,
    N_EXPR_CALL,
    N_EXPR_METHOD,      // receiver.method(args)
    N_EXPR_FIELD,       // receiver.field
    N_EXPR_INDEX,
    N_EXPR_SLICE,
    N_EXPR_CAST,
    N_EXPR_TUPLE,
    N_EXPR_ARRAY,
    N_EXPR_STRUCT_LIT,
    N_EXPR_FIELD_INIT,
    N_EXPR_IF,
    N_EXPR_MATCH,
    N_EXPR_WHILE,
    N_EXPR_FOR,
    N_EXPR_LOOP,
    N_EXPR_LAMBDA,
    N_EXPR_RANGE,
    N_EXPR_ASSIGN,
    /*
     NOTE: `|>` does NOT use a dedicated kind. It is an N_EXPR_BINARY whose
     operator token is TOKEN_PIPELINE, with p.aux == 1 marking the `*`
     fixpoint form. A separate N_EXPR_PIPELINE existed with no producer and
     no consumer, which made the enum look like it supported a construct it
     did not. Removed rather than left as decoration.

     `await` is likewise absent: it is not in the spec's 79-keyword list.
    */
    N_EXPR_TRY,         // expr?
    N_EXPR_REF,         // &expr / &mut expr
    N_EXPR_DEREF,       // *expr
    N_EXPR_ALLOC,
    N_EXPR_FREE,
    N_EXPR_SIZEOF,
    N_EXPR_ALIGNOF,
    N_EXPR_OFFSETOF,
    N_EXPR_TRANSMUTE,
    N_EXPR_SYSCALL,
    N_EXPR_ASM,
    N_EXPR_UNSAFE,
    N_EXPR_UNCHECKED,
    N_EXPR_COMPTIME,
    N_EXPR_QUOTE,
    N_EXPR_SPLICE,
    // MSP operators (spec §20). Stage-NEUTRAL: `reify` turns a value into
    // its representation and `eval` runs one, so neither defers to a later
    // stage and neither may be modelled as quotation.
    N_EXPR_REIFY,
    N_EXPR_EVAL,
    N_EXPR_PERFORM,     // perform E.op(args)
    N_EXPR_HANDLE,      // handle comp | arms
    N_EXPR_RESUME,
    N_EXPR_ASSERT,
    N_EXPR_ASSUME,
    N_EXPR_UB,
    /*
     `poison` — a value that propagates UB IF USED (spec §14). Distinct
     from `ub!`, which is an immediate ⊥-typed statement requiring an
     enclosing `unsafe`. Reusing N_EXPR_UB made every `poison` demand an
     `unsafe` block the spec does not ask for.
    */
    N_EXPR_POISON,
    N_EXPR_UNREACHABLE,
    N_EXPR_TRAP,
    N_EXPR_ATOMIC,
    N_EXPR_FENCE,
    N_EXPR_VOLATILE,

    // -- patterns --------------------------------------------------------
    N_PAT_WILDCARD,
    N_PAT_IDENT,
    N_PAT_LITERAL,
    N_PAT_TUPLE,
    N_PAT_ARRAY,
    N_PAT_STRUCT,
    N_PAT_FIELD,
    N_PAT_VARIANT,      // Enum.Variant(payload)
    N_PAT_RANGE,
    N_PAT_OR,
    N_PAT_REF,
    N_PAT_REST,         // ..

    // -- types -----------------------------------------------------------
    N_TY_NAME,
    N_TY_PATH,
    N_TY_PTR,
    N_TY_REF,
    N_TY_ARRAY,
    N_TY_SLICE,
    N_TY_TUPLE,
    N_TY_FN,
    N_TY_GENERIC,       // Name<A, B>
    N_TY_UNION,         // A ∪ B
    N_TY_INTERSECT,     // A ∩ B
    N_TY_NEGATION,      // ¬A
    N_TY_BOTTOM,
    N_TY_UNIT,
    N_TY_SELF,
    N_TY_INFER,         // `_` in type position
    N_TY_EFFECT_ROW,
    N_TY_EFFECT_ELEM,
    N_TY_WHERE,
    N_TY_CONSTRAINT,

    /*
     Quantified types, spec §13.4: `∀ A . A -> A`, `∃ T . T ∩ Eq<T>`.
     children[0] is the bound type variable, children[1] the body.
    */
    N_TY_FORALL,
    N_TY_EXISTS,

    /*
     `typeof(expr)` — the type of an expression, spec §14's keyword list.
     children[0] is the EXPRESSION, which must be resolved as one.

     It was building an N_TY_NAME with no name and an unvisited expression
     child, so the operand came out as an unresolved identifier and the
     type itself was nameless. A distinct kind is what lets the resolver
     tell "resolve my child as an expression" from "look my name up".
    */
    N_TY_TYPEOF,

    /*
     A refinement predicate in type position, spec §13.1:
       `i32 ∩ (> 0)`, `f32 ∩ (>= 0.0) ∩ (<= 1.0)`
     `p.op` holds the comparison token, children[0] the bound expression.
     It is a TYPE node rather than an expression because it only ever
     appears as an operand of the set algebra.
    */
    N_TY_REFINE,

    N_KIND_COUNT
}

// Range markers for cheap category tests.
const NodeKind N_DECL_FIRST = NodeKind.N_DECL_FN;
const NodeKind N_DECL_LAST  = NodeKind.N_DECL_TYPEPARAM;
const NodeKind N_EXPR_FIRST = NodeKind.N_EXPR_INT;
const NodeKind N_EXPR_LAST  = NodeKind.N_EXPR_VOLATILE;
const NodeKind N_PAT_FIRST  = NodeKind.N_PAT_WILDCARD;
const NodeKind N_PAT_LAST   = NodeKind.N_PAT_REST;
const NodeKind N_TY_FIRST   = NodeKind.N_TY_NAME;
const NodeKind N_TY_LAST    = NodeKind.N_TY_REFINE;

fn bool is_decl(NodeKind k)    { return (int)k >= (int)N_DECL_FIRST && (int)k <= (int)N_DECL_LAST; }
fn bool is_expr(NodeKind k)    { return (int)k >= (int)N_EXPR_FIRST && (int)k <= (int)N_EXPR_LAST; }
fn bool is_pattern(NodeKind k) { return (int)k >= (int)N_PAT_FIRST  && (int)k <= (int)N_PAT_LAST; }
fn bool is_type(NodeKind k)    { return (int)k >= (int)N_TY_FIRST   && (int)k <= (int)N_TY_LAST; }

// ── Payload ─────────────────────────────────────────────────────────────────
// A single struct rather than a union: C3 unions complicate zero-init, and the
// node count here (tens of thousands) makes the extra bytes irrelevant next to
// the correctness win of never reading the wrong union arm.
struct Payload
{
    ulong  ival;        // integer literal / enum ordinal / atomic order
    double fval;        // float literal
    char*  sptr;        // string/char literal bytes, identifier text
    usz    slen;
    int    op;          // operator token (as int, avoids lexer dep here)
    int    aux;         // secondary discriminant (cast kind, asm dialect, ...)
    char   width;       // integer/float bit width (8/16/32/64), 0 = unset
    bool   is_signed;
}

// ── The AST node ────────────────────────────────────────────────────────────
struct PNode
{
    NodeKind kind;
    uint     id;
    int      line;
    int      col;
    uint     span_start;
    uint     span_end;

    uint     name_id;      // interned identifier (0 = anonymous)
    uint     flags;
    ulong    effects;

    PNode*   type_ann;     // declared/annotated type
    PNode*   type_slot;    // inferred type (filled by a later pass)
    PNode*   resolved;     // the declaration this name refers to
    PNode*   parent;
    Symbol*  sym;          // symbol table slot, for decls and resolved idents
    Module*  owner;        // module this node was parsed from

    usz      child_count;
    usz      child_cap;
    PNode**  children;

    Payload  p;
}

// ── Arena ───────────────────────────────────────────────────────────────────
const usz SLAB_SIZE = 4 * 1024 * 1024;
const usz MAX_SLABS = 512;

struct Arena
{
    char*[MAX_SLABS] slabs;
    usz              slab_count;
    usz              cursor;       // offset into the current (last) slab
    usz              cur_cap;
    uint             next_id;
    usz              node_count;
    usz              bytes_used;
    bool             oom;
}

fn bool Arena.init(Arena* a)
{
    a.slab_count = 0;
    a.cursor = 0;
    a.cur_cap = 0;
    a.next_id = 1;
    a.node_count = 0;
    a.bytes_used = 0;
    a.oom = false;
    return a.grow(SLAB_SIZE);
}

fn bool Arena.grow(Arena* a, usz want)
{
    if (a.slab_count >= MAX_SLABS) { a.oom = true; return false; }
    usz cap = SLAB_SIZE;
    while (cap < want) { cap = cap * 2; }
    char* s = (char*)malloc(cap);
    if (s == null) { a.oom = true; return false; }
    memset((void*)s, 0, cap);
    a.slabs[a.slab_count] = s;
    a.slab_count = a.slab_count + 1;
    a.cursor = 0;
    a.cur_cap = cap;
    return true;
}

fn void* Arena.alloc(Arena* a, usz size, usz align)
{
    if (size == 0) { size = 1; }
    usz mask = align - 1;
    usz cur  = (a.cursor + mask) & ~mask;
    if (cur + size > a.cur_cap)
    {
        if (!a.grow(size + align)) { return null; }
        cur = 0;
    }
    char* slab = a.slabs[a.slab_count - 1];
    a.cursor = cur + size;
    a.bytes_used = a.bytes_used + size;
    return (void*)(slab + cur);
}

fn void Arena.destroy(Arena* a)
{
    for (usz i = 0; i < a.slab_count; i++)
    {
        if (a.slabs[i] != null) { free((void*)a.slabs[i]); a.slabs[i] = null; }
    }
    a.slab_count = 0;
    a.cursor = 0;
    a.cur_cap = 0;
}

fn char* Arena.dup(Arena* a, char* src, usz len)
{
    char* d = (char*)a.alloc(len + 1, 1);
    if (d == null) { return null; }
    for (usz i = 0; i < len; i++) { d[i] = src[i]; }
    d[len] = 0;
    return d;
}

// ── Node construction ───────────────────────────────────────────────────────
const usz CHILD_INIT_CAP = 4;

fn PNode* Arena.node(Arena* a, NodeKind k, int line, int col)
{
    PNode* n = (PNode*)a.alloc(PNode::size, 8);
    if (n == null) { return null; }
    n.kind = k;
    n.id = a.next_id;
    a.next_id = a.next_id + 1;
    a.node_count = a.node_count + 1;
    n.line = line;
    n.col = col;
    n.span_start = 0;
    n.span_end = 0;
    n.name_id = 0;
    n.flags = NF_NONE;
    n.effects = EFF_PURE;
    n.type_ann = null;
    n.type_slot = null;
    n.resolved = null;
    n.parent = null;
    n.sym = null;
    n.owner = null;
    n.child_count = 0;
    n.child_cap = 0;
    n.children = null;
    n.p.ival = 0;
    n.p.fval = 0.0;
    n.p.sptr = null;
    n.p.slen = 0;
    n.p.op = 0;
    n.p.aux = 0;
    n.p.width = 0;
    n.p.is_signed = true;
    return n;
}

fn bool Arena.add_child(Arena* a, PNode* parent, PNode* child)
{
    if (parent == null || child == null) { return false; }
    if (parent.child_count == parent.child_cap)
    {
        usz ncap = parent.child_cap == 0 ? CHILD_INIT_CAP : parent.child_cap * 2;
        PNode** arr = (PNode**)a.alloc(ncap * (usz)8, 8);
        if (arr == null) { return false; }
        for (usz i = 0; i < parent.child_count; i++) { arr[i] = parent.children[i]; }
        parent.children = arr;
        parent.child_cap = ncap;
    }
    parent.children[parent.child_count] = child;
    parent.child_count = parent.child_count + 1;
    child.parent = parent;
    // Effects propagate upward: a call inside a block makes the block effectful.
    parent.effects = parent.effects | child.effects;
    return true;
}

fn PNode* Arena.node1(Arena* a, NodeKind k, PNode* c0, int line, int col)
{
    PNode* n = a.node(k, line, col);
    if (n == null) { return null; }
    a.add_child(n, c0);
    return n;
}

fn PNode* Arena.node2(Arena* a, NodeKind k, PNode* c0, PNode* c1, int line, int col)
{
    PNode* n = a.node(k, line, col);
    if (n == null) { return null; }
    a.add_child(n, c0);
    a.add_child(n, c1);
    return n;
}

fn PNode* Arena.node3(Arena* a, NodeKind k, PNode* c0, PNode* c1, PNode* c2, int line, int col)
{
    PNode* n = a.node(k, line, col);
    if (n == null) { return null; }
    a.add_child(n, c0);
    a.add_child(n, c1);
    a.add_child(n, c2);
    return n;
}

// Replace child `i` of `parent`, keeping the parent link correct.
//
// Rewriting passes routinely do `n.children[i] = replacement`, which silently
// leaves `replacement.parent` pointing at wherever the node used to live (or
// at null, for a freshly created node). Every pass that walks UPWARD then
// leaves the tree through a stale pointer, and the verifier reports a
// parent-link break per rewritten node.
//
// Funnelling every in-place replacement through this one function is what
// keeps the invariant true no matter how many passes rewrite the tree.
fn void PNode.set_child(PNode* parent, usz i, PNode* c)
{
    if (parent == null || i >= parent.child_count) { return; }
    parent.children[i] = c;
    if (c != null)
    {
        c.parent = parent;
        parent.effects = parent.effects | c.effects;
    }
}

fn PNode* PNode.child(PNode* n, usz i)
{
    if (n == null || i >= n.child_count) { return null; }
    return n.children[i];
}

// ── String interner ─────────────────────────────────────────────────────────
// FNV-1a into open-addressed buckets. Ids are 1-based so 0 means "no name".
const usz INTERN_BUCKETS = 16384;
const usz INTERN_MAX     = 65536;

struct InternEntry
{
    char* ptr;
    usz   len;
    uint  id;
    uint  hash;
}

struct Interner
{
    InternEntry[INTERN_BUCKETS] buckets;
    char*[INTERN_MAX]           by_id;
    usz[INTERN_MAX]             len_by_id;
    uint                        count;
    Arena*                      arena;
}

fn uint fnv1a(char* s, usz len)
{
    uint h = 2166136261u;
    for (usz i = 0; i < len; i++)
    {
        h = h ^ (uint)(char)s[i];
        h = h * 16777619u;
    }
    if (h == 0) { h = 1; }
    return h;
}

fn bool span_eq(char* a, usz alen, char* b, usz blen)
{
    if (alen != blen) { return false; }
    for (usz i = 0; i < alen; i++) { if (a[i] != b[i]) { return false; } }
    return true;
}

fn void Interner.init(Interner* it, Arena* a)
{
    it.arena = a;
    it.count = 0;
    for (usz i = 0; i < INTERN_BUCKETS; i++)
    {
        it.buckets[i].ptr = null;
        it.buckets[i].len = 0;
        it.buckets[i].id = 0;
        it.buckets[i].hash = 0;
    }
    it.by_id[0] = null;
    it.len_by_id[0] = 0;
}

fn uint Interner.intern(Interner* it, char* s, usz len)
{
    if (s == null || len == 0) { return 0; }
    uint h = fnv1a(s, len);
    usz idx = (usz)h & (INTERN_BUCKETS - 1);
    for (usz probe = 0; probe < INTERN_BUCKETS; probe++)
    {
        InternEntry* e = &it.buckets[idx];
        if (e.ptr == null)
        {
            if ((usz)it.count + 1 >= INTERN_MAX) { return 0; }
            char* copy = it.arena.dup(s, len);
            if (copy == null) { return 0; }
            it.count = it.count + 1;
            uint id = it.count;
            e.ptr = copy;
            e.len = len;
            e.id = id;
            e.hash = h;
            it.by_id[id] = copy;
            it.len_by_id[id] = len;
            return id;
        }
        if (e.hash == h && span_eq(e.ptr, e.len, s, len)) { return e.id; }
        idx = (idx + 1) & (INTERN_BUCKETS - 1);
    }
    return 0;
}

fn char* Interner.text(Interner* it, uint id)
{
    if (id == 0 || id > it.count) { return null; }
    return it.by_id[id];
}

fn usz Interner.text_len(Interner* it, uint id)
{
    if (id == 0 || id > it.count) { return 0; }
    return it.len_by_id[id];
}

// ── Diagnostics ─────────────────────────────────────────────────────────────
enum Severity : int { SEV_ERROR, SEV_WARNING, SEV_NOTE }

enum Phase : int { PH_LEX, PH_PARSE, PH_RESOLVE, PH_MODULE }

struct Diag
{
    Severity sev;
    Phase    phase;
    int      code;      // E0xxx / W0xxx numeric part
    int      line;
    int      col;
    char*    msg;
    char*    hint;      // may be null
    char*    file;      // owning file path, may be null
}

const usz MAX_DIAGS = 4096;

struct DiagBag
{
    Diag[MAX_DIAGS] items;
    usz             count;
    usz             error_count;
    usz             warning_count;
    bool            overflow;
    bool            suppress;    // set during speculative parses
    bool            advisories;  // --lint: surface optional style advice
    usz             advisory_suppressed;
}

fn void DiagBag.init(DiagBag* d)
{
    d.count = 0;
    d.error_count = 0;
    d.warning_count = 0;
    d.overflow = false;
    d.suppress = false;
    d.advisories = false;
    d.advisory_suppressed = 0;
}

fn void DiagBag.add(DiagBag* d, Severity sev, Phase ph, int code,
                    int line, int col, char* msg, char* hint, char* file)
{
    if (d.suppress) { return; }
    if (sev == Severity.SEV_ERROR) { d.error_count = d.error_count + 1; }
    if (sev == Severity.SEV_WARNING) { d.warning_count = d.warning_count + 1; }
    if (d.count >= MAX_DIAGS) { d.overflow = true; return; }
    Diag* it = &d.items[d.count];
    it.sev = sev;
    it.phase = ph;
    it.code = code;
    it.line = line;
    it.col = col;
    it.msg = msg;
    it.hint = hint;
    it.file = file;
    d.count = d.count + 1;
}

fn void DiagBag.error(DiagBag* d, Phase ph, int code, int line, int col, char* msg, char* file)
{
    d.add(Severity.SEV_ERROR, ph, code, line, col, msg, null, file);
}

fn void DiagBag.error_hint(DiagBag* d, Phase ph, int code, int line, int col,
                           char* msg, char* hint, char* file)
{
    d.add(Severity.SEV_ERROR, ph, code, line, col, msg, hint, file);
}

fn void DiagBag.warn(DiagBag* d, Phase ph, int code, int line, int col, char* msg, char* file)
{
    d.add(Severity.SEV_WARNING, ph, code, line, col, msg, null, file);
}

fn void DiagBag.note(DiagBag* d, Phase ph, int code, int line, int col, char* msg, char* file)
{
    d.add(Severity.SEV_NOTE, ph, code, line, col, msg, null, file);
}

// ── Advisories ──────────────────────────────────────────────────────────────
// Pride is an UNTYPED language: the compiler does not get to reject a program
// because a type does not line up. It assumes the developer meant what they
// wrote. Analyses that used to raise hard type errors still RUN — their facts
// drive the optimizer (see pfront_opt.c3) — but they speak only when the user
// explicitly opts in with `--lint`, and then only as warnings.
//
// This is the single chokepoint for that policy. If a diagnostic goes through
// `advisory`, it can never fail a build by default.
fn void DiagBag.advisory(DiagBag* d, Phase ph, int code, int line, int col,
                         char* msg, char* file)
{
    d.advisory_suppressed = d.advisory_suppressed + 1;
    if (!d.advisories) { return; }
    d.advisory_suppressed = d.advisory_suppressed - 1;
    d.add(Severity.SEV_WARNING, ph, code, line, col, msg, null, file);
}

fn void DiagBag.advisory_hint(DiagBag* d, Phase ph, int code, int line, int col,
                              char* msg, char* hint, char* file)
{
    d.advisory_suppressed = d.advisory_suppressed + 1;
    if (!d.advisories) { return; }
    d.advisory_suppressed = d.advisory_suppressed - 1;
    d.add(Severity.SEV_WARNING, ph, code, line, col, msg, hint, file);
}

fn char* sev_name(Severity s)
{
    switch (s)
    {
        case SEV_ERROR:   return "error";
        case SEV_WARNING: return "warning";
        case SEV_NOTE:    return "note";
    }
}

fn char* phase_name(Phase p)
{
    switch (p)
    {
        case PH_LEX:     return "lex";
        case PH_PARSE:   return "parse";
        case PH_RESOLVE: return "resolve";
        case PH_MODULE:  return "module";
    }
}

fn void DiagBag.dump(DiagBag* d)
{
    for (usz i = 0; i < d.count; i++)
    {
        Diag* it = &d.items[i];
        char* f = it.file == null ? (char*)"<input>" : it.file;
        char prefix = it.sev == Severity.SEV_ERROR ? 'E' : 'W';
        printf("  %s:%d:%d: %s [%c%04d/%s] %s\n",
               f, it.line, it.col, sev_name(it.sev),
               prefix, it.code, phase_name(it.phase), it.msg);
        if (it.hint != null) { printf("      hint: %s\n", it.hint); }
    }
    if (d.overflow) { printf("  ... (diagnostic buffer full, further messages dropped)\n"); }
}

// ── Symbols and scopes ──────────────────────────────────────────────────────
enum SymKind : int
{
    SYM_NONE,
    SYM_FN,
    SYM_VALUE,        // let / const / static / param
    SYM_TYPE,         // struct / enum / union / alias / newtype
    SYM_TYPEPARAM,
    SYM_MODULE,
    SYM_EFFECT,
    SYM_EFFECT_OP,
    SYM_VARIANT,
    SYM_FIELD,
    SYM_INTERFACE,
    SYM_LABEL,
    SYM_BUILTIN_TYPE,
    SYM_BUILTIN_FN
}

// Two namespaces, as in most ML-family languages: `Foo` the type and `Foo` the
// constructor can coexist. Labels get their own so `'loop` never collides.
const int NS_VALUE = 0;
const int NS_TYPE  = 1;
const int NS_LABEL = 2;
const int NS_COUNT = 3;

struct Symbol
{
    uint     name_id;
    SymKind  kind;
    int      ns;
    PNode*   decl;
    Module*  owner;
    Symbol*  next;        // bucket chain
    bool     is_pub;
    bool     used;
    int      depth;       // scope depth where it was declared
}

const usz SCOPE_BUCKETS = 64;

struct Scope
{
    Symbol*[SCOPE_BUCKETS] buckets;
    Scope*                 parent;
    int                    depth;
    PNode*                 owner_node;   // fn/block that opened this scope
    bool                   is_fn_boundary;
}

fn void Scope.init(Scope* s, Scope* parent, PNode* owner)
{
    for (usz i = 0; i < SCOPE_BUCKETS; i++) { s.buckets[i] = null; }
    s.parent = parent;
    s.depth = parent == null ? 0 : parent.depth + 1;
    s.owner_node = owner;
    s.is_fn_boundary = false;
}

fn usz sym_bucket(uint name_id, int ns)
{
    uint h = name_id * 2654435761u + (uint)ns * 40503u;
    return (usz)(h & (uint)(SCOPE_BUCKETS - 1));
}

fn Symbol* Scope.lookup_local(Scope* s, uint name_id, int ns)
{
    Symbol* cur = s.buckets[sym_bucket(name_id, ns)];
    while (cur != null)
    {
        if (cur.name_id == name_id && cur.ns == ns) { return cur; }
        cur = cur.next;
    }
    return null;
}

fn Symbol* Scope.lookup(Scope* s, uint name_id, int ns)
{
    Scope* cur = s;
    while (cur != null)
    {
        Symbol* f = cur.lookup_local(name_id, ns);
        if (f != null) { return f; }
        cur = cur.parent;
    }
    return null;
}

fn void Scope.insert(Scope* s, Symbol* sym)
{
    usz b = sym_bucket(sym.name_id, sym.ns);
    sym.next = s.buckets[b];
    s.buckets[b] = sym;
    sym.depth = s.depth;
}

// ── Modules ─────────────────────────────────────────────────────────────────
enum ModState : int
{
    MOD_UNLOADED,
    MOD_LOADING,      // on the stack — revisiting means a cycle
    MOD_PARSED,
    MOD_RESOLVED,
    MOD_FAILED
}

const usz MOD_EXPORT_BUCKETS = 256;

struct Module
{
    uint     name_id;         // interned dotted path, e.g. "pride.core.mem"
    char*    path;            // filesystem path actually loaded
    char*    source;          // owned source buffer
    usz      source_len;
    ModState state;
    PNode*   ast;             // N_MODULE root
    Symbol*[MOD_EXPORT_BUCKETS] exports;   // pub symbols, by (name,ns)
    Module*[64] imports;      // resolved `use` targets
    usz      import_count;
    int      load_order;
}

fn void Module.init(Module* m, uint name_id, char* path)
{
    m.name_id = name_id;
    m.path = path;
    m.source = null;
    m.source_len = 0;
    m.state = ModState.MOD_UNLOADED;
    m.ast = null;
    for (usz i = 0; i < MOD_EXPORT_BUCKETS; i++) { m.exports[i] = null; }
    m.import_count = 0;
    m.load_order = 0;
}

fn usz export_bucket(uint name_id, int ns)
{
    uint h = name_id * 2246822519u + (uint)ns * 3266489917u;
    return (usz)(h & (uint)(MOD_EXPORT_BUCKETS - 1));
}

fn void Module.add_export(Module* m, Symbol* s)
{
    usz b = export_bucket(s.name_id, s.ns);
    s.next = m.exports[b];
    m.exports[b] = s;
}

fn Symbol* Module.find_export(Module* m, uint name_id, int ns)
{
    Symbol* cur = m.exports[export_bucket(name_id, ns)];
    while (cur != null)
    {
        if (cur.name_id == name_id && cur.ns == ns) { return cur; }
        cur = cur.next;
    }
    return null;
}

fn bool Module.add_import(Module* m, Module* dep)
{
    if (m.import_count >= 64) { return false; }
    for (usz i = 0; i < m.import_count; i++) { if (m.imports[i] == dep) { return true; } }
    m.imports[m.import_count] = dep;
    m.import_count = m.import_count + 1;
    return true;
}

// ── Node kind names (diagnostics + AST dump) ────────────────────────────────
fn char* kind_name(NodeKind k)
{
    switch (k)
    {
        case N_INVALID:        return "invalid";
        case N_PROGRAM:        return "program";
        case N_MODULE:         return "module";
        case N_MODULE_PATH:    return "module-path";
        case N_PATH_SEG:       return "path-seg";
        case N_USE:            return "use";
        case N_USE_ITEM:       return "use-item";
        case N_DOC:            return "doc";
        case N_DECL_FN:        return "fn";
        case N_DECL_LET:       return "let";
        case N_DECL_CONST:     return "const";
        case N_DECL_STATIC:    return "static";
        case N_DECL_TYPE:      return "type";
        case N_DECL_STRUCT:    return "struct";
        case N_DECL_UNION:     return "union";
        case N_DECL_ENUM:      return "enum";
        case N_DECL_NEWTYPE:   return "newtype";
        case N_DECL_EFFECT:    return "effect";
        case N_DECL_INTERFACE: return "interface";
        case N_DECL_IMPL:      return "impl";
        case N_DECL_EXTERN_FN: return "extern-fn";
        case N_DECL_FIELD:     return "field";
        case N_DECL_VARIANT:   return "variant";
        case N_DECL_EFFECT_OP: return "effect-op";
        case N_DECL_PARAM:     return "param";
        case N_DECL_TYPEPARAM: return "typaram";
        case N_CLAUSE:         return "clause";
        case N_MATCH_ARM:      return "match-arm";
        case N_HANDLER_ARM:    return "handler-arm";
        case N_GUARD:          return "guard";
        case N_STMT_EXPR:      return "stmt-expr";
        case N_STMT_RETURN:    return "return";
        case N_STMT_BREAK:     return "break";
        case N_STMT_CONTINUE:  return "continue";
        case N_STMT_DEFER:     return "defer";
        case N_STMT_ASSIGN:    return "assign";
        case N_STMT_COMPOUND_ASSIGN: return "compound-assign";
        case N_BLOCK:          return "block";
        case N_EXPR_INT:       return "int";
        case N_EXPR_FLOAT:     return "float";
        case N_EXPR_BOOL:      return "bool";
        case N_EXPR_CHAR:      return "char";
        case N_EXPR_STRING:    return "string";
        case N_EXPR_BYTES:     return "bytes";
        case N_EXPR_NULL:      return "null";
        case N_EXPR_UNIT:      return "unit";
        case N_EXPR_IDENT:     return "ident";
        case N_EXPR_PATH:      return "path";
        case N_EXPR_SELF:      return "self";
        case N_EXPR_BINARY:    return "binary";
        case N_EXPR_UNARY:     return "unary";
        case N_EXPR_CALL:      return "call";
        case N_EXPR_METHOD:    return "method";
        case N_EXPR_FIELD:     return "field-access";
        case N_EXPR_INDEX:     return "index";
        case N_EXPR_SLICE:     return "slice";
        case N_EXPR_CAST:      return "cast";
        case N_EXPR_TUPLE:     return "tuple";
        case N_EXPR_ARRAY:     return "array";
        case N_EXPR_STRUCT_LIT: return "struct-lit";
        case N_EXPR_FIELD_INIT: return "field-init";
        case N_EXPR_IF:        return "if";
        case N_EXPR_MATCH:     return "match";
        case N_EXPR_WHILE:     return "while";
        case N_EXPR_FOR:       return "for";
        case N_EXPR_LOOP:      return "loop";
        case N_EXPR_LAMBDA:    return "lambda";
        case N_EXPR_RANGE:     return "range";
        case N_EXPR_ASSIGN:    return "expr-assign";
        case N_EXPR_TRY:       return "try";
        case N_EXPR_REF:       return "ref";
        case N_EXPR_DEREF:     return "deref";
        case N_EXPR_ALLOC:     return "alloc";
        case N_EXPR_FREE:      return "free";
        case N_EXPR_SIZEOF:    return "sizeof";
        case N_EXPR_ALIGNOF:   return "alignof";
        case N_EXPR_OFFSETOF:  return "offsetof";
        case N_EXPR_TRANSMUTE: return "transmute";
        case N_EXPR_SYSCALL:   return "syscall";
        case N_EXPR_ASM:       return "asm";
        case N_EXPR_UNSAFE:    return "unsafe";
        case N_EXPR_UNCHECKED: return "unchecked";
        case N_EXPR_COMPTIME:  return "comptime";
        case N_EXPR_QUOTE:     return "quote";
        case N_EXPR_SPLICE:    return "splice";
        case N_EXPR_REIFY:     return "reify";
        case N_EXPR_EVAL:      return "eval";
        case N_EXPR_PERFORM:   return "perform";
        case N_EXPR_HANDLE:    return "handle";
        case N_EXPR_RESUME:    return "resume";
        case N_EXPR_ASSERT:    return "assert";
        case N_EXPR_ASSUME:    return "assume";
        case N_EXPR_UB:        return "ub";
        case N_EXPR_POISON:    return "poison";
        case N_EXPR_UNREACHABLE: return "unreachable";
        case N_EXPR_TRAP:      return "trap";
        case N_EXPR_ATOMIC:    return "atomic";
        case N_EXPR_FENCE:     return "fence";
        case N_EXPR_VOLATILE:  return "volatile";
        case N_PAT_WILDCARD:   return "pat-wildcard";
        case N_PAT_IDENT:      return "pat-ident";
        case N_PAT_LITERAL:    return "pat-literal";
        case N_PAT_TUPLE:      return "pat-tuple";
        case N_PAT_ARRAY:      return "pat-array";
        case N_PAT_STRUCT:     return "pat-struct";
        case N_PAT_FIELD:      return "pat-field";
        case N_PAT_VARIANT:    return "pat-variant";
        case N_PAT_RANGE:      return "pat-range";
        case N_PAT_OR:         return "pat-or";
        case N_PAT_REF:        return "pat-ref";
        case N_PAT_REST:       return "pat-rest";
        case N_TY_NAME:        return "ty-name";
        case N_TY_PATH:        return "ty-path";
        case N_TY_PTR:         return "ty-ptr";
        case N_TY_REF:         return "ty-ref";
        case N_TY_ARRAY:       return "ty-array";
        case N_TY_SLICE:       return "ty-slice";
        case N_TY_TUPLE:       return "ty-tuple";
        case N_TY_FN:          return "ty-fn";
        case N_TY_GENERIC:     return "ty-generic";
        case N_TY_UNION:       return "ty-union";
        case N_TY_INTERSECT:   return "ty-intersect";
        case N_TY_NEGATION:    return "ty-negation";
        case N_TY_BOTTOM:      return "ty-bottom";
        case N_TY_UNIT:        return "ty-unit";
        case N_TY_SELF:        return "ty-self";
        case N_TY_INFER:       return "ty-infer";
        case N_TY_EFFECT_ROW:  return "ty-effect-row";
        case N_TY_EFFECT_ELEM: return "ty-effect-elem";
        case N_TY_WHERE:       return "ty-where";
        case N_TY_CONSTRAINT:  return "ty-constraint";
        case N_TY_FORALL:      return "ty-forall";
        case N_TY_EXISTS:      return "ty-exists";
        case N_TY_TYPEOF:      return "ty-typeof";
        case N_TY_REFINE:      return "ty-refine";
        case N_KIND_COUNT:     return "?";
    }
}

fn char* sym_kind_name(SymKind k)
{
    switch (k)
    {
        case SYM_NONE:         return "none";
        case SYM_FN:           return "fn";
        case SYM_VALUE:        return "value";
        case SYM_TYPE:         return "type";
        case SYM_TYPEPARAM:    return "typaram";
        case SYM_MODULE:       return "module";
        case SYM_EFFECT:       return "effect";
        case SYM_EFFECT_OP:    return "effect-op";
        case SYM_VARIANT:      return "variant";
        case SYM_FIELD:        return "field";
        case SYM_INTERFACE:    return "interface";
        case SYM_LABEL:        return "label";
        case SYM_BUILTIN_TYPE: return "builtin-type";
        case SYM_BUILTIN_FN:   return "builtin-fn";
    }
}
