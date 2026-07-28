// integrity.c3 — Frontend integrity verifier (pre-lowering guardrail)
// Implementation language: C3 (host).
// PURPOSE. Before any lowering / LLVM / runtime work consumes the AST, this
// pass AUDITS the invariants that lowering silently assumes. The frontend's
// diagnostics are intentionally SOFT (warnings, not hard errors, per Pride's
// "trust the programmer" design) — but lowering needs a HARD guarantee that the
// tree it walks is well-formed: every value-position name resolved, every
// expression typed, no structurally-broken nodes. A silent gap here is exactly
// what "tangles" a backend.
// This verifier does NOT change semantics. It produces a report (counts +
// precise locations) so that:
//   * the frontend can be proven airtight on a corpus (every count 0), and
//   * the lowering phase can assert these invariants as preconditions.
// Invariants checked (on the FINAL, post-resolve/post-typecheck AST):
//   I1. Every value-position identifier (NODE_IDENT in an expression) has a
//       non-null `.resolved` — i.e. it binds to a declaration. (Module-
//       qualified members and known soft cases are excluded.)
//   I2. Every expression node carries a `.type_annotation` (the type checker
//       reached it). Diverging/None-typed forms are excluded.
//   I3. No NODE_INVALID survives anywhere in the tree (parser recovery sentinel).
//   I4. Structural arity: nodes that lowering destructures by fixed child
//       positions have the children they require (e.g. binary has 2 operands).
// All findings are reported with location; the caller decides severity.

module integrity;

import ast;
import lexer;
import parser;
import resolve;
import typecheck;
import effectcheck;
import lint;

extern fn int printf(char* fmt, ...);
extern fn void* malloc(usz size);
extern fn usz   strlen(char* s);
extern fn void  free(void* ptr);

alias Node = ast::AstNode;
alias Nk = ast::NodeKind;

const usz MAX_FINDINGS = 256;
const int IW_MAX_DEPTH = 1500;

struct Finding { char* msg; int line; int col; }

struct Verifier
{
    Finding[MAX_FINDINGS] findings;
    int    finding_count;
    int    depth;
    bool   overflow;

    // counts by invariant
    int    unresolved_names;
    int    untyped_exprs;
    int    invalid_nodes;
    int    arity_breaks;
}

fn void Verifier.init(Verifier* self)
{
    self.finding_count = 0;
    self.depth = 0;
    self.overflow = false;
    self.unresolved_names = 0;
    self.untyped_exprs = 0;
    self.invalid_nodes = 0;
    self.arity_breaks = 0;
}

fn void Verifier.report(Verifier* self, char* msg, int line, int col)
{
    if (self.finding_count >= (int)MAX_FINDINGS) { self.overflow = true; return; }
    self.findings[self.finding_count].msg = msg;
    self.findings[self.finding_count].line = line;
    self.findings[self.finding_count].col = col;
    self.finding_count++;
}

fn int Verifier.total(Verifier* self)
{
    return self.unresolved_names + self.untyped_exprs + self.invalid_nodes + self.arity_breaks;
}

// An expression whose type the checker legitimately leaves null (diverging or
// statement-like forms), so the absence of a type_annotation is NOT a defect.
fn bool expr_type_optional(Node* n)
{
    // diverging / bottom-typed forms the checker may skip, plus metaprogramming
    // / quotation operands which are not ordinary typed values.
    switch (n.kind)
    {
        case Nk.NODE_UB_BANG:
        case Nk.NODE_STMT_UNREACHABLE:
        case Nk.NODE_STMT_TRAP:
        case Nk.NODE_LIT_BOTTOM:
        case Nk.NODE_SIGIL_TREE:
        case Nk.NODE_SIGIL_DATA:
        case Nk.NODE_SIGIL_BYTES:
        case Nk.NODE_EXPR_RANGE:
            return true;
        default:
            return false;
    }
}

// A cross-module member reference (`m::sq`, `m::sq(n)`) that the type checker
// could NOT resolve to a member (so it has no type) — e.g. an unresolved import
// or a member that doesn't exist. Resolved cross-module members ARE typed now,
// so only the genuinely-unresolved tail is excused.
fn bool is_unresolved_cross_module(Node* n)
{
    if (n == null) return false;
    if (n.kind == Nk.NODE_EXPR_CALL && n.child_count >= 1)
    {
        return is_unresolved_cross_module(n.children[0]);
    }
    if (n.kind == Nk.NODE_EXPR_FIELD && n.child_count >= 2)
    {
        Node* base = n.children[0];
        Node* member = n.children[1];
        if (base == null) return false;
        bool base_is_module =
            (base.resolved != null
             && (base.resolved.kind == Nk.NODE_DECL_MOD || base.resolved.kind == Nk.NODE_DECL_USE
                 || base.resolved.kind == Nk.NODE_DECL_IMPORT))
            || base.kind == Nk.NODE_MODULE_PATH;
        // only excuse it when the member did NOT resolve (truly unknown import)
        if (base_is_module && (member == null || member.resolved == null)) return true;
        return false;
    }
    return false;
}

// A type-level node: its subtree is types/dimensions/kinds, not value exprs.
fn bool is_type_kind(Nk k)
{
    switch (k)
    {
        case Nk.NODE_TYPE_PRIMITIVE:
        case Nk.NODE_TYPE_PATH:
        case Nk.NODE_TYPE_PTR:
        case Nk.NODE_TYPE_REF:
        case Nk.NODE_TYPE_MUT_REF:
        case Nk.NODE_TYPE_ARRAY:
        case Nk.NODE_TYPE_SLICE:
        case Nk.NODE_TYPE_TUPLE:
        case Nk.NODE_TYPE_FN:
        case Nk.NODE_TYPE_UNION:
        case Nk.NODE_TYPE_INTERSECT:
        case Nk.NODE_TYPE_NEGATION:
        case Nk.NODE_TYPE_BOTTOM:
        case Nk.NODE_TYPE_FORALL:
        case Nk.NODE_TYPE_EXISTS:
        case Nk.NODE_TYPE_GENERIC_APP:
        case Nk.NODE_TYPE_REFINEMENT:
        case Nk.NODE_TYPE_TENSOR:
        case Nk.NODE_EFFECT_ROW:
            return true;
        default:
            return false;
    }
}

// Declarative / metaprogramming / effect forms whose subtrees are NOT ordinary
// value expressions. The integrity verifier audits the value/expression code
// that the SSI-IR lowering walks; these forms are handled by dedicated passes
// (IRDL, MSP staging, effect checker) and have their own well-formedness rules.
fn bool is_optedout_kind(Nk k)
{
    switch (k)
    {
        case Nk.NODE_DIALECT:
        case Nk.NODE_IRDL:
        case Nk.NODE_LOWER:
        case Nk.NODE_GRAPH:
        case Nk.NODE_NODE_DECL:
        case Nk.NODE_EDGE_DECL:
        case Nk.NODE_HYPEREDGE_DECL:
        case Nk.NODE_BLOCK_IR:
        case Nk.NODE_OPCODE:
        case Nk.NODE_REGION:
        case Nk.NODE_PGEN:
        case Nk.NODE_REWRITE:
        case Nk.NODE_REWRITE_RULE:
        case Nk.NODE_PATTERN_DECL:
        case Nk.NODE_DECL_EFFECT:
        case Nk.NODE_EFFECT_HANDLE:
        case Nk.NODE_HANDLER_ARM:
        case Nk.NODE_EFFECT_WITH:
        case Nk.NODE_DECL_USE:
        case Nk.NODE_DECL_IMPORT:
        case Nk.NODE_DECL_ENUM:       // variant name idents are definitions, not uses
            return true;
        default:
            return false;
    }
}

// A node kind that INTRODUCES names (its identifier children are binders /
// declarations, not value uses, so they legitimately have no `.resolved`).
fn bool is_decl_kind(Nk k)
{
    switch (k)
    {
        case Nk.NODE_DECL_FN:
        case Nk.NODE_DECL_LET:
        case Nk.NODE_DECL_MUT:
        case Nk.NODE_DECL_CONST:
        case Nk.NODE_DECL_STATIC:
        case Nk.NODE_DECL_TYPE:
        case Nk.NODE_DECL_STRUCT:
        case Nk.NODE_DECL_UNION:
        case Nk.NODE_DECL_EFFECT:
        case Nk.NODE_DECL_MOD:
        case Nk.NODE_DECL_USE:
        case Nk.NODE_DECL_IMPORT:
        case Nk.NODE_PARAM:
        case Nk.NODE_GENERIC_PARAM:
        case Nk.NODE_FIELD_DECL:
        case Nk.NODE_PATTERN_DECL:
        case Nk.NODE_REWRITE_RULE:
        case Nk.NODE_PGEN:
        case Nk.NODE_DIALECT:
        case Nk.NODE_OPCODE:
        case Nk.NODE_REGION:
        case Nk.NODE_BLOCK_IR:
        case Nk.NODE_NODE_DECL:
        case Nk.NODE_EDGE_DECL:
        case Nk.NODE_HYPEREDGE_DECL:
        case Nk.NODE_GRAPH:
        case Nk.NODE_LOWER:
        case Nk.NODE_EFFECT_WITH:
            return true;
        default:
            return false;
    }
}

// A pattern node: its identifier children are BINDERS, not uses.
fn bool is_pattern_kind(Nk k)
{
    switch (k)
    {
        case Nk.NODE_PATTERN_IDENT:
        case Nk.NODE_PATTERN_WILDCARD:
        case Nk.NODE_PATTERN_LITERAL:
        case Nk.NODE_PATTERN_TUPLE:
        case Nk.NODE_PATTERN_OR:
        case Nk.NODE_PATTERN_STRUCT:
        case Nk.NODE_PATTERN_FIELD:
        case Nk.NODE_PATTERN_GUARD:
            return true;
        default:
            return false;
    }
}

// True if an IDENT child at this position is a member/field name that name
// resolution legitimately leaves unresolved (resolved later by type info).
fn bool ident_resolution_optional(Node* parent, usz child_index)
{
    if (parent == null) return false;
    switch (parent.kind)
    {
        case Nk.NODE_EXPR_FIELD:
            return child_index == 1;          // [base, fieldName]
        case Nk.NODE_EXPR_METHOD_CALL:
            return child_index == 1;          // [base, methodName, args...]
        case Nk.NODE_FIELD_INIT:
            return child_index == 0;          // [fieldName, value]
        case Nk.NODE_MODULE_PATH:
        case Nk.NODE_TYPE_PATH:
            return child_index >= 1;          // only head must resolve
        case Nk.NODE_HANDLER_ARM:
            return true;                      // op head + binders
        case Nk.NODE_EFFECT_HANDLE:
            return true;
        default:
            return false;
    }
}

// Recurse, auditing each node. `parent`/`idx` give the slot context; `in_binder`
// is true when this subtree sits in a binder/declaration-name position (so its
// identifiers are binders, not value uses, and must not be flagged unresolved).
fn void Verifier.walk(Verifier* self, Node* n, Node* parent, usz idx, bool in_binder)
{
    if (n == null) return;
    if (self.depth >= IW_MAX_DEPTH) { self.overflow = true; return; }
    self.depth++;
    self.walk_body(n, parent, idx, in_binder);
    self.depth--;
}

fn void Verifier.walk_body(Verifier* self, Node* n, Node* parent, usz idx, bool in_binder)
{
    // I3 — no parser-recovery sentinel survives (checked everywhere).
    if (n.kind == Nk.NODE_INVALID)
    {
        self.invalid_nodes++;
        self.report("INVALID node survived parsing (recovery sentinel reached lowering)", n.line, n.col);
        return;
    }

    // Do not descend into subtrees whose contents are not ordinary value
    // expressions that lowering walks positionally:
    //   * attribute lists / type subtrees (metadata, type-level dims/kinds),
    //   * declarative metaprogramming forms (IRDL rules, dialects, pgen, rewrite,
    //     graph IR), whose bodies are templates/patterns resolved specially,
    //   * effect handlers / handler arms / `use` imports / `with` resources,
    //     which the type checker intentionally does not fully synthesize.
    // These are validated by their own passes; auditing them here would only
    // produce false "untyped"/"unresolved" findings on well-formed programs.
    if (n.kind == Nk.NODE_ATTRIBUTE_LIST || is_type_kind(n.kind)) return;
    if (is_optedout_kind(n.kind)) return;
    // ub! / trap / unreachable carry a diagnostic message operand, not a
    // computed value — don't audit their children as value expressions.
    if (n.kind == Nk.NODE_UB_BANG || n.kind == Nk.NODE_STMT_TRAP
        || n.kind == Nk.NODE_STMT_UNREACHABLE) return;

    // I1 — value-position identifier must be resolved (skip binders/members).
    if (n.kind == Nk.NODE_IDENT && !in_binder)
    {
        if (n.resolved == null && !ident_resolution_optional(parent, idx))
        {
            bool is_underscore = n.p.ident.name_len == 1 && n.p.ident.name_ptr[0] == '_';
            if (!is_underscore)
            {
                self.unresolved_names++;
                self.report("identifier in value position has no resolution", n.line, n.col);
            }
        }
    }

    // I2 — expression nodes must be typed (except the optional set / binders).
    if (!in_binder && is_expr_kind(n.kind) && n.type_annotation == null && !expr_type_optional(n))
    {
        // Cross-module member access / calls (`m::sq(n)`, `geom::Point` field)
        // are now fully typed by the checker; only a member it genuinely could
        // not resolve (e.g. an unresolved import) stays soft.
        if (!(n.kind == Nk.NODE_IDENT && ident_resolution_optional(parent, idx))
            && !is_unresolved_cross_module(n))
        {
            self.untyped_exprs++;
            self.report("expression node carries no type after type-checking", n.line, n.col);
        }
    }

    // I4 — structural arity for nodes lowering destructures positionally.
    self.check_arity(n);

    // Decide the binder context for each child.
    bool node_is_pattern = is_pattern_kind(n.kind);
    bool node_is_decl = is_decl_kind(n.kind);
    for (usz i = 0; i < n.child_count; i++)
    {
        bool child_binder = in_binder;
        // Inside a pattern, every identifier is a binder — EXCEPT a guard
        // expression (PATTERN_GUARD child), which contains real value uses.
        if (node_is_pattern)
        {
            child_binder = n.kind != Nk.NODE_PATTERN_GUARD;
        }
        // A declaration's NAME child(ren) are binders; its other children
        // (types, bodies, initializers) are normal and re-enter use context.
        if (node_is_decl)
        {
            child_binder = decl_child_is_binder(n.kind, i);
        }
        self.walk(n.children[i], n, i, child_binder);
    }
}

// Which child positions of a declaration node are binder NAMES (vs. types/
// bodies/initializers that contain ordinary uses).
fn bool decl_child_is_binder(Nk k, usz i)
{
    switch (k)
    {
        case Nk.NODE_DECL_FN:
        case Nk.NODE_DECL_TYPE:
        case Nk.NODE_DECL_STRUCT:
        case Nk.NODE_DECL_UNION:
        case Nk.NODE_DECL_EFFECT:
        case Nk.NODE_DECL_MOD:
        case Nk.NODE_PATTERN_DECL:
        case Nk.NODE_REWRITE_RULE:
        case Nk.NODE_PGEN:
        case Nk.NODE_DIALECT:
        case Nk.NODE_OPCODE:
        case Nk.NODE_REGION:
        case Nk.NODE_BLOCK_IR:
        case Nk.NODE_NODE_DECL:
        case Nk.NODE_GRAPH:
        case Nk.NODE_ENUM_VARIANT:    // child 0 = variant name (binder); rest = payload types
        case Nk.NODE_DECL_ENUM:       // child 0 = enum type name (binder)
        case Nk.NODE_DECL_NEWTYPE:    // child 0 = newtype name (binder)
            return i == 0;             // child 0 is the declared name
        case Nk.NODE_EDGE_DECL:
        case Nk.NODE_HYPEREDGE_DECL:
            return false;              // all endpoints are references (uses)
        case Nk.NODE_PARAM:
        case Nk.NODE_GENERIC_PARAM:
        case Nk.NODE_FIELD_DECL:
            return i == 0;             // name; the type child is a use position
        case Nk.NODE_DECL_LET:
        case Nk.NODE_DECL_MUT:
        case Nk.NODE_DECL_CONST:
        case Nk.NODE_DECL_STATIC:
            return i == 0;             // the bound pattern (handled as pattern too)
        case Nk.NODE_LOWER:
        case Nk.NODE_EFFECT_WITH:
            return false;              // handled by their own resolvers; treat as uses
        default:
            return false;
    }
}

fn void Verifier.check_arity(Verifier* self, Node* n)
{
    switch (n.kind)
    {
        case Nk.NODE_EXPR_BINARY:
            if (n.child_count < 2)
            {
                self.arity_breaks++;
                self.report("binary expression with fewer than 2 operands", n.line, n.col);
            }
        case Nk.NODE_EXPR_UNARY:
            if (n.child_count < 1)
            {
                self.arity_breaks++;
                self.report("unary expression with no operand", n.line, n.col);
            }
        case Nk.NODE_EXPR_FIELD:
            if (n.child_count < 2)
            {
                self.arity_breaks++;
                self.report("field access without base and field name", n.line, n.col);
            }
        case Nk.NODE_EXPR_CALL:
            if (n.child_count < 1)
            {
                self.arity_breaks++;
                self.report("call expression with no callee", n.line, n.col);
            }
        case Nk.NODE_EXPR_INDEX:
            if (n.child_count < 2)
            {
                self.arity_breaks++;
                self.report("index expression without base and index", n.line, n.col);
            }
        default:
            break;
    }
}

// The set of expression kinds this verifier expects to be typed. Kept local so
// it is independent of the type checker's internal helper.
fn bool is_expr_kind(Nk k)
{
    switch (k)
    {
        case Nk.NODE_LIT_INT:
        case Nk.NODE_LIT_FLOAT:
        case Nk.NODE_LIT_BOOL:
        case Nk.NODE_LIT_CHAR:
        case Nk.NODE_LIT_STRING:
        case Nk.NODE_EXPR_BINARY:
        case Nk.NODE_EXPR_UNARY:
        case Nk.NODE_EXPR_CALL:
        case Nk.NODE_EXPR_FIELD:
        case Nk.NODE_EXPR_INDEX:
        case Nk.NODE_EXPR_STRUCT_LIT:
            return true;
        default:
            return false;
    }
}

// Public entry: audit a whole program. Returns total findings.
fn int Verifier.verify(Verifier* self, Node* program)
{
    if (program == null) return 0;
    self.walk(program, null, 0, false);
    return self.total();
}


// ── Spec-lock doctests (r14) ──────────────────────────────────────────────
// Canonical, minimal Pride snippets — the exact surface syntax v.md teaches
// — run through the REAL frontend pipeline in-process (`pride --self-test`),
// each with a declared expectation. Documentation syntax stops rotting in
// silence: a regression in any documented form becomes a named failure with
// the stage, the snippet, and what was expected vs what was found — never a
// quiet "EXPECTED diagnostic" folded into somebody else's conformance tally.
//
// Every snippet runs the same stages as a real compile of the same text:
//   lex → parse → resolve → typecheck → effectcheck → lint
//
// Expectation language:
//   "clean"         — zero diagnostics at every stage (mirrors conformance
//                     EXPECT-CLEAN exactly)
//   "parse:<sub>"   — at least one PARSE error whose text contains <sub>
//   "resolve:<sub>" — at least one RESOLVER error containing <sub>
//   "type:<sub>"    — at least one TYPE diagnostic containing <sub>
//   "effect:<sub>"  — at least one EFFECT diagnostic containing <sub>
// (Negative tests assert the DIAGNOSTIC exists; other diagnostics around it
// are tolerated — a good error message staying loud is what matters.)

struct DocTest
{
    char* group;     // the doc section the syntax comes from
    char* name;      // short slug printed in reports
    char* expect;    // expectation per the language above
    char* src;       // the canonical snippet, verbatim as a user writes it
}

const DocTest[15] R14_DOCTESTS =
{
    // §6 — functions are clause-based; both layouts.
    { "6 functions", "clause-multiline", "clean",
      "fn add : (i64, i64) -> i64\n  | (a, b) -> a + b\n\n"
      "fn main : () -> i64\n  | () -> add(40, 2)\n" },
    { "6 functions", "clause-oneline", "clean",
      "fn inc : i64 -> i64 | x -> x + 1\n\n"
      "fn main : () -> i64\n  | () -> inc(40)\n" },

    // §9 — unions, both representations (r13 shape rule).
    { "9 unions", "c-union-fields", "clean",
      "union FloatBits\n  f : f32\n  i : u32\n\n"
      "fn get_i : FloatBits -> u32\n  | fb -> fb.i\n\n"
      "fn get_f : FloatBits -> f32\n  | fb -> fb.f\n" },
    { "9 unions", "tagged-union-match", "clean",
      "type Opt = union\n  some : i32\n  none : ()\n"
      "fn unwrap : Opt -> i32\n  | { some: v } -> v\n  | { none: n } -> n\n" },

    // §776 — transmute takes its target from the ascription / codomain.
    { "transmute", "transmute-fn-codomain", "clean",
      "fn float_bits : f32 -> u32\n  | x -> transmute(x)\n\n"
      "fn bits_float : u32 -> f32\n  | b -> transmute(b)\n" },
    { "transmute", "transmute-let-ascription", "clean",
      "fn main : () -> i64\n  | () ->\n"
      "      let bits : u32 = transmute(3.14f32)\n      bits as i64\n" },

    // §16 — term rewriting: first-class rules, |> application.
    { "16 rewriting", "rewrite-metavars", "clean",
      "let arith = rewrite\n  | x + 0 \xe2\x86\xa6 x\n  | x * 1 \xe2\x86\xa6 x\n"
      "fn apply_it : i64 -> i64\n  | n -> n |> arith\n" },

    // §17 — pattern generation language.
    { "17 pgl", "pgen-metavars", "clean",
      "pgen elim_add_zero<T> ->\n  [x : T]\n  where [x + 0]\n  \xe2\x86\xa6 x\n" },

    // §18 — code quotation sigils.
    { "18 quotation", "sigil-tree", "clean",
      "fn main : () -> i64\n  | () ->\n"
      "      let _node = ~Tree (1 + 2 * 3)\n      0\n" },

    // §19 — IRDL dialects: declare, lower, use.
    { "19 irdl", "dialect-lowering", "clean",
      "fn add : (i32, i32) -> i32\n  | (a, b) -> a + b\n"
      "dialect Gpu\n  opcode gadd\n"
      "irdl\n  Gpu.gadd [x : i32, y : i32] \xe2\x86\xa6 add(x, y)\n"
      "fn use_dialect : (i32, i32) -> i32\n  | (p, q) -> Gpu.gadd(p, q)\n" },

    // r13 negative — a C-union has no discriminant; matching one is a hard
    // type error, loudly, at the first arm.
    { "9 unions", "match-c-union-is-error", "type:discriminant",
      "union FloatBits\n  f : f32\n  i : u32\n\n"
      "fn main : () -> i64\n  | () ->\n"
      "      let fb = FloatBits.i(1u32)\n"
      "      match fb\n"
      "        | { i: v } -> v\n"
      "        | { f: w } -> 0\n" },

    // r13 negative — an aggregate payload cannot fit the 64-bit cell.
    { "9 unions", "aggregate-payload-ctor-is-error", "type:64-bit cell",
      "struct Pair\n  a : i32\n  b : i32\n\n"
      "union PairOrInt\n  i : i32\n  p : Pair\n\n"
      "fn main : () -> i64\n  | () ->\n"
      "      let _x = PairOrInt.p(Pair { a: 1, b: 2 })\n      0\n" },

    // §5 — bindings: shadowing rebinding (newest wins, like Rust), and
    // module-scope literal lets (read back like const).
    { "5 bindings", "shadow-rebind", "clean",
      "fn main : () -> i64\n  | () ->\n"
      "      let x : i64 = 10\n      let y : i64 = x\n"
      "      let x : i64 = 32\n      x + y\n" },
    { "5 bindings", "module-let-literal", "clean",
      "let answer : i64 = 42\n\n"
      "fn main : () -> i64\n  | () -> answer\n" },

    // Front-end honesty — unknown names are loud (E0270-class), never
    // silently zero-fabricated.
    { "diagnostics", "undefined-name-is-loud", "resolve:undefined",
      "fn main : () -> i64\n  | () -> missing_fn(1)\n" },
};

const usz R14_DOCTEST_COUNT = 15;

// ── runner helpers ────────────────────────────────────────────────────────

fn bool dt_contains(char* hay, char* needle)
{
    if (hay == null || needle == null) return false;
    usz hl = strlen(hay);
    usz nl = strlen(needle);
    if (nl == 0 || nl > hl) return false;
    for (usz i = 0; i + nl <= hl; i++)
    {
        bool eq = true;
        for (usz k = 0; k < nl; k++)
        {
            if (hay[i + k] != needle[k]) { eq = false; break; }
        }
        if (eq) return true;
    }
    return false;
}

fn bool dt_prefix_eq(char* s, char* prefix)
{
    if (s == null || prefix == null) return false;
    usz pl = strlen(prefix);
    for (usz i = 0; i < pl; i++)
    {
        if (s[i] != prefix[i]) return false;
    }
    return true;
}

// Print one diagnostic line (compact form; the same facts the normal
// reporters show, just denser so --self-test stays scannable).
fn void dt_print_diag(char* stage, char* msg, int line, int col)
{
    printf("      [%s %d:%d] %s\n", stage, line, col, msg);
}

// ── the runner ────────────────────────────────────────────────────────────
// Runs every registered snippet through the frontend and checks its
// expectation. Returns the number of FAILED doctests (0 = all locked).
fn int run_doctests()
{
    int dt_pass = 0;
    int dt_fail = 0;
    printf("=== spec-lock doctests (r14) ===\n");

    for (usz ti = 0; ti < R14_DOCTEST_COUNT; ti++)
    {
        DocTest* dt = &R14_DOCTESTS[ti];
        usz src_len = strlen(dt.src);

        lexer::Lexer lx;
        lx.init(dt.src, src_len);

        ast::AstArena arena;
        if (!arena.init(ast::DEFAULT_ARENA_BYTES))
        {
            printf("  FAIL %s/%s: arena allocation failed\n", dt.group, dt.name);
            dt_fail++;
            continue;
        }

        parser::Parser p;
        p.init(&lx, &arena);
        Node* program = p.parse_program();

        resolve::Resolver* r = (resolve::Resolver*)malloc(resolve::Resolver::size);
        if (r != null)
        {
            r.init();
            if (program != null) r.resolve_program(program);
        }

        typecheck::TypeChecker tc;
        tc.init(&arena, false);
        if (program != null) tc.check_program(program);

        effectcheck::EffectChecker ec;
        ec.init(false);
        if (program != null) ec.check_program(program);

        lint::Linter* lt = (lint::Linter*)malloc(lint::Linter::size);
        if (lt != null)
        {
            lt.init(false);
            if (program != null) lt.run(program);
        }

        int lex_count  = lx.get_diag_count();
        int parse_cnt  = p.error_count;
        int res_cnt    = (r != null) ? r.error_count : 0;
        int type_cnt   = tc.diag_count;
        int eff_cnt    = ec.diag_count;
        int lint_cnt   = (lt != null) ? lt.diag_count : 0;
        int total      = lex_count + parse_cnt + res_cnt + type_cnt + eff_cnt + lint_cnt;

        bool ok = false;
        bool want_clean = dt_prefix_eq(dt.expect, "clean");
        if (want_clean)
        {
            ok = (total == 0);
        }
        else
        {
            // "<stage>:<substring>" — find the stage tag, assert the text.
            char* sub = null;
            int stage_id = 0;   // 1 parse, 2 resolve, 3 type, 4 effect, 5 lint
            if (dt_prefix_eq(dt.expect, "parse:"))   { stage_id = 1; sub = dt.expect + 6; }
            if (dt_prefix_eq(dt.expect, "resolve:")) { stage_id = 2; sub = dt.expect + 8; }
            if (dt_prefix_eq(dt.expect, "type:"))    { stage_id = 3; sub = dt.expect + 5; }
            if (dt_prefix_eq(dt.expect, "effect:"))  { stage_id = 4; sub = dt.expect + 7; }
            if (dt_prefix_eq(dt.expect, "lint:"))    { stage_id = 5; sub = dt.expect + 5; }
            switch (stage_id)
            {
                case 1:
                    for (int i = 0; i < parse_cnt && !ok; i++)
                    { if (dt_contains(p.errors[i].msg, sub)) ok = true; }
                case 2:
                    if (r != null) for (int i = 0; i < res_cnt && !ok; i++)
                    { if (dt_contains(r.errors[i].msg, sub)) ok = true; }
                case 3:
                    for (int i = 0; i < type_cnt && !ok; i++)
                    { if (dt_contains(tc.diags[i].msg, sub)) ok = true; }
                case 4:
                    for (int i = 0; i < eff_cnt && !ok; i++)
                    { if (dt_contains(ec.diags[i].msg, sub)) ok = true; }
                case 5:
                    if (lt != null) for (int i = 0; i < lint_cnt && !ok; i++)
                    { if (dt_contains(lt.diags[i].msg, sub)) ok = true; }
                default:
                    break;
            }
        }

        if (ok)
        {
            dt_pass++;
        }
        else
        {
            dt_fail++;
            printf("  FAIL %s/%s — expected [%s], found %d diagnostic(s)\n",
                   dt.group, dt.name, dt.expect, total);
            for (int i = 0; i < lex_count && i < 4; i++)
            {
                lexer::Diagnostic d = lx.get_diag(i);
                dt_print_diag("lex", d.msg, d.line, d.col);
            }
            for (int i = 0; i < parse_cnt && i < 4; i++)
            { dt_print_diag("parse", p.errors[i].msg, p.errors[i].line, p.errors[i].col); }
            if (r != null) for (int i = 0; i < res_cnt && i < 4; i++)
            { dt_print_diag("resolve", r.errors[i].msg, r.errors[i].line, r.errors[i].col); }
            for (int i = 0; i < type_cnt && i < 4; i++)
            { dt_print_diag(tc.diags[i].is_error ? "type-err" : "type-warn",
                            tc.diags[i].msg, tc.diags[i].line, tc.diags[i].col); }
            for (int i = 0; i < eff_cnt && i < 4; i++)
            { dt_print_diag(ec.diags[i].is_error ? "effect-err" : "effect-warn",
                            ec.diags[i].msg, ec.diags[i].line, ec.diags[i].col); }
            if (lt != null) for (int i = 0; i < lint_cnt && i < 4; i++)
            { dt_print_diag(lt.diags[i].is_error ? "lint-err" : "lint-warn",
                            lt.diags[i].msg, lt.diags[i].line, lt.diags[i].col); }
        }

        if (lt != null) free((void*)lt);
        if (r != null) free((void*)r);
        arena.destroy();
    }

    printf("spec-lock: pass=%d fail=%d\n", dt_pass, dt_fail);
    return dt_fail;
}
