// ============================================================================
// irdl_msp.c3 — IRDL: dialect registration, validation & lowering
// ----------------------------------------------------------------------------
// Implementation language: C3 (host). MSP Step 5.
//
// IRDL (IR Definition Language, MLIR's idea) lets a program DECLARE its own
// intermediate-representation opcodes ("dialects") and the rules that LOWER
// those opcodes to other ops (ultimately target instructions). In Pride:
//
//   dialect GpuD                         -- registers opcodes/regions
//     opcode gadd
//     opcode gmul
//     region body
//
//   irdl                                 -- registers LOWERING rules
//     GpuD.gadd [a, b] ↦ a + b           -- gadd lowers to an integer add
//     GpuD.gmul [a, b] ↦ a * b
//
//   fn f : (i32,i32) -> i32              -- a USE of a dialect opcode
//     | (x, y) -> GpuD.gadd(x, y)        -- becomes  x + y  after lowering
//
// This module:
//   1. REGISTERS every `dialect` block's opcodes/regions into a DialectTable.
//   2. REGISTERS every `irdl` block's lowering rule (head path, binding list,
//      action template), validating it names a real opcode and binds a sane
//      arity.
//   3. VALIDATES every dialect-op USE in the program against the registry
//      (unknown dialect / unknown opcode / arity mismatch ⇒ MSP diagnostic).
//   4. LOWERS every dialect-op use by substituting the call's arguments into
//      the matching rule's action template — a structural rewrite, the same
//      shape the term-rewriting engine uses (§3), specialised to opcode heads.
//
// Lowering is a fixpoint to a bounded depth: a lowered action may itself contain
// dialect-op uses (one dialect lowering to ops of a lower dialect), so we re-run
// until no dialect ops remain or the fuel runs out.
// ============================================================================

module irdl_msp;

import lexer;
import ast;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

alias Node = ast::AstNode;
alias Nk = ast::NodeKind;
alias Tt = lexer::TokenType;

const usz MAX_DIALECTS  = 256;
const usz MAX_OPCODES   = 4096;   // total across all dialects
const usz MAX_ARG_KINDS = 16;     // declared parameter kinds per opcode
const usz MAX_REGIONS   = 1024;
const usz MAX_LOWERINGS = 4096;
const usz MAX_DIAGS     = 512;
const int LOWER_FUEL    = 100000; // max op-instance lowerings per run
const int LOWER_MAX_DEPTH = 600;  // dialect-chain depth guard

// ── Registered entities ──────────────────────────────────────────────────────
// One lowering rule for an opcode. An opcode may have SEVERAL rules; at lowering
// time the first rule whose binding patterns (literal positions) and guard all
// match the actual use is applied. This is what makes IRDL a real, flexible
// term-rewriting target rather than a one-shot macro: rules can constant-fold,
// special-case, and pattern-dispatch.
const usz MAX_RULES_PER_OP = 8;
struct LowerRule
{
    int    arity;         // binding count from the rule's [..] group
    Node*  bindings;      // the bracket-group NODE_EXPR_ARRAY_LIT (or null)
    Node*  guard;         // optional guard expression (or null)
    Node*  action;        // the RHS action template
    bool   variadic;      // arity is a lower bound (untyped/flexible opcode)
}

struct Opcode
{
    Node*  dialect;       // owning NODE_DIALECT
    char*  dname;         // dialect name
    usz    dname_len;
    char*  name;          // opcode name
    usz    name_len;
    Node*  decl;          // the NODE_OPCODE declaration

    // SIGNATURE (from `opcode name : (T0, T1) -> R`), or absent.
    bool   has_sig;
    Node*  sig;           // the NODE_TYPE_FN signature node (or null)
    int    sig_arity;     // declared parameter count (-1 if no signature)
    Node*[MAX_ARG_KINDS] arg_kinds;   // declared parameter type nodes
    usz    arg_kind_count;
    Node*  result_kind;   // declared result type node (or null)

    // lowering rules (filled when `irdl` rules name this opcode):
    bool   has_rule;
    LowerRule[MAX_RULES_PER_OP] rules;
    usz    rule_count;
}

struct Region
{
    char*  dname;
    usz    dname_len;
    char*  name;
    usz    name_len;
    Node*  decl;
}

struct IrdlDiag { char* msg; int line; int col; bool is_error; }

struct DialectTable
{
    Node*[MAX_DIALECTS] dialects;
    usz    dialect_count;

    Opcode[MAX_OPCODES] opcodes;
    usz    opcode_count;

    Region[MAX_REGIONS] regions;
    usz    region_count;

    IrdlDiag[MAX_DIAGS] diags;
    int    diag_count;

    ast::AstArena* arena;

    // standalone graph-IR (top-level `graph`/`node`/`edge`/`hyperedge`)
    usz    graph_count;
    usz    graph_node_count;
    usz    graph_edge_count;

    // stats
    int    lowerings_applied;
    bool   out_of_fuel;
    bool   too_deep;
    int    fuel;
    int    walk_depth;     // current tree-walk recursion depth (guard)
    bool   overflow;
}

const int WALK_MAX_DEPTH = 1200;   // tree-walk recursion guard

// ── Setup ────────────────────────────────────────────────────────────────────
fn void DialectTable.init(DialectTable* t, ast::AstArena* arena)
{
    t.dialect_count = 0;
    t.opcode_count = 0;
    t.region_count = 0;
    t.diag_count = 0;
    t.arena = arena;
    t.graph_count = 0;
    t.graph_node_count = 0;
    t.graph_edge_count = 0;
    t.lowerings_applied = 0;
    t.out_of_fuel = false;
    t.too_deep = false;
    t.fuel = LOWER_FUEL;
    t.walk_depth = 0;
    t.overflow = false;
}

fn void DialectTable.diag(DialectTable* t, char* msg, int line, int col, bool is_error)
{
    if ((usz)t.diag_count >= MAX_DIAGS) return;
    IrdlDiag* d = &t.diags[t.diag_count];
    t.diag_count++;
    d.msg = msg;
    d.line = line;
    d.col = col;
    d.is_error = is_error;
}

// ── Small name helpers ───────────────────────────────────────────────────────
fn bool name_eq(char* a, usz alen, char* b, usz blen)
{
    if (alen != blen) return false;
    for (usz i = 0; i < alen; i++) { if (a[i] != b[i]) return false; }
    return true;
}

// The text of an Ident/TypeVar node, or (null,0).
fn void node_name(Node* n, char** ptr, usz* len)
{
    *ptr = null;
    *len = 0;
    if (n == null) return;
    if (n.kind == Nk.NODE_IDENT || n.kind == Nk.NODE_TYPEVAR)
    {
        *ptr = n.p.ident.name_ptr;
        *len = n.p.ident.name_len;
    }
}

// ============================================================================
// Phase 1 — registration
// ============================================================================
fn void DialectTable.register(DialectTable* t, Node* program)
{
    if (program == null) return;
    t.scan_dialects(program);
    t.scan_lowerings(program);
    t.scan_graphs(program);
}

// Count standalone (top-level or nested) graph-IR declarations so the IRDL
// report reflects graph descriptions a program builds, not just dialect ops.
fn void DialectTable.scan_graphs(DialectTable* t, Node* n)
{
    if (n == null) return;
    if (t.walk_depth > WALK_MAX_DEPTH) { t.too_deep = true; return; }
    if (n.kind == Nk.NODE_DIALECT || n.kind == Nk.NODE_IRDL) return;  // dialect-internal handled elsewhere
    switch (n.kind)
    {
        case Nk.NODE_GRAPH:        t.graph_count++;
        case Nk.NODE_NODE_DECL:    t.graph_node_count++;
        case Nk.NODE_EDGE_DECL:    t.graph_edge_count++;
        case Nk.NODE_HYPEREDGE_DECL:t.graph_edge_count++;
        default: break;
    }
    t.walk_depth++;
    for (usz i = 0; i < n.child_count; i++) t.scan_graphs(n.children[i]);
    t.walk_depth--;
}

fn void DialectTable.scan_dialects(DialectTable* t, Node* n)
{
    if (n == null) return;
    if (t.walk_depth > WALK_MAX_DEPTH) { t.too_deep = true; return; }
    if (n.kind == Nk.NODE_DIALECT)
    {
        t.register_dialect(n);
        return;   // dialect members handled inside; don't double-scan
    }
    t.walk_depth++;
    for (usz i = 0; i < n.child_count; i++) t.scan_dialects(n.children[i]);
    t.walk_depth--;
}

fn void DialectTable.register_dialect(DialectTable* t, Node* d)
{
    // first child = dialect name (TypeVar/Ident); then a body block of members.
    char* dname; usz dname_len;
    node_name(d.child_count >= 1 ? d.children[0] : null, &dname, &dname_len);

    if (t.dialect_count < MAX_DIALECTS) { t.dialects[t.dialect_count] = d; t.dialect_count++; }
    else { t.overflow = true; }

    // body block (members; regions/blocks may nest further members)
    for (usz i = 0; i < d.child_count; i++)
    {
        Node* c = d.children[i];
        if (c == null || c.kind != Nk.NODE_EXPR_BLOCK) continue;
        t.register_members(d, dname, dname_len, c, 0);
    }
}

// Register the members of a member-block, recursing into region/block bodies so
// nested opcodes are registered too. `depth` bounds the nesting.
fn void DialectTable.register_members(DialectTable* t, Node* dialect, char* dname, usz dname_len, Node* block, int depth)
{
    if (block == null || depth > LOWER_MAX_DEPTH) return;
    for (usz j = 0; j < block.child_count; j++)
    {
        Node* m = block.children[j];
        if (m == null) continue;
        switch (m.kind)
        {
            case Nk.NODE_OPCODE:
                t.add_opcode(dialect, dname, dname_len, m);
            case Nk.NODE_REGION:
            case Nk.NODE_BLOCK_IR:
            case Nk.NODE_GRAPH:
                t.add_region(dname, dname_len, m);
                // recurse into the region/block/graph body for nested members
                for (usz k = 0; k < m.child_count; k++)
                {
                    Node* b = m.children[k];
                    if (b != null && b.kind == Nk.NODE_EXPR_BLOCK)
                    {
                        t.register_members(dialect, dname, dname_len, b, depth + 1);
                    }
                }
            default:
                break;
        }
    }
}

fn void DialectTable.add_opcode(DialectTable* t, Node* dialect, char* dname, usz dname_len, Node* m)
{
    char* oname; usz oname_len;
    node_name(m.child_count >= 1 ? m.children[0] : null, &oname, &oname_len);
    if (oname == null) return;

    // duplicate opcode within the same dialect?
    for (usz i = 0; i < t.opcode_count; i++)
    {
        Opcode* o = &t.opcodes[i];
        if (name_eq(o.dname, o.dname_len, dname, dname_len) && name_eq(o.name, o.name_len, oname, oname_len))
        {
            t.diag("duplicate opcode in dialect", m.line, m.col, false);
            return;
        }
    }

    if (t.opcode_count >= MAX_OPCODES) { t.overflow = true; return; }
    Opcode* o = &t.opcodes[t.opcode_count];
    t.opcode_count++;
    o.dialect = dialect;
    o.dname = dname;
    o.dname_len = dname_len;
    o.name = oname;
    o.name_len = oname_len;
    o.decl = m;
    o.has_rule = false;
    o.rule_count = 0;

    // SIGNATURE: `opcode name : (T0,T1) -> R` parses as a NODE_TYPE_FN child
    // [paramType, resultType] where paramType is a tuple (n args) or single type.
    o.has_sig = false;
    o.sig = null;
    o.sig_arity = -1;
    o.arg_kind_count = 0;
    o.result_kind = null;
    for (usz i = 1; i < m.child_count; i++)
    {
        Node* c = m.children[i];
        if (c != null && c.kind == Nk.NODE_TYPE_FN && c.child_count >= 2)
        {
            o.has_sig = true;
            o.sig = c;
            Node* params = c.children[0];
            o.result_kind = c.children[1];
            if (params != null && params.kind == Nk.NODE_TYPE_TUPLE)
            {
                for (usz j = 0; j < params.child_count && o.arg_kind_count < MAX_ARG_KINDS; j++)
                {
                    o.arg_kinds[o.arg_kind_count] = params.children[j];
                    o.arg_kind_count++;
                }
            }
            else if (params != null)
            {
                // single (non-tuple) parameter type
                o.arg_kinds[0] = params;
                o.arg_kind_count = 1;
            }
            o.sig_arity = (int)o.arg_kind_count;
            break;
        }
    }
}

fn void DialectTable.add_region(DialectTable* t, char* dname, usz dname_len, Node* m)
{
    char* rname; usz rname_len;
    node_name(m.child_count >= 1 ? m.children[0] : null, &rname, &rname_len);
    if (rname == null) return;
    if (t.region_count >= MAX_REGIONS) { t.overflow = true; return; }
    Region* r = &t.regions[t.region_count];
    t.region_count++;
    r.dname = dname;
    r.dname_len = dname_len;
    r.name = rname;
    r.name_len = rname_len;
    r.decl = m;
}

// Find an opcode by dialect+name.
fn Opcode* DialectTable.find_opcode(DialectTable* t, char* dname, usz dlen, char* oname, usz olen)
{
    for (usz i = 0; i < t.opcode_count; i++)
    {
        Opcode* o = &t.opcodes[i];
        if (name_eq(o.dname, o.dname_len, dname, dlen) && name_eq(o.name, o.name_len, oname, olen))
        {
            return o;
        }
    }
    return null;
}

fn bool DialectTable.dialect_known(DialectTable* t, char* dname, usz dlen)
{
    for (usz i = 0; i < t.dialect_count; i++)
    {
        char* nm; usz nl;
        Node* d = t.dialects[i];
        node_name(d.child_count >= 1 ? d.children[0] : null, &nm, &nl);
        if (name_eq(nm, nl, dname, dlen)) return true;
    }
    return false;
}

// ── A dotted opcode head (Dialect.op) → (dialect-name, opcode-name) ──────────
// The IRDL rule head is NODE_EXPR_FIELD(TypeVar/Ident dialect, Ident op).
struct HeadRef { char* dname; usz dlen; char* oname; usz olen; bool ok; }

fn HeadRef split_head(Node* head)
{
    HeadRef h;
    h.ok = false;
    h.dname = null; h.dlen = 0; h.oname = null; h.olen = 0;
    if (head == null) return h;
    if (head.kind == Nk.NODE_EXPR_FIELD && head.child_count >= 2)
    {
        node_name(head.children[0], &h.dname, &h.dlen);
        node_name(head.children[1], &h.oname, &h.olen);
        h.ok = h.dname != null && h.oname != null;
    }
    return h;
}

// ── Phase 1b — lowering-rule registration ────────────────────────────────────
fn void DialectTable.scan_lowerings(DialectTable* t, Node* n)
{
    if (n == null) return;
    if (t.walk_depth > WALK_MAX_DEPTH) { t.too_deep = true; return; }
    if (n.kind == Nk.NODE_LOWER)
    {
        t.register_lowering(n);
        return;
    }
    t.walk_depth++;
    for (usz i = 0; i < n.child_count; i++) t.scan_lowerings(n.children[i]);
    t.walk_depth--;
}

// NODE_LOWER children: [head-path, binding-group?, guard?, action].
// An opcode may have MULTIPLE rules (pattern/guard-dispatched). We append each
// rule; lowering tries them in source order and applies the first whose literal
// binding patterns and guard match the use.
fn void DialectTable.register_lowering(DialectTable* t, Node* rule)
{
    if (rule.child_count < 2) return;
    Node* head = rule.children[0];
    Node* bindings = null;
    Node* guard = null;
    Node* action = rule.children[rule.child_count - 1];

    // middle children: an array-lit binding group and/or a guard.
    for (usz i = 1; i + 1 < rule.child_count; i++)
    {
        Node* mid = rule.children[i];
        if (mid == null) continue;
        if (mid.kind == Nk.NODE_EXPR_ARRAY_LIT) { bindings = mid; }
        else if (mid.kind == Nk.NODE_PATTERN_GUARD && mid.child_count >= 1) { guard = mid.children[0]; }
    }

    HeadRef h = split_head(head);
    if (!h.ok)
    {
        t.diag("irdl lowering rule head is not a Dialect.opcode path", rule.line, rule.col, false);
        return;
    }
    if (!t.dialect_known(h.dname, h.dlen))
    {
        t.diag("irdl rule references unknown dialect", head.line, head.col, true);
        return;
    }
    Opcode* o = t.find_opcode(h.dname, h.dlen, h.oname, h.olen);
    if (o == null)
    {
        t.diag("irdl rule references unknown opcode", head.line, head.col, true);
        return;
    }
    int arity = bindings != null ? (int)bindings.child_count : 0;

    // A binding list ending in `..rest` (a bare Ident named "rest" prefixed by
    // the range token is hard to encode; instead we treat an opcode WITHOUT a
    // signature and whose last binding is a plain spread-style binder as
    // flexible). For now: untyped/flexible opcodes are those with NO signature —
    // their arity is a lower bound so variadic dialect ops can be lowered.
    bool variadic = !o.has_sig && bindings_has_rest(bindings);

    // If the opcode declared a signature, a NON-variadic rule's binding count
    // must match the signature's parameter count.
    if (o.has_sig && o.sig_arity >= 0 && arity != o.sig_arity && !variadic)
    {
        t.diag("lowering rule arity disagrees with opcode signature", rule.line, rule.col, true);
    }
    if (o.rule_count >= MAX_RULES_PER_OP)
    {
        t.diag("too many lowering rules for one opcode", rule.line, rule.col, true);
        return;
    }
    LowerRule* lr = &o.rules[o.rule_count];
    lr.arity = arity;
    lr.bindings = bindings;
    lr.guard = guard;
    lr.action = action;
    lr.variadic = variadic;
    o.rule_count++;
    o.has_rule = true;
}

// A binding group is "variadic" when its last entry is a rest-binder written
// `..name` (parsed as a NODE_EXPR_RANGE / unary range over an ident). We detect
// the spread form structurally so flexible opcodes can accept any extra args.
fn bool bindings_has_rest(Node* bindings)
{
    if (bindings == null || bindings.child_count == 0) return false;
    Node* last = bindings.children[bindings.child_count - 1];
    if (last == null) return false;
    // `..name` lexes as a range/spread; accept either an EXPR_RANGE leaf or a
    // PARAM/Ident whose name starts with the rest marker handled by the parser.
    if (last.kind == Nk.NODE_EXPR_RANGE) return true;
    return false;
}

// ============================================================================
// Phase 2 — validation of opcode USES across the program
// ============================================================================
// A dialect-op use is a Call/MethodCall whose callee is a Dialect.op path:
//   MethodCall[TypeVar dialect, Ident op, args...]   (GpuD.gadd(x,y))
//   Call[Field(dialect, op), args...]                (alternate shape)
struct OpUse { char* dname; usz dlen; char* oname; usz olen; usz argc; Node** args; bool ok; }

fn OpUse classify_use(Node* n)
{
    OpUse u;
    u.ok = false;
    u.dname = null; u.dlen = 0; u.oname = null; u.olen = 0; u.argc = 0; u.args = null;

    if (n == null) return u;

    if (n.kind == Nk.NODE_EXPR_METHOD_CALL && n.child_count >= 2)
    {
        // [dialect, op, args...]
        node_name(n.children[0], &u.dname, &u.dlen);
        node_name(n.children[1], &u.oname, &u.olen);
        if (u.dname != null && u.oname != null && (n.children[0].kind == Nk.NODE_TYPEVAR))
        {
            u.args = &n.children[2];
            u.argc = n.child_count - 2;
            u.ok = true;
        }
        return u;
    }

    if (n.kind == Nk.NODE_EXPR_CALL && n.child_count >= 1)
    {
        Node* callee = n.children[0];
        if (callee != null && callee.kind == Nk.NODE_EXPR_FIELD && callee.child_count >= 2
            && callee.children[0] != null && callee.children[0].kind == Nk.NODE_TYPEVAR)
        {
            node_name(callee.children[0], &u.dname, &u.dlen);
            node_name(callee.children[1], &u.oname, &u.olen);
            if (u.dname != null && u.oname != null)
            {
                u.args = &n.children[1];
                u.argc = n.child_count - 1;
                u.ok = true;
            }
        }
        return u;
    }

    return u;
}

// The statically-known primitive KIND of a node, as (name, len), or (null,0).
// A type-annotation primitive wins; otherwise integer/bool/float/string literals
// have an obvious kind. Unknown ⇒ (null,0) and the kind check is skipped (soft).
fn void kind_name_of(Node* n, char** ptr, usz* len)
{
    *ptr = null; *len = 0;
    if (n == null) return;
    // an explicit type annotation (set by the type checker) is most reliable
    if (n.type_annotation != null && n.type_annotation.kind == Nk.NODE_TYPE_PRIMITIVE)
    {
        *ptr = n.type_annotation.p.ident.name_ptr;
        *len = n.type_annotation.p.ident.name_len;
        return;
    }
    switch (n.kind)
    {
        case Nk.NODE_TYPE_PRIMITIVE:
            *ptr = n.p.ident.name_ptr; *len = n.p.ident.name_len;
        case Nk.NODE_LIT_BOOL:
            *ptr = "bool"; *len = 4;
        case Nk.NODE_LIT_STRING:
            *ptr = "Str"; *len = 3;
        default:
            break;   // int/float literals: width unknown without context → skip
    }
}

// Check each argument's statically-known kind against the opcode's declared
// parameter kind. Mismatches (both primitive, different names) are diagnosed.
fn void DialectTable.check_arg_kinds(DialectTable* t, Opcode* o, OpUse* u)
{
    usz nchk = u.argc < o.arg_kind_count ? u.argc : o.arg_kind_count;
    for (usz i = 0; i < nchk; i++)
    {
        Node* decl = o.arg_kinds[i];
        Node* arg  = u.args[i];
        char* dn; usz dl;
        char* an; usz al;
        // declared kind must be a primitive to compare by name
        dn = null; dl = 0;
        if (decl != null && decl.kind == Nk.NODE_TYPE_PRIMITIVE) { dn = decl.p.ident.name_ptr; dl = decl.p.ident.name_len; }
        kind_name_of(arg, &an, &al);
        if (dn != null && an != null && !name_eq(dn, dl, an, al))
        {
            t.diag("opcode argument kind does not match its signature", arg.line, arg.col, true);
        }
    }
}

// Walk the program (skipping dialect/irdl decls themselves) validating uses.
fn void DialectTable.validate_uses(DialectTable* t, Node* n)
{
    if (n == null) return;
    if (t.walk_depth > WALK_MAX_DEPTH) { t.too_deep = true; return; }
    if (n.kind == Nk.NODE_DIALECT || n.kind == Nk.NODE_IRDL) return;

    OpUse u = classify_use(n);
    if (u.ok && t.dialect_known(u.dname, u.dlen))
    {
        Opcode* o = t.find_opcode(u.dname, u.dlen, u.oname, u.olen);
        if (o == null)
        {
            t.diag("use of unknown opcode in registered dialect", n.line, n.col, true);
        }
        else
        {
            // Arity check: prefer the declared SIGNATURE arity. Otherwise the
            // use is valid if SOME rule can accept it (exact arity, or a
            // variadic rule whose fixed-prefix count it meets). With no rules
            // and no signature, arity is unconstrained (flexible/untyped op).
            if (o.has_sig && o.sig_arity >= 0)
            {
                if ((int)u.argc != o.sig_arity)
                {
                    t.diag("opcode use arity does not match its signature", n.line, n.col, true);
                }
            }
            else if (o.has_rule && !o.opcode_accepts_arity((int)u.argc))
            {
                t.diag("opcode use arity matches no lowering rule", n.line, n.col, true);
            }
            // Kind check: where an argument has a statically-known kind and the
            // opcode declared its parameter kinds, the two must agree.
            if (o.has_sig)
            {
                t.check_arg_kinds(o, &u);
            }
            if (!o.has_rule)
            {
                t.diag("opcode has no lowering rule (cannot be lowered)", n.line, n.col, false);
            }
        }
    }

    t.walk_depth++;
    for (usz i = 0; i < n.child_count; i++) t.validate_uses(n.children[i]);
    t.walk_depth--;
}

// ============================================================================
// Phase 3 — lowering (substitute args into the rule action)
// ============================================================================
// Extract the i-th binding NAME from a bracket-group child. A binding is either
// a bare Ident or a NODE_PARAM[Ident, Type].
fn void binding_name(Node* bindings, usz i, char** ptr, usz* len)
{
    *ptr = null; *len = 0;
    if (bindings == null || i >= bindings.child_count) return;
    Node* b = bindings.children[i];
    if (b == null) return;
    if (b.kind == Nk.NODE_PARAM && b.child_count >= 1) { node_name(b.children[0], ptr, len); return; }
    node_name(b, ptr, len);
}

// Substitute: clone `tmpl`, replacing any Ident whose name matches a binding
// with the corresponding argument node. (Bound args are real subterms, reused.)
fn Node* DialectTable.substitute(DialectTable* t, Node* tmpl, Node* bindings, Node** args, usz argc)
{
    if (tmpl == null) return null;
    if (t.walk_depth > WALK_MAX_DEPTH) { t.too_deep = true; return tmpl; }

    // an Ident matching a binding → that argument
    if (tmpl.kind == Nk.NODE_IDENT)
    {
        usz n = bindings != null ? bindings.child_count : 0;
        for (usz i = 0; i < n && i < argc; i++)
        {
            char* bp; usz bl;
            binding_name(bindings, i, &bp, &bl);
            if (bp != null && name_eq(bp, bl, tmpl.p.ident.name_ptr, tmpl.p.ident.name_len))
            {
                return args[i];
            }
        }
        return tmpl;   // free identifier in the action: keep as-is
    }

    if (tmpl.child_count == 0) return tmpl;   // leaf: reuse

    // rebuild children
    Node*[32] buf;
    usz cc = tmpl.child_count <= 32 ? tmpl.child_count : 32;
    t.walk_depth++;
    for (usz i = 0; i < cc; i++)
    {
        buf[i] = t.substitute(tmpl.children[i], bindings, args, argc);
    }
    t.walk_depth--;
    Node* fresh;
    if (tmpl.kind == Nk.NODE_EXPR_BINARY || tmpl.kind == Nk.NODE_EXPR_UNARY)
    {
        fresh = ast::node_op(t.arena, tmpl.kind, tmpl.p.op.op, &buf[0], cc, tmpl.line, tmpl.col);
    }
    else
    {
        fresh = ast::node_n(t.arena, tmpl.kind, &buf[0], cc, tmpl.line, tmpl.col);
        if (fresh != null) fresh.p = tmpl.p;
    }
    return fresh;
}

// Does any registered rule for this opcode accept `argc` arguments?
fn bool Opcode.opcode_accepts_arity(Opcode* o, int argc)
{
    for (usz i = 0; i < o.rule_count; i++)
    {
        LowerRule* r = &o.rules[i];
        if (r.variadic) { if (argc >= r.arity - 1) return true; }
        else { if (argc == r.arity) return true; }
    }
    return false;
}

// Does a literal binding pattern in the rule match the corresponding argument?
// A binding position holds either a binder (Ident / Param[Ident,Type]) which
// matches anything, or a LITERAL (e.g. `[a, 0]`) which matches only an argument
// that is the same literal. This is what lets a rule constant-fold.
fn bool binding_matches(Node* bindings, usz i, Node* arg)
{
    if (bindings == null || i >= bindings.child_count) return true;
    Node* b = bindings.children[i];
    if (b == null) return true;
    // binders match anything
    if (b.kind == Nk.NODE_IDENT) return true;
    if (b.kind == Nk.NODE_PARAM) return true;
    if (b.kind == Nk.NODE_EXPR_RANGE) return true;   // rest-binder
    // a literal binding matches only an equal literal argument
    if (b.kind == Nk.NODE_LIT_INT)
    {
        Node* a = arg;
        if (a != null && a.kind == Nk.NODE_LIT_INT)
        {
            return a.p.lit_int.int_val == b.p.lit_int.int_val;
        }
        return false;   // not a literal arg → this specialised rule doesn't apply
    }
    if (b.kind == Nk.NODE_LIT_BOOL)
    {
        return arg != null && arg.kind == Nk.NODE_LIT_BOOL
            && arg.p.lit_bool.bool_val == b.p.lit_bool.bool_val;
    }
    return true;   // other binding shapes: treat as binder
}

// Select the first rule whose arity, literal patterns, and guard all match.
fn LowerRule* DialectTable.select_rule(DialectTable* t, Opcode* o, OpUse* u)
{
    for (usz ri = 0; ri < o.rule_count; ri++)
    {
        LowerRule* r = &o.rules[ri];
        // arity
        if (r.variadic) { if ((int)u.argc < r.arity - 1) continue; }
        else { if ((int)u.argc != r.arity) continue; }
        // literal binding patterns
        bool ok = true;
        usz nchk = u.argc < (usz)r.arity ? u.argc : (usz)r.arity;
        for (usz i = 0; i < nchk; i++)
        {
            if (!binding_matches(r.bindings, i, u.args[i])) { ok = false; break; }
        }
        if (!ok) continue;
        // guard: a constant-foldable guard must evaluate true; an
        // unevaluable guard conservatively does NOT match (skip to next rule).
        if (r.guard != null)
        {
            int g = t.eval_guard(r.guard, r.bindings, u.args, u.argc);
            if (g != 1) continue;
        }
        return r;
    }
    return null;
}

// Evaluate a rule guard after substituting the use's args. Returns 1 (true),
// 0 (false), or -1 (unknown / not constant-foldable). Supports the common
// comparison/arithmetic guards on integer literals — enough for folding rules
// like `[a, b], b == 0 ↦ a`.
fn int DialectTable.eval_guard(DialectTable* t, Node* guard, Node* bindings, Node** args, usz argc)
{
    Node* g = t.substitute(guard, bindings, args, argc);
    return const_truth(g);
}

// Constant-evaluate a (substituted) boolean expression over integer literals.
fn int const_truth(Node* e)
{
    if (e == null) return -1;
    if (e.kind == Nk.NODE_LIT_BOOL) return e.p.lit_bool.bool_val ? 1 : 0;
    if (e.kind == Nk.NODE_EXPR_BINARY && e.child_count >= 2)
    {
        long l; long r;
        if (!const_int(e.children[0], &l)) return -1;
        if (!const_int(e.children[1], &r)) return -1;
        switch (e.p.op.op)
        {
            case Tt.TOKEN_EQEQ:   return l == r ? 1 : 0;
            case Tt.TOKEN_NEQ:    return l != r ? 1 : 0;
            case Tt.TOKEN_NEQ_UNI:return l != r ? 1 : 0;
            case Tt.TOKEN_LT:     return l <  r ? 1 : 0;
            case Tt.TOKEN_GT:     return l >  r ? 1 : 0;
            case Tt.TOKEN_LTEQ:   return l <= r ? 1 : 0;
            case Tt.TOKEN_GTEQ:   return l >= r ? 1 : 0;
            case Tt.TOKEN_LEQ_UNI:return l <= r ? 1 : 0;
            case Tt.TOKEN_GEQ_UNI:return l >= r ? 1 : 0;
            default: return -1;
        }
    }
    return -1;
}

// Read a node as a constant integer (literal, or a tiny folded arithmetic).
fn bool const_int(Node* e, long* out)
{
    if (e == null) return false;
    if (e.kind == Nk.NODE_LIT_INT) { *out = (long)e.p.lit_int.int_val; return true; }
    if (e.kind == Nk.NODE_EXPR_UNARY && e.child_count >= 1)
    {
        long v;
        if (!const_int(e.children[0], &v)) return false;
        switch (e.p.op.op)
        {
            case Tt.TOKEN_MINUS: *out = -v; return true;
            case Tt.TOKEN_PLUS:  *out =  v; return true;
            default: return false;
        }
    }
    if (e.kind == Nk.NODE_EXPR_BINARY && e.child_count >= 2)
    {
        long l; long r;
        if (!const_int(e.children[0], &l)) return false;
        if (!const_int(e.children[1], &r)) return false;
        switch (e.p.op.op)
        {
            case Tt.TOKEN_PLUS:    *out = l + r; return true;
            case Tt.TOKEN_MINUS:   *out = l - r; return true;
            case Tt.TOKEN_STAR:    *out = l * r; return true;
            case Tt.TOKEN_SLASH:   if (r == 0) return false; *out = l / r; return true;
            default: return false;
        }
    }
    return false;
}

// Lower one node if it is a lowerable dialect-op use; else return it unchanged.
fn Node* DialectTable.lower_one(DialectTable* t, Node* n)
{
    OpUse u = classify_use(n);
    if (!u.ok || !t.dialect_known(u.dname, u.dlen)) return n;
    Opcode* o = t.find_opcode(u.dname, u.dlen, u.oname, u.olen);
    if (o == null || !o.has_rule) return n;
    LowerRule* r = t.select_rule(o, &u);
    if (r == null) return n;   // no matching rule (arity/pattern/guard) → keep
    if (t.fuel <= 0) { t.out_of_fuel = true; return n; }
    t.fuel--;
    t.lowerings_applied++;
    return t.substitute(r.action, r.bindings, u.args, u.argc);
}

// Recursively lower a node and all its children (post-order, then re-lower the
// node itself so a chained dialect lowering collapses). Returns the new node.
fn Node* DialectTable.lower_node(DialectTable* t, Node* n, int depth)
{
    if (n == null) return null;
    if (n.kind == Nk.NODE_DIALECT || n.kind == Nk.NODE_IRDL) return n;   // keep decls
    if (depth > LOWER_MAX_DEPTH) { t.too_deep = true; return n; }

    // lower children first
    for (usz i = 0; i < n.child_count; i++)
    {
        n.children[i] = t.lower_node(n.children[i], depth + 1);
    }
    // then try to lower this node; if it changed (and is itself a dialect op),
    // lower the result too (bounded by fuel + depth).
    Node* res = t.lower_one(n);
    if (res != n)
    {
        res = t.lower_node(res, depth + 1);
    }
    return res;
}

// Public driver: register, validate, lower in place. Returns the (possibly new)
// program root.
fn Node* DialectTable.run(DialectTable* t, Node* program)
{
    if (program == null) return program;
    t.register(program);
    t.validate_uses(program);
    return t.lower_node(program, 0);
}

// ── Stats / reporting ────────────────────────────────────────────────────────
fn int DialectTable.error_count(DialectTable* t)
{
    int e = 0;
    for (int i = 0; i < t.diag_count; i++) { if (t.diags[i].is_error) e++; }
    return e;
}
