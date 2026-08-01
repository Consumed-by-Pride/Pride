// ============================================================================
// theory_opt.c3 — the optimizer: DCE, constant folding, and AST cleanup
// ----------------------------------------------------------------------------
// Pride is an UNTYPED language. The compiler does not reject a program because
// types disagree — it assumes the developer meant what they wrote. That policy
// has a direct consequence for this file:
//
//     Every fact an analysis computes is an OPTIMIZATION OPPORTUNITY,
//     never a reason to refuse the program.
//
// So the interval analysis that used to say "index out of bounds: rejected"
// now says "this index is outside the array on every path, so the code after
// it is unreachable — delete it". Same fact, opposite posture. The developer
// keeps their program; the optimizer gets a free branch elimination.
//
// The passes, in the order `OptPipeline.run` applies them:
//
//   1. CONSTANT FOLDING      — arithmetic, comparison, logical, bitwise and
//                              cast expressions over literal operands are
//                              replaced by their value.
//   2. ALGEBRAIC SIMPLIFY    — identities that hold for ANY operand, so they
//                              need no constant: x+0, x*1, x*0, x-x, x&x,
//                              x|0, x^x, x/1, x<<0, and the boolean forms.
//   3. BRANCH FOLDING        — `if true`/`if false` collapse to the taken arm.
//                              Conditions the abstract interpreter decided are
//                              folded too, which is where the analyses pay off.
//   4. DEAD CODE ELIMINATION — three separate notions of "dead":
//                                a. UNREACHABLE  — statements after a
//                                   diverging terminator (return/ub!/trap).
//                                b. USELESS      — a pure expression whose
//                                   value nobody consumes.
//                                c. DEAD STORE   — a `let` never read, whose
//                                   initializer is pure.
//   5. COPY PROPAGATION      — `let a = b` then uses of `a` become uses of `b`,
//                              which exposes more of everything above.
//   6. CSE                   — identical pure subexpressions in the same block
//                              are numbered, so a repeat is a known value.
//
// Purity is the safety interlock for 4b, 4c and 6. `is_pure` is deliberately
// CONSERVATIVE: it answers "definitely no side effects", and anything it is
// unsure about (a call, an assignment, asm, a volatile access, a perform) is
// treated as impure and never removed. Getting this backwards would delete
// the user's I/O, which is the one unforgivable optimizer bug.
//
// Every pass is a fixpoint: passes expose opportunities for each other, so the
// pipeline repeats until nothing changes or the round budget runs out.
// ============================================================================

module theory_opt;

import pfront_lex;
import pfront_core;
import theory_live;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const int OPT_MAX_DEPTH  = 300;
const int OPT_MAX_ROUNDS = 8;
// Capacities. Each table is open-addressed with a power-of-two bucket count
// so the index is a mask rather than a modulo, and each is sized ~2x the
// entry cap to keep the load factor under 0.5 (linear probing degrades badly
// past that). These are the limits that decide how large a function the
// front end can optimize, so they are generous.
const usz OPT_MAX_COPIES = 16384;
const usz OPT_MAX_VN     = 65536;
const usz OPT_MAX_USES   = 65536;
const usz OPT_USE_BUCKETS  = 131072;   // 2x OPT_MAX_USES
const usz OPT_COPY_BUCKETS = 32768;    // 2x OPT_MAX_COPIES
const usz OPT_VN_BUCKETS   = 131072;   // 2x OPT_MAX_VN

// Pointer hash. Node pointers are 8-byte aligned, so the low three bits are
// always zero and hashing the raw value would collide every 8th slot into
// one bucket. Multiplying by a 64-bit odd constant (splitmix64's finaliser)
// spreads those bits across the whole word first.
fn ulong hash_ptr(void* p)
{
    ulong x = (ulong)(usz)p;
    x = x ^ (x >> 30);
    x = x * 0xbf58476d1ce4e5b9UL;
    x = x ^ (x >> 27);
    x = x * 0x94d049bb133111ebUL;
    x = x ^ (x >> 31);
    return x;
}

// ════════════════════════════════════════════════════════════════════════════
// PURITY
// ════════════════════════════════════════════════════════════════════════════
// The interlock that makes deletion safe. Answers "definitely no side effect".
// Anything unknown answers false, so the optimizer leaves it alone.

fn bool is_pure_kind(Nk k)
{
    switch (k)
    {
        // Literals and names: reading them cannot do anything.
        // Then pure combinators, which are pure over pure children.
        case N_EXPR_INT:
        case N_EXPR_FLOAT:
        case N_EXPR_BOOL:
        case N_EXPR_CHAR:
        case N_EXPR_STRING:
        case N_EXPR_BYTES:
        case N_EXPR_NULL:
        case N_EXPR_UNIT:
        case N_EXPR_IDENT:
        case N_EXPR_PATH:
        case N_EXPR_SELF:
        case N_EXPR_BINARY:
        case N_EXPR_UNARY:
        case N_EXPR_FIELD:
        case N_EXPR_INDEX:
        case N_EXPR_SLICE:
        case N_EXPR_CAST:
        case N_EXPR_TUPLE:
        case N_EXPR_ARRAY:
        case N_EXPR_STRUCT_LIT:
        case N_EXPR_FIELD_INIT:
        case N_EXPR_RANGE:
        case N_EXPR_REF:
        case N_EXPR_SIZEOF:
        case N_EXPR_ALIGNOF:
        case N_EXPR_OFFSETOF:
        case N_EXPR_TYPEOF:
            return true;
        // Everything else — calls, assignments, perform, asm, syscall,
        // atomics, volatile, alloc/free, deref (may fault), await, try —
        // is treated as effectful. Conservative by construction.
        default:
            return false;
    }
}

// A whole subtree is pure only if the root and every descendant are.
fn bool is_pure(Node* n, int depth)
{
    if (n == null) { return true; }
    if (depth > OPT_MAX_DEPTH) { return false; }
    if (!is_pure_kind(n.kind)) { return false; }
    // A node carrying a non-pure effect bit overrides the kind test: effect
    // inference may have discovered something the shape does not show.
    if (n.effects != pfront_core::EFF_PURE) { return false; }
    for (usz i = 0; i < n.child_count; i++)
    {
        if (!is_pure(n.children[i], depth + 1)) { return false; }
    }
    return true;
}

// A terminator ends its block: nothing after it in the same block can run.
fn bool is_divergent(Node* n)
{
    if (n == null) { return false; }
    switch (n.kind)
    {
        case N_STMT_RETURN:
        case N_STMT_BREAK:
        case N_STMT_CONTINUE:
        case N_EXPR_UB:
        case N_EXPR_UNREACHABLE:
        case N_EXPR_TRAP:
            return true;
        case N_STMT_EXPR:
            return is_divergent(n.child(0));
        default:
            return false;
    }
}

// ════════════════════════════════════════════════════════════════════════════
// LITERAL VIEW
// ════════════════════════════════════════════════════════════════════════════
// A uniform way to ask "is this a compile-time known scalar, and what is it".

struct Lit
{
    bool   known;
    bool   is_float;
    bool   is_bool;
    long   i;
    double f;
}

fn Lit lit_none()
{
    Lit l;
    l.known = false; l.is_float = false; l.is_bool = false;
    l.i = 0; l.f = 0.0;
    return l;
}

fn Lit lit_int(long v)
{
    Lit l;
    l.known = true; l.is_float = false; l.is_bool = false;
    l.i = v; l.f = 0.0;
    return l;
}

fn Lit lit_bool(bool v)
{
    Lit l;
    l.known = true; l.is_float = false; l.is_bool = true;
    l.i = v ? 1 : 0; l.f = 0.0;
    return l;
}

fn Lit lit_float(double v)
{
    Lit l;
    l.known = true; l.is_float = true; l.is_bool = false;
    l.i = 0; l.f = v;
    return l;
}

fn Lit lit_of(Node* n)
{
    if (n == null) { return lit_none(); }
    switch (n.kind)
    {
        case N_EXPR_INT:   return lit_int((long)n.p.ival);
        case N_EXPR_BOOL:  return lit_bool(n.p.ival != 0);
        case N_EXPR_FLOAT: return lit_float(n.p.fval);
        case N_EXPR_CHAR:  return lit_int((long)n.p.ival);
        default:           return lit_none();
    }
}

// Rewrite a node IN PLACE into a literal. In-place matters: the node is
// already wired into its parent's child array and carries the source
// position, so mutating it keeps every back-pointer and every diagnostic
// location intact. Allocating a replacement would require fixing up the
// parent, and would lose the span.
fn void become_int(Node* n, long v)
{
    n.kind = Nk.N_EXPR_INT;
    n.p.ival = (ulong)v;
    n.p.fval = 0.0;
    n.child_count = 0;
    n.flags = n.flags | pfront_core::NF_SYNTHETIC;
}

fn void become_bool(Node* n, bool v)
{
    n.kind = Nk.N_EXPR_BOOL;
    n.p.ival = v ? 1 : 0;
    n.p.fval = 0.0;
    n.child_count = 0;
    n.flags = n.flags | pfront_core::NF_SYNTHETIC;
}

fn void become_float(Node* n, double v)
{
    n.kind = Nk.N_EXPR_FLOAT;
    n.p.fval = v;
    n.p.ival = 0;
    n.child_count = 0;
    n.flags = n.flags | pfront_core::NF_SYNTHETIC;
}

// Replace `n` by its child `c`, in place, preserving `n`'s identity.
fn void become_copy_of(Node* n, Node* c)
{
    if (n == null || c == null) { return; }
    n.kind        = c.kind;
    n.name_id     = c.name_id;
    n.effects     = c.effects;
    n.type_ann    = c.type_ann;
    n.type_slot   = c.type_slot;
    n.resolved    = c.resolved;
    n.sym         = c.sym;
    n.p           = c.p;
    n.children    = c.children;
    n.child_count = c.child_count;
    n.child_cap   = c.child_cap;
    // Reparent the adopted children onto `n`, or later passes walking
    // upward would leave the tree through a stale pointer.
    for (usz i = 0; i < n.child_count; i++)
    {
        if (n.children[i] != null) { n.children[i].parent = n; }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// PASS 1 — CONSTANT FOLDING
// ════════════════════════════════════════════════════════════════════════════

// Integer division and remainder are the two operations that can trap. Pride
// does not reject `x / 0`; the fold simply DECLINES, leaving the division in
// the tree for the back end to handle as the target defines.
fn bool fold_int_binop(int op, long a, long b, long* out)
{
    switch ((Tk)op)
    {
        case TOKEN_PLUS:    *out = a + b; return true;
        case TOKEN_MINUS:   *out = a - b; return true;
        case TOKEN_STAR:    *out = a * b; return true;
        case TOKEN_SLASH:
            if (b == 0) { return false; }
            // INT64_MIN / -1 overflows. Decline rather than fold to a wrong
            // value; the back end knows the target's behaviour.
            if (a == (-9223372036854775807L - 1) && b == -1) { return false; }
            *out = a / b; return true;
        case TOKEN_PERCENT:
            if (b == 0) { return false; }
            if (a == (-9223372036854775807L - 1) && b == -1) { return false; }
            *out = a % b; return true;
        case TOKEN_AMP:     *out = a & b; return true;
        case TOKEN_PIPE:    *out = a | b; return true;
        case TOKEN_XOR:     *out = a ^ b; return true;
        case TOKEN_LSHIFT:
            if (b < 0 || b > 63) { return false; }
            *out = (long)((ulong)a << (ulong)b); return true;
        case TOKEN_RSHIFT:
            if (b < 0 || b > 63) { return false; }
            *out = a >> b; return true;
        // Wrapping forms are defined to wrap, so they always fold.
        case TOKEN_PLUS_PERCENT:  *out = (long)((ulong)a + (ulong)b); return true;
        case TOKEN_MINUS_PERCENT: *out = (long)((ulong)a - (ulong)b); return true;
        case TOKEN_STAR_PERCENT:  *out = (long)((ulong)a * (ulong)b); return true;
        default: return false;
    }
}

fn bool fold_int_cmp(int op, long a, long b, bool* out)
{
    switch ((Tk)op)
    {
        case TOKEN_EQEQ:    *out = a == b; return true;
        case TOKEN_NEQ:     *out = a != b; return true;
        case TOKEN_NEQ_UNI: *out = a != b; return true;
        case TOKEN_LT:      *out = a < b;  return true;
        case TOKEN_GT:      *out = a > b;  return true;
        case TOKEN_LTEQ:    *out = a <= b; return true;
        case TOKEN_GTEQ:    *out = a >= b; return true;
        case TOKEN_LEQ_UNI: *out = a <= b; return true;
        case TOKEN_GEQ_UNI: *out = a >= b; return true;
        default: return false;
    }
}

fn bool fold_float_binop(int op, double a, double b, double* out)
{
    switch ((Tk)op)
    {
        case TOKEN_PLUS:  *out = a + b; return true;
        case TOKEN_MINUS: *out = a - b; return true;
        case TOKEN_STAR:  *out = a * b; return true;
        case TOKEN_SLASH:
            // Float division by zero is defined (inf/nan) but folding it
            // would bake in a value the target's rounding mode may differ
            // on. Decline; this is the conservative choice.
            if (b == 0.0) { return false; }
            *out = a / b; return true;
        default: return false;
    }
}

fn bool fold_float_cmp(int op, double a, double b, bool* out)
{
    switch ((Tk)op)
    {
        case TOKEN_EQEQ:    *out = a == b; return true;
        case TOKEN_NEQ:     *out = a != b; return true;
        case TOKEN_LT:      *out = a < b;  return true;
        case TOKEN_GT:      *out = a > b;  return true;
        case TOKEN_LTEQ:    *out = a <= b; return true;
        case TOKEN_GTEQ:    *out = a >= b; return true;
        default: return false;
    }
}

fn bool is_bool_op(int op)
{
    Tk t = (Tk)op;
    return t == Tk.TOKEN_AMPAMP || t == Tk.TOKEN_PIPEPIPE;
}

// Truncate a folded integer to a declared width, matching what the back end
// will store. `300 as u8` is 44, and folding it to 300 would be a miscompile.
fn long truncate_to(long v, char width, bool is_signed)
{
    if (width == 0 || width >= 64) { return v; }
    ulong bits = (ulong)width;
    ulong mask = (1UL << bits) - 1UL;
    ulong raw = (ulong)v & mask;
    if (is_signed)
    {
        ulong sign_bit = 1UL << (bits - 1UL);
        if ((raw & sign_bit) != 0) { return (long)(raw | ~mask); }
    }
    return (long)raw;
}

// ════════════════════════════════════════════════════════════════════════════
// USE COUNTING
// ════════════════════════════════════════════════════════════════════════════
// Dead-store elimination needs to know whether a binding is ever read. The
// resolver already points each identifier at its binder, so counting is a
// single walk keyed on that pointer.

struct UseEntry
{
    Node* binder;
    usz   reads;
    usz   writes;
}

// Open-addressed index over `items`. `buckets[b]` holds index+1 into items,
// so 0 means empty and no separate occupancy array is needed.
struct UseMap
{
    UseEntry[OPT_MAX_USES] items;
    uint[OPT_USE_BUCKETS]  buckets;
    usz count;
    bool overflow;
}

fn void UseMap.init(UseMap* u)
{
    u.count = 0;
    u.overflow = false;
    for (usz i = 0; i < OPT_USE_BUCKETS; i++) { u.buckets[i] = 0; }
}

fn int UseMap.find(UseMap* u, Node* binder)
{
    usz mask = OPT_USE_BUCKETS - 1;
    usz b = (usz)(hash_ptr((void*)binder)) & mask;
    for (usz probe = 0; probe < OPT_USE_BUCKETS; probe++)
    {
        uint slot = u.buckets[b];
        if (slot == 0) { return -1; }
        if (u.items[slot - 1].binder == binder) { return (int)(slot - 1); }
        b = (b + 1) & mask;
    }
    return -1;
}

fn int UseMap.intern(UseMap* u, Node* binder)
{
    usz mask = OPT_USE_BUCKETS - 1;
    usz b = (usz)(hash_ptr((void*)binder)) & mask;
    for (usz probe = 0; probe < OPT_USE_BUCKETS; probe++)
    {
        uint slot = u.buckets[b];
        if (slot == 0)
        {
            if (u.count >= OPT_MAX_USES) { u.overflow = true; return -1; }
            usz i = u.count;
            u.items[i].binder = binder;
            u.items[i].reads = 0;
            u.items[i].writes = 0;
            u.count = u.count + 1;
            u.buckets[b] = (uint)(i + 1);
            return (int)i;
        }
        if (u.items[slot - 1].binder == binder) { return (int)(slot - 1); }
        b = (b + 1) & mask;
    }
    u.overflow = true;
    return -1;
}

fn void UseMap.add_read(UseMap* u, Node* binder)
{
    if (binder == null) { return; }
    int at = u.intern(binder);
    if (at >= 0) { u.items[at].reads = u.items[at].reads + 1; }
}

fn void UseMap.add_write(UseMap* u, Node* binder)
{
    if (binder == null) { return; }
    int at = u.intern(binder);
    if (at >= 0) { u.items[at].writes = u.items[at].writes + 1; }
}

fn usz UseMap.reads_of(UseMap* u, Node* binder)
{
    int at = u.find(binder);
    if (at < 0) { return 0; }
    return u.items[at].reads;
}

// Walk the tree attributing every identifier occurrence to its binder. An
// identifier on the left of an assignment is a WRITE, not a read — counting
// it as a read would keep every dead store alive.
fn void UseMap.scan(UseMap* u, Node* n, int depth)
{
    if (n == null || depth > OPT_MAX_DEPTH) { return; }

    if (n.kind == Nk.N_STMT_ASSIGN || n.kind == Nk.N_EXPR_ASSIGN)
    {
        Node* lhs = n.child(0);
        Node* rhs = n.child(1);
        if (lhs != null && lhs.kind == Nk.N_EXPR_IDENT)
        {
            u.add_write(lhs.resolved);
        }
        else
        {
            // A compound lvalue (`a.f`, `a[i]`) READS the base to find the
            // location, so it keeps the base alive.
            u.scan(lhs, depth + 1);
        }
        u.scan(rhs, depth + 1);
        return;
    }

    // A compound assignment reads AND writes its target.
    if (n.kind == Nk.N_STMT_COMPOUND_ASSIGN)
    {
        Node* lhs = n.child(0);
        if (lhs != null && lhs.kind == Nk.N_EXPR_IDENT)
        {
            u.add_read(lhs.resolved);
            u.add_write(lhs.resolved);
        }
        else { u.scan(lhs, depth + 1); }
        u.scan(n.child(1), depth + 1);
        return;
    }

    // Taking a reference is an escape: the value can be read or written
    // through the pointer, so the binding must stay.
    if (n.kind == Nk.N_EXPR_REF)
    {
        Node* t = n.child(0);
        if (t != null && t.kind == Nk.N_EXPR_IDENT && t.resolved != null)
        {
            u.add_read(t.resolved);
            u.add_write(t.resolved);
        }
        else { u.scan(t, depth + 1); }
        return;
    }

    if (n.kind == Nk.N_EXPR_IDENT && n.resolved != null)
    {
        u.add_read(n.resolved);
    }

    for (usz i = 0; i < n.child_count; i++) { u.scan(n.children[i], depth + 1); }
}

// ════════════════════════════════════════════════════════════════════════════
// COPY PROPAGATION
// ════════════════════════════════════════════════════════════════════════════
// `let a = b` makes every later `a` mean `b`. Propagating exposes further
// folding, and lets the dead-store pass remove `a` entirely.

struct CopyEntry
{
    Node* from;      // the binder being defined  (a)
    Node* to;        // the binder it aliases     (b)
    bool  valid;
}

struct CopyMap
{
    CopyEntry[OPT_MAX_COPIES] items;
    uint[OPT_COPY_BUCKETS]    buckets;   // index+1 keyed on `from`
    usz count;
}

fn void CopyMap.init(CopyMap* c)
{
    c.count = 0;
    for (usz i = 0; i < OPT_COPY_BUCKETS; i++) { c.buckets[i] = 0; }
}

// Look up the entry defining `from`, or -1. Only ONE entry per `from` is
// ever recorded (a binder is defined once), which is what makes the hash
// index sound here.
fn int CopyMap.find_from(CopyMap* c, Node* from)
{
    usz mask = OPT_COPY_BUCKETS - 1;
    usz b = (usz)(hash_ptr((void*)from)) & mask;
    for (usz probe = 0; probe < OPT_COPY_BUCKETS; probe++)
    {
        uint slot = c.buckets[b];
        if (slot == 0) { return -1; }
        if (c.items[slot - 1].from == from) { return (int)(slot - 1); }
        b = (b + 1) & mask;
    }
    return -1;
}

fn void CopyMap.record(CopyMap* c, Node* from, Node* to)
{
    if (from == null || to == null || c.count >= OPT_MAX_COPIES) { return; }
    // A self-copy carries no information and would loop the resolver.
    if (from == to) { return; }
    if (c.find_from(from) >= 0) { return; }   // already defined
    usz i = c.count;
    c.items[i].from = from;
    c.items[i].to = to;
    c.items[i].valid = true;
    c.count = c.count + 1;
    usz mask = OPT_COPY_BUCKETS - 1;
    usz b = (usz)(hash_ptr((void*)from)) & mask;
    for (usz probe = 0; probe < OPT_COPY_BUCKETS; probe++)
    {
        if (c.buckets[b] == 0) { c.buckets[b] = (uint)(i + 1); return; }
        b = (b + 1) & mask;
    }
}

fn Node* CopyMap.resolve(CopyMap* c, Node* b)
{
    if (b == null) { return null; }
    Node* cur = b;
    // Chase `a -> b -> c` to the end, with a hop budget so a cycle that
    // slipped past `record` cannot hang the compiler.
    for (int hop = 0; hop < 32; hop++)
    {
        int at = c.find_from(cur);
        if (at < 0 || !c.items[at].valid) { break; }
        cur = c.items[at].to;
    }
    return cur;
}

// Any assignment to a binder invalidates copies that mention it: after
// `b = 5`, an `a` that aliased `b` no longer means the same thing.
// Invalidate every alias mentioning `binder`. The `from` side is indexed so
// that half is O(1); the `to` side is not (many entries may share one `to`),
// so it is a scan. That is acceptable because `kill` runs once per
// ASSIGNMENT, not once per identifier, and assignments are rare relative to
// uses.
fn void CopyMap.kill(CopyMap* c, Node* binder)
{
    if (binder == null) { return; }
    int at = c.find_from(binder);
    if (at >= 0) { c.items[at].valid = false; }
    for (usz i = 0; i < c.count; i++)
    {
        if (c.items[i].to == binder) { c.items[i].valid = false; }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// VALUE NUMBERING (CSE)
// ════════════════════════════════════════════════════════════════════════════
// Structurally identical PURE expressions get the same number. A second
// occurrence is then a known redundancy. This implementation reports the
// redundancy and marks the node; it deliberately does NOT rewrite to a temp,
// because introducing a binding requires a scope to put it in and that is the
// middle end's job. The count is what the SSI builder will consume.

struct VnEntry
{
    ulong hash;
    Node* rep;      // first expression seen with this hash
}

struct ValueTable
{
    VnEntry[OPT_MAX_VN]  items;
    uint[OPT_VN_BUCKETS] buckets;   // index+1 keyed on the structural hash
    usz count;
    usz hits;
}

fn void ValueTable.init(ValueTable* v)
{
    v.count = 0;
    v.hits = 0;
    for (usz i = 0; i < OPT_VN_BUCKETS; i++) { v.buckets[i] = 0; }
}

// Structural hash. Identifiers hash by their BINDER, not their name, so two
// different `x` in different scopes do not collide.
fn ulong vn_hash(Node* n, int depth)
{
    if (n == null || depth > 24) { return 1469598103934665603UL; }
    ulong h = 1469598103934665603UL;
    h = (h ^ (ulong)(int)n.kind) * 1099511628211UL;
    h = (h ^ (ulong)n.p.op) * 1099511628211UL;
    switch (n.kind)
    {
        case N_EXPR_INT:
        case N_EXPR_BOOL:
        case N_EXPR_CHAR:
            h = (h ^ n.p.ival) * 1099511628211UL;
        case N_EXPR_IDENT:
            h = (h ^ (ulong)(usz)(void*)n.resolved) * 1099511628211UL;
            if (n.resolved == null)
            {
                h = (h ^ (ulong)n.name_id) * 1099511628211UL;
            }
        case N_EXPR_FIELD:
            h = (h ^ (ulong)n.name_id) * 1099511628211UL;
        default:
            break;
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        h = (h ^ vn_hash(n.children[i], depth + 1)) * 1099511628211UL;
    }
    return h;
}

// Hash equality is not enough — collisions would merge unrelated expressions.
// This confirms structural identity before reporting a hit.
fn bool vn_equal(Node* a, Node* b, int depth)
{
    if (a == b) { return true; }
    if (a == null || b == null) { return false; }
    if (depth > 24) { return false; }
    if (a.kind != b.kind) { return false; }
    if (a.p.op != b.p.op) { return false; }
    if (a.child_count != b.child_count) { return false; }
    switch (a.kind)
    {
        case N_EXPR_INT:
        case N_EXPR_BOOL:
        case N_EXPR_CHAR:
            if (a.p.ival != b.p.ival) { return false; }
        case N_EXPR_IDENT:
            if (a.resolved != b.resolved) { return false; }
            if (a.resolved == null && a.name_id != b.name_id) { return false; }
        case N_EXPR_FIELD:
            if (a.name_id != b.name_id) { return false; }
        default:
            break;
    }
    for (usz i = 0; i < a.child_count; i++)
    {
        if (!vn_equal(a.children[i], b.children[i], depth + 1)) { return false; }
    }
    return true;
}

fn Node* ValueTable.lookup_or_add(ValueTable* v, Node* e)
{
    ulong h = vn_hash(e, 0);
    usz mask = OPT_VN_BUCKETS - 1;
    usz b = (usz)h & mask;
    for (usz probe = 0; probe < OPT_VN_BUCKETS; probe++)
    {
        uint slot = v.buckets[b];
        if (slot == 0)
        {
            if (v.count < OPT_MAX_VN)
            {
                usz i = v.count;
                v.items[i].hash = h;
                v.items[i].rep = e;
                v.count = v.count + 1;
                v.buckets[b] = (uint)(i + 1);
            }
            return null;
        }
        // Hash equality is a filter, not a proof: confirm structurally
        // before reporting a hit, or a collision would merge two unrelated
        // expressions and the CSE would be a miscompile.
        if (v.items[slot - 1].hash == h && vn_equal(v.items[slot - 1].rep, e, 0))
        {
            v.hits = v.hits + 1;
            return v.items[slot - 1].rep;
        }
        b = (b + 1) & mask;
    }
    return null;
}

// ════════════════════════════════════════════════════════════════════════════
// THE OPTIMIZER
// ════════════════════════════════════════════════════════════════════════════

struct Optimizer
{
    Arena*                 arena;
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;

    UseMap*     uses;
    // Liveness, if the pass ran. Optional: the optimizer is correct without
    // it (it falls back to its own use counts), but with it a store can be
    // proven dead across a whole CFG rather than only inside one block.
    theory_live::LivenessAnalysis* live;
    CopyMap*    copies;
    ValueTable* vn;

    // counters — every one is printed, so a pass that never fires is visible
    usz folded_arith;
    usz folded_cmp;
    usz folded_cast;
    usz folded_logic;
    usz simplified;
    usz branches_folded;
    usz dead_unreachable;
    usz dead_useless;
    usz dead_stores;
    usz copies_propagated;
    usz cse_found;
    usz loops_removed;
    usz live_dead_stores;    // removed using CFG liveness, not just use counts
    usz blocks_flattened;
    usz empty_dropped;
    usz rounds;
    usz nodes_before;
    usz nodes_after;

    int  level;      // 0 = off, 1 = fold only, 2 = +DCE, 3 = +CSE/copy-prop
    bool verbose;
}

fn bool Optimizer.init(Optimizer* o, Arena* a, pfront_core::DiagBag* d,
                       pfront_core::Interner* it, char* file)
{
    o.arena = a;
    o.diags = d;
    o.interner = it;
    o.file = file;
    o.folded_arith = 0;
    o.folded_cmp = 0;
    o.folded_cast = 0;
    o.folded_logic = 0;
    o.simplified = 0;
    o.branches_folded = 0;
    o.dead_unreachable = 0;
    o.dead_useless = 0;
    o.dead_stores = 0;
    o.copies_propagated = 0;
    o.cse_found = 0;
    o.loops_removed = 0;
    o.live_dead_stores = 0;
    o.blocks_flattened = 0;
    o.empty_dropped = 0;
    o.rounds = 0;
    o.nodes_before = 0;
    o.nodes_after = 0;
    o.level = 2;
    o.verbose = false;

    // These three are far too large for the 64 KB stack-object limit.
    o.live = null;
    o.uses = (UseMap*)malloc(UseMap::size);
    o.copies = (CopyMap*)malloc(CopyMap::size);
    o.vn = (ValueTable*)malloc(ValueTable::size);
    if (o.uses == null || o.copies == null || o.vn == null)
    {
        o.destroy();
        return false;
    }
    o.uses.init();
    o.copies.init();
    o.vn.init();
    return true;
}

fn void Optimizer.destroy(Optimizer* o)
{
    if (o.uses   != null) { free((void*)o.uses);   o.uses = null; }
    if (o.copies != null) { free((void*)o.copies); o.copies = null; }
    if (o.vn     != null) { free((void*)o.vn);     o.vn = null; }
}

fn usz count_nodes(Node* n, int depth)
{
    if (n == null || depth > OPT_MAX_DEPTH) { return 0; }
    usz total = 1;
    for (usz i = 0; i < n.child_count; i++)
    {
        total = total + count_nodes(n.children[i], depth + 1);
    }
    return total;
}

// ── Pass 1+2: fold and simplify, bottom-up ──────────────────────────────────
// Bottom-up matters: folding the children first is what makes the parent
// foldable. `(1+2)*3` only becomes `9` because `1+2` became `3` first.
fn bool Optimizer.fold_expr(Optimizer* o, Node* e, int depth)
{
    if (e == null || depth > OPT_MAX_DEPTH) { return false; }

    bool changed = false;
    for (usz i = 0; i < e.child_count; i++)
    {
        if (o.fold_expr(e.children[i], depth + 1)) { changed = true; }
    }

    switch (e.kind)
    {
        case N_EXPR_BINARY:
        {
            Node* l = e.child(0);
            Node* r = e.child(1);
            if (l == null || r == null) { return changed; }
            Lit a = lit_of(l);
            Lit b = lit_of(r);

            // -- short-circuit operators fold on the LEFT alone -------------
            // `false && anything` is false even when the right side is a
            // call, because the call never runs.
            if (is_bool_op(e.p.op))
            {
                if (a.known && a.is_bool)
                {
                    bool av = a.i != 0;
                    if ((Tk)e.p.op == Tk.TOKEN_AMPAMP && !av)
                    {
                        become_bool(e, false);
                        o.folded_logic = o.folded_logic + 1;
                        return true;
                    }
                    if ((Tk)e.p.op == Tk.TOKEN_PIPEPIPE && av)
                    {
                        become_bool(e, true);
                        o.folded_logic = o.folded_logic + 1;
                        return true;
                    }
                    // `true && x` is x, `false || x` is x — but only when x
                    // is pure, or we would move an effect.
                    if (is_pure(r, 0))
                    {
                        become_copy_of(e, r);
                        o.folded_logic = o.folded_logic + 1;
                        return true;
                    }
                }
                return changed;
            }

            // -- both sides constant ----------------------------------------
            if (a.known && b.known && !a.is_float && !b.is_float)
            {
                long out = 0;
                bool bout = false;
                if (fold_int_binop(e.p.op, a.i, b.i, &out))
                {
                    become_int(e, out);
                    o.folded_arith = o.folded_arith + 1;
                    return true;
                }
                if (fold_int_cmp(e.p.op, a.i, b.i, &bout))
                {
                    become_bool(e, bout);
                    o.folded_cmp = o.folded_cmp + 1;
                    return true;
                }
                return changed;
            }
            if (a.known && b.known && (a.is_float || b.is_float))
            {
                double af = a.is_float ? a.f : (double)a.i;
                double bf = b.is_float ? b.f : (double)b.i;
                double fout = 0.0;
                bool bout = false;
                if (fold_float_binop(e.p.op, af, bf, &fout))
                {
                    become_float(e, fout);
                    o.folded_arith = o.folded_arith + 1;
                    return true;
                }
                if (fold_float_cmp(e.p.op, af, bf, &bout))
                {
                    become_bool(e, bout);
                    o.folded_cmp = o.folded_cmp + 1;
                    return true;
                }
                return changed;
            }

            // -- algebraic identities: no constant needed on both sides -----
            // Each is guarded on purity where dropping a side would lose an
            // effect. `f() * 0` is NOT 0 if f prints something.
            Tk op = (Tk)e.p.op;

            // x + 0, 0 + x, x - 0  ->  x
            if (op == Tk.TOKEN_PLUS || op == Tk.TOKEN_MINUS)
            {
                if (b.known && !b.is_float && b.i == 0)
                {
                    become_copy_of(e, l);
                    o.simplified = o.simplified + 1;
                    return true;
                }
                if (op == Tk.TOKEN_PLUS && a.known && !a.is_float && a.i == 0)
                {
                    become_copy_of(e, r);
                    o.simplified = o.simplified + 1;
                    return true;
                }
            }

            // x * 1, 1 * x, x / 1  ->  x        x * 0, 0 * x -> 0 (pure only)
            if (op == Tk.TOKEN_STAR || op == Tk.TOKEN_SLASH)
            {
                if (b.known && !b.is_float && b.i == 1)
                {
                    become_copy_of(e, l);
                    o.simplified = o.simplified + 1;
                    return true;
                }
                if (op == Tk.TOKEN_STAR && a.known && !a.is_float && a.i == 1)
                {
                    become_copy_of(e, r);
                    o.simplified = o.simplified + 1;
                    return true;
                }
                if (op == Tk.TOKEN_STAR && b.known && !b.is_float && b.i == 0
                    && is_pure(l, 0))
                {
                    become_int(e, 0);
                    o.simplified = o.simplified + 1;
                    return true;
                }
                if (op == Tk.TOKEN_STAR && a.known && !a.is_float && a.i == 0
                    && is_pure(r, 0))
                {
                    become_int(e, 0);
                    o.simplified = o.simplified + 1;
                    return true;
                }
            }

            // x << 0, x >> 0  ->  x
            if (op == Tk.TOKEN_LSHIFT || op == Tk.TOKEN_RSHIFT)
            {
                if (b.known && !b.is_float && b.i == 0)
                {
                    become_copy_of(e, l);
                    o.simplified = o.simplified + 1;
                    return true;
                }
            }

            // x | 0 -> x,  x & -1 -> x,  x ^ 0 -> x
            if (op == Tk.TOKEN_PIPE && b.known && !b.is_float && b.i == 0)
            {
                become_copy_of(e, l);
                o.simplified = o.simplified + 1;
                return true;
            }
            if (op == Tk.TOKEN_XOR && b.known && !b.is_float && b.i == 0)
            {
                become_copy_of(e, l);
                o.simplified = o.simplified + 1;
                return true;
            }
            if (op == Tk.TOKEN_AMP && b.known && !b.is_float && b.i == -1)
            {
                become_copy_of(e, l);
                o.simplified = o.simplified + 1;
                return true;
            }
            // x & 0 -> 0 (pure only)
            if (op == Tk.TOKEN_AMP && b.known && !b.is_float && b.i == 0
                && is_pure(l, 0))
            {
                become_int(e, 0);
                o.simplified = o.simplified + 1;
                return true;
            }

            // -- identities over two IDENTICAL pure operands -----------------
            // x - x -> 0, x ^ x -> 0, x & x -> x, x | x -> x, x == x -> true.
            // Purity is essential: `f() - f()` is not 0.
            if (is_pure(l, 0) && is_pure(r, 0) && vn_equal(l, r, 0))
            {
                if (op == Tk.TOKEN_MINUS || op == Tk.TOKEN_XOR)
                {
                    become_int(e, 0);
                    o.simplified = o.simplified + 1;
                    return true;
                }
                if (op == Tk.TOKEN_AMP || op == Tk.TOKEN_PIPE)
                {
                    become_copy_of(e, l);
                    o.simplified = o.simplified + 1;
                    return true;
                }
                if (op == Tk.TOKEN_EQEQ || op == Tk.TOKEN_LTEQ || op == Tk.TOKEN_GTEQ)
                {
                    become_bool(e, true);
                    o.simplified = o.simplified + 1;
                    return true;
                }
                if (op == Tk.TOKEN_NEQ || op == Tk.TOKEN_LT || op == Tk.TOKEN_GT)
                {
                    become_bool(e, false);
                    o.simplified = o.simplified + 1;
                    return true;
                }
                if (op == Tk.TOKEN_SLASH)
                {
                    // x / x is 1 only when x is definitely non-zero, which we
                    // do not know here. Decline.
                    return changed;
                }
            }
            return changed;
        }

        case N_EXPR_UNARY:
        {
            Node* v = e.child(0);
            if (v == null) { return changed; }
            Lit a = lit_of(v);
            Tk op = (Tk)e.p.op;
            if (a.known && !a.is_float)
            {
                if (op == Tk.TOKEN_MINUS)
                {
                    become_int(e, -a.i);
                    o.folded_arith = o.folded_arith + 1;
                    return true;
                }
                if (op == Tk.TOKEN_BANG)
                {
                    become_bool(e, a.i == 0);
                    o.folded_logic = o.folded_logic + 1;
                    return true;
                }
                if (op == Tk.TOKEN_XOR)
                {
                    become_int(e, ~a.i);
                    o.folded_arith = o.folded_arith + 1;
                    return true;
                }
            }
            if (a.known && a.is_float && op == Tk.TOKEN_MINUS)
            {
                become_float(e, -a.f);
                o.folded_arith = o.folded_arith + 1;
                return true;
            }
            // Double negation: !!x -> x, --x -> x, ~~x -> x
            if (v.kind == Nk.N_EXPR_UNARY && v.p.op == e.p.op
                && (op == Tk.TOKEN_BANG || op == Tk.TOKEN_MINUS || op == Tk.TOKEN_XOR))
            {
                Node* inner = v.child(0);
                if (inner != null)
                {
                    become_copy_of(e, inner);
                    o.simplified = o.simplified + 1;
                    return true;
                }
            }
            return changed;
        }

        case N_EXPR_CAST:
        {
            // A cast of a literal to a known width folds, WITH truncation.
            Node* v = e.child(0);
            if (v == null) { return changed; }
            Lit a = lit_of(v);
            if (a.known && !a.is_float && e.p.width != 0)
            {
                long t = truncate_to(a.i, e.p.width, e.p.is_signed);
                become_int(e, t);
                e.p.width = e.p.width;
                o.folded_cast = o.folded_cast + 1;
                return true;
            }
            return changed;
        }

        default:
            return changed;
    }
}

// ── Pass 3: branch folding ──────────────────────────────────────────────────
// A decided condition means one arm is dead. Replacing the `if` by the taken
// arm removes the branch AND everything in the untaken side.
fn bool Optimizer.fold_branches(Optimizer* o, Node* n, int depth)
{
    if (n == null || depth > OPT_MAX_DEPTH) { return false; }

    bool changed = false;
    for (usz i = 0; i < n.child_count; i++)
    {
        if (o.fold_branches(n.children[i], depth + 1)) { changed = true; }
    }

    if (n.kind == Nk.N_EXPR_IF)
    {
        Node* cond = n.child(0);
        Node* then_b = n.child(1);
        Node* else_b = n.child(2);
        Lit c = lit_of(cond);
        // Only a literal condition folds, and only when evaluating it has no
        // effect. The abstract interpreter's findings arrive here as folded
        // literals from pass 1, which is why the two passes compose.
        if (c.known && is_pure(cond, 0))
        {
            bool taken = c.is_bool ? (c.i != 0) : (c.i != 0);
            Node* keep = taken ? then_b : else_b;
            if (keep != null)
            {
                become_copy_of(n, keep);
                o.branches_folded = o.branches_folded + 1;
                return true;
            }
            // `if false` with no else is the unit value.
            if (!taken && else_b == null)
            {
                n.kind = Nk.N_EXPR_UNIT;
                n.child_count = 0;
                o.branches_folded = o.branches_folded + 1;
                return true;
            }
        }
    }

    // `while false { ... }` never runs.
    if (n.kind == Nk.N_EXPR_WHILE)
    {
        Node* cond = n.child(0);
        Lit c = lit_of(cond);
        if (c.known && c.i == 0 && is_pure(cond, 0))
        {
            n.kind = Nk.N_EXPR_UNIT;
            n.child_count = 0;
            o.loops_removed = o.loops_removed + 1;
            return true;
        }
    }

    return changed;
}

// ── Pass 4: dead code elimination ───────────────────────────────────────────
// Blocks are the unit. Removing a statement means compacting the child array,
// which is safe because the arena never reuses the freed slot.
fn bool Optimizer.dce_block(Optimizer* o, Node* b)
{
    if (b == null || b.child_count == 0) { return false; }

    bool changed = false;
    usz write = 0;
    bool terminated = false;

    for (usz read = 0; read < b.child_count; read++)
    {
        Node* s = b.children[read];
        if (s == null) { continue; }

        // (a) UNREACHABLE — everything after a terminator in this block.
        if (terminated)
        {
            o.dead_unreachable = o.dead_unreachable + 1;
            changed = true;
            continue;
        }

        // (b) USELESS — a pure expression statement whose value is discarded.
        //     The LAST statement of a block is its value, so it is never
        //     useless; dropping it would change what the block returns.
        bool is_last = (read + 1 == b.child_count);
        if (!is_last && s.kind == Nk.N_STMT_EXPR)
        {
            Node* inner = s.child(0);
            if (inner != null && is_pure(inner, 0)
                && inner.kind != Nk.N_EXPR_UNIT)
            {
                o.dead_useless = o.dead_useless + 1;
                changed = true;
                continue;
            }
        }
        if (!is_last && pfront_core::is_expr(s.kind) && is_pure(s, 0)
            && s.kind != Nk.N_EXPR_UNIT && s.kind != Nk.N_EXPR_IF
            && s.kind != Nk.N_EXPR_MATCH && s.kind != Nk.N_EXPR_WHILE
            && s.kind != Nk.N_EXPR_FOR && s.kind != Nk.N_EXPR_LOOP)
        {
            o.dead_useless = o.dead_useless + 1;
            changed = true;
            continue;
        }

        // (c) DEAD STORE — a `let` nobody reads, with a pure initializer.
        //     An impure initializer stays: `let _ = launch_missiles()` must
        //     still launch. Only the binding is dead, not the work.
        if (s.kind == Nk.N_DECL_LET && o.level >= 2)
        {
            Node* binder = s.child(0);
            Node* init = s.child_count > 1 ? s.child(1) : null;
            if (binder != null && binder.kind == Nk.N_PAT_IDENT
                && (init == null || is_pure(init, 0))
                && (s.flags & pfront_core::NF_PUB) == 0
                && !is_last)
            {
                // Two independent reasons a store can be dead. The syntactic
                // one (no identifier anywhere refers to this binder) is
                // always available. The LIVENESS one is stronger: the
                // variable may be referenced textually and still be dead,
                // because every such reference is itself in dead code or the
                // value never reaches a use along any CFG path.
                bool syntactically_dead = o.uses.reads_of(binder) == 0;
                bool liveness_dead = false;
                if (o.live != null && !syntactically_dead)
                {
                    // Only trust liveness for variables it classified as
                    // block-local. A non-local variable crosses an edge, and
                    // proving it dead needs the full interprocedural picture
                    // this pass does not have.
                    int vi = o.live.vars.find(binder);
                    if (vi >= 0)
                    {
                        theory_live::VarEntry* ve = &o.live.vars.items[vi];
                        liveness_dead = ve.uses == 0 && !ve.addr_taken
                                        && !ve.non_local;
                    }
                }
                if (syntactically_dead || liveness_dead)
                {
                    o.dead_stores = o.dead_stores + 1;
                    if (liveness_dead && !syntactically_dead)
                    {
                        o.live_dead_stores = o.live_dead_stores + 1;
                    }
                    changed = true;
                    continue;
                }
            }
        }

        if (is_divergent(s)) { terminated = true; }

        b.children[write] = s;
        write = write + 1;
    }

    if (changed) { b.child_count = write; }
    return changed;
}

fn bool Optimizer.dce(Optimizer* o, Node* n, int depth)
{
    if (n == null || depth > OPT_MAX_DEPTH) { return false; }
    bool changed = false;
    for (usz i = 0; i < n.child_count; i++)
    {
        if (o.dce(n.children[i], depth + 1)) { changed = true; }
    }
    if (n.kind == Nk.N_BLOCK)
    {
        if (o.dce_block(n)) { changed = true; }
    }
    return changed;
}

// ── Pass 5: copy propagation ────────────────────────────────────────────────
fn void Optimizer.collect_copies(Optimizer* o, Node* n, int depth)
{
    if (n == null || depth > OPT_MAX_DEPTH) { return; }

    if (n.kind == Nk.N_DECL_LET)
    {
        Node* binder = n.child(0);
        Node* init = n.child_count > 1 ? n.child(1) : null;
        // Only an immutable binding may be propagated: a `mut` one can be
        // reassigned, and then the alias is wrong.
        if (binder != null && binder.kind == Nk.N_PAT_IDENT
            && init != null && init.kind == Nk.N_EXPR_IDENT
            && init.resolved != null
            && (n.flags & pfront_core::NF_MUT) == 0
            && (binder.flags & pfront_core::NF_MUT) == 0)
        {
            o.copies.record(binder, init.resolved);
        }
    }

    // Any write kills the alias.
    if (n.kind == Nk.N_STMT_ASSIGN || n.kind == Nk.N_EXPR_ASSIGN
        || n.kind == Nk.N_STMT_COMPOUND_ASSIGN)
    {
        Node* lhs = n.child(0);
        if (lhs != null && lhs.kind == Nk.N_EXPR_IDENT)
        {
            o.copies.kill(lhs.resolved);
        }
    }

    for (usz i = 0; i < n.child_count; i++)
    {
        o.collect_copies(n.children[i], depth + 1);
    }
}

fn bool Optimizer.apply_copies(Optimizer* o, Node* n, int depth)
{
    if (n == null || depth > OPT_MAX_DEPTH) { return false; }
    bool changed = false;

    if (n.kind == Nk.N_EXPR_IDENT && n.resolved != null)
    {
        Node* target = o.copies.resolve(n.resolved);
        if (target != null && target != n.resolved)
        {
            n.resolved = target;
            if (target.name_id != 0) { n.name_id = target.name_id; }
            o.copies_propagated = o.copies_propagated + 1;
            changed = true;
        }
    }

    for (usz i = 0; i < n.child_count; i++)
    {
        if (o.apply_copies(n.children[i], depth + 1)) { changed = true; }
    }
    return changed;
}

// ── Pass 6: CSE census ──────────────────────────────────────────────────────
fn void Optimizer.cse_scan(Optimizer* o, Node* n, int depth)
{
    if (n == null || depth > OPT_MAX_DEPTH) { return; }

    if (n.kind == Nk.N_BLOCK)
    {
        // A fresh table per block: two blocks are not guaranteed to run in
        // sequence, so a value from one is not available in the other.
        o.vn.init();
    }

    // Only non-trivial pure expressions are worth numbering. A bare
    // identifier or literal is already as cheap as it gets.
    if ((n.kind == Nk.N_EXPR_BINARY || n.kind == Nk.N_EXPR_UNARY
         || n.kind == Nk.N_EXPR_FIELD || n.kind == Nk.N_EXPR_INDEX)
        && is_pure(n, 0))
    {
        Node* rep = o.vn.lookup_or_add(n);
        if (rep != null && rep != n)
        {
            o.cse_found = o.cse_found + 1;
            // Mark it so the SSI builder can reuse the earlier value.
            n.flags = n.flags | pfront_core::NF_USED;
        }
    }

    for (usz i = 0; i < n.child_count; i++)
    {
        o.cse_scan(n.children[i], depth + 1);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// PASS 7 — BLOCK FLATTENING
// ════════════════════════════════════════════════════════════════════════════
// Folding a branch leaves the taken arm's BLOCK nested inside the parent
// block. Semantically fine, but it hides later opportunities: a statement in
// the inner block cannot be seen as "after a return" by the parent's
// unreachable scan, and CSE gives up at the block boundary.
//
// Splicing a nested block into its parent is only sound when the inner block
// declares nothing -- a `let` inside it would otherwise leak into the outer
// scope and change what later names resolve to.
fn bool Optimizer.flatten_blocks(Optimizer* o, Node* b, int depth)
{
    if (b == null || depth > OPT_MAX_DEPTH) { return false; }

    bool changed = false;
    for (usz i = 0; i < b.child_count; i++)
    {
        if (o.flatten_blocks(b.children[i], depth + 1)) { changed = true; }
    }
    if (b.kind != Nk.N_BLOCK) { return changed; }

    // Count what the splice would produce, so the child array is grown once.
    usz needed = 0;
    bool has_splice = false;
    for (usz i = 0; i < b.child_count; i++)
    {
        Node* c = b.children[i];
        if (c != null && c.kind == Nk.N_BLOCK && block_declares_nothing(c))
        {
            needed = needed + c.child_count;
            has_splice = true;
        }
        else { needed = needed + 1; }
    }
    if (!has_splice || needed > b.child_cap) { return changed; }

    // Splice in place, back to front, so earlier indices stay valid.
    usz write = needed;
    usz read = b.child_count;
    while (read > 0)
    {
        read = read - 1;
        Node* c = b.children[read];
        if (c != null && c.kind == Nk.N_BLOCK && block_declares_nothing(c))
        {
            usz k = c.child_count;
            while (k > 0)
            {
                k = k - 1;
                write = write - 1;
                b.children[write] = c.children[k];
                if (c.children[k] != null) { c.children[k].parent = b; }
            }
            o.blocks_flattened = o.blocks_flattened + 1;
            changed = true;
        }
        else
        {
            write = write - 1;
            b.children[write] = c;
        }
    }
    b.child_count = needed;
    return changed;
}

// A block that declares nothing can be spliced into its parent without
// changing name resolution.
fn bool block_declares_nothing(Node* b)
{
    if (b == null) { return false; }
    if (b.child_count == 0) { return true; }
    for (usz i = 0; i < b.child_count; i++)
    {
        Node* c = b.children[i];
        if (c == null) { continue; }
        if (pfront_core::is_decl(c.kind)) { return false; }
    }
    return true;
}

// ════════════════════════════════════════════════════════════════════════════
// PASS 8 — UNREACHABLE FUNCTION-LEVEL CLEANUP
// ════════════════════════════════════════════════════════════════════════════
// After branch folding, a whole `if` arm may have collapsed to nothing. An
// empty block left in a statement position is noise for every later pass and
// for the AST dump, so it is removed.
fn bool Optimizer.drop_empty(Optimizer* o, Node* n, int depth)
{
    if (n == null || depth > OPT_MAX_DEPTH) { return false; }
    bool changed = false;
    for (usz i = 0; i < n.child_count; i++)
    {
        if (o.drop_empty(n.children[i], depth + 1)) { changed = true; }
    }
    if (n.kind != Nk.N_BLOCK || n.child_count == 0) { return changed; }

    usz write = 0;
    for (usz read = 0; read < n.child_count; read++)
    {
        Node* c = n.children[read];
        bool drop = false;
        if (c != null && c.kind == Nk.N_BLOCK && c.child_count == 0)
        {
            drop = true;
        }
        // A bare unit expression in non-tail position does nothing.
        if (c != null && c.kind == Nk.N_EXPR_UNIT && read + 1 < n.child_count)
        {
            drop = true;
        }
        if (drop) { o.empty_dropped = o.empty_dropped + 1; changed = true; continue; }
        n.children[write] = c;
        write = write + 1;
    }
    if (changed) { n.child_count = write; }
    return changed;
}

// ── Driver ──────────────────────────────────────────────────────────────────
fn Node* Optimizer.run(Optimizer* o, Node* root)
{
    if (root == null || o.level <= 0) { return root; }

    o.nodes_before = count_nodes(root, 0);

    for (int round = 0; round < OPT_MAX_ROUNDS; round++)
    {
        bool changed = false;
        o.rounds = o.rounds + 1;

        // Use counts must be recomputed each round: the previous round's
        // deletions change which bindings are still read.
        o.uses.init();
        o.uses.scan(root, 0);

        if (o.fold_expr(root, 0))     { changed = true; }
        if (o.fold_branches(root, 0)) { changed = true; }

        if (o.level >= 2)
        {
            // Recount after folding — a folded branch just deleted uses.
            o.uses.init();
            o.uses.scan(root, 0);
            if (o.dce(root, 0)) { changed = true; }
            // Flattening exposes the NEXT round's unreachable statements: a
            // `return` spliced up from a folded arm terminates the parent.
            if (o.flatten_blocks(root, 0)) { changed = true; }
            if (o.drop_empty(root, 0)) { changed = true; }
        }

        if (o.level >= 3)
        {
            o.copies.init();
            o.collect_copies(root, 0);
            if (o.apply_copies(root, 0)) { changed = true; }
        }

        if (!changed) { break; }
    }

    if (o.level >= 3)
    {
        o.vn.init();
        o.cse_scan(root, 0);
    }

    o.nodes_after = count_nodes(root, 0);
    return root;
}

fn usz Optimizer.total_changes(Optimizer* o)
{
    return o.folded_arith + o.folded_cmp + o.folded_cast + o.folded_logic
         + o.simplified + o.branches_folded + o.dead_unreachable
         + o.dead_useless + o.dead_stores + o.copies_propagated
         + o.loops_removed + o.blocks_flattened + o.empty_dropped;
}

fn void Optimizer.report(Optimizer* o)
{
    printf("=== optimizer (-O%d, %d rounds) ===\n", o.level, (int)o.rounds);
    printf("  const fold       : %d arith, %d compare, %d cast, %d logic\n",
           (int)o.folded_arith, (int)o.folded_cmp,
           (int)o.folded_cast, (int)o.folded_logic);
    printf("  algebraic        : %d identities\n", (int)o.simplified);
    printf("  branches         : %d folded, %d loops removed\n",
           (int)o.branches_folded, (int)o.loops_removed);
    printf("  dead code        : %d unreachable, %d useless, %d dead stores\n",
           (int)o.dead_unreachable, (int)o.dead_useless, (int)o.dead_stores);
    if (o.live_dead_stores > 0)
    {
        printf("  liveness-driven  : %d stores dead by CFG liveness alone\n",
               (int)o.live_dead_stores);
    }
    if (o.blocks_flattened > 0 || o.empty_dropped > 0)
    {
        printf("  cleanup          : %d blocks flattened, %d empties dropped\n",
               (int)o.blocks_flattened, (int)o.empty_dropped);
    }
    if (o.level >= 3)
    {
        printf("  copy prop        : %d rewritten\n", (int)o.copies_propagated);
        printf("  cse              : %d redundant expressions\n", (int)o.cse_found);
    }
    long delta = (long)o.nodes_before - (long)o.nodes_after;
    int pct = o.nodes_before > 0 ? (int)((delta * 100) / (long)o.nodes_before) : 0;
    printf("  nodes            : %d -> %d  (%d removed, %d%%)\n",
           (int)o.nodes_before, (int)o.nodes_after, (int)delta, pct);
}
