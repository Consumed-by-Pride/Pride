// ============================================================================
// theory_stage.c3 — staged partial evaluation (part 21)
// ----------------------------------------------------------------------------
// Multi-stage programming is only useful if stage-0 code actually RUNS at
// compile time. `theory_msp` proves a program is well-staged; this module
// executes the stage-0 fragment and leaves residual code for later stages.
//
// The classic formulation is BINDING-TIME ANALYSIS followed by SPECIALISATION:
//
//   1. Every expression is classified STATIC (computable now) or DYNAMIC
//      (must wait for runtime). The rule is simple and must be conservative:
//      an expression is static only when all its inputs are static and its
//      operation is total.
//   2. Static subexpressions are EVALUATED; dynamic ones are RESIDUALISED,
//      that is, emitted as code with their static parts already folded.
//
// Worked example. Given
//
//     fn power : (i64, i64) -> i64
//       | (n, x) -> if n == 0 then 1 else x * power(n - 1, x)
//
// with `n` static and `x` dynamic, specialising at `n = 3` unrolls to
// `x * (x * (x * 1))` — no loop, no recursion, no comparison at runtime.
//
// The interpreter is deliberately SMALL and TOTAL:
//   * a value domain of integers, floats, bools, strings, unit and tuples
//   * fuel on every reduction, so a divergent stage-0 program is a diagnostic
//     rather than a hung compiler
//   * an environment with lexical scoping and proper shadowing
//   * no heap, no pointers, no I/O — anything it cannot model stays dynamic
//
// Refusing to evaluate is always safe; evaluating something it should not is
// not. Every uncertain case therefore falls back to DYNAMIC.
// ============================================================================

module theory_stage;

import pfront_lex;
import pfront_core;
import theory_term;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz PE_MAX_ENV      = 4096;
const usz PE_MAX_TUPLE    = 16;
const usz PE_MAX_FRAMES   = 256;
const int PE_FUEL         = 200000;
const int PE_MAX_DEPTH    = 256;
const int PE_MAX_UNROLL   = 64;

// ── Binding time ────────────────────────────────────────────────────────────
enum BindingTime : int
{
    BT_STATIC,     // fully known now
    BT_DYNAMIC,    // must wait for runtime
    BT_UNKNOWN     // not yet classified
}

fn char* bt_name(BindingTime b)
{
    switch (b)
    {
        case BT_STATIC:  return "static";
        case BT_DYNAMIC: return "dynamic";
        case BT_UNKNOWN: return "unknown";
    }
}

// ── Value domain ────────────────────────────────────────────────────────────
enum ValKind : int
{
    V_UNIT,
    V_INT,
    V_FLOAT,
    V_BOOL,
    V_CHAR,
    V_STRING,
    V_TUPLE,
    V_CODE,        // a residual fragment: dynamic, but structurally known
    /*
     A QUOTED AST, `~Tree e` / `~Data e` / `~Bytes e`, or an MSP operator
     over one. Structurally this is a code fragment like V_CODE, but it is
     STATIC: the tree exists at compile time and is exactly what the
     programmer asked `comptime` to produce.

     V_CODE means "could not be computed"; V_QUOTED means "computed, and
     the answer is a tree". Collapsing the two made every `comptime`
     containing a quotation or a rewrite fail as non-computable — spec §18
     and §16's central examples.
    */
    V_QUOTED,
    V_ERROR
}

struct Value
{
    ValKind kind;
    long    ival;
    double  fval;
    char*   sptr;
    usz     slen;
    int[PE_MAX_TUPLE] elems;   // indices into the value pool
    usz     elem_count;
    Node*   code;              // V_CODE payload
}

fn Value v_unit()  { Value v; v.kind = ValKind.V_UNIT; v.ival = 0; v.fval = 0.0; v.sptr = null; v.slen = 0; v.elem_count = 0; v.code = null; return v; }
fn Value v_int(long x)   { Value v = v_unit(); v.kind = ValKind.V_INT; v.ival = x; return v; }
fn Value v_bool(bool b)  { Value v = v_unit(); v.kind = ValKind.V_BOOL; v.ival = b ? 1 : 0; return v; }
fn Value v_float(double f) { Value v = v_unit(); v.kind = ValKind.V_FLOAT; v.fval = f; return v; }
fn Value v_code(Node* n) { Value v = v_unit(); v.kind = ValKind.V_CODE; v.code = n; return v; }
fn Value v_error() { Value v = v_unit(); v.kind = ValKind.V_ERROR; return v; }

fn bool v_is_static(Value* v)
{
    return v.kind != ValKind.V_CODE && v.kind != ValKind.V_ERROR;
}

/*
 A quoted tree: static, and its value is the node itself.

 Distinct from v_code, which signals "this could not be reduced". See the
 V_QUOTED comment on ValKind for why conflating them broke `comptime`.
*/
fn Value v_quoted(Node* n)
{
    Value v = v_unit();
    v.kind = ValKind.V_QUOTED;
    v.code = n;
    return v;
}

// ── Environment ─────────────────────────────────────────────────────────────
struct Binding
{
    uint        name_id;
    Value       value;
    BindingTime bt;
    int         frame;
}

struct Env
{
    Binding[PE_MAX_ENV] bindings;
    usz                 count;
    usz[PE_MAX_FRAMES]  frame_base;
    usz                 frame_count;
}

fn void Env.init(Env* e)
{
    e.count = 0;
    e.frame_count = 0;
    e.push_frame();
}

fn void Env.push_frame(Env* e)
{
    if (e.frame_count >= PE_MAX_FRAMES) { return; }
    e.frame_base[e.frame_count] = e.count;
    e.frame_count = e.frame_count + 1;
}

fn void Env.pop_frame(Env* e)
{
    if (e.frame_count == 0) { return; }
    e.frame_count = e.frame_count - 1;
    e.count = e.frame_base[e.frame_count];
}

fn bool Env.bind(Env* e, uint name, Value v, BindingTime bt)
{
    if (e.count >= PE_MAX_ENV || name == 0) { return false; }
    Binding* b = &e.bindings[e.count];
    b.name_id = name;
    b.value = v;
    b.bt = bt;
    b.frame = (int)e.frame_count - 1;
    e.count = e.count + 1;
    return true;
}

// Innermost binding wins, which is what gives correct shadowing.
fn Binding* Env.lookup(Env* e, uint name)
{
    usz i = e.count;
    while (i > 0)
    {
        i = i - 1;
        if (e.bindings[i].name_id == name) { return &e.bindings[i]; }
    }
    return null;
}

// ── Partial evaluator ───────────────────────────────────────────────────────
struct PartialEvaluator
{
    Env                    env;
    Arena*                 arena;
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;

    int  fuel;
    int  fuel_start;
    usz  evaluated;
    usz  residualised;
    usz  folded;
    usz  unrolled;
    usz  fuel_exhausted;
    usz  static_exprs;
    usz  dynamic_exprs;
    int  unroll_depth;
    int  call_depth;
    bool enabled;
}

fn void PartialEvaluator.init(PartialEvaluator* pe, Arena* a,
                              pfront_core::DiagBag* d,
                              pfront_core::Interner* it, char* file)
{
    pe.env.init();
    pe.arena = a;
    pe.diags = d;
    pe.interner = it;
    pe.file = file;
    pe.fuel = PE_FUEL;
    pe.fuel_start = PE_FUEL;
    pe.evaluated = 0;
    pe.residualised = 0;
    pe.folded = 0;
    pe.unrolled = 0;
    pe.fuel_exhausted = 0;
    pe.static_exprs = 0;
    pe.dynamic_exprs = 0;
    pe.unroll_depth = 0;
    pe.call_depth = 0;
    pe.enabled = true;
}

// ── Binding-time analysis ───────────────────────────────────────────────────
// Conservative by construction: anything not provably static is dynamic.
fn BindingTime PartialEvaluator.binding_time(PartialEvaluator* pe, Node* e, int depth)
{
    if (e == null || depth > PE_MAX_DEPTH) { return BindingTime.BT_DYNAMIC; }

    switch (e.kind)
    {
        case N_EXPR_INT:
        case N_EXPR_FLOAT:
        case N_EXPR_BOOL:
        case N_EXPR_CHAR:
        case N_EXPR_STRING:
        case N_EXPR_UNIT:
            return BindingTime.BT_STATIC;

        case N_EXPR_IDENT:
        {
            Binding* b = pe.env.lookup(e.name_id);
            if (b != null) { return b.bt; }
            // A `const` declaration is static by definition.
            if (e.resolved != null && e.resolved.kind == Nk.N_DECL_CONST)
            {
                return BindingTime.BT_STATIC;
            }
            return BindingTime.BT_DYNAMIC;
        }

        case N_EXPR_BINARY:
        {
            BindingTime l = pe.binding_time(e.child(0), depth + 1);
            BindingTime r = pe.binding_time(e.child(1), depth + 1);
            // Static only when BOTH operands are: one dynamic input
            // contaminates the result.
            if (l == BindingTime.BT_STATIC && r == BindingTime.BT_STATIC)
            {
                return BindingTime.BT_STATIC;
            }
            return BindingTime.BT_DYNAMIC;
        }

        case N_EXPR_UNARY:
        case N_EXPR_CAST:
            return pe.binding_time(e.child(0), depth + 1);

        case N_EXPR_IF:
        {
            // The whole conditional is static only if the condition is; a
            // dynamic condition means both branches survive.
            if (pe.binding_time(e.child(0), depth + 1) != BindingTime.BT_STATIC)
            {
                return BindingTime.BT_DYNAMIC;
            }
            BindingTime t = pe.binding_time(e.child(1), depth + 1);
            if (e.child_count < 3) { return t; }
            BindingTime f = pe.binding_time(e.child(2), depth + 1);
            if (t == BindingTime.BT_STATIC && f == BindingTime.BT_STATIC)
            {
                return BindingTime.BT_STATIC;
            }
            return BindingTime.BT_DYNAMIC;
        }

        case N_EXPR_TUPLE:
        {
            for (usz i = 0; i < e.child_count; i++)
            {
                if (pe.binding_time(e.children[i], depth + 1) != BindingTime.BT_STATIC)
                {
                    return BindingTime.BT_DYNAMIC;
                }
            }
            return BindingTime.BT_STATIC;
        }

        case N_EXPR_COMPTIME:
            // An explicit `comptime` is a demand that this be static.
            return BindingTime.BT_STATIC;

        default:
            // Calls, memory, effects, I/O: all dynamic. Refusing to evaluate is
            // always sound; the reverse is not.
            return BindingTime.BT_DYNAMIC;
    }
}

// ── Evaluation ──────────────────────────────────────────────────────────────
fn Value PartialEvaluator.eval(PartialEvaluator* pe, Node* e, int depth)
{
    if (e == null || depth > PE_MAX_DEPTH) { return v_error(); }
    if (pe.fuel <= 0)
    {
        pe.fuel_exhausted = pe.fuel_exhausted + 1;
        return v_error();
    }
    pe.fuel = pe.fuel - 1;
    pe.evaluated = pe.evaluated + 1;

    switch (e.kind)
    {
        case N_EXPR_INT:   return v_int((long)e.p.ival);
        case N_EXPR_BOOL:  return v_bool(e.p.ival != 0);
        case N_EXPR_CHAR:  return v_int((long)e.p.ival);
        case N_EXPR_FLOAT: return v_float(e.p.fval);
        case N_EXPR_UNIT:  return v_unit();
        case N_EXPR_STRING:
        {
            Value v = v_unit();
            v.kind = ValKind.V_STRING;
            v.sptr = e.p.sptr;
            v.slen = e.p.slen;
            return v;
        }

        case N_EXPR_IDENT:
        {
            Binding* b = pe.env.lookup(e.name_id);
            if (b != null && b.bt == BindingTime.BT_STATIC) { return b.value; }
            if (e.resolved != null && e.resolved.kind == Nk.N_DECL_CONST)
            {
                for (usz i = 0; i < e.resolved.child_count; i++)
                {
                    Node* init = e.resolved.children[i];
                    if (init != null && pfront_core::is_expr(init.kind))
                    {
                        return pe.eval(init, depth + 1);
                    }
                }
            }
            return v_code(e);
        }

        case N_EXPR_UNARY:
        {
            Value a = pe.eval(e.child(0), depth + 1);
            if (!v_is_static(&a)) { return v_code(e); }
            Tk op = (Tk)e.p.op;
            if (op == Tk.TOKEN_MINUS)
            {
                if (a.kind == ValKind.V_FLOAT) { return v_float(-a.fval); }
                return v_int(-a.ival);
            }
            if (op == Tk.TOKEN_BANG || op == Tk.TOKEN_KW_NOT) { return v_bool(a.ival == 0); }
            if (op == Tk.TOKEN_TILDE) { return v_int((long)(~(ulong)a.ival)); }
            return v_code(e);
        }

        case N_EXPR_QUOTE:
        {
            /*
             A QUOTATION IS ALREADY A COMPILE-TIME VALUE.

             `~Tree e` reifies the AST of `e`; it does not evaluate `e`, so
             it is static regardless of what `e` mentions. The evaluator
             had no case for it and fell through to "dynamic", which made
             the spec's §18 example

                 comptime
                   let folded = ~Tree (1 + 2 + 3) |> arith*

             fail with "not computable at compile time" — the one place
             quotation is *supposed* to be used.

             Residualised as a quoted tree: static, value is the node.
            */
            return v_quoted(e);
        }

        case N_EXPR_REIFY:
        case N_EXPR_EVAL:
            // Same reasoning: MSP operators over a representation are
            // compile-time constructs, not runtime dependencies.
            return v_quoted(e);

        case N_EXPR_BINARY:
        {
            Tk bop = (Tk)e.p.op;
            /*
             `expr |> rules` and `expr |> rules*` are REWRITING, which by
             definition happens at compile time (spec §16: "They fire at
             compile time over the AST, in the MSP stage. Zero runtime
             cost."). Treating the pipeline as an ordinary binary operator
             asked the evaluator to compute a rule set as a value, which it
             cannot, so every rewrite inside a `comptime` was rejected.
            */
            if (bop == Tk.TOKEN_PIPELINE) { return v_quoted(e); }

            Value l = pe.eval(e.child(0), depth + 1);
            if (!v_is_static(&l)) { return v_code(e); }
            Tk op = (Tk)e.p.op;

            // Short-circuit operators must not evaluate the right side when
            // the left already decides the answer. Doing so would be wrong if
            // the right side is dynamic or diverges.
            if (op == Tk.TOKEN_AMPAMP || op == Tk.TOKEN_KW_AND)
            {
                if (l.ival == 0) { return v_bool(false); }
            }
            if (op == Tk.TOKEN_PIPEPIPE || op == Tk.TOKEN_KW_OR)
            {
                if (l.ival != 0) { return v_bool(true); }
            }

            Value r = pe.eval(e.child(1), depth + 1);
            if (!v_is_static(&r)) { return v_code(e); }
            return pe.apply_binop(op, l, r, e);
        }

        case N_EXPR_IF:
        {
            Value c = pe.eval(e.child(0), depth + 1);
            if (!v_is_static(&c)) { return v_code(e); }
            // The condition is known: only the taken branch is evaluated, and
            // the other disappears entirely.
            pe.folded = pe.folded + 1;
            if (c.ival != 0) { return pe.eval(e.child(1), depth + 1); }
            if (e.child_count >= 3) { return pe.eval(e.child(2), depth + 1); }
            return v_unit();
        }

        case N_EXPR_CAST:
            return pe.eval(e.child(0), depth + 1);

        case N_EXPR_COMPTIME:
        {
            Value last = v_unit();
            for (usz i = 0; i < e.child_count; i++)
            {
                last = pe.eval(e.children[i], depth + 1);
            }
            return last;
        }

        case N_BLOCK:
        {
            pe.env.push_frame();
            Value last = v_unit();
            for (usz i = 0; i < e.child_count; i++)
            {
                Node* s = e.children[i];
                if (s == null) { continue; }
                if (s.kind == Nk.N_DECL_LET)
                {
                    Value init = v_unit();
                    bool have = false;
                    for (usz k = 1; k < s.child_count; k++)
                    {
                        Node* c = s.children[k];
                        if (c == null || pfront_core::is_pattern(c.kind)) { continue; }
                        init = pe.eval(c, depth + 1);
                        have = true;
                    }
                    Node* pat = s.child(0);
                    if (pat != null && pat.kind == Nk.N_PAT_IDENT)
                    {
                        BindingTime bt = have && v_is_static(&init)
                                       ? BindingTime.BT_STATIC : BindingTime.BT_DYNAMIC;
                        pe.env.bind(pat.name_id, init, bt);
                    }
                    continue;
                }
                last = pe.eval(s, depth + 1);
            }
            pe.env.pop_frame();
            return last;
        }

        case N_EXPR_TUPLE:
        {
            // Tuples are static when every element is.
            for (usz i = 0; i < e.child_count; i++)
            {
                Value el = pe.eval(e.children[i], depth + 1);
                if (!v_is_static(&el)) { return v_code(e); }
            }
            Value v = v_unit();
            v.kind = ValKind.V_TUPLE;
            v.elem_count = e.child_count;
            return v;
        }

        default:
            return v_code(e);
    }
}

fn Value PartialEvaluator.apply_binop(PartialEvaluator* pe, Tk op,
                                      Value l, Value r, Node* site)
{
    // Float arithmetic when either side is a float.
    if (l.kind == ValKind.V_FLOAT || r.kind == ValKind.V_FLOAT)
    {
        double a = l.kind == ValKind.V_FLOAT ? l.fval : (double)l.ival;
        double b = r.kind == ValKind.V_FLOAT ? r.fval : (double)r.ival;
        switch (op)
        {
            case TOKEN_PLUS:  return v_float(a + b);
            case TOKEN_MINUS: return v_float(a - b);
            case TOKEN_STAR:  return v_float(a * b);
            case TOKEN_SLASH:
            {
                // Division by zero at compile time is a diagnostic, not an
                // infinity silently baked into the program.
                if (b == 0.0) { return v_code(site); }
                return v_float(a / b);
            }
            case TOKEN_LT:    return v_bool(a < b);
            case TOKEN_GT:    return v_bool(a > b);
            case TOKEN_LTEQ:  return v_bool(a <= b);
            case TOKEN_GTEQ:  return v_bool(a >= b);
            case TOKEN_EQEQ:  return v_bool(a == b);
            case TOKEN_NEQ:   return v_bool(a != b);
            default:          return v_code(site);
        }
    }

    long a = l.ival;
    long b = r.ival;
    switch (op)
    {
        case TOKEN_PLUS:
        {
            if (add_ovf(a, b)) { return v_code(site); }
            return v_int(a + b);
        }
        case TOKEN_MINUS:
        {
            if (add_ovf(a, -b)) { return v_code(site); }
            return v_int(a - b);
        }
        case TOKEN_STAR:
        {
            if (mul_ovf(a, b)) { return v_code(site); }
            return v_int(a * b);
        }
        case TOKEN_SLASH:
        {
            if (b == 0) { return v_code(site); }
            if (a == -9223372036854775807L - 1 && b == -1) { return v_code(site); }
            return v_int(a / b);
        }
        case TOKEN_PERCENT:
        {
            if (b == 0) { return v_code(site); }
            return v_int(a % b);
        }
        case TOKEN_LSHIFT:
        {
            if (b < 0 || b > 63) { return v_code(site); }
            return v_int((long)((ulong)a << (ulong)b));
        }
        case TOKEN_RSHIFT:
        {
            if (b < 0 || b > 63) { return v_code(site); }
            return v_int(a >> b);
        }
        case TOKEN_AMP:      return v_int((long)((ulong)a & (ulong)b));
        case TOKEN_PIPE:     return v_int((long)((ulong)a | (ulong)b));
        case TOKEN_XOR:      return v_int((long)((ulong)a ^ (ulong)b));
        case TOKEN_EQEQ:     return v_bool(a == b);
        case TOKEN_NEQ:      return v_bool(a != b);
        case TOKEN_LT:       return v_bool(a < b);
        case TOKEN_LTEQ:     return v_bool(a <= b);
        case TOKEN_GT:       return v_bool(a > b);
        case TOKEN_GTEQ:     return v_bool(a >= b);
        case TOKEN_AMPAMP:
        case TOKEN_KW_AND:   return v_bool(a != 0 && b != 0);
        case TOKEN_PIPEPIPE:
        case TOKEN_KW_OR:    return v_bool(a != 0 || b != 0);
        default:             return v_code(site);
    }
}

fn bool add_ovf(long a, long b)
{
    if (b > 0 && a > 9223372036854775807L - b) { return true; }
    if (b < 0 && a < -9223372036854775807L - 1 - b) { return true; }
    return false;
}

fn bool mul_ovf(long a, long b)
{
    if (a == 0 || b == 0) { return false; }
    long r = a * b;
    return r / b != a;
}

// ── Residualisation ─────────────────────────────────────────────────────────
// Turn a value back into an AST node so it can replace the original term.
fn Node* PartialEvaluator.residualise(PartialEvaluator* pe, Value* v, Node* origin)
{
    if (origin == null) { return null; }
    switch (v.kind)
    {
        case V_INT:
        {
            Node* n = pe.arena.node(Nk.N_EXPR_INT, origin.line, origin.col);
            if (n == null) { return origin; }
            n.p.ival = (ulong)v.ival;
            n.p.width = origin.p.width;
            n.p.is_signed = origin.p.is_signed;
            n.flags = pfront_core::NF_SYNTHETIC;
            n.type_ann = origin.type_ann;
            n.owner = origin.owner;
            pe.residualised = pe.residualised + 1;
            return n;
        }
        case V_BOOL:
        {
            Node* n = pe.arena.node(Nk.N_EXPR_BOOL, origin.line, origin.col);
            if (n == null) { return origin; }
            n.p.ival = v.ival != 0 ? 1 : 0;
            n.flags = pfront_core::NF_SYNTHETIC;
            n.owner = origin.owner;
            pe.residualised = pe.residualised + 1;
            return n;
        }
        case V_FLOAT:
        {
            Node* n = pe.arena.node(Nk.N_EXPR_FLOAT, origin.line, origin.col);
            if (n == null) { return origin; }
            n.p.fval = v.fval;
            n.p.width = origin.p.width;
            n.flags = pfront_core::NF_SYNTHETIC;
            n.owner = origin.owner;
            pe.residualised = pe.residualised + 1;
            return n;
        }
        case V_UNIT:
        {
            Node* n = pe.arena.node(Nk.N_EXPR_UNIT, origin.line, origin.col);
            if (n == null) { return origin; }
            n.flags = pfront_core::NF_SYNTHETIC;
            n.owner = origin.owner;
            return n;
        }
        case V_CODE:
            return v.code == null ? origin : v.code;
        default:
            return origin;
    }
}

// Specialise a whole tree: evaluate what is static, keep what is dynamic.
fn Node* PartialEvaluator.specialise(PartialEvaluator* pe, Node* e, int depth)
{
    if (!pe.enabled || e == null || depth > PE_MAX_DEPTH) { return e; }

    BindingTime bt = pe.binding_time(e, 0);
    if (bt == BindingTime.BT_STATIC)
    {
        pe.static_exprs = pe.static_exprs + 1;
        // Only fold expressions; a static STATEMENT still has to run.
        if (pfront_core::is_expr(e.kind) && e.kind != Nk.N_BLOCK)
        {
            Value v = pe.eval(e, 0);
            if (v_is_static(&v)) { return pe.residualise(&v, e); }
        }
    }
    else
    {
        pe.dynamic_exprs = pe.dynamic_exprs + 1;
    }

    // Dynamic: recurse so static SUBterms are still folded.
    for (usz i = 0; i < e.child_count; i++)
    {
        Node* before = e.children[i];
        Node* after = pe.specialise(before, depth + 1);
        if (after != null && after != before) { e.set_child(i, after); }
    }
    return e;
}

// ── Loop unrolling ──────────────────────────────────────────────────────────
// A `while` whose bound is static can be unrolled. Bounded by PE_MAX_UNROLL:
// unrolling a million-iteration loop would be technically correct and
// practically catastrophic for compile time and code size.
fn Node* PartialEvaluator.try_unroll(PartialEvaluator* pe, Node* loop, int depth)
{
    if (loop == null || loop.kind != Nk.N_EXPR_WHILE) { return loop; }
    Node* cond = loop.child(0);
    if (cond == null) { return loop; }
    if (pe.binding_time(cond, 0) != BindingTime.BT_STATIC) { return loop; }

    Node* body = loop.child(1);
    if (body == null) { return loop; }

    Node* unrolled = pe.arena.node(Nk.N_BLOCK, loop.line, loop.col);
    if (unrolled == null) { return loop; }
    unrolled.flags = pfront_core::NF_SYNTHETIC;

    int iterations = 0;
    while (iterations < PE_MAX_UNROLL)
    {
        Value c = pe.eval(cond, 0);
        if (!v_is_static(&c)) { return loop; }   // became dynamic: give up
        if (c.ival == 0) { break; }
        Node* copy = theory_term::clone_term(pe.arena, body, 0);
        pe.arena.add_child(unrolled, copy);
        pe.eval(body, 0);                        // advance the static state
        iterations = iterations + 1;
        if (pe.fuel <= 0) { return loop; }
    }
    if (iterations == 0) { return unrolled; }    // loop never ran
    if (iterations >= PE_MAX_UNROLL) { return loop; }
    pe.unrolled = pe.unrolled + 1;
    return unrolled;
}

fn void PartialEvaluator.report(PartialEvaluator* pe)
{
    printf("  partial eval     : %d exprs (%d static, %d dynamic)\n",
           (int)pe.evaluated, (int)pe.static_exprs, (int)pe.dynamic_exprs);
    printf("  specialisation   : %d folded, %d residualised, %d loops unrolled\n",
           (int)pe.folded, (int)pe.residualised, (int)pe.unrolled);
    printf("  pe fuel          : %d / %d used\n",
           pe.fuel_start - pe.fuel, pe.fuel_start);
    if (pe.fuel_exhausted > 0)
    {
        printf("  WARNING          : stage-0 evaluation ran out of fuel %d times\n",
               (int)pe.fuel_exhausted);
    }
}

// ── Comptime driver ─────────────────────────────────────────────────────────
// Finds every `comptime` block and forces it to a value. A comptime block that
// cannot be evaluated is an ERROR: the programmer explicitly demanded
// compile-time evaluation, so silently deferring it would break that promise.
struct ComptimeRunner
{
    PartialEvaluator* pe;
    pfront_core::DiagBag* diags;
    char* file;
    usz blocks;
    usz succeeded;
    usz failed;
}

fn void ComptimeRunner.init(ComptimeRunner* cr, PartialEvaluator* pe,
                            pfront_core::DiagBag* d, char* file)
{
    cr.pe = pe;
    cr.diags = d;
    cr.file = file;
    cr.blocks = 0;
    cr.succeeded = 0;
    cr.failed = 0;
}

fn Node* ComptimeRunner.run(ComptimeRunner* cr, Node* n, int depth)
{
    if (n == null || depth > PE_MAX_DEPTH) { return n; }

    if (n.kind == Nk.N_EXPR_COMPTIME)
    {
        cr.blocks = cr.blocks + 1;
        // Evaluate at the CURRENT environment depth rather than resetting it:
        // a `comptime` inside a block may legitimately reference static
        // bindings introduced earlier in that block. Resetting the frame made
        // `let x = comptime ...` fail while the same expression at top level
        // succeeded, which is an inconsistency the user would rightly call a
        // bug rather than a limitation.
        int saved_fuel = cr.pe.fuel;
        if (saved_fuel <= 0) { cr.pe.fuel = 1024; }
        Value v = cr.pe.eval(n, 0);
        if (v_is_static(&v))
        {
            cr.succeeded = cr.succeeded + 1;
            return cr.pe.residualise(&v, n);
        }
        cr.failed = cr.failed + 1;
        cr.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3280, n.line, n.col,
                            "`comptime` expression is not computable at compile time",
                            "it depends on a runtime value, a call, or memory",
                            cr.file);
        return n;
    }

    if (n.kind == Nk.N_EXPR_WHILE)
    {
        Node* u = cr.pe.try_unroll(n, depth);
        if (u != n) { return u; }
    }

    for (usz i = 0; i < n.child_count; i++)
    {
        Node* before = n.children[i];
        Node* after = cr.run(before, depth + 1);
        if (after != null && after != before) { n.set_child(i, after); }
    }
    return n;
}

fn void ComptimeRunner.report(ComptimeRunner* cr)
{
    if (cr.blocks == 0) { return; }
    printf("  comptime         : %d blocks (%d evaluated, %d failed)\n",
           (int)cr.blocks, (int)cr.succeeded, (int)cr.failed);
}
