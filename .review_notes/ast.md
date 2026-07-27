# ast.c3 review

## BUG (major, design-level): PrecTable is entirely write-only — user-defined operator precedence has zero effect
`ast.c3` defines a full `PrecTable` (open-addressed hash table, `PrecEntry`
struct with prec/assoc/is_user_defined) explicitly so that "user-defined
operators (NODE_DECL_OPERATOR) can register entries at parse time and
participate in expression parsing with custom precedence" (comment at ~line
649). `PrecTable.register_user_op()` IS called, from `node_decl_operator()`
(ast.c3:973) whenever the parser builds an `operator (...)` declaration node
(parser.c3 parse_operator_decl). BUT `PrecTable.find()` — the only read path
into the table — is **never called anywhere in the entire codebase** (grep
across all *.c3 confirms zero call sites outside its own definition). The
actual expression parser (`Parser.parse_assign`/`parse_compose`/`parse_range`/
.../`parse_add`/`parse_mul`/...) is a fully hardcoded, fixed-precedence
recursive-descent chain (parser.c3 ~2699-2960) that does not consult PrecTable
at all — each precedence tier is its own function checking a fixed, literal
list of TokenTypes.
Consequence: declaring `operator (+) : (T,T)->T #prec(3) #assoc(right) | ... `
parses fine and produces a NODE_DECL_OPERATOR node with `is_user_defined=true`
correctly stored in the table — but this has **zero effect on how `+` (or any
other operator) is subsequently parsed**: `+` is still always additive,
left-assoc, fixed precedence, hardcoded in `parse_add`. The #prec/#assoc
attributes on an `operator` declaration are pure decoration; the precedence
table update is dead data nobody reads.
This means "operator overloading with custom precedence" is not a partially
working feature but a **completely non-functional one at the parser level**
(separately from the codegen-side issue already noted in finds.md #6 about
IR_UNKNOWN dispatch for operator-overload calls — that note assumes the
operator is even parsed with correct precedence, which it structurally cannot
be). Also: nothing stops `operator (+)` from being declared twice with
different #prec, since insert() has no duplicate check (just appends, up to
PREC_TABLE_MAX=256, then silently drops further inserts) — table is populated
but again nothing ever distinguishes/uses those distinctions.

## Minor: same silent-drop-on-overflow pattern in PrecTable.insert
`PrecTable.insert` (line ~711): `if (t.count >= PREC_TABLE_MAX) return;` silently
discards the entry past 256 without any diagnostic — consistent with the
broader pattern already noted (lexer diag cap, ssi_ir pending_inner_fns cap).
Low real-world impact here specifically since it's moot anyway (find() is
dead code), but indicative of the pattern.

## Potential host-UB in fold_binary (compile-time constant folding)
`fold_binary()` (ast.c3 ~1345-1408) performs constant folding of integer
literal binary expressions using native C3 (host-language) arithmetic. Two
classes of undefined/implementation-defined behavior in the HOST compiler
itself (not just the target program) are not guarded against:

1. **Shift amount not masked/range-checked**: `x << y` and `x >> y` (and the
   arithmetic-shift `sx >> y` for signed) are computed directly with the
   RHS literal value `y` as the shift count, with no check that `y < 64`
   (or < bit-width). A Pride program containing `1 << 100` as a literal
   constant expression would fold at compile time using `y = 100`, which is
   undefined behavior in C (and likely in C3, which targets similar
   semantics) for shifting a 64-bit value by ≥64. This could crash the
   compiler itself, produce a compiler-host-platform-dependent folded
   result, or (best case) just silently compute garbage — silently baking
   a platform-dependent wrong constant into the compiled program, which is
   worse than a runtime bug since it can't be caught by testing on other
   platforms.
2. **Signed overflow in division/negation**: `sx / sy` and `sx % sy`
   (ast.c3 ~1362-1370) guard against `y == 0` but NOT against the classic
   `INT64_MIN / -1` overflow case (mathematically 2^63, which does not fit
   in i64) — this is undefined behavior for signed division in C-family
   languages. A Pride literal expression like `(-9223372036854775808) / (-1)`
   as a folded compile-time constant would invoke this UB in the host
   compiler's own arithmetic.
3. Multiplication/addition/subtraction (`x + y`, `x - y`, `x * y`) are done
   on the `ulong` (unsigned) views, so these specific ops are well-defined
   (wraparound is spec'd for unsigned) — fine. But the **signed comparison
   folding** (`sx < sy` etc.) and the two issues above operate on `long`
   (signed) — worth double-checking C3's own overflow semantics, but per
   the C-like traditions this project otherwise follows (see wrapping/
   checked/saturating operator design elsewhere), it's likely these were
   simply not considered for the *constant-folding* path specifically,
   since the runtime codegen path for shift/div likely has its own
   (separate) UB handling policy (worth cross-checking against codegen.c3's
   div/shift codegen, which might correctly guard these at RUNTIME while
   the CONSTANT-FOLD path at compile time does not).
Recommendation: add bounds checks (`y < 64` for shifts; `!(sx==INT64_MIN &&
sy==-1)` for division/modulo) before folding, and fall back to NOT folding
(return null, let codegen emit the runtime op, which may have its own UB
policy) rather than executing the operation in host arithmetic.

## FnData metadata (arity/clause_count/is_recursive/is_tail_recursive/is_extern/is_variadic) is write-only
`ast.c3`'s `FnData` payload struct is populated exactly once, by
`Parser.parse_fn()` (parser.c3 ~1010) via `ast::node_fn_set_meta(...)`, always
passing `is_recursive=false, is_tail_recursive=false` with the comment
"recursion detected later" — but no later pass (resolve.c3, typecheck.c3,
effectcheck.c3, ssi.c3, ssi_ir.c3, mono.c3, codegen.c3) ever reads
`.fn_data.*` or calls any setter to update `is_recursive`/`is_tail_recursive`
(confirmed: `grep -rn "fn_data\." *.c3` outside ast.c3 returns zero hits).
So:
  - `arity` and `clause_count` are computed correctly at parse time but never
    consumed downstream either (same grep, zero hits) — every pass that needs
    a function's arity/clause count recomputes it by walking children
    directly instead (e.g. typecheck.c3 has its own arity-checking logic
    elsewhere). Redundant but harmless.
  - `is_recursive`/`is_tail_recursive` are hardcoded `false` FOREVER — dead
    fields that are never true and never read. The `TOKEN_KW_TAIL` keyword
    /"tail call guarantee" feature mentioned in the lexer's token doc comment
    (`TOKEN_KW_TAIL, // tail — tail call guarantee`) and `NODE_EXPR_TAILCALL`
    AST node exist, but tail-recursion *detection* (as opposed to the
    explicit `tail` keyword forcing a tailcall) appears to be entirely
    vestigial — the struct field and its doc comment ("all recursive calls
    are in tail position") describe a feature that was never implemented,
    matching the checklist's own admission elsewhere that some features are
    parse-only. This one isn't even mentioned in CAPABILITIES_CHECKLIST.md or
    finds.md, so it's an undocumented gap.
