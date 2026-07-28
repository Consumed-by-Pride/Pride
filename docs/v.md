# Pryde Programming Language
## Language Reference — v0.3 (Implementation-Grounded)

> **"The over-engineered C."**
> Fast. Dense. Principled. A systems language with formal semantics and zero apologies.
>
> *"You can still shoot yourself in the foot. You will now do so with mathematical precision."*

This document reflects the **actual current implementation**: a complete,
crash-hardened frontend written in **C3** —
`lexer.c3 → parser.c3 → ast.c3 → resolve.c3 → typecheck.c3 → effectcheck.c3 → lint.c3`.
Everything described here is either already working or directly derived from the
implemented token set, AST node kinds, and analysis passes.

> ⚠️ **C3 is the implementation language, not a compilation target.** Pryde is
> *written in* C3 the way CPython is written in C. Pryde does **not** compile to
> C3. C3 is a build-time tool; it never appears in Pryde's output.

---

## Table of Contents

1. Philosophy
2. Compilation Pipeline
3. Lexical Structure
4. Primitive Types
5. Bindings
6. Functions
7. Control Flow
8. Pattern Matching
9. Structs and Unions
10. Algebraic Effects
11. Tensors
12. Generics and Where Clauses
13. The Type System
14. Explicit Undefined Behavior
15. Memory
16. Term Rewriting
17. Pattern Generation Language (PGL)
18. Code Quotation (~Tree, ~Data, ~Bytes)
19. IRDL — IR Dialect Language
20. Metaprogramming (MSP)
21. Modules
22. The AST
23. Diagnostics and Soft Typing
24. Operator Precedence
25. Keyword Reference

---

## 1. Philosophy

Pryde is a **mid-level, AOT-compiled systems language**. It occupies the same
territory as C++ — direct hardware access, manual memory, zero-cost abstractions
— but with a formal foundation and a metaprogramming model that treats the
compiler's IR as a first-class, user-programmable object.

**Core tenets:**

- **No hidden behavior.** Undefined behavior is declared with `ub!`, typed as
  `⊥`, and tracked via the `UB` effect. The compiler never invents UB silently,
  and a function that can trigger UB must say so in its effect row.
- **Dense and mathematical.** Unicode operators (`→ ↦ ∩ ∪ ¬ ⊥ ∀ ∃ ∈ ∅`) are
  first-class tokens. Indentation replaces braces. Less noise per idea.
- **Mid-level and explicit.** Pointers, sizes, alignment, calling conventions,
  inline assembly — all visible. No implicit numeric promotion: you write the
  size you mean.
- **Formally grounded.** Semantic subtyping (types are *sets of values*),
  row-polymorphic effect types, and flow-sensitive refinements give real
  semantics, not convention.
- **Soft by default, strict on demand.** Type and lint problems are *warnings*;
  the compiler inserts the obvious thing and keeps going. `--strict` promotes
  every warning to a hard error for production builds. Pryde trusts you.
- **Metaprogramming at the IR level.** Term rewriting, PGL, and IRDL operate on
  the compile-time AST directly. Not textual macros. Not C++ templates. Real
  tree transformations, run by the MSP stage. The MSP stage is **untyped and
  unrestricted** by design — it can do anything, with precision.
- **Effect-driven standard library.** Nothing owns resources implicitly.
  Allocation, I/O, and error handling are provided by handlers at the call site.
  You control everything.

**Influences:**

| Language | What Pryde Takes                                   |
|----------|----------------------------------------------------|
| C++      | Memory model, mid-level abstraction, struct layout |
| Swift    | `fn`, `let`, generic constraint syntax, attributes |
| Prolog   | Clause-based function definitions, `\|` patterns    |
| Koka     | Row-polymorphic effect types `! [...]`             |
| CDuce    | Semantic subtyping `∩`, `∪`, `¬`                    |
| Haskell  | First-class rewrite rules, combinator composition  |
| MetaOCaml| Staged metaprogramming (brackets / escape / run)   |
| MLIR     | IRDL dialect infrastructure                        |
| NumPy    | Shaped tensors and the `@` contraction operator    |

---

## 2. Compilation Pipeline

```
Pryde source (.pry)
    ↓
Lexer          — tokenizes to a flat Token[] stream (layout-aware)
    ↓
Parser         — recursive descent, produces an AST
    ↓
Resolver       — links every name to its declaration (two namespaces)
    ↓
Type Checker   — semantic subtyping, generics, tensor shapes (soft warnings)
    ↓
Effect Checker — verifies declared effect rows match actual effects
    ↓
Lint           — exhaustiveness, unreachable code, unused bindings
    ↓
MSP Stage      — term rewriting, PGL, IRDL lowering, comptime (untyped)
    ↓
ClangIR / LLVM IR
    ↓
Native machine code
```

The AST is a compile-time-only structure. It is **arena-allocated** (64 MB
default slab) and discarded as a single free after codegen — no GC, no reference
counting, no per-node frees. The frontend is crash-hardened: a recursion-depth
guard rejects pathologically nested input rather than overflowing the stack, and
the whole pipeline is fuzz- and AddressSanitizer-clean.

---

## 3. Lexical Structure

### 3.1 Comments

```pryde
-- single line comment

--[
  nested block comment
  --[ can go arbitrarily deep ]--
  no limit on nesting
]--
```

Pryde uses `--` for line comments and `--[ ... ]--` for nestable block comments.
(The compiler is written in C3, which uses `//` and `/* */` — do not confuse the
two. Pryde source always uses `--`.)

### 3.2 Identifiers

```
identifier ::= [a-zA-Z_][a-zA-Z0-9_]*
```

**Type variables** start with an uppercase letter (`T`, `Elem`, `Key`, `Vec3`).
A lone `_` is the wildcard token — not an identifier. A name prefixed with `_`
(e.g. `_unused`) suppresses the "unused binding" lint. Unicode identifiers are
allowed (high bytes pass through the lexer).

### 3.3 Layout

Pryde is **indentation-sensitive**. INDENT / DEDENT / NEWLINE are real tokens.
Inside `()`, `[]`, or `{}` they are suppressed — multi-line expressions flow
freely. Tabs in indentation are a hard lex error. Spaces only.

```pryde
fn foo : i32 → i32
  | 0 → 1
  | n →
      let x = n * 2
      x + 1
```

### 3.4 Literals

```pryde
-- integers (suffix selects type, default i64)
42          42u64       42i8
0xFF        0b1010_1100  0o755
1_000_000   0xDEAD_BEEFu32

-- floats (suffix selects type, default f64)
3.14        3.14f32     1.0e10      1.5e-3f32

-- booleans
true   false

-- character (u32 codepoint)
'A'    '\n'    '\xFF'    '\u{1F600}'

-- strings (UTF-8)
"hello, world"    "escape: \n \t \u{03B1}"

-- raw byte strings (*u8, no escape processing)
b"raw bytes"

-- null pointer
null
```

Constant integer/boolean expressions are **folded at parse time**
(`6 * 7` becomes the literal `42`). Division/modulo by a literal zero is *not*
folded — it is reported as declared-UB territory instead.

### 3.5 Unicode Operators

First-class tokens, matched by raw UTF-8 byte sequence:

| Symbol | Token            | Use                            |
|--------|------------------|--------------------------------|
| `→`    | TOKEN_ARROW      | function type / clause arrow   |
| `↦`    | TOKEN_MAPSTO     | rewrite rule arrow             |
| `∩`    | TOKEN_INTERSECT  | type intersection              |
| `∪`    | TOKEN_UNION_SYM  | type union                     |
| `¬`    | TOKEN_NEGATION   | type negation                  |
| `⊥`    | TOKEN_BOTTOM     | bottom type                    |
| `≥`    | TOKEN_GEQ_UNI    | greater-or-equal               |
| `≤`    | TOKEN_LEQ_UNI    | less-or-equal                  |
| `≠`    | TOKEN_NEQ_UNI    | not-equal                      |
| `∀`    | TOKEN_FORALL     | universal quantifier in types  |
| `∃`    | TOKEN_EXISTS     | existential quantifier         |
| `∈`    | TOKEN_ELEMENT    | element-of / set membership    |
| `∅`    | TOKEN_EMPTYSET   | empty set / empty effect row   |
| `σ`    | TOKEN_SIGMA      | SSI sigma node (internal)      |
| `φ`    | TOKEN_PHI        | SSI phi node (internal)        |

ASCII fallbacks are provided where useful: `->` for `→`, `!=` for `≠`, etc.

---

## 4. Primitive Types

```pryde
-- signed integers
i8   i16   i32   i64

-- unsigned integers
u8   u16   u32   u64

-- IEEE 754 floats
f32   f64

-- other
bool        -- true / false
char        -- u32 codepoint
ptr         -- raw untyped pointer (void*)
Str         -- UTF-8 string
*T          -- typed pointer to T (auto-deref through . access)
[T; N]      -- fixed-size array
[T]         -- slice
(A, B, ...) -- tuple
()          -- unit type
⊥           -- bottom type (never returns — type of ub!, unreachable, trap)
```

No platform-dependent `int` or `long`. **No implicit numeric promotions** — an
`i32` and an `i64` do not mix silently. An *untyped* integer literal, however,
adapts to its context: `let x : i32 = 0` and `n + 2` (with `n : i32`) are fine.

---

## 5. Bindings

```pryde
-- immutable (default)
let x : i32 = 42
let y = 42                    -- type inferred from the initializer

-- mutable
let mut z : i32 = 0
z = z + 1                     -- ok: z is mutable
z += 1                        -- compound assignment: += -= *= /= %= &= |= ^= <<= >>=

-- tuple destructuring
let (a, b) = (1, 2)

-- struct destructuring
let { x, y } = point

-- ignore
let (_, important) = pair
let _ = side_effect()

-- with explicit effect in the type
let line : Str ! [IO] = IO.read_line()
```

Assigning to an immutable `let` (or to a function parameter, which is never
mutable) is a soft warning. Duplicate binders in one pattern (`(a, a)`) are
flagged.

---

## 6. Functions

### 6.1 Clause Syntax

Functions use **Prolog-style clause matching**. Each `|` is one clause, matched
top-to-bottom. Guards follow the pattern after a comma.

```pryde
fn name : InputType → OutputType ! [Effects]
  | pattern_1              → body_1
  | pattern_2, guard_expr  → body_2
  | _                      → default_body
```

The compiler checks each clause body against the declared return type, binds
parameter types from the signature, and warns when the clause set is
non-exhaustive (no catch-all).

### 6.2 Examples

```pryde
-- recursive factorial
fn fact : i64 → i64
  | 0 → 1
  | n → n * fact(n - 1)

-- multi-argument tuple
fn gcd : (i64, i64) → i64
  | (a, 0) → a
  | (a, b) → gcd(b, a % b)

-- guard condition
fn classify : i32 → Str
  | 0        → "zero"
  | n, n > 0 → "positive"
  | _        → "negative"

-- effect in the signature, explicit UB
fn divide : (i32, i32) → i32 ! [UB]
  | (_, 0) → ub! "division by zero"
  | (a, b) → a / b

-- multi-line body with control flow + memory
fn find_max : (*i32, u64) → i32 ! [UB]
  | (_, 0)     → ub! "empty array"
  | (arr, len) →
      let mut top = arr[0]
      for i in 1..len
        if arr[i] > top
          top = arr[i]
      top
```

Inline `if c then a else b` is supported (`then` is a contextual soft keyword).

### 6.3 Attributes

```pryde
fn hot : i32 → i32
  #inline #vectorize
  | n → n * 2

fn exported : (i32, i32) → i32
  #export("pryde_add") #cc(c)
  | (a, b) → a + b

-- ABI / FFI declarations
fn sin    : f64 → f64  #extern("sin")    #cc(c)
fn malloc : u64 → ptr  #extern("malloc") #cc(c)
```

Recognised attributes: `extern`, `export`, `inline`, `noinline`, `packed`,
`align`, `volatile`, `atomic`, `unsafe`, `pure`. Any other `#name(args)` is kept
as a generic attribute.

### 6.4 Inline Assembly

```pryde
fn rdtsc : () → u64
  | () →
      asm
        "rdtsc"
        "shl rdx, 32"
        "or  rax, rdx"
        : out rax

fn clflush : *u8 → ()
  | p → asm "clflush (%{p})" : in (p)
```

Inline asm always carries the `Unsafe` effect.

---

## 7. Control Flow

```pryde
-- if / else if / else (an expression — returns the taken branch's value)
if condition
  body
else if other
  body
else
  body

-- inline if-expression
let m = if a > b then a else b

-- while
while condition
  body

-- do-while
do
  body
while condition

-- for range (exclusive / inclusive)
for i in 0..n
  body
for i in 0..=n
  body

-- early exit
return expr
break
continue
```

An `if` used as a value has the **union** of its branch types. `unreachable`
marks a path the optimizer should treat as dead. `trap` emits a hardware trap.
Both are typed `⊥`. Code after a diverging statement (`return`, `unreachable`,
`trap`, `ub!`) is flagged as unreachable.

---

## 8. Pattern Matching

```pryde
match expr
  | pattern         → body
  | pattern, guard  → body
  | _               → default

-- literal patterns
match n
  | 0        → "zero"
  | n, n < 0 → "negative"
  | _        → "positive"

-- tuple patterns
match pair
  | (0, 0) → "origin"
  | (a, 0) → a
  | (0, b) → b
  | (a, b) → a + b

-- struct patterns
match point
  | { x: 0, y: 0 } → "origin"
  | { x: 0, y }    → "on y-axis"
  | { x, y }       → "general"

-- null check
match ptr
  | null → ub! "null dereference"
  | p    → *p

-- OR patterns
match c
  | 'a' | 'e' | 'i' | 'o' | 'u' → "vowel"
  | _                           → "consonant"

-- exhaustive bool match needs no catch-all
match b
  | true  → 1
  | false → 0
```

Non-exhaustive matches emit a **soft warning** — not a hard error. The compiler
recognises a catch-all (`_` or a bare binder) and full bool coverage as total.
An arm after a catch-all is flagged unreachable.

---

## 9. Structs and Unions

```pryde
-- struct definition
type Vec3f = struct
  x : f32
  y : f32
  z : f32

-- with attributes
type CacheLine = struct #align(64)
  data : [u8; 64]

type PackedHdr = struct #packed
  magic   : u32
  version : u8
  flags   : u8
  length  : u16

-- self-referential
type Node = struct
  val  : i32
  next : *Node

-- construction (all fields validated: unknown / missing / mistyped fields warn)
let v = Vec3f { x: 1.0, y: 2.0, z: 3.0 }

-- update syntax (new value, original unchanged)
let v2 = v { x: 99.0 }

-- field access (auto-deref through pointers, no ->)
let p : *Vec3f = alloc Vec3f
p.x = 1.0
let chained = node.next.next.val

-- union
type FloatBits = union
  f : f32
  i : u32       -- same bytes, different interpretation
```

Field access checks the field exists on the (auto-derefed) struct and yields its
type. Indexing requires a pointer, array, slice, or tensor.

---

## 10. Algebraic Effects

Effects are the unified answer to exceptions, I/O, state, allocation, and any
computational side effect. They are **resumable** via the continuation `k`,
**composable** by nesting handlers, and **tracked** in function types.

### 10.1 Defining Effects

```pryde
effect IO
  read_byte  : ()  → u8
  write_byte : u8  → ()
  flush      : ()  → ()

effect State<S>
  get : ()  → S
  put : S   → ()

effect Err<E>
  raise : E → ⊥        -- ⊥: never returns
```

### 10.2 Using and Declaring Effects

```pryde
fn write_str : Str → () ! [IO]
  | s →
      for i in 0..s.len
        IO.write_byte(s[i])
      IO.flush()
```

The **effect checker** verifies that every effect a function performs appears in
its `! [...]` row. Calling an effectful function propagates its effects to the
caller; a `handle` block discharges the effects it handles. An open row `..r`
admits any further effects. Missing declarations are soft warnings.

### 10.3 Handling Effects

```pryde
-- k is the continuation; calling k(v) resumes the computation with value v
handle computation
  | IO.write_byte byte k → (sys_write(byte); k ())
  | IO.read_byte  ()   k → k sys_read()
  | IO.flush      ()   k → (sys_flush(); k ())

-- state backed by a mutable local
let mut s : i32 = 0
handle computation
  | State.get () k → k s
  | State.put v  k → (s = v; k ())
```

Continuations resume by *juxtaposition application*: `k v` calls `k` with `v`.

### 10.4 Effect Polymorphism

```pryde
-- forwards any effects f has
fn apply_twice<A> : (A → A ! [..r], A) → A ! [..r]
  | (f, x) → f(f(x))
```

### 10.5 Built-in Effect Flags

The AST tracks effects as a bitmask on every node:

| Flag           | Meaning                                          |
|----------------|--------------------------------------------------|
| `EFFECT_PURE`  | 0 — no effects                                   |
| `EFFECT_IO`    | bit 0 — performs I/O                             |
| `EFFECT_ALLOC` | bit 1 — allocates or frees memory                |
| `EFFECT_UNSAFE`| bit 2 — unsafe operation or inline asm           |
| `EFFECT_UB`    | bit 3 — may trigger declared undefined behaviour |
| `EFFECT_PANIC` | bit 4 — may panic                                |

Builtin effects propagate upward automatically: a parent node's mask is the
union of its children's. `IO`/`Alloc`/etc. in a row, and user-declared effects,
are checked by name against the function body.

---

## 11. Tensors

Pryde has **shape-checked tensors** as a first-class numeric type — the slight
edge for numerical and ML-adjacent code.

```pryde
-- type:  Tensor<ElementType ; Dim0, Dim1, ...>
let v : Tensor<f32; 3>    = [| 1.0, 2.0, 3.0 |]
let m : Tensor<f32; 2, 2> = [| [| 1.0, 2.0 |], [| 3.0, 4.0 |] |]

-- the @ operator is matrix / tensor contraction (binds tighter than *)
let mm = m @ m                 -- (2×2) @ (2×2) → (2×2)
let mv = m @ v                 -- (2×2) @ (2)   → (2)   (when shapes agree)
```

Tensor literals use `[| ... |]`; nesting encodes rank. The type checker:

- infers a literal's shape from its nesting and flags **ragged** (non-rectangular)
  literals,
- checks a literal against a declared `Tensor<...>` (rank, element type, and any
  **constant** dimensions),
- checks `@` contraction shapes: matrix×matrix, matrix×vector, vector×matrix,
  and vector·vector (dot product), reporting inner-dimension mismatches.

Constant dimensions are checked exactly; symbolic dimensions (e.g. a generic
`N`) are treated as wildcards for now.

---

## 12. Generics and Where Clauses

```pryde
-- single / multiple type parameters
fn identity<A> : A → A
  | x → x

fn apply<A, B> : (A → B, A) → B
  | (f, x) → f(x)

-- with a constraint (enforced: the inferred type must satisfy it)
fn max<T : Ord> : (T, T) → T
  | (a, b) → if a > b then a else b

-- generic struct
type Pair<A, B> = struct
  fst : A
  snd : B

-- where clause (the binding is applied when checking the body)
fn zip<A, B, C> : (*A, *B, u64) → *C
  where C = Pair<A, B>
  | (xs, ys, n) →
      let out : *C = alloc [C; n]
      for i in 0..n
        out[i] = Pair { fst: xs[i], snd: ys[i] }
      out
```

At a call site the type checker **infers** the type arguments by unifying the
declared parameter types against the actual argument types, then **substitutes**
them into the return type — so `identity(5) : i64` and `identity(true) : bool`.
Generic constraints (`T : Ord`) and `where C = T` equalities are enforced.

---

## 13. The Type System

### 13.1 Semantic Subtyping

Types are **sets of values**. The algebra is a lattice:

```pryde
A ∩ B    -- intersection: values that satisfy both A and B
A ∪ B    -- union: values that satisfy A or B
¬A       -- negation: all values NOT in A
⊥        -- bottom: the empty set (no values; ⊥ <: everything)
```

```pryde
type NonNull<T>   = T ∩ ¬null
type Positive     = i32 ∩ (> 0)
type NormalizedF  = f32 ∩ (>= 0.0) ∩ (<= 1.0)
type IntOrStr     = i32 ∪ Str
```

Subtyping decides set inclusion: `i32 <: i32 ∪ i64`, `⊥ <: A`, `A <: A ∪ B`,
function types are contravariant in the argument and covariant in the result,
pointers are invariant, tuples are componentwise. Negation is decided via a real
disjointness relation: `i32 <: ¬bool` holds (they share no values), `bool <:
¬bool` does not.

### 13.2 Effect Rows

```pryde
A → B               -- pure function
A → B ! [IO]        -- function with IO effect
A → B ! [IO, UB]    -- multiple effects
A → B ! [..r]       -- open effect row (polymorphic)
A → B ! [IO, ..r]   -- IO plus whatever else
```

### 13.3 Flow-Sensitive Refinement (SSI)

At every `if`, `match`, and `while`, the parser inserts σ-nodes (type splits)
and φ-nodes (type merges). After a branch the compiler can know more about a
value:

```pryde
fn safe_sqrt : f64 → f64 ! [UB]
  | x →
      if x < 0.0
        ub! "negative sqrt"
      -- here: x : f64 ∩ (≥ 0.0)
      sqrt(x)
```

### 13.4 Quantifiers

```pryde
∀ A . A → A           -- the identity type
∃ T . T ∩ Eq<T>       -- some type that implements Eq
```

---

## 14. Explicit Undefined Behavior

UB is never silent. Every UB path is:

- Declared with `ub! "message"` — a single keyword token,
- Typed as `⊥` (bottom — never returns),
- Tracked with `EFFECT_UB` — visible in the function's effect row.

```pryde
fn divide : (i32, i32) → i32 ! [UB]
  | (_, 0) → ub! "division by zero"
  | (a, b) → a / b

assume n > 0          -- optimizer hint; wrong assumption is your problem
unchecked p[i]        -- strips bounds/overflow checking from a sub-expression
poison                -- a value that propagates UB if used
freeze n              -- stops UB propagation from a poison value
trap                  -- emit a hardware trap instruction
unreachable           -- mark a path dead for the optimizer
```

Division or modulo by a **literal** zero is reported as declared-UB territory
(guard it or use `ub!`). Non-literal divisors are your responsibility.

---

## 15. Memory

Manual memory. No GC. No RC. No RAII unless you build it via effects.

```pryde
let p   : *i32  = alloc i32          -- EFFECT_ALLOC
let arr : *f32  = alloc [f32; 256]

*p = 42                              -- write through pointer
let v = *p                           -- dereference (requires a pointer)
let a = &x                           -- address-of

p + 1          -- pointer arithmetic (advances by element size)
p[n]           -- *(p + n)

free p                               -- EFFECT_ALLOC

p as *u8       -- reinterpret (raw bits)
x as i64       -- numeric widening/narrowing
let bits : u32 = transmute(3.14f32)  -- bitcast, no conversion
```

`alloc`/`free` carry the `Alloc` effect; a function that uses them must declare
`! [Alloc]`.

---

## 16. Term Rewriting

Rewrite rules are **first-class values**. They compose with `++` and apply with
`|>`. They fire at compile time over the AST, in the MSP stage. Zero runtime
cost.

```pryde
let arith : Rewrite = rewrite
  | x + 0    ↦ x
  | x * 1    ↦ x
  | x * 2    ↦ x << 1

let strength : Rewrite = rewrite
  | x * n, is_power_of_2(n) ↦ x << log2(n)

-- a single named rule
rule fold_zero = x + 0 ↦ x

-- compose rule sets
let full : Rewrite = arith ++ strength

-- apply once / to a fixpoint
expr |> arith
expr |> arith*
```

> Rewriting is part of the **MSP stage**, which is intentionally **untyped and
> unrestricted** — rules may inspect, compose, and transform any part of the AST.

---

## 17. Pattern Generation Language (PGL)

PGL generates pattern matchers **programmatically** at compile time — decision
trees for instruction selection, optimization passes, and analysis.

```pryde
pgen name<TypeConstraints> →
  [bindings : Types] where [conditions] ↦ action
```

```pryde
pgen elim_add_zero<T : Numeric> →
  [x : T] where [_ + 0 | 0 + _] ↦ x

pgen mul_to_shift<T : Int> →
  [x : T, n : T] where [x * n, is_power_of_2(n)] ↦ x << log2(n)

pgen select_add_i32 →
  [a : i32, b : i32] where [a + b] ↦ emit_asm("addl %{b:reg}, %{a:reg}")
```

---

## 18. Code Quotation (~Tree, ~Data, ~Bytes)

Three sigils quote an expression as a different representation of the same AST.
They are distinct first-class tokens and each produces its own node kind.

```pryde
~Tree  expr    -- expr as an AST node tree (inspect, rewrite, transform)
~Data  expr    -- expr as raw Any-typed data (addressable, serializable)
~Bytes expr    -- expr as a raw byte sequence (u8 slice)
```

```pryde
let node = ~Tree (x + y * z)        -- an AST node; pattern-match, apply rules
let code = ~Bytes my_function        -- the function's compiled bytes
let raw  = ~Data  my_vec3f           -- a struct as raw data

comptime
  let folded = ~Tree (1 + 2 + 3) |> arith*   -- at compile time: the integer 6
```

---

## 19. IRDL — IR Dialect Language

IRDL defines **custom IR dialects** for the backend: new opcodes, regions,
edges, and hyperedges that the MSP stage and code generator can recognise and
lower.

```pryde
-- declare a dialect with named opcodes
dialect MyDialect
  opcode add_i32
  opcode mul_f32
  region entry
  region exit

-- irdl block: lowering rules from dialect ops to a target
irdl
  MyDialect.add_i32 [a : i32, b : i32] ↦ emit_asm("addl %{b:reg}, %{a:reg}")
```

IRDL keywords: `irdl dialect opcode region block node edge hyperedge graph`.

---

## 20. Metaprogramming (MSP)

The MSP (Meta-Staging / Program) stage runs the metaprogramming constructs over
the AST at compile time. It is modelled on **MetaOCaml's** staging: brackets
(quote), escape (splice/unquote), and run (eval).

```pryde
comptime
  let table = build_table(256)       -- evaluated entirely at compile time

stage
  let specialized = splice(generate_code(my_type))

expr |> rules*                       -- apply rules to a fixpoint
```

MSP keywords: `rewrite pgen stage quote splice unquote reify eval comptime
runtime pattern rule fixpoint meta generate lower`.

> **The MSP stage is untyped and unrestricted by design.** Unlike the rest of
> the frontend, it does not enforce types or effects — it can run arbitrary
> compile-time transformations. This is deliberate: the metaprogramming layer is
> where you reach in and reshape the program. The type and effect checkers
> *skip* MSP bodies entirely.

---

## 21. Modules

```pryde
-- declare a module (nested modules allowed)
mod math
  fn sin  : f64 → f64 #extern("sin")  #cc(c)
  fn sqrt : f64 → f64 #extern("sqrt") #cc(c)

-- import
use std::mem
use std::io
use math::sin
use math as m

-- qualified access
let s = math::sin(1.0)
let n = m::cos(1.0)
```

The resolver gives each module its own scope, hoists declarations (so mutual
recursion and forward references work), and tracks two namespaces (values and
types) so a name can be both a type and a value.

---

## 22. The AST

Pryde's compiler builds a **plain, standard Abstract Syntax Tree** — every node
has exactly one parent: a conventional, debuggable tree.

### 22.1 Node

Every `AstNode` carries:

```
kind            : NodeKind         -- one of ~155 kinds
id              : u32              -- monotonically increasing
line, col       : source location
type_annotation : *AstNode         -- synthesized/declared type (filled by typecheck)
effects         : u64 bitmask      -- EFFECT_* (union of children)
flags           : u32 bitmask      -- mut / folded / range-inclusive / typed / used / ...
resolved        : *AstNode         -- the declaration a name use refers to (filled by resolve)
child_count     : u16
children        : **AstNode        -- arena-allocated
payload union   : literals, operator token, identifier span
```

### 22.2 Arena

The AST lives in a single contiguous bump-allocated slab (64 MB default). All
nodes are bump-allocated; the whole tree is released in one `free` after
codegen. No GC, no per-node frees.

### 22.3 Parse-Time Constant Folding

The parser folds obvious constants immediately:
- `LitInt op LitInt` → folded `LitInt` (or `LitBool` for comparisons),
- `LitBool and/or LitBool` → folded `LitBool`,
- division/modulo by zero → not folded (reported instead).

### 22.4 Node Kind Families

Literals · Names (Ident / TypeVar / Wildcard) · Types (primitive, ptr, ref,
array, slice, tuple, fn, union, intersect, negation, bottom, forall, exists,
generic-app, refinement, **tensor**) · Declarations (let, mut, fn, type, struct,
union, effect, mod, use, const, static) · Statements (return, break, continue,
defer, asm, assume, assert, invariant, unreachable, trap) · Expressions (if,
match, while, for, do-while, block, assign, binary, unary, call, method-call,
field, index, cast, tuple-lit, array-lit, struct-lit, **tensor-lit**, alloc,
free, range, pipeline, sizeof, alignof, transmute, unchecked, **matmul**, unit)
· Patterns · Effects (handle, with, perform, op-decl) · Attributes · Safety/UB
· Metaprogramming · Code quotation sigils · IRDL · SSI (sigma / phi).

---

## 23. Diagnostics and Soft Typing

Pryde's analysis passes are **advisory by default**. A type mismatch, an
undeclared effect, a non-exhaustive match, an unused binding — each is a
**warning**, and the compiler continues. This is the "trust the programmer"
half of the philosophy.

```
pryde <file.pry>            -- soft mode: warnings, never blocks
pryde --strict <file.pry>   -- every warning becomes a hard error (exit 2)
```

The passes and what they catch:

| Pass          | Catches (soft warnings unless `--strict`)                       |
|---------------|------------------------------------------------------------------|
| Resolver      | undefined names, duplicate definitions, duplicate pattern binders |
| Type checker  | type mismatches, bad field/index/deref, call arity, generic constraints, tensor shapes, operator domains, mutability |
| Effect checker| effects performed but not declared in the `! [...]` row          |
| Lint          | non-exhaustive match/clauses, unreachable code, unused bindings   |

The frontend is hardened: a recursion-depth guard prevents stack overflow on
pathological nesting, and the whole pipeline is clean under thousands of random
and mutation fuzz inputs, including AddressSanitizer.

---

## 24. Operator Precedence (High → Low)

```
1.   Postfix:    f()  arr[i]  obj.field  obj.method()  expr?
2.   Prefix:     *p  &x  not x  ¬  ~Tree ~Data ~Bytes  $  `  ~
3.   Cast:       expr as Type
4.   MatMul:     @
5.   Mul:        *  /  %
6.   Add:        +  -
7.   Shift:      <<  >>
8.   Bitwise &:  &
9.   Bitwise ^:  ^
10.  Bitwise |:  |
11.  Compare:    <  >  <=  >=  ==  !=  ≤  ≥  ≠  ∈
12.  Logical &&: and  &&
13.  Logical ||: or   ||
14.  Pipeline:   |>            (with trailing * for fixpoint)
15.  Range:      ..   ..=
16.  Compose:    ++            (rewrite-rule composition)
17.  Assign:     =  +=  -=  *=  /=  %=  &=  |=  ^=  <<=  >>=
-- in type position only:
     Arrow →   ·   Type ops ∩ ∪ ¬   ·   Effect row ! [...]   ·   Rewrite ↦
```

Application by juxtaposition (`k v`, `f x`) is used for continuation resumption
and curried calls in clause/handler bodies.

---

## 25. Keyword Reference

**79 reserved keywords**, by category:

**Core (24):**
`fn  let  mut  type  struct  union  effect  handle  match  if  else  while  for
do  in  as  and  or  not  return  continue  break  use  mod`

**Low-level / ABI (14):**
`extern  export  inline  noinline  packed  align  volatile  atomic  static
const  unsafe  pure  sizeof  alignof`

**Memory (3):**
`alloc  free  transmute`

**Control (4):**
`defer  asm  where  with`

**Safety / UB (9):**
`ub!  assume  assert  invariant  unreachable  trap  poison  freeze  unchecked`

**Metaprogramming (16):**
`rewrite  pgen  stage  quote  splice  unquote  reify  eval  comptime  runtime
pattern  rule  fixpoint  meta  generate  lower`

**IRDL / Graph IR (9):**
`irdl  dialect  opcode  region  block  node  edge  hyperedge  graph`

**Sigils (3, dedicated tokens, not keywords):**
`~Tree  ~Data  ~Bytes`

Contextual soft keyword: `then` (in inline `if … then … else`).

---

*Pryde Language Reference v0.3 — derived from lexer.c3, ast.c3, parser.c3,*
*resolve.c3, typecheck.c3, effectcheck.c3, lint.c3.*
*"You can still shoot yourself in the foot. You will now do so with mathematical precision."*
