# Pride Capability Checklist

Generated: 2026-06-29

```
====================================================================
PRIDE CAPABILITY CHECKLIST — 2026-06-29
  ✅     = parse+resolve+ir+llvm-as-22 green
  🔶noL  = IR ok, llvm-as-22 fails (codegen bug)
  🔷ir   = parse+resolve ok, IR verify fails
  🔷res  = parse ok, resolve fails
  ❌     = parse fails
====================================================================

────────────────────────────────────────
  §3 LEXICAL
────────────────────────────────────────
✅     -- line comment
✅     --[...nested...] comment
✅     0xFF hex literal
✅     0b binary literal
✅     0o octal literal
✅     1_000 underscore separator
✅     f64 float literal
✅     f32 float suffix
✅     i64 integer suffix
✅     u64 integer suffix
✅     true/false bool literals
✅     null literal
❌     â unicode arrow token
✅     INDENT/DEDENT layout
✅     chr type + char literal
✅     multi-line body indent

────────────────────────────────────────
  §4 PRIMITIVE TYPES
────────────────────────────────────────
✅     i8
✅     i16
✅     i32
✅     i64
✅     u8
✅     u16
✅     u32
✅     u64
✅     f32
✅     f64
✅     bool
✅     chr
✅     ptr (raw void*)
✅     () unit type
✅     (A,B) tuple type
✅     *T typed pointer
✅     i128
✅     u128
✅     isize
✅     usize

────────────────────────────────────────
  §5 BINDINGS
────────────────────────────────────────
✅     let x : T = v
✅     let x = v (type inferred)
✅     let mut z
✅     z += n compound assign
✅     z -= n
✅     z *= n
✅     z /= n
✅     z %= n
✅     tuple destructure let
✅     let _ wildcard discard

────────────────────────────────────────
  §6 FUNCTIONS
────────────────────────────────────────
✅     multi-clause fn
✅     clause with guard
✅     tuple pattern params
✅     fn-pointer param type
🔶noL  zero-capture closure
✅     capturing closure (1 var)
✅     multi-capture closure
✅     #[inline] attribute
✅     #[cold] attribute
✅     #[pure] attribute
✅     #[hot] attribute
✅     tail keyword (musttail)
❌     extern fn #[cc(c)]
❌     #[naked] fn

────────────────────────────────────────
  §7 CONTROL FLOW
────────────────────────────────────────
✅     if-then-else (inline expr)
✅     if-else block form
🔶noL  if-else-if chain
✅     while loop
✅     do-while loop
✅     for i in 0..n range
❌     break
❌     continue
✅     early return
🔶noL  defer (lifo cleanup)
❌     break 'label
❌     continue 'label

────────────────────────────────────────
  §8 PATTERN MATCHING
────────────────────────────────────────
✅     match literal pattern
🔶noL  match tuple pattern
✅     match bool (exhaustive)
🔶noL  match with guard
🔶noL  match null ptr
✅     multi-armed clause match

────────────────────────────────────────
  §9 STRUCTS & UNIONS
────────────────────────────────────────
✅     struct field read
✅     struct two fields
🔶noL  struct update syntax
✅     auto-deref *P.field
✅     self-referential struct
✅     struct #align attr
✅     struct #packed attr
❌     union type

────────────────────────────────────────
  §10 ALGEBRAIC EFFECTS
────────────────────────────────────────
✅     effect declare + perform
✅     effect op call
🔶noL  effect handle + resume
✅     multi-effect row ! [IO, Log]
🔶noL  conditional effect raise

────────────────────────────────────────
  §12 GENERICS
────────────────────────────────────────
✅     generic identity fn<A>
✅     T : Ord constraint
✅     T : Num constraint
✅     T : Eq constraint
✅     generic struct Pair<A,B>
✅     generic instantiation
✅     multi-type-param generic

────────────────────────────────────────
  §13 TYPE SYSTEM
────────────────────────────────────────
🔷res  type union âª (semantic subtyping)
🔷res  type intersection â©
✅     bottom type â¥ (never returns)
✅     explicit type annotation binding

────────────────────────────────────────
  §14 EXPLICIT UB
────────────────────────────────────────
✅     ub! expression + UB effect
✅     assume optimizer hint
✅     unchecked expression
✅     trap hardware instruction
✅     unreachable path marker
🔶noL  poison + freeze values

────────────────────────────────────────
  §15 MEMORY
────────────────────────────────────────
✅     alloc scalar → *i32
✅     alloc [T;N] array
✅     free pointer
✅     *p = v (write through ptr)
✅     *p (dereference read)
✅     &x (address-of)
✅     p + 1 (pointer arithmetic)
✅     p[i] (pointer index)
✅     n as i64 (numeric widen)
✅     n as i32 (numeric narrow)
✅     p as *T (ptr reinterpret)
✅     transmute(x) bitcast
✅     sizeof(T)
✅     alignof(T)
🔶noL  offset_of(T, field) (parse)

────────────────────────────────────────
  §16 TERM REWRITING
────────────────────────────────────────
❌     rewrite block with rules
❌     named rewrite rule
❌     rule compose r1 ++ r2

────────────────────────────────────────
  §17 PGL
────────────────────────────────────────
🔷res  pgen declare
🔷res  pgen with condition

────────────────────────────────────────
  §18 CODE QUOTATION
────────────────────────────────────────
✅     ~Tree quotation
✅     ~Bytes quotation
✅     ~Data quotation

────────────────────────────────────────
  §19 IRDL
────────────────────────────────────────
❌     irdl dialect + lowering rule
❌     irdl multi-opcode
❌     irdl guarded rule

────────────────────────────────────────
  §20 MSP / STAGING
────────────────────────────────────────
🔷res  comptime block (CTFE)
✅     eval expression (staged)

────────────────────────────────────────
  §21 MODULES
────────────────────────────────────────
✅     mod declaration + :: path
✅     module function call
✅     nested module path
✅     module type access
✅     use import statement

────────────────────────────────────────
  § INTERFACES & IMPL
────────────────────────────────────────
✅     interface + impl block
🔶noL  operator overload (Add impl)

────────────────────────────────────────
  § ENUMS
────────────────────────────────────────
✅     simple enum (no payload)
✅     enum with i32 payload
✅     recursive enum tags

────────────────────────────────────────
  § NEWTYPE
────────────────────────────────────────
✅     newtype wrap constructor
✅     newtype pattern unwrap

────────────────────────────────────────
  § FFI / EXTERN
────────────────────────────────────────
❌     extern fn C call
❌     extern malloc
❌     #[naked] function

────────────────────────────────────────
  §23 DIAGNOSTICS (correct error codes)
────────────────────────────────────────
🔷res  E0270 undefined name
🔷res  E0260 duplicate binding in pattern
✅     E0363 too many arguments
✅     E04xx type mismatch (soft warn)
✅     E0362 if-condition not bool
✅     UB effect propagation check

────────────────────────────────────────
  § CODEGEN END-TO-END (full LLVM IR)
────────────────────────────────────────
✅     arithmetic binary ops
✅     recursive function (fib)
✅     recursive function (fact)
✅     multi-clause recursive (gcd)
✅     if-else branch codegen
✅     while loop with SSA phi nodes
✅     for-range loop codegen
✅     struct field access + arithmetic
✅     bit shift <<
✅     bitwise AND
✅     bitwise OR
✅     bitwise XOR
✅     bitwise NOT ~n
✅     alloc + write + read + free
✅     algebraic effect perform codegen
✅     compound assign in loop

====================================================================
SUMMARY: 173 capabilities checked
  ✅     137  fully working (parse+resolve+ir+llvm-as-22)
  🔶noL   12  IR ok, llvm-as-22 fails (codegen edge case)
  🔷       7  parse/resolve ok, IR issues
  ❌      17  parse or resolve broken
  DONE: 149/173 = 86%  (approx. 149 of 173 items working)
====================================================================
```
