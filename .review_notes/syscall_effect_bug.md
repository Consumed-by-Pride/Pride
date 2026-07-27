# effectcheck.c3 / parser.c3 — `syscall(...)` is treated as a PURE (effect-free) operation — undermines the core "no hidden behavior" guarantee

## Confirmed via static analysis + dynamic reproduction
`Parser`'s handling of `syscall(num, args...)` (parser.c3 ~3677-3690, building
`NODE_EXPR_SYSCALL`) is the ONLY literal/expression constructor in the entire
parser that does NOT call `ast::node_add_effect(...)` to tag itself with a
relevant `EFFECT_*` bit. Contrast with every other effectful primitive in the
same file:
  - `NODE_STMT_ASM` → tagged `EFFECT_UNSAFE` (parser.c3 ~1577)
  - `NODE_EXPR_FREE` → tagged `EFFECT_ALLOC` (parser.c3 ~3075)
  - `alloc` (parse_alloc) → tagged `EFFECT_ALLOC` (parser.c3 ~3181)
  - `ub!` → tagged `EFFECT_UB` (parser.c3 ~4054)
  - `handle` → tagged `EFFECT_IO` (parser.c3 ~4450)
  - `unsafe { }` block → tagged `EFFECT_UNSAFE` (parser.c3 ~4707)
  - `NODE_EXPR_SYSCALL` → **no `node_add_effect` call at all.**

Since `AstNode.effects` starts at `EFFECT_PURE` (0) in `node_raw()` and is
only ever OR-propagated upward from children (`node_attach`/`add_child`), a
`syscall(...)` call's effects bitmask is exactly the union of its ARGUMENTS'
effects — if the arguments are plain literals (the overwhelmingly common
case: `syscall(1, 1, buf as i64, len + 1)`, `syscall(231, 0)` as seen in the
project's own `examples/fib.pie` and `tests/exec/*.pie`), the syscall
expression itself carries **zero** effect bits.

This is independently confirmed in `effectcheck.c3`: `EffectChecker.gather_body`
(the pass that computes a function's ACTUAL performed effects to check
against its DECLARED `! [...]` row) has explicit cases for `NODE_EXPR_ALLOC`/
`NODE_EXPR_FREE` (→ EFFECT_ALLOC), `NODE_STMT_ASM` (→ EFFECT_UNSAFE),
`NODE_UB_BANG`/`NODE_EXPR_POISON` (→ EFFECT_UB), `NODE_STMT_ASSERT`/
`NODE_STMT_INVARIANT` (→ EFFECT_PANIC) — but **no case for
`NODE_EXPR_SYSCALL`** (confirmed via grep: zero mentions of
`NODE_EXPR_SYSCALL` in effectcheck.c3). It therefore falls into the generic
`default: self.gather_children(n, acc);` branch, which only recurses into
children (the syscall number and argument expressions) without contributing
any effect bit for the syscall operation itself.

## Empirical confirmation
```
fn bad_io : () -> ()          <-- NO effect row declared at all!
  | () -> syscall(1, 1, 0, 0) <-- raw write(2) syscall — should require ! [IO] (or Unsafe)

fn main : () -> () ! [IO, Alloc]
  | () ->
      bad_io()
      syscall(231, 0)
```
Compiling this with `--strict` (which promotes soft effect warnings to
errors) produces: `effect errors 0`, `effect warnings 0` — **no diagnostic
whatsoever** for `bad_io`, a function that performs a raw kernel syscall
(equivalent to a `write()`) while declaring `() -> ()` with NO effect row at
all. This directly contradicts the project's own stated core promise,
verbatim from `effectcheck.c3`'s own header comment: *"Pride's core promise
(v.md §1, §15, §22): 'No hidden behavior.' Every effect a function can
perform must appear in its declared effect row `! [...]`."*

## Severity
This is a soundness hole in the single most heavily marketed feature of the
language (algebraic effect tracking / "no hidden behavior"). Since `syscall`
is the ONLY way Pride programs interact with the OS at all (per the example
programs — there's no separate stdlib I/O primitive used in the exec tests;
`tests/exec/*.pie` and `examples/fib.pie` all call `syscall(1, 1, buf, len)`
for writes and `syscall(231, 0)` for exit), and this exact call pattern is
completely invisible to the effect system, EVERY example/test program in the
repository that "declares" `! [IO, Alloc]` and uses syscalls for I/O is
technically getting a free pass regardless of whether the `IO` annotation is
present — the effect checker cannot actually verify the IO claim on any
program using raw syscalls, which is the project's own idiomatic way to do
I/O. This means the checker's enforcement of the IO effect specifically is
close to vacuous for any realistic program in this codebase's own style.

## Fix
Add `ast::node_add_effect(node, ast::EFFECT_IO)` (or introduce/require a more
nuanced classification, e.g. mapping specific syscall numbers to IO vs. Unsafe
vs. both) to the `NODE_EXPR_SYSCALL` builder in `parser.c3`, and add a
corresponding `case Nk.NODE_EXPR_SYSCALL: acc.add_builtin(ast::EFFECT_IO);
self.gather_children(n, acc);` arm to `EffectChecker.gather_body`. Given
`syscall` is inherently unsafe/unchecked by nature (arbitrary numeric syscall,
no type safety on args), `EFFECT_UNSAFE` might be equally or more appropriate
than/in addition to `EFFECT_IO` — a design decision, but currently NEITHER is
applied, which is unambiguously wrong.
