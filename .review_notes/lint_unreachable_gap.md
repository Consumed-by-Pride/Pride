# lint.c3 — unreachable-code detection misses break/continue (and labeled variants)

`Linter.is_diverging()` (lint.c3 ~430-448) — the function that decides whether
a statement "always transfers control away, never falls through", used by
`lint_block` to flag dead code after it — only recognizes:
`NODE_STMT_RETURN`, `NODE_STMT_UNREACHABLE`, `NODE_STMT_TRAP`, `NODE_UB_BANG`
(and an expression-statement wrapping one of those). It does NOT include
`NODE_STMT_BREAK`, `NODE_STMT_BREAK_LABEL`, `NODE_STMT_CONTINUE`, or
`NODE_STMT_CONTINUE_LABEL` — all of which unconditionally transfer control
out of the current block (to the loop's exit or next-iteration point) exactly
as unconditionally as `return` does. Confirmed via grep: zero mentions of
`NODE_STMT_BREAK`/`NODE_STMT_CONTINUE`/label variants anywhere in `lint.c3`.

Concretely:
```
while true
  break
  let x = 1      -- statically dead: unreachable after break
  foo()          -- also dead
```
The lint pass will NOT flag `let x = 1` or `foo()` as unreachable code here,
even though they can never execute — `break`/`continue` are just as
control-flow-terminal as `return` for this purpose. This is a straightforward
completeness gap (false negative) in the "unreachable code after a diverging
statement" lint (lint #3 in the module's own header doc list) — not a
crash/soundness bug, but a real coverage hole in an advertised lint.

Fix: add `case Nk.NODE_STMT_BREAK: case Nk.NODE_STMT_BREAK_LABEL: case
Nk.NODE_STMT_CONTINUE: case Nk.NODE_STMT_CONTINUE_LABEL: return true;` to
`is_diverging()`.
