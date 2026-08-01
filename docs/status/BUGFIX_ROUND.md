# Bug-fix round — the last 4 stdlib failures

**Verified 2026-08-01** · c3c 0.8.1 · LLVM 22.1.8 · Debian 13 trixie x86-64

Every number below was produced by running the compiler. Each fix has a
regression test that was **re-run against a deliberately reverted binary** to
confirm it actually fails when the bug returns.

---

## Result

| Metric | Before | After |
|---|---:|---:|
| stdlib self-clean | 254 / 258 | **258 / 258** |
| megaload (all modules, one unit) | 4 errors | **0 errors**, 164 ms |
| identifiers accounted for | 30,119 / 33,508 (89.9%) | **33,508 / 33,508 (100%)** |
| pfront regression suite | 85 pass | **100 pass**, 0 fail |
| experiments | 14 / 14 | 14 / 14 |
| conformance (legacy, frozen) | 261 / 262 | 261 / 262 |
| exec (legacy, frozen) | 44 / 47 | 44 / 47 |
| AST invariant violations | 0 | 0 |

---

## The seven defects

### 1. Inline body mistaken for a virtual block — `parse_block_or_expr`

The long-standing `let x = <if / else if / else>` bug. **Three previous
attempts failed** because they all assumed the fault was in `parse_if`'s
`else if` recursion. It was not.

`parse_block_or_expr` decides "block or bare expression" by column: deeper
than the owning statement means block. The inline `else 3i64` of a chain
nested in an initializer *is* deeper, so it took the virtual-block path.
`parse_virtual_block` then ran to the next DEDENT and consumed it — but that
DEDENT closed the **initializer**, so the initializer's own block never
terminated and swallowed the following statement.

Verified on the real token stream: the `else` body is at L10 C14; the stolen
DEDENT (`len=8`, the initializer level) is at L11.

**Fix:** a block the lexer folded away still *begins on a later line* than the
construct introducing it; an inline body sits on the same line. Added
`Parser.prev_line`, updated only by non-layout tokens.

Fixes `stdlib/fmt/float.pie`.

### 2. Stale `implicit_block` leaked across constructs

`implicit_block` is a one-shot hint set *at a distance* by a line continuation
(`settle_continuation`, and the debt-drop in the binary-operator parser). It
was never invalidated, so a continuation inside one `else if` branch survived
to the **inline `else` of the same chain** and turned it into a block — again
eating the initializer's DEDENT.

Found by tagging every DEDENT-consuming site and printing which one fired:
`BOE path=implicit` at L16 C14, then `SITE vblock` stealing `len=8` at L17.

**Fix:** same line invariant; clear the flag either way, since it has been
answered.

Fixes `stdlib/hash/wyhash.pie` and `stdlib/hash/auto_hash.pie`.

### 3. Soft keyword `then` misread as a construct head

`then` is contextual (spec §25) and arrives as `TOKEN_IDENT` so it stays usable
as a variable name. Three soft-keyword disambiguators — `tail`, `handle`,
`stage` — all asked *"does an identifier follow?"* and answered yes to `then`,
consuming the token that terminates the enclosing condition.

```pride
if head == tail then 0 as *IoUringCqe     -- `tail then` read as a tail call
```

The `if` lost its body and the error surfaced as "unresolved name `then`".

**Fix:** added `tok_is_then`, excluded at all three sites. Also fixed `handle`,
whose guard enumerated only closers and separators — a `handle` on the *left*
of an operator (`if handle == n then`) still opened a handler. It now treats a
following infix operator as proof it was an operand. The genuine `tail f(x)`
annotation still applies (asserted).

### 4. LEXER: hanging-indent realign destroyed enclosing levels

The worst of the seven, because it is **completely silent**.

When a line lands on a column never pushed as a block level, the lexer pops to
the nearest enclosing level and reconciles — by *overwriting*
`indents[indent_idx]`. That is only safe when the observed column is not
deeper than the level being written over. When it *is* deeper, a live block is
destroyed and its closing DEDENT is never emitted.

Each wrapped `else if` condition consumed one stack slot. Measured on the real
indent stack:

```
L8   REALIGN idx=2  4 -> 6     clause-body level destroyed
L9   REALIGN idx=1  2 -> 4     clause level destroyed
L12  REALIGN idx=0  0 -> 4     FILE level destroyed
L14  REALIGN idx=0  4 -> 0     no DEDENT possible: idx == 0
```

After the file level is clobbered the pop loop is dead (`indent_idx > 0`) and
**no DEDENT is ever emitted again**. The next top-level function is parsed
*inside* its predecessor, with **zero diagnostics**.

**Fix:** push a new level when the column is deeper than the enclosing one;
only overwrite when it is not, which can happen only at index 0.

Recovered 3 of 4 functions in `convert_fast.pie` (`fast_f32`,
`mantissa_fits_f64`, `mantissa_fits_f32`) that every caller had been failing
to import.

**Honest scope:** a stdlib-wide sweep comparing top-level declaration counts
before and after found exactly **one** affected file, 3 functions recovered
(3,915 → 3,918). The bug is severe but rare.

### 5. RESOLVER: a local binding did not shadow a same-named module

Module-qualified reads are tried *first* — that is what makes
`os.linux.malloc(n)` work, since the parser cannot distinguish a method call
from a module member and always builds `N_EXPR_METHOD`. But the module reading
was tried **unconditionally**.

`stdlib/target.pie` declares `mod target`, so in `stdlib/pride/rewrite.pie`:

```pride
| (u, pat, target) -> ... target.tag ...
```

the parameter `target` was read as the *module* `target`. The file was clean
compiled alone and produced 4 errors in the 258-module graph — the hardest
kind of failure to place, because the broken file is correct.

**Fix:** added `Resolver.seg_is_local_value`. A module **alias** bound by `use`
deliberately does *not* count as shadowing, since that is exactly what a module
path should match.

### 6. Verifier counted module-path prefixes as unresolved

The counter tested `resolved == null && sym == null`, ignoring the
`NF_RESOLVED` flag the resolver sets on a segment naming a module. Reported
**3,389 phantom unresolved identifiers** across the stdlib while emitting zero
errors.

### 7. `try_resolve_module_chain` never flagged its receiver

The qualified-**call** path calls `mark_chain_resolved`; the qualified-**value**
path did not. `os.linux.malloc(n)` was clean but `os.linux.PROT_READ` left `os`
unflagged.

Together, 6 and 7 took identifier accounting from 89.9% to **100.000%**.

---

## Stdlib source debt (real source bugs, not compiler gaps)

* **`parse_float.pie`**
  * `F64_NAN_BITS` read from `os.linux`; it lives in `float_info`.
  * Two constants written `fn NAME : TYPE = expr` — not a declaration form.
    Both duplicated real `const`s already in `float_info`; deleted.
  * Calls to `slow_f64_from_number` / `slow_f32_from_number`, which **never
    existed**. The real entry points are `slow_path_f64` / `slow_path_f32`, and
    they take `(ptr, len, neg)` — the slow converter re-reads the original text
    at arbitrary precision, so passing the already-truncated 19-digit mantissa
    was wrong regardless of the name.

  *(Correction to an earlier note: `convert_slow` and `convert_hex` **do**
  exist. The claim that they were missing was wrong.)*

* **`io_uring.pie`**: `|> (p -> p[0u32])` used a lambda syntax Pride does not
  have — no anonymous-function form appears in the spec or anywhere else in the
  stdlib. Rewritten to the index form every sibling accessor already uses.

---

## Why the tests assert structure, not error counts

Bugs 1, 2 and 4 **reparent code silently**. A count-based test passes while the
tree is wrong. Two concrete demonstrations:

* An s-expression substring test for bug 1 passed against **both** the fixed
  and the buggy binary — the two trees share the same tail. Discarded.
* For bug 4, the reverted binary still reports `0 errors` on the regression
  file; only the top-level declaration count (1 instead of 6) reveals it.

So the assertions check AST indentation depth, top-level declaration counts,
and binder identity. Every one was validated against a reverted build:

```
=== BUG (reverted binary) ===
  FAIL  elseif_init      let depth=9 use depth=0 unresolved=1
  FAIL  elseif_init2     d=9 e=13 unresolved=3
  FAIL  implicit_leak    tuple-let=13 let-s=17 unresolved=2
  FAIL  indent_stack     1 top-level fns, want 6
  FAIL  indent_stack2    convert_fast: 1 fns, want 4
  FAIL  shadow_module    unresolved=3 target-bound=0
  FAIL  megaload         4 errors over 259 modules
```

**`megaload` is now permanent.** It builds a file that `use`s every stdlib
module and compiles it as one unit. That configuration is the only one that
exposes bug 5 and the earlier alias/module collision, and it runs on every
invocation of `pfront_tests/run.sh` rather than as an occasional manual check.

---

## New regression cases

| Case | Asserts |
|---|---|
| `71_elseif_init` | 5 shapes of `let x = if/else if/else`; trailing statement is a sibling |
| `72_implicit_block_leak` | continuation in branch 1, branch 2, and with no tuple pattern |
| `73_soft_then_kw` | `tail`/`handle`/`stage` before `then`; real `tail f(x)` still annotated |
| `74_hanging_indent_stack` | 2- and 3-link wrapped chains; all 6 functions stay top-level |
| `75_local_shadows_module` | parameter and `let` shadow `mod target`; `use` alias still resolves |
| `megaload` | 258 modules, one unit, 0 errors |
| `ident_accounting` | 7 heavy modules, 0 unaccounted identifiers |

---

## Still not done

1. **`impl ... for`** is unimplemented. Unused anywhere in the stdlib, so it is
   unexercised syntax rather than a blocker.
2. **Block flattening never fires on real stdlib code** (0 sites). Tested by the
   suite, but its real-world value remains unproven.
3. **CSE reports, it does not rewrite.** Introducing a temporary needs a scope
   to hold it — a middle-end job.
4. **Liveness is intra-procedural.** A store to a variable captured by a closure
   or reachable through a pointer is conservatively kept.
5. **`--strict-types` is nearly inert** now that Pride is untyped. It should
   probably be removed or aliased to `--lint`.
6. **Legacy `conformance` 261/262 and `exec` 44/47** are unchanged. Those
   failures predate this work and live in the frozen legacy pipeline
   (`case 258` uses an unimplemented effect-handler form).
