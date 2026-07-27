# parser.c3 — CRITICAL BUG: compile-time "macro" detection (`include_bytes`/`env`/`concat`/`format`) uses a fragile byte-signature check that COLLIDES with ordinary identifiers and silently hijacks real function calls

## Confirmed via static analysis AND live reproduction against the shipped binary
`Parser.parse_primary()`'s `TOKEN_IDENT` case (parser.c3 ~3474-3512) implements
detection of the four "compile-time macro" pseudo-functions `include_bytes(...)`,
`env(...)`, `concat(...)`, `format(...)` NOT by comparing the identifier's full
text, but via ad-hoc, partial byte-position checks chosen apparently to avoid
calling a proper string-equality helper:
```
bool ib = (t.len==13&&t.start[0]=='i'&&t.start[7]=='_'&&t.start[8]=='b'); // include_bytes
bool ev = (t.len==3&&t.start[0]=='e'&&t.start[1]=='n'&&t.start[2]=='v');   // env
bool cc = (t.len==6&&t.start[0]=='c'&&t.start[1]=='o'&&t.start[5]=='t');   // concat
bool fm = (t.len==6&&t.start[0]=='f'&&t.start[1]=='o'&&t.start[2]=='r'&&t.start[3]=='m'&&t.start[4]=='a'&&t.start[5]=='t'); // format
```
Only `ib` (include_bytes, checking bytes at indices 0,7,8 plus length 13) is
reasonably specific (5 constraints for the 13-char name — still theoretically
collidable but much less likely). The other three are dangerously
under-constrained:
  - `ev`: ANY 3-letter identifier starting with `"en"` and any third
    character — wait, actually checks `t.start[2]=='v'` too, so it does
    require exactly `"env"`... Correction: re-reading, `ev` requires ALL
    THREE characters match "env" exactly (since len==3 and all 3 byte
    positions are checked) — so `ev` is actually fully correct (accidentally,
    by exhausting all positions for a 3-character word). Not a collision risk.
  - `cc` (concat): only checks length==6, `start[0]=='c'`, `start[1]=='o'`,
    and `start[5]=='t'` — bytes at INDICES 2, 3, 4 are never checked! Any
    6-letter identifier starting with "co" and ending in "t" matches,
    regardless of the middle three letters. E.g. `cobalt`, `covert`,
    `comfit`, `coffet`, `corrupt`(7 chars, doesn't match len), `cocoat`,
    `cabinet`(7, no) — but 6-letter ones: "cobalt", "covent", "cofact",
    "comnet"... ALL of these would incorrectly trigger the `concat!`-style
    macro rewrite if followed by `(`.
  - `fm` (format): checks length==6 and ALL SIX character positions
    (`f,o,r,m,a,t`) — so `fm` is fully correct, no collision risk (name must
    be exactly "format").
So the confirmed defective check is `cc` (concat) — verified by REPRODUCING
LIVE against the shipped `./pryde` binary: a user function literally named
`cobalt` (6 letters, starts 'c','o', ends 't' — an entirely ordinary,
plausible identifier with ZERO relation to string concatenation) called as
`cobalt(5)` is silently parsed as `Concat(LitInt(5))` — the identifier
`cobalt` is discarded entirely (never even becomes a `NODE_IDENT`, so it can
never resolve, never appear as a call, and the "call" silently becomes a
compile-time string-concat pseudo-op instead)! This reproduced exactly as
predicted from static analysis.

## Impact
Any identifier of exactly 6 bytes, starting with "co", ending in "t", used as
a callable name (function or macro-like call `name(...)`) — e.g. `cobalt`,
`covent`, `cofact`, `content`(7 chars→ doesn't match, safe), `comfort`(7→
safe), but 6-char hits include real plausible names like `commit`("co"+"t"?
c-o-m-m-i-t: last char 't', starts "co" — YES matches!), `count`(5 chars,
no), `coast`(5, no), `corset`, `comet`+1... — silently has its call
expression replaced by a `NODE_EXPR_CONCAT` node whose only child is the
first parenthesized argument (subsequent comma-separated arguments, if any,
are simply DROPPED — since only ONE `arg2 = self.parse_expr()` is read, with
no comma-loop, unlike the `format!` case). This is a silent, severe
correctness bug: no diagnostic is ever produced; the user's actual function
call is deleted from the program and replaced with nonsense, and (per the
finding that NODE_EXPR_CONCAT itself has zero downstream implementation —
see the earlier zero-coverage grep sweep) the resulting `Concat` node isn't
even lowered anywhere either, meaning the whole call effectively vanishes /
becomes an opaque no-op by the time it reaches codegen.

## Additional related issues in the same code block
1. Even for the CORRECTLY-identified macro names, argument-list parsing is
   broken for all three of include_bytes/env/concat: only a SINGLE argument
   is parsed (`Node* arg2 = null; if (!self.check(RPAREN)) arg2 =
   self.parse_expr();` — no comma/loop), so `concat("a", "b", "c")` (as
   documented in the node's own comment: "concat!(\"a\", \"b\", ...) — string
   concat at compile time") only ever captures the FIRST argument; everything
   after the first comma is silently discarded by the subsequent
   `self.accept(Tt.TOKEN_RPAREN)` failing to match (since the parser is still
   sitting on a `,`), which likely cascades into a parse error or worse,
   silently eats the rest of the expression as if it were something else
   (needs deeper testing, but at minimum the documented multi-arg
   `concat!(...)` API is not actually implemented — single-arg only).
2. These "macros" don't require the `!` at all — `self.check(Tt.TOKEN_BANG)`
   is optional (`if (self.check(...)) self.advance();`), meaning `env(x)`
   (no bang) ALSO triggers macro detection, further widening the collision
   surface: ANY 3-letter call starting/ending exactly "env" — well `env` is
   only one 3-letter word, so this specific one is fine — but combined with
   the broken `cc` check, `format`/`include_bytes` collisions require exact
   name matches (safe) while `concat`'s check (broken) does not.
3. NONE of `NODE_EXPR_INCLUDE_BYTES` / `NODE_EXPR_ENV_VAR` / `NODE_EXPR_CONCAT`
   have ANY downstream handling in resolve/typecheck/effectcheck/ssi_ir/codegen
   (confirmed via the earlier project-wide zero-coverage grep sweep) — so even
   when correctly identified, these three "compile-time macros" are entirely
   unimplemented past parsing: they parse into inert AST nodes with no
   resolution, no type, no codegen. (`format!` IS implemented, as established
   earlier — it's the one node here that actually works.)

## Fix
1. Replace `cc`'s ad-hoc partial-byte check with either a call to the
   existing `tok_text_eq(t, "concat", 6)` helper (already used elsewhere in
   this exact file for other keyword-like text comparisons) or add the
   missing byte checks for indices 2, 3, 4.
2. Implement proper comma-separated multi-argument parsing for
   include_bytes/env/concat (matching the `format!` case's loop), or scope
   them down to their actual single-argument use if that's the intended
   design — but the doc comments explicitly promise multi-arg `concat!`.
3. Implement resolve/typecheck/ssi_ir/codegen support for these three node
   kinds, or explicitly document them as unimplemented/reserved syntax (as
   the project does elsewhere for admitted gaps).
4. More fundamentally: relying on bare identifier-name sniffing (rather than
   a proper `!`-suffixed macro-invocation token/grammar production, or at
   minimum consistent full-string comparison via `tok_text_eq`) to detect
   "special" call forms is inherently fragile and the root cause of this bug
   class — worth reconsidering the whole mechanism, especially since it
   silently and unconditionally hijacks otherwise-valid user code with no
   possible escape hatch (there's no way to call a function literally named
   `env`, `format`, `concat`, or `include_bytes` — or, due to the `cc` bug,
   many other 6-letter co...t identifiers).
