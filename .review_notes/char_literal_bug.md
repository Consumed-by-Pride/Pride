# parser.c3 — CRITICAL BUG: character literals ALWAYS evaluate to codepoint 0

## Confirmed
Both places the parser builds a char-literal AST node hardcode the value to
literal `0`, discarding the actual token text entirely:
  - `Parser.parse_primary()`, `case Tt.TOKEN_LIT_CHAR:` (parser.c3 ~3364-3366):
    ```
    case Tt.TOKEN_LIT_CHAR:
        self.advance();
        return ast::node_char(self.arena, 0, t.line, t.col);
    ```
  - `Parser.parse_pattern_atom()`, `case Tt.TOKEN_LIT_CHAR:` (parser.c3
    ~4281-4284) — identical hardcoded `0`, used for character literal PATTERNS
    (e.g. `match c | 'a' -> ...`).

There is no helper function anywhere in the codebase (confirmed via grep for
`parse_char_value`/`decode_char`/`char_value_of`/similar) that decodes a
`TOKEN_LIT_CHAR` token's source text (e.g. `'a'`, `'\n'`, `'\x41'`,
`'\u{1F600}'`) into a codepoint. The lexer (`lexer.c3`'s `lex_char`) does the
work of validating that a char literal is syntactically well-formed
(escape sequences, unterminated-literal checks, empty-literal checks) but
never computes or stores the decoded value on the Token — it only returns a
`Token{type, start, len, line, col}` span. The parser is the one place that
would need to interpret escapes and produce the final `char_val`, and it
simply never does — every `node_char()` call site (only these two) passes
the literal integer `0`.

## Consequence
**Every character literal in Pride source code compiles to the same value:
the null character (codepoint 0), regardless of what character was written.**
- `'a'`, `'Z'`, `'\n'`, `'\t'`, `'0'` — all become `0`.
- Character-literal PATTERNS in `match` are equally broken: `| 'a' -> foo() |
  'b' -> bar() | _ -> baz()` — since `'a'` and `'b'` both parse to the pattern
  literal `0`, the SECOND arm (`'b'`) is dead code (unreachable — it can never
  match anything the first arm didn't already catch, since both represent the
  literal 0), and neither arm actually matches an input character with value
  `'a'` (97) or `'b'` (98) — only literal NUL bytes.
- Every downstream consumer (`rewrite.c3`'s term hashing/equality/pattern
  matching, `ssi_ir.c3`'s constant lowering, `stage.c3`'s CTFE equality) reads
  `p.lit_char.char_val` faithfully and correctly — the bug is entirely
  isolated to the parser never setting it to anything but 0. This means the
  bug is a single, very localized, very high-impact defect: two one-line
  fixes (decode escape sequences from `t.start+1 .. t.len-1` into a codepoint,
  mirroring the validation logic already present in `lexer.c3::lex_char`) would
  fix character literals project-wide.

## Severity assessment
This is arguably the single most severe correctness bug found in the review:
char literals are an extremely common, basic language feature (used for
character comparisons, byte-buffer construction/parsing, ASCII art, tokenizer
implementations — including, ironically, the '\n' newline byte constant used
throughout the project's OWN example/test `.pie` files, e.g.
`examples/fib.pie`'s `buf[len] = 10u8 -- newline` which sidesteps the bug by
using an integer literal `10u8` instead of `'\n'` — suggesting either the
example authors already knew char literals don't work, or independently
avoided them). It silently produces WRONG running programs with no
diagnostic — the worst class of bug. It is not mentioned in
`CAPABILITIES_CHECKLIST.md` (which claims "Char literal, string literal, raw
bytes... ✅" under §3 Lexical — technically true only for LEXING, not for
the parser's semantic value, an important but easy-to-miss distinction) nor
in `finds.md`.

## Fix sketch
In `parse_primary`'s and `parse_pattern_atom`'s `TOKEN_LIT_CHAR` cases, decode
the codepoint from `t.start`/`t.len` (skipping the surrounding `'` quotes,
handling `\n \r \t \0 \\ \' \" \xHH \u{HHHH}` escapes exactly as validated in
`lexer.c3::lex_char`) and pass the resulting `uint` to `ast::node_char(...)`
instead of the literal `0`.

## SECOND, COMPOUNDING BUG: single-letter/underscore char literals are misparsed as label references
Verified BOTH statically and dynamically (against the stale `./pryde`, whose
lexer logic for this is unchanged from current `lexer.c3` — this is a lexer-
level ambiguity, and the lexer hasn't been shown to differ from source for
this feature): `lexer.c3`'s main dispatch (~1936-1946) special-cases a `'`
followed by an alphabetic character or underscore as the START of a
`'label_name` loop-label reference (`TOKEN_LABEL_REF`), consuming identifier
characters greedily — and only falls back to `lex_char()` (actual character
literal lexing) when the character after `'` is NOT alpha/underscore.
This means:
  - `'a'`, `'x'`, `'_'`, `'z'` etc. (a single-letter char literal) are
    ALWAYS lexed as a `TOKEN_LABEL_REF` spanning `'a` (2 chars) — completely
    swallowing the intended char literal syntax. The trailing `'` closing
    quote is left as a separate, dangling `'` character, which then fails to
    lex as anything valid, producing an "unterminated character literal"
    lexer diagnostic and cascading parse/resolve errors (exactly reproduced
    above: `let c = 'a'` → lexer diagnostic "unterminated character literal"
    at the position of the trailing quote, plus parser/resolver error
    cascades).
  - By contrast, `'5'` (digit) and `'\n'` (escape - starts with `\`, not
    alpha) correctly fall through to `lex_char()` and parse as
    `TOKEN_LIT_CHAR` — but then hit the FIRST bug (hardcoded value 0),
    silently becoming NUL.
So in practice: char literals whose content is a single letter or `_` don't
even parse as char literals at all (compile error), and char literals whose
content is a digit, punctuation, or escape sequence parse but always
evaluate to 0. **There is no way to write a working, correctly-valued
character literal in Pride today** for ANY character — letters can't even
be lexed as char literals, and everything else silently becomes NUL.
(Multi-character content like `'ab'` — invalid as a char literal anyway per
the language's own char-literal semantics — would also mislex if `a` is
alpha, consuming `'ab` as a label ref, though that's a lower-priority
edge case since it's not valid syntax regardless.)

This ambiguity is a real, structural lexer design issue (not just missing
code): resolving "is `'x` the start of a label reference or a character
literal?" requires unbounded lookahead past the identifier to see whether a
closing `'` follows immediately after exactly one character, which the
current single-token-of-lookahead architecture doesn't do. A correct fix
needs either (a) 2-character lookahead specifically: `'<alpha>'` (quote,
one alpha char, quote) unambiguously means "char literal", so check
`peek_at(self,2) == '\''` before committing to the label-ref path, or (b) a
syntax change (Rust-style requires only reserved lifetime-like label
identifiers to start with a specific longer pattern). Given Pride's existing
grammar (`'label_name` with no closing quote, vs `'x'` always exactly
one-character-then-quote for simple literals — though escapes like `'\n'`
are longer), option (a) — peeking two characters ahead for a bare
single-char-then-quote case, falling back to lex_char default otherwise
which already handles escapes — is the natural fix and would resolve the
common case (`'a'`, `'5'`, `'_'`) while preserving label-ref parsing for
`'loop_label` (which is never immediately followed by a closing `'`).
