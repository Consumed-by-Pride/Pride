# lexer.c3 review

## BUG: dead keyword branches due to wrong length bucket in keyword_type()
`keyword_type()` switches on `len` first, then does span_eq comparisons within
each case block — but four keywords are misplaced under the WRONG case (their
literal string's true length doesn't match the case they're nested in), so
they are unreachable and always fall through to TOKEN_IDENT (or TOKEN_TYPEVAR
since they're lowercase... no, lowercase so TOKEN_IDENT).

- line 1262: `if (span_eq(p, len, "typeof", 6)) return TOKEN_KW_TYPEOF;`
  nested inside `case 4:` (len==4), but "typeof" has 6 bytes → span_eq(p,4,"typeof",6)
  always false (span_eq first checks len!=lit_len). DEAD CODE.
- line 1263: same for "typeof_unqual" (13 bytes) inside case 4. DEAD.
- line 1269: `"nullptr"` (7 bytes) inside `case 4:`. DEAD.
- line 1297: `"constexpr"` (9 bytes) inside `case 5:` (len==5). DEAD.

Verified empirically: `./pryde` on a file using `typeof(1)`, `nullptr`, or
`constexpr let x = 1` lexes them as TOKEN_IDENT, not the keyword — confirmed via
AST dump (Ident 'nullptr', Ident 'constexpr' as bogus expr statement, `typeof`
resolves as an unresolved call to ident 'typeof').
Meanwhile `parser.c3` has real, apparently-tested-looking code paths for
TOKEN_KW_TYPEOF (line 1811), TOKEN_KW_TYPEOF_UNQUAL (1812), TOKEN_KW_NULLPTR
(2982, 3153, 3455, 4298), TOKEN_KW_CONSTEXPR (431, 2602) — all permanently
unreachable in practice because the lexer never emits these tokens.
Impact: `typeof`, `typeof_unqual`, `nullptr`, `constexpr` are silently broken
language features — advertised (comments call them "C23" keywords) but 100%
nonfunctional. Not caught by conformance suite (no test uses these keywords).

Trivial fix: move the three misfiled `if` lines to `case 6:`/`case 13:`/`case 7:`/`case 9:`
buckets respectively (typeof→6, typeof_unqual→13, nullptr→7, constexpr→9 — note
9 already has other entries so just moving to the right case each).

## BUG: TOKEN_SIGMA / TOKEN_PHI unicode byte sequences are wrong (wrong codepoints)
`unicode_operator_at()` (~line 1479-1495) matches σ and φ against the WRONG
UTF-8 byte sequences:
  - line ~1489: `b1==0x83 && b2==0x83` (bytes E2 83 83) is claimed to be σ (U+03C3),
    but E2 83 83 actually decodes to U+20C3 "COMBINING ENCLOSING CIRCLE
    BACKSLASH" — real σ (U+03C3) is only 2 bytes: CF 83.
  - line ~1490: `b1==0x86 && b2==0x95` (bytes E2 86 95) is claimed to be φ
    (U+03C6), but E2 86 95 actually decodes to U+2195 "UP DOWN ARROW" — real φ
    (U+03C6) is 2 bytes: CF 86.
  Comment even hints at the problem: "// σ (U+03C3 — note: encoded differently)"
  — i.e. the author noticed U+03C3 doesn't fit the 3-byte E2.. pattern used for
  the other operators (which are all in the U+2190-U+22FF range, correctly
  3-byte E2 8x/9x sequences) but never actually fixed the lookup.
  Verified empirically: writing an actual `σ` character (CF 83) in source is
  lexed as a plain identifier (high-byte ident-start), not TOKEN_SIGMA.
Impact: TOKEN_SIGMA/TOKEN_PHI are dead — never produced by the lexer for the
literal characters they're named after. (Low real-world impact since these are
described as internal/metaprogramming-only tokens not expected in normal
surface syntax, and no conformance test exercises them — but as shipped, the
feature literally cannot be typed by a user.)

## BUG (major): checked-arithmetic operators +? -? *? are never lexed as single tokens
`lex_punct()` has explicit two-char lookahead cases for wrapping (`+%` `-%` `*%`)
and saturating (`+|` `-|` `*|`) operators, but there is NO corresponding
lookahead case for `+?`, `-?`, `*?` (TOKEN_PLUS_QUESTION/MINUS_QUESTION/STAR_QUESTION
exist as enum values, referenced throughout parser.c3/codegen.c3, but the lexer
never produces them). `case '?':` (line ~1807) unconditionally returns a bare
TOKEN_QUESTION with no lookbehind/lookahead fusion, and there's no check
earlier in lex_punct for `c=='+' && peek_at(1)=='?'` etc. (contrast with the
`+%`/`+|` cases immediately below/above it in the same function).
Verified empirically: `1 +? 2` lexes as `PLUS` then a separate `?` token,
which the parser turns into `Binary(+, 1, <invalid>)` — a parse error, not a
checked-add. The `CAPABILITIES_CHECKLIST.md` claims:
  "| `+?` `-?` `*?` checked (returns `{T, bool}`) | ✅ | Via `llvm.sadd.with.overflow` |"
This is FALSE — the codegen support in codegen.c3:2074-2085 (llvm.sadd.with.overflow
etc.) and the parser support in parser.c3:2926,2945 are both unreachable dead
code because the lexer never emits the token they're matching on. This is the
single highest-impact finding in the lexer: an entire advertised, "exec
verified" language feature is completely non-functional.
Fix: add three lookahead branches to lex_punct() mirroring the existing
`+%`/`+|` pattern:
  if (c=='+' && peek_at(self,1)=='?') { ...; return TOKEN_PLUS_QUESTION; }
  if (c=='-' && peek_at(self,1)=='?') { ...; return TOKEN_MINUS_QUESTION; }
  if (c=='*' && peek_at(self,1)=='?') { ...; return TOKEN_STAR_QUESTION; }
placed before the generic `case '?':` fallback and before/near the existing
+%/+| checks so it is tried first (must come before bare '+' handling, which
happens via the switch at the bottom — this is fine since it's a distinct
sequence check like the others done earlier in the function).
Caveat: `?` is also the try/propagate postfix operator (TOKEN_QUESTION per
parser usage) — need to make sure `+?`/`-?`/`*?` fusion doesn't break any
place someone writes e.g. `f()? + 1` (postfix ? immediately followed by +).
That's `?` then `+`, i.e. QUESTION PLUS, order-reversed, so it's unaffected;
only PLUS immediately followed by QUESTION (no space) collides, which is the
intended new-operator sequence anyway.

## Toolchain note (affects verification methodology for rest of review)
The committed `./pryde` binary is STALE relative to the current source: `nm pryde`
shows 140 `parser.Parser.*` symbols vs 144 function definitions in the current
`parser.c3`, and specifically LACKS `parser.Parser.parse_operator_decl` (present
in source, referenced from `parse_top_decl`'s "operator" contextual-keyword
branch) even though `parse_interface`, `parse_impl` etc. are present. This means
dynamic testing against the shipped binary can only be trusted for older/stable
features; for newer source (operator overloading decl, doc-comment attachment,
etc.) only static reading is reliable in this sandbox.
c3c v0.8.1 could not be re-fetched to rebuild (`release-assets.githubusercontent.com`
is TLS-blocked in this sandbox; only `codeload.github.com`/`api.github.com` are
reachable, and codeload only has the c3c *source*, which requires a matching
LLVM dev package that apt cannot fetch either — `deb.debian.org` is also
unreachable over HTTP in this network namespace). All later findings below are
therefore from careful static reading + cross-referencing (grep for every
producer/consumer of a symbol, struct field, enum case) rather than execution,
except where explicitly marked "verified via ./pryde" for older, stable
features that the stale binary still faithfully represents (e.g. the keyword_type
and lex_punct bugs above, which are lexer-level and match the binary's observed
behavior exactly).

## (ssi_ir.c3) Minor: silent truncation of pending inner-fn/closure list at 64
`SsiModule.pending_inner_fns` is a fixed `Node*[64]` (ssi_ir.c3:250). Two call
sites (ssi_ir.c3:1854 and 2586) guard pushes with `if (m.pending_inner_count < 64)`
but there is NO else-branch diagnostic — the 65th+ nested function/closure
literal in a single module is silently dropped (never lowered, never linked),
which would produce a binary that fails to link (undefined symbol) or,worse,
silently miscompiles by leaving a dangling IR_UNKNOWN callee reference with no
backing definition. Same "silently truncate on overflow, no diagnostic"
pattern recurs project-wide (see stage.c3 gensym note, lexer diag cap, mono.c3
cbuf comment) — this is a systemic house style that trades safety for
simplicity but should at minimum emit a diagnostic/abort instead of silent
data loss for anything that affects program correctness (as opposed to e.g.
"only report the first 256 lex errors", which is a fine, harmless cap).

## INCONCLUSIVE (needs live rebuild to confirm): `0..10 by 2` / `for i in 0..10 by 2`
Empirically, running the shipped (stale) `./pryde` binary on `let x = 0..10 by 2`
lexes/parses `by` as a plain NODE_IDENT (producing a bogus `Call(by, 2)` after
the range, with a resolve error "undefined name [by?]"), rather than invoking
`node_range_step`. HOWEVER — static reading of the CURRENT source shows:
  - `keyword_type()` case 2 (lexer.c3 ~1245) correctly matches `"by"` (2 bytes)
    to TOKEN_KW_BY (no length-bucket mismatch, unlike the typeof/nullptr/
    constexpr bugs above).
  - `Parser.parse_range()` (parser.c3:2773) correctly checks
    `self.check(Tt.TOKEN_KW_BY)` after parsing the range bounds and, if
    present, builds a `NODE_EXPR_RANGE_STEP` via `ast::node_range_step`.
  - `Resolver.resolve_node_body`'s default case does generic child recursion,
    which for a real RANGE_STEP node would just re-resolve start/end/step,
    not treat "by" as an identifier.
This strongly suggests the "by"-step-range feature was added to the source
AFTER the currently-committed `pryde` binary was built (consistent with the
already-confirmed staleness re: `parse_operator_decl`), and is NOT a live bug
in current source — but this could not be confirmed by actually rebuilding
(toolchain unreachable in this sandbox, see toolchain note above). Flagging as
inconclusive/needs-CI-rebuild rather than a confirmed defect.
Separately, real gaps regardless of the above: I could not find any handling
of `NODE_EXPR_RANGE_STEP` in typecheck.c3, effectcheck.c3, ssi.c3, ssi_ir.c3,
sasi.c3, sasi_opt.c3, mono.c3, or codegen.c3 (grep across all of them for
"RANGE_STEP" returns zero hits outside ast.c3). If the parser really does
build this node (which static reading says it does), the SSI-IR lowering
(`SsiModule.lower_expr`, ssi_ir.c3) has no case for it and it would fall into
whatever the default arm of that switch does — worth checking directly (see
below, ssi_ir.c3 section) since if the default arm there returns an IR_UNKNOWN
or crashes, then `for i in 0..10 by 2` / `x..y by z` step-ranges are unlowerable
even though they parse, i.e. another "parses but silently produces broken/no
code" gap in the same family as the union/intersection issue already
documented in finds.md.

## Methodology correction: attribute-block dynamic test was a stale-binary artifact, not a real bug
Empirically `./pryde` mis-parses `#[inline]\nfn main...` as a bogus
`Index(Invalid, Invalid)` expression rather than invoking parse_attr_block.
However, static reading of the CURRENT parser.c3 source (parse_top_decl's
`if (self.check(Tt.TOKEN_HASH)) { ... parse_attr_block() ... }` at line ~373,
parse_attr_block at line 1163, parse_attribute at line 1204, attr_kind_for at
line ~1290) traces through correctly for `#[inline]`: HASH branch is taken at
top-decl level, parse_attr_block consumes the bracketed attribute correctly,
attr_kind_for maps "inline" to NODE_ATTR_INLINE, and the attribute list is
correctly grafted onto the following decl. This appears to be another
manifestation of the stale-binary problem (the committed `pryde` was built
before some parser refactor — likely the same rebuild that predates
parse_operator_decl/doc-comment support). Given TWO independent confirmed
cases of dynamic-test-vs-source divergence, I am downgrading confidence in
ALL further dynamic (`./pryde ...`) tests for anything except the most
basic/stable lexer token behavior (already cross-validated: keyword_type
length-bucket bug and lex_punct +?/-?/*? bug both reproduce EXACTLY what
static reading of lexer.c3 predicts, so those two remain HIGH CONFIDENCE
confirmed bugs). From here on, the review proceeds by static cross-referencing
(grep every producer vs. every consumer of each AST node kind / struct field /
function) rather than executing the stale binary, and clearly marks anything
still empirically tested.
