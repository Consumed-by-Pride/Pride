# parser.c3 / ast.c3 — bare-string interpolation ("hello {name}") is entirely non-functional beyond parsing (format!() is fine, see correction below)

## Confirmed: NODE_INTERPOLATED_STRING is a dead end — zero downstream consumers, and the hole expressions are never even parsed as expressions
`Parser.parse_primary()`'s TOKEN_LIT_STRING case (parser.c3 ~3365-3449) detects
`{...}` holes in string literals and builds a `NODE_INTERPOLATED_STRING` node.
But by the parser's OWN admission in its comments:
  "Full re-lexing of holes requires a sub-lexer; for now emit a raw-bytes node
   carrying the expression source text so that the semantic analyser can
   re-parse it with a nested lexer."
Each hole's contents (e.g. the `name` in `"hello {name}"`) is packaged as a
**`NODE_LIT_RAW_BYTES`** node holding the raw, unparsed source text of the
hole (`src + hole_start, hole_end - hole_start`) — i.e. it is NOT an
expression AST at all, just a byte-string literal whose payload happens to be
the characters `n`,`a`,`m`,`e`.

Searching the entire codebase confirms this "later re-parse" NEVER happens:
`grep -rn "re-parse\|sub-lexer\|nested lexer\|reparse" *.c3` finds only the
three comments in parser.c3 quoted above — no resolve.c3/typecheck.c3/
ssi_ir.c3/codegen.c3 code implements the promised nested-lexer re-parse step.
Additionally `grep -rn NODE_INTERPOLATED_STRING *.c3` shows the node kind is
referenced in exactly 3 places: its own enum declaration, its constructor
(called once, from the parser), and its `node_kind_name()` pretty-printer
string — it has **zero cases in resolve.c3, typecheck.c3, effectcheck.c3,
lint.c3, integrity.c3, ssi.c3, ssi_ir.c3, sasi.c3, mono.c3, or codegen.c3**.

## Consequences
1. Every pass that walks the AST generically (resolve.c3's default-recursion
   arm, integrity.c3's generic walker) will visit the `NODE_INTERPOLATED_STRING`
   node's children — which include, for each hole, a `NODE_LIT_RAW_BYTES` node
   holding raw source text like `name` — as ordinary children. `NODE_LIT_RAW_BYTES`
   is a *literal* kind (resolve.c3's `resolve_node_body` switch lists it
   under the "literals, no resolution needed" bucket alongside
   NODE_LIT_INT/NODE_LIT_STRING/etc., `break;`), so the resolver will NOT try
   to resolve `name` as an identifier — meaning **the interpolation variable
   reference is silently never looked up, never type-checked, and never
   evaluated**. The net behavior of `"hello {name}"` is indistinguishable
   from the compiler's perspective from a literal string containing the
   raw bytes `hello ` + `name` (as an opaque byte blob) + trailing segment —
   there is no code path anywhere that would substitute the *value* of the
   variable `name` into the output string at runtime.
2. Because `NODE_INTERPOLATED_STRING` has no ssi_ir.c3 lowering case either,
   it falls into `lower_expr_body`'s generic `default:` arm (same as
   `NODE_EXPR_RANGE_STEP`, discussed elsewhere) — becoming an opaque
   `IR_UNKNOWN` whose args are the lowered children (the literal segments AND
   the raw-bytes "hole" pseudo-literals, each lowered independently as
   `IR_CONST_STR`-ish values via the `NODE_LIT_RAW_BYTES` case in
   `lower_expr_body`, ~line offset 48 in the earlier awk scan). Codegen would
   then have no idea this is supposed to be a runtime string-formatting
   operation — there is no `IR_FORMAT`/`IR_CONCAT`-style opcode for building
   the final interpolated string, and no runtime helper for string
   concatenation of the segments + stringified hole values.
3. **CORRECTION after deeper check**: `format!("template", args...)`
   (`NODE_EXPR_FORMAT`, parser.c3 ~3504) is a SEPARATE, macro-style construct
   from `"..{..}.."` interpolation, and unlike bare-string interpolation it
   IS actually implemented end-to-end: `ssi_ir.c3` (~2397-2419) has a real
   `case Nk.NODE_EXPR_FORMAT` that lowers the args (real sub-expressions this
   time, since format! args are ordinary comma-separated expressions, not
   raw-byte holes) into an `IR_UNKNOWN` tagged with the format node;
   `codegen.c3` (~4370-4450+) has a substantial, genuine codegen path that
   walks the template string byte-by-byte at compile time, emits
   `pride_str_init`/segment-push/arg-push call sequences against a stack
   `{ptr,i64,i64}` String struct; and `runtime/compiler_rt.c` provides real
   `pride_str_init`, `pride_str_push_str`, `pride_str_push_i64`,
   `pride_str_push_f64` implementations. So `format!(...)` is a working
   feature — retracting the earlier blanket claim that it was inert.

## Summary (revised)
Only bare **`"...{expr}..."` string interpolation** (as opposed to the
separate, working `format!(...)` macro-call form) is confirmed dead: it
parses into a `NODE_INTERPOLATED_STRING` AST shape, but the interpolation
holes are packaged as inert `NODE_LIT_RAW_BYTES` literals rather than real
sub-expressions (per the parser's own comments, a promised "nested lexer
re-parse" of hole contents was never implemented), and `NODE_INTERPOLATED_STRING`
has zero cases in every downstream pass (resolve/typecheck/effectcheck/lint/
integrity/ssi/ssi_ir/sasi/mono/codegen — confirmed via grep, the only 3 hits
project-wide are the enum declaration, the one constructor call site in the
parser, and the pretty-printer name). This is more severe than the
already-documented union/intersection-type gap (which at least resolves and
type-checks correctly, only failing at codegen) — here, even name resolution
is skipped, since the interpolation holes are opaque byte blobs, not
expressions. Neither `CAPABILITIES_CHECKLIST.md` nor `finds.md` mentions this
gap. (The similarly-named but functionally distinct `format!(...)` macro is
NOT affected — see correction above.)
