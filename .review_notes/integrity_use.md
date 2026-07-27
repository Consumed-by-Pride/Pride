# integrity.c3 / resolve.c3 / typecheck.c3 — NODE_DECL_USE vs NODE_DECL_IMPORT mismatch

## Confirmed structural bug: integrity verifier's exemptions target a node kind the parser never produces
The parser (`parser.c3`, `Parser.parse_use`) ALWAYS builds a `NODE_DECL_IMPORT`
node (via `ast::node_decl_import`) for every `use` statement — there is no
constructor function for `NODE_DECL_USE` anywhere in `ast.c3`
(`grep -n "node_decl_use" ast.c3` → zero hits), and no call site in
`parser.c3` ever builds one directly either. `NODE_DECL_USE` appears to be a
legacy/aspirational node kind that predates the `NODE_DECL_IMPORT` refactor
(the "structured import" node with an `ImportData` payload, per its doc
comment "avoids string-walking children to resolve paths") and was never
fully migrated out of the passes that still reference it by name:

- `resolve.c3` (hoist_decl:476-478, resolve_node_body:772+) correctly handles
  BOTH kinds together in every switch (`case NODE_DECL_USE: case
  NODE_DECL_IMPORT:`), so name resolution itself is fine.
- `integrity.c3`'s `is_optedout_kind()` (line ~183) and `is_decl_kind()`
  (line ~207) list ONLY `NODE_DECL_USE` — never `NODE_DECL_IMPORT`. Likewise
  the module-base exemption in the field-access check (integrity.c3 ~118)
  checks `base.resolved.kind == ... || Nk.NODE_DECL_USE` — never
  `NODE_DECL_IMPORT`.
- `typecheck.c3`'s `mod_decl_of()` (line ~1228-1253), which resolves a `use`
  alias back to its target `NODE_DECL_MOD` for cross-module member lookups,
  also only checks `r.kind == Nk.NODE_DECL_USE` — never `NODE_DECL_IMPORT`.

## Consequences
1. **integrity.c3 false positives ("clean program ⟺ 0 integrity issues" is
   FALSE for any file with a non-trivial `use`)**: Because `NODE_DECL_IMPORT`
   is absent from `is_optedout_kind`, `Verifier.walk()` does NOT early-return
   when it reaches a `use` statement, and instead audits its children as
   ordinary value/declaration content:
     - The **alias name** in `use foo as Bar` is pushed as a plain `NODE_IDENT`
       child of the `NODE_DECL_IMPORT` node (parser.c3 `parse_use`,
       `s.push(self.name_from(alias_tok, Nk.NODE_IDENT))`). Because
       `NODE_DECL_IMPORT` is also absent from `is_decl_kind`,
       `decl_child_is_binder()` is never consulted for it, so the walker does
       NOT treat this child as a binder — it audits it as an ordinary
       value-position identifier under invariant I1 ("every value-position
       identifier must be resolved"). But `Resolver.hoist_use()` only ever
       *registers* the alias name into scope (`bind_name_node`, which updates
       the resolver's scope table, not the node's own `.resolved` field) — it
       never sets `.resolved` on the alias identifier node itself. Net
       result: **every `use ... as Alias` statement trips a spurious
       "identifier in value position has no resolution" integrity finding.**
     - Similarly, **named-import lists** `use foo.{A, B, C}` push `A`, `B`,
       `C` as plain `NODE_IDENT` children (parser.c3 `parse_use`, the
       `IMPORT_NAMED` branch) that are likewise never `.resolved` — same
       false-positive.
     - **Multi-segment paths** `use a.b.c` produce a `NODE_MODULE_PATH` with
       three `NODE_IDENT` children, of which by explicit, intentional design
       only the head (`a`) is resolved by `Resolver.resolve_node_body`'s
       `NODE_TYPE_PATH`/`NODE_MODULE_PATH` case (comment: "resolve ONLY the
       head segment ... Trailing segments name members of that module and
       are looked up later"). Since `NODE_DECL_IMPORT` isn't opted out, the
       generic default-recursion in `Verifier.walk` will reach into the
       `NODE_MODULE_PATH`'s non-head children as ordinary identifiers too
       (no special case for `NODE_MODULE_PATH` inside `integrity.c3`) —
       **another guaranteed false "unresolved name" finding for any
       multi-segment `use` path.**
   This directly contradicts the documented invariant in
   `docs/FRONTEND_STATUS.md` §4: *"Proven property: clean program ⟺ 0
   integrity issues... Every EXPECT-CLEAN conformance case audits to 0; only
   genuinely-erroneous programs carry findings."* A program with `use
   std::mem as M` or `use foo.{bar, baz}` — both syntactically ordinary,
   semantically valid imports — will report nonzero integrity issues despite
   being perfectly well-formed. (Not caught by the conformance suite because,
   per grep, none of the `conformance/cases/*.pie` files appear to exercise
   aliased or multi-segment `use` — the suite's coverage gap masks this bug.)

2. **typecheck.c3 cross-module member resolution silently degrades**:
   `mod_decl_of()` is the sole mechanism by which `m::sq(n)` (member access
   through a `use`-introduced alias) resolves the alias back to the actual
   module declaration for signature/arity checking (this is the exact
   feature `docs/FRONTEND_STATUS.md` calls out as "cross-module member typing
   fully works"). Since it only matches `r.kind == Nk.NODE_DECL_USE` and the
   resolver only ever attaches `.resolved` pointers to `NODE_DECL_IMPORT`
   nodes, `mod_decl_of()` returns `null` for EVERY use-alias in practice,
   falling through to whatever the caller does when no module is found
   (typically treating the member access as an ordinary/unqualified
   reference, which would misbehave or produce a spurious diagnostic).
   This needs a live rebuild to confirm the exact user-visible symptom, but
   structurally the "module decl of a use-node" lookup can never succeed
   given the current node-kind naming, since the checked kind is never
   instantiated.

## Fix
Add `Nk.NODE_DECL_IMPORT` alongside every existing `Nk.NODE_DECL_USE` case in
`integrity.c3` (`is_optedout_kind`, `is_decl_kind`, and the field-access
module-base check) and in `typecheck.c3`'s `mod_decl_of()`. Given `resolve.c3`
already treats both kinds identically everywhere, this is a very targeted,
low-risk fix. (Optionally: since `NODE_DECL_USE` is seemingly fully
superseded and never constructed, consider removing it from the enum/switches
entirely to eliminate the confusion — but the minimal fix is just adding the
missing `NODE_DECL_IMPORT` cases.)
