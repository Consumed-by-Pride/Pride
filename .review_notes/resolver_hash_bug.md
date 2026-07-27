# resolve.c3 — Scope hash-index fast path: dead/never-built AND reads uninitialized memory for every scope but the outermost

## Bug 1: hash_idx is declared, read, but NEVER populated (write side is entirely missing)
`Scope.hash_idx[SCOPE_HASH_SIZE]` and `Scope.hash_valid` exist specifically so
`Resolver.lookup_local()` can do an O(1) hashed lookup instead of a linear
scan once a scope has more than 4 bindings (resolve.c3 ~164-181: `if
(s.hash_valid && s.count > 4) { ...hash into s.hash_idx[hslot]... }`).
However, grepping the ENTIRE codebase for `hash_valid` shows exactly 3
occurrences: the struct field declaration, `Resolver.init()` setting
`self.scopes[0].hash_valid = false` (only for the top-level scope, at
program start), and the one read site in `lookup_local`. **`hash_valid` is
never, anywhere, set to `true`.** There is also no function that populates
`hash_idx` (no `rebuild_hash`/`build_hash`/similar — grep confirms zero
write sites to `hash_idx` outside its declaration and the dead read in
`lookup_local`). So the entire "fast hash lookup" branch is unreachable in
practice (since the guard `s.hash_valid` can never legitimately be true) —
this "optimization" is pure dead code; every actual name lookup goes through
the `// Fallback: linear scan for small scopes` path regardless of scope
size. Not a correctness bug by itself (the linear scan is correct), but it
means the documented O(1) fast path (and the design effort that went into
the FNV-hash-based slot computation matching `lookup_local`'s exact hash
recipe) provides zero actual benefit — pure vestigial code.

## Bug 2 (latent, allocator-dependent): `Scope.hash_valid`/`hash_idx` are uninitialized for every scope except scope 0
`Resolver` is heap-allocated via a bare `malloc(resolve::Resolver::size)`
call in `pride.c3` (~line 1205) — NOT zero-initialized (`calloc`/`memset`
would be needed for that). `Resolver.init()` only explicitly zeroes
`hash_valid`/`hash_idx` for `self.scopes[0]` (the single top-level scope
that exists at start). Every OTHER scope — i.e. every scope entered via
`Resolver.push_scope()` for a function body, block, match arm, etc. — is
never initialized: `push_scope()` (resolve.c3 ~117-125) only sets `.count =
0` and `.parent`; it does NOT reset `.hash_valid` or clear `.hash_idx`.
Since bug 1 means `hash_valid` is never intentionally set true, this is
currently harmless in combination — the guard `s.hash_valid && s.count > 4`
reads uninitialized memory for `hash_valid`, and IF that uninitialized byte
happens to be nonzero (entirely possible: heap memory reused from a
previous allocation in the same process, e.g. after AST-arena churn, is not
guaranteed zero, especially for a compiler processing multiple functions/
modules where thousands of `Scope` structs — 256 bytes of `Binding` array
each, 512 x 8-byte `hash_idx`, ~4KB+ per `Scope`, `MAX_SCOPES=256` scopes
statically embedded inside `Resolver` — get reused across `push_scope`/
`pop_scope` cycles) — the "fast path" would activate on top of a `hash_idx`
array that was ALSO never populated for that scope (all its slots being
equally uninitialized garbage, not zero-initialized "empty" sentinels).
This would cause `lookup_local` to walk garbage slot values, comparing
`s.bindings[idx-1]` for effectively random `idx` values — at best returning
"not found" for names that ARE bound in that scope (since the hash indices
don't actually point to the right bindings), causing spurious "duplicate
definition" checks to fail to detect real duplicates (since `dup_is_error`
relies on `lookup_local` correctly finding a same-scope prior binding); at
worst, if a garbage `idx` value happens to be `>= 1` and `idx - 1 <
SCOPE_CAP` by chance, it reads whatever `Binding` happens to occupy that
slot (uninitialized or stale from a previous scope's use of the same memory
address, since `Scope` structs are reused positionally across nested
push/pop cycles at the same stack depth) — a use of uninitialized/stale
data that could misresolve names in rare, hard-to-reproduce, allocator- and
history-dependent ways.
This is CLASSIFIED AS LATENT/LOW-PROBABILITY because bug 1's total absence
of any `hash_valid = true` write means the "fast path" can only trigger via
uninitialized-memory-happens-to-be-nonzero, which is unlikely but NOT
impossible (particularly under AddressSanitizer's poison-on-free behavior,
which the project's own `make asan` target would be well-positioned to
catch — worth specifically fuzzing multi-scope-reentrant programs, e.g. many
sequential function definitions each with >4 local bindings, under
`pryde_asan` to check whether MSan/ASan's uninitialized-read detection
flags this).

## Fix
1. Remove the dead hashed-lookup fast path entirely (simplest — it provides
   no benefit since it's never actually taken), OR
2. Properly implement it: have `push_scope()` initialize `hash_valid = false`
   and zero `hash_idx` for the newly-entered scope (mirroring what `init()`
   already does for scope 0), and add the missing insert-into-hash-table
   logic to `Resolver.bind()` (alongside the existing linear-array append)
   so `hash_idx` is actually populated and `hash_valid` is set true once
   `count` crosses a threshold, so the "fast path" is real. Either way, the
   current state (declared, partially initialized, guarded by a
   never-true-except-by-accident condition) should not ship as-is.
