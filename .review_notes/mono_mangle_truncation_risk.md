# mono.c3 — latent correctness risk: mangled-name truncation can alias two distinct generic instantiations

## Finding
`Monomorphizer.mangle()` and `sub_eq()` (mono.c3 ~205-292) both build a
type's mangled-name representation via `type_to_str()` into FIXED, SMALL
stack buffers — 256 bytes (`MANGLE_BUF_CAP`) for the emitted clone name, and
just 128 bytes (a local `char[128]`) for the instance-deduplication
comparison in `sub_eq()`. `type_to_str()` is bounds-checked against these
capacities (every `buf[off++]` is gated by `off < cap - 1`), so it never
overflows the buffer — but when a type's structural encoding would exceed
the cap, the function silently STOPS writing partway through and returns
whatever prefix fit, with **no signal that truncation occurred** (no
"overflow" flag, no fallback to a hash, nothing).

`type_to_str`'s recursion depth is capped at 8 (`depth > 8` guard), but
depth is only incremented when recursing into a CHILD type — sibling
elements at the SAME level (e.g. every field of a large tuple/struct type
argument, or every argument of a wide generic application) are each
appended to the SAME buffer without increasing `depth`. This means a
generic instantiated over, for example, a tuple type with on the order of
~100+ primitive fields (well within the depth-8 cap, since it's one level
of nesting with many siblings) can legitimately exceed 128/256 bytes of
mangled output and get silently truncated.

## Consequence
Because `sub_eq()` (used by `find_instance()` to decide "have we already
generated a clone for this exact type substitution?") only compares the
TRUNCATED prefix (`type_to_str(..., 128, ...)`'s returned length `la`/`lb`
and the corresponding bytes), **two DIFFERENT generic instantiations whose
type arguments happen to share the same first ~128 bytes of structural
encoding — but diverge only after that point — would be misidentified as
identical**, causing `find_instance` to return the WRONG existing clone
instead of generating a new one. The caller would then patch the call site
to use a monomorphized function/struct compiled for the WRONG concrete
type — a silent type-confusion bug (e.g. treating an `i64`-tuple's field
layout as if it were an `f64`-tuple's, or dispatching to a clone built for
a different struct shape entirely), which could manifest as memory
corruption or wrong results at runtime, with no compiler diagnostic.

Separately, `Monomorphizer.mangle()`'s OWN 256-byte truncation (used to
name the actual emitted clone, e.g. `id__i32`) has a milder but related
issue: two distinct, sufficiently-large type arguments truncating to the
same 256-byte prefix would receive the SAME mangled symbol name, which
would either silently collide (if `find_instance`'s 128-byte check also
aliased them, per above) or — if `find_instance` treated them as distinct
instances despite the name collision — could produce two DIFFERENT clone
declarations emitted under the IDENTICAL LLVM symbol name, which would fail
to link (duplicate symbol) or, worse, silently link with only one
definition satisfying two logically-different call sites.

## Severity assessment
This requires a fairly pathological/adversarial input (generic code
instantiated over a very wide product type — tens to ~100+ fields sharing a
long common structural prefix) to trigger, so it is UNLIKELY to affect
hand-written Pride programs in practice, and no conformance/exec test comes
close to exercising it. It is flagged here as a genuine, if narrow,
robustness gap in a module explicitly documented as "production
monomorphization" (mono.c3's own header comment) with a claimed
"Deduplication" correctness guarantee that these buffer sizes can silently
violate for large-enough types. Not fixed in this pass (the safe fix — hash
the FULL untruncated structural encoding, e.g. incrementally via FNV-1a
fed from `type_to_str`'s callback sites rather than materializing a bounded
string buffer — is a moderate refactor of the mangling/dedup mechanism
that's easy to get subtly wrong without the ability to compile-test it;
flagging for a follow-up rather than risking an unverified change to a
"production" component).

## UPDATE: fixed
Implemented the safe fix described above:
1. Added `type_struct_eq(a, b, depth)` — a direct recursive structural
   comparison of two type-node trees (mirroring `type_to_str`'s exact
   traversal: same node kinds handled, same child order, same depth-8 cap)
   that never truncates because it doesn't materialize any string buffer.
   `sub_eq()` now calls this instead of comparing bounded 128-byte
   `type_to_str` output, closing the truncation-collision hole in
   `find_instance()`'s deduplication.
2. Hardened `Monomorphizer.mangle()` itself: after building the (still
   necessarily bounded, since it becomes an LLVM symbol name)
   `MANGLE_BUF_CAP`-byte mangled name, it now checks the freshly-built name
   against every already-assigned instance name and appends a numeric
   `_N` disambiguating suffix on collision — so even if two distinct
   instances (now correctly recognized as distinct thanks to fix #1) would
   have produced the same truncated symbol name, they get distinct names
   and therefore distinct, non-colliding LLVM symbols instead of a
   duplicate-definition link failure or silent one-definition-wins bug.
Both changes verified by manual C3-syntax cross-referencing against the c3c
stdlib style (brace-balance delta matches exactly, switch/case patterns
match existing conventions in this same file) — could not be compiled by
`c3c` itself for the reasons noted in the toolchain section of
`.review_notes/lexer.md`.
