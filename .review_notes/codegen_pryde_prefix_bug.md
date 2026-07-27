# codegen.c3 — leftover "Pryde" (old project name) byte-check makes the `pride_str_*` runtime-symbol guard permanently dead

`name_is_runtime_decl()` (codegen.c3 ~5064-5079) exists to prevent emitting a
duplicate `declare` line for a function name that's already hardcoded into
the emitted LLVM IR's runtime-declaration preamble (avoiding an LLVM
assembler error from redeclaring a symbol with conflicting/duplicate
signatures). It has a guard for `pride_str_*`-prefixed names:
```c
if (len > 9 && name[0]=='p'&&name[1]=='r'&&name[2]=='y'&&name[3]=='d') { return true; }   // pride_str_* prefix
```
The comment claims this matches the `pride_str_` prefix, but the actual byte
check tests for `p`,`r`,`y`,`d` — i.e. the string **"pryd..."** (matching the
OLD project name "Pryde", per the project's own history/rename, as also
documented in `finds.md` §5's "split-brain directory" finding about the
Pryde→Pride rename leaving stale artifacts) — NOT **"prid..."** (the actual
prefix of the real runtime symbols `pride_str_init`, `pride_str_push_str`,
`pride_str_push_i64`, `pride_str_push_f64` defined in
`runtime/compiler_rt.c` and referenced by `codegen.c3`'s `format!` codegen).
Verified with a byte-by-byte check: `"pride_str_init"[0..3]` = `p,r,i,d` ≠
`p,r,y,d`. **This guard can never match any of the runtime's real
`pride_str_*` symbol names — it is permanently dead code**, a leftover
byte-pattern from before the project was renamed from "Pryde" to "Pride"
that nobody updated when the identifier prefix changed.

## Practical impact (currently low, but real)
Because the guard never fires, if a user (or any future generated/library
code) declares an `extern fn` with `#[extern("pride_str_init")]` (or any
other `pride_str_*` name) pointing at the same symbol the runtime already
provides, `name_is_runtime_decl` will incorrectly return `false`, and
`CgenModule.emit_function`'s extern-handling path will go ahead and emit a
SECOND `declare` line for that symbol — alongside the codegen's own
hardcoded runtime declarations (`declare void @pride_str_init(ptr)` etc., if
those exist in the fixed preamble — worth cross-checking `emit_runtime_decls`
directly) — which would cause a duplicate-symbol assembly failure in
`llvm-as`. This is currently a latent/edge-case bug (most user code doesn't
have any reason to explicitly re-declare an internal runtime symbol by exact
name) rather than something that fails on ordinary programs, but it's a
clear, unambiguous defect: the code's own comment says what it's SUPPOSED to
match, and the literal byte values contradict that comment outright.

## Fix
Change the byte check from `name[2]=='y'` to `name[2]=='i'` (matching
"prid" instead of "pryd"), i.e.:
```c
if (len > 9 && name[0]=='p'&&name[1]=='r'&&name[2]=='i'&&name[3]=='d') { return true; }
```
Given how error-prone these ad-hoc byte-position checks have already proven
to be in this codebase (see also the `concat`/`cobalt` collision bug found
in `parser.c3`), consider replacing this whole family of hand-rolled partial
string matchers with a shared, correct `starts_with(name, len, "pride_str_")`
helper that checks every byte of the expected prefix rather than a hand-picked
subset of index positions.

## UPDATE: fixed architecturally, and a second related bug found+fixed in the same sweep
While refactoring `name_is_runtime_decl` to eliminate the whole "partial
byte-position check" bug class (replacing it with a `span_is()` full-string
comparison helper plus an explicit `RUNTIME_DECL_NAMES` table extracted
directly from `emit_runtime_decls()`'s actual `declare` lines), a SECOND,
previously-undocumented bug was found: the old code claimed `printf` and
`putchar` were "already declared in the hardcoded runtime decl section" (per
its own comment) and skipped emitting a `declare` for any `#[extern("printf")]`
/`#[extern("putchar")]` function — but grepping `emit_runtime_decls()`'s
actual output confirms NEITHER symbol is ever declared there (only
`malloc`/`free`/`realloc`/`calloc`/pthread/libm/etc. — no printf, no
putchar). So any Pride program declaring `#[extern("printf")]` (as the
project's own dead `compiler/stdlib/{bench,test}.pie` files do) would
silently get NO `declare` line at all for that symbol, which — while it
happens to slip past the LLVM assembler for direct calls to an implicitly-
declared external symbol in some configurations — is not correct IR and
would in general fail `llvm-as`/`llc`/`ld.lld` for a genuinely undeclared
external reference. Fixed as part of the same edit: `printf`/`putchar` are
simply removed from the "already declared" table (since they never were),
so a `#[extern("printf")]` function now correctly falls through to the
ordinary extern-declaration codegen path and gets a proper, real `declare`
line synthesized from its Pride-side signature — exactly like any other
extern function.
