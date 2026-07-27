# Pride: Promises vs Reality Findings

This document tracks inconsistencies and bugs between the stated promises of the Pride language (in `CAPABILITIES_CHECKLIST.md` and documentation) and the actual implementation.

## 1. Semantic Subtyping Hallucination (Intersections & Unions)
**Promise**: True structural semantic subtyping with Unions (`|`) and Intersections (`&`). The checklist explicitly states: `🔷 ∩ intersection type (parse ok, codegen partial)` and `❌ union type (∪ parse gap; ASCII | accepted but codegen incomplete)`.
**Reality**: 
- `NODE_TYPE_UNION` and `NODE_TYPE_INTERSECT` are successfully parsed and represented in the `typecheck.c3` subtyping lattice.
- However, `ssi_ir.c3` and `codegen.c3` completely drop these nodes on the floor. Neither file handles them. If a union or intersection type makes it out of the type checker, the compiler will panic or ignore it during IR lowering and code generation.

## 2. Multi-Stage Programming (MSP) Leaks
**Promise**: Compile-time staging, `comptime`, and evaluation interleaving smoothly with compilation.
**Reality**:
- `stage.c3` correctly evaluates `NODE_STAGE` and `NODE_EXPR_COMPTIME` nodes.
- **Inconsistency**: If an unresolved `NODE_STAGE` block (e.g. dependent on generic parameters or untracked state) escapes `stage.c3` and reaches LLVM generation, there is no code path in `ssi_ir.c3` or `codegen.c3` to catch or gracefully reject it. The backend will crash.

## 3. Algebraic Effects: Hardcoded Variadic ABI
**Promise**: Native, strongly-typed effect tracking and perform/resume mechanics.
**Reality**:
- The frontend tracking and `IR_EFFECT_OP` IR translation are quite impressive.
- **Inconsistency**: In `codegen.c3` (lines ~4050-4080), the code generator blindly widens sub-i64 integer arguments to make them fit a hardcoded variadic ABI call to `__pride_perform` (`call @__pride_perform(op_id, ...)`). This is a brittle hack that circumvents the type-map and will likely corrupt complex struct arguments or vectors.

## 4. Term Rewriting `MAX_REWRITE_DEPTH` Hack
**Promise**: Turing-complete, first-class AST term rewriting.
**Reality**:
- The engine implements `strat_innermost`, `strat_outermost`, and confluence checking.
- **Inconsistency**: To prevent infinite recursion, `rewrite.c3` forces `MAX_REWRITE_DEPTH = 800`. If a rewrite sequence reaches 800 steps, it silently aborts and returns the partially rewritten AST (`rw.too_deep = true; return t;`). No warning or error is surfaced to the user; the compiler simply proceeds with malformed code.

## 5. The "Split-Brain" Directory Issue
**Major Architectural Bug**: The codebase has two divergent sources of truth for the compiler frontend.
- There is a `compiler/` directory full of `.c3` files (`compiler/codegen.c3`, `compiler/ssi_ir.c3`, etc.).
- There are duplicate `.c3` files directly in the root directory.
- `build.sh` and `Makefile` use the root files. The files in `compiler/` seem to be a ghost version (e.g., `compiler/codegen.c3` is 211KB and references "Pryde", whereas `./codegen.c3` is 296KB and references "Pride").
- Any changes made to the `compiler/` directory are ignored by the build system.

## 6. Operator Overloading IR Generation Bug
**Promise**: Operator overloading via interface dispatch.
**Reality**:
- `ssi_ir.c3` accurately detects operator overload calls and attempts to generate an `IR_CALL`.
- **Inconsistency**: The callee is injected as `IR_UNKNOWN` with its binder pointing to the AST `NODE_DECL_FN`. While `codegen.c3` tries to catch this with `known_fn_ref` logic, the indirection is extremely brittle and bypasses standard function pointer resolution if the impl method isn't monomorphized correctly.

## 7. Deep line-by-line review + real-toolchain verification (this pass)

A follow-up deep-dive review went beyond static reading: a working LLVM 22
toolchain (`clang-22`, `ld.lld`, `llc`, `opt`, `llvm-as`, `llvm-dis`) was
assembled in-sandbox from PyPI wheels (`karellen-llvm-core`,
`karellen-llvm-clang`, `xtc-llvm-tools`) since the official c3c/LLVM release
channels were network-blocked, letting several long-standing bugs be
compiled, run, and cross-checked against independent reference
implementations (Python bignum arithmetic, the reference `xxhash` package)
rather than only reasoned about from source. All of the following were
found AND fixed in this pass:

- **CRITICAL — 128-bit division/modulo silently corrupted data.**
  `runtime/compiler_rt_arch.c`'s `__udivti3`/`__divti3`/`__umodti3`/
  `__modti3` (the compiler-rt intrinsics real LLVM `i128`/`u128` codegen
  calls for division) were declared with 64-bit parameter/return types,
  silently truncating every 128-bit operand to its low 64 bits before
  dividing. Verified empirically: `((u128)64<<64|5)/3` returned `hi=5 lo=0`
  instead of the correct `hi=21 lo=6148914691236517207`. Fixed with a
  manual, self-recursion-safe 128-bit binary long division (naively
  widening the types to `__int128` and using `/` directly causes the
  function to call itself infinitely and stack-overflow immediately — x86-64
  has no hardware 128-bit divide instruction, so GCC/Clang route `__int128 /`
  through this very libcall). Added the missing `__udivmodti4`
  (quotient+remainder combined call). Verified via real `llc`-compiled
  `udiv/urem/sdiv/srem i128` IR linked against the fixed object file,
  cross-checked against Python bignum division.
- **`__pride_xxhash32` produced non-standard hashes for any 16+ byte input**
  — the main 16-byte-stripe loop's required `rotl32(v, 13)` step had been
  collapsed into a no-op `>>0u`. Fixed and verified byte-for-byte against
  the reference `xxhash` PyPI package for a 32-byte test vector.
- **Lexer**: `typeof`/`typeof_unqual`/`nullptr`/`constexpr` keywords were
  dead code (misplaced in the wrong length-bucket of `keyword_type`'s
  switch, so `span_eq` could never match); `+?`/`-?`/`*?` (checked
  arithmetic) were never lexed as single tokens at all, despite the
  checklist claiming this feature "✅ Exec verified"; `σ`/`φ` matched the
  wrong UTF-8 byte sequences; a single-letter char literal (`'a'`, `'x'`,
  `'_'`) was always mislexed as the start of a loop-label reference.
- **Parser**: character literals ALWAYS evaluated to codepoint 0 (the two
  `node_char(...)` call sites hardcoded `0` instead of decoding the token
  text) — every char literal in Pride source silently became NUL; a
  6-letter identifier starting "co" and ending "t" (e.g. a user function
  named `cobalt`) collided with the `concat!` compile-time-macro detection
  and had its call silently replaced with a no-op `Concat` node, due to a
  partial byte-position check that only tested 3 of 6 bytes.
- **CLI (`pride.c3` `main()`)**: the argument parser's byte-sniffing
  `else if` chain made `--strip` permanently dispatch as `--stage` (both
  start `--st`, and `--stage`'s check came first), and made `--emit-obj`/
  `--emit-bin` permanently UNREACHABLE (checked the wrong byte indices
  entirely) — meaning the compiler's native-binary output pipeline
  (`--emit-bin`) could never actually be invoked. Rewrote the whole
  dispatcher to use exact full-string comparison.
- **codegen.c3**: `is_main_fn`/`is_main` name checks (deciding whether to
  emit `@main` vs. a mangled name) matched on as few as 1 of 4 bytes,
  meaning any 4-letter function starting with 'm' would be silently
  renamed to `@main` in the emitted IR; `name_is_runtime_decl`'s "already
  declared, skip re-declaring" guard tested `pryd` instead of `prid`
  (leftover from the Pryde→Pride rename) so it could never match the real
  `pride_str_*` runtime symbols, and separately claimed `printf`/`putchar`
  were "already declared" when neither actually is — any
  `#[extern("printf")]` function was silently dropped with no `declare`
  line at all. Replaced every partial-byte check project-wide with a
  shared exact-match helper (`span_is`/`arg_is`).
- **Effect checker**: `syscall(...)` — the project's own idiomatic (and, in
  the exec-test suite, ONLY) way to perform I/O — carried no effect tag at
  all, so a function calling `syscall(1, 1, buf, len)` with no `! [IO]`
  effect row produced zero diagnostics even under `--strict`, directly
  contradicting the effect checker's own stated "no hidden behavior"
  design goal.
- **Resolver / integrity verifier**: `NODE_DECL_USE` (checked by
  `integrity.c3` and `typecheck.c3`'s cross-module lookup) is a legacy node
  kind the parser never actually constructs — every `use` statement builds
  `NODE_DECL_IMPORT` instead — so `use ... as Alias` and multi-segment
  `use a.b.c` statements tripped false-positive integrity findings and
  silently broke cross-module member resolution through aliases.
- **Build system**: `Makefile`'s `compile`/`runtime` targets and
  `runtime/README.md`'s documented manual build never linked
  `compiler_rt_arch.o` at all and never added `-lgcc`/`-lgcc_s` — both
  required (as `tests/run_exec.sh`'s already-working recipe independently
  confirms) for the 128-bit-division intrinsics above and other
  compiler-generated libcalls; `runtime:`'s `gcc` invocation was also
  missing `-msse4.1`, which the SIMD helpers require to compile at all on
  a strict compiler. Also fixed `conformance/run.sh`/`tests/run_exec.sh`
  referencing a nonexistent `../pride` binary (the real build artifact is
  named `pryde`) — this alone made the conformance harness silently
  produce a misleading pass/fail count.
- Assorted smaller correctness/robustness fixes: `resolve.c3`'s per-scope
  name-lookup hash index was declared but never populated/invalidated
  (dead "fast path", or a latent uninitialized-read hazard on scope-slot
  reuse) — implemented properly with lazy rebuild + invalidate-on-insert;
  `lint.c3`'s unreachable-code check didn't recognize `break`/`continue` as
  diverging; `for i in lo..hi by step` parsed into a dedicated
  `NODE_EXPR_RANGE_STEP` node that no lowering pass ever recognized (fell
  back to a hardcoded step of 1, silently ignoring the user's `by` clause)
  — wired through typecheck/ssi_ir; added type checks for non-integer index
  expressions (`arr[true]`) and out-of-range/negative shift amounts
  (`x << 100`), including the equivalent host-side UB risk in the
  compile-time constant folder (`ast.c3::fold_binary`, which also lacked an
  `INT64_MIN / -1` overflow guard for the same reason).

See `.review_notes/` in this checkout for the full, individually-verified
write-up of every finding above (methodology, reproduction steps, and for
the two runtime bugs, exact toolchain commands and expected-vs-actual
output).

## 8. This session: attempted to obtain the pinned `c3c` v0.8.2 binary; blocked by sandbox network policy

The user added a pre-built `c3c` v0.8.2 toolchain to this workspace via
**Git LFS** (`bin/c3c`, `bin/c3fmt` on `dev`) and, when that path proved
unreachable, via a **GitHub Release asset**
(`toolchain-c3c-0.8.2` → `c3c-0.8.2-linux-x86_64-pride-workspace.tar.gz`,
~40 MB). Both were investigated exhaustively this session:

- **Git LFS**: confirmed the LFS pointer files resolve correctly (via the
  LFS batch API against `github.com/.../info/lfs/objects/batch`, which
  *is* reachable), and produce valid signed download URLs — but every one
  of those URLs points at `*.githubusercontent.com` media-storage hosts
  (`media.githubusercontent.com`, `objects.githubusercontent.com`,
  `github-cloud.githubusercontent.com`, `objects-origin.githubusercontent.com`,
  `gist.githubusercontent.com`, `raw.githubusercontent.com`), and **every**
  one of those hosts fails at the TLS layer from this sandbox
  (`OpenSSL SSL_connect: SSL_ERROR_SYSCALL`, confirmed via direct `curl -v`
  against each, not just an HTTP-level redirect issue) — the exact same
  class of block the previous session already documented for official
  `c3c`/LLVM GitHub *release* downloads.
- **GitHub Releases**: same result — `gh release download`, direct
  `browser_download_url` fetches, and the `api.github.com/.../releases/assets/{id}`
  endpoint (which itself returns HTTP 200 but then 302-redirects to
  `release-assets.githubusercontent.com`) all fail identically. Confirmed
  this is a *general* sandbox network policy, not something specific to
  this repository, by reproducing the identical failure against a
  well-known public repository's release asset (`git-lfs/git-lfs` v3.5.1).
- What *does* work: `github.com`, `codeload.github.com` (plain git blob/
  tarball transfer of **non-LFS** content — confirmed via a full `dev`
  branch tarball fetch, which correctly returned the 134-byte LFS *pointer*
  text for `bin/c3c`, proving the transport itself is fine, just not for
  LFS-backed content), and `api.github.com` for metadata.
- Given this, obtaining the binary bytes into the sandbox would require the
  user to re-host them through a plain (non-LFS, non-Release) git-tracked
  blob or an unaffiliated plain HTTPS host — the user opted instead to have
  this session finalize a PR with the fixes already made rather than pursue
  that further.

**Net effect on this session's methodology**: unchanged from the previous
session's documented limitation — every `.c3` compiler-source fix in this
repository remains verified via careful static/grep-based cross-referencing
rather than by compiling `pride`/`pryde` itself, while the two C runtime
files (`runtime/compiler_rt.c`, `runtime/compiler_rt_arch.c`) remain the
only components that were compiled and executed for real (via the
self-assembled PyPI-wheel-based LLVM/Clang toolchain documented in §7),
which is how the critical i128-division and xxhash32 bugs were found and
proven fixed.
