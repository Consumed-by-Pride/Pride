# pride.c3 — CRITICAL: main()'s CLI argument parser had multiple flag collisions/dead flags, fully rewritten

## Confirmed via exhaustive simulation of the exact byte-check logic
`main()`'s command-line argument loop used the same "partial byte-position
sniffing" anti-pattern found elsewhere in the codebase (parser.c3's macro-name
detection, codegen.c3's `name_is_runtime_decl`) — but here applied to the
compiler's OWN CLI flags, which I simulated exhaustively in Python against
the literal condition chain transcribed from source:

1. **`--strip` was completely unreachable** — dead flag. Its check
   (`a_len==7 && a_raw[2]=='s' && a_raw[3]=='t' && a_raw[4]=='r' && ...`)
   comes AFTER `--stage`'s check in the if/else-if chain, and `--stage`'s
   check (`a_len==7 && a_raw[0]=='-' && a_raw[1]=='-' && a_raw[2]=='s' &&
   a_raw[3]=='t'`) matches BOTH "--stage" and "--strip" (both are 7
   characters starting with "--st"). Since `--stage`'s branch is tried
   first, every user who typed `--strip` silently got `--stage`'s behavior
   (`dump_stage = true`) instead, and `emit_strip` could never become true.
2. **`--emit-obj` and `--emit-bin` were BOTH completely unreachable** — the
   checks tested the wrong byte indices entirely
   (`a_raw[2]=='e' && a_raw[5]=='-' && a_raw[6]=='o'`) — for the actual
   string "--emit-obj", index 5 is `t` and index 6 is `-`, not `-`/`o` as
   the check expects (verified precisely in Python: `"--emit-obj"[5]` is
   `'t'`, not `'-'`). No possible user input could ever satisfy either
   condition — both flags were 100% dead code from day one, silently
   falling through to being treated as the source-file path argument
   instead (since the final `else if (!found_path)` branch would catch it).
3. Even the constructs that DID technically work relied on checking only a
   handful of byte positions per flag (e.g. `--verify` matched by testing
   just `a_raw[2]=='v'`) — fragile and one edit away from a NEW collision
   (e.g. any future `--v...` flag of length 8 would silently collide).

## Fix: full architectural replacement
Replaced the entire ~100-line if/else-if byte-sniffing chain with:
  - Two new, correct helper functions near the top of `pride.c3`:
    `arg_is(s, slen, literal)` (exact full-string comparison) and
    `arg_starts_with(s, slen, prefix, prefix_len)` (for `--target=`/`--cfg=`/
    `--opt=`/`--emit-llvm [file]`-style flags that carry an inline or
    following value).
  - Every flag dispatch in `main()`'s argument loop now goes through one of
    these two helpers with the flag's FULL literal text, eliminating the
    entire bug class (no more hand-picked byte indices to get wrong, and no
    length-collision between same-length flags is possible since the
    comparison is exhaustive).
  - Verified exhaustively (Python re-simulation of the new dispatch order
    against every one of the compiler's ~26 documented flags): every flag
    now dispatches to itself and only itself, including the two previously
    dead flags (`--emit-obj`, `--emit-bin`) and the previously-shadowed one
    (`--strip`).
This is a genuine functional fix, not just a style cleanup: `--strip`,
`--emit-obj`, and `--emit-bin` are real, documented, user-facing compiler
flags (declared with their own local variables and referenced later in
`main()`'s codegen-invocation logic) that were silently non-functional.
