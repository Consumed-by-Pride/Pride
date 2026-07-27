# runtime/compiler_rt.c — CRITICAL, VERIFIED BUG: __pride_xxhash32() produced non-standard hashes for any 16+ byte input

## Confirmed via actual compilation + execution (using a real LLVM 22 clang
## toolchain obtained for this review — see toolchain notes) and cross-checked
## against the reference `xxhash` Python library

`__pride_xxhash32()`'s main 16-byte-stripe processing loop was supposed to
implement the standard xxHash32 "round" function:
```
v += input * PRIME2;
v = rotl32(v, 13);
v *= PRIME1;
```
but the actual code collapsed the rotate-left-by-13 into a shift-right-by-
ZERO (a complete no-op), evidently a botched transcription:
```c
v1 = ((v1+(t*P2)>>0u)*P1);   // BUG: >>0u does nothing; rotate step is missing
```
This compiles and runs without crashing (it's valid C, just semantically
wrong), so it was never caught by any test — but the function silently
produced a completely different, non-standard 32-bit value for every input
of 16 bytes or more, while still matching the correct xxHash32 output for
shorter inputs (which don't touch this loop). This makes the "xxHash32"
label a lie for any real-world-sized input: any other implementation,
language, or system that also claims to implement xxHash32 would compute a
*different* hash for the same bytes, defeating the entire point of naming it
after and claiming compatibility with a standardized, cross-language,
cross-platform algorithm (used for things like file integrity checks,
content-addressed caching, and network protocol checksums, where hash
agreement across independently-written implementations is the only reason
to pick a named standard algorithm over an ad hoc one).

## Fix, and verification methodology
Restored the correct `rotl32(v, 13)` step:
```c
v1 += t * P2; v1 = (v1 << 13) | (v1 >> 19); v1 *= P1;
```
(and identically for v2/v3/v4).

**This is the first bug fix in this entire review that was verified by
actually compiling and running real code**, made possible by assembling a
working LLVM 22 toolchain in this sandbox from PyPI wheels (`karellen-llvm-
core`, `karellen-llvm-clang` — see `.review_notes/toolchain.md`), since the
official `c3c`/LLVM release channels were network-blocked. I wrote a
standalone C reproduction of both the buggy and fixed `__pride_xxhash32`,
confirmed the buggy version's short-input path (<16 bytes) already matched
known xxHash32 test vectors (`xxh32("")=0x02CC5D05`, `xxh32("a")=0x550D7456`,
`xxh32("abc")=0x32D153FF` — all reproduced exactly), then confirmed the FIXED
version's long-input path (32-byte buffer of `0x00..0x1F`, seed 0) produces
`0x830741C1`, which is an EXACT match against the independent reference
`xxhash` PyPI package's `xxhash.xxh32(bytes(range(32)), seed=0)` — also
`0x830741c1`. This is a fully independently cross-validated fix, not just a
plausible-looking patch.

## Where this is used
`__pride_xxhash32` is declared as a lang-item hash primitive in the runtime
(`runtime/README.md` / `compiler_rt.c` §headers list it under "Hash
functions (non-cryptographic)" alongside FNV-1a), intended to back Pride's
`stdlib/hash/xxhash.pie` module (referenced in the stdlib module list). Any
Pride program using the stdlib xxHash binding for content hashing,
deduplication, or any interop scenario expecting real xxHash32 compatibility
was silently getting a different, incompatible hash for every input of 16+
bytes — the single most common case for a hash function in practice (short
strings under 16 bytes are the unusual case).
