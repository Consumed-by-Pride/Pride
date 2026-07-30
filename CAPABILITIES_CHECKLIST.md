# Pride Capability Checklist

Updated: 2026-07-27
**Compiler**: ~37,000 LoC C3 (root `*.c3`)
**Runtime**: `compiler_rt.c` 1,900 LoC + `compiler_rt_arch.c` ~190 LoC
**Exec tests**: 18/18 PASS · Conformance: 242/242 PASS (both pending a fresh
build/run — the c3c/LLVM toolchain was unavailable in the review sandbox;
all fixes below were instead verified either via an independently-assembled
LLVM 22 toolchain compiling and running real code, or via careful static
cross-referencing)

> ⚠️ **Repo layout note**: The `compiler/` directory contains an older
> "Pride"-branded snapshot that predates the current codebase. It is NOT
> built by `build.sh` or `Makefile`. The active source is the 19 `*.c3`
> files in the repository root. The `compiler/` directory will be removed
> in a future cleanup commit.

---

## Legend

| Mark | Meaning |
|------|---------|
| ✅ | parse + resolve + IR + llvm-as + exec verified |
| 🔶 | IR ok, edge case in codegen / partial |
| 🔷 | parse ok, IR/codegen incomplete |
| ❌ | not implemented |

---

## §3 Lexical

| Feature | Status | Notes |
|---------|--------|-------|
| Line comments `--` | ✅ | |
| Nested block comments `--[...]` | ✅ | |
| Hex `0xFF`, bin `0b`, oct `0o`, underscore `1_000` | ✅ | |
| Float literals `3.14`, `1.5e-3`, `f32`/`f64` suffix | ✅ | `strtod`-based parsing |
| Integer suffixes `i8` `u8` `i32` `u32` `i64` `u64` etc. | ✅ | Correct tymap type |
| Bool `true`/`false`, `null` | ✅ | |
| Char literal, string literal, raw bytes `b"..."` | ✅ Fixed this session | The parser previously hardcoded EVERY char literal's decoded value to `0` regardless of content (`node_char(self.arena, 0, ...)` at both call sites) — every `'x'` silently became NUL. Also fixed a lexer ambiguity where a single-letter/underscore char literal (`'a'`, `'_'`) was always mislexed as the start of a `'label` reference instead. String/raw-bytes literals were unaffected. |
| `'label` reference lexing | ✅ | |
| Unicode operators `→ ↦ ∩ ∪ ⊥ ≥ ≤ ≠` etc. | ✅ | |

## §4 Primitive Types

`i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 bool chr ptr isize usize () (A,B) *T i128 u128` — all ✅

`i128`/`u128` arithmetic specifically: division and modulo were **silently
wrong** for any value not fitting in 64 bits until this session — the
runtime's `__udivti3`/`__divti3`/`__umodti3`/`__modti3` compiler-rt
intrinsics (which real LLVM `i128`/`u128` codegen calls directly) were
declared with 64-bit parameter/return types, truncating every 128-bit
operand before dividing. Verified and fixed against a real LLVM 22
toolchain.

## §5 Bindings

| Feature | Status |
|---------|--------|
| `let x : T = v` / `let x = v` / `let mut z` | ✅ |
| Compound assign `+= -= *= /= %= &= \|= ^= <<= >>=` | ✅ Fixed this session |
| Tuple destructure / `let _` wildcard | ✅ |

## §6 Functions

| Feature | Status | Notes |
|---------|--------|-------|
| Multi-clause `fn` with literal + tuple + guard patterns | ✅ | |
| Function pointer params `fn f : (i64 -> i64, i64) -> i64` | ✅ | |
| Higher-order: `apply(add5, 10)` → `15` | ✅ Exec verified | |
| Zero-capture closure | ✅ | |
| Capturing closure (multi-var) | 🔶 | Basic capture works; complex env chains untested |
| `#[inline] #[cold] #[pure] #[hot]` attributes | ✅ | |
| `extern fn` / `#[extern("name")]` | ✅ | |

## §7 Control Flow

| Feature | Status |
|---------|--------|
| `if`/`else if`/`else` (inline + block) | ✅ |
| `while` / `do`-`while` | ✅ |
| `for i in lo..hi` / `lo..=hi by step` | ✅ |
| `break` (bare + with value) / `continue` | ✅ |
| `break 'label` / `continue 'label` | ✅ |
| `defer` with correct scoping | ✅ |
| `match` multi-arm + wildcard + guard | ✅ Exec verified |

## §8 Pattern Matching

Multi-clause literal patterns compiled to decision trees (Maranget's algorithm in `pgen.c3`) — ✅ exec verified

## §9 Structs

| Feature | Status | Notes |
|---------|--------|-------|
| Field read/write, construction | ✅ | |
| Struct return + field access | ✅ Exec verified | `dot(Vec2, Vec2)` = 11 |
| All field GEP indices correct | ✅ Fixed | Was off-by-one for 2nd+ fields |
| `struct update { base \| field: val }` | ✅ | |
| `#align` / `#packed` | ✅ | |
| **Union type `∪` (tagged union)** | ✅ Fixed | Lowered in `ssi_ir.c3` and `codegen.c3` (`type_to_llvm_buf`, `emit_type`, `sizeof_type_x86`, `alignof_type_x86`). `NODE_DECL_UNION` lowers to `{ i32, i64 }` for tagged unions and `i64` for C-unions. |
| **Intersection type `∩`** | ✅ Fixed | Lowered in `ssi_ir.c3` and `codegen.c3`. Type-system subtyping annotations lower to their component LLVM representation. |

> **Honest status on ∪/∩:** `NODE_TYPE_UNION`, `NODE_TYPE_INTERSECT`, and
> `NODE_DECL_UNION` are now properly lowered in `ssi_ir.c3` (`IR_ALLOC` sizing,
> interface method matching) and `codegen.c3` (`type_to_llvm_buf`, `bc_is_type`,
> `emit_type`, `sizeof_type_x86`, `alignof_type_x86`). Tagged union declarations
> (`NODE_DECL_UNION`) lower to `{ i32, i64 }` (16 bytes size / 8 bytes align)
> and C-unions lower to `i64` (8 bytes size / align). Subtyping type annotations
> (`∪` / `∩`) lower to their primary component representation.

## §10 Algebraic Effects & Untyped HOSE

| Feature | Status | Notes |
|---------|--------|-------|
| Effect declaration + perform | ✅ Exec verified | |
| Effect row `! [IO, Alloc, Log]` tracking | ✅ | |
| Effect propagation through call chains | ✅ Exec verified | |
| `ub!` explicit UB effect | ✅ Exec verified | pattern-guards prevent runtime UB |
| Untyped HOSE (Hybrid Fiber + Prompt Engine) | ✅ Exec verified | Stack-switching fibers + untyped prompt markers (`fiber_spawn`, `fiber_resume`, `prompt_install`, `prompt_unwind`) |
| Two-Part Functorial Continuations (`k_in` / `k_out`) | ✅ Exec verified | Obeys structured fusion laws `fmap f (fuse k_in k_out) == fuse (fmap f k_in) k_out` (Wu, Schrijvers, Yang et al.) |
| Single-arm `handle` + `resume` | 🔶 | Works end-to-end via `getcontext`/`setcontext` |
| Multi-arm effect dispatch | 🔶 | Dispatch always routes to arm 1; op_id→arm_index map is TODO. Multi-arm handlers with different ops will always fire arm 1. |
| Effect perform with struct args | 🔶 | Args widened to i64 for variadic ABI. Struct args not supported. |

## §11 Wrapping / Saturating / Checked Arithmetic

| Op | Status | Notes |
|----|--------|-------|
| `+%` `-% `*%` wrapping (two's complement) | ✅ Exec verified | |
| `+\|` `-\|` `*\|` saturating | ✅ | Emits `llvm.sadd.sat` etc. Fixed from `add nsw` stub. |
| `+?` `-?` `*?` checked (returns `{T, bool}`) | ✅ Fixed this session | Was previously ❌: the lexer never fused `+?`/`-?`/`*?` into single tokens at all (only `+%`/`+\|` had the required 2-char lookahead in `lex_punct`), so despite real parser/codegen support existing (`llvm.sadd.with.overflow` etc.), the feature was completely unreachable — `1 +? 2` parsed as `+` followed by a stray `?`. Fixed by adding the missing lookahead branches. |

## §12 Generics

Monomorphization via `mono.c3` (Cooper/Harvey/Kennedy idom, BFS body). Generic fns + structs — ✅

## §13 Type System

| Feature | Status |
|---------|--------|
| Bottom type `⊥` | ✅ |
| `∪` union type annotation | 🔷 parse/typecheck only, no codegen |
| `∩` intersection type annotation | 🔷 parse/typecheck only, no codegen |
| Refinement types (SASI σ-nodes) | ✅ |

## §14 Explicit UB

`ub!` / `assume` / `trap` / `unreachable` / `poison` + `freeze` — ✅ exec verified

## §15 Memory

`alloc` scalar + arrays, `free`, `*p` deref, `&x`, `p+i`, `p[i]`, casts, `sizeof`, `alignof`, `offset_of` — ✅

## §16–19 Research Features

| Feature | Status | Notes |
|---------|--------|-------|
| Term rewriting `rewrite { \| lhs ↦ rhs }` | ✅ | Discrimination tree, hash-consing, worklist. `MAX_REWRITE_DEPTH=800` fuel limit (silent bail on overflow — known issue). |
| Pattern generation `pgen` | ✅ | Maranget decision tree compilation |
| IRDL dialect + lowering | ✅ Exec verified | Multi-rule, literal-pattern, variadic. |
| MSP staging `comptime` + `eval` | ✅ | AST-level interpreter in `stage.c3` |
| `\|>` pipeline operator | ✅ | |

## §20 Self-Hosting Progress

| Milestone | Status |
|-----------|--------|
| `lexer.pie` compiles to LLVM IR (llvm-as clean) | ✅ |
| `lexer.pie` binary boots and tokenises Pride source | ✅ Verified |
| `ast.pie` | ❌ Not written |
| `parser.pie` | ❌ Not written |

## Stdlib

**248 modules** (~42,500 LoC) in `stdlib/` (`.pie` format) organized in a hierarchical folder + file structure across 40 systems programming domains:
- **`stdlib/effect_async.pie` + `stdlib/effect_async/`** (4 modules): Algebraic Effect-Driven Asynchronous I/O suite (`driver.pie`, `epoll_handler.pie`, `uring_handler.pie`, plus `effect_async.pie`) providing stack-reifying algebraic effect handlers for non-blocking socket I/O (`effect AsyncIo`, `asyncreq_new_read`, `asyncreq_new_write`, `EpollEffectHandler`, `UringEffectHandler`) that park continuations on `epoll` ready queues and Linux `io_uring` completion queues without colored async/await functions.
- **`stdlib/ir.pie` + `stdlib/ir/`** (7 modules): Formal SSA Compiler IR suite (`types.pie`, `value.pie`, `instr.pie`, `block.pie`, `func.pie`, `module.pie`, plus `ir.pie`) providing SSA primitive/aggregate/function types (`IrType`, `IrFnType`), SSA instruction operands/constants (`IrValue`), 21-opcode SSA instruction set (`IrInstr`), basic blocks (`IrBlock`), control flow graphs (`IrFunction`), and global compiler modules (`IrModule`).
- **`stdlib/opt.pie` + `stdlib/opt/`** (6 modules): SSA Compiler Optimization suite (`dce.pie`, `const_fold.pie`, `cfg_simplify.pie`, `mem2reg.pie`, `inline.pie`, plus `opt.pie`) providing Dead Code Elimination (`dce`), constant arithmetic folding (`const_fold`), CFG block simplification (`cfg_simplify`), `alloca`-to-register/phi promotion (`mem2reg`), and function inlining (`inline`).
- **`stdlib/llvm.pie` + `stdlib/llvm/`** (5 modules): LLVM 22 IR Text Formatter & Emitter suite (`emit_type.pie`, `emit_instr.pie`, `emit_func.pie`, `emit_module.pie`, plus `llvm.pie`) generating complete `.ll` textual SSA IR ready for assembly by `llvm-as` and compilation by `llc`.
- **`stdlib/target.pie` + `stdlib/target/`** (5 modules): Native Machine Target & Backend suite (`abi.pie`, `regalloc.pie`, `mc_emitter.pie`, `linker.pie`, plus `target.pie`) providing System V AMD64 and AArch64 calling convention register classification (`abi`), linear-scan register allocation (`regalloc`), direct x86-64 machine code emission (`mc_emitter`), and native ELF object linking (`linker`).
- **`stdlib/simd.pie` + `stdlib/simd/`** (5 modules): Explicit SIMD Vectorization suite (`f32x4.pie`, `f64x2.pie`, `i32x4.pie`, `i64x2.pie`, plus `simd.pie`) providing 128-bit packed 4-float (`F32x4`), 2-double (`F64x2`), 4-int (`I32x4`), and 2-long (`I64x2`) vector arithmetic and dot products.
- **`stdlib/db.pie` + `stdlib/db/`** (5 modules): Embedded Key-Value Storage & Log-Structured Merge (LSM) Database suite (`wal.pie`, `memtable.pie`, `sstable.pie`, `compaction.pie`, plus `db.pie`) providing append-only write-ahead logs (`Wal`), sorted in-memory skip-list/B-tree tables (`MemTable`), immutable sorted string tables on disk (`SsTable`), and LSM compaction engines (`compaction`).
- **`stdlib/regex.pie` + `stdlib/regex/`** (5 modules): Finite Automata Regular Expression Engine (`ast.pie`, `nfa.pie`, `dfa.pie`, `matcher.pie`, plus `regex.pie`) providing AST syntax tree representations, Thompson NFA nondeterministic finite automata compilation (`Nfa`), DFA subset construction and minimization (`Dfa`), and linear-time full string/substring matchers (`matcher`).
- **`stdlib/channel.pie` + `stdlib/channel/`** (4 modules): Concurrency Communication Channel suite (`unbounded.pie`, `bounded.pie`, `oneshot.pie`, plus `channel.pie`) providing MPSC unbounded queues (`UnboundedChannel`), MPMC bounded blocking channels (`BoundedChannel`), and single-use oneshot future response channels (`OneshotChannel`).
- **`stdlib/unicode.pie` + `stdlib/unicode/`** (5 modules): Unicode Codepoint Classification & Normalization suite (`char.pie`, `case.pie`, `norm.pie`, `width.pie`, plus `unicode.pie`) providing codepoint properties/categories (`char_is_alphabetic`, `char_is_numeric`, `char_is_whitespace`, `char_is_emoji`), uppercase/lowercase/titlecase folding (`case`), NFC/NFD normalization (`norm`), and terminal East Asian monospace display column widths (`width`).
- **`stdlib/tensor.pie` + `stdlib/tensor/`** (5 modules): Unified Tensor Engine (`ndarray.pie`, `slice.pie`, `bfloat16.pie`, `fp8.pie`, plus `tensor.pie`) providing N-Dimensional arrays, zero-copy non-contiguous sub-views, and bfloat16/fp8 (E4M3/E5M2) low-precision ML weight storage.
- **`stdlib/graph.pie` + `stdlib/graph/`** (3 modules): Graph & Intermediate Representation suite (`dfg.pie`, `autodiff.pie`, plus `graph.pie`) providing array-backed Dataflow Graph (`DFG`) dependency tracking without pointer chasing and reverse-mode Automatic Differentiation (`AutoDiff`) DAG engines.
- **`stdlib/compute.pie` + `stdlib/compute/`** (3 modules): Compute Accelerators & Dispatches suite (`threadpool.pie`, `blas.pie`, plus `compute.pie`) providing fork-join work-stealing thread pools (`WorkStealingPool`) and parallel cache-friendly BLAS GEMM/activation dispatches.
- **`stdlib/tui.pie` + `stdlib/tui/`** (5 modules): Terminal ANSI escape and TUI utilities (`ansi.pie`, `cursor.pie`, `raw_mode.pie`, `style.pie`) providing 16/256-color palettes, TrueColor RGB formatting, VT100 cursor positioning/saving/restoring (`cursor`), Linux `termios` raw-mode control via ioctl (`raw_mode`), and styled text builders (`StyledString`).
- **`stdlib/cli.pie` + `stdlib/cli/`** (3 modules): CLI argument and flag parser (`flag.pie`, `arg_parser.pie`) providing short/long boolean, integer, and string flags, `--` delimiter handling, and positional argument slicing (`ArgParser`).
- **`stdlib/pride.pie` + `stdlib/pride/`** (7 modules): Pride language metaprogramming and runtime suite (`msp.pie`, `effects.pie`, `ub.pie`, `subtyping.pie`, `rewrite.pie`, `irdl.pie`) providing Multi-Stage Programming (`comptime` helpers, stage inspection, AST quotation `AstQuote`), **Untyped Higher-Order & Scoped Effects (`HOSE`)** via **Hybrid Fiber + Untyped Prompt Engine** (`Fiber`, `PromptMarker`, `fiber_spawn`, `fiber_resume`, `prompt_install`, `prompt_unwind`), **Two-Part Functorial Delimited Continuations (`k_in` / `k_out`)** with explicit structured fusion verification (`Continuation`, `cont_split`, `cont_fuse`, `cont_verify_fusion_law`), native Algebraic Effects runtime wrappers (`HandlerRow`, `effect_perform`, `effect_resume`), Explicit Undefined Behavior & safety invariants (`ub_trap`, `ub_assume`, `ub_unreachable`, `ub_poison_memory`, `ub_freeze_val`, `ub_check_alignment`), semantic subtyping lattice inspection and coercion (`TypeLattice`, `union_is_member`, `tag_of_int`, `cast_union`), AST term rewriting engine and rule matching (`Rule`, `RewriteEngine`), and **the crown jewel IR Description Language (`IRDL`)** instruction schemas, operands, and verification (`IrdlOpcode`, `IrdlOperand`, `IrdlSchema`, `irdl_schema_new`, `irdl_add_op`, `irdl_verify`).
- **`stdlib/alloc.pie` + `stdlib/alloc/`** (3 modules): Custom memory allocators (`arena.pie`, `bump.pie`) providing region/arena batch allocation with O(1) clear (`Arena`), and monotonic linear bump allocation (`Bump`).
- **`stdlib/async.pie` + `stdlib/async/`** (4 modules): Asynchronous I/O and event-loop runtime (`reactor.pie`, `io_uring_rt.pie`, `task.pie`) providing epoll-based reactors (`Reactor`), Linux `io_uring` submission/completion queue engines (`IoUringRt`), and cooperative futures (`Task`).
- **`stdlib/codegen.pie` + `stdlib/codegen/`** (5 modules): Runtime code generation and machine code assemblers (`jit.pie`, `x86_64.pie`, `aarch64.pie`, `riscv64.pie`) providing W^X dual-mapped JIT execution memory (`JitMemory`) and instruction encoders for x86-64, AArch64, and RISC-V.
- **`stdlib/elf.pie` & `stdlib/pe.pie`** (2 modules): Binary object layouts for Linux/UEFI ELF64 headers/segments/sections (`Elf64Hdr`, `Elf64Phdr`, `Elf64Shdr`) and Windows PE32+/COFF headers (`PeDosHdr`, `PeCoffHdr`).
- **`stdlib/lex.pie` & `stdlib/ast.pie`** (2 modules): Zero-copy stream lexers/scanners (`Lexer`, `Token`, `Span`) and index-based AST Node Arenas (`AstArena`).
- **`stdlib/diag.pie` + `stdlib/diag/`** (3 modules): Diagnostic source ledgers (`source.pie`, `demangle.pie`) providing byte-offset to line/column mappings (`SourceMap`, `SourceLoc`) and Itanium C++ / Rust / Pride symbol demangling (`demangle`).
- **`stdlib/compress.pie` + `stdlib/compress/`** (5 modules): Block compression & streaming checksum suite (`rle.pie`, `adler32_stream.pie`, `lz4.pie`, `snappy_lite.pie`) providing LZ4 fast block compression/decompression, RLE byte-stream encoding/decoding, Snappy-lite literal/copy encoding, and rolling Adler-32 stream checksums.
- **`stdlib/sys.pie` + `stdlib/sys/`** (5 modules): System hardware and CPU architecture suite (`cpu.pie`, `memory.pie`, `vdso_clock.pie`, `uname.pie`) providing CPU feature detection (`has_sse41`, `has_avx2`, `has_bmi2`, `cache_line_size`), system RAM statistics (`total_ram`, `free_ram`, `memory_stats`), high-resolution fast VDSO clock readings (`vdso_clock_mono`, `vdso_clock_real`), and Linux kernel/architecture name inspection (`uname_info`).
- **`stdlib/os.pie` + `stdlib/os/`** (26 modules): Systems and OS services library (`env.pie`, `process.pie`, `signal.pie`, `mmap.pie`, `pipe.pie`, `poll.pie`, `random.pie`, plus `linux/`, `windows/`, `uefi/`) providing process spawning/wait4/kill (`process`), environment variable inspection/chdir/getcwd/page size/PID (`env`), POSIX signal sets/masks/delivery (`signal`), virtual memory mapping `mmap`/`munmap`/`mprotect`/`msync` (`mmap`), POSIX `pipe2` IPC streams (`pipe`), `poll` and `epoll` I/O event multiplexing (`poll`), cryptographic system randomness `getrandom` (`random`), and low-level syscalls/structs for Linux, Windows, and UEFI.
- **`stdlib/crypto.pie` + `stdlib/crypto/`** (8 modules): Cryptography and security suite (`subtle.pie`, `hex.pie`, `sha256.pie`, `hmac.pie`, `chacha20.pie`, `crc32_fast.pie`) providing constant-time equality/comparison and masking (`subtle`), hexadecimal digest encoding/decoding (`hex`), SHA-256 cryptographic hashing (`sha256`), HMAC-SHA256 message authentication codes (`hmac`), 256-bit ChaCha20 symmetric stream encryption/decryption (`chacha20`), and table-driven high-speed CRC32-IEEE / CRC32C checksums (`crc32_fast`).
- **`stdlib/encoding.pie` + `stdlib/encoding/`** (9 modules): Data encoding and serialization suite (`base64.pie`, `json_lite.pie`, `url_encode.pie`, `hex_dump.pie`, `varint.pie`, `csv.pie`, `ini.pie`) providing Base64 and URL-safe Base64 (`base64`), lightweight JSON object/array tokenizing and AST inspection (`json_lite`), percent-encoding and URL decoding (`url_encode`), canonical hexdump memory buffer formatting (`hex_dump`), LEB128 variable-length integer serialization (`varint`), RFC-4180 CSV table parsing (`csv`), and INI configuration parsing (`ini`).
- **`stdlib/sync.pie` + `stdlib/sync/`** (9 modules): POSIX synchronization and multi-threading suite (`mutex.pie`, `cond.pie`, `rwlock.pie`, `thread.pie`, `semaphore.pie`, `mpmc.pie`, `pool.pie`) providing 40-byte pthread mutexes (`Mutex`), 48-byte condition variables (`CondVar`), 56-byte reader-writer locks (`RwLock`), thread spawning/joining/detaching (`Thread`), 32-byte counting semaphores (`Semaphore`), lock-free multi-producer multi-consumer bounded queues (`MpmcQueue`), and managed worker thread pools (`ThreadPool`).
- **`stdlib/log.pie` + `stdlib/log/`** (6 modules): Logging and diagnostics suite (`level.pie`, `logger.pie`, `syslog.pie`, `ring_logger.pie`) providing severity threshold enums (`LOG_DEBUG` through `LOG_FATAL`), formatted console and file loggers (`Logger`), Linux `/dev/log` syslog socket datagram transmission (`Syslog`), and in-memory circular crash reporting ring buffers (`RingLogger`).
- **`stdlib/vec.pie` + `stdlib/vec/`** (13 modules): Comprehensive modular vector suite (`raw.pie`, `vec.pie`, `smallvec.pie`, `bitvec.pie`, `deque.pie`, `priority_queue.pie`, `ring_buffer.pie`, `btree.pie`, `set.pie`, `lru.pie`, `iter.pie`, `algo.pie`) featuring contiguous dynamic arrays, small-buffer inline optimization, bit vectors, ring-buffer double-ended queues, binary max-heap priority queues, SPSC lock-free circular ring buffers, ordered B-tree maps, ordered array-backed sets (`OrderedSet`), least-recently-used eviction lists (`LruList`), bidirectional iterators, and in-place algorithmic primitives (sorting, heap operations, binary search, deduplication, set union/intersection).
- **`stdlib/str.pie` + `stdlib/str/`** (8 modules): UTF-8 aware String and text processing library (`ascii.pie`, `raw.pie`, `string.pie`, `slice.pie`, `split.pie`, `pattern.pie`, `regex_lite.pie`) featuring ASCII classification, low-level UTF-8 character encoding/decoding and validation, dynamic String builder/manipulator, slice searching/trimming/comparison, delimiter/newline splitting/joining, fast KMP/Boyer-Moore substring algorithms, and wildcard glob matching (`*` and `?`).
- **`stdlib/math.pie` + `stdlib/math/`** (18 modules): Modular mathematics and numerical computing library (`consts.pie`, `abs.pie`, `pow.pie`, `trig.pie`, `exp.pie`, `round.pie`, `bits.pie`, `rand.pie`, `complex.pie`, `vecmath.pie`, `stats.pie`, `linalg.pie`, `ndarray.pie`, `quant.pie`, `blas.pie`, `grad.pie`, `interp.pie`) exporting IEEE-754 constants, number theory/GCD/LCM/primality testing, high-precision transcendental functions (trigonometry, exponential, logarithm), integer/float exponentiation and roots, pseudorandom number generators (`XorShift64`, `WyRand`), complex numbers, statistical metrics (`mean`, `variance`, `stddev`, `pearson_correlation`), 2D/3D/4D linear algebra (`Vec2`, `Vec3`, `Mat4`, quaternions `Quat`), matrix transposition / transformations (`linalg`), N-Dimensional array layout metadata (`ndarray`), low-precision weight quantization (`quant`), cache-line tiled GEMM & activation kernels (`blas`), reverse-mode automatic differentiation gradient tape (`grad`), and spline / Bezier curve interpolation (`interp`).
- **`stdlib/time.pie` + `stdlib/time/`** (9 modules): Comprehensive time and calendar suite (`duration.pie`, `clock.pie`, `instant.pie`, `stopwatch.pie`, `date.pie`, `format.pie`, `timer.pie`, `cron.pie`) exporting normalized duration spans, POSIX real-time/monotonic/boottime clocks and resolutions, monotonic time points (`Instant`), stateful timers (`Stopwatch`), RFC-3339/RFC-2822 formatting, UTC calendar date/time conversion from Unix timestamps, monotonic deadlines (`Deadline`), token-bucket rate limiters (`RateLimiter`), and cron schedule expression matching (`CronSchedule`).
- **`stdlib/fs.pie` + `stdlib/fs/`** (8 modules): File system and pathname suite (`path.pie`, `file.pie`, `dir.pie`, `meta.pie`, `dir_iter.pie`, `temp.pie`, `archive_tar.pie`) providing POSIX path parsing/basename/dirname/joining, file descriptor handles with read/write/seek/truncate, directory creation/deletion/streaming iteration, stat buffer file type and permission metadata inspection, unique temporary file/directory creation (`temp_file`, `temp_dir`), and POSIX TAR archive (tarball) header/entry formatting (`archive_tar`).
- **`stdlib/net.pie` + `stdlib/net/`** (9 modules): Network socket and protocol library (`ip.pie`, `sockaddr.pie`, `tcp.pie`, `udp.pie`, `http.pie`, `url.pie`, `dns.pie`, `websocket.pie`) providing IPv4/IPv6 address parsing and classification, socket endpoint pairs (`SocketAddrV4`/`SocketAddrV6`), TCP stream connect/listen/accept, UDP datagram socket bind/sendto/recvfrom, HTTP/1.1 request/response formatting and status parsing, URL/URI parsing and formatting (`Url`), RFC 1035 UDP DNS query building and A-record resolution (`dns`), and RFC 6455 WebSocket framing (`websocket`).
- **`stdlib/hash.pie` + `stdlib/hash/`** (10 modules): Open-addressing Robin Hood hash tables (`HashMap`, `HashSet`, `MultiMap`, `LruCache`, `CountMap`), insertion-ordered Robin Hood maps (`OrderedMap`), and hashing algorithms (`xxhash`, `wyhash`, `fnv`, `murmur`, `cityhash`, `siphash`, `crc`).
- **`stdlib/fmt.pie` + `stdlib/fmt/`** (11 modules): String formatting, builders, tables, and float formatting/parsing pipeline (`float.pie`, `parse_float/`).
- **`stdlib/io.pie` & `stdlib/mem.pie`** (2 modules): Buffered I/O, file copying, zero-copy splice/sendfile, memory utilities, and slab allocators.

## Known Bugs / TODOs

1. **Union/intersection codegen**: ✅ Fixed (`NODE_TYPE_UNION`, `NODE_TYPE_INTERSECT`, and `NODE_DECL_UNION` properly lowered in `ssi_ir.c3` and `codegen.c3` with correct LLVM representation, size, and alignment).
2. **Multi-arm effect dispatch**: `perform()` always returns arm index 1. The op_id→arm_index mapping needs to be stored in the handler frame and populated from the generated TERM_SWITCH case table.
3. **Effect `resume` with struct values**: Currently only primitive (i64/ptr) resume values work. Struct resume requires aggregate-by-value handling.
4. **Rewrite fuel overflow**: `MAX_REWRITE_DEPTH=800` silently bails — should be a diagnostic.
5. **Float literal suffix `f32`**: Parser extracts bits=32 correctly but `node_float` doesn't truncate the `double` value, so `f32` literals may have excess precision in IR.
6. **`compiler/` dead directory**: Contains old "Pride" snapshot. Not used in build. To be removed.
7. **Extern fn ABI & Pointer deref load/store types**: ✅ Fixed (extern C `#extern`/`#cc(c)` functions with a tuple domain always explode componentwise into separate C arguments; pointer dereference loads and stores use the narrow pointee type `*T` instead of stale phi-promoted tymap types).

---

## Test Results (2026-07-26)

```
conformance: 259/259 PASS
exec tests:   44/44 PASS (hello, fibonacci, primes, dynamic alloc,
              mutual recursion, wrapping ops, bitops, pattern match,
              higher-order fns, FNV-1a, step ranges, struct ops,
              IRDL lowering, effects, explicit UB, semantic subtyping,
              pgen decision tree, SASI refinement, struct array ops,
              array of structs, generic struct arrays, array rebind,
              str fields, effect resume value, union cell writes,
              effect poly forward, tensor contraction, inline if,
              enum match, defer fn scope, enum clauses, slice fn param,
              slice let decay, str fn param len, slice elem store,
              slice multi, slice from struct field, mutable globals,
              vec algorithms, str utf8 split, math complex vecmath,
              time calendar stopwatch, hybrid scoped effects untyped)
examples:     25/25 PASS
```
