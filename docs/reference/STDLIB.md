# Pride Standard Library

**Location:** `stdlib/` (257 `.pie` files across 40+ module trees)

**Status:** All stdlib files compile to valid LLVM IR.  Cross-module `use`
imports do not function at runtime — the compiler is single-file.  Stdlib
modules are currently useful as **reference implementations and copy-paste
sources**, not as a linked library.

---

## Architecture Constraint: Single-File Compiler

Pride currently compiles **one `.pie` file at a time**.  There is no
linker-level module system for `.pie` files.  The `use module.sub` declaration
is parsed and (partially) resolved, but the referenced module's source is not
automatically loaded and compiled.

**Consequence:** To use stdlib code in a `.pie` file you currently have two
options:

1. **Copy the relevant functions into your file** — the approach used in all
   exec tests and examples.
2. **Wait for the module loader** — not yet implemented; see Roadmap.

---

## Module Inventory

### `stdlib/pride/` — Compiler-internal metaprogramming

| Module | What it provides | Status |
|---|---|---|
| `pride.effects` | Extern bindings to all `__pride_*` C runtime symbols | ✅ Working |
| `pride.msp` | CMTT box, stage stack, quote table, staged eval | ✅ Working |
| `pride.irdl` | IRDL opcode IDs and schema registry | ✅ Working |
| `pride.ub` | Explicit UB traps, alignment checks, poison registry | ✅ Working |
| `pride.rewrite` | Term rewriting engine + Robinson unification | Compiles; not wired |
| `pride.subtyping` | Subtype relation structs | Compiles; not wired |

### `stdlib/vec/` — Collections

| Module | What it provides |
|---|---|
| `vec.vec` | Growable `Vec` (heap-allocated, `elem_size`-parameterized) |
| `vec.smallvec` | Inline-storage SmallVec (stack-avoids-heap for small N) |
| `vec.bitvec` | Bit vector with popcount, flip, AND/OR/XOR operations |
| `vec.deque` | Ring-buffer VecDeque |
| `vec.btree` | B-tree (bulk ops) |
| `vec.collections` | VecDeque + BinaryHeap (max-heap) |
| `vec.set` | Hash-based set |
| `vec.lru` | LRU cache |
| `vec.ring_buffer` | Fixed-capacity ring buffer |
| `vec.priority_queue` | Binary heap priority queue |
| `vec.algo` | Sorting, binary search, partitioning |
| `vec.iter` | Iterator protocol adapters |
| `vec.raw` | Raw pointer array utilities |

### `stdlib/hash/` — Hash functions and maps

| Module | What it provides |
|---|---|
| `hash.map` | Robin Hood open-addressing `HashMap<i64,i64>` |
| `hash.ordered_map` | Ordered map (sorted by key) |
| `hash.fnv` | FNV-1a 32/64-bit |
| `hash.xxhash` | xxHash32 (correct rotl32 implementation) |
| `hash.murmur` | MurmurHash3 |
| `hash.siphash` | SipHash-2-4 |
| `hash.cityhash` | CityHash64 |
| `hash.crc` | CRC-32 |
| `hash.auto_hash` | Selects best hash for input size |
| `hash.wyhash` | WyHash |

### `stdlib/str/` — Strings

| Module | What it provides |
|---|---|
| `str.string` | Growable UTF-8 `String` (push_byte, push_char, push_slice) |
| `str.ascii` | ASCII predicates and transforms |
| `str.split` | Split by delimiter, whitespace, lines |
| `str.pattern` | KMP pattern search |
| `str.slice` | Slice views (non-owning) |
| `str.regex_lite` | NFA-based regex (no backtracking) |
| `str.raw` | Raw byte operations |

### `stdlib/math/` — Mathematics

| Module | What it provides |
|---|---|
| `math.abs` | Absolute value, signum |
| `math.trig` | sin, cos, tan, atan2, etc. (wraps libm) |
| `math.exp` | exp, log, log2, log10, pow |
| `math.pow` | Integer exponentiation |
| `math.round` | floor, ceil, round, trunc |
| `math.consts` | π, e, √2, etc. |
| `math.complex` | Complex number arithmetic |
| `math.vecmath` | SIMD-friendly 2/3/4-component vector math |
| `math.linalg` | Matrix multiply, transpose, determinant |
| `math.ndarray` | N-dimensional arrays |
| `math.stats` | mean, variance, stddev, percentile |
| `math.rand` | xoshiro256** PRNG |
| `math.bits` | Bit operations (popcount, clz, ctz — with C23/builtin fallbacks) |
| `math.blas` | BLAS-style dense linear algebra |
| `math.interp` | Linear/cubic interpolation |
| `math.grad` | Numerical gradient |
| `math.quant` | Quantization (for ML) |

### `stdlib/fs/` — Filesystem

| Module | What it provides |
|---|---|
| `fs.file` | File open/read/write/seek/close/flush |
| `fs.dir` | Directory listing |
| `fs.dir_iter` | Iterator over directory entries |
| `fs.path` | Path manipulation (join, dirname, basename, extension) |
| `fs.meta` | File metadata (size, mtime, permissions) |
| `fs.temp` | Temporary file/directory creation |
| `fs.archive_tar` | TAR archive reader/writer |

### `stdlib/net/` — Networking

| Module | What it provides |
|---|---|
| `net.tcp` | TCP connect/listen/accept/read/write |
| `net.udp` | UDP send/recv |
| `net.ip` | IPv4 parsing and formatting |
| `net.dns` | DNS resolution (getaddrinfo wrapper) |
| `net.http` | Minimal HTTP/1.1 client |
| `net.url` | URL parsing |
| `net.sockaddr` | Socket address structs |
| `net.websocket` | WebSocket framing |

### `stdlib/time/` — Time

| Module | What it provides |
|---|---|
| `time.clock` | Monotonic and wall-clock reads |
| `time.instant` | Instant type (nanoseconds since epoch) |
| `time.duration` | Duration arithmetic |
| `time.date` | ISO-8601 date formatting |
| `time.format` | strftime-style formatting |
| `time.stopwatch` | Elapsed-time measurement |
| `time.timer` | One-shot and repeating timers |
| `time.cron` | Cron-style schedule parsing |

### `stdlib/crypto/` — Cryptography

| Module | What it provides |
|---|---|
| `crypto.sha256` | SHA-256 hash |
| `crypto.chacha20` | ChaCha20 stream cipher |
| `crypto.hmac` | HMAC-SHA256 |
| `crypto.hex` | Hex encode/decode |
| `crypto.crc32_fast` | Fast CRC-32 |
| `crypto.subtle` | Constant-time comparison |

### `stdlib/compress/` — Compression

| Module | What it provides |
|---|---|
| `compress.rle` | Run-length encoding |
| `compress.lz4` | LZ4 block compression |
| `compress.snappy_lite` | Snappy-compatible compression |
| `compress.adler32_stream` | Adler-32 streaming checksum |

### `stdlib/effect_async/` — Structured Concurrency (HOSE)

| Module | What it provides |
|---|---|
| `effect_async.nursery` | Structured task nurseries (spawn, join, cancel) |
| `effect_async.timeout` | Delimited timeout scopes |
| `effect_async.bracket` | Async RAII bracketing |
| `effect_async.fiber_pool` | Work-stealing fiber pool |
| `effect_async.driver` | Event loop driver |
| `effect_async.epoll_handler` | epoll-based async I/O |
| `effect_async.uring_handler` | io_uring-based async I/O |

### Other modules

`stdlib/sync/` — mutex, rwlock, semaphore, condvar, thread, pool, mpmc  
`stdlib/alloc/` — arena allocator, bump allocator  
`stdlib/channel/` — bounded, unbounded, oneshot channels  
`stdlib/io/` — file I/O, buffered I/O (`io.bufio`)  
`stdlib/os/` — env, signal, process, mmap, pipe, poll, random  
`stdlib/sys/` — CPU features, memory stats, low-level mem ops  
`stdlib/encoding/` — base64, CSV, hex dump, INI, JSON-lite, URL encode, varint  
`stdlib/log/` — level-filtered logger, ring logger, syslog  
`stdlib/db/` — memtable, SSTable, WAL, compaction  
`stdlib/tui/` — ANSI sequences, cursor control, raw mode, style  
`stdlib/regex/` — NFA, DFA, matcher, AST  
`stdlib/unicode/` — char classification, case, normalization, width  
`stdlib/simd/` — f32x4, f64x2, i32x4, i64x2 operations  
`stdlib/codegen/` — x86_64, aarch64, riscv64 backend stubs, JIT  
`stdlib/ir/` — IR module/function/block/value/type representations  
`stdlib/llvm/` — LLVM IR text emitter stubs  
`stdlib/graph/` — data-flow graph, autodiff  
`stdlib/diag/` — symbol demangling, source location  
`stdlib/lex/` — generic lexer utilities  
`stdlib/tensor/` — ndarray, bf16, fp8 formats  
`stdlib/target/` — ABI, linker, register allocator, machine-code emitter stubs  
`stdlib/ast.pie` — AST node type stubs  
`stdlib/cli/` — argument parser, flag handling  
`stdlib/opt.pie` — SSA optimization pass stubs (DCE, const-fold, mem2reg, inline)  
`stdlib/compute/` — BLAS wrapper, thread pool  
`stdlib/pe.pie`, `stdlib/elf.pie` — binary format stubs  

---

## What stdlib is NOT

- **Not a linked library.** No `#include`-equivalent for `.pie` files yet.
- **Not tested against the current exec suite.** The 43 passing exec tests
  all inline their required functions rather than `use`-importing stdlib.
- **Not all production-quality.** The deeper modules (`effect_async`, `db`,
  `codegen` stubs) are scaffolding for future work — the APIs are designed,
  the implementations are first-draft.

---

## Roadmap: Making Stdlib Usable

1. **Module loader**: when `use vec.vec` appears, load and parse
   `stdlib/vec/vec.pie` into the same compilation unit.
2. **Name resolution across modules**: qualified names `vec.vec_new()` resolve
   to the correct definition.
3. **Incremental compilation**: cache compiled modules to avoid re-parsing
   everything on each `pride` invocation.
4. **Standard prelude**: automatically include a small set of ubiquitous
   definitions (Option, Result, io helpers) without explicit `use`.
