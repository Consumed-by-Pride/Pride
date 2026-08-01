# Pride

A hobby systems language. The compiler is written in **C3** and targets
**LLVM 22**.

```pride
fn divide : (i32, i32) -> i32 ! [UB]
  | (_, 0) -> ub! "division by zero"
  | (a, b) -> a / b
```

---

## Documentation

**→ [`docs/README.md`](docs/README.md)** is the index. Start there.

| | |
|---|---|
| The language | [`docs/reference/v.md`](docs/reference/v.md) |
| What actually works | [`docs/status/HONEST_STATUS.md`](docs/status/HONEST_STATUS.md) |
| The new front end | [`docs/pfront/README.md`](docs/pfront/README.md) |
| Measured results | [`docs/pfront/REPORT.md`](docs/pfront/REPORT.md) |

---

## Build

```sh
# C3 toolchain (into /tmp, which does not persist)
curl -sSL -o /tmp/c3.tar.gz \
  https://github.com/c3lang/c3c/releases/download/v0.8.1/c3-linux-static.tar.gz
tar xzf /tmp/c3.tar.gz -C /tmp

# legacy pipeline -> ./pride
bash build.sh
export PATH=/usr/lib/llvm-22/bin:$PATH
bash conformance/run.sh          # 261/262

# new front end -> ./pfrontc
/tmp/c3/c3c compile pfront/*.c3 pfront/theory/*.c3 -o pfrontc
chmod +x pfrontc
bash pfront_tests/run.sh         # 84/84
```

---

## Two front ends, on purpose

`pfront/` is a from-scratch replacement, under active development. The root
`*.c3` pipeline is **frozen** — it is the regression net that proves the new
work has not broken anything.

The rewrite exists because the legacy front end had no module system: `use`
parsed but never opened a second file, so only 4 of 257 stdlib modules
compiled. `pfront` gets **258 / 258**, and loads all of them into one
compilation unit with 0 errors.

---

## Pride is untyped

The compiler does not reject a program because types disagree. It assumes the
developer knows what they are doing.

Analyses still run — intervals, nullness, liveness, effects — but what they
prove is used to **optimize**, never to refuse. An index proven out of bounds
marks that path unreachable so the optimizer can delete it. Type and
mutability advice is available under `--lint`, always as warnings.

There is no borrow checker and none is planned.
