# Pride — Documentation Index

Pride is a hobby systems language. Its compiler is written in **C3** and
targets **LLVM 22**.

```
[ Frontend (C3) ]  parse → PON → analyses → optimize → emit .bc
                                  ↓
      [ Standard LLVM 22 toolchain reads the .bc, optimizes, emits code ]
```

---

## Start here

| If you want to… | Read |
|---|---|
| Learn the language | [`reference/v.md`](reference/v.md) — the language spec |
| Know what actually works today | [`status/HONEST_STATUS.md`](status/HONEST_STATUS.md) |
| Work on the new front end | [`pfront/README.md`](pfront/README.md) |
| Understand the analyses | [`pfront/THEORY.md`](pfront/THEORY.md) |
| Understand the backend IR | [`design/SSI_IR.md`](design/SSI_IR.md) |

---

## Layout

```
docs/
├── README.md            ← you are here
├── pfront/              the from-scratch front end (current work)
│   ├── README.md        architecture, module map, how to build
│   ├── THEORY.md        every analysis pass, what it proves, what it costs
│   └── REPORT.md        measured results and known gaps
├── design/              how a subsystem is built, and why
│   ├── SSI_IR.md        the SSA-CFG the backend consumes
│   ├── MSP_DESIGN.md    multi-stage programming core
│   ├── MSP_AND_STAGING.md
│   ├── MSP_STAGE5_6_DESIGN.md
│   ├── SASI_DESIGN.md   / SASI_OPT_DESIGN.md
│   ├── CMTT_AND_MODAL.md contextual modal type theory
│   └── HOSE_AND_EFFECTS.md algebraic effects and handlers
├── status/              what works, measured — not aspirational
│   ├── HONEST_STATUS.md
│   ├── FRONTEND_STATUS.md
│   └── CONFORMANCE.md
└── reference/           stable, user-facing
    ├── v.md             the language specification
    ├── STDLIB.md
    └── CAPABILITY_CHECKLIST.md
```

---

## The two pipelines

The repository contains **two** front ends. This is deliberate and temporary.

### Legacy (root `*.c3`) — frozen, green

The original pipeline: `lexer.c3` → `parser.c3` → `resolve.c3` →
`typecheck.c3` → `ssi_ir.c3` → `codegen.c3`. It emits LLVM IR and passes
**conformance 261/262**.

It is **not** being modified. Its tests are the regression net that proves the
new work has not broken anything.

```sh
bash build.sh            # -> ./pride
bash conformance/run.sh  # 261/262
bash tests/run_exec.sh
```

### `pfront/` — the rewrite, under active development

A from-scratch front end. It exists because the legacy pipeline had **no
module system**: `use` was lexed, parsed and hoisted, but the compiler never
opened a second file and exited 0 silently. Only **4 of 257** stdlib modules
were compilable, and all four were empty shells.

`pfront` currently gets **249 / 258** stdlib modules self-clean.

```sh
/tmp/c3/c3c compile pfront/*.c3 pfront/theory/*.c3 -o pfrontc
chmod +x pfrontc
bash pfront_tests/run.sh   # 84/84
```

---

## Design commitment: Pride is untyped

**The compiler does not reject a program because types disagree.** It assumes
the developer knows what they are doing.

Analyses still run — intervals, nullness, liveness, effects — but a fact they
compute is an **optimization opportunity**, never grounds for refusal. An
index proven out of bounds marks the path unreachable so the optimizer can
delete it; it does not fail the build.

Type, arity, mutability and bounds advice is available under `--lint`, always
as warnings. See [`pfront/THEORY.md`](pfront/THEORY.md) for the full policy
and the chokepoint that enforces it.

There is **no borrow checker, no lifetime checker and no ownership analysis**,
and none is planned.

---

## Environment

`/tmp` does not persist between sessions. Re-fetch as needed:

```sh
# C3 compiler
curl -sSL -o /tmp/c3.tar.gz \
  https://github.com/c3lang/c3c/releases/download/v0.8.1/c3-linux-static.tar.gz
tar xzf /tmp/c3.tar.gz -C /tmp        # -> /tmp/c3/c3c

# LLVM 22 (Debian trixie ships only 19)
curl -sSL https://apt.llvm.org/llvm-snapshot.gpg.key \
  | sudo gpg --batch --yes --dearmor -o /etc/apt/keyrings/llvm.gpg
echo "deb [signed-by=/etc/apt/keyrings/llvm.gpg] \
http://apt.llvm.org/trixie/ llvm-toolchain-trixie-22 main" \
  | sudo tee /etc/apt/sources.list.d/llvm22.list
sudo apt-get update && sudo apt-get install -y llvm-22 llvm-22-dev clang-22 lld-22
export PATH=/usr/lib/llvm-22/bin:$PATH   # legacy scripts call unsuffixed names
```

Workspace snapshots drop the exec bit — `chmod +x pfrontc` after a restore.
