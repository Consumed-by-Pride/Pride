# Multi-Stage Programming (MSP) in Pride

**Status: Stage-0 (`comptime`) is fully working and exec-verified.
Stages 1+ (quote/splice/unquote) are parsed but not codegen-lowered.**

---

## The Three Layers of Pride MSP

### Layer 0 — `comptime` (Working)

`comptime <expr>` folds an expression at compile time during the staging pass
(`stage.c3`, `Stager.ctfe_eval`).  The result replaces the node in the AST
before codegen sees it.

**What works:**
```pie
let n         = comptime 8 * 1024          -- integer arithmetic
let is_debug  = comptime false             -- boolean
let mask      = comptime 0xFF_FF_FF_FFi64  -- hex
```

**What comptime can fold:**
- Integer and boolean arithmetic over literal constants
- Calls to pure functions whose bodies are themselves comptime-evaluable
- Array element access over comptime arrays

**What comptime cannot fold (currently):**
- Calls to extern fns (they are opaque at compile time)
- Heap allocation (`alloc`/`malloc`)
- Anything that performs IO or effects

### Layer 1 — `quote` / `splice` (Parsed, not codegen-lowered)

The lexer and parser recognise `quote`, `splice`, `unquote` as keywords and
build `NODE_QUOTE`, `NODE_SPLICE`, `NODE_UNQUOTE` AST nodes.  The modal
checker (`modal.c3`) validates that quotes and splices obey the stage
discipline.  But `codegen.c3` does **not** lower these nodes to LLVM IR;
any function containing them will either produce no output or incorrect IR.

### Layer 2 — Open-code pattern matching (Specced, not implemented)

`msp.c3` has the data structures and functions for open-code pattern matching
(`MspMatchContext`, `msp_match_pattern`, `msp_rewrite_open_code`) and
cross-stage escape analysis (`MspEscapeChecker`, `msp_verify_no_escape`).
None of these are called from the compiler pipeline.  They exist as a
foundation for a future rewrite pass.

---

## `msp.c3` — What it contains

| Component | Lines | Status |
|---|---|---|
| `MspQuoteRegistry` + hash-consing | ~100 | Built, not wired |
| `msp_hash_ast` (FNV structural hash) | ~30 | Working |
| `msp_ast_equal` (structural equality) | ~30 | Working |
| `MspMatchContext` + `msp_match_pattern` | ~80 | Built, not called |
| `MspEscapeChecker` + `msp_verify_no_escape` | ~80 | Built, not called |
| `msp_rewrite_open_code` | ~50 | Built, not called |
| `MspSpliceGraph` + DFS cycle check | ~70 | Built, not called |
| `MspCmttLedger` (binding ledger) | ~30 | Built, not called |

---

## `parse_modal.c3` — The surface syntax parser

Implements recursive-descent parsing for:

1. **Stage level annotations** — `at Stage L`, `at Stage L+1`
2. **CMTT box declarations** — `box[Γ] <expr> at Stage L`  
3. **Open-code pattern matching** — `case <perform with_timeout(0) { ~body }> at Stage L+1 => expr`
4. **Scoped effect signatures** — effect ops with `k_in`/`k_out` annotations

These parsers are compiled and linked.  They are **not hooked into the main
`parser.c3`** — they exist as a library (`parse_modal::`) callable from
future macro-expansion code.

---

## The `pride.msp` stdlib module

The user-facing MSP library (`stdlib/pride/msp.pie`) exposes:

```pie
-- Stage stack (mirrors the modal typechecker's internal state)
fn stage_stack_new : () -> StageStack
fn stage_stack_push : (*StageStack, i64) -> i64
fn stage_stack_pop  : *StageStack -> i64

-- Comptime-stage level query
fn msp_stage_level  : () -> i64    -- always returns 0 at runtime
fn msp_is_comptime  : () -> bool   -- always false at runtime

-- CMTT Box: open-code fragment at a given stage with effect annotations
fn cmtt_box_new        : (i64, ptr, ptr) -> CmttBox
fn cmtt_box_add_effect_op : (*CmttBox, i64) -> ()
fn cmtt_box_inspect    : (*CmttBox, i64) -> bool
fn cmtt_box_split_effects : *CmttBox -> (ptr, ptr)   -- (k_in, k_out)
fn cmtt_box_fuse_aot   : (*CmttBox, ptr, ptr) -> ptr  -- identity elim

-- Quote table (intern AST fragments by ID)
fn msp_quote_table_new  : () -> AstQuoteTable
fn msp_quote_register   : (*AstQuoteTable, i64, ptr) -> bool
fn msp_quote_lookup     : (*AstQuoteTable, i64) -> ptr

-- Staged arithmetic (fold at compile time)
fn msp_eval_const_i64 : (i64, i64, i64) -> i64   -- op=0:add 1:sub 2:mul
```

These are fully callable from `.pie` code and exec-tested in
`examples/01_comptime_generic_specialization.pie` and
`examples/05_modal_stage_checker.pie`.

---

## Roadmap to full MSP

1. Wire `parse_modal.c3` into `parser.c3` so `box[Γ] expr` is parseable
2. Add codegen lowering for `NODE_QUOTE`/`NODE_SPLICE` to produce
   quoted value structs (pointer + stage tag)
3. Call `msp_verify_no_escape` from `effectcheck.c3` or a new pass
4. Implement macro-time `msp_match_pattern` dispatch in `stage.c3`
5. Add stage-polymorphic function declarations `fn f : ∀L. T[L]`
