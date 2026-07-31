# Contextual Modal Type Theory (CMTT) in Pride

**Status: Compiler-internal pass — implemented and running. Surface syntax
for `quote`/`splice`/`box` is parsed; the full modal surface language is not
yet usable from `.pie` files without workarounds.**

---

## What CMTT is

CMTT (Contextual Modal Type Theory, after Nanevski & Pfenning 2008) is the
type-theoretic foundation for Pride's multi-stage programming layer.  It
extends the simply-typed lambda calculus with a **modal box type**:

```
□_{Γ'}^{L'} τ
```

Read: "an open code fragment of type `τ` that will be evaluated at future
stage `L'`, depending on the lexical environment `Γ'`".

In practice this means:

- **Stage 0**: normal runtime values — ordinary `let`-bindings.
- **Stage 1**: compile-time code — inside `comptime` / `quote`.
- **Stage 2+**: macro bodies, meta-level computations.

A value of type `□_{Γ'}^{L'} τ` is a *code value* — a syntactic object
carrying a future computation.  You cannot run it at the current stage; you
can only `splice` it into a surrounding quote at stage `L'-1` to obtain
something runnable.

---

## What Pride implements

### `modal.c3` — the checker (887 lines)

Implements the well-stagedness judgment **Γ ⊢^E e : τ at L**:

| Function | What it checks |
|---|---|
| `ModalLattice.push_scope` / `pop_scope` | Enter/exit a quote boundary (stage+1) or splice (stage-1) |
| `ModalLattice.bind_var` | Record a binder at its definition stage |
| `ModalLattice.lookup_var` | Retrieve a binder's stage; error if stage-0 var referenced at stage>0 without splice |
| `check_well_staged_expr` | Recursive AST walk enforcing the stage judgment |
| `modal_env_is_subtype` | Check Γ' ⊆ Γ for box modality |
| `modal_ast_alpha_equal` | Structural equality of open code fragments |

The checker is **integrated into `typecheck.c3`**: `check_well_staged_expr`
runs on every function body during `TypeChecker.check_fn`.  Any
well-stagedness violation is reported as a soft diagnostic (does not block
codegen).

### Continuation Tree rewriting (`modal.c3`, 7 rules)

When a scoped effect handler (bracket, local, catch, nursery, timeout) appears
inside a quoted block, `modal.c3` builds an explicit **Continuation Tree T**:

```
T ::= Leaf(e)
    | Node(op, k_in, k_out)
    | Seq(T1, T2)
    | Fmap(f, T)
    | Fuse(T_in, T_out)
    | Abort(e)
```

The tree is then normalized by repeatedly applying these rewrite rules until
a fixpoint (capped at 25,000 steps):

| Rule | LHS | RHS | Justification |
|---|---|---|---|
| 1 | Node(op, k_in, **Id**) | k_in | Identity elimination |
| 2 | Node(op, **Abort(e)**, k_out) | Abort(e) | Dead-scope pruning |
| 3 | Fmap(f, Node(op, k_in, k_out)) | Node(op, Fmap(f, k_in), k_out) | Functorial fusion (Wu et al.) |
| 4 | Fmap(f, Id) | Id | Map over identity |
| 5 | Fuse(Fmap(f, k_in), k_out) | Fmap(f, Fuse(k_in, k_out)) | Structured fusion (Wu et al.) |
| 6 | Fuse(k_in, **Id**) | k_in | Fuse with right identity |
| 7 | Seq(Seq(T1,T2), T3) | Seq(T1, Seq(T2,T3)) | Sequential associativity |

When the normalized tree has k_out collapsed to Id, the entire handler
installation is eliminated — **zero runtime prompt overhead**.

### AOT Stage Fusion (`stage.c3`)

`Stager.try_fuse_scoped_effect_aot` inspects each `NODE_EFFECT_HANDLE` node
during the staging pass.  It calls `modal_try_aot_fuse_effect_node`, which
builds the ContTree and runs the rewriter.  If the result is a Leaf (or the
k_out is Id), the handler is replaced with the raw computation — the runtime
prompt stack is never touched.

Identity handlers (single arm, body = `NODE_EXPR_UNIT`) are also fused
directly without building the full ContTree.

---

## What is NOT implemented

| Feature | Status |
|---|---|
| **`box[Γ] expr at Stage L` surface syntax** | Parsed by `parse_modal.c3` but **not wired into the standard parser**. Cannot currently be written in `.pie` files. |
| **Open-code pattern matching `case <quote> at L => expr`** | Parse structs exist; no evaluation path. |
| **Cross-stage variable escape check surfacing** | The `msp_verify_no_escape` function exists in `msp.c3`; it is not called from any pass. |
| **Full CMTT box type in typecheck** | The checker detects stage errors (quote/splice/ident mismatches) but does not annotate AST nodes with modal types. |
| **Stage-polymorphic functions** | No `∀L. code` quantifier. |
| **`splice` / `unquote` in `.pie` files** | Parsed; codegen does not lower them. |

---

## What you can do today

```pie
-- comptime <expr>: fold at stage 0 (fully working)
let table_size = comptime 8 * 1024    -- emits as LLVM constant

-- The CmttBox struct from pride.msp: model open-code fragments
-- at the library level (works in examples, no compiler enforcement)
let mut box = msp.cmtt_box_new(1, null, null)
msp.cmtt_box_add_effect_op(&box, 34)   -- annotate with HOSE yield_in opcode
let fused = msp.cmtt_box_fuse_aot(&box, box.k_in, null)  -- identity elim
```

The CMTT machinery is **live in the compiler** (running on every function)
and **available as a library** via `stdlib/pride/msp.pie`.  The missing piece
is the surface syntax to write modal programs directly in `.pie`.
