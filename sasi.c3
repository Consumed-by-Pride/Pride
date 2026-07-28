// sasi.c3 — SASI: Sparsely-Annotated Single Information (extraction pass)
// Implementation language: C3 (host). Pipeline step 2.
// The flattener (`ssi_ir.c3`) lowers the SSI tree into an SSI-CFG that still
// carries σ-nodes IN-BAND (one IR value per learned flow fact, e.g.
// `%n.1 = σ(%n.0)  refined:(>0)`). Full SSI is analytically powerful but a
// backend wants CLEAN standard SSA with no σ. SASI resolves this:
//   * EXTRACT every σ into a SPARSE side-map keyed by SSA value-id
//       %n.1 → Fact{ source = %n.0, refinement = (>0), parent = <dominating σ> }
//   * STRIP the physical σ instruction from its block's instruction list.
//   * LEAVE downstream instructions untouched — they still reference %n.1 as a
//     *virtual* identifier, now an "abstract" value defined by the SASI map
//     rather than a physical instruction. This is the e-SSA sparseness trick:
//     zero use-rewriting, facts attached exactly where they exist.
// After this pass the block instruction lists are σ-free (φ + ordinary ops =
// standard LLVM-shaped SSA), while the fact map preserves all path information.
// `resolve()` collapses a σ handle to its non-σ root for any consumer (a SASI-
// unaware backend, or the eventual SSA teardown). Step 4 (`sasi_opt.c3`) queries
// `fact_of()` to fold redundant comparisons / branches.
// Path info is kept MINIMAL per your design: each fact stores its immediate
// predicate plus a `parent` pointer to the dominating σ on the same binder, so a
// consumer can crawl the dominating-σ chain on demand without precomputing a
// conjunction matrix.

module sasi;

import lexer;
import ast;
import ssi_ir;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

alias Node = ast::AstNode;
alias Nk = ast::NodeKind;
alias Tt = lexer::TokenType;
alias IrVal = ssi_ir::IrVal;
alias IrBlock = ssi_ir::IrBlock;
alias SsiModule = ssi_ir::SsiModule;

const usz MAX_FACTS = 65536;
const int RESOLVE_GUARD = 100000;   // chain-walk cap (cycles can't happen, but be safe)

struct SasiFact
{
    IrVal*    value;       // the σ value this fact annotates (the map key)
    IrVal*    source;      // immediate operand the σ refined (σ.args[0])
    IrVal*    root;        // ultimate non-σ root of the σ chain
    Node*     refinement;  // NODE_TYPE_REFINEMENT: op + bound (the predicate)
    SasiFact* parent;      // dominating fact on the SAME binder (chain), or null
    Node*     binder;      // the source binder this version refines
    int       block;       // block the σ was defined in (where the fact holds on)
    int       next_by_source; // index of next fact with same source (reverse chain, -1=end)
}

struct SasiMap
{
    SsiModule* mod;

    SasiFact* facts;       // fact pool
    usz       fact_count;

    // value-id → fact index (or -1). Sized to the module's value count, so a
    // fact lookup is O(1). This is the "sparse" index: only σ values populate it.
    int*      by_value;
    usz       value_cap;

    // REVERSE INDEX: source_id → first fact index that refines this value.
    // Lets decide_compare find refinements of a comparison operand in O(1).
    int*      by_source;   // source_id → fact index (or -1)

    // stats
    int       swept;       // σ instructions physically removed from blocks
    int       chains;      // facts whose source was itself a σ (chain links)
    bool      overflow;
}

fn bool SasiMap.init(SasiMap* s, SsiModule* mod)
{
    s.mod = mod;
    s.fact_count = 0;
    s.swept = 0;
    s.chains = 0;
    s.overflow = false;

    s.facts = (SasiFact*)malloc(MAX_FACTS * SasiFact::size);
    if (s.facts == null) return false;

    s.value_cap = mod.val_count;
    if (s.value_cap == 0) s.value_cap = 1;
    s.by_value = (int*)malloc(s.value_cap * int::size);
    if (s.by_value == null) { free(s.facts); s.facts = null; return false; }
    for (usz i = 0; i < s.value_cap; i++) s.by_value[i] = -1;
    s.by_source = (int*)malloc(s.value_cap * int::size);
    if (s.by_source == null) { free(s.by_value); free(s.facts); s.facts = null; return false; }
    for (usz i = 0; i < s.value_cap; i++) s.by_source[i] = -1;
    return true;
}

fn void SasiMap.destroy(SasiMap* s)
{
    if (s.facts != null) { free(s.facts); s.facts = null; }
    if (s.by_value  != null) { free(s.by_value);  s.by_value  = null; }
    if (s.by_source != null) { free(s.by_source); s.by_source = null; }
}

// The fact annotating `v`, or null if `v` is an ordinary (non-σ) value.
fn SasiFact* SasiMap.fact_of(SasiMap* s, IrVal* v)
{
    if (v == null) return null;
    if (v.id < 0 || (usz)v.id >= s.value_cap) return null;
    int fi = s.by_value[v.id];
    if (fi < 0) return null;
    return &s.facts[fi];
}

// First fact that has source == v (reverse lookup via by_source index).
fn SasiFact* SasiMap.first_fact_of_source(SasiMap* s, IrVal* v)
{
    if (v == null) return null;
    if (s.by_source == null) return null;
    if (v.id < 0 || (usz)v.id >= s.value_cap) return null;
    int fi = s.by_source[v.id];
    if (fi < 0) return null;
    return &s.facts[fi];
}

fn SasiFact* SasiMap.next_fact_of_source(SasiMap* s, SasiFact* f)
{
    if (f == null || f.next_by_source < 0) return null;
    return &s.facts[f.next_by_source];
}

// Collapse a σ handle to its ultimate non-σ root value (a backend that ignores
// SASI uses this to "see through" σ). Returns `v` unchanged if it isn't a σ.
fn IrVal* SasiMap.resolve(SasiMap* s, IrVal* v)
{
    int guard = 0;
    while (v != null)
    {
        SasiFact* f = s.fact_of(v);
        if (f == null) return v;          // not a σ handle → the root
        if (f.source == null) return v;   // dangling source → stop
        v = f.source;
        guard++;
        if (guard > RESOLVE_GUARD) return v;
    }
    return v;
}

// Three linear passes over the CFG:
//   1. harvest every σ into a fact (index by value-id),
//   2. link parents (dominating σ on the same binder) and compute roots,
//   3. physically unlink σ from each block's instruction list.
fn void SasiMap.extract(SasiMap* s)
{
    s.harvest();
    s.link_chains();
    s.strip();
}

// Pass 1 — record every σ value found in any block's straight-line list.
fn void SasiMap.harvest(SasiMap* s)
{
    SsiModule* m = s.mod;
    for (usz bi = 0; bi < m.block_count; bi++)
    {
        IrBlock* b = &m.blocks[bi];
        IrVal* in = b.head;
        while (in != null)
        {
            if (in.op == ssi_ir::IrOp.IR_SIGMA)
            {
                s.add_fact(in, b.id);
            }
            in = in.next;
        }
    }
}

fn void SasiMap.add_fact(SasiMap* s, IrVal* sigma, int block)
{
    if (s.fact_count >= MAX_FACTS) { s.overflow = true; return; }
    if (sigma.id < 0 || (usz)sigma.id >= s.value_cap) return;
    // A σ with no source value refines nothing — recording it would create an
    // unresolvable fact. Skip it (defensive; emit_sigmas already avoids these).
    if (sigma.arg_count < 1 || sigma.args[0] == null) return;
    usz fi = s.fact_count;
    s.fact_count++;
    SasiFact* f = &s.facts[fi];
    f.value = sigma;
    f.source = sigma.arg_count >= 1 ? sigma.args[0] : null;
    f.root = null;
    f.refinement = sigma.refinement;
    f.parent = null;
    f.binder = sigma.binder;
    f.block = block;
    f.next_by_source = -1;
    s.by_value[sigma.id] = (int)fi;
    // Populate reverse index: by_source[source_id] → chain of facts.
    if (f.source != null && f.source.id >= 0 && (usz)f.source.id < s.value_cap)
    {
        int src_id = f.source.id;
        f.next_by_source = s.by_source[src_id];   // prepend
        s.by_source[src_id] = (int)fi;
    }
}

// Pass 2 — for each fact, if its source is itself a σ (has a fact), that fact is
// the dominating refinement on the same value: link it as the parent. Then
// compute the ultimate non-σ root by walking the source chain.
fn void SasiMap.link_chains(SasiMap* s)
{
    for (usz i = 0; i < s.fact_count; i++)
    {
        SasiFact* f = &s.facts[i];
        SasiFact* pf = s.fact_of(f.source);
        if (pf != null)
        {
            f.parent = pf;
            s.chains++;
        }
        f.root = s.resolve(f.value);
    }
}

// Pass 3 — rebuild each block's instruction list, dropping σ values. The σ
// IrVals stay alive in the module pool (instructions still point at them as
// abstract handles), but no longer appear as physical block instructions.
fn void SasiMap.strip(SasiMap* s)
{
    SsiModule* m = s.mod;
    for (usz bi = 0; bi < m.block_count; bi++)
    {
        IrBlock* b = &m.blocks[bi];
        IrVal* new_head = null;
        IrVal* new_tail = null;
        IrVal* in = b.head;
        while (in != null)
        {
            IrVal* nxt = in.next;
            if (in.op == ssi_ir::IrOp.IR_SIGMA)
            {
                in.block = -1;     // mark abstract (defined by the SASI map)
                in.next = null;
                s.swept++;
            }
            else
            {
                in.next = null;
                if (new_tail == null) { new_head = in; new_tail = in; }
                else { new_tail.next = in; new_tail = in; }
            }
            in = nxt;
        }
        b.head = new_head;
        b.tail = new_tail;
    }
}

// Confirms the CFG is now σ-free in every block (the cleanliness guarantee) and
// that every fact resolves to a non-σ root. Returns the count of leftover σ
// instructions (must be 0) plus unresolved facts (must be 0).
struct SasiVerify { int leftover_sigma; int unresolved; int facts; int chains; }

fn SasiVerify SasiMap.verify(SasiMap* s)
{
    SasiVerify r;
    r.leftover_sigma = 0;
    r.unresolved = 0;
    r.facts = (int)s.fact_count;
    r.chains = s.chains;

    SsiModule* m = s.mod;
    for (usz bi = 0; bi < m.block_count; bi++)
    {
        IrBlock* b = &m.blocks[bi];
        IrVal* in = b.head;
        while (in != null)
        {
            if (in.op == ssi_ir::IrOp.IR_SIGMA) r.leftover_sigma++;
            in = in.next;
        }
        // φ lists must never have held σ, but check for completeness.
        IrVal* ph = b.phi_head;
        while (ph != null)
        {
            if (ph.op == ssi_ir::IrOp.IR_SIGMA) r.leftover_sigma++;
            ph = ph.next;
        }
    }
    for (usz i = 0; i < s.fact_count; i++)
    {
        SasiFact* f = &s.facts[i];
        IrVal* root = f.root;
        if (root != null && root.op == ssi_ir::IrOp.IR_SIGMA) r.unresolved++;
    }
    return r;
}

fn char* cmp_name(Node* refinement)
{
    if (refinement == null) return "?";
    return lexer::token_type_name(refinement.p.op.op);
}

fn void print_binder(Node* binder)
{
    if (binder == null) { printf("?"); return; }
    Node* nm = binder.child_count >= 1 ? binder.children[0] : binder;
    if (nm != null && nm.kind == Nk.NODE_PATTERN_IDENT && nm.child_count >= 1) nm = nm.children[0];
    if (nm != null && (nm.kind == Nk.NODE_IDENT || nm.kind == Nk.NODE_TYPEVAR))
    {
        for (usz i = 0; i < nm.p.ident.name_len; i++) printf("%c", nm.p.ident.name_ptr[i]);
    }
    else { printf("?"); }
}

// Compact rendering of a bound expression (the right side of the predicate).
fn void print_bound(Node* refinement)
{
    if (refinement == null || refinement.child_count < 1) { printf("?"); return; }
    Node* b = refinement.children[0];
    if (b == null) { printf("?"); return; }
    switch (b.kind)
    {
        case Nk.NODE_LIT_INT:   printf("%llu", b.p.lit_int.int_val);
        case Nk.NODE_LIT_BOOL:  printf("%s", b.p.lit_bool.bool_val ? "true" : "false");
        case Nk.NODE_IDENT:
            for (usz i = 0; i < b.p.ident.name_len; i++) printf("%c", b.p.ident.name_ptr[i]);
        default:                printf("<expr>");
    }
}

fn void SasiMap.dump(SasiMap* s)
{
    printf("\n=== SASI fact map (%llu facts, %d chained) ===\n",
        (ulong)s.fact_count, s.chains);
    for (usz i = 0; i < s.fact_count; i++)
    {
        SasiFact* f = &s.facts[i];
        printf("    v%d {", f.value != null ? f.value.id : -1);
        print_binder(f.binder);
        printf("}  :=  ");
        print_binder(f.binder);
        printf(" %s ", cmp_name(f.refinement));
        print_bound(f.refinement);
        if (f.source != null) { printf("   [from v%d", f.source.id); }
        else { printf("   [from _"); }
        if (f.root != null) printf(", root v%d", f.root.id);
        printf(", B%d]", f.block);
        if (f.parent != null && f.parent.value != null) printf("   parent v%d", f.parent.value.id);
        printf("\n");
    }
    SasiVerify v = s.verify();
    printf("  -- post-strip: %d σ left in blocks, %d unresolved facts --\n",
        v.leftover_sigma, v.unresolved);
}
