// msp.c3 — Formal Multi-Stage Programming (MSP) & CMTT Open-Code Rewriting
// Implementation language: C3 (host).
//
// This module implements the Contextual Modal Open-Code Quotation Engine,
// Open-Code Pattern-Matching, Cross-Stage Variable Escape Analysis, and
// AST Quotation Hash-Consing for Pride's Multi-Level Contextual Effect Engine:
//
//   1. OPEN-CODE PATTERN MATCHING (`msp_match_pattern`, `msp_rewrite_open_code`):
//      Allows macros executing at Stage L to inspect open code blocks at Stage L+1
//      (e.g., `<perform with_timeout(0) { ~body }> at Stage L+1`), extract spliced
//      subtrees (`~body`), and rewrite structural operations ahead of time.
//
//   2. CROSS-STAGE VARIABLE ESCAPE ANALYSIS (`msp_verify_no_escape`):
//      Enforces Contextual Modal Type Theory sound scoping: proves that no lexical
//      variable bound in environment Γ at Stage L escapes into an outer stage L-1
//      without an explicit box modality □_{Γ'}^{L'} τ.
//
//   3. AST QUOTATION HASH-CONSING (`msp_hash_cons_quote`):
//      Deduplicates structural quotations so identical quoted code blocks share
//      canonical AST nodes in memory, enabling O(1) equality comparison.

module msp;

import lexer;
import ast;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

alias Node = ast::AstNode;
alias Nk   = ast::NodeKind;
alias Tt   = lexer::TokenType;

const usz MSP_MAX_QUOTES    = 2048;
const usz MSP_MAX_PATTERNS  = 512;
const usz MSP_MAX_BINDINGS  = 256;
const int MSP_MAX_STAGE     = 100;
const int MSP_MAX_DEPTH     = 500;

// ── Open-Code Quotation Table & Hash-Consing Registry ───────────────────────
//
// STORAGE & COMPLEXITY. The entry array is the canonical store (stable
// pointers, insertion order). Lookups go through an open hash index:
// 2048-entry MCS-style separate chaining — each bucket heads an intrusive
// chain threaded through MspQuoteEntry.next_idx, so lookup is O(chain) with
// an expected chain of < 1 at the capped registry size, versus the previous
// O(n) full scan per insert (O(n²) total for n quotations).
//
// OBSERVABILITY. `inserts`/`hits`/`probes`/`longest_chain` make the dedup
// ratio and index health queryable once the engine is wired into staging;
// report() prints them.
//
// NOTE: the struct is ~200 KB — instances MUST be heap-allocated.

const usz MSP_IDX_CAP = 8192;   // power of two, 4× MSP_MAX_QUOTES

struct MspQuoteEntry
{
    uint64_t hash_code;
    int      stage_level;
    Node*    ast_node;
    Node*    context_node; // explicit environment Γ' for CMTT
    usz      next_idx;     // hash-chain link: entry index + 1 (0 = chain end)
}

struct MspQuoteRegistry
{
    MspQuoteEntry[MSP_MAX_QUOTES] entries;
    usz                           count;
    int                           errors;
    char[256][64]                 error_msgs;
    usz[MSP_IDX_CAP]              idx;        // bucket → entry index + 1 (0 = empty)
    usz                           hits;          // dedup: returned existing entry
    usz                           inserts;       // genuinely new quotations
    usz                           probes;         // chain steps (lookup cost)
    usz                           longest_chain;  // worst chain seen (index health)
}

fn void MspQuoteRegistry.init(MspQuoteRegistry* r)
{
    r.count = 0;
    r.errors = 0;
    for (usz i = 0; i < MSP_IDX_CAP; i++) r.idx[i] = 0;
    r.hits = 0;
    r.inserts = 0;
    r.probes = 0;
    r.longest_chain = 0;
}

fn void MspQuoteRegistry.report_error(MspQuoteRegistry* r, char* msg)
{
    if (r.errors < 64 && msg != null)
    {
        char* dst = &r.error_msgs[r.errors][0];
        usz i = 0;
        while (msg[i] != 0 && i < 255) { dst[i] = msg[i]; i++; }
        dst[i] = 0;
        r.errors++;
    }
}

// Compute structural FNV-1a hash of a quoted AST subtree
fn uint64_t msp_hash_ast(Node* n, int depth)
{
    if (n == null || depth > MSP_MAX_DEPTH) return 14695981039346656037ULL;
    uint64_t h = 14695981039346656037ULL;
    h ^= (uint64_t)n.kind;
    h *= 1099511628211ULL;
    if (n.kind == Nk.NODE_IDENT && n.p.ident.name_ptr != null)
    {
        for (usz i = 0; i < n.p.ident.name_len; i++)
        {
            h ^= (uint64_t)n.p.ident.name_ptr[i];
            h *= 1099511628211ULL;
        }
    }
    else if (n.kind == Nk.NODE_LIT_INT)
    {
        h ^= (uint64_t)n.p.lit_int.int_val;
        h *= 1099511628211ULL;
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        h ^= msp_hash_ast(n.children[i], depth + 1);
        h *= 1099511628211ULL;
    }
    return h;
}

// Check structural equality of two AST subtrees
fn bool msp_ast_equal(Node* a, Node* b, int depth)
{
    if (a == b) return true;
    if (a == null || b == null || depth > MSP_MAX_DEPTH) return false;
    if (a.kind != b.kind || a.child_count != b.child_count) return false;
    if (a.kind == Nk.NODE_IDENT)
    {
        if (a.p.ident.name_len != b.p.ident.name_len) return false;
        if (a.p.ident.name_ptr == null || b.p.ident.name_ptr == null) return false;
        for (usz i = 0; i < a.p.ident.name_len; i++)
        {
            if (a.p.ident.name_ptr[i] != b.p.ident.name_ptr[i]) return false;
        }
        return true;
    }
    if (a.kind == Nk.NODE_LIT_INT) return a.p.lit_int.int_val == b.p.lit_int.int_val;
    for (usz i = 0; i < a.child_count; i++)
    {
        if (!msp_ast_equal(a.children[i], b.children[i], depth + 1)) return false;
    }
    return true;
}

// Register or lookup a quoted AST node via hash-consing.
// Returns the canonical interned AST pointer.
// Lookup walks only the chain of the node-hash bucket (expected length < 1
// at the capped 2048 entries rather than the previous O(n) full scan);
// structural equality (msp_ast_equal) is still the final arbiter, so hash
// collisions can never cause a false intern.
fn Node* MspQuoteRegistry.hash_cons(MspQuoteRegistry* r, Node* n, int stage, Node* ctx)
{
    if (n == null) return null;
    uint64_t h = msp_hash_ast(n, 0);
    usz bucket = (usz)(h & (uint64_t)(MSP_IDX_CAP - 1));
    usz chain_len = 0;

    usz link = r.idx[bucket];
    while (link != 0)
    {
        MspQuoteEntry* e = &r.entries[link - 1];
        r.probes++;
        chain_len++;
        // Same structural hash AND same stage, then confirm structurally.
        if (e.hash_code == h && e.stage_level == stage
            && msp_ast_equal(e.ast_node, n, 0))
        {
            r.hits++;
            if (chain_len > r.longest_chain) r.longest_chain = chain_len;
            return e.ast_node;
        }
        link = e.next_idx;
    }
    if (chain_len > r.longest_chain) r.longest_chain = chain_len;

    if (r.count < MSP_MAX_QUOTES)
    {
        usz idx = r.count++;
        r.entries[idx].hash_code    = h;
        r.entries[idx].stage_level  = stage;
        r.entries[idx].ast_node     = n;
        r.entries[idx].context_node = ctx;
        // Prepend to the bucket chain (chain order is irrelevant to equality).
        r.entries[idx].next_idx     = r.idx[bucket];
        r.idx[bucket]               = idx + 1;
        r.inserts++;
    }
    return n;
}

// Dedup ratio snapshot: (canonical entries, dedup hits, new inserts).
fn void MspQuoteRegistry.stats(MspQuoteRegistry* r, usz* out_entries,
                               usz* out_hits, usz* out_inserts)
{
    if (out_entries != null) *out_entries = r.count;
    if (out_hits != null)    *out_hits = r.hits;
    if (out_inserts != null) *out_inserts = r.inserts;
}

// Print the registry's dedup/index health report (for the staging report and
// future `--stage-verbose` tooling).
fn void MspQuoteRegistry.report(MspQuoteRegistry* r)
{
    printf("  quotes interned     : %llu (dedup hits %llu, fresh %llu)\n",
           (ulong)r.count, (ulong)r.hits, (ulong)r.inserts);
    printf("  index probes        : %llu (longest chain %llu / %llu buckets)\n",
           (ulong)r.probes, (ulong)r.longest_chain, (ulong)MSP_IDX_CAP);
}

// ── Open-Code Pattern Matching & Spliced Subtree Extraction ────────────────

struct MspBinding
{
    char* name_ptr;
    usz   name_len;
    Node* bound_node;
    int   stage_level;
}

struct MspMatchContext
{
    MspBinding[MSP_MAX_BINDINGS] bindings;
    usz                          binding_count;
    bool                         is_matched;
}

fn void MspMatchContext.init(MspMatchContext* m)
{
    m.binding_count = 0;
    m.is_matched = true;
}

fn bool MspMatchContext.bind(MspMatchContext* m, char* name, usz len, Node* val, int stage)
{
    if (m.binding_count >= MSP_MAX_BINDINGS) return false;
    usz idx = m.binding_count++;
    m.bindings[idx].name_ptr    = name;
    m.bindings[idx].name_len    = len;
    m.bindings[idx].bound_node  = val;
    m.bindings[idx].stage_level = stage;
    return true;
}

fn Node* MspMatchContext.lookup(MspMatchContext* m, char* name, usz len)
{
    for (usz i = 0; i < m.binding_count; i++)
    {
        MspBinding* b = &m.bindings[i];
        if (b.name_len == len && b.name_ptr != null && name != null)
        {
            bool eq = true;
            for (usz k = 0; k < len; k++)
            {
                if (b.name_ptr[k] != name[k]) { eq = false; break; }
            }
            if (eq) return b.bound_node;
        }
    }
    return null;
}

// Match an open code AST tree against a modal pattern AST tree.
// Spliced variables (~x) in the pattern bind matching AST subtrees in `m`.
fn bool msp_match_pattern_rec(MspMatchContext* m, Node* pat, Node* code, int stage, int depth)
{
    if (!m.is_matched || depth > MSP_MAX_DEPTH) return false;
    if (pat == null && code == null) return true;
    if (pat == null || code == null) { m.is_matched = false; return false; }

    // Pattern splice (~x): bind the target code AST subtree
    if (pat.kind == Nk.NODE_SPLICE || pat.kind == Nk.NODE_UNQUOTE)
    {
        if (pat.child_count >= 1 && pat.children[0] != null
            && pat.children[0].kind == Nk.NODE_IDENT)
        {
            Node* id = pat.children[0];
            m.bind(id.p.ident.name_ptr, id.p.ident.name_len, code, stage);
            return true;
        }
        m.is_matched = false;
        return false;
    }

    if (pat.kind != code.kind || pat.child_count != code.child_count)
    {
        m.is_matched = false;
        return false;
    }

    if (pat.kind == Nk.NODE_IDENT)
    {
        if (pat.p.ident.name_len != code.p.ident.name_len) { m.is_matched = false; return false; }
        if (pat.p.ident.name_ptr == null || code.p.ident.name_ptr == null) { m.is_matched = false; return false; }
        for (usz i = 0; i < pat.p.ident.name_len; i++)
        {
            if (pat.p.ident.name_ptr[i] != code.p.ident.name_ptr[i]) { m.is_matched = false; return false; }
        }
        return true;
    }
    if (pat.kind == Nk.NODE_LIT_INT)
    {
        if (pat.p.lit_int.int_val != code.p.lit_int.int_val) { m.is_matched = false; return false; }
        return true;
    }

    for (usz i = 0; i < pat.child_count; i++)
    {
        if (!msp_match_pattern_rec(m, pat.children[i], code.children[i], stage, depth + 1))
        {
            m.is_matched = false;
            return false;
        }
    }
    return true;
}

fn bool msp_match_pattern(MspMatchContext* m, Node* pat, Node* code, int stage)
{
    m.init();
    return msp_match_pattern_rec(m, pat, code, stage, 0);
}

// ── Cross-Stage Variable Escape Analysis ───────────────────────────────────

// Verify that no lexical variable bound at Stage L escapes into Stage L-1
// without an explicit Contextual Modal Box (□_{Γ'}^{L'} τ) wrapping.
struct MspEscapeChecker
{
    char*[1024] bound_names;
    usz[1024]   bound_lens;
    int[1024]   bound_stages;
    usz         bound_count;
    int         errors;
    char[256][32] error_msgs;
}

fn void MspEscapeChecker.init(MspEscapeChecker* c)
{
    c.bound_count = 0;
    c.errors = 0;
}

fn void MspEscapeChecker.bind(MspEscapeChecker* c, char* name, usz len, int stage)
{
    if (c.bound_count >= 1024) return;
    usz idx = c.bound_count++;
    c.bound_names[idx]  = name;
    c.bound_lens[idx]   = len;
    c.bound_stages[idx] = stage;
}

fn int MspEscapeChecker.lookup_stage(MspEscapeChecker* c, char* name, usz len)
{
    for (int i = (int)c.bound_count - 1; i >= 0; i--)
    {
        if (c.bound_lens[i] == len && c.bound_names[i] != null && name != null)
        {
            bool eq = true;
            for (usz k = 0; k < len; k++)
            {
                if (c.bound_names[i][k] != name[k]) { eq = false; break; }
            }
            if (eq) return c.bound_stages[i];
        }
    }
    return -1; // unbound / top-level global
}

fn void MspEscapeChecker.report_error(MspEscapeChecker* c, char* msg)
{
    if (c.errors < 32 && msg != null)
    {
        char* dst = &c.error_msgs[c.errors][0];
        usz i = 0;
        while (msg[i] != 0 && i < 255) { dst[i] = msg[i]; i++; }
        dst[i] = 0;
        c.errors++;
    }
}

fn bool msp_verify_no_escape_rec(MspEscapeChecker* c, Node* n, int curr_stage, int depth)
{
    if (n == null || depth > MSP_MAX_DEPTH) return true;
    switch (n.kind)
    {
        case Nk.NODE_QUOTE:
        case Nk.NODE_STAGE:
            for (usz i = 0; i < n.child_count; i++)
            {
                msp_verify_no_escape_rec(c, n.children[i], curr_stage + 1, depth + 1);
            }
            return c.errors == 0;

        case Nk.NODE_SPLICE:
        case Nk.NODE_UNQUOTE:
            for (usz i = 0; i < n.child_count; i++)
            {
                msp_verify_no_escape_rec(c, n.children[i], curr_stage - 1, depth + 1);
            }
            return c.errors == 0;

        case Nk.NODE_DECL_LET:
        case Nk.NODE_DECL_MUT:
            if (n.child_count >= 1 && n.children[0] != null
                && n.children[0].kind == Nk.NODE_PATTERN_IDENT)
            {
                Node* id = n.children[0];
                c.bind(id.p.ident.name_ptr, id.p.ident.name_len, curr_stage);
            }
            for (usz i = 1; i < n.child_count; i++)
            {
                msp_verify_no_escape_rec(c, n.children[i], curr_stage, depth + 1);
            }
            return c.errors == 0;

        case Nk.NODE_IDENT:
            {
                int bstage = c.lookup_stage(n.p.ident.name_ptr, n.p.ident.name_len);
                if (bstage >= 0 && bstage > curr_stage)
                {
                    // Variable bound at a future stage escapes into an earlier stage!
                    c.report_error((char*)"cross-stage variable escape error: future-bound variable escapes into an earlier stage without CMTT box modality");
                    return false;
                }
                return true;
            }

        default:
            for (usz i = 0; i < n.child_count; i++)
            {
                msp_verify_no_escape_rec(c, n.children[i], curr_stage, depth + 1);
            }
            return c.errors == 0;
    }
}

fn bool msp_verify_no_escape(MspEscapeChecker* c, Node* root)
{
    c.init();
    return msp_verify_no_escape_rec(c, root, 0, 0);
}

// ── Open-Code Rewriting Engine ──────────────────────────────────────────────

// Given an open code AST node and a match context with bindings from
// `msp_match_pattern`, rewrite the open code by replacing any spliced
// variables (~x) with their bound AST subtrees.
fn Node* msp_rewrite_open_code(MspMatchContext* m, Node* template_ast, int stage, int depth)
{
    if (template_ast == null || depth > MSP_MAX_DEPTH) return template_ast;
    if (template_ast.kind == Nk.NODE_SPLICE || template_ast.kind == Nk.NODE_UNQUOTE)
    {
        if (template_ast.child_count >= 1 && template_ast.children[0] != null
            && template_ast.children[0].kind == Nk.NODE_IDENT)
        {
            Node* id = template_ast.children[0];
            Node* bound = m.lookup(id.p.ident.name_ptr, id.p.ident.name_len);
            if (bound != null) return bound;
        }
    }
    for (usz i = 0; i < template_ast.child_count; i++)
    {
        template_ast.children[i] = msp_rewrite_open_code(m, template_ast.children[i], stage, depth + 1);
    }
    return template_ast;
}

// ── Multi-Stage Code Splicing Graph & Fixpoint Normalizer ───────────────────
// Builds an explicit dependency graph of open code quotations and splices
// across stage levels L -> L+1 -> L-1, proving acyclicity and evaluating
// cross-stage constant expressions in topological order.

struct MspSpliceNode
{
    int   node_id;
    int   stage_level;
    Node* ast_node;
    int   dependency_count;
    int[16] dependencies;
    bool  is_visited;
    bool  is_in_stack;
    bool  is_evaluated;
}

struct MspSpliceGraph
{
    MspSpliceNode[256] nodes;
    usz                node_count;
    int                errors;
    char[256][64]      error_msgs;
}

fn void MspSpliceGraph.init(MspSpliceGraph* g)
{
    g.node_count = 0;
    g.errors = 0;
}

fn int MspSpliceGraph.add_node(MspSpliceGraph* g, int stage, Node* ast_node)
{
    if (g.node_count >= 256) return -1;
    usz idx = g.node_count++;
    g.nodes[idx].node_id = (int)idx;
    g.nodes[idx].stage_level = stage;
    g.nodes[idx].ast_node = ast_node;
    g.nodes[idx].dependency_count = 0;
    g.nodes[idx].is_visited = false;
    g.nodes[idx].is_in_stack = false;
    g.nodes[idx].is_evaluated = false;
    return (int)idx;
}

fn void MspSpliceGraph.add_dependency(MspSpliceGraph* g, int from_id, int to_id)
{
    if (from_id < 0 || (usz)from_id >= g.node_count || to_id < 0 || (usz)to_id >= g.node_count) return;
    MspSpliceNode* fn_node = &g.nodes[(usz)from_id];
    if (fn_node.dependency_count < 16)
    {
        fn_node.dependencies[fn_node.dependency_count++] = to_id;
    }
}

fn bool msp_graph_dfs_cycle_check(MspSpliceGraph* g, int node_id)
{
    if (node_id < 0 || (usz)node_id >= g.node_count) return true;
    MspSpliceNode* n = &g.nodes[(usz)node_id];
    if (n.is_in_stack)
    {
        if (g.errors < 64)
        {
            char* msg = (char*)"msp splice graph error: cyclic stage dependency detected across quotation and splice boundaries";
            char* dst = &g.error_msgs[g.errors][0];
            usz i = 0;
            while (msg[i] != 0 && i < 255) { dst[i] = msg[i]; i++; }
            dst[i] = 0;
            g.errors++;
        }
        return false;
    }
    if (n.is_visited) return true;
    n.is_visited = true;
    n.is_in_stack = true;
    for (int i = 0; i < n.dependency_count; i++)
    {
        if (!msp_graph_dfs_cycle_check(g, n.dependencies[i]))
        {
            n.is_in_stack = false;
            return false;
        }
    }
    n.is_in_stack = false;
    return true;
}

fn bool MspSpliceGraph.verify_acyclic(MspSpliceGraph* g)
{
    for (usz i = 0; i < g.node_count; i++)
    {
        g.nodes[i].is_visited = false;
        g.nodes[i].is_in_stack = false;
    }
    for (usz i = 0; i < g.node_count; i++)
    {
        if (!g.nodes[i].is_visited)
        {
            if (!msp_graph_dfs_cycle_check(g, (int)i)) return false;
        }
    }
    return g.errors == 0;
}

// ── Contextual Modal Type Theory (CMTT) Diagnostic Ledger ───────────────────
// Formats an explicit human-readable diagnostic ledger of open code environments
// Γ', stage levels, and free variable bindings for compiler stage inspection.

struct MspCmttLedgerEntry
{
    int   stage_level;
    char* var_name;
    usz   var_len;
    Node* type_node;
    bool  is_spliced_binding;
}

struct MspCmttLedger
{
    MspCmttLedgerEntry[256] entries;
    usz                     count;
    int                     max_stage_seen;
}

fn void MspCmttLedger.init(MspCmttLedger* l)
{
    l.count = 0;
    l.max_stage_seen = 0;
}

fn void MspCmttLedger.record_binding(MspCmttLedger* l, int stage, char* name, usz len, Node* type_node, bool spliced)
{
    if (l.count >= 256) return;
    usz idx = l.count++;
    l.entries[idx].stage_level        = stage;
    l.entries[idx].var_name           = name;
    l.entries[idx].var_len            = len;
    l.entries[idx].type_node          = type_node;
    l.entries[idx].is_spliced_binding = spliced;
    if (stage > l.max_stage_seen) l.max_stage_seen = stage;
}

fn usz MspCmttLedger.format_ledger(MspCmttLedger* l, char* buf, usz cap)
{
    if (buf == null || cap == 0) return 0;
    buf[0] = 0;
    usz pos = 0;
    char* hdr = (char*)"=== Contextual Modal Type Theory (CMTT) Open Code Ledger ===\n";
    usz hl = 0; while (hdr[hl] != 0 && pos < cap - 1) { buf[pos++] = hdr[hl++]; }

    for (usz i = 0; i < l.count && pos < cap - 48; i++)
    {
        MspCmttLedgerEntry* e = &l.entries[i];
        char* tag = e.is_spliced_binding ? (char*)"[SPLICE_VAR] " : (char*)"[MODAL_VAR]  ";
        usz tl = 0; while (tag[tl] != 0 && pos < cap - 1) { buf[pos++] = tag[tl++]; }
        buf[pos++] = 'L';
        if (e.stage_level >= 0 && e.stage_level <= 9)
        {
            buf[pos++] = (char)('0' + e.stage_level);
        }
        else
        {
            buf[pos++] = '+';
        }
        buf[pos++] = ':';
        buf[pos++] = ' ';
        if (e.var_name != null)
        {
            for (usz k = 0; k < e.var_len && pos < cap - 16; k++)
            {
                buf[pos++] = e.var_name[k];
            }
        }
        buf[pos++] = '\n';
    }
    buf[pos] = 0;
    return pos;
}
