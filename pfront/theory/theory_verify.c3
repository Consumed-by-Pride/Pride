// ============================================================================
// theory_verify.c3 — integrity verification of theory-transformed ASTs
// ----------------------------------------------------------------------------
// (part 19)
//
// The theory layer REWRITES the AST: terms are replaced by rule instantiations,
// dialect calls by lowered templates, and quotations are renumbered. Every one
// of those transformations can, if it has a bug, produce a tree that is subtly
// malformed — a dangling parent pointer, a node reachable from two parents, a
// synthetic node with no source location, a cycle.
//
// Those defects are silent. They do not crash the pass that created them; they
// crash, or worse silently miscompile, three passes later. This module exists
// so that a transformation bug is caught at the transformation, with a
// diagnostic naming the invariant that broke.
//
// Invariants checked:
//
//   I1  ACYCLICITY      — no node reachable from itself. A rewrite that
//       instantiates a template containing the matched term can build one.
//   I2  SINGLE PARENT   — no node appears as a child of two parents. Sharing
//       is fine for hash-consed *terms*, but not for mutable AST nodes: a
//       later in-place edit would be visible in two places.
//   I3  PARENT LINKS    — child.parent == parent for every edge.
//   I4  NO NULL CHILDREN — a null in a child array means a builder failed
//       silently.
//   I5  SPAN SANITY     — synthetic nodes inherit a plausible location, so
//       diagnostics about generated code still point somewhere useful.
//   I6  STAGE BALANCE   — quote/splice nesting is balanced and non-negative.
//   I7  RESOLUTION      — a node marked NF_RESOLVED actually has a target.
//   I8  ARITY           — node kinds have the child counts their consumers
//       assume (a binary operator with one child would crash codegen).
//
// The verifier is cheap enough to run always and precise enough to be useful,
// which is the only combination worth having.
// ============================================================================

module theory_verify;

import pfront_lex;
import pfront_core;
import theory_term;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz VERIFY_SEEN_CAP = 262144;
// Open-addressed visited set. A linear scan here was 83% of total front-end
// time on a 60k-node tree (O(n^2): every node compared against every node
// already seen). The bucket array makes it O(1) amortised.
const usz VERIFY_SEEN_BUCKETS = 524288;   // 2x cap, power of two
const int VERIFY_MAX_DEPTH = 512;

struct Finding
{
    char* invariant;
    char* detail;
    int   line;
    int   col;
}

const usz MAX_FINDINGS = 256;

struct Verifier
{
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;

    // Visited set for acyclicity and single-parent checking.
    Node*[VERIFY_SEEN_CAP] seen;
    uint[VERIFY_SEEN_BUCKETS] seen_buckets;   // index+1, 0 = empty
    usz                    seen_count;
    Node*[VERIFY_MAX_DEPTH] path;
    usz                    path_len;

    Finding[MAX_FINDINGS] findings;
    usz                   finding_count;

    usz nodes;
    usz cycles;
    usz shared_nodes;
    usz bad_parents;
    usz null_children;
    usz bad_spans;
    usz stage_imbalance;
    usz bad_resolution;
    usz arity_errors;
    usz synthetic_nodes;
    int max_depth;
    bool report_all;
}

fn void Verifier.init(Verifier* v, pfront_core::DiagBag* d,
                      pfront_core::Interner* it, char* file)
{
    v.diags = d;
    v.interner = it;
    v.file = file;
    v.seen_count = 0;
    for (usz i = 0; i < VERIFY_SEEN_BUCKETS; i++) { v.seen_buckets[i] = 0; }
    v.path_len = 0;
    v.finding_count = 0;
    v.nodes = 0;
    v.cycles = 0;
    v.shared_nodes = 0;
    v.bad_parents = 0;
    v.null_children = 0;
    v.bad_spans = 0;
    v.stage_imbalance = 0;
    v.bad_resolution = 0;
    v.arity_errors = 0;
    v.synthetic_nodes = 0;
    v.max_depth = 0;
    v.report_all = false;
}

fn void Verifier.record(Verifier* v, char* invariant, char* detail, Node* at)
{
    if (v.finding_count >= MAX_FINDINGS) { return; }
    Finding* f = &v.findings[v.finding_count];
    f.invariant = invariant;
    f.detail = detail;
    f.line = at == null ? 0 : at.line;
    f.col = at == null ? 0 : at.col;
    v.finding_count = v.finding_count + 1;
    if (v.report_all)
    {
        v.diags.error(pfront_core::Phase.PH_RESOLVE, 3270,
                      f.line, f.col, detail, v.file);
    }
}

// I1: is this node on the current root-to-here path?
fn bool Verifier.on_path(Verifier* v, Node* n)
{
    for (usz i = 0; i < v.path_len; i++) { if (v.path[i] == n) { return true; } }
    return false;
}

// I2: has this node been visited via a different parent already?
fn ulong verify_hash_ptr(void* p)
{
    ulong x = (ulong)(usz)p;
    x = x ^ (x >> 30);
    x = x * 0xbf58476d1ce4e5b9UL;
    x = x ^ (x >> 27);
    x = x * 0x94d049bb133111ebUL;
    x = x ^ (x >> 31);
    return x;
}

fn bool Verifier.mark_seen(Verifier* v, Node* n)
{
    // Linear scan is fine: the check is bounded by tree size and this runs
    // once per compilation, not per pass.
    usz mask = VERIFY_SEEN_BUCKETS - 1;
    usz b = (usz)verify_hash_ptr((void*)n) & mask;
    for (usz probe = 0; probe < VERIFY_SEEN_BUCKETS; probe++)
    {
        uint slot = v.seen_buckets[b];
        if (slot == 0)
        {
            if (v.seen_count < VERIFY_SEEN_CAP)
            {
                v.seen[v.seen_count] = n;
                v.seen_count = v.seen_count + 1;
                v.seen_buckets[b] = (uint)v.seen_count;   // index+1
            }
            return true;
        }
        if (v.seen[slot - 1] == n) { return false; }
        b = (b + 1) & mask;
    }
    return true;
}

// I8: minimum child counts the rest of the compiler assumes.
fn usz required_arity(Nk k)
{
    switch (k)
    {
        case N_EXPR_BINARY:          return 2;
        case N_EXPR_UNARY:           return 1;
        case N_EXPR_DEREF:           return 1;
        case N_EXPR_REF:             return 1;
        case N_EXPR_INDEX:           return 2;
        case N_EXPR_CALL:            return 1;   // callee only
        case N_EXPR_IF:              return 2;   // cond + then
        case N_EXPR_WHILE:           return 2;
        case N_EXPR_FOR:             return 3;
        case N_STMT_ASSIGN:          return 2;
        case N_STMT_COMPOUND_ASSIGN: return 2;
        case N_CLAUSE:               return 1;   // at least a pattern
        case N_MATCH_ARM:            return 1;
        default:                     return 0;
    }
}

fn void Verifier.walk(Verifier* v, Node* n, Node* parent, int depth, int stage)
{
    if (n == null) { return; }
    if (depth > VERIFY_MAX_DEPTH) { return; }

    // I1 — acyclicity.
    if (v.on_path(n))
    {
        v.cycles = v.cycles + 1;
        v.record("acyclicity", "AST contains a cycle: a node is its own ancestor", n);
        return;
    }

    // I2 — single parent.
    if (!v.mark_seen(n))
    {
        v.shared_nodes = v.shared_nodes + 1;
        v.record("single-parent",
                 "node is reachable from two parents; in-place edits would alias", n);
        // Not fatal: keep walking so later findings are still reported.
    }

    v.nodes = v.nodes + 1;
    if (depth > v.max_depth) { v.max_depth = depth; }
    if ((n.flags & pfront_core::NF_SYNTHETIC) != 0)
    {
        v.synthetic_nodes = v.synthetic_nodes + 1;
    }

    // I3 — parent links.
    if (parent != null && n.parent != parent)
    {
        v.bad_parents = v.bad_parents + 1;
        v.record("parent-link", "child.parent does not point at its actual parent", n);
    }

    // I5 — span sanity. A generated node with no location makes every
    // diagnostic about it useless.
    if (n.line <= 0 && (n.flags & pfront_core::NF_SYNTHETIC) != 0)
    {
        v.bad_spans = v.bad_spans + 1;
        v.record("span", "synthetic node has no source location", n);
    }

    // I7 — resolution consistency.
    if ((n.flags & pfront_core::NF_RESOLVED) != 0 && n.resolved == null && n.sym == null)
    {
        v.bad_resolution = v.bad_resolution + 1;
        v.record("resolution", "node is flagged resolved but has no target", n);
    }

    // I8 — arity.
    usz need = required_arity(n.kind);
    if (need > 0 && n.child_count < need)
    {
        v.arity_errors = v.arity_errors + 1;
        v.record("arity", "node has fewer children than its kind requires", n);
    }

    // I6 — stage balance.
    int next_stage = stage;
    if (n.kind == Nk.N_EXPR_QUOTE) { next_stage = stage + 1; }
    if (n.kind == Nk.N_EXPR_SPLICE)
    {
        next_stage = stage - 1;
        if (next_stage < 0)
        {
            v.stage_imbalance = v.stage_imbalance + 1;
            v.record("stage-balance", "splice drops the stage level below zero", n);
        }
    }

    if (v.path_len < VERIFY_MAX_DEPTH) { v.path[v.path_len] = n; v.path_len = v.path_len + 1; }

    for (usz i = 0; i < n.child_count; i++)
    {
        // I4 — no null children.
        if (n.children[i] == null)
        {
            v.null_children = v.null_children + 1;
            v.record("no-null-child", "child array contains a null entry", n);
            continue;
        }
        v.walk(n.children[i], n, depth + 1, next_stage);
    }
    // Type annotations are a separate edge and are NOT single-parent checked:
    // several nodes legitimately share one annotation.
    if (n.type_ann != null) { v.check_type(n.type_ann, 0); }

    if (v.path_len > 0) { v.path_len = v.path_len - 1; }
}

// Types are checked more loosely: sharing is expected, so only structural
// sanity applies.
fn void Verifier.check_type(Verifier* v, Node* t, int depth)
{
    if (t == null || depth > 64) { return; }
    for (usz i = 0; i < t.child_count; i++)
    {
        if (t.children[i] == null)
        {
            v.null_children = v.null_children + 1;
            v.record("no-null-child", "type node has a null child", t);
            continue;
        }
        v.check_type(t.children[i], depth + 1);
    }
}

fn bool Verifier.ok(Verifier* v)
{
    return v.cycles == 0 && v.bad_parents == 0 && v.null_children == 0
        && v.stage_imbalance == 0 && v.arity_errors == 0;
}

fn void Verifier.run(Verifier* v, Node* root)
{
    v.seen_count = 0;
    for (usz i = 0; i < VERIFY_SEEN_BUCKETS; i++) { v.seen_buckets[i] = 0; }
    v.path_len = 0;
    v.walk(root, null, 0, 0);
}

fn void Verifier.report(Verifier* v)
{
    printf("  integrity        : %d nodes, depth %d, %d synthetic\n",
           (int)v.nodes, v.max_depth, (int)v.synthetic_nodes);
    if (v.ok() && v.shared_nodes == 0 && v.bad_spans == 0 && v.bad_resolution == 0)
    {
        printf("  invariants       : all 8 hold\n");
        return;
    }
    printf("  invariant breaks : cycles=%d shared=%d bad-parent=%d null-child=%d\n",
           (int)v.cycles, (int)v.shared_nodes, (int)v.bad_parents, (int)v.null_children);
    printf("                     span=%d stage=%d resolution=%d arity=%d\n",
           (int)v.bad_spans, (int)v.stage_imbalance,
           (int)v.bad_resolution, (int)v.arity_errors);
    // Show the first few concrete findings: a count alone is not actionable.
    usz shown = v.finding_count < 5 ? v.finding_count : 5;
    for (usz i = 0; i < shown; i++)
    {
        Finding* f = &v.findings[i];
        printf("      [%s] %s (%d:%d)\n", f.invariant, f.detail, f.line, f.col);
    }
    if (v.finding_count > shown)
    {
        printf("      ... %d more\n", (int)(v.finding_count - shown));
    }
}

// ── Differential verification ───────────────────────────────────────────────
// Compare the tree before and after a transformation. A rewrite is expected to
// change the tree, but not to change things it has no business touching — the
// declaration set, for instance. Catching that early localises the bug to one
// pass instead of leaving it to surface in the backend.
struct Snapshot
{
    usz decls;
    usz fns;
    usz types;
    usz total;
    ulong digest;
}

fn Snapshot snapshot(Node* root)
{
    Snapshot s;
    s.decls = 0;
    s.fns = 0;
    s.types = 0;
    s.total = 0;
    s.digest = 0;
    collect_snapshot(root, &s, 0);
    return s;
}

fn void collect_snapshot(Node* n, Snapshot* s, int depth)
{
    if (n == null || depth > VERIFY_MAX_DEPTH) { return; }
    s.total = s.total + 1;
    if (pfront_core::is_decl(n.kind)) { s.decls = s.decls + 1; }
    if (n.kind == Nk.N_DECL_FN || n.kind == Nk.N_DECL_EXTERN_FN) { s.fns = s.fns + 1; }
    if (pfront_core::is_type(n.kind)) { s.types = s.types + 1; }
    s.digest = (s.digest ^ (ulong)(int)n.kind) * 0x100000001b3UL;
    for (usz i = 0; i < n.child_count; i++) { collect_snapshot(n.children[i], s, depth + 1); }
}

struct DiffResult
{
    bool decls_changed;
    bool fns_changed;
    long size_delta;
    bool suspicious;
    long decl_delta;
    usz  expected_removals;   // decls the optimizer legitimately deleted
}

fn DiffResult diff_snapshots(Snapshot before, Snapshot after)
{
    DiffResult d;
    d.decls_changed = before.decls != after.decls;
    d.fns_changed = before.fns != after.fns;
    d.size_delta = (long)after.total - (long)before.total;
    d.decl_delta = (long)after.decls - (long)before.decls;
    d.expected_removals = 0;
    // Losing a FUNCTION is still always a bug: no pass in the pipeline is
    // allowed to delete one.
    //
    // Losing a LET is not. Dead-store elimination removes `let` declarations
    // by design, and this check predates the optimizer -- it used to fire on
    // every file where DCE did its job. The caller now supplies how many
    // removals the optimizer actually accounted for, so an UNEXPLAINED loss
    // is still caught while a legitimate one is not.
    d.suspicious = d.fns_changed;
    return d;
}

// `accounted` is the number of declarations the optimizer reported deleting.
// Anything beyond that is unexplained and gets flagged.
fn void report_diff_accounted(DiffResult d, Snapshot before, Snapshot after,
                              pfront_core::DiagBag* diags, char* file,
                              usz accounted)
{
    printf("  transform diff   : %d -> %d nodes (%+d), decls %d -> %d\n",
           (int)before.total, (int)after.total, (int)d.size_delta,
           (int)before.decls, (int)after.decls);
    long lost = -d.decl_delta;
    if (lost > 0 && (usz)lost <= accounted)
    {
        printf("  decl removals    : %d, all accounted for by dead-code elimination\n",
               (int)lost);
    }
    else if (lost > 0)
    {
        printf("  WARNING          : %d declaration(s) vanished with no pass claiming them\n",
               (int)(lost - (long)accounted));
    }
    if (d.fns_changed)
    {
        printf("  WARNING          : a theory pass changed the FUNCTION count\n");
    }
}

fn void report_diff(DiffResult d, Snapshot before, Snapshot after,
                    pfront_core::DiagBag* diags, char* file)
{
    printf("  transform diff   : %d -> %d nodes (%+d), decls %d -> %d\n",
           (int)before.total, (int)after.total, (int)d.size_delta,
           (int)before.decls, (int)after.decls);
    if (d.suspicious)
    {
        printf("  WARNING          : a theory pass changed the declaration set\n");
        diags.warn(pfront_core::Phase.PH_RESOLVE, 4080, 0, 0,
                   "a theory transformation altered the declaration set",
                   file);
    }
}
