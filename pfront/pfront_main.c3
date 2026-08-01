// ============================================================================
// pfront_main.c3 — driver for the new front end (part 4)
// ----------------------------------------------------------------------------
// Usage:
//   pfront <file.pie> [options]
//     -I <dir>      add a module search root (repeatable)
//     --dump-ast    print the resolved AST
//     --dump-mods   print the module graph
//     --quiet       diagnostics + summary only
//     --sweep <dir> compile every .pie under <dir>, print ok/fail totals
//
// Exit codes:
//   0  clean
//   1  warnings only
//   2  errors  <- unresolved imports land here, unlike the old front end
// ============================================================================

module pfront_main;

import pfront_lex;
import pfront_core;
import pfront_parse;
import pfront_resolve;
import pfront_ext;
import pfront_sema;
import pfront_flow;
import theory_check;
import pfront_source;
import pfront_types;
import pfront_infer;
import pfront_narrow;
import pfront_check;
import pfront_dump;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);
extern fn int   strncmp(char* a, char* b, usz n);

alias Node = pfront_core::PNode;
alias Nk   = pfront_core::NodeKind;

fn usz slen(char* s)
{
    if (s == null) { return 0; }
    usz n = 0;
    while (s[n] != 0) { n = n + 1; }
    return n;
}

fn bool streq(char* a, char* b)
{
    usz la = slen(a);
    usz lb = slen(b);
    if (la != lb) { return false; }
    for (usz i = 0; i < la; i++) { if (a[i] != b[i]) { return false; } }
    return true;
}

// ── AST dump ────────────────────────────────────────────────────────────────
fn void indent_by(int n)
{
    for (int i = 0; i < n; i++) { printf("  "); }
}

fn void dump_node(Node* n, pfront_core::Interner* it, int depth)
{
    if (n == null || depth > 40) { return; }
    indent_by(depth);
    printf("%s", pfront_core::kind_name(n.kind));
    if (n.name_id != 0)
    {
        char* nm = it.text(n.name_id);
        if (nm != null) { printf(" '%s'", nm); }
    }
    if (n.kind == Nk.N_EXPR_INT) { printf(" = %llu", n.p.ival); }
    if (n.kind == Nk.N_EXPR_BOOL) { printf(" = %s", n.p.ival != 0 ? "true" : "false"); }
    if (n.resolved != null)
    {
        printf("  -> %s", pfront_core::kind_name(n.resolved.kind));
        if (n.resolved.name_id != 0)
        {
            char* rn = it.text(n.resolved.name_id);
            if (rn != null) { printf(" '%s'", rn); }
        }
    }
    else if (n.kind == Nk.N_EXPR_IDENT)
    {
        // A module-path segment (the `lib` in `lib.add(x)`) names a MODULE,
        // not a value, so it has no declaration to point at. The resolver
        // flags it NF_RESOLVED to say "handled, deliberately no target".
        // Printing UNRESOLVED for it made a correct build look broken.
        if ((n.flags & pfront_core::NF_RESOLVED) != 0) { printf("  [module]"); }
        else { printf("  [UNRESOLVED]"); }
    }
    if ((n.flags & pfront_core::NF_PUB) != 0) { printf(" +pub"); }
    if ((n.flags & pfront_core::NF_MUT) != 0) { printf(" +mut"); }
    printf("  (%d:%d)\n", n.line, n.col);
    if (n.type_ann != null)
    {
        indent_by(depth + 1);
        printf(": type\n");
        dump_node(n.type_ann, it, depth + 2);
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        dump_node(n.children[i], it, depth + 1);
    }
}

// ── AST integrity check ─────────────────────────────────────────────────────
// Verifies the invariants the parser promises, so a structural bug shows up
// here rather than as mysterious behaviour three passes downstream.
struct Verifier
{
    usz nodes;
    usz bad_parent;
    usz null_children;
    usz unresolved_idents;
    usz resolved_idents;
    usz orphan_types;
    int max_depth;
}

fn void Verifier.init(Verifier* v)
{
    v.nodes = 0;
    v.bad_parent = 0;
    v.null_children = 0;
    v.unresolved_idents = 0;
    v.resolved_idents = 0;
    v.orphan_types = 0;
    v.max_depth = 0;
}

fn void Verifier.walk(Verifier* v, Node* n, Node* expect_parent, int depth)
{
    if (n == null) { return; }
    if (depth > 200) { return; }
    v.nodes = v.nodes + 1;
    if (depth > v.max_depth) { v.max_depth = depth; }
    if (expect_parent != null && n.parent != expect_parent) { v.bad_parent = v.bad_parent + 1; }
    if (n.kind == Nk.N_EXPR_IDENT)
    {
        // A module-path PREFIX (`os` in `os.linux.malloc(n)`) names a module,
        // not a value, so it has no declaration to point `resolved`/`sym` at.
        // The resolver records that it was accounted for by setting
        // NF_RESOLVED (see mark_chain_resolved). Counting purely on the two
        // pointers reported 3,389 phantom "unresolved" identifiers across the
        // stdlib while the compiler emitted ZERO errors -- a number that
        // invited exactly the wrong conclusion about front-end health.
        bool accounted = n.resolved != null || n.sym != null
                      || (n.flags & pfront_core::NF_RESOLVED) != 0;
        if (!accounted) { v.unresolved_idents = v.unresolved_idents + 1; }
        else { v.resolved_idents = v.resolved_idents + 1; }
    }
    if (pfront_core::is_type(n.kind) && n.kind == Nk.N_TY_NAME)
    {
        if (n.resolved == null && n.sym == null) { v.orphan_types = v.orphan_types + 1; }
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        if (n.children[i] == null) { v.null_children = v.null_children + 1; continue; }
        v.walk(n.children[i], n, depth + 1);
    }
    if (n.type_ann != null) { v.walk(n.type_ann, null, depth + 1); }
}

fn void Verifier.report(Verifier* v)
{
    printf("  ast nodes        : %d\n", (int)v.nodes);
    printf("  max depth        : %d\n", v.max_depth);
    printf("  idents resolved  : %d\n", (int)v.resolved_idents);
    printf("  idents unresolved: %d\n", (int)v.unresolved_idents);
    printf("  unbound ty-names : %d\n", (int)v.orphan_types);
    printf("  broken parents   : %d\n", (int)v.bad_parent);
    printf("  null children    : %d\n", (int)v.null_children);
}

// ── Compile one file ────────────────────────────────────────────────────────
struct RunResult
{
    usz errors;
    usz warnings;
    usz modules;
    usz nodes;
    usz resolved;
    usz unresolved;
    bool ok;
}

// Diagnostics record (line, col) in the file they came from. Convert that back
// into a global span so the renderer can locate the snippet. Falls back to a
// zero span when the file is not in the map, which the renderer handles.
fn pfront_source::Span span_for_diag(pfront_source::SourceMap* m, pfront_core::Diag* d)
{
    if (m == null || d.file == null) { return pfront_source::span_empty(); }
    for (usz i = 0; i < m.file_count; i++)
    {
        pfront_source::SourceFile* f = &m.files[i];
        if (!path_eq(f.path, d.file)) { continue; }
        if (d.line <= 0) { return pfront_source::span_empty(); }
        usz li = (usz)(d.line - 1);
        if (li >= f.line_count) { return pfront_source::span_empty(); }
        uint ls = f.line_start(li);
        uint le = f.line_end(li);
        // d.col is a 1-based BYTE column as recorded by the lexer.
        uint off = ls + (uint)(d.col > 0 ? d.col - 1 : 0);
        if (off > le) { off = le; }
        uint start = f.base_offset + off;
        // Highlight to the end of the current token-ish run for a useful caret.
        uint stop = off;
        while (stop < le)
        {
            char ch = f.text[stop];
            bool wordy = (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')
                      || (ch >= '0' && ch <= '9') || ch == '_';
            if (!wordy) { break; }
            stop = stop + 1;
        }
        if (stop == off) { stop = off + 1 <= le ? off + 1 : le; }
        return pfront_source::span_make(start, f.base_offset + stop);
    }
    return pfront_source::span_empty();
}

fn bool path_eq(char* a, char* b)
{
    if (a == null || b == null) { return false; }
    usz i = 0;
    while (a[i] != 0 && b[i] != 0)
    {
        if (a[i] != b[i]) { return false; }
        i = i + 1;
    }
    return a[i] == 0 && b[i] == 0;
}

fn RunResult compile_one(char* path, char*[] roots, usz root_count,
                         bool dump_ast, bool dump_mods, bool verify, bool quiet,
                         bool rich, int context_lines, bool strict_types,
                         bool report_dead, bool strict_vis, bool run_theory,
                         bool lint, bool optimize, int opt_level,
                         bool emit_ast, bool emit_sexp, bool time_passes,
                         bool dump_cfg)
{
    RunResult rr;
    rr.errors = 0; rr.warnings = 0; rr.modules = 0;
    rr.nodes = 0; rr.resolved = 0; rr.unresolved = 0; rr.ok = false;

    pfront_core::Arena* arena = (pfront_core::Arena*)malloc(pfront_core::Arena::size);
    if (arena == null) { return rr; }
    if (!arena.init()) { free((void*)arena); return rr; }

    pfront_core::Interner* it = (pfront_core::Interner*)malloc(pfront_core::Interner::size);
    if (it == null) { arena.destroy(); free((void*)arena); return rr; }
    it.init(arena);

    pfront_core::DiagBag* diags = (pfront_core::DiagBag*)malloc(pfront_core::DiagBag::size);
    if (diags == null) { arena.destroy(); free((void*)arena); free((void*)it); return rr; }
    diags.init();
    // Pride is untyped. Type/mutability advice is OFF unless `--lint` asks.
    diags.advisories = lint;

    pfront_resolve::Loader* ld = (pfront_resolve::Loader*)malloc(pfront_resolve::Loader::size);
    if (ld == null) { arena.destroy(); free((void*)arena); free((void*)it); free((void*)diags); return rr; }
    ld.init(arena, it, diags);

    // Source map: registers every file the loader reads so diagnostics can be
    // rendered with a snippet and a caret instead of a bare line:col.
    pfront_source::SourceMap* smap =
        (pfront_source::SourceMap*)malloc(pfront_source::SourceMap::size);
    if (smap != null) { smap.init(arena); ld.attach_source_map(smap); }
    for (usz i = 0; i < root_count; i++) { ld.add_root(roots[i]); }

    pfront_core::Module* entry = ld.load_entry(path);

    pfront_resolve::Resolver* rs =
        (pfront_resolve::Resolver*)malloc(pfront_resolve::Resolver::size);
    if (rs != null)
    {
        rs.init(arena, it, diags, ld);
        rs.resolve_all();
        rr.resolved = rs.resolved_count;
        rr.unresolved = rs.unresolved_count;
    }

    if (dump_mods) { ld.report(); }

    if (dump_ast && entry != null && entry.ast != null)
    {
        printf("=== AST (%s) ===\n", path);
        dump_node(entry.ast, it, 0);
    }

    if (verify && entry != null && entry.ast != null)
    {
        Verifier v;
        v.init();
        v.walk(entry.ast, null, 0);
        if (!quiet)
        {
            printf("=== AST verification ===\n");
            v.report();
        }
        rr.nodes = v.nodes;

        // Effect inference, lints and exhaustiveness run over the resolved
        // tree. They need `.resolved` populated, hence their position here.
        pfront_ext::EffectPass ep;
        ep.init();
        ep.run(entry.ast);

        pfront_ext::Linter lt;
        lt.init(diags, it, path);
        lt.walk(entry.ast, 0);

        pfront_ext::ExhaustCheck xc;
        xc.init(diags, path);
        xc.walk(entry.ast, 0);

        // ---- semantic analyses (SCC, visibility, usefulness, cycles) ----
        // The SCC graph carries large CSR arrays; heap-allocate it rather
        // than putting ~150 KB on the stack.
        pfront_sema::ModuleGraph* mg =
            (pfront_sema::ModuleGraph*)malloc(pfront_sema::ModuleGraph::size);
        if (mg != null) { mg.build(ld); }

        pfront_sema::VisibilityCheck vc;
        vc.init(diags, it, path);
        vc.enforce = strict_vis;
        vc.walk(entry.ast, entry, 0);

        pfront_sema::PatternAnalysis pa;
        pa.init(diags, it, path);
        pa.walk(entry.ast, 0);

        // ---- type inference (fills type_slot / NF_TYPED) ----
        pfront_types::TypeTable* tt =
            (pfront_types::TypeTable*)malloc(pfront_types::TypeTable::size);
        pfront_infer::Inferencer* inf = null;
        if (tt != null)
        {
            tt.init();
            inf = (pfront_infer::Inferencer*)malloc(pfront_infer::Inferencer::size);
            if (inf != null)
            {
                inf.init(tt, diags, it, path);
                inf.strict = strict_types;
                inf.run(entry.ast);
            }
        }

        // ---- substantive checking: traits, coercions, narrowing, access ----
        pfront_check::Checker* ckr =
            (pfront_check::Checker*)malloc(pfront_check::Checker::size);
        if (ckr != null && tt != null)
        {
            ckr.init(arena, tt, diags, it, path);
            ckr.strict = strict_types;
            ckr.run(entry.ast);
        }

        pfront_sema::ConstEval ce;
        ce.init(diags, path);
        ce.walk(entry.ast, 0);

        // ---- call graph, recursion, reachability, effect fixpoint ----
        pfront_flow::CallGraph* cg =
            (pfront_flow::CallGraph*)malloc(pfront_flow::CallGraph::size);
        pfront_sema::SccGraph* cg_scc =
            (pfront_sema::SccGraph*)malloc(pfront_sema::SccGraph::size);
        int eff_rounds = 0;
        if (cg != null)
        {
            cg.init();
            cg.build(entry.ast, it);
            cg.compute_reachability();
            if (cg_scc != null) { cg.compute_recursion(cg_scc); }
            eff_rounds = cg.propagate_effects();
            if (report_dead) { cg.report_dead(diags, it, path); }
        }

        // ---- intra-procedural control flow ----
        pfront_flow::FlowAnalysis fa;
        fa.init(diags, it, path);
        fa.run(entry.ast);

        pfront_sema::TypeCycleCheck tcc;
        tcc.init(diags, it, path);
        tcc.walk(entry.ast, 0);

        // ---- theory layer: MSP/CMTT, TRS, IRDL, PGL, effects, UB, sorts ----
        theory_check::TheoryPipeline* tp =
            (theory_check::TheoryPipeline*)malloc(theory_check::TheoryPipeline::size);
        bool theory_ok = false;
        if (tp != null && run_theory)
        {
            theory_ok = tp.init(arena, diags, it, path);
            if (theory_ok)
            {
                tp.strict_sorts = strict_types;
                tp.timing = time_passes;
                tp.dump_cfg = dump_cfg;
                tp.optimize = optimize;
                tp.opt_level = opt_level;
                entry.ast = tp.run(entry.ast);
            }
        }

        // The FINAL tree: after rewriting, partial evaluation, e-graph
        // extraction and the optimizer. This is what the middle end will
        // consume, so it is the tree worth looking at.
        if (emit_ast)
        {
            pfront_dump::emit_ast(entry.ast, it, path, emit_sexp);
        }

        pfront_ext::Stats st;
        st.init();
        st.walk(entry.ast, 0);

        // Attach did-you-mean hints by matching each unresolved identifier
        // against the names actually in scope for its module.
        pfront_ext::Suggester sug;
        sug.init(it);
        suggest_for_unresolved(entry.ast, &sug, it, diags, path, 0);

        if (!quiet)
        {
            printf("=== effects ===\n");
            ep.report();
            printf("=== lints ===\n");
            lt.report();
            xc.report();
            printf("=== types ===\n");
            if (tt != null) { tt.report(); }
            if (inf != null) { inf.report(); }
            if (ckr != null) { ckr.report(); }
            printf("=== semantics ===\n");
            if (mg != null) { mg.report(ld); }
            vc.report();
            pa.report();
            ce.report();
            tcc.report();
            if (cg != null) { cg.report(it); }
            printf("  effect fixpoint  : %d rounds\n", eff_rounds);
            fa.report();
            if (theory_ok && tp != null) { tp.report(); }
            printf("=== ast statistics ===\n");
            st.report(it);
            sug.report();
            if (dump_ast) { st.report_histogram(12); }
        }
        if (cg_scc != null) { free((void*)cg_scc); }
        if (cg != null) { free((void*)cg); }
        if (ckr != null) { free((void*)ckr); }
        if (inf != null) { free((void*)inf); }
        if (tt != null) { free((void*)tt); }
        if (theory_ok && tp != null) { tp.destroy(); }
        if (tp != null) { free((void*)tp); }
        if (mg != null) { free((void*)mg); }
    }

    rr.errors = diags.error_count;
    rr.warnings = diags.warning_count;
    rr.modules = ld.module_count;
    rr.ok = diags.error_count == 0;

    if (!quiet && diags.count > 0)
    {
        printf("=== diagnostics (%d) ===\n", (int)diags.count);
        if (smap != null && rich)
        {
            pfront_source::Renderer rend;
            rend.init(smap);
            rend.show_snippets = true;
            rend.context_lines = context_lines;
            for (usz i = 0; i < diags.count; i++)
            {
                pfront_core::Diag* d = &diags.items[i];
                rend.render(d, span_for_diag(smap, d));
            }
            rend.summary();
        }
        else { diags.dump(); }
    }
    if (!quiet && rs != null)
    {
        printf("=== resolution ===\n");
        rs.report();
    }

    if (rs != null) { free((void*)rs); }
    free((void*)ld);
    free((void*)diags);
    free((void*)it);
    arena.destroy();
    free((void*)arena);
    return rr;
}

fn int main(String[] args)
{
    if (args.len < 2)
    {
        printf("pfront — Pride front end (parse + resolve + module load)\n");
            printf("usage: pfront <file.pie> [-I dir] [options]\n");
        printf("  -I <dir>       add a module search root (repeatable)\n");
        printf("  --dump-ast     print the resolved AST\n");
        printf("  --dump-mods    print the module graph\n");
        printf("  --context <n>  lines of context around each diagnostic\n");
        printf("  --plain        one-line diagnostics (no snippets)\n");
        printf("  --strict-types report type mismatches as errors\n");
        printf("  --dead-code    warn about functions no entry point reaches\n");
        printf("  --strict-vis   enforce pub/private across module boundaries\n");
        printf("  --no-theory    skip the MSP/TRS/IRDL/effects theory layer\n");
        printf("  --quiet        summary only\n");
        return 2;
    }

    char*[16] roots;
    usz root_count = 0;
    char* input = null;
    bool dump_ast = false;
    bool dump_mods = false;
    bool quiet = false;
    bool verify = true;
    bool rich = true;
    int  context_lines = 0;
    bool strict_types = false;
    bool report_dead = false;
    bool strict_vis = false;
    bool run_theory = true;
    bool lint = false;
    bool emit_ast = false;
    bool emit_sexp = false;
    bool time_passes = false;
    bool dump_cfg = false;
    bool optimize = true;
    int  opt_level = 2;

    for (usz i = 1; i < args.len; i++)
    {
        char* a = (char*)args[i].ptr;
        if (streq(a, "-I"))
        {
            if (i + 1 < args.len && root_count < 16)
            {
                roots[root_count] = (char*)args[i + 1].ptr;
                root_count = root_count + 1;
                i = i + 1;
            }
        }
        else if (streq(a, "--dump-ast"))  { dump_ast = true; }
        else if (streq(a, "--dump-mods")) { dump_mods = true; }
        else if (streq(a, "--quiet"))     { quiet = true; }
        else if (streq(a, "--no-verify")) { verify = false; }
        else if (streq(a, "--plain"))     { rich = false; }
        else if (streq(a, "--strict-types")) { strict_types = true; }
        else if (streq(a, "--dead-code"))    { report_dead = true; }
        else if (streq(a, "--strict-vis"))   { strict_vis = true; }
        else if (streq(a, "--no-theory"))    { run_theory = false; }
        else if (streq(a, "--lint"))         { lint = true; }
        else if (streq(a, "--emit-ast"))     { emit_ast = true; }
        else if (streq(a, "--emit-sexp"))    { emit_ast = true; emit_sexp = true; }
        else if (streq(a, "--time-passes"))  { time_passes = true; }
        else if (streq(a, "--dump-cfg"))     { dump_cfg = true; }
        else if (streq(a, "--no-opt"))       { optimize = false; }
        else if (streq(a, "-O0")) { opt_level = 0; optimize = false; }
        else if (streq(a, "-O1")) { opt_level = 1; }
        else if (streq(a, "-O2")) { opt_level = 2; }
        else if (streq(a, "-O3")) { opt_level = 3; }
        else if (streq(a, "--context"))
        {
            if (i + 1 < args.len)
            {
                char* v = (char*)args[i + 1].ptr;
                int nctx = 0;
                usz k = 0;
                while (v[k] >= '0' && v[k] <= '9') { nctx = nctx * 10 + (int)(v[k] - '0'); k = k + 1; }
                if (nctx > 8) { nctx = 8; }
                context_lines = nctx;
                i = i + 1;
            }
        }
        else if (a[0] != '-')             { input = a; }
    }

    if (input == null) { printf("error: no input file\n"); return 2; }

    if (root_count == 0)
    {
        roots[0] = (char*)".";
        roots[1] = (char*)"stdlib";
        root_count = 2;
    }

    RunResult rr = compile_one(input, roots[..], root_count,
                               dump_ast, dump_mods, verify, quiet,
                               rich, context_lines, strict_types, report_dead, strict_vis, run_theory,
                               lint, optimize, opt_level, emit_ast, emit_sexp, time_passes, dump_cfg);

    if (!quiet)
    {
        printf("=== summary ===\n");
        printf("  modules   : %d\n", (int)rr.modules);
        printf("  errors    : %d\n", (int)rr.errors);
        printf("  warnings  : %d\n", (int)rr.warnings);
    }
    else
    {
        printf("%s: errors=%d warnings=%d modules=%d\n",
               input, (int)rr.errors, (int)rr.warnings, (int)rr.modules);
    }

    if (rr.errors > 0) { return 2; }
    if (rr.warnings > 0) { return 1; }
    return 0;
}

// Collect the names a module declares, so suggestions come from real symbols
// rather than the whole intern table.
fn usz collect_decl_names(Node* n, uint* out, usz cap, usz count, int depth)
{
    if (n == null || depth > 60 || count >= cap) { return count; }
    if (pfront_core::is_decl(n.kind) && n.name_id != 0)
    {
        bool dup = false;
        for (usz i = 0; i < count; i++) { if (out[i] == n.name_id) { dup = true; } }
        if (!dup) { out[count] = n.name_id; count = count + 1; }
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        count = collect_decl_names(n.children[i], out, cap, count, depth + 1);
    }
    return count;
}

fn void suggest_for_unresolved(Node* root, pfront_ext::Suggester* sug,
                               pfront_core::Interner* it,
                               pfront_core::DiagBag* diags,
                               char* file, int depth)
{
    uint[512] names;
    usz n = collect_decl_names(root, &names[0], 512, 0, 0);
    if (n == 0) { return; }
    walk_suggest(root, sug, &names[0], n, it, diags, file, 0);
}

fn void walk_suggest(Node* node, pfront_ext::Suggester* sug,
                     uint* names, usz name_count,
                     pfront_core::Interner* it, pfront_core::DiagBag* diags,
                     char* file, int depth)
{
    if (node == null || depth > 200) { return; }
    if (node.kind == Nk.N_EXPR_IDENT && node.resolved == null
        && node.sym == null && node.name_id != 0)
    {
        uint m = sug.best_match(node.name_id, names, name_count);
        if (m != 0)
        {
            char* cand = it.text(m);
            if (cand != null)
            {
                diags.add(pfront_core::Severity.SEV_NOTE,
                          pfront_core::Phase.PH_RESOLVE, 3005,
                          node.line, node.col,
                          "a similarly named declaration exists", cand, file);
            }
        }
    }
    for (usz i = 0; i < node.child_count; i++)
    {
        walk_suggest(node.children[i], sug, names, name_count, it, diags, file, depth + 1);
    }
}
