// ============================================================================
// pfront_resolve.c3 — Pride front-end: module loader + name resolver (part 3)
// ----------------------------------------------------------------------------
// This is the component the old front end never had. It does three jobs:
//
//   1. MODULE LOADING — maps a dotted path (`pride.core.mem`) to a file on
//      disk, reads it, lexes it, parses it, and caches it. Load-once, with
//      cycle detection, so a diamond import graph costs one parse per module.
//
//   2. EXPORT COLLECTION — walks each parsed module and records its public
//      declarations into the module's export table, keyed by (name_id, ns).
//
//   3. RESOLUTION — walks every function body binding each identifier to its
//      declaration, across module boundaries. Every N_EXPR_IDENT ends up with
//      `.resolved` pointing at a real decl, or a reported error. There is no
//      silent-success path: an unresolvable `use` is a hard error, which is
//      precisely the defect that let 253 stdlib modules "pass" before.
//
// Search-path semantics for `use a.b.c`, tried in order:
//      <root>/a/b/c.pie
//      <root>/a/b/c/mod.pie
//      <root>/a/b/c/c.pie
//      <root>/a.b.c.pie
// for each configured root, in registration order.
// ============================================================================

module pfront_resolve;

import pfront_lex;
import pfront_core;
import pfront_source;
import pfront_parse;

alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;
alias Mod   = pfront_core::Module;
alias Sym   = pfront_core::Symbol;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);
alias CFile = void*;
extern fn CFile fopen(char* path, char* mode);
extern fn int   fclose(CFile stream);
extern fn usz   fread(void* ptr, usz size, usz nmemb, CFile stream);
extern fn int   fseek(CFile stream, long offset, int whence);
extern fn long  ftell(CFile stream);

const int SEEK_SET_V = 0;
const int SEEK_END_V = 2;

const usz MAX_MODULES  = 1024;
const usz MAX_ROOTS    = 16;
const usz MAX_SCOPES   = 512;
const usz PATH_MAX_LEN = 1024;

// ── Loader ──────────────────────────────────────────────────────────────────
struct Loader
{
    Arena*                 arena;
    pfront_core::Interner* interner;
    pfront_core::DiagBag*  diags;

    char*[MAX_ROOTS]       roots;
    usz                    root_count;

    Mod*[MAX_MODULES]      modules;
    usz                    module_count;

    // Load stack, for cycle detection and error reporting.
    uint[64]               loading;
    usz                    loading_depth;

    usz                    files_read;
    usz                    parse_failures;
    bool                   verbose;

    // Optional source map: when present, every file read is registered so the
    // renderer can turn a byte offset back into a file/line/column + snippet.
    pfront_source::SourceMap* smap;
}

fn void Loader.init(Loader* l, Arena* a, pfront_core::Interner* it,
                    pfront_core::DiagBag* d)
{
    l.arena = a;
    l.interner = it;
    l.diags = d;
    l.root_count = 0;
    l.module_count = 0;
    l.loading_depth = 0;
    l.files_read = 0;
    l.parse_failures = 0;
    l.verbose = false;
    l.smap = null;
}

fn void Loader.attach_source_map(Loader* l, pfront_source::SourceMap* m)
{
    l.smap = m;
}

fn bool Loader.add_root(Loader* l, char* path)
{
    if (l.root_count >= MAX_ROOTS) { return false; }
    l.roots[l.root_count] = path;
    l.root_count = l.root_count + 1;
    return true;
}

fn usz cstr_len(char* s)
{
    if (s == null) { return 0; }
    usz n = 0;
    while (s[n] != 0) { n = n + 1; }
    return n;
}

// Build "<root>/<a>/<b>/<c><suffix>" from a dotted module name.
fn usz build_path(char* out, usz cap, char* root, char* dotted, usz dlen,
                  char* suffix, bool dots_to_slash)
{
    usz pos = 0;
    usz rlen = cstr_len(root);
    for (usz i = 0; i < rlen && pos < cap - 1; i++) { out[pos] = root[i]; pos = pos + 1; }
    if (pos > 0 && out[pos - 1] != '/' && pos < cap - 1) { out[pos] = '/'; pos = pos + 1; }
    for (usz i = 0; i < dlen && pos < cap - 1; i++)
    {
        char c = dotted[i];
        if (c == '.' && dots_to_slash) { c = '/'; }
        out[pos] = c;
        pos = pos + 1;
    }
    usz slen = cstr_len(suffix);
    for (usz i = 0; i < slen && pos < cap - 1; i++) { out[pos] = suffix[i]; pos = pos + 1; }
    out[pos] = 0;
    return pos;
}

// Appends "/<last-segment>.pie" — supports the a/b/c/c.pie convention.
fn usz build_path_lastseg(char* out, usz cap, char* root, char* dotted, usz dlen)
{
    usz pos = build_path(out, cap, root, dotted, dlen, "", true);
    usz last = 0;
    for (usz i = 0; i < dlen; i++) { if (dotted[i] == '.') { last = i + 1; } }
    if (pos < cap - 1) { out[pos] = '/'; pos = pos + 1; }
    for (usz i = last; i < dlen && pos < cap - 1; i++) { out[pos] = dotted[i]; pos = pos + 1; }
    char* sfx = ".pie";
    for (usz i = 0; i < 4 && pos < cap - 1; i++) { out[pos] = sfx[i]; pos = pos + 1; }
    out[pos] = 0;
    return pos;
}

fn bool file_exists(char* path)
{
    CFile f = fopen(path, "rb");
    if (f == null) { return false; }
    fclose(f);
    return true;
}

fn char* Loader.read_file(Loader* l, char* path, usz* out_len)
{
    CFile f = fopen(path, "rb");
    if (f == null) { return null; }
    fseek(f, 0, SEEK_END_V);
    long fsize = ftell(f);
    fseek(f, 0, SEEK_SET_V);
    if (fsize < 0) { fclose(f); return null; }
    char* buf = (char*)l.arena.alloc((usz)fsize + 1, 1);
    if (buf == null) { fclose(f); return null; }
    usz got = fread((void*)buf, 1, (usz)fsize, f);
    fclose(f);
    buf[got] = 0;
    *out_len = got;
    l.files_read = l.files_read + 1;
    if (l.smap != null) { l.smap.add_file(path, buf, got); }
    return buf;
}

fn Mod* Loader.find_module(Loader* l, uint name_id)
{
    for (usz i = 0; i < l.module_count; i++)
    {
        if (l.modules[i].name_id == name_id) { return l.modules[i]; }
    }
    return null;
}

fn Mod* Loader.new_module(Loader* l, uint name_id, char* path)
{
    if (l.module_count >= MAX_MODULES) { return null; }
    Mod* m = (Mod*)l.arena.alloc(Mod::size, 8);
    if (m == null) { return null; }
    m.init(name_id, path);
    m.load_order = (int)l.module_count;
    l.modules[l.module_count] = m;
    l.module_count = l.module_count + 1;
    return m;
}

// Resolve a dotted module name to an on-disk file, trying each layout.
fn char* Loader.locate(Loader* l, char* dotted, usz dlen)
{
    for (usz r = 0; r < l.root_count; r++)
    {
        char* buf = (char*)l.arena.alloc(PATH_MAX_LEN, 1);
        if (buf == null) { return null; }

        build_path(buf, PATH_MAX_LEN, l.roots[r], dotted, dlen, ".pie", true);
        if (file_exists(buf)) { return buf; }

        build_path(buf, PATH_MAX_LEN, l.roots[r], dotted, dlen, "/mod.pie", true);
        if (file_exists(buf)) { return buf; }

        build_path_lastseg(buf, PATH_MAX_LEN, l.roots[r], dotted, dlen);
        if (file_exists(buf)) { return buf; }

        build_path(buf, PATH_MAX_LEN, l.roots[r], dotted, dlen, ".pie", false);
        if (file_exists(buf)) { return buf; }
    }
    return null;
}

fn bool Loader.is_loading(Loader* l, uint name_id)
{
    for (usz i = 0; i < l.loading_depth; i++)
    {
        if (l.loading[i] == name_id) { return true; }
    }
    return false;
}

// Load (or return cached) a module by interned dotted name.
fn Mod* Loader.load(Loader* l, uint name_id, int line, int col, char* requester)
{
    if (name_id == 0) { return null; }

    Mod* existing = l.find_module(name_id);
    if (existing != null)
    {
        if (existing.state == pfront_core::ModState.MOD_LOADING)
        {
            l.diags.error(pfront_core::Phase.PH_MODULE, 2001, line, col,
                          "circular module dependency", requester);
            return existing;
        }
        return existing;
    }

    if (l.is_loading(name_id))
    {
        l.diags.error(pfront_core::Phase.PH_MODULE, 2001, line, col,
                      "circular module dependency", requester);
        return null;
    }

    char* dotted = l.interner.text(name_id);
    usz   dlen   = l.interner.text_len(name_id);
    char* path   = l.locate(dotted, dlen);
    if (path == null)
    {
        l.diags.error_hint(pfront_core::Phase.PH_MODULE, 2002, line, col,
                           "cannot find module for this import",
                           "checked <root>/a/b/c.pie, /mod.pie, /c.pie and a.b.c.pie",
                           requester);
        return null;
    }

    Mod* m = l.new_module(name_id, path);
    if (m == null) { return null; }
    m.state = pfront_core::ModState.MOD_LOADING;
    if (l.loading_depth < 64)
    {
        l.loading[l.loading_depth] = name_id;
        l.loading_depth = l.loading_depth + 1;
    }

    usz src_len = 0;
    char* src = l.read_file(path, &src_len);
    if (src == null)
    {
        l.diags.error(pfront_core::Phase.PH_MODULE, 2003, line, col,
                      "module file exists but could not be read", path);
        m.state = pfront_core::ModState.MOD_FAILED;
        if (l.loading_depth > 0) { l.loading_depth = l.loading_depth - 1; }
        return m;
    }
    m.source = src;
    m.source_len = src_len;

    pfront_lex::Lexer* lx = (pfront_lex::Lexer*)malloc(pfront_lex::Lexer::size);
    if (lx == null) { m.state = pfront_core::ModState.MOD_FAILED; return m; }
    lx.init(src, src_len);

    pfront_parse::Parser* ps = (pfront_parse::Parser*)malloc(pfront_parse::Parser::size);
    if (ps == null) { free((void*)lx); m.state = pfront_core::ModState.MOD_FAILED; return m; }
    ps.init(lx, l.arena, l.interner, l.diags, m, path);
    Node* ast = ps.parse_program();
    m.ast = ast;

    // Surface lexer diagnostics through the same bag.
    int ld = lx.get_diag_count();
    for (int i = 0; i < ld; i++)
    {
        pfront_lex::Diagnostic d = lx.get_diag(i);
        l.diags.error(pfront_core::Phase.PH_LEX, 2010, d.line, d.col, d.msg, path);
    }

    free((void*)ps);
    free((void*)lx);

    m.state = pfront_core::ModState.MOD_PARSED;
    if (l.loading_depth > 0) { l.loading_depth = l.loading_depth - 1; }

    // Recursively load whatever this module imports.
    l.load_imports_of(m);
    return m;
}

fn void Loader.load_imports_of(Loader* l, Mod* m)
{
    if (m == null || m.ast == null) { return; }
    l.walk_imports(m, m.ast, 0);
}

fn void Loader.walk_imports(Loader* l, Mod* m, Node* n, int depth)
{
    if (n == null || depth > 64) { return; }
    if (n.kind == Nk.N_USE)
    {
        Mod* dep = l.load(n.name_id, n.line, n.col, m.path);
        if (dep != null)
        {
            m.add_import(dep);
            n.resolved = dep.ast;
        }
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        l.walk_imports(m, n.children[i], depth + 1);
    }
}

// Load a root file directly by path (the file named on the command line).
fn Mod* Loader.load_entry(Loader* l, char* path)
{
    usz src_len = 0;
    char* src = l.read_file(path, &src_len);
    if (src == null)
    {
        l.diags.error(pfront_core::Phase.PH_MODULE, 2004, 0, 0,
                      "cannot open input file", path);
        return null;
    }
    uint nid = l.interner.intern(path, cstr_len(path));
    Mod* m = l.new_module(nid, path);
    if (m == null) { return null; }
    m.source = src;
    m.source_len = src_len;
    m.state = pfront_core::ModState.MOD_LOADING;

    pfront_lex::Lexer* lx = (pfront_lex::Lexer*)malloc(pfront_lex::Lexer::size);
    if (lx == null) { return null; }
    lx.init(src, src_len);
    pfront_parse::Parser* ps = (pfront_parse::Parser*)malloc(pfront_parse::Parser::size);
    if (ps == null) { free((void*)lx); return null; }
    ps.init(lx, l.arena, l.interner, l.diags, m, path);
    m.ast = ps.parse_program();

    int ld = lx.get_diag_count();
    for (int i = 0; i < ld; i++)
    {
        pfront_lex::Diagnostic d = lx.get_diag(i);
        l.diags.error(pfront_core::Phase.PH_LEX, 2010, d.line, d.col, d.msg, path);
    }
    free((void*)ps);
    free((void*)lx);
    m.state = pfront_core::ModState.MOD_PARSED;
    l.load_imports_of(m);
    return m;
}

// ── Resolver ────────────────────────────────────────────────────────────────
struct Resolver
{
    Arena*                 arena;
    pfront_core::Interner* interner;
    pfront_core::DiagBag*  diags;
    Loader*                loader;

    pfront_core::Scope*    scopes;      // current scope (linked via .parent)
    pfront_core::Scope*[MAX_SCOPES] pool;
    usz                    pool_used;

    Mod*                   cur_module;
    char*                  cur_file;
    Node*                  cur_fn;
    int                    loop_depth;
    int                    handler_depth;

    usz                    resolved_count;
    usz                    unresolved_count;
    usz                    builtin_hits;
}

fn bool Resolver.init(Resolver* r, Arena* a, pfront_core::Interner* it,
                      pfront_core::DiagBag* d, Loader* l)
{
    r.arena = a;
    r.interner = it;
    r.diags = d;
    r.loader = l;
    r.scopes = null;
    r.pool_used = 0;
    r.cur_module = null;
    r.cur_file = null;
    r.cur_fn = null;
    r.loop_depth = 0;
    r.handler_depth = 0;
    r.resolved_count = 0;
    r.unresolved_count = 0;
    r.builtin_hits = 0;
    return true;
}

fn void Resolver.push_scope(Resolver* r, Node* owner)
{
    pfront_core::Scope* s = (pfront_core::Scope*)r.arena.alloc(pfront_core::Scope::size, 8);
    if (s == null) { return; }
    s.init(r.scopes, owner);
    r.scopes = s;
}

fn void Resolver.pop_scope(Resolver* r)
{
    if (r.scopes != null) { r.scopes = r.scopes.parent; }
}

fn Sym* Resolver.declare(Resolver* r, uint name_id, pfront_core::SymKind k,
                         int ns, Node* decl, bool is_pub)
{
    if (name_id == 0) { return null; }
    Sym* s = (Sym*)r.arena.alloc(Sym::size, 8);
    if (s == null) { return null; }
    s.name_id = name_id;
    s.kind = k;
    s.ns = ns;
    s.decl = decl;
    s.owner = r.cur_module;
    s.next = null;
    s.is_pub = is_pub;
    s.used = false;
    s.depth = 0;
    if (r.scopes != null)
    {
        Sym* prev = r.scopes.lookup_local(name_id, ns);
        if (prev != null && prev.decl != decl)
        {
            // Function clauses and overloads legitimately repeat a name; only
            // flag genuinely conflicting value bindings in the same scope.
            if (k != pfront_core::SymKind.SYM_FN && prev.kind != pfront_core::SymKind.SYM_FN)
            {
                char* nm = r.interner.text(name_id);
                r.diags.warn(pfront_core::Phase.PH_RESOLVE, 3010,
                             decl == null ? 0 : decl.line,
                             decl == null ? 0 : decl.col,
                             "this binding shadows an earlier one in the same scope",
                             r.cur_file);
            }
        }
        r.scopes.insert(s);
    }
    if (decl != null)
    {
        decl.sym = s;
        decl.flags = decl.flags | pfront_core::NF_RESOLVED;
    }
    return s;
}

// ── Builtins ────────────────────────────────────────────────────────────────
// Primitive type names and intrinsic functions are pre-declared in the root
// scope so `i64`, `bool`, `printf` etc. resolve without a prelude file.
fn void Resolver.install_builtins(Resolver* r)
{
    char*[24] tynames = {
        "i8", "i16", "i32", "i64", "i128",
        "u8", "u16", "u32", "u64", "u128",
        "f32", "f64", "bool", "char", "str",
        "usz", "isz", "unit", "never", "void",
        "byte", "rune", "ptr", "any"
    };
    for (usz i = 0; i < 24; i++)
    {
        uint id = r.interner.intern(tynames[i], cstr_len(tynames[i]));
        r.declare(id, pfront_core::SymKind.SYM_BUILTIN_TYPE, pfront_core::NS_TYPE, null, true);
    }
    char*[10] fnnames = {
        "printf", "malloc", "free", "memcpy", "memset",
        "len", "cap", "panic", "print", "println"
    };
    for (usz i = 0; i < 10; i++)
    {
        uint id = r.interner.intern(fnnames[i], cstr_len(fnnames[i]));
        r.declare(id, pfront_core::SymKind.SYM_BUILTIN_FN, pfront_core::NS_VALUE, null, true);
    }
    char*[6] effnames = { "IO", "Alloc", "Panic", "Unsafe", "Div", "State" };
    for (usz i = 0; i < 6; i++)
    {
        uint id = r.interner.intern(effnames[i], cstr_len(effnames[i]));
        r.declare(id, pfront_core::SymKind.SYM_EFFECT, pfront_core::NS_TYPE, null, true);
    }
}

// ── Pass 1: hoist declarations into scope (so order does not matter) ────────
fn void Resolver.hoist_decls(Resolver* r, Node* container)
{
    if (container == null) { return; }
    for (usz i = 0; i < container.child_count; i++)
    {
        Node* d = container.children[i];
        if (d == null) { continue; }
        r.hoist_one(d);
    }
}

fn void Resolver.hoist_one(Resolver* r, Node* d)
{
    bool pub = (d.flags & pfront_core::NF_PUB) != 0;
    switch (d.kind)
    {
        case N_DECL_FN:
        case N_DECL_EXTERN_FN:
            r.declare(d.name_id, pfront_core::SymKind.SYM_FN, pfront_core::NS_VALUE, d, pub);
        case N_DECL_STRUCT:
        case N_DECL_UNION:
            r.declare(d.name_id, pfront_core::SymKind.SYM_TYPE, pfront_core::NS_TYPE, d, pub);
        case N_DECL_ENUM:
        {
            r.declare(d.name_id, pfront_core::SymKind.SYM_TYPE, pfront_core::NS_TYPE, d, pub);
            // Variants live in the value namespace so `Some(x)` resolves.
            for (usz i = 0; i < d.child_count; i++)
            {
                Node* v = d.children[i];
                if (v != null && v.kind == Nk.N_DECL_VARIANT)
                {
                    r.declare(v.name_id, pfront_core::SymKind.SYM_VARIANT,
                              pfront_core::NS_VALUE, v, pub);
                }
            }
        }
        case N_DECL_TYPE:
        case N_DECL_NEWTYPE:
            r.declare(d.name_id, pfront_core::SymKind.SYM_TYPE, pfront_core::NS_TYPE, d, pub);
        case N_DECL_EFFECT:
        {
            r.declare(d.name_id, pfront_core::SymKind.SYM_EFFECT, pfront_core::NS_TYPE, d, pub);
            for (usz i = 0; i < d.child_count; i++)
            {
                Node* op = d.children[i];
                if (op != null && op.kind == Nk.N_DECL_EFFECT_OP)
                {
                    r.declare(op.name_id, pfront_core::SymKind.SYM_EFFECT_OP,
                              pfront_core::NS_VALUE, op, pub);
                }
            }
        }
        case N_DECL_INTERFACE:
            r.declare(d.name_id, pfront_core::SymKind.SYM_INTERFACE, pfront_core::NS_TYPE, d, pub);
        case N_DECL_CONST:
        case N_DECL_STATIC:
            r.declare(d.name_id, pfront_core::SymKind.SYM_VALUE, pfront_core::NS_VALUE, d, pub);
        case N_DECL_LET:
        {
            if (d.name_id != 0)
            {
                r.declare(d.name_id, pfront_core::SymKind.SYM_VALUE, pfront_core::NS_VALUE, d, pub);
            }
        }
        case N_MODULE:
            r.hoist_decls(d);
        default:
            break;
    }
}

// ── Import binding: pull a dependency's exports into this scope ─────────────
fn void Resolver.bind_imports(Resolver* r, Node* container)
{
    if (container == null) { return; }
    for (usz i = 0; i < container.child_count; i++)
    {
        Node* n = container.children[i];
        if (n == null) { continue; }
        if (n.kind == Nk.N_USE) { r.bind_one_import(n); }
        else if (n.kind == Nk.N_MODULE) { r.bind_imports(n); }
    }
}

fn void Resolver.bind_one_import(Resolver* r, Node* use_node)
{
    Mod* dep = r.loader.find_module(use_node.name_id);
    if (dep == null || dep.ast == null)
    {
        // HARD ERROR. The old front end silently swallowed this and exited 0,
        // which is what let 253 broken stdlib modules look healthy.
        char* nm = r.interner.text(use_node.name_id);
        r.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3001,
                           use_node.line, use_node.col,
                           "unresolved import: this module could not be loaded",
                           "check the module name and that the file exists on the search path",
                           r.cur_file);
        return;
    }

    bool is_glob = (use_node.flags & pfront_core::NF_GLOB) != 0;
    bool has_items = false;
    for (usz i = 0; i < use_node.child_count; i++)
    {
        if (use_node.children[i] != null && use_node.children[i].kind == Nk.N_USE_ITEM)
        {
            has_items = true;
        }
    }

    if (has_items)
    {
        for (usz i = 0; i < use_node.child_count; i++)
        {
            Node* item = use_node.children[i];
            if (item == null || item.kind != Nk.N_USE_ITEM) { continue; }
            bool found = false;
            for (int ns = 0; ns < pfront_core::NS_COUNT; ns++)
            {
                Sym* s = dep.find_export(item.name_id, ns);
                if (s != null)
                {
                    uint bind_as = item.p.aux != 0 ? (uint)item.p.aux : item.name_id;
                    r.rebind(bind_as, s);
                    item.resolved = s.decl;
                    found = true;
                }
            }
            if (!found)
            {
                r.diags.error(pfront_core::Phase.PH_RESOLVE, 3002, item.line, item.col,
                              "this name is not exported by the imported module", r.cur_file);
            }
        }
        return;
    }

    // Glob or plain module import: bring every export into scope. A plain
    // `use a.b` also makes `b.name` work via the module symbol.
    for (usz b = 0; b < pfront_core::MOD_EXPORT_BUCKETS; b++)
    {
        Sym* cur = dep.exports[b];
        while (cur != null)
        {
            r.rebind(cur.name_id, cur);
            cur = cur.next;
        }
    }
    if (!is_glob)
    {
        // Bind the last path segment as a module alias for qualified access.
        Node* path = use_node.child(0);
        if (path != null && path.child_count > 0)
        {
            Node* last = path.children[path.child_count - 1];
            uint bind_name = use_node.p.aux != 0 ? (uint)use_node.p.aux : last.name_id;
            Sym* ms = (Sym*)r.arena.alloc(Sym::size, 8);
            if (ms != null)
            {
                ms.name_id = bind_name;
                ms.kind = pfront_core::SymKind.SYM_MODULE;
                ms.ns = pfront_core::NS_TYPE;
                ms.decl = dep.ast;
                ms.owner = dep;
                ms.next = null;
                ms.is_pub = false;
                ms.used = false;
                if (r.scopes != null) { r.scopes.insert(ms); }
            }
        }
    }
}

// Insert an existing symbol under a (possibly different) name in this scope.
fn void Resolver.rebind(Resolver* r, uint name_id, Sym* src)
{
    if (r.scopes == null || src == null || name_id == 0) { return; }
    Sym* s = (Sym*)r.arena.alloc(Sym::size, 8);
    if (s == null) { return; }
    s.name_id = name_id;
    s.kind = src.kind;
    s.ns = src.ns;
    s.decl = src.decl;
    s.owner = src.owner;
    s.next = null;
    s.is_pub = false;
    s.used = false;
    r.scopes.insert(s);
}

// ── Export collection ───────────────────────────────────────────────────────
fn void Resolver.collect_exports(Resolver* r, Mod* m)
{
    if (m == null || m.ast == null) { return; }
    r.collect_exports_from(m, m.ast, 0);
}

fn void Resolver.collect_exports_from(Resolver* r, Mod* m, Node* n, int depth)
{
    if (n == null || depth > 32) { return; }
    for (usz i = 0; i < n.child_count; i++)
    {
        Node* d = n.children[i];
        if (d == null) { continue; }
        if (d.kind == Nk.N_MODULE) { r.collect_exports_from(m, d, depth + 1); continue; }
        if (!pfront_core::is_decl(d.kind)) { continue; }
        // Pride treats module-level declarations as exported unless the file
        // marks otherwise; `pub` is honoured when present.
        int ns = pfront_core::NS_VALUE;
        pfront_core::SymKind k = pfront_core::SymKind.SYM_VALUE;
        switch (d.kind)
        {
            case N_DECL_FN:
            case N_DECL_EXTERN_FN:
                k = pfront_core::SymKind.SYM_FN; ns = pfront_core::NS_VALUE;
            case N_DECL_STRUCT:
            case N_DECL_UNION:
            case N_DECL_TYPE:
            case N_DECL_NEWTYPE:
                k = pfront_core::SymKind.SYM_TYPE; ns = pfront_core::NS_TYPE;
            case N_DECL_ENUM:
                k = pfront_core::SymKind.SYM_TYPE; ns = pfront_core::NS_TYPE;
            case N_DECL_EFFECT:
                k = pfront_core::SymKind.SYM_EFFECT; ns = pfront_core::NS_TYPE;
            case N_DECL_INTERFACE:
                k = pfront_core::SymKind.SYM_INTERFACE; ns = pfront_core::NS_TYPE;
            case N_DECL_CONST:
            case N_DECL_STATIC:
            case N_DECL_LET:
                k = pfront_core::SymKind.SYM_VALUE; ns = pfront_core::NS_VALUE;
            default:
                continue;
        }
        if (d.name_id == 0) { continue; }
        Sym* s = (Sym*)r.arena.alloc(Sym::size, 8);
        if (s == null) { continue; }
        s.name_id = d.name_id;
        s.kind = k;
        s.ns = ns;
        s.decl = d;
        s.owner = m;
        s.next = null;
        s.is_pub = true;
        s.used = false;
        m.add_export(s);

        // Enum variants and effect ops are exported alongside their parent.
        if (d.kind == Nk.N_DECL_ENUM)
        {
            for (usz j = 0; j < d.child_count; j++)
            {
                Node* v = d.children[j];
                if (v == null || v.kind != Nk.N_DECL_VARIANT || v.name_id == 0) { continue; }
                Sym* vs = (Sym*)r.arena.alloc(Sym::size, 8);
                if (vs == null) { continue; }
                vs.name_id = v.name_id;
                vs.kind = pfront_core::SymKind.SYM_VARIANT;
                vs.ns = pfront_core::NS_VALUE;
                vs.decl = v;
                vs.owner = m;
                vs.next = null;
                vs.is_pub = true;
                vs.used = false;
                m.add_export(vs);
            }
        }
        if (d.kind == Nk.N_DECL_EFFECT)
        {
            for (usz j = 0; j < d.child_count; j++)
            {
                Node* op = d.children[j];
                if (op == null || op.kind != Nk.N_DECL_EFFECT_OP || op.name_id == 0) { continue; }
                Sym* os = (Sym*)r.arena.alloc(Sym::size, 8);
                if (os == null) { continue; }
                os.name_id = op.name_id;
                os.kind = pfront_core::SymKind.SYM_EFFECT_OP;
                os.ns = pfront_core::NS_VALUE;
                os.decl = op;
                os.owner = m;
                os.next = null;
                os.is_pub = true;
                os.used = false;
                m.add_export(os);
            }
        }
    }
}

// ── Pattern binding ─────────────────────────────────────────────────────────
fn void Resolver.bind_pattern(Resolver* r, Node* pat)
{
    if (pat == null) { return; }
    switch (pat.kind)
    {
        case N_PAT_IDENT:
        {
            // A bare uppercase name is ambiguous between a nullary enum
            // variant and a binder; the parser tagged it PAT_MAYBE_VARIANT
            // and left the decision to us, because only scope knows.
            //
            // Look the name up as a variant FIRST. If it is one, restore the
            // refutable-pattern reading. If it is not, fall through and bind
            // it — which is what makes `| (a, b, c, M, N, K) ->` work.
            if (pat.p.aux == pfront_parse::PAT_MAYBE_VARIANT)
            {
                Sym* v = r.scopes == null
                       ? null
                       : r.scopes.lookup(pat.name_id, pfront_core::NS_VALUE);
                bool is_variant = v != null && v.decl != null
                               && v.decl.kind == Nk.N_DECL_VARIANT;
                if (!is_variant)
                {
                    Sym* tv = r.scopes == null
                            ? null
                            : r.scopes.lookup(pat.name_id, pfront_core::NS_TYPE);
                    is_variant = tv != null && tv.decl != null
                              && tv.decl.kind == Nk.N_DECL_VARIANT;
                }
                if (is_variant)
                {
                    pat.kind = Nk.N_PAT_VARIANT;
                    pat.flags = pat.flags | pfront_core::NF_REFUTABLE;
                    Node* path = pat.child(0);
                    if (path != null) { r.resolve_path_value(path, pat); }
                    return;
                }
                // Binder after all: the path child was only the variant
                // reading, so drop it rather than leave a stray unresolved
                // module-path hanging off a binding.
                pat.child_count = 0;
            }
            r.declare(pat.name_id, pfront_core::SymKind.SYM_VALUE,
                      pfront_core::NS_VALUE, pat, false);
            if (pat.type_ann != null) { r.resolve_type(pat.type_ann); }
        }
        case N_PAT_VARIANT:
        {
            // First child is the path naming the variant; the rest are subpatterns.
            Node* path = pat.child(0);
            if (path != null) { r.resolve_path_value(path, pat); }
            for (usz i = 1; i < pat.child_count; i++) { r.bind_pattern(pat.children[i]); }
        }
        case N_PAT_STRUCT:
        {
            Node* path = pat.child(0);
            if (path != null) { r.resolve_path_type(path, pat); }
            for (usz i = 1; i < pat.child_count; i++)
            {
                Node* f = pat.children[i];
                if (f == null) { continue; }
                if (f.kind == Nk.N_PAT_FIELD) { r.bind_pattern(f.child(0)); }
                else { r.bind_pattern(f); }
            }
        }
        case N_PAT_LITERAL:
        {
            for (usz i = 0; i < pat.child_count; i++) { r.resolve_expr(pat.children[i]); }
        }
        default:
        {
            for (usz i = 0; i < pat.child_count; i++) { r.bind_pattern(pat.children[i]); }
            if (pat.type_ann != null) { r.resolve_type(pat.type_ann); }
        }
    }
}

// ── Type resolution ─────────────────────────────────────────────────────────
fn void Resolver.resolve_type(Resolver* r, Node* t)
{
    if (t == null) { return; }
    switch (t.kind)
    {
        case N_TY_NAME:
        {
            if (t.name_id == 0) { break; }
            Sym* s = r.scopes == null ? null : r.scopes.lookup(t.name_id, pfront_core::NS_TYPE);
            if (s != null)
            {
                t.resolved = s.decl;
                t.sym = s;
                s.used = true;
                t.flags = t.flags | pfront_core::NF_RESOLVED;
                r.resolved_count = r.resolved_count + 1;
                if (s.kind == pfront_core::SymKind.SYM_BUILTIN_TYPE)
                {
                    r.builtin_hits = r.builtin_hits + 1;
                }
            }
            else
            {
                r.unresolved_count = r.unresolved_count + 1;
                r.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3003, t.line, t.col,
                                   "unknown type name",
                                   "declare it, or import the module that defines it",
                                   r.cur_file);
            }
        }
        case N_TY_PATH:
            r.resolve_path_type(t, t);
        case N_TY_EFFECT_ROW:
        {
            for (usz i = 0; i < t.child_count; i++)
            {
                Node* e = t.children[i];
                if (e == null || e.kind != Nk.N_TY_EFFECT_ELEM) { continue; }
                if (e.p.aux == 1) { continue; }   // open-row tail variable
                Sym* s = r.scopes == null ? null : r.scopes.lookup(e.name_id, pfront_core::NS_TYPE);
                if (s != null) { e.resolved = s.decl; e.sym = s; s.used = true; }
            }
        }
        default:
        {
            for (usz i = 0; i < t.child_count; i++) { r.resolve_type(t.children[i]); }
        }
    }
}

fn void Resolver.resolve_path_type(Resolver* r, Node* path, Node* site)
{
    if (path == null) { return; }
    // Head segment may name a module; the tail names the type inside it.
    if (path.child_count == 0)
    {
        if (path.name_id != 0)
        {
            Sym* s = r.scopes == null ? null : r.scopes.lookup(path.name_id, pfront_core::NS_TYPE);
            if (s != null) { site.resolved = s.decl; site.sym = s; s.used = true; }
        }
        return;
    }
    Node* head = path.children[0];
    if (head == null) { return; }
    Sym* hs = r.scopes == null ? null : r.scopes.lookup(head.name_id, pfront_core::NS_TYPE);
    if (hs != null && hs.kind == pfront_core::SymKind.SYM_MODULE && path.child_count >= 2)
    {
        Node* last = path.children[path.child_count - 1];

        // Two imports can bind the SAME short alias:
        //     use vec.raw      -- exports RawVec
        //     use str.raw      -- exports utf8 helpers, no RawVec
        // Both insert a module symbol named `raw`, so `raw.RawVec` finds
        // whichever the scope returns first. Stopping there reported
        // "this module does not export that type" even though a later
        // candidate did export it — which is exactly what broke
        // stdlib/str/string.pie and every module that transitively used it.
        //
        // Walk the whole alias chain and take the first candidate that
        // actually has the name. Ambiguity is resolved by availability,
        // which is the only sensible rule when the alias is a suffix.
        Sym* cand = hs;
        while (cand != null)
        {
            if (cand.kind == pfront_core::SymKind.SYM_MODULE && cand.owner != null)
            {
                Sym* ts = cand.owner.find_export(last.name_id, pfront_core::NS_TYPE);
                if (ts != null)
                {
                    site.resolved = ts.decl;
                    site.sym = ts;
                    ts.used = true;
                    cand.used = true;
                    site.flags = site.flags | pfront_core::NF_RESOLVED;
                    r.resolved_count = r.resolved_count + 1;
                    return;
                }
            }
            cand = cand.next;
        }
        r.unresolved_count = r.unresolved_count + 1;
        r.diags.error(pfront_core::Phase.PH_RESOLVE, 3004, site.line, site.col,
                      "this module does not export that type", r.cur_file);
        return;
    }
    // Fall back to resolving the final segment in the current scope.
    Node* last2 = path.children[path.child_count - 1];
    if (last2 != null && last2.name_id != 0)
    {
        Sym* s = r.scopes == null ? null : r.scopes.lookup(last2.name_id, pfront_core::NS_TYPE);
        if (s != null)
        {
            site.resolved = s.decl;
            site.sym = s;
            s.used = true;
            site.flags = site.flags | pfront_core::NF_RESOLVED;
            r.resolved_count = r.resolved_count + 1;
        }
    }
}

fn void Resolver.resolve_path_value(Resolver* r, Node* path, Node* site)
{
    if (path == null || path.child_count == 0) { return; }
    Node* head = path.children[0];
    Node* last = path.children[path.child_count - 1];
    if (head == null || last == null) { return; }

    if (path.child_count >= 2)
    {
        Sym* hs = r.scopes == null ? null : r.scopes.lookup(head.name_id, pfront_core::NS_TYPE);
        if (hs != null && hs.kind == pfront_core::SymKind.SYM_MODULE)
        {
            Mod* dep = hs.owner;
            if (dep != null)
            {
                Sym* vs = dep.find_export(last.name_id, pfront_core::NS_VALUE);
                if (vs != null)
                {
                    site.resolved = vs.decl;
                    site.sym = vs;
                    vs.used = true;
                    site.flags = site.flags | pfront_core::NF_RESOLVED;
                    r.resolved_count = r.resolved_count + 1;
                    return;
                }
            }
        }
        // Enum.Variant — head names the enum type, last names the variant.
        if (hs != null && hs.decl != null && hs.decl.kind == Nk.N_DECL_ENUM)
        {
            for (usz i = 0; i < hs.decl.child_count; i++)
            {
                Node* v = hs.decl.children[i];
                if (v != null && v.kind == Nk.N_DECL_VARIANT && v.name_id == last.name_id)
                {
                    site.resolved = v;
                    site.flags = site.flags | pfront_core::NF_RESOLVED;
                    r.resolved_count = r.resolved_count + 1;
                    return;
                }
            }
        }
        // Effect.op
        Sym* es = r.scopes == null ? null : r.scopes.lookup(head.name_id, pfront_core::NS_TYPE);
        if (es != null && es.decl != null && es.decl.kind == Nk.N_DECL_EFFECT)
        {
            for (usz i = 0; i < es.decl.child_count; i++)
            {
                Node* op = es.decl.children[i];
                if (op != null && op.kind == Nk.N_DECL_EFFECT_OP && op.name_id == last.name_id)
                {
                    site.resolved = op;
                    site.flags = site.flags | pfront_core::NF_RESOLVED;
                    r.resolved_count = r.resolved_count + 1;
                    return;
                }
            }
        }
    }

    Sym* s = r.scopes == null ? null : r.scopes.lookup(last.name_id, pfront_core::NS_VALUE);
    if (s != null)
    {
        site.resolved = s.decl;
        site.sym = s;
        s.used = true;
        site.flags = site.flags | pfront_core::NF_RESOLVED;
        r.resolved_count = r.resolved_count + 1;
        return;
    }
    r.unresolved_count = r.unresolved_count + 1;
    r.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3005, site.line, site.col,
                       "unresolved name",
                       "check spelling, or import the module that defines it",
                       r.cur_file);
}

// Flatten a left-leaning N_EXPR_FIELD chain into its name segments.
// `os.linux.malloc` -> ["os", "linux", "malloc"]. Returns 0 if the chain is
// not purely name-shaped (e.g. `f(x).y`, which is a real field access).
fn usz flatten_chain(Node* e, uint* out, usz cap)
{
    if (e == null) { return 0; }
    if (e.kind == Nk.N_EXPR_IDENT)
    {
        if (cap < 1 || e.name_id == 0) { return 0; }
        out[0] = e.name_id;
        return 1;
    }
    if (e.kind != Nk.N_EXPR_FIELD || e.p.aux == 1 || e.name_id == 0) { return 0; }
    usz n = flatten_chain(e.child(0), out, cap);
    if (n == 0 || n >= cap) { return 0; }
    out[n] = e.name_id;
    return n + 1;
}

// A LOCAL VALUE BINDING SHADOWS A MODULE NAME.
//
// `stdlib/target/` makes `target` a module, and `pride/rewrite.pie` has
//     fn unify_terms : (*RuleUnifier, *AstTerm, *AstTerm) -> bool
//       | (u, pat, target) -> ... target.tag ...
// The module reading is tried first (that is what makes `os.linux.malloc(n)`
// work), so `target.tag` was read as "member `tag` of module `target`" and
// reported E3004 -- but only in a build that also loaded stdlib/target/*.
// The file was clean on its own, which is the hardest kind of failure to
// place. Ordinary lexical scoping settles it: if the first segment names a
// value in scope, the chain is a field access, not a module path.
fn bool Resolver.seg_is_local_value(Resolver* r, uint seg)
{
    if (r.scopes == null) { return false; }
    Sym* v = r.scopes.lookup(seg, pfront_core::NS_VALUE);
    if (v == null) { return false; }
    // A module alias bound by `use` also lands in scope; it is exactly what
    // the module path SHOULD match, so it must not count as shadowing.
    return v.kind != pfront_core::SymKind.SYM_MODULE;
}

// Try to read a field chain as <module-path>.<member>. Returns true when the
// chain resolved as a qualified module member.
fn bool Resolver.try_resolve_module_chain(Resolver* r, Node* e)
{
    uint[16] segs;
    usz n = flatten_chain(e, &segs[0], 16);
    if (n < 2) { return false; }
    if (r.seg_is_local_value(segs[0])) { return false; }

    // The member is the last segment; everything before it is the module path.
    // Try the longest prefix first so `a.b.c.f` prefers module `a.b.c`.
    char[512] buf;
    for (usz take = n - 1; take >= 1; take--)
    {
        usz pos = 0;
        for (usz i = 0; i < take; i++)
        {
            if (i > 0 && pos < 511) { buf[pos] = '.'; pos = pos + 1; }
            char* seg = r.interner.text(segs[i]);
            usz sl = r.interner.text_len(segs[i]);
            for (usz j = 0; j < sl && pos < 511; j++) { buf[pos] = seg[j]; pos = pos + 1; }
        }
        buf[pos] = 0;
        uint modname = r.interner.intern(&buf[0], pos);
        Mod* dep = r.loader.find_module(modname);
        if (dep != null)
        {
            uint member = segs[n - 1];
            for (int ns = 0; ns < pfront_core::NS_COUNT; ns++)
            {
                Sym* s = dep.find_export(member, ns);
                if (s != null)
                {
                    e.resolved = s.decl;
                    e.sym = s;
                    s.used = true;
                    e.flags = e.flags | pfront_core::NF_RESOLVED;
                    r.resolved_count = r.resolved_count + 1;
                    if (s.decl != null) { s.decl.flags = s.decl.flags | pfront_core::NF_USED; }
                    // Flag the RECEIVER chain too. `os` in `os.linux.PROT_READ`
                    // names a module and has no declaration to point at, so
                    // without this it was reported as an unresolved identifier
                    // even though the whole chain resolved. The qualified-CALL
                    // path already did this; the value path did not, which is
                    // why `os.linux.malloc(n)` looked clean but
                    // `os.linux.PROT_READ` did not.
                    mark_chain_resolved(e.child(0));
                    return true;
                }
            }
            // The module exists but has no such member: report precisely here
            // rather than letting it fall through to a vague "unresolved name".
            r.unresolved_count = r.unresolved_count + 1;
            r.diags.error(pfront_core::Phase.PH_RESOLVE, 3004, e.line, e.col,
                          "this module does not export that name", r.cur_file);
            return true;
        }
        if (take == 1) { break; }
    }
    return false;
}

// `recv.member(args)` where `recv` is a module PATH rather than a value.
//
// The receiver arrives as a left-leaning N_EXPR_FIELD chain (`os.linux` is
// field-access 'linux' over ident 'os'), or as a bare ident for the
// single-segment case (`linux.malloc`). Flatten it, then try the longest
// module prefix first so `a.b.c` prefers module `a.b.c` over module `a.b`.
//
// Returns true when the call resolved as a qualified module member, in which
// case the caller must NOT try to resolve the receiver as a value — doing so
// is what produced the spurious "unresolved name" on `os` itself.
fn bool Resolver.try_resolve_qualified_call(Resolver* r, Node* call, Node* recv)
{
    uint[16] segs;
    usz n = flatten_chain(recv, &segs[0], 16);
    if (n < 1) { return false; }
    // See seg_is_local_value: a parameter or local named like a module makes
    // this a METHOD call on a value, not a module-qualified call.
    if (r.seg_is_local_value(segs[0])) { return false; }

    char[512] buf;
    for (usz take = n; take >= 1; take--)
    {
        usz pos = 0;
        for (usz i = 0; i < take; i++)
        {
            if (i > 0 && pos < 511) { buf[pos] = '.'; pos = pos + 1; }
            char* seg = r.interner.text(segs[i]);
            usz sl = r.interner.text_len(segs[i]);
            for (usz j = 0; j < sl && pos < 511; j++) { buf[pos] = seg[j]; pos = pos + 1; }
        }
        buf[pos] = 0;
        uint modname = r.interner.intern(&buf[0], pos);
        Mod* dep = r.loader.find_module(modname);
        if (dep != null)
        {
            for (int ns = 0; ns < pfront_core::NS_COUNT; ns++)
            {
                Sym* s = dep.find_export(call.name_id, ns);
                if (s != null)
                {
                    call.resolved = s.decl;
                    call.sym = s;
                    s.used = true;
                    call.flags = call.flags | pfront_core::NF_RESOLVED;
                    r.resolved_count = r.resolved_count + 1;
                    if (s.decl != null)
                    {
                        s.decl.flags = s.decl.flags | pfront_core::NF_USED;
                    }
                    // Mark the receiver chain resolved too, so the unresolved
                    // sweep and the did-you-mean pass skip it.
                    mark_chain_resolved(recv);
                    return true;
                }
            }
            // The module exists under this literal name but exports no such
            // member. Do NOT report yet: the receiver may be a local ALIAS
            // that happens to collide with a real module name.
            //
            //     use vec.vec        -- binds the alias `vec`
            //     vec.vec_len(v)     -- means vec.vec::vec_len
            //
            // A program that also loads a top-level module literally called
            // `vec` made the literal-name lookup win, and every call through
            // the alias failed with "does not export that name". The file was
            // clean on its own and broke only in a large graph — the worst
            // kind of failure to diagnose, because the broken file is correct.
            //
            // Fall through to the alias path below and only report if that
            // fails too.
            break;
        }
        if (take == 1) { break; }
    }

    // ALIAS path. The receiver's first segment may be a module alias bound by
    // a `use`, which is not the same thing as a module whose literal name
    // matches. Walk every alias with that spelling — several `use`s can bind
    // the same short name — and take the first whose module exports the
    // member.
    if (n >= 1)
    {
        Sym* cand = r.scopes == null
                  ? null
                  : r.scopes.lookup(segs[0], pfront_core::NS_TYPE);
        while (cand != null)
        {
            if (cand.kind == pfront_core::SymKind.SYM_MODULE && cand.owner != null)
            {
                for (int ns = 0; ns < pfront_core::NS_COUNT; ns++)
                {
                    Sym* s = cand.owner.find_export(call.name_id, ns);
                    if (s != null)
                    {
                        call.resolved = s.decl;
                        call.sym = s;
                        s.used = true;
                        cand.used = true;
                        call.flags = call.flags | pfront_core::NF_RESOLVED;
                        r.resolved_count = r.resolved_count + 1;
                        if (s.decl != null)
                        {
                            s.decl.flags = s.decl.flags | pfront_core::NF_USED;
                        }
                        mark_chain_resolved(recv);
                        return true;
                    }
                }
            }
            cand = cand.next;
        }
        // An alias existed but no candidate exported the member: that IS the
        // error, and blaming the member rather than the receiver is right.
        if (r.scopes != null
            && r.scopes.lookup(segs[0], pfront_core::NS_TYPE) != null)
        {
            Sym* first = r.scopes.lookup(segs[0], pfront_core::NS_TYPE);
            if (first.kind == pfront_core::SymKind.SYM_MODULE)
            {
                r.unresolved_count = r.unresolved_count + 1;
                r.diags.error(pfront_core::Phase.PH_RESOLVE, 3004,
                              call.line, call.col,
                              "this module does not export that name",
                              r.cur_file);
                mark_chain_resolved(recv);
                return true;
            }
        }
    }
    return false;
}

// Flag every node of a receiver chain as resolved. The chain names a module,
// not a value, so there is no declaration to point at — but leaving the nodes
// unflagged makes later passes report them as unresolved identifiers.
fn void mark_chain_resolved(Node* n)
{
    if (n == null) { return; }
    n.flags = n.flags | pfront_core::NF_RESOLVED;
    if (n.kind == Nk.N_EXPR_FIELD || n.kind == Nk.N_EXPR_PATH)
    {
        for (usz i = 0; i < n.child_count; i++) { mark_chain_resolved(n.children[i]); }
    }
}

// ── Expression resolution ───────────────────────────────────────────────────
fn void Resolver.resolve_expr(Resolver* r, Node* e)
{
    if (e == null) { return; }
    switch (e.kind)
    {
        case N_EXPR_IDENT:
        {
            if (e.name_id == 0) { break; }
            Sym* s = r.scopes == null ? null : r.scopes.lookup(e.name_id, pfront_core::NS_VALUE);
            if (s == null)
            {
                // A bare uppercase name may denote a type used as a value
                // (constructor position), so try the type namespace too.
                s = r.scopes == null ? null : r.scopes.lookup(e.name_id, pfront_core::NS_TYPE);
            }
            if (s != null)
            {
                e.resolved = s.decl;
                e.sym = s;
                s.used = true;
                e.flags = e.flags | pfront_core::NF_RESOLVED;
                r.resolved_count = r.resolved_count + 1;
                if (s.kind == pfront_core::SymKind.SYM_BUILTIN_FN)
                {
                    r.builtin_hits = r.builtin_hits + 1;
                }
                if (s.decl != null) { s.decl.flags = s.decl.flags | pfront_core::NF_USED; }
            }
            else
            {
                r.unresolved_count = r.unresolved_count + 1;
                r.diags.error_hint(pfront_core::Phase.PH_RESOLVE, 3005, e.line, e.col,
                                   "unresolved name",
                                   "check spelling, or import the module that defines it",
                                   r.cur_file);
            }
        }

        case N_EXPR_PATH:
            r.resolve_path_value(e, e);

        case N_EXPR_FIELD:
        {
            // `os.linux.malloc` parses as a chain of field accesses, but the
            // prefix may name a MODULE rather than a value. Try to interpret
            // the chain as a qualified name first; only if that fails do we
            // treat it as a genuine field access on a value.
            if (r.try_resolve_module_chain(e)) { break; }
            r.resolve_expr(e.child(0));
        }

        case N_EXPR_METHOD:
        {
            // `a.b.f(x)` is ambiguous in surface syntax: it is either a METHOD
            // call on the value `a.b`, or a call to `f` exported by the MODULE
            // `a.b`. The parser cannot tell them apart, so it always builds
            // N_EXPR_METHOD and resolution decides.
            //
            // Try the module reading FIRST, because a module path is an exact
            // match against the loaded-module table while the value reading is
            // a scope lookup that would fail and emit "unresolved name" for a
            // perfectly valid call. `os.linux.malloc(n)` is the canonical
            // case, and it appears throughout the stdlib.
            Node* recv = e.child(0);
            if (recv != null && e.name_id != 0
                && r.try_resolve_qualified_call(e, recv))
            {
                // Receiver is a module path — do NOT resolve it as a value.
                // Arguments still need resolving.
                for (usz i = 1; i < e.child_count; i++)
                {
                    r.resolve_expr(e.children[i]);
                }
                break;
            }
            for (usz i = 0; i < e.child_count; i++) { r.resolve_expr(e.children[i]); }
        }

        case N_EXPR_STRUCT_LIT:
        {
            Node* nm = e.child(0);
            if (nm != null && nm.name_id != 0)
            {
                Sym* s = r.scopes == null ? null : r.scopes.lookup(nm.name_id, pfront_core::NS_TYPE);
                if (s != null)
                {
                    e.resolved = s.decl;
                    nm.resolved = s.decl;
                    s.used = true;
                    r.resolved_count = r.resolved_count + 1;
                }
                else
                {
                    r.unresolved_count = r.unresolved_count + 1;
                    r.diags.error(pfront_core::Phase.PH_RESOLVE, 3006, e.line, e.col,
                                  "unknown struct type in literal", r.cur_file);
                }
            }
            for (usz i = 1; i < e.child_count; i++)
            {
                Node* fi = e.children[i];
                if (fi != null) { r.resolve_expr(fi.child(0)); }
            }
        }

        case N_EXPR_IF:
        {
            r.resolve_expr(e.child(0));
            r.push_scope(e);
            r.resolve_expr(e.child(1));
            r.pop_scope();
            if (e.child_count >= 3)
            {
                r.push_scope(e);
                r.resolve_expr(e.child(2));
                r.pop_scope();
            }
        }

        case N_EXPR_WHILE:
        {
            r.resolve_expr(e.child(0));
            r.loop_depth = r.loop_depth + 1;
            r.push_scope(e);
            r.resolve_expr(e.child(1));
            r.pop_scope();
            r.loop_depth = r.loop_depth - 1;
        }

        case N_EXPR_FOR:
        {
            r.resolve_expr(e.child(1));      // iterable, resolved outside the body scope
            r.loop_depth = r.loop_depth + 1;
            r.push_scope(e);
            r.bind_pattern(e.child(0));
            r.resolve_expr(e.child(2));
            r.pop_scope();
            r.loop_depth = r.loop_depth - 1;
        }

        case N_EXPR_MATCH:
        {
            r.resolve_expr(e.child(0));
            for (usz i = 1; i < e.child_count; i++)
            {
                Node* arm = e.children[i];
                if (arm == null) { continue; }
                r.push_scope(arm);
                r.bind_pattern(arm.child(0));
                for (usz j = 1; j < arm.child_count; j++)
                {
                    r.resolve_expr(arm.children[j]);
                }
                r.pop_scope();
            }
        }

        case N_EXPR_HANDLE:
        {
            r.handler_depth = r.handler_depth + 1;
            r.resolve_expr(e.child(0));
            for (usz i = 1; i < e.child_count; i++)
            {
                Node* arm = e.children[i];
                if (arm == null) { continue; }
                r.push_scope(arm);
                // child 0 is the effect path; remaining leading children are binders
                for (usz j = 0; j < arm.child_count; j++)
                {
                    Node* c = arm.children[j];
                    if (c == null) { continue; }
                    if (j == 0 && c.kind == Nk.N_MODULE_PATH) { r.resolve_path_value(c, arm); continue; }
                    if (pfront_core::is_pattern(c.kind)) { r.bind_pattern(c); }
                    else { r.resolve_expr(c); }
                }
                r.pop_scope();
            }
            r.handler_depth = r.handler_depth - 1;
        }

        case N_EXPR_LAMBDA:
        {
            r.push_scope(e);
            for (usz i = 0; i < e.child_count; i++)
            {
                Node* c = e.children[i];
                if (c == null) { continue; }
                if (c.kind == Nk.N_DECL_PARAM)
                {
                    r.bind_pattern(c.child(0));
                    if (c.type_ann != null) { r.resolve_type(c.type_ann); }
                }
                else if (c.kind == Nk.N_CLAUSE)
                {
                    r.push_scope(c);
                    r.bind_pattern(c.child(0));
                    for (usz j = 1; j < c.child_count; j++) { r.resolve_expr(c.children[j]); }
                    r.pop_scope();
                }
                else { r.resolve_expr(c); }
            }
            if (e.type_ann != null) { r.resolve_type(e.type_ann); }
            r.pop_scope();
        }

        case N_BLOCK:
        {
            r.push_scope(e);
            // Hoist nested declarations so mutual recursion inside a block works.
            for (usz i = 0; i < e.child_count; i++)
            {
                Node* c = e.children[i];
                if (c != null && (c.kind == Nk.N_DECL_FN || c.kind == Nk.N_DECL_STRUCT
                               || c.kind == Nk.N_DECL_ENUM || c.kind == Nk.N_DECL_TYPE))
                {
                    r.hoist_one(c);
                }
            }
            for (usz i = 0; i < e.child_count; i++) { r.resolve_stmt(e.children[i]); }
            r.pop_scope();
        }

        case N_EXPR_CAST:
        {
            r.resolve_expr(e.child(0));
            if (e.type_ann != null) { r.resolve_type(e.type_ann); }
        }

        case N_EXPR_ALLOC:
        case N_EXPR_SIZEOF:
        case N_EXPR_ALIGNOF:
        case N_EXPR_OFFSETOF:
        case N_EXPR_TRANSMUTE:
        {
            if (e.type_ann != null) { r.resolve_type(e.type_ann); }
            for (usz i = 0; i < e.child_count; i++) { r.resolve_expr(e.children[i]); }
        }

        default:
        {
            for (usz i = 0; i < e.child_count; i++)
            {
                Node* c = e.children[i];
                if (c == null) { continue; }
                if (pfront_core::is_pattern(c.kind)) { r.bind_pattern(c); }
                else { r.resolve_stmt(c); }
            }
            if (e.type_ann != null) { r.resolve_type(e.type_ann); }
        }
    }
}

fn void Resolver.resolve_stmt(Resolver* r, Node* s)
{
    if (s == null) { return; }
    switch (s.kind)
    {
        case N_DECL_LET:
        {
            // Initializer is resolved BEFORE the binder enters scope, so
            // `let x = x` refers to an outer x rather than itself.
            for (usz i = 1; i < s.child_count; i++) { r.resolve_expr(s.children[i]); }
            if (s.type_ann != null) { r.resolve_type(s.type_ann); }
            r.bind_pattern(s.child(0));
        }
        case N_DECL_CONST:
        case N_DECL_STATIC:
        {
            for (usz i = 0; i < s.child_count; i++) { r.resolve_expr(s.children[i]); }
            if (s.type_ann != null) { r.resolve_type(s.type_ann); }
            r.declare(s.name_id, pfront_core::SymKind.SYM_VALUE, pfront_core::NS_VALUE, s, false);
        }
        case N_DECL_FN:
            r.resolve_fn(s);
        case N_STMT_BREAK:
        case N_STMT_CONTINUE:
        {
            if (r.loop_depth == 0)
            {
                r.diags.error(pfront_core::Phase.PH_RESOLVE, 3007, s.line, s.col,
                              "break/continue used outside a loop", r.cur_file);
            }
            for (usz i = 0; i < s.child_count; i++) { r.resolve_expr(s.children[i]); }
        }
        case N_STMT_ASSIGN:
        case N_STMT_COMPOUND_ASSIGN:
        {
            r.resolve_expr(s.child(0));
            r.resolve_expr(s.child(1));
            // Assigning to an immutable binding is a real error worth catching
            // here, while we still have the declaration in hand.
            Node* lhs = s.child(0);
            if (lhs != null && lhs.kind == Nk.N_EXPR_IDENT && lhs.resolved != null)
            {
                Node* d = lhs.resolved;
                bool mutable = (d.flags & pfront_core::NF_MUT) != 0;
                // ADVISORY, not an error. Pride is untyped and assumes the
                // developer knows what they are doing; mutability is
                // documentation, not a gate. This site was missed when the
                // other mutability checks were demoted (E3330/E3331/E3332 in
                // pfront_check.c3) and was still failing builds on every
                // module-level lazy-init table in the stdlib.
                if (!mutable && d.kind == Nk.N_DECL_LET)
                {
                    r.diags.advisory_hint(pfront_core::Phase.PH_RESOLVE, 3008,
                                          s.line, s.col,
                                          "assignment to a binding not declared `mut`",
                                          "Pride allows this; `let mut` documents the intent",
                                          r.cur_file);
                }
            }
        }
        default:
            r.resolve_expr(s);
    }
}

// A `rewrite` block is parsed as a synthetic N_DECL_FN whose clauses are
// RULES, not function arms. In a rule, a bare lowercase identifier is a
// PATTERN METAVARIABLE that matches any subterm — it is not a reference to
// something in scope:
//
//     rewrite arith
//       | x + 0 ↦ x        -- `x` binds here, it does not resolve
//
// Resolving those as ordinary identifiers reported "unresolved name" for
// every metavariable in every rule, which made the whole documented rewrite
// syntax unusable. theory_trs matches them structurally and never consults
// the symbol table, so binding them locally is both correct and sufficient.
fn bool is_rewrite_decl(Node* f)
{
    if (f == null || f.kind != Nk.N_DECL_FN) { return false; }
    if ((f.flags & pfront_core::NF_SYNTHETIC) == 0) { return false; }
    // A rewrite block has clauses but no signature; a real function always
    // carries a type annotation.
    return f.type_ann == null;
}

// Declare every identifier appearing in a rule as a metavariable, so later
// occurrences on the right-hand side resolve to the same binder.
fn void Resolver.bind_metavars(Resolver* r, Node* n, int depth)
{
    if (n == null || depth > 200) { return; }
    if (n.kind == Nk.N_EXPR_IDENT && n.name_id != 0)
    {
        Sym* existing = r.scopes == null
                      ? null
                      : r.scopes.lookup(n.name_id, pfront_core::NS_VALUE);
        if (existing == null)
        {
            r.declare(n.name_id, pfront_core::SymKind.SYM_VALUE,
                      pfront_core::NS_VALUE, n, false);
        }
    }
    for (usz i = 0; i < n.child_count; i++)
    {
        r.bind_metavars(n.children[i], depth + 1);
    }
}

fn void Resolver.resolve_fn(Resolver* r, Node* f)
{
    if (f == null) { return; }
    Node* saved_fn = r.cur_fn;
    r.cur_fn = f;
    r.push_scope(f);

    if (is_rewrite_decl(f))
    {
        // One scope per rule: `x` in one rule is unrelated to `x` in the next.
        for (usz i = 0; i < f.child_count; i++)
        {
            Node* rule = f.children[i];
            if (rule == null || rule.kind != Nk.N_CLAUSE) { continue; }
            r.push_scope(rule);
            r.bind_metavars(rule, 0);
            for (usz j = 0; j < rule.child_count; j++)
            {
                r.resolve_expr(rule.children[j]);
            }
            r.pop_scope();
        }
        r.pop_scope();
        r.cur_fn = saved_fn;
        return;
    }

    // Type parameters first, so the signature can mention them.
    for (usz i = 0; i < f.child_count; i++)
    {
        Node* c = f.children[i];
        if (c != null && c.kind == Nk.N_DECL_TYPEPARAM)
        {
            r.declare(c.name_id, pfront_core::SymKind.SYM_TYPEPARAM,
                      pfront_core::NS_TYPE, c, false);
        }
    }
    if (f.type_ann != null) { r.resolve_type(f.type_ann); }

    for (usz i = 0; i < f.child_count; i++)
    {
        Node* c = f.children[i];
        if (c == null) { continue; }
        switch (c.kind)
        {
            case N_DECL_TYPEPARAM:
                break;
            case N_DECL_PARAM:
            {
                if (c.type_ann != null) { r.resolve_type(c.type_ann); }
                r.bind_pattern(c.child(0));
            }
            case N_CLAUSE:
            {
                r.push_scope(c);
                r.bind_pattern(c.child(0));
                for (usz j = 1; j < c.child_count; j++)
                {
                    Node* cc = c.children[j];
                    if (cc == null) { continue; }
                    if (cc.kind == Nk.N_GUARD) { r.resolve_expr(cc.child(0)); }
                    else { r.resolve_expr(cc); }
                }
                r.pop_scope();
            }
            case N_TY_EFFECT_ROW:
                r.resolve_type(c);
            case N_TY_WHERE:
                r.resolve_type(c);
            case N_DOC:
                break;
            default:
                r.resolve_expr(c);
        }
    }
    r.pop_scope();
    r.cur_fn = saved_fn;
}

// ── Top-level driver ────────────────────────────────────────────────────────
fn void Resolver.resolve_module(Resolver* r, Mod* m)
{
    if (m == null || m.ast == null) { return; }
    if (m.state == pfront_core::ModState.MOD_RESOLVED) { return; }
    m.state = pfront_core::ModState.MOD_RESOLVED;

    Mod* saved = r.cur_module;
    char* saved_file = r.cur_file;
    r.cur_module = m;
    r.cur_file = m.path;

    r.push_scope(m.ast);
    r.install_builtins();
    r.bind_imports(m.ast);
    r.hoist_decls(m.ast);

    for (usz i = 0; i < m.ast.child_count; i++)
    {
        Node* d = m.ast.children[i];
        if (d == null) { continue; }
        switch (d.kind)
        {
            case N_DECL_FN:
            case N_DECL_EXTERN_FN:
                r.resolve_fn(d);
            case N_DECL_STRUCT:
            case N_DECL_UNION:
            {
                r.push_scope(d);
                for (usz j = 0; j < d.child_count; j++)
                {
                    Node* fl = d.children[j];
                    if (fl == null) { continue; }
                    if (fl.kind == Nk.N_DECL_TYPEPARAM)
                    {
                        r.declare(fl.name_id, pfront_core::SymKind.SYM_TYPEPARAM,
                                  pfront_core::NS_TYPE, fl, false);
                    }
                }
                for (usz j = 0; j < d.child_count; j++)
                {
                    Node* fl = d.children[j];
                    if (fl != null && fl.kind == Nk.N_DECL_FIELD && fl.type_ann != null)
                    {
                        r.resolve_type(fl.type_ann);
                    }
                }
                r.pop_scope();
            }
            case N_DECL_ENUM:
            {
                r.push_scope(d);
                for (usz j = 0; j < d.child_count; j++)
                {
                    Node* v = d.children[j];
                    if (v == null) { continue; }
                    if (v.kind == Nk.N_DECL_TYPEPARAM)
                    {
                        r.declare(v.name_id, pfront_core::SymKind.SYM_TYPEPARAM,
                                  pfront_core::NS_TYPE, v, false);
                    }
                }
                for (usz j = 0; j < d.child_count; j++)
                {
                    Node* v = d.children[j];
                    if (v == null || v.kind != Nk.N_DECL_VARIANT) { continue; }
                    for (usz k = 0; k < v.child_count; k++)
                    {
                        Node* pt = v.children[k];
                        if (pt != null && pfront_core::is_type(pt.kind)) { r.resolve_type(pt); }
                        else if (pt != null) { r.resolve_expr(pt); }
                    }
                }
                r.pop_scope();
            }
            case N_DECL_TYPE:
            case N_DECL_NEWTYPE:
            {
                r.push_scope(d);
                for (usz j = 0; j < d.child_count; j++)
                {
                    Node* tp = d.children[j];
                    if (tp != null && tp.kind == Nk.N_DECL_TYPEPARAM)
                    {
                        r.declare(tp.name_id, pfront_core::SymKind.SYM_TYPEPARAM,
                                  pfront_core::NS_TYPE, tp, false);
                    }
                }
                if (d.type_ann != null) { r.resolve_type(d.type_ann); }
                r.pop_scope();
            }
            case N_DECL_EFFECT:
            {
                r.push_scope(d);
                for (usz j = 0; j < d.child_count; j++)
                {
                    Node* op = d.children[j];
                    if (op == null || op.kind != Nk.N_DECL_EFFECT_OP) { continue; }
                    for (usz k = 0; k < op.child_count; k++)
                    {
                        r.resolve_type(op.children[k]);
                    }
                }
                r.pop_scope();
            }
            case N_DECL_INTERFACE:
            case N_DECL_IMPL:
            {
                r.push_scope(d);
                // `Self` names the implementing type and is in scope for the
                // whole body:
                //     interface Add
                //       fn add : (Self, Self) -> Self
                // Nothing declared it, so every mention resolved to nothing
                // and reported "unknown type name" — which made every
                // interface in the stdlib fail on its own signature.
                //
                // Bind it to the declaration itself. For an `impl` that is
                // the concrete type; for an `interface` it is the abstract
                // one, which is exactly the distinction `Self` expresses.
                uint self_id = r.interner.intern("Self", 4);
                r.declare(self_id, pfront_core::SymKind.SYM_TYPE,
                          pfront_core::NS_TYPE, d, false);
                for (usz j = 0; j < d.child_count; j++)
                {
                    Node* c = d.children[j];
                    if (c == null) { continue; }
                    if (c.kind == Nk.N_DECL_FN) { r.resolve_fn(c); }
                    else if (pfront_core::is_type(c.kind)) { r.resolve_type(c); }
                }
                r.pop_scope();
            }
            case N_DECL_LET:
            case N_DECL_CONST:
            case N_DECL_STATIC:
            {
                for (usz j = 0; j < d.child_count; j++)
                {
                    Node* c = d.children[j];
                    if (c != null && !pfront_core::is_pattern(c.kind)) { r.resolve_expr(c); }
                }
                if (d.type_ann != null) { r.resolve_type(d.type_ann); }
            }
            case N_USE:
            case N_DOC:
                break;
            case N_MODULE:
            {
                r.hoist_decls(d);
                for (usz j = 0; j < d.child_count; j++)
                {
                    Node* c = d.children[j];
                    if (c != null && c.kind == Nk.N_DECL_FN) { r.resolve_fn(c); }
                }
            }
            default:
                r.resolve_stmt(d);
        }
    }
    r.pop_scope();
    r.cur_module = saved;
    r.cur_file = saved_file;
}

// Resolve every loaded module, dependencies first.
fn void Resolver.resolve_all(Resolver* r)
{
    // Collect exports for every module before resolving any of them, so that
    // import order does not matter and cycles still see each other's symbols.
    for (usz i = 0; i < r.loader.module_count; i++)
    {
        r.collect_exports(r.loader.modules[i]);
    }
    // Resolve in reverse load order: dependencies were appended after their
    // requester, so this visits leaves first.
    usz n = r.loader.module_count;
    for (usz i = n; i > 0; i--)
    {
        r.resolve_module(r.loader.modules[i - 1]);
    }
}

// ── Reporting ───────────────────────────────────────────────────────────────
fn void Resolver.report(Resolver* r)
{
    printf("  modules loaded   : %d\n", (int)r.loader.module_count);
    printf("  files read       : %d\n", (int)r.loader.files_read);
    printf("  names resolved   : %d\n", (int)r.resolved_count);
    printf("  names unresolved : %d\n", (int)r.unresolved_count);
    printf("  builtin hits     : %d\n", (int)r.builtin_hits);
}

fn void Loader.report(Loader* l)
{
    printf("  === module graph (%d modules) ===\n", (int)l.module_count);
    for (usz i = 0; i < l.module_count; i++)
    {
        Mod* m = l.modules[i];
        char* nm = l.interner.text(m.name_id);
        printf("    [%d] %s  (%d imports, %d bytes)\n",
               (int)i, nm == null ? (char*)"<entry>" : nm,
               (int)m.import_count, (int)m.source_len);
    }
}
