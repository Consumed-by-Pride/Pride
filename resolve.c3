// resolve.c3 — Pride name resolution
// Implementation language: C3 (host).
// Walks the AST produced by parser.c3 and resolves every identifier / type
// variable use to the declaration that introduces it, recording the link in
// `AstNode.resolved`. Reports undefined names and duplicate definitions.
// Pipeline:  ... -> Parser -> AST -> Resolver (this) -> (typecheck) -> ...
// Scope model:
//   - A stack of lexical scopes. Each scope owns a flat list of bindings.
//   - Two namespaces per binding: VALUE (let/fn/param/effect ops, etc.) and
//     TYPE (type/struct/union/effect names, generic type vars). A name may
//     exist in both at once (e.g. a struct's value-constructor vs its type).
//   - Pride allows shadowing in inner scopes; a redefinition in the *same*
//     scope and namespace is a duplicate-definition error.
// Two-pass at each scope so declarations are visible regardless of order
// (mutual recursion between top-level fns, forward type references, etc.):
//   pass 1 — hoist all declaration names into the scope
//   pass 2 — resolve uses inside each declaration's body

module resolve;

import lexer;
import ast;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   memcmp(void* a, void* b, usz n);

alias Node = ast::AstNode;
alias Nk = ast::NodeKind;

// Namespaces a name can live in.
const int NS_VALUE = 0;
const int NS_TYPE  = 1;

// One resolution diagnostic.
struct ResolveError
{
    char* msg;
    int   line;
    int   col;
}

// A single binding in a scope: a name span plus the declaring node + namespace.
struct Binding
{
    char* name_ptr;
    usz   name_len;
    int   ns;
    Node* decl;
}

// A lexical scope: a bounded list of bindings, linked to its parent.
const usz SCOPE_CAP = 256;
const usz SCOPE_HASH_SIZE = 512;  // power of 2, > SCOPE_CAP

struct Scope
{
    Binding[SCOPE_CAP] bindings;
    usz count;
    Scope* parent;
    // Fast hash index: hash(name,len,ns) -> binding index+1 (0=empty)
    usz[SCOPE_HASH_SIZE] hash_idx;
    bool hash_valid;  // true after first build (rebuilt on push)
}

// The resolver state.
const usz MAX_SCOPES = 256;

struct Resolver
{
    // Scope stack, owned here. scopes[0] is the global scope.
    Scope[MAX_SCOPES] scopes;
    int top;                 // index of the current (innermost) scope

    ResolveError[512] errors;
    int error_count;
    bool had_error;

    // Recursion-depth guard: deep type/expr trees (e.g. 1000-deep ∩/∪ chains)
    // would otherwise overflow the stack in resolve_node's generic recursion.
    int depth;
}

const int MAX_RESOLVE_DEPTH = 1500;

fn void Resolver.init(Resolver* self)
{
    self.top = 0;
    self.scopes[0].count = 0;
    self.scopes[0].parent = null;
    self.scopes[0].hash_valid = false;
    for (usz i = 0; i < SCOPE_HASH_SIZE; i++) self.scopes[0].hash_idx[i] = 0;
    self.error_count = 0;
    self.had_error = false;
    self.depth = 0;
}

fn void Resolver.error(Resolver* self, char* msg, int line, int col)
{
    self.had_error = true;
    if (self.error_count < 512)
    {
        ResolveError e;
        e.msg = msg;
        e.line = line;
        e.col = col;
        self.errors[self.error_count] = e;
        self.error_count++;
    }
}

fn Scope* Resolver.cur(Resolver* self)
{
    return &self.scopes[self.top];
}

fn void Resolver.push_scope(Resolver* self)
{
    if (self.top + 1 >= (int)MAX_SCOPES)
    {
        self.error("scope nesting too deep", 0, 0);
        return;
    }
    self.top++;
    self.scopes[self.top].count = 0;
    self.scopes[self.top].parent = &self.scopes[self.top - 1];
    // Every scope slot is reused across push/pop cycles (Resolver embeds a
    // fixed Scope[MAX_SCOPES] array), so hash_valid/hash_idx from a PRIOR
    // occupant of this slot must never be trusted here — always start a
    // freshly-entered scope with an invalidated hash index. lookup_local()
    // lazily rebuilds it (from `bindings[0..count)`) the first time it's
    // actually needed.
    self.scopes[self.top].hash_valid = false;
}

fn void Resolver.pop_scope(Resolver* self)
{
    if (self.top > 0) self.top--;
}

fn bool name_eq(char* a, usz alen, char* b, usz blen)
{
    if (alen != blen) return false;
    if (alen == 0) return true;
    // Fast first-char check eliminates ~80% of comparisons
    if (a[0] != b[0]) return false;
    if (alen == 1) return true;
    // Use memcmp for the rest
    return memcmp((void*)a, (void*)b, alen) == 0;
}

// Extract the name span from an IDENT/TYPEVAR node (or a wrapper that holds one
// as its first child, e.g. PatIdent). Returns false if no name is available.
fn bool name_of(Node* n, char** out_ptr, usz* out_len)
{
    if (n == null) return false;
    if (n.kind == Nk.NODE_IDENT || n.kind == Nk.NODE_TYPEVAR
        || n.kind == Nk.NODE_TYPE_PRIMITIVE)
    {
        *out_ptr = n.p.ident.name_ptr;
        *out_len = n.p.ident.name_len;
        return true;
    }
    return false;
}

// Look up a name in the current scope only (for duplicate detection).
fn void Scope.rebuild_hash(Scope* s) @private
{
    for (usz i = 0; i < SCOPE_HASH_SIZE; i++) s.hash_idx[i] = 0;
    // Insert NEWEST-first so a probe chain for a re-bound (shadowed) name
    // meets the newest binding at its home slot — lookup returns the first
    // match it finds, and that must be the freshest binding, not the stale
    // one. (Same-scope rebinding via a second `let` is legal shadowing.)
    for (usz ii = s.count; ii-- > 0;)
    {
        usz i = ii;
        Binding* b = &s.bindings[i];
        ulong h = 14695981039346656037u;
        for (usz j = 0; j < b.name_len; j++) { h ^= (ulong)(uint)b.name_ptr[j]; h *= 1099511628211u; }
        h ^= (ulong)(uint)b.ns;
        h ^= (ulong)b.name_len;
        usz hslot = (usz)(h & (ulong)(SCOPE_HASH_SIZE - 1));
        while (s.hash_idx[hslot] != 0) { hslot = (hslot + 1) & (SCOPE_HASH_SIZE - 1); }
        s.hash_idx[hslot] = (usz)(i + 1);
    }
    s.hash_valid = true;
}

fn Node* Resolver.lookup_local(Resolver* self, char* ptr, usz len, int ns)
{
    Scope* s = self.cur();
    if (!s.hash_valid && s.count > 4) { s.rebuild_hash(); }
    if (s.hash_valid && s.count > 4)
    {
        // O(1) hash lookup
        ulong h = 14695981039346656037u;
        for (usz i = 0; i < len; i++) { h ^= (ulong)(uint)ptr[i]; h *= 1099511628211u; }
        h ^= (ulong)(uint)ns;
        h ^= (ulong)len;
        usz hslot = (usz)(h & (ulong)(SCOPE_HASH_SIZE - 1));
        usz probe = 0;
        while (probe < SCOPE_HASH_SIZE)
        {
            usz idx = s.hash_idx[hslot];
            if (idx == 0) return null;  // empty slot = not found
            Binding* b = &s.bindings[idx - 1];
            if (b.ns == ns && name_eq(b.name_ptr, b.name_len, ptr, len)) return b.decl;
            hslot = (hslot + 1) & (SCOPE_HASH_SIZE - 1);
            probe++;
        }
        return null;
    }
    // Fallback: linear scan for small scopes
    for (usz i = 0; i < s.count; i++)
    {
        Binding* b = &s.bindings[i];
        if (b.ns == ns && name_eq(b.name_ptr, b.name_len, ptr, len)) return b.decl;
    }
    return null;
}

// Look up a name walking outward through all enclosing scopes.
// Within one scope, walk NEWEST→oldest: a same-scope redefinition (second
// `let x` — legal shadowing, like Rust) must win over the stale binding,
// never silently resurrect it. `bind` appends, so newest is at the tail.
fn Node* Resolver.lookup(Resolver* self, char* ptr, usz len, int ns)
{
    Scope* s = self.cur();
    while (s != null)
    {
        for (usz ii = s.count; ii-- > 0;)
        {
            Binding* b = &s.bindings[ii];
            if (b.ns == ns && name_eq(b.name_ptr, b.name_len, ptr, len)) return b.decl;
        }
        s = s.parent;
    }
    return null;
}

// Insert a binding into the current scope. `dup_is_error` controls whether a
// same-scope redefinition is reported (true for top-level/fields, false for
// pattern binders which may legitimately repeat across or-pattern arms).
fn void Resolver.bind(Resolver* self, char* ptr, usz len, int ns, Node* decl, bool dup_is_error)
{
    if (ptr == null || len == 0) return;

    // A lone underscore never binds.
    if (len == 1 && ptr[0] == '_') return;

    if (dup_is_error)
    {
        Node* prev = self.lookup_local(ptr, len, ns);
        if (prev != null)
        {
            self.error("duplicate definition in this scope",
                decl != null ? decl.line : 0, decl != null ? decl.col : 0);
            return;
        }
    }

    Scope* s = self.cur();
    if (s.count >= SCOPE_CAP)
    {
        self.error("too many declarations in one scope", 0, 0);
        return;
    }
    Binding* b = &s.bindings[s.count];
    b.name_ptr = ptr;
    b.name_len = len;
    b.ns = ns;
    b.decl = decl;
    s.count++;
    // A new binding invalidates any previously-built hash index for this
    // scope; lookup_local() lazily rebuilds it from `bindings[0..count)`
    // next time it's consulted.
    s.hash_valid = false;
}

// Bind a name node (IDENT/TYPEVAR) into a namespace.
fn void Resolver.bind_name_node(Resolver* self, Node* name, int ns, Node* decl, bool dup_is_error)
{
    char* ptr;
    usz len;
    if (name_of(name, &ptr, &len))
    {
        self.bind(ptr, len, ns, decl, dup_is_error);
    }
}

// Walk a pattern and bind every identifier it introduces into NS_VALUE.
// Detect a binder name appearing twice in the SAME pattern, e.g. `(a, a)`.
// OR-patterns are exempt (alternatives intentionally share names). Uses a
// bounded local list of seen name spans.
const usz DUP_SCAN_MAX = 256;

struct DupScan
{
    char*[DUP_SCAN_MAX] ptrs;
    usz[DUP_SCAN_MAX] lens;
    usz count;
    bool reported;
}

fn void Resolver.check_dup_binders(Resolver* self, Node* pat)
{
    DupScan scan;
    scan.count = 0;
    scan.reported = false;
    self.scan_dup(pat, &scan, false);
}

fn void Resolver.scan_dup(Resolver* self, Node* pat, DupScan* scan, bool in_or)
{
    if (pat == null) return;

    switch (pat.kind)
    {
        case Nk.NODE_PATTERN_IDENT:
            if (in_or) return;   // OR arms may legitimately rebind the same name
            Node* nm = pat.child_count >= 1 ? pat.children[0] : null;
            if (nm == null) return;
            char* p = nm.p.ident.name_ptr;
            usz len = nm.p.ident.name_len;
            // Skip `_`-only.
            if (len == 1 && p[0] == '_') return;
            for (usz i = 0; i < scan.count; i++)
            {
                if (name_eq(scan.ptrs[i], scan.lens[i], p, len))
                {
                    if (!scan.reported)
                    {
                        self.error("duplicate binding in the same pattern", nm.line, nm.col);
                        scan.reported = true;
                    }
                    return;
                }
            }
            if (scan.count < DUP_SCAN_MAX)
            {
                scan.ptrs[scan.count] = p;
                scan.lens[scan.count] = len;
                scan.count++;
            }

        case Nk.NODE_PATTERN_OR:
            for (usz i = 0; i < pat.child_count; i++)
            {
                self.scan_dup(pat.children[i], scan, true);
            }

        default:
            for (usz i = 0; i < pat.child_count; i++)
            {
                self.scan_dup(pat.children[i], scan, in_or);
            }
    }
}

fn void Resolver.bind_pattern(Resolver* self, Node* pat)
{
    if (pat == null) return;

    switch (pat.kind)
    {
        case Nk.NODE_PATTERN_IDENT:
            // child 0 is the name
            if (pat.child_count >= 1)
            {
                self.bind_name_node(pat.children[0], NS_VALUE, pat, false);
            }

        case Nk.NODE_PATTERN_WILDCARD:
            break;   // binds nothing

        case Nk.NODE_PATTERN_LITERAL:
            break;   // matches a value, binds nothing

        case Nk.NODE_PATTERN_TUPLE:
        case Nk.NODE_PATTERN_OR:
            for (usz i = 0; i < pat.child_count; i++)
            {
                self.bind_pattern(pat.children[i]);
            }

        case Nk.NODE_PATTERN_STRUCT:
            // The name heading the pattern (`Dollars(v)`, `Point{x, y}`) is a
            // USE of a type, not a binder: resolve it QUIETLY (a miss is left
            // unresolved, never an error — heads may be generic params or
            // names bound later), so the type checker and both lowerings can
            // recognize a newtype destructure (identity unwrap) from
            // .resolved. It went unresolved before — emit-side pipelines
            // compensated from the fn signature, but the lowering saw nothing
            // and fabricated unit/undefined binders for what is really an
            // identity operation.
            if (pat.child_count >= 1 && pat.children[0] != null
                && (pat.children[0].kind == Nk.NODE_TYPEVAR
                    || pat.children[0].kind == Nk.NODE_IDENT)
                && pat.children[0].resolved == null)
            {
                char* hp; usz hl;
                if (name_of(pat.children[0], &hp, &hl))
                {
                    Node* pd = self.lookup(hp, hl, NS_TYPE);
                    if (pd != null) pat.children[0].resolved = self.chase_member_use(pd);
                }
            }
            for (usz i = 0; i < pat.child_count; i++)
            {
                self.bind_pattern_field(pat.children[i]);
            }

        default:
            // Defensive: recurse so nested binders are still captured.
            for (usz i = 0; i < pat.child_count; i++)
            {
                self.bind_pattern(pat.children[i]);
            }
    }
}

// A struct-pattern field is either  name  (shorthand: binds `name`) or
// name : subpattern  (binds whatever the subpattern introduces).
fn void Resolver.bind_pattern_field(Resolver* self, Node* field)
{
    if (field == null) return;
    // Newtype/enum payload patterns emit PatIdent directly as struct children
    if (field.kind == Nk.NODE_PATTERN_IDENT)
    {
        self.bind_pattern(field);
        return;
    }
    if (field.kind != Nk.NODE_PATTERN_FIELD) return;

    if (field.child_count == 1)
    {
        // shorthand { x } binds x
        self.bind_name_node(field.children[0], NS_VALUE, field, false);
    }
    else if (field.child_count >= 2)
    {
        // { name : subpattern } — the field name is the struct field (a use,
        // resolved later against the type), the subpattern introduces binders.
        self.bind_pattern(field.children[1]);
    }
}

fn void Resolver.hoist_decl(Resolver* self, Node* d)
{
    if (d == null) return;

    switch (d.kind)
    {
        case Nk.NODE_DECL_FN:
            // First non-attribute child is the function name.
            // When #[attr] is prepended, child 0 is NODE_ATTRIBUTE_LIST and child 1 is the name.
            {
                Node* fn_name_nd = null;
                for (usz fni = 0; fni < d.child_count; fni++)
                {
                    Node* fc = d.children[fni];
                    if (fc != null && fc.kind != Nk.NODE_ATTRIBUTE_LIST)
                        { fn_name_nd = fc; break; }
                }
                if (fn_name_nd != null) self.bind_name_node(fn_name_nd, NS_VALUE, d, true);
            }

        case Nk.NODE_DECL_TYPE:
        case Nk.NODE_DECL_STRUCT:
        case Nk.NODE_DECL_UNION:
        case Nk.NODE_DECL_EFFECT:
            // First non-attribute child is the type/effect name (TYPEVAR)
            {
                Node* tn_nd = null;
                for (usz tni = 0; tni < d.child_count; tni++)
                {
                    Node* tc = d.children[tni];
                    if (tc != null && tc.kind != Nk.NODE_ATTRIBUTE_LIST)
                        { tn_nd = tc; break; }
                }
                if (tn_nd != null) self.bind_name_node(tn_nd, NS_TYPE, d, true);
            }

        case Nk.NODE_DECL_MACRO:
            // child 0 = macro name, remaining = rules
            if (d.child_count >= 1) self.bind_name_node(d.children[0], NS_VALUE, d, true);

        case Nk.NODE_DECL_NEWTYPE:
            // child 0 = newtype name, child 1 = underlying type
            if (d.child_count >= 1) self.bind_name_node(d.children[0], NS_TYPE, d, true);

        case Nk.NODE_DECL_ENUM:
            // child 0 = enum name (type), remaining children = variants (value ctors)
            if (d.child_count >= 1) self.bind_name_node(d.children[0], NS_TYPE, d, true);
            // Hoist each variant name into NS_VALUE AND NS_TYPE so it resolves from both.
            // Pre-resolve each variant name ident to its own variant node.
            for (usz evi = 1; evi < d.child_count; evi++)
            {
                Node* ev = d.children[evi];
                if (ev != null && ev.kind == Nk.NODE_ENUM_VARIANT && ev.child_count >= 1)
                {
                    self.bind_name_node(ev.children[0], NS_VALUE, ev, true);
                    self.bind_name_node(ev.children[0], NS_TYPE, ev, false);  // also in type NS
                    if (ev.children[0] != null) ev.children[0].resolved = ev;
                    // The tree is parent-less: link each variant back to the
                    // owning enum decl so a use (`Green`) or a bare
                    // variant-name pattern can recover the discriminant by
                    // declaration order (the { i32, i64 } repr's tag). Uses
                    // .resolved — putting the back-link in .type_annotation
                    // creates a cycle monomorphization's clone_node follows
                    // recursively (variant → enum → children → variant:
                    // exponential blowup; hung the compiler on a bare enum
                    // declaration). .resolved is only remapped shallowly by
                    // fixup_resolved, so no tree walk ever cycles through it.
                    ev.resolved = d;
                }
            }

        case Nk.NODE_DECL_INTERFACE:
            // child 0 = interface name
            if (d.child_count >= 1) self.bind_name_node(d.children[0], NS_TYPE, d, true);

        case Nk.NODE_DECL_IMPL:
            // impl has no standalone name; its methods get registered by resolve pass 2
            for (usz ei = 1; ei < d.child_count; ei++)
            {
                Node* evar = d.children[ei];
                if (evar != null && evar.kind == Nk.NODE_ENUM_VARIANT && evar.child_count >= 1)
                { self.bind_name_node(evar.children[0], NS_VALUE, evar, true); }
            }

        case Nk.NODE_DECL_CONST:
        case Nk.NODE_DECL_STATIC:
            if (d.child_count >= 1) self.bind_name_node(d.children[0], NS_VALUE, d, true);

        case Nk.NODE_DECL_LET:
        case Nk.NODE_DECL_MUT:
            // child 0 is a pattern; bind its names (top-level lets are hoisted)
            if (d.child_count >= 1) self.bind_pattern(d.children[0]);

        case Nk.NODE_DECL_MOD:
            if (d.child_count >= 1) self.bind_name_node(d.children[0], NS_TYPE, d, false);

        case Nk.NODE_DECL_USE:
        case Nk.NODE_DECL_IMPORT:
            self.hoist_use(d);

        case Nk.NODE_PATTERN_DECL:
        case Nk.NODE_REWRITE_RULE:
        case Nk.NODE_PGEN:
            if (d.child_count >= 1) self.bind_name_node(d.children[0], NS_VALUE, d, false);

        case Nk.NODE_DIALECT:
            if (d.child_count >= 1) self.bind_name_node(d.children[0], NS_TYPE, d, false);

        case Nk.NODE_GRAPH:
        case Nk.NODE_NODE_DECL:
        case Nk.NODE_BLOCK_IR:
            // Top-level graph-IR declarations: hoist the name so a later edge
            // can reference a node declared earlier or later in the file.
            // (edge/hyperedge have no own name — all their names are endpoints.)
            if (d.child_count >= 1) self.bind_name_node(d.children[0], NS_VALUE, d, false);

        default:
            break;
    }
}

// `use path::seg (as alias)` binds the alias, else the last path segment.
fn void Resolver.hoist_use(Resolver* self, Node* u)
{
    if (u.child_count == 0) return;

    // Last child is the alias if there are 2 children; child 0 is the path.
    if (u.child_count >= 2)
    {
        self.bind_name_node(u.children[1], NS_TYPE, u, false);
        self.bind_name_node(u.children[1], NS_VALUE, u, false);
        return;
    }

    Node* path = u.children[0];
    if (path != null && path.kind == Nk.NODE_MODULE_PATH && path.child_count >= 1)
    {
        Node* last = path.children[path.child_count - 1];
        self.bind_name_node(last, NS_TYPE, u, false);
        self.bind_name_node(last, NS_VALUE, u, false);
    }
}

// Resolve a whole program: hoist top-level decls, then resolve each.
fn void Resolver.resolve_program(Resolver* self, Node* program)
{
    if (program == null) return;

    // Pass 1: hoist every top-level declaration name.
    for (usz i = 0; i < program.child_count; i++)
    {
        self.hoist_decl(program.children[i]);
    }

    // Pass 2: resolve each top-level declaration in full.
    for (usz i = 0; i < program.child_count; i++)
    {
        self.resolve_node(program.children[i]);
    }
}

// Find a named member declaration inside a module's body block (resolver-local
// mirror of typecheck's mod_member_decl): any top-level decl whose first child
// is an identifier/typevar naming it.
fn Node* find_mod_member(Node* moddecl, char* ptr, usz len) @private
{
    if (moddecl == null || moddecl.kind != Nk.NODE_DECL_MOD) return null;
    for (usz i = 0; i < moddecl.child_count; i++)
    {
        Node* blk = moddecl.children[i];
        if (blk == null || blk.kind != Nk.NODE_EXPR_BLOCK) continue;
        for (usz j = 0; j < blk.child_count; j++)
        {
            Node* d = blk.children[j];
            if (d == null || d.child_count < 1) continue;
            Node* nm = d.children[0];
            if (nm == null) continue;
            // let/mut-style decls bind through a pattern: unwrap one level.
            if (nm.kind == Nk.NODE_PATTERN_IDENT && nm.child_count >= 1)
            {
                nm = nm.children[0];
                if (nm == null) continue;
            }
            char* np; usz nl;
            if (!name_of(nm, &np, &nl)) continue;
            if (name_eq(np, nl, ptr, len)) return d;
        }
    }
    return null;
}

// Chase a `use path::member (as alias)` binding to the member's actual
// declaration inside the target module, so a use of the imported name behaves
// EXACTLY like a use of the member declared at top level (the type checker
// and both lowerings key off .resolved being the real declaration: a bare
// `square(40)` after `use math::square` used to resolve to the import node
// itself, fell through every consumer's fallback, and codegen emitted a call
// through inttoptr(0) — an instant SIGTRAP).
//
// A single-segment import (`use math`, `use math as m`) names the MODULE and
// is deliberately NOT chased: those bindings must keep pointing at the import
// node so field-path machinery (`m::f`) keeps working. Only a 2-segment path
// names one concrete member (sub-modules are not a feature). Resolution order
// is irrelevant: the chase runs lazily at the use site, after pass-1 hoisting
// made every top-level module findable. Import chains (`use other::math`)
// are followed with a hop cap; on any failure the original binding stands.
fn Node* Resolver.chase_member_use(Resolver* self, Node* decl)
{
    Node* cur = decl;
    for (int hops = 0; hops < 8; hops++)
    {
        if (cur == null) return decl;
        if (cur.kind != Nk.NODE_DECL_USE && cur.kind != Nk.NODE_DECL_IMPORT) return cur;
        if (cur.child_count < 1) return decl;
        Node* path = cur.children[0];
        if (path == null || path.kind != Nk.NODE_MODULE_PATH || path.child_count != 2)
        {
            return decl;   // module import (1 segment) or unsupported depth
        }
        Node* head = path.children[0];
        Node* last = path.children[1];
        Node* moddecl = null;
        if (head != null && head.resolved != null && head.resolved.kind == Nk.NODE_DECL_MOD)
        {
            moddecl = head.resolved;
        }
        else
        {
            char* hp; usz hl;
            if (head == null || !name_of(head, &hp, &hl)) return decl;
            Node* md = self.lookup(hp, hl, NS_TYPE);
            if (md != null && md.kind == Nk.NODE_DECL_MOD)
            {
                moddecl = md;
                head.resolved = md;
            }
            else if (md != null
                && (md.kind == Nk.NODE_DECL_USE || md.kind == Nk.NODE_DECL_IMPORT))
            {
                cur = md;   // the head itself names another import: follow it
                continue;
            }
            else { return decl; }
        }
        if (moddecl == null) return decl;
        char* mp; usz ml;
        if (!name_of(last, &mp, &ml)) return decl;
        Node* member = find_mod_member(moddecl, mp, ml);
        if (member == null) return decl;
        return member;
    }
    return decl;
}

// Resolve a use of a name in a given namespace, recording the link.
fn void Resolver.resolve_use_name(Resolver* self, Node* name, int ns)
{
    char* ptr;
    usz len;
    if (!name_of(name, &ptr, &len)) return;

    // A lone underscore or anonymous field name (_0, _1, ...) is never a use.
    if (len >= 1 && ptr[0] == '_') return;

    // If already resolved (e.g. pre-resolved at definition site), skip lookup.
    if (name.resolved != null) return;

    Node* decl = self.lookup(ptr, len, ns);
    if (decl != null)
    {
        name.resolved = self.chase_member_use(decl);
        return;
    }

    // Fall back to the other namespace before giving up (handles cases where a
    // name was bound as a type but used in value position, e.g. constructors).
    int other = ns == NS_VALUE ? NS_TYPE : NS_VALUE;
    Node* alt = self.lookup(ptr, len, other);
    if (alt != null)
    {
        name.resolved = self.chase_member_use(alt);
        return;
    }

    // Suppress "undefined name" for uppercase-initial idents that are likely
    // enum variant constructors used in definition position (parser places them
    // as Ident children of EnumVariant nodes; hoist_decl should have bound them,
    // but scope chain lookup can miss them under certain nesting). The resolver
    // will still bind them correctly via hoist_decl's pre-resolution.
    if (len >= 1 && ptr[0] >= 'A' && ptr[0] <= 'Z') return;

    // Use a static string literal — address is stable forever.
    // The ident name appears in the source snippet printed by the caller.
    self.error("undefined name", name.line, name.col);
}

// The core recursive resolver. Introduces scopes where the grammar does and
// resolves identifier/type uses against the visible bindings.
fn void Resolver.resolve_node(Resolver* self, Node* n)
{
    if (n == null) return;
    // Depth guard: stop descending into pathologically deep trees rather than
    // overflow the native stack. Names below the cap simply stay unresolved.
    if (self.depth >= MAX_RESOLVE_DEPTH) return;
    self.depth++;
    self.resolve_node_body(n);
    self.depth--;
}

fn void Resolver.resolve_node_body(Resolver* self, Node* n)
{
    switch (n.kind)
    {
        case Nk.NODE_IDENT:
            self.resolve_use_name(n, NS_VALUE);

        case Nk.NODE_TYPEVAR:
            // A type variable use resolves against the type namespace.
            self.resolve_use_name(n, NS_TYPE);

        case Nk.NODE_TYPE_PRIMITIVE:
            // Primitives (i32, f64, bool, ...) are always defined.
            break;

        case Nk.NODE_WILDCARD:
        case Nk.NODE_LIT_INT:
        case Nk.NODE_LIT_FLOAT:
        case Nk.NODE_LIT_BOOL:
        case Nk.NODE_LIT_CHAR:
        case Nk.NODE_LIT_STRING:
        case Nk.NODE_LIT_RAW_BYTES:
        case Nk.NODE_LIT_NULL:
        case Nk.NODE_LIT_BOTTOM:
            break;

        case Nk.NODE_EXPR_FIELD:
            // base.field — resolve the base; the field name is a member, looked
            // up against the base's type later (in the type checker), not here.
            if (n.child_count >= 1) self.resolve_node(n.children[0]);

        case Nk.NODE_TYPE_PATH:
        case Nk.NODE_MODULE_PATH:
            // mod::Type / a::b::Type — resolve ONLY the head segment (the module
            // or root name). Trailing segments name members of that module and
            // are looked up later; resolving them as plain names here would
            // wrongly report "undefined name" (mirrors how value `mod::fn`
            // paths, built as Field nodes, resolve only their base).
            if (n.child_count >= 1) self.resolve_node(n.children[0]);
            // Resolve any generic type arguments on the LAST segment if present
            // (e.g. geom::Point<i32> — the <i32> must still resolve).
            for (usz i = 1; i < n.child_count; i++)
            {
                Node* seg = n.children[i];
                if (seg != null && seg.kind == Nk.NODE_TYPE_GENERIC_APP)
                {
                    for (usz j = 1; j < seg.child_count; j++) self.resolve_node(seg.children[j]);
                }
            }

        case Nk.NODE_EXPR_STRUCT_LIT:
            // Name { field: value, ... } — resolve the type name (child 0) and
            // each field *value*; field *names* are members, not value uses.
            if (n.child_count >= 1) self.resolve_node(n.children[0]);
            for (usz i = 1; i < n.child_count; i++)
            {
                Node* fi = n.children[i];
                if (fi == null) continue;
                if (fi.kind == Nk.NODE_FIELD_INIT && fi.child_count >= 2)
                {
                    self.resolve_node(fi.children[1]);   // the value only
                }
                else if (fi.kind != Nk.NODE_FIELD_INIT)
                {
                    self.resolve_node(fi);
                }
            }

        case Nk.NODE_EXPR_METHOD_CALL:
            // [base, methodName, args...] — resolve base + args, skip the name.
            if (n.child_count >= 1) self.resolve_node(n.children[0]);
            for (usz i = 2; i < n.child_count; i++) self.resolve_node(n.children[i]);

        case Nk.NODE_DECL_FN:
            self.resolve_fn(n);

        case Nk.NODE_DECL_LET:
        case Nk.NODE_DECL_MUT:
            self.resolve_let(n);

        case Nk.NODE_DECL_CONST:
        case Nk.NODE_DECL_STATIC:
            self.resolve_const_static(n);

        case Nk.NODE_DECL_TYPE:
            self.resolve_type_decl(n);

        case Nk.NODE_DECL_STRUCT:
        case Nk.NODE_DECL_UNION:
            self.resolve_struct_union(n);

        case Nk.NODE_DECL_ENUM:
            // Resolve only the payload TYPES in each variant (skip name idents)
            for (usz _vi = 1; _vi < n.child_count; _vi++)
            {
                Node* _ev = n.children[_vi];
                if (_ev == null || _ev.kind != Nk.NODE_ENUM_VARIANT) continue;
                for (usz _fi = 1; _fi < _ev.child_count; _fi++)
                {
                    Node* _f = _ev.children[_fi];
                    if (_f == null) continue;
                    if (_f.kind == Nk.NODE_FIELD_DECL && _f.child_count >= 2)
                    { self.resolve_node(_f.children[1]); }  // skip [0]=name, resolve [1]=type
                    else if (_f.kind != Nk.NODE_IDENT && _f.kind != Nk.NODE_TYPEVAR)
                    { self.resolve_node(_f); }
                }
            }

        case Nk.NODE_DECL_INTERFACE:
            // Register default method bodies for later injection into impls.
            for (usz ii = 1; ii < n.child_count; ii++)
            {
                Node* ch = n.children[ii];
                if (ch != null && ch.kind == Nk.NODE_DECL_FN)
                { self.bind_name_node(ch.children[0], NS_VALUE, ch, false); self.resolve_fn(ch); }
            }

        case Nk.NODE_DECL_IMPL:
            {
                // Resolve all fn children + inject default impls from interface
                Node* iface_node = null;
                // child[0] is the interface name — look up its decl
                if (n.child_count >= 1 && n.children[0] != null
                    && n.children[0].resolved != null
                    && n.children[0].resolved.kind == Nk.NODE_DECL_INTERFACE)
                { iface_node = n.children[0].resolved; }

                for (usz ii = 1; ii < n.child_count; ii++)
                {
                    Node* ch = n.children[ii];
                    if (ch != null && ch.kind == Nk.NODE_DECL_FN)
                    { self.bind_name_node(ch.children[0], NS_VALUE, ch, false); self.resolve_fn(ch); }
                }
                // Inject any missing default methods from the interface
                if (iface_node != null)
                {
                    for (usz di = 1; di < iface_node.child_count; di++)
                    {
                        Node* dflt = iface_node.children[di];
                        if (dflt == null || dflt.kind != Nk.NODE_DECL_FN) continue;
                        // Check if impl already has this method (by name)
                        if (dflt.child_count < 1 || dflt.children[0] == null) continue;
                        char* dn = dflt.children[0].p.ident.name_ptr;
                        usz   dl = dflt.children[0].p.ident.name_len;
                        bool  found_impl = false;
                        for (usz ii2 = 1; ii2 < n.child_count && !found_impl; ii2++)
                        {
                            Node* ch2 = n.children[ii2];
                            if (ch2 == null || ch2.kind != Nk.NODE_DECL_FN) continue;
                            if (ch2.child_count < 1 || ch2.children[0] == null) continue;
                            char* mn = ch2.children[0].p.ident.name_ptr;
                            usz   ml = ch2.children[0].p.ident.name_len;
                            if (ml == dl)
                            {
                                bool eq = true;
                                for (usz ci = 0; ci < ml; ci++)
                                { if (mn[ci] != dn[ci]) { eq = false; break; } }
                                if (eq) { found_impl = true; }
                            }
                        }
                        // If the default method has a body (has clauses), inject it
                        if (!found_impl && dflt.child_count >= 3)
                        {
                            // Register the default as available under the impl type name
                            self.bind_name_node(dflt.children[0], NS_VALUE, dflt, false);
                        }
                    }
                }
            }

        case Nk.NODE_DECL_EFFECT:
            self.resolve_effect_decl(n);

        case Nk.NODE_DECL_MOD:
            self.resolve_mod(n);

        case Nk.NODE_DECL_USE:
        case Nk.NODE_DECL_IMPORT:
            // Link the imported module path's head to its module declaration so
            // the type checker can resolve cross-module members (`m::sq`). The
            // alias name was already hoisted; here we resolve the path target.
            if (n.child_count >= 1)
            {
                Node* path = n.children[0];
                Node* headname = path;
                if (path != null && path.kind == Nk.NODE_MODULE_PATH && path.child_count >= 1)
                {
                    headname = path.children[0];
                }
                if (headname != null)
                {
                    char* hp;
                    usz hl;
                    if (name_of(headname, &hp, &hl))
                    {
                        Node* moddecl = self.lookup(hp, hl, NS_TYPE);
                        if (moddecl != null && moddecl.kind == Nk.NODE_DECL_MOD)
                        {
                            headname.resolved = moddecl;
                            // also stamp the Use node itself for direct access
                            n.type_annotation = moddecl;
                            // A 2-segment member import names ONE member of a
                            // known module: be loud when it isn't there — an
                            // unresolved member used to bind silently and any
                            // call became an indirect jump to null. (Heads
                            // that don't name a local mod — `use std::mem` —
                            // are not diagnosed here; extern namespaces stay
                            // permissive.)
                            if (path != null && path.kind == Nk.NODE_MODULE_PATH
                                && path.child_count == 2)
                            {
                                Node* memseg = path.children[1];
                                char* mp2; usz ml2;
                                if (memseg != null && name_of(memseg, &mp2, &ml2))
                                {
                                    Node* member = find_mod_member(moddecl, mp2, ml2);
                                    if (member == null)
                                    {
                                        self.error("module has no member with this name",
                                                   memseg.line, memseg.col);
                                    }
                                    else { memseg.resolved = member; }
                                }
                            }
                        }
                    }
                }
            }

        case Nk.NODE_EXPR_MATCH:
            self.resolve_match(n);

        case Nk.NODE_MATCH_ARM:
            self.resolve_match_arm(n);

        case Nk.NODE_CLAUSE:
            self.resolve_clause(n);

        case Nk.NODE_EXPR_FOR:
            self.resolve_for(n);

        case Nk.NODE_EXPR_BLOCK:
            self.resolve_block(n);

        case Nk.NODE_HANDLER_ARM:
            self.resolve_handler_arm(n);

        case Nk.NODE_EFFECT_HANDLE:
            // [computation, arms...] — each arm scopes its own binders.
            for (usz i = 0; i < n.child_count; i++) self.resolve_node(n.children[i]);

        case Nk.NODE_EFFECT_WITH:
            self.resolve_with(n);

        case Nk.NODE_EFFECT_ROW:
            self.resolve_effect_row(n);

        case Nk.NODE_PGEN:
            self.resolve_pgen(n);

        case Nk.NODE_REWRITE:
            // A rewrite block is a list of rules; each rule scopes its own
            // pattern metavariables.
            for (usz i = 0; i < n.child_count; i++) self.resolve_node(n.children[i]);

        case Nk.NODE_REWRITE_RULE:
            self.resolve_rewrite_rule(n);

        case Nk.NODE_ATTRIBUTE_LIST:
            // Attributes (`#extern("malloc")`, `#cc(c)`, `#inline`, …) are
            // metadata: their names and bareword args (extern, cc, c, vectorize)
            // are NOT value/type uses, so we must not resolve them as names.
            // Skip the whole list. (Numeric args like `#align(16)` are literals.)
            break;

        case Nk.NODE_DIALECT:
            self.resolve_dialect(n);

        case Nk.NODE_IRDL:
            // A list of lowering rules; each scopes its own binding metavars.
            for (usz i = 0; i < n.child_count; i++) self.resolve_node(n.children[i]);

        case Nk.NODE_LOWER:
            self.resolve_lower(n);

        case Nk.NODE_GRAPH:
        case Nk.NODE_NODE_DECL:
        case Nk.NODE_EDGE_DECL:
        case Nk.NODE_HYPEREDGE_DECL:
        case Nk.NODE_BLOCK_IR:
            self.resolve_graph_member(n);

        case Nk.NODE_ENUM_VARIANT:
            // Variant name (child 0) is a definition site — handled by hoist_decl.
            // Payload types are resolved when DECL_ENUM is handled above.
            // Do nothing here to prevent double-resolution or spurious errors.
            break;

        case Nk.NODE_STMT_BREAK_LABEL:
        case Nk.NODE_STMT_CONTINUE_LABEL:
            // Child ident is a loop label reference — not a value use.
            // Labels are tracked by the IR lowering pass, not the name resolver.
            break;

        case Nk.NODE_EXPR_LABELED:
            // 'label: <loop>  — child[0] is the label name (declaration site, not a use),
            // child[1] is the loop body that must be fully resolved.
            if (n.child_count >= 2 && n.children[1] != null)
            {
                self.resolve_node(n.children[1]);
            }

        case Nk.NODE_EXPR_OFFSETOF:
            // offset_of(Type, field_name)
            // child[0] = type (resolve as type), child[1] = field name (NOT a value use).
            if (n.child_count >= 1 && n.children[0] != null)
            {
                self.resolve_node(n.children[0]);   // resolve the type
            }
            // child[1] is the field name ident — skip it (it's a member ref, not a value)

        default:
            // Generic recursion for everything else (expressions, types,
            // statements, metaprogramming nodes, IRDL, etc.).
            for (usz i = 0; i < n.child_count; i++)
            {
                self.resolve_node(n.children[i]);
            }
            if (n.type_annotation != null) self.resolve_node(n.type_annotation);

        // fence(ordering): the ordering ident is not a value reference.
        case Nk.NODE_EXPR_FENCE:
            break;   // ordering string handled by lowering directly, not resolved

        // atomic_rmw(ptr, val): resolve both args but not any ordering literal.
        case Nk.NODE_EXPR_ATOMIC_RMW:
        case Nk.NODE_EXPR_ATOMIC_CMPXCHG:
            for (usz i = 0; i < n.child_count; i++)
                { self.resolve_node(n.children[i]); }
    }
}

// fn name <generics>? : sig (! row)? (where)? (attrs)? clauses
// Generics scope over the signature, where-clause, and body.
fn void Resolver.resolve_fn(Resolver* self, Node* fn_node)
{
    self.push_scope();

    // Bind generic type parameters first (visible in the signature).
    for (usz i = 0; i < fn_node.child_count; i++)
    {
        Node* c = fn_node.children[i];
        if (c != null && c.kind == Nk.NODE_GENERIC_PARAM)
        {
            self.bind_generics(c);
        }
    }

    // Resolve all children (signature types, effect row, where, attrs, clauses).
    // The function name (child 0) was already hoisted into the outer scope.
    for (usz i = 0; i < fn_node.child_count; i++)
    {
        Node* c = fn_node.children[i];
        if (c == null) continue;
        // Skip the function name node (IDENT) wherever it appears — might be
        // child 0 normally, or child 1+ if an attribute list was prepended.
        if (c.kind == Nk.NODE_IDENT || c.kind == Nk.NODE_INVALID) continue;
        // Skip attribute lists — they're declarative metadata, not value expressions.
        if (c.kind == Nk.NODE_ATTRIBUTE_LIST) continue;
        // Generic params were already bound + constraint-resolved softly above;
        // re-resolving here would (wrongly) treat the constraint as a plain name.
        if (c.kind == Nk.NODE_GENERIC_PARAM) continue;
        self.resolve_node(c);
    }

    self.pop_scope();
}

// Bind every type variable declared in a <...> generic list.
fn void Resolver.bind_generics(Resolver* self, Node* generics)
{
    for (usz i = 0; i < generics.child_count; i++)
    {
        Node* param = generics.children[i];
        if (param == null) continue;
        // A generic param is NODE_PARAM whose child 0 is the TYPEVAR name and
        // optional child 1 is a constraint type.
        if (param.child_count >= 1)
        {
            self.bind_name_node(param.children[0], NS_TYPE, param, false);
        }
        // Resolve the constraint (if present). A constraint names a CONCEPT
        // (e.g. `Num`, `Ord`, `Eq`) or a user-defined trait — not an ordinary
        // type. We resolve it SOFTLY: if it's a visible declaration, link it;
        // otherwise treat it as a built-in concept (no "undefined name" error,
        // per Pride's soft-typing design). Only the constraint's *head* name is
        // soft; any nested type arguments still resolve normally.
        if (param.child_count >= 2)
        {
            self.resolve_constraint(param.children[1]);
        }
    }
}

// Resolve a generic constraint softly: the head name is a concept/trait and is
// allowed to be a built-in (no error if absent); nested type arguments of a
// generic-app constraint still resolve normally.
fn void Resolver.resolve_constraint(Resolver* self, Node* c)
{
    if (c == null) return;
    switch (c.kind)
    {
        case Nk.NODE_TYPEVAR:
        case Nk.NODE_IDENT:
            // soft lookup: link if visible, else leave as a built-in concept
            char* ptr;
            usz len;
            if (name_of(c, &ptr, &len))
            {
                Node* decl = self.lookup(ptr, len, NS_TYPE);
                if (decl != null) c.resolved = decl;
            }
        case Nk.NODE_TYPE_GENERIC_APP:
            // head is the concept (soft); the rest are real type args
            if (c.child_count >= 1) self.resolve_constraint(c.children[0]);
            for (usz i = 1; i < c.child_count; i++) self.resolve_node(c.children[i]);
        default:
            self.resolve_node(c);
    }
}

// let (mut)? pattern (: type)? (! row)? (= init)
// The initializer is resolved BEFORE the pattern binds, so `let x = x` refers
// to an outer x. The binders then become visible to subsequent statements.
fn void Resolver.resolve_let(Resolver* self, Node* let_node)
{
    Node* pat = null;
    for (usz i = 0; i < let_node.child_count; i++)
    {
        Node* c = let_node.children[i];
        if (c == null) continue;
        if (i == 0)
        {
            pat = c;   // the pattern; resolve its type uses but bind later
            continue;
        }
        self.resolve_node(c);   // type, effect row, initializer
    }

    // Now bring the pattern's binders into scope for following statements.
    if (pat != null) { self.check_dup_binders(pat); self.bind_pattern(pat); }
}

fn void Resolver.resolve_const_static(Resolver* self, Node* d)
{
    // [name, (type)?, (value)?] — name already hoisted; resolve the rest.
    for (usz i = 1; i < d.child_count; i++)
    {
        self.resolve_node(d.children[i]);
    }
}

// type Name <generics>? = body
fn void Resolver.resolve_type_decl(Resolver* self, Node* d)
{
    self.push_scope();
    for (usz i = 0; i < d.child_count; i++)
    {
        Node* c = d.children[i];
        if (c == null) continue;
        if (i == 0) continue;   // the type name (already hoisted)
        if (c.kind == Nk.NODE_GENERIC_PARAM)
        {
            self.bind_generics(c);
            continue;
        }
        self.resolve_node(c);
    }
    self.pop_scope();
}

// struct/union: resolve field types; field names are members, not local names.
fn void Resolver.resolve_struct_union(Resolver* self, Node* d)
{
    // Generic parameters (`struct Stack<T>`) scope over the field types, so bind
    // them first inside a fresh scope.
    self.push_scope();
    for (usz i = 0; i < d.child_count; i++)
    {
        Node* c = d.children[i];
        if (c != null && c.kind == Nk.NODE_GENERIC_PARAM) self.bind_generics(c);
    }

    for (usz i = 0; i < d.child_count; i++)
    {
        Node* c = d.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_GENERIC_PARAM) continue;   // already bound above
        // The fields live in a NODE_EXPR_BLOCK; each field is FIELD_DECL[name,ty].
        if (c.kind == Nk.NODE_EXPR_BLOCK)
        {
            for (usz j = 0; j < c.child_count; j++)
            {
                Node* field = c.children[j];
                if (field != null && field.kind == Nk.NODE_FIELD_DECL && field.child_count >= 2)
                {
                    self.resolve_node(field.children[1]);   // field type
                }
            }
        }
        else
        {
            self.resolve_node(c);   // attributes, etc.
        }
    }
    self.pop_scope();
}

fn void Resolver.resolve_enum(Resolver* self, Node* d)
{
    // Resolve type names inside each variant's payload fields
    for (usz vi = 1; vi < d.child_count; vi++)
    {
        Node* evar = d.children[vi];
        if (evar == null || evar.kind != Nk.NODE_ENUM_VARIANT) continue;
        // Start at fi=1: child 0 is the variant name ident (definition, not use)
        for (usz fi = 1; fi < evar.child_count; fi++)
        {
            Node* field = evar.children[fi];
            if (field == null) continue;
            if (field.kind == Nk.NODE_FIELD_DECL)
            {
                // FIELD_DECL: child 0 = name (def, skip), child 1 = type (resolve)
                if (field.child_count >= 2 && field.children[1] != null)
                { self.resolve_node(field.children[1]); }
                else if (field.child_count >= 1 && field.children[0] != null
                         && field.children[0].kind != Nk.NODE_IDENT
                         && field.children[0].kind != Nk.NODE_TYPEVAR)
                { self.resolve_node(field.children[0]); }
            }
            else
            {
                // Direct type child (no FIELD_DECL wrapper)
                self.resolve_node(field);
            }
        }
    }
}



// pgen name<Generics>? -> [bindings] where [conds] ↦ action  (v.md §12).
// The binding list declares pattern metavariables (`[x : T]`) that, together
// with any generic params, scope over the where-conditions and the action. We
// bind them in a fresh scope so they resolve like ordinary names.
fn void Resolver.resolve_pgen(Resolver* self, Node* d)
{
    self.push_scope();

    // Generic params (`<T>`) first — visible in binding types, conds, action.
    for (usz i = 0; i < d.child_count; i++)
    {
        Node* c = d.children[i];
        if (c != null && c.kind == Nk.NODE_GENERIC_PARAM) self.bind_generics(c);
    }

    // Binding list: NODE_EXPR_ARRAY_LIT of NODE_PARAM[name, type] (or bare name).
    // Bind each metavariable name into the value namespace and resolve its type.
    for (usz i = 0; i < d.child_count; i++)
    {
        Node* c = d.children[i];
        if (c == null || c.kind != Nk.NODE_EXPR_ARRAY_LIT) continue;
        for (usz j = 0; j < c.child_count; j++)
        {
            Node* b = c.children[j];
            if (b == null) continue;
            if (b.kind == Nk.NODE_PARAM && b.child_count >= 1)
            {
                self.bind_name_node(b.children[0], NS_VALUE, b, false);
                if (b.child_count >= 2) self.resolve_node(b.children[1]);   // type
            }
            else if (b.kind == Nk.NODE_EXPR_RANGE && b.child_count >= 1)
            {
                // `..rest` spread binder: bind the rest name.
                self.bind_name_node(b.children[0], NS_VALUE, b, false);
            }
            else
            {
                self.bind_name_node(b, NS_VALUE, b, false);
            }
        }
    }

    // Now resolve the where-conditions and the action (last child / mapsto body),
    // which reference the bound metavariables.
    for (usz i = 0; i < d.child_count; i++)
    {
        Node* c = d.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_IDENT && i == 0) continue;        // pgen name (hoisted)
        if (c.kind == Nk.NODE_GENERIC_PARAM) continue;          // already bound
        if (c.kind == Nk.NODE_EXPR_ARRAY_LIT) continue;         // bindings handled
        self.resolve_node(c);                                    // where / action
    }

    self.pop_scope();
}

// A rewrite rule `| lhs (, guard)? ↦ rhs`: the LHS pattern introduces
// metavariables (any bare identifier appearing in it) that scope over the guard
// and the RHS. Bind those first, then resolve all three parts.
fn void Resolver.resolve_rewrite_rule(Resolver* self, Node* rule)
{
    self.push_scope();

    // Collect + bind every bare identifier in the LHS (child 0) as a metavar.
    if (rule.child_count >= 1) self.bind_rewrite_metavars(rule.children[0]);

    // Resolve LHS, guard, RHS against the bound metavars.
    for (usz i = 0; i < rule.child_count; i++)
    {
        self.resolve_node(rule.children[i]);
    }

    self.pop_scope();
}

// Walk a rewrite-rule LHS expression and bind each bare identifier as a pattern
// metavariable (idempotent: re-binding the same name is fine). Operators,
// literals, and call heads that are known functions are left alone.
fn void Resolver.bind_rewrite_metavars(Resolver* self, Node* e)
{
    if (e == null) return;
    if (e.kind == Nk.NODE_IDENT || e.kind == Nk.NODE_TYPEVAR)
    {
        char* ptr;
        usz len;
        if (name_of(e, &ptr, &len))
        {
            // Don't shadow a name that already resolves to a real top-level decl
            // (e.g. a function called in the pattern); only bind free metavars.
            if (self.lookup(ptr, len, NS_VALUE) == null)
            {
                self.bind(ptr, len, NS_VALUE, e, false);
            }
        }
        return;
    }
    for (usz i = 0; i < e.child_count; i++)
    {
        self.bind_rewrite_metavars(e.children[i]);
    }
}

// dialect Name <indented opcode/region/... members>  (v.md §19).
// The dialect name (child 0) was hoisted. Member declarations (opcode/region/
// block/node/edge/hyperedge/graph) introduce NAMES that are members of the
// dialect — they are NOT uses, so we must not resolve them as ordinary names.
// We bind each member name into the dialect's scope so qualified references
// (`Dialect.opcode`) and the IRDL lowering pass can find them, and recurse into
// nested region/graph bodies. Optional opcode signature types still resolve.
fn void Resolver.resolve_dialect(Resolver* self, Node* d)
{
    for (usz i = 0; i < d.child_count; i++)
    {
        Node* c = d.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_EXPR_BLOCK)
        {
            self.resolve_dialect_members(c);
        }
    }
}

// A standalone (top-level) graph-IR declaration: `graph cfg`, `node entry`,
// `edge from to`, `hyperedge a b c`, `block b`. The first name is a binder; for
// edge/hyperedge the remaining names are endpoint REFERENCES (resolved softly —
// graph IR is intentionally loose, so an unknown endpoint is not a hard error).
// Graph/block bodies recurse as their own member sets.
fn void Resolver.resolve_graph_member(Resolver* self, Node* n)
{
    // The declaration's own name (child 0) was hoisted at the top level.
    if (n.kind == Nk.NODE_EDGE_DECL || n.kind == Nk.NODE_HYPEREDGE_DECL)
    {
        // `edge from to` / `hyperedge a b c`: every name is an endpoint
        // REFERENCE (there is no separate edge name). Link if visible, but do
        // not error if absent (loose IR semantics).
        for (usz i = 0; i < n.child_count; i++)
        {
            Node* ep = n.children[i];
            if (ep == null) continue;
            char* p;
            usz l;
            if (name_of(ep, &p, &l))
            {
                Node* d = self.lookup(p, l, NS_VALUE);
                if (d != null) ep.resolved = d;
            }
        }
        return;
    }

    // graph/node/block: recurse into a nested body block of members.
    for (usz i = 1; i < n.child_count; i++)
    {
        Node* c = n.children[i];
        if (c != null && c.kind == Nk.NODE_EXPR_BLOCK) self.resolve_dialect_members(c);
    }
}

// Walk a dialect/region body: each member's NAME is a declaration (bound, not
// resolved); an optional opcode signature type resolves; region/graph bodies
// recurse.
fn void Resolver.resolve_dialect_members(Resolver* self, Node* block)
{
    // Pass 1: bind every member's own name first, so an edge can reference a
    // node declared later in the same body (forward references).
    for (usz j = 0; j < block.child_count; j++)
    {
        Node* m = block.children[j];
        if (m == null || m.child_count < 1) continue;
        switch (m.kind)
        {
            case Nk.NODE_OPCODE:
            case Nk.NODE_REGION:
            case Nk.NODE_BLOCK_IR:
            case Nk.NODE_NODE_DECL:
            case Nk.NODE_GRAPH:
                // edge/hyperedge excluded: they have no own name (all endpoints).
                self.bind_name_node(m.children[0], NS_VALUE, m, false);
            default:
                break;
        }
    }

    // Pass 2: resolve endpoints, signatures, and nested bodies.
    for (usz j = 0; j < block.child_count; j++)
    {
        Node* m = block.children[j];
        if (m == null) continue;
        switch (m.kind)
        {
            case Nk.NODE_EDGE_DECL:
            case Nk.NODE_HYPEREDGE_DECL:
                // every name is an endpoint reference — link softly (loose IR).
                for (usz k = 0; k < m.child_count; k++)
                {
                    Node* ep = m.children[k];
                    if (ep == null) continue;
                    char* p;
                    usz l;
                    if (name_of(ep, &p, &l))
                    {
                        Node* d = self.lookup(p, l, NS_VALUE);
                        if (d != null) ep.resolved = d;
                    }
                }
            case Nk.NODE_OPCODE:
            case Nk.NODE_REGION:
            case Nk.NODE_BLOCK_IR:
            case Nk.NODE_NODE_DECL:
            case Nk.NODE_GRAPH:
                // name bound in pass 1; resolve signature types / nested bodies.
                for (usz k = 1; k < m.child_count; k++)
                {
                    Node* c = m.children[k];
                    if (c == null) continue;
                    if (c.kind == Nk.NODE_EXPR_BLOCK)
                    {
                        self.resolve_dialect_members(c);   // nested region/graph body
                    }
                    else
                    {
                        self.resolve_node(c);              // opcode signature type
                    }
                }
            default:
                self.resolve_node(m);
        }
    }
}

// irdl lowering rule:  Dialect.opcode [a : T, b : T] ↦ action  (v.md §19).
// The binding group declares metavariables that scope over the action. The head
// path `Dialect.opcode` names a dialect (resolvable) and one of its opcodes
// (a member, looked up by the IRDL pass — resolve only the dialect head).
fn void Resolver.resolve_lower(Resolver* self, Node* rule)
{
    self.push_scope();

    // Bind the [name : Type] metavariables (NODE_EXPR_ARRAY_LIT of PARAMs).
    for (usz i = 0; i < rule.child_count; i++)
    {
        Node* c = rule.children[i];
        if (c == null || c.kind != Nk.NODE_EXPR_ARRAY_LIT) continue;
        for (usz j = 0; j < c.child_count; j++)
        {
            Node* b = c.children[j];
            if (b == null) continue;
            if (b.kind == Nk.NODE_PARAM && b.child_count >= 1)
            {
                self.bind_name_node(b.children[0], NS_VALUE, b, false);
                if (b.child_count >= 2) self.resolve_node(b.children[1]);   // type
            }
            else if (b.kind == Nk.NODE_EXPR_RANGE && b.child_count >= 1)
            {
                // `..rest` spread binder: bind the rest name.
                self.bind_name_node(b.children[0], NS_VALUE, b, false);
            }
            else
            {
                self.bind_name_node(b, NS_VALUE, b, false);
            }
        }
    }

    // Resolve head (dialect part only) and the action.
    for (usz i = 0; i < rule.child_count; i++)
    {
        Node* c = rule.children[i];
        if (c == null) continue;
        if (c.kind == Nk.NODE_EXPR_ARRAY_LIT) continue;   // bindings handled
        if (i == 0 && c.kind == Nk.NODE_EXPR_FIELD)
        {
            // head Dialect.opcode — link the dialect name SOFTLY (no "undefined
            // name" if absent: the IRDL pass reports a precise "unknown dialect"
            // diagnostic, so erroring here too would be a confusing double-report).
            if (c.child_count >= 1)
            {
                Node* dh = c.children[0];
                char* dp;
                usz dl;
                if (dh != null && name_of(dh, &dp, &dl))
                {
                    Node* dd = self.lookup(dp, dl, NS_TYPE);
                    if (dd == null) dd = self.lookup(dp, dl, NS_VALUE);
                    if (dd != null) dh.resolved = dd;
                }
            }
            continue;
        }
        self.resolve_node(c);   // the action
    }

    self.pop_scope();
}

// effect Name <generics>? <op decls>
fn void Resolver.resolve_effect_decl(Resolver* self, Node* d)
{
    self.push_scope();
    for (usz i = 0; i < d.child_count; i++)
    {
        Node* c = d.children[i];
        if (c == null) continue;
        if (i == 0) continue;   // effect name
        if (c.kind == Nk.NODE_GENERIC_PARAM)
        {
            self.bind_generics(c);
            continue;
        }
        // Operation decls block: each op is EFFECT_OP_DECL[name, type].
        if (c.kind == Nk.NODE_EXPR_BLOCK)
        {
            for (usz j = 0; j < c.child_count; j++)
            {
                Node* op = c.children[j];
                if (op != null && op.kind == Nk.NODE_EFFECT_OP_DECL)
                {
                    // Bind the op name in the value namespace (callable).
                    if (op.child_count >= 1) self.bind_name_node(op.children[0], NS_VALUE, op, false);
                    if (op.child_count >= 2) self.resolve_node(op.children[1]);
                }
            }
        }
    }
    self.pop_scope();
}

// mod Name <decls> — a nested scope that also hoists its members two-pass.
fn void Resolver.resolve_mod(Resolver* self, Node* m)
{
    self.push_scope();
    for (usz i = 0; i < m.child_count; i++)
    {
        Node* c = m.children[i];
        if (c != null && c.kind == Nk.NODE_EXPR_BLOCK)
        {
            for (usz j = 0; j < c.child_count; j++) self.hoist_decl(c.children[j]);
            for (usz j = 0; j < c.child_count; j++) self.resolve_node(c.children[j]);
        }
    }
    self.pop_scope();
}

// A block introduces a scope; lets become visible to following statements.
fn void Resolver.resolve_block(Resolver* self, Node* block)
{
    self.push_scope();

    // Hoist nested fn/type declarations so they can be mutually recursive.
    for (usz i = 0; i < block.child_count; i++)
    {
        Node* c = block.children[i];
        if (c != null && (c.kind == Nk.NODE_DECL_FN
            || c.kind == Nk.NODE_DECL_TYPE
            || c.kind == Nk.NODE_DECL_STRUCT
            || c.kind == Nk.NODE_DECL_UNION
            || c.kind == Nk.NODE_DECL_EFFECT))
        {
            self.hoist_decl(c);
        }
    }

    for (usz i = 0; i < block.child_count; i++)
    {
        self.resolve_node(block.children[i]);
    }

    self.pop_scope();
}

// match scrutinee sigma arms... phi
fn void Resolver.resolve_match(Resolver* self, Node* m)
{
    for (usz i = 0; i < m.child_count; i++)
    {
        self.resolve_node(m.children[i]);
    }
}

// arm: pattern (guard)? body — the pattern binders scope over guard + body.
fn void Resolver.resolve_match_arm(Resolver* self, Node* arm)
{
    self.push_scope();
    if (arm.child_count >= 1) { self.check_dup_binders(arm.children[0]); self.bind_pattern(arm.children[0]); }
    for (usz i = 1; i < arm.child_count; i++)
    {
        self.resolve_node(arm.children[i]);
    }
    self.pop_scope();
}

// clause: pattern (guard)? body — binders scope over guard + body.
fn void Resolver.resolve_clause(Resolver* self, Node* clause)
{
    self.push_scope();

    // The first child is the parameter pattern (when present). A clause with a
    // lone body (anonymous `-> body`) has just the body.
    usz start = 0;
    if (clause.child_count >= 1)
    {
        Node* first = clause.children[0];
        if (first != null && is_pattern(first))
        {
            self.check_dup_binders(first);
            self.bind_pattern(first);
            start = 1;
        }
    }

    for (usz i = start; i < clause.child_count; i++)
    {
        self.resolve_node(clause.children[i]);
    }

    self.pop_scope();
}

// for binder in iter body — binder scopes over the body (not the iterable).
fn void Resolver.resolve_for(Resolver* self, Node* f)
{
    // [binder, iter, body]
    if (f.child_count >= 2) self.resolve_node(f.children[1]);   // iterable first

    self.push_scope();
    if (f.child_count >= 1) { self.check_dup_binders(f.children[0]); self.bind_pattern(f.children[0]); }   // loop binder
    if (f.child_count >= 3) self.resolve_node(f.children[2]);   // body
    self.pop_scope();
}

// handler arm: op-head binder* body — binders (args + continuation) scope body.
// An effect row  ! [Eff1, Eff2, ..r]. User effect names resolve against the
// TYPE namespace; the builtin names (IO/Alloc/Unsafe/UB/Panic) are always
// valid; the `..r` open tail names a row variable and is not a use.
fn void Resolver.resolve_effect_row(Resolver* self, Node* row)
{
    for (usz i = 0; i < row.child_count; i++)
    {
        Node* ref = row.children[i];
        if (ref == null) continue;
        if (ref.kind == Nk.NODE_EFFECT_OPEN) continue;   // ..r row variable
        if (ref.kind != Nk.NODE_EFFECT_REF) continue;

        Node* name = ref.child_count >= 1 ? ref.children[0] : null;
        if (name == null) continue;

        // Try to link the effect name to a user `effect` declaration (so a row
        // `! [IO]` and a call `IO.op` agree on the same decl). If it doesn't
        // resolve, it's a builtin (IO/Alloc/Unsafe/UB/Panic) — never an error.
        char* p = name.p.ident.name_ptr;
        usz len = name.p.ident.name_len;
        Node* decl = self.lookup(p, len, NS_TYPE);
        if (decl != null) name.resolved = decl;
    }
}

// with resource body  /  with r = resource ... body  (v.md §10).
// The resource expression is evaluated, and in the `r = resource` form the name
// `r` is bound for the duration of the body (RAII-style scoped binding).
fn void Resolver.resolve_with(Resolver* self, Node* n)
{
    self.push_scope();

    if (n.child_count >= 1)
    {
        Node* res = n.children[0];
        if (res != null && res.kind == Nk.NODE_EXPR_ASSIGN && res.child_count >= 2)
        {
            // `with r = resource` — resolve the resource (RHS) then bind r (LHS).
            self.resolve_node(res.children[1]);
            self.bind_name_node(res.children[0], NS_VALUE, res, false);
        }
        else
        {
            self.resolve_node(res);   // `with handler` — a plain expression
        }
    }

    // The governed body (and any further children) see the bound resource.
    for (usz i = 1; i < n.child_count; i++)
    {
        self.resolve_node(n.children[i]);
    }

    self.pop_scope();
}

fn void Resolver.resolve_handler_arm(Resolver* self, Node* arm)
{
    self.push_scope();

    // `resume` is the implicit continuation primitive available in every handler
    // arm body (algebraic effects, v.md §10): `resume(v)` resumes the suspended
    // computation with `v`. Bind it so it is not flagged as an undefined name.
    self.bind("resume", 6, NS_VALUE, arm, false);

    // child 0 is the operation head (Effect.op or a name) — resolve the effect.
    if (arm.child_count >= 1)
    {
        Node* head = arm.children[0];
        if (head != null && head.kind == Nk.NODE_EXPR_FIELD && head.child_count >= 1)
        {
            self.resolve_use_name(head.children[0], NS_TYPE);   // the effect
        }
    }

    // Middle children are binder patterns; the last is the body.
    if (arm.child_count >= 2)
    {
        usz last = arm.child_count - 1;
        for (usz i = 1; i < last; i++)
        {
            self.bind_pattern(arm.children[i]);
        }
        self.resolve_node(arm.children[last]);
    }

    self.pop_scope();
}

// Is this node a pattern kind?
fn bool is_pattern(Node* n)
{
    if (n == null) return false;
    switch (n.kind)
    {
        case Nk.NODE_PATTERN_WILDCARD:
        case Nk.NODE_PATTERN_LITERAL:
        case Nk.NODE_PATTERN_IDENT:
        case Nk.NODE_PATTERN_TUPLE:
        case Nk.NODE_PATTERN_STRUCT:
        case Nk.NODE_PATTERN_UNION:
        case Nk.NODE_PATTERN_OR:
            return true;
        default:
            return false;
    }
}
