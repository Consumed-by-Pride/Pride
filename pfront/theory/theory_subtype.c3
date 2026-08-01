// ============================================================================
// theory_subtype.c3 — set-theoretic semantic subtyping (part 26)
// ----------------------------------------------------------------------------
// `theory_modal` has a structural `subtype()` that handles unions and
// intersections by distributing over them. That is correct as far as it goes,
// but it cannot decide the cases that make set-theoretic types worth having:
//
//     (A ∪ B) ∩ C  <:  (A ∩ C) ∪ (B ∩ C)      distributivity
//     A ∩ ¬A       <:  ⊥                       contradiction
//     A            <:  A ∪ ¬A                  excluded middle
//     ¬(A ∪ B)     ≡   ¬A ∩ ¬B                 De Morgan
//
// Deciding those needs the SEMANTIC reading: a type denotes a SET of values,
// and `A <: B` means `⟦A⟧ ⊆ ⟦B⟧`, equivalently `⟦A ∩ ¬B⟧ = ∅`. So subtyping
// reduces to EMPTINESS, and emptiness is decided on a normal form.
//
// The normal form used here is DISJUNCTIVE NORMAL FORM over atoms:
//
//     τ  ≡  ⋁ᵢ ( ⋀ⱼ aᵢⱼ  ∧  ⋀ₖ ¬bᵢₖ )
//
// A DNF clause is empty when it contains an atom and its negation, or two
// atoms that cannot coexist (`i64 ∩ bool` is empty because no value is both).
// The whole type is empty when every clause is.
//
// This is the Castagna–Frisch algorithm in miniature. The full version handles
// arrow types by a subtle decomposition; this implementation is complete for
// atoms, products, and negation, and is CONSERVATIVE for arrows — it answers
// "not a subtype" when it cannot prove otherwise, which is the safe direction:
// a false negative rejects a valid program with a clear message, a false
// positive accepts an invalid one and miscompiles it.
// ============================================================================

module theory_subtype;

import pfront_lex;
import pfront_core;
import theory_term;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz ST_MAX_ATOMS    = 64;
const usz ST_MAX_CLAUSES  = 128;
const usz ST_MAX_CACHE    = 8192;
const int ST_MAX_DEPTH    = 64;

// ── Atoms ───────────────────────────────────────────────────────────────────
// An atom is an indivisible type: a primitive, a named nominal type, or a
// structural former whose components are themselves types.
enum AtomKind : int
{
    AT_PRIM,        // i64, bool, f64 ...
    AT_NAMED,       // struct / enum / newtype
    AT_PTR,
    AT_SLICE,
    AT_ARRAY,
    AT_TUPLE,
    AT_ARROW,
    AT_UNIT,
    AT_TOP,         // any value
    AT_BOTTOM       // no value
}

struct Atom
{
    AtomKind kind;
    uint     name_id;
    Node*    decl;
    Node*    node;
    bool     negated;
}

fn bool atom_eq(Atom* a, Atom* b)
{
    if (a.kind != b.kind) { return false; }
    if (a.kind == AtomKind.AT_PRIM || a.kind == AtomKind.AT_NAMED)
    {
        if (a.decl != null && b.decl != null) { return a.decl == b.decl; }
        return a.name_id == b.name_id;
    }
    return theory_term::term_eq(a.node, b.node, 0);
}

// Two atoms are DISJOINT when no value inhabits both. This is what makes
// `i64 ∩ bool` provably empty rather than merely unusual.
fn bool atoms_disjoint(Atom* a, Atom* b)
{
    if (a.kind == AtomKind.AT_BOTTOM || b.kind == AtomKind.AT_BOTTOM) { return true; }
    if (a.kind == AtomKind.AT_TOP || b.kind == AtomKind.AT_TOP) { return false; }

    // Different structural formers never overlap: a pointer is not a tuple.
    if (a.kind != b.kind) { return true; }

    // Same former, different identity: two distinct nominal types are
    // disjoint because Pride has nominal (not structural) named types.
    if (a.kind == AtomKind.AT_NAMED)
    {
        if (a.decl != null && b.decl != null) { return a.decl != b.decl; }
        return a.name_id != b.name_id;
    }
    if (a.kind == AtomKind.AT_PRIM) { return a.name_id != b.name_id; }
    return false;
}

// ── DNF clauses ─────────────────────────────────────────────────────────────
// One clause is a conjunction of possibly-negated atoms.
struct Clause
{
    Atom[ST_MAX_ATOMS] atoms;
    usz                count;
    bool               known_empty;
}

fn void Clause.init(Clause* c)
{
    c.count = 0;
    c.known_empty = false;
}

fn bool Clause.add(Clause* c, Atom a)
{
    if (c.count >= ST_MAX_ATOMS) { return false; }
    // A clause containing both A and ¬A is empty: no value is in a set and
    // its complement.
    for (usz i = 0; i < c.count; i++)
    {
        if (atom_eq(&c.atoms[i], &a) && c.atoms[i].negated != a.negated)
        {
            c.known_empty = true;
        }
        // Two disjoint positive atoms also make the clause empty.
        if (!c.atoms[i].negated && !a.negated && atoms_disjoint(&c.atoms[i], &a))
        {
            c.known_empty = true;
        }
        // Duplicate: idempotent, skip.
        if (atom_eq(&c.atoms[i], &a) && c.atoms[i].negated == a.negated)
        {
            return true;
        }
    }
    c.atoms[c.count] = a;
    c.count = c.count + 1;
    return true;
}

fn bool Clause.is_empty(Clause* c)
{
    if (c.known_empty) { return true; }
    // A clause with a positive BOTTOM is empty; one with only negations of
    // TOP is empty too.
    for (usz i = 0; i < c.count; i++)
    {
        Atom* a = &c.atoms[i];
        if (!a.negated && a.kind == AtomKind.AT_BOTTOM) { return true; }
        if (a.negated && a.kind == AtomKind.AT_TOP) { return true; }
    }
    return false;
}

// ── DNF ─────────────────────────────────────────────────────────────────────
struct Dnf
{
    Clause[ST_MAX_CLAUSES] clauses;
    usz                    count;
    bool                   overflowed;
}

fn void Dnf.init(Dnf* d)
{
    d.count = 0;
    d.overflowed = false;
}

fn bool Dnf.add_clause(Dnf* d, Clause* c)
{
    // An empty clause contributes nothing to a union.
    if (c.is_empty()) { return true; }
    if (d.count >= ST_MAX_CLAUSES) { d.overflowed = true; return false; }
    d.clauses[d.count] = *c;
    d.count = d.count + 1;
    return true;
}

// The whole type is empty exactly when every clause is.
fn bool Dnf.is_empty(Dnf* d)
{
    if (d.overflowed) { return false; }   // cannot prove: assume inhabited
    for (usz i = 0; i < d.count; i++)
    {
        if (!d.clauses[i].is_empty()) { return false; }
    }
    return true;
}

// ── Conversion to DNF ───────────────────────────────────────────────────────
struct DnfBuilder
{
    Arena*                arena;
    pfront_core::DiagBag* diags;
    char*                 file;

    usz conversions;
    usz distributions;
    usz demorgan_steps;
    usz overflows;
    int max_depth;
}

fn void DnfBuilder.init(DnfBuilder* b, Arena* a, pfront_core::DiagBag* d, char* file)
{
    b.arena = a;
    b.diags = d;
    b.file = file;
    b.conversions = 0;
    b.distributions = 0;
    b.demorgan_steps = 0;
    b.overflows = 0;
    b.max_depth = 0;
}

fn Atom make_atom(Node* t, bool negated)
{
    Atom a;
    a.name_id = t == null ? 0 : t.name_id;
    a.decl = t == null ? null : t.resolved;
    a.node = t;
    a.negated = negated;
    a.kind = AtomKind.AT_NAMED;
    if (t == null) { a.kind = AtomKind.AT_TOP; return a; }
    switch (t.kind)
    {
        case N_TY_UNIT:   a.kind = AtomKind.AT_UNIT;
        case N_TY_BOTTOM: a.kind = AtomKind.AT_BOTTOM;
        case N_TY_PTR:
        case N_TY_REF:    a.kind = AtomKind.AT_PTR;
        case N_TY_SLICE:  a.kind = AtomKind.AT_SLICE;
        case N_TY_ARRAY:  a.kind = AtomKind.AT_ARRAY;
        case N_TY_TUPLE:  a.kind = AtomKind.AT_TUPLE;
        case N_TY_FN:     a.kind = AtomKind.AT_ARROW;
        case N_TY_INFER:  a.kind = AtomKind.AT_TOP;
        case N_TY_NAME:
        {
            // A primitive is recognised by spelling; anything else is nominal.
            char* s = t.p.sptr;
            usz n = t.p.slen;
            bool prim = false;
            if (s != null && n >= 2)
            {
                if ((s[0] == 'i' || s[0] == 'u' || s[0] == 'f')
                    && s[1] >= '0' && s[1] <= '9') { prim = true; }
                if (n == 4 && s[0] == 'b' && s[1] == 'o') { prim = true; }
                if (n == 4 && s[0] == 'c' && s[1] == 'h') { prim = true; }
                if (n == 3 && s[0] == 's' && s[1] == 't') { prim = true; }
            }
            a.kind = prim ? AtomKind.AT_PRIM : AtomKind.AT_NAMED;
        }
        default:
            a.kind = AtomKind.AT_NAMED;
    }
    return a;
}

// Convert a type to DNF. `negate` implements De Morgan lazily: pushing a
// negation inward swaps union and intersection.
fn void DnfBuilder.to_dnf(DnfBuilder* b, Node* t, bool negate, Dnf* out, int depth)
{
    if (depth > ST_MAX_DEPTH) { out.overflowed = true; return; }
    if (depth > b.max_depth) { b.max_depth = depth; }
    b.conversions = b.conversions + 1;

    if (t == null)
    {
        Clause c;
        c.init();
        c.add(make_atom(null, negate));
        out.add_clause(&c);
        return;
    }

    switch (t.kind)
    {
        case N_TY_NEGATION:
        {
            // ¬¬A ≡ A; otherwise push the negation inward.
            b.demorgan_steps = b.demorgan_steps + 1;
            b.to_dnf(t.child(0), !negate, out, depth + 1);
            return;
        }

        case N_TY_UNION:
        {
            if (!negate)
            {
                // A ∪ B in DNF: the clauses of A followed by those of B.
                for (usz i = 0; i < t.child_count; i++)
                {
                    b.to_dnf(t.children[i], false, out, depth + 1);
                }
                return;
            }
            // ¬(A ∪ B) ≡ ¬A ∩ ¬B — a conjunction, so DISTRIBUTE.
            b.demorgan_steps = b.demorgan_steps + 1;
            b.conjoin_children(t, true, out, depth);
            return;
        }

        case N_TY_INTERSECT:
        {
            if (!negate)
            {
                b.conjoin_children(t, false, out, depth);
                return;
            }
            // ¬(A ∩ B) ≡ ¬A ∪ ¬B — a disjunction.
            b.demorgan_steps = b.demorgan_steps + 1;
            for (usz i = 0; i < t.child_count; i++)
            {
                b.to_dnf(t.children[i], true, out, depth + 1);
            }
            return;
        }

        default:
        {
            Clause c;
            c.init();
            c.add(make_atom(t, negate));
            out.add_clause(&c);
            return;
        }
    }
}

// Conjoin the children of an intersection: the DNF of a conjunction is the
// cross product of the operands' clause sets. This is where the combinatorial
// blow-up lives, hence the clause cap.
fn void DnfBuilder.conjoin_children(DnfBuilder* b, Node* t, bool negate_each,
                                    Dnf* out, int depth)
{
    Dnf* acc = (Dnf*)malloc(Dnf::size);
    if (acc == null) { out.overflowed = true; return; }
    acc.init();

    // Seed with the first operand.
    if (t.child_count == 0) { free((void*)acc); return; }
    b.to_dnf(t.children[0], negate_each, acc, depth + 1);

    Dnf* tmp = (Dnf*)malloc(Dnf::size);
    if (tmp == null) { free((void*)acc); out.overflowed = true; return; }

    for (usz i = 1; i < t.child_count; i++)
    {
        Dnf* rhs = (Dnf*)malloc(Dnf::size);
        if (rhs == null) { break; }
        rhs.init();
        b.to_dnf(t.children[i], negate_each, rhs, depth + 1);

        tmp.init();
        // Cross product: every clause of acc with every clause of rhs.
        for (usz x = 0; x < acc.count; x++)
        {
            for (usz y = 0; y < rhs.count; y++)
            {
                Clause merged = acc.clauses[x];
                for (usz k = 0; k < rhs.clauses[y].count; k++)
                {
                    merged.add(rhs.clauses[y].atoms[k]);
                }
                if (!merged.is_empty()) { tmp.add_clause(&merged); }
                b.distributions = b.distributions + 1;
            }
        }
        *acc = *tmp;
        free((void*)rhs);
        if (acc.overflowed) { b.overflows = b.overflows + 1; break; }
    }

    for (usz i = 0; i < acc.count; i++) { out.add_clause(&acc.clauses[i]); }
    if (acc.overflowed) { out.overflowed = true; }
    free((void*)tmp);
    free((void*)acc);
}

// ── Semantic subtyping ──────────────────────────────────────────────────────
// A <: B  ⟺  ⟦A ∩ ¬B⟧ = ∅. Reducing subtyping to emptiness is what makes the
// distributive laws fall out automatically instead of being special-cased.
struct CacheEntry
{
    Node* a;
    Node* b;
    bool  result;
}

struct SemanticSubtyper
{
    DnfBuilder builder;
    CacheEntry[ST_MAX_CACHE] cache;
    usz                      cache_count;

    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    Arena*                 arena;
    char*                  file;

    usz queries;
    usz cache_hits;
    usz emptiness_checks;
    usz proved_empty;
    usz arrow_conservative;   // arrow cases answered conservatively
}

fn void SemanticSubtyper.init(SemanticSubtyper* s, Arena* a,
                              pfront_core::DiagBag* d,
                              pfront_core::Interner* it, char* file)
{
    s.builder.init(a, d, file);
    s.cache_count = 0;
    s.diags = d;
    s.interner = it;
    s.arena = a;
    s.file = file;
    s.queries = 0;
    s.cache_hits = 0;
    s.emptiness_checks = 0;
    s.proved_empty = 0;
    s.arrow_conservative = 0;
}

fn bool SemanticSubtyper.cache_get(SemanticSubtyper* s, Node* a, Node* b, bool* out)
{
    for (usz i = 0; i < s.cache_count; i++)
    {
        if (s.cache[i].a == a && s.cache[i].b == b)
        {
            *out = s.cache[i].result;
            s.cache_hits = s.cache_hits + 1;
            return true;
        }
    }
    return false;
}

fn void SemanticSubtyper.cache_put(SemanticSubtyper* s, Node* a, Node* b, bool r)
{
    if (s.cache_count >= ST_MAX_CACHE) { return; }
    s.cache[s.cache_count].a = a;
    s.cache[s.cache_count].b = b;
    s.cache[s.cache_count].result = r;
    s.cache_count = s.cache_count + 1;
}

// Is `t` uninhabited?
fn bool SemanticSubtyper.is_empty(SemanticSubtyper* s, Node* t)
{
    s.emptiness_checks = s.emptiness_checks + 1;
    Dnf* d = (Dnf*)malloc(Dnf::size);
    if (d == null) { return false; }
    d.init();
    s.builder.to_dnf(t, false, d, 0);
    bool empty = d.is_empty();
    if (empty) { s.proved_empty = s.proved_empty + 1; }
    free((void*)d);
    return empty;
}

// The main entry point.
fn bool SemanticSubtyper.subtype(SemanticSubtyper* s, Node* a, Node* b)
{
    if (a == null || b == null) { return false; }
    if (a == b) { return true; }
    s.queries = s.queries + 1;

    bool cached = false;
    if (s.cache_get(a, b, &cached)) { return cached; }

    // Build A ∩ ¬B as a DNF directly: the clauses of A, each conjoined with
    // every clause of ¬B.
    Dnf* da = (Dnf*)malloc(Dnf::size);
    Dnf* db = (Dnf*)malloc(Dnf::size);
    if (da == null || db == null)
    {
        if (da != null) { free((void*)da); }
        if (db != null) { free((void*)db); }
        return false;
    }
    da.init();
    db.init();
    s.builder.to_dnf(a, false, da, 0);
    s.builder.to_dnf(b, true, db, 0);     // ¬B

    bool all_empty = true;
    for (usz i = 0; i < da.count && all_empty; i++)
    {
        for (usz j = 0; j < db.count && all_empty; j++)
        {
            Clause merged = da.clauses[i];
            for (usz k = 0; k < db.clauses[j].count; k++)
            {
                merged.add(db.clauses[j].atoms[k]);
            }
            if (!merged.is_empty()) { all_empty = false; }
        }
    }

    // Overflow means "could not decide"; answer conservatively.
    if (da.overflowed || db.overflowed) { all_empty = false; }

    free((void*)da);
    free((void*)db);
    s.cache_put(a, b, all_empty);
    return all_empty;
}

// Structural refinement for the cases DNF alone cannot see through: an arrow
// is contravariant in its argument, a tuple is covariant componentwise.
fn bool SemanticSubtyper.subtype_structural(SemanticSubtyper* s, Node* a, Node* b,
                                            int depth)
{
    if (a == null || b == null || depth > ST_MAX_DEPTH) { return false; }
    if (s.subtype(a, b)) { return true; }
    if (a.kind != b.kind) { return false; }

    switch (a.kind)
    {
        case N_TY_TUPLE:
        {
            if (a.child_count != b.child_count) { return false; }
            for (usz i = 0; i < a.child_count; i++)
            {
                if (!s.subtype_structural(a.children[i], b.children[i], depth + 1))
                {
                    return false;
                }
            }
            return true;
        }
        case N_TY_SLICE:
            return s.subtype_structural(a.child(0), b.child(0), depth + 1);
        case N_TY_FN:
        {
            // Contravariant in the parameter, covariant in the result. The
            // full set-theoretic decomposition of arrow subtyping is more
            // involved; this covers the common case and answers
            // conservatively otherwise.
            s.arrow_conservative = s.arrow_conservative + 1;
            if (a.child_count == 0 || b.child_count == 0) { return false; }
            if (!s.subtype_structural(b.children[0], a.children[0], depth + 1))
            {
                return false;
            }
            Node* ar = a.children[a.child_count - 1];
            Node* br = b.children[b.child_count - 1];
            return s.subtype_structural(ar, br, depth + 1);
        }
        default:
            return false;
    }
}

// Type equivalence: mutual subtyping. `A ∪ B` and `B ∪ A` are equivalent
// despite being syntactically different, which a term comparison cannot see.
fn bool SemanticSubtyper.equivalent(SemanticSubtyper* s, Node* a, Node* b)
{
    return s.subtype(a, b) && s.subtype(b, a);
}

// Is the intersection of these two types inhabited? Used to decide whether a
// match arm is reachable given the scrutinee's type.
fn bool SemanticSubtyper.overlaps(SemanticSubtyper* s, Node* a, Node* b)
{
    Dnf* da = (Dnf*)malloc(Dnf::size);
    Dnf* db = (Dnf*)malloc(Dnf::size);
    if (da == null || db == null)
    {
        if (da != null) { free((void*)da); }
        if (db != null) { free((void*)db); }
        return true;
    }
    da.init();
    db.init();
    s.builder.to_dnf(a, false, da, 0);
    s.builder.to_dnf(b, false, db, 0);

    bool found = false;
    for (usz i = 0; i < da.count && !found; i++)
    {
        for (usz j = 0; j < db.count && !found; j++)
        {
            Clause merged = da.clauses[i];
            for (usz k = 0; k < db.clauses[j].count; k++)
            {
                merged.add(db.clauses[j].atoms[k]);
            }
            if (!merged.is_empty()) { found = true; }
        }
    }
    free((void*)da);
    free((void*)db);
    return found;
}

// Simplify a type by dropping empty clauses and absorbing redundant ones.
// `(A ∩ ¬A) ∪ B` becomes `B`.
fn Node* SemanticSubtyper.simplify(SemanticSubtyper* s, Node* t)
{
    if (t == null) { return null; }
    if (t.kind != Nk.N_TY_UNION && t.kind != Nk.N_TY_INTERSECT) { return t; }

    Dnf* d = (Dnf*)malloc(Dnf::size);
    if (d == null) { return t; }
    d.init();
    s.builder.to_dnf(t, false, d, 0);

    if (d.is_empty())
    {
        free((void*)d);
        // Everything cancelled: the type is uninhabited.
        Node* bot = s.arena.node(Nk.N_TY_BOTTOM, t.line, t.col);
        return bot == null ? t : bot;
    }

    // A single surviving clause with a single atom simplifies to that atom.
    if (d.count == 1 && d.clauses[0].count == 1 && !d.clauses[0].atoms[0].negated)
    {
        Node* only = d.clauses[0].atoms[0].node;
        free((void*)d);
        return only == null ? t : only;
    }
    free((void*)d);
    return t;
}

fn void SemanticSubtyper.report(SemanticSubtyper* s)
{
    printf("  semantic subtype : %d queries, %d cached, %d emptiness checks\n",
           (int)s.queries, (int)s.cache_hits, (int)s.emptiness_checks);
    printf("  dnf              : %d conversions, %d distributions, %d De Morgan\n",
           (int)s.builder.conversions, (int)s.builder.distributions,
           (int)s.builder.demorgan_steps);
    if (s.proved_empty > 0 || s.builder.overflows > 0)
    {
        printf("  type emptiness   : %d proved uninhabited, %d undecided (overflow)\n",
               (int)s.proved_empty, (int)s.builder.overflows);
    }
}

// ── Type-directed match refinement ──────────────────────────────────────────
// With semantic subtyping available, a match arm can be checked against the
// scrutinee's type: an arm whose pattern type does not overlap the scrutinee
// is dead regardless of clause order.
struct MatchRefiner
{
    SemanticSubtyper*      sub;
    pfront_core::DiagBag*  diags;
    char*                  file;
    usz arms_checked;
    usz impossible_arms;
    usz refinements;
    usz aliases_checked;
    usz empty_aliases;
}

fn void MatchRefiner.init(MatchRefiner* m, SemanticSubtyper* s,
                          pfront_core::DiagBag* d, char* file)
{
    m.sub = s;
    m.diags = d;
    m.file = file;
    m.arms_checked = 0;
    m.aliases_checked = 0;
    m.empty_aliases = 0;
    m.impossible_arms = 0;
    m.refinements = 0;
}

fn void MatchRefiner.check_match(MatchRefiner* m, Node* match_expr)
{
    if (match_expr == null || match_expr.child_count < 2) { return; }
    Node* scrut = match_expr.child(0);
    if (scrut == null) { return; }
    Node* scrut_ty = scrut.type_ann;
    if (scrut_ty == null && scrut.resolved != null)
    {
        scrut_ty = scrut.resolved.type_ann;
    }
    if (scrut_ty == null) { return; }

    for (usz i = 1; i < match_expr.child_count; i++)
    {
        Node* arm = match_expr.children[i];
        if (arm == null) { continue; }
        Node* pat = arm.child(0);
        if (pat == null || pat.type_ann == null) { continue; }
        m.arms_checked = m.arms_checked + 1;

        // An arm whose pattern type cannot overlap the scrutinee is dead.
        if (!m.sub.overlaps(scrut_ty, pat.type_ann))
        {
            m.impossible_arms = m.impossible_arms + 1;
            m.diags.warn(pfront_core::Phase.PH_RESOLVE, 4100, arm.line, arm.col,
                         "this arm's pattern type cannot match the scrutinee",
                         m.file);
        }
        else
        {
            m.refinements = m.refinements + 1;
        }
    }
}

fn void MatchRefiner.walk(MatchRefiner* m, Node* n, int depth)
{
    if (n == null || depth > 300) { return; }
    if (n.kind == Nk.N_EXPR_MATCH) { m.check_match(n); }
    // A DECLARED type alias built from the set algebra is worth analysing on
    // its own. `type Impossible = i32 ∩ bool` is uninhabited, and saying so
    // at the declaration is far more useful than waiting for a value to flow
    // into it. Previously the subtyper only ever saw match scrutinees, so a
    // file full of ∩ / ∪ / ¬ aliases produced "0 queries" and the whole DNF
    // engine sat idle.
    if (n.kind == Nk.N_DECL_TYPE && n.type_ann != null)
    {
        m.check_alias(n);
    }
    for (usz i = 0; i < n.child_count; i++) { m.walk(n.children[i], depth + 1); }
}

// Analyse one `type NAME = <set expression>` declaration.
fn void MatchRefiner.check_alias(MatchRefiner* m, Node* decl)
{
    Node* ty = decl.type_ann;
    if (ty == null || m.sub == null) { return; }

    // Only the set-theoretic forms are interesting; a plain alias to a
    // nominal type has nothing to decide.
    bool algebraic = has_set_operator(ty, 0);
    if (!algebraic) { return; }

    m.aliases_checked = m.aliases_checked + 1;

    // Uninhabited alias: no value can ever have this type. Reported as an
    // advisory because Pride is untyped -- writing it is legal, and it may
    // even be deliberate (a "never" marker).
    if (m.sub.is_empty(ty))
    {
        m.empty_aliases = m.empty_aliases + 1;
        m.diags.advisory_hint(pfront_core::Phase.PH_RESOLVE, 3291,
                              decl.line, decl.col,
                              "this type is uninhabited: no value can inhabit it",
                              "an intersection of disjoint sets reduces to the empty set",
                              m.file);
    }
}

// Does this type mention any of ∩ / ∪ / ¬ anywhere inside?
fn bool has_set_operator(Node* t, int depth)
{
    if (t == null || depth > 64) { return false; }
    if (t.kind == Nk.N_TY_UNION || t.kind == Nk.N_TY_INTERSECT
        || t.kind == Nk.N_TY_NEGATION)
    {
        return true;
    }
    for (usz i = 0; i < t.child_count; i++)
    {
        if (has_set_operator(t.children[i], depth + 1)) { return true; }
    }
    return false;
}

fn void MatchRefiner.report(MatchRefiner* m)
{
    if (m.aliases_checked > 0)
    {
        printf("  type algebra     : %d aliases analysed, %d uninhabited\n",
               (int)m.aliases_checked, (int)m.empty_aliases);
    }
    if (m.arms_checked == 0) { return; }
    printf("  match refinement : %d arms typed, %d impossible, %d refined\n",
           (int)m.arms_checked, (int)m.impossible_arms, (int)m.refinements);
}
