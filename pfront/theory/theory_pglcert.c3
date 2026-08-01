// ============================================================================
// theory_pglcert.c3 — PGL exhaustiveness and reachability certificates
// ----------------------------------------------------------------------------
// (part 25)
//
// `theory_irdl` compiles pattern clauses into a decision tree. This module
// answers the two questions a decision tree alone leaves open, and answers
// them with EVIDENCE rather than a boolean:
//
//   EXHAUSTIVENESS — does some value match no clause? If so, produce a
//                    concrete counter-example the programmer can read.
//   REACHABILITY   — can each clause ever fire? If not, name the earlier
//                    clauses that subsume it.
//
// A yes/no answer to either is nearly useless in practice. "This match is not
// exhaustive" sends the reader hunting; "this match does not handle
// `Some(None)`" does not. The certificate machinery therefore carries a
// WITNESS: an actual value description that demonstrates the gap.
//
// The witness search is a constructive reading of Maranget's usefulness
// algorithm. At each step:
//
//   * If the matrix has no rows, ANY value is a witness — emit wildcards.
//   * If the constructor set in the first column is INCOMPLETE, a witness uses
//     a missing constructor; recurse on the default matrix for the rest.
//   * If the set is COMPLETE, try each constructor in turn; a witness under
//     any of them lifts to a witness for the whole.
//
// The "complete signature" test is what makes this precise. For `bool` the
// signature is {true, false}; for an enum it is its variant list; for integers
// it is unbounded, so a listed set is never complete and a witness always
// exists outside it.
//
// Certificates are also emitted for the POSITIVE case. Knowing a match is
// provably exhaustive lets the backend omit the fallback branch entirely,
// which is a real code-size win, so the proof is worth recording.
// ============================================================================

module theory_pglcert;

import pfront_lex;
import pfront_core;
import theory_term;
import theory_irdl;

alias Tk    = pfront_lex::TokenType;
alias Node  = pfront_core::PNode;
alias Nk    = pfront_core::NodeKind;
alias Arena = pfront_core::Arena;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz PC_MAX_ROWS     = 128;
const usz PC_MAX_COLS     = 12;
const usz PC_MAX_CTORS    = 64;
const usz PC_WITNESS_CAP  = 512;
const usz PC_MAX_DEPTH    = 12;

// ── Witness values ──────────────────────────────────────────────────────────
// A witness is a partial VALUE, not a pattern: it describes something that
// would reach the match and fall through every clause.
enum WKind : int
{
    W_WILDCARD,     // any value works here
    W_CTOR,         // a named constructor with arguments
    W_INT,
    W_BOOL,
    W_TUPLE,
    W_RANGE_GAP     // an integer outside every listed case
}

struct Witness
{
    WKind kind;
    uint  ctor_name;
    long  ival;
    int[8] args;      // indices into the witness pool
    usz   arg_count;
}

struct WitnessPool
{
    Witness[PC_WITNESS_CAP] items;
    usz                     count;
}

fn void WitnessPool.init(WitnessPool* p) { p.count = 0; }

fn int WitnessPool.mk(WitnessPool* p, WKind k)
{
    if (p.count >= PC_WITNESS_CAP) { return -1; }
    int id = (int)p.count;
    p.count = p.count + 1;
    Witness* w = &p.items[id];
    w.kind = k;
    w.ctor_name = 0;
    w.ival = 0;
    w.arg_count = 0;
    return id;
}

fn int WitnessPool.wildcard(WitnessPool* p) { return p.mk(WKind.W_WILDCARD); }

fn int WitnessPool.ctor(WitnessPool* p, uint name)
{
    int id = p.mk(WKind.W_CTOR);
    if (id >= 0) { p.items[id].ctor_name = name; }
    return id;
}

fn int WitnessPool.int_val(WitnessPool* p, long v)
{
    int id = p.mk(WKind.W_INT);
    if (id >= 0) { p.items[id].ival = v; }
    return id;
}

fn int WitnessPool.bool_val(WitnessPool* p, bool v)
{
    int id = p.mk(WKind.W_BOOL);
    if (id >= 0) { p.items[id].ival = v ? 1 : 0; }
    return id;
}

fn bool WitnessPool.add_arg(WitnessPool* p, int parent, int child)
{
    if (parent < 0 || (usz)parent >= p.count) { return false; }
    Witness* w = &p.items[parent];
    if (w.arg_count >= 8) { return false; }
    w.args[w.arg_count] = child;
    w.arg_count = w.arg_count + 1;
    return true;
}

// Render a witness so the diagnostic can name the missing case.
fn void WitnessPool.render(WitnessPool* p, int id, pfront_core::Interner* it,
                           char* buf, usz cap, usz* pos, int depth)
{
    if (id < 0 || (usz)id >= p.count || *pos + 4 >= cap || depth > 8)
    {
        return;
    }
    Witness* w = &p.items[id];
    switch (w.kind)
    {
        case W_WILDCARD:
            pc_append(buf, cap, pos, "_");
        case W_BOOL:
            pc_append(buf, cap, pos, w.ival != 0 ? "true" : "false");
        case W_INT:
            pc_append_num(buf, cap, pos, w.ival);
        case W_RANGE_GAP:
        {
            pc_append_num(buf, cap, pos, w.ival);
            pc_append(buf, cap, pos, " (outside every listed case)");
        }
        case W_TUPLE:
        {
            pc_append(buf, cap, pos, "(");
            for (usz i = 0; i < w.arg_count; i++)
            {
                if (i > 0) { pc_append(buf, cap, pos, ", "); }
                p.render(w.args[i], it, buf, cap, pos, depth + 1);
            }
            pc_append(buf, cap, pos, ")");
        }
        case W_CTOR:
        {
            char* nm = it.text(w.ctor_name);
            if (nm != null) { pc_append(buf, cap, pos, nm); }
            else { pc_append(buf, cap, pos, "?"); }
            if (w.arg_count > 0)
            {
                pc_append(buf, cap, pos, "(");
                for (usz i = 0; i < w.arg_count; i++)
                {
                    if (i > 0) { pc_append(buf, cap, pos, ", "); }
                    p.render(w.args[i], it, buf, cap, pos, depth + 1);
                }
                pc_append(buf, cap, pos, ")");
            }
        }
    }
    buf[*pos] = 0;
}

fn void pc_append(char* buf, usz cap, usz* pos, char* s)
{
    usz i = 0;
    while (s[i] != 0 && *pos + 1 < cap) { buf[*pos] = s[i]; *pos = *pos + 1; i = i + 1; }
    buf[*pos] = 0;
}

fn void pc_append_num(char* buf, usz cap, usz* pos, long v)
{
    if (v < 0) { pc_append(buf, cap, pos, "-"); v = -v; }
    char[24] tmp;
    int n = 0;
    if (v == 0) { tmp[0] = '0'; n = 1; }
    while (v > 0 && n < 24) { tmp[n] = (char)('0' + (int)(v % 10)); v = v / 10; n = n + 1; }
    for (int i = n - 1; i >= 0 && *pos + 1 < cap; i--) { buf[*pos] = tmp[i]; *pos = *pos + 1; }
    buf[*pos] = 0;
}

// ── Constructor signatures ──────────────────────────────────────────────────
// A signature is COMPLETE when the listed constructors exhaust the type. That
// test is what distinguishes "you missed a case" from "there is always another
// integer".
enum SigKind : int
{
    SIG_ENUM,        // finite: the variant list
    SIG_BOOL,        // finite: {true, false}
    SIG_UNIT,        // finite: one value
    SIG_TUPLE,       // finite: one constructor
    SIG_INFINITE     // integers, strings: never complete
}

struct Signature
{
    SigKind kind;
    uint[PC_MAX_CTORS] ctors;
    usz[PC_MAX_CTORS]  arities;
    usz                ctor_count;
    Node*              decl;
}

fn void Signature.init(Signature* s, SigKind k)
{
    s.kind = k;
    s.ctor_count = 0;
    s.decl = null;
}

fn bool Signature.add(Signature* s, uint name, usz arity)
{
    if (s.ctor_count >= PC_MAX_CTORS) { return false; }
    s.ctors[s.ctor_count] = name;
    s.arities[s.ctor_count] = arity;
    s.ctor_count = s.ctor_count + 1;
    return true;
}

// Derive the signature of whatever a column scrutinises.
fn void signature_of(Node* enum_decl, Node* sample, Signature* out)
{
    if (enum_decl != null && enum_decl.kind == Nk.N_DECL_ENUM)
    {
        out.init(SigKind.SIG_ENUM);
        out.decl = enum_decl;
        for (usz i = 0; i < enum_decl.child_count; i++)
        {
            Node* v = enum_decl.children[i];
            if (v == null || v.kind != Nk.N_DECL_VARIANT) { continue; }
            usz arity = 0;
            for (usz k = 0; k < v.child_count; k++)
            {
                Node* p = v.children[k];
                if (p != null && pfront_core::is_type(p.kind)) { arity = arity + 1; }
            }
            out.add(v.name_id, arity);
        }
        return;
    }
    if (sample != null && sample.kind == Nk.N_PAT_LITERAL)
    {
        Node* lit = sample.child(0);
        if (lit != null && lit.kind == Nk.N_EXPR_BOOL)
        {
            out.init(SigKind.SIG_BOOL);
            out.add(0, 0);   // false
            out.add(1, 0);   // true
            return;
        }
    }
    if (sample != null && sample.kind == Nk.N_PAT_TUPLE)
    {
        out.init(SigKind.SIG_TUPLE);
        out.add(0, sample.child_count);
        return;
    }
    out.init(SigKind.SIG_INFINITE);
}

// ── Certificate matrix ──────────────────────────────────────────────────────
struct CertRow
{
    Node*[PC_MAX_COLS] cols;
    usz                width;
    int                clause_index;
    bool               live;
    bool               guarded;
}

struct CertMatrix
{
    CertRow[PC_MAX_ROWS] rows;
    usz                  row_count;
    usz                  width;
}

fn void CertMatrix.init(CertMatrix* m, usz w)
{
    m.row_count = 0;
    m.width = w < PC_MAX_COLS ? w : PC_MAX_COLS;
}

fn bool CertMatrix.add(CertMatrix* m, Node** cols, usz n, int clause, bool guarded)
{
    if (m.row_count >= PC_MAX_ROWS) { return false; }
    CertRow* r = &m.rows[m.row_count];
    r.width = n < PC_MAX_COLS ? n : PC_MAX_COLS;
    for (usz i = 0; i < r.width; i++) { r.cols[i] = cols[i]; }
    r.clause_index = clause;
    r.live = true;
    r.guarded = guarded;
    m.row_count = m.row_count + 1;
    return true;
}

fn bool pat_is_wild(Node* p)
{
    if (p == null) { return true; }
    if (p.kind == Nk.N_PAT_WILDCARD) { return true; }
    if (p.kind == Nk.N_PAT_IDENT) { return true; }
    if (p.kind == Nk.N_PAT_REST) { return true; }
    return false;
}

fn uint pat_ctor_name(Node* p)
{
    if (p == null) { return 0; }
    if (p.kind == Nk.N_PAT_VARIANT) { return p.name_id; }
    if (p.kind == Nk.N_PAT_LITERAL)
    {
        Node* lit = p.child(0);
        if (lit != null && lit.kind == Nk.N_EXPR_BOOL) { return lit.p.ival != 0 ? 1 : 0; }
    }
    return 0;
}

// Specialise for a constructor, as in Maranget's S(c, P).
fn void cert_specialise(CertMatrix* src, usz col, uint ctor, usz arity,
                        CertMatrix* dst)
{
    usz nw = arity + (src.width > 0 ? src.width - 1 : 0);
    dst.init(nw == 0 ? 1 : nw);
    for (usz r = 0; r < src.row_count; r++)
    {
        CertRow* row = &src.rows[r];
        if (!row.live) { continue; }
        Node* p = row.cols[col];
        bool wild = pat_is_wild(p);
        if (!wild && pat_ctor_name(p) != ctor) { continue; }

        Node*[PC_MAX_COLS] cols;
        usz w = 0;
        usz first = 0;
        if (!wild && p != null && p.kind == Nk.N_PAT_VARIANT) { first = 1; }
        for (usz k = 0; k < arity && w < PC_MAX_COLS; k++)
        {
            cols[w] = wild ? null : (p == null ? null : p.child(first + k));
            w = w + 1;
        }
        for (usz k = 0; k < row.width && w < PC_MAX_COLS; k++)
        {
            if (k == col) { continue; }
            cols[w] = row.cols[k];
            w = w + 1;
        }
        dst.add(&cols[0], w, row.clause_index, row.guarded);
    }
}

fn void cert_default(CertMatrix* src, usz col, CertMatrix* dst)
{
    dst.init(src.width > 0 ? src.width - 1 : 0);
    for (usz r = 0; r < src.row_count; r++)
    {
        CertRow* row = &src.rows[r];
        if (!row.live) { continue; }
        if (!pat_is_wild(row.cols[col])) { continue; }
        Node*[PC_MAX_COLS] cols;
        usz w = 0;
        for (usz k = 0; k < row.width && w < PC_MAX_COLS; k++)
        {
            if (k == col) { continue; }
            cols[w] = row.cols[k];
            w = w + 1;
        }
        dst.add(&cols[0], w, row.clause_index, row.guarded);
    }
}

// ── Certificate generator ───────────────────────────────────────────────────
struct Certificate
{
    bool exhaustive;
    int  witness;              // -1 when exhaustive
    usz  unreachable_count;
    int[PC_MAX_ROWS] unreachable;
    usz  depth_reached;
}

const usz CERT_POOL = 16;

struct CertMatrixPool
{
    CertMatrix[PC_MAX_DEPTH + 2] level;
}

CertMatrixPool g_cert_pool @private;

struct PglCertifier
{
    WitnessPool            witnesses;
    pfront_core::DiagBag*  diags;
    pfront_core::Interner* interner;
    char*                  file;

    usz matches_certified;
    usz proved_exhaustive;
    usz witnesses_found;
    usz unreachable_clauses;
    usz guarded_skipped;
    int max_depth;
    bool strict;
}

fn void PglCertifier.init(PglCertifier* pc, pfront_core::DiagBag* d,
                          pfront_core::Interner* it, char* file)
{
    pc.witnesses.init();
    pc.diags = d;
    pc.interner = it;
    pc.file = file;
    pc.matches_certified = 0;
    pc.proved_exhaustive = 0;
    pc.witnesses_found = 0;
    pc.unreachable_clauses = 0;
    pc.guarded_skipped = 0;
    pc.max_depth = 0;
    pc.strict = false;
}

// The constructive core: find a value matching no row, or prove none exists.
// Returns a witness index, or -1 when the matrix is exhaustive.
fn int PglCertifier.find_witness(PglCertifier* pc, CertMatrix* m,
                                 Node* enum_decl, int depth)
{
    if (depth > (int)PC_MAX_DEPTH) { return -1; }
    if (depth > pc.max_depth) { pc.max_depth = depth; }

    usz live = 0;
    usz first = 0;
    for (usz r = 0; r < m.row_count; r++)
    {
        if (m.rows[r].live) { if (live == 0) { first = r; } live = live + 1; }
    }

    // No rows: every value falls through, so a wildcard is a witness.
    if (live == 0)
    {
        int w = pc.witnesses.wildcard();
        for (usz i = 1; i < m.width; i++)
        {
            // A witness needs one component per column.
            pc.witnesses.add_arg(w, pc.witnesses.wildcard());
        }
        return w;
    }

    // No columns left and a live row exists: that row matches everything.
    if (m.width == 0) { return -1; }

    // Gather the constructors present in column 0.
    uint[PC_MAX_CTORS] present;
    usz[PC_MAX_CTORS]  arity;
    usz np = 0;
    Node* sample = null;
    for (usz r = 0; r < m.row_count; r++)
    {
        if (!m.rows[r].live) { continue; }
        Node* p = m.rows[r].cols[0];
        if (pat_is_wild(p)) { continue; }
        if (sample == null) { sample = p; }
        uint c = pat_ctor_name(p);
        bool dup = false;
        for (usz i = 0; i < np; i++) { if (present[i] == c) { dup = true; break; } }
        if (dup || np >= PC_MAX_CTORS) { continue; }
        present[np] = c;
        usz a = 0;
        if (p != null && p.kind == Nk.N_PAT_VARIANT && p.child_count > 0)
        {
            a = p.child_count - 1;
        }
        arity[np] = a;
        np = np + 1;
    }

    Signature sig;
    signature_of(enum_decl, sample, &sig);

    // No constructor at all in this column: the column is uninformative.
    if (np == 0)
    {
        CertMatrix* d = &g_cert_pool.level[depth];
        cert_default(m, 0, d);
        int sub = pc.find_witness(d, null, depth + 1);
        if (sub < 0) { return -1; }
        int w = pc.witnesses.wildcard();
        return w;
    }

    // INCOMPLETE signature: a missing constructor is itself the witness.
    bool complete = sig.kind != SigKind.SIG_INFINITE && np >= sig.ctor_count;
    if (!complete)
    {
        uint missing = 0;
        bool have_missing = false;
        if (sig.kind == SigKind.SIG_ENUM)
        {
            for (usz i = 0; i < sig.ctor_count; i++)
            {
                bool covered = false;
                for (usz k = 0; k < np; k++)
                {
                    if (present[k] == sig.ctors[i]) { covered = true; break; }
                }
                if (!covered) { missing = sig.ctors[i]; have_missing = true; break; }
            }
        }
        if (have_missing)
        {
            int w = pc.witnesses.ctor(missing);
            return w;
        }
        if (sig.kind == SigKind.SIG_BOOL && np < 2)
        {
            // One of true/false is unhandled.
            bool has_true = false;
            for (usz k = 0; k < np; k++) { if (present[k] == 1) { has_true = true; } }
            return pc.witnesses.bool_val(!has_true);
        }
        // Infinite signature: pick a value outside the listed set.
        int w = pc.witnesses.mk(WKind.W_RANGE_GAP);
        if (w >= 0)
        {
            long candidate = 0;
            bool taken = true;
            int guard = 0;
            while (taken && guard < 1024)
            {
                taken = false;
                for (usz r = 0; r < m.row_count; r++)
                {
                    if (!m.rows[r].live) { continue; }
                    Node* p = m.rows[r].cols[0];
                    if (p == null || p.kind != Nk.N_PAT_LITERAL) { continue; }
                    Node* lit = p.child(0);
                    if (lit != null && (long)lit.p.ival == candidate) { taken = true; break; }
                }
                if (taken) { candidate = candidate + 1; }
                guard = guard + 1;
            }
            pc.witnesses.items[w].ival = candidate;
        }
        return w;
    }

    // COMPLETE signature: a witness must exist under some constructor.
    for (usz i = 0; i < np; i++)
    {
        CertMatrix* s = &g_cert_pool.level[depth];
        cert_specialise(m, 0, present[i], arity[i], s);
        int sub = pc.find_witness(s, null, depth + 1);
        if (sub >= 0)
        {
            int w = pc.witnesses.ctor(present[i]);
            pc.witnesses.add_arg(w, sub);
            return w;
        }
    }
    return -1;
}

// A clause is UNREACHABLE when the matrix of its predecessors already covers
// everything it could match.
fn void PglCertifier.find_unreachable(PglCertifier* pc, CertMatrix* full,
                                      Node* enum_decl, Certificate* cert)
{
    cert.unreachable_count = 0;
    for (usz r = 0; r < full.row_count; r++)
    {
        if (!full.rows[r].live) { continue; }
        // A guarded clause can always fail its guard, so it is never
        // provably unreachable.
        if (full.rows[r].guarded) { pc.guarded_skipped = pc.guarded_skipped + 1; continue; }

        // Build the matrix of strictly earlier rows.
        CertMatrix* prior = &g_cert_pool.level[PC_MAX_DEPTH];
        prior.init(full.width);
        for (usz k = 0; k < r; k++)
        {
            if (!full.rows[k].live) { continue; }
            if (full.rows[k].guarded) { continue; }
            prior.add(&full.rows[k].cols[0], full.rows[k].width,
                      full.rows[k].clause_index, false);
        }
        if (prior.row_count == 0) { continue; }

        // Row r is reachable iff it is USEFUL with respect to the prior rows.
        // Approximated by asking whether the prior matrix already covers this
        // row's own constructor shape.
        CertMatrix* probe = &g_cert_pool.level[PC_MAX_DEPTH + 1];
        probe.init(full.width);
        probe.add(&full.rows[r].cols[0], full.rows[r].width,
                  full.rows[r].clause_index, false);

        if (pc.covered_by(prior, probe, enum_decl))
        {
            if (cert.unreachable_count < PC_MAX_ROWS)
            {
                cert.unreachable[cert.unreachable_count] = full.rows[r].clause_index;
                cert.unreachable_count = cert.unreachable_count + 1;
            }
            pc.unreachable_clauses = pc.unreachable_clauses + 1;
        }
    }
}

// Does `prior` already match everything `probe`'s single row matches?
fn bool PglCertifier.covered_by(PglCertifier* pc, CertMatrix* prior,
                                CertMatrix* probe, Node* enum_decl)
{
    if (probe.row_count == 0) { return false; }
    CertRow* target = &probe.rows[0];
    for (usz r = 0; r < prior.row_count; r++)
    {
        CertRow* p = &prior.rows[r];
        bool subsumes = true;
        for (usz c = 0; c < target.width && c < p.width; c++)
        {
            Node* pp = p.cols[c];
            Node* tp = target.cols[c];
            if (pat_is_wild(pp)) { continue; }   // wildcard covers anything
            if (pat_is_wild(tp)) { subsumes = false; break; }
            if (pat_ctor_name(pp) != pat_ctor_name(tp)) { subsumes = false; break; }
        }
        if (subsumes) { return true; }
    }
    return false;
}

// Certify one match expression.
fn Certificate PglCertifier.certify(PglCertifier* pc, Node* match_expr,
                                    Node* enum_decl)
{
    Certificate cert;
    cert.exhaustive = true;
    cert.witness = -1;
    cert.unreachable_count = 0;
    cert.depth_reached = 0;

    if (match_expr == null || match_expr.child_count < 2) { return cert; }
    pc.matches_certified = pc.matches_certified + 1;

    CertMatrix* m = &g_cert_pool.level[PC_MAX_DEPTH];
    m.init(1);
    for (usz i = 1; i < match_expr.child_count; i++)
    {
        Node* arm = match_expr.children[i];
        if (arm == null) { continue; }
        bool guarded = false;
        for (usz k = 1; k < arm.child_count; k++)
        {
            Node* c = arm.children[k];
            if (c != null && c.kind == Nk.N_GUARD) { guarded = true; }
        }
        Node*[PC_MAX_COLS] cols;
        cols[0] = arm.child(0);
        m.add(&cols[0], 1, (int)i, guarded);
    }

    // A guarded row cannot contribute to coverage, so exclude it from the
    // exhaustiveness matrix (but keep it for reachability).
    CertMatrix* cov = &g_cert_pool.level[0];
    cov.init(1);
    for (usz r = 0; r < m.row_count; r++)
    {
        if (m.rows[r].guarded) { continue; }
        cov.add(&m.rows[r].cols[0], m.rows[r].width, m.rows[r].clause_index, false);
    }

    int w = pc.find_witness(cov, enum_decl, 1);
    if (w >= 0)
    {
        cert.exhaustive = false;
        cert.witness = w;
        pc.witnesses_found = pc.witnesses_found + 1;
    }
    else
    {
        pc.proved_exhaustive = pc.proved_exhaustive + 1;
        // Record the proof so the backend can drop the fallback branch.
        match_expr.flags = match_expr.flags | pfront_core::NF_EXHAUSTIVE;
    }

    pc.find_unreachable(m, enum_decl, &cert);
    cert.depth_reached = (usz)pc.max_depth;
    return cert;
}

// Emit the certificate as diagnostics.
fn void PglCertifier.report_certificate(PglCertifier* pc, Node* at,
                                        Certificate* cert)
{
    if (!cert.exhaustive && cert.witness >= 0)
    {
        char[256] buf;
        usz pos = 0;
        buf[0] = 0;
        pc.witnesses.render(cert.witness, pc.interner, &buf[0], 256, &pos, 0);
        // A named counter-example is the whole point: "not exhaustive" alone
        // sends the reader hunting.
        pc.diags.add(pfront_core::Severity.SEV_WARNING,
                     pfront_core::Phase.PH_RESOLVE, 4090,
                     at == null ? 0 : at.line, at == null ? 0 : at.col,
                     "match is not exhaustive; this value is unhandled",
                     &buf[0], pc.file);
    }
    for (usz i = 0; i < cert.unreachable_count; i++)
    {
        pc.diags.warn(pfront_core::Phase.PH_RESOLVE, 4091,
                      at == null ? 0 : at.line, at == null ? 0 : at.col,
                      "this clause can never match: an earlier clause covers it",
                      pc.file);
    }
}

fn Node* enum_for_scrutinee(Node* scrut)
{
    if (scrut == null || scrut.resolved == null) { return null; }
    Node* d = scrut.resolved;
    if (d.kind == Nk.N_DECL_ENUM) { return d; }
    if (d.type_ann != null && d.type_ann.resolved != null
        && d.type_ann.resolved.kind == Nk.N_DECL_ENUM) { return d.type_ann.resolved; }
    // A clause binder gets its type from the enclosing signature.
    Node* cur = d;
    int hops = 0;
    while (cur != null && hops < 24)
    {
        if (cur.kind == Nk.N_DECL_FN && cur.type_ann != null)
        {
            Node* p0 = cur.type_ann.child(0);
            if (p0 != null && p0.resolved != null
                && p0.resolved.kind == Nk.N_DECL_ENUM) { return p0.resolved; }
            return null;
        }
        cur = cur.parent;
        hops = hops + 1;
    }
    return null;
}

fn void PglCertifier.walk(PglCertifier* pc, Node* n, int depth)
{
    if (n == null || depth > 300) { return; }
    if (n.kind == Nk.N_EXPR_MATCH)
    {
        Node* en = enum_for_scrutinee(n.child(0));
        Certificate cert = pc.certify(n, en);
        pc.report_certificate(n, &cert);
    }
    for (usz i = 0; i < n.child_count; i++) { pc.walk(n.children[i], depth + 1); }
}

fn void PglCertifier.report(PglCertifier* pc)
{
    printf("  pgl certificates : %d matches, %d proved exhaustive, %d witnesses\n",
           (int)pc.matches_certified, (int)pc.proved_exhaustive,
           (int)pc.witnesses_found);
    printf("  pgl reachability : %d unreachable clauses, %d guarded skipped\n",
           (int)pc.unreachable_clauses, (int)pc.guarded_skipped);
    if (pc.proved_exhaustive > 0)
    {
        printf("  backend benefit  : %d matches can omit their fallback branch\n",
               (int)pc.proved_exhaustive);
    }
}
