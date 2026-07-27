// lint.c3 — Pride lint pass (style / soundness warnings)
// Implementation language: C3 (host).
// Pipeline:  ... -> Resolver -> TypeChecker -> EffectChecker -> Lint (this)
// A light, post-resolution pass that surfaces *advisory* problems. Per v.md
// (line 429: "Non-exhaustive matches emit a soft warning ... Pride trusts
// you"), every lint is a WARNING by default; `--strict` promotes to an error.
// Lints implemented:
//   1. Non-exhaustive `match`  — no wildcard `_`, no catch-all bare binder,
//      and (for a small set) no obvious total coverage -> warn.
//   2. Non-exhaustive clause set on a `fn` — same idea over clause patterns.
//   3. Unreachable code after a diverging statement (return / unreachable /
//      trap / ub!) within a block.
//   4. Unreachable match arm / clause after a catch-all (`_` or bare binder).
//   5. Unused binding — a `let`/parameter binder that is never referenced
//      (skips names starting with `_`, the conventional "intentionally unused").
// This pass relies on `AstNode.resolved` (set by the resolver): every use
// points at its binder, so "unused" = a binder no use points to.

module lint;

import lexer;
import ast;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);

alias Node = ast::AstNode;
alias Nk = ast::NodeKind;

const usz MAX_BINDERS = 16384;

struct LintError
{
    char* msg;
    int   line;
    int   col;
    bool  is_error;
}

struct Linter
{
    bool strict;

    LintError[2048] diags;
    int diag_count;
    int error_count;
    int warning_count;

    // All binder declaration nodes we have seen (for unused detection).
    Node*[MAX_BINDERS] binders;
    usz binder_count;

    int walk_depth;   // recursion guard against pathologically deep trees
}

// Cap on lint recursion depth. The parser already bounds nesting (~150), but
// these walks run under ASan's larger stack frames; cap conservatively so a
// deeply-nested tree degrades gracefully instead of overflowing the stack.
const int LINT_MAX_DEPTH = 1200;

fn void Linter.init(Linter* self, bool strict)
{
    self.strict = strict;
    self.diag_count = 0;
    self.error_count = 0;
    self.warning_count = 0;
    self.binder_count = 0;
    self.walk_depth = 0;
}

fn void Linter.warn(Linter* self, char* msg, int line, int col)
{
    bool is_error = self.strict;
    if (is_error) { self.error_count++; }
    else { self.warning_count++; }

    if (self.diag_count < 2048)
    {
        LintError e;
        e.msg = msg;
        e.line = line;
        e.col = col;
        e.is_error = is_error;
        self.diags[self.diag_count] = e;
        self.diag_count++;
    }
}

fn bool name_starts_underscore(Node* nameNode)
{
    if (nameNode == null) return false;
    if (nameNode.kind != Nk.NODE_IDENT && nameNode.kind != Nk.NODE_TYPEVAR) return false;
    return nameNode.p.ident.name_len >= 1 && nameNode.p.ident.name_ptr[0] == '_';
}

fn void Linter.run(Linter* self, Node* program)
{
    if (program == null) return;

    // Pass A: structural lints (exhaustiveness, unreachable code).
    self.walk(program);

    // Pass B: unused-binding detection.
    //   1. collect every binder, 2. mark binders referenced by resolved uses,
    //   3. report binders that stayed unmarked.
    self.binder_count = 0;
    self.collect_binders(program);
    self.mark_used(program);
    self.report_unused();
}

fn void Linter.walk(Linter* self, Node* n)
{
    if (n == null) return;
    if (self.walk_depth > LINT_MAX_DEPTH) return;
    self.walk_depth++;
    self.walk_body(n);
    self.walk_depth--;
}

fn void Linter.walk_body(Linter* self, Node* n)
{
    switch (n.kind)
    {
        case Nk.NODE_EXPR_MATCH:
            self.lint_match(n);

        case Nk.NODE_DECL_FN:
            self.lint_fn_clauses(n);
            self.walk_children(n);

        case Nk.NODE_EXPR_BLOCK:
            self.lint_block(n);
            self.walk_children(n);

        // MSP / metaprogramming bodies are untyped and unrestricted by design;
        // we don't lint their internals (vision: "shoot yourself in the foot").
        case Nk.NODE_REWRITE:
        case Nk.NODE_REWRITE_RULE:
        case Nk.NODE_PGEN:
        case Nk.NODE_STAGE:
        case Nk.NODE_QUOTE:
        case Nk.NODE_SPLICE:
        case Nk.NODE_UNQUOTE:
        case Nk.NODE_REIFY:
        case Nk.NODE_EVAL:
        case Nk.NODE_COMPTIME:
        case Nk.NODE_RUNTIME:
        case Nk.NODE_FIXPOINT:
        case Nk.NODE_META:
        case Nk.NODE_GENERATE:
        case Nk.NODE_LOWER:
        case Nk.NODE_IRDL:
        case Nk.NODE_DIALECT:
            break;

        default:
            self.walk_children(n);
    }
}

fn void Linter.walk_children(Linter* self, Node* n)
{
    for (usz i = 0; i < n.child_count; i++)
    {
        self.walk(n.children[i]);
    }
}

// match scrutinee sigma arm* phi   — arms are NODE_MATCH_ARM.
fn void Linter.lint_match(Linter* self, Node* m)
{
    bool saw_catchall = false;
    bool reported_unreachable = false;
    // Track bool-literal coverage: a `match b | true ... | false ...` is total
    // over bool with no catch-all needed.
    bool saw_true = false;
    bool saw_false = false;

    for (usz i = 0; i < m.child_count; i++)
    {
        Node* arm = m.children[i];
        if (arm == null || arm.kind != Nk.NODE_MATCH_ARM) continue;

        // Walk the arm body for nested lints first.
        self.walk(arm);

        if (saw_catchall && !reported_unreachable)
        {
            self.warn("unreachable match arm (a previous arm matches everything)",
                arm.line, arm.col);
            reported_unreachable = true;
        }

        Node* pat = arm.child_count >= 1 ? arm.children[0] : null;
        // An UNGUARDED catch-all (wildcard or bare binder) covers everything.
        if (is_catchall_arm(arm, pat))
        {
            saw_catchall = true;
        }
        // Record unguarded bool-literal coverage.
        if (!arm_has_guard(arm))
        {
            pattern_bool_coverage(pat, &saw_true, &saw_false);
        }
    }

    if (saw_catchall) return;                 // total via catch-all
    if (saw_true && saw_false) return;        // total over bool {true, false}
    if ((m.flags & ast::FLAG_EXHAUSTIVE) != 0) return;  // total over union variants

    self.warn("non-exhaustive match: no catch-all arm (add `| _ -> ...`)",
        m.line, m.col);
}

// Does an arm carry a guard (NODE_PATTERN_GUARD child)?
fn bool arm_has_guard(Node* arm)
{
    for (usz i = 0; i < arm.child_count; i++)
    {
        if (arm.children[i] != null && arm.children[i].kind == Nk.NODE_PATTERN_GUARD) return true;
    }
    return false;
}

// Mark which of true/false a (possibly OR-) pattern of bool literals covers.
fn void pattern_bool_coverage(Node* pat, bool* saw_true, bool* saw_false)
{
    if (pat == null) return;
    if (pat.kind == Nk.NODE_PATTERN_OR)
    {
        for (usz i = 0; i < pat.child_count; i++)
        {
            pattern_bool_coverage(pat.children[i], saw_true, saw_false);
        }
        return;
    }
    if (pat.kind == Nk.NODE_PATTERN_LITERAL && pat.child_count >= 1)
    {
        Node* lit = pat.children[0];
        if (lit != null && lit.kind == Nk.NODE_LIT_BOOL)
        {
            if (lit.p.lit_bool.bool_val) { *saw_true = true; }
            else { *saw_false = true; }
        }
    }
}

// An arm is a catch-all when it has no guard and its pattern is a wildcard or a
// bare identifier binder (which matches any value).
fn bool is_catchall_arm(Node* arm, Node* pat)
{
    if (pat == null) return false;
    // A guard is present when a NODE_PATTERN_GUARD child exists.
    for (usz i = 0; i < arm.child_count; i++)
    {
        if (arm.children[i] != null && arm.children[i].kind == Nk.NODE_PATTERN_GUARD)
        {
            return false;   // guarded arms never count as total
        }
    }
    return is_irrefutable(pat);
}

// A pattern that matches every value of its type.
fn bool is_irrefutable(Node* pat)
{
    if (pat == null) return false;
    switch (pat.kind)
    {
        case Nk.NODE_PATTERN_WILDCARD:
            return true;
        case Nk.NODE_PATTERN_IDENT:
            return true;   // bare binder matches anything
        case Nk.NODE_PATTERN_TUPLE:
            // A tuple pattern is total iff every component is total. The empty
            // tuple `()` (unit) is vacuously total — the unit type has one value.
            for (usz i = 0; i < pat.child_count; i++)
            {
                if (!is_irrefutable(pat.children[i])) return false;
            }
            return true;
        case Nk.NODE_PATTERN_STRUCT:
            // A struct pattern matching a UNION variant is refutable (it only
            // matches that one variant); the type checker stamps FLAG_REFUTABLE
            // on those. A struct pattern over a product struct is total iff
            // every field subpattern is total (`{ x }` shorthand binds).
            if ((pat.flags & ast::FLAG_REFUTABLE) != 0) return false;
            for (usz i = 0; i < pat.child_count; i++)
            {
                Node* f = pat.children[i];
                if (f == null || f.kind != Nk.NODE_PATTERN_FIELD) return false;
                // `{ name }` shorthand (1 child) is a binder -> irrefutable.
                // `{ name : sub }` (2 children) is total iff `sub` is.
                if (f.child_count >= 2 && !is_irrefutable(f.children[1])) return false;
            }
            return true;
        default:
            return false;
    }
}

// A fn's clause list is the NODE_EXPR_BLOCK of NODE_CLAUSE children.
fn void Linter.lint_fn_clauses(Linter* self, Node* fn_node)
{
    Node* clauses = null;
    for (usz i = 0; i < fn_node.child_count; i++)
    {
        Node* c = fn_node.children[i];
        if (c != null && c.kind == Nk.NODE_EXPR_BLOCK)
        {
            // Confirm it actually holds clauses (not a struct field block, etc.)
            if (c.child_count >= 1 && c.children[0] != null
                && c.children[0].kind == Nk.NODE_CLAUSE)
            {
                clauses = c;
            }
        }
    }
    if (clauses == null) return;

    // A single anonymous-body clause (no pattern) is a total function body.
    if (clauses.child_count == 1)
    {
        Node* only = clauses.children[0];
        if (only != null && only.kind == Nk.NODE_CLAUSE && is_anonymous_clause(only))
        {
            return;
        }
    }

    bool saw_catchall = false;
    bool reported_unreachable = false;

    for (usz i = 0; i < clauses.child_count; i++)
    {
        Node* clause = clauses.children[i];
        if (clause == null || clause.kind != Nk.NODE_CLAUSE) continue;

        if (saw_catchall && !reported_unreachable)
        {
            self.warn("unreachable clause (a previous clause matches everything)",
                clause.line, clause.col);
            reported_unreachable = true;
        }

        if (is_catchall_clause(clause))
        {
            saw_catchall = true;
        }
    }

    // The type checker may have proven the clause set total over a union's
    // variants (it can see variants; this syntactic pass cannot).
    if ((clauses.flags & ast::FLAG_EXHAUSTIVE) != 0) return;

    if (!saw_catchall)
    {
        self.warn("non-exhaustive clauses: no catch-all (add `| _ -> ...`)",
            fn_node.line, fn_node.col);
    }
}

// A clause with no parameter pattern (anonymous `-> body`).
fn bool is_anonymous_clause(Node* clause)
{
    if (clause.child_count == 0) return true;
    Node* first = clause.children[0];
    return !is_pattern_kind(first);
}

// A catch-all clause: irrefutable pattern and no guard.
fn bool is_catchall_clause(Node* clause)
{
    if (clause.child_count == 0) return false;
    Node* first = clause.children[0];
    if (!is_pattern_kind(first)) return true;   // anonymous body = total

    for (usz i = 0; i < clause.child_count; i++)
    {
        if (clause.children[i] != null && clause.children[i].kind == Nk.NODE_PATTERN_GUARD)
        {
            return false;
        }
    }
    return is_irrefutable(first);
}

fn bool is_pattern_kind(Node* n)
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

// Within a block, anything following a statement that always diverges
// (return / unreachable / trap / a bare ub!) cannot run.
fn void Linter.lint_block(Linter* self, Node* block)
{
    bool diverged = false;

    for (usz i = 0; i < block.child_count; i++)
    {
        Node* stmt = block.children[i];
        if (stmt == null) continue;

        if (diverged)
        {
            self.warn("unreachable code (a previous statement always diverges)",
                stmt.line, stmt.col);
            // Only report the first dead statement per block to avoid spam.
            return;
        }

        if (is_diverging(stmt)) diverged = true;
    }
}

// Does this statement always transfer control away (never falls through)?
fn bool is_diverging(Node* n)
{
    if (n == null) return false;
    switch (n.kind)
    {
        case Nk.NODE_STMT_RETURN:
        case Nk.NODE_STMT_UNREACHABLE:
        case Nk.NODE_STMT_TRAP:
        case Nk.NODE_UB_BANG:
        case Nk.NODE_STMT_BREAK:
        case Nk.NODE_STMT_BREAK_LABEL:
        case Nk.NODE_STMT_CONTINUE:
        case Nk.NODE_STMT_CONTINUE_LABEL:
            return true;
        case Nk.NODE_STMT_EXPR:
            // an expression-statement wrapping a diverging expr (e.g. ub!)
            if (n.child_count >= 1) return is_diverging(n.children[0]);
            return false;
        default:
            return false;
    }
}

// Step 1: collect every binder node (PatIdent inside let/clause/for/match/etc.)
fn void Linter.collect_binders(Linter* self, Node* n)
{
    if (n == null) return;
    if (self.walk_depth > LINT_MAX_DEPTH) return;
    self.walk_depth++;
    self.collect_binders_body(n);
    self.walk_depth--;
}

fn void Linter.collect_binders_body(Linter* self, Node* n)
{
    if (n.kind == Nk.NODE_PATTERN_IDENT)
    {
        Node* nm = n.child_count >= 1 ? n.children[0] : null;
        // Skip `_`-prefixed names (conventionally intentionally unused).
        if (!name_starts_underscore(nm))
        {
            if (self.binder_count < MAX_BINDERS)
            {
                self.binders[self.binder_count] = n;
                self.binder_count++;
            }
        }
        return;
    }

    for (usz i = 0; i < n.child_count; i++)
    {
        self.collect_binders(n.children[i]);
    }
    if (n.type_annotation != null) self.collect_binders(n.type_annotation);
}

// Step 2: every resolved use marks its binder as used.
fn void Linter.mark_used(Linter* self, Node* n)
{
    if (n == null) return;
    if (self.walk_depth > LINT_MAX_DEPTH) return;
    self.walk_depth++;
    self.mark_used_body(n);
    self.walk_depth--;
}

fn void Linter.mark_used_body(Linter* self, Node* n)
{
    if ((n.kind == Nk.NODE_IDENT || n.kind == Nk.NODE_TYPEVAR) && n.resolved != null)
    {
        // Don't count the binder's own internal name node as a use of itself.
        n.resolved.flags |= ast::FLAG_USED;
    }

    for (usz i = 0; i < n.child_count; i++)
    {
        self.mark_used(n.children[i]);
    }
}

// Step 3: report binders that were never marked used.
fn void Linter.report_unused(Linter* self)
{
    for (usz i = 0; i < self.binder_count; i++)
    {
        Node* b = self.binders[i];
        if (b == null) continue;
        if ((b.flags & ast::FLAG_USED) != 0) continue;

        Node* nm = b.child_count >= 1 ? b.children[0] : null;
        int ln = nm != null ? nm.line : b.line;
        int cl = nm != null ? nm.col : b.col;
        self.warn("unused binding (prefix with `_` if intentional)", ln, cl);
    }
}
