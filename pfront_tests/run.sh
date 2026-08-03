#!/usr/bin/env bash
# pfront regression suite.
#
# Each case is a .pie file plus an EXPECT_<name> line giving the number of
# diagnostics the case should report in its OWN file. Cases that are supposed
# to produce errors (type cycles, non-exhaustive matches) assert the count,
# so a silent regression to "no diagnostics" fails the suite.
set -u
cd "$(dirname "$0")/.." || exit 1
BIN=./pfrontc
[ -x "$BIN" ] || { echo "build ./pfront first"; exit 2; }

declare -A EXPECT=(
  [01_match_inline]=0        # match arms on one line, `|` not bitwise-or
  [02_bitor_in_arm]=0        # `a | b` IS bitwise-or inside a clause body
  [03_continuation]=0        # trailing-operator line continuation
  [04_let_block_init]=0      # `let n =` + indented if/else block
  [05_then_brace]=0          # `then { ... } else { ... }`
  [06_if_then_multiline]=0   # `if c then` / `else` at hanging indent
  [07_crossmod]=0            # cross-module `use` resolution
  [08_typecycle]=2           # two mutually recursive by-value structs
  [09_nonexhaustive]=0       # warning only, not an error
  [10_consteval]=0           # BASE*4 folds across const references
  [11_const_divzero]=1       # div-by-zero in a const IS an error
  [12_utf8_cols]=2           # two unresolved names; checks UTF-8 caret alignment
  [13_typemismatch]=0        # permissive by default; see STRICT block below
  [14_arity]=0
  [15_array_cycle]=1         # struct holding [Self; N] IS infinite-sized
  [16_cast_trunc]=0          # `300 as u8` folds to 44, no diagnostic
  [17_recursion]=0           # mutual + self recursion, 3 dead functions
  [18_flow]=0                # nested loops, depth 2, no missing return
  [19_selfinit]=1            # `let x = x + 1` -> resolver reports unresolved
  [20_do_block]=0            # `while c do { ... break ... }` body must attach
  [21_nested_init_if]=0      # `let q = if/else` must not swallow the next `let`
  [22_visibility]=0          # only the pub symbol is referenced
  [23_kw_field_name]=0       # `JitMemory { region: ... }` -- `region` is a keyword
  [24_kw_module_type]=0      # `meta.Metadata` -- `meta` is a keyword
  [25_qualified_struct_lit]=0 # `thing.Thing { ... }` qualified struct literal
  [26_effects_perform]=0     # effect decl + `perform E.op()` parses and registers
  [27_ub_outside_unsafe]=1   # `ub!` outside `unsafe` IS an error
  [28_stage_escape]=1        # cross-stage variable escape IS an error
  [29_splice_stage0]=1       # splice with no enclosing quotation IS an error
  [30_gradual_sort]=0        # calling a non-function warns (permissive default)
  [31_trs_rule]=0            # rewrite block collects and fires
  [32_irdl_dialect]=0        # dialect + opcode registers
  [33_comptime_let]=0        # `let x = comptime 3*4` must evaluate, not swallow
  [34_exhaustive_witness]=0  # missing variant -> warning with a named witness
  [35_egraph_rewrite]=0      # e-graph builds classes and saturates
  [36_dup_field]=1           # two fields with the same name
  [37_dup_discriminant]=1    # two variants sharing an explicit discriminant
  [38_immutable_assign]=0    # UNTYPED: assigning to a non-mut `let` is ACCEPTED
  [39_ptr_field_write]=0     # `c.buf = v` through a pointer is LEGAL
  [40_interval_divzero]=0    # interval analysis proves the divisor is 0 (warning)
  [41_decided_branch]=0      # `x=5; if x > 100` proven always false (note)
  [42_opt_algebraic]=0       # x*1, x+0, x-x, x*0 -- all optimized away
  [43_opt_dce]=0             # code after `return` is deleted
  [44_opt_purity]=0          # impure initializer is NEVER deleted
  [45_opt_branch]=0          # `if false` and `while 0` collapse
  [46_liveness_loop]=0       # loop-carried vars are non-local (need phi)
  [47_liveness_local]=0      # straight-line vars are all block-local
  [48_opt_cascade]=0         # fold -> flatten -> unreachable, all in one run
  [49_kw_tail_binder]=0      # `tail` as a BINDER and as a tail-call annotation
  [50_qualified_call]=0      # `os.linux.malloc(n)` -- 3-segment module call
  [51_semi_fields]=0         # `a : u64; b : u64` semicolon fields + `fn K : T = v`
  [52_kw_handle_arg]=0       # `handle` as an ordinary argument name
  [53_resume_juxtapose]=0    # `resume v` juxtaposition (v.md 10.3), not just resume(v)
  [54_upper_binder]=0        # bare uppercase pattern: binder vs nullary variant
  [55_array_repeat]=0        # `[v; n]` array-repeat form, incl. inside struct literals
  [56_while_then]=0          # `while c then body` alongside `do` and `if..then`
  [57_mut_tuple_pat]=0       # `let (mut a, mut b) = ...` per-element mut
  [58_kw_stage_field]=0      # `stage` as field/value AND as a staging block
  [59_cast_bitor]=0          # `x as i64 | y` is bitwise-or, not a union type
  [60_wrapped_cond]=0        # wrapped condition + else, body shallower than continuation
  [61_nested_inline_else]=0  # nested `if ... else <inline>` + outer else ladder
  [62_polymorphism]=0        # generic inference: T inferred per call site
  [63_modsys]=0              # mod/use: nested paths, cross-module calls resolve
  [64_then_stmt_kw]=0        # `then break` / `then continue` / `-> return v`
  [65_op_continuation]=0     # trailing-operator continuation in assign/let/chain
  [66_inline_let_chain]=0    # `| s -> let n = ...; use(n)` semicolon chain
  [67_interface_self]=0      # `Self` in scope; inline single-method interface
  [68_brace_semi_close]=0    # `else ();` followed by `}` closes the block
  [69_alias_collision]=0     # alias `pkg` vs real module `pkg` in one graph
  [70_comment_in_braces]=0   # `--` comment on the first line inside {} or ()
  [71_elseif_init]=0          # `let x = if/else if/else` chain; next stmt must NOT nest
  [72_implicit_block_leak]=0 # stale implicit_block must not eat the initializer's DEDENT
  [73_soft_then_kw]=0        # soft keyword `then` vs. tail/handle/stage lookahead
  [74_hanging_indent_stack]=0 # lexer realign must not destroy enclosing levels
  [75_local_shadows_module]=0 # a local binding shadows a same-named module
  [76_numeric_suffix_hex]=0   # width/sign suffixes on hex literals
  [77_field_types]=0          # struct field types reach the IR
)

# ---------------------------------------------------------------------------
# SEMI-PRUNED LIVENESS
# The whole point of semi-pruned SSA is the SPLIT: variables that cross a
# control-flow edge need a phi, variables that do not are block-local. A pass
# that classified everything one way would still "run" but be worthless, so
# both directions are asserted against contrasting inputs.

# ---------------------------------------------------------------------------
# OPTIMIZER
# Each entry asserts a MINIMUM count for one optimizer statistic. A pass that
# silently stops firing is the failure mode these catch -- the node counts
# alone would not, because another pass could mask the regression.
#   field = the grep key, want = minimum value
declare -A OPT_FIELD=(
  [42_opt_algebraic]="algebraic"
  [43_opt_dce]="dead code"
  [45_opt_branch]="branches"
)
declare -A OPT_MIN=(
  [42_opt_algebraic]=4       # n*1, +0, b-b, n*0
  [43_opt_dce]=2             # 2 statements after `return`
  [45_opt_branch]=1          # `if 1 > 100` folds to the else arm
)

# Cases that must produce errors ONLY under --strict-types. Running them twice
# proves the permissive default stays quiet and the strict mode actually fires.
declare -A STRICT=(
  [14_arity]=0               # UNTYPED: arity is advice, never an error
)

# ---------------------------------------------------------------------------
# UNTYPED-LANGUAGE POLICY
# Pride assumes the developer knows what they are doing. A type mismatch, an
# arity difference or a write to a non-`mut` binding must NEVER fail a build.
# The analyses still run (their facts drive the optimizer) but they speak only
# under `--lint`, and then only as warnings.
#
# Each entry asserts BOTH halves: 0 errors ever, and >=N warnings with --lint.
declare -A ADVISORY=(
  [13_typemismatch]=1        # bool parameter given an i64 argument
  [14_arity]=1               # 2-parameter function called with 1 argument
  [38_immutable_assign]=1    # assigning to a binding not declared `mut`
)

pass=0; fail=0
for f in pfront_tests/*.pie; do
  name=$(basename "$f" .pie)
  want=${EXPECT[$name]:-0}
  got=$("$BIN" "$f" -I pfront_tests -I stdlib -I . 2>&1 | grep -c "$f:.*error")
  if [ "$got" = "$want" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s (%s errors)\n' "$name" "$got"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s expected %s, got %s\n' "$name" "$want" "$got"
  fi
done

for name in "${!STRICT[@]}"; do
  want=${STRICT[$name]}
  got=$("$BIN" "pfront_tests/$name.pie" --strict-types 2>&1 | grep -c "error\[")
  if [ "$got" = "$want" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s (strict: %s errors)\n' "$name" "$got"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s strict: expected %s, got %s\n' "$name" "$want" "$got"
  fi
done

# Untyped-language policy: never an error, advisory only under --lint.
for name in "${!ADVISORY[@]}"; do
  want=${ADVISORY[$name]}
  # half 1: zero errors even with every strict switch on
  errs=$("$BIN" "pfront_tests/$name.pie" --strict-types --strict-vis 2>&1 | grep -c "error\[")
  # half 2: --lint surfaces at least `want` warnings
  warns=$("$BIN" "pfront_tests/$name.pie" --lint 2>&1 | grep -c "warning\[")
  if [ "$errs" = "0" ] && [ "$warns" -ge "$want" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s (untyped: 0 err, %s advisory)\n' "$name" "$warns"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s untyped: want 0 err/>=%s warn, got %s/%s\n' "$name" "$want" "$errs" "$warns"
  fi
done

# Optimizer: assert each pass actually fires.
for name in "${!OPT_FIELD[@]}"; do
  field=${OPT_FIELD[$name]}
  want=${OPT_MIN[$name]}
  line=$("$BIN" "pfront_tests/$name.pie" 2>&1 | grep "  $field ")
  got=$(echo "$line" | grep -oE '[0-9]+' | head -1)
  got=${got:-0}
  if [ "$got" -ge "$want" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s (opt %s: %s>=%s)\n' "$name" "$field" "$got" "$want"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s opt %s: want >=%s, got %s\n' "$name" "$field" "$want" "$got"
  fi
done

# STRUCTURAL assertion for the `let x = <if/else if/else>` initializer bug.
#
# An error count alone is too weak: the failure mode was that the statement
# AFTER the initializer got REPARENTED INSIDE it, which is still 0 errors in
# any file where the swallowed name happens to resolve anyway. An s-expression
# substring is also too weak (verified: the buggy and fixed trees share the
# same tail). Assert the INDENT DEPTH instead -- in the clause block, the
# trailing `ident 'a'` must sit at exactly the same depth as `let 'a'`, i.e.
# be its SIBLING. With the bug present it is two levels deeper and UNRESOLVED.
d_let=$("$BIN" pfront_tests/71_elseif_init.pie --dump-ast --plain --quiet 2>&1 \
        | sed -n "/fn 'chain3'/,/fn 'chain4'/p" | grep "let 'a'" \
        | sed 's/[^ ].*//' | head -1 | wc -c)
d_use=$("$BIN" pfront_tests/71_elseif_init.pie --dump-ast --plain --quiet 2>&1 \
        | sed -n "/fn 'chain3'/,/fn 'chain4'/p" | grep "ident 'a'  ->" \
        | sed 's/[^ ].*//' | head -1 | wc -c)
unres=$("$BIN" pfront_tests/71_elseif_init.pie --dump-ast --plain --quiet 2>&1 \
        | sed -n "/fn 'chain3'/,/fn 'chain4'/p" | grep -c "UNRESOLVED")
if [ "${d_let:-0}" -gt 1 ] && [ "$d_let" = "$d_use" ] && [ "$unres" = "0" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (else-if init: use is a sibling, depth %s)\n' "elseif_init" "$d_let"
else
  fail=$((fail+1)); printf '  FAIL  %-26s else-if init: let depth=%s use depth=%s unresolved=%s\n' "elseif_init" "$d_let" "$d_use" "$unres"
fi

# Back-to-back initializers: `two_inits` must show TWO sibling `let`s at the
# same depth, not one nested inside the other's initializer.
tw=$("$BIN" pfront_tests/71_elseif_init.pie --dump-ast --plain --quiet 2>&1 \
     | sed -n "/fn 'two_inits'/,/fn 'multi_stmt'/p")
dd=$(echo "$tw" | grep "let 'd'" | sed 's/[^ ].*//' | head -1 | wc -c)
de=$(echo "$tw" | grep "let 'e'" | sed 's/[^ ].*//' | head -1 | wc -c)
tw_unres=$(echo "$tw" | grep -c "UNRESOLVED")
if [ "${dd:-0}" -gt 1 ] && [ "$dd" = "$de" ] && [ "$tw_unres" = "0" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (else-if init: 2 sibling initializers at depth %s)\n' "elseif_init2" "$dd"
else
  fail=$((fail+1)); printf '  FAIL  %-26s else-if init: d=%s e=%s unresolved=%s\n' "elseif_init2" "$dd" "$de" "$tw_unres"
fi

# STRUCTURAL assertion for the stale-`implicit_block` leak (wyhash.pie).
#
# Same reparenting failure class as 71: the statement after the initializer
# was pulled INSIDE it, so assert depths rather than error counts. In `wy`
# the trailing `a + b + s` and the `let s` must both be siblings of the
# tuple `let`, and nothing in the function may be UNRESOLVED.
wy=$("$BIN" pfront_tests/72_implicit_block_leak.pie --dump-ast --plain --quiet 2>&1 \
     | sed -n "/fn 'wy'/,/fn 'wy2'/p")
d_tup=$(echo "$wy" | grep -n "pat-tuple" | head -1 | cut -d: -f1)
dl_let=$(echo "$wy" | grep "let  (" | sed 's/[^ ].*//' | head -1 | wc -c)
dl_s=$(echo "$wy" | grep "let 's'" | sed 's/[^ ].*//' | head -1 | wc -c)
wy_unres=$(echo "$wy" | grep -c "UNRESOLVED")
if [ "${dl_let:-0}" -gt 1 ] && [ "$dl_let" = "$dl_s" ] && [ "$wy_unres" = "0" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (implicit_block: siblings at depth %s)\n' "implicit_leak" "$dl_let"
else
  fail=$((fail+1)); printf '  FAIL  %-26s implicit_block: tuple-let=%s let-s=%s unresolved=%s\n' "implicit_leak" "$dl_let" "$dl_s" "$wy_unres"
fi

# All three shapes in the file (continuation in branch 1, branch 2, and with
# no tuple pattern) must resolve every name.
leak_unres=$("$BIN" pfront_tests/72_implicit_block_leak.pie --dump-ast --plain --quiet 2>&1 | grep -c "UNRESOLVED")
if [ "$leak_unres" = "0" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (implicit_block: 0 unresolved across 3 shapes)\n' "implicit_leak2"
else
  fail=$((fail+1)); printf '  FAIL  %-26s implicit_block: %s unresolved\n' "implicit_leak2" "$leak_unres"
fi

# Soft keyword `then` (spec 25) must not be mistaken for the start of a
# tail-call annotation, a handler head, or a staging block -- AND the real
# `tail f(x)` annotation must survive. Assert BOTH halves: zero unresolved
# names anywhere in the file, and the `call tail` flag still on tail_call.
then_unres=$("$BIN" pfront_tests/73_soft_then_kw.pie --dump-ast --plain --quiet 2>&1 | grep -c "UNRESOLVED")
then_tail=$("$BIN" pfront_tests/73_soft_then_kw.pie --emit-ast --quiet 2>&1 \
            | sed -n "/fn 'tail_call'/,/fn 'handle_then'/p" | grep -c "call tail")
if [ "$then_unres" = "0" ] && [ "$then_tail" = "1" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (soft `then`: 0 unresolved, tail annotation kept)\n' "soft_then"
else
  fail=$((fail+1)); printf '  FAIL  %-26s soft then: unresolved=%s tail-annot=%s (want 0/1)\n' "soft_then" "$then_unres" "$then_tail"
fi

# LEXER: the hanging-indent realign must not destroy an enclosing block
# level. When it did, the closing DEDENT was never emitted and the NEXT
# top-level function was silently parsed INSIDE the previous one -- with
# zero diagnostics, which is why an error count cannot catch this. Count
# top-level declarations instead.
hi_fns=$("$BIN" pfront_tests/74_hanging_indent_stack.pie --dump-ast --plain --quiet 2>&1 | grep -cE "^  fn ")
if [ "$hi_fns" = "6" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (hanging indent: all 6 fns top-level)\n' "indent_stack"
else
  fail=$((fail+1)); printf '  FAIL  %-26s hanging indent: %s top-level fns, want 6\n' "indent_stack" "$hi_fns"
fi

# The same shape in the real stdlib file that exposed it: convert_fast.pie
# must export all four of its functions.
cf_fns=$("$BIN" stdlib/fmt/parse_float/convert_fast.pie -I stdlib --dump-ast --plain --quiet 2>&1 | grep -cE "^  fn ")
if [ "$cf_fns" = "4" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (convert_fast: 4 fns visible)\n' "indent_stack2"
else
  fail=$((fail+1)); printf '  FAIL  %-26s convert_fast: %s fns, want 4\n' "indent_stack2" "$cf_fns"
fi

# A local value binding must shadow a module of the same name, AND the
# module-alias path must keep working. This only reproduces when the graph
# actually loads the colliding module, so resolve against -I stdlib and
# assert on field accesses reaching their binder.
sh=$("$BIN" pfront_tests/75_local_shadows_module.pie -I stdlib --dump-ast --plain --quiet 2>&1)
sh_unres=$(echo "$sh" | grep -c "UNRESOLVED")
sh_bound=$(echo "$sh" | grep -c "ident 'target'  -> pat-ident 'target'")
if [ "$sh_unres" = "0" ] && [ "$sh_bound" -ge 2 ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (local shadows module: %s bound, 0 unresolved)\n' "shadow_module" "$sh_bound"
else
  fail=$((fail+1)); printf '  FAIL  %-26s shadow: unresolved=%s target-bound=%s (want 0/>=2)\n' "shadow_module" "$sh_unres" "$sh_bound"
fi

# WHOLE-GRAPH check: every stdlib module loaded into ONE compilation unit.
# This is the configuration that exposed both the alias/module collision and
# the local/module collision -- each file was clean alone and broke only here.
cat > /tmp/pfront_megaload.pie <<'MEGA'
mod megaload
MEGA
find stdlib -name '*.pie' | sort | while read -r m; do
  head -1 "$m" | sed -n 's/^mod /use /p'
done >> /tmp/pfront_megaload.pie
printf '\nfn main : i64 -> i64\n  | x -> x\n' >> /tmp/pfront_megaload.pie
mega=$("$BIN" /tmp/pfront_megaload.pie -I stdlib --plain --quiet 2>&1)
mega_err=$(echo "$mega" | grep -oE 'errors=[0-9]+' | cut -d= -f2)
mega_mod=$(echo "$mega" | grep -oE 'modules=[0-9]+' | cut -d= -f2)
if [ "${mega_err:-99}" = "0" ] && [ "${mega_mod:-0}" -ge 250 ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (megaload: %s modules, 0 errors)\n' "megaload" "$mega_mod"
else
  fail=$((fail+1)); printf '  FAIL  %-26s megaload: %s errors over %s modules\n' "megaload" "$mega_err" "$mega_mod"
fi

# Every identifier in the standard library must be ACCOUNTED FOR: bound to a
# declaration, or flagged as a module-path segment. A module prefix (`os` in
# `os.linux.PROT_READ`) has no declaration to point at, and the value path
# used to leave it unflagged -- reporting 3,389 phantom unresolved names
# across the stdlib while emitting zero errors. Sweep a representative set
# of heavy modules and require a clean zero.
sweep_unres=0
for m in stdlib/mem.pie stdlib/io.pie stdlib/ast.pie stdlib/fmt/parse_float.pie \
         stdlib/hash/wyhash.pie stdlib/os/linux/io_uring.pie stdlib/pride/rewrite.pie; do
  u=$("$BIN" "$m" -I stdlib --plain 2>&1 | grep 'idents unresolved' | grep -oE '[0-9]+')
  sweep_unres=$((sweep_unres + ${u:-0}))
done
if [ "$sweep_unres" = "0" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (7 heavy modules: 0 unaccounted idents)\n' "ident_accounting"
else
  fail=$((fail+1)); printf '  FAIL  %-26s %s unaccounted identifiers\n' "ident_accounting" "$sweep_unres"
fi

# ── ADVERSARIAL STRESS FILES ────────────────────────────────────────────
#
# pfront_tests/stress/ exercises spec features with little or no stdlib
# coverage. They were written to BREAK the front end and did: s01 found 7
# bugs and s02 found 9, none of which the 258-module stdlib sweep could
# reach because the stdlib never uses those constructs.
#
# Both must stay at zero errors. Warnings are allowed (unused bindings in
# a file whose point is syntax coverage).
for sf in pfront_tests/stress/*.pie; do
  [ -e "$sf" ] || continue
  sname=$(basename "$sf" .pie)
  serr=$("$BIN" "$sf" -I stdlib -I . --plain --quiet 2>&1 | grep -oE 'errors=[0-9]+' | cut -d= -f2)
  if [ "${serr:-1}" = "0" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s (stress: 0 errors)\n' "$sname"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s stress: %s errors\n' "$sname" "$serr"
    "$BIN" "$sf" -I stdlib -I . --plain 2>&1 | grep 'error \[' | sed 's/^/      /' | head -6
  fi
done

# Specific constructs the stress files proved were broken. Asserted
# individually so a regression names the feature, not just "s01 failed".
#
#   ¬null          spec §13.1's canonical `T ∩ ¬null` did not parse: `null`
#                  lexes as a literal, so the type atom parser rejected it
#   A<B<C<T>>>     `>>` lexed as a right-shift, the C++ problem
#   ∀ / ∃          quantified types had no parse rule at all
#   (> 0)          refinement predicates had no parse rule at all
#   (A -> B)       a parenthesised function type did not parse
#   where          function where-clauses had no parse rule at all
cat > /tmp/pf_ty.pie <<'PIE'
mod t
type A<X> = X
type B<X> = X
type C<X> = X
type NonNull<T> = T ∩ ¬null
type Deep<T>    = A<B<C<T>>>
type Ident      = ∀ X . X -> X
type Some       = ∃ X . X ∩ ¬null
type Pos        = i32 ∩ (> 0)
type Higher     = (i64 -> i64) -> i64
fn wf<X> : X -> i64
  where Y = X ∩ ¬null
  | _ -> 0i64
PIE
tyerr=$("$BIN" /tmp/pf_ty.pie --plain --quiet 2>&1 | grep -oE 'errors=[0-9]+' | cut -d= -f2)
if [ "${tyerr:-1}" = "0" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (lattice, nested generics, quantifiers, refinements, where)\n' "type_algebra"
else
  fail=$((fail+1)); printf '  FAIL  %-26s %s errors\n' "type_algebra" "$tyerr"
  "$BIN" /tmp/pf_ty.pie --plain 2>&1 | grep 'error \[' | sed 's/^/      /'
fi

#   rewrite as a value, `++` composition, `|>` and `|>` with `*`
#   ~Tree/~Data/~Bytes must NOT be treated as a staging level
#   pgen header arrow and `where [conditions]` list
#   irdl operand types, and irdl must stop at the next declaration
cat > /tmp/pf_meta.pie <<'PIE'
mod t
let r1 : Rewrite = rewrite
  | x + 0i64 ↦ x
let r2 : Rewrite = rewrite
  | x * 1i64 ↦ x
let both : Rewrite = r1 ++ r2
pgen pg<T> →
  [x : T] where [x + 0i64] ↦ x
dialect D
  opcode add_i32
  region entry
irdl
  D.add_i32 [a : i32, b : i32] ↦ a
fn after_irdl : i64 -> i64
  | x ->
    let t = ~Tree (x + 1i64)
    let d = ~Data x
    let b = ~Bytes x
    let f = x |> r1*
    let g = x |> r1 |> r2*
    x
PIE
merr=$("$BIN" /tmp/pf_meta.pie --plain --quiet 2>&1 | grep -oE 'errors=[0-9]+' | cut -d= -f2)
# `after_irdl` must survive as a TOP-LEVEL function: an un-braced `irdl`
# block used to run to end of file and swallow everything after it.
# (`pgen` is also a synthetic fn node, so count the named one.)
mfns=$("$BIN" /tmp/pf_meta.pie --plain --dump-ast --quiet 2>&1 | grep -cE "^  fn 'after_irdl'")
if [ "${merr:-1}" = "0" ] && [ "$mfns" = "1" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (rewrite values, ++, |>*, sigils, pgen, irdl)\n' "metaprogramming"
else
  fail=$((fail+1)); printf '  FAIL  %-26s %s errors, after_irdl present=%s (want 0/1)\n' "metaprogramming" "$merr" "$mfns"
  "$BIN" /tmp/pf_meta.pie --plain 2>&1 | grep 'error \[' | sed 's/^/      /'
fi

# A reification sigil must NOT bump the stage level. `~Tree (x + y)` over
# outer locals is spec §18's own example; treating it as a quotation
# reported every local as a cross-stage escape, and tripped the CMTT level
# guard inside `comptime`.
cat > /tmp/pf_sigil.pie <<'PIE'
mod t
let ar : Rewrite = rewrite
  | x + 0i64 ↦ x
fn f : (i64, i64) -> i64
  | (x, y) ->
    let node = ~Tree (x + y * 3i64)
    comptime
      let folded = ~Tree (1i64 + 2i64 + 3i64) |> ar*
      folded
    x
PIE
sigerr=$("$BIN" /tmp/pf_sigil.pie --plain --quiet 2>&1 | grep -oE 'errors=[0-9]+' | cut -d= -f2)
if [ "${sigerr:-1}" = "0" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (sigils are stage-neutral, comptime accepts them)\n' "sigil_not_stage"
else
  fail=$((fail+1)); printf '  FAIL  %-26s %s errors\n' "sigil_not_stage" "$sigerr"
  "$BIN" /tmp/pf_sigil.pie --plain 2>&1 | grep 'error \[' | sed 's/^/      /'
fi

# But a REAL staging construct must still be policed: `stage` and `quote`
# defer evaluation, so an outer local inside one IS an escape. If this
# stops firing, the sigil fix went too far and disabled the check.
cat > /tmp/pf_escape.pie <<'PIE'
mod t
fn f : i64 -> i64
  | x ->
    stage 1
      x + 1i64
PIE
esc=$("$BIN" /tmp/pf_escape.pie --plain 2>&1 | grep -c 'E3202')
if [ "$esc" -ge 1 ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (real cross-stage escape still caught)\n' "stage_escape_kept"
else
  fail=$((fail+1)); printf '  FAIL  %-26s E3202 no longer fires on a genuine escape\n' "stage_escape_kept"
fi

# Constructs s03 proved were broken. `impl ... for` in particular has ZERO
# stdlib uses, so nothing else can catch a regression in it.
#
#   type X = struct   spec §9's primary spelling; the stdlib only writes
#                     the bare `struct X` form, so this never parsed
#   #align/#packed    struct attributes were never consumed
#   { x, y }          anonymous struct patterns (§8 uses them everywhere)
#   v { x: 1 }        struct UPDATE syntax — only the uppercase literal
#                     form checked for a following brace
#   | a | b ->        or-patterns in a function clause
#   | n, guard ->     comma guards (only the `if` spelling worked)
#   impl I for T      `for` is a keyword, not a 3-char identifier
#   poison/freeze/invariant/offsetof
cat > /tmp/pf_data.pie <<'PIE'
mod t
type V = struct #align(16)
  x : i64
  y : i64
interface S
  fn show : Self -> i64
impl S for V
  fn show : Self -> i64
    | _ -> 1i64
fn after_impl : i64 -> i64
  | _ -> 0i64
fn upd : V -> V
  | v -> v { x: 1i64 }
fn pat : V -> i64
  | { x, y } -> x + y
fn orpat : i64 -> bool
  | 1i64 | 2i64 | 3i64 -> true
  | _ -> false
fn guard : i64 -> i64
  | n, n < 0i64 -> 0i64
  | _ -> 1i64
fn ubops : i64 -> i64
  | n ->
    invariant n > 0i64
    let f = freeze n
    let o = offsetof(V, y)
    f + o
fn deref_line : i64 -> i64
  | n ->
    let a = &n
    *a
PIE
derr=$("$BIN" /tmp/pf_data.pie --plain --quiet 2>&1 | grep -oE 'errors=[0-9]+' | cut -d= -f2)
# `after_impl` must be TOP-LEVEL: the impl block used to run to end of file
# and nest every later declaration inside itself.
dfn=$("$BIN" /tmp/pf_data.pie --plain --dump-ast --quiet 2>&1 | grep -cE "^  fn 'after_impl'")
if [ "${derr:-1}" = "0" ] && [ "$dfn" = "1" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (type=struct, attrs, impl-for, patterns, update, UB ops)\n' "structs_impl"
else
  fail=$((fail+1)); printf '  FAIL  %-26s %s errors, after_impl top-level=%s\n' "structs_impl" "$derr" "$dfn"
  "$BIN" /tmp/pf_data.pie --plain 2>&1 | grep 'error \[' | sed 's/^/      /' | head -6
fi

# NO ORPHAN NODE KINDS.
#
# A NodeKind that is declared and named but never PRODUCED looks
# implemented and is not. That is precisely how `typeof` hid: it built an
# unnamed N_TY_NAME whose expression child the resolver never visited, so
# the operand came out unresolved while the file still reported 0 errors.
#
# Two kinds (N_EXPR_PIPELINE, N_EXPR_AWAIT) had no producer AND no
# consumer and were deleted. The rest must all have a producer.
#
# Exemptions are listed explicitly with a reason, so adding one is a
# deliberate act rather than an oversight.
orphans=""
for k in $(grep -oE "^\s+N_[A-Z0-9_]+," pfront/pfront_core.c3 | tr -d ' ,'); do
  case "$k" in
    # Structural markers, produced by the loader rather than the parser.
    N_PROGRAM|N_INVALID|N_KIND_COUNT) continue ;;
    # Aliases the parser deliberately never emits: an assignment is always
    # N_STMT_ASSIGN, a qualified name is always N_MODULE_PATH.
    N_STMT_EXPR|N_EXPR_PATH|N_EXPR_ASSIGN) continue ;;
    # `loop` is not in the spec's 79-keyword list; kept as a reserved slot.
    N_EXPR_LOOP) continue ;;
  esac
  if ! grep -q "Nk\.$k" pfront/pfront_parse.c3 && ! grep -q "Nk\.$k" pfront/pfront_ext.c3 \
     && ! grep -q "NodeKind\.$k" pfront/pfront_parse.c3; then
    orphans="$orphans $k"
  fi
done
if [ -z "$orphans" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (every node kind has a producer)\n' "no_orphan_kinds"
else
  fail=$((fail+1)); printf '  FAIL  %-26s declared but never produced:%s\n' "no_orphan_kinds" "$orphans"
fi

# `typeof(e)` must resolve its OPERAND as an expression. It produced an
# unnamed N_TY_NAME, so the operand was never visited and came out
# unresolved — with the file still reporting zero errors, because an
# unresolved name inside a type annotation is only a note.
cat > /tmp/pf_typeof.pie <<'PIE'
mod t
fn f : i64 -> i64
  | n ->
    let t : typeof(n) = n
    t
PIE
tof=$("$BIN" /tmp/pf_typeof.pie --plain --dump-ast --quiet 2>&1)
t_unres=$(echo "$tof" | grep -c "UNRESOLVED")
t_kind=$(echo "$tof" | grep -c "ty-typeof")
if [ "$t_unres" = "0" ] && [ "$t_kind" = "1" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (typeof operand resolved)\n' "typeof_operand"
else
  fail=$((fail+1)); printf '  FAIL  %-26s unresolved=%s ty-typeof=%s\n' "typeof_operand" "$t_unres" "$t_kind"
fi

# The purity interlock: exactly ONE of two dead stores may be removed. The
# other has a function call as its initializer and MUST survive. This is the
# single most important correctness property of the DCE pass.
purity=$("$BIN" pfront_tests/44_opt_purity.pie 2>&1 | grep "dead stores" | grep -oE '[0-9]+ dead stores' | grep -oE '^[0-9]+')
purity=${purity:-0}
if [ "$purity" = "1" ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (purity: 1 pure store removed, impure kept)\n' "44_opt_purity"
else
  fail=$((fail+1)); printf '  FAIL  %-26s purity: want exactly 1 dead store, got %s\n' "44_opt_purity" "$purity"
fi

# --emit-ast / --emit-sexp must render the FINAL (optimized) tree, not the
# parse tree. 43_opt_dce has 2 statements after `return`; if the emitter were
# printing the pre-optimization tree they would still be there.
sexp=$("$BIN" pfront_tests/43_opt_dce.pie --emit-sexp --quiet 2>&1 | grep '^(fn')
if [ -n "$sexp" ] && ! echo "$sexp" | grep -q "after"; then
  pass=$((pass+1)); printf '  PASS  %-26s (emit-sexp: dead code absent)\n' "emit_ast"
else
  fail=$((fail+1)); printf '  FAIL  %-26s emit-sexp wrong: %s\n' "emit_ast" "$sexp"
fi

# Folded constants must be marked SYN so a reader can tell compiler output
# from source text.
syn=$("$BIN" pfront_tests/42_opt_algebraic.pie --emit-ast --quiet 2>&1 | grep -c "SYN")
if [ "$syn" -ge 2 ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (emit-ast: %s synthetic marked)\n' "emit_syn" "$syn"
else
  fail=$((fail+1)); printf '  FAIL  %-26s emit-ast: want >=2 SYN, got %s\n' "emit_syn" "$syn"
fi

# Semi-pruned: a loop must produce non-local variables (they cross the back
# edge), straight-line code must produce none.
nl_loop=$("$BIN" pfront_tests/46_liveness_loop.pie 2>&1 | grep "semi-pruned" | grep -oE '[0-9]+ non-local' | grep -oE '^[0-9]+')
nl_str=$("$BIN" pfront_tests/47_liveness_local.pie 2>&1 | grep "semi-pruned" | grep -oE '[0-9]+ non-local' | grep -oE '^[0-9]+')
loc_str=$("$BIN" pfront_tests/47_liveness_local.pie 2>&1 | grep "semi-pruned" | grep -oE '[0-9]+ block-local' | grep -oE '^[0-9]+')
if [ "${nl_loop:-0}" -ge 2 ] && [ "${nl_str:-9}" = "0" ] && [ "${loc_str:-0}" -ge 3 ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (semi-pruned: loop=%s non-local, straight=%s/%s local)\n' "liveness" "$nl_loop" "$nl_str" "$loc_str"
else
  fail=$((fail+1)); printf '  FAIL  %-26s semi-pruned: loop=%s (want>=2), straight nonlocal=%s (want 0), local=%s (want>=3)\n' "liveness" "$nl_loop" "$nl_str" "$loc_str"
fi

# The loop CFG must contain a real back edge: the body block's successor is
# the loop header. Without it, liveness would converge in one iteration and
# every loop-carried variable would be misclassified as local.
backedge=$("$BIN" pfront_tests/46_liveness_loop.pie --dump-cfg 2>&1 | grep -cE "b3 +body +succ=\[b2\]")
iters=$("$BIN" pfront_tests/46_liveness_loop.pie 2>&1 | grep -oE '[0-9]+ iters' | grep -oE '^[0-9]+')
if [ "$backedge" -ge 1 ] && [ "${iters:-0}" -ge 2 ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (back edge present, %s dataflow iters)\n' "cfg_backedge" "$iters"
else
  fail=$((fail+1)); printf '  FAIL  %-26s back edge=%s iters=%s\n' "cfg_backedge" "$backedge" "$iters"
fi

# Pass COMPOSITION. Each pass exposing work for the next is the whole reason
# the pipeline iterates to a fixpoint. This asserts the full cascade:
#   fold `1>0` -> take the then-arm -> flatten it into the parent
#   -> the spliced `return` makes the following statements unreachable.
# Asserting only the final node count would pass even if one link broke.
casc=$("$BIN" pfront_tests/48_opt_cascade.pie 2>&1)
c_br=$(echo "$casc" | grep "branches" | grep -oE '[0-9]+' | head -1)
c_fl=$(echo "$casc" | grep "cleanup" | grep -oE '[0-9]+' | head -1)
c_un=$(echo "$casc" | grep "dead code" | grep -oE '[0-9]+' | head -1)
c_sx=$("$BIN" pfront_tests/48_opt_cascade.pie --emit-sexp --quiet 2>&1 | grep '^(fn')
if [ "${c_br:-0}" -ge 1 ] && [ "${c_fl:-0}" -ge 1 ] && [ "${c_un:-0}" -ge 2 ] \
   && ! echo "$c_sx" | grep -q "after"; then
  pass=$((pass+1)); printf '  PASS  %-26s (cascade: %s fold, %s flatten, %s unreachable)\n' "opt_cascade" "$c_br" "$c_fl" "$c_un"
else
  fail=$((fail+1)); printf '  FAIL  %-26s cascade: fold=%s flatten=%s unreach=%s sexp=%s\n' "opt_cascade" "$c_br" "$c_fl" "$c_un" "$c_sx"
fi

# POLYMORPHISM: the pass must actually SOLVE, not just count. Assert every
# call is fully inferred and no bogus conflicts are reported -- `pair<A,B>`
# regressed to "1 conflict" when the parameter tuple was matched positionally.
poly=$("$BIN" pfront_tests/62_polymorphism.pie --plain 2>&1)
p_full=$(echo "$poly" | grep "inference " | grep -oE '[0-9]+ fully' | grep -oE '^[0-9]+' | head -1)
p_conf=$(echo "$poly" | grep -c "problems ")
p_sub=$(echo "$poly" | grep "substitution " | grep -oE '[0-9]+ nodes' | grep -oE '^[0-9]+' | head -1)
if [ "${p_full:-0}" -ge 3 ] && [ "${p_conf:-1}" = "0" ] && [ "${p_sub:-0}" -ge 4 ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (poly: %s inferred, %s nodes substituted)\n' "polymorphism" "$p_full" "$p_sub"
else
  fail=$((fail+1)); printf '  FAIL  %-26s poly: inferred=%s problems=%s subst=%s\n' "polymorphism" "$p_full" "$p_conf" "$p_sub"
fi

# MODULE SYSTEM. The whole reason pfront exists: the legacy front end lexed
# and parsed `use` but never opened a second file, so 4/257 stdlib modules
# compiled. Assert the loader actually pulls in dependencies AND that the
# cross-module calls bind to real declarations.
ms=$("$BIN" pfront_tests/63_modsys.pie -I pfront_tests -I stdlib -I . --quiet 2>&1)
ms_mods=$(echo "$ms" | grep -oE 'modules=[0-9]+' | grep -oE '[0-9]+')
ms_bound=$("$BIN" pfront_tests/63_modsys.pie -I pfront_tests -I stdlib -I . --dump-ast --quiet 2>&1 \
           | grep -cE "method '(add|triple)' +-> fn")
if [ "${ms_mods:-0}" -ge 3 ] && [ "${ms_bound:-0}" -ge 2 ]; then
  pass=$((pass+1)); printf '  PASS  %-26s (%s modules loaded, %s cross-module calls bound)\n' "modsys" "$ms_mods" "$ms_bound"
else
  fail=$((fail+1)); printf '  FAIL  %-26s modules=%s bound=%s (want >=3, >=2)\n' "modsys" "$ms_mods" "$ms_bound"
fi

# ── SYNTAX SUITE: written from the SPEC, not from the implementation ────
#
# pfront_tests/syntax/ exists because every earlier test was written
# against constructs the compiler already handled, so a construct the spec
# lists and nothing exercises stayed broken indefinitely. These files are
# generated from section 24's operator table and section 7's control-flow
# list. On their first run they found eight defects, four of them silent
# miscompiles rather than parse errors.
for f in pfront_tests/syntax/x*.pie; do
  [ -e "$f" ] || continue
  name=$(basename "$f" .pie)
  errs=$(./pfrontc -I stdlib "$f" 2>&1 | grep -cE "error\[")
  if [ "$errs" = "0" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "syntax_$name" "(parses clean)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "syntax_$name" "($errs parse errors)"
    ./pfrontc -I stdlib "$f" 2>&1 | grep "error\[" | head -3 | sed 's/^/      /'
  fi
done

# `not x` and `¬x` are LOGICAL negation. Both lowered to bitwise
# complement (AUO_BNOT) because only TOKEN_BANG was mapped, so `not true`
# became ~1 = -2 rather than false. Assert the opcode, since the parse was
# always fine and only the lowering was wrong.
if [ -x ./pearc ]; then
  nt=$(printf 'mod t\nfn f : bool -> bool\n  | p -> not p\nfn g : bool -> bool\n  | p -> ¬ p\n' > /tmp/pf_not.pie; ./pearc /tmp/pf_not.pie 2>&1)
  n_not=$(echo "$nt" | grep -c 'op=not')
  n_bnot=$(echo "$nt" | grep -c 'op=bnot')
  if [ "$n_not" = "2" ] && [ "$n_bnot" = "0" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "syntax_not_is_logical" "(not/¬ lower to op=not, not bnot)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "syntax_not_is_logical" "op=not:$n_not op=bnot:$n_bnot (want 2/0)"
  fi

  # `and`/`or` are core keywords (section 25). Only && and || were mapped,
  # so the keyword spellings lowered to AIR_UNKNOWN.
  ao=$(printf 'mod t\nfn f : (bool,bool) -> bool\n  | (p,q) -> p and q\nfn g : (bool,bool) -> bool\n  | (p,q) -> p or q\n' > /tmp/pf_ao.pie; ./pearc /tmp/pf_ao.pie 2>&1)
  if echo "$ao" | grep -q 'op=land' && echo "$ao" | grep -q 'op=lor' && ! echo "$ao" | grep -q 'unknown'; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "syntax_and_or_keywords" "(and/or lower like &&/||)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "syntax_and_or_keywords" "keyword and/or did not lower"
  fi

  # `for` must become a REAL loop, not a hole. Assert the induction
  # variable is bounded by the range: `for i in 0..16` gives i in [0,16] at
  # the header and [0,15] in the body, which is the fact that removes a
  # bounds check. Before this, `for` lowered to AIR_UNKNOWN.
  printf 'mod t\nfn f : i64 -> i64\n  | u ->\n    let mut s = 0i64\n    for i in 0i64..16i64\n      s = s + i\n    s\n' > /tmp/pf_for.pie
  ./pearc /tmp/pf_for.pie > /tmp/pf_for.air 2>/dev/null
  if [ -x ./pear_a2 ] && ./pear_a2 /tmp/pf_for.air 2>/dev/null | grep -qE 'sigma .*\[range=0\.\.15( |\])'; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "syntax_for_is_a_loop" "(for i in 0..16 proves i in [0,15] in body)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "syntax_for_is_a_loop" "for did not lower to a bounded loop"
  fi

  # do-while runs its BODY FIRST. With the entry edge pointing at the
  # header the body was hoisted into the entry block and ran once
  # regardless of the condition -- a miscompile, not an imprecision.
  printf 'mod t\nfn f : i64 -> i64\n  | n ->\n    let mut i = 0i64\n    do\n      i = i + 1i64\n    while i < n\n    i\n' > /tmp/pf_dw.pie
  dw=$(./pearc /tmp/pf_dw.pie 2>/dev/null)
  dw_entry=$(echo "$dw" | grep -oE 'entry=\S+' | head -1 | cut -d= -f2)
  # Match the block HEADER by prefix: a block line may carry a `; pred=`
  # suffix, so an exact-string compare finds nothing.
  dw_tgt=$(echo "$dw" | awk -v e="$dw_entry" '$1=="block" && $2==e {f=1} f && $1=="jump" {print $2; exit}')
  dw_body=$(echo "$dw" | awk -v b="$dw_tgt" '$1=="block" && $2==b {f=1;next} f && $1=="end" {exit} f')
  if echo "$dw_body" | grep -q 'op=add' && ! echo "$dw_body" | grep -q 'op=lt'; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "syntax_dowhile_posttest" "(entry jumps to the body, not the test)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "syntax_dowhile_posttest" "do-while ran its test first"
  fi

  # Multi-clause dispatch is Pride's PRIMARY function syntax (section 6.1)
  # and only the first clause used to be lowered, so the spec's own
  # `fact` example compiled to `fn fact = 1`. Assert the dispatch exists:
  # a test against 0, a recursive call, and a phi joining the two arms.
  printf 'mod t\nfn fact : i64 -> i64\n  | 0i64 -> 1i64\n  | n -> n * fact(n - 1i64)\n' > /tmp/pf_fact.pie
  fa=$(./pearc /tmp/pf_fact.pie 2>&1)
  if echo "$fa" | grep -q 'op=eq' && echo "$fa" | grep -q 'name=fact' && echo "$fa" | grep -q 'phi '; then
    printf '  PASS  %-26s %s\n' "syntax_multiclause" "(fact dispatches: test, recurse, join)"
  else
    printf '  FAIL  %-26s %s\n' "syntax_multiclause" "only the first clause was lowered"
    pass=$((pass-1)); fail=$((fail+1))
  fi
  pass=$((pass+1))

  # A guard must GATE its arm. N_GUARD appeared nowhere in a1, so a
  # guarded arm ran unconditionally -- a miscompile, not a missing
  # optimisation. Both spellings (comma and `if`) must produce a branch on
  # the guard expression.
  printf 'mod t\nfn f : i64 -> i64\n  | n ->\n    match n\n      | x, x > 100i64 -> 1i64\n      | _ -> 2i64\n' > /tmp/pf_grd.pie
  gd=$(./pearc /tmp/pf_grd.pie 2>&1)
  if echo "$gd" | grep -q 'op=gt' && echo "$gd" | grep -q 'branch '; then
    printf '  PASS  %-26s %s\n' "syntax_guard_gates_arm" "(guard becomes a real branch)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "syntax_guard_gates_arm" "guard was dropped; arm runs unconditionally"
    fail=$((fail+1))
  fi

  # `assert` must become a real conditional trap, not an opaque node.
  # Lowering it as branch+trap is what lets a2's branch folding delete it
  # once the range analysis proves the condition -- with no assert-specific
  # code in a2 at all.
  printf 'mod t\nfn f : i64 -> i64\n  | n ->\n    assert n > 0i64\n    n\n' > /tmp/pf_as.pie
  asrt=$(./pearc /tmp/pf_as.pie 2>&1)
  if echo "$asrt" | grep -q 'branch ' && echo "$asrt" | grep -q 'trap'; then
    printf '  PASS  %-26s %s\n' "syntax_assert_is_branch_trap" "(assert lowers to branch + trap)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "syntax_assert_is_branch_trap" "assert did not become a conditional trap"
    fail=$((fail+1))
  fi

  # A struct pattern's fields go through N_PAT_FIELD. a1 treated that
  # wrapper as a pattern, hit the default arm and dropped the test, so
  # `| { x: 0, y }` matched every P. Assert the field comparison exists.
  printf 'mod t\nstruct P\n  x : i64\n  y : i64\nfn f : P -> i64\n  | p ->\n    match p\n      | { x: 0i64, y } -> y\n      | { x, y } -> x + y\n' > /tmp/pf_sp.pie
  sp=$(./pearc /tmp/pf_sp.pie 2>&1)
  if echo "$sp" | grep -q 'op=eq' && echo "$sp" | grep -q 'field=x'; then
    printf '  PASS  %-26s %s\n' "syntax_struct_pattern_tests" "(field pattern tests x, name serialised)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "syntax_struct_pattern_tests" "struct pattern field test was dropped"
    fail=$((fail+1))
  fi

  # freeze and assume share a node kind and MUST NOT collapse: assume
  # yields no value, freeze does. Emitting one for the other leaves a
  # consumer with a null operand or an unused promise.
  printf 'mod t\nfn f : i64 -> i64\n  | n -> freeze n\nfn g : i64 -> i64\n  | n ->\n    assume n > 0i64\n    n\n' > /tmp/pf_fz.pie
  fz=$(./pearc /tmp/pf_fz.pie 2>&1)
  if echo "$fz" | grep -q '= freeze ' && echo "$fz" | grep -q '= assume '; then
    printf '  PASS  %-26s %s\n' "syntax_freeze_vs_assume" "(distinct opcodes, not collapsed)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "syntax_freeze_vs_assume" "freeze and assume collapsed"
    fail=$((fail+1))
  fi

  # `handle` did not parse AT ALL. `|` is both bitwise-or and the arm
  # separator, and the computation is parsed with a function that
  # continues across the layout, so `handle c(n)` swallowed the `|` of the
  # first arm as an operator. Assert the handler structure survives into
  # the IR.
  printf 'mod t\neffect E\n  op : i64 -> i64\nfn c : i64 -> i64 ! [E]\n  | n -> perform E.op(n)\nfn f : i64 -> i64\n  | n ->\n    handle c(n)\n      | E.op v k -> k v\n' > /tmp/pf_h.pie
  perr=$(./pfrontc /tmp/pf_h.pie 2>&1 | grep -c "error\[")
  hh=$(./pearc /tmp/pf_h.pie 2>&1)
  if [ "$perr" = "0" ] && echo "$hh" | grep -q 'handle.arm' && echo "$hh" | grep -q 'perform'; then
    printf '  PASS  %-26s %s\n' "syntax_handle_parses" "(handler arms survive to AIR)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "syntax_handle_parses" "handle broke ($perr parse errors)"
    fail=$((fail+1))
  fi

  # Continuations resume by JUXTAPOSITION (section 10.3): `k v` calls k
  # with v. It was implemented nowhere -- `k v` parsed as two separate
  # expressions, so the arm body was just `k` and the argument escaped the
  # arm and surfaced as an unresolved name outside it.
  #
  # The guard matters as much as the feature: `then` is a soft keyword
  # lexed as IDENT, so the first version of this rule turned
  # `if a > b then a else b` into `(b then) a` and broke every inline if.
  printf 'mod t\neffect E\n  op : i64 -> i64\nfn c : i64 -> i64 ! [E]\n  | n -> perform E.op(n)\nfn f : i64 -> i64\n  | n ->\n    handle c(n)\n      | E.op v k -> k v\nfn g : (i64,i64) -> i64\n  | (a,b) -> if a > b then a else b\n' > /tmp/pf_jx.pie
  jx=$(./pfrontc /tmp/pf_jx.pie 2>&1 | grep -c "error\[")
  jxa=$(./pfrontc --dump-ast /tmp/pf_jx.pie 2>&1)
  if [ "$jx" = "0" ] && echo "$jxa" | grep -q "ident 'k'  -> pat-ident 'k'"; then
    printf '  PASS  %-26s %s\n' "syntax_juxtaposition" "(k v is a call; then/else unaffected)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "syntax_juxtaposition" "juxtaposition broken ($jx errors)"
    fail=$((fail+1))
  fi

  # Attributes on their OWN LINE are the spec's primary spelling (6.3) and
  # only the trailing-on-the-signature form was handled, so `#inline` on
  # the next line was parsed as an expression and reported unresolved.
  printf 'mod t\nfn hot : i64 -> i64\n  #inline #noinline\n  | n -> n * 2i64\n' > /tmp/pf_at.pie
  if [ "$(./pfrontc /tmp/pf_at.pie 2>&1 | grep -c 'error\[')" = "0" ]; then
    printf '  PASS  %-26s %s\n' "syntax_attrs_own_line" "(attributes on their own line parse)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "syntax_attrs_own_line" "own-line attributes rejected"
    fail=$((fail+1))
  fi

  # `~Tree e` is REIFICATION: it describes e, it does not evaluate it.
  # Assert both halves -- the reification is recorded AND the quoted
  # addition is absent. Lowering the body would run code the program never
  # asked for and would duplicate any effect inside it.
  printf 'mod t\nfn f : (i64,i64) -> i64\n  | (x,y) ->\n    let node = ~Tree (x + y)\n    x\n' > /tmp/pf_q.pie
  qq=$(./pearc /tmp/pf_q.pie 2>&1)
  if echo "$qq" | grep -q 'name=~Tree' && ! echo "$qq" | grep -q 'op=add'; then
    printf '  PASS  %-26s %s\n' "syntax_quote_not_evaluated" "(~Tree reified, body not executed)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "syntax_quote_not_evaluated" "quotation lowered its body as code"
    fail=$((fail+1))
  fi

  # The compiler's own OUTPUT must be valid text.
  #
  # A diagnostic hint is stored as a bare char* and printed with %s long
  # after the producing call returns, so a hint rendered into a STACK
  # buffer prints whatever later overwrote that frame. Two places did
  # exactly that -- theory_pglcert.c3's non-exhaustiveness witness and
  # theory_bidi.c3's modal mismatch -- and the first emitted raw pointer
  # bytes into stdout, making the compiler's output invalid UTF-8.
  #
  # Checked as a PROPERTY of every syntax file rather than as one case:
  # the bug only shows when enough stack traffic separates the render
  # from the print, so a small input prints plausible text and hides it.
  nonascii=0
  for f in pfront_tests/syntax/x*.pie; do
    [ -e "$f" ] || continue
    if ./pfrontc -I stdlib "$f" 2>&1 | LC_ALL=C grep -qP '[\x80-\xff]'; then
      # Genuine UTF-8 in a source echo is fine; raw control bytes are not.
      if ./pfrontc -I stdlib "$f" 2>&1 | iconv -f UTF-8 -t UTF-8 >/dev/null 2>&1; then
        : # valid UTF-8, e.g. the unicode-operator file echoing its own source
      else
        nonascii=$((nonascii+1))
        printf '        %s emits invalid UTF-8\n' "$f"
      fi
    fi
  done
  if [ "$nonascii" = "0" ]; then
    printf '  PASS  %-26s %s\n' "syntax_output_is_text" "(no diagnostic prints a dead stack buffer)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "syntax_output_is_text" "$nonascii files emit corrupted diagnostics"
    fail=$((fail+1))
  fi

  # MALFORMED INPUT MUST NOT CRASH.
  #
  # pfront documents three exits: 0 clean, 1 warnings, 2 errors. Anything
  # else is a crash, and a compiler that segfaults on bad input cannot be
  # run over a corpus to find out what else is wrong.
  #
  # The corpus in pfront_tests/fuzz/ is deliberately hostile: unterminated
  # strings and block comments, unbalanced brackets in both directions, a
  # NUL byte mid-file, bare CR line endings, mixed tabs and spaces, a
  # 400-digit integer, 500 stacked unary minuses, non-ASCII identifiers,
  # an invalid UTF-8 sequence, a self-referential type and a
  # self-referential struct.
  fz_bad=0
  for f in pfront_tests/fuzz/*.pie; do
    [ -e "$f" ] || continue
    ./pfrontc "$f" >/tmp/pf_fz.out 2>&1
    rc=$?
    if [ "$rc" -gt 2 ]; then
      fz_bad=$((fz_bad+1)); printf '        %s -> rc=%s\n' "$(basename "$f")" "$rc"
    fi
    if ! iconv -f UTF-8 -t UTF-8 /tmp/pf_fz.out >/dev/null 2>&1; then
      fz_bad=$((fz_bad+1)); printf '        %s -> corrupt output\n' "$(basename "$f")"
    fi
  done
  fz_n=$(ls pfront_tests/fuzz/*.pie 2>/dev/null | wc -l)
  if [ "$fz_bad" = "0" ] && [ "$fz_n" -ge 20 ]; then
    printf '  PASS  %-26s %s\n' "fuzz_no_crash" "($fz_n malformed inputs, 0 crashes)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "fuzz_no_crash" "$fz_bad of $fz_n inputs crashed or corrupted output"
    fail=$((fail+1))
  fi

  # PGL DECISION TREES must actually be BUILT, and must not cry wolf.
  #
  # PgenCompiler was allocated, initialised and reported, and
  # build_from_clauses was called from nowhere: every compilation of every
  # file printed "pgl trees: 0 built" and could not print anything else.
  #
  # Once wired up it reported redundant clauses on correct code, so both
  # directions are asserted. A checker that flags valid matches is worse
  # than one that runs never -- it trains readers to ignore it.
  pgt=0; pgr=0
  for f in stdlib/*.pie stdlib/*/*.pie; do
    [ -e "$f" ] || continue
    o=$(./pfrontc -I stdlib "$f" 2>/dev/null)
    a=$(echo "$o" | grep -oE 'pgl trees        : [0-9]+' | grep -oE '[0-9]+$')
    b=$(echo "$o" | grep -oE '[0-9]+ redundant' | grep -oE '[0-9]+')
    pgt=$((pgt + ${a:-0})); pgr=$((pgr + ${b:-0}))
  done
  if [ "$pgt" -ge 5 ] && [ "$pgr" = "0" ]; then
    printf '  PASS  %-26s %s\n' "pgl_trees_built" "($pgt trees over the stdlib, 0 false redundancies)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "pgl_trees_built" "trees=$pgt false_redundant=$pgr"
    fail=$((fail+1))
  fi

  # ...and it must still catch a clause that genuinely cannot fire. Three
  # shapes, because each needs a different key to be distinguished:
  # a clause after a catch-all, a duplicate literal, a duplicate variant.
  printf 'mod t\nfn f : i64 -> i64\n  | n ->\n    match n\n      | _ -> 1i64\n      | 2i64 -> 2i64\n' > /tmp/pf_red1.pie
  printf 'mod t\nfn f : i64 -> i64\n  | n ->\n    match n\n      | 1i64 -> 1i64\n      | 1i64 -> 2i64\n      | _ -> 3i64\n' > /tmp/pf_red2.pie
  printf 'mod t\nenum E\n  A\n  B\nfn f : E -> i64\n  | e ->\n    match e\n      | E.A -> 1i64\n      | E.A -> 2i64\n      | E.B -> 3i64\n' > /tmp/pf_red3.pie
  caught=0
  for rf in /tmp/pf_red1.pie /tmp/pf_red2.pie /tmp/pf_red3.pie; do
    n=$(./pfrontc "$rf" 2>&1 | grep -oE '[0-9]+ redundant' | grep -oE '[0-9]+')
    [ "${n:-0}" -ge 1 ] && caught=$((caught+1))
  done
  if [ "$caught" = "3" ]; then
    printf '  PASS  %-26s %s\n' "pgl_catches_dead_clause" "(catch-all, dup literal, dup variant)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "pgl_catches_dead_clause" "only $caught of 3 dead clauses detected"
    fail=$((fail+1))
  fi

  # Quotations must SHARE structurally.
  #
  # Two identical `~Tree (a + b)` describe one tree and should be one
  # object. The sigil path returned early -- correctly, to stop sigils
  # being treated as a stage bump, since they are reification not staging
  # -- and took quotes.intern with it. So "quote sharing: 0 unique, 0
  # deduplicated" was printed for programs full of sigils, while the
  # staging counter on the line above reported them.
  printf 'mod t\nfn f : (i64,i64) -> i64\n  | (a,b) ->\n    let q1 = ~Tree (a + b)\n    let q2 = ~Tree (a + b)\n    let q3 = ~Tree (a * b)\n    a\n' > /tmp/pf_qs.pie
  qs=$(./pfrontc /tmp/pf_qs.pie 2>&1 | grep -oE 'quote sharing    : [0-9]+ unique, [0-9]+ dedup')
  qu=$(echo "$qs" | grep -oE ': [0-9]+ unique' | grep -oE '[0-9]+')
  qd=$(echo "$qs" | grep -oE '[0-9]+ dedup' | grep -oE '[0-9]+')
  if [ "${qu:-0}" = "2" ] && [ "${qd:-0}" = "1" ]; then
    printf '  PASS  %-26s %s\n' "quote_sharing" "(3 quotes -> 2 unique, 1 shared)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "quote_sharing" "unique=$qu dedup=$qd (want 2/1)"
    fail=$((fail+1))
  fi

  # IRDL dialect USES must be recognised and checked.
  #
  # split_dialect_call only matched N_EXPR_CALL over N_EXPR_FIELD, and the
  # parser builds N_EXPR_METHOD for `T.add(a, b)` -- it cannot tell a
  # method call on a value from a call to a dialect member, so it always
  # emits a method node. Every dialect call written the ordinary way was
  # therefore invisible: "6 opcodes, 0 uses validated", with arity
  # checking, unknown-opcode diagnosis and emit_asm lowering all
  # unreachable for real source.
  #
  # Validation also ran AFTER the rewriter, comptime folding and partial
  # evaluation had rebuilt the tree, so calls that survived the shape
  # check were still missed. It runs against the source tree now.
  printf 'mod t\ndialect T\n  opcode add\n  opcode mul\nfn f : (i64,i64) -> i64\n  | (a,b) -> T.add(a, b)\nfn g : (i64,i64) -> i64\n  | (a,b) -> T.mul(a, b)\n' > /tmp/pf_irdl.pie
  iu=$(./pfrontc /tmp/pf_irdl.pie 2>&1 | grep -oE '[0-9]+ uses validated' | grep -oE '[0-9]+')
  # ...and an opcode the dialect does not declare must be REJECTED.
  printf 'mod t\ndialect T\n  opcode add\nfn f : (i64,i64) -> i64\n  | (a,b) -> T.nosuch(a, b)\n' > /tmp/pf_irdl2.pie
  ib=$(./pfrontc /tmp/pf_irdl2.pie 2>&1 | grep -c 'E3210')
  if [ "${iu:-0}" -ge 2 ] && [ "$ib" -ge 1 ]; then
    printf '  PASS  %-26s %s\n' "irdl_uses_validated" "($iu uses seen, unknown opcode rejected)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "irdl_uses_validated" "validated=$iu unknown_rejected=$ib (want >=2 and >=1)"
    fail=$((fail+1))
  fi

  # The TERM REWRITER must converge, and must not rewrite its own rules.
  #
  # Three compounding bugs made a two-rule chain take 32,768 firings and
  # never reach a fixpoint:
  #
  #   * normalize() walked the `rewrite` block itself, so the rewriter
  #     matched its own left-hand sides and rewrote the RULES into their
  #     right-hand sides -- corrupting the rule set, not just looping
  #   * after each root rewrite it re-normalised every child, re-walking
  #     an already-normal subtree once per step
  #   * top_key's new bands sat at 1,000,000 while theory_trs indexes a
  #     1024-bucket discrimination table with that value and clamps, so
  #     every literal, variant and call collapsed into one bucket
  #
  # `foo(x) -> bar(x)` and `bar(x) -> x` is the whole test: two rules, one
  # term. Anything above a handful of firings means it is not converging.
  printf 'mod t\nlet r : Rewrite = rewrite\n  | foo(x) ↦ bar(x)\n  | bar(x) ↦ x\nfn f : i64 -> i64\n  | n -> foo(n)\nfn foo : i64 -> i64\n  | x -> x\nfn bar : i64 -> i64\n  | x -> x\n' > /tmp/pf_trs.pie
  fr=$(./pfrontc /tmp/pf_trs.pie 2>&1 | grep -oE '[0-9]+ firings' | grep -oE '[0-9]+')
  # Threshold is 2, not "small": the correct answer for two rules on one
  # term is exactly two firings. Allowing 16 let the rule-body fix be
  # reverted (6 firings) while the test still passed, which is a test
  # that measures the wrong thing.
  if [ "${fr:-99999}" -le 2 ]; then
    printf '  PASS  %-26s %s\n' "trs_converges" "(2-rule chain in $fr firings)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "trs_converges" "$fr firings -- not converging"
    fail=$((fail+1))
  fi

  # ...and it must still FIRE. A rewriter that converges by doing nothing
  # would pass the check above.
  printf 'mod t\nlet r : Rewrite = rewrite\n  | zero_add(x) ↦ x\nfn zero_add : i64 -> i64\n  | x -> x\nfn use_it : i64 -> i64\n  | n -> zero_add(n) |> r\n' > /tmp/pf_trs2.pie
  f2=$(./pfrontc /tmp/pf_trs2.pie 2>&1 | grep -oE '[0-9]+ firings' | grep -oE '[0-9]+')
  if [ "${f2:-0}" -ge 1 ]; then
    printf '  PASS  %-26s %s\n' "trs_still_fires" "($f2 firing on a matching term)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "trs_still_fires" "the rewriter fired nothing at all"
    fail=$((fail+1))
  fi

  # Distinct CALL patterns are distinct constructors. `emit_msg(m)` and
  # `recv_msg(m)` can never match the same term, and top_key returned the
  # node KIND for both -- so essentially every rule set with more than one
  # call-headed rule was reported as having a redundant rule.
  printf 'mod t\nlet r : Rewrite = rewrite\n  | foo(x) ↦ x\n  | bar(x) ↦ x\nfn f : i64 -> i64\n  | n -> n\n' > /tmp/pf_ck.pie
  printf 'mod t\nlet r : Rewrite = rewrite\n  | foo(x) ↦ x\n  | foo(y) ↦ y\nfn f : i64 -> i64\n  | n -> n\n' > /tmp/pf_ck2.pie
  ck=$(./pfrontc /tmp/pf_ck.pie 2>&1 | grep -oE '[0-9]+ redundant' | grep -oE '[0-9]+')
  ck2=$(./pfrontc /tmp/pf_ck2.pie 2>&1 | grep -oE '[0-9]+ redundant' | grep -oE '[0-9]+')
  if [ "${ck:-1}" = "0" ] && [ "${ck2:-0}" -ge 1 ]; then
    printf '  PASS  %-26s %s\n' "trs_call_keys" "(distinct callees separate, duplicate caught)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "trs_call_keys" "distinct=$ck duplicate=$ck2 (want 0 and >=1)"
    fail=$((fail+1))
  fi

  # GIVING UP MUST BE VISIBLE.
  #
  # The rewriter counts depth_exceeded when it abandons a subterm past
  # TRS_MAX_DEPTH and fuel_exhausted when it runs out of budget. Both were
  # recorded and never printed, so a rewrite that silently stopped early
  # was indistinguishable from one that reached a normal form. Same class
  # as D6's silent truncation, in a different file.
  #
  # Asserted in both directions: a term just inside the limit reports
  # nothing, and one past it says so.
  # Generated with awk rather than a nested heredoc: a heredoc inside a
  # heredoc does not expand here and silently produced empty files, which
  # made this check pass on nothing.
  gen_deep() {
    n=$1; out=$2
    { printf 'mod t\nlet r : Rewrite = rewrite\n  | wrap(x) \xe2\x86\xa6 x\nfn wrap : i64 -> i64\n  | x -> x\nfn deep : i64 -> i64\n  | n -> '
      awk -v k="$n" 'BEGIN{for(i=0;i<k;i++) printf "wrap("; printf "n"; for(i=0;i<k;i++) printf ")"; printf "\n"}'
    } > "$out"
  }
  gen_deep 380 /tmp/pf_deep_ok.pie
  gen_deep 450 /tmp/pf_deep_bad.pie
  d_ok=$(./pfrontc /tmp/pf_deep_ok.pie 2>&1 | grep -c 'INCOMPLETE')
  d_bad=$(./pfrontc /tmp/pf_deep_bad.pie 2>&1 | grep -c 'INCOMPLETE')
  if [ "$d_ok" = "0" ] && [ "$d_bad" -ge 1 ]; then
    printf '  PASS  %-26s %s\n' "trs_reports_giving_up" "(silent truncation is now reported)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "trs_reports_giving_up" "clean=$d_ok truncated=$d_bad (want 0 and >=1)"
    fail=$((fail+1))
  fi

  # An anonymous function is a VALUE and must lower to a real function.
  #
  # `fn | x -> e` parsed, resolved and type-checked, and a1 had no rule
  # for it: N_EXPR_LAMBDA appeared in build.c3 only as a scope boundary,
  # never as a lowering case. `let g = fn | x -> x + 1` produced three
  # holes and the call through `g` invoked an AIR_UNKNOWN.
  printf 'mod t\nfn f : i64 -> i64\n  | n ->\n    let g = fn | x -> x + 1i64\n    g(n)\n' > /tmp/pf_lam.pie
  lam_h=$(./pearc --stats /tmp/pf_lam.pie 2>/dev/null | grep -oE 'unsupported      : [0-9]+' | grep -oE '[0-9]+$')
  lam_o=$(./pearc /tmp/pf_lam.pie 2>/dev/null)
  # The lambda must become its own function with a lowered body, and the
  # use site must hold a reference to it -- not an opaque unknown.
  if [ "${lam_h:-9}" = "0" ] && echo "$lam_o" | grep -q 'func.ref' \
     && echo "$lam_o" | grep -q 'op=add'; then
    printf '  PASS  %-26s %s\n' "lambda_lowers" "(anonymous fn becomes a real function)"
    pass=$((pass+1))
  else
    printf '  FAIL  %-26s %s\n' "lambda_lowers" "holes=$lam_h; lambda did not lower"
    fail=$((fail+1))
  fi

  # No construct in the syntax suite may leave a lowering hole.
  #
  # The exit status is checked FIRST and separately. `${n:-0}` treats a
  # missing number as zero, and a crash produces no number -- so this
  # assertion read "0 holes, PASS" for a file that segfaulted. x09 did
  # exactly that: pearc died with SIGSEGV on it and the suite called it
  # clean. A crash is now its own failure, and it cannot be mistaken for
  # coverage.
  sh=0
  crashed=""
  for f in pfront_tests/syntax/x*.pie; do
    [ -e "$f" ] || continue
    out=$(./pearc -I stdlib --stats "$f" 2>/dev/null)
    rc=$?
    if [ "$rc" -ge 2 ]; then crashed="$crashed $(basename "$f")(rc=$rc)"; continue; fi
    n=$(echo "$out" | grep -oE 'unsupported      : [0-9]+' | grep -oE '[0-9]+$')
    if [ -z "$n" ]; then crashed="$crashed $(basename "$f")(no-stats)"; continue; fi
    sh=$((sh + n))
  done
  if [ -n "$crashed" ]; then
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "syntax_lowering_no_crash" "pearc failed on:$crashed"
  else
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "syntax_lowering_no_crash" "(every syntax file lowers without crashing)"
  fi
  # FIELD TYPES must reach the IR, and the pass must actually RUN.
  #
  # `field access` reported 0 lookups on all 258 stdlib modules -- not
  # merely unwired but actively switched off, because the inferencer
  # cached a TypeId in the same integer that marks a numeric tuple index.
  # Assert the lookups happen, that a narrow field bounds the value, that
  # a wide one does not over-claim, and that a tuple index still works.
  ft_out=$(./pfrontc pfront_tests/77_field_types.pie -I stdlib 2>&1)
  ft_look=$(echo "$ft_out" | grep -oE 'field access     : [0-9]+' | grep -oE '[0-9]+$')
  ft_miss=$(echo "$ft_out" | grep -oE '[0-9]+ miss' | grep -oE '[0-9]+')
  ft_air=$(./pearc pfront_tests/77_field_types.pie 2>/dev/null)
  ft_hit=$(echo "$ft_out" | grep -oE '\([0-9]+ hit' | grep -oE '[0-9]+')
  ft_ok=1
  [ "${ft_look:-0}" -ge 4 ] || ft_ok=0
  [ "${ft_hit:-0}" -ge 3 ] || ft_ok=0
  # An UNKNOWN field must be looked up and MISSED, not skipped. This is
  # the half the p.aux collision destroyed: it made the checker return
  # before looking anything up, so the miss was invisible.
  [ "${ft_miss:-0}" = "1" ] || ft_ok=0
  echo "$ft_air" | grep -q 'field=b .*range=0\.\.255 w=8'   || ft_ok=0
  echo "$ft_air" | grep -q 'field=h .*range=0\.\.65535 w=16' || ft_ok=0
  echo "$ft_air" | grep -qE 'field=big .*range='             && ft_ok=0
  if [ "$ft_ok" = "1" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "field_types_reach_ir" "($ft_look lookups, $ft_hit hit, $ft_miss miss; u8 -> [0,255])"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "field_types_reach_ir" "lookups=$ft_look hit=$ft_hit miss=$ft_miss (want >=4 / >=3 / 1)"
    echo "$ft_air" | grep 'load\.field' | sed 's/^/      /' | head -4
  fi

  # And over the REAL library, where the number is what makes it credible.
  ftl=0; ftm=0
  for f in $(find stdlib -name '*.pie' | sort); do
    o=$(./pfrontc "$f" -I stdlib 2>&1)
    l=$(echo "$o" | grep -oE 'field access     : [0-9]+' | grep -oE '[0-9]+$')
    m=$(echo "$o" | grep -oE '[0-9]+ miss' | grep -oE '[0-9]+')
    ftl=$((ftl + ${l:-0})); ftm=$((ftm + ${m:-0}))
  done
  if [ "$ftl" -ge 4000 ] && [ "$ftm" = "0" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "stdlib_fields_resolve" "($ftl lookups, $ftm misses; was 0 lookups)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "stdlib_fields_resolve" "lookups=$ftl misses=$ftm (want >=4000 / 0)"
  fi

  # GRAMMAR FUZZ CORPUS: 168 files of hostile but token-shaped input.
  #
  # Kept in the tree rather than regenerated, because a corpus that
  # changes every run cannot regress. These found the irdl progress loop
  # and the operator-named-function bug; both fixtures are in
  # pfront_tests/fuzz/ alongside.
  #
  # Three properties, in increasing strength:
  #   1. neither binary exits on a signal or hangs;
  #   2. everything a1 lowers VERIFIES;
  #   3. AIR_UNKNOWN appears only where pfront already reported an error
  #      -- i.e. no lowering holes on input the front end accepted.
  gf_sig=0; gf_verr=0; gf_hole=0; gf_n=0
  for f in pfront_tests/fuzz/grammar/*.pie; do
    [ -e "$f" ] || continue
    gf_n=$((gf_n+1))
    ( ulimit -v 3000000; timeout 25 ./pfrontc "$f" -I stdlib --plain --quiet >/dev/null 2>&1 )
    [ $? -ge 124 ] && gf_sig=$((gf_sig+1))
    out=$( ( ulimit -v 3000000; timeout 25 ./pearc --verify "$f" -I stdlib 2>/dev/null ) )
    rc=$?
    if [ $rc -ge 124 ]; then gf_sig=$((gf_sig+1)); continue; fi
    e=$(echo "$out" | grep 'errors / warnings' | sed -E 's/.*: *([0-9]+) *\/.*/\1/')
    u=$(echo "$out" | grep -oE 'unsupported      : [0-9]+' | grep -oE '[0-9]+$')
    gf_verr=$((gf_verr + ${e:-0}))
    if [ "${u:-0}" != "0" ]; then
      pe=$(./pfrontc "$f" -I stdlib --plain --quiet 2>&1 | grep -oE 'errors=[0-9]+' | grep -oE '[0-9]+')
      [ "${pe:-0}" = "0" ] && gf_hole=$((gf_hole+1))
    fi
  done
  if [ "$gf_sig" = "0" ] && [ "$gf_verr" = "0" ] && [ "$gf_hole" = "0" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "grammar_fuzz_corpus" "($gf_n files: 0 signals, 0 verify errors, 0 holes on clean input)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "grammar_fuzz_corpus" "signals=$gf_sig verify_errors=$gf_verr holes_on_clean=$gf_hole of $gf_n"
  fi

  # RESOURCE CEILING: measured PEAK RSS, not a ulimit.
  #
  # `ulimit -v` does NOT constrain this binary in this environment -- a
  # 24 MB compile succeeds with the limit set to 20 MB, because the
  # kernel is not enforcing RLIMIT_AS for these mappings. A test built on
  # it passes no matter what, which is worse than no test. Measured from
  # /proc/<pid>/status instead, which cannot be fooled.
  #
  # KNOWN OPEN ISSUE this bounds: a four-line `pgen` block with a
  # wildcard peaks around 77 MB against 2.8 MB for a trivial file, and a
  # 2 KB fuzzed file reaches ~1.4 GB and is OOM-killed. See
  # pfront_tests/known_issues/README.md for what has been ruled out.
  # This assertion pins REAL modules so the number cannot drift; it does
  # not pretend the pgen case is fixed.
  peak_of() {
    "$@" >/dev/null 2>&1 &
    local pid=$! peak=0 cur
    while kill -0 $pid 2>/dev/null; do
      cur=$(awk '/VmHWM/{print $2}' /proc/$pid/status 2>/dev/null)
      [ -n "$cur" ] && [ "$cur" -gt "$peak" ] && peak=$cur
      sleep 0.02
    done
    echo "$peak"
  }
  rc_small=$(peak_of ./pfrontc pfront_tests/known_issues/pgen_memory_min.pie -I stdlib --plain --quiet)
  rc_io=$(peak_of ./pfrontc stdlib/io.pie -I stdlib --plain --quiet)
  # 120 MB: io.pie measures ~24 MB, so this is 5x headroom for machine
  # variation while still catching an order-of-magnitude regression.
  if [ "${rc_io:-999999}" -lt 120000 ]; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "resource_ceiling" "(stdlib/io.pie peak ${rc_io} kB; pgen known-heavy ${rc_small} kB)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "resource_ceiling" "stdlib/io.pie now peaks at ${rc_io} kB (was ~24000)"
  fi

  # PROGRESS: no block scanner may loop without consuming a token.
  #
  # `irdl` followed by `{ *` is eight characters and hung pfrontc until
  # the OOM killer took it -- 3.7 million iterations in five seconds, all
  # on the same token, allocating an AST node each time. parse_irdl_decl
  # was the one block scanner without an `else { break; }`, so a token
  # that parse_module_path could not consume left the loop exactly where
  # it started.
  #
  # Found by fuzzing, so the fuzz input that found it is kept alongside
  # the minimal case. Both are run under a MEMORY CAP as well as a
  # timeout: an infinite loop that allocates shows up as rc=137 rather
  # than rc=124 depending on which limit it hits first, and either is a
  # failure.
  pg_bad=""
  for f in pfront_tests/fuzz/f_irdl_minimal.pie pfront_tests/fuzz/f_irdl_progress.pie; do
    [ -e "$f" ] || continue
    ( ulimit -v 2000000; timeout 15 ./pfrontc "$f" -I stdlib --plain --quiet >/dev/null 2>&1 )
    rc=$?
    [ "$rc" -ge 124 ] && pg_bad="$pg_bad $(basename "$f")(rc=$rc)"
  done
  if [ -z "$pg_bad" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "parser_makes_progress" "(irdl block cannot spin on one token)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "parser_makes_progress" "hung or OOMed on:$pg_bad"
  fi

  # DEEP INPUT MUST NOT CRASH THE COMPILER.
  #
  # A left-associative chain `a + b + c + ...` is FLAT to the parser --
  # MAX_DEPTH never fires -- and a tree N deep to every walker that
  # recurses on children. Both pfront's resolver (resolve_expr /
  # resolve_stmt, mutually recursive) and a1's lowering walk had no guard
  # at all, and both died on a signal with no diagnostic: pfrontc
  # segfaulted at ~5,000 terms, pearc at ~900.
  #
  # Generated here rather than committed as a fixture because the sizes
  # are the point and a 20,000-term file is not worth versioning. The
  # requirement is not that these COMPILE -- refusing them is fine -- but
  # that the compiler always exits cleanly and says why.
  dc_bad=""
  for n in 900 1500 5000 20000; do
    awk -v n="$n" 'BEGIN{
      printf "mod deepchain\nfn f : (i64) -> i64\n  | n -> n";
      for (i = 1; i < n; i++) printf " + n";
      printf "\n" }' > /tmp/pf_deepchain.pie
    ./pfrontc /tmp/pf_deepchain.pie --plain --quiet >/dev/null 2>&1
    rc1=$?
    ./pearc /tmp/pf_deepchain.pie >/dev/null 2>&1
    rc2=$?
    [ "$rc1" -ge 128 ] && dc_bad="$dc_bad pfront@$n(rc=$rc1)"
    [ "$rc2" -ge 128 ] && dc_bad="$dc_bad pearc@$n(rc=$rc2)"
  done
  if [ -z "$dc_bad" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "deep_chain_no_crash" "(900..20000 terms: no signal, always a diagnostic)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "deep_chain_no_crash" "crashed on:$dc_bad"
  fi

  # WIDE CONSTRUCTS: no fixed-size buffer may silently drop operands.
  #
  # Asserting the WIDTHS, not just that the file compiles. Every one of
  # these numbers is past a cap that used to be in a1, and each cap
  # dropped its excess with no error: calls/structs/tuples/arrays at 16,
  # clauses and match arms and phi operands at 64. A phi short of its
  # block's predecessor count reads undefined values on the edges it
  # omits, which is why the phi width is checked against the predecessor
  # count rather than against a constant.
  wc_air=$(./pearc -I stdlib pfront_tests/syntax/x13_wide_constructs.pie 2>/dev/null)
  wc_call=$(echo "$wc_air" | awk '/= call /{n=gsub(/%[0-9]+/,"&"); if(n>m)m=n} END{print m+0}')
  wc_struct=$(echo "$wc_air" | awk '/= struct /{n=gsub(/%[0-9]+/,"&"); if(n>m)m=n} END{print m+0}')
  wc_phi=$(echo "$wc_air" | awk '/= phi /{n=gsub(/%[0-9]+@/,"&"); if(n>m)m=n} END{print m+0}')
  wc_unsup=$(./pearc -I stdlib --stats pfront_tests/syntax/x13_wide_constructs.pie 2>/dev/null | grep -oE 'unsupported      : [0-9]+' | grep -oE '[0-9]+$')
  wc_err=$(./pearc -I stdlib --verify pfront_tests/syntax/x13_wide_constructs.pie 2>/dev/null | grep 'errors / warnings' | grep -oE '[0-9]+ / [0-9]+' | cut -d' ' -f1)
  if [ "${wc_call:-0}" -ge 21 ] && [ "${wc_struct:-0}" -ge 21 ] \
     && [ "${wc_phi:-0}" -ge 81 ] && [ "${wc_unsup:-1}" = "0" ] && [ "${wc_err:-1}" = "0" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "wide_constructs" "(call=$wc_call struct=$wc_struct phi=$wc_phi, 0 dropped)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "wide_constructs" "call=$wc_call struct=$wc_struct phi=$wc_phi unsup=$wc_unsup err=$wc_err"
  fi

  # A phi must have exactly one operand per predecessor, everywhere in the
  # syntax suite. This is the property the 64-cap violated, and it is
  # cheap enough to check over every file rather than one fixture.
  pm_bad=0
  for f in pfront_tests/syntax/x*.pie; do
    [ -e "$f" ] || continue
    ./pearc -I stdlib "$f" 2>/dev/null | awk '
      /^func /{fn=$2}
      /^  block /{blk=$2; np=0; if (match($0,/pred=[A-Za-z0-9,]+/)) {
          s=substr($0,RSTART+5,RLENGTH-5); np=split(s,a,",") } preds[fn" "blk]=np }
      /= phi /{n=gsub(/%[0-9]+@/,"&"); if (n != preds[fn" "blk]) print "BAD" }
    ' | grep -q BAD && pm_bad=$((pm_bad+1))
  done
  if [ "$pm_bad" = "0" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "phi_operand_arity" "(every phi covers every predecessor)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "phi_operand_arity" "$pm_bad syntax files have a phi short of its predecessors"
  fi

  if [ "$sh" = "0" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "syntax_no_lowering_holes" "(every syntax file lowers with 0 unknowns)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "syntax_no_lowering_holes" "$sh AIR_UNKNOWN across the syntax suite"
  fi

  # The width a literal DECLARES must be the width it CARRIES, and the
  # value must fit it. Asserting the widths themselves, not just that the
  # file parses: the hex bug parsed perfectly and produced w=6.
  ns=$(./pearc -I stdlib pfront_tests/76_numeric_suffix_hex.pie 2>/dev/null)
  ns_ok=1
  echo "$ns" | grep -q 'ival=8317987319222330741 .*w=64' || ns_ok=0   # 0x..u64, f in mantissa
  echo "$ns" | grep -q 'ival=3735928559 .*w=64'          || ns_ok=0   # 0xdeadbeefu64
  echo "$ns" | grep -q 'ival=31 .*w=64'                  || ns_ok=0   # 0x1fi64
  echo "$ns" | grep -q 'ival=200 .*w=8'                  || ns_ok=0   # 200u8
  echo "$ns" | grep -q 'ival=4294967295 .*w=32'          || ns_ok=0   # 4294967295u32
  if [ "$ns_ok" = "1" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "numeric_suffix_widths" "(hex mantissa never mistaken for a suffix)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "numeric_suffix_widths" "a literal carries the wrong declared width"
    echo "$ns" | grep -E 'ival=(8317987319222330741|3735928559|31|200|4294967295) ' | sed 's/^/      /'
  fi

  # And the whole standard library must be free of values that do not fit
  # their own declared width. This was 4,969 before the suffix, boolean
  # signedness and u64 representation fixes; it is the metric that says
  # the width fact can actually be TRUSTED by a later stage.
  wx=0
  for f in $(find stdlib -name '*.pie' | sort); do
    n=$(./pearc --verify "$f" 2>/dev/null | grep -oE 'width exceeded: [0-9]+' | grep -oE '[0-9]+$')
    wx=$((wx + ${n:-0}))
  done
  if [ "$wx" = "0" ]; then
    pass=$((pass+1)); printf '  PASS  %-26s %s\n' "stdlib_width_sound" "(0 values exceed their declared width; was 4969)"
  else
    fail=$((fail+1)); printf '  FAIL  %-26s %s\n' "stdlib_width_sound" "$wx values exceed their own declared width"
  fi
fi

echo "---"
echo "pfront regression: pass=$pass fail=$fail"

# Stdlib sweep: the metric that actually tracks front-end capability.
sc=0; tot=0
for f in $(find stdlib -name '*.pie' 2>/dev/null); do
  tot=$((tot+1))
  own=$("$BIN" "$f" -I stdlib -I . 2>&1 | grep 'error' | grep -c "$f:")
  [ "$own" = "0" ] && sc=$((sc+1))
done
echo "stdlib self-clean: $sc / $tot   (baseline before rewrite: 4)"
[ "$fail" -eq 0 ] || exit 1
