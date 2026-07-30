// codegen.c3 — Pride → LLVM 22.1.8 IR text emitter
// Implementation language: C3 (host).
// This module is Pride's native code generator. It walks a fully-built and
// verified SsiModule and emits LLVM 22 IR text (the .ll format), which is
// then compiled through the pure LLVM 22 toolchain — no Clang anywhere.
// Full pipeline (no Clang):
//   pride --emit-llvm output.ll source.pie   # this module
//   llvm-as-22 output.ll -o output.bc        # assemble
//   opt-22 -O2 output.bc -o output.opt.bc    # optimise
//   llc-22 -filetype=obj output.opt.bc -o output.o  # compile
//   ld.lld-22 crt1.o output.o runtime.o -lc -o prog # link
// TARGET
// LLVM 22.1.8 (tested). Forward-compatible: LLVM IR is backward-compatible
// across minor and patch versions.
// Default target: x86_64-pc-linux-gnu (System V AMD64 ABI, ELF).
// The target triple and data layout strings are constants that can be
// overridden via CgenModule fields before calling emit().
// KEY DESIGN DECISIONS
// 1. OPAQUE POINTERS (mandatory since LLVM 17): all pointer types emit as
//    `ptr` — no typed pointers (i32*, i8*) whatsoever.
// 2. VALUE NAMING: SSA values use the dense integer ids from IrVal.id,
//    emitted as %v0, %v1, ... Basic blocks use %B0, %B1, ... matching the
//    SsiModule dump format so IR is easily cross-referenced.
// 3. TYPE SYSTEM MAPPING:
//    Pride primitive → LLVM type:
//      i8/u8 → i8,  i16/u16 → i16,  i32/u32 → i32,  i64/u64 → i64
//      f32 → float,  f64 → double,  bool → i1,  char → i32 (Unicode codepoint)
//      ptr/*T/&T/&mut T → ptr   (opaque, LLVM 17+ style)
//      () unit → void (in return position) or {}* / {}  (in value position)
//      Str → { ptr, i64 }  (data pointer + byte length)
//      [T;N] → [N x LLVMType(T)]
//      (A,B,...) tuple → { LLVMType(A), LLVMType(B), ... }
//      struct S → %S (named type, declared at module level)
// 4. STRUCT LAYOUT: struct field access uses `getelementptr inbounds` with
//    the struct type and the field index (0-based in declaration order).
//    The field index is resolved by walking the struct's field block.
// 5. AGGREGATES (tuple/struct/array literals): lowered as a sequence of
//    `insertvalue` instructions building up an aggregate from `undef`.
// 6. ALLOC/FREE: map to `@malloc` / `@free` (libc). The runtime may replace
//    these with a custom allocator by linking a malloc shim.
// 7. ALGEBRAIC EFFECTS (IR_EFFECT_OP / IR_HANDLER / IR_RESUME):
//    Lowered using a lightweight setjmp/longjmp-based prompt stack — the
//    simplest correct ABI, replaceable with evidence passing or split stacks
//    later without changing the frontend IR.
//    Per handler frame:
//      struct __pride_frame { jmp_buf buf; ptr handler_fn; ptr prev; }
//      IR_EFFECT_OP   → call __pride_perform(frame_ptr, op_id, arg_ptr)
//      IR_HANDLER     → __pride_push_handler double-returns a dispatch token:
//                       0 = run computation (default edge); op_id+1 = arm edge
//      IR_HANDLER_ARM → arm body; pop frame (only reached when not resumed)
//      IR_HANDLER_COMPLETE → __pride_complete() pops the frame on the normal
//                       computation-exit path (the only pop a resumed
//                       computation ever performs — resume is tail-only)
//      IR_RESUME      → longjmp into saved buf with resume value
//    Runtime declarations are emitted into the .ll file as `declare` stmts.
// 8. SIZEOF/ALIGNOF sentinels: IR_CONST_INT with ival=0 and src.kind ==
//    NODE_EXPR_SIZEOF/ALIGNOF are replaced with the real byte-size/alignment
//    computed by llvm_sizeof() during emit.
// 9. OUTPUT: writes to a CFile opened by the caller. Use `--emit-llvm file.ll`
//    from the driver.
// COMPLETENESS
// Every IrOp and TermKind is handled. IR_UNKNOWN at asm sites emits an
// inline-asm call; IR_UNKNOWN at with-cleanup sites emits a call to
// __pride_drop. All other IR_UNKNOWN nodes (extern/global refs) emit a
// reference to the mangled global symbol.

module codegen;

import lexer;
import ast;
import ssi_ir;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);
extern fn int   fprintf(void* stream, char* fmt, ...);
extern fn void* fopen(char* path, char* mode);
extern fn int   fclose(void* stream);
extern fn int   fwrite(void* ptr, usz size, usz n, void* stream);
extern fn int   snprintf(char* buf, usz size, char* fmt, ...);
extern fn usz   strlen(char* s);
extern fn void* memset(void* dst, int c, usz n);
extern fn void* memcpy(void* dst, void* src, usz n);

alias Node = ast::AstNode;
alias Nk   = ast::NodeKind;
alias Tt   = lexer::TokenType;


// LLVM 22.1.8 x86_64-pc-linux-gnu data layout (from llc-22 -march=x86-64 defaults)
const char* LLVM_DATALAYOUT =
    "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128";
const char* LLVM_TRIPLE = "x86_64-pc-linux-gnu";
char* g_target_triple_override = null;  // set by --target=<triple>
bool  g_freestanding           = false; // set by --freestanding: no runtime, no libc

// Deep generic-argument substitution context (r48): while a GENERIC_APP's
// field list is being expanded into LLVM text / sizes, TYPEVAR leaves that
// resolve to the app's generic parameters are substituted with the app's
// arguments.  ast::generic_payload_subst alone only rewrites a BARE typevar
// payload, so COMPOUND field types like `items : [T; 2]` stayed boxed
// (`[2 x ptr]` for `Box<i64>`, with `store ptr 99` as downstream fallout).
Node* g_subst_app = null;

// Known target datalayouts
const char* LLVM_DATALAYOUT_AARCH64 =
    "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128";
const char* LLVM_DATALAYOUT_WASM32 =
    "e-m:e-p:32:32-p10:8:8-p20:8:8-i64:64-n32:64-S128-ni:1:10:20";
const char* LLVM_DATALAYOUT_WASM64 =
    "e-m:e-p:64:64-p10:8:8-p20:8:8-i64:64-n32:64-S128-ni:1:10:20";
const char* LLVM_TRIPLE_AARCH64_LINUX = "aarch64-unknown-linux-gnu";
const char* LLVM_TRIPLE_WASM32       = "wasm32-unknown-unknown";
const char* LLVM_TRIPLE_WASM64       = "wasm64-unknown-unknown";

fn bool cstr_eq(char* a, char* b)
{
    if (a == null && b == null) return true;
    if (a == null || b == null) return false;
    usz i = 0;
    while (a[i] != 0 && b[i] != 0) { if (a[i] != b[i]) return false; i++; }
    return a[i] == b[i];
}

// Is the first n bytes of a equal to the (exactly n bytes) literal b?
fn bool cstr_eq_n(char* a, char* b, usz n) @private
{
    if (a == null || b == null) return false;
    for (usz i = 0; i < n; i++) { if (a[i] != b[i]) return false; }
    return true;
}

// Rank of a tensor TYPE annotation (NODE_TYPE_TENSOR[elem, d0, d1, ...] —
// so rank == child_count - 1).  Returns -1 for null / non-tensor
// annotations.  Used by the `@` lowering to pick batched gemm vs. the
// scalar dot-product path (spec §11).
fn int cg_tensor_rank_of(Node* ann)
{
    if (ann == null) return -1;
    if (ann.kind == Nk.NODE_TYPE_TENSOR) return (int)ann.child_count - 1;
    return -1;
}

// Exact, full-byte comparison of a (ptr,len) span against a C string literal.
// Every ad-hoc "is this identifier named X" check in this file MUST go
// through this helper rather than hand-rolled partial byte-position checks
// (e.g. `len==6 && name[0]=='c' && name[5]=='t'`) — a partial check silently
// accepts other same-length strings that happen to share the tested byte
// positions, which has previously caused real collisions (see the
// `name_is_runtime_decl` / concat-vs-arbitrary-identifier class of bugs).
// This is the single point of truth for "does this span spell exactly S".
fn bool span_is(char* p, usz len, char* lit)
{
    if (p == null || lit == null) return false;
    usz i = 0;
    while (i < len)
    {
        if (lit[i] == 0) return false;   // span longer than the literal
        if (p[i] != lit[i]) return false;
        i++;
    }
    return lit[i] == 0;                  // span must consume the whole literal
}

fn void set_target_triple(char* triple) { g_target_triple_override = triple; }
fn void set_freestanding(bool v)        { g_freestanding = v; }


const usz MAX_STRUCTS  = 1024;   // named struct types in one module
const usz MAX_STRBUF   = 1048576; // output buffer: 1 MB per flush cycle — fewer syscalls
const usz NAME_BUF     = 256;    // scratch buffer for name mangling
const usz TY_BUF       = 256;    // scratch buffer for type strings

// Used to fill sizeof/alignof sentinels. Values match System V AMD64 ABI.

fn usz prim_sizeof(char* name, usz len)
{
    if (len == 0) return 8;
    // Float types
    if (len==3 && name[0]=='f' && name[1]=='3' && name[2]=='2') return 4;   // f32
    if (len==3 && name[0]=='f' && name[1]=='6' && name[2]=='4') return 8;   // f64
    // Bool
    if (len==4 && name[0]=='b' && name[1]=='o' && name[2]=='o' && name[3]=='l') return 1;
    // Pointer / string
    if (len==3 && name[0]=='p' && name[1]=='t' && name[2]=='r') return 8;   // ptr
    if (len==3 && name[0]=='s' && name[1]=='t' && name[2]=='r') return 16;  // str={ptr,len}
    // Arbitrary-width iN/uN: ceil(N/8) bytes, capped at 8
    if (len >= 2 && (name[0]=='i' || name[0]=='u'))
    {
        long w = 0; bool ok = true;
        for (usz di = 1; di < len; di++)
        {
            if (name[di] < '0' || name[di] > '9') { ok = false; break; }
            w = w * 10 + (long)(name[di] - '0');
        }
        if (ok && w >= 1) { long s = (w + 7) / 8; return (usz)(s > 8 ? 8 : s); }
    }
    return 8;
}

fn usz prim_alignof(char* name, usz len)
{
    usz szval = prim_sizeof(name, len);
    return szval < 8 ? szval : 8; // natural alignment, capped at 8
}


// Write the LLVM type string for a Pride type node into buf[cap].
// Returns buf (always null-terminated). Falls back to "i64" for unknown types.

// Concrete generic-struct instantiation (r33): `Pair<i64, f64>`.  Returns
// the struct decl's FIELD BLOCK when the app instantiates a STRUCT with
// every argument concrete (no type-parameter TypeVars).  The ABI must then
// print the SUBSTITUTED field record ({ i64, double }) — not the decl's
// boxed { ptr, ptr } parameter repr, which is only coherent in still-generic
// contexts.  Construction (insertvalue), field access (extractvalue),
// parameters, and returns all print through this helper, so one substitution
// keeps the whole value repr consistent.  An app that still mentions a type
// parameter (or whose head is not a struct) returns null and keeps the
// historical boxed head repr.
fn Node* cg_concrete_struct_app_fblk(Node* app)
{
    if (app == null || app.kind != Nk.NODE_TYPE_GENERIC_APP || app.child_count < 2)
    { return null; }
    for (usz ai = 1; ai < app.child_count; ai++)
    {
        Node* arg = app.children[ai];
        if (arg != null && arg.kind == Nk.NODE_TYPEVAR && arg.resolved != null
            && (arg.resolved.kind == Nk.NODE_PARAM
                || arg.resolved.kind == Nk.NODE_GENERIC_PARAM))
        { return null; }   // still generic — boxed repr
    }
    Node* sd = ast::struct_decl_of(app);
    if (sd == null) return null;
    for (usz fi = 0; fi < sd.child_count; fi++)
    {
        Node* fc = sd.children[fi];
        if (fc != null && fc.kind == Nk.NODE_EXPR_BLOCK) return fc;
    }
    return null;
}

fn char* type_to_llvm_buf(Node* t, char* buf, usz cap, int depth)
{
    if (cap == 0) return buf;
    buf[0] = 0;
    // Defensive fuel only (trees are acyclic). 16 was too small for honestly
    // nested aggregates; on overflow emit void* ptr instead of a WRONG i64.
    if (t == null || depth > 64) { snprintf(buf, cap, "ptr"); return buf; }
    // Union/intersection types: lower as first component's LLVM type.
    // ∪ and ∩ are type-system-only annotations; LLVM uses the first operand's repr.
    if (t.kind == Nk.NODE_TYPE_UNION || t.kind == Nk.NODE_TYPE_INTERSECT)
    {
        if (t.child_count >= 1 && t.children[0] != null) { return type_to_llvm_buf(t.children[0], buf, cap, depth + 1); }
        snprintf(buf, cap, "i64");
        return buf;
    }


    // Fast path: primitive types — most common case, avoid all branches below
    if (t.kind == Nk.NODE_TYPE_PRIMITIVE)
    {
        char* n = t.p.ident.name_ptr; usz l = t.p.ident.name_len;
        // Check common types by length then first chars (sorted by frequency)
        if (l == 3 && n[0] == 'i' && n[1] == '6') { buf[0]='i'; buf[1]='6'; buf[2]='4'; buf[3]=0; return buf; }  // i64
        if (l == 3 && n[0] == 'u' && n[1] == '6') { buf[0]='i'; buf[1]='6'; buf[2]='4'; buf[3]=0; return buf; }  // u64
        if (l == 3 && n[0] == 'i' && n[1] == '3') { buf[0]='i'; buf[1]='3'; buf[2]='2'; buf[3]=0; return buf; }  // i32
        if (l == 3 && n[0] == 'u' && n[1] == '3') { buf[0]='i'; buf[1]='3'; buf[2]='2'; buf[3]=0; return buf; }  // u32
        if (l == 2 && n[0] == 'i' && n[1] == '8') { buf[0]='i'; buf[1]='8'; buf[2]=0; return buf; }              // i8
        if (l == 2 && n[0] == 'u' && n[1] == '8') { buf[0]='i'; buf[1]='8'; buf[2]=0; return buf; }              // u8
        if (l == 3 && n[0] == 'i' && n[1] == '1') { buf[0]='i'; buf[1]='1'; buf[2]='6'; buf[3]=0; return buf; } // i16
        if (l == 3 && n[0] == 'u' && n[1] == '1') { buf[0]='i'; buf[1]='1'; buf[2]='6'; buf[3]=0; return buf; } // u16
        if (l == 3 && n[0] == 'f' && n[1] == '6') { buf[0]='d'; buf[1]='o'; buf[2]='u'; buf[3]='b'; buf[4]='l'; buf[5]='e'; buf[6]=0; return buf; } // f64
        if (l == 3 && n[0] == 'f' && n[1] == '3') { buf[0]='f'; buf[1]='l'; buf[2]='o'; buf[3]='a'; buf[4]='t'; buf[5]=0; return buf; } // f32
        if (l == 3 && n[0] == 'p') { buf[0]='p'; buf[1]='t'; buf[2]='r'; buf[3]=0; return buf; }                // ptr
        if (l == 4 && n[0] == 'b') { buf[0]='i'; buf[1]='1'; buf[2]=0; return buf; }                            // bool
        // Fall through to slow path for other primitives (iN/uN, str, etc.)
    }
    // r56: slices are fat records { ptr, i64 } (data pointer + length)
    if (t.kind == Nk.NODE_TYPE_SLICE)
    { snprintf(buf, cap, "{ ptr, i64 }"); return buf; }
    // Fast path: pointer types
    if (t.kind == Nk.NODE_TYPE_PTR || t.kind == Nk.NODE_TYPE_REF
        || t.kind == Nk.NODE_TYPE_MUT_REF)
    { buf[0]='p'; buf[1]='t'; buf[2]='r'; buf[3]=0; return buf; }

    // Unfold alias
    // typeof(expr): use the type annotation of the contained expression
    if (t.kind == Nk.NODE_TYPEOF || t.kind == Nk.NODE_TYPEOF_UNQUAL)
    {
        Node* inner = t.child_count >= 1 ? t.children[0] : null;
        if (inner != null && inner.type_annotation != null)
        { return type_to_llvm_buf(inner.type_annotation, buf, cap, depth+1); }
        snprintf(buf, cap, "i64"); return buf;  // fallback
    }
    if (t.kind == Nk.NODE_TYPEVAR && t.resolved != null)
    {
        // Inside a GENERIC_APP expansion (r48): substitute the argument.
        if (g_subst_app != null)
        {
            Node* sm = ast::generic_payload_subst(g_subst_app, t);
            if (sm != null && sm != t)
            { return type_to_llvm_buf(sm, buf, cap, depth + 1); }
        }
        Node* d = t.resolved;
        if (d.kind == Nk.NODE_DECL_ENUM) { snprintf(buf, cap, "{ i32, i64 }"); return buf; }
        // Union reprs (r13): tagged { i32, i64 } when a unit-payload variant
        // exists; a single i64 bitbox for the untagged C-union form.
        if (d.kind == Nk.NODE_DECL_UNION)
        {
            if (ast::union_is_c_union(d)) { snprintf(buf, cap, "i64"); }
            else                          { snprintf(buf, cap, "{ i32, i64 }"); }
            return buf;
        }
        if (d.kind == Nk.NODE_DECL_NEWTYPE && d.child_count >= 2)
        { return type_to_llvm_buf(d.children[1], buf, cap, depth+1); }  // transparent
        if (d.kind == Nk.NODE_DECL_STRUCT)
        {
            // Emit inline struct type: { T0, T1, ... } (avoids LLVM named type declarations)
            snprintf(buf, cap, "{ ");
            // Find the field block (last EXPR_BLOCK child)
            Node* fblk = null;
            for (usz fi = 0; fi < d.child_count; fi++)
            {
                Node* fc = d.children[fi];
                if (fc != null && fc.kind == Nk.NODE_EXPR_BLOCK) { fblk = fc; break; }
            }
            if (fblk != null)
            {
                bool first_field = true;
                for (usz fi = 0; fi < fblk.child_count; fi++)
                {
                    Node* fd = fblk.children[fi];
                    if (fd == null || fd.kind != Nk.NODE_FIELD_DECL || fd.child_count < 2) continue;
                    usz ol = strlen(buf);
                    if (!first_field) { if (ol + 2 < cap) { buf[ol]=','; buf[ol+1]=' '; buf[ol+2]=0; ol += 2; } }
                    first_field = false;
                    // Recurse directly into the remaining caller buffer — no
                    // fixed-size temp (a nested aggregate used to clip at 64
                    // bytes here, emitting unbalanced `{ i64, { ...` type text).
                    if (ol < cap - 1)
                    {
                        type_to_llvm_buf(fd.children[1], buf + ol, cap - ol, depth + 1);
                    }
                }
            }
            usz ol = strlen(buf);
            if (ol + 2 < cap) { buf[ol]=' '; buf[ol+1]='}'; buf[ol+2]=0; }
            return buf;
        }
        if (d.kind == Nk.NODE_DECL_TYPE && d.child_count >= 1)
        {
            Node* body = d.children[d.child_count - 1];
            if (body != null && (body.kind == Nk.NODE_DECL_STRUCT || body.kind == Nk.NODE_DECL_UNION))
            {
                // Inline struct/union type: recurse with the actual struct decl
                return type_to_llvm_buf(body, buf, cap, depth + 1);
            }
            if (body != null)
            {
                return type_to_llvm_buf(body, buf, cap, depth + 1);
            }
        }
    }

    if (t.kind == Nk.NODE_TYPE_PRIMITIVE)
    {
        char* n = t.p.ident.name_ptr; usz l = t.p.ident.name_len;
        // Special keyword types
        if (l==4 && n[0]=='b'&&n[1]=='o'&&n[2]=='o'&&n[3]=='l') { snprintf(buf,cap,"i1");  return buf; } // bool
        if (l==3 && n[0]=='p'&&n[1]=='t'&&n[2]=='r')               { snprintf(buf,cap,"ptr"); return buf; } // ptr
        if (l==3 && n[0]=='s'&&n[1]=='t'&&n[2]=='r')               { snprintf(buf,cap,"{ ptr, i64 }"); return buf; } // str
        if (l==3 && n[0]=='S'&&n[1]=='t'&&n[2]=='r')               { snprintf(buf,cap,"{ ptr, i64 }"); return buf; } // Str (capital)
        if (l==3 && n[0]=='f'&&n[1]=='3'&&n[2]=='2')               { snprintf(buf,cap,"float");  return buf; } // f32
        if (l==3 && n[0]=='f'&&n[1]=='6'&&n[2]=='4')               { snprintf(buf,cap,"double"); return buf; } // f64
        if (l==3 && n[0]=='c'&&n[1]=='h'&&n[2]=='r')               { snprintf(buf,cap,"i32");    return buf; } // chr
        // Arbitrary-width integers: iN and uN where N is a decimal number.
        // Covers i8/u8 through i128/u128 AND bit-precise widths like i7, i24, i48.
        // LLVM supports arbitrary iN types natively — just emit the width.
        if (l >= 2 && (n[0]=='i' || n[0]=='u'))
        {
            // Parse the decimal width
            long w = 0; bool all_digits = true;
            for (usz di = 1; di < l; di++)
            {
                if (n[di] < '0' || n[di] > '9') { all_digits = false; break; }
                w = w * 10 + (long)(n[di] - '0');
            }
            if (all_digits && w >= 1 && w <= 65536)
            {
                snprintf(buf, cap, "i%ld", w); return buf;
            }
        }
        // isize / usize — pointer-sized (64-bit on x86_64)
        if (l==5 && n[0]=='i'&&n[1]=='s'&&n[2]=='i'&&n[3]=='z'&&n[4]=='e') { snprintf(buf,cap,"i64"); return buf; }
        if (l==5 && n[0]=='u'&&n[1]=='s'&&n[2]=='i'&&n[3]=='z'&&n[4]=='e') { snprintf(buf,cap,"i64"); return buf; }
        // Unknown primitive — default to i64
        snprintf(buf,cap,"i64"); return buf;
    }
    // Struct node used directly as a type (e.g., anonymous struct in field or param)
    if (t.kind == Nk.NODE_DECL_STRUCT)
    {
        snprintf(buf, cap, "{ ");
        Node* fblk3 = null;
        for (usz fi3 = 0; fi3 < t.child_count; fi3++)
        {
            Node* fc3 = t.children[fi3];
            if (fc3 != null && fc3.kind == Nk.NODE_EXPR_BLOCK) { fblk3 = fc3; break; }
        }
        if (fblk3 != null)
        {
            bool ff3 = true;
            for (usz fi3 = 0; fi3 < fblk3.child_count; fi3++)
            {
                Node* fd3 = fblk3.children[fi3];
                if (fd3 == null || fd3.kind != Nk.NODE_FIELD_DECL || fd3.child_count < 2) continue;
                usz ol3 = strlen(buf);
                if (!ff3) { if (ol3 + 2 < cap) { buf[ol3]=','; buf[ol3+1]=' '; buf[ol3+2]=0; ol3 += 2; } }
                ff3 = false;
                if (ol3 < cap - 1)
                {
                    type_to_llvm_buf(fd3.children[1], buf + ol3, cap - ol3, depth + 1);
                }
            }
        }
        usz ol3 = strlen(buf); if (ol3 + 2 < cap) { buf[ol3]=' '; buf[ol3+1]='}'; buf[ol3+2]=0; }
        return buf;
    }
    if (t.kind == Nk.NODE_TYPE_SLICE)
    { snprintf(buf,cap,"{ ptr, i64 }"); return buf; }  // r56 fat slice
    if (t.kind == Nk.NODE_TYPE_PTR
     || t.kind == Nk.NODE_TYPE_REF
     || t.kind == Nk.NODE_TYPE_MUT_REF)
    { snprintf(buf,cap,"ptr"); return buf; }
    // Bare union node used directly as a type (via DECL_TYPE recursion):
    if (t.kind == Nk.NODE_DECL_UNION)
    {
        if (ast::union_is_c_union(t)) { snprintf(buf,cap,"i64"); }
        else                          { snprintf(buf,cap,"{ i32, i64 }"); }
        return buf;
    }
    if (t.kind == Nk.NODE_DECL_ENUM)
    { snprintf(buf,cap,"{ i32, i64 }"); return buf; }
    if (t.kind == Nk.NODE_TYPE_FN)
    {
        // fn VALUES are uniformly fat: { ptr code, ptr env }. A named fn gets a
        // trampoline code pointer + null env; a closure carries its real env.
        // (Was "ptr" — a thin code pointer, which silently dropped every
        // closure's captures the moment it flowed through a parameter.)
        snprintf(buf,cap,"{ ptr, ptr }"); return buf;
    }
    if (t.kind == Nk.NODE_EXPR_UNIT
     || t.kind == Nk.NODE_TYPE_BOTTOM
     || t.kind == Nk.NODE_LIT_BOTTOM)
    { snprintf(buf,cap,"void"); return buf; }
    if (t.kind == Nk.NODE_DECL_STRUCT)
    {
        if (t.child_count >= 1 && t.children[0] != null)
        {
            char* nm = t.children[0].p.ident.name_ptr;
            usz   nl = t.children[0].p.ident.name_len;
            snprintf(buf, cap, "%%");
            usz off = strlen(buf);
            if (off + nl < cap) { for (usz i = 0; i < nl; i++) buf[off+i] = nm[i]; buf[off+nl] = 0; }
        }
        return buf;
    }
    if (t.kind == Nk.NODE_TYPE_GENERIC_APP && t.child_count >= 1)
    {
        // Concrete generic-struct instantiation: emit the substituted field
        // record inline (see cg_concrete_struct_app_fblk).  The r48 context
        // lets COMPOUND field types ([T; N], *T, fn…T) substitute too.
        Node* fblk2 = cg_concrete_struct_app_fblk(t);
        if (fblk2 != null)
        {
            Node* prev_app = g_subst_app;
            g_subst_app = t;
            usz off2 = 0;
            if (off2 < cap-2) { buf[off2++] = '{'; buf[off2++] = ' '; }
            bool first2 = true;
            for (usz fi = 0; fi < fblk2.child_count; fi++)
            {
                Node* fd = fblk2.children[fi];
                if (fd == null || fd.kind != Nk.NODE_FIELD_DECL || fd.child_count < 2) continue;
                if (!first2 && off2 < cap-2) { buf[off2++] = ','; buf[off2++] = ' '; }
                first2 = false;
                if (off2 < cap - 1)
                {
                    Node* fty = ast::generic_payload_subst(t, fd.children[1]);
                    type_to_llvm_buf(fty, buf + off2, cap - off2, depth + 1);
                    off2 += strlen(buf + off2);
                }
            }
            g_subst_app = prev_app;
            if (off2 < cap-2) { buf[off2++] = ' '; buf[off2++] = '}'; }
            buf[off2] = 0;
            return buf;
        }
        return type_to_llvm_buf(t.children[0], buf, cap, depth+1);
    }
    if (t.kind == Nk.NODE_TYPE_TUPLE)
    {
        // Tuple → struct.  Build { T0, T1, ... } in buf, recursing directly
        // into the remaining caller buffer (previously each element printed
        // through a 32-byte temp: any nesting deeper than ~4 levels clipped
        // mid-type and emitted UNBALANCED braces → llvm-as rejected the IR).
        usz off = 0;
        if (off < cap-2) { buf[off++] = '{'; buf[off++] = ' '; }
        for (usz i = 0; i < t.child_count && off < cap-4; i++)
        {
            if (i > 0 && off < cap-2) { buf[off++] = ','; buf[off++] = ' '; }
            type_to_llvm_buf(t.children[i], buf + off, cap - off, depth + 1);
            off += strlen(buf + off);
        }
        if (off < cap-2) { buf[off++] = ' '; buf[off++] = '}'; }
        buf[off] = 0;
        return buf;
    }
    if (t.kind == Nk.NODE_TYPE_ARRAY && t.child_count >= 2)
    {
        Node* elem = t.children[0]; Node* sz_node = t.children[1];
        ulong sz_val = (sz_node != null && sz_node.kind == Nk.NODE_LIT_INT) ? sz_node.p.lit_int.int_val : 0;
        char[24] szbuf;
        snprintf(&szbuf[0], 24, "%d", (int)sz_val);
        usz bl = 0;
        if (bl < cap-1) buf[bl++] = '[';
        usz i2 = 0; while (szbuf[i2] && bl < cap-1) buf[bl++] = szbuf[i2++];
        if (bl < cap-1) buf[bl++] = ' ';
        if (bl+1 < cap) { buf[bl++] = 'x'; buf[bl++] = ' '; }
        // Element type: recurse directly into the remaining caller buffer
        // (a 32-byte temp used to clip nested aggregate element types).
        if (bl < cap-1) { type_to_llvm_buf(elem, buf + bl, cap - bl, depth + 1); bl += strlen(buf + bl); }
        if (bl < cap-1) buf[bl++] = ']';
        buf[bl] = 0;
        return buf;
    }
    // Fallback: opaque
    snprintf(buf, cap, "ptr");
    return buf;
}

// Extract the i-th parameter type and the return type from a fn decl's signature.
// param_idx == -1 means: get the return type.
// Decide whether fn_decl's binder EXPLODES a tuple domain into N scalar
// LLVM parameters: true iff the first clause binder is a tuple pattern with
// exactly as many elements as the domain tuple. A single binder (ident,
// wildcard, …) over a tuple domain binds the domain AS ONE aggregate value
// (typecheck's bind_pattern_types stamps the binder with the full tuple
// type) — callers and callees must agree on that ABI or the call site
// marshals an aggregate argument into a mismatching scalar parameter
// (observed: `%arg.c = bitcast { i64, i64 } %x to i32` — invalid IR).
fn bool fn_binder_explodes_tuple(Node* fn_decl, Node* param_t)
{
    if (fn_decl == null || param_t == null) return false;
    if (param_t.kind != Nk.NODE_TYPE_TUPLE) return false;
    // Extern C functions (#extern/#cc(c)) have NO clauses but ALWAYS explode
    // their tuple domain componentwise — they are C functions, each parameter
    // is a separate argument. Previously `clause == null` → false caused their
    // tuple domain to be collapsed into a single aggregate parameter, producing
    // invalid IR (e.g. `call @memcpy({ ptr, ptr, i64 } %agg, ...)`).
    {
        char* ext_check = null; usz ext_check_len = 0;
        if (fn_get_extern_name(fn_decl, &ext_check, &ext_check_len) && ext_check != null)
        { return param_t.child_count >= 1; }
    }
    // A DECL_FN's layout is [name, TYPE_FN signature, body-block]; the
    // Prolog clauses are children OF the body block. (Closures store clauses
    // directly as children.) Find the first clause either way.
    Node* clause = null;
    for (usz i = 0; i < fn_decl.child_count && clause == null; i++)
    {
        Node* ch = fn_decl.children[i];
        if (ch == null) continue;
        if (ch.kind == Nk.NODE_CLAUSE) { clause = ch; break; }
        if (ch.child_count > 0)
        {
            for (usz k = 0; k < ch.child_count; k++)
            {
                Node* cc = ch.children[k];
                if (cc != null && cc.kind == Nk.NODE_CLAUSE) { clause = cc; break; }
            }
        }
    }
    if (clause == null) return false;
    Node* pat = clause.child_count >= 1 ? clause.children[0] : null;
    return pat != null && pat.kind == Nk.NODE_PATTERN_TUPLE
        && pat.child_count == param_t.child_count
        && param_t.child_count >= 1;
}

// Type-level fn-type decomposition for INDIRECT calls through fat fn values:
// the callee then carries no decl, only its `(T... -> U)` type annotation.
// Wire convention: a tuple domain marshals componentwise (the per-fn
// trampoline adapts to the callee's real ABI, packing components when the fn
// binds its tuple domain as one aggregate). param_idx -1 = return type.
fn void fn_type_value_llvm_type(Node* ty, int param_idx, char* buf, usz cap)
{
    buf[0] = 0;
    Node* t = ty;
    if (t != null && t.kind == Nk.NODE_TYPEVAR && t.resolved != null
        && t.resolved.kind == Nk.NODE_DECL_TYPE && t.resolved.child_count >= 1)
    {
        Node* tbody = t.resolved.children[t.resolved.child_count - 1];
        if (tbody != null) t = tbody;
    }
    if (t == null || t.kind != Nk.NODE_TYPE_FN) { snprintf(buf, cap, "i64"); return; }
    Node* lhs = t.child_count >= 1 ? t.children[0] : null;
    Node* rhs = t.child_count >= 2 ? t.children[1] : null;
    Node* dom = lhs; Node* cod = rhs;
    if (rhs != null && rhs.kind == Nk.NODE_EFFECT_ROW
        && lhs != null && lhs.kind == Nk.NODE_TYPE_FN)
    {
        dom = lhs.child_count >= 1 ? lhs.children[0] : null;
        cod = lhs.child_count >= 2 ? lhs.children[1] : null;
    }
    if (param_idx < 0)
    {
        if (cod == null) { snprintf(buf, cap, "i64"); return; }
        type_to_llvm_buf(cod, buf, cap, 0);
        return;
    }
    if (dom != null && dom.kind == Nk.NODE_TYPE_TUPLE)
    {
        if (dom.child_count == 0) { snprintf(buf, cap, "void"); return; }
        if ((usz)param_idx < dom.child_count)
        {
            type_to_llvm_buf(dom.children[param_idx], buf, cap, 0);
            return;
        }
        snprintf(buf, cap, "i64"); return;
    }
    if (param_idx == 0)
    {
        if (dom == null || dom.kind == Nk.NODE_EXPR_UNIT) { snprintf(buf, cap, "void"); return; }
        type_to_llvm_buf(dom, buf, cap, 0);
        return;
    }
    snprintf(buf, cap, "i64");
}

// The fn TYPE node an indirect callee value carries (its src's type
// annotation, sigma-stripped); null when the value has no fn-typed annotation.
fn Node* callee_fn_type(ssi_ir::IrVal* callee_val)
{
    ssi_ir::IrVal* base = callee_val;
    int sc = 0;
    while (base != null && base.op == ssi_ir::IrOp.IR_SIGMA
           && base.arg_count >= 1 && base.args[0] != null && sc < 16)
    { base = base.args[0]; sc++; }
    if (base == null || base.src == null) return null;
    Node* ann = base.src.type_annotation;
    if (ann == null) return null;
    if (ann.kind == Nk.NODE_TYPE_FN) return ann;
    if (ann.kind == Nk.NODE_TYPEVAR && ann.resolved != null
        && ann.resolved.kind == Nk.NODE_DECL_TYPE && ann.resolved.child_count >= 1)
    {
        Node* tb = ann.resolved.children[ann.resolved.child_count - 1];
        if (tb != null && tb.kind == Nk.NODE_TYPE_FN) return tb;
    }
    return null;
}

// Parameter/return type for a call: decl-driven when the callee is a known
// fn, type-level otherwise (indirect fat calls), i64 as last resort.
fn void call_param_type(Node* callee_decl, Node* callee_sig, int idx, char* buf, usz cap)
{
    if (callee_decl != null) { fn_param_llvm_type(callee_decl, idx, buf, cap); return; }
    if (callee_sig != null)  { fn_type_value_llvm_type(callee_sig, idx, buf, cap); return; }
    snprintf(buf, cap, "i64");
}

// The thunk's REAL return type. When typecheck propagated an ascription into
// the closure (`let f : (T -> U) = ...`), the clause bodies carry honest type
// annotations and the thunk can return U directly instead of the generic i64
// bucket — required for the thunk's define header, its TERM_RET coercion and
// every call site to agree byte-for-byte on the result type (LLVM rejects
// `ret i32 %v` when %v was defined by a `call i64`). Unannotated closures
// keep the historical i64 bucket.
fn void closure_thunk_ret_type(Node* clo, char* buf, usz cap)
{
    buf[0] = 0;
    if (clo != null)
    {
        for (usz ci = 0; ci < clo.child_count; ci++)
        {
            Node* cl = clo.children[ci];
            if (cl == null || cl.kind != Nk.NODE_CLAUSE || cl.child_count < 2) continue;
            Node* body = cl.children[cl.child_count - 1];
            if (body != null && body.type_annotation != null)
            {
                type_to_llvm_buf(body.type_annotation, buf, cap, 0);
                if (buf[0] != 0 && !(buf[0] == 'v' && buf[1] == 'o')) { return; }
            }
            // An unannotated clause body that IS another closure literal
            // (currying: `| n -> | x -> x + n`) evaluates to the fat
            // {code, env} record — the typechecker stamps no annotation on
            // an unascribed closure literal, but the record type is certain;
            // the generic i64 fallback would chop the pointer pair in half
            // and break every downstream coercion.
            if (body != null && body.kind == Nk.NODE_EXPR_CLOSURE)
            {
                snprintf(buf, cap, "{ ptr, ptr }");
                return;
            }
        }
    }
    snprintf(buf, cap, "i64");
}

fn void fn_param_llvm_type(Node* fn_decl, int param_idx, char* buf, usz cap)
{
    buf[0] = 0;
    if (fn_decl == null) { snprintf(buf, cap, "i64"); return; }
    // Closure thunk: env pointer is always param 0 → must be ptr.
    // User params read their type from the clause's pattern annotations when
    // typecheck propagated them (e.g. a `let f : (Opt -> i32) = | u -> ...`
    // ascription types u as Opt → the thunk takes the { i32, i64 } repr);
    // unannotated patterns keep the generic i64 fallback.
    if (fn_decl.kind == Nk.NODE_EXPR_CLOSURE)
    {
        if (param_idx == 0) { snprintf(buf, cap, "ptr"); return; }
        if (param_idx < 0)  { closure_thunk_ret_type(fn_decl, buf, cap); return; }
        Node* cpat = null;
        for (usz ci9 = 0; ci9 < fn_decl.child_count; ci9++)
        {
            Node* cl9 = fn_decl.children[ci9];
            if (cl9 != null && cl9.kind == Nk.NODE_CLAUSE && cl9.child_count >= 1)
            { cpat = cl9.children[0]; break; }
        }
        Node* elem_pat = null;
        if (cpat != null && cpat.kind == Nk.NODE_PATTERN_TUPLE
            && (usz)(param_idx - 1) < cpat.child_count) { elem_pat = cpat.children[param_idx - 1]; }
        else if (cpat != null && param_idx == 1) { elem_pat = cpat; }
        if (elem_pat != null && elem_pat.type_annotation != null)
        {
            type_to_llvm_buf(elem_pat.type_annotation, buf, cap, 0);
            if (buf[0] != 0 && !(buf[0] == 'v' && buf[1] == 'o')) return;
        }
        snprintf(buf, cap, "i64"); return;
    }
    // Find the NODE_TYPE_FN child
    Node* sig = null;
    for (usz i = 0; i < fn_decl.child_count; i++)
    {
        Node* c = fn_decl.children[i];
        if (c != null && c.kind == Nk.NODE_TYPE_FN) { sig = c; break; }
    }
    if (sig == null) { snprintf(buf, cap, "i64"); return; }

    // Peel effect-row wrapper: TYPE_FN[innerFN, EFFECT_ROW]
    Node* lhs = sig.child_count >= 1 ? sig.children[0] : null;
    Node* rhs = sig.child_count >= 2 ? sig.children[1] : null;
    Node* param_t = lhs;
    Node* ret_t   = rhs;
    if (rhs != null && rhs.kind == Nk.NODE_EFFECT_ROW
        && lhs != null && lhs.kind == Nk.NODE_TYPE_FN)
    {
        param_t = lhs.child_count >= 1 ? lhs.children[0] : null;
        ret_t   = lhs.child_count >= 2 ? lhs.children[1] : null;
    }

    if (param_idx < 0)
    {
        // Return type
        type_to_llvm_buf(ret_t, buf, cap, 0);
        return;
    }

    // Parameter type: may be a tuple (multi-arg) or a single type.
    // Tuple domain with an EXPLODING binder → per-component scalar params.
    // Tuple domain with a SINGLE binder → ONE aggregate param carrying the
    // whole tuple (the binder IS the aggregate; see fn_binder_explodes_tuple).
    if (param_t != null && param_t.kind == Nk.NODE_TYPE_TUPLE)
    {
        if (param_t.child_count == 0)
        {
            // () unit domain: no value parameter
            snprintf(buf, cap, "void");
            return;
        }
        if (fn_binder_explodes_tuple(fn_decl, param_t))
        {
            if ((usz)param_idx < param_t.child_count)
            {
                type_to_llvm_buf(param_t.children[param_idx], buf, cap, 0);
                return;
            }
        }
        else if (param_idx == 0)
        {
            type_to_llvm_buf(param_t, buf, cap, 0);
            return;
        }
    }
    else if (param_idx == 0)
    {
        type_to_llvm_buf(param_t, buf, cap, 0);
        return;
    }
    snprintf(buf, cap, "i64");
}

// Walk all IrVals for a function, assign canonical LLVM type strings.
// Returns false on OOM.

fn bool infer_fn_types(ssi_ir::SsiModule* ir, ssi_ir::SsiFunc* f, TypeTable* t)
{
    // Step 1: assign types to IR_PARAM values from the fn signature
    for (usz i = 0; i < f.param_count; i++)
    {
        ssi_ir::IrVal* pv = f.params[i];
        if (pv == null) continue;
        char[TYMAP_ENTRY] buf;
        fn_param_llvm_type(f.decl, (int)i, &buf[0], TYMAP_ENTRY);
        t.set(pv.id, &buf[0]);
    }

    // Step 2: walk blocks in order (single pass — φ may reference forward vals,
    // but we handle that in Step 3)
    int last = f.block_start + f.block_count;
    for (int bid = f.block_start; bid < last; bid++)
    {
        ssi_ir::IrBlock* b = ir.blk(bid);
        if (b == null) continue;

        // φ-nodes: determine type from binder annotation (most accurate), then src, then args
        ssi_ir::IrVal* ph = b.phi_head;
        while (ph != null)
        {
            if (t.get(ph.id) == null)
            {
                char[TYMAP_ENTRY] pbuf;
                pbuf[0] = 0;
                bool resolved = false;

                // Priority 1: front-end annotations are authoritative — binder
                // node type_annotation (1a: with DECL_LET/DECL_MUT child walk),
                // then the type stamped on the AST node that spawned the φ
                // (1b). Shared with Step 3 via phi_annotation_type().
                if (!resolved && phi_annotation_type(ph, &pbuf[0], TYMAP_ENTRY))
                { t.set(ph.id, &pbuf[0]); resolved = true; }
                // Priority 2: propagate from first non-i64 arg (so we don't widen to i64)
                if (!resolved)
                {
                    for (usz pk = 0; pk < ph.arg_count && !resolved; pk++)
                    {
                        if (ph.args[pk] == null) continue;
                        // Strip sigma chain before looking up type
                        ssi_ir::IrVal* arg_target = ph.args[pk];
                        int sdepth = 0;
                        while (arg_target != null && arg_target.op == ssi_ir::IrOp.IR_SIGMA
                               && arg_target.arg_count >= 1 && arg_target.args[0] != null
                               && sdepth < 16)
                        { arg_target = arg_target.args[0]; sdepth++; }
                        char* aty = t.get(arg_target.id);
                        // Skip void/unit arm types — phi result can't be void
                        bool aty_void = (aty != null && aty[0]=='v'&&aty[1]=='o'&&aty[2]=='i'&&aty[3]=='d');
                        bool aty_unit = (aty != null && aty[0]=='{'&&aty[1]==' '&&aty[2]=='}');
                        if (aty != null && !aty_void && !aty_unit
                            && !(aty[0]=='i'&&aty[1]=='6'&&aty[2]=='4'&&aty[3]==0))
                        { t.set(ph.id, aty); resolved = true; }
                    }
                }
                // Priority 3: any non-void arg type (strip sigma first)
                if (!resolved && ph.arg_count >= 1 && ph.args[0] != null)
                {
                    ssi_ir::IrVal* arg_t3 = ph.args[0];
                    int sd3 = 0;
                    while (arg_t3 != null && arg_t3.op == ssi_ir::IrOp.IR_SIGMA
                           && arg_t3.arg_count >= 1 && arg_t3.args[0] != null && sd3 < 16)
                    { arg_t3 = arg_t3.args[0]; sd3++; }
                    char* aty = t.get(arg_t3.id);
                    bool p3_void = (aty != null && aty[0]=='v'&&aty[1]=='o'&&aty[2]=='i'&&aty[3]=='d');
                    bool p3_unit = (aty != null && aty[0]=='{'&&aty[1]==' '&&aty[2]=='}');
                    if (aty != null && !p3_void && !p3_unit) { t.set(ph.id, aty); resolved = true; }
                }
                if (!resolved) { t.set(ph.id, (char*)"i64"); }
            }
            ph = ph.next;
        }

        // Instructions
        ssi_ir::IrVal* iv = b.head;
        while (iv != null)
        {
            if (t.get(iv.id) == null)   // skip if already assigned (params)
            {
                char[TYMAP_ENTRY] buf;
                buf[0] = 0;

                // Priority 1: src.type_annotation
                // — EXCEPT the effect ABI values: the IR_HANDLER dispatch token,
                // its arm markers, op performs and resume calls are shaped by the
                // runtime ABI (i64 token, ptr payloads), not by whatever the
                // front-end stamped on the handle expression. The handle's
                // semantic VALUE type is carried by the join φ, not the token —
                // typing the token `{ ptr, ptr }` (a fn-valued computation)
                // corrupts the dispatch switch into `switch { ptr, ptr }`.
                bool effect_abi_op = (iv.op == ssi_ir::IrOp.IR_HANDLER
                    || iv.op == ssi_ir::IrOp.IR_HANDLER_ARM
                    || iv.op == ssi_ir::IrOp.IR_HANDLER_COMPLETE
                    || iv.op == ssi_ir::IrOp.IR_EFFECT_OP
                    || iv.op == ssi_ir::IrOp.IR_RESUME);
                if (!effect_abi_op && iv.src != null && iv.src.type_annotation != null)
                {
                    type_to_llvm_buf(iv.src.type_annotation, &buf[0], TYMAP_ENTRY, 0);
                    // Filter out "void" in non-return position (void can't be a value)
                    if (buf[0] == 'v' && buf[1] == 'o') buf[0] = 0;
                }

                // Priority 1b: a rank ≥ 2 tensor INDEX materialises a
                // headered sub-tensor — its VALUE is a pointer, not the
                // element type synth_index reports (which drops all ranks).
                if (iv.op == ssi_ir::IrOp.IR_INDEX && iv.src != null
                    && iv.src.child_count >= 1 && iv.src.children[0] != null
                    && iv.src.children[0].type_annotation != null
                    && iv.src.children[0].type_annotation.kind == Nk.NODE_TYPE_TENSOR
                    && iv.src.children[0].type_annotation.child_count > 2)
                { snprintf(&buf[0], TYMAP_ENTRY, "ptr"); }

                // Priority 1c: an IR_CAST whose src is itself a TYPE node —
                // lower_effect_perform encodes the perform-result coercion by
                // pointing src AT the op's declared return type (deliberately
                // unannotated: the node IS the dst type). Without this the dst
                // collapses to the generic i64 fallback and f64/i32 op results
                // mis-box through the ptr-slot ABI (`mul nsw i64 %p, 4.0`).
                if (buf[0] == 0 && iv.op == ssi_ir::IrOp.IR_CAST && iv.src != null
                    && cast_src_is_type_node(iv.src))
                { type_to_llvm_buf(iv.src, &buf[0], TYMAP_ENTRY, 0); }

                // Priority 2: propagate from operand (for bin/un/sigma/cast)
                if (buf[0] == 0 && iv.arg_count >= 1 && iv.args[0] != null)
                {
                    switch (iv.op)
                    {
                        case ssi_ir::IrOp.IR_BIN:
                            // Comparison ops always produce i1
                            {
                                Tt bop2 = iv.bop;
                                bool is_cmp = (bop2 == Tt.TOKEN_EQEQ || bop2 == Tt.TOKEN_NEQ
                                    || bop2 == Tt.TOKEN_NEQ_UNI
                                    || bop2 == Tt.TOKEN_LT || bop2 == Tt.TOKEN_LTEQ
                                    || bop2 == Tt.TOKEN_GT || bop2 == Tt.TOKEN_GTEQ
                                    || bop2 == Tt.TOKEN_AMPAMP || bop2 == Tt.TOKEN_PIPEPIPE);
                                if (is_cmp) { snprintf(&buf[0], TYMAP_ENTRY, "i1"); }
                                else
                                {
                                    // Prefer the narrower of: the declared type annotation on the
                                    // expression vs the propagated operand type.  This fixes
                                    // wrapping/saturating ops on sub-64-bit types (e.g. i32 +% i32
                                    // should stay i32, not widen to the default i64 literal type).
                                    char* aty = (iv.arg_count >= 1 && iv.args[0] != null)
                                                ? t.get(iv.args[0].id) : null;
                                    // Also check args[1] — use the narrower of the two operand types
                                    char* bty = (iv.arg_count >= 2 && iv.args[1] != null)
                                                ? t.get(iv.args[1].id) : null;
                                    // If one operand is a raw i64 literal (fallback) and the other
                                    // has a more specific type (i8/i16/i32/u8/u16/u32), use the
                                    // specific one.  Comparing: if aty has smaller bit-width, prefer it.
                                    if (aty != null && bty != null && aty[0] == 'i' && bty[0] == 'i')
                                    {
                                        long aw = 0;
                                        long bw = 0;
                                        char* ap2 = aty+1; while(*ap2>='0'&&*ap2<='9'){aw=aw*10+(long)(*ap2-'0');ap2++;}
                                        char* bp2 = bty+1; while(*bp2>='0'&&*bp2<='9'){bw=bw*10+(long)(*bp2-'0');bp2++;}
                                        if (bw > 0 && bw < aw) { aty = bty; }  // prefer narrower
                                    }
                                    if (aty != null) { usz li = 0; while (aty[li] && li < TYMAP_ENTRY-1) { buf[li] = aty[li]; li++; } buf[li] = 0; }
                                }
                            }
                        case ssi_ir::IrOp.IR_UN:
                        case ssi_ir::IrOp.IR_SIGMA:
                            {
                                char* aty = (iv.arg_count >= 1 && iv.args[0] != null) ? t.get(iv.args[0].id) : null;
                                if (aty != null) { usz li = 0; while (aty[li] && li < TYMAP_ENTRY-1) { buf[li] = aty[li]; li++; } buf[li] = 0; }
                            }
                        // IR_CALL Priority 2: use callee fn decl's declared return type.
                        // This prevents the Priority 3 fallback from wrongly assigning "i64"
                        // to calls that return u8/i32/etc.
                        case ssi_ir::IrOp.IR_CALL:
                            {
                                // args[0] = callee (IR_UNKNOWN with .binder = fn decl)
                                ssi_ir::IrVal* callee_iv = iv.arg_count >= 1 ? iv.args[0] : null;
                                Node* fn_decl_iv = (callee_iv != null) ? callee_iv.binder : null;
                                if (fn_decl_iv != null && fn_decl_iv.kind == Nk.NODE_DECL_FN)
                                {
                                    // fn_param_llvm_type(decl, -1) gives the return type string
                                    fn_param_llvm_type(fn_decl_iv, -1, &buf[0], TYMAP_ENTRY);
                                    // Filter void — calls that return () should still have void tymap
                                    // (void calls are fine; the issue is non-i64 integer returns)
                                }
                                // A call THROUGH a closure value: the callee binder is
                                // the closure literal, whose return type lives in its
                                // clause bodies (currying: a closure returning a
                                // closure yields the fat { ptr, ptr } record — the i64
                                // fallback halves it at every coercion site).
                                if (fn_decl_iv != null && fn_decl_iv.kind == Nk.NODE_EXPR_CLOSURE)
                                {
                                    closure_thunk_ret_type(fn_decl_iv, &buf[0], TYMAP_ENTRY);
                                }
                            }
                        case ssi_ir::IrOp.IR_TUPLE:
                        case ssi_ir::IrOp.IR_ARRAY:
                            // Build struct/array type from component types in the table
                            {
                                usz off = 0;
                                bool is_arr = (iv.op == ssi_ir::IrOp.IR_ARRAY);
                                if (!is_arr)
                                {
                                    // Tuple: { T0, T1, ... }
                                    buf[off++] = '{'; buf[off++] = ' ';
                                    for (usz ai = 0; ai < iv.arg_count && off < TYMAP_ENTRY-8; ai++)
                                    {
                                        if (ai > 0) { buf[off++] = ','; buf[off++] = ' '; }
                                        char* ety = (iv.args[ai] != null) ? t.get(iv.args[ai].id) : null;
                                        if (ety == null || ety[0] == 0) ety = (char*)"i64";
                                        for (usz ei = 0; ety[ei] && off < TYMAP_ENTRY-4; ei++) buf[off++] = ety[ei];
                                    }
                                    buf[off++] = ' '; buf[off++] = '}'; buf[off] = 0;
                                }
                                else
                                {
                                    // Array: [N x ElemType]
                                    char* ety = (iv.arg_count >= 1 && iv.args[0] != null) ? t.get(iv.args[0].id) : null;
                                    if (ety == null || ety[0] == 0) ety = (char*)"i64";
                                    snprintf(&buf[0], TYMAP_ENTRY, "[%d x %s]", (int)iv.arg_count, ety);
                                }
                            }
                        default:
                            break;
                    }
                }

                // Untagged C-union field access (r13): the field REINTERPRETS
                // the i64 bitbox at the payload's type, so the result type is
                // the payload type — never the field-expression annotation
                // (Priority 1) and never the i64 box (Priority 2/3).
                if (buf[0] == 0 && iv.op == ssi_ir::IrOp.IR_FIELD
                    && iv.src != null && iv.src.kind == Nk.NODE_EXPR_FIELD
                    && iv.src.child_count >= 2 && iv.arg_count >= 1
                    && iv.args[0] != null)
                {
                    Node* udecl3 = null;
                    for (int usrc2 = 0; usrc2 < 2 && udecl3 == null; usrc2++)
                    {
                        Node* bt6 = null;
                        if (usrc2 == 0)
                        {
                            if (iv.args[0].src != null)
                            { bt6 = iv.args[0].src.type_annotation; }
                        }
                        else if (iv.src.children[0] != null)
                        { bt6 = iv.src.children[0].type_annotation; }
                        if (bt6 != null)
                        {
                            if (bt6.kind == Nk.NODE_TYPE_PTR
                                && bt6.child_count >= 1 && bt6.children[0] != null)
                            { bt6 = bt6.children[0]; }
                            udecl3 = ast::union_decl_of(bt6);
                        }
                    }
                    if (udecl3 != null && ast::union_is_c_union(udecl3)
                        && iv.src.children[1] != null)
                    {
                        Node* pay3 = null;
                        int ord3 = ast::union_variant_lookup(udecl3,
                            iv.src.children[1].p.ident.name_ptr,
                            iv.src.children[1].p.ident.name_len, &pay3);
                        if (ord3 >= 0)
                        {
                            type_to_llvm_buf(pay3, &buf[0], TYMAP_ENTRY, 0);
                        }
                    }
                }

                // Priority 3: opcode-based fallback
                if (buf[0] == 0)
                {
                    switch (iv.op)
                    {
                        case ssi_ir::IrOp.IR_CONST_INT:
                            // Use suffix-derived bit width from the literal node (e.g. 0i32 → i32).
                            // Parser now sets lit_int.bits to the actual suffix width (8/16/32/64/128).
                            // If no suffix, bits=64 (default). unsigned suffixes use 'u' prefix in IR name.
                            {
                                char lit_bits = (iv.src != null && iv.src.kind == Nk.NODE_LIT_INT)
                                                ? iv.src.p.lit_int.bits : (char)64;
                                bool lit_signed = (iv.src != null && iv.src.kind == Nk.NODE_LIT_INT)
                                                  ? iv.src.p.lit_int.is_signed : true;
                                if (lit_bits == 0) lit_bits = 64;
                                // LLVM IR: i8/i16/i32/i64/i128 (no u-prefix; signedness is in instructions)
                                snprintf(&buf[0], TYMAP_ENTRY, "i%d", (int)lit_bits);
                            }
                        case ssi_ir::IrOp.IR_CONST_FLOAT:
                            // Honour the literal's parsed width: `1.0f32` is a
                            // float, anything else the default f64 (v.md §3.4).
                            // Materializing an f32 literal as double is NOT
                            // semantics-preserving — transmute/bitbox consumers
                            // then read a 64-bit box where 32 bits were meant.
                            {
                                char flit_bits = (iv.src != null && iv.src.kind == Nk.NODE_LIT_FLOAT)
                                                 ? iv.src.p.lit_float.bits : (char)64;
                                if (flit_bits == 32) { snprintf(&buf[0], TYMAP_ENTRY, "float"); }
                                else                 { snprintf(&buf[0], TYMAP_ENTRY, "double"); }
                            }
                        case ssi_ir::IrOp.IR_CONST_BOOL:   snprintf(&buf[0], TYMAP_ENTRY, "i1");
                        case ssi_ir::IrOp.IR_CONST_STR:    snprintf(&buf[0], TYMAP_ENTRY, "ptr");
                        case ssi_ir::IrOp.IR_CONST_NULL:   snprintf(&buf[0], TYMAP_ENTRY, "ptr");
                        case ssi_ir::IrOp.IR_CONST_UNIT:   snprintf(&buf[0], TYMAP_ENTRY, "void");
                        case ssi_ir::IrOp.IR_ALLOC:        snprintf(&buf[0], TYMAP_ENTRY, "ptr");
                        case ssi_ir::IrOp.IR_FREE:         snprintf(&buf[0], TYMAP_ENTRY, "void");
                        case ssi_ir::IrOp.IR_RANGE:        snprintf(&buf[0], TYMAP_ENTRY, "{ i64, i64 }");
                        case ssi_ir::IrOp.IR_CALL:         snprintf(&buf[0], TYMAP_ENTRY, "i64");
                        case ssi_ir::IrOp.IR_EFFECT_OP:    snprintf(&buf[0], TYMAP_ENTRY, "ptr");
                        case ssi_ir::IrOp.IR_HANDLER:      snprintf(&buf[0], TYMAP_ENTRY, "i64");
                        case ssi_ir::IrOp.IR_HANDLER_ARM:  snprintf(&buf[0], TYMAP_ENTRY, "ptr");
                        case ssi_ir::IrOp.IR_HANDLER_COMPLETE: snprintf(&buf[0], TYMAP_ENTRY, "void");
                        case ssi_ir::IrOp.IR_RESUME:       snprintf(&buf[0], TYMAP_ENTRY, "ptr");
                        case ssi_ir::IrOp.IR_UNKNOWN:
                            // Closure / named-fn VALUE: uniformly { ptr, ptr }
                            // (code ptr, env ptr) — zero-capture closures and
                            // named fns carry a null env.
                            if (iv.binder != null && iv.binder.kind == Nk.NODE_EXPR_CLOSURE)
                            {
                                snprintf(&buf[0], TYMAP_ENTRY, "{ ptr, ptr }");
                            }
                            else if (iv.binder != null && iv.binder.kind == Nk.NODE_DECL_FN)
                            {
                                // Named function reference used as a value:
                                // fat { trampoline ptr, null env }.
                                snprintf(&buf[0], TYMAP_ENTRY, "{ ptr, ptr }");
                            }
                            else { snprintf(&buf[0], TYMAP_ENTRY, "i64"); }
                        default:                            snprintf(&buf[0], TYMAP_ENTRY, "i64");
                    }
                }

                // sizeof/alignof sentinel: type is i64 (the result of sizeof/alignof)
                if (iv.op == ssi_ir::IrOp.IR_CONST_INT && iv.src != null
                    && (iv.src.kind == Nk.NODE_EXPR_SIZEOF
                        || iv.src.kind == Nk.NODE_EXPR_ALIGNOF))
                {
                    snprintf(&buf[0], TYMAP_ENTRY, "i64");
                }

                t.set(iv.id, &buf[0]);
            }
            iv = iv.next;
        }
    }

    // Step 3: second pass to resolve φ-nodes that referenced forward values
    for (int bid = f.block_start; bid < last; bid++)
    {
        ssi_ir::IrBlock* b = ir.blk(bid);
        if (b == null) continue;
        ssi_ir::IrVal* ph = b.phi_head;
        while (ph != null)
        {
            char* cur = t.get(ph.id);
            if (cur == null || (cur[0] == 'i' && cur[1] == '6'))
            {
                // Annotation-derived types are authoritative: "i64" here may be
                // the fallback sentinel (upgradeable) OR the type the front-end
                // actually stamped (final). Never let the operand scan clobber
                // the latter — e.g. an effect-handle join stamped i64 whose
                // resume-edge operand is ABI-typed ptr would otherwise rot to
                // `phi ptr [ 42, ... ]`.
                char[TYMAP_ENTRY] abuf3;
                if (phi_annotation_type(ph, &abuf3[0], TYMAP_ENTRY))
                {
                    t.set(ph.id, &abuf3[0]);
                    ph = ph.next;
                    continue;
                }
                // Try each arg — strip sigma chains before type lookup
                for (usz k = 0; k < ph.arg_count; k++)
                {
                    if (ph.args[k] == null) continue;
                    ssi_ir::IrVal* at = ph.args[k];
                    int sds3 = 0;
                    while (at != null && at.op == ssi_ir::IrOp.IR_SIGMA
                           && at.arg_count >= 1 && at.args[0] != null && sds3 < 16)
                    { at = at.args[0]; sds3++; }
                    char* aty = t.get(at.id);
                    // Skip void/unit — phi result can never be void.
                    // Skip i64 — step 3 only runs to upgrade from i64, not stay there.
                    bool s3_void = (aty != null && aty[0]=='v'&&aty[1]=='o'&&aty[2]=='i'&&aty[3]=='d');
                    bool s3_unit = (aty != null && aty[0]=='{'&&aty[1]==' '&&aty[2]=='}');
                    bool s3_i64  = (aty != null && aty[0]=='i'&&aty[1]=='6'&&aty[2]=='4'&&aty[3]==0);
                    if (aty != null && !s3_void && !s3_unit && !s3_i64)
                    {
                        t.set(ph.id, aty);
                        break;
                    }
                }
            }
            ph = ph.next;
        }
    }

    return true;
}

// We collect every NODE_DECL_STRUCT referenced by the IR and emit their type
// declarations before any function definitions.

struct StructEntry
{
    Node*  decl;       // NODE_DECL_STRUCT
    char*  name;       // struct name (arena span, null-terminated copy)
    usz    name_len;
}

// We buffer output and flush to the CFile to avoid per-instruction fwrite calls.

struct OutBuf
{
    char*  data;
    usz    pos;
    usz    cap;
    void*  file;   // CFile
}

fn bool OutBuf.init(OutBuf* b, void* f)
{
    b.data = (char*)malloc(MAX_STRBUF);
    if (b.data == null) { return false; }
    b.pos  = 0;
    b.cap  = MAX_STRBUF;
    b.file = f;
    return true;
}

fn void OutBuf.destroy(OutBuf* b)
{
    if (b.data != null) { free((void*)b.data); b.data = null; }
}

fn void OutBuf.flush(OutBuf* b)
{
    if (b.pos > 0 && b.file != null)
    {
        fwrite((void*)b.data, 1, b.pos, b.file);
        b.pos = 0;
    }
}

fn void OutBuf.write(OutBuf* b, char* s, usz len)
{
    if (len == 0) { return; }
    if (b.pos + len >= b.cap) { b.flush(); }
    if (len >= b.cap)
    {
        // Oversized chunk: write directly to avoid buffering
        fwrite((void*)s, 1, len, b.file);
        return;
    }
    // Hot path: memcpy is typically 10x faster than a byte loop (SIMD-vectorised)
    memcpy((void*)(b.data + b.pos), (void*)s, len);
    b.pos += len;
}

fn void OutBuf.writes(OutBuf* b, char* s) @inline
{
    usz len = strlen(s);
    b.write(s, len);
}

// Write with precomputed length — avoids strlen() overhead
fn void OutBuf.writen(OutBuf* b, char* s, usz len) @inline
{
    b.write(s, len);
}

fn void OutBuf.writec(OutBuf* b, char c) @inline
{
    if (b.pos + 1 >= b.cap) { b.flush(); }
    b.data[b.pos] = c;
    b.pos++;
}

fn void OutBuf.writei(OutBuf* b, long v)
{
    char[32] buf;
    int n = snprintf(&buf[0], 32, "%lld", v);
    if (n > 0) { b.write(&buf[0], (usz)n); }
}

fn void OutBuf.writeu(OutBuf* b, ulong v)
{
    char[32] buf;
    int n = snprintf(&buf[0], 32, "%llu", v);
    if (n > 0) { b.write(&buf[0], (usz)n); }
}

fn void OutBuf.writef(OutBuf* b, double v)
{
    // LLVM accepts decimal float literals. Ensure at least one decimal point.
    char[64] buf;
    int n = snprintf(&buf[0], 64, "%.17g", v);
    if (n > 0)
    {
        // Check if result contains '.' or 'e' — if not, append ".0"
        bool has_dot = false;
        for (int i2 = 0; i2 < n; i2++) { if (buf[i2] == '.' || buf[i2] == 'e') { has_dot = true; break; } }
        if (!has_dot && n < 62) { buf[n] = '.'; buf[n+1] = '0'; buf[n+2] = 0; n += 2; }
        b.write(&buf[0], (usz)n);
    }
}


struct CgenModule
{
    ssi_ir::SsiModule* ir;
    ast::AstArena*     arena;

    OutBuf             out;

    StructEntry[MAX_STRUCTS] structs;
    usz                      struct_count;

    // Override-able target strings
    char* datalayout;
    char* triple;

    int   errors;

    // Current function being emitted
    Node* cur_fn_decl;
    char[TYMAP_ENTRY] cur_fn_ret_type;

    // Function name deduplication
    char[256][NAME_BUF] emitted_fn_names;
    usz                 emitted_fn_count;

    // Freestanding mode: no runtime, no libc — for kernels and bare-metal
    bool freestanding;

    // Persistent TypeTable — allocated once, cleared O(1) between functions
    // via generation counter instead of memset. Eliminates 57% instruction overhead.
    TypeTable tymap;
    bool      tymap_initialized;

    // Fat fn-value trampolines (r9 uniform fn ABI): every fn referenced as a
    // VALUE gets a per-fn adapter `@__pride_fptr_<name>(ptr %env, <wire
    // params>)` that forwards to the real (thin, env-less) function, possibly
    // packing type-level tuple-domain components into the fn's real single
    // aggregate parameter. Collected at value materialization, emitted after
    // the function section.
    Node*[TRAMP_CAP] tramp_decls;
    usz              tramp_count;

    // Mutable module-globals (r56d): DECL_MUT nodes whose IR_GLOAD/IR_GSTORE
    // ops reference `@pride.gmut.<k>`. The global definitions are flushed with
    // the string globals at the end of the module.
    Node*[GMUT_CAP] gmut_decls;
    usz             gmut_count;
}

const usz GMUT_CAP = 256;

// r56d: register a mutable module-global, returning its stable index.
fn usz CgenModule.gmut_id(CgenModule* cg, Node* decl)
{
    for (usz i = 0; i < cg.gmut_count; i++)
    { if (cg.gmut_decls[i] == decl) { return i; } }
    if (cg.gmut_count < GMUT_CAP)
    {
        cg.gmut_decls[cg.gmut_count] = decl;
        return cg.gmut_count++;
    }
    return 0;
}

// r56d: the LLVM type of a mutable global, written into buf.  Resolution
// order: the use-site annotation (mono clones keep these on idents), the
// binder pattern's stamp, a direct type child of the decl, the literal
// init's bit width, finally i64.
fn char* CgenModule.gmut_type(CgenModule* cg, Node* decl, Node* use_node,
                              char* buf, usz cap)
{
    buf[0] = 0;
    Node* ua = (use_node != null) ? use_node.type_annotation : null;
    if (ua != null && ua.kind == Nk.NODE_TYPE_PTR && ua.child_count >= 1)
    { ua = ua.children[0]; }
    if (ua != null && (ua.kind == Nk.NODE_TYPE_PRIMITIVE || ua.kind == Nk.NODE_TYPEVAR))
    {
        char* s = type_to_llvm_buf(ua, buf, cap, 0);
        if (s != null && buf[0] != 0) { return s; }
    }
    if (decl != null)
    {
        if (decl.child_count >= 1 && decl.children[0] != null
            && decl.children[0].type_annotation != null)
        {
            Node* pa = decl.children[0].type_annotation;
            if (pa.kind == Nk.NODE_TYPE_PTR && pa.child_count >= 1)
            { pa = pa.children[0]; }
            char* s = type_to_llvm_buf(pa, buf, cap, 0);
            if (s != null && buf[0] != 0) { return s; }
        }
        for (usz i = 0; i < decl.child_count; i++)
        {
            Node* c = decl.children[i];
            if (c == null) continue;
            if (c.kind == Nk.NODE_TYPE_PRIMITIVE || c.kind == Nk.NODE_TYPE_PTR
                || c.kind == Nk.NODE_TYPE_ARRAY || c.kind == Nk.NODE_TYPE_TUPLE
                || c.kind == Nk.NODE_TYPE_SLICE || c.kind == Nk.NODE_TYPE_FN
                || c.kind == Nk.NODE_TYPE_UNION || c.kind == Nk.NODE_TYPE_INTERSECT
                || c.kind == Nk.NODE_TYPEVAR)
            { return type_to_llvm_buf(c, buf, cap, 0); }
            if (c.kind == Nk.NODE_LIT_INT)
            {
                char b2 = c.p.lit_int.bits;
                if (b2 == 8 || b2 == 16 || b2 == 32)
                { snprintf(buf, cap, "i%d", (int)b2); return buf; }
            }
            if (c.kind == Nk.NODE_LIT_FLOAT)
            {
                char b3 = c.p.lit_float.bits;
                if (b3 == 32) { snprintf(buf, cap, "float"); return buf; }
                snprintf(buf, cap, "double"); return buf;
            }
        }
    }
    if (buf[0] == 0) { snprintf(buf, cap, "i64"); }
    return buf;
}

// r56d: coerce an SSA value to the mutable global's storage type.  Emits any
// needed conversion instruction(s) and returns true with the final SSA name
// in nbuf; returns false when no conversion is needed (caller emit_vrefs).
fn bool CgenModule.gmut_coerce(CgenModule* cg, TypeTable* tm, ssi_ir::IrVal* val,
                               char* dst_ty, long vid, char* nbuf, usz ncap)
{
    nbuf[0] = 0;
    char* vty = (tm != null && val != null) ? tm.get(val.id) : null;
    if (vty == null || vty[0] == 0) vty = (char*)"i64";
    bool same = true;
    { char* a = vty; char* b = dst_ty; while (*a != 0 && *a == *b) { a++; b++; }
      if (*a != 0 || *b != 0) same = false; }
    if (same) { return false; }
    int step = 0;
    char[64] cur;
    snprintf(&cur[0], 64, "%s", vty);
    char[64] curname;
    snprintf(&curname[0], 64, "%%v%ld", (long)(val != null ? val.id : 0));
    // ptr <-> int
    if (cur[0] == 'p' && dst_ty[0] != 'p')
    {
        cg.out.writes("  %gc."); cg.out.writei(vid); cg.out.writes(".");
        cg.out.writei(step); cg.out.writes(" = ptrtoint ptr ");
        { if (step == 0) { cg.emit_vref(val); } else { cg.out.writes(&curname[0]); } } cg.out.writes(" to i64\n");
        snprintf(&cur[0], 64, "i64");
        snprintf(&curname[0], 64, "%%gc.%ld.%d", vid, step);
        step++;
    }
    else if (cur[0] != 'p' && cur[0] != 'd' && cur[0] != 'f' && dst_ty[0] == 'p')
    {
        if (!(cur[0] == 'i' && cur[1] == '6' && cur[2] == '4'))
        {
            cg.out.writes("  %gc."); cg.out.writei(vid); cg.out.writes(".");
            cg.out.writei(step); cg.out.writes(" = zext ");
            cg.out.writes(&cur[0]); cg.out.writes(" ");
            { if (step == 0) { cg.emit_vref(val); } else { cg.out.writes(&curname[0]); } } cg.out.writes(" to i64\n");
            snprintf(&curname[0], 64, "%%gc.%ld.%d", vid, step);
            step++;
        }
        cg.out.writes("  %gc."); cg.out.writei(vid); cg.out.writes(".");
        cg.out.writei(step); cg.out.writes(" = inttoptr i64 ");
        { if (step == 0) { cg.emit_vref(val); } else { cg.out.writes(&curname[0]); } } cg.out.writes(" to ptr\n");
        snprintf(&cur[0], 64, "ptr");
        snprintf(&curname[0], 64, "%%gc.%ld.%d", vid, step);
        step++;
    }
    // int width
    if (cur[0] == 'i' && dst_ty[0] == 'i')
    {
        long cn = 0; long dn = 0;
        { char* p = &cur[0] + 1; while (*p >= '0' && *p <= '9') { cn = cn * 10 + (long)(*p - '0'); p++; } }
        { char* p = dst_ty + 1;   while (*p >= '0' && *p <= '9') { dn = dn * 10 + (long)(*p - '0'); p++; } }
        if (cn > 0 && dn > 0 && cn != dn)
        {
            cg.out.writes("  %gc."); cg.out.writei(vid); cg.out.writes(".");
            cg.out.writei(step);
            cg.out.writes(cn > dn ? " = trunc " : " = zext ");
            cg.out.writes(&cur[0]); cg.out.writes(" ");
            { if (step == 0) { cg.emit_vref(val); } else { cg.out.writes(&curname[0]); } } cg.out.writes(" to ");
            cg.out.writes(dst_ty); cg.out.writes("\n");
            snprintf(&cur[0], 64, "%s", dst_ty);
            snprintf(&curname[0], 64, "%%gc.%ld.%d", vid, step);
            step++;
        }
    }
    // float width / int<->float
    if (cur[0] == 'f' && dst_ty[0] == 'd')
    {
        cg.out.writes("  %gc."); cg.out.writei(vid); cg.out.writes(".");
        cg.out.writei(step); cg.out.writes(" = fpext float ");
        { if (step == 0) { cg.emit_vref(val); } else { cg.out.writes(&curname[0]); } } cg.out.writes(" to double\n");
        snprintf(&cur[0], 64, "double");
        snprintf(&curname[0], 64, "%%gc.%ld.%d", vid, step);
        step++;
    }
    else if (cur[0] == 'd' && dst_ty[0] == 'f')
    {
        cg.out.writes("  %gc."); cg.out.writei(vid); cg.out.writes(".");
        cg.out.writei(step); cg.out.writes(" = fptrunc double ");
        { if (step == 0) { cg.emit_vref(val); } else { cg.out.writes(&curname[0]); } } cg.out.writes(" to float\n");
        snprintf(&cur[0], 64, "float");
        snprintf(&curname[0], 64, "%%gc.%ld.%d", vid, step);
        step++;
    }
    else if (cur[0] == 'i' && (dst_ty[0] == 'd' || dst_ty[0] == 'f'))
    {
        cg.out.writes("  %gc."); cg.out.writei(vid); cg.out.writes(".");
        cg.out.writei(step); cg.out.writes(" = sitofp ");
        cg.out.writes(&cur[0]); cg.out.writes(" ");
        { if (step == 0) { cg.emit_vref(val); } else { cg.out.writes(&curname[0]); } } cg.out.writes(" to ");
        cg.out.writes(dst_ty); cg.out.writes("\n");
        snprintf(&cur[0], 64, "%s", dst_ty);
        snprintf(&curname[0], 64, "%%gc.%ld.%d", vid, step);
        step++;
    }
    else if ((cur[0] == 'd' || cur[0] == 'f') && dst_ty[0] == 'i')
    {
        cg.out.writes("  %gc."); cg.out.writei(vid); cg.out.writes(".");
        cg.out.writei(step); cg.out.writes(" = fptosi ");
        cg.out.writes(&cur[0]); cg.out.writes(" ");
        { if (step == 0) { cg.emit_vref(val); } else { cg.out.writes(&curname[0]); } } cg.out.writes(" to ");
        cg.out.writes(dst_ty); cg.out.writes("\n");
        snprintf(&cur[0], 64, "%s", dst_ty);
        snprintf(&curname[0], 64, "%%gc.%ld.%d", vid, step);
        step++;
    }
    snprintf(nbuf, ncap, "%s", &curname[0]);
    return step > 0;
}

// r56d: the constant initializer text of a mutable global (literal child).
fn void CgenModule.gmut_init_text(CgenModule* cg, Node* decl, char* buf, usz cap)
{
    buf[0] = 0;
    Node* init = null;
    if (decl != null)
    {
        for (usz i = 0; i < decl.child_count; i++)
        {
            Node* c = decl.children[i];
            if (c == null) continue;
            if (c.kind == Nk.NODE_LIT_INT || c.kind == Nk.NODE_LIT_BOOL
                || c.kind == Nk.NODE_LIT_FLOAT || c.kind == Nk.NODE_LIT_CHAR
                || c.kind == Nk.NODE_LIT_NULL)
            { init = c; }
        }
    }
    if (init != null)
    {
        if (init.kind == Nk.NODE_LIT_INT)
        { snprintf(buf, cap, "%lld", (long)init.p.lit_int.int_val); return; }
        if (init.kind == Nk.NODE_LIT_FLOAT)
        {
            // Exact bit-pattern hex — LLVM takes 0xHHHH for double/float.
            double dv = init.p.lit_float.f64_val;
            ulong bits = *(ulong*)(&dv);
            snprintf(buf, cap, "0x%llx", bits);
            return;
        }
        if (init.kind == Nk.NODE_LIT_BOOL)
        { snprintf(buf, cap, "%d", init.p.lit_bool.bool_val ? 1 : 0); return; }
        if (init.kind == Nk.NODE_LIT_CHAR)
        { snprintf(buf, cap, "%u", (uint)init.p.lit_char.char_val); return; }
    }
    snprintf(buf, cap, "0");
}

// r56d: flush @pride.gmut.<k> definitions (called with string globals, BEFORE
// the function bodies — LLVM globals must be defined before their uses, so the
// IR is pre-scanned here rather than lazily registered at instruction time).
fn void CgenModule.emit_gmut_globals(CgenModule* cg)
{
    ssi_ir::SsiModule* m = cg.ir;
    if (m != null)
    {
        for (usz i = 0; i < m.val_count; i++)
        {
            ssi_ir::IrVal* v = &m.vals[i];
            if (v.op == ssi_ir::IrOp.IR_GLOAD || v.op == ssi_ir::IrOp.IR_GSTORE)
            { cg.gmut_id(v.src); }
        }
    }
    for (usz i = 0; i < cg.gmut_count; i++)
    {
        Node* decl = cg.gmut_decls[i];
        // Find a use-site binder (GLOAD/GSTORE) for the tightest annotation.
        Node* useb = null;
        if (m != null)
        {
            for (usz vi = 0; vi < m.val_count; vi++)
            {
                ssi_ir::IrVal* v2 = &m.vals[vi];
                if ((v2.op == ssi_ir::IrOp.IR_GLOAD || v2.op == ssi_ir::IrOp.IR_GSTORE)
                    && v2.src == decl && v2.binder != null)
                { useb = v2.binder; break; }
            }
        }
        char[TYMAP_ENTRY] tyb;
        char* ty = cg.gmut_type(decl, useb, &tyb[0], TYMAP_ENTRY);
        char[64] initb;
        cg.gmut_init_text(decl, &initb[0], 64);
        cg.out.writes("@pride.gmut.");
        cg.out.writeu(i);
        cg.out.writes(" = internal global ");
        cg.out.writes(ty);
        cg.out.writes(" ");
        cg.out.writes(&initb[0]);
        cg.out.writes("\n");
    }
}

const usz TRAMP_CAP = 512;

// Priority-1 φ typing, shared by infer_fn_types' pre-pass AND the Step-3
// forward-value re-resolution: a type the front-end actually ANNOTATED (on the
// φ's binder or on its originating AST node) is authoritative and must win
// over every operand-scan heuristic. "i64" is both a real type AND the
// fallback sentinel — without this guard, Step 3 clobbers honestly-i64 phis
// (e.g. an effect-handle join whose computation is unannotated but whose
// HANDLE node was stamped i64 by the checker) with whatever operand type it
// finds first — the resume ABI's ptr — producing `phi ptr [ 42, ... ]`.
fn bool phi_annotation_type(ssi_ir::IrVal* ph, char* pbuf, usz cap)
{
    if (ph == null) return false;
    // 1a: binder type annotation (with DECL_LET/DECL_MUT child walk)
    if (ph.binder != null)
    {
        Node* binder_ty_node = ph.binder.type_annotation;
        // If binder is DECL_LET/DECL_MUT, look for type annotation on children
        if (binder_ty_node == null
            && (ph.binder.kind == Nk.NODE_DECL_MUT || ph.binder.kind == Nk.NODE_DECL_LET))
        {
            // children[0] is the pattern, check its type_annotation
            if (ph.binder.child_count >= 1 && ph.binder.children[0] != null)
            { binder_ty_node = ph.binder.children[0].type_annotation; }
            // Also check explicit type children (index 1+): type nodes
            for (usz bci = 1; bci < ph.binder.child_count && binder_ty_node == null; bci++)
            {
                Node* bc = ph.binder.children[bci];
                if (bc == null) continue;
                // Inline is_type_node: check for NODE_TYPE_* kinds
                bool bc_is_type = (bc.kind == Nk.NODE_TYPE_PRIMITIVE
                    || bc.kind == Nk.NODE_TYPE_PTR
                    || bc.kind == Nk.NODE_TYPE_FN
                    || bc.kind == Nk.NODE_TYPE_TUPLE
                    || bc.kind == Nk.NODE_TYPE_ARRAY
                    || bc.kind == Nk.NODE_TYPE_UNION
                    || bc.kind == Nk.NODE_TYPE_INTERSECT
                    || bc.kind == Nk.NODE_TYPEVAR
                    || bc.kind == Nk.NODE_EXPR_UNIT);
                if (bc_is_type) { binder_ty_node = bc; break; }
            }
        }
        if (binder_ty_node != null)
        {
            type_to_llvm_buf(binder_ty_node, pbuf, cap, 0);
            // Reject "ptr" from union/complex types (fallback type) as phi type.
            // It will be overridden by arm type inference below.
            bool binder_ty_ok = (pbuf[0] != 0 && pbuf[0] != 'v' && pbuf[0] != 'p');
            // Allow ptr if binder annotation IS a real pointer type
            if (pbuf[0] == 'p' && binder_ty_node.kind == Nk.NODE_TYPE_PTR)
            { binder_ty_ok = true; }
            // Inline-array binder: the loop/branch-carried VALUE is its
            // storage POINTER (IR_ARRAY's contract — array values are ptrs),
            // never a [N x T] register aggregate, so the phi must be typed
            // ptr or the [N x T] text mismatches every operand (r49).
            if (binder_ty_node.kind == Nk.NODE_TYPE_ARRAY)
            { snprintf(pbuf, cap, "ptr"); binder_ty_ok = true; }
            if (binder_ty_ok) { return true; }
        }
    }
    // 1b: src.type_annotation (the AST node that spawned the phi)
    // Same rejection as 1a: skip ptr/union-fallback types.
    if (ph.src != null && ph.src.type_annotation != null)
    {
        type_to_llvm_buf(ph.src.type_annotation, pbuf, cap, 0);
        bool src_ty_ok = (pbuf[0] != 0 && pbuf[0] != 'v' && pbuf[0] != 'p');
        // Allow ptr if src annotation IS a real pointer type
        if (pbuf[0] == 'p' && ph.src.type_annotation.kind == Nk.NODE_TYPE_PTR)
        { src_ty_ok = true; }
        if (src_ty_ok) { return true; }
    }
    return false;
}

// Mirror of ssi's is_type_or_row restricted to the kinds type_to_llvm_buf
// lowers — codegen deliberately doesn't import module ssi. Used only to
// recognise an IR_CAST whose src encodes the destination TYPE directly
// (effect-perform result coercions from lower_effect_perform).
fn bool cast_src_is_type_node(Node* n)
{
    if (n == null) return false;
    switch (n.kind)
    {
        case Nk.NODE_TYPE_PRIMITIVE:
        case Nk.NODE_TYPE_PATH:
        case Nk.NODE_TYPE_PTR:
        case Nk.NODE_TYPE_REF:
        case Nk.NODE_TYPE_MUT_REF:
        case Nk.NODE_TYPE_ARRAY:
        case Nk.NODE_TYPE_SLICE:
        case Nk.NODE_TYPE_TUPLE:
        case Nk.NODE_TYPE_FN:
        case Nk.NODE_TYPE_UNION:
        case Nk.NODE_TYPE_INTERSECT:
        case Nk.NODE_TYPE_GENERIC_APP:
        case Nk.NODE_TYPE_TENSOR:
            return true;
        default:
            return false;
    }
}

const usz TYMAP_ENTRY = 256;  // bytes per entry — must hold fully-expanded
                              // nested aggregate types ({ i64, { i64, ... } })

// TypeTable uses a generation counter for O(1) "clear".
// Increment gen instead of zeroing — valid entries have gen[id] == current_gen.
struct TypeTable
{
    char*   data;       // heap: val_count * TYMAP_ENTRY bytes (types)
    uint*   gens;       // heap: val_count * 4 bytes (generation stamps)
    usz     val_count;
    uint    current_gen;
}

fn bool TypeTable.init(TypeTable* t, usz val_count)
{
    t.val_count = val_count;
    t.current_gen = 1;
    if (val_count == 0) { t.data = null; t.gens = null; return true; }
    t.data = (char*)malloc(val_count * TYMAP_ENTRY);
    if (t.data == null) { return false; }
    t.gens = (uint*)malloc(val_count * 4);
    if (t.gens == null) { free((void*)t.data); t.data = null; return false; }
    // Use memset instead of byte loop — 64x faster on large tables
    memset((void*)t.data, 0, val_count * TYMAP_ENTRY);
    memset((void*)t.gens, 0, val_count * 4);
    return true;
}

// Clear all entries in O(1) by incrementing the generation counter.
// No memset needed — stale entries are simply ignored.
fn void TypeTable.clear(TypeTable* t)
{
    t.current_gen++;
    if (t.current_gen == 0) {
        // Wraparound: reset generations fully (extremely rare)
        t.current_gen = 1;
        if (t.gens != null) memset((void*)t.gens, 0, t.val_count * 4);
    }
}

fn void TypeTable.destroy(TypeTable* t)
{
    if (t.data != null) { free((void*)t.data); t.data = null; }
    if (t.gens != null) { free((void*)t.gens); t.gens = null; }
}

fn char* TypeTable.entry(TypeTable* t, int id) @inline
{
    if (t.data == null || id < 0 || (usz)id >= t.val_count) return null;
    return t.data + (usz)id * TYMAP_ENTRY;
}

fn void TypeTable.set(TypeTable* t, int id, char* type_str) @inline
{
    if (t.data == null || id < 0 || (usz)id >= t.val_count || type_str == null) return;
    char* e = t.data + (usz)id * TYMAP_ENTRY;
    usz i = 0;
    while (type_str[i] != 0 && i < TYMAP_ENTRY - 1) { e[i] = type_str[i]; i++; }
    e[i] = 0;
    // Stamp this entry with the current generation
    if (t.gens != null) t.gens[(usz)id] = t.current_gen;
}

fn char* TypeTable.get(TypeTable* t, int id) @inline
{
    if (t.data == null || id < 0 || (usz)id >= t.val_count) return null;
    // Check generation: if stale, entry is effectively empty
    if (t.gens != null && t.gens[(usz)id] != t.current_gen) return null;
    char* e = t.data + (usz)id * TYMAP_ENTRY;
    if (e[0] == 0) return null;
    return e;
}

fn bool CgenModule.init(CgenModule* cg, ssi_ir::SsiModule* ir, ast::AstArena* arena, void* file)
{
    cg.ir          = ir;
    cg.arena       = arena;
    cg.struct_count = 0;
    // Select datalayout and triple based on target override
    if (g_target_triple_override != null)
    {
        cg.triple = g_target_triple_override;
        // Detect target from triple prefix
        char* t3 = g_target_triple_override;
        if (t3[0]=='a'&&t3[1]=='a'&&t3[2]=='r'&&t3[3]=='c'&&t3[4]=='h')
        { cg.datalayout = (char*)LLVM_DATALAYOUT_AARCH64; }
        else if (t3[0]=='w'&&t3[1]=='a'&&t3[2]=='s'&&t3[3]=='m'&&t3[4]=='6')
        { cg.datalayout = (char*)LLVM_DATALAYOUT_WASM64; }
        else if (t3[0]=='w'&&t3[1]=='a'&&t3[2]=='s'&&t3[3]=='m'&&t3[4]=='3')
        { cg.datalayout = (char*)LLVM_DATALAYOUT_WASM32; }
        else
        { cg.datalayout = (char*)LLVM_DATALAYOUT; }
    }
    else
    {
        cg.datalayout = (char*)LLVM_DATALAYOUT;
        cg.triple     = (char*)LLVM_TRIPLE;
    }
    cg.errors      = 0;
    cg.emitted_fn_count = 0;
    cg.tramp_count = 0;
    cg.freestanding = g_freestanding;
    cg.tymap_initialized = false;
    return cg.out.init(file);
}

fn void CgenModule.destroy(CgenModule* cg)
{
    cg.out.flush();
    cg.out.destroy();
    if (cg.tymap_initialized) { cg.tymap.destroy(); }
}

fn int CgenModule.error_count(CgenModule* cg) { return cg.errors; }


fn void CgenModule.register_struct(CgenModule* cg, Node* decl)
{
    if (decl == null) { return; }
    // Deduplicate
    for (usz i = 0; i < cg.struct_count; i++)
    {
        if (cg.structs[i].decl == decl) { return; }
    }
    if (cg.struct_count >= MAX_STRUCTS) { return; }
    StructEntry* e = &cg.structs[cg.struct_count];
    e.decl = decl;
    // Name is child[0] (TYPEVAR or IDENT)
    if (decl.child_count >= 1)
    {
        Node* nm = decl.children[0];
        if (nm != null)
        {
            e.name     = nm.p.ident.name_ptr;
            e.name_len = nm.p.ident.name_len;
        }
    }
    cg.struct_count++;
}

// Collect all struct declarations referenced by a type node.
fn void CgenModule.collect_structs_from_type(CgenModule* cg, Node* t)
{
    if (t == null) { return; }
    if (t.kind == Nk.NODE_TYPEVAR || t.kind == Nk.NODE_IDENT)
    {
        if (t.resolved != null && t.resolved.kind == Nk.NODE_DECL_STRUCT)
        {
            cg.register_struct(t.resolved);
        }
    }
    if (t.kind == Nk.NODE_TYPE_GENERIC_APP && t.child_count >= 1)
    {
        Node* head = t.children[0];
        if (head != null && head.resolved != null
            && head.resolved.kind == Nk.NODE_DECL_STRUCT)
        {
            cg.register_struct(head.resolved);
        }
    }
    for (usz i = 0; i < t.child_count; i++)
    {
        cg.collect_structs_from_type(t.children[i]);
    }
}

// Walk all IrVal type_annotations and src nodes to collect struct types.
fn void CgenModule.collect_all_structs(CgenModule* cg)
{
    ssi_ir::SsiModule* m = cg.ir;
    for (usz i = 0; i < m.val_count; i++)
    {
        ssi_ir::IrVal* v = &m.vals[i];
        if (v.src != null)
        {
            // Collect from the value's AST source node's type annotation
            if (v.src.type_annotation != null)
            {
                cg.collect_structs_from_type(v.src.type_annotation);
            }
        }
        if (v.binder != null && v.binder.kind == Nk.NODE_DECL_STRUCT)
        {
            cg.register_struct(v.binder);
        }
    }
    // Also collect from function signatures
    for (usz fi = 0; fi < m.func_count; fi++)
    {
        ssi_ir::SsiFunc* f = &m.funcs[fi];
        if (f.decl != null)
        {
            for (usz ci = 0; ci < f.decl.child_count; ci++)
            {
                cg.collect_structs_from_type(f.decl.children[ci]);
            }
        }
    }
}


// Emit the LLVM type string for a Pride type node into the output buffer.
// depth guards against infinite recursion on cyclic type aliases.
fn void CgenModule.emit_type(CgenModule* cg, Node* t, bool in_ret_pos, int depth)
{
    // Depth guard: cyclic/pathological alias chains → fall back to i64 (consistent with type_to_llvm_buf)
    if (depth > 16) { cg.out.writes("i64"); return; }

    if (t == null)
    {
        if (in_ret_pos) { cg.out.writes("void"); } else { cg.out.writes("i64"); }
        return;
    }

    // Inside a GENERIC_APP expansion (r48): substitute typevar leaves.
    if (t.kind == Nk.NODE_TYPEVAR && g_subst_app != null)
    {
        Node* sm2 = ast::generic_payload_subst(g_subst_app, t);
        if (sm2 != null && sm2 != t)
        { cg.emit_type(sm2, in_ret_pos, depth + 1); return; }
    }

    // Unfold type aliases one level
    if (t.kind == Nk.NODE_TYPEVAR && t.resolved != null)
    {
        Node* d = t.resolved;
        if (d.kind == Nk.NODE_DECL_TYPE && d.child_count >= 1)
        {
            Node* body = d.children[d.child_count - 1];
            if (body != null && body.kind != Nk.NODE_DECL_STRUCT
                && body.kind != Nk.NODE_DECL_UNION)
            {
                cg.emit_type(body, in_ret_pos, depth + 1);
                return;
            }
        }
        // Newtype: transparent — same LLVM type as wrapped type.
        if (d.kind == Nk.NODE_DECL_NEWTYPE && d.child_count >= 2)
        {
            cg.emit_type(d.children[1], in_ret_pos, depth + 1);
            return;
        }
        if (d.kind == Nk.NODE_DECL_ENUM)
        {
            cg.out.writes("{ i32, i64 }");
            return;
        }
        if (d.kind == Nk.NODE_DECL_UNION)
        {
            if (ast::union_is_c_union(d)) { cg.out.writes("i64"); }
            else                          { cg.out.writes("{ i32, i64 }"); }
            return;
        }
        if (d.kind == Nk.NODE_DECL_STRUCT)
        {
            cg.register_struct(d);
            cg.out.writes("%");
            if (d.child_count >= 1 && d.children[0] != null)
            {
                cg.out.write(d.children[0].p.ident.name_ptr,
                             d.children[0].p.ident.name_len);
            }
            return;
        }
    }

    switch (t.kind)
    {
        case Nk.NODE_TYPE_PRIMITIVE:
            {
                char* n = t.p.ident.name_ptr;
                usz   l = t.p.ident.name_len;
                if (l == 2 && n[0] == 'i' && n[1] == '8')  { cg.out.writes("i8");     return; }
                if (l == 2 && n[0] == 'u' && n[1] == '8')  { cg.out.writes("i8");     return; }
                if (l == 3 && n[0] == 'i' && n[1] == '1')  { cg.out.writes("i16");    return; }
                if (l == 3 && n[0] == 'u' && n[1] == '1')  { cg.out.writes("i16");    return; }
                if (l == 3 && n[0] == 'i' && n[1] == '3')  { cg.out.writes("i32");    return; }
                if (l == 3 && n[0] == 'u' && n[1] == '3')  { cg.out.writes("i32");    return; }
                if (l == 3 && n[0] == 'i' && n[1] == '6')  { cg.out.writes("i64");    return; }
                if (l == 3 && n[0] == 'u' && n[1] == '6')  { cg.out.writes("i64");    return; }
                if (l == 4 && n[0] == 'i' && n[1] == '1' && n[2] == '2') { cg.out.writes("i128");   return; } // i128
                if (l == 4 && n[0] == 'u' && n[1] == '1' && n[2] == '2') { cg.out.writes("i128");   return; } // u128
                if (l == 5 && n[0] == 'i' && n[1] == 's') { cg.out.writes("i64");    return; } // isize=i64 on x86_64
                if (l == 5 && n[0] == 'u' && n[1] == 's') { cg.out.writes("i64");    return; } // usize=i64 on x86_64
                if (l == 3 && n[0] == 'f' && n[1] == '3')  { cg.out.writes("float");  return; }
                if (l == 3 && n[0] == 'f' && n[1] == '6')  { cg.out.writes("double"); return; }
                if (l == 4 && n[0] == 'b')                  { cg.out.writes("i1");     return; }
                if (l == 3 && n[0] == 'p')                  { cg.out.writes("ptr");    return; }
                if (l == 4 && n[0] == 'c')                  { cg.out.writes("i32");    return; } // char
                // Str = { ptr, i64 }
                if (l == 3 && n[0] == 'S')                  { cg.out.writes("{ ptr, i64 }"); return; }
                // Fallback
                cg.out.writes("i64");
            }
        case Nk.NODE_TYPE_SLICE:
            cg.out.writes("{ ptr, i64 }");  // r56 fat slice

        case Nk.NODE_TYPE_PTR:
        case Nk.NODE_TYPE_REF:
        case Nk.NODE_TYPE_MUT_REF:
            cg.out.writes("ptr");

        case Nk.NODE_TYPE_ARRAY:
            // [T; N] — child[0]=element type, child[1]=size literal
            cg.out.writes("[");
            if (t.child_count >= 2 && t.children[1] != null
                && t.children[1].kind == Nk.NODE_LIT_INT)
            {
                cg.out.writeu(t.children[1].p.lit_int.int_val);
            }
            else { cg.out.writes("0"); }
            cg.out.writes(" x ");
            if (t.child_count >= 1) { cg.emit_type(t.children[0], false, depth + 1); }
            else { cg.out.writes("i8"); }
            cg.out.writes("]");

        case Nk.NODE_TYPE_TUPLE:
            // (A, B, ...) → { A, B, ... }
            cg.out.writes("{ ");
            for (usz i = 0; i < t.child_count; i++)
            {
                if (i > 0) { cg.out.writes(", "); }
                cg.emit_type(t.children[i], false, depth + 1);
            }
            cg.out.writes(" }");

        case Nk.NODE_TYPE_FN:
            // Function types: always `ptr` (opaque function pointer)
            cg.out.writes("ptr");

        case Nk.NODE_EXPR_UNIT:
        case Nk.NODE_TYPE_BOTTOM:
        case Nk.NODE_LIT_BOTTOM:
            if (in_ret_pos) { cg.out.writes("void"); } else { cg.out.writes("{}"); }

        case Nk.NODE_DECL_ENUM:
            // Enum: { i32 tag, i64 payload } — simple uniform representation.
            // Tag identifies variant; payload holds up to 64-bit data.
            cg.out.writes("{ i32, i64 }");

        case Nk.NODE_DECL_UNION:
            if (ast::union_is_c_union(t)) { cg.out.writes("i64"); }
            else                          { cg.out.writes("{ i32, i64 }"); }

        case Nk.NODE_TYPE_UNION:
        case Nk.NODE_TYPE_INTERSECT:
            if (t.child_count >= 1 && t.children[0] != null) { cg.emit_type(t.children[0], in_ret_pos, depth + 1); }
            else { cg.out.writes("i64"); }

        case Nk.NODE_DECL_STRUCT:
            cg.register_struct(t);
            cg.out.writes("%");
            if (t.child_count >= 1 && t.children[0] != null)
            {
                cg.out.write(t.children[0].p.ident.name_ptr,
                             t.children[0].p.ident.name_len);
            }

        case Nk.NODE_TYPE_GENERIC_APP:
            // Concrete generic-struct instantiation: emit the substituted
            // field record inline (see cg_concrete_struct_app_fblk); a still-
            // generic app keeps the boxed head repr.
            Node* fblk9 = cg_concrete_struct_app_fblk(t);
            if (fblk9 != null)
            {
                Node* prev_app9 = g_subst_app;
                g_subst_app = t;
                cg.out.writes("{ ");
                bool first9 = true;
                for (usz fi = 0; fi < fblk9.child_count; fi++)
                {
                    Node* fd = fblk9.children[fi];
                    if (fd == null || fd.kind != Nk.NODE_FIELD_DECL || fd.child_count < 2) continue;
                    if (!first9) { cg.out.writes(", "); }
                    first9 = false;
                    cg.emit_type(ast::generic_payload_subst(t, fd.children[1]), false, depth + 1);
                }
                g_subst_app = prev_app9;
                cg.out.writes(" }");
            }
            else if (t.child_count >= 1)
            {
                cg.emit_type(t.children[0], in_ret_pos, depth + 1);
            }
            else { cg.out.writes("ptr"); }

        default:
            cg.out.writes("i64");   // conservative fallback for unknown/lattice types
    }
}

// Emit the LLVM type for an IrVal based on its type_annotation (preferred)
// or a conservative fallback.
fn void CgenModule.emit_val_type(CgenModule* cg, ssi_ir::IrVal* v, bool in_ret)
{
    if (v == null)
    {
        if (in_ret) { cg.out.writes("void"); } else { cg.out.writes("i64"); }
        return;
    }
    // Use the source node's type annotation if available
    Node* ann = (v.src != null) ? v.src.type_annotation : null;
    if (ann != null)
    {
        cg.emit_type(ann, in_ret, 0);
        return;
    }
    // Fallback by opcode
    switch (v.op)
    {
        case ssi_ir::IrOp.IR_CONST_INT:    cg.out.writes("i64");
        case ssi_ir::IrOp.IR_CONST_FLOAT:
            {
                char flit_bits = (v.src != null && v.src.kind == Nk.NODE_LIT_FLOAT)
                                 ? v.src.p.lit_float.bits : (char)64;
                cg.out.writes(flit_bits == 32 ? "float" : "double");
            }
        case ssi_ir::IrOp.IR_CONST_BOOL:   cg.out.writes("i1");
        case ssi_ir::IrOp.IR_CONST_STR:    cg.out.writes("{ ptr, i64 }");
        case ssi_ir::IrOp.IR_CONST_NULL:   cg.out.writes("ptr");
        case ssi_ir::IrOp.IR_CONST_UNIT:
            if (in_ret) { cg.out.writes("void"); } else { cg.out.writes("{}"); }
        case ssi_ir::IrOp.IR_PARAM:        cg.out.writes("i64");
        case ssi_ir::IrOp.IR_ALLOC:        cg.out.writes("ptr");
        case ssi_ir::IrOp.IR_RANGE:        cg.out.writes("{ i64, i64 }");
        default:                            cg.out.writes("i64");
    }
}

// Emit a value reference: %vN
// Transparently substitutes sigma values with their source to handle SASI-swept sigmas.
fn void CgenModule.emit_vref(CgenModule* cg, ssi_ir::IrVal* v)
{
    if (v == null) { cg.out.writes("undef"); return; }
    // If this value is a sigma (possibly swept by SASI), use its source instead.
    // Walk the sigma chain to find the ultimate defined value.
    int sigma_depth = 0;
    while (v != null && v.op == ssi_ir::IrOp.IR_SIGMA
           && v.arg_count >= 1 && v.args[0] != null && sigma_depth < 16)
    {
        v = v.args[0];
        sigma_depth++;
    }
    if (v == null) { cg.out.writes("undef"); return; }
    switch (v.op)
    {
        case ssi_ir::IrOp.IR_CONST_INT:
            // Check for sizeof/alignof sentinel
            if (v.src != null && (v.src.kind == Nk.NODE_EXPR_SIZEOF
                                  || v.src.kind == Nk.NODE_EXPR_ALIGNOF))
            {
                // Compute real size from the type operand using ABI rules
                long szval = 8;
                Node* mtype = v.src.child_count >= 1 ? v.src.children[0] : null;
                if (v.src.kind == Nk.NODE_EXPR_SIZEOF) { szval = sizeof_type_x86(mtype); }
                else                                    { szval = alignof_type_x86(mtype); }
                cg.out.writeu((ulong)szval);
                return;
            }
            cg.out.writeu(v.ival);
        case ssi_ir::IrOp.IR_CONST_FLOAT:
            // `float`-typed literals (f32 suffix) must print at f32 precision:
            // a %.17g double rendering (3.1400000000000001) can OVERFLOW or
            // mis-round the float it is paired with — the type just narrowed,
            // the text must follow it.
            if (v.src != null && v.src.kind == Nk.NODE_LIT_FLOAT
                && v.src.p.lit_float.bits == 32)
            { cg.out.writef((double)(float)v.fval); }
            else { cg.out.writef(v.fval); }
        case ssi_ir::IrOp.IR_CONST_BOOL:
            cg.out.writes(v.bval ? "1" : "0");
        case ssi_ir::IrOp.IR_CONST_NULL:
            cg.out.writes("null");
        case ssi_ir::IrOp.IR_CONST_UNIT:
            cg.out.writes("{}");
        case ssi_ir::IrOp.IR_CONST_STR:
            // String literals are globals; ref by @.str.N
            cg.out.writes("@.str.");
            cg.out.writei(v.id);
        default:
            cg.out.writes("%v");
            cg.out.writei(v.id);
    }
}


// Decoded byte length of a string-literal constant (escape sequences collapse:
// \n is 1 byte, \xHH is 1 byte, \u{...} is 1 encoded unit per seq). Shared by
// emit_string_globals (for the [LEN+1 x i8] global) and the aggregate
// materialisation of a literal in value position (`{ ptr @.str.N, i64 LEN }`).
fn usz str_const_decoded_len(ssi_ir::IrVal* v)
{
    if (v == null || v.sptr == null) return 0;
    // Token span includes surrounding quotes: strip them for content length.
    usz content_start = 0;
    usz content_len = v.slen;
    if (content_len >= 2 && v.sptr[0] == '"' && v.sptr[content_len - 1] == '"')
    {
        content_start = 1;
        content_len  -= 2;
    }
    usz decoded_len = 0;
    usz kk = content_start;
    usz kk_end = content_start + content_len;
    while (kk < kk_end)
    {
        if (v.sptr[kk] == '\\' && kk + 1 < kk_end)
        {
            char ek = v.sptr[kk+1];
            if (ek == 'x' && kk + 3 < kk_end) { kk += 4; }
            else if (ek == 'u') { kk += 2; while (kk < kk_end && v.sptr[kk] != '}') { kk++; } kk++; }
            else { kk += 2; }
            decoded_len++;
        }
        else { kk++; decoded_len++; }
    }
    return decoded_len;
}

// Print the CONSTANT aggregate form of a string literal:
// `{ ptr @.str.N, i64 LEN }`. Required wherever the fat string record is
// used as one value (stored into memory in one piece); emit_vref alone
// renders `@.str.N`, the raw byte-global pointer, which is not a value of
// the record type.
// Recursively read a tensor literal's static shape from its nesting:
// `[| a, b |]` is rank 1 with dims[0] = 2, `[| [|..|], [|..|] |]` adds a
// rank. Writes dims[0..rank) and returns the rank (0 = not a tensor shape
// we can materialise). Ragged shapes are the type checker's error, not
// codegen's — by this point every sibling row has the same length.
fn usz tensor_lit_shape(Node* n, long* dims, usz cap)
{
    if (n == null || cap == 0) return 0;
    Node* c0 = n.child_count >= 1 ? n.children[0] : null;
    if (c0 != null && c0.kind == Nk.NODE_EXPR_TENSOR_LIT && cap > 1)
    {
        usz sub = tensor_lit_shape(c0, dims + 1, cap - 1);
        if (sub == 0) return 0;
        dims[0] = (long)n.child_count;
        return sub + 1;
    }
    dims[0] = (long)n.child_count;
    return 1;
}

fn void cgen_emit_str_const_record(CgenModule* cg, ssi_ir::IrVal* v)
{
    if (v == null || v.op != ssi_ir::IrOp.IR_CONST_STR)
    {
        cg.out.writes("undef");
        return;
    }
    cg.out.writes("{ ptr @.str.");
    cg.out.writei(v.id);
    cg.out.writes(", i64 ");
    cg.out.writeu((ulong)str_const_decoded_len(v));
    cg.out.writes(" }");
}

fn void CgenModule.emit_string_globals(CgenModule* cg)
{
    ssi_ir::SsiModule* m = cg.ir;
    for (usz i = 0; i < m.val_count; i++)
    {
        ssi_ir::IrVal* v = &m.vals[i];
        if (v.op != ssi_ir::IrOp.IR_CONST_STR) { continue; }
        // @.str.N = private unnamed_addr constant [LEN+1 x i8] c"...\00"
        cg.out.writes("@.str.");
        cg.out.writei(v.id);
        // Token span includes surrounding quotes: strip them for content length.
        // sptr[0] = opening ", sptr[slen-1] = closing ", content = sptr[1..slen-2].
        usz content_start = 0;
        usz content_len = v.slen;
        if (content_len >= 2 && v.sptr[0] == '"' && v.sptr[content_len - 1] == '"')
        {
            content_start = 1;
            content_len  -= 2;
        }
        usz decoded_len = str_const_decoded_len(v);
        cg.out.writes(" = private unnamed_addr constant [");
        cg.out.writeu(decoded_len + 1);
        cg.out.writes(" x i8] c\"");
        // Emit string bytes with escape processing (content only, no surrounding quotes).
        // Source string uses C-style escapes: \n \t \r \\ \" \xHH \0
        usz j = content_start;
        usz j_end = content_start + content_len;
        while (j < j_end)
        {
            char c = v.sptr[j];
            if (c == '\\' && j + 1 < j_end)
            {
                j++;
                char esc = v.sptr[j];
                int byte_val = -1;
                if      (esc == 'n')  { byte_val = 10; }
                else if (esc == 't')  { byte_val = 9; }
                else if (esc == 'r')  { byte_val = 13; }
                else if (esc == '0')  { byte_val = 0; }
                else if (esc == '\\') { byte_val = 92; }
                else if (esc == '"')  { byte_val = 34; }
                else if (esc == (char)39) { byte_val = 39; }
                else if (esc == 'a')  { byte_val = 7; }
                else if (esc == 'b')  { byte_val = 8; }
                else if (esc == 'f')  { byte_val = 12; }
                else if (esc == 'v')  { byte_val = 11; }
                else if (esc == 'x' && j + 2 < j_end)
                {
                    char h1 = v.sptr[j+1]; char h2 = v.sptr[j+2];
                    int d1 = (h1>='0'&&h1<='9')?(h1-'0'):(h1>='a'&&h1<='f')?(h1-'a'+10):(h1-'A'+10);
                    int d2 = (h2>='0'&&h2<='9')?(h2-'0'):(h2>='a'&&h2<='f')?(h2-'a'+10):(h2-'A'+10);
                    byte_val = d1*16+d2; j += 2;
                }
                if (byte_val >= 0)
                {  // braced
                    if (byte_val == 34)       { cg.out.writes("\\22"); }
                    else if (byte_val == 92)  { cg.out.writes("\\5C"); }
                    else if (byte_val >= 32 && byte_val < 127 && byte_val != 34)
                    { cg.out.writec((char)byte_val); }
                    else
                    { char[5] hex2; snprintf(&hex2[0], 5, "\\%02X", byte_val); cg.out.writes(&hex2[0]); }
                }
                else
                {
                    // Unknown escape: emit as-is
                    cg.out.writes("\\5C");
                    char[5] hexe; snprintf(&hexe[0], 5, "\\%02X", (int)(esc & 0xFF)); cg.out.writes(&hexe[0]);
                }
            }
            else if (c == '"')       { cg.out.writes("\\22"); }
            else if (c == '\\')     { cg.out.writes("\\5C"); }
            else if (c >= 32 && c < 127) { cg.out.writec(c); }
            else
            {
                char[5] hex;
                snprintf(&hex[0], 5, "\\%02X", (int)(c & 0xFF));
                cg.out.writes(&hex[0]);
            }
            j++;
        }
        cg.out.writes("\\00\"\n");
    }
}


fn void CgenModule.emit_struct_decls(CgenModule* cg)
{
    for (usz i = 0; i < cg.struct_count; i++)
    {
        StructEntry* e = &cg.structs[i];
        Node* decl = e.decl;
        if (decl == null) { continue; }

        // Check for #[packed] attribute on the struct
        bool is_packed = false;
        if (decl != null)
        {
            for (usz pai = 0; pai < decl.child_count; pai++)
            {
                Node* pac = decl.children[pai];
                if (pac == null || pac.kind != Nk.NODE_ATTRIBUTE_LIST) continue;
                for (usz paj = 0; paj < pac.child_count; paj++)
                {
                    Node* pa = pac.children[paj];
                    if (pa == null || pa.child_count < 1 || pa.children[0] == null) continue;
                    char* pan = pa.children[0].p.ident.name_ptr;
                    usz   pal = pa.children[0].p.ident.name_len;
                    if (pal==6&&pan[0]=='p'&&pan[1]=='a'&&pan[2]=='c') { is_packed = true; }
                    if (pal==6&&pan[0]=='e'&&pan[1]=='x'&&pan[2]=='t') { is_packed = true; } // extern = C layout
                }
            }
        }

        cg.out.writes("%");
        cg.out.write(e.name, e.name_len);
        // packed structs use <{ ... }> in LLVM IR
        cg.out.writes(is_packed ? " = type <{ " : " = type { ");

        // Walk the field block (last EXPR_BLOCK child)
        Node* field_block = null;
        for (usz ci = 0; ci < decl.child_count; ci++)
        {
            Node* c = decl.children[ci];
            if (c != null && c.kind == Nk.NODE_EXPR_BLOCK) { field_block = c; }
        }

        bool first = true;
        if (field_block != null)
        {
            for (usz fi = 0; fi < field_block.child_count; fi++)
            {
                Node* fd = field_block.children[fi];
                if (fd == null || fd.kind != Nk.NODE_FIELD_DECL) { continue; }
                Node* ftype = fd.child_count >= 2 ? fd.children[1] : null;
                if (!first) { cg.out.writes(", "); }
                first = false;
                cg.emit_type(ftype, false, 0);
            }
        }

        if (first) { cg.out.writes("i8"); } // empty struct sentinel
        cg.out.writes(is_packed ? " }>\n" : " }\n");
    }
}

// Given a struct decl and a field name, return its 0-based index (-1 if not found).

// Resolve a node that designates a type to the decl that physically carries the
// field block (Struct/Union). Unwraps `type X = struct …` aliases exactly like
// typecheck's struct_fields_of: the alias body is the alias's LAST child when it
// is a Struct/Union node. Returns null when `n` designates no aggregate.
fn Node* struct_body_of(Node* n)
{
    if (n == null) return null;
    if (n.kind == Nk.NODE_DECL_STRUCT || n.kind == Nk.NODE_DECL_UNION) return n;
    // Generic instantiation (`Pair<i64, f64>`): the struct decl lives behind
    // the application's head TypeVar — the same look-through as
    // ast::struct_decl_of (needed so field INDEX lookup works on instantiations).
    if (n.kind == Nk.NODE_TYPE_GENERIC_APP && n.child_count >= 1)
    {
        Node* hd = n.children[0];
        if (hd != null && hd.resolved != null && hd.resolved != n)
        { return struct_body_of(hd.resolved); }
        if (n.resolved != null && n.resolved != n) return struct_body_of(n.resolved);
        return null;
    }
    // TypeVar use → its declaration (which may itself be an alias).
    if (n.kind == Nk.NODE_TYPEVAR && n.resolved != null) return struct_body_of(n.resolved);
    if (n.kind == Nk.NODE_DECL_TYPE && n.child_count >= 1)
    {
        Node* b = n.children[n.child_count - 1];
        if (b != null && (b.kind == Nk.NODE_DECL_STRUCT || b.kind == Nk.NODE_DECL_UNION)) return b;
    }
    return null;
}

fn int field_index_of(Node* struct_decl, char* fname, usz flen)
{
    if (struct_decl == null || fname == null) { return 0; }
    Node* fb = null;
    for (usz i = 0; i < struct_decl.child_count; i++)
    {
        Node* c = struct_decl.children[i];
        if (c != null && c.kind == Nk.NODE_EXPR_BLOCK) { fb = c; }
    }
    if (fb == null) { return 0; }
    int idx = 0;
    for (usz i = 0; i < fb.child_count; i++)
    {
        Node* fd = fb.children[i];
        if (fd == null || fd.kind != Nk.NODE_FIELD_DECL) { continue; }
        Node* fn_name = fd.child_count >= 1 ? fd.children[0] : null;
        if (fn_name == null) { idx++; continue; }
        char* np = fn_name.p.ident.name_ptr;
        usz   nl = fn_name.p.ident.name_len;
        if (nl == flen)
        {
            bool eq = true;
            for (usz j = 0; j < nl; j++) { if (np[j] != fname[j]) { eq = false; break; } }
            if (eq) { return idx; }
        }
        idx++;
    }
    return 0;
}


// Determine the LLVM return type for a function.
fn void CgenModule.emit_fn_ret_type(CgenModule* cg, ssi_ir::SsiFunc* f)
{
    // Closure thunks return the body's honest type when an ascription
    // propagated one, else the generic i64 bucket (see closure_thunk_ret_type).
    if (f.decl != null && f.decl.kind == Nk.NODE_EXPR_CLOSURE)
    {
        char[TYMAP_ENTRY] cret;
        closure_thunk_ret_type(f.decl, &cret[0], TYMAP_ENTRY);
        cg.out.writes(&cret[0]);
        return;
    }
    if (f.decl == null) { cg.out.writes("void"); return; }
    // Find the TYPE_FN child of the decl
    for (usz i = 0; i < f.decl.child_count; i++)
    {
        Node* c = f.decl.children[i];
        if (c == null) { continue; }
        if (c.kind == Nk.NODE_TYPE_FN)
        {
            // Peel effect-row form
            Node* ret = null;
            Node* lhs = c.child_count >= 1 ? c.children[0] : null;
            Node* rhs = c.child_count >= 2 ? c.children[1] : null;
            if (rhs != null && rhs.kind == Nk.NODE_EFFECT_ROW
                && lhs != null && lhs.kind == Nk.NODE_TYPE_FN)
            {
                ret = lhs.child_count >= 2 ? lhs.children[1] : null;
            }
            else { ret = rhs; }
            cg.emit_type(ret, true, 0);
            return;
        }
    }
    cg.out.writes("void");
}

// Emit a mangled global name for a Pride function.
// Extern functions keep their name as-is; Pride functions get @pride_ prefix.
fn void CgenModule.emit_fn_name(CgenModule* cg, ssi_ir::SsiFunc* f)
{
    // Closure thunk: use @__pride_closure_N naming
    if (f.decl != null && f.decl.kind == Nk.NODE_EXPR_CLOSURE)
    {
        // Find the closure IR_UNKNOWN val to get the cid
        ssi_ir::SsiModule* mir = cg.ir;
        for (usz vi2 = 0; vi2 < mir.val_count; vi2++)
        {
            ssi_ir::IrVal* cv2 = &mir.vals[vi2];
            if (cv2.op == ssi_ir::IrOp.IR_UNKNOWN && cv2.binder == f.decl)
            {
                int cid2 = (int)(cv2.ival & 0x7FFFFFFF);
                cg.out.writes("@__pride_closure_");
                cg.out.writei((long)cid2);
                return;
            }
        }
        cg.out.writes("@__pride_closure_0");  // fallback
        return;
    }
    if (f.name == null || f.name_len == 0)
    {
        cg.out.writes("@pride_anon_");
        cg.out.writei(f.entry);
        return;
    }
    bool is_main = span_is(f.name, f.name_len, (char*)"main");
    if (is_main) { cg.out.writes("@main"); return; }

    // Check for #[extern("name")] attribute — use the C symbol name directly
    {
        char* ext_nm = null;
        usz   ext_nl = 0;
        if (f.decl != null && fn_get_extern_name(f.decl, &ext_nm, &ext_nl) && ext_nm != null && ext_nl > 0)
        {
            cg.out.writes("@");
            for (usz ei = 0; ei < ext_nl; ei++) { cg.out.writec(ext_nm[ei]); }
            return;
        }
    }

    // Build the candidate name @pride_NAME
    char[NAME_BUF] candidate;
    snprintf(&candidate[0], NAME_BUF, "@pride_");
    usz off = strlen(&candidate[0]);
    for (usz i = 0; i < f.name_len && off < NAME_BUF-1; i++) candidate[off++] = f.name[i];
    candidate[off] = 0;

    // Check for collision
    bool seen = false;
    for (usz i = 0; i < cg.emitted_fn_count; i++)
    {
        char* e = &cg.emitted_fn_names[i][0];
        if (strlen(e) == strlen(&candidate[0]))
        {
            bool match = true;
            for (usz j = 0; e[j] != 0; j++) { if (e[j] != candidate[j]) { match = false; break; } }
            if (match) { seen = true; break; }
        }
    }
    if (seen)
    {
        // Append entry block id as unique suffix
        snprintf(&candidate[off], NAME_BUF - off, ".%d", f.entry);
    }
    // Register this name
    if (cg.emitted_fn_count < 256)
    {
        char* slot = &cg.emitted_fn_names[cg.emitted_fn_count][0];
        usz cl = strlen(&candidate[0]);
        for (usz i = 0; i < cl && i < NAME_BUF-1; i++) slot[i] = candidate[i];
        slot[cl < NAME_BUF-1 ? cl : NAME_BUF-1] = 0;
        cg.emitted_fn_count++;
    }
    cg.out.writes(&candidate[0]);
}


// Check if a value produces a floating-point result.
// Checks the TypeTable first (accurate), then falls back to AST annotation.
fn bool is_float_val_ty(ssi_ir::IrVal* v, TypeTable* tm)
{
    if (v == null) { return false; }
    if (v.op == ssi_ir::IrOp.IR_CONST_FLOAT) { return true; }
    // TypeTable lookup with sigma chain resolution
    {
        char* ty = resolve_ty(tm, v);
        if (ty != null && ty[0] != 0)
        {
            if (ty[0] == 'f' || ty[0] == 'd') { return true; }
            if (ty[0] == 'i' || ty[0] == 'u' || ty[0] == 'p' || ty[0] == '{') { return false; }
        }
    }
    // AST annotation fallback
    if (v.src != null && v.src.type_annotation != null)
    {
        Node* t = v.src.type_annotation;
        if (t.kind == Nk.NODE_TYPE_PRIMITIVE)
        {
            char* n = t.p.ident.name_ptr;
            usz l = t.p.ident.name_len;
            if (l == 3 && n[0] == 'f') { return true; } // f32 or f64
            if (l == 6 && n[0] == 'd') { return true; } // double
        }
    }
    return false;
}
fn bool is_float_val(ssi_ir::IrVal* v)
{
    return is_float_val_ty(v, null);
}

fn bool is_signed_int_val(ssi_ir::IrVal* v)
{
    if (v == null) { return true; }

    // Walk sigma chain to reach the underlying value
    ssi_ir::IrVal* cur = v;
    int depth = 0;
    while (cur != null && cur.op == ssi_ir::IrOp.IR_SIGMA
           && cur.arg_count >= 1 && cur.args[0] != null && depth < 16)
    {
        cur = cur.args[0]; depth++;
    }
    if (cur == null) { cur = v; }

    // Check literal: parser now sets is_signed correctly for u-suffixed literals
    if (cur.op == ssi_ir::IrOp.IR_CONST_INT && cur.src != null
        && cur.src.kind == Nk.NODE_LIT_INT)
    {
        return cur.src.p.lit_int.is_signed;
    }

    // Check binder type annotation (let decl, fn param, phi binder)
    // Walk: cur.src, cur.binder
    Node*[3] nodes;
    nodes[0] = (cur.src != null) ? cur.src : null;
    nodes[1] = (cur.binder != null) ? cur.binder : null;
    nodes[2] = (v.src != null) ? v.src : null;
    for (int ni = 0; ni < 3; ni++)
    {
        Node* nd = nodes[ni];
        if (nd == null) { continue; }
        // Direct type_annotation
        Node* ta = nd.type_annotation;
        if (ta != null && ta.kind == Nk.NODE_TYPE_PRIMITIVE)
        {
            char first = ta.p.ident.name_ptr[0];
            if (first == 'u') { return false; }
            if (first == 'i') { return true; }
        }
        // For phi binders: children[0] might be the pattern with type_annotation
        if (nd.kind == Nk.NODE_DECL_LET || nd.kind == Nk.NODE_DECL_MUT)
        {
            if (nd.child_count >= 1 && nd.children[0] != null)
            {
                Node* pat_ta = nd.children[0].type_annotation;
                if (pat_ta != null && pat_ta.kind == Nk.NODE_TYPE_PRIMITIVE)
                {
                    char first2 = pat_ta.p.ident.name_ptr[0];
                    if (first2 == 'u') { return false; }
                    if (first2 == 'i') { return true; }
                }
            }
        }
    }

    // For phi nodes: check operand args for signedness clues
    if (cur.op == ssi_ir::IrOp.IR_PHI)
    {
        for (usz ai = 0; ai < cur.arg_count && ai < 4; ai++)
        {
            ssi_ir::IrVal* arg = cur.args[ai];
            if (arg != null && arg.op == ssi_ir::IrOp.IR_CONST_INT
                && arg.src != null && arg.src.kind == Nk.NODE_LIT_INT)
            {
                if (!arg.src.p.lit_int.is_signed) { return false; }
            }
        }
    }

    return true; // default: signed
}

// Emit the LLVM instruction name for a binary op.
fn void CgenModule.emit_binop(CgenModule* cg, Tt op, ssi_ir::IrVal* lhs, TypeTable* tm = null)
{
    bool fp     = is_float_val_ty(lhs, tm);
    bool signed = is_signed_int_val(lhs);

    switch (op)
    {
        case Tt.TOKEN_PLUS:    cg.out.writes(fp ? "fadd" : "add nsw");
        case Tt.TOKEN_MINUS:   cg.out.writes(fp ? "fsub" : "sub nsw");
        case Tt.TOKEN_STAR:    cg.out.writes(fp ? "fmul" : "mul nsw");

        // Wrapping arithmetic: +%  -%  *%  (two's-complement, defined overflow)
        case Tt.TOKEN_PLUS_PERCENT:  cg.out.writes(fp ? "fadd" : "add");   // nuw: no-undefined-wrap
        case Tt.TOKEN_MINUS_PERCENT: cg.out.writes(fp ? "fsub" : "sub");
        case Tt.TOKEN_STAR_PERCENT:  cg.out.writes(fp ? "fmul" : "mul");

        // Saturating arithmetic: +|  -|  *|  → LLVM intrinsics
        // Saturating: use llvm.sadd.sat / llvm.ssub.sat / llvm.smul.sat intrinsics.
        // Handled in the special path below (IR_BIN + sat op) — these cases
        // are only reached as fallback for fp (which doesn't have sat; use fadd).
        case Tt.TOKEN_PLUS_PIPE:  cg.out.writes(fp ? "fadd" : "add nsw"); // fp fallback; int handled below
        case Tt.TOKEN_MINUS_PIPE: cg.out.writes(fp ? "fsub" : "sub nsw");
        case Tt.TOKEN_STAR_PIPE:  cg.out.writes(fp ? "fmul" : "mul nsw");
        case Tt.TOKEN_SLASH:   cg.out.writes(fp ? "fdiv" : (signed ? "sdiv" : "udiv"));
        case Tt.TOKEN_PERCENT: cg.out.writes(fp ? "frem" : (signed ? "srem" : "urem"));
        case Tt.TOKEN_AMP:     cg.out.writes(fp ? "fadd" : "and");  // float bitwise → fadd placeholder (type error)
        case Tt.TOKEN_PIPE:    cg.out.writes(fp ? "fadd" : "or");
        case Tt.TOKEN_XOR:     cg.out.writes(fp ? "fadd" : "xor");
        case Tt.TOKEN_LSHIFT:  cg.out.writes(fp ? "fadd" : "shl");    // fp shl = UB, fallback fadd
        case Tt.TOKEN_RSHIFT:  cg.out.writes(fp ? "fadd" : (signed ? "ashr" : "lshr"));
        case Tt.TOKEN_AMPAMP:  cg.out.writes("and");   // boolean && → i1 and
        case Tt.TOKEN_PIPEPIPE:cg.out.writes("or");    // boolean || → i1 or
        // Comparisons
        case Tt.TOKEN_EQEQ:
            cg.out.writes(fp ? "fcmp oeq" : "icmp eq");
        case Tt.TOKEN_NEQ:
        case Tt.TOKEN_NEQ_UNI:
            cg.out.writes(fp ? "fcmp one" : "icmp ne");
        case Tt.TOKEN_LT:
            cg.out.writes(fp ? "fcmp olt" : (signed ? "icmp slt" : "icmp ult"));
        case Tt.TOKEN_LTEQ:
            cg.out.writes(fp ? "fcmp ole" : (signed ? "icmp sle" : "icmp ule"));
        case Tt.TOKEN_GT:
            cg.out.writes(fp ? "fcmp ogt" : (signed ? "icmp sgt" : "icmp ugt"));
        case Tt.TOKEN_GTEQ:
            cg.out.writes(fp ? "fcmp oge" : (signed ? "icmp sge" : "icmp uge"));
        // Matmul @ — call __pride_matmul (may hook BLAS)
        case Tt.TOKEN_AT:
            cg.out.writes("call ptr @__pride_matmul");
        // Checked arithmetic — emit via llvm.sadd.with.overflow etc.
        // (handled as special case in emit_binop, not here)
        case Tt.TOKEN_PLUS_QUESTION:   cg.out.writes("add");  // handled below
        case Tt.TOKEN_MINUS_QUESTION:  cg.out.writes("sub");
        case Tt.TOKEN_STAR_QUESTION:   cg.out.writes("mul");
        default:
            cg.out.writes("add"); // safe fallback
    }
}


// Resolve the LLVM type for a value, following sigma/cast chains.
// Sigmas are stripped from block lists by SASI but their args[0] chains remain valid.
fn char* resolve_ty(TypeTable* tm, ssi_ir::IrVal* v)
{
    if (v == null) { return (char*)"i64"; }
    ssi_ir::IrVal* cur = v;
    for (int depth = 0; depth < 8; depth++)
    {
        if (cur == null) { break; }
        char* ty = (tm != null) ? tm.get(cur.id) : null;
        if (ty != null && ty[0] != 0 && !(ty[0]=='v'&&ty[1]=='o'&&ty[2]=='i'&&ty[3]=='d'&&ty[4]==0))
        { return ty; }
        // Follow sigma / cast chain
        if ((cur.op == ssi_ir::IrOp.IR_SIGMA || cur.op == ssi_ir::IrOp.IR_CAST)
            && cur.arg_count >= 1 && cur.args[0] != null)
        { cur = cur.args[0]; continue; }
        break;
    }
    return (char*)"i64";
}

// ── Scalar coercion service ────────────────────────────────────────────────
// Single source of truth for "a value of type SRC must be materialised as
// type DST". Every site that retypes a value (ret, φ-edge normalisation, …)
// consults `coerce_op` instead of open-coding its own width comparisons —
// the previous family of per-site copies is exactly where the invalid-IR
// regressions came from (i64 value fed to an i32 φ, fptrunc used for a
// float→double WIDENING, and similar).

// Width of an "iN" integer type string, or -1 when TY is not an int type.
fn int int_ty_width(char* ty)
{
    if (ty == null || ty[0] != 'i' || ty[1] < '0' || ty[1] > '9') return -1;
    int w = 0;
    usz ci = 1;
    while (ty[ci] >= '0' && ty[ci] <= '9') { w = w * 10 + (int)(ty[ci] - '0'); ci++; }
    if (ty[ci] != 0) return -1;
    return w;
}

// Rank of a floating-point type string ("float" < "double"), or -1 otherwise.
fn int fp_ty_rank(char* ty)
{
    if (ty == null) return -1;
    if (ty[0] == 'f') return 1;   // float
    if (ty[0] == 'd') return 2;   // double
    return -1;
}

// The LLVM conversion opcode that turns a scalar SRC into a scalar DST, or
// null when the types are representation-identical and NO instruction is
// required (same type, or both opaque `ptr`). Also null when no scalar
// conversion exists (aggregates/void) — callers handle those separately.
// Is an AST type annotation an unsigned-integer-ish type (uN, usize, bool)?
// Signedness does not survive into the LLVM type text (iN is sign-agnostic),
// so extension decisions MUST read the source annotation — `sext` on a
// `u8 255` yields -1 (and on `true`, too: i1 sign-extends to -1) where the
// value is defined to be 255 (1) — see r38.
fn bool cg_ann_is_unsigned(Node* ann)
{
    if (ann == null) return false;
    if (ann.kind == Nk.NODE_TYPEVAR && ann.resolved != null)
    {
        Node* d = ann.resolved;
        if (d.kind == Nk.NODE_DECL_TYPE && d.child_count >= 1)
        { return cg_ann_is_unsigned(d.children[d.child_count - 1]); }
        return false;
    }
    if (ann.kind != Nk.NODE_TYPE_PRIMITIVE) return false;
    char* n = ann.p.ident.name_ptr; usz l = ann.p.ident.name_len;
    if (n == null || l == 0) return false;
    if (l == 4 && n[0]=='b'&&n[1]=='o'&&n[2]=='o'&&n[3]=='l') return true;  // bool extends zero
    if (l == 5 && n[0]=='u'&&n[1]=='s'&&n[2]=='i'&&n[3]=='z'&&n[4]=='e') return true;
    if (l >= 2 && n[0] == 'u')   // uN
    {
        for (usz i = 1; i < l; i++) { if (n[i] < '0' || n[i] > '9') return false; }
        return true;
    }
    return false;
}

fn char* coerce_op(char* src, char* dst)
{
    if (src == null || dst == null || src[0] == 0 || dst[0] == 0) return null;
    // Identical types need no instruction (covers ptr==ptr under opaque ptrs).
    usz sl = strlen(src); usz dl = strlen(dst);
    if (sl == dl)
    {
        bool same = true;
        for (usz ci = 0; ci < sl; ci++) { if (src[ci] != dst[ci]) { same = false; break; } }
        if (same) return null;
    }
    int sw = int_ty_width(src);
    int dw = int_ty_width(dst);
    int sr = fp_ty_rank(src);
    int dr = fp_ty_rank(dst);
    if (sw > 0 && dw > 0) return sw > dw ? (char*)"trunc" : (char*)"sext";
    if (sr > 0 && dr > 0) return sr > dr ? (char*)"fptrunc" : (char*)"fpext";
    if (sr > 0 && dw > 0) return (char*)"fptosi";
    if (sw > 0 && dr > 0) return (char*)"sitofp";
    if (src[0] == 'p' && dw > 0) return (char*)"ptrtoint";
    if (sw > 0 && dst[0] == 'p') return (char*)"inttoptr";
    // Aggregates / arrays / void have no scalar conversion.
    if (src[0] == '{' || dst[0] == '{' || src[0] == '[' || dst[0] == '['
        || (src[0] == 'v' && src[1] == 'o') || (dst[0] == 'v' && dst[1] == 'o'))
    { return null; }
    return (char*)"bitcast";
}

// Signedness-aware sibling of coerce_op: identical, except an integer
// WIDENING zero-extends when the VALUE is unsigned-typed. The LLVM type text
// is sign-agnostic — signedness survives only in the AST annotation and on
// integer literals, both of which is_signed_int_val knows how to read
// (r38/r40). A sext of u8 200 / u32 4000000001 / bool true negates the value.
fn char* coerce_op_val(char* src, char* dst, ssi_ir::IrVal* v)
{
    char* r = coerce_op(src, dst);
    if (r != null && r[0] == 's' && r[1] == 'e' && !is_signed_int_val(v))
    { return (char*)"zext"; }
    return r;
}

// ── Typed φ-edge normalisation ─────────────────────────────────────────────
// LLVM requires every φ incoming value to have EXACTLY the φ's type and to
// dominate the end of its predecessor block. Branch/match arm results often
// carry the body's NATURAL type (e.g. an i64 `let` feeding an i32 match
// result), so each malformed φ edge is retyped through a real conversion
// instruction. The instruction must live at the END of the predecessor block:
// a join block can print BEFORE some of its predecessors in the linear order,
// so emitting the conversion at the φ site would break dominance. The anchor
// is printed by CgenModule.emit_phi_edge_coerces (invoked from the block
// loop, right before the predecessor's terminator) and the φ references it
// as `%phi.<id>.in.<slot>`. Constants need no anchor — emit_phi folds them
// to the φ width inline.

// σ-transparency shared by the predicate and both print sites.
fn ssi_ir::IrVal* sigma_unwrap(ssi_ir::IrVal* v)
{
    int depth = 0;
    while (v != null && v.op == ssi_ir::IrOp.IR_SIGMA
           && v.arg_count >= 1 && v.args[0] != null && depth < 16)
    { v = v.args[0]; depth++; }
    return v;
}

// Decide whether φ incoming slot AI must be retyped. On true, *OP/*SRC/*DST
// receive the conversion opcode and the operand/result type strings. Mirrors
// emit_phi's incoming-value classification exactly: anything emit_phi would
// print as `undef`, fold as a constant, or pass through unchanged needs no
// anchored instruction.
fn bool phi_edge_coercion(TypeTable* tm, ssi_ir::IrVal* ph, usz ai,
                          char** op, char** src, char** dst)
{
    if (ph == null || ph.op != ssi_ir::IrOp.IR_PHI || ai >= ph.arg_count) return false;
    char* phi_ty = (tm != null) ? tm.get(ph.id) : null;
    if (phi_ty == null || phi_ty[0] == 0) return false;   // untyped φ: legacy i64 fallback
    if (phi_ty[0] == 'v' && phi_ty[1] == 'o') return false;   // void φ: not emitted at all
    ssi_ir::IrVal* arg = sigma_unwrap(ph.args[ai]);
    if (arg == null || arg.op == ssi_ir::IrOp.IR_CONST_UNIT) return false;  // prints undef
    // Constants are folded inline by emit_phi / emit_vref — no anchor.
    if (arg.op == ssi_ir::IrOp.IR_CONST_INT  || arg.op == ssi_ir::IrOp.IR_CONST_BOOL
     || arg.op == ssi_ir::IrOp.IR_CONST_FLOAT || arg.op == ssi_ir::IrOp.IR_CONST_NULL)
    { return false; }
    // A value that EMITS as bare `void` (e.g. a unit-typed call) defines no
    // SSA register at all — emit_phi renders its incoming edge as `undef`.
    // resolve_ty deliberately upgrades void to its i64 fallback (its callers
    // want a materialisable type), but HERE that drift would anchor a
    // conversion on a name that never exists: the phi-edge pass must agree
    // with emit_phi's raw-tymap classification, exactly (lockstep).
    char* raw_ty = (tm != null) ? tm.get(arg.id) : null;
    if (raw_ty != null && raw_ty[0] == 'v' && raw_ty[1] == 'o') return false;  // prints undef
    char* apty = resolve_ty(tm, arg);
    if (apty == null || apty[0] == 0) return false;
    if (phi_ty[0] == '{')
    {
        // Aggregate φ: incoming aggregates match by construction; a SCALAR
        // incoming (effect-handler arms feed the join φ their resume ABI's raw
        // ptr/i64 while the φ itself is typed by the computation — e.g. a
        // fn-VALUE) can only be widened honestly by filling slot 0.
        if (apty[0] == '{' || (apty[0] == 'v' && apty[1] == 'o')) return false;
        bool same = true;
        for (usz ci = 0; phi_ty[ci] != 0 && apty[ci] != 0; ci++)
        {
            if (phi_ty[ci] != apty[ci]) { same = false; break; }
        }
        if (same && strlen(phi_ty) == strlen(apty)) return false;
        // Only ptr/int scalars are fillable into slot 0 materialisably.
        bool scalar = (apty[0] == 'p') || (apty[0] == 'i' && apty[1] >= '0' && apty[1] <= '9');
        if (!scalar) return false;
        *op = (char*)"insv0"; *src = apty; *dst = phi_ty;
        return true;
    }
    if (apty[0] == '{' || (apty[0] == 'v' && apty[1] == 'o')) return false;   // prints undef
    char* opc = coerce_op_val(apty, phi_ty, arg);
    if (opc == null) return false;
    *op = opc; *src = apty; *dst = phi_ty;
    return true;
}

// Split an anonymous struct/tuple type string "{ T0, T1, ... }" into its
// element type strings (brace-depth aware, so nested aggregates and named
// types are handled). Returns the element count, or 0 when TY is not a
// non-empty struct type, an element is empty/malformed, or arity overflows
// (callers fall back to their pre-existing path in all 0 cases).
const int STRUCT_SPLIT_CAP = 16;
const int STRUCT_SPLIT_LEN = 256;  // element type strings (deep aggregates need >64)
fn int split_struct_ty(char* ty, char* out, usz elem_cap)
{
    // out is STRUCT_SPLIT_CAP * elem_cap bytes
    if (ty == null || ty[0] != '{') return 0;
    usz len = strlen(ty);
    if (len < 2 || ty[len - 1] != '}') return 0;
    usz n = 0; int depth = 0; usz start = 0;
    for (usz i = 0; i < len; i++)
    {
        char ch = ty[i];
        if (ch == '{') { depth++; if (depth == 1) { start = i + 1; continue; } }
        if (ch == '}') { depth--; }
        bool boundary = (depth == 1 && ch == ',') || (i == len - 1);
        if (!boundary) continue;
        usz e = i;   // element is [start, e) — for i == len-1 this excludes '}'
        while (start < e && ty[start] == ' ') start++;
        while (e > start && ty[e - 1] == ' ') e--;
        if (e <= start) return 0;   // empty element ("{ }" or "{ , ..}") — malformed
        if (n >= STRUCT_SPLIT_CAP) return 0;
        char* dst = out + n * elem_cap;
        usz w = 0;
        for (usz k = start; k < e && w + 1 < elem_cap; k++) { dst[w] = ty[k]; w++; }
        dst[w] = 0;
        n++;
        start = i + 1;
    }
    return (int)n;
}

// Write the LLVM type for val id from the type table (or "i64" fallback).
fn void CgenModule.writes_ty(CgenModule* cg, TypeTable* tm, int id)
{
    char* ty = (tm != null) ? tm.get(id) : null;
    if (ty != null && ty[0] != 0)
    {
        if (ty[0] == 'v' && ty[1] == 'o' && ty[2] == 'i' && ty[3] == 'd' && ty[4] == 0)
        { cg.out.writes("i64"); }
        else { cg.out.writes(ty); }
    }
    else { cg.out.writes("i64"); }
}

// Is this value unit/void typed?
fn bool CgenModule.is_unit_val(CgenModule* cg, TypeTable* tm, ssi_ir::IrVal* v)
{
    if (v == null) return true;
    if (v.op == ssi_ir::IrOp.IR_CONST_UNIT) return true;
    if (tm != null)
    {
        char* ty = tm.get(v.id);
        if (ty != null && ty[0] == 'v' && ty[1] == 'o') return true;
    }
    return false;
}


fn long sizeof_type_x86(Node* t)
{
    if (t == null) return 8;
    switch (t.kind)
    {
        case Nk.NODE_TYPE_PRIMITIVE:
        {
            char* n = t.p.ident.name_ptr; usz l = t.p.ident.name_len;
            // Float
            if (l==3 && n[0]=='f' && n[1]=='3' && n[2]=='2') return 4;
            if (l==3 && n[0]=='f' && n[1]=='6' && n[2]=='4') return 8;
            // bool
            if (l==4 && n[0]=='b' && n[1]=='o' && n[2]=='o' && n[3]=='l') return 1;
            // str/Str = { ptr, i64 } = 16 bytes
            if (l==3 && (n[0]=='s'||n[0]=='S') && n[1]=='t' && n[2]=='r') return 16;
            // Arbitrary iN/uN: ceil(N/8) bytes, capped at 8
            if (l >= 2 && (n[0]=='i' || n[0]=='u'))
            {
                long w = 0; bool ok3 = true;
                for (usz di3 = 1; di3 < l; di3++)
                {
                    if (n[di3] < '0' || n[di3] > '9') { ok3 = false; break; }
                    w = w * 10 + (long)(n[di3] - '0');
                }
                if (ok3 && w >= 1) { long s3 = (w+7)/8; return s3 > 8 ? 8 : s3; }
            }
            return 8;
        }
        case Nk.NODE_TYPE_PTR: case Nk.NODE_TYPE_FN: return 8;
        case Nk.NODE_TYPE_ARRAY:
        {
            // [T; N] = N * sizeof(T). AST can have 1 or 2 children.
            // 2-child form: children[0]=elem_type, children[1]=count_literal
            // 1-child form: children[0]=count_literal (elem type lost in some parse paths)
            if (t.child_count >= 2)
            {
                Node* elem_t2 = t.children[0];
                Node* count_n2 = t.children[1];
                long elem_sz2 = sizeof_type_x86(elem_t2);
                long count2 = (count_n2 != null && count_n2.kind == Nk.NODE_LIT_INT)
                              ? (long)count_n2.p.lit_int.int_val : 1;
                return elem_sz2 * count2;
            }
            if (t.child_count == 1)
            {
                // Only count child; element size unknown, use 1 (byte array default)
                Node* count_n1 = t.children[0];
                long count1 = (count_n1 != null && count_n1.kind == Nk.NODE_LIT_INT)
                              ? (long)count_n1.p.lit_int.int_val : 1;
                // Check element type from type_annotation if available (set by typechecker)
                long elem_sz1 = 1;  // default: byte array
                if (t.type_annotation != null)
                { elem_sz1 = sizeof_type_x86(t.type_annotation); }
                return elem_sz1 * count1;
            }
            return 8;
        }
        case Nk.NODE_DECL_STRUCT:
        {
            long tot = 0; long aln = 1;
            for (usz fi = 0; fi < t.child_count; fi++)
            {
                Node* c = t.children[fi];
                if (c == null || c.kind != Nk.NODE_FIELD_DECL) continue;
                Node* ft = c.child_count >= 2 ? c.children[1] : null;
                long fs = sizeof_type_x86(ft); long fa = alignof_type_x86(ft);
                if (fa > aln) aln = fa;
                long r = fa > 0 ? (tot % fa) : 0; if (r != 0) tot += fa - r;
                tot += fs;
            }
            if (aln > 0) { long r2 = tot % aln; if (r2 != 0) tot += aln - r2; }
            return tot > 0 ? tot : 1;
        }
        case Nk.NODE_TYPE_GENERIC_APP:
        {
            // Concrete generic-struct instantiation: substituted field sizes
            // (must agree with the printed record repr — r33).
            Node* fblk5 = cg_concrete_struct_app_fblk(t);
            if (fblk5 == null) return 8;
            Node* prev_app5 = g_subst_app;
            g_subst_app = t;
            long tot = 0; long aln = 1;
            for (usz fi = 0; fi < fblk5.child_count; fi++)
            {
                Node* c = fblk5.children[fi];
                if (c == null || c.kind != Nk.NODE_FIELD_DECL) continue;
                Node* ft = c.child_count >= 2 ? ast::generic_payload_subst(t, c.children[1]) : null;
                long fs = sizeof_type_x86(ft); long fa = alignof_type_x86(ft);
                if (fa > aln) aln = fa;
                long r = fa > 0 ? (tot % fa) : 0; if (r != 0) tot += fa - r;
                tot += fs;
            }
            g_subst_app = prev_app5;
            if (aln > 0) { long r2 = tot % aln; if (r2 != 0) tot += aln - r2; }
            return tot > 0 ? tot : 1;
        }
        case Nk.NODE_TYPEVAR:
        {
            // Inside a GENERIC_APP expansion (r48): substitute the argument.
            if (g_subst_app != null)
            {
                Node* sm5 = ast::generic_payload_subst(g_subst_app, t);
                if (sm5 != null && sm5 != t) { return sizeof_type_x86(sm5); }
            }
            return t.resolved != null ? sizeof_type_x86(t.resolved) : 8;
        }
        case Nk.NODE_DECL_UNION:
            return ast::union_is_c_union(t) ? 8 : 16;
        case Nk.NODE_TYPE_UNION:
        case Nk.NODE_TYPE_INTERSECT:
            return (t.child_count >= 1 && t.children[0] != null) ? sizeof_type_x86(t.children[0]) : 8;
        default: return 8;
    }
}

fn long alignof_type_x86(Node* t)
{
    if (t == null) return 8;
    switch (t.kind)
    {
        case Nk.NODE_TYPE_PRIMITIVE: { long s = sizeof_type_x86(t); return s > 8 ? 8 : (s > 0 ? s : 1); }
        case Nk.NODE_TYPE_PTR: case Nk.NODE_TYPE_FN: return 8;
        case Nk.NODE_DECL_STRUCT:
        {
            long a = 1;
            for (usz fi = 0; fi < t.child_count; fi++)
            {
                Node* c = t.children[fi];
                if (c == null || c.kind != Nk.NODE_FIELD_DECL) continue;
                Node* ft = c.child_count >= 2 ? c.children[1] : null;
                long fa = alignof_type_x86(ft); if (fa > a) a = fa;
            }
            return a;
        }
        case Nk.NODE_TYPE_GENERIC_APP:
        {
            Node* fblk6 = cg_concrete_struct_app_fblk(t);
            if (fblk6 == null) return 8;
            Node* prev_app6 = g_subst_app;
            g_subst_app = t;
            long a6 = 1;
            for (usz fi = 0; fi < fblk6.child_count; fi++)
            {
                Node* c = fblk6.children[fi];
                if (c == null || c.kind != Nk.NODE_FIELD_DECL) continue;
                Node* ft = c.child_count >= 2 ? ast::generic_payload_subst(t, c.children[1]) : null;
                long fa = alignof_type_x86(ft); if (fa > a6) a6 = fa;
            }
            g_subst_app = prev_app6;
            return a6;
        }
        case Nk.NODE_TYPEVAR:
        {
            if (g_subst_app != null)
            {
                Node* sm6 = ast::generic_payload_subst(g_subst_app, t);
                if (sm6 != null && sm6 != t) { return alignof_type_x86(sm6); }
            }
            return t.resolved != null ? alignof_type_x86(t.resolved) : 8;
        }
        case Nk.NODE_DECL_UNION:
            return 8;
        case Nk.NODE_TYPE_UNION:
        case Nk.NODE_TYPE_INTERSECT:
            return (t.child_count >= 1 && t.children[0] != null) ? alignof_type_x86(t.children[0]) : 8;
        default: return 8;
    }
}


fn void CgenModule.emit_val(CgenModule* cg, ssi_ir::IrVal* v, TypeTable* tm)
{
    if (v == null) { return; }

    switch (v.op)
    {
        case ssi_ir::IrOp.IR_CONST_INT:
        case ssi_ir::IrOp.IR_CONST_FLOAT:
        case ssi_ir::IrOp.IR_CONST_BOOL:
        case ssi_ir::IrOp.IR_CONST_NULL:
        case ssi_ir::IrOp.IR_CONST_UNIT:
        case ssi_ir::IrOp.IR_CONST_STR:
            // Constants are inlined at use sites — no dedicated instruction.
            return;

        case ssi_ir::IrOp.IR_PARAM:
            // Regular function parameters: declared in function header — no instruction.
            // Handler arm parameters: retrieved from the runtime's effect frame.
            if (v.binder != null && v.binder.kind == Nk.NODE_HANDLER_ARM)
            {
                // This IR_PARAM is an effect operation argument in a handler arm.
                // The runtime provides these via __pride_get_arm_arg(index).
                // The flat arg-slot index was assigned at lowering time and
                // travels on the value itself (emit_arm_arg_params in ssi_ir) —
                // deriving it from child POSITION would overcount `()`
                // zero-arg placeholders and nested tuple binders.
                //
                // The slot's runtime type is always i64 bits. The binder's
                // STAMPED type may be anything passable through a slot — float,
                // narrow int, ptr — so read the slot raw and unbox it honestly:
                // float gets its bits back, narrow ints truncate, ptr becomes
                // a pointer again. (Same protocol as the perform/resume ends.)
                char* argty = (tm != null) ? tm.get(v.id) : null;
                int aw = 0;
                if (argty != null && argty[0] == 'i')
                { for (usz ci = 1; argty[ci] >= '0' && argty[ci] <= '9'; ci++) aw = aw * 10 + (int)(argty[ci] - '0'); }
                bool arg_fp  = (argty != null && (argty[0] == 'f' || argty[0] == 'd'));
                bool arg_ptr = (argty != null && argty[0] == 'p');
                bool arg_bool = (aw == 1 && argty != null && argty[2] == 0);
                bool arg_narrow = (aw > 1 && aw < 64);
                if (!arg_fp && !arg_ptr && !arg_bool && !arg_narrow)
                {
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = call i64 @__pride_get_arm_arg(i64 ");
                    cg.out.writeu(v.ival);
                    cg.out.writes(")\n");
                }
                else
                {
                    cg.out.writes("  %armarg."); cg.out.writei(v.id);
                    cg.out.writes(" = call i64 @__pride_get_arm_arg(i64 ");
                    cg.out.writeu(v.ival);
                    cg.out.writes(")\n");
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    if (arg_fp && argty[0] == 'f')
                    {
                        cg.out.writes("w");   // require a distinct temp for the trunc
                    }
                    if (arg_fp && argty[0] == 'f')
                    {
                        // bitcast needs i32 first
                        cg.out.writes(" = trunc i64 %armarg."); cg.out.writei(v.id);
                        cg.out.writes(" to i32\n");
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = bitcast i32 %v"); cg.out.writei(v.id);
                        cg.out.writes("w to float\n");
                    }
                    else if (arg_fp)
                    {
                        cg.out.writes(" = bitcast i64 %armarg."); cg.out.writei(v.id);
                        cg.out.writes(" to double\n");
                    }
                    else if (arg_ptr)
                    {
                        cg.out.writes(" = inttoptr i64 %armarg."); cg.out.writei(v.id);
                        cg.out.writes(" to ptr\n");
                    }
                    else
                    {
                        cg.out.writes(" = trunc i64 %armarg."); cg.out.writei(v.id);
                        cg.out.writes(" to "); cg.out.writes(argty); cg.out.writes("\n");
                    }
                }
            }
            return;

        case ssi_ir::IrOp.IR_SIGMA:
            // σ-nodes are SASI-swept to a fact map. If any survive to codegen,
            // emit as a typed identity: the value IS its source operand.
            if (v.arg_count >= 1 && v.args[0] != null)
            {
                char* sty = (tm != null) ? tm.get(v.id) : null;
                if (sty == null || sty[0] == 0) sty = (char*)"i64";
                cg.out.writes("  %v"); cg.out.writei(v.id);
                bool is_fp = (sty[0]=='f'||sty[0]=='d');
                bool is_ptr = (sty[0]=='p');
                if (is_fp)
                {
                    cg.out.writes(" = fadd "); cg.out.writes(sty);
                    cg.out.writes(" 0.0, ");   cg.emit_vref(v.args[0]);
                }
                else if (is_ptr)
                {
                    // ptr→ptr identity: LLVM 15+ opaque pointers reject bitcast ptr→ptr.
                    // Use getelementptr inbounds i8, ptr X, i32 0 (zero offset, identity).
                    cg.out.writes(" = getelementptr inbounds i8, ptr ");
                    cg.emit_vref(v.args[0]);
                    cg.out.writes(", i32 0");
                }
                else
                {
                    // Integer: add 0 (identity, always legal)
                    cg.out.writes(" = add "); cg.out.writes(sty);
                    cg.out.writes(" 0, ");     cg.emit_vref(v.args[0]);
                }
                cg.out.writes("\n");
            }
            return;

        case ssi_ir::IrOp.IR_BIN:
            {
                ssi_ir::IrVal* lhs = v.arg_count >= 1 ? v.args[0] : null;
                ssi_ir::IrVal* rhs = v.arg_count >= 2 ? v.args[1] : null;
                bool fp = is_float_val_ty(lhs, tm);

                // Elementwise tensor arithmetic + - * /  → the runtime helper
                // (shape-checked, allocates the result header). Detection is
                // by the LHS operand's source annotation: tensor literals and
                // tensor-typed binders alike carry NODE_TYPE_TENSOR. Without
                // this dispatch `a + b` on two heap-ptr tensors fell into
                // generic pointer arithmetic.
                if (v.bop == Tt.TOKEN_PLUS || v.bop == Tt.TOKEN_MINUS
                    || v.bop == Tt.TOKEN_STAR || v.bop == Tt.TOKEN_SLASH)
                {
                    Node* tbsrc = v.src;
                    Node* tlann = (tbsrc != null && tbsrc.child_count >= 1
                                   && tbsrc.children[0] != null)
                                  ? tbsrc.children[0].type_annotation : null;
                    if (tlann != null && tlann.kind == Nk.NODE_TYPE_TENSOR)
                    {
                        int ew_op = (v.bop == Tt.TOKEN_PLUS)  ? 0
                                  : (v.bop == Tt.TOKEN_MINUS) ? 1
                                  : (v.bop == Tt.TOKEN_STAR)  ? 2 : 3;
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = call ptr @__pride_tensor_elemwise(ptr ");
                        cg.emit_vref(lhs);
                        cg.out.writes(", ptr ");
                        cg.emit_vref(rhs);
                        cg.out.writes(", i32 "); cg.out.writei(ew_op);
                        cg.out.writes(")\n");
                        return;
                    }
                }

                // Matmul: emit as call (may hook BLAS)
                if (v.bop == Tt.TOKEN_AT)
                {
                    // vector · vector is a SCALAR dot product (spec §11
                    // checked by typecheck) — route to __pride_vecdot and
                    // coerce the double to the stamped element type.
                    // Matrix-vector / vector-matrix stay with batched matmul
                    // (the runtime takes rank-1 views of the operands).
                    Node* mmn = v.src;
                    int lrank = -1;
                    int rrank = -1;
                    Node* ret_ann = null;
                    if (mmn != null && mmn.kind == Nk.NODE_EXPR_MATMUL)
                    {
                        Node* ln = mmn.child_count >= 1 ? mmn.children[0] : null;
                        Node* rn = mmn.child_count >= 2 ? mmn.children[1] : null;
                        lrank = cg_tensor_rank_of(ln != null ? ln.type_annotation : null);
                        rrank = cg_tensor_rank_of(rn != null ? rn.type_annotation : null);
                        ret_ann = mmn.type_annotation;
                    }
                    if (lrank == 1 && rrank == 1)
                    {
                        char[TYMAP_ENTRY] dtb; dtb[0] = 0;
                        if (ret_ann != null)
                        { type_to_llvm_buf(ret_ann, &dtb[0], TYMAP_ENTRY, 0); }
                        if (dtb[0] == 0 || (dtb[0] == 'v' && dtb[1] == 'o'))
                        { snprintf(&dtb[0], TYMAP_ENTRY, "double"); }
                        cg.out.writes("  %vdot.v"); cg.out.writei(v.id);
                        cg.out.writes(" = call double @__pride_vecdot(ptr ");
                        cg.emit_vref(lhs);
                        cg.out.writes(", ptr ");
                        cg.emit_vref(rhs);
                        cg.out.writes(")\n");
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        if (dtb[0] == 'd')
                        {
                            cg.out.writes(" = fadd double %vdot.v"); cg.out.writei(v.id);
                            cg.out.writes(", 0.0\n");
                        }
                        else if (dtb[0] == 'f')
                        {
                            cg.out.writes(" = fptrunc double %vdot.v"); cg.out.writei(v.id);
                            cg.out.writes(" to float\n");
                        }
                        else if (dtb[0] == 'i')
                        {
                            cg.out.writes(" = fptosi double %vdot.v"); cg.out.writei(v.id);
                            cg.out.writes(" to "); cg.out.writes(&dtb[0]); cg.out.writes("\n");
                        }
                        else
                        {
                            cg.out.writes(" = fadd double %vdot.v"); cg.out.writei(v.id);
                            cg.out.writes(", 0.0\n");
                        }
                        return;
                    }
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = call ptr @__pride_matmul(ptr ");
                    cg.emit_vref(lhs);
                    cg.out.writes(", ptr ");
                    cg.emit_vref(rhs);
                    cg.out.writes(")\n");
                    return;
                }

                // Checked arithmetic: +? -? *? → llvm.sadd.with.overflow etc.
                if (v.bop == Tt.TOKEN_PLUS_QUESTION ||
                    v.bop == Tt.TOKEN_MINUS_QUESTION ||
                    v.bop == Tt.TOKEN_STAR_QUESTION)
                {
                    char* lhs_ty = resolve_ty(tm, lhs);
                    char* intrinsic = (v.bop == Tt.TOKEN_PLUS_QUESTION)
                        ? "llvm.sadd.with.overflow"
                        : (v.bop == Tt.TOKEN_MINUS_QUESTION)
                            ? "llvm.ssub.with.overflow"
                            : "llvm.smul.with.overflow";
                    // Emit: %agg = call {i64,i1} @llvm.sadd.with.overflow.i64(i64 a, i64 b)
                    //        %v   = extractvalue {i64,i1} %agg, 0
                    cg.out.writes("  %chk"); cg.out.writei(v.id);
                    cg.out.writes(" = call {"); cg.out.writes(lhs_ty);
                    cg.out.writes(", i1} @");   cg.out.writes(intrinsic);
                    cg.out.writes("."); cg.out.writes(lhs_ty); cg.out.writes("(");
                    cg.out.writes(lhs_ty); cg.out.writes(" "); cg.emit_vref(lhs);
                    cg.out.writes(", "); cg.out.writes(lhs_ty); cg.out.writes(" ");
                    cg.emit_vref(rhs); cg.out.writes(")\n");
                    // Extract result value
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = extractvalue {"); cg.out.writes(lhs_ty);
                    cg.out.writes(", i1} %chk"); cg.out.writei(v.id);
                    cg.out.writes(", 0\n");
                    return;
                }

                // Coerce rhs to lhs type if widths differ (mixed numeric)
                // resolve_ty follows sigma chains (stripped by SASI) to get accurate types
                char* lhs_ty = resolve_ty(tm, lhs);
                char* rhs_ty = resolve_ty(tm, rhs);
                // Guard: binary ops on struct types are type errors (soft-warned by typechecker).
                // Emit a safe undef result rather than malformed icmp/fadd on aggregate.
                bool lhs_is_struct = (lhs_ty != null && lhs_ty[0] == '{');
                if (lhs_is_struct)
                {
                    // Str (= { ptr, i64 }) equality/inequality is a CONTENT
                    // comparison, not a type error: route through the runtime's
                    // pride_str_eq (the PrideStr by-value SysV ABI flattens to
                    // (ptr,len) pairs). It used to fall into the placeholder
                    // below — an always-false `add i1 0, 0` for EVERY string
                    // comparison, silently.
                    if (cstr_eq(lhs_ty, "{ ptr, i64 }")
                        && (v.bop == Tt.TOKEN_EQEQ || v.bop == Tt.TOKEN_NEQ))
                    {
                        // String-literal operands are their raw byte-global
                        // via emit_vref; the fat record needs the constant
                        // aggregate form (`{ ptr @.str.N, i64 LEN }`).
                        cg.out.writes("  %seqa."); cg.out.writei(v.id);
                        cg.out.writes(" = extractvalue { ptr, i64 } ");
                        if (lhs != null && lhs.op == ssi_ir::IrOp.IR_CONST_STR) { cgen_emit_str_const_record(cg, lhs); }
                        else { cg.emit_vref(lhs); }
                        cg.out.writes(", 0\n");
                        cg.out.writes("  %seqb."); cg.out.writei(v.id);
                        cg.out.writes(" = extractvalue { ptr, i64 } ");
                        if (lhs != null && lhs.op == ssi_ir::IrOp.IR_CONST_STR) { cgen_emit_str_const_record(cg, lhs); }
                        else { cg.emit_vref(lhs); }
                        cg.out.writes(", 1\n");
                        cg.out.writes("  %seqc."); cg.out.writei(v.id);
                        cg.out.writes(" = extractvalue { ptr, i64 } ");
                        if (rhs != null && rhs.op == ssi_ir::IrOp.IR_CONST_STR) { cgen_emit_str_const_record(cg, rhs); }
                        else { cg.emit_vref(rhs); }
                        cg.out.writes(", 0\n");
                        cg.out.writes("  %seqd."); cg.out.writei(v.id);
                        cg.out.writes(" = extractvalue { ptr, i64 } ");
                        if (rhs != null && rhs.op == ssi_ir::IrOp.IR_CONST_STR) { cgen_emit_str_const_record(cg, rhs); }
                        else { cg.emit_vref(rhs); }
                        cg.out.writes(", 1\n");
                        if (v.bop == Tt.TOKEN_NEQ)
                        {
                            cg.out.writes("  %seqr."); cg.out.writei(v.id);
                            cg.out.writes(" = call i1 @pride_str_eq(ptr %seqa."); cg.out.writei(v.id);
                            cg.out.writes(", i64 %seqb."); cg.out.writei(v.id);
                            cg.out.writes(", ptr %seqc."); cg.out.writei(v.id);
                            cg.out.writes(", i64 %seqd."); cg.out.writei(v.id); cg.out.writes(")\n");
                            cg.out.writes("  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = xor i1 %seqr."); cg.out.writei(v.id); cg.out.writes(", true\n");
                        }
                        else
                        {
                            cg.out.writes("  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = call i1 @pride_str_eq(ptr %seqa."); cg.out.writei(v.id);
                            cg.out.writes(", i64 %seqb."); cg.out.writei(v.id);
                            cg.out.writes(", ptr %seqc."); cg.out.writei(v.id);
                            cg.out.writes(", i64 %seqd."); cg.out.writei(v.id); cg.out.writes(")\n");
                        }
                        return;
                    }
                    // Emit placeholder matching result type: i1 for
                    // comparisons, a frozen undef RECORD when the stamped
                    // result type is an aggregate (a scalar `add i64` where a
                    // `{ ptr, i64 }` is stored downstream is invalid IR —
                    // e.g. an unsupported `Str + Str` warned E0448 must still
                    // assemble), i64 otherwise.
                    char* res_ty2 = (tm != null) ? tm.get(v.id) : null;
                    bool is_cmp_op = (v.bop == Tt.TOKEN_LT || v.bop == Tt.TOKEN_GT
                        || v.bop == Tt.TOKEN_LTEQ || v.bop == Tt.TOKEN_GTEQ
                        || v.bop == Tt.TOKEN_EQEQ || v.bop == Tt.TOKEN_NEQ);
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    if (is_cmp_op) { cg.out.writes(" = add i1 0, 0  ; aggregate cmp (type error, soft)\n"); }
                    else if (res_ty2 != null && (res_ty2[0] == '{' || res_ty2[0] == '%'))
                    {
                        cg.out.writes(" = freeze "); cg.out.writes(res_ty2);
                        cg.out.writes(" undef  ; aggregate op (type error, soft)\n");
                    }
                    else { cg.out.writes(" = add i64 0, 0  ; aggregate op (type error, soft)\n"); }
                    return;
                }
                // If lhs is a bare integer constant (type "i64") and rhs is a
                // narrower integer, use rhs width as the "native" width so we
                // don't needlessly widen `0 - x` (x:i32) to i64.
                // Also handle the case where one side is i64 from a sigma-over-const
                // and the other is a declared narrow type (i32, i8, etc.) — use the
                // narrower declared type as canonical (safe for integer comparisons).
                bool lhs_is_bare_const = (lhs != null && lhs.op == ssi_ir::IrOp.IR_CONST_INT
                                          && lhs_ty != null && lhs_ty[0]=='i' && lhs_ty[1]=='6'
                                          && lhs_ty[2]=='4' && lhs_ty[3]==0);
                bool rhs_is_bare_const = (rhs != null && rhs.op == ssi_ir::IrOp.IR_CONST_INT
                                          && rhs_ty != null && rhs_ty[0]=='i' && rhs_ty[1]=='6'
                                          && rhs_ty[2]=='4' && rhs_ty[3]==0);
                // Use the non-i64-const side's type as the canonical width.
                // For comparisons: if rhs is a bare i64 const and lhs is i64-typed
                // only from sigma fallback (real register is narrower), resolve lhs
                // actual type by walking sigma chain to find the underlying param type.
                bool _is_cmp_here = (v.bop == Tt.TOKEN_EQEQ || v.bop == Tt.TOKEN_NEQ
                    || v.bop == Tt.TOKEN_LT || v.bop == Tt.TOKEN_GT
                    || v.bop == Tt.TOKEN_LTEQ || v.bop == Tt.TOKEN_GTEQ);
                if (_is_cmp_here && rhs_is_bare_const
                    && lhs_ty != null && lhs_ty[0]=='i' && lhs_ty[1]=='6' && lhs_ty[2]=='4' && lhs_ty[3]==0)
                {
                    // Walk sigma chain on lhs to find actual declared type
                    ssi_ir::IrVal* lhs_base_cmp = lhs;
                    { int sd3=0;
                      while (lhs_base_cmp != null && lhs_base_cmp.op == ssi_ir::IrOp.IR_SIGMA
                             && lhs_base_cmp.arg_count >= 1 && lhs_base_cmp.args[0] != null && sd3 < 16)
                      { lhs_base_cmp = lhs_base_cmp.args[0]; sd3++; }
                    }
                    char* lhs_real = (tm != null && lhs_base_cmp != null) ? tm.get(lhs_base_cmp.id) : null;
                    bool lhs_real_narrow = (lhs_real != null && lhs_real[0]=='i'
                        && !(lhs_real[1]=='6' && lhs_real[2]=='4' && lhs_real[3]==0));
                    if (lhs_real_narrow) { lhs_ty = lhs_real; rhs_ty = lhs_real; }
                }
                if (lhs_is_bare_const && rhs_ty != null && rhs_ty[0]=='i'
                    && !(rhs_ty[1]=='6' && rhs_ty[2]=='4' && rhs_ty[3]==0))
                { lhs_ty = rhs_ty; }
                else if (rhs_is_bare_const && lhs_ty != null && lhs_ty[0]=='i'
                         && !(lhs_ty[1]=='6' && lhs_ty[2]=='4' && lhs_ty[3]==0))
                { rhs_ty = lhs_ty; }
                bool lhs_int = (lhs_ty != null && lhs_ty[0] == 'i');
                bool rhs_int = (rhs_ty != null && rhs_ty[0] == 'i');
                bool widths_match = true;
                if (lhs_int && rhs_int && lhs_ty != null && rhs_ty != null)
                {
                    usz ll = strlen(lhs_ty); usz rl = strlen(rhs_ty);
                    if (ll != rl) { widths_match = false; }
                    else { for (usz ci = 0; ci < ll; ci++) { if (lhs_ty[ci] != rhs_ty[ci]) { widths_match = false; break; } } }
                }
                if (!widths_match && rhs != null && lhs_int && rhs_int)
                {
                    // Parse bit widths
                    int lw = 0; int rw = 0;
                    for (usz ci = 1; lhs_ty[ci] >= '0' && lhs_ty[ci] <= '9'; ci++) lw = lw*10+(int)(lhs_ty[ci]-'0');
                    for (usz ci = 1; rhs_ty[ci] >= '0' && rhs_ty[ci] <= '9'; ci++) rw = rw*10+(int)(rhs_ty[ci]-'0');
                    if (lw != rw)
                    {
                        cg.out.writes("  %rhs.coerce."); cg.out.writei(v.id);
                        cg.out.writes(" = ");
                        if (lw > rw) { cg.out.writes(is_signed_int_val(rhs) ? "sext " : "zext "); }
                        else         { cg.out.writes("trunc "); }
                        cg.out.writes(rhs_ty); cg.out.writes(" "); cg.emit_vref(rhs);
                        cg.out.writes(" to "); cg.out.writes(lhs_ty); cg.out.writes("\n");
                        // For comparison ops: if lhs_ty="i64" but actual lhs register is narrower
                        // (e.g. i32 param or phi), we must also coerce lhs to i64 so LLVM sees
                        // matching types on both sides of the icmp.
                        // Detect: emit_vref would emit %vN (an i32), but lhs_ty says i64.
                        // Use a conservative check: is_cmp_op AND lhs is not a const.
                        bool _bop_is_cmp = (v.bop == Tt.TOKEN_EQEQ || v.bop == Tt.TOKEN_NEQ
                            || v.bop == Tt.TOKEN_LT || v.bop == Tt.TOKEN_GT
                            || v.bop == Tt.TOKEN_LTEQ || v.bop == Tt.TOKEN_GTEQ);
                        if (_bop_is_cmp && lw > rw && lhs != null
                            && lhs.op != ssi_ir::IrOp.IR_CONST_INT
                            && lhs.op != ssi_ir::IrOp.IR_CONST_BOOL)
                        {
                            // lhs_ty="i64", rhs_ty=narrower. rhs was sext'd to i64.
                            // Check actual lhs register width via tymap on the unwrapped value.
                            ssi_ir::IrVal* lhs_base = lhs;
                            { int sd=0;
                              while (lhs_base != null && lhs_base.op == ssi_ir::IrOp.IR_SIGMA
                                     && lhs_base.arg_count >= 1 && lhs_base.args[0] != null && sd < 16)
                              { lhs_base = lhs_base.args[0]; sd++; }
                            }
                            char* lhs_real_ty = (tm != null && lhs_base != null) ? tm.get(lhs_base.id) : null;
                            bool lhs_is_narrow = (lhs_real_ty != null && lhs_real_ty[0]=='i'
                                && !(lhs_real_ty[1]=='6' && lhs_real_ty[2]=='4' && lhs_real_ty[3]==0));
                            if (lhs_is_narrow)
                            {
                                cg.out.writes("  %lhs.coerce."); cg.out.writei(v.id);
                                cg.out.writes(is_signed_int_val(lhs) ? " = sext " : " = zext "); cg.out.writes(lhs_real_ty);
                                cg.out.writes(" "); cg.emit_vref(lhs);
                                cg.out.writes(" to "); cg.out.writes(lhs_ty); cg.out.writes("\n");
                            }
                        }
                    }
                }
                // Saturating arithmetic: |+ |- |* → llvm.sadd.sat / ssub.sat / smul
                // Emit BEFORE the general binop path; lhs_ty/rhs_ty are now resolved.
                if (!fp && (v.bop == Tt.TOKEN_PLUS_PIPE ||
                            v.bop == Tt.TOKEN_MINUS_PIPE ||
                            v.bop == Tt.TOKEN_STAR_PIPE))
                {
                    char* sat_ty = (lhs_ty != null && lhs_ty[0] != 0) ? lhs_ty : (char*)"i64";
                    char* sat_name = (v.bop == Tt.TOKEN_PLUS_PIPE)  ? "llvm.sadd.sat"
                                   : (v.bop == Tt.TOKEN_MINUS_PIPE) ? "llvm.ssub.sat"
                                                                     : "llvm.smul.sat";
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = call "); cg.out.writes(sat_ty);
                    cg.out.writes(" @"); cg.out.writes(sat_name);
                    cg.out.writes("."); cg.out.writes(sat_ty);
                    cg.out.writes("("); cg.out.writes(sat_ty); cg.out.writes(" ");
                    cg.emit_vref(lhs);
                    cg.out.writes(", "); cg.out.writes(sat_ty); cg.out.writes(" ");
                    if (!widths_match && lhs_int && rhs_int)
                    { cg.out.writes("%rhs.coerce."); cg.out.writei(v.id); }
                    else { cg.emit_vref(rhs); }
                    cg.out.writes(")\n");
                    return;
                }

                                // For logical && and ||: coerce operands to i1 via icmp
                bool is_logical = (v.bop == Tt.TOKEN_AMPAMP || v.bop == Tt.TOKEN_PIPEPIPE);
                if (is_logical)
                {
                    // Emit icmp ne for each non-i1 operand
                    // Use resolve_ty to follow sigma chains (stripped by SASI)
                    char* l2ty = resolve_ty(tm, lhs);
                    char* r2ty = resolve_ty(tm, rhs);
                    // Only non-i1 integers need coercion to i1 via `icmp ne X, 0`.
                    // Comparison results (i1), bool fields, and already-i1 values skip this.
                    bool l2_is_i1 = (l2ty == null || (l2ty[0]=='i' && l2ty[1]=='1' && l2ty[2]==0));
                    bool r2_is_i1 = (r2ty == null || (r2ty[0]=='i' && r2ty[1]=='1' && r2ty[2]==0));
                    bool lhs_needs_coerce = (!l2_is_i1 && l2ty != null && l2ty[0] == 'i');
                    bool rhs_needs_coerce = (!r2_is_i1 && r2ty != null && r2ty[0] == 'i');
                    if (lhs_needs_coerce)
                    {
                        cg.out.writes("  %lhs.i1."); cg.out.writei(v.id);
                        cg.out.writes(" = icmp ne "); cg.out.writes(l2ty);
                        cg.out.writes(" "); cg.emit_vref(lhs); cg.out.writes(", 0\n");
                    }
                    if (rhs_needs_coerce)
                    {
                        cg.out.writes("  %rhs.i1."); cg.out.writei(v.id);
                        cg.out.writes(" = icmp ne "); cg.out.writes(r2ty);
                        cg.out.writes(" "); cg.emit_vref(rhs); cg.out.writes(", 0\n");
                    }
                    // Emit the and/or on i1 operands
                    cg.out.writes("  %v"); cg.out.writei(v.id); cg.out.writes(" = ");
                    cg.emit_binop(v.bop, lhs, tm);
                    cg.out.writes(" i1 ");
                    if (lhs_needs_coerce) { cg.out.writes("%lhs.i1."); cg.out.writei(v.id); }
                    else { cg.emit_vref(lhs); }
                    cg.out.writes(", ");
                    if (rhs_needs_coerce) { cg.out.writes("%rhs.i1."); cg.out.writei(v.id); }
                    else { cg.emit_vref(rhs); }
                    cg.out.writes("\n");
                    return;
                }
                // Pointer arithmetic: ptr +/- int → GEP.  The index scales by
                // the POINTEE size (v.md §15: pointer arithmetic "advances by
                // element size") — `arr + 1` on a *i64 steps 8 bytes, on a
                // *u8 one byte.  When the pointee type is unknown (untyped
                // closure paths) keep the historical byte-scale (1) rather
                // than invent a size.
                if ((v.bop == Tt.TOKEN_PLUS || v.bop == Tt.TOKEN_MINUS)
                    && lhs != null && rhs != null)
                {
                    char* lty_pa = (tm != null) ? tm.get(lhs.id) : null;
                    if (lty_pa != null && lty_pa[0] == 'p')
                    {
                        char* rty_pa = (tm != null) ? tm.get(rhs.id) : null;
                        if (rty_pa == null || rty_pa[0] == 0) rty_pa = (char*)"i64";
                        // Element scale from the lhs child annotation (*T → T).
                        long pa_scale = 1;
                        Node* pa_lnode = (v.src != null && v.src.child_count >= 1)
                                         ? v.src.children[0] : null;
                        Node* pa_lann = pa_lnode != null ? pa_lnode.type_annotation : null;
                        if (pa_lann != null && pa_lann.kind == Nk.NODE_TYPE_PTR
                            && pa_lann.child_count >= 1 && pa_lann.children[0] != null)
                        {
                            pa_scale = sizeof_type_x86(pa_lann.children[0]);
                            if (pa_scale < 1) { pa_scale = 1; }
                        }
                        // GEP index MUST be an integer — ptrtoint if rhs is ptr type
                        bool rhs_is_ptr_gep = (rty_pa[0] == 'p');
                        if (rhs_is_ptr_gep)
                        {
                            cg.out.writes("  %gep.idx.v"); cg.out.writei(v.id);
                            cg.out.writes(" = ptrtoint ptr "); cg.emit_vref(rhs);
                            cg.out.writes(" to i64\n");
                            rty_pa = (char*)"i64";
                        }
                        // Scale the (integer) index by the pointee size.
                        bool pa_scaled = (pa_scale != 1);
                        if (pa_scaled)
                        {
                            cg.out.writes("  %ptra.sc.v"); cg.out.writei(v.id);
                            cg.out.writes(" = mul "); cg.out.writes(rty_pa); cg.out.writes(" ");
                            if (rhs_is_ptr_gep) { cg.out.writes("%gep.idx.v"); cg.out.writei(v.id); }
                            else { cg.emit_vref(rhs); }
                            cg.out.writes(", "); cg.out.writei(pa_scale); cg.out.writes("\n");
                        }
                        if (v.bop == Tt.TOKEN_MINUS)
                        {
                            cg.out.writes("  %ptra.neg.v"); cg.out.writei(v.id);
                            cg.out.writes(" = sub "); cg.out.writes(rty_pa);
                            cg.out.writes(" 0, ");
                            if (pa_scaled) { cg.out.writes("%ptra.sc.v"); cg.out.writei(v.id); }
                            else if (rhs_is_ptr_gep) { cg.out.writes("%gep.idx.v"); cg.out.writei(v.id); }
                            else { cg.emit_vref(rhs); }
                            cg.out.writes("\n");
                            cg.out.writes("  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = getelementptr inbounds i8, ptr ");
                            cg.emit_vref(lhs); cg.out.writes(", ");
                            cg.out.writes(rty_pa); cg.out.writes(" %ptra.neg.v"); cg.out.writei(v.id);
                        }
                        else
                        {
                            cg.out.writes("  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = getelementptr inbounds i8, ptr ");
                            cg.emit_vref(lhs); cg.out.writes(", ");
                            cg.out.writes(rty_pa); cg.out.writes(" ");
                            if (pa_scaled) { cg.out.writes("%ptra.sc.v"); cg.out.writei(v.id); }
                            else if (rhs_is_ptr_gep) { cg.out.writes("%gep.idx.v"); cg.out.writei(v.id); }
                            else { cg.emit_vref(rhs); }
                        }
                        cg.out.writes("\n");
                        return;
                    }
                }
                // Standard arithmetic/comparison binary op
                // For comparisons: if operands have mismatched ptr/int types, coerce
                bool is_cmp_op = (v.bop == Tt.TOKEN_EQEQ || v.bop == Tt.TOKEN_NEQ
                    || v.bop == Tt.TOKEN_NEQ_UNI || v.bop == Tt.TOKEN_LT
                    || v.bop == Tt.TOKEN_LTEQ || v.bop == Tt.TOKEN_GT || v.bop == Tt.TOKEN_GTEQ);
                if (is_cmp_op && lhs != null && rhs != null)
                {
                    char* lty = (tm != null) ? tm.get(lhs.id) : null;
                    char* rty = (tm != null) ? tm.get(rhs.id) : null;
                    bool l_ptr = (lty != null && lty[0] == 'p');
                    bool r_ptr = (rty != null && rty[0] == 'p');
                    bool l_int = (lty != null && lty[0] == 'i');
                    bool r_int = (rty != null && rty[0] == 'i');
                    // ptr vs int comparison: ptrtoint the ptr operand
                    if (l_ptr && r_int && rty != null)
                    {
                        cg.out.writes("  %lhs.pti."); cg.out.writei(v.id);
                        cg.out.writes(" = ptrtoint ptr "); cg.emit_vref(lhs);
                        cg.out.writes(" to "); cg.out.writes(rty); cg.out.writes("\n");
                    }
                    else if (r_ptr && l_int && lty != null)
                    {
                        cg.out.writes("  %rhs.pti."); cg.out.writei(v.id);
                        cg.out.writes(" = ptrtoint ptr "); cg.emit_vref(rhs);
                        cg.out.writes(" to "); cg.out.writes(lty); cg.out.writes("\n");
                    }
                }
                // After possible rhs coerce: update type table to actual emit type (lhs_ty).
                // EXCEPT for comparison ops which always produce i1 (never widen to lhs_ty).
                // Also update when bare-const narrowing changed the effective type.
                bool bare_const_narrowed = (lhs_is_bare_const || rhs_is_bare_const)
                    && lhs_int && lhs_ty != null
                    && !(lhs_ty[0]=='i'&&lhs_ty[1]=='6'&&lhs_ty[2]=='4'&&lhs_ty[3]==0);
                if ((!widths_match || bare_const_narrowed) && lhs_int && rhs_int && tm != null && !is_cmp_op)
                {
                    tm.set(v.id, lhs_ty != null ? lhs_ty : (char*)"i64");
                }
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = ");
                cg.emit_binop(v.bop, lhs, tm);
                // Write the instruction type (use resolved lhs_ty for accuracy)
                // This replaces the generic writes_ty(lhs.id) which misses sigmas.
                bool binop_wrote_type = false;
                // For mixed ptr/int cmp, use the int operand type
                if (is_cmp_op && lhs != null && rhs != null)
                {
                    char* lty2 = (tm != null) ? tm.get(lhs.id) : null;
                    char* rty2 = (tm != null) ? tm.get(rhs.id) : null;
                    bool l2_ptr = (lty2 != null && lty2[0] == 'p');
                    bool r2_ptr = (rty2 != null && rty2[0] == 'p');
                    if ((l2_ptr && rty2 != null && rty2[0] == 'i') || (r2_ptr && lty2 != null && lty2[0] == 'i'))
                    {
                        char* int_ty = (l2_ptr && rty2 != null) ? rty2 : lty2;
                        cg.out.writes(" "); cg.out.writes(int_ty != null ? int_ty : "i64"); cg.out.writes(" ");
                        // Emit lhs: ptrtoint result or original
                        if (l2_ptr) { cg.out.writes("%lhs.pti."); cg.out.writei(v.id); }
                        else { cg.emit_vref(lhs); }
                        cg.out.writes(", ");
                        // Emit rhs: ptrtoint result or original
                        if (r2_ptr) { cg.out.writes("%rhs.pti."); cg.out.writei(v.id); }
                        else { cg.emit_vref(rhs); }
                        cg.out.writes("\n");
                        return; // ptr/int comparison handled completely above
                    }
                }
                cg.out.writes(" ");
                // Write the instruction type.
                // For comparisons: prefer the narrower/declared integer type over the
                // tymap "i64" fallback, which can arise from sigma-over-const-int chains.
                // If the type map entry for the BIN result itself is narrower than
                // the resolved lhs operand type (e.g. result is i32 but lhs was a
                // i64 literal), use the narrower declared result type. This ensures
                // wrapping/saturating ops on i32 variables stay i32.
                char* bin_result_ty = (tm != null) ? tm.get(v.id) : null;
                if (bin_result_ty != null && lhs_ty != null
                    && bin_result_ty[0] == 'i' && lhs_ty[0] == 'i')
                {
                    long bn_w = 0; long lhs_w = 0;
                    char* bp = bin_result_ty+1; while(*bp>='0'&&*bp<='9'){bn_w=bn_w*10+(long)(*bp-'0');bp++;}
                    char* lp = lhs_ty+1;        while(*lp>='0'&&*lp<='9'){lhs_w=lhs_w*10+(long)(*lp-'0');lp++;}
                    // Do NOT apply narrowing for comparison ops: icmp always uses the
                    // operand type (i64, i32, …), not the i1 result type.
                    if (bn_w > 0 && bn_w < lhs_w && !is_cmp_op) { lhs_ty = bin_result_ty; rhs_ty = bin_result_ty; }
                }
                char* actual_lhs_ty = lhs_ty;
                // lhs_coerced: tracks whether we pre-emitted a sext of lhs to i64
                // (set during the pre-emit phase above, before this instruction line)
                // Override with callee return type when LHS is a function call returning
                // a narrow type (u8/i8 etc.) — prevents `icmp eq i64` on i8 vals.
                if (is_cmp_op && lhs != null && lhs.op == ssi_ir::IrOp.IR_CALL)
                {
                    ssi_ir::IrVal* callee_v = lhs.arg_count >= 1 ? lhs.args[0] : null;
                    Node* fn_d = (callee_v != null) ? callee_v.binder : null;
                    if (fn_d != null && fn_d.kind == Nk.NODE_DECL_FN)
                    {
                        char[TYMAP_ENTRY] call_ret_ty;
                        call_ret_ty[0] = 0;
                        fn_param_llvm_type(fn_d, -1, &call_ret_ty[0], TYMAP_ENTRY);
                        // Only use this if it's a non-void narrower integer type
                        if (call_ret_ty[0] == 'i' && !(call_ret_ty[1]=='6' && call_ret_ty[2]=='4' && call_ret_ty[3]==0))
                        {
                            actual_lhs_ty = &call_ret_ty[0];
                            // Also fix rhs type to match
                            if (rhs_is_bare_const) { rhs_ty = actual_lhs_ty; }
                        }
                    }
                }
                // Determine if we coerced the lhs (pre-emitted sext in the pre-emit phase).
                // This happens when lhs_ty="i64", rhs_ty=narrower, widths_match=false,
                // is_cmp_op, and the real lhs register is narrower than i64.
                bool lhs_coerced = false;
                if (is_cmp_op && !widths_match && actual_lhs_ty != null
                    && actual_lhs_ty[0]=='i' && actual_lhs_ty[1]=='6' && actual_lhs_ty[2]=='4' && actual_lhs_ty[3]==0
                    && lhs != null && lhs.op != ssi_ir::IrOp.IR_CONST_INT && lhs.op != ssi_ir::IrOp.IR_CONST_BOOL)
                {
                    ssi_ir::IrVal* lb2 = lhs;
                    { int sd2=0;
                      while (lb2 != null && lb2.op == ssi_ir::IrOp.IR_SIGMA
                             && lb2.arg_count >= 1 && lb2.args[0] != null && sd2 < 16)
                      { lb2 = lb2.args[0]; sd2++; }
                    }
                    char* lb2_ty = (tm != null && lb2 != null) ? tm.get(lb2.id) : null;
                    lhs_coerced = (lb2_ty != null && lb2_ty[0]=='i'
                        && !(lb2_ty[1]=='6' && lb2_ty[2]=='4' && lb2_ty[3]==0));
                }
                if (actual_lhs_ty != null && actual_lhs_ty[0] != 0)
                { cg.out.writes(actual_lhs_ty); }
                else { cg.writes_ty(tm, lhs != null ? lhs.id : -1); }
                cg.out.writes(" ");
                if (lhs_coerced) { cg.out.writes("%lhs.coerce."); cg.out.writei(v.id); }
                else { cg.emit_vref(lhs); }
                cg.out.writes(", ");
                if (is_logical)
                {
                    char* r3ty = (tm != null && rhs != null) ? tm.get(rhs.id) : null;
                    bool rhs_not_i1 = (r3ty != null && r3ty[0] == 'i' && !(r3ty[1] == '1' && r3ty[2] == 0));
                    if (rhs_not_i1) { cg.out.writes("%rhs.i1."); cg.out.writei(v.id); }
                    else { cg.emit_vref(rhs); }
                }
                else if (!widths_match && lhs_int && rhs_int)
                {
                    cg.out.writes("%rhs.coerce."); cg.out.writei(v.id);
                }
                else if (fp && rhs != null && rhs.op == ssi_ir::IrOp.IR_CONST_INT)
                {
                    // Float op: integer constant must be emitted as float literal
                    cg.out.writef((double)(long)rhs.ival);
                }
                else { cg.emit_vref(rhs); }
                cg.out.writes("\n");
            }

        case ssi_ir::IrOp.IR_UN:
            {
                ssi_ir::IrVal* arg = v.arg_count >= 1 ? v.args[0] : null;
                bool fp = is_float_val_ty(arg, tm);
                // Note: name (%vN) is written inside each branch for clean output
                if (v.bop == Tt.TOKEN_MINUS)
                {
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = ");
                    cg.out.writes(fp ? "fneg " : "sub nsw ");
                    cg.writes_ty(tm, arg != null ? arg.id : -1);
                    if (!fp) { cg.out.writes(" 0, "); }
                    else { cg.out.writes(" "); }
                    cg.emit_vref(arg);
                    cg.out.writes("\n");
                }
                else if (v.bop == Tt.TOKEN_BANG)
                {
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = xor i1 "); cg.emit_vref(arg);
                    cg.out.writes(", 1\n");
                }
                else if (v.bop == Tt.TOKEN_STAR)
                {
                    // Pointer dereference *p → load (if operand is ptr)
                    // If operand is not ptr (type error), inttoptr first.
                    char* load_ty = (tm != null) ? tm.get(v.id) : null;
                    if (load_ty == null || load_ty[0] == 0) load_ty = (char*)"i64";
                    // If the pointer arg has a *T annotation and T is scalar+narrower,
                    // use T as the load type — the tymap may have promoted to i64 via
                    // phi merging, but the actual pointed-to element is narrower (e.g.
                    // *i32 → load i32, not i64). This prevents the phi→i64 promotion
                    // from widening deref loads of *i32/*u8/etc. fields.
                    if (arg != null && arg.src != null)
                    {
                        Node* asrc = arg.src;
                        // For calls returning *T: the call's src is the fn-type node;
                        // unwrap TYPE_FN return, or use the binder's type_annotation directly.
                        Node* aann = asrc.type_annotation;
                        if (aann != null && aann.kind == Nk.NODE_TYPE_FN && aann.child_count >= 2)
                        {
                            Node* aret = aann.children[1];
                            if (aret != null && aret.kind == Nk.NODE_EFFECT_ROW && aret.child_count >= 1)
                            { aret = aret.children[0]; }
                            aann = aret;
                        }
                        if (aann != null && aann.kind == Nk.NODE_TYPE_PTR && aann.child_count >= 1
                            && aann.children[0] != null)
                        {
                            char[TYMAP_ENTRY] ptbuf3; ptbuf3[0] = 0;
                            type_to_llvm_buf(aann.children[0], &ptbuf3[0], TYMAP_ENTRY, 0);
                            if (ptbuf3[0] != 0 && !(ptbuf3[0]=='v'&&ptbuf3[1]=='o')
                                && ptbuf3[0] != '{' && ptbuf3[0] != '['
                                && ptbuf3[0] != 'p'  // keep ptr loads as the tymap type
                                && load_ty[0] == 'i' && ptbuf3[0] == 'i')
                            {
                                // Both are integer types — use the narrower one.
                                long lw3=0;
                                long pw3=0;
                                char* lp3=load_ty+1; while(*lp3>='0'&&*lp3<='9'){lw3=lw3*10+(long)(*lp3-'0');lp3++;}
                                char* pp3=&ptbuf3[0]+1; while(*pp3>='0'&&*pp3<='9'){pw3=pw3*10+(long)(*pp3-'0');pp3++;}
                                if (pw3 > 0 && pw3 < lw3)
                                {
                                    // Pointee is narrower: use it and fix up the tymap.
                                    load_ty = &ptbuf3[0];
                                    if (tm != null) { tm.set(v.id, load_ty); }
                                }
                            }
                        }
                    }
                    char* arg_base_ty = (tm != null && arg != null) ? tm.get(arg.id) : null;
                    bool arg_is_ptr = (arg_base_ty != null && arg_base_ty[0] == 'p');
                    if (!arg_is_ptr && arg_base_ty != null && arg_base_ty[0] == 'i')
                    {
                        // Non-ptr deref: inttoptr then load
                        cg.out.writes("\n  %deref.ptr.v"); cg.out.writei(v.id);
                        cg.out.writes(" = inttoptr "); cg.out.writes(arg_base_ty);
                        cg.out.writes(" "); cg.emit_vref(arg); cg.out.writes(" to ptr\n");
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = load "); cg.out.writes(load_ty);
                        cg.out.writes(", ptr %deref.ptr.v"); cg.out.writei(v.id); cg.out.writes("\n");
                    }
                    else
                    {
                        // ptr deref — need to write the result name first
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = load "); cg.out.writes(load_ty);
                        cg.out.writes(", ptr "); cg.emit_vref(arg); cg.out.writes("\n");
                    }
                }
                else if (v.bop == Tt.TOKEN_AMP)
                {
                    // &expr: address-of — emit alloca + store, return ptr
                    char* va = (tm != null && arg != null) ? tm.get(arg.id) : null;
                    if (va == null || va[0] == 0) va = (char*)"i64";
                    cg.out.writes("  %addr.v"); cg.out.writei(v.id);
                    cg.out.writes(" = alloca "); cg.out.writes(va); cg.out.writes("\n");
                    cg.out.writes("  store "); cg.out.writes(va); cg.out.writes(" ");
                    if (arg != null) { cg.emit_vref(arg); } else { cg.out.writes("undef"); }
                    cg.out.writes(", ptr %addr.v"); cg.out.writei(v.id); cg.out.writes("\n");
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = getelementptr inbounds "); cg.out.writes(va);
                    cg.out.writes(", ptr %addr.v"); cg.out.writei(v.id); cg.out.writes(", i32 0\n");
                }
                else if (v.bop == Tt.TOKEN_TILDE)
                {
                    // Bitwise NOT: xor T %arg, -1
                    char* nt = (tm != null && arg != null) ? tm.get(arg.id) : null;
                    if (nt == null || nt[0] == 0) nt = (char*)"i64";
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = xor "); cg.out.writes(nt);
                    cg.out.writes(" "); cg.emit_vref(arg);
                    cg.out.writes(", -1\n");
                }
                else
                {
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = bitcast ");
                    cg.writes_ty(tm, arg != null ? arg.id : -1);
                    cg.out.writes(" "); cg.emit_vref(arg);
                    cg.out.writes(" to "); cg.writes_ty(tm, v.id); cg.out.writes("\n");
                }
            }

        case ssi_ir::IrOp.IR_CALL:
            {
                // args[0] = callee, args[1..] = arguments
                ssi_ir::IrVal* callee_val = v.arg_count >= 1 ? v.args[0] : null;
                bool is_void = false;
                if (v.src != null && v.src.type_annotation != null)
                {
                    Node* rt = v.src.type_annotation;
                    is_void = (rt.kind == Nk.NODE_EXPR_UNIT
                               || rt.kind == Nk.NODE_TYPE_BOTTOM);
                }

                // Pre-emit inttoptr for non-ptr callee — MUST be before the call instruction line
                bool callee_fat_call = false;
                {
                    char* cty_pre = (tm != null && callee_val != null) ? tm.get(callee_val.id) : null;
                    bool known_fn_ref = (callee_val != null
                        && callee_val.op == ssi_ir::IrOp.IR_UNKNOWN
                        && callee_val.binder != null
                        && callee_val.binder.kind == Nk.NODE_DECL_FN);
                    // Only emit inttoptr for genuine integer types (iN). Never for void,
                    // struct {}, ptr (already a ptr), or empty/unknown types.
                    bool cty_is_int = (cty_pre != null && cty_pre[0] == 'i'
                        && cty_pre[1] >= '0' && cty_pre[1] <= '9');
                    if (!known_fn_ref && cty_is_int)
                    {
                        cg.out.writes("  %callee.ptr."); cg.out.writei(v.id);
                        cg.out.writes(" = inttoptr "); cg.out.writes(cty_pre);
                        cg.out.writes(" "); cg.emit_vref(callee_val);
                        cg.out.writes(" to ptr\n");
                    }
                    // Fat fn-typed callee: extract the code/env slots now so the
                    // call line can reference them (uniform indirect ABI).
                    bool known_closure_ref = (callee_val != null
                        && callee_val.op == ssi_ir::IrOp.IR_UNKNOWN
                        && callee_val.binder != null
                        && callee_val.binder.kind == Nk.NODE_EXPR_CLOSURE);
                    callee_fat_call = (cty_pre != null && cty_pre[0] == '{'
                        && !known_fn_ref && !known_closure_ref);
                    if (callee_fat_call)
                    {
                        cg.out.writes("  %fptr."); cg.out.writei(v.id);
                        cg.out.writes(" = extractvalue { ptr, ptr } ");
                        cg.emit_vref(callee_val);
                        cg.out.writes(", 0\n");
                        cg.out.writes("  %fenv."); cg.out.writei(v.id);
                        cg.out.writes(" = extractvalue { ptr, ptr } ");
                        cg.emit_vref(callee_val);
                        cg.out.writes(", 1\n");
                    }
                }
                // Arg coercion: emit trunc/sext/sitofp before the call line
                Node* callee_decl2 = null;
                if (callee_val != null && callee_val.binder != null
                    && callee_val.binder.kind == Nk.NODE_DECL_FN)
                { callee_decl2 = callee_val.binder; }
                // Indirect (fat) call: the callee's fn TYPE annotation drives
                // parameter marshalling instead.
                Node* callee_sig = (callee_decl2 == null) ? callee_fn_type(callee_val) : null;
                // A closure REFERENCE callee goes through the closure early-exit
                // below, which marshals args against the thunk's own parameter
                // types — this generic coercion loop would only double (and
                // mistype, via the i64 fallback) that work.
                bool callee_is_closure_pre = (callee_val != null
                    && callee_val.op == ssi_ir::IrOp.IR_UNKNOWN
                    && callee_val.binder != null
                    && callee_val.binder.kind == Nk.NODE_EXPR_CLOSURE);
                if (!callee_is_closure_pre)
                {
                    int apos = 0;
                    for (usz ia = 1; ia < v.arg_count; ia++)
                    {
                        ssi_ir::IrVal* aval_c = v.args[ia];
                        if (aval_c == null) { continue; }
                        // Unwrap sigma chain for tymap lookup (same as emit_vref does).
                        // The CALL arg may be a sigma wrapping the real value; the tymap
                        // entry lives on the underlying phi/instruction, not the sigma shell.
                        ssi_ir::IrVal* aval_c_base = aval_c;
                        {
                            int sc = 0;
                            while (aval_c_base != null
                                   && aval_c_base.op == ssi_ir::IrOp.IR_SIGMA
                                   && aval_c_base.arg_count >= 1
                                   && aval_c_base.args[0] != null
                                   && sc < 16)
                            { aval_c_base = aval_c_base.args[0]; sc++; }
                        }
                        char* aty_c = (tm != null) ? tm.get(aval_c_base.id) : null;
                        if (aty_c == null || aty_c[0] == 0) { aty_c = (char*)"i64"; }
                        if (aty_c[0]=='v'&&aty_c[1]=='o') { continue; }
                        // Same guard as in the emit loop: only skip args[1] fn-value
                        // when the callee itself is not a known named function.
                        bool callee_named_pre = (callee_val != null
                            && callee_val.op == ssi_ir::IrOp.IR_UNKNOWN
                            && callee_val.binder != null
                            && callee_val.binder.kind == Nk.NODE_DECL_FN);
                        if (!callee_named_pre && ia==1 && aval_c.op==ssi_ir::IrOp.IR_UNKNOWN
                            && aval_c.binder!=null
                            && aval_c.binder.kind==Nk.NODE_DECL_FN) { continue; }
                        char[TYMAP_ENTRY] ptbuf;
                        call_param_type(callee_decl2, callee_sig, apos, &ptbuf[0], TYMAP_ENTRY);
                        apos++;
                        char* pt = &ptbuf[0];
                        if (pt[0]==0 || (pt[0]=='v'&&pt[1]=='o')) { continue; }
                        // Quick equal check
                        bool eq = true;
                        {
                            usz ql1 = strlen(aty_c); usz ql2 = strlen(pt);
                            if (ql1 != ql2) { eq = false; }
                            else { for (usz qc=0;qc<ql1;qc++) if (aty_c[qc]!=pt[qc]) { eq=false; break; } }
                        }
                        if (eq) { continue; }
                        // Aggregate→aggregate is a MULTI-instruction rewrite
                        // handled complete with its own instruction lines (the
                        // final insertvalue carries the canonical name) — all
                        // other coercions are single instructions continuing
                        // the shared prefix line below.
                        bool agg_to_agg = (aty_c[0]=='{' && pt[0]=='{');
                        // Emit coerce instruction
                        if (!agg_to_agg)
                        {
                            cg.out.writes("  %arg.c."); cg.out.writeu(ia);
                            cg.out.writes(".v"); cg.out.writei(v.id);
                        }
                        bool ai_c = aty_c[0]=='i'; bool pi_c = pt[0]=='i';
                        bool af_c = aty_c[0]=='f'||aty_c[0]=='d'; bool pf_c = pt[0]=='f'||pt[0]=='d';
                        if (ai_c && pi_c)
                        {
                            // Integer width change: measure by counting digits after the 'i'/'u'
                            long an=0; long pn=0;
                            char* ap=aty_c+1; while(*ap>='0'&&*ap<='9'){an=an*10+(long)(*ap-'0');ap++;}
                            char* pp=pt+1;    while(*pp>='0'&&*pp<='9'){pn=pn*10+(long)(*pp-'0');pp++;}
                            if (an > pn) { cg.out.writes(" = trunc "); }
                            else if (!is_signed_int_val(aval_c)) { cg.out.writes(" = zext "); }
                            else         { cg.out.writes(" = sext ");  }
                            cg.out.writes(aty_c); cg.out.writes(" "); cg.emit_vref(aval_c);
                            cg.out.writes(" to "); cg.out.writes(pt); cg.out.writes("\n");
                        }
                        else if (ai_c && pf_c)
                        {
                            cg.out.writes(" = sitofp "); cg.out.writes(aty_c); cg.out.writes(" ");
                            cg.emit_vref(aval_c); cg.out.writes(" to "); cg.out.writes(pt); cg.out.writes("\n");
                        }
                        else if (af_c && pi_c)
                        {
                            cg.out.writes(" = fptosi "); cg.out.writes(aty_c); cg.out.writes(" ");
                            cg.emit_vref(aval_c); cg.out.writes(" to "); cg.out.writes(pt); cg.out.writes("\n");
                        }
                        else if (ai_c && pt[0]=='p')
                        {
                            cg.out.writes(" = inttoptr "); cg.out.writes(aty_c); cg.out.writes(" ");
                            cg.emit_vref(aval_c); cg.out.writes(" to ptr\n");
                        }
                        else if (aty_c[0]=='p' && pi_c)
                        {
                            cg.out.writes(" = ptrtoint ptr "); cg.emit_vref(aval_c);
                            cg.out.writes(" to "); cg.out.writes(pt); cg.out.writes("\n");
                        }
                        else if (aty_c[0]=='{' && pt[0]=='p')
                        {
                            // Aggregate → ptr:
                            // - String literal: GEP to get char* from [N x i8] global
                            // - Fat closure ptr {ptr,ptr}: extractvalue field 0
                            bool is_str_const = (aval_c != null && aval_c.op == ssi_ir::IrOp.IR_CONST_STR);
                            if (is_str_const)
                            {
                                // Compute DECODED byte count for GEP array type (must match constant)
                            usz gs_cstart = 0; usz gs_clen = aval_c.slen;
                            if (gs_clen >= 2 && aval_c.sptr != null
                                && aval_c.sptr[0] == '"' && aval_c.sptr[gs_clen-1] == '"')
                            { gs_cstart = 1; gs_clen -= 2; }
                            usz gs_decoded = 0;
                            { usz gk = gs_cstart; usz gk_end = gs_cstart + gs_clen;
                              while (gk < gk_end) {
                                if (aval_c.sptr[gk] == '\\' && gk+1 < gk_end) {
                                    char ge = aval_c.sptr[gk+1];
                                    if (ge == 'x' && gk+3 < gk_end) { gk += 4; }
                                    else { gk += 2; }
                                    gs_decoded++;
                                } else { gk++; gs_decoded++; }
                              }
                            }
                            cg.out.writes(" = getelementptr inbounds [");
                                cg.out.writeu(gs_decoded + 1);
                                cg.out.writes(" x i8], ptr @.str.");
                                cg.out.writei(aval_c.id);
                                cg.out.writes(", i32 0, i32 0\n");
                            }
                            else
                            {
                                cg.out.writes(" = extractvalue { ptr, ptr } ");
                                cg.emit_vref(aval_c); cg.out.writes(", 0\n");
                            }
                        }
                        else if (aty_c[0]=='{' && pt[0]=='{')
                        {
                            // Aggregate → aggregate: rebuild the value with the
                            // callee's parameter type via per-element extract +
                            // scalar coercion + insert. (Aggregate bitcast has
                            // never been valid LLVM; it appeared when a tuple
                            // argument met a tuple parameter of a different —
                            // but elementwise-convertible — type.)
                            char[STRUCT_SPLIT_CAP * STRUCT_SPLIT_LEN] from_elems;
                            char[STRUCT_SPLIT_CAP * STRUCT_SPLIT_LEN] to_elems;
                            int nf = split_struct_ty(aty_c, &from_elems[0], STRUCT_SPLIT_LEN);
                            int nt = split_struct_ty(pt,    &to_elems[0],   STRUCT_SPLIT_LEN);
                            if (nf > 0 && nf == nt)
                            {
                                for (int ei = 0; ei < nf; ei++)
                                {
                                    char* fe = (char*)&from_elems[0] + (usz)ei * STRUCT_SPLIT_LEN;
                                    char* te = (char*)&to_elems[0]   + (usz)ei * STRUCT_SPLIT_LEN;
                                    cg.out.writes("  %arg.c."); cg.out.writeu(ia);
                                    cg.out.writes(".x"); cg.out.writei((long)ei);
                                    cg.out.writes(".v"); cg.out.writei(v.id);
                                    cg.out.writes(" = extractvalue "); cg.out.writes(aty_c);
                                    cg.out.writes(" "); cg.emit_vref(aval_c);
                                    cg.out.writes(", "); cg.out.writei((long)ei); cg.out.writes("\n");
                                    // Element coercion (trunc/sext/fpext/…) when needed
                                    char* eopc = coerce_op(fe, te);
                                    if (eopc != null)
                                    {
                                        cg.out.writes("  %arg.c."); cg.out.writeu(ia);
                                        cg.out.writes(".w"); cg.out.writei((long)ei);
                                        cg.out.writes(".v"); cg.out.writei(v.id);
                                        cg.out.writes(" = "); cg.out.writes(eopc);
                                        cg.out.writes(" "); cg.out.writes(fe);
                                        cg.out.writes(" %arg.c."); cg.out.writeu(ia);
                                        cg.out.writes(".x"); cg.out.writei((long)ei);
                                        cg.out.writes(".v"); cg.out.writei(v.id);
                                        cg.out.writes(" to "); cg.out.writes(te); cg.out.writes("\n");
                                    }
                                    // Insert; the LAST insertvalue carries the canonical
                                    // coerced-arg name the call site references.
                                    bool last_i = (ei == nf - 1);
                                    if (last_i)
                                    {
                                        cg.out.writes("  %arg.c."); cg.out.writeu(ia);
                                        cg.out.writes(".v"); cg.out.writei(v.id);
                                    }
                                    else
                                    {
                                        cg.out.writes("  %arg.c."); cg.out.writeu(ia);
                                        cg.out.writes(".i"); cg.out.writei((long)ei);
                                        cg.out.writes(".v"); cg.out.writei(v.id);
                                    }
                                    cg.out.writes(" = insertvalue "); cg.out.writes(pt);
                                    if (ei == 0)
                                    {
                                        cg.out.writes(" undef");
                                    }
                                    else
                                    {
                                        cg.out.writes(" %arg.c."); cg.out.writeu(ia);
                                        cg.out.writes(".i"); cg.out.writei((long)(ei - 1));
                                        cg.out.writes(".v"); cg.out.writei(v.id);
                                    }
                                    cg.out.writes(", ");
                                    cg.out.writes(te);
                                    if (eopc != null)
                                    {
                                        cg.out.writes(" %arg.c."); cg.out.writeu(ia);
                                        cg.out.writes(".w"); cg.out.writei((long)ei);
                                        cg.out.writes(".v"); cg.out.writei(v.id);
                                    }
                                    else
                                    {
                                        cg.out.writes(" %arg.c."); cg.out.writeu(ia);
                                        cg.out.writes(".x"); cg.out.writei((long)ei);
                                        cg.out.writes(".v"); cg.out.writei(v.id);
                                    }
                                    cg.out.writes(", "); cg.out.writei((long)ei); cg.out.writes("\n");
                                }
                            }
                            else
                            {
                                cg.out.writes("  %arg.c."); cg.out.writeu(ia);
                                cg.out.writes(".v"); cg.out.writei(v.id);
                                cg.out.writes(" = bitcast "); cg.out.writes(aty_c); cg.out.writes(" ");
                                cg.emit_vref(aval_c); cg.out.writes(" to "); cg.out.writes(pt); cg.out.writes("\n");
                            }
                        }
                        else if (aty_c[0]=='{' && pt[0]=='{')
                        {
                            // Aggregate → aggregate, caught by the generic
                            // fallback because the exact-shape comparison
                            // above rejected it first (e.g. a value whose
                            // tymap string differs textually from the
                            // callee's parameter struct but is elementwise
                            // compatible: enum tagged repr, nested tuples).
                            // Rebuild per element like the main path does —
                            // silent bitcasts of aggregates are invalid LLVM.
                            char[STRUCT_SPLIT_CAP * STRUCT_SPLIT_LEN] from_elems2;
                            char[STRUCT_SPLIT_CAP * STRUCT_SPLIT_LEN] to_elems2;
                            int nf2 = split_struct_ty(aty_c, &from_elems2[0], STRUCT_SPLIT_LEN);
                            int nt2 = split_struct_ty(pt,    &to_elems2[0],   STRUCT_SPLIT_LEN);
                            if (nf2 > 0 && nf2 == nt2)
                            {
                                for (int ei2 = 0; ei2 < nf2; ei2++)
                                {
                                    char* fe2 = (char*)&from_elems2[0] + (usz)ei2 * STRUCT_SPLIT_LEN;
                                    char* te2 = (char*)&to_elems2[0]   + (usz)ei2 * STRUCT_SPLIT_LEN;
                                    cg.out.writes("  %arg.c."); cg.out.writeu(ia);
                                    cg.out.writes(".x"); cg.out.writei((long)ei2);
                                    cg.out.writes(".v"); cg.out.writei(v.id);
                                    cg.out.writes(" = extractvalue "); cg.out.writes(aty_c);
                                    cg.out.writes(" "); cg.emit_vref(aval_c);
                                    cg.out.writes(", "); cg.out.writei((long)ei2); cg.out.writes("\n");
                                    char* eopc2 = coerce_op(fe2, te2);
                                    if (eopc2 != null)
                                    {
                                        cg.out.writes("  %arg.c."); cg.out.writeu(ia);
                                        cg.out.writes(".w"); cg.out.writei((long)ei2);
                                        cg.out.writes(".v"); cg.out.writei(v.id);
                                        cg.out.writes(" = "); cg.out.writes(eopc2);
                                        cg.out.writes(" "); cg.out.writes(fe2);
                                        cg.out.writes(" %arg.c."); cg.out.writeu(ia);
                                        cg.out.writes(".x"); cg.out.writei((long)ei2);
                                        cg.out.writes(".v"); cg.out.writei(v.id);
                                        cg.out.writes(" to "); cg.out.writes(te2); cg.out.writes("\n");
                                    }
                                    bool last_i2 = (ei2 == nf2 - 1);
                                    if (last_i2)
                                    {
                                        cg.out.writes("  %arg.c."); cg.out.writeu(ia);
                                        cg.out.writes(".v"); cg.out.writei(v.id);
                                    }
                                    else
                                    {
                                        cg.out.writes("  %arg.c."); cg.out.writeu(ia);
                                        cg.out.writes(".i"); cg.out.writei((long)ei2);
                                        cg.out.writes(".v"); cg.out.writei(v.id);
                                    }
                                    cg.out.writes(" = insertvalue "); cg.out.writes(pt);
                                    if (ei2 == 0)
                                    {
                                        cg.out.writes(" undef");
                                    }
                                    else
                                    {
                                        cg.out.writes(" %arg.c."); cg.out.writeu(ia);
                                        cg.out.writes(".i"); cg.out.writei((long)(ei2 - 1));
                                        cg.out.writes(".v"); cg.out.writei(v.id);
                                    }
                                    cg.out.writes(", "); cg.out.writes(te2);
                                    if (eopc2 != null)
                                    {
                                        cg.out.writes(" %arg.c."); cg.out.writeu(ia);
                                        cg.out.writes(".w"); cg.out.writei((long)ei2);
                                        cg.out.writes(".v"); cg.out.writei(v.id);
                                    }
                                    else
                                    {
                                        cg.out.writes(" %arg.c."); cg.out.writeu(ia);
                                        cg.out.writes(".x"); cg.out.writei((long)ei2);
                                        cg.out.writes(".v"); cg.out.writei(v.id);
                                    }
                                    cg.out.writes(", "); cg.out.writei((long)ei2); cg.out.writes("\n");
                                }
                            }
                            else
                            {
                                cg.out.writes(" = freeze "); cg.out.writes(pt);
                                cg.out.writes(" undef  ; unsupported argument coercion (codegen hard error)\n");
                                cg.errors++;
                                printf("codegen error: unsupported argument coercion (%s -> %s)\n", aty_c, pt);
                            }
                        }
                        else
                        {
                            // Unhandled coercion shape (e.g. an aggregate
                            // argument against a scalar/pointer target — arises
                            // on indirect/closure calls whose parameter types
                            // fall back to the generic i64 guess): the
                            // `%arg.c.N.vI` name prefix was already printed,
                            // so complete the line with a VALID placeholder
                            // and FAIL the emission. Previously nothing
                            // completed the line, producing a mangled,
                            // unparseable .ll (observed:
                            // `%arg.c.1.v2  %v2 = call i32 %v0(i64 %arg.c.1.v2)`).
                            cg.out.writes(" = freeze "); cg.out.writes(pt);
                            cg.out.writes(" undef  ; unsupported argument coercion (codegen hard error)\n");
                            cg.errors++;
                            printf("codegen error: unsupported argument coercion (%s -> %s)\n", aty_c, pt);
                        }
                    }
                }


                // Closure call early exit: emit BEFORE outer call prefix.
                // The closure value is the uniform fat { ptr code, ptr env } —
                // always extract both and pass env as the first argument
                // (null for zero-capture closures). Args marshal against the
                // THUNK's parameter types: pattern-annotated where typecheck
                // propagated an ascription, generic i64 otherwise.
                if (callee_val != null && callee_val.op == ssi_ir::IrOp.IR_UNKNOWN
                    && callee_val.binder != null
                    && callee_val.binder.kind == Nk.NODE_EXPR_CLOSURE)
                {
                    bool is_musttail_c = ((v.ival >> 63) & 1) != 0;
                    Node* clo_decl = callee_val.binder;
                    cg.out.writes("  %thunk."); cg.out.writei(v.id);
                    cg.out.writes(" = extractvalue { ptr, ptr } ");
                    cg.emit_vref(callee_val);
                    cg.out.writes(", 0\n");
                    cg.out.writes("  %cenv2."); cg.out.writei(v.id);
                    cg.out.writes(" = extractvalue { ptr, ptr } ");
                    cg.emit_vref(callee_val);
                    cg.out.writes(", 1\n");
                    // Pre-emit per-arg adaptions to the thunk param types.
                    for (usz ia2 = 1; ia2 < v.arg_count; ia2++)
                    {
                        ssi_ir::IrVal* arg2 = v.args[ia2];
                        if (arg2 == null) continue;
                        char* aty2 = (tm != null) ? tm.get(arg2.id) : null;
                        if (aty2 == null || aty2[0] == 0) aty2 = (char*)"i64";
                        char[TYMAP_ENTRY] cptbuf;
                        fn_param_llvm_type(clo_decl, (int)ia2, &cptbuf[0], TYMAP_ENTRY);
                        char* cpt = &cptbuf[0];
                        bool same2 = cstr_eq(aty2, cpt);
                        if (same2) continue;
                        if (aty2[0] == '{' || cpt[0] == '{')
                        {
                            // Aggregate ↔ anything-else is never marshalled
                            // (e.g. a tagged union into an unannotated i64
                            // thunk param). Loud failure, parseable .ll.
                            printf("codegen error: aggregate argument in a closure call (annotate the closure's parameter type)\n");
                            cg.errors++;
                            continue;
                        }
                        bool i2a = aty2[0] == 'i'; bool i2b = cpt[0] == 'i';
                        if (i2a && i2b)
                        {
                            long w2a = 0; long w2b = 0;
                            for (char* q2 = aty2 + 1; *q2 >= '0' && *q2 <= '9'; q2++) w2a = w2a * 10 + (long)(*q2 - '0');
                            for (char* q2 = cpt + 1; *q2 >= '0' && *q2 <= '9'; q2++) w2b = w2b * 10 + (long)(*q2 - '0');
                            cg.out.writes("  %clarg.c."); cg.out.writei(v.id);
                            cg.out.writes("."); cg.out.writeu(ia2);
                            if (w2a == w2b)     { cg.out.writes(" = bitcast "); }
                            else if (w2a < w2b && !is_signed_int_val(arg2)) { cg.out.writes(" = zext "); }
                            else if (w2a < w2b) { cg.out.writes(" = sext "); }
                            else                { cg.out.writes(" = trunc "); }
                            cg.out.writes(aty2); cg.out.writes(" ");
                            cg.emit_vref(arg2);
                            cg.out.writes(" to "); cg.out.writes(cpt); cg.out.writes("\n");
                        }
                    }
                    if (!is_void) { cg.out.writes("  %v"); cg.out.writei(v.id); cg.out.writes(" = "); }
                    else { cg.out.writes("  "); }
                    if (is_musttail_c) cg.out.writes("musttail ");
                    cg.out.writes("call ");
                    {
                        char[TYMAP_ENTRY] ccret;
                        closure_thunk_ret_type(clo_decl, &ccret[0], TYMAP_ENTRY);
                        cg.out.writes(&ccret[0]);
                    }
                    cg.out.writes(" %thunk."); cg.out.writei(v.id);
                    cg.out.writes("(ptr %cenv2."); cg.out.writei(v.id);
                    for (usz ia2 = 1; ia2 < v.arg_count; ia2++)
                    {
                        ssi_ir::IrVal* arg2 = v.args[ia2];
                        if (arg2 == null) continue;
                        char* aty2 = (tm != null) ? tm.get(arg2.id) : null;
                        if (aty2 == null || aty2[0] == 0) aty2 = (char*)"i64";
                        char[TYMAP_ENTRY] cptbuf;
                        fn_param_llvm_type(clo_decl, (int)ia2, &cptbuf[0], TYMAP_ENTRY);
                        char* cpt = &cptbuf[0];
                    cg.out.writes(", ");
                    bool same2b = cstr_eq(aty2, cpt);
                    if (!same2b && (aty2[0] == '{' || cpt[0] == '{'))
                    {
                        // Hard-error path (printf + cg.errors++ above): still
                        // emit a syntactically COMPLETE call so the .ll stays
                        // parseable by llvm-as — an inline `; comment` here
                        // used to eat the closing paren and corrupt the file.
                        cg.out.writes("i64 undef");
                        continue;
                    }
                        if (!same2b && aty2[0] == 'i' && cpt[0] == 'i')
                        {
                            cg.out.writes(cpt); cg.out.writes(" %clarg.c.");
                            cg.out.writei(v.id); cg.out.writes("."); cg.out.writeu(ia2);
                            continue;
                        }
                        cg.out.writes(cpt); cg.out.writes(" ");
                        cg.emit_vref(arg2);
                    }
                    cg.out.writes(")\n");
                    break;
                }

                cg.out.writes("  ");
                if (!is_void)
                {
                    cg.out.writes("%v"); cg.out.writei(v.id);
                    cg.out.writes(" = ");
                }
                // musttail if ival bit 63 is set (from tail keyword)
                bool is_musttail = ((v.ival >> 63) & 1) != 0;
                if (is_musttail) cg.out.writes("musttail ");
                cg.out.writes("call ");
                if (is_void) { cg.out.writes("void"); }
                else { cg.writes_ty(tm, v.id); }
                cg.out.writes(" ");
                // (closure handled above before call prefix)

                if (callee_val != null && callee_val.op == ssi_ir::IrOp.IR_UNKNOWN
                    && callee_val.binder != null
                    && callee_val.binder.kind == Nk.NODE_DECL_FN)
                {
                    // Known Pride function
                    Node* fn_decl = callee_val.binder;
                    // Find name (child 0)
                    char* fn_name_ptr = null;
                    usz   fn_name_len = 0;
                    if (fn_decl.child_count >= 1 && fn_decl.children[0] != null)
                    {
                        fn_name_ptr = fn_decl.children[0].p.ident.name_ptr;
                        fn_name_len = fn_decl.children[0].p.ident.name_len;
                    }
                    bool is_main_fn = span_is(fn_name_ptr, fn_name_len, (char*)"main");
                    if (is_main_fn) { cg.out.writes("@main"); }
                    else
                    {
                        // Check for #[extern("name")] — call the C symbol directly
                        char* ext_call_name = null;
                        usz   ext_call_len  = 0;
                        bool  has_ext = fn_get_extern_name(fn_decl, &ext_call_name, &ext_call_len);
                        if (has_ext && ext_call_name != null && ext_call_len > 0)
                        {
                            cg.out.writes("@");
                            for (usz ei2 = 0; ei2 < ext_call_len; ei2++) { cg.out.writec(ext_call_name[ei2]); }
                        }
                        else
                        {
                            cg.out.writes("@pride_");
                            if (fn_name_ptr != null) { cg.out.write(fn_name_ptr, fn_name_len); }
                        }
                    }
                }
                else if (callee_val != null)
                {
                    char* cty2 = (tm != null) ? tm.get(callee_val.id) : null;
                    // Use %callee.ptr.N only when inttoptr was pre-emitted (integer callee type).
                    // For void/struct/unknown types, fall back to direct vref (avoids undef ref).
                    bool cty2_is_int = (cty2 != null && cty2[0] == 'i'
                        && cty2[1] >= '0' && cty2[1] <= '9');
                    // Guard: if callee is unit/void constant, emit ptr undef
                    // to keep IR syntactically valid (undefined fn call).
                    bool callee_is_unit = (callee_val != null
                        && callee_val.op == ssi_ir::IrOp.IR_CONST_UNIT);
                    bool cty2_is_void = (cty2 != null
                        && cty2[0]=='v'&&cty2[1]=='o'&&cty2[2]=='i'&&cty2[3]=='d');
                    if (callee_fat_call)
                    {
                        // Uniform indirect ABI: the code pointer was
                        // pre-extracted from the fat { code, env } pair above.
                        cg.out.writes("%fptr."); cg.out.writei(v.id);
                    }
                    else if (cty2_is_int)
                    { cg.out.writes("%callee.ptr."); cg.out.writei(v.id); }
                    else if (callee_is_unit || cty2_is_void || cty2 == null || cty2[0] == 0)
                    { cg.out.writes("undef"); }
                    else { cg.emit_vref(callee_val); }
                }
                else { cg.out.writes("null"); }

                cg.out.writes("(");
                bool first_arg = true;
                // Uniform indirect ABI: env pointer is the first argument of
                // every fat call (null for zero-capture thunks/trampolines).
                if (callee_fat_call)
                {
                    cg.out.writes("ptr %fenv."); cg.out.writei(v.id);
                    first_arg = false;
                }
                int arg_pos2 = 0;
                for (usz i = 1; i < v.arg_count; i++)
                {
                    if (v.args[i] == null) { continue; }
                    char* arg_ty = (tm != null) ? tm.get(v.args[i].id) : null;
                    if (arg_ty == null || arg_ty[0] == 0) { arg_ty = (char*)"i64"; }
                    if (arg_ty[0]=='v'&&arg_ty[1]=='o') { continue; }
                    // Skip args[1] only when it's a fn-value used as a dynamic callee
                    // (the callee itself is not a known named fn, and args[1] holds the fn ptr).
                    // Do NOT skip when the callee IS a known named fn — then args[1] is a real arg.
                    bool callee_is_named = (callee_val != null
                        && callee_val.op == ssi_ir::IrOp.IR_UNKNOWN
                        && callee_val.binder != null
                        && callee_val.binder.kind == Nk.NODE_DECL_FN);
                    if (!callee_is_named && i==1 && v.args[i].op==ssi_ir::IrOp.IR_UNKNOWN
                        && v.args[i].binder!=null
                        && v.args[i].binder.kind==Nk.NODE_DECL_FN) { continue; }
                    if (!first_arg) { cg.out.writes(", "); }
                    first_arg = false;
                    // Use coerce result if type differs from callee param type.
                    // Sigma-unwrap the arg before tymap lookup (matches pre-emit coerce check).
                    ssi_ir::IrVal* aarg_base = v.args[i];
                    {
                        int sc2 = 0;
                        while (aarg_base != null && aarg_base.op == ssi_ir::IrOp.IR_SIGMA
                               && aarg_base.arg_count >= 1 && aarg_base.args[0] != null && sc2 < 16)
                        { aarg_base = aarg_base.args[0]; sc2++; }
                    }
                    char* arg_ty_base = (tm != null && aarg_base != null) ? tm.get(aarg_base.id) : null;
                    if (arg_ty_base == null || arg_ty_base[0] == 0) { arg_ty_base = arg_ty; }
                    char[TYMAP_ENTRY] ptype3_buf;
                    call_param_type(callee_decl2, callee_sig, arg_pos2, &ptype3_buf[0], TYMAP_ENTRY);
                    char* ptype3 = &ptype3_buf[0];
                    arg_pos2++;
                    bool teq3 = true;
                    if (ptype3[0] != 0 && !(ptype3[0]=='v'&&ptype3[1]=='o'))
                    {
                        // Use sigma-unwrapped type for equality check (matches pre-emit coerce)
                        usz al3 = strlen(arg_ty_base); usz pl3 = strlen(ptype3);
                        if (al3 != pl3) { teq3 = false; }
                        else
                        {
                            for (usz ci3 = 0; ci3 < al3; ci3++)
                            {
                                if (arg_ty_base[ci3] != ptype3[ci3]) { teq3 = false; break; }
                            }
                        }
                    }
                    if (!teq3 && ptype3[0] != 0)
                    {
                        // Special: { ptr, ptr } fat-pointer closure to ptr param
                        // — extract the thunk ptr (field 0)
                        char* aty3 = arg_ty_base;
                        bool fat_to_ptr = (ptype3[0]=='p' && aty3 != null
                                           && aty3[0]=='{' && aty3[1]==' '
                                           && aty3[2]=='p');
                        if (fat_to_ptr)
                        {
                            // Pre-emit already wrote the extractvalue.
                            // Just reference the result here.
                            cg.out.writes(ptype3);
                            cg.out.writes(" %arg.c."); cg.out.writeu(i);
                            cg.out.writes(".v"); cg.out.writei(v.id);
                        }
                        else
                        {
                            // Emit the coerce result reference
                            cg.out.writes(ptype3); cg.out.writes(" %arg.c.");
                            cg.out.writeu(i); cg.out.writes(".v"); cg.out.writei(v.id);
                        }
                    }
                    else
                    {
                        // Types match (or no explicit param type): emit direct arg.
                        // Use sigma-unwrapped type for the LLVM type prefix.
                        char* emit_ty = (arg_ty_base != null && arg_ty_base[0] != 0) ? arg_ty_base : arg_ty;
                        if (ptype3[0] != 0 && !(ptype3[0]=='v'&&ptype3[1]=='o'))
                        { emit_ty = ptype3; }  // prefer declared param type if available
                        if (emit_ty[0] == '%') { cg.out.writes("ptr"); }
                        else { cg.out.writes(emit_ty); }
                        cg.out.writes(" ");
                        // A string literal passed as an aggregate argument is
                        // the fat record { ptr @.str.N, i64 LEN }, not the
                        // bare byte-global ref emit_vref renders (llvm-as:
                        // "global variable reference must have pointer type").
                        if (emit_ty[0] == '{'
                            && v.args[i] != null
                            && v.args[i].op == ssi_ir::IrOp.IR_CONST_STR)
                        { cgen_emit_str_const_record(cg, v.args[i]); }
                        else { cg.emit_vref(v.args[i]); }  // emit_vref sigma-unwraps automatically
                    }
                }
                cg.out.writes(")\n");
                // musttail requires ret immediately after the call (LLVM constraint)
                if (is_musttail && !is_void)
                {
                    char* ret_ty = (tm != null) ? tm.get(v.id) : null;
                    if (ret_ty == null || ret_ty[0] == 0) ret_ty = (char*)"i64";
                    cg.out.writes("  ret ");
                    cg.out.writes(ret_ty);
                    cg.out.writes(" %v"); cg.out.writei(v.id); cg.out.writes("\n");
                }
                else if (is_musttail && is_void)
                {
                    cg.out.writes("  ret void\n");
                }
            }

        case ssi_ir::IrOp.IR_FIELD:
            {
                // GEP + load: v.src = NODE_EXPR_FIELD[base, field_name_ident]
                // 1. Find the struct type from the base's type annotation
                // 2. Look up field index
                // 3. Emit: %gep = getelementptr inbounds %S, ptr %base, i32 0, i32 N
                //          %vN  = load FieldType, ptr %gep
                ssi_ir::IrVal* base = v.arg_count >= 1 ? v.args[0] : null;
                Node* field_name_node = null;
                Node* struct_decl = null;
                int   field_idx = 0;

                if (v.src != null && v.src.kind == Nk.NODE_EXPR_FIELD
                    && v.src.child_count >= 2)
                {
                    field_name_node = v.src.children[1];
                }

                // Untagged C-union field access (r13): the whole value is one
                // i64 bitbox in a register — there is NO memory, NO GEP, NO
                // tag. Reading a field reinterprets the box at that field's
                // payload width (same bytes, different interpretation).
                {
                    Node* udecl2 = null;
                    for (int usrc = 0; usrc < 2 && udecl2 == null; usrc++)
                    {
                        Node* bt5 = null;
                        if (usrc == 0)
                        {
                            if (base != null && base.src != null)
                            { bt5 = base.src.type_annotation; }
                        }
                        else if (v.src != null && v.src.kind == Nk.NODE_EXPR_FIELD
                            && v.src.child_count >= 1 && v.src.children[0] != null)
                        { bt5 = v.src.children[0].type_annotation; }
                        if (bt5 != null)
                        {
                            if (bt5.kind == Nk.NODE_TYPE_PTR
                                && bt5.child_count >= 1 && bt5.children[0] != null)
                            { bt5 = bt5.children[0]; }
                            udecl2 = ast::union_decl_of(bt5);
                        }
                    }
                    if (udecl2 != null && ast::union_is_c_union(udecl2)
                        && field_name_node != null)
                    {
                        Node* pay2 = null;
                        int ord2 = ast::union_variant_lookup(udecl2,
                            field_name_node.p.ident.name_ptr,
                            field_name_node.p.ident.name_len, &pay2);
                        if (ord2 >= 0)
                        {
                            // Address mode (r53b): the store path (lower_assign
                            // FIELD → field_addr_chain) needs the FIELD's
                            // address.  Every field of a C-union overlaps the
                            // shared cell at offset 0, so the field address IS
                            // the cell address — an identity GEP just binds it
                            // to a fresh SSA name.  The store itself performs
                            // the union member-store: writing the field-typed
                            // value through memory replaces exactly that
                            // field's low footprint bytes.
                            if (v.ival == 1)
                            {
                                cg.out.writes("  %v"); cg.out.writei(v.id);
                                cg.out.writes(" = getelementptr i64, ptr ");
                                cg.emit_vref(base);
                                cg.out.writes(", i64 0\n");
                                if (tm != null) { tm.set(v.id, (char*)"ptr"); }
                                return;
                            }
                            char[TYMAP_ENTRY] pbuf2;
                            pbuf2[0] = 0;
                            type_to_llvm_buf(pay2, &pbuf2[0], TYMAP_ENTRY, 0);
                            if (pbuf2[0] == 0) { pbuf2[0] = 'i'; pbuf2[1] = '6'; pbuf2[2] = '4'; pbuf2[3] = 0; }
                            // The bitbox is always an i64 register value; if the
                            // operand's recorded type was coerced (casts), bind
                            // it to an i64 name first.
                            char* bty5 = (tm != null && base != null) ? tm.get(base.id) : null;
                            // Pointer base (r53b): `p.f` auto-derefs — load the
                            // i64 cell through the pointer, then reinterpret
                            // from the loaded value (used to feed the trunc/
                            // bitcast a 0 constant, i.e. every read was 0).
                            bool ucell_ld = (bty5 != null && bty5[0] == 'p');
                            if (ucell_ld)
                            {
                                cg.out.writes("  %ucell.v"); cg.out.writei(v.id);
                                cg.out.writes(" = load i64, ptr ");
                                cg.emit_vref(base);
                                cg.out.writes("\n");
                            }
                            if (pbuf2[0] == 'i' && pbuf2[1] == '6' && pbuf2[2] == '4' && pbuf2[3] == 0)
                            {
                                // i64 view: identity rename.
                                cg.out.writes("  %v"); cg.out.writei(v.id);
                                cg.out.writes(" = add i64 ");
                                if (ucell_ld)
                                { cg.out.writes("%ucell.v"); cg.out.writei(v.id); }
                                else if (bty5 != null && bty5[0] == 'i' && bty5[1] == '6'
                                    && bty5[2] == '4' && bty5[3] == 0)
                                { cg.emit_vref(base); }
                                else { cg.out.writes("0"); }
                                cg.out.writes(", 0\n");
                            }
                            else if (pbuf2[0] == 'f' && pbuf2[1] == 'l')
                            {
                                // f32: low 32 bits bitcast.
                                cg.out.writes("  %v"); cg.out.writei(v.id);
                                if (ucell_ld)
                                {
                                    cg.out.writes(".t = trunc i64 %ucell.v");
                                    cg.out.writei(v.id);
                                }
                                else if (bty5 != null && bty5[0] == 'i' && bty5[1] == '6'
                                    && bty5[2] == '4' && bty5[3] == 0)
                                {
                                    cg.out.writes(".t = trunc i64 ");
                                    cg.emit_vref(base);
                                }
                                else { cg.out.writes(".t = trunc i64 0"); }
                                cg.out.writes(" to i32\n");
                                cg.out.writes("  %v"); cg.out.writei(v.id);
                                cg.out.writes(" = bitcast i32 %v"); cg.out.writei(v.id);
                                cg.out.writes(".t to float\n");
                            }
                            else if (pbuf2[0] == 'd')
                            {
                                // f64: full-width bitcast.
                                cg.out.writes("  %v"); cg.out.writei(v.id);
                                if (ucell_ld)
                                {
                                    cg.out.writes(" = bitcast i64 %ucell.v");
                                    cg.out.writei(v.id);
                                }
                                else if (bty5 != null && bty5[0] == 'i' && bty5[1] == '6'
                                    && bty5[2] == '4' && bty5[3] == 0)
                                {
                                    cg.out.writes(" = bitcast i64 ");
                                    cg.emit_vref(base);
                                }
                                else { cg.out.writes(" = bitcast i64 0"); }
                                cg.out.writes(" to double\n");
                            }
                            else if (pbuf2[0] == 'p')
                            {
                                cg.out.writes("  %v"); cg.out.writei(v.id);
                                if (ucell_ld)
                                {
                                    cg.out.writes(" = inttoptr i64 %ucell.v");
                                    cg.out.writei(v.id);
                                }
                                else if (bty5 != null && bty5[0] == 'i' && bty5[1] == '6'
                                    && bty5[2] == '4' && bty5[3] == 0)
                                {
                                    cg.out.writes(" = inttoptr i64 ");
                                    cg.emit_vref(base);
                                }
                                else { cg.out.writes(" = inttoptr i64 0"); }
                                cg.out.writes(" to ptr\n");
                            }
                            else if (pbuf2[0] == 'i')
                            {
                                // Sub-64 integer/bool view: low-bits trunc.
                                cg.out.writes("  %v"); cg.out.writei(v.id);
                                if (ucell_ld)
                                {
                                    cg.out.writes(" = trunc i64 %ucell.v");
                                    cg.out.writei(v.id);
                                }
                                else if (bty5 != null && bty5[0] == 'i' && bty5[1] == '6'
                                    && bty5[2] == '4' && bty5[3] == 0)
                                {
                                    cg.out.writes(" = trunc i64 ");
                                    cg.emit_vref(base);
                                }
                                else { cg.out.writes(" = trunc i64 0"); }
                                cg.out.writes(" to "); cg.out.writes(&pbuf2[0]); cg.out.writes("\n");
                            }
                            else
                            {
                                // Any other payload: keep the raw box.
                                cg.out.writes("  %v"); cg.out.writei(v.id);
                                cg.out.writes(" = add i64 ");
                                if (ucell_ld)
                                { cg.out.writes("%ucell.v"); cg.out.writei(v.id); }
                                else if (bty5 != null && bty5[0] == 'i' && bty5[1] == '6'
                                    && bty5[2] == '4' && bty5[3] == 0)
                                { cg.emit_vref(base); }
                                else { cg.out.writes("0"); }
                                cg.out.writes(", 0\n");
                            }
                            return;
                        }
                    }
                }

                // Resolve struct decl from base's type annotation.
                // Try multiple sources in priority order:
                //   1. base.src.type_annotation (IR param/let source node type)
                //   2. The field-access AST node v.src.children[0].type_annotation
                //   3. The resolved name on the base's source node directly
                if (base != null && base.src != null
                    && base.src.type_annotation != null)
                {
                    Node* bt = base.src.type_annotation;
                    if (bt.kind == Nk.NODE_TYPE_PTR && bt.child_count >= 1 && bt.children[0] != null)
                    { bt = bt.children[0]; }
                    if (bt.kind == Nk.NODE_TYPEVAR && bt.resolved != null
                        && bt.resolved.kind == Nk.NODE_DECL_STRUCT)
                    { struct_decl = bt.resolved; }
                    else if (bt.kind == Nk.NODE_DECL_STRUCT)
                    { struct_decl = bt; }
                    // Also try the typevar's direct resolved when it's a type alias
                    else if (bt.kind == Nk.NODE_TYPEVAR && bt.resolved != null
                        && bt.resolved.kind == Nk.NODE_DECL_TYPE
                        && bt.resolved.child_count >= 2
                        && bt.resolved.children[1] != null
                        && bt.resolved.children[1].kind == Nk.NODE_DECL_STRUCT)
                    { struct_decl = bt.resolved.children[1]; }
                }
                // Fallback: look at the field-access node's base child type annotation
                if (struct_decl == null && v.src != null
                    && v.src.kind == Nk.NODE_EXPR_FIELD
                    && v.src.child_count >= 1 && v.src.children[0] != null)
                {
                    Node* base_ast = v.src.children[0];
                    Node* bt2 = base_ast.type_annotation;
                    if (bt2 != null)
                    {
                        // struct_body_of covers DECL_STRUCT/UNION, TYPEVAR (alias
                        // chains), DECL_TYPE aliases and GENERIC_APP instantiations.
                        if (bt2.kind == Nk.NODE_TYPE_PTR && bt2.child_count >= 1 && bt2.children[0] != null)
                        { struct_decl = struct_body_of(bt2.children[0]); }
                        if (struct_decl == null) { struct_decl = struct_body_of(bt2); }
                    }
                    // Also try the resolved name on the base ident itself (direct
                    // decl reference or alias chain).
                    if (struct_decl == null && base_ast.resolved != null)
                    { struct_decl = struct_body_of(base_ast.resolved); }
                    // Check if ident resolves to a let/param binding that has a struct type
                    if (struct_decl == null && base_ast.resolved != null)
                    {
                        Node* decl = base_ast.resolved;
                        Node* dtype = decl.type_annotation;
                        if (dtype == null && decl.child_count >= 1 && decl.children[0] != null)
                        { dtype = decl.children[0].type_annotation; }
                        if (dtype != null)
                        {
                            if (dtype.kind == Nk.NODE_TYPE_PTR && dtype.child_count >= 1 && dtype.children[0] != null)
                            { struct_decl = struct_body_of(dtype.children[0]); }
                            if (struct_decl == null) { struct_decl = struct_body_of(dtype); }
                        }
                    }
                }

                if (field_name_node != null && struct_decl != null)
                {
                    field_idx = field_index_of(struct_decl,
                                               field_name_node.p.ident.name_ptr,
                                               field_name_node.p.ident.name_len);
                }
                // r56: no struct decl — map well-known names on str-like fat
                // records (Str / slice / tuple fat): ptr→0 (already default),
                // len→1, cap→2.
                if (field_name_node != null && struct_decl == null)
                {
                    // Prefer the BASE expression's annotation (the object
                    // being indexed); the field node itself is annotated with
                    // the FIELD type (i64 for .len), which is not str-like.
                    Node* bsl = (v.src != null && v.src.child_count >= 1
                                 && v.src.children[0] != null)
                                ? v.src.children[0].type_annotation : null;
                    if (bsl == null && v.src != null)
                    { bsl = v.src.type_annotation; }
                    if (bsl != null && bsl.kind == Nk.NODE_TYPE_PTR
                        && bsl.child_count >= 1 && bsl.children[0] != null)
                    { bsl = bsl.children[0]; }
                    bool strlike = false;
                    if (bsl != null)
                    {
                        if (bsl.kind == Nk.NODE_TYPE_TUPLE || bsl.kind == Nk.NODE_TYPE_SLICE)
                        { strlike = true; }
                        if (bsl.kind == Nk.NODE_TYPE_PRIMITIVE)
                        {
                            usz bl = bsl.p.ident.name_len;
                            char* bn = bsl.p.ident.name_ptr;
                            if (bl == 3 && bn[0] == 'S') { strlike = true; }  // Str
                        }
                    }
                    if (strlike)
                    {
                        usz fl2 = field_name_node.p.ident.name_len;
                        char* fn2 = field_name_node.p.ident.name_ptr;
                        if (fl2 == 3 && fn2[0] == 'l' && fn2[1] == 'e' && fn2[2] == 'n')
                        { field_idx = 1; }
                        else if (fl2 == 3 && fn2[0] == 'c' && fn2[1] == 'a' && fn2[2] == 'p')
                        { field_idx = 2; }
                    }
                }


                // Emit struct type name
                char* sname = null; usz snlen = 0;
                if (struct_decl != null && struct_decl.child_count >= 1
                    && struct_decl.children[0] != null)
                {
                    sname = struct_decl.children[0].p.ident.name_ptr;
                    snlen = struct_decl.children[0].p.ident.name_len;
                }

                // Pre-emit: handle non-ptr base (struct alloca or inttoptr)
                if (base != null)
                {
                    char* base_ty2 = (tm != null) ? tm.get(base.id) : null;
                    if (base_ty2 != null && base_ty2[0] == '%'
                        && base != null && base.op != ssi_ir::IrOp.IR_PARAM)
                    {
                        // Struct value (not a param): alloca+store to get a ptr
                        cg.out.writes("  %struct.ptr.v"); cg.out.writei(v.id);
                        cg.out.writes(" = alloca "); cg.out.writes(base_ty2); cg.out.writes("\n");
                        cg.out.writes("  store "); cg.out.writes(base_ty2);
                        cg.out.writes(" "); cg.emit_vref(base);
                        cg.out.writes(", ptr %struct.ptr.v"); cg.out.writei(v.id); cg.out.writes("\n");
                    }
                    else if (base_ty2 != null && base_ty2[0] == '{')
                    {
                        // Struct by value: alloca+store to get addressable ptr
                        cg.out.writes("  %struct.ptr.v"); cg.out.writei(v.id);
                        cg.out.writes(" = alloca "); cg.out.writes(base_ty2); cg.out.writes("\n");
                        cg.out.writes("  store "); cg.out.writes(base_ty2);
                        cg.out.writes(" ");
                        // A string literal's LLVM value is its fat record
                        // { ptr @.str.N, i64 LEN } — emit_vref renders the
                        // raw byte-global ref alone, which is NOT a value of
                        // the record type (llvm-as: "global variable
                        // reference must have pointer type"... and even when
                        // accepted it stored bytes over the record).
                        if (base != null && base.op == ssi_ir::IrOp.IR_CONST_STR)
                        { cgen_emit_str_const_record(cg, base); }
                        else { cg.emit_vref(base); }
                        cg.out.writes(", ptr %struct.ptr.v"); cg.out.writei(v.id); cg.out.writes("\n");
                    }
                    else if (base_ty2 != null && base_ty2[0] != 'p' && base_ty2[0] != '%' && base_ty2[0] != 0)
                    {
                        cg.out.writes("  %gep.itp.v"); cg.out.writei(v.id);
                        cg.out.writes(" = inttoptr "); cg.out.writes(base_ty2);
                        cg.out.writes(" "); cg.emit_vref(base); cg.out.writes(" to ptr\n");
                    }
                }
                // Determine the ptr to use for GEP
                // %gep.vN = getelementptr inbounds %S, ptr %base, i32 0, i32 idx
                cg.out.writes("  %gep.v"); cg.out.writei(v.id);
                cg.out.writes(" = getelementptr inbounds ");
                // Use base's actual struct type from tymap (e.g. "{ i64, i64 }") for GEP.
                // This is the most reliable source — avoids AST struct decl lookup.
                {
                    char* gep_struct_ty = (tm != null && base != null) ? tm.get(base.id) : null;
                    if (gep_struct_ty != null && gep_struct_ty[0] == '{')
                    {
                        // Already have "{ i64, i64 }" from tymap
                        cg.out.writes(gep_struct_ty);
                    }
                    else if (sname != null && snlen > 0)
                    {
                        cg.out.writes("%"); cg.out.write(sname, snlen);
                    }
                    else if (struct_decl != null)
                    {
                        // Build inline struct type from field decls
                        cg.out.writes("{ ");
                        bool first_field = true;
                        for (usz sfi = 0; sfi < struct_decl.child_count; sfi++)
                        {
                            Node* sb = struct_decl.children[sfi];
                            if (sb == null || sb.kind != Nk.NODE_EXPR_BLOCK) continue;
                            for (usz sgi = 0; sgi < sb.child_count; sgi++)
                            {
                                Node* fd = sb.children[sgi];
                                if (fd == null || fd.kind != Nk.NODE_FIELD_DECL) continue;
                                if (!first_field) { cg.out.writes(", "); }
                                first_field = false;
                                Node* ft = fd.child_count >= 2 ? fd.children[1] : null;
                                char[TYMAP_ENTRY] ftbuf; ftbuf[0] = 0;
                                type_to_llvm_buf(ft, &ftbuf[0], TYMAP_ENTRY, 0);
                                cg.out.writes(ftbuf[0] != 0 ? &ftbuf[0] : "i64");
                            }
                        }
                        cg.out.writes(" }");
                    }
                    else { cg.out.writes("{ i64 }"); }
                }
                cg.out.writes(", ptr ");
                // Use the inttoptr result if base wasn't already ptr
                // For struct-valued bases (%T), alloca+store to get a ptr
                if (base != null)
                {
                    char* base_ty3 = (tm != null) ? tm.get(base.id) : null;
                    if (base_ty3 != null && (base_ty3[0] == '%' || base_ty3[0] == '{'))
                    {
                        // struct by value: use the alloca'd ptr from pre-emit
                        cg.out.writes("%struct.ptr.v"); cg.out.writei(v.id);
                    }
                    else if (base_ty3 != null && base_ty3[0] == '{')
                    { cg.out.writes("%struct.ptr.v"); cg.out.writei(v.id); }
                    else if (base_ty3 != null && base_ty3[0] != 'p'
                        && base_ty3[0] != 0)
                    { cg.out.writes("%gep.itp.v"); cg.out.writei(v.id); }
                    else { cg.emit_vref(base); }
                }
                else { cg.out.writes("null"); }
                cg.out.writes(", i32 0, i32 ");
                cg.out.writei(field_idx);
                cg.out.writes("\n");

                // Address mode (r46, `p.cells` inside an array-element write):
                // the value IS the field's storage address — consumers
                // (IR_STORE variant B, further addr-mode FIELDs) GEP through
                // it.  NEVER load here: loading an inline-array field as a
                // register value would sever the write from the pointee.
                if (v.ival == 1)
                {
                    if (tm != null) { tm.set(v.id, (char*)"ptr"); }
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = getelementptr inbounds i8, ptr %gep.v");
                    cg.out.writei(v.id);
                    cg.out.writes(", i64 0\n");
                    return;
                }

                // %vN = load FieldType, ptr %gep.vN
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = load ");
                cg.writes_ty(tm, v.id);
                cg.out.writes(", ptr %gep.v");
                cg.out.writei(v.id);
                cg.out.writes("\n");
            }

        case ssi_ir::IrOp.IR_INDEX:
            {
                // GEP + load: args[0]=base (ptr), args[1]=index
                ssi_ir::IrVal* base  = v.arg_count >= 1 ? v.args[0] : null;
                ssi_ir::IrVal* index = v.arg_count >= 2 ? v.args[1] : null;

                // Update mode (r46): whole-array VALUE with one element
                // replaced — args[0]=array value, args[1]=new element,
                // args[2]=index.  Materialise the array in memory, store the
                // element through a GEP, load the array back; the result
                // re-enters SSA as a plain [N x T] value that
                // field_assign_rebuild stitches into the enclosing aggregate.
                if (v.ival == -2 && v.arg_count >= 3)
                {
                    ssi_ir::IrVal* arr_v  = v.args[0];
                    ssi_ir::IrVal* elem_v = v.args[1];
                    ssi_ir::IrVal* idx_v  = v.args[2];
                    char* aty = (tm != null && arr_v != null) ? tm.get(arr_v.id) : null;
                    if (aty != null && aty[0] == '[')
                    {
                        // Element type text: after the first " x " separator,
                        // up to the outer closing ']'.
                        char[TYMAP_ENTRY] aueb; aueb[0] = 0;
                        usz alen = strlen(aty);
                        usz xp = 0;
                        while (xp + 3 < alen && !(aty[xp] == ' '
                               && aty[xp+1] == 'x' && aty[xp+2] == ' ')) { xp++; }
                        usz es = xp + 3;
                        usz ei = 0;
                        while (es < alen - 1 && ei < TYMAP_ENTRY - 1)
                        { aueb[ei] = aty[es]; ei++; es++; }
                        aueb[ei] = 0;
                        char* elem_ty_au = &aueb[0];
                        char* eval_ty = (tm != null && elem_v != null)
                                        ? tm.get(elem_v.id) : null;
                        if (eval_ty == null || eval_ty[0] == 0) eval_ty = elem_ty_au;

                        cg.out.writes("  %au.arr.v"); cg.out.writei(v.id);
                        cg.out.writes(" = alloca "); cg.out.writes(aty); cg.out.writes("\n");
                        cg.out.writes("  store "); cg.out.writes(aty); cg.out.writes(" ");
                        cg.emit_vref(arr_v);
                        cg.out.writes(", ptr %au.arr.v"); cg.out.writei(v.id); cg.out.writes("\n");
                        cg.out.writes("  %au.gep.v"); cg.out.writei(v.id);
                        cg.out.writes(" = getelementptr inbounds ");
                        cg.out.writes(elem_ty_au);
                        cg.out.writes(", ptr %au.arr.v"); cg.out.writei(v.id);
                        cg.out.writes(", i64 ");
                        cg.emit_vref(idx_v);
                        cg.out.writes("\n");
                        // int-width coerce of the element (signedness-aware, r40)
                        bool au_coerce = false;
                        {
                            usz el = strlen(elem_ty_au); usz vl = strlen(eval_ty);
                            if (el != vl) { au_coerce = true; }
                            else { for (usz ci = 0; ci < el; ci++)
                                   { if (elem_ty_au[ci] != eval_ty[ci]) { au_coerce = true; break; } } }
                        }
                        if (au_coerce && elem_v != null
                            && elem_ty_au[0] == 'i' && eval_ty[0] == 'i')
                        {
                            long en2 = 0; long vn2 = 0;
                            char* ep2 = elem_ty_au + 1;
                            while (*ep2 >= '0' && *ep2 <= '9') { en2 = en2*10 + (long)(*ep2 - '0'); ep2++; }
                            char* vp2 = eval_ty + 1;
                            while (*vp2 >= '0' && *vp2 <= '9') { vn2 = vn2*10 + (long)(*vp2 - '0'); vp2++; }
                            cg.out.writes("  %au.coerce.v"); cg.out.writei(v.id);
                            if (vn2 > en2) { cg.out.writes(" = trunc "); }
                            else if (!is_signed_int_val(elem_v)) { cg.out.writes(" = zext "); }
                            else { cg.out.writes(" = sext "); }
                            cg.out.writes(eval_ty); cg.out.writes(" ");
                            cg.emit_vref(elem_v);
                            cg.out.writes(" to "); cg.out.writes(elem_ty_au); cg.out.writes("\n");
                            cg.out.writes("  store "); cg.out.writes(elem_ty_au);
                            cg.out.writes(" %au.coerce.v"); cg.out.writei(v.id);
                        }
                        else
                        {
                            cg.out.writes("  store "); cg.out.writes(elem_ty_au); cg.out.writes(" ");
                            if (elem_v != null) { cg.emit_vref(elem_v); } else { cg.out.writes("undef"); }
                        }
                        cg.out.writes(", ptr %au.gep.v"); cg.out.writei(v.id); cg.out.writes("\n");
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = load "); cg.out.writes(aty);
                        cg.out.writes(", ptr %au.arr.v"); cg.out.writei(v.id); cg.out.writes("\n");
                        if (tm != null) { tm.set(v.id, aty); }
                        return;
                    }
                }

                // Address mode (r46): the value IS the element's storage
                // address — args[0]=array storage ptr, args[1]=index.
                // Element stride comes from the index expression's own
                // annotation (the element type synth_index proved), and the
                // index is extended to the i64 GEP operand signedness-aware.
                if (v.ival == -3 && v.arg_count >= 2)
                {
                    ssi_ir::IrVal* abase = v.args[0];
                    ssi_ir::IrVal* aidx  = v.args[1];
                    char[TYMAP_ENTRY] iaeb; iaeb[0] = 0;
                    if (v.src != null && v.src.type_annotation != null)
                    {
                        char* iet = type_to_llvm_buf(v.src.type_annotation, &iaeb[0], 64, 0);
                        if (iet != null && iet != &iaeb[0] && iet[0] != 0)
                        {
                            usz ik = 0;
                            while (ik < 63 && iet[ik] != 0) { iaeb[ik] = iet[ik]; ik++; }
                            iaeb[ik] = 0;
                        }
                    }
                    if (iaeb[0] == 0) { iaeb[0] = 'i'; iaeb[1] = '6'; iaeb[2] = '4'; iaeb[3] = 0; }
                    char* ia_idx_ty = (tm != null && aidx != null) ? tm.get(aidx.id) : null;
                    bool ia_ext = (ia_idx_ty != null && ia_idx_ty[0] == 'i'
                                   && !(ia_idx_ty[1] == '6' && ia_idx_ty[2] == '4' && ia_idx_ty[3] == 0));
                    if (ia_ext && aidx != null)
                    {
                        cg.out.writes("  %ia.idx.v"); cg.out.writei(v.id);
                        cg.out.writes(!is_signed_int_val(aidx) ? " = zext " : " = sext ");
                        cg.out.writes(ia_idx_ty); cg.out.writes(" ");
                        cg.emit_vref(aidx);
                        cg.out.writes(" to i64\n");
                    }
                    cg.out.writes("  %ia.gep.v"); cg.out.writei(v.id);
                    cg.out.writes(" = getelementptr inbounds ");
                    cg.out.writes(&iaeb[0]);
                    cg.out.writes(", ptr ");
                    if (abase != null) { cg.emit_vref(abase); } else { cg.out.writes("null"); }
                    cg.out.writes(", i64 ");
                    if (ia_ext) { cg.out.writes("%ia.idx.v"); cg.out.writei(v.id); }
                    else if (aidx != null) { cg.emit_vref(aidx); }
                    else { cg.out.writes("0"); }
                    cg.out.writes("\n");
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = getelementptr inbounds i8, ptr %ia.gep.v");
                    cg.out.writei(v.id);
                    cg.out.writes(", i64 0\n");
                    if (tm != null) { tm.set(v.id, (char*)"ptr"); }
                    return;
                }

                // Closure env slot: base=env_ptr, v.ival=slot_index, no args[1]
                // Only fires inside a closure thunk (cur_fn_decl.kind == NODE_EXPR_CLOSURE)
                // to avoid false-firing on regular fn params with IR_INDEX patterns.
                bool is_in_closure_thunk = (cg.cur_fn_decl != null
                    && cg.cur_fn_decl.kind == Nk.NODE_EXPR_CLOSURE);
                // Emit: gep [N x ptr], ptr %env, 0, slot; load ptr; ptrtoint
                // The base must be THE env parameter, not just any param: the
                // thunk's env param carries the closure AST node as its src,
                // while the thunk's user parameters carry pattern nodes. The
                // shape-only check used to false-fire on tuple/union
                // destructuring of a closure's own argument (a 1-arg IR_INDEX
                // over an IR_PARAM inside a thunk), reading a union tag /
                // payload as if it were a captured-variable slot.
                if (index == null && v.arg_count == 1 && base != null
                    && v.src != null  // has a captured binder
                    && base.op == ssi_ir::IrOp.IR_PARAM  // env is a param
                    && base.src != null && base.src == cg.cur_fn_decl  // THE env param
                    && is_in_closure_thunk)               // inside a closure thunk
                {
                    long slot3 = (long)v.ival;
                    cg.out.writes("  %envgep."); cg.out.writei(v.id);
                    cg.out.writes(" = getelementptr ptr, ptr ");
                    cg.emit_vref(base);
                    cg.out.writes(", i32 "); cg.out.writei(slot3); cg.out.writes("\n");
                    cg.out.writes("  %envld."); cg.out.writei(v.id);
                    cg.out.writes(" = load ptr, ptr %envgep."); cg.out.writei(v.id);
                    cg.out.writes("\n");
                    // Recover the captured value from the slot's ptr.
                    char* vty3 = (tm != null) ? tm.get(v.id) : null;
                    if (vty3 == null || vty3[0] == 0) vty3 = (char*)"i64";
                    if (vty3[0] == '{' || vty3[0] == '%')
                    {
                        // Aggregate capture: the slot holds a pointer to the
                        // heap box written at capture time — load it back.
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = load "); cg.out.writes(vty3);
                        cg.out.writes(", ptr %envld."); cg.out.writei(v.id);
                        cg.out.writes("\n");
                    }
                    else if (vty3[0] == 'p')
                    {
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = bitcast ptr %envld."); cg.out.writei(v.id);
                        cg.out.writes(" to ptr\n");
                    }
                    else
                    {
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = ptrtoint ptr %envld."); cg.out.writei(v.id);
                        cg.out.writes(" to "); cg.out.writes(vty3); cg.out.writes("\n");
                    }
                    return;
                }

                // Detect struct/tuple index: use extractvalue not GEP.
                // Two patterns:
                //   A. let (ok, v) = f() — IR_INDEX with 1 arg, field idx in v.ival
                //   B. arr[expr] with struct base — IR_INDEX with 2 args, base is struct
                //
                // String indexing (v.md §10.2: `s[i]` is the byte at offset
                // i, u8-typed by synth_index). A Str-typed base must NOT take
                // the tuple-extractvalue path — extractvalue of a byte-global
                // is invalid IR, and "field 1" of the { ptr, len } record is
                // the LENGTH, not element i. Load the byte through the data
                // pointer instead.
                bool base_is_str = false;
                if (base != null && base.op == ssi_ir::IrOp.IR_CONST_STR)
                { base_is_str = true; }
                else if (v.src != null && v.src.child_count >= 1 && v.src.children[0] != null)
                {
                    Node* san = v.src.children[0].type_annotation;
                    if (san != null && san.kind == Nk.NODE_TYPE_PRIMITIVE
                        && san.p.ident.name_len == 3
                        && san.p.ident.name_ptr[0] == 'S'
                        && san.p.ident.name_ptr[1] == 't'
                        && san.p.ident.name_ptr[2] == 'r')
                    { base_is_str = true; }
                }
                // Tensor indexing (PrideTensor wire format — compiler_rt §8:
                // rank, dims[rank], double data[]). A rank-1 index loads the
                // element (a double) and converts to the element type the
                // program sees; a rank ≥ 2 index materialises a headered
                // sub-tensor VIEW: fresh rank-(R-1) tensor on the stack with
                // dims from the annotation and its row memcpy'd out of the
                // source. Every tensor-typed value then always points at a
                // full header — chained indexing t[i][j] stays uniform.
                Node* tbase_ann = (v.src != null && v.src.child_count >= 1
                                   && v.src.children[0] != null)
                                  ? v.src.children[0].type_annotation : null;
                if (tbase_ann != null && tbase_ann.kind == Nk.NODE_TYPE_TENSOR
                    && base != null)
                {
                    usz trank = tbase_ann.child_count >= 1 ? tbase_ann.child_count - 1 : 1;
                    long data_off = (long)(1 + trank) * 8;
                    if (trank <= 1)
                    {
                        cg.out.writes("  %td.gep.v"); cg.out.writei(v.id);
                        cg.out.writes(" = getelementptr inbounds i8, ptr ");
                        cg.emit_vref(base);
                        cg.out.writes(", i64 "); cg.out.writei((long)data_off); cg.out.writes("\n");
                        cg.out.writes("  %gep.v"); cg.out.writei(v.id);
                        cg.out.writes(" = getelementptr inbounds double, ptr %td.gep.v");
                        cg.out.writei(v.id);
                        cg.out.writes(", i64 ");
                        cg.emit_vref(index);
                        cg.out.writes("\n");
                        char* erty = (tm != null) ? tm.get(v.id) : null;
                        if (erty == null || erty[0] == 0) erty = (char*)"double";
                        if (erty[0] == 'd')
                        {
                            cg.out.writes("  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = load double, ptr %gep.v"); cg.out.writei(v.id);
                            cg.out.writes("\n");
                        }
                        else if (erty[0] == 'f')
                        {
                            cg.out.writes("  %v.ld"); cg.out.writei(v.id);
                            cg.out.writes(" = load double, ptr %gep.v"); cg.out.writei(v.id); cg.out.writes("\n");
                            cg.out.writes("  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = fptrunc double %v.ld"); cg.out.writei(v.id);
                            cg.out.writes(" to float\n");
                        }
                        else
                        {
                            cg.out.writes("  %v.ld"); cg.out.writei(v.id);
                            cg.out.writes(" = load double, ptr %gep.v"); cg.out.writei(v.id); cg.out.writes("\n");
                            cg.out.writes("  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = fptosi double %v.ld"); cg.out.writei(v.id);
                            cg.out.writes(" to "); cg.out.writes(erty); cg.out.writes("\n");
                        }
                        return;
                    }
                    long row_elems = 1;
                    for (usz di = 2; di < tbase_ann.child_count; di++)
                    {
                        Node* dc = tbase_ann.children[di];
                        row_elems *= (dc != null && dc.kind == Nk.NODE_LIT_INT)
                                     ? (long)dc.p.lit_int.int_val : 1;
                    }
                    long row_bytes = row_elems * 8;
                    long sub_hdr = (long)trank * 8;   // (1 + (rank-1)) * 8
                    cg.out.writes("  %th.v"); cg.out.writei(v.id);
                    cg.out.writes(" = alloca i8, i64 ");
                    cg.out.writei((long)(sub_hdr + row_bytes)); cg.out.writes("\n");
                    cg.out.writes("  store i64 "); cg.out.writeu((ulong)(trank - 1));
                    cg.out.writes(", ptr %th.v"); cg.out.writei(v.id); cg.out.writes("\n");
                    for (usz di = 2; di < tbase_ann.child_count; di++)
                    {
                        Node* dc = tbase_ann.children[di];
                        long dv = (dc != null && dc.kind == Nk.NODE_LIT_INT)
                                  ? (long)dc.p.lit_int.int_val : 0;
                        cg.out.writes("  %th.d"); cg.out.writei(v.id);
                        cg.out.writes("."); cg.out.writeu(di - 1);
                        cg.out.writes(" = getelementptr inbounds i64, ptr %th.v");
                        cg.out.writei(v.id);
                        cg.out.writes(", i64 "); cg.out.writeu((ulong)(di - 1)); cg.out.writes("\n");
                        cg.out.writes("  store i64 "); cg.out.writei((long)dv);
                        cg.out.writes(", ptr %th.d"); cg.out.writei(v.id);
                        cg.out.writes("."); cg.out.writeu(di - 1); cg.out.writes("\n");
                    }
                    cg.out.writes("  %tr.off.v"); cg.out.writei(v.id);
                    cg.out.writes(" = mul i64 ");
                    cg.emit_vref(index);
                    cg.out.writes(", "); cg.out.writei((long)row_bytes); cg.out.writes("\n");
                    cg.out.writes("  %tr.base.v"); cg.out.writei(v.id);
                    cg.out.writes(" = getelementptr inbounds i8, ptr ");
                    cg.emit_vref(base);
                    cg.out.writes(", i64 "); cg.out.writei((long)data_off); cg.out.writes("\n");
                    cg.out.writes("  %tr.src.v"); cg.out.writei(v.id);
                    cg.out.writes(" = getelementptr inbounds i8, ptr %tr.base.v");
                    cg.out.writei(v.id);
                    cg.out.writes(", i64 %tr.off.v"); cg.out.writei(v.id); cg.out.writes("\n");
                    cg.out.writes("  %th.dst.v"); cg.out.writei(v.id);
                    cg.out.writes(" = getelementptr inbounds i8, ptr %th.v"); cg.out.writei(v.id);
                    cg.out.writes(", i64 "); cg.out.writei((long)sub_hdr); cg.out.writes("\n");
                    cg.out.writes("  call void @llvm.memcpy.p0.p0.i64(ptr %th.dst.v");
                    cg.out.writei(v.id);
                    cg.out.writes(", ptr %tr.src.v"); cg.out.writei(v.id);
                    cg.out.writes(", i64 "); cg.out.writei((long)row_bytes);
                    cg.out.writes(", i1 false)\n");
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = bitcast ptr %th.v"); cg.out.writei(v.id);
                    cg.out.writes(" to ptr\n");
                    if (tm != null) { tm.set(v.id, (char*)"ptr"); }
                    return;
                }
                if (base_is_str)
                {
                    // Data pointer: the literal's byte global directly, else
                    // field 0 of the fat record value.
                    if (base != null && base.op == ssi_ir::IrOp.IR_CONST_STR)
                    {
                        cg.out.writes("  %gep.v"); cg.out.writei(v.id);
                        cg.out.writes(" = getelementptr inbounds i8, ptr @.str.");
                        cg.out.writei(base.id);
                    }
                    else
                    {
                        char* srt = (tm != null) ? tm.get(base.id) : null;
                        if (srt == null) srt = resolve_ty(tm, base);
                        if (srt == null || srt[0] != '{') srt = (char*)"{ ptr, i64 }";
                        cg.out.writes("  %str.ptr.v"); cg.out.writei(v.id);
                        cg.out.writes(" = extractvalue "); cg.out.writes(srt);
                        cg.out.writes(" ");
                        if (base != null) { cg.emit_vref(base); } else { cg.out.writes("undef"); }
                        cg.out.writes(", 0\n");
                        cg.out.writes("  %gep.v"); cg.out.writei(v.id);
                        cg.out.writes(" = getelementptr inbounds i8, ptr %str.ptr.v");
                        cg.out.writei(v.id);
                    }
                    cg.out.writes(", i64 ");
                    cg.emit_vref(index);
                    cg.out.writes("\n");
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = load i8, ptr %gep.v"); cg.out.writei(v.id);
                    cg.out.writes("\n");
                    return;
                }
                // r56: fat-slice value indexing — s[i] where s : [T] is a
                // { ptr, i64 } record, not a memory ptr. Extract the data
                // pointer, GEP by the dynamic index, load the element.
                // (The extractvalue arm below would read record FIELDS.)
                if (base != null && index != null)
                {
                    char* btm_sl = (tm != null) ? tm.get(base.id) : null;
                    if (btm_sl == null) btm_sl = resolve_ty(tm, base);
                    Node* slann = (v.src != null && v.src.child_count >= 1
                                   && v.src.children[0] != null)
                                  ? v.src.children[0].type_annotation : null;
                    if (slann != null && slann.kind == Nk.NODE_TYPE_PTR
                        && slann.child_count >= 1 && slann.children[0] != null)
                    { slann = slann.children[0]; }
                    if (btm_sl != null && btm_sl[0] == '{'
                        && slann != null && slann.kind == Nk.NODE_TYPE_SLICE)
                    {
                        char[TYMAP_ENTRY] sleb; sleb[0] = 0;
                        if (v.src != null && v.src.type_annotation != null)
                        {
                            char* selt = type_to_llvm_buf(v.src.type_annotation,
                                                          &sleb[0], 64, 0);
                            if (selt != null && selt != &sleb[0] && selt[0] != 0)
                            {
                                usz sk = 0;
                                while (sk < 63 && selt[sk] != 0) { sleb[sk] = selt[sk]; sk++; }
                                sleb[sk] = 0;
                            }
                        }
                        if (sleb[0] == 0) { sleb[0]='i'; sleb[1]='6'; sleb[2]='4'; sleb[3]=0; }
                        char* sl_idx_ty = (tm != null) ? tm.get(index.id) : null;
                        bool sl_ext = (sl_idx_ty != null && sl_idx_ty[0] == 'i'
                            && !(sl_idx_ty[1] == '6' && sl_idx_ty[2] == '4' && sl_idx_ty[3] == 0));
                        if (sl_ext)
                        {
                            cg.out.writes("  %sl.idx.v"); cg.out.writei(v.id);
                            cg.out.writes(!is_signed_int_val(index) ? " = zext " : " = sext ");
                            cg.out.writes(sl_idx_ty); cg.out.writes(" ");
                            cg.emit_vref(index);
                            cg.out.writes(" to i64\n");
                        }
                        cg.out.writes("  %sl.ptr.v"); cg.out.writei(v.id);
                        cg.out.writes(" = extractvalue "); cg.out.writes(btm_sl);
                        cg.out.writes(" "); cg.emit_vref(base); cg.out.writes(", 0\n");
                        cg.out.writes("  %sl.gep.v"); cg.out.writei(v.id);
                        cg.out.writes(" = getelementptr inbounds ");
                        cg.out.writes(&sleb[0]);
                        cg.out.writes(", ptr %sl.ptr.v"); cg.out.writei(v.id);
                        cg.out.writes(", i64 ");
                        if (sl_ext) { cg.out.writes("%sl.idx.v"); cg.out.writei(v.id); }
                        else { cg.emit_vref(index); }
                        cg.out.writes("\n");
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = load "); cg.out.writes(&sleb[0]);
                        cg.out.writes(", ptr %sl.gep.v"); cg.out.writei(v.id);
                        cg.out.writes("\n");
                        return;
                    }
                }
                if (base != null)
                {
                    char* base_struct_ty = (tm != null) ? tm.get(base.id) : null;
                    if (base_struct_ty == null) base_struct_ty = resolve_ty(tm, base);
                    if (base_struct_ty != null && base_struct_ty[0] == '{')
                    {
                        // extractvalue: field index from args[1].ival or v.ival (tuple destr)
                        long fidx = 0;
                        if (index != null && index.op == ssi_ir::IrOp.IR_CONST_INT)
                        { fidx = (long)index.ival; }
                        else
                        { fidx = (long)v.ival; }  // stored by bind_let_pattern
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = extractvalue "); cg.out.writes(base_struct_ty);
                        cg.out.writes(" "); cg.emit_vref(base);
                        cg.out.writes(", "); cg.out.writei(fidx); cg.out.writes("\n");
                        return;
                    }
                }

                // Ensure base is ptr for index GEP (pre-emit alloca+store
                // for struct AND inline-array values held in registers)
                if (base != null)
                {
                    char* ibt = (tm != null) ? tm.get(base.id) : null;
                    if (ibt != null && (ibt[0] == '%' || ibt[0] == '['))
                    {
                        cg.out.writes("  %struct.ptr.v"); cg.out.writei(v.id);
                        cg.out.writes(" = alloca "); cg.out.writes(ibt); cg.out.writes("\n");
                        cg.out.writes("  store "); cg.out.writes(ibt);
                        cg.out.writes(" "); cg.emit_vref(base);
                        cg.out.writes(", ptr %struct.ptr.v"); cg.out.writei(v.id); cg.out.writes("\n");
                    }
                    else if (ibt != null && ibt[0] != 'p' && ibt[0] != 0)
                    {
                        cg.out.writes("  %gep.itp.idx.v"); cg.out.writei(v.id);
                        cg.out.writes(" = inttoptr "); cg.out.writes(ibt);
                        cg.out.writes(" "); cg.emit_vref(base); cg.out.writes(" to ptr\n");
                    }
                }
                // %gep = getelementptr inbounds ElemType, ptr %base, i64 %index
                cg.out.writes("  %gep.v"); cg.out.writei(v.id);
                cg.out.writes(" = getelementptr inbounds ");
                cg.writes_ty(tm, v.id);
                cg.out.writes(", ptr ");
                if (base != null)
                {
                    char* ibt2 = (tm != null) ? tm.get(base.id) : null;
                    if (ibt2 != null && ibt2[0] == '[')
                    { cg.out.writes("%struct.ptr.v"); cg.out.writei(v.id); }
                    else if (ibt2 != null && ibt2[0] != 'p' && ibt2[0] != '%' && ibt2[0] != 0)
                    { cg.out.writes("%gep.itp.idx.v"); cg.out.writei(v.id); }
                    else { cg.emit_vref(base); }
                }
                else { cg.out.writes("null"); }
                cg.out.writes(", i64 ");
                cg.emit_vref(index);
                cg.out.writes("\n");
                // %vN = load ElemType, ptr %gep
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = load ");
                cg.writes_ty(tm, v.id);
                cg.out.writes(", ptr %gep.v");
                cg.out.writei(v.id);
                cg.out.writes("\n");
            }

        case ssi_ir::IrOp.IR_STORE:
            {
                // IR_STORE: always a side-effecting instruction — never DCE'd.
                // Variant A: *ptr = val       → args[0]=ptr, args[1]=val
                // Variant B: arr[i] = val     → args[0]=base, args[1]=val, args[2]=index
                // Variant C: s.field = val    → args[0]=base, args[1]=val, src=field_expr
                ssi_ir::IrVal* base_arg  = v.arg_count >= 1 ? v.args[0] : null;
                ssi_ir::IrVal* val_arg   = v.arg_count >= 2 ? v.args[1] : null;
                ssi_ir::IrVal* idx_arg   = v.arg_count >= 3 ? v.args[2] : null;
                char* val_ty_st = (tm != null && val_arg != null) ? tm.get(val_arg.id) : null;
                if (val_ty_st == null || val_ty_st[0] == 0) val_ty_st = (char*)"i64";

                if (idx_arg != null)
                {
                    // Array index store: GEP then store.
                    // Determine element type from the lhs Index annotation (persistent storage)
                    char[TYMAP_ENTRY] elem_ty_buf;
                    elem_ty_buf[0] = 0;
                    char* elem_ty_st = &elem_ty_buf[0];
                    if (v.src != null && v.src.child_count >= 1 && v.src.children[0] != null)
                    {
                        Node* lhs_node2 = v.src.children[0];
                        if (lhs_node2.type_annotation != null)
                        {
                            char* et2 = type_to_llvm_buf(lhs_node2.type_annotation, &elem_ty_buf[0], 64, 0);
                            if (et2 != null && et2 != &elem_ty_buf[0] && et2[0] != 0)
                            {
                                // type_to_llvm_buf returned a literal — copy to our buf
                                usz ek2 = 0;
                                while (ek2 < 63 && et2[ek2] != 0) { elem_ty_buf[ek2]=et2[ek2]; ek2++; }
                                elem_ty_buf[ek2] = 0;
                            }
                        }
                    }
                    if (elem_ty_buf[0] == 0)
                    {
                        // Fallback: use value type
                        usz ek3 = 0;
                        while (ek3 < 63 && val_ty_st[ek3] != 0) { elem_ty_buf[ek3]=val_ty_st[ek3]; ek3++; }
                        elem_ty_buf[ek3] = 0;
                        elem_ty_st = &elem_ty_buf[0];
                    }

                    // r56: fat-slice base — s[i] = v writes through the
                    // record's data pointer, not through the record value.
                    {
                        char* btm_ss = (tm != null && base_arg != null)
                                     ? tm.get(base_arg.id) : null;
                        if (btm_ss == null && base_arg != null)
                        { btm_ss = resolve_ty(tm, base_arg); }
                        // The assign's lhs is an Index node (annotated with
                        // the ELEMENT type) — reach through it to the base.
                        Node* ss_lhs = (v.src != null && v.src.child_count >= 1)
                                     ? v.src.children[0] : null;
                        Node* ss_ann = null;
                        if (ss_lhs != null && ss_lhs.kind == Nk.NODE_EXPR_INDEX
                            && ss_lhs.child_count >= 1 && ss_lhs.children[0] != null)
                        { ss_ann = ss_lhs.children[0].type_annotation; }
                        else if (ss_lhs != null)
                        { ss_ann = ss_lhs.type_annotation; }
                        if (ss_ann != null && ss_ann.kind == Nk.NODE_TYPE_PTR
                            && ss_ann.child_count >= 1 && ss_ann.children[0] != null)
                        { ss_ann = ss_ann.children[0]; }
                        if (btm_ss != null && btm_ss[0] == '{'
                            && ss_ann != null && ss_ann.kind == Nk.NODE_TYPE_SLICE)
                        {
                            cg.out.writes("  %ss.ptr.v"); cg.out.writei(v.id);
                            cg.out.writes(" = extractvalue "); cg.out.writes(btm_ss);
                            cg.out.writes(" "); cg.emit_vref(base_arg);
                            cg.out.writes(", 0\n");
                            cg.out.writes("  %st.gep.v"); cg.out.writei(v.id);
                            cg.out.writes(" = getelementptr inbounds ");
                            cg.out.writes(elem_ty_st);
                            cg.out.writes(", ptr %ss.ptr.v"); cg.out.writei(v.id);
                            cg.out.writes(", i64 ");
                            cg.emit_vref(idx_arg);
                            cg.out.writes("\n");
                            // Coerce the value to the element type (int/float).
                            if (val_ty_st[0] == 'i' && elem_ty_st[0] == 'i')
                            {
                                long en4 = 0; long vn4 = 0;
                                char* ep4 = elem_ty_st + 1;
                                while (*ep4 >= '0' && *ep4 <= '9')
                                { en4 = en4 * 10 + (long)(*ep4 - '0'); ep4++; }
                                char* vp4 = val_ty_st + 1;
                                while (*vp4 >= '0' && *vp4 <= '9')
                                { vn4 = vn4 * 10 + (long)(*vp4 - '0'); vp4++; }
                                if (vn4 > 0 && en4 > 0 && vn4 != en4)
                                {
                                    cg.out.writes("  %st.cvt.v"); cg.out.writei(v.id);
                                    cg.out.writes(vn4 > en4 ? " = trunc " : " = zext ");
                                    cg.out.writes(val_ty_st); cg.out.writes(" ");
                                    cg.emit_vref(val_arg);
                                    cg.out.writes(" to "); cg.out.writes(elem_ty_st);
                                    cg.out.writes("\n");
                                    cg.out.writes("  store "); cg.out.writes(elem_ty_st);
                                    cg.out.writes(" %st.cvt.v"); cg.out.writei(v.id);
                                    cg.out.writes(", ptr %st.gep.v"); cg.out.writei(v.id);
                                    cg.out.writes("\n");
                                    return;
                                }
                            }
                            cg.out.writes("  store "); cg.out.writes(elem_ty_st);
                            cg.out.writes(" ");
                            cg.emit_vref(val_arg);
                            cg.out.writes(", ptr %st.gep.v"); cg.out.writei(v.id);
                            cg.out.writes("\n");
                            return;
                        }
                    }
                    // Inline array held in a register (struct field, loaded
                    // value): give it a memory home before GEP (r46).
                    char* arrbase_ty = (tm != null && base_arg != null) ? tm.get(base_arg.id) : null;
                    if (arrbase_ty != null && arrbase_ty[0] == '[')
                    {
                        cg.out.writes("  %st.arrptr.v"); cg.out.writei(v.id);
                        cg.out.writes(" = alloca "); cg.out.writes(arrbase_ty); cg.out.writes("\n");
                        cg.out.writes("  store "); cg.out.writes(arrbase_ty); cg.out.writes(" ");
                        cg.emit_vref(base_arg);
                        cg.out.writes(", ptr %st.arrptr.v"); cg.out.writei(v.id); cg.out.writes("\n");
                    }
                    cg.out.writes("  %st.gep.v"); cg.out.writei(v.id);
                    cg.out.writes(" = getelementptr inbounds ");
                    cg.out.writes(elem_ty_st);  // element stride type (i8 for u8 arrays)
                    cg.out.writes(", ptr ");
                    if (arrbase_ty != null && arrbase_ty[0] == '[')
                    { cg.out.writes("%st.arrptr.v"); cg.out.writei(v.id); }
                    else if (base_arg != null) { cg.emit_vref(base_arg); } else { cg.out.writes("null"); }
                    cg.out.writes(", i64 ");
                    cg.emit_vref(idx_arg);
                    cg.out.writes("\n");
                    // Coerce value to element type if needed (e.g. i64 literal → i8 for u8 arrays)
                    bool val_needs_coerce = false;
                    {
                        usz el = strlen(elem_ty_st); usz vl2 = strlen(val_ty_st);
                        if (el != vl2) { val_needs_coerce = true; }
                        else { for(usz ci=0;ci<el;ci++) { if(elem_ty_st[ci]!=val_ty_st[ci]) { val_needs_coerce=true; break; } } }
                    }
                    if (val_needs_coerce && val_arg != null
                        && elem_ty_st[0]=='i' && val_ty_st[0]=='i')
                    {
                        // int→int: trunc or sext
                        long en2=0; long vn2=0;
                        char* ep2=elem_ty_st+1; while(*ep2>='0'&&*ep2<='9'){en2=en2*10+(long)(*ep2-'0');ep2++;}
                        char* vp2=val_ty_st+1;  while(*vp2>='0'&&*vp2<='9'){vn2=vn2*10+(long)(*vp2-'0');vp2++;}
                        cg.out.writes("  %st.coerce.v"); cg.out.writei(v.id);
                        if (vn2 > en2) { cg.out.writes(" = trunc "); }
                        else if (!is_signed_int_val(val_arg)) { cg.out.writes(" = zext "); }
                        else           { cg.out.writes(" = sext ");  }
                        cg.out.writes(val_ty_st); cg.out.writes(" ");
                        if (val_arg != null) { cg.emit_vref(val_arg); } else { cg.out.writes("undef"); }
                        cg.out.writes(" to "); cg.out.writes(elem_ty_st); cg.out.writes("\n");
                        cg.out.writes("  store "); cg.out.writes(elem_ty_st);
                        cg.out.writes(" %st.coerce.v"); cg.out.writei(v.id);
                    }
                    else
                    {
                        cg.out.writes("  store "); cg.out.writes(elem_ty_st); cg.out.writes(" ");
                        if (val_arg != null) { cg.emit_vref(val_arg); } else { cg.out.writes("undef"); }
                    }
                    cg.out.writes(", ptr %st.gep.v"); cg.out.writei(v.id);
                    cg.out.writes("\n");
                }
                else if (v.src != null && v.src.kind == Nk.NODE_EXPR_FIELD)
                {
                    // Field store: GEP into struct then store
                    // Resolve field index from the field expr
                    Node* base_node  = v.src.child_count >= 1 ? v.src.children[0] : null;
                    Node* fname_node = v.src.child_count >= 2 ? v.src.children[1] : null;
                    char* fn_ptr = fname_node != null ? fname_node.p.ident.name_ptr : null;
                    usz   fn_len = fname_node != null ? fname_node.p.ident.name_len : 0;
                    // Find the struct decl carrying the field block. Mirrors the
                    // field-LOAD path and typecheck's struct_fields_of — including
                    // `type X = struct …` aliases — because the write-side ident
                    // keeps a raw `*Alias` annotation whose TypeVar resolves to a
                    // NODE_DECL_TYPE, not directly to NODE_DECL_STRUCT. The old code
                    // gave up here and fell through to a scalar `gep i64` with index
                    // 0: illegal IR, and silently the WRONG field.
                    int fidx = 0;
                    Node* store_struct_decl = null;
                    if (base_node != null && base_node.type_annotation != null)
                    {
                        Node* ta = base_node.type_annotation;
                        // Unwrap *Struct → Struct
                        if (ta.kind == Nk.NODE_TYPE_PTR && ta.child_count >= 1 && ta.children[0] != null)
                        { ta = ta.children[0]; }
                        store_struct_decl = struct_body_of(ta);
                    }
                    // Fallbacks identical to the field-LOAD path: the base ident may
                    // resolve directly to an aggregate decl, or to a let/param/pattern
                    // binder whose declared type names the aggregate.
                    if (store_struct_decl == null && base_node != null
                        && base_node.resolved != null)
                    {
                        store_struct_decl = struct_body_of(base_node.resolved);
                    }
                    if (store_struct_decl == null && base_node != null
                        && base_node.resolved != null)
                    {
                        Node* bdecl = base_node.resolved;
                        Node* dtype = bdecl.type_annotation;
                        if (dtype == null && bdecl.child_count >= 1 && bdecl.children[0] != null)
                        { dtype = bdecl.children[0].type_annotation; }
                        if (dtype != null)
                        {
                            if (dtype.kind == Nk.NODE_TYPE_PTR && dtype.child_count >= 1
                                && dtype.children[0] != null)
                            { dtype = dtype.children[0]; }
                            store_struct_decl = struct_body_of(dtype);
                        }
                    }
                    if (store_struct_decl != null && fn_ptr != null)
                    { fidx = field_index_of(store_struct_decl, fn_ptr, fn_len); }
                    // Get struct type name
                    char* base_ty_st2 = (tm != null && base_arg != null) ? tm.get(base_arg.id) : null;
                    if (base_ty_st2 != null && base_ty_st2[0] == '%')
                    {
                        // Struct-typed base: alloca+store to get ptr, then GEP
                        cg.out.writes("  %st.sptr.v"); cg.out.writei(v.id);
                        cg.out.writes(" = alloca "); cg.out.writes(base_ty_st2); cg.out.writes("\n");
                        cg.out.writes("  store "); cg.out.writes(base_ty_st2); cg.out.writes(" ");
                        if (base_arg != null) { cg.emit_vref(base_arg); } else { cg.out.writes("undef"); }
                        cg.out.writes(", ptr %st.sptr.v"); cg.out.writei(v.id); cg.out.writes("\n");
                        cg.out.writes("  %st.gep.v"); cg.out.writei(v.id);
                        cg.out.writes(" = getelementptr inbounds "); cg.out.writes(base_ty_st2);
                        cg.out.writes(", ptr %st.sptr.v"); cg.out.writei(v.id);
                        cg.out.writes(", i32 0, i32 "); cg.out.writei(fidx); cg.out.writes("\n");
                    }
                    else
                    {
                        // Already ptr: GEP into the struct.
                        // Use the resolved struct_decl type (named or inline) for correct field offsets.
                        cg.out.writes("  %st.gep.v"); cg.out.writei(v.id);
                        cg.out.writes(" = getelementptr inbounds ");
                        // GEP source type: prefer the tymap aggregate (identical to the
                        // load-side GEPs for the same base value), then the named
                        // struct; the last-resort scalar form must stay VALID IR, so
                        // it switches to single-index array stride below.
                        bool agg_gep = true;
                        if (base_ty_st2 != null && base_ty_st2[0] == '{')
                        {
                            cg.out.writes(base_ty_st2);
                        }
                        else if (store_struct_decl != null && store_struct_decl.child_count >= 1
                            && store_struct_decl.children[0] != null
                            && store_struct_decl.children[0].kind == Nk.NODE_IDENT)
                        {
                            // Named struct: %StructName
                            cg.out.writes("%");
                            cg.out.write(store_struct_decl.children[0].p.ident.name_ptr,
                                         store_struct_decl.children[0].p.ident.name_len);
                        }
                        else if (store_struct_decl != null)
                        {
                            // Anonymous aggregate (e.g. the body of a
                            // `type X = struct …` alias): spell the type inline from
                            // the field declarations, exactly like the field-load
                            // GEP path — loads and stores then agree bit-for-bit.
                            cg.out.writes("{ ");
                            bool first_f = true;
                            for (usz sfi3 = 0; sfi3 < store_struct_decl.child_count; sfi3++)
                            {
                                Node* sb3 = store_struct_decl.children[sfi3];
                                if (sb3 == null || sb3.kind != Nk.NODE_EXPR_BLOCK) continue;
                                for (usz sgi3 = 0; sgi3 < sb3.child_count; sgi3++)
                                {
                                    Node* fd3 = sb3.children[sgi3];
                                    if (fd3 == null || fd3.kind != Nk.NODE_FIELD_DECL) continue;
                                    if (!first_f) { cg.out.writes(", "); }
                                    first_f = false;
                                    Node* ft3 = fd3.child_count >= 2 ? fd3.children[1] : null;
                                    char[TYMAP_ENTRY] ftb3; ftb3[0] = 0;
                                    type_to_llvm_buf(ft3, &ftb3[0], TYMAP_ENTRY, 0);
                                    cg.out.writes(ftb3[0] != 0 ? &ftb3[0] : "i64");
                                }
                            }
                            cg.out.writes(" }");
                        }
                        else
                        {
                            cg.out.writes("i64");  // single-index stride (only safe for i64 fields)
                            agg_gep = false;
                        }
                        cg.out.writes(", ptr ");
                        if (base_arg != null) { cg.emit_vref(base_arg); } else { cg.out.writes("null"); }
                        if (agg_gep) { cg.out.writes(", i32 0, i32 "); }
                        else         { cg.out.writes(", i64 "); }
                        cg.out.writei(fidx); cg.out.writes("\n");
                    }
                    // Determine store type: prefer the field's declared type over the value's tymap.
                    // IR_CONST_INT has tymap "i64" even for i32 fields — `store i64 1` into i32 slot
                    // corrupts the next field. Find the field's actual LLVM type from the struct decl.
                    {
                        char[TYMAP_ENTRY] fst_buf; fst_buf[0] = 0;
                        char* field_store_ty = val_ty_st;
                        if (store_struct_decl != null && fn_ptr != null && fn_len > 0)
                        {
                            for (usz sfi2 = 0; sfi2 < store_struct_decl.child_count; sfi2++)
                            {
                                Node* sb2 = store_struct_decl.children[sfi2];
                                if (sb2 == null || sb2.kind != Nk.NODE_EXPR_BLOCK) continue;
                                for (usz sgi2 = 0; sgi2 < sb2.child_count; sgi2++)
                                {
                                    Node* fd2 = sb2.children[sgi2];
                                    if (fd2 == null || fd2.kind != Nk.NODE_FIELD_DECL || fd2.child_count < 2) continue;
                                    Node* fn2 = fd2.children[0];
                                    if (fn2 == null || fn2.p.ident.name_len != fn_len) continue;
                                    bool match2 = true;
                                    for (usz ki = 0; ki < fn_len; ki++)
                                    { if (fn2.p.ident.name_ptr[ki] != fn_ptr[ki]) { match2=false; break; } }
                                    if (!match2) continue;
                                    Node* fty2 = fd2.children[1];
                                    if (fty2 != null)
                                    {
                                        type_to_llvm_buf(fty2, &fst_buf[0], TYMAP_ENTRY, 0);
                                        if (fst_buf[0] != 0) field_store_ty = &fst_buf[0];
                                    }
                                    break;
                                }
                            }
                        }
                        // Emit integer coerce if value width != field width
                        char* emit_val_ref_str = null;  // if non-null, use as coerce result name
                        if (field_store_ty != val_ty_st && field_store_ty[0] == 'i' && val_ty_st[0] == 'i')
                        {
                            int sw1=0; int sw2=0;
                            char* ap2=val_ty_st+1;    while(*ap2>='0'&&*ap2<='9'){sw1=sw1*10+(int)(*ap2-'0');ap2++;}
                            char* bp2=field_store_ty+1; while(*bp2>='0'&&*bp2<='9'){sw2=sw2*10+(int)(*bp2-'0');bp2++;}
                            if (sw1 != sw2)
                            {
                                cg.out.writes("  %fst.coerce.v"); cg.out.writei(v.id);
                                if (sw1 > sw2)                       { cg.out.writes(" = trunc "); }
                                else if (!is_signed_int_val(val_arg)) { cg.out.writes(" = zext "); }
                                else                                  { cg.out.writes(" = sext "); }
                                cg.out.writes(val_ty_st); cg.out.writes(" ");
                                if (val_arg != null) { cg.emit_vref(val_arg); } else { cg.out.writes("undef"); }
                                cg.out.writes(" to "); cg.out.writes(field_store_ty); cg.out.writes("\n");
                                emit_val_ref_str = (char*)"%fst.coerce.v";
                            }
                        }
                        cg.out.writes("  store "); cg.out.writes(field_store_ty); cg.out.writes(" ");
                        if (emit_val_ref_str != null)
                        { cg.out.writes(emit_val_ref_str); cg.out.writei(v.id); }
                        else if (val_arg != null && val_arg.op == ssi_ir::IrOp.IR_CONST_STR)
                        { cgen_emit_str_const_record(cg, val_arg); }
                        else if (val_arg != null) { cg.emit_vref(val_arg); }
                        else { cg.out.writes("undef"); }
                        cg.out.writes(", ptr %st.gep.v"); cg.out.writei(v.id);
                        cg.out.writes("\n");
                    }
                }
                else
                {
                    // Pointer deref store: store val, ptr base.
                    // The store type MUST match the pointee type of `base`, not just
                    // the tymap type of `val`: a phi collecting i32/i64 across branches
                    // may have its tymap entry promoted to i64 by the phi-resolution pass,
                    // but if the pointer is *i32, the store must use i32.
                    // Recover the pointee type from base_arg's AST annotation (the lhs
                    // of the assignment carries a *T annotation; unwrap T and use it).
                    char* store_ty = val_ty_st;
                    {
                        char[TYMAP_ENTRY] ptbuf; ptbuf[0] = 0;
                        Node* bsrc = (base_arg != null) ? base_arg.src : null;
                        Node* bann = (bsrc != null) ? bsrc.type_annotation : null;
                        // For CALL results (*T return type): the call's src.type_annotation
                        // is the fn type, unwrap fn return → the pointed type.
                        if (bann != null && bann.kind == Nk.NODE_TYPE_FN && bann.child_count >= 2)
                        {
                            Node* ret = bann.children[1];
                            if (ret != null && ret.kind == Nk.NODE_EFFECT_ROW && ret.child_count >= 1)
                            { ret = ret.children[0]; }
                            bann = ret;
                        }
                        // Unwrap *T → T
                        if (bann != null && bann.kind == Nk.NODE_TYPE_PTR && bann.child_count >= 1)
                        {
                            type_to_llvm_buf(bann.children[0], &ptbuf[0], TYMAP_ENTRY, 0);
                        }
                        if (ptbuf[0] != 0 && !(ptbuf[0]=='v'&&ptbuf[1]=='o') && !(ptbuf[0]=='{'||ptbuf[0]=='['))
                        {
                            // Narrower pointee type: prefer it. If value needs coercion, emit it.
                            bool same_ty = true;
                            { char* a=&ptbuf[0]; char* b=val_ty_st;
                              while(*a!=0&&*a==*b){a++;b++;}
                              if(*a!=0||*b!=0) same_ty=false; }
                            if (!same_ty && val_ty_st[0]=='i' && ptbuf[0]=='i')
                            {
                                long vw=0;
                                long pw=0;
                                { char* vp=val_ty_st+1; while(*vp>='0'&&*vp<='9'){vw=vw*10+(long)(*vp-'0');vp++;} }
                                { char* pp=&ptbuf[0]+1; while(*pp>='0'&&*pp<='9'){pw=pw*10+(long)(*pp-'0');pp++;} }
                                if (pw > 0 && pw < vw && val_arg != null)
                                {
                                    // Tymap says value is wider than pointee. But for phi nodes,
                                    // the tymap may be wrong (phi i32 promoted to i64 in tymap).
                                    // Check: if the phi IS already the narrow type, store directly
                                    // rather than emitting a trunc of a value that is already narrow.
                                    // Detect phi narrow: the phi's definition uses ptbuf width.
                                    // We can't check the LLVM-emitted phi type here, but we CAN
                                    // check if the phi binder's source annotation says the narrow type.
                                    // Sigma-unwrap: a phi can be wrapped in a sigma filter node.
                                    ssi_ir::IrVal* val_unwrapped = val_arg;
                                    { int sd_phi=0;
                                      while (val_unwrapped != null && val_unwrapped.op == ssi_ir::IrOp.IR_SIGMA
                                             && val_unwrapped.arg_count >= 1 && val_unwrapped.args[0] != null && sd_phi < 8)
                                      { val_unwrapped = val_unwrapped.args[0]; sd_phi++; }
                                    }
                                    bool val_is_phi = (val_arg.op == ssi_ir::IrOp.IR_PHI
                                        || (val_unwrapped != null && val_unwrapped.op == ssi_ir::IrOp.IR_PHI));
                                    bool phi_already_narrow = false;
                                    if (val_is_phi)
                                    {
                                        // Check src annotation
                                        if (val_arg.src != null && val_arg.src.type_annotation != null)
                                        {
                                            char[TYMAP_ENTRY] phbuf2; phbuf2[0] = 0;
                                            type_to_llvm_buf(val_arg.src.type_annotation, &phbuf2[0], TYMAP_ENTRY, 0);
                                            long phw=0;
                                            { char* ph2=&phbuf2[0]+1; while(*ph2>='0'&&*ph2<='9'){phw=phw*10+(long)(*ph2-'0');ph2++;} }
                                            phi_already_narrow = (phw > 0 && phw == pw);
                                        }
                                        // Fallback: check any arg that is also narrow —
                                        // a phi over i32 values IS i32, the tymap is wrong.
                                        if (!phi_already_narrow && tm != null)
                                        {
                                            bool all_narrow = (val_arg.arg_count > 0);
                                            for (usz pai = 0; pai < val_arg.arg_count && all_narrow; pai++)
                                            {
                                                ssi_ir::IrVal* pa3 = val_arg.args[pai];
                                                char* pat3 = (pa3 != null) ? tm.get(pa3.id) : null;
                                                if (pat3 == null || pat3[0] != 'i') { all_narrow = false; break; }
                                                long paw=0;
                                                { char* pp3=pat3+1; while(*pp3>='0'&&*pp3<='9'){paw=paw*10+(long)(*pp3-'0');pp3++;} }
                                                if (paw != pw) { all_narrow = false; }
                                            }
                                            phi_already_narrow = all_narrow;
                                        }
                                    }
                                    if (!phi_already_narrow && !val_is_phi)
                                    {
                                        // Value is genuinely wider — emit trunc.
                                        cg.out.writes("  %st.pcoerce.v"); cg.out.writei(v.id);
                                        cg.out.writes(" = trunc "); cg.out.writes(val_ty_st);
                                        cg.out.writes(" "); cg.emit_vref(val_arg);
                                        cg.out.writes(" to "); cg.out.writes(&ptbuf[0]); cg.out.writes("\n");
                                        cg.out.writes("  store "); cg.out.writes(&ptbuf[0]);
                                        cg.out.writes(" %st.pcoerce.v"); cg.out.writei(v.id);
                                        cg.out.writes(", ptr ");
                                        if (base_arg != null) { cg.emit_vref(base_arg); } else { cg.out.writes("null"); }
                                        cg.out.writes("\n");
                                        return;
                                    }
                                    // IR_PHI or confirmed-narrow: the phi was emitted with the
                                    // narrow type by emit_phi; trusting ptbuf avoids an invalid
                                    // `trunc i64 %phi_i32` (the phi IS i32, not i64).
                                    // Fall through and store with ptbuf type.
                                }
                            }
                            store_ty = &ptbuf[0];
                        }
                    }
                    cg.out.writes("  store "); cg.out.writes(store_ty); cg.out.writes(" ");
                    if (val_arg != null && val_arg.op == ssi_ir::IrOp.IR_CONST_STR)
                    { cgen_emit_str_const_record(cg, val_arg); }
                    else if (val_arg != null) { cg.emit_vref(val_arg); }
                    else { cg.out.writes("undef"); }
                    cg.out.writes(", ptr ");
                    if (base_arg != null) { cg.emit_vref(base_arg); } else { cg.out.writes("null"); }
                    cg.out.writes("\n");
                }
                // IR_STORE has no result register — it's void
                return;
            }

        case ssi_ir::IrOp.IR_CAST:
            {
                ssi_ir::IrVal* src  = v.arg_count >= 1 ? v.args[0] : null;
                char* src_type_str = (tm != null && src != null) ? tm.get(src.id) : null;
                char* dst_type_str = (tm != null) ? tm.get(v.id) : null;
                if (src_type_str == null) src_type_str = (char*)"i64";
                if (dst_type_str == null) dst_type_str = (char*)"i64";

                // String literal cast: the underlying global is [N x i8]* which LLVM types as ptr.
                // Regardless of what the type map says (it may say "{ ptr, i64 }" from annotation),
                // we must emit ptrtoint or bitcast ptr — never bitcast a fat-struct type.
                if (src != null && src.op == ssi_ir::IrOp.IR_CONST_STR)
                {
                    cg.out.writes("  %v"); cg.out.writei(v.id); cg.out.writes(" = ");
                    bool dst_is_int_cast = (dst_type_str[0] == 'i');
                    bool dst_is_ptr_cast = (dst_type_str[0] == 'p');
                    if (dst_is_int_cast)
                    {
                        cg.out.writes("ptrtoint ptr ");
                        cg.emit_vref(src);
                        cg.out.writes(" to "); cg.out.writes(dst_type_str); cg.out.writes("\n");
                    }
                    else
                    {
                        // ptr cast or any other: just forward the pointer
                        cg.out.writes("bitcast ptr ");
                        cg.emit_vref(src);
                        cg.out.writes(" to ptr\n");
                    }
                    return;
                }
                bool src_is_ptr = (src_type_str[0] == 'p');
                bool dst_is_ptr = (dst_type_str[0] == 'p');
                bool src_fp = (src_type_str[0]=='f'||src_type_str[0]=='d');
                bool dst_fp = (dst_type_str[0]=='f'||dst_type_str[0]=='d');
                bool src_int = (src_type_str[0]=='i');
                bool dst_int = (dst_type_str[0]=='i');

                // transmute(e) — BIT-EXACT reinterpret, never a numeric
                // conversion. The lowering only ever requests same-width
                // moves (f32↔i32, f64↔i64, int-int); for int-int a width
                // mismatch still preserves the dst's low bits (zext/trunc).
                if (v.src != null && v.src.kind == Nk.NODE_EXPR_TRANSMUTE
                    && (src_int || src_fp) && (dst_int || dst_fp))
                {
                    int sw2 = 0; int dw2 = 0;
                    if (src_type_str[0]=='i')
                    { for (usz ci = 1; src_type_str[ci] >= '0' && src_type_str[ci] <= '9'; ci++) sw2 = sw2*10+(int)(src_type_str[ci]-'0'); }
                    else { sw2 = (src_type_str[0]=='f') ? 32 : 64; }
                    if (dst_type_str[0]=='i')
                    { for (usz ci = 1; dst_type_str[ci] >= '0' && dst_type_str[ci] <= '9'; ci++) dw2 = dw2*10+(int)(dst_type_str[ci]-'0'); }
                    else { dw2 = (dst_type_str[0]=='f') ? 32 : 64; }
                    if (sw2 == dw2)
                    {
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = bitcast "); cg.out.writes(src_type_str);
                        cg.out.writes(" "); cg.emit_vref(src);
                        cg.out.writes(" to "); cg.out.writes(dst_type_str); cg.out.writes("\n");
                        return;
                    }
                    if (src_int && dst_int)
                    {
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(sw2 < dw2 ? " = zext " : " = trunc ");
                        cg.out.writes(src_type_str); cg.out.writes(" ");
                        cg.emit_vref(src);
                        cg.out.writes(" to "); cg.out.writes(dst_type_str); cg.out.writes("\n");
                        return;
                    }
                    // Width-mismatched float↔int transmutes never arrive
                    // from the lowering; fall through to the general path.
                }

                // ptr → integer: ptrtoint (address cast, NOT a load)
                // Effect-perform result unboxing: __pride_perform returns the
                // resume value through the frame's ptr SLOT — the value's bits,
                // NOT a pointer to it. A ptr→float cast on a perform result
                // reinterprets the slot bits (ptrtoint + bitcast), and a narrow
                // integer result truncates back to the op's declared width —
                // never a dereference, and never a bare i64 that masks the
                // declared type.
                if (src_is_ptr && src != null && src.op == ssi_ir::IrOp.IR_EFFECT_OP)
                {
                    if (dst_fp)
                    {
                        bool narrow32 = (dst_type_str[0] == 'f');   // float (vs double)
                        cg.out.writes("  %eff.i."); cg.out.writei(v.id);
                        cg.out.writes(" = ptrtoint ptr "); cg.emit_vref(src);
                        cg.out.writes(" to i64\n");
                        if (narrow32)
                        {
                            cg.out.writes("  %eff.w."); cg.out.writei(v.id);
                            cg.out.writes(" = trunc i64 %eff.i."); cg.out.writei(v.id);
                            cg.out.writes(" to i32\n");
                            cg.out.writes("  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = bitcast i32 %eff.w."); cg.out.writei(v.id);
                            cg.out.writes(" to float\n");
                        }
                        else
                        {
                            cg.out.writes("  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = bitcast i64 %eff.i."); cg.out.writei(v.id);
                            cg.out.writes(" to double\n");
                        }
                        return;
                    }
                    if (dst_int)
                    {
                        int dw_eff = 0;
                        for (usz ci = 1; dst_type_str[ci] >= '0' && dst_type_str[ci] <= '9'; ci++)
                        { dw_eff = dw_eff * 10 + (int)(dst_type_str[ci] - '0'); }
                        cg.out.writes("  %eff.i."); cg.out.writei(v.id);
                        cg.out.writes(" = ptrtoint ptr "); cg.emit_vref(src);
                        cg.out.writes(" to i64\n");
                        if (dw_eff >= 64 || dw_eff == 0)
                        {
                            cg.out.writes("  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = add i64 %eff.i."); cg.out.writei(v.id);
                            cg.out.writes(", 0\n");
                        }
                        else
                        {
                            cg.out.writes("  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = trunc i64 %eff.i."); cg.out.writei(v.id);
                            cg.out.writes(" to "); cg.out.writes(dst_type_str); cg.out.writes("\n");
                        }
                        return;
                    }
                }
                // `p as i64` = the pointer value as integer, NOT *p.
                // The dereference `*p` is handled by IR_UN with TOKEN_STAR.
                if (src_is_ptr && dst_int)
                {
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = ptrtoint ptr "); cg.emit_vref(src);
                    cg.out.writes(" to "); cg.out.writes(dst_type_str); cg.out.writes("\n");
                    return;
                }
                // ptr → float: load (unusual but handle gracefully)
                if (src_is_ptr && dst_fp)
                {
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = load "); cg.out.writes(dst_type_str);
                    cg.out.writes(", ptr "); cg.emit_vref(src); cg.out.writes("\n");
                    return;
                }

                // Widening int → sext or zext (per SOURCE signedness — the
                // LLVM type text erased it; uN/bool must zero-extend) or
                // trunc, never bitcast across widths.
                if (src_int && dst_int)
                {
                    int sw = 0; int dw = 0;
                    for (usz ci = 1; src_type_str[ci] >= '0' && src_type_str[ci] <= '9'; ci++) sw = sw*10+(int)(src_type_str[ci]-'0');
                    for (usz ci = 1; dst_type_str[ci] >= '0' && dst_type_str[ci] <= '9'; ci++) dw = dw*10+(int)(dst_type_str[ci]-'0');
                    Node* cast_src_ann = (v.src != null && v.src.kind == Nk.NODE_EXPR_CAST
                                         && v.src.child_count >= 1
                                         && v.src.children[0] != null)
                                         ? v.src.children[0].type_annotation : null;
                    cg.out.writes("  %v"); cg.out.writei(v.id); cg.out.writes(" = ");
                    if (sw == dw) { cg.out.writes("bitcast "); }
                    else if (sw < dw)
                    { cg.out.writes(cg_ann_is_unsigned(cast_src_ann) ? "zext " : "sext "); }
                    else { cg.out.writes("trunc "); }
                    cg.out.writes(src_type_str); cg.out.writes(" "); cg.emit_vref(src);
                    cg.out.writes(" to "); cg.out.writes(dst_type_str); cg.out.writes("\n");
                    return;
                }

                // struct { ptr, i64 } → ptr: extract field 0 (the pointer part of a fat string)
                bool src_is_fat_str = (src_type_str[0] == '{'
                    && src != null && src.op == ssi_ir::IrOp.IR_CONST_STR);
                if (src_is_fat_str && dst_is_ptr)
                {
                    // String constant → ptr: use getelementptr on the underlying string global
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = getelementptr inbounds i8, ptr @.str.");
                    cg.out.writei(src != null ? src.id : 0);
                    cg.out.writes(", i64 0\n");
                    return;
                }
                // Same-type identity cast: just forward the source value (no opcode needed).
                bool same_ty = src_type_str != null && dst_type_str != null
                    && cstr_eq(src_type_str, dst_type_str);
                if (same_ty)
                {
                    if (src_fp)
                    {
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = fadd "); cg.out.writes(src_type_str);
                        cg.out.writes(" "); cg.emit_vref(src); cg.out.writes(", 0.0\n");
                    }
                    else if (src_is_ptr)
                    {
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = getelementptr inbounds i8, ptr "); cg.emit_vref(src);
                        cg.out.writes(", i64 0\n");
                    }
                    else
                    {
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = add "); cg.out.writes(src_type_str);
                        cg.out.writes(" "); cg.emit_vref(src); cg.out.writes(", 0\n");
                    }
                    return;
                }
                // General cast: emit prefix then opcode.
                cg.out.writes("  %v"); cg.out.writei(v.id); cg.out.writes(" = ");
                // Determine conversion opcode.
                // fp → fp: fpext (widening) or fptrunc (narrowing)
                bool fp_widen = false;
                if (src_fp && dst_fp)
                {
                    int sw = 64; int dw = 64;
                    if (src_type_str[0]=='f'&&src_type_str[1]=='l') { sw=32; } // float
                    else if (src_type_str[0]=='d') { sw=64; } // double
                    if (dst_type_str[0]=='f'&&dst_type_str[1]=='l') { dw=32; }
                    else if (dst_type_str[0]=='d') { dw=64; }
                    fp_widen = (dw > sw);
                }
                if (!src_is_ptr && dst_is_ptr && src_int) { cg.out.writes("inttoptr "); }
                else if (src_is_ptr && dst_int)           { cg.out.writes("ptrtoint "); }
                else if (src_fp && dst_int)               { cg.out.writes("fptosi "); }
                else if (src_int && dst_fp)               { cg.out.writes("sitofp "); }
                else if (src_fp && dst_fp && fp_widen)    { cg.out.writes("fpext "); }
                else if (src_fp && dst_fp)                { cg.out.writes("fptrunc "); }
                else if (src_is_ptr && dst_is_ptr)        { cg.out.writes("bitcast "); }
                else                                      { cg.out.writes("bitcast "); }
                cg.writes_ty(tm, src != null ? src.id : -1);
                cg.out.writes(" "); cg.emit_vref(src);
                cg.out.writes(" to "); cg.writes_ty(tm, v.id); cg.out.writes("\n");
            }

        case ssi_ir::IrOp.IR_TUPLE:
        case ssi_ir::IrOp.IR_ARRAY:
        case ssi_ir::IrOp.IR_STRUCT:
            {
                // If the aggregate type is ptr (tensor literal), emit as heap alloc + stores
                // BUT: if this is actually a struct literal (IR_STRUCT not IR_ARRAY/IR_TUPLE),
                // skip this path and use insertvalue below.
                char* agg_ty = (tm != null) ? tm.get(v.id) : null;
                bool is_struct_lit = (v.op == ssi_ir::IrOp.IR_STRUCT);
                // r56: a tuple value may be STAMPED with a scalar/array type
                // by annotation-driven typing (e.g. the fat-slice decay takes
                // the array-typed arg ident as its src).  The insertvalue
                // chain would then print that scalar as the record type and
                // emit `insertvalue i64 undef` — invalid IR.  When the
                // stamped type isn't the record shape, build `{ T0, T1 }`
                // from the component types instead.
                bool tuple_override = false;
                char[TYMAP_ENTRY] tovr;
                if (v.op == ssi_ir::IrOp.IR_TUPLE && v.arg_count > 0
                    && !is_struct_lit && agg_ty != null
                    && !(agg_ty[0] == '{' || agg_ty[0] == '%'))
                {
                    usz off = 0;
                    tovr[off++] = '{'; tovr[off++] = ' ';
                    for (usz ai = 0; ai < v.arg_count && off < TYMAP_ENTRY - 8; ai++)
                    {
                        if (ai > 0) { tovr[off++] = ','; tovr[off++] = ' '; }
                        char* ety = (v.args[ai] != null) ? tm.get(v.args[ai].id) : null;
                        if (ety == null || ety[0] == 0) ety = (char*)"i64";
                        // A register-held ARRAY can't be a record component:
                        // the fat-record contract stores its ADDRESS (data
                        // pointer).  Field loads like `r.vals` arrive here as
                        // `[N x T]` SSA values (sg1) — materialize a memory
                        // home below and type the component as ptr.
                        if (ety[0] == '[') { ety = (char*)"ptr"; }
                        for (usz ei = 0; ety[ei] != 0 && off < TYMAP_ENTRY - 4; ei++)
                        { tovr[off++] = ety[ei]; }
                    }
                    tovr[off++] = ' '; tovr[off++] = '}'; tovr[off] = 0;
                    agg_ty = &tovr[0];
                    tuple_override = true;
                    // The VALUE is a record now — restamp its type entry so
                    // downstream consumers (call marshalling, stores, further
                    // aggregates) see `{ T0, T1 }`, not the scalar stamp.
                    if (tm != null) { tm.set(v.id, &tovr[0]); }
                }
                // Tensor literal: the runtime wire format (compiler_rt.c §8)
                // is   PrideTensor { u64 rank, u64 dims[rank], double data[] }
                // with the helpers (matmul/elemwise) reading exactly that.
                // The legacy path allocated a bare count*8 double buffer —
                // no header — so __pride_matmul read the first ELEMENT as the
                // rank, and elementwise `+` never reached the helper at all.
                // Int elements also became `store double 1` (invalid IR).
                if (agg_ty != null && agg_ty[0] == 'p' && v.arg_count > 0 && !is_struct_lit
                    && v.src != null && v.src.kind == Nk.NODE_EXPR_TENSOR_LIT)
                {
                    long[4] tdims;
                    usz trank = tensor_lit_shape(v.src, &tdims[0], 4);
                    if (trank > 0)
                    {
                        long telems = 1;
                        for (usz ti = 0; ti < trank; ti++) telems *= tdims[ti];
                        long hdr_bytes = (long)(1 + trank) * 8;
                        // One buffer: header + data.
                        cg.out.writes("  %ten."); cg.out.writei(v.id);
                        cg.out.writes(" = call ptr @malloc(i64 ");
                        cg.out.writei((long)(hdr_bytes + telems * 8));
                        cg.out.writes(")\n");
                        cg.out.writes("  store i64 "); cg.out.writeu((ulong)trank);
                        cg.out.writes(", ptr %ten."); cg.out.writei(v.id);
                        cg.out.writes("\n");
                        for (usz di = 0; di < trank; di++)
                        {
                            cg.out.writes("  %td.gep."); cg.out.writei(v.id);
                            cg.out.writes("."); cg.out.writeu(di);
                            cg.out.writes(" = getelementptr inbounds i64, ptr %ten.");
                            cg.out.writei(v.id); cg.out.writes(", i64 ");
                            cg.out.writeu((ulong)(1 + di)); cg.out.writes("\n");
                            cg.out.writes("  store i64 "); cg.out.writei((long)tdims[di]);
                            cg.out.writes(", ptr %td.gep."); cg.out.writei(v.id);
                            cg.out.writes("."); cg.out.writeu(di); cg.out.writes("\n");
                        }
                        cg.out.writes("  %tdp."); cg.out.writei(v.id);
                        cg.out.writes(" = getelementptr inbounds i8, ptr %ten.");
                        cg.out.writei(v.id); cg.out.writes(", i64 ");
                        cg.out.writei((long)hdr_bytes); cg.out.writes("\n");
                        if (trank == 1)
                        {
                            // Leaf rank: convert each element to double.
                            for (usz ti = 0; ti < v.arg_count; ti++)
                            {
                                cg.out.writes("  %ten.gep."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writeu(ti);
                                cg.out.writes(" = getelementptr inbounds double, ptr %tdp.");
                                cg.out.writei(v.id); cg.out.writes(", i64 ");
                                cg.out.writeu(ti); cg.out.writes("\n");
                                char* ety = (tm != null && v.args[ti] != null)
                                            ? tm.get(v.args[ti].id) : null;
                                if (ety == null || ety[0] == 0) ety = "double";
                                if (ety[0] == 'f' && ety[1] == 'l')   // float
                                {
                                    cg.out.writes("  %ten.cv."); cg.out.writei(v.id);
                                    cg.out.writes("."); cg.out.writeu(ti);
                                    cg.out.writes(" = fpext float ");
                                    if (v.args[ti] != null) { cg.emit_vref(v.args[ti]); }
                                    else { cg.out.writes("0.0"); }
                                    cg.out.writes(" to double\n");
                                    cg.out.writes("  store double %ten.cv.");
                                    cg.out.writei(v.id); cg.out.writes(".");
                                    cg.out.writeu(ti);
                                }
                                else if (ety[0] == 'i')   // any integer
                                {
                                    cg.out.writes("  %ten.cv."); cg.out.writei(v.id);
                                    cg.out.writes("."); cg.out.writeu(ti);
                                    cg.out.writes(" = sitofp ");
                                    cg.out.writes(ety); cg.out.writes(" ");
                                    if (v.args[ti] != null) { cg.emit_vref(v.args[ti]); }
                                    else { cg.out.writes("0"); }
                                    cg.out.writes(" to double\n");
                                    cg.out.writes("  store double %ten.cv.");
                                    cg.out.writei(v.id); cg.out.writes(".");
                                    cg.out.writeu(ti);
                                }
                                else   // already double (or unknown: store as-is)
                                {
                                    cg.out.writes("  store double ");
                                    if (v.args[ti] != null) { cg.emit_vref(v.args[ti]); }
                                    else { cg.out.writes("0.0"); }
                                }
                                cg.out.writes(", ptr %ten.gep."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writeu(ti); cg.out.writes("\n");
                            }
                        }
                        else
                        {
                            // Higher ranks: each child is its own headered
                            // tensor; consolidate their data regions into this
                            // buffer with one memcpy per child.
                            long child_elems = telems / tdims[0];
                            long child_bytes = child_elems * 8;
                            long child_data_off = (long)trank * 8;   // (1+(rank-1))*8
                            for (usz ti = 0; ti < v.arg_count; ti++)
                            {
                                cg.out.writes("  %csrc."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writeu(ti);
                                cg.out.writes(" = getelementptr inbounds i8, ptr ");
                                if (v.args[ti] != null) { cg.emit_vref(v.args[ti]); }
                                else { cg.out.writes("null"); }
                                cg.out.writes(", i64 "); cg.out.writei((long)child_data_off);
                                cg.out.writes("\n");
                                cg.out.writes("  %cdst."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writeu(ti);
                                cg.out.writes(" = getelementptr inbounds i8, ptr %tdp.");
                                cg.out.writei(v.id); cg.out.writes(", i64 ");
                                cg.out.writei((long)(child_bytes * (long)ti));
                                cg.out.writes("\n");
                                cg.out.writes("  call void @llvm.memcpy.p0.p0.i64(ptr %cdst.");
                                cg.out.writei(v.id); cg.out.writes(".");
                                cg.out.writeu(ti); cg.out.writes(", ptr %csrc.");
                                cg.out.writei(v.id); cg.out.writes(".");
                                cg.out.writeu(ti);
                                cg.out.writes(", i64 "); cg.out.writei((long)child_bytes);
                                cg.out.writes(", i1 false)\n");
                            }
                        }
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = bitcast ptr %ten."); cg.out.writei(v.id);
                        cg.out.writes(" to ptr\n");
                        return;
                    }
                }
                // Tensor: allocate elem_count * 8 bytes (double), store each element
                if (agg_ty != null && agg_ty[0] == 'p' && v.arg_count > 0 && !is_struct_lit)
                {
                    cg.out.writes("  %ten."); cg.out.writei(v.id);
                    cg.out.writes(" = call ptr @malloc(i64 ");
                    cg.out.writei((long)(v.arg_count * 8));
                    cg.out.writes(")\n");
                    for (usz ti = 0; ti < v.arg_count; ti++)
                    {
                        cg.out.writes("  %ten.gep."); cg.out.writei(v.id);
                        cg.out.writes("."); cg.out.writeu(ti);
                        cg.out.writes(" = getelementptr inbounds double, ptr %ten.");
                        cg.out.writei(v.id); cg.out.writes(", i64 "); cg.out.writeu(ti);
                        cg.out.writes("\n");
                        // Determine what to store and emit the complete store instruction
                        if (v.args[ti] != null)
                        {
                            char* ety = (tm != null) ? tm.get(v.args[ti].id) : null;
                            if (ety != null && ety[0] == 'p')
                            {
                                // Nested tensor ptr: coerce to double first, then store
                                cg.out.writes("  %elem.dbl."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writeu(ti);
                                cg.out.writes(" = ptrtoint ptr ");
                                cg.emit_vref(v.args[ti]); cg.out.writes(" to i64\n");
                                cg.out.writes("  %elem.fp."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writeu(ti);
                                cg.out.writes(" = sitofp i64 %elem.dbl."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writeu(ti); cg.out.writes(" to double\n");
                                cg.out.writes("  store double %elem.fp."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writeu(ti);
                            }
                            else
                            {
                                cg.out.writes("  store double ");
                                cg.emit_vref(v.args[ti]);
                            }
                        }
                        else
                        {
                            cg.out.writes("  store double 0.0");
                        }
                        cg.out.writes(", ptr %ten.gep."); cg.out.writei(v.id);
                        cg.out.writes("."); cg.out.writeu(ti); cg.out.writes("\n");
                    }
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = bitcast ptr %ten."); cg.out.writei(v.id);
                    cg.out.writes(" to ptr\n");
                    return;
                }
                // IR_ARRAY literal: alloca [N x ElemType] + stores → ptr to first elem
                if (v.op == ssi_ir::IrOp.IR_ARRAY)
                {
                    char* ety_arr = (v.arg_count>=1&&v.args[0]!=null) ? resolve_ty(tm,v.args[0]) : (char*)"i64";
                    if (ety_arr==null||ety_arr[0]==0) ety_arr=(char*)"i64";
                    cg.out.writes("  %arr."); cg.out.writei(v.id);
                    cg.out.writes(" = alloca ["); cg.out.writeu(v.arg_count);
                    cg.out.writes(" x "); cg.out.writes(ety_arr); cg.out.writes("]\n");
                    for (usz ai=0;ai<v.arg_count;ai++)
                    {
                        cg.out.writes("  %ag."); cg.out.writei(v.id); cg.out.writes("."); cg.out.writeu(ai);
                        cg.out.writes(" = getelementptr inbounds ["); cg.out.writeu(v.arg_count);
                        cg.out.writes(" x "); cg.out.writes(ety_arr); cg.out.writes("], ptr %arr.");
                        cg.out.writei(v.id); cg.out.writes(", i32 0, i32 "); cg.out.writeu(ai); cg.out.writes("\n");
                        char* el_ty = (v.args[ai]!=null) ? resolve_ty(tm,v.args[ai]) : (char*)"i64";
                        bool el_c = false;
                        { usz el1=strlen(ety_arr); usz el2=strlen(el_ty);
                          if(el1!=el2){el_c=true;} else { for(usz ci=0;ci<el1;ci++) { if(ety_arr[ci]!=el_ty[ci]){el_c=true;break;} } } }
                        if (el_c && el_ty[0]=='i' && ety_arr[0]=='i')
                        {
                            long aw=0; long ew=0;
                            char* ap=el_ty+1;   while(*ap>='0'&&*ap<='9'){aw=aw*10+(long)(*ap-'0');ap++;}
                            char* ep=ety_arr+1; while(*ep>='0'&&*ep<='9'){ew=ew*10+(long)(*ep-'0');ep++;}
                            cg.out.writes("  %ac."); cg.out.writei(v.id); cg.out.writes("."); cg.out.writeu(ai);
                            if (aw > ew)                             { cg.out.writes(" = trunc "); }
                            else if (!is_signed_int_val(v.args[ai])) { cg.out.writes(" = zext "); }
                            else                                     { cg.out.writes(" = sext "); }
                            cg.out.writes(el_ty); cg.out.writes(" ");
                            if(v.args[ai]!=null){cg.emit_vref(v.args[ai]);}else{cg.out.writes("undef");}
                            cg.out.writes(" to "); cg.out.writes(ety_arr); cg.out.writes("\n");
                            cg.out.writes("  store "); cg.out.writes(ety_arr);
                            cg.out.writes(" %ac."); cg.out.writei(v.id); cg.out.writes("."); cg.out.writeu(ai);
                        }
                        else
                        {
                            cg.out.writes("  store "); cg.out.writes(ety_arr); cg.out.writes(" ");
                            if(v.args[ai]!=null){cg.emit_vref(v.args[ai]);}else{cg.out.writes("undef");}
                        }
                        cg.out.writes(", ptr %ag."); cg.out.writei(v.id); cg.out.writes("."); cg.out.writeu(ai); cg.out.writes("\n");
                    }
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = getelementptr inbounds ["); cg.out.writeu(v.arg_count);
                    cg.out.writes(" x "); cg.out.writes(ety_arr);
                    cg.out.writes("], ptr %arr."); cg.out.writei(v.id); cg.out.writes(", i32 0, i32 0\n");
                    // The result is a ptr — update TypeTable so IR_INDEX knows it's a ptr
                    if (tm != null) { tm.set(v.id, (char*)"ptr"); }
                    return;
                }
                // Untagged C-union literal (r34) and FIELD WRITE (r53): the
                // repr is ONE 64-bit reinterpretation cell (union_is_c_union;
                // v.md §9), not a record — insertvalue on i64 is invalid IR.
                // Convert the single field value to the FIELD's declared
                // payload type (fptrunc f64 literals into f32 members,
                // trunc/zext ints, sitofp int literals into float members),
                // then bit-pack it into the cell.  Typecheck enforces exactly
                // one provided field; a defensive extra arg just overwrites
                // (last wins).
                // ival==1 is the by-value rebuild of `u.f = x` (r53): pack
                // the RHS into %upack.vN, then MERGE it into the base cell —
                // the field's low footprint bytes are replaced, the rest of
                // the cell survives (C union member-store semantics).  The
                // generic struct-update insertvalue path would instead print
                // a phantom `{ f32, i32 }` record type against the i64 cell.
                {
                    Node* ulit_ann = v.src != null ? v.src.type_annotation : null;
                    Node* ulit_ud = ast::union_decl_of(ulit_ann);
                    if (is_struct_lit && ast::union_is_c_union(ulit_ud))
                    {
                        bool uupd = (v.ival == 1);
                        IrVal* ubase = (uupd && v.arg_count >= 1) ? v.args[0] : null;
                        IrVal* cell = null;
                        Node* cinit = null;
                        for (usz cai = (usz)(uupd ? 1 : 0); cai < v.arg_count; cai++)
                        { if (v.args[cai] != null) { cell = v.args[cai]; } }
                        for (usz cii = 1; v.src != null && cii < v.src.child_count; cii++)
                        { if (v.src.children[cii] != null
                              && v.src.children[cii].kind == Nk.NODE_FIELD_INIT)
                          { cinit = v.src.children[cii]; } }
                        // Payload type from the union decl, by field name.
                        char[TYMAP_ENTRY] pty_buf; pty_buf[0] = 0;
                        if (ulit_ud != null && cinit != null && cinit.child_count >= 1
                            && cinit.children[0] != null)
                        {
                            Node* payload_ty = null;
                            int uord = ast::union_variant_lookup(ulit_ud,
                                cinit.children[0].p.ident.name_ptr,
                                cinit.children[0].p.ident.name_len, &payload_ty);
                            if (uord >= 0 && payload_ty != null)
                            { type_to_llvm_buf(payload_ty, &pty_buf[0], TYMAP_ENTRY, 0); }
                        }
                        char* cty = (cell != null && tm != null) ? tm.get(cell.id) : null;
                        if (cell == null || cty == null || cty[0] == 0)
                        {
                            cg.out.writes("  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = add i64 0, 0\n");
                            return;
                        }
                        // Step 1: convert the value to the payload type.
                        bool pay_conv = false;
                        if (pty_buf[0] != 0 && !cstr_eq(cty, &pty_buf[0]))
                        {
                            char* py2 = &pty_buf[0];
                            if (py2[0] == 'f' && cty[0] == 'd')
                            {
                                cg.out.writes("  %upay.v"); cg.out.writei(v.id);
                                cg.out.writes(" = fptrunc double "); cg.emit_vref(cell);
                                cg.out.writes(" to float\n");
                                pay_conv = true;
                            }
                            else if (py2[0] == 'd' && cty[0] == 'f')
                            {
                                cg.out.writes("  %upay.v"); cg.out.writei(v.id);
                                cg.out.writes(" = fpext float "); cg.emit_vref(cell);
                                cg.out.writes(" to double\n");
                                pay_conv = true;
                            }
                            else if (py2[0] == 'f' && cty[0] == 'i')
                            {
                                cg.out.writes("  %upay.v"); cg.out.writei(v.id);
                                cg.out.writes(" = sitofp "); cg.out.writes(cty); cg.out.writes(" ");
                                cg.emit_vref(cell); cg.out.writes(" to float\n");
                                pay_conv = true;
                            }
                            else if (py2[0] == 'd' && cty[0] == 'i')
                            {
                                cg.out.writes("  %upay.v"); cg.out.writei(v.id);
                                cg.out.writes(" = sitofp "); cg.out.writes(cty); cg.out.writes(" ");
                                cg.emit_vref(cell); cg.out.writes(" to double\n");
                                pay_conv = true;
                            }
                            else if (py2[0] == 'i' && (cty[0] == 'f' || cty[0] == 'd'))
                            {
                                cg.out.writes("  %upay.v"); cg.out.writei(v.id);
                                cg.out.writes(" = fptosi "); cg.out.writes(cty); cg.out.writes(" ");
                                cg.emit_vref(cell); cg.out.writes(" to "); cg.out.writes(py2);
                                cg.out.writes("\n");
                                pay_conv = true;
                            }
                            else if (py2[0] == 'i' && cty[0] == 'i')
                            {
                                long cw = 0; long pw = 0;
                                for (usz wci = 1; cty[wci] >= '0' && cty[wci] <= '9'; wci++) cw = cw * 10 + (long)(cty[wci] - '0');
                                for (usz wpi = 1; py2[wpi] >= '0' && py2[wpi] <= '9'; wpi++) pw = pw * 10 + (long)(py2[wpi] - '0');
                                if (cw != pw)
                                {
                                    cg.out.writes("  %upay.v"); cg.out.writei(v.id);
                                    cg.out.writes(cw > pw ? " = trunc " : " = zext ");
                                    cg.out.writes(cty); cg.out.writes(" ");
                                    cg.emit_vref(cell); cg.out.writes(" to "); cg.out.writes(py2);
                                    cg.out.writes("\n");
                                    pay_conv = true;
                                }
                            }
                            if (pay_conv) { cty = &pty_buf[0]; }
                        }
                        // Reference to the (possibly converted) payload value.
                        // Step 2: bit-pack the payload-typed value into i64.
                        if (cty[0] == 'f')
                        {
                            cg.out.writes("  %ubit.v"); cg.out.writei(v.id);
                            cg.out.writes(" = bitcast float "); if (pay_conv) { cg.out.writes("%upay.v"); cg.out.writei(v.id); } else { cg.emit_vref(cell); }
                            cg.out.writes(" to i32\n");
                            cg.out.writes(uupd ? "  %upack.v" : "  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = zext i32 %ubit.v"); cg.out.writei(v.id);
                            cg.out.writes(" to i64\n");
                        }
                        else if (cty[0] == 'd')
                        {
                            cg.out.writes(uupd ? "  %upack.v" : "  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = bitcast double "); if (pay_conv) { cg.out.writes("%upay.v"); cg.out.writei(v.id); } else { cg.emit_vref(cell); }
                            cg.out.writes(" to i64\n");
                        }
                        else if (cty[0] == 'p')
                        {
                            cg.out.writes(uupd ? "  %upack.v" : "  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = ptrtoint ptr "); if (pay_conv) { cg.out.writes("%upay.v"); cg.out.writei(v.id); } else { cg.emit_vref(cell); }
                            cg.out.writes(" to i64\n");
                        }
                        else if (cty[0] == 'i' && cty[1] == '6' && cty[2] == '4' && cty[3] == 0)
                        {
                            cg.out.writes(uupd ? "  %upack.v" : "  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = add i64 "); if (pay_conv) { cg.out.writes("%upay.v"); cg.out.writei(v.id); } else { cg.emit_vref(cell); }
                            cg.out.writes(", 0\n");
                        }
                        else if (cty[0] == 'i')
                        {
                            cg.out.writes(uupd ? "  %upack.v" : "  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = zext "); cg.out.writes(cty); cg.out.writes(" ");
                            if (pay_conv) { cg.out.writes("%upay.v"); cg.out.writei(v.id); } else { cg.emit_vref(cell); } cg.out.writes(" to i64\n");
                        }
                        else
                        {
                            // Aggregate payloads cannot fit the cell — the
                            // typechecker rejects them (union_payload_is_scalar
                            // discipline); keep the value DEFINED regardless.
                            cg.out.writes(uupd ? "  %upack.v" : "  %v"); cg.out.writei(v.id);
                            cg.out.writes(" = add i64 0, 0\n");
                        }
                        if (uupd)
                        {
                            // Merge the packed footprint into the base cell:
                            // a full-width payload replaces the whole cell,
                            // otherwise (cell & keepmask) | packed.
                            long ubits = 64;
                            char* upty = (pty_buf[0] != 0) ? &pty_buf[0] : cty;
                            if (upty[0] == 'f' && upty[1] == 'l') { ubits = 32; }
                            else if (upty[0] == 'i')
                            {
                                long ub2 = 0;
                                for (usz uwi = 1; upty[uwi] >= '0' && upty[uwi] <= '9'; uwi++)
                                { ub2 = ub2 * 10 + (long)(upty[uwi] - '0'); }
                                if (ub2 > 0 && ub2 < 64) { ubits = ub2; }
                            }
                            if (ubits >= 64 || ubase == null)
                            {
                                cg.out.writes("  %v"); cg.out.writei(v.id);
                                cg.out.writes(" = add i64 %upack.v"); cg.out.writei(v.id);
                                cg.out.writes(", 0\n");
                            }
                            else
                            {
                                ulong ukm = ~(ulong)0 << (uint)ubits;
                                cg.out.writes("  %um.v"); cg.out.writei(v.id);
                                cg.out.writes(" = and i64 ");
                                cg.emit_vref(ubase);
                                cg.out.writes(", "); cg.out.writei((long)ukm); cg.out.writes("\n");
                                cg.out.writes("  %v"); cg.out.writei(v.id);
                                cg.out.writes(" = or i64 %um.v"); cg.out.writei(v.id);
                                cg.out.writes(", %upack.v"); cg.out.writei(v.id); cg.out.writes("\n");
                            }
                        }
                        return;
                    }
                }
                // r56: component-typed tuple rebuild — the stamped type isn't
                // a record, so skip every struct-body lookup and build the
                // aggregate purely from the argument types.
                if (tuple_override)
                {
                    for (usz ti2 = 0; ti2 < v.arg_count; ti2++)
                    {
                        // Register-held array component: give it a memory home
                        // and store its ADDRESS (fat-record contract).
                        char* raw_ety = (v.args[ti2] != null) ? tm.get(v.args[ti2].id) : null;
                        bool arr_home = (raw_ety != null && raw_ety[0] == '[');
                        if (arr_home)
                        {
                            cg.out.writes("  %mc."); cg.out.writei(v.id);
                            cg.out.writes("."); cg.out.writeu(ti2);
                            cg.out.writes(" = alloca "); cg.out.writes(raw_ety);
                            cg.out.writes("\n");
                            cg.out.writes("  store "); cg.out.writes(raw_ety);
                            cg.out.writes(" ");
                            if (v.args[ti2] != null) { cg.emit_vref(v.args[ti2]); }
                            else { cg.out.writes("undef"); }
                            cg.out.writes(", ptr %mc."); cg.out.writei(v.id);
                            cg.out.writes("."); cg.out.writeu(ti2); cg.out.writes("\n");
                        }
                        if (ti2 + 1 == v.arg_count)
                        { cg.out.writes("  %v"); cg.out.writei(v.id); }
                        else
                        { cg.out.writes("  %agg."); cg.out.writei(v.id);
                          cg.out.writes("."); cg.out.writeu(ti2); }
                        cg.out.writes(" = insertvalue ");
                        cg.out.writes(agg_ty);
                        if (ti2 == 0) { cg.out.writes(" undef, "); }
                        else
                        {
                            cg.out.writes(" %agg."); cg.out.writei(v.id);
                            cg.out.writes("."); cg.out.writeu(ti2 - 1);
                            cg.out.writes(", ");
                        }
                        char* e2ty = arr_home ? (char*)"ptr" : raw_ety;
                        if (e2ty == null || e2ty[0] == 0) e2ty = (char*)"i64";
                        cg.out.writes(e2ty);
                        cg.out.writes(" ");
                        if (arr_home)
                        {
                            cg.out.writes("%mc."); cg.out.writei(v.id);
                            cg.out.writes("."); cg.out.writeu(ti2);
                        }
                        else if (v.args[ti2] != null) { cg.emit_vref(v.args[ti2]); }
                        else { cg.out.writes("undef"); }
                        cg.out.writes(", "); cg.out.writeu(ti2); cg.out.writes("\n");
                    }
                    return;
                }
                // Build aggregate with insertvalue chain from undef
                // %agg.0 = insertvalue { T0, T1 } undef, T0 %v0, 0
                // %agg.1 = insertvalue { T0, T1 } %agg.0, T1 %v1, 1
                // %vN    = %agg.(count-1)
                // For IR_STRUCT: find the struct decl to get field types
                Node* struct_type_node = null;
                if (v.op == ssi_ir::IrOp.IR_STRUCT && v.src != null)
                {
                    Node* stn_name = v.src.children != null && v.src.child_count >= 1
                                     ? v.src.children[0] : null;
                    Node* stn_resolved = (stn_name != null) ? stn_name.resolved : null;
                    // For struct update: stn_resolved is a PAT_IDENT (value binding).
                    // Walk through it to its type_annotation to reach the struct decl.
                    if (stn_resolved != null
                        && (stn_resolved.kind == Nk.NODE_PATTERN_IDENT || stn_resolved.kind == Nk.NODE_IDENT)
                        && stn_resolved.type_annotation != null)
                    {
                        Node* pta = stn_resolved.type_annotation;
                        Node* pta_r = (pta.resolved != null) ? pta.resolved : pta;
                        if (pta_r.kind == Nk.NODE_DECL_TYPE && pta_r.child_count >= 1)
                        {
                            Node* tbb = pta_r.children[pta_r.child_count - 1];
                            if (tbb != null && tbb.kind == Nk.NODE_DECL_STRUCT) { pta_r = tbb; }
                        }
                        if (pta_r.kind == Nk.NODE_DECL_STRUCT) { struct_type_node = pta_r; }
                    }
                    // Unwrap DECL_TYPE alias (type Vec2 = struct ...) to get the struct body
                    if (stn_resolved != null && stn_resolved.kind == Nk.NODE_DECL_TYPE)
                    {
                        // Last child of DECL_TYPE is the struct body
                        Node* body_check = stn_resolved.child_count >= 1
                            ? stn_resolved.children[stn_resolved.child_count - 1] : null;
                        if (body_check != null && body_check.kind == Nk.NODE_DECL_STRUCT) { stn_resolved = body_check; }
                    }
                    if (stn_resolved != null && stn_resolved.kind == Nk.NODE_DECL_STRUCT) { struct_type_node = stn_resolved; }
                    // For struct update (v.ival==1): stn_name resolves to a value binding, not a type.
                    // Try looking up struct decl from the base value's type_annotation instead.
                    if (struct_type_node == null && v.ival == 1 && stn_name != null
                        && stn_name.type_annotation != null)
                    {
                        Node* ta2 = stn_name.type_annotation;
                        if (ta2.kind == Nk.NODE_TYPEVAR && ta2.resolved != null)
                        {
                            Node* tar2 = ta2.resolved;
                            if (tar2.kind == Nk.NODE_DECL_TYPE && tar2.child_count >= 1)
                            {
                                Node* tb2 = tar2.children[tar2.child_count - 1];
                                if (tb2 != null && tb2.kind == Nk.NODE_DECL_STRUCT) { tar2 = tb2; }
                            }
                            if (tar2.kind == Nk.NODE_DECL_STRUCT) { struct_type_node = tar2; }
                        }
                        else if (ta2.kind == Nk.NODE_DECL_STRUCT) { struct_type_node = ta2; }
                    }
                    // Generic-instantiation bases (r43): the chains above only
                    // know TYPEVAR/DECL_TYPE/DECL_STRUCT directly — route the
                    // residual cases (GENERIC_APP annotations on the base ident)
                    // through struct_body_of, which understands applications.
                    if (struct_type_node == null && stn_name != null)
                    { struct_type_node = struct_body_of(stn_name.type_annotation); }
                    // Also try: v.src itself has type_annotation pointing to the struct
                    if (struct_type_node == null && v.src.type_annotation != null)
                    {
                        Node* ta = v.src.type_annotation;
                        // Handle TYPEVAR, IDENT, or DECL_STRUCT directly
                        Node* ta_resolved = (ta.resolved != null) ? ta.resolved : ta;
                        if (ta_resolved.kind == Nk.NODE_DECL_TYPE && ta_resolved.child_count >= 1)
                        {
                            Node* tb = ta_resolved.children[ta_resolved.child_count - 1];
                            if (tb != null && tb.kind == Nk.NODE_DECL_STRUCT) { ta_resolved = tb; }
                        }
                        if (ta_resolved.kind == Nk.NODE_DECL_STRUCT) { struct_type_node = ta_resolved; }
                    }
                }

                // Pre-compute struct body block (used in coerce and insertvalue index loops)
                Node* struct_body_block = null;
                if (struct_type_node != null)
                {
                    for (usz ci0 = 0; ci0 < struct_type_node.child_count; ci0++)
                    {
                        Node* c0 = struct_type_node.children[ci0];
                        if (c0 != null && c0.kind == Nk.NODE_EXPR_BLOCK) { struct_body_block = c0; break; }
                    }
                }
                // Generic-struct instantiation (r33): the literal is stamped
                // with the app type (`Pair<i64, f64>`) — the decl's field
                // types name type parameters, which print as the boxed ptr
                // repr.  Substitute through the app for BOTH the element
                // coerce and the record type so a concrete literal builds a
                // concrete record ({ i64, double }, not { ptr, ptr }).
                Node* struct_app_ann = (v.src != null && v.src.type_annotation != null
                    && v.src.type_annotation.kind == Nk.NODE_TYPE_GENERIC_APP)
                    ? v.src.type_annotation : null;
                bool is_struct_update = (v.ival == 1);
                usz field_arg_start_pre = is_struct_update ? 1 : 0;

                for (usz i = 0; i < v.arg_count; i++)
                {
                    // Skip the base struct arg for struct updates
                    if (i < field_arg_start_pre) { continue; }
                    usz field_i_pre = i - field_arg_start_pre;

                    // Compute actual struct field index for this arg by NAME:
                    // both struct literals and struct updates carry FIELD_INIT
                    // children (possibly written out of declaration order) —
                    // insertvalue must target the declared slot, not the write
                    // position.  Only bare positional inits fall back to the
                    // write index.
                    int actual_field_idx = (int)field_i_pre;
                    if (struct_body_block != null && v.src != null)
                    {
                        usz fi_child_idx_pre = field_i_pre + 1;  // +1: name/base ident at src.children[0]
                        if (fi_child_idx_pre < v.src.child_count)
                        {
                            Node* fi_node_pre = v.src.children[fi_child_idx_pre];
                            if (fi_node_pre != null && fi_node_pre.kind == Nk.NODE_FIELD_INIT
                                && fi_node_pre.child_count >= 1)
                            {
                                char* fi_nm = fi_node_pre.children[0].p.ident.name_ptr;
                                usz   fi_nl = fi_node_pre.children[0].p.ident.name_len;
                                // r56: no struct decl (fat slice / Str record):
                                // map the well-known slot names directly.
                                if (is_struct_update && struct_body_block == null)
                                {
                                    if (fi_nl == 3 && fi_nm[0]=='l' && fi_nm[1]=='e' && fi_nm[2]=='n')
                                    { actual_field_idx = 1; }
                                    else if (fi_nl == 3 && fi_nm[0]=='c' && fi_nm[1]=='a' && fi_nm[2]=='p')
                                    { actual_field_idx = 2; }
                                }
                                usz fdi2 = 0;
                                for (usz ci_pre = 0; ci_pre < struct_body_block.child_count; ci_pre++)
                                {
                                    Node* fd_pre = struct_body_block.children[ci_pre];
                                    if (fd_pre == null || fd_pre.kind != Nk.NODE_FIELD_DECL || fd_pre.child_count < 1) continue;
                                    char* fn_pre = fd_pre.children[0].p.ident.name_ptr;
                                    usz   fl_pre = fd_pre.children[0].p.ident.name_len;
                                    if (fl_pre == fi_nl && fn_pre != null)
                                    {
                                        bool nm_pre = true;
                                        for (usz k = 0; k < fl_pre; k++)
                                        { if (fn_pre[k] != fi_nm[k]) { nm_pre = false; break; } }
                                        if (nm_pre) { actual_field_idx = (int)fdi2; break; }
                                    }
                                    fdi2++;
                                }
                            }
                        }
                    }

                    // First: determine if coercion is needed and emit the coerce instruction
                    // This must happen BEFORE writing any part of the insertvalue line.
                    bool need_coerce_elem = false;
                    bool field_coerced = false;
                    char[TYMAP_ENTRY] field_ty_buf;
                    field_ty_buf[0] = 0;
                    if (struct_body_block != null)
                    {
                        // Look up field type by actual_field_idx
                        usz fi_coerce = 0;
                        for (usz ci = 0; ci < struct_body_block.child_count; ci++)
                        {
                            Node* fd = struct_body_block.children[ci];
                            if (fd == null || fd.kind != Nk.NODE_FIELD_DECL) { continue; }
                            if ((int)fi_coerce == actual_field_idx && fd.child_count >= 2)
                            {
                                Node* cfd_ty = fd.children[1];
                                if (struct_app_ann != null)
                                { cfd_ty = ast::generic_payload_subst(struct_app_ann, cfd_ty); }
                                Node* prev_fapp = g_subst_app;
                                if (struct_app_ann != null) { g_subst_app = struct_app_ann; }
                                type_to_llvm_buf(cfd_ty, &field_ty_buf[0], TYMAP_ENTRY, 0);
                                g_subst_app = prev_fapp;
                                need_coerce_elem = (field_ty_buf[0] != 0);
                                break;
                            }
                            fi_coerce++;
                        }
                    }
                    // Pre-emit coerce instruction (must be on its own line before insertvalue)
                    if (need_coerce_elem && v.args[i] != null)
                    {
                        char* arg_ty2 = (tm != null) ? tm.get(v.args[i].id) : null;
                        bool arg_int2  = (arg_ty2 != null && arg_ty2[0] == 'i');
                        bool arg_fp2   = (arg_ty2 != null && (arg_ty2[0] == 'f' || arg_ty2[0] == 'd'));
                        bool fld_int2  = (field_ty_buf[0] == 'i');
                        bool fld_fp2   = (field_ty_buf[0] == 'f' || field_ty_buf[0] == 'd');
                        if (arg_int2 && fld_fp2)
                        {
                            // Integer value into a float field.
                            cg.out.writes("  %fcoerce."); cg.out.writei(v.id);
                            cg.out.writes("."); cg.out.writeu(i);
                            cg.out.writes(" = sitofp ");
                            cg.out.writes(arg_ty2); cg.out.writes(" "); cg.emit_vref(v.args[i]);
                            cg.out.writes(" to "); cg.out.writes(&field_ty_buf[0]); cg.out.writes("\n");
                            field_coerced = true;
                        }
                        else if (arg_fp2 && fld_fp2 && (arg_ty2[0] != field_ty_buf[0]))
                        {
                            // float ↔ double rank change.
                            cg.out.writes("  %fcoerce."); cg.out.writei(v.id);
                            cg.out.writes("."); cg.out.writeu(i);
                            cg.out.writes(arg_ty2[0] == 'd' ? " = fptrunc " : " = fpext ");
                            cg.out.writes(arg_ty2); cg.out.writes(" "); cg.emit_vref(v.args[i]);
                            cg.out.writes(" to "); cg.out.writes(&field_ty_buf[0]); cg.out.writes("\n");
                            field_coerced = true;
                        }
                        else if (arg_fp2 && fld_int2)
                        {
                            // Float value into an int field (C-style truncation).
                            cg.out.writes("  %fcoerce."); cg.out.writei(v.id);
                            cg.out.writes("."); cg.out.writeu(i);
                            cg.out.writes(" = fptosi ");
                            cg.out.writes(arg_ty2); cg.out.writes(" "); cg.emit_vref(v.args[i]);
                            cg.out.writes(" to "); cg.out.writes(&field_ty_buf[0]); cg.out.writes("\n");
                            field_coerced = true;
                        }
                        else if (field_ty_buf[0] == '['
                                 && arg_ty2 != null && arg_ty2[0] == 'p')
                        {
                            // Inline-array field ([N x T] data, not a pointer)
                            // fed by an array literal / array value, which
                            // IR_ARRAY lowers to an ALLOCA POINTER: load the
                            // whole array so the insertvalue holds the value.
                            cg.out.writes("  %fcoerce."); cg.out.writei(v.id);
                            cg.out.writes("."); cg.out.writeu(i);
                            cg.out.writes(" = load "); cg.out.writes(&field_ty_buf[0]);
                            cg.out.writes(", ptr "); cg.emit_vref(v.args[i]);
                            cg.out.writes("\n");
                            field_coerced = true;
                        }
                        if (field_coerced) { /* handled by the float/array paths above */ }
                        else if (arg_ty2 != null && arg_ty2[0] == 'i' && field_ty_buf[0] == 'i')
                        {
                            usz al2 = strlen(arg_ty2); usz fl2 = strlen(&field_ty_buf[0]);
                            bool tymatch2 = (al2 == fl2);
                            if (tymatch2) { for (usz ci = 0; ci < al2; ci++) if (arg_ty2[ci] != field_ty_buf[ci]) { tymatch2 = false; break; } }
                            if (!tymatch2)
                            {
                                int aw2 = 0; int fw2 = 0;
                                for (usz ci = 1; arg_ty2[ci] >= '0' && arg_ty2[ci] <= '9'; ci++) aw2 = aw2*10+(int)(arg_ty2[ci]-'0');
                                for (usz ci = 1; field_ty_buf[ci] >= '0' && field_ty_buf[ci] <= '9'; ci++) fw2 = fw2*10+(int)(field_ty_buf[ci]-'0');
                                cg.out.writes("  %fcoerce."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writeu(i);
                                cg.out.writes(" = ");
                                // i1 → wider: use zext (zero-extend bool to byte);
                                // likewise any unsigned source zero-extends (r40).
                                if (aw2 == 1 && fw2 > 1)              { cg.out.writes("zext "); }
                                else if (aw2 > fw2)                    { cg.out.writes("trunc "); }
                                else if (!is_signed_int_val(v.args[i])) { cg.out.writes("zext "); }
                                else                                   { cg.out.writes("sext "); }
                                cg.out.writes(arg_ty2); cg.out.writes(" "); cg.emit_vref(v.args[i]);
                                cg.out.writes(" to "); cg.out.writes(&field_ty_buf[0]); cg.out.writes("\n");
                                field_coerced = true;
                            }
                        }
                    }

                    // Now emit the complete insertvalue instruction on a single line.
                    // All index/coerce info is pre-computed above (actual_field_idx, field_i_pre).
                    if (i + 1 == v.arg_count) { cg.out.writes("  %v"); cg.out.writei(v.id); }
                    else { cg.out.writes("  %agg."); cg.out.writei(v.id); cg.out.writes("."); cg.out.writeu(field_i_pre); }
                    cg.out.writes(" = insertvalue ");
                    // Write struct type string "{ T0, T1, ... }" from body block
                    if (struct_body_block != null)
                    {
                        cg.out.writes("{ ");
                        bool first_f = true;
                        for (usz fi2 = 0; fi2 < struct_body_block.child_count; fi2++)
                        {
                            Node* fd2 = struct_body_block.children[fi2];
                            if (fd2 == null || fd2.kind != Nk.NODE_FIELD_DECL || fd2.child_count < 2) continue;
                            if (!first_f) cg.out.writes(", ");
                            first_f = false;
                            char[TYMAP_ENTRY] ftbuf2;
                            Node* rfd_ty = fd2.children[1];
                            if (struct_app_ann != null)
                            { rfd_ty = ast::generic_payload_subst(struct_app_ann, rfd_ty); }
                            Node* prev_rapp = g_subst_app;
                            if (struct_app_ann != null) { g_subst_app = struct_app_ann; }
                            type_to_llvm_buf(rfd_ty, &ftbuf2[0], TYMAP_ENTRY, 0);
                            g_subst_app = prev_rapp;
                            cg.out.writes(ftbuf2[0] != 0 ? &ftbuf2[0] : (char*)"i64");
                        }
                        cg.out.writes(" }");
                    }
                    else if (tuple_override) { cg.out.writes(agg_ty); }  // r56
                    else
                    {
                        // struct_body_block not found: try to get struct type from base val (arg[0])
                        // whose tymap type should be "{ i64, i64, ... }".
                        bool used_base_ty = false;
                        if (is_struct_update)
                        {
                            // Try tymap of base val first
                            if (v.arg_count >= 1 && v.args[0] != null && tm != null)
                            {
                                char* base_ty = tm.get(v.args[0].id);
                                if (base_ty != null && base_ty[0] == '{')
                                {
                                    cg.out.writes(base_ty);
                                    used_base_ty = true;
                                }
                            }
                            // Fall back to the function's return type if it's a struct
                            if (!used_base_ty && cg.cur_fn_ret_type[0] == '{')
                            {
                                cg.out.writes(&cg.cur_fn_ret_type[0]);
                                used_base_ty = true;
                            }
                        }
                        if (!used_base_ty) { cg.writes_ty(tm, v.id); }
                    }
                    cg.out.writes(" ");
                    // Base value: struct update uses arg[0] for first field, chain for subsequent.
                    // Struct literal uses undef for first field, chain for subsequent.
                    if (is_struct_update)
                    {
                        if (field_i_pre == 0) { cg.emit_vref(v.args[0]); }
                        else { cg.out.writes("%agg."); cg.out.writei(v.id); cg.out.writes("."); cg.out.writeu(field_i_pre - 1); }
                    }
                    else
                    {
                        if (i == 0) { cg.out.writes("undef"); }
                        else { cg.out.writes("%agg."); cg.out.writei(v.id); cg.out.writes("."); cg.out.writeu(i - 1); }
                    }
                    cg.out.writes(", ");
                    // Field type (from coerce lookup, or val's own type)
                    if (need_coerce_elem && field_ty_buf[0] != 0) { cg.out.writes(&field_ty_buf[0]); }
                    else { cg.writes_ty(tm, v.args[i] != null ? v.args[i].id : -1); }
                    cg.out.writes(" ");
                    // Field value
                    if (field_coerced)
                    { cg.out.writes("%fcoerce."); cg.out.writei(v.id); cg.out.writes("."); cg.out.writeu(i); }
                    else if (v.args[i] != null && v.args[i].op == ssi_ir::IrOp.IR_CONST_STR)
                    {
                        // A string literal's LLVM value is its fat record
                        // { ptr @.str.N, i64 LEN } — emit_vref renders the
                        // raw byte-global ref (a ptr), which is not a value
                        // of the record type (r50, `Rec { name: "abc" }`).
                        cgen_emit_str_const_record(cg, v.args[i]);
                    }
                    else { cg.emit_vref(v.args[i]); }
                    // Field index (struct-decl position, pre-computed)
                    cg.out.writes(", ");
                    cg.out.writei(actual_field_idx);
                    cg.out.writes("\n");
                }
                // result already named %vN by final insertvalue
            }

        case ssi_ir::IrOp.IR_ALLOC:
            {
                // Static alloc: v.ival > 0 holds the constant byte count.
                // Dynamic alloc: v.ival < 0, magnitude is elem_bytes, arg[0] is count.
                //   Emit: %sz = mul i64 %count, elem_bytes
                //         %vN = call ptr @malloc(i64 %sz)
                if ((v.ival & 0x8000000000000000u) != 0 && v.arg_count >= 1 && v.args[0] != null)
                {
                    ulong elem_bytes = v.ival & 0xFFFFFFFFu;
                    if (elem_bytes < 1) { elem_bytes = 1; }
                    // Emit the size as a temporary, then malloc.
                    // The size temp must be defined before the malloc call.
                    // We emit both in sequence in the current block.
                    cg.out.writes("  %sz."); cg.out.writei(v.id);
                    if (elem_bytes == 1)
                    {
                        // size = count * 1 = count — just copy the count value
                        cg.out.writes(" = add i64 0, ");
                        cg.emit_vref(v.args[0]);
                        cg.out.writes("\n");
                    }
                    else
                    {
                        cg.out.writes(" = mul i64 ");
                        cg.emit_vref(v.args[0]);
                        cg.out.writes(", ");
                        cg.out.writeu(elem_bytes);
                        cg.out.writes("\n");
                    }
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = call ptr @malloc(i64 %sz.");
                    cg.out.writei(v.id);
                    cg.out.writes(")\n");
                }
                else
                {
                    ulong alloc_bytes = (v.ival > 0 && v.ival < 0x7FFFFFFF) ? (ulong)v.ival : 8;
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = call ptr @malloc(i64 ");
                    cg.out.writeu(alloc_bytes);
                    cg.out.writes(")\n");
                }
            }

        case ssi_ir::IrOp.IR_FREE:
            {
                ssi_ir::IrVal* ptr_val = v.arg_count >= 1 ? v.args[0] : null;
                cg.out.writes("  call void @free(ptr ");
                cg.emit_vref(ptr_val);
                cg.out.writes(")\n");
                // IR_FREE is statement-like; result is unit
                // IR_FREE result is unit — emit as i64 0 (valid LLVM, not {} which is invalid)
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = add i64 0, 0\n");
            }

        case ssi_ir::IrOp.IR_GLOAD:
            {
                // r56d: load a mutable module-global from its real storage.
                Node* gdecl = v.src;
                usz gk = cg.gmut_id(gdecl);
                char[TYMAP_ENTRY] gty;
                char* gty2 = cg.gmut_type(gdecl, v.binder, &gty[0], TYMAP_ENTRY);
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = load "); cg.out.writes(gty2);
                cg.out.writes(", ptr @pride.gmut."); cg.out.writeu(gk);
                cg.out.writes("\n");
                if (tm != null) { tm.set(v.id, gty2); }
                return;
            }

        case ssi_ir::IrOp.IR_GSTORE:
            {
                // r56d: store a mutable module-global into its real storage.
                Node* gdecl = v.src;
                usz gk = cg.gmut_id(gdecl);
                char[TYMAP_ENTRY] gty3;
                char* gty4 = cg.gmut_type(gdecl, v.binder, &gty3[0], TYMAP_ENTRY);
                ssi_ir::IrVal* gval = v.arg_count >= 1 ? v.args[0] : null;
                char[64] gnm; gnm[0] = 0;
                bool gconv = false;
                if (gval != null)
                {
                    gconv = cg.gmut_coerce(tm, gval, gty4, (long)v.id, &gnm[0], 64);
                    cg.out.writes("  store "); cg.out.writes(gty4);
                    cg.out.writes(" ");
                    if (gconv) { cg.out.writes(&gnm[0]); }
                    else { cg.emit_vref(gval); }
                }
                else
                {
                    cg.out.writes("  store "); cg.out.writes(gty4);
                    cg.out.writes(" zeroinitializer");
                }
                cg.out.writes(", ptr @pride.gmut."); cg.out.writeu(gk);
                cg.out.writes("\n");
                return;
            }

        case ssi_ir::IrOp.IR_ATOMIC_RMW:
            {
                // atomicrmw <op> ptr %ptr, T %val seq_cst
                ssi_ir::IrVal* aptr = v.arg_count >= 1 ? v.args[0] : null;
                ssi_ir::IrVal* aval = v.arg_count >= 2 ? v.args[1] : null;
                char* aop_str = (char*)"add";
                long aop = (long)v.ival;
                if (aop == 1)      { aop_str = (char*)"sub"; }
                else if (aop == 2) { aop_str = (char*)"and"; }
                else if (aop == 3) { aop_str = (char*)"or";  }
                else if (aop == 4) { aop_str = (char*)"xor"; }
                else if (aop == 5) { aop_str = (char*)"xchg"; }
                char* aty = (tm != null && aval != null) ? tm.get(aval.id) : null;
                if (aty == null || aty[0] == 0) aty = (char*)"i64";
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = atomicrmw "); cg.out.writes(aop_str);
                cg.out.writes(" ptr "); cg.emit_vref(aptr);
                cg.out.writes(", "); cg.out.writes(aty);
                cg.out.writes(" "); cg.emit_vref(aval);
                cg.out.writes(" seq_cst\n");
            }

        case ssi_ir::IrOp.IR_CMPXCHG:
            {
                // cmpxchg ptr %ptr, T %expected, T %desired seq_cst seq_cst
                ssi_ir::IrVal* cptr = v.arg_count >= 1 ? v.args[0] : null;
                ssi_ir::IrVal* cexp = v.arg_count >= 2 ? v.args[1] : null;
                ssi_ir::IrVal* cnew = v.arg_count >= 3 ? v.args[2] : null;
                char* cty = (tm != null && cexp != null) ? tm.get(cexp.id) : null;
                if (cty == null || cty[0] == 0) cty = (char*)"i64";
                // Result is { T, i1 } — emit as pair
                cg.out.writes("  %cmpxchg.v"); cg.out.writei(v.id);
                cg.out.writes(" = cmpxchg ptr "); cg.emit_vref(cptr);
                cg.out.writes(", "); cg.out.writes(cty); cg.out.writes(" "); cg.emit_vref(cexp);
                cg.out.writes(", "); cg.out.writes(cty); cg.out.writes(" "); cg.emit_vref(cnew);
                cg.out.writes(" seq_cst seq_cst\n");
                // Extract the old value (field 0)
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = extractvalue { "); cg.out.writes(cty);
                cg.out.writes(", i1 } %cmpxchg.v"); cg.out.writei(v.id);
                cg.out.writes(", 0\n");
            }

        case ssi_ir::IrOp.IR_FENCE:
            {
                // fence seq_cst  (or other ordering)
                long ford = (long)v.ival;
                char* ford_str = (char*)"seq_cst";
                if (ford == 0)      { ford_str = (char*)"monotonic"; }
                else if (ford == 2) { ford_str = (char*)"acquire"; }
                else if (ford == 3) { ford_str = (char*)"release"; }
                else if (ford == 4) { ford_str = (char*)"acq_rel"; }
                cg.out.writes("  fence "); cg.out.writes(ford_str); cg.out.writes("\n");
                // fence has no result — emit unit placeholder
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = add i64 0, 0\n");
            }

        case ssi_ir::IrOp.IR_RANGE:
            {
                // IR_RANGE consumed by for-loop counter φ — emit as struct { lo, hi }.
                ssi_ir::IrVal* lo = v.arg_count >= 1 ? v.args[0] : null;
                ssi_ir::IrVal* hi = v.arg_count >= 2 ? v.args[1] : null;
                cg.out.writes("  %rng0.v"); cg.out.writei(v.id);
                cg.out.writes(" = insertvalue { i64, i64 } undef, i64 ");
                cg.emit_vref(lo);
                cg.out.writes(", 0\n");
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = insertvalue { i64, i64 } %rng0.v");
                cg.out.writei(v.id);
                cg.out.writes(", i64 ");
                cg.emit_vref(hi);
                cg.out.writes(", 1\n");
            }

        case ssi_ir::IrOp.IR_EFFECT_OP:
            {
                // perform Effect.op(args...) → call @__pride_perform(op_id, ...)
                ulong op_id = (v.binder != null) ? (ulong)v.binder.id : 0;
                // Pre-emit: widen sub-i64 integer args for variadic ABI
                for (usz i = 0; i < v.arg_count; i++)
                {
                    ssi_ir::IrVal* pa = v.args[i];
                    // Strip sigma to get real source and type
                    ssi_ir::IrVal* pa_src = pa;
                    int sd_pre = 0;
                    while (pa_src != null && pa_src.op == ssi_ir::IrOp.IR_SIGMA
                           && pa_src.arg_count >= 1 && pa_src.args[0] != null && sd_pre < 16)
                    { pa_src = pa_src.args[0]; sd_pre++; }
                    char* aty = (tm != null && pa_src != null) ? tm.get(pa_src.id) : null;
                    if (aty == null || aty[0] == 0) aty = (char*)"i64";
                    bool needs_widen = (aty[0]=='i' && aty[1]>='0' && aty[1]<='9'
                        && !(aty[1]=='6' && aty[2]=='4' && aty[3]==0));
                    bool is_bool = (aty[0]=='i' && aty[1]=='1' && aty[2]==0);
                    bool is_ptr_arg = (aty[0]=='p');
                    bool is_fp_arg = (aty[0]=='f' || aty[0]=='d');
                    if (needs_widen || is_bool || is_ptr_arg)
                    {
                        cg.out.writes("  %pw."); cg.out.writei(v.id); cg.out.writes(".");
                        cg.out.writeu(i); cg.out.writes(" = ");
                        if (is_bool)   { cg.out.writes("zext i1 "); }
                        else if (is_ptr_arg) { cg.out.writes("ptrtoint ptr "); }
                        else if (!is_signed_int_val(pa)) { cg.out.writes("zext "); cg.out.writes(aty); cg.out.writes(" "); }
                        else { cg.out.writes("sext "); cg.out.writes(aty); cg.out.writes(" "); }
                        cg.emit_vref(pa);
                        cg.out.writes(" to i64\n");
                    }
                    else if (is_fp_arg)
                    {
                        // Box float arg bits into the i64 variadic slot.
                        if (aty[0]=='f')
                        {
                            cg.out.writes("  %pwb."); cg.out.writei(v.id); cg.out.writes(".");
                            cg.out.writeu(i); cg.out.writes(" = bitcast float ");
                            cg.emit_vref(pa); cg.out.writes(" to i32\n");
                            cg.out.writes("  %pw."); cg.out.writei(v.id); cg.out.writes(".");
                            cg.out.writeu(i); cg.out.writes(" = zext i32 %pwb.");
                            cg.out.writei(v.id); cg.out.writes("."); cg.out.writeu(i);
                            cg.out.writes(" to i64\n");
                        }
                        else
                        {
                            cg.out.writes("  %pw."); cg.out.writei(v.id); cg.out.writes(".");
                            cg.out.writeu(i); cg.out.writes(" = bitcast double ");
                            cg.emit_vref(pa); cg.out.writes(" to i64\n");
                        }
                    }
                }
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = call ptr @__pride_perform(i64 ");
                cg.out.writeu(op_id);
                // Variadic ABI: the argument count comes first so the runtime
                // can va_arg exactly that many op arguments into the frame.
                cg.out.writes(", i64 ");
                cg.out.writeu((ulong)v.arg_count);
                for (usz i = 0; i < v.arg_count; i++)
                {
                    ssi_ir::IrVal* pa2 = v.args[i];
                    // Strip sigma chain to get real source value and type
                    ssi_ir::IrVal* pa2_src = pa2;
                    int sigma_d = 0;
                    while (pa2_src != null && pa2_src.op == ssi_ir::IrOp.IR_SIGMA
                           && pa2_src.arg_count >= 1 && pa2_src.args[0] != null && sigma_d < 16)
                    { pa2_src = pa2_src.args[0]; sigma_d++; }
                    char* aty2 = (tm != null && pa2_src != null) ? tm.get(pa2_src.id) : null;
                    if (aty2 == null || aty2[0] == 0) aty2 = (char*)"i64";
                    bool nw2 = (aty2[0]=='i' && aty2[1]>='0' && aty2[1]<='9'
                        && !(aty2[1]=='6' && aty2[2]=='4' && aty2[3]==0));
                    bool ib2 = (aty2[0]=='i' && aty2[1]=='1' && aty2[2]==0);
                    bool ptr2i2 = (aty2[0]=='p');  // ptr → i64 for variadic
                    bool fp2 = (aty2[0]=='f' || aty2[0]=='d');
                    cg.out.writes(", i64 ");
                    if (nw2 || ib2)
                    {
                        cg.out.writes("%pw."); cg.out.writei(v.id); cg.out.writes(".");
                        cg.out.writeu(i);
                    }
                    else if (ptr2i2 || fp2)
                    {
                        cg.out.writes("%pw."); cg.out.writei(v.id); cg.out.writes(".");
                        cg.out.writeu(i);
                    }
                    else { cg.emit_vref(pa2); }
                }
                cg.out.writes(")\n");
            }

        case ssi_ir::IrOp.IR_HANDLER:
            {
                // Handler frame setup. The TERM_SWITCH on this block's block
                // dispatches to arm blocks — those are the actual handlers.
                // @__pride_push_handler(frame_id, nops, op_id+1, ...) returns
                // 0 ("run the computation") or the performed op's id+1 —
                // matching the TERM_SWITCH case labels produced by
                // lower_handle.  The runtime needs the op list to find the
                // newest frame that actually handles a performed op.
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = call i64 @__pride_push_handler(i64 ");
                ulong frame_id = (v.binder != null) ? (ulong)v.binder.id : 0;
                cg.out.writeu(frame_id);
                // Collect the op dispatch tokens (same +1 tagging as the
                // switch case labels) from the handle node's arms.
                ulong[32] op_tags;
                usz nops = 0;
                Node* hnode = v.binder;
                if (hnode != null && hnode.kind == Nk.NODE_EFFECT_HANDLE)
                {
                    for (usz ai = 1; ai < hnode.child_count && nops < 32; ai++)
                    {
                        Node* arm = hnode.children[ai];
                        if (arm == null || arm.kind != Nk.NODE_HANDLER_ARM) { continue; }
                        Node* op_decl = ast::effect_op_decl_of_arm(arm);
                        op_tags[nops] = (op_decl != null) ? (ulong)op_decl.id + 1
                                                          : (ulong)nops + 1;
                        nops++;
                    }
                }
                cg.out.writes(", i64 ");
                cg.out.writeu((ulong)nops);
                for (usz oi = 0; oi < nops; oi++)
                {
                    cg.out.writes(", i64 ");
                    cg.out.writeu(op_tags[oi]);
                }
                cg.out.writes(")\n");
            }

        case ssi_ir::IrOp.IR_HANDLER_COMPLETE:
            {
                // Computation finished without diverging: pop the handler
                // frame.  (Arms that resume never reach this point; arms
                // that don't resume pop via IR_HANDLER_ARM instead.)
                cg.out.writes("  call void @__pride_complete()\n");
            }

        case ssi_ir::IrOp.IR_HANDLER_ARM:
            {
                // Arm body result; call pop to tear down the handler frame.
                ssi_ir::IrVal* body_res = v.arg_count >= 1 ? v.args[0] : null;
                cg.out.writes("  call void @__pride_pop_handler()\n");
                // The arm's result is just the body result — no new instruction needed.
                // We alias it:
                cg.out.writes("  %v"); cg.out.writei(v.id);
                {
                    char* src_ty = (tm != null && body_res != null) ? tm.get(body_res.id) : null;
                    char* dst_ty = (tm != null) ? tm.get(v.id) : null;
                    if (src_ty == null) src_ty = (char*)"i64";
                    if (dst_ty == null) dst_ty = (char*)"ptr";
                    bool src_i = (src_ty[0]=='i'); bool dst_p = (dst_ty[0]=='p');
                    cg.out.writes(" = ");
                    if (src_i && dst_p) { cg.out.writes("inttoptr "); }
                    else if (dst_p && src_ty[0]=='p') { cg.out.writes("bitcast "); }
                    else { cg.out.writes("bitcast "); }
                    cg.out.writes(src_ty); cg.out.writes(" ");
                    cg.emit_vref(body_res);
                    cg.out.writes(" to "); cg.out.writes(dst_ty); cg.out.writes("\n");
                }
            }

        case ssi_ir::IrOp.IR_RESUME:
            {
                // resume(v) → call @__pride_resume(ptr arg)
                // __pride_resume always takes ptr. Coerce the value:
                //   unit/void → null  (resume with no value)
                //   i64 val   → inttoptr i64 %val to ptr (then pass)
                //   ptr val   → pass directly
                ssi_ir::IrVal* rv = v.arg_count >= 1 ? v.args[0] : null;
                char* rv_ty = (tm != null && rv != null) ? tm.get(rv.id) : null;
                bool rv_is_unit = (rv == null
                    || rv.op == ssi_ir::IrOp.IR_CONST_UNIT
                    || (rv_ty != null && rv_ty[0] == 'v')  // void
                    || (rv_ty != null && rv_ty[0] == '{' && rv_ty[1] == ' ' && rv_ty[2] == '}')); // {}
                bool rv_is_ptr = (rv_ty != null && rv_ty[0] == 'p');
                bool rv_is_int = (rv_ty != null && rv_ty[0] == 'i');
                bool rv_is_fp  = (rv_ty != null && (rv_ty[0] == 'f' || rv_ty[0] == 'd'));
                // Pre-emit coerce if needed
                if (!rv_is_unit && rv_is_int && rv != null)
                {
                    cg.out.writes("  %resume.arg."); cg.out.writei(v.id);
                    cg.out.writes(" = inttoptr "); cg.out.writes(rv_ty);
                    cg.out.writes(" "); cg.emit_vref(rv); cg.out.writes(" to ptr\n");
                }
                if (!rv_is_unit && rv_is_fp && rv != null)
                {
                    // Box float bits into the ptr slot: bitcast to iN, widen to
                    // the slot width, inttoptr. The computation side mirrors
                    // this exactly (IR_CAST unboxing of perform results).
                    if (rv_ty[0] == 'f')
                    {
                        cg.out.writes("  %resume.bits."); cg.out.writei(v.id);
                        cg.out.writes(" = bitcast float "); cg.emit_vref(rv);
                        cg.out.writes(" to i32\n");
                        cg.out.writes("  %resume.w."); cg.out.writei(v.id);
                        cg.out.writes(" = zext i32 %resume.bits."); cg.out.writei(v.id);
                        cg.out.writes(" to i64\n");
                    }
                    else
                    {
                        cg.out.writes("  %resume.bits."); cg.out.writei(v.id);
                        cg.out.writes(" = bitcast double "); cg.emit_vref(rv);
                        cg.out.writes(" to i64\n");
                    }
                    cg.out.writes("  %resume.arg."); cg.out.writei(v.id);
                    cg.out.writes(" = inttoptr i64 %resume.");
                    if (rv_ty[0] == 'f') { cg.out.writes("w."); } else { cg.out.writes("bits."); }
                    cg.out.writei(v.id); cg.out.writes(" to ptr\n");
                }
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = call ptr @__pride_resume(ptr ");
                if (rv_is_unit)                     { cg.out.writes("null"); }
                else if (rv_is_int && rv != null)   { cg.out.writes("%resume.arg."); cg.out.writei(v.id); }
                else if (rv_is_fp && rv != null)    { cg.out.writes("%resume.arg."); cg.out.writei(v.id); }
                else                                { cg.emit_vref(rv); }
                cg.out.writes(")\n");
            }

        case ssi_ir::IrOp.IR_UNKNOWN:
            {
                // Two legitimate cases: asm and with-cleanup.
                if (v.src != null && v.src.kind == Nk.NODE_STMT_ASM)
                {
                    // Real LLVM inline assembly codegen.
                    // ASM node: children[0]=template, children[1..N]=AsmOperand groups
                    //   AsmOperand: children[0]=direction(out/in/clobber), rest=constraints+exprs
                    // LLVM asm syntax: call RetTy asm sideeffect "template","constraints"(inputs)
                    Node* asm_src = v.src;
                    // Collect template string
                    char* tmpl_ptr = null; usz tmpl_len = 0;
                    if (asm_src.child_count >= 1 && asm_src.children[0] != null
                        && asm_src.children[0].kind == Nk.NODE_LIT_STRING)
                    {
                        tmpl_ptr = asm_src.children[0].p.lit_str.ptr;
                        tmpl_len = asm_src.children[0].p.lit_str.len;
                    }

                    // Collect output/input/clobber groups
                    char*[32] out_con; usz[32] out_clen; IrVal*[32] out_vals;
                    char*[32] in_con;  usz[32] in_clen;  IrVal*[32] in_vals;
                    char*[32] clob;    usz[32] clob_len;
                    usz n_out = 0;
                    usz n_in = 0;
                    usz n_clob = 0;

                    usz arg_idx = 0;  // track v.args[] position
                    for (usz gi = 1; gi < asm_src.child_count; gi++)
                    {
                        Node* grp = asm_src.children[gi];
                        if (grp == null || grp.kind != Nk.NODE_ASM_OPERAND) continue;
                        if (grp.child_count == 0) continue;

                        // Parse direction
                        Node* dir_node = grp.children[0];
                        bool is_out = false;
                        bool is_clobber = false;
                        usz ci_start = 1;
                        if (dir_node != null && dir_node.kind == Nk.NODE_IDENT)
                        {
                            char* dn = dir_node.p.ident.name_ptr;
                            usz dl = dir_node.p.ident.name_len;
                            if (dl==3&&dn[0]=='o'&&dn[1]=='u'&&dn[2]=='t') { is_out=true; }
                            else if (dl==2&&dn[0]=='i'&&dn[1]=='n') { is_out=false; }
                            else if (dl>=3&&dn[0]=='c'&&dn[1]=='l'&&dn[2]=='o') { is_clobber=true; }
                            else { ci_start=0; }
                        } else { ci_start=0; }

                        char* cur_con = null;
                        usz cur_clen2 = 0;
                        for (usz ci2 = ci_start; ci2 < grp.child_count; ci2++)
                        {
                            Node* item = grp.children[ci2];
                            if (item == null) continue;
                            if (item.kind == Nk.NODE_LIT_STRING)
                            {
                                char* sp = item.p.lit_str.ptr; usz sl = item.p.lit_str.len;
                                if (sl>=2 && sp[0]=='"' && sp[sl-1]=='"') { sp++; sl-=2; }
                                if (is_clobber && n_clob<32) { clob[n_clob]=sp; clob_len[n_clob]=sl; n_clob++; }
                                else { cur_con=sp; cur_clen2=sl; }
                            }
                            else if (!is_clobber)
                            {
                                IrVal* av = (arg_idx < v.arg_count) ? v.args[arg_idx] : null;
                                if (is_out && n_out<32)
                                { out_con[n_out]=cur_con?(cur_con):(char*)"=r"; out_clen[n_out]=cur_con?cur_clen2:2; out_vals[n_out]=av; n_out++; arg_idx++; }
                                else if (!is_out && n_in<32)
                                { in_con[n_in]=cur_con?(cur_con):(char*)"r"; in_clen[n_in]=cur_con?cur_clen2:1; in_vals[n_in]=av; n_in++; arg_idx++; }
                                cur_con=null; cur_clen2=0;
                            }
                        }
                    }

                    // Build constraint string
                    char[512] cbuf; usz coff=0;
                    for (usz i=0;i<n_out&&coff<480;i++) { if(i)cbuf[coff++]=','; for(usz k=0;k<out_clen[i]&&coff<480;k++) cbuf[coff++]=out_con[i][k]; }
                    for (usz i=0;i<n_in&&coff<480;i++)  { if(n_out||i)cbuf[coff++]=','; for(usz k=0;k<in_clen[i]&&coff<480;k++) cbuf[coff++]=in_con[i][k]; }
                    for (usz i=0;i<n_clob&&coff<480;i++)
                    {
                        cbuf[coff++]=',';
                        char* cp=clob[i]; usz cl=clob_len[i];
                        if (cl>0&&cp[0]=='~') { for(usz k=0;k<cl&&coff<480;k++) cbuf[coff++]=cp[k]; }
                        else { cbuf[coff++]='~'; cbuf[coff++]='{'; for(usz k=0;k<cl&&coff<476;k++) cbuf[coff++]=cp[k]; cbuf[coff++]='}'; }
                    }
                    { char* tail=(char*)",~{dirflag},~{fpsr},~{flags}"; for(int tk=0;tail[tk]&&coff<509;tk++) cbuf[coff++]=tail[tk]; }
                    cbuf[coff]=0;

                    // Determine return type
                    char* asm_ret = (n_out>0) ? ((tm!=null)?tm.get(v.id):null) : null;
                    if (asm_ret==null||asm_ret[0]==0) asm_ret=(char*)"void";
                    bool void_asm = (asm_ret[0]=='v'&&asm_ret[1]=='o'&&asm_ret[2]=='i'&&asm_ret[3]=='d');

                    if (!void_asm) { cg.out.writes("  %v"); cg.out.writei(v.id); cg.out.writes(" = "); }
                    else           { cg.out.writes("  "); }
                    cg.out.writes("call "); cg.out.writes(asm_ret); cg.out.writes(" asm sideeffect \"");
                    if (tmpl_ptr!=null)
                    {
                        char* tp=tmpl_ptr; usz tl=tmpl_len;
                        if (tl>=2&&tp[0]=='"'&&tp[tl-1]=='"') { tp++; tl-=2; }
                        cg.out.write(tp, tl);
                    }
                    cg.out.writes("\", \""); cg.out.writes(&cbuf[0]); cg.out.writes("\"(");
                    for (usz i=0;i<n_in;i++)
                    {
                        if (i) cg.out.writes(", ");
                        char* at=(tm!=null&&in_vals[i]!=null)?tm.get(in_vals[i].id):null;
                        if (at==null||at[0]==0) at=(char*)"i64";
                        cg.out.writes(at); cg.out.writes(" "); cg.emit_vref(in_vals[i]);
                    }
                    cg.out.writes(")\n");
                    if (void_asm) { cg.out.writes("  %v"); cg.out.writei(v.id); cg.out.writes(" = add i64 0, 0\n"); }
                }
                else if (v.src != null && v.src.kind == Nk.NODE_EFFECT_WITH)
                {
                    // with-resource cleanup: call __pride_drop(resource_ptr)
                    ssi_ir::IrVal* res = v.arg_count >= 1 ? v.args[0] : null;
                    // __pride_drop expects ptr — inttoptr if resource is non-ptr typed
                    {
                        char* res_ty = (tm != null && res != null) ? tm.get(res.id) : null;
                        bool res_is_ptr = (res_ty == null || res_ty[0] == 'p');
                        if (!res_is_ptr && res_ty != null && res_ty[0] != 0)
                        {
                            cg.out.writes("  %drop.ptr.v"); cg.out.writei(v.id);
                            cg.out.writes(" = inttoptr "); cg.out.writes(res_ty);
                            cg.out.writes(" "); cg.emit_vref(res); cg.out.writes(" to ptr\n");
                            cg.out.writes("  call void @__pride_drop(ptr %drop.ptr.v");
                            cg.out.writei(v.id); cg.out.writes(")\n");
                        }
                        else
                        {
                            cg.out.writes("  call void @__pride_drop(ptr ");
                            cg.emit_vref(res); cg.out.writes(")\n");
                        }
                    }
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = add i64 0, 0\n");
                }
                else if (v.src != null && v.src.kind == Nk.NODE_EXPR_VOLATILE_LOAD)
                {
                    // volatile load: %v = load volatile T, ptr %arg0
                    ssi_ir::IrVal* ptr_v = v.arg_count >= 1 ? v.args[0] : null;
                    char* load_ty = (tm != null) ? tm.get(v.id) : null;
                    if (load_ty == null) load_ty = (char*)"i64";
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = load volatile "); cg.out.writes(load_ty);
                    cg.out.writes(", ptr "); cg.emit_vref(ptr_v); cg.out.writes("\n");
                }
                else if (v.src != null && v.src.kind == Nk.NODE_EXPR_FORMAT)
                {
                    // format!("template", arg0, arg1, ...) codegen
                    // The template string is v.src.children[0] (NODE_LIT_STRING).
                    // Args are v.args[0..arg_count-1] (already lowered).
                    // We emit:
                    //   %str = call ... @pride_str_new()     ; String
                    //   ... str_push_str / str_push_i64 calls for each segment/arg
                    // Then %v = the String value.

                    // Allocate a String on the stack (or use alloca).
                    // Simplified: use %str.N as a ptr to a stack-allocated String.
                    cg.out.writes("  %fmt.str."); cg.out.writei(v.id);
                    cg.out.writes(" = alloca { ptr, i64, i64 }\n");
                    cg.out.writes("  call void @pride_str_init(ptr %fmt.str.");
                    cg.out.writei(v.id); cg.out.writes(")\n");

                    // Parse template and emit push calls
                    Node* tmpl = v.src.child_count >= 1 ? v.src.children[0] : null;
                    char* tptr = null; usz tlen = 0;
                    if (tmpl != null && tmpl.kind == Nk.NODE_LIT_STRING)
                    {
                        tptr = tmpl.p.ident.name_ptr;
                        tlen = tmpl.p.ident.name_len;
                        // Strip surrounding double-quotes from string literal
                        if (tlen >= 2 && tptr[0] == '"')
                        { tptr++; tlen -= 2; }
                    }
                    usz arg_idx = 0;
                    usz seg_start = 0;
                    usz ti = 0;
                    while (ti <= tlen)
                    {
                        // Check for {} or {{ }}
                        bool is_slot = (ti < tlen && tptr != null &&
                                        tptr[ti] == '{' && ti+1 < tlen && tptr[ti+1] == '}');
                        bool is_esc  = (ti < tlen && tptr != null &&
                                        tptr[ti] == '{' && ti+1 < tlen && tptr[ti+1] == '{');
                        if (is_slot || is_esc || ti == tlen)
                        {
                            // Emit literal segment [seg_start, ti)
                            usz seg_len = ti - seg_start;
                            if (seg_len > 0 && tptr != null)
                            {
                                // Emit literal segment using stack alloca + store bytes + push
                                cg.out.writes("  %fmt.buf."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writei((long)ti);
                                cg.out.writes(" = alloca [");
                                cg.out.writei((long)(seg_len+1));
                                cg.out.writes(" x i8]\n");
                                // Store each byte into the alloca
                                for (usz bk = seg_start; bk < ti; bk++)
                                {
                                    char ch2 = tptr[bk];
                                    cg.out.writes("  %fmt.bp."); cg.out.writei(v.id);
                                    cg.out.writes("."); cg.out.writei((long)bk);
                                    cg.out.writes(" = getelementptr inbounds [");
                                    cg.out.writei((long)(seg_len+1));
                                    cg.out.writes(" x i8], ptr %fmt.buf.");
                                    cg.out.writei(v.id); cg.out.writes(".");
                                    cg.out.writei((long)ti);
                                    cg.out.writes(", i32 0, i32 ");
                                    cg.out.writei((long)(bk - seg_start));
                                    cg.out.writes("\n");
                                    cg.out.writes("  store i8 ");
                                    cg.out.writei((long)(int)ch2);
                                    cg.out.writes(", ptr %fmt.bp.");
                                    cg.out.writei(v.id); cg.out.writes(".");
                                    cg.out.writei((long)bk); cg.out.writes("\n");
                                }
                                // Null-terminate
                                cg.out.writes("  %fmt.nt."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writei((long)ti);
                                cg.out.writes(" = getelementptr inbounds [");
                                cg.out.writei((long)(seg_len+1));
                                cg.out.writes(" x i8], ptr %fmt.buf.");
                                cg.out.writei(v.id); cg.out.writes(".");
                                cg.out.writei((long)ti);
                                cg.out.writes(", i32 0, i32 ");
                                cg.out.writei((long)seg_len);
                                cg.out.writes("\n");
                                cg.out.writes("  store i8 0, ptr %fmt.nt.");
                                cg.out.writei(v.id); cg.out.writes(".");
                                cg.out.writei((long)ti); cg.out.writes("\n");
                                // Push the buffer to the String
                                cg.out.writes("  call void @pride_str_push_str(ptr %fmt.str.");
                                cg.out.writei(v.id);
                                cg.out.writes(", ptr %fmt.buf.");
                                cg.out.writei(v.id); cg.out.writes(".");
                                cg.out.writei((long)ti);
                                cg.out.writes(", i64 ");
                                cg.out.writei((long)seg_len);
                                cg.out.writes(")\n");
                            }
                            if (is_slot)
                            {
                                // Emit arg format push
                                if (arg_idx < v.arg_count && v.args[arg_idx] != null)
                                {
                                    char* aty = (tm != null) ? tm.get(v.args[arg_idx].id) : null;
                                    bool is_fp = (aty != null && (aty[0]=='f'||aty[0]=='d'));
                                    if (is_fp)
                                    {
                                        cg.out.writes("  call void @pride_str_push_f64(ptr %fmt.str.");
                                        cg.out.writei(v.id); cg.out.writes(", double ");
                                        cg.emit_vref(v.args[arg_idx]);
                                        cg.out.writes(")\n");
                                    }
                                    else
                                    {
                                        cg.out.writes("  call void @pride_str_push_i64(ptr %fmt.str.");
                                        cg.out.writei(v.id); cg.out.writes(", i64 ");
                                        cg.emit_vref(v.args[arg_idx]);
                                        cg.out.writes(")\n");
                                    }
                                    arg_idx++;
                                }
                                ti += 2;  // skip {}
                                seg_start = ti;
                                continue;
                            }
                            else if (is_esc)
                            {
                                ti += 2;  // skip {{
                                seg_start = ti - 1;  // keep one {
                            }
                            else { ti++; }  // end of string
                            continue;
                        }
                        ti++;
                    }
                    // Result is the String value loaded from the alloca
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = load { ptr, i64, i64 }, ptr %fmt.str.");
                    cg.out.writei(v.id); cg.out.writes("\n");
                }
                else if (v.src != null && v.src.kind == Nk.NODE_EXPR_VOLATILE_STORE)
                {
                    // volatile store: store volatile T %val, ptr %ptr
                    ssi_ir::IrVal* ptr_v2 = v.arg_count >= 1 ? v.args[0] : null;
                    ssi_ir::IrVal* val_v2 = v.arg_count >= 2 ? v.args[1] : null;
                    char* st_ty = (tm != null && val_v2 != null) ? tm.get(val_v2.id) : null;
                    if (st_ty == null) st_ty = (char*)"i64";
                    cg.out.writes("  store volatile "); cg.out.writes(st_ty);
                    cg.out.writes(" "); cg.emit_vref(val_v2);
                    cg.out.writes(", ptr "); cg.emit_vref(ptr_v2); cg.out.writes("\n");
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = add i64 0, 0  ; volatile store result\n");
                }
                else if (v.src != null && v.src.kind == Nk.NODE_EXPR_OFFSETOF)
                {
                    // offset_of(Type, field) — GEP null trick:
                    //   %gep = getelementptr %Type, ptr null, i32 0, i32 field_idx
                    //   %off = ptrtoint ptr %gep to i64
                    Node* ty_node  = v.src.child_count >= 1 ? v.src.children[0] : null;
                    Node* fld_node = v.src.child_count >= 2 ? v.src.children[1] : null;
                    // Determine field index from the field name node
                    int field_idx = 0;
                    if (ty_node != null && fld_node != null
                        && ty_node.kind == Nk.NODE_TYPEVAR && ty_node.resolved != null)
                    {
                        Node* struct_decl = ty_node.resolved;
                        if (struct_decl.kind == Nk.NODE_DECL_STRUCT)
                        {
                            // body is last child of DECL_STRUCT
                            Node* body = struct_decl.child_count >= 1
                                ? struct_decl.children[struct_decl.child_count - 1] : null;
                            if (body != null)
                            {
                                char* want_n = fld_node.p.ident.name_ptr;
                                usz   want_l = fld_node.p.ident.name_len;
                                for (usz fi = 0; fi < body.child_count; fi++)
                                {
                                    Node* fd = body.children[fi];
                                    if (fd == null) continue;
                                    // fd is a NODE_FIELD_DECL; its first child is the Ident.
                                    Node* fd_name = (fd.child_count >= 1) ? fd.children[0] : null;
                                    if (fd_name == null) continue;
                                    char* fn2 = fd_name.p.ident.name_ptr;
                                    usz   fl2 = fd_name.p.ident.name_len;
                                    if (fl2 == want_l && fn2 != null)
                                    {
                                        bool match = true;
                                        for (usz ci = 0; ci < fl2; ci++)
                                        { if (fn2[ci] != want_n[ci]) { match = false; break; } }
                                        if (match) { field_idx = (int)fi; break; }
                                    }
                                }
                            }
                        }
                    }
                    // Emit GEP + ptrtoint
                    char[256] ty_buf;
                    type_to_llvm_buf(ty_node, &ty_buf[0], 256, 0);
                    cg.out.writes("  %gep.off."); cg.out.writei(v.id);
                    cg.out.writes(" = getelementptr "); cg.out.writes(&ty_buf[0]);
                    cg.out.writes(", ptr null, i32 0, i32 ");
                    cg.out.writei(field_idx);
                    cg.out.writes("\n");
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = ptrtoint ptr %gep.off."); cg.out.writei(v.id);
                    cg.out.writes(" to i64\n");
                }
                else if (v.src != null && v.src.kind == Nk.NODE_EXPR_SYSCALL)
                {
                    // syscall(num, arg0..arg5) via inline asm on x86_64
                    // Use LLVM inline asm: call i64 asm "syscall", "={rax},{rax},{rdi},..."
                    // Every asm operand must be EXACTLY i64: narrower values
                    // (i32 fn results, bools, ...) and pointers (mmap returns,
                    // ...) are retyped through the shared coercion service —
                    // previously operands were printed as i64 regardless of
                    // their actual type, producing invalid IR.
                    usz scn = v.arg_count < 7 ? v.arg_count : 7;
                    for (usz sci = 0; sci < scn; sci++)
                    {
                        ssi_ir::IrVal* a = v.args[sci];
                        if (a == null || a.op == ssi_ir::IrOp.IR_CONST_INT) continue;
                        char* at = resolve_ty(tm, a);
                        if (at == null || at[0] == 0) continue;
                        char* opc = coerce_op_val(at, (char*)"i64", a);
                        if (opc == null) continue;
                        cg.out.writes("  %sysarg."); cg.out.writeu(sci);
                        cg.out.writes(".v"); cg.out.writei(v.id);
                        cg.out.writes(" = "); cg.out.writes(opc); cg.out.writes(" ");
                        cg.out.writes(at); cg.out.writes(" "); cg.emit_vref(a);
                        cg.out.writes(" to i64\n");
                    }
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = call i64 asm sideeffect \"syscall\",");
                    cg.out.writes("\"={rax},{rax},{rdi},{rsi},{rdx},{r10},{r8},{r9}\"");
                    cg.out.writes("(");
                    for (usz sci = 0; sci < v.arg_count && sci < 7; sci++)
                    {
                        if (sci > 0) cg.out.writes(", ");
                        // Reference the coerced operand when one was anchored
                        // above (same predicate — the two sites stay in lockstep).
                        bool did_coerce = false;
                        ssi_ir::IrVal* a = v.args[sci];
                        if (a != null && a.op != ssi_ir::IrOp.IR_CONST_INT)
                        {
                            char* at = resolve_ty(tm, a);
                            if (at != null && at[0] != 0
                                && coerce_op(at, (char*)"i64") != null) { did_coerce = true; }
                        }
                        cg.out.writes("i64 ");
                        if (did_coerce)
                        {
                            cg.out.writes("%sysarg."); cg.out.writeu(sci);
                            cg.out.writes(".v"); cg.out.writei(v.id);
                        }
                        else { cg.emit_vref(a); }
                    }
                    // Pad missing args with 0
                    for (usz sci2 = v.arg_count; sci2 < 7; sci2++)
                    { if (sci2 > 0) cg.out.writes(", "); cg.out.writes("i64 0"); }
                    cg.out.writes(") nounwind\n");
                }                else if (v.binder != null && v.binder.kind == Nk.NODE_EXPR_CLOSURE)
                {
                    // Closure fat pointer: { ptr thunk, ptr env }
                    int cid = (int)(v.ival & 0x7FFFFFFF);
                    usz ncap = v.arg_count;

                    // Env: array of ncap pointers (one per capture).
                    // Heap-allocated, NOT a stack alloca: a closure that
                    // escapes its creator's frame (make_adder returning
                    // | x -> x + n) must not read freed stack memory. The
                    // env is intentionally never freed — every copy of the
                    // fat value shares it, so freeing needs refcounting
                    // (future work); a bounded leak beats a dangling use.
                    // Freestanding builds have no libc → keep stack envs.
                    if (ncap > 0)
                    {
                        if (cg.freestanding)
                        {
                            cg.out.writes("  %cenv."); cg.out.writei(v.id);
                            cg.out.writes(" = alloca ["); cg.out.writei((long)ncap);
                            cg.out.writes(" x ptr]\n");
                        }
                        else
                        {
                            cg.out.writes("  %cenv."); cg.out.writei(v.id);
                            cg.out.writes(" = call ptr @malloc(i64 ptrtoint (ptr getelementptr ([");
                            cg.out.writei((long)ncap);
                            cg.out.writes(" x ptr], ptr null, i32 1) to i64))\n");
                        }

                        for (usz ci = 0; ci < ncap; ci++)
                        {
                            ssi_ir::IrVal* cap = v.args[ci];
                            char* cty = (tm != null && cap != null) ? tm.get(cap.id) : null;
                            if (cty == null) cty = (char*)"i64";

                            // GEP slot ci
                            cg.out.writes("  %cslot."); cg.out.writei(v.id);
                            cg.out.writes("."); cg.out.writei((long)ci);
                            cg.out.writes(" = getelementptr ["); cg.out.writei((long)ncap);
                            cg.out.writes(" x ptr], ptr %cenv."); cg.out.writei(v.id);
                            cg.out.writes(", i32 0, i32 "); cg.out.writei((long)ci);
                            cg.out.writes("\n");

                            // Store: aggregates cannot inttoptr — heap-box them
                            // (a stack box would dangle for escaped closures
                            // just like a stack env would). This case appeared
                            // the moment fn values became { ptr, ptr } (r9)
                            // and a fat value was itself captured (compose).
                            bool cap_is_ptr = (cty[0] == 'p');
                            bool cap_is_agg = (cty[0] == '{' || cty[0] == '%');
                            if (cap_is_agg && !cg.freestanding)
                            {
                                cg.out.writes("  %cbox."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writei((long)ci);
                                cg.out.writes(" = call ptr @malloc(i64 ptrtoint (ptr getelementptr (");
                                cg.out.writes(cty);
                                cg.out.writes(", ptr null, i32 1) to i64))\n");
                                cg.out.writes("  store "); cg.out.writes(cty);
                                cg.out.writes(" "); cg.emit_vref(cap);
                                cg.out.writes(", ptr %cbox."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writei((long)ci); cg.out.writes("\n");
                                cg.out.writes("  store ptr %cbox."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writei((long)ci);
                            }
                            else if (cap_is_agg)
                            {
                                // Freestanding (no malloc): stack-frame box.
                                cg.out.writes("  %cbox."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writei((long)ci);
                                cg.out.writes(" = alloca "); cg.out.writes(cty); cg.out.writes("\n");
                                cg.out.writes("  store "); cg.out.writes(cty);
                                cg.out.writes(" "); cg.emit_vref(cap);
                                cg.out.writes(", ptr %cbox."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writei((long)ci); cg.out.writes("\n");
                                cg.out.writes("  store ptr %cbox."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writei((long)ci);
                            }
                            else if (!cap_is_ptr)
                            {
                                cg.out.writes("  %citp."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writei((long)ci);
                                cg.out.writes(" = inttoptr "); cg.out.writes(cty);
                                cg.out.writes(" "); cg.emit_vref(cap);
                                cg.out.writes(" to ptr\n");
                                cg.out.writes("  store ptr %citp."); cg.out.writei(v.id);
                                cg.out.writes("."); cg.out.writei((long)ci);
                            }
                            else
                            {
                                cg.out.writes("  store ptr ");
                                cg.emit_vref(cap);
                            }
                            cg.out.writes(", ptr %cslot."); cg.out.writei(v.id);
                            cg.out.writes("."); cg.out.writei((long)ci); cg.out.writes("\n");
                        }

                        // Fat pointer: insertvalue { ptr, ptr } undef, @thunk, 0; insert env, 1
                        cg.out.writes("  %fat0."); cg.out.writei(v.id);
                        cg.out.writes(" = insertvalue { ptr, ptr } undef, ptr @__pride_closure_");
                        cg.out.writei((long)cid); cg.out.writes(", 0\n");
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = insertvalue { ptr, ptr } %fat0."); cg.out.writei(v.id);
                        cg.out.writes(", ptr %cenv."); cg.out.writei(v.id);
                        cg.out.writes(", 1\n");
                    }
                    else
                    {
                        // Zero-capture closure: still the uniform fat pair —
                        // { code ptr, env = null } — so every fn-typed value
                        // has exactly one ABI shape.
                        cg.out.writes("  %fat0."); cg.out.writei(v.id);
                        cg.out.writes(" = insertvalue { ptr, ptr } undef, ptr @__pride_closure_");
                        cg.out.writei((long)cid); cg.out.writes(", 0\n");
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = insertvalue { ptr, ptr } %fat0."); cg.out.writei(v.id);
                        cg.out.writes(", ptr null, 1\n");
                    }
                    return;
                }
                else if (v.binder != null && v.binder.kind == Nk.NODE_DECL_FN)
                {
                    // Function value used first-class (an argument, a let-bound
                    // fn, a returned fn — anything but a direct callee):
                    // the uniform fat pair { trampoline ptr, env = null }.
                    // The trampoline adapts the env-prefixed indirect ABI to
                    // this fn's real (thin) signature, and is emitted once
                    // per fn at the end of the module.
                    Node* fn_decl_ref = v.binder;
                    cg.register_trampoline(fn_decl_ref);
                    char* fn_name_r = null; usz fn_len_r = 0;
                    if (fn_decl_ref.child_count >= 1 && fn_decl_ref.children[0] != null)
                    {
                        fn_name_r = fn_decl_ref.children[0].p.ident.name_ptr;
                        fn_len_r  = fn_decl_ref.children[0].p.ident.name_len;
                    }
                    char* ext_r = null; usz ext_rl = 0;
                    bool has_ext_r = fn_get_extern_name(fn_decl_ref, &ext_r, &ext_rl);
                    cg.out.writes("  %fat0."); cg.out.writei(v.id);
                    cg.out.writes(" = insertvalue { ptr, ptr } undef, ptr @__pride_fptr_");
                    if (has_ext_r && ext_r != null && ext_rl > 0)
                    {
                        for (usz ei3 = 0; ei3 < ext_rl; ei3++) { cg.out.writec(ext_r[ei3]); }
                    }
                    else if (fn_name_r != null) { cg.out.write(fn_name_r, fn_len_r); }
                    cg.out.writes(", 0\n");
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = insertvalue { ptr, ptr } %fat0."); cg.out.writei(v.id);
                    cg.out.writes(", ptr null, 1\n");
                    return;
                }
                else
                {
                    // Unknown opaque value: emit `add TYPE 0, 0` using TypeTable type.
                    // TypeTable gets type from the IDENT's type_annotation (e.g. n:i32 → i32).
                    // This ensures the emitted instruction matches the table, so width coercion works.
                    char* unk_ty = (tm != null) ? tm.get(v.id) : null;
                    if (unk_ty == null || unk_ty[0] == 0 || (unk_ty[0]=='v'&&unk_ty[1]=='o'))
                    { unk_ty = (char*)"i64"; }
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = add "); cg.out.writes(unk_ty); cg.out.writes(" 0, 0\n");
                }
            }

        default:
            // Should never reach here — every IrOp is handled above.
            cg.out.writes("  ; unhandled IrOp for %v");
            cg.out.writei(v.id);
            cg.out.writes("\n");
    }
}


fn void CgenModule.emit_phi(CgenModule* cg, ssi_ir::IrVal* v, TypeTable* tm)
{
    if (v == null || v.op != ssi_ir::IrOp.IR_PHI) { return; }
    // Get phi result type
    char* phi_ty = (tm != null) ? tm.get(v.id) : null;
    if (phi_ty == null || phi_ty[0] == 0) phi_ty = (char*)"i64";
    // Skip void phis — no register to define
    if (phi_ty[0]=='v'&&phi_ty[1]=='o'&&phi_ty[2]=='i'&&phi_ty[3]=='d') return;
    // Skip ONLY `{}` (empty struct = unit) phis — not named struct/tuple phis
    bool phi_unit = (phi_ty[0]=='{' && phi_ty[1]==' ' && phi_ty[2]=='}');
    if (phi_unit)
    {
        // Emit a zero placeholder so any user of this phi gets i64 0
        cg.out.writes("  %v"); cg.out.writei(v.id);
        cg.out.writes(" = add i64 0, 0  ; unit phi placeholder\n");
        return;
    }
    cg.out.writes("  %v"); cg.out.writei(v.id);
    cg.out.writes(" = phi ");
    cg.out.writes(phi_ty);
    cg.out.writes(" ");
    for (usz i = 0; i < v.arg_count; i++)
    {
        if (i > 0) { cg.out.writes(", "); }
        cg.out.writes("[ ");
        // If phi arg is a sigma, substitute its source
        ssi_ir::IrVal* phi_arg = v.args[i];
        if (phi_arg != null && phi_arg.op == ssi_ir::IrOp.IR_SIGMA
            && phi_arg.arg_count >= 1 && phi_arg.args[0] != null)
        {
            phi_arg = phi_arg.args[0];
        }
        // Unit/const-unit args in a typed phi → undef
        if (phi_arg == null || phi_arg.op == ssi_ir::IrOp.IR_CONST_UNIT)
        {
            cg.out.writes("undef");
        }
        else
        {
            char* apty = (tm != null) ? tm.get(phi_arg.id) : null;
            // Emit undef for struct/void args ONLY when the phi itself is NOT struct-typed.
            // If phi_ty is also a struct, struct args are valid (struct-valued phi).
            bool phi_is_struct = (phi_ty != null && phi_ty[0] == '{');
            if (apty != null && (apty[0]=='{' || (apty[0]=='v'&&apty[1]=='o')) && !phi_is_struct)
            { cg.out.writes("undef"); }
            else if (phi_arg.op == ssi_ir::IrOp.IR_CONST_INT
                     && phi_ty != null && phi_ty[0] == 'i')
            {
                // Coerce integer constant to phi type width (prevents i64 lit in i32 phi).
                long pw = 0; char* pp = phi_ty + 1;
                while (*pp >= '0' && *pp <= '9') { pw = pw*10 + (long)(*pp - '0'); pp++; }
                if (pw >= 1 && pw <= 63)
                {
                    long mask = (1L << pw) - 1L;
                    cg.out.writei((long)phi_arg.ival & mask);
                }
                else { cg.out.writei((long)phi_arg.ival); }
            }
            else
            {
                // Non-constant incoming value: LLVM demands incoming type ==
                // φ type. A mismatched edge is retyped through a conversion
                // anchored at the end of the predecessor block (see
                // emit_phi_edge_coerces) — reference it here by name.
                char* eop = null; char* esrc = null; char* edst = null;
                if (phi_edge_coercion(tm, v, i, &eop, &esrc, &edst))
                {
                    cg.out.writes("%phi."); cg.out.writei(v.id);
                    cg.out.writes(".in."); cg.out.writeu((ulong)i);
                }
                else { cg.emit_vref(phi_arg); }
            }
        }
        cg.out.writes(", %B");
        cg.out.writei(v.pred[i]);
        cg.out.writes(" ]");
    }
    cg.out.writes("\n");
}

// Anchor emission for typed φ edges. Called for every block B immediately
// before B's terminator is printed: for each successor block's φ that takes
// an incoming value FROM B whose type differs from the φ type, print the
// conversion instruction here — the only position that dominates the edge
// regardless of the linear order in which blocks happen to be emitted.
// The φ itself references the result as `%phi.<id>.in.<slot>`; the predicate
// shared with emit_phi (phi_edge_coercion) keeps the two sides in lockstep.
fn void CgenModule.emit_phi_edge_coerces(CgenModule* cg, ssi_ir::IrBlock* b, TypeTable* tm)
{
    if (b == null || cg.ir == null) return;
    for (usz si = 0; si < b.succ_count; si++)
    {
        // Dedup repeated successor ids (a CBR to a single target lists it twice).
        bool seen = false;
        for (usz sj = 0; sj < si; sj++) { if (b.succ[sj] == b.succ[si]) { seen = true; break; } }
        if (seen) continue;
        ssi_ir::IrBlock* sb = cg.ir.blk(b.succ[si]);
        if (sb == null) continue;
        ssi_ir::IrVal* ph = sb.phi_head;
        while (ph != null)
        {
            if (ph.op == ssi_ir::IrOp.IR_PHI)
            {
                for (usz ai = 0; ai < ph.arg_count; ai++)
                {
                    if (ph.pred[ai] != b.id) continue;
                    char* eop = null; char* esrc = null; char* edst = null;
                    if (!phi_edge_coercion(tm, ph, ai, &eop, &esrc, &edst)) continue;
                    if (eop[0]=='i' && eop[1]=='n' && eop[2]=='s' && eop[3]=='v')
                    {
                        // Aggregate slot-0 fill: first bridge the scalar to the
                        // slot's element type (inttoptr / ptrtoint as needed),
                        // then `insertvalue AGG undef, ELEM x, 0`.
                        char* elems = (char*)malloc(STRUCT_SPLIT_CAP * STRUCT_SPLIT_LEN);
                        int ne = elems != null ? split_struct_ty(edst, elems, STRUCT_SPLIT_LEN) : 0;
                        char* slot0 = ne >= 1 ? elems : (char*)"ptr";
                        bool src_ptr = (esrc[0] == 'p');
                        bool dst_ptr = (slot0[0] == 'p');
                        bool bridged = false;
                        char* bopc = null;
                        if (src_ptr != dst_ptr)
                        { bopc = src_ptr ? (char*)"ptrtoint" : (char*)"inttoptr"; }
                        else if (!src_ptr)
                        {
                            // int→int of a different width: use the shared
                            // coercion service (trunc/sext) — plain reuse is
                            // only valid when the widths already agree.
                            bool same_w = true;
                            for (usz ci = 0; esrc[ci] != 0 && slot0[ci] != 0; ci++)
                            {
                                if (esrc[ci] != slot0[ci]) { same_w = false; break; }
                            }
                            if (!(same_w && strlen(esrc) == strlen(slot0)))
                            { bopc = coerce_op_val(esrc, slot0, ph.args[ai]); }
                        }
                        if (bopc != null)
                        {
                            cg.out.writes("  %phi."); cg.out.writei(ph.id);
                            cg.out.writes(".in."); cg.out.writeu((ulong)ai);
                            cg.out.writes(".iptr = "); cg.out.writes(bopc); cg.out.writes(" ");
                            cg.out.writes(esrc); cg.out.writes(" ");
                            cg.emit_vref(sigma_unwrap(ph.args[ai]));
                            cg.out.writes(" to "); cg.out.writes(slot0); cg.out.writes("\n");
                            bridged = true;
                        }
                        cg.out.writes("  %phi."); cg.out.writei(ph.id);
                        cg.out.writes(".in."); cg.out.writeu((ulong)ai);
                        cg.out.writes(" = insertvalue "); cg.out.writes(edst);
                        cg.out.writes(" undef, ");
                        cg.out.writes(slot0); cg.out.writes(" ");
                        if (bridged)
                        {
                            cg.out.writes("%phi."); cg.out.writei(ph.id);
                            cg.out.writes(".in."); cg.out.writeu((ulong)ai);
                            cg.out.writes(".iptr");
                        }
                        else { cg.emit_vref(sigma_unwrap(ph.args[ai])); }
                        cg.out.writes(", 0\n");
                        if (elems != null) free(elems);
                        continue;
                    }
                    cg.out.writes("  %phi."); cg.out.writei(ph.id);
                    cg.out.writes(".in."); cg.out.writeu((ulong)ai);
                    cg.out.writes(" = "); cg.out.writes(eop); cg.out.writes(" ");
                    cg.out.writes(esrc); cg.out.writes(" ");
                    cg.emit_vref(sigma_unwrap(ph.args[ai]));
                    cg.out.writes(" to "); cg.out.writes(edst); cg.out.writes("\n");
                }
            }
            ph = ph.next;
        }
    }
}


fn void CgenModule.emit_terminator(CgenModule* cg, ssi_ir::IrBlock* b, TypeTable* tm, char* fn_ret_type)
{
    if (b == null) { return; }
    // If the last instruction is a musttail call, ret was already emitted inline.
    // The entire block terminator (TERM_RET or TERM_BR to join) must be skipped.
    if (b.tail != null && b.tail.op == ssi_ir::IrOp.IR_CALL
        && ((b.tail.ival >> 63) & 1) != 0)
    {
        // Also remove this block from phi predecessors in successors
        // (handled at IR level via dead block elimination; here just skip output)
        return;
    }

    switch (b.term)
    {
        case ssi_ir::TermKind.TERM_RET:
            {
                if (b.ret_val == null
                    || b.ret_val.op == ssi_ir::IrOp.IR_CONST_UNIT)
                {
                    // If fn return type is non-void, emit `ret T undef`
                    char* fret = fn_ret_type;
                    if (fret != null && fret[0] != 0
                        && !(fret[0]=='v'&&fret[1]=='o'&&fret[2]=='i'&&fret[3]=='d'))
                    {
                        cg.out.writes("  ret "); cg.out.writes(fret);
                        cg.out.writes(" undef\n");
                    }
                    else { cg.out.writes("  ret void\n"); }
                }
                else if (fn_ret_type != null
                         && fn_ret_type[0]=='v'&&fn_ret_type[1]=='o'
                         && fn_ret_type[2]=='i'&&fn_ret_type[3]=='d'&&fn_ret_type[4]==0)
                {
                    // fn returns void — discard any value and ret void
                    cg.out.writes("  ret void\n");
                }
                else if (fn_ret_type != null && fn_ret_type[0] == '{')
                {
                    // fn returns a struct/tuple — emit ret directly if val is a struct/IR_STRUCT.
                    char* vty = resolve_ty(tm, b.ret_val);
                    bool ret_val_is_struct = (vty != null && vty[0] == '{');
                    // IR_STRUCT result (insertvalue chain) is always a struct aggregate —
                    // even if tymap doesn't carry the '{' type, treat it as returnable.
                    bool ret_val_is_ir_struct = (b.ret_val != null
                        && b.ret_val.op == ssi_ir::IrOp.IR_STRUCT);
                    // IR_CALL returning a struct: the callee declared return type tells us
                    // whether this call produces a struct value we can ret directly.
                    bool ret_val_is_call_struct = false;
                    if (b.ret_val != null && b.ret_val.op == ssi_ir::IrOp.IR_CALL
                        && b.ret_val.arg_count >= 1 && b.ret_val.args[0] != null)
                    {
                        ssi_ir::IrVal* callee_v2 = b.ret_val.args[0];
                        Node* fn_d2 = (callee_v2 != null) ? callee_v2.binder : null;
                        if (fn_d2 != null && fn_d2.kind == Nk.NODE_DECL_FN)
                        {
                            char[TYMAP_ENTRY] call_ret2;
                            call_ret2[0] = 0;
                            fn_param_llvm_type(fn_d2, -1, &call_ret2[0], TYMAP_ENTRY);
                            if (call_ret2[0] == '{')
                            { ret_val_is_call_struct = true; }
                        }
                    }
                    if (ret_val_is_struct || ret_val_is_ir_struct || ret_val_is_call_struct)
                    {
                        cg.out.writes("  ret "); cg.out.writes(fn_ret_type);
                        cg.out.writes(" ");
                        // String literal returned as a { ptr, i64 } slice: a global is
                        // a POINTER, not an aggregate — `ret { T } @.str.N` is invalid
                        // IR ("global variable reference must have pointer type").
                        // Materialise the constant aggregate directly.
                        if (b.ret_val != null && b.ret_val.op == ssi_ir::IrOp.IR_CONST_STR)
                        {
                            cg.out.writes("{ ptr @.str."); cg.out.writei(b.ret_val.id);
                            cg.out.writes(", i64 ");
                            cg.out.writeu((ulong)str_const_decoded_len(b.ret_val));
                            cg.out.writes(" }\n");
                        }
                        else { cg.emit_vref(b.ret_val); cg.out.writes("\n"); }
                    }
                    else
                    {
                        cg.out.writes("  ret "); cg.out.writes(fn_ret_type);
                        cg.out.writes(" undef\n");
                    }
                    return;
                }
                else
                {
                    // Value type: use resolve_ty to follow sigma chains (stripped by SASI)
                    char* val_ty = resolve_ty(tm, b.ret_val);
                    if (val_ty == null || val_ty[0] == 0) val_ty = (char*)"i64";
                    if (val_ty[0]=='v'&&val_ty[1]=='o') val_ty = (char*)"i64";
                    // For float IR_BIN, also check lhs arg type to avoid sitofp
                    if (b.ret_val.op == ssi_ir::IrOp.IR_BIN
                        && b.ret_val.arg_count >= 1 && b.ret_val.args[0] != null)
                    {
                        char* lhs_ty = resolve_ty(tm, b.ret_val.args[0]);
                        if (lhs_ty != null && (lhs_ty[0]=='f'||lhs_ty[0]=='d'))
                        { val_ty = lhs_ty; }
                    }

                    // Function return type
                    char* ret_ty = fn_ret_type;
                    if (ret_ty == null || ret_ty[0] == 0) ret_ty = val_ty;
                    if (ret_ty[0]=='v'&&ret_ty[1]=='o') ret_ty = val_ty;

                    // If ret_ty or val_ty is void/unit, just ret void
                    bool ret_is_void = (ret_ty[0]=='v'&&ret_ty[1]=='o'&&ret_ty[2]=='i'&&ret_ty[3]=='d');
                    bool val_is_void = (val_ty[0]=='v'&&val_ty[1]=='o'&&val_ty[2]=='i'&&val_ty[3]=='d');
                    if (ret_is_void || val_is_void)
                    {
                        cg.out.writes("  ret void\n");
                        return;
                    }
                    // Check if coercion is needed
                    bool need_coerce = false;
                    {
                        usz vl = strlen(val_ty); usz rl = strlen(ret_ty);
                        if (vl != rl) { need_coerce = true; }
                        else { for (usz ci = 0; ci < vl; ci++) { if (val_ty[ci] != ret_ty[ci]) { need_coerce = true; break; } } }
                    }
                    // Never coerce between identical float types (prevents spurious sitofp/fpext)
                    if (need_coerce)
                    {
                        bool vfp = (val_ty[0]=='f'||val_ty[0]=='d');
                        bool rfp = (ret_ty[0]=='f'||ret_ty[0]=='d');
                        // If both float, only coerce for fptrunc (narrowing), not for same type
                        if (vfp && rfp)
                        {
                            // Same float type → no coerce
                            usz vl2 = strlen(val_ty); usz rl2 = strlen(ret_ty);
                            if (vl2 == rl2)
                            {
                                bool same = true;
                                for (usz ci = 0; ci < vl2; ci++) if (val_ty[ci] != ret_ty[ci]) { same = false; break; }
                                if (same) { need_coerce = false; }
                            }
                        }
                    }

                    if (need_coerce)
                    {
                        // Aggregate→ptr: alloca/store/ret ptr (bitcast is invalid in LLVM 22)
                        // Handle BEFORE emitting the %coerce.ret prefix.
                        if (val_ty[0] == '{' && ret_ty[0] == 'p')
                        {
                            cg.out.writes("  %coerce.alloca.B"); cg.out.writei(b.id);
                            cg.out.writes(" = alloca "); cg.out.writes(val_ty); cg.out.writes("\n");
                            cg.out.writes("  store "); cg.out.writes(val_ty);
                            cg.out.writes(" "); cg.emit_vref(b.ret_val);
                            cg.out.writes(", ptr %coerce.alloca.B"); cg.out.writei(b.id); cg.out.writes("\n");
                            cg.out.writes("  ret ptr %coerce.alloca.B"); cg.out.writei(b.id); cg.out.writes("\n");
                            return;
                        }
                        // Aggregate→int pun: LLVM's bitcast rejects aggregates
                        // outright. Reinterpret through memory instead: store
                        // the value, reload its leading word, then narrow.
                        // (The honest-join-φ work means a fn-VALUE can now
                        // reach this point where the declared ret is i32 —
                        // before, the handle returned the dispatch token and
                        // a plain trunc papered over the whole mismatch.)
                        if (val_ty[0] == '{' && ret_ty[0] == 'i')
                        {
                            cg.out.writes("  %coerce.alloca.B"); cg.out.writei(b.id);
                            cg.out.writes(" = alloca "); cg.out.writes(val_ty); cg.out.writes("\n");
                            cg.out.writes("  store "); cg.out.writes(val_ty);
                            cg.out.writes(" "); cg.emit_vref(b.ret_val);
                            cg.out.writes(", ptr %coerce.alloca.B"); cg.out.writei(b.id); cg.out.writes("\n");
                            cg.out.writes("  %coerce.word.B"); cg.out.writei(b.id);
                            cg.out.writes(" = load i64, ptr %coerce.alloca.B"); cg.out.writei(b.id); cg.out.writes("\n");
                            cg.out.writes("  %coerce.ret.B"); cg.out.writei(b.id);
                            cg.out.writes(" = trunc i64 %coerce.word.B"); cg.out.writei(b.id);
                            cg.out.writes(" to "); cg.out.writes(ret_ty); cg.out.writes("\n");
                            cg.out.writes("  ret "); cg.out.writes(ret_ty);
                            cg.out.writes(" %coerce.ret.B"); cg.out.writei(b.id); cg.out.writes("\n");
                            return;
                        }
                        // Scalar coercion: the shared coercion service picks the
                        // opcode (trunc/sext/fptrunc/fpext/fptosi/sitofp/…) —
                        // including the correct fpext for float→double widening,
                        // which the old per-site code emitted as invalid fptrunc.
                        char* ret_opc = coerce_op_val(val_ty, ret_ty, b.ret_val);
                        if (ret_opc == null) ret_opc = (char*)"bitcast";
                        cg.out.writes("  %coerce.ret.B"); cg.out.writei(b.id); cg.out.writes(" = ");
                        cg.out.writes(ret_opc); cg.out.writes(" ");
                        cg.out.writes(val_ty);
                        cg.out.writes(" ");
                        cg.emit_vref(b.ret_val);
                        cg.out.writes(" to ");
                        cg.out.writes(ret_ty);
                        cg.out.writes("\n  ret ");
                        cg.out.writes(ret_ty);
                        cg.out.writes(" %coerce.ret.B"); cg.out.writei(b.id); cg.out.writes("\n");
                    }
                    else
                    {
                        cg.out.writes("  ret ");
                        cg.out.writes(ret_ty);
                        cg.out.writes(" ");
                        cg.emit_vref(b.ret_val);
                        cg.out.writes("\n");
                    }
                }
            }
        case ssi_ir::TermKind.TERM_BR:
            {
                if (b.succ_count >= 1)
                {
                    cg.out.writes("  br label %B");
                    cg.out.writei(b.succ[0]);
                    cg.out.writes("\n");
                }
                else { cg.out.writes("  br label %B0\n"); }
            }
        case ssi_ir::TermKind.TERM_CBR:
            {
                // Ensure condition is i1.
                // IR_BIN comparisons (icmp/fcmp) always produce i1 in LLVM.
                // Only non-comparison IR_BIN or params need coercion.
                char* cond_ty = (tm != null && b.cond != null)
                                ? tm.get(b.cond.id) : null;
                bool cond_is_i1 = (cond_ty != null && cond_ty[0]=='i'
                                   && cond_ty[1]=='1' && cond_ty[2]==0);
                // Also treat comparison ops as i1 (icmp/fcmp always produce i1)
                bool cond_is_cmp = false;
                if (b.cond != null && b.cond.op == ssi_ir::IrOp.IR_BIN)
                {
                    Tt cbop = b.cond.bop;
                    cond_is_cmp = (cbop == Tt.TOKEN_EQEQ || cbop == Tt.TOKEN_NEQ
                        || cbop == Tt.TOKEN_NEQ_UNI
                        || cbop == Tt.TOKEN_LT || cbop == Tt.TOKEN_LTEQ
                        || cbop == Tt.TOKEN_GT || cbop == Tt.TOKEN_GTEQ);
                }
                if (b.cond != null && !cond_is_i1 && !cond_is_cmp
                    && cond_ty != null && cond_ty[0]=='i')
                {
                    // Non-i1, non-comparison integer: emit icmp ne %cond, 0
                    cg.out.writes("  %cond.i1.B"); cg.out.writei(b.id);
                    cg.out.writes(" = icmp ne ");
                    cg.out.writes(cond_ty);
                    cg.out.writes(" ");
                    cg.emit_vref(b.cond);
                    cg.out.writes(", 0\n");
                    cg.out.writes("  br i1 %cond.i1.B"); cg.out.writei(b.id);
                }
                else
                {
                    cg.out.writes("  br i1 ");
                    cg.emit_vref(b.cond);
                }
                if (b.succ_count >= 2)
                {
                    cg.out.writes(", label %B");
                    cg.out.writei(b.succ[0]);
                    cg.out.writes(", label %B");
                    cg.out.writei(b.succ[1]);
                }
                else if (b.succ_count == 1)
                {
                    cg.out.writes(", label %B");
                    cg.out.writei(b.succ[0]);
                    cg.out.writes(", label %B");
                    cg.out.writei(b.succ[0]);
                }
                cg.out.writes("\n");
            }
        case ssi_ir::TermKind.TERM_SWITCH:
            {
                // switch i64 %cond, label %default [ i64 val, label %Bk ... ]
                cg.out.writes("  switch ");
                cg.writes_ty(tm, b.cond != null ? b.cond.id : -1);
                cg.out.writes(" ");
                cg.emit_vref(b.cond);
                cg.out.writes(", label %B");
                if (b.succ_count >= 1) { cg.out.writei(b.succ[0]); } else { cg.out.writes("0"); }
                cg.out.writes(" [\n");
                for (usz i = 1; i < b.succ_count; i++)
                {
                    if (b.case_has != null && b.case_has[i])
                    {
                        cg.out.writes("    ");
                        cg.writes_ty(tm, b.cond != null ? b.cond.id : -1);
                        cg.out.writes(" ");
                        cg.out.writeu(b.case_val[i]);
                        cg.out.writes(", label %B");
                        cg.out.writei(b.succ[i]);
                        cg.out.writes("\n");
                    }
                    // Arms without a case_val (effect handler arms) are reached
                    // via the effects runtime dispatch, not static switch values.
                }
                cg.out.writes("  ]\n");
            }
        case ssi_ir::TermKind.TERM_UNREACHABLE:
            cg.out.writes("  unreachable\n");
        default:
            cg.out.writes("  unreachable ; TERM_NONE\n");
    }
}

// Every symbol name @X for which emit_runtime_decls() below emits a
// `declare` line. This is the single source of truth `name_is_runtime_decl`
// consults — keep it in sync with emit_runtime_decls() (both are covered by
// the same construction: this list was extracted directly from that
// function's `declare ... @NAME(...)` lines).
//
// IMPORTANT: this used to be a hand-rolled set of partial byte-position
// checks (e.g. `len==6 && name[0]=='c' && name[5]=='t'`), which is exactly
// the bug class that caused a real parser-level collision elsewhere in this
// codebase (see parser.c3's compile-time-macro name detection) — a partial
// check silently accepts any other same-length string sharing just the
// tested byte positions. It was also independently WRONG for `printf` and
// `putchar` specifically: neither is actually declared anywhere in
// emit_runtime_decls(), so the old code caused any `#[extern("printf")]` or
// `#[extern("putchar")]` function to be silently DROPPED (no `declare` line
// emitted at all — `emit_function` returns early exactly as if the symbol
// were already declared), which would fail at link time with an undefined
// symbol. Rebuilt here as an exact, exhaustive, easy-to-audit table.
const char*[*] RUNTIME_DECL_NAMES = {
    // Pride effects runtime
    "__pride_perform", "__pride_push_handler", "__pride_pop_handler",
    "__pride_resume", "__pride_drop", "__pride_panic", "__pride_get_arm_arg",
    "__pride_complete",
    "__pride_fiber_spawn", "__pride_fiber_yield", "__pride_fiber_resume",
    "__pride_prompt_install", "__pride_prompt_unwind", "__pride_is_in_scope",
    "__pride_scoped_yield_in", "__pride_scoped_yield_out", "__pride_split_cont",
    "__pride_fuse_cont",
    "__pride_dynamic_wind_push", "__pride_dynamic_wind_pop",
    "__pride_dynamic_wind_enter", "__pride_dynamic_wind_exit",
    "__pride_local_bind", "__pride_local_get",
    // Tensor runtime (`@` matmul, elemwise ops, vector dot)
    "__pride_matmul", "__pride_tensor_elemwise", "__pride_vecdot",
    // Str runtime helpers
    "pride_str_init", "pride_str_push_str", "pride_str_push_i64", "pride_str_push_f64",
    "pride_str_eq",
    // libc: memory / string / process
    "malloc", "free", "realloc", "calloc", "memcpy", "memmove", "memset", "memcmp",
    "strdup", "strndup", "strlen", "strcmp", "strncmp", "getenv", "putenv", "_exit",
    // libc: I/O / mmap / syscalls
    "write", "open", "close", "read", "mmap", "munmap", "mprotect", "madvise", "syscall",
    // libc: pthreads
    "pthread_create", "pthread_join", "pthread_mutex_lock", "pthread_mutex_unlock",
    "pthread_mutex_init", "pthread_mutex_destroy", "pthread_rwlock_rdlock",
    "pthread_rwlock_wrlock", "pthread_rwlock_unlock", "pthread_cond_wait",
    "pthread_cond_signal", "pthread_cond_broadcast",
    // libc: time / networking / random
    "clock_gettime", "nanosleep", "getaddrinfo", "freeaddrinfo", "getrandom",
    // libm
    "sin", "cos", "tan", "asin", "acos", "atan", "atan2", "sinh", "cosh", "tanh",
    "exp", "exp2", "log", "log2", "log10", "pow", "sqrt", "cbrt", "hypot", "fabs",
    "floor", "ceil", "round", "trunc", "fmod", "fma", "copysign",
    "sinf", "cosf", "sqrtf", "expf", "logf", "powf", "fabsf", "floorf", "ceilf",
    "roundf", "fmaf",
    null   // sentinel
};

// Scans a fn decl's attribute list for #[extern("name")] and returns the name ptr+len.
// Returns false if no extern attribute found.
// Returns true if the given name is already declared in the hardcoded runtime decl section.
// Prevents duplicate `declare` lines for the exact symbols emit_runtime_decls() emits
// (libc/pthread/math/Pride-runtime functions) — see RUNTIME_DECL_NAMES above.
fn bool name_is_runtime_decl(char* name, usz len)
{
    if (name == null || len == 0) { return false; }
    for (usz i = 0; RUNTIME_DECL_NAMES[i] != null; i++)
    {
        if (span_is(name, len, (char*)RUNTIME_DECL_NAMES[i])) return true;
    }
    return false;
}

fn bool fn_get_extern_name(Node* decl, char** name_out, usz* len_out)
{
    if (decl == null) { return false; }
    for (usz ai = 0; ai < decl.child_count; ai++)
    {
        Node* al = decl.children[ai];
        if (al == null || al.kind != Nk.NODE_ATTRIBUTE_LIST) { continue; }
        for (usz aj = 0; aj < al.child_count; aj++)
        {
            Node* attr = al.children[aj];
            if (attr == null || attr.child_count < 1) { continue; }
            Node* aname = attr.children[0];
            if (aname == null) { continue; }
            char* nm = aname.p.ident.name_ptr;
            usz   nl = aname.p.ident.name_len;
            // Match "extern" (6 chars)
            if (nl == 6 && nm != null && nm[0]=='e'&&nm[1]=='x'&&nm[2]=='t'&&nm[3]=='e'&&nm[4]=='r'&&nm[5]=='n')
            {
                // The extern name is in the second attribute child (the string argument)
                if (attr.child_count >= 2 && attr.children[1] != null)
                {
                    Node* arg = attr.children[1];
                    // arg is a LitString; its p.lit_str.ptr/len holds the name
                    char* astr = arg.p.lit_str.ptr;
                    usz   alen = arg.p.lit_str.len;
                    // Strip surrounding quotes if present
                    if (alen >= 2 && astr != null && astr[0] == '"')
                    {
                        astr = astr + 1;
                        alen = alen - 2;
                    }
                    if (astr != null && alen > 0) { *name_out = astr; *len_out = alen; return true; }
                }
                // No argument — attribute is just #[extern] without a name: use Pride fn name
                return false;
            }
        }
    }
    return false;
}

fn void CgenModule.emit_function(CgenModule* cg, ssi_ir::SsiFunc* f)
{
    ssi_ir::SsiModule* m = cg.ir;

    // Track current function for emit_val IR_INDEX closure-env guard
    cg.cur_fn_decl = f.decl;

    // If the fn has #[extern("name")], it's a foreign declaration — no body.
    {
        char* ext_name = null;
        usz   ext_len  = 0;
        if (f.decl != null && fn_get_extern_name(f.decl, &ext_name, &ext_len))
        {
            // If it's a runtime symbol already declared, just skip this fn entirely — no define, no declare.
            if (name_is_runtime_decl(ext_name, ext_len)) { cg.cur_fn_decl = null; return; }
        }
        if (f.decl != null && fn_get_extern_name(f.decl, &ext_name, &ext_len)
         && !name_is_runtime_decl(ext_name, ext_len))
        {
            // Compute return type
            char[TYMAP_ENTRY] ext_ret;
            ext_ret[0] = 0;
            fn_param_llvm_type(f.decl, -1, &ext_ret[0], TYMAP_ENTRY);
            if (ext_ret[0] == 0) { snprintf(&ext_ret[0], TYMAP_ENTRY, "void"); }
            cg.out.writes("declare ");
            cg.out.writes(&ext_ret[0]);
            cg.out.writes(" @");
            // Write the extern name
            for (usz ei = 0; ei < ext_len; ei++) { cg.out.writec(ext_name[ei]); }
            cg.out.writes("(");
            // Emit parameter types (no names)
            if (f.decl != null)
            {
                // Walk the fn type to get param types
                bool found_ty = false;
                for (usz pi = 0; pi < f.decl.child_count; pi++)
                {
                    Node* fc = f.decl.children[pi];
                    if (fc == null) { continue; }
                    if (fc.kind == Nk.NODE_TYPE_FN && fc.child_count >= 1)
                    {
                        // First child is domain type (param(s))
                        Node* domain = fc.children[0];
                        if (domain != null)
                        {
                            if (domain.kind == Nk.NODE_TYPE_TUPLE)
                            {
                                // Multiple params
                                for (usz ti = 0; ti < domain.child_count; ti++)
                                {
                                    if (ti > 0) { cg.out.writes(", "); }
                                    cg.emit_type(domain.children[ti], false, 0);
                                }
                                found_ty = true;
                            }
                            else if (domain.kind != Nk.NODE_TYPE_PRIMITIVE
                                  || domain.p.ident.name_len != 0)
                            {
                                // Single param
                                cg.emit_type(domain, false, 0);
                                found_ty = true;
                            }
                        }
                        break;
                    }
                }
            }
            cg.out.writes(")\n");
            cg.cur_fn_decl = null;
            return;
        }
    }

    // Compute ret-type string ONCE so define header and all block terminators agree.
    // fn_param_llvm_type(decl,-1) and emit_fn_ret_type can diverge for broken/null decls.
    char[TYMAP_ENTRY] fn_ret_canonical;
    {
        fn_ret_canonical[0] = 0;
        if (f.decl != null && f.decl.kind == Nk.NODE_EXPR_CLOSURE)
        { closure_thunk_ret_type(f.decl, &fn_ret_canonical[0], TYMAP_ENTRY); }
        else if (f.decl == null)
        { snprintf(&fn_ret_canonical[0], TYMAP_ENTRY, "void"); }
        else
        { fn_param_llvm_type(f.decl, -1, &fn_ret_canonical[0], TYMAP_ENTRY); }
        if (fn_ret_canonical[0] == 0) snprintf(&fn_ret_canonical[0], TYMAP_ENTRY, "void");
    }

    // Function header: define RetType @name(ParamType %v0, ...) {
    // Store fn return type for use by emit_val (struct update needs it)
    {
        usz rlen = strlen(&fn_ret_canonical[0]);
        for (usz ri = 0; ri < rlen && ri < TYMAP_ENTRY-1; ri++)
        {
            cg.cur_fn_ret_type[ri] = fn_ret_canonical[ri];
        }
        cg.cur_fn_ret_type[rlen < TYMAP_ENTRY-1 ? rlen : TYMAP_ENTRY-1] = 0;
    }
    // Calling convention (if any) goes between "define" and return type.
    // Pre-scan attributes for #[interrupt] so we can emit CC before ret type.
    bool pre_interrupt = false;
    if (f.decl != null)
    {
        for (usz pci = 0; pci < f.decl.child_count && !pre_interrupt; pci++)
        {
            Node* pc = f.decl.children[pci];
            if (pc == null || pc.kind != Nk.NODE_ATTRIBUTE_LIST) continue;
            for (usz pci2 = 0; pci2 < pc.child_count && !pre_interrupt; pci2++)
            {
                Node* pa = pc.children[pci2];
                if (pa == null || pa.child_count < 1 || pa.children[0] == null) continue;
                char* pan = pa.children[0].p.ident.name_ptr;
                usz   pal = pa.children[0].p.ident.name_len;
                if (pal==9&&pan[0]=='i'&&pan[1]=='n'&&pan[2]=='t') { pre_interrupt = true; }
            }
        }
    }
    cg.out.writes("define ");
    if (pre_interrupt) { cg.out.writes("x86_intrcc "); }
    cg.out.writes(&fn_ret_canonical[0]);
    cg.out.writes(" ");
    cg.emit_fn_name(f);
    // Use the module-level TypeTable — allocated once, cleared O(1) per function.
    ssi_ir::SsiModule* mir_pre = cg.ir;
    if (!cg.tymap_initialized)
    {
        cg.tymap.data = null; cg.tymap.gens = null;
        cg.tymap.val_count = 0; cg.tymap.current_gen = 0;
        cg.tymap_initialized = cg.tymap.init(mir_pre.val_count);
    }
    else if (cg.tymap.val_count < mir_pre.val_count)
    {
        // Grow if IR expanded (rare)
        cg.tymap.destroy();
        cg.tymap_initialized = cg.tymap.init(mir_pre.val_count);
    }
    else
    {
        // O(1) clear via generation counter
        cg.tymap.clear();
    }
    if (cg.tymap_initialized) { infer_fn_types(mir_pre, f, &cg.tymap); }

    cg.out.writes("(");

    // Check if the function takes a unit parameter ((): zero params in LLVM IR).
    // We detect this by checking if there's exactly one param whose declared type
    // is void/unit — that means the fn signature was `() -> T`.
    bool unit_param = false;
    if (f.param_count == 1 && f.params[0] != null)
    {
        char[TYMAP_ENTRY] upbuf; upbuf[0] = 0;
        fn_param_llvm_type(f.decl, 0, &upbuf[0], TYMAP_ENTRY);
        // "void" = unit.  "{}" = empty struct = unit.  "{ i64, i64 }" = NOT unit.
        bool is_void_ty = (upbuf[0] == 'v' && upbuf[1] == 'o');
        bool is_empty_struct = (upbuf[0] == '{' && upbuf[1] == ' ' && upbuf[2] == '}');
        if (is_void_ty || is_empty_struct) { unit_param = true; }
    }

    usz emitted_params = 0;
    for (usz i = 0; i < f.param_count; i++)
    {
        ssi_ir::IrVal* pv = f.params[i];
        // Use type table for accurate param type
        if (pv != null)
        {
            char* pty = cg.tymap.get(pv.id);
            if (pty == null || pty[0] == 0) pty = (char*)"i64";
            // Skip unit/void parameters entirely — they carry no value in LLVM IR.
            if (pty[0]=='v'&&pty[1]=='o'&&pty[2]=='i'&&pty[3]=='d') { continue; }
            if (pty[0]=='{'&&pty[1]==' '&&pty[2]=='}') { continue; }
            // Also skip if declared type is unit
            if (unit_param && i == 0) { continue; }
            if (emitted_params > 0) { cg.out.writes(", "); }
            emitted_params++;
            // void is not valid as a param type — use i64 for unit params (fallback)
            if (pty[0]=='v'&&pty[1]=='o'&&pty[2]=='i'&&pty[3]=='d') { cg.out.writes("i64"); }
            // Structs are passed by pointer per System V AMD64 ABI
            else if (pty[0] == '%') { cg.out.writes("ptr"); }
            else
            {
                cg.out.writes(pty);
                // Add noalias to ptr params (pure Pride params never alias; helps vectorizer)
                if (pty[0] == 'p') { cg.out.writes(" noalias"); }
            }
            cg.out.writes(" %v");
            cg.out.writei(pv.id);
        }
    }
    // Check for vararg flag / #[vararg] attribute or ... in type signature
    // Emit ", ..." in the LLVM function signature for variadic functions.
    bool fn_vararg = false;
    if (f.decl != null)
    {
        for (usz vfi = 0; vfi < f.decl.child_count && !fn_vararg; vfi++)
        {
            Node* vfc = f.decl.children[vfi];
            if (vfc == null) continue;
            if (vfc.kind == Nk.NODE_ATTRIBUTE_LIST)
            {
                for (usz vfj = 0; vfj < vfc.child_count && !fn_vararg; vfj++)
                {
                    Node* vfa = vfc.children[vfj];
                    if (vfa == null || vfa.child_count < 1 || vfa.children[0] == null) continue;
                    char* vfan = vfa.children[0].p.ident.name_ptr;
                    usz   vfal = vfa.children[0].p.ident.name_len;
                    if (vfal == 6 && vfan[0]=='v'&&vfan[1]=='a'&&vfan[2]=='r'&&vfan[3]=='a'&&vfan[4]=='r'&&vfan[5]=='g')
                    { fn_vararg = true; }
                }
            }
            // Also check NODE_TYPE_FN for ... param type (NODE_ELLIPSIS or TYPE_VARIADIC)
            if (vfc.kind == Nk.NODE_TYPE_FN || vfc.kind == Nk.NODE_TYPE_TUPLE)
            {
                for (usz vfk = 0; vfk < vfc.child_count && !fn_vararg; vfk++)
                {
                    Node* vftp = vfc.children[vfk];
                    if (vftp != null && vftp.kind == Nk.NODE_TYPE_PRIMITIVE
                        && vftp.p.ident.name_len == 3
                        && vftp.p.ident.name_ptr[0] == '.'
                        && vftp.p.ident.name_ptr[1] == '.'
                        && vftp.p.ident.name_ptr[2] == '.')
                    { fn_vararg = true; }
                }
            }
        }
    }
    if (fn_vararg && f.param_count > 0) { cg.out.writes(", ..."); }
    else if (fn_vararg) { cg.out.writes("..."); }
    // Determine attribute group: check for [[noreturn]] attr on the fn decl
    bool fn_noreturn = false;
    if (f.decl != null)
    {
        for (usz fai = 0; fai < f.decl.child_count && !fn_noreturn; fai++)
        {
            Node* fac = f.decl.children[fai];
            if (fac == null || fac.kind != Nk.NODE_ATTRIBUTE_LIST) continue;
            for (usz faj = 0; faj < fac.child_count && !fn_noreturn; faj++)
            {
                Node* fa = fac.children[faj];
                if (fa == null || fa.child_count < 1 || fa.children[0] == null) continue;
                char* fan = fa.children[0].p.ident.name_ptr;
                usz   fal = fa.children[0].p.ident.name_len;
                // Check for "noreturn"
                if (fal==8&&fan[0]=='n'&&fan[1]=='o'&&fan[2]=='r') { fn_noreturn = true; }
            }
        }
    }
    // Scan fn attributes: naked, pure/const, cold, hot, section, interrupt, align
    bool fn_naked = false; bool fn_pure = false; bool fn_cold = false; bool fn_hot = false;
    bool fn_interrupt = false;
    char* fn_section  = null;  // #[section(".text.boot")] value string
    usz   fn_section_len = 0;
    long  fn_align    = 0;     // #[align(N)]
    if (f.decl != null)
    {
        for (usz fai2 = 0; fai2 < f.decl.child_count; fai2++)
        {
            Node* fac2 = f.decl.children[fai2];
            if (fac2 == null || fac2.kind != Nk.NODE_ATTRIBUTE_LIST) continue;
            for (usz faj2 = 0; faj2 < fac2.child_count; faj2++)
            {
                Node* fa2 = fac2.children[faj2];
                if (fa2 == null || fa2.child_count < 1 || fa2.children[0] == null) continue;
                char* fan2 = fa2.children[0].p.ident.name_ptr;
                usz   fal2 = fa2.children[0].p.ident.name_len;
                if (fal2==5&&fan2[0]=='n'&&fan2[1]=='a'&&fan2[2]=='k') { fn_naked = true; }
                if (fal2==4&&fan2[0]=='p'&&fan2[1]=='u'&&fan2[2]=='r') { fn_pure  = true; }
                if (fal2==4&&fan2[0]=='c'&&fan2[1]=='o'&&fan2[2]=='l') { fn_cold  = true; }
                if (fal2==3&&fan2[0]=='h'&&fan2[1]=='o'&&fan2[2]=='t') { fn_hot   = true; }
                // #[interrupt] — x86 interrupt handler calling convention
                if (fal2==9&&fan2[0]=='i'&&fan2[1]=='n'&&fan2[2]=='t') { fn_interrupt = true; }
                // #[section("name")] — linker section placement
                if (fal2==7&&fan2[0]=='s'&&fan2[1]=='e'&&fan2[2]=='c')
                {
                    if (fa2.child_count >= 2 && fa2.children[1] != null
                        && fa2.children[1].kind == Nk.NODE_LIT_STRING)
                    {
                        fn_section     = fa2.children[1].p.lit_str.ptr;
                        fn_section_len = fa2.children[1].p.lit_str.len;
                        // Strip surrounding quotes if present
                        if (fn_section_len >= 2 && fn_section[0] == '"')
                        { fn_section++; fn_section_len -= 2; }
                    }
                }
                // #[align(N)]
                if (fal2==5&&fan2[0]=='a'&&fan2[1]=='l'&&fan2[2]=='i')
                {
                    if (fa2.child_count >= 2 && fa2.children[1] != null
                        && fa2.children[1].kind == Nk.NODE_LIT_INT)
                    { fn_align = (long)fa2.children[1].p.lit_int.int_val; }
                }
            }
        }
    }

    // Build closing suffix: attribute group + optional section + optional align
    // These go AFTER the closing ')' and BEFORE '{'
    char[256] fn_suffix; fn_suffix[0] = 0;
    if (fn_naked)      { snprintf(&fn_suffix[0], 256, " naked nounwind"); }
    else if (fn_interrupt) { snprintf(&fn_suffix[0], 256, " nounwind"); }  // CC already emitted before rettype
    else if (fn_pure)  { snprintf(&fn_suffix[0], 256, " #4"); }
    else if (fn_cold)  { snprintf(&fn_suffix[0], 256, " #5"); }
    else if (fn_hot)   { snprintf(&fn_suffix[0], 256, " #6"); }
    else if (fn_noreturn && f.block_count <= 2) { snprintf(&fn_suffix[0], 256, " #2"); }
    else if (fn_noreturn)        { snprintf(&fn_suffix[0], 256, " #3"); }
    else if (f.block_count <= 2) { snprintf(&fn_suffix[0], 256, " #0"); }

    // Section attribute: section "name"
    if (fn_section != null && fn_section_len > 0)
    {
        usz sl = strlen(&fn_suffix[0]);
        snprintf(&fn_suffix[0] + sl, 256 - sl, " section \"");
        sl = strlen(&fn_suffix[0]);
        for (usz si = 0; si < fn_section_len && sl + 2 < 255; si++)
        { fn_suffix[sl++] = fn_section[si]; }
        fn_suffix[sl++] = '"'; fn_suffix[sl] = 0;
    }

    // Align attribute
    if (fn_align > 0)
    {
        usz sl = strlen(&fn_suffix[0]);
        snprintf(&fn_suffix[0] + sl, 256 - sl, " align %ld", fn_align);
    }

    // Emit closing paren + suffix + opening brace
    cg.out.writes(")");
    cg.out.writes(&fn_suffix[0]);
    cg.out.writes(" {\n");

    // Naked function body: just unreachable — inline asm handles the real work
    if (fn_naked)
    {
        cg.out.writes("entry:\n  unreachable\n}\n\n");
        cg.cur_fn_decl = null;
        return;
    }

    // Emit blocks
    int last_blk = f.block_start + f.block_count;
    for (int bid = f.block_start; bid < last_blk; bid++)
    {
        ssi_ir::IrBlock* b = m.blk(bid);
        if (b == null) { continue; }

        // Block label
        cg.out.writes("B");
        cg.out.writei(bid);
        cg.out.writes(":\n");

        // φ-nodes
        ssi_ir::IrVal* ph = b.phi_head;
        while (ph != null) { cg.emit_phi(ph, &cg.tymap); ph = ph.next; }

        // Straight-line instructions
        ssi_ir::IrVal* instr = b.head;
        while (instr != null) { cg.emit_val(instr, &cg.tymap); instr = instr.next; }

        // Typed φ edges: conversions incoming to successor φs are anchored
        // at the end of THIS block (their predecessor), before the terminator.
        cg.emit_phi_edge_coerces(b, &cg.tymap);

        // Terminator — use the canonical ret type computed once at function entry
        cg.emit_terminator(b, &cg.tymap, &fn_ret_canonical[0]);
    }

    cg.out.writes("}\n\n");
    cg.cur_fn_decl = null;
}


fn void CgenModule.emit_runtime_decls(CgenModule* cg)
{
    // Pride runtime (implemented in runtime.c, linked separately)
    // Effects runtime (the ONLY runtime.c dependency — ucontext-based)
    cg.out.writes("; Pride effects runtime\n");
    cg.out.writes("declare ptr  @__pride_perform(i64, i64, ...)\n");
    cg.out.writes("declare i64  @__pride_push_handler(i64, i64, ...)\n");
    cg.out.writes("declare void @__pride_pop_handler()\n");
    cg.out.writes("declare void @__pride_complete()\n");
    cg.out.writes("declare ptr  @__pride_resume(ptr)\n");
    cg.out.writes("declare void @__pride_drop(ptr)\n");
    cg.out.writes("declare void @__pride_panic(ptr, i64)\n");
    cg.out.writes("declare i64  @__pride_get_arm_arg(i64)\n");
    // Untyped HOSE (Hybrid Fiber + Prompt Engine)
    cg.out.writes("declare ptr  @__pride_fiber_spawn(ptr, ptr)\n");
    cg.out.writes("declare ptr  @__pride_fiber_yield(ptr)\n");
    cg.out.writes("declare ptr  @__pride_fiber_resume(ptr, ptr)\n");
    cg.out.writes("declare i64  @__pride_prompt_install(i64)\n");
    cg.out.writes("declare void @__pride_prompt_unwind(i64)\n");
    cg.out.writes("declare i1   @__pride_is_in_scope(i64)\n");
    cg.out.writes("declare ptr  @__pride_scoped_yield_in(i64, i64, ptr)\n");
    cg.out.writes("declare ptr  @__pride_scoped_yield_out(i64, i64, ptr)\n");
    cg.out.writes("declare ptr  @__pride_split_cont(ptr)\n");
    cg.out.writes("declare ptr  @__pride_fuse_cont(ptr)\n");
    cg.out.writes("declare void @__pride_dynamic_wind_push(i64, ptr, ptr, ptr)\n");
    cg.out.writes("declare void @__pride_dynamic_wind_pop(i64)\n");
    cg.out.writes("declare void @__pride_dynamic_wind_enter(i64)\n");
    cg.out.writes("declare void @__pride_dynamic_wind_exit(i64)\n");
    cg.out.writes("declare i64  @__pride_local_bind(i64, ptr, i64)\n");
    cg.out.writes("declare ptr  @__pride_local_get(i64)\n");
    // Tensor matmul (`@` operator) — implemented in runtime/compiler_rt.c
    cg.out.writes("declare ptr  @__pride_matmul(ptr, ptr)\n");
    cg.out.writes("declare ptr  @__pride_tensor_elemwise(ptr, ptr, i32)\n");
    // vector · vector dot product (spec §11: rank-1 @ rank-1 -> scalar)
    cg.out.writes("declare double @__pride_vecdot(ptr, ptr)\n");
    // Str runtime helpers (string builder used by fmt)
    cg.out.writes("declare void @pride_str_init(ptr)\n");
    cg.out.writes("declare void @pride_str_push_str(ptr, ptr, i64)\n");
    cg.out.writes("declare void @pride_str_push_i64(ptr, i64)\n");
    cg.out.writes("declare void @pride_str_push_f64(ptr, double)\n");
    cg.out.writes("declare i1   @pride_str_eq(ptr, i64, ptr, i64)\n");
    // LLVM intrinsics — zero runtime cost, inlined by the backend
    // Bit manipulation
    cg.out.writes("declare i64 @llvm.ctpop.i64(i64)\n");
    cg.out.writes("declare i64 @llvm.ctlz.i64(i64, i1)\n");
    cg.out.writes("declare i64 @llvm.cttz.i64(i64, i1)\n");
    cg.out.writes("declare i64 @llvm.fshl.i64(i64, i64, i64)\n");
    cg.out.writes("declare i64 @llvm.fshr.i64(i64, i64, i64)\n");
    cg.out.writes("declare i64 @llvm.bitreverse.i64(i64)\n");
    cg.out.writes("declare i64 @llvm.bswap.i64(i64)\n");
    // Overflow-checked arithmetic (returns {iN, i1})
    cg.out.writes("declare {i32, i1} @llvm.sadd.with.overflow.i32(i32, i32)\n");
    cg.out.writes("declare {i64, i1} @llvm.sadd.with.overflow.i64(i64, i64)\n");
    cg.out.writes("declare {i32, i1} @llvm.ssub.with.overflow.i32(i32, i32)\n");
    cg.out.writes("declare {i64, i1} @llvm.ssub.with.overflow.i64(i64, i64)\n");
    cg.out.writes("declare {i32, i1} @llvm.smul.with.overflow.i32(i32, i32)\n");
    cg.out.writes("declare {i64, i1} @llvm.smul.with.overflow.i64(i64, i64)\n");
    cg.out.writes("declare {i32, i1} @llvm.uadd.with.overflow.i32(i32, i32)\n");
    cg.out.writes("declare {i64, i1} @llvm.uadd.with.overflow.i64(i64, i64)\n");
    // Saturating arithmetic
    // Saturating arithmetic — i8/i16/i32/i64 widths for sadd/ssub/smul/uadd/usub
    cg.out.writes("declare i8  @llvm.sadd.sat.i8 (i8,  i8 )\n");
    cg.out.writes("declare i16 @llvm.sadd.sat.i16(i16, i16)\n");
    cg.out.writes("declare i32 @llvm.sadd.sat.i32(i32, i32)\n");
    cg.out.writes("declare i64 @llvm.sadd.sat.i64(i64, i64)\n");
    cg.out.writes("declare i8  @llvm.ssub.sat.i8 (i8,  i8 )\n");
    cg.out.writes("declare i16 @llvm.ssub.sat.i16(i16, i16)\n");
    cg.out.writes("declare i32 @llvm.ssub.sat.i32(i32, i32)\n");
    cg.out.writes("declare i64 @llvm.ssub.sat.i64(i64, i64)\n");
    cg.out.writes("declare i8  @llvm.smul.sat.i8 (i8,  i8 )\n");
    cg.out.writes("declare i16 @llvm.smul.sat.i16(i16, i16)\n");
    cg.out.writes("declare i32 @llvm.smul.sat.i32(i32, i32)\n");
    cg.out.writes("declare i64 @llvm.smul.sat.i64(i64, i64)\n");
    cg.out.writes("declare i64 @llvm.uadd.sat.i64(i64, i64)\n");
    cg.out.writes("declare i64 @llvm.usub.sat.i64(i64, i64)\n");
    // Memory
    cg.out.writes("declare void @llvm.memset.p0.i64(ptr nocapture writeonly, i8, i64, i1)\n");
    cg.out.writes("declare void @llvm.memcpy.p0.p0.i64(ptr nocapture writeonly, ptr nocapture readonly, i64, i1)\n");
    cg.out.writes("declare void @llvm.memmove.p0.p0.i64(ptr nocapture, ptr nocapture readonly, i64, i1)\n");
    // Fences / barriers — emit as LLVM fence instruction, not a call
    // Math
    cg.out.writes("declare double @llvm.sqrt.f64(double)\n");
    cg.out.writes("declare float  @llvm.sqrt.f32(float)\n");
    cg.out.writes("declare double @llvm.fabs.f64(double)\n");
    cg.out.writes("declare float  @llvm.fabs.f32(float)\n");
    cg.out.writes("declare double @llvm.floor.f64(double)\n");
    cg.out.writes("declare double @llvm.ceil.f64(double)\n");
    cg.out.writes("declare double @llvm.round.f64(double)\n");
    cg.out.writes("declare double @llvm.trunc.f64(double)\n");
    cg.out.writes("declare double @llvm.fma.f64(double, double, double)\n");
    cg.out.writes("declare double @llvm.pow.f64(double, double)\n");
    cg.out.writes("declare double @llvm.log.f64(double)\n");
    cg.out.writes("declare double @llvm.log2.f64(double)\n");
    cg.out.writes("declare double @llvm.log10.f64(double)\n");
    cg.out.writes("declare double @llvm.exp.f64(double)\n");
    cg.out.writes("declare double @llvm.exp2.f64(double)\n");
    cg.out.writes("declare double @llvm.sin.f64(double)\n");
    cg.out.writes("declare double @llvm.cos.f64(double)\n");
    cg.out.writes("declare double @llvm.minnum.f64(double, double)\n");
    cg.out.writes("declare double @llvm.maxnum.f64(double, double)\n");
    cg.out.writes("declare double @llvm.copysign.f64(double, double)\n");
    // libc — Pride links -lc, so these are zero-cost declarations
    cg.out.writes("; libc\n");
    cg.out.writes("declare ptr   @malloc(i64)\n");
    cg.out.writes("declare void  @free(ptr)\n");
    cg.out.writes("declare ptr   @realloc(ptr, i64)\n");
    cg.out.writes("declare ptr   @calloc(i64, i64)\n");
    cg.out.writes("declare ptr   @memcpy(ptr, ptr, i64)\n");
    cg.out.writes("declare ptr   @memmove(ptr, ptr, i64)\n");
    cg.out.writes("declare ptr   @memset(ptr, i32, i64)\n");
    cg.out.writes("declare i32   @memcmp(ptr, ptr, i64)\n");
    cg.out.writes("declare ptr   @strdup(ptr)\n");
    cg.out.writes("declare ptr   @strndup(ptr, i64)\n");
    cg.out.writes("declare i64   @strlen(ptr)\n");
    cg.out.writes("declare i32   @strcmp(ptr, ptr)\n");
    cg.out.writes("declare i32   @strncmp(ptr, ptr, i64)\n");
    cg.out.writes("declare ptr   @getenv(ptr)\n");
    cg.out.writes("declare i32   @putenv(ptr)\n");
    cg.out.writes("declare void  @_exit(i32) noreturn\n");
    cg.out.writes("declare i32   @write(i32, ptr, i64)\n");
    cg.out.writes("declare i32   @open(ptr, i32, ...)\n");
    cg.out.writes("declare i32   @close(i32)\n");
    cg.out.writes("declare i64   @read(i32, ptr, i64)\n");
    cg.out.writes("declare ptr   @mmap(ptr, i64, i32, i32, i32, i64)\n");
    cg.out.writes("declare i32   @munmap(ptr, i64)\n");
    cg.out.writes("declare i32   @mprotect(ptr, i64, i32)\n");
    cg.out.writes("declare i32   @madvise(ptr, i64, i32)\n");
    cg.out.writes("declare i64   @syscall(i64, ...)\n");
    cg.out.writes("declare i32   @pthread_create(ptr, ptr, ptr, ptr)\n");
    cg.out.writes("declare i32   @pthread_join(i64, ptr)\n");
    cg.out.writes("declare i32   @pthread_mutex_lock(ptr)\n");
    cg.out.writes("declare i32   @pthread_mutex_unlock(ptr)\n");
    cg.out.writes("declare i32   @pthread_mutex_init(ptr, ptr)\n");
    cg.out.writes("declare i32   @pthread_mutex_destroy(ptr)\n");
    cg.out.writes("declare i32   @pthread_rwlock_rdlock(ptr)\n");
    cg.out.writes("declare i32   @pthread_rwlock_wrlock(ptr)\n");
    cg.out.writes("declare i32   @pthread_rwlock_unlock(ptr)\n");
    cg.out.writes("declare i32   @pthread_cond_wait(ptr, ptr)\n");
    cg.out.writes("declare i32   @pthread_cond_signal(ptr)\n");
    cg.out.writes("declare i32   @pthread_cond_broadcast(ptr)\n");
    cg.out.writes("declare i32   @clock_gettime(i32, ptr)\n");
    cg.out.writes("declare i32   @nanosleep(ptr, ptr)\n");
    cg.out.writes("declare i32   @getaddrinfo(ptr, ptr, ptr, ptr)\n");
    cg.out.writes("declare void  @freeaddrinfo(ptr)\n");
    cg.out.writes("declare i64   @getrandom(ptr, i64, i32)\n");
    // libm (linked via -lm)
    cg.out.writes("; libm\n");
    cg.out.writes("declare double @sin(double)\n");
    cg.out.writes("declare double @cos(double)\n");
    cg.out.writes("declare double @tan(double)\n");
    cg.out.writes("declare double @asin(double)\n");
    cg.out.writes("declare double @acos(double)\n");
    cg.out.writes("declare double @atan(double)\n");
    cg.out.writes("declare double @atan2(double, double)\n");
    cg.out.writes("declare double @sinh(double)\n");
    cg.out.writes("declare double @cosh(double)\n");
    cg.out.writes("declare double @tanh(double)\n");
    cg.out.writes("declare double @exp(double)\n");
    cg.out.writes("declare double @exp2(double)\n");
    cg.out.writes("declare double @log(double)\n");
    cg.out.writes("declare double @log2(double)\n");
    cg.out.writes("declare double @log10(double)\n");
    cg.out.writes("declare double @pow(double, double)\n");
    cg.out.writes("declare double @sqrt(double)\n");
    cg.out.writes("declare double @cbrt(double)\n");
    cg.out.writes("declare double @hypot(double, double)\n");
    cg.out.writes("declare double @fabs(double)\n");
    cg.out.writes("declare double @floor(double)\n");
    cg.out.writes("declare double @ceil(double)\n");
    cg.out.writes("declare double @round(double)\n");
    cg.out.writes("declare double @trunc(double)\n");
    cg.out.writes("declare double @fmod(double, double)\n");
    cg.out.writes("declare double @fma(double, double, double)\n");
    cg.out.writes("declare double @copysign(double, double)\n");
    cg.out.writes("declare float  @sinf(float)\n");
    cg.out.writes("declare float  @cosf(float)\n");
    cg.out.writes("declare float  @sqrtf(float)\n");
    cg.out.writes("declare float  @expf(float)\n");
    cg.out.writes("declare float  @logf(float)\n");
    cg.out.writes("declare float  @powf(float, float)\n");
    cg.out.writes("declare float  @fabsf(float)\n");
    cg.out.writes("declare float  @floorf(float)\n");
    cg.out.writes("declare float  @ceilf(float)\n");
    cg.out.writes("declare float  @roundf(float)\n");
    cg.out.writes("declare float  @fmaf(float, float, float)\n");
    cg.out.writes("\n");
    // Attribute sets tuned for execution speed and binary size
    // #0: small pure functions (most Pride fns) — inline + willreturn for aggressive opt
    cg.out.writes("attributes #0 = { inlinehint nounwind willreturn mustprogress }\n");
    // #1: non-inline functions
    cg.out.writes("attributes #1 = { nounwind willreturn mustprogress }\n");
    // #2: noreturn small (panic, unreachable)
    cg.out.writes("attributes #2 = { inlinehint nounwind noreturn }\n");
    // #3: noreturn
    cg.out.writes("attributes #3 = { nounwind noreturn }\n");
    // #4: readonly — pure fn with no side effects
    cg.out.writes("attributes #4 = { inlinehint nounwind readonly willreturn mustprogress }\n");
    // #5: cold path
    cg.out.writes("attributes #5 = { nounwind cold willreturn }\n");
    // #6: hot path — inline aggressively
    cg.out.writes("attributes #6 = { inlinehint nounwind hot willreturn mustprogress }\n");
    cg.out.writes("\n");
}


// For each `impl Interface for Type` block encountered, emit a global constant
// array of function pointers in the order the interface declares its methods.
// Symbol name: @__pride_vtable_<Interface>_<Type>

fn void CgenModule.emit_vtables(CgenModule* cg, ssi_ir::SsiModule* ir)
{
    // Walk all function declarations looking for impl blocks
    // For each NODE_DECL_IMPL: emit vtable global
    // We scan funcs to find impl-associated functions grouped by impl decl.
    // Simple approach: emit one vtable per unique impl block seen in the IR.
    // The impl decl node is stored as f.decl.parent (not directly accessible here).
    // Instead: collect impl decls from the AST program node via the IR module's arena.
    // For now emit a structural vtable: if a fn is tagged with an impl parent,
    // group them and emit the vtable.
    // This is the scaffolding — full wiring happens via lower_fn tagging.
    // (Vtable generation is complete in stdlib/dyn.pie at the language level.)
    // LLVM-level vtable: emitted per impl block found during fn scan.
    for (usz fi = 0; fi < ir.func_count; fi++)
    {
        ssi_ir::SsiFunc* f = &ir.funcs[fi];
        if (f.decl == null) continue;
        // Check if this fn is inside an impl block (parent is NODE_DECL_IMPL)
        // The fn's decl parent is not directly stored; we use a naming convention:
        // impl methods are emitted normally. The vtable is a separate pass that
        // the user constructs via dyn_new() with explicit fn pointers.
        // Full auto-vtable generation is a future pass.
    }
}

// NOTE: thread_local globals use "thread_local" storage class in LLVM IR.
// NODE_DECL_TLS nodes are lowered by the SSI IR builder as IR_UNKNOWN with TLS tag.
// The codegen emits: @name = thread_local global T init


// ── Fat fn-value trampolines (r9 uniform indirect ABI) ─────────────────────
// Every named fn referenced AS A VALUE is materialized as the fat pair
// { ptr @__pride_fptr_<name>, ptr null }. Each registered fn gets exactly one
// adapter emitted here:
//
//     define RET @__pride_fptr_<name>(ptr %env, W0 %w0, ..., Wn %w(n-1)) {
//         %r = call RET @<real>(<marshalled args>)
//         ret RET %r
//     }
//
// The wire convention (shared with every indirect fat call site, which
// marshals against the callee's `(T... -> U)` TYPE) explodes a tuple domain
// componentwise. The adapter translates to the callee's real ABI: direct
// pass-through for an exploding binder / an extern declare, or an
// insertvalue-pack into the single aggregate parameter when the fn binds
// its whole tuple domain under one pattern.

// Record `decl` as needing a trampoline (deduped by decl pointer).
fn void CgenModule.register_trampoline(CgenModule* cg, Node* decl)
{
    if (decl == null || decl.kind != Nk.NODE_DECL_FN) return;
    for (usz i = 0; i < cg.tramp_count; i++)
    {
        if (cg.tramp_decls[i] == decl) { return; }
    }
    if (cg.tramp_count >= TRAMP_CAP)
    {
        printf("codegen error: too many fn values used through the indirect ABI (TRAMP_CAP reached)\n");
        cg.errors++;
        return;
    }
    cg.tramp_decls[cg.tramp_count] = decl;
    cg.tramp_count++;
}

// The trampoline symbol's base name: the #[extern] C symbol when present,
// else the fn's source name. Written NUL-terminated into buf.
fn void tramp_base_name(Node* decl, char* buf, usz cap)
{
    if (cap == 0) return;
    buf[0] = 0;
    char* src = null;
    usz   len = 0;
    char* ext = null; usz extl = 0;
    if (decl != null && fn_get_extern_name(decl, &ext, &extl)
        && ext != null && extl > 0)
    {
        src = ext; len = extl;
    }
    else if (decl != null && decl.child_count >= 1 && decl.children[0] != null)
    {
        src = decl.children[0].p.ident.name_ptr;
        len = decl.children[0].p.ident.name_len;
    }
    if (src == null) return;
    usz off = 0;
    while (off < len && off + 1 < cap) { buf[off] = src[off]; off++; }
    buf[off] = 0;
}

fn void CgenModule.emit_fn_trampolines(CgenModule* cg)
{
    if (cg.tramp_count == 0) return;
    cg.out.writes("\n; ── Fat fn-value trampolines ────────────────────────────────────\n");
    for (usz ti = 0; ti < cg.tramp_count; ti++)
    {
        Node* decl = cg.tramp_decls[ti];
        if (decl == null) continue;

        // Symbol base name; dedupe by NAME (two different decls sharing one
        // source name already alias at the value materialization, which is
        // name-based — emitting two identical symbols would be invalid IR).
        char[NAME_BUF] tname;
        tramp_base_name(decl, &tname[0], NAME_BUF);
        if (tname[0] == 0) continue;
        bool dup = false;
        for (usz tj = 0; tj < ti && !dup; tj++)
        {
            char[NAME_BUF] prev;
            tramp_base_name(cg.tramp_decls[tj], &prev[0], NAME_BUF);
            if (cstr_eq(&tname[0], &prev[0])) { dup = true; }
        }
        if (dup) continue;

        // Signature / domain
        Node* sig = null;
        for (usz si = 0; si < decl.child_count; si++)
        {
            Node* sc = decl.children[si];
            if (sc != null && sc.kind == Nk.NODE_TYPE_FN) { sig = sc; break; }
        }
        Node* dom = null;
        if (sig != null)
        {
            Node* lhs = sig.child_count >= 1 ? sig.children[0] : null;
            Node* rhs = sig.child_count >= 2 ? sig.children[1] : null;
            dom = lhs;
            if (rhs != null && rhs.kind == Nk.NODE_EFFECT_ROW
                && lhs != null && lhs.kind == Nk.NODE_TYPE_FN)
            {
                dom = lhs.child_count >= 1 ? lhs.children[0] : null;
            }
        }
        bool unit_dom = (dom == null)
            || (dom.kind == Nk.NODE_EXPR_UNIT)
            || (dom.kind == Nk.NODE_TYPE_TUPLE && dom.child_count == 0)
            || (dom.kind == Nk.NODE_TYPE_PRIMITIVE && dom.p.ident.name_len == 0);
        bool tuple_dom = (dom != null && dom.kind == Nk.NODE_TYPE_TUPLE && !unit_dom);
        usz nwire = unit_dom ? (usz)0 : (tuple_dom ? dom.child_count : (usz)1);

        // Return type mirrors the real fn's exactly (decl-driven; both sides
        // of the forwarder must agree, so only one string is computed).
        char[TYMAP_ENTRY] ret_ty;
        ret_ty[0] = 0;
        fn_param_llvm_type(decl, -1, &ret_ty[0], TYMAP_ENTRY);
        if (ret_ty[0] == 0) { snprintf(&ret_ty[0], TYMAP_ENTRY, "void"); }
        bool ret_void = (ret_ty[0]=='v' && ret_ty[1]=='o')
                     || (ret_ty[0]=='{' && ret_ty[1]==' ' && ret_ty[2]=='}');

        // Real target symbol
        char* ext2 = null; usz ext2l = 0;
        bool has_ext2 = fn_get_extern_name(decl, &ext2, &ext2l)
                     && ext2 != null && ext2l > 0;
        bool is_main2 = (decl.child_count >= 1 && decl.children[0] != null)
            && span_is(decl.children[0].p.ident.name_ptr,
                       decl.children[0].p.ident.name_len, (char*)"main");

        // Pack when the real fn binds its tuple domain as ONE aggregate
        // parameter (non-exploding binder). Externs explode exactly like the
        // wire (their declare is componentwise), so they pass through.
        bool pack = tuple_dom && !has_ext2 && !is_main2
            && !fn_binder_explodes_tuple(decl, dom);

        cg.out.writes("define ");
        cg.out.writes(&ret_ty[0]);
        cg.out.writes(" @__pride_fptr_");
        cg.out.writes(&tname[0]);
        cg.out.writes("(ptr %env");
        for (usz wi = 0; wi < nwire; wi++)
        {
            char[TYMAP_ENTRY] wty;
            wty[0] = 0;
            if (tuple_dom) { type_to_llvm_buf(dom.children[wi], &wty[0], TYMAP_ENTRY, 0); }
            else           { type_to_llvm_buf(dom,               &wty[0], TYMAP_ENTRY, 0); }
            if (wty[0]==0 || (wty[0]=='v'&&wty[1]=='o')) { snprintf(&wty[0], TYMAP_ENTRY, "i64"); }
            cg.out.writes(", ");
            cg.out.writes(&wty[0]);
            cg.out.writes(" %w");
            cg.out.writeu(wi);
        }
        cg.out.writes(") {\nentry:\n");

        if (pack)
        {
            char[TYMAP_ENTRY] agty;
            type_to_llvm_buf(dom, &agty[0], TYMAP_ENTRY, 0);
            for (usz wi = 0; wi < nwire; wi++)
            {
                char[TYMAP_ENTRY] wty2;
                type_to_llvm_buf(dom.children[wi], &wty2[0], TYMAP_ENTRY, 0);
                if (wty2[0] == 0) { snprintf(&wty2[0], TYMAP_ENTRY, "i64"); }
                cg.out.writes("  %pk."); cg.out.writeu(wi);
                cg.out.writes(" = insertvalue ");
                cg.out.writes(&agty[0]);
                if (wi == 0) { cg.out.writes(" undef, "); }
                else { cg.out.writes(" %pk."); cg.out.writeu(wi - 1); cg.out.writes(", "); }
                cg.out.writes(&wty2[0]);
                cg.out.writes(" %w"); cg.out.writeu(wi);
                cg.out.writes(", "); cg.out.writeu(wi); cg.out.writes("\n");
            }
        }

        if (!ret_void) { cg.out.writes("  %r = "); }
        else           { cg.out.writes("  "); }
        cg.out.writes("call ");
        cg.out.writes(&ret_ty[0]);
        cg.out.writes(" ");
        if (is_main2) { cg.out.writes("@main"); }
        else if (has_ext2)
        {
            cg.out.writes("@");
            for (usz e2 = 0; e2 < ext2l; e2++) { cg.out.writec(ext2[e2]); }
        }
        else { cg.out.writes("@pride_"); cg.out.writes(&tname[0]); }
        cg.out.writes("(");
        if (pack)
        {
            char[TYMAP_ENTRY] agty2;
            type_to_llvm_buf(dom, &agty2[0], TYMAP_ENTRY, 0);
            cg.out.writes(&agty2[0]);
            cg.out.writes(" %pk."); cg.out.writeu(nwire - 1);
        }
        else
        {
            for (usz wi = 0; wi < nwire; wi++)
            {
                if (wi > 0) { cg.out.writes(", "); }
                char[TYMAP_ENTRY] wty3;
                if (tuple_dom) { type_to_llvm_buf(dom.children[wi], &wty3[0], TYMAP_ENTRY, 0); }
                else           { type_to_llvm_buf(dom,               &wty3[0], TYMAP_ENTRY, 0); }
                if (wty3[0]==0 || (wty3[0]=='v'&&wty3[1]=='o')) { snprintf(&wty3[0], TYMAP_ENTRY, "i64"); }
                cg.out.writes(&wty3[0]);
                cg.out.writes(" %w"); cg.out.writeu(wi);
            }
        }
        cg.out.writes(")\n");
        if (ret_void) { cg.out.writes("  ret void\n"); }
        else { cg.out.writes("  ret "); cg.out.writes(&ret_ty[0]); cg.out.writes(" %r\n"); }
        cg.out.writes("}\n\n");
    }
}

fn bool CgenModule.emit(CgenModule* cg, char* source_filename)
{
    ssi_ir::SsiModule* m = cg.ir;
    cg.gmut_count = 0;   // r56d: fresh registry per module

    cg.out.writes("; ModuleID = '");
    if (source_filename != null) { cg.out.writes(source_filename); }
    cg.out.writes("'\n");
    cg.out.writes("source_filename = \"");
    if (source_filename != null) { cg.out.writes(source_filename); }
    cg.out.writes("\"\n");
    cg.out.writes("target datalayout = \"");
    cg.out.writes(cg.datalayout);
    cg.out.writes("\"\n");
    cg.out.writes("target triple = \"");
    cg.out.writes(cg.triple);
    cg.out.writes("\"\n\n");

    cg.collect_all_structs();
    if (cg.struct_count > 0)
    {
        cg.out.writes("; ── Named struct types ──────────────────────────────────────\n");
        cg.emit_struct_decls();
        cg.out.writes("\n");
    }

    // Module-level optimization metadata
    // !0 = !{i32 1} — 1=required, 7=max-one-use, 2=allow-override
    cg.out.writes("!llvm.module.flags = !{!0}\n");
    cg.out.writes("!0 = !{i32 1, !\"wchar_size\", i32 4}\n");

    cg.out.writes("; ── String constants ────────────────────────────────────────\n");
    cg.emit_string_globals();
    cg.emit_gmut_globals();   // r56d mutable module-globals
    cg.out.writes("\n");

    if (!cg.freestanding)
    {
        cg.emit_runtime_decls();
    }

    cg.out.writes("; ── Function definitions ────────────────────────────────────\n");
    for (usz fi = 0; fi < m.func_count; fi++)
    {
        cg.emit_function(&m.funcs[fi]);
    }

    // Uniform indirect ABI adapters for every fn referenced as a value
    // (registered during value materialization inside emit_function).
    cg.emit_fn_trampolines();

    cg.out.flush();
    return cg.errors == 0;
}


// For each IR_UNKNOWN value tagged as a closure (binder.kind == NODE_EXPR_CLOSURE),
// emit a standalone LLVM function that:
//   1. Receives (ptr %__env, args...) 
//   2. Loads each captured value from the env array (via ptrtoint)
//   3. Executes the closure body inline
// The closure body is the AST NODE_EXPR_CLOSURE's clause children.
// We emit it as a dedicated SSI function via a synthetic lower pass.

fn void CgenModule.emit_closure_thunks(CgenModule* cg)
{
    ssi_ir::SsiModule* m = cg.ir;

    // Scan all vals for closure IR_UNKNOWN nodes
    for (usz vi = 0; vi < m.val_count; vi++)
    {
        ssi_ir::IrVal* v = &m.vals[vi];
        if (v.op != ssi_ir::IrOp.IR_UNKNOWN) continue;
        if (v.binder == null || v.binder.kind != Nk.NODE_EXPR_CLOSURE) continue;

        int cid = (int)(v.ival & 0x7FFFFFFF);
        usz ncap = v.arg_count;
        Node* closure = v.binder;

        // Determine parameter count from the first clause's pattern
        usz nparams = 0;
        if (closure.child_count >= 1 && closure.children[0] != null)
        {
            Node* clause = closure.children[0];
            Node* pat = clause.child_count >= 1 ? clause.children[0] : null;
            if (pat != null && pat.kind == Nk.NODE_PATTERN_TUPLE)
            { nparams = pat.child_count; }
            else if (pat != null && pat.kind == Nk.NODE_PATTERN_IDENT)
            { nparams = 1; }
        }

        // Emit: define i64 @__pride_closure_N(ptr %__env, i64 %a0, i64 %a1, ...)
        cg.out.writes("; closure thunk\n");
        cg.out.writes("define i64 @__pride_closure_");
        cg.out.writei((long)cid);
        cg.out.writes("(ptr %__env");
        for (usz pi = 0; pi < nparams; pi++)
        {
            cg.out.writes(", i64 %ca"); cg.out.writei((long)pi);
        }
        cg.out.writes(") {\n");
        cg.out.writes("entry:\n");

        // Unpack captures from env array
        for (usz ci = 0; ci < ncap; ci++)
        {
            cg.out.writes("  %eslot."); cg.out.writei((long)ci);
            cg.out.writes(" = getelementptr ["); cg.out.writei((long)ncap);
            cg.out.writes(" x ptr], ptr %__env, i32 0, i32 "); cg.out.writei((long)ci);
            cg.out.writes("\n");
            cg.out.writes("  %ecap."); cg.out.writei((long)ci);
            cg.out.writes(" = load ptr, ptr %eslot."); cg.out.writei((long)ci);
            cg.out.writes("\n");
            // ptrtoint to i64 for arithmetic use inside body
            cg.out.writes("  %ecapi."); cg.out.writei((long)ci);
            cg.out.writes(" = ptrtoint ptr %ecap."); cg.out.writei((long)ci);
            cg.out.writes(" to i64\n");
        }

        // Emit the closure body.
        // For each clause: evaluate body expression with params bound.
        // Simplified: emit a call-through to the first body expression.
        // Full CTFE lowering would require re-running the SSI pass on the body AST.
        // For now: emit a placeholder that returns 0, which will be replaced once
        // the closure body is lowered via lower_fn (registered in pending_inner_fns).
        // The actual thunk body will be emitted when the closure AST node is lowered
        // as a synthetic fn via lower_fn — see note below.
        // NOTE: The real body lowering happens via pending_inner_fns in ssi_ir.c3.
        // This thunk is a forward declaration that gets filled in by that pass.
        // For closures with bodies, the thunk IS the lowered fn.
        // Here we emit a minimal stub that calls the SSI-lowered body via tail call.
        cg.out.writes("  ; closure body (lowered by SSI pass)\n");
        cg.out.writes("  ret i64 0  ; TODO: link to SSI-lowered body\n");
        cg.out.writes("}\n\n");
    }
}


fn bool emit_llvm_file(ssi_ir::SsiModule* ir, ast::AstArena* arena,
                       char* source_filename, char* output_path)
{
    void* f = fopen(output_path, "wb");
    if (f == null) { printf("codegen: cannot open output file\n"); return false; }

    CgenModule* cg = (CgenModule*)malloc(CgenModule::size);
    if (cg == null) { fclose(f); printf("codegen: OOM\n"); return false; }
    if (!cg.init(ir, arena, f))
    {
        free((void*)cg);
        fclose(f);
        printf("codegen: failed to allocate output buffer\n");
        return false;
    }

    bool ok = cg.emit(source_filename);
    cg.destroy();
    free((void*)cg);
    fclose(f);
    return ok;
}

// Convenience: emit to stdout (for --emit-llvm - or piping)
fn bool emit_llvm_stdout(ssi_ir::SsiModule* ir, ast::AstArena* arena,
                         char* source_filename)
{
    // stdout = fd 1; we use printf directly via the output buffer writing to null
    // file means no fwrite. Instead use a heap buf and printf at flush.
    // Simplest: just call emit_llvm_file with "/dev/stdout"
    return emit_llvm_file(ir, arena, source_filename, (char*)"/dev/stdout");
}
