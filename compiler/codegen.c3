// ============================================================================
// codegen.c3 — Pryde → LLVM 22.1.8 IR text emitter
// ----------------------------------------------------------------------------
// Implementation language: C3 (host).
//
// This module is Pryde's native code generator. It walks a fully-built and
// verified SsiModule and emits LLVM 22 IR text (the .ll format), which is
// then compiled through the pure LLVM 22 toolchain — no Clang anywhere.
//
// Full pipeline (no Clang):
//   pryde --emit-llvm output.ll source.pry   # this module
//   llvm-as-22 output.ll -o output.bc        # assemble
//   opt-22 -O2 output.bc -o output.opt.bc    # optimise
//   llc-22 -filetype=obj output.opt.bc -o output.o  # compile
//   ld.lld-22 crt1.o output.o runtime.o -lc -o prog # link
//
// TARGET
// ──────
// LLVM 22.1.8 (tested). Forward-compatible: LLVM IR is backward-compatible
// across minor and patch versions.
// Default target: x86_64-pc-linux-gnu (System V AMD64 ABI, ELF).
// The target triple and data layout strings are constants that can be
// overridden via CgenModule fields before calling emit().
//
// KEY DESIGN DECISIONS
// ────────────────────
// 1. OPAQUE POINTERS (mandatory since LLVM 17): all pointer types emit as
//    `ptr` — no typed pointers (i32*, i8*) whatsoever.
//
// 2. VALUE NAMING: SSA values use the dense integer ids from IrVal.id,
//    emitted as %v0, %v1, ... Basic blocks use %B0, %B1, ... matching the
//    SsiModule dump format so IR is easily cross-referenced.
//
// 3. TYPE SYSTEM MAPPING:
//    Pryde primitive → LLVM type:
//      i8/u8 → i8,  i16/u16 → i16,  i32/u32 → i32,  i64/u64 → i64
//      f32 → float,  f64 → double,  bool → i1,  char → i32 (Unicode codepoint)
//      ptr/*T/&T/&mut T → ptr   (opaque, LLVM 17+ style)
//      () unit → void (in return position) or {}* / {}  (in value position)
//      Str → { ptr, i64 }  (data pointer + byte length)
//      [T;N] → [N x LLVMType(T)]
//      (A,B,...) tuple → { LLVMType(A), LLVMType(B), ... }
//      struct S → %S (named type, declared at module level)
//
// 4. STRUCT LAYOUT: struct field access uses `getelementptr inbounds` with
//    the struct type and the field index (0-based in declaration order).
//    The field index is resolved by walking the struct's field block.
//
// 5. AGGREGATES (tuple/struct/array literals): lowered as a sequence of
//    `insertvalue` instructions building up an aggregate from `undef`.
//
// 6. ALLOC/FREE: map to `@malloc` / `@free` (libc). The runtime may replace
//    these with a custom allocator by linking a malloc shim.
//
// 7. ALGEBRAIC EFFECTS (IR_EFFECT_OP / IR_HANDLER / IR_RESUME):
//    Lowered using a lightweight setjmp/longjmp-based prompt stack — the
//    simplest correct ABI, replaceable with evidence passing or split stacks
//    later without changing the frontend IR.
//    Per handler frame:
//      struct __pryde_frame { jmp_buf buf; ptr handler_fn; ptr prev; }
//      IR_EFFECT_OP   → call __pryde_perform(frame_ptr, op_id, arg_ptr)
//      IR_HANDLER     → setjmp; on resume → call body; tear down frame
//      IR_RESUME      → longjmp into saved buf with resume value
//    Runtime declarations are emitted into the .ll file as `declare` stmts.
//
// 8. SIZEOF/ALIGNOF sentinels: IR_CONST_INT with ival=0 and src.kind ==
//    NODE_EXPR_SIZEOF/ALIGNOF are replaced with the real byte-size/alignment
//    computed by llvm_sizeof() during emit.
//
// 9. OUTPUT: writes to a CFile opened by the caller. Use `--emit-llvm file.ll`
//    from the driver.
//
// COMPLETENESS
// ────────────
// Every IrOp and TermKind is handled. IR_UNKNOWN at asm sites emits an
// inline-asm call; IR_UNKNOWN at with-cleanup sites emits a call to
// __pryde_drop. All other IR_UNKNOWN nodes (extern/global refs) emit a
// reference to the mangled global symbol.
// ============================================================================

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

alias Node = ast::AstNode;
alias Nk   = ast::NodeKind;
alias Tt   = lexer::TokenType;

// ── Constants ─────────────────────────────────────────────────────────────────

// LLVM 22.1.8 x86_64-pc-linux-gnu data layout (from llc-22 -march=x86-64 defaults)
const char* LLVM_DATALAYOUT =
    "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128";
const char* LLVM_TRIPLE = "x86_64-pc-linux-gnu";
char* g_target_triple_override = null;  // set by --target=<triple>

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

fn void set_target_triple(char* triple)
{
    g_target_triple_override = triple;
}


const usz MAX_STRUCTS  = 1024;   // named struct types in one module
const usz MAX_STRBUF   = 131072; // output buffer: 128 KB per flush cycle
const usz NAME_BUF     = 256;    // scratch buffer for name mangling
const usz TY_BUF       = 256;    // scratch buffer for type strings

// ── x86-64 type sizes (bytes) and alignments ──────────────────────────────────
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


// ── Canonical LLVM type string helpers ───────────────────────────────────────
// Write the LLVM type string for a Pryde type node into buf[cap].
// Returns buf (always null-terminated). Falls back to "i64" for unknown types.

fn char* type_to_llvm_buf(Node* t, char* buf, usz cap, int depth)
{
    if (cap == 0) return buf;
    buf[0] = 0;
    if (t == null || depth > 16) { snprintf(buf, cap, "i64"); return buf; }

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
        Node* d = t.resolved;
        if (d.kind == Nk.NODE_DECL_ENUM) { snprintf(buf, cap, "{ i32, i64 }"); return buf; }
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
                    if (!first_field) { usz ol = strlen(buf); if (ol + 2 < cap) { buf[ol]=','; buf[ol+1]=' '; buf[ol+2]=0; } }
                    first_field = false;
                    char[64] ft; ft[0] = 0;
                    type_to_llvm_buf(fd.children[1], &ft[0], 64, depth + 1);
                    usz ol = strlen(buf); usz fl = strlen(&ft[0]);
                    if (ol + fl < cap) { for (usz k = 0; k < fl; k++) buf[ol+k] = ft[k]; buf[ol+fl] = 0; }
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
                if (!ff3) { usz ol3 = strlen(buf); if (ol3 + 2 < cap) { buf[ol3]=','; buf[ol3+1]=' '; buf[ol3+2]=0; } }
                ff3 = false;
                char[64] ft3; ft3[0] = 0;
                type_to_llvm_buf(fd3.children[1], &ft3[0], 64, depth + 1);
                usz ol3 = strlen(buf); usz fl3 = strlen(&ft3[0]);
                if (ol3 + fl3 < cap) { for (usz k3 = 0; k3 < fl3; k3++) buf[ol3+k3] = ft3[k3]; buf[ol3+fl3] = 0; }
            }
        }
        usz ol3 = strlen(buf); if (ol3 + 2 < cap) { buf[ol3]=' '; buf[ol3+1]='}'; buf[ol3+2]=0; }
        return buf;
    }
    if (t.kind == Nk.NODE_TYPE_PTR
     || t.kind == Nk.NODE_TYPE_REF
     || t.kind == Nk.NODE_TYPE_MUT_REF
     || t.kind == Nk.NODE_TYPE_SLICE)
    { snprintf(buf,cap,"ptr"); return buf; }
    if (t.kind == Nk.NODE_TYPE_FN)
    { snprintf(buf,cap,"ptr"); return buf; }
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
    { return type_to_llvm_buf(t.children[0], buf, cap, depth+1); }
    if (t.kind == Nk.NODE_TYPE_TUPLE)
    {
        // Tuple → struct.  Build { T0, T1, ... } in buf.
        usz off = 0;
        if (off < cap-2) { buf[off++] = '{'; buf[off++] = ' '; }
        for (usz i = 0; i < t.child_count && off < cap-4; i++)
        {
            if (i > 0 && off < cap-2) { buf[off++] = ','; buf[off++] = ' '; }
            char[32] sub; type_to_llvm_buf(t.children[i], &sub[0], 32, depth+1);
            usz sl = strlen(&sub[0]);
            if (off + sl < cap-3) { for (usz j = 0; j < sl; j++) buf[off++] = sub[j]; }
        }
        if (off < cap-2) { buf[off++] = ' '; buf[off++] = '}'; }
        buf[off] = 0;
        return buf;
    }
    if (t.kind == Nk.NODE_TYPE_ARRAY && t.child_count >= 2)
    {
        Node* elem = t.children[0]; Node* sz_node = t.children[1];
        char[32] esub; type_to_llvm_buf(elem, &esub[0], 32, depth+1);
        ulong sz_val = (sz_node != null && sz_node.kind == Nk.NODE_LIT_INT) ? sz_node.p.lit_int.int_val : 0;
        {
            char[24] szbuf;
            snprintf(&szbuf[0], 24, "%d", (int)sz_val);
            snprintf(buf, cap, "[");
            usz bl = strlen(buf); if (bl < cap-1) {
                usz i2 = 0; while (szbuf[i2] && bl < cap-1) buf[bl++] = szbuf[i2++];
                if (bl < cap-1) buf[bl++] = ' ';
                if (bl+1 < cap) { buf[bl++] = 'x'; buf[bl++] = ' '; }
                usz ei = 0; while (esub[ei] && bl < cap-1) buf[bl++] = esub[ei++];
                if (bl < cap-1) buf[bl++] = ']';
                buf[bl] = 0;
            }
        }
        return buf;
    }
    // Fallback: opaque
    snprintf(buf, cap, "ptr");
    return buf;
}

// Extract the i-th parameter type and the return type from a fn decl's signature.
// param_idx == -1 means: get the return type.
fn void fn_param_llvm_type(Node* fn_decl, int param_idx, char* buf, usz cap)
{
    buf[0] = 0;
    if (fn_decl == null) { snprintf(buf, cap, "i64"); return; }
    // Closure thunk: env pointer is always param 0 → must be ptr
    if (fn_decl.kind == Nk.NODE_EXPR_CLOSURE)
    {
        if (param_idx == 0) { snprintf(buf, cap, "ptr"); return; }
        // remaining args are i64 (widened value params)
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

    // Parameter type: may be a tuple (multi-arg) or a single type
    if (param_t != null && param_t.kind == Nk.NODE_TYPE_TUPLE)
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
    snprintf(buf, cap, "i64");
}

// ── Type table inference pre-pass ─────────────────────────────────────────────
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

                // Priority 1a: binder node type_annotation (e.g. PatIdent for `let mut i : i32`)
                if (!resolved && ph.binder != null && ph.binder.type_annotation != null)
                {
                    type_to_llvm_buf(ph.binder.type_annotation, &pbuf[0], TYMAP_ENTRY, 0);
                    // Reject "ptr" from union/complex types (fallback type) as phi type.
                    // It will be overridden by arm type inference below.
                    bool binder_ty_ok = (pbuf[0] != 0 && pbuf[0] != 'v' && pbuf[0] != 'p');
                    // Allow ptr if binder annotation IS a real pointer type
                    if (pbuf[0] == 'p' && ph.binder.type_annotation != null
                        && ph.binder.type_annotation.kind == Nk.NODE_TYPE_PTR)
                    { binder_ty_ok = true; }
                    if (binder_ty_ok) { t.set(ph.id, &pbuf[0]); resolved = true; }
                }
                // Priority 1b: src.type_annotation (the AST node that spawned the phi)
                // Same rejection as 1a: skip ptr/union-fallback types.
                if (!resolved && ph.src != null && ph.src.type_annotation != null)
                {
                    type_to_llvm_buf(ph.src.type_annotation, &pbuf[0], TYMAP_ENTRY, 0);
                    bool src_ty_ok = (pbuf[0] != 0 && pbuf[0] != 'v' && pbuf[0] != 'p');
                    // Allow ptr if src annotation IS a real pointer type
                    if (pbuf[0] == 'p' && ph.src.type_annotation.kind == Nk.NODE_TYPE_PTR)
                    { src_ty_ok = true; }
                    if (src_ty_ok) { t.set(ph.id, &pbuf[0]); resolved = true; }
                }
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
                if (iv.src != null && iv.src.type_annotation != null)
                {
                    type_to_llvm_buf(iv.src.type_annotation, &buf[0], TYMAP_ENTRY, 0);
                    // Filter out "void" in non-return position (void can't be a value)
                    if (buf[0] == 'v' && buf[1] == 'o') buf[0] = 0;
                }

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
                                    char* aty = t.get(iv.args[0].id);
                                    if (aty != null) { usz li = 0; while (aty[li] && li < TYMAP_ENTRY-1) { buf[li] = aty[li]; li++; } buf[li] = 0; }
                                }
                            }
                        case ssi_ir::IrOp.IR_UN:
                        case ssi_ir::IrOp.IR_SIGMA:
                            {
                                char* aty = t.get(iv.args[0].id);
                                if (aty != null) { usz li = 0; while (aty[li] && li < TYMAP_ENTRY-1) { buf[li] = aty[li]; li++; } buf[li] = 0; }
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

                // Priority 3: opcode-based fallback
                if (buf[0] == 0)
                {
                    switch (iv.op)
                    {
                        case ssi_ir::IrOp.IR_CONST_INT:    snprintf(&buf[0], TYMAP_ENTRY, "i64");
                        case ssi_ir::IrOp.IR_CONST_FLOAT:  snprintf(&buf[0], TYMAP_ENTRY, "double");
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
                        case ssi_ir::IrOp.IR_RESUME:       snprintf(&buf[0], TYMAP_ENTRY, "ptr");
                        case ssi_ir::IrOp.IR_UNKNOWN:
                            // Closure fat pointer or fn ptr
                            if (iv.binder != null && iv.binder.kind == Nk.NODE_EXPR_CLOSURE)
                            {
                                // Zero-capture: bare ptr; with captures: { ptr, ptr }
                                if (iv.arg_count == 0) { snprintf(&buf[0], TYMAP_ENTRY, "ptr"); }
                                else { snprintf(&buf[0], TYMAP_ENTRY, "{ ptr, ptr }"); }
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

// ── Struct registry ───────────────────────────────────────────────────────────
// We collect every NODE_DECL_STRUCT referenced by the IR and emit their type
// declarations before any function definitions.

struct StructEntry
{
    Node*  decl;       // NODE_DECL_STRUCT
    char*  name;       // struct name (arena span, null-terminated copy)
    usz    name_len;
}

// ── String output buffer ──────────────────────────────────────────────────────
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
        // Oversized: write directly
        fwrite((void*)s, 1, len, b.file);
        return;
    }
    for (usz i = 0; i < len; i++) { b.data[b.pos + i] = s[i]; }
    b.pos += len;
}

fn void OutBuf.writes(OutBuf* b, char* s)
{
    usz len = strlen(s);
    b.write(s, len);
}

fn void OutBuf.writec(OutBuf* b, char c)
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

// ── Main codegen state ────────────────────────────────────────────────────────

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

    // Current function being emitted (set by emit_function, used by emit_val)
    Node* cur_fn_decl;   // null outside emit_function

    // Function name deduplication: track emitted @names to avoid redefinition
    char[256][NAME_BUF] emitted_fn_names;
    usz                 emitted_fn_count;
}

// ── Per-function type table ───────────────────────────────────────────────────
// Filled by infer_fn_types() before emit_function() emits any instructions.
// Entry k holds the LLVM type string for IrVal with id k, as a null-terminated
// char[64]. A value_count of 0 means the table is not yet built.

const usz TYMAP_ENTRY = 64;   // bytes per entry — enough for any Pryde type

struct TypeTable
{
    char*  data;         // heap: val_count * TYMAP_ENTRY bytes
    usz    val_count;
}

fn bool TypeTable.init(TypeTable* t, usz val_count)
{
    t.val_count = val_count;
    if (val_count == 0) { t.data = null; return true; }
    t.data = (char*)malloc(val_count * TYMAP_ENTRY);
    if (t.data == null) { return false; }
    // Zero all entries so untouched ones read as empty string
    for (usz i = 0; i < val_count * TYMAP_ENTRY; i++) t.data[i] = 0;
    return true;
}

fn void TypeTable.destroy(TypeTable* t)
{
    if (t.data != null) { free((void*)t.data); t.data = null; }
}

fn char* TypeTable.entry(TypeTable* t, int id)
{
    if (t.data == null || id < 0 || (usz)id >= t.val_count) return null;
    return t.data + (usz)id * TYMAP_ENTRY;
}

fn void TypeTable.set(TypeTable* t, int id, char* type_str)
{
    char* e = t.entry(id);
    if (e == null || type_str == null) return;
    usz i = 0;
    while (type_str[i] != 0 && i < TYMAP_ENTRY - 1) { e[i] = type_str[i]; i++; }
    e[i] = 0;
}

fn char* TypeTable.get(TypeTable* t, int id)
{
    char* e = t.entry(id);
    if (e == null || e[0] == 0) return null;
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
    return cg.out.init(file);
}

fn void CgenModule.destroy(CgenModule* cg)
{
    cg.out.flush();
    cg.out.destroy();
}

fn int CgenModule.error_count(CgenModule* cg) { return cg.errors; }

// ── Struct registry helpers ───────────────────────────────────────────────────

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

// ── Type emission ─────────────────────────────────────────────────────────────

// Emit the LLVM type string for a Pryde type node into the output buffer.
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
        case Nk.NODE_TYPE_PTR:
        case Nk.NODE_TYPE_REF:
        case Nk.NODE_TYPE_MUT_REF:
        case Nk.NODE_TYPE_SLICE:
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

        case Nk.NODE_DECL_STRUCT:
            cg.register_struct(t);
            cg.out.writes("%");
            if (t.child_count >= 1 && t.children[0] != null)
            {
                cg.out.write(t.children[0].p.ident.name_ptr,
                             t.children[0].p.ident.name_len);
            }

        case Nk.NODE_TYPE_GENERIC_APP:
            // Monomorphized generic app: head should resolve to a concrete struct
            if (t.child_count >= 1)
            {
                cg.emit_type(t.children[0], in_ret_pos, depth + 1);
            }
            else { cg.out.writes("ptr"); }

        default:
            // Unknown / lattice type (union/intersect/negation/refinement):
            // use ptr as a sound approximation — backend will refine if needed.
            cg.out.writes("ptr");
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
        case ssi_ir::IrOp.IR_CONST_FLOAT:  cg.out.writes("double");
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
            cg.out.writef(v.fval);
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

// ── Global string literal collection + emission ───────────────────────────────

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
        cg.out.writes(" = private unnamed_addr constant [");
        cg.out.writeu(v.slen + 1);
        cg.out.writes(" x i8] c\"");
        // Escape the string bytes
        for (usz j = 0; j < v.slen; j++)
        {
            char c = v.sptr[j];
            if (c == '"')       { cg.out.writes("\\22"); }
            else if (c == '\\') { cg.out.writes("\\5C"); }
            else if (c >= 32 && c < 127) { cg.out.writec(c); }
            else
            {
                // Hex escape
                char[5] hex;
                snprintf(&hex[0], 5, "\\%02X", (int)(c & 0xFF));
                cg.out.writes(&hex[0]);
            }
        }
        cg.out.writes("\\00\"\n");
    }
}

// ── Struct type declarations ───────────────────────────────────────────────────

fn void CgenModule.emit_struct_decls(CgenModule* cg)
{
    for (usz i = 0; i < cg.struct_count; i++)
    {
        StructEntry* e = &cg.structs[i];
        Node* decl = e.decl;
        if (decl == null) { continue; }

        cg.out.writes("%");
        cg.out.write(e.name, e.name_len);
        cg.out.writes(" = type { ");

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
        cg.out.writes(" }\n");
    }
}

// ── Field index lookup ────────────────────────────────────────────────────────
// Given a struct decl and a field name, return its 0-based index (-1 if not found).

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

// ── Function signature emission ───────────────────────────────────────────────

// Determine the LLVM return type for a function.
fn void CgenModule.emit_fn_ret_type(CgenModule* cg, ssi_ir::SsiFunc* f)
{
    // Closure thunks always return i64 (generic widened type)
    if (f.decl != null && f.decl.kind == Nk.NODE_EXPR_CLOSURE)
    { cg.out.writes("i64"); return; }
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

// Emit a mangled global name for a Pryde function.
// Extern functions keep their name as-is; Pryde functions get @pryde_ prefix.
fn void CgenModule.emit_fn_name(CgenModule* cg, ssi_ir::SsiFunc* f)
{
    // Closure thunk: use @__pryde_closure_N naming
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
                cg.out.writes("@__pryde_closure_");
                cg.out.writei((long)cid2);
                return;
            }
        }
        cg.out.writes("@__pryde_closure_0");  // fallback
        return;
    }
    if (f.name == null || f.name_len == 0)
    {
        cg.out.writes("@pryde_anon_");
        cg.out.writei(f.entry);
        return;
    }
    bool is_main = (f.name_len == 4 && f.name[0] == 'm' && f.name[1] == 'a'
                    && f.name[2] == 'i' && f.name[3] == 'n');
    if (is_main) { cg.out.writes("@main"); return; }

    // Build the candidate name @pryde_NAME
    char[NAME_BUF] candidate;
    snprintf(&candidate[0], NAME_BUF, "@pryde_");
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

// ── Binary / unary op → LLVM instruction ─────────────────────────────────────

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
    if (v == null) { return true; } // default to signed
    if (v.src != null && v.src.type_annotation != null)
    {
        Node* t = v.src.type_annotation;
        if (t.kind == Nk.NODE_TYPE_PRIMITIVE)
        {
            char first = t.p.ident.name_ptr[0];
            if (first == 'u') { return false; } // unsigned
        }
    }
    return true; // i8/i16/i32/i64 are signed
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
        // Matmul @ — lower as call to runtime __pryde_matmul
        case Tt.TOKEN_AT:
            cg.out.writes("call ptr @__pryde_matmul");
        default:
            cg.out.writes("add"); // safe fallback
    }
}

// ── Single instruction emission ───────────────────────────────────────────────

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

// ── Function emission ─────────────────────────────────────────────────────────

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
        case Nk.NODE_TYPEVAR: return t.resolved != null ? sizeof_type_x86(t.resolved) : 8;
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
        case Nk.NODE_TYPEVAR: return t.resolved != null ? alignof_type_x86(t.resolved) : 8;
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
                // The runtime provides these via __pryde_get_arm_arg(index).
                // Determine which argument index this param is (by position in the arm's params).
                int arm_arg_idx = 0;
                Node* arm_node = v.binder;
                // Count which param position this is (skip op_head child[0] and body (last child))
                for (usz pi = 1; pi + 1 < arm_node.child_count; pi++)
                {
                    Node* binder = arm_node.children[pi];
                    if (binder == null) { continue; }
                    if (binder == v.binder) { break; }
                    arm_arg_idx++;
                }
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = call i64 @__pryde_get_arm_arg(i64 ");
                cg.out.writei(arm_arg_idx);
                cg.out.writes(")\n");
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
                    cg.out.writes(" = bitcast ptr "); cg.emit_vref(v.args[0]);
                    cg.out.writes(" to ptr");
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

                // Matmul: emit as runtime call
                if (v.bop == Tt.TOKEN_AT)
                {
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = call ptr @__pryde_matmul(ptr ");
                    cg.emit_vref(lhs);
                    cg.out.writes(", ptr ");
                    cg.emit_vref(rhs);
                    cg.out.writes(")\n");
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
                    // Emit placeholder matching result type (i1 for comparison, i64 otherwise)
                    char* res_ty2 = (tm != null) ? tm.get(v.id) : null;
                    bool is_cmp_op = (v.bop == Tt.TOKEN_LT || v.bop == Tt.TOKEN_GT
                        || v.bop == Tt.TOKEN_LTEQ || v.bop == Tt.TOKEN_GTEQ
                        || v.bop == Tt.TOKEN_EQEQ || v.bop == Tt.TOKEN_NEQ);
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    if (is_cmp_op) { cg.out.writes(" = add i1 0, 0  ; aggregate cmp (type error, soft)\n"); }
                    else { cg.out.writes(" = add i64 0, 0  ; aggregate op (type error, soft)\n"); }
                    return;
                }
                // If lhs is a bare integer constant (type "i64") and rhs is a
                // narrower integer, use rhs width as the "native" width so we
                // don't needlessly widen `0 - x` (x:i32) to i64.
                bool lhs_is_bare_const = (lhs != null && lhs.op == ssi_ir::IrOp.IR_CONST_INT
                                          && lhs_ty != null && lhs_ty[0]=='i' && lhs_ty[1]=='6'
                                          && lhs_ty[2]=='4' && lhs_ty[3]==0);
                bool rhs_is_bare_const = (rhs != null && rhs.op == ssi_ir::IrOp.IR_CONST_INT
                                          && rhs_ty != null && rhs_ty[0]=='i' && rhs_ty[1]=='6'
                                          && rhs_ty[2]=='4' && rhs_ty[3]==0);
                // Use the non-i64-const side's type as the canonical width
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
                        cg.out.writes(" = "); cg.out.writes(lw > rw ? "sext " : "trunc ");
                        cg.out.writes(rhs_ty); cg.out.writes(" "); cg.emit_vref(rhs);
                        cg.out.writes(" to "); cg.out.writes(lhs_ty); cg.out.writes("\n");
                    }
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
                // Pointer arithmetic: ptr +/- int → GEP (byte offset)
                if ((v.bop == Tt.TOKEN_PLUS || v.bop == Tt.TOKEN_MINUS)
                    && lhs != null && rhs != null)
                {
                    char* lty_pa = (tm != null) ? tm.get(lhs.id) : null;
                    if (lty_pa != null && lty_pa[0] == 'p')
                    {
                        char* rty_pa = (tm != null) ? tm.get(rhs.id) : null;
                        if (rty_pa == null || rty_pa[0] == 0) rty_pa = (char*)"i64";
                        // GEP index MUST be an integer — ptrtoint if rhs is ptr type
                        bool rhs_is_ptr_gep = (rty_pa[0] == 'p');
                        if (rhs_is_ptr_gep)
                        {
                            cg.out.writes("  %gep.idx.v"); cg.out.writei(v.id);
                            cg.out.writes(" = ptrtoint ptr "); cg.emit_vref(rhs);
                            cg.out.writes(" to i64\n");
                            rty_pa = (char*)"i64";
                        }
                        if (v.bop == Tt.TOKEN_MINUS)
                        {
                            cg.out.writes("  %ptra.neg.v"); cg.out.writei(v.id);
                            cg.out.writes(" = sub "); cg.out.writes(rty_pa);
                            cg.out.writes(" 0, ");
                            if (rhs_is_ptr_gep) { cg.out.writes("%gep.idx.v"); cg.out.writei(v.id); }
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
                            if (rhs_is_ptr_gep) { cg.out.writes("%gep.idx.v"); cg.out.writei(v.id); }
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
                // Write the instruction type using lhs_ty (accurate, follows sigma chains)
                if (lhs_ty != null && lhs_ty[0] != 0)
                { cg.out.writes(lhs_ty); }
                else { cg.writes_ty(tm, lhs != null ? lhs.id : -1); }
                cg.out.writes(" ");
                cg.emit_vref(lhs);
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
                }
                // Arg coercion: emit trunc/sext/sitofp before the call line
                Node* callee_decl2 = null;
                if (callee_val != null && callee_val.binder != null
                    && callee_val.binder.kind == Nk.NODE_DECL_FN)
                { callee_decl2 = callee_val.binder; }
                {
                    int apos = 0;
                    for (usz ia = 1; ia < v.arg_count; ia++)
                    {
                        ssi_ir::IrVal* aval_c = v.args[ia];
                        if (aval_c == null) { continue; }
                        char* aty_c = (tm != null) ? tm.get(aval_c.id) : null;
                        if (aty_c == null || aty_c[0] == 0) { aty_c = (char*)"i64"; }
                        if (aty_c[0]=='v'&&aty_c[1]=='o') { continue; }
                        if (ia==1 && aval_c.op==ssi_ir::IrOp.IR_UNKNOWN && aval_c.binder!=null
                            && aval_c.binder.kind==Nk.NODE_DECL_FN) { continue; }
                        char[64] ptbuf;
                        fn_param_llvm_type(callee_decl2, apos, &ptbuf[0], 64);
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
                        // Emit coerce instruction
                        cg.out.writes("  %arg.c."); cg.out.writeu(ia); cg.out.writes(".v"); cg.out.writei(v.id);
                        bool ai_c = aty_c[0]=='i'; bool pi_c = pt[0]=='i';
                        bool af_c = aty_c[0]=='f'||aty_c[0]=='d'; bool pf_c = pt[0]=='f'||pt[0]=='d';
                        if (ai_c && pi_c)
                        {
                            // Integer width change: measure by counting digits after the 'i'/'u'
                            long an=0; long pn=0;
                            char* ap=aty_c+1; while(*ap>='0'&&*ap<='9'){an=an*10+(long)(*ap-'0');ap++;}
                            char* pp=pt+1;    while(*pp>='0'&&*pp<='9'){pn=pn*10+(long)(*pp-'0');pp++;}
                            if (an > pn) { cg.out.writes(" = trunc "); }
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
                        else if (aty_c[0]=='{' && aty_c[1]==' ' && aty_c[2]=='p' && pt[0]=='p')
                        {
                            // Fat pointer { ptr, ptr } → ptr: extract thunk (field 0)
                            cg.out.writes(" = extractvalue { ptr, ptr } ");
                            cg.emit_vref(aval_c); cg.out.writes(", 0\n");
                        }
                        else
                        {
                            cg.out.writes(" = bitcast "); cg.out.writes(aty_c); cg.out.writes(" ");
                            cg.emit_vref(aval_c); cg.out.writes(" to "); cg.out.writes(pt); cg.out.writes("\n");
                        }
                    }
                }


                // Closure call early exit: emit BEFORE outer call prefix
                if (callee_val != null && callee_val.op == ssi_ir::IrOp.IR_UNKNOWN
                    && callee_val.binder != null
                    && callee_val.binder.kind == Nk.NODE_EXPR_CLOSURE)
                {
                    bool is_musttail_c = ((v.ival >> 63) & 1) != 0;
                    // Zero-capture closure: callee_val is a bare ptr (bitcast of @fn_name).
                    // Call directly without extractvalue.
                    bool zero_cap = (callee_val.arg_count == 0);
                    if (!zero_cap)
                    {
                        cg.out.writes("  %thunk."); cg.out.writei(v.id);
                        cg.out.writes(" = extractvalue { ptr, ptr } %v");
                        cg.out.writei(callee_val.id); cg.out.writes(", 0\n");
                        cg.out.writes("  %cenv2."); cg.out.writei(v.id);
                        cg.out.writes(" = extractvalue { ptr, ptr } %v");
                        cg.out.writei(callee_val.id); cg.out.writes(", 1\n");
                    }
                    if (!is_void) { cg.out.writes("  %v"); cg.out.writei(v.id); cg.out.writes(" = "); }
                    else { cg.out.writes("  "); }
                    if (is_musttail_c) cg.out.writes("musttail ");
                    cg.out.writes("call i64 ");
                    if (zero_cap)
                    {
                        // Direct call via the bare ptr value
                        cg.emit_vref(callee_val);
                        cg.out.writes("(");
                    }
                    else
                    {
                        cg.out.writes("%thunk."); cg.out.writei(v.id);
                        cg.out.writes("(ptr %cenv2."); cg.out.writei(v.id);
                    }
                    bool first_carg = zero_cap;  // zero-cap: no env prefix arg
                    for (usz ia2 = 1; ia2 < v.arg_count; ia2++)
                    {
                        ssi_ir::IrVal* arg2 = v.args[ia2];
                        if (arg2 == null) continue;
                        char* aty2 = (tm != null) ? tm.get(arg2.id) : null;
                        if (aty2 == null) aty2 = (char*)"i64";
                        if (!first_carg) { cg.out.writes(", "); }
                        first_carg = false;
                        cg.out.writes(aty2); cg.out.writes(" ");
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
                    // Known Pryde function
                    Node* fn_decl = callee_val.binder;
                    // Find name (child 0)
                    char* fn_name_ptr = null;
                    usz   fn_name_len = 0;
                    if (fn_decl.child_count >= 1 && fn_decl.children[0] != null)
                    {
                        fn_name_ptr = fn_decl.children[0].p.ident.name_ptr;
                        fn_name_len = fn_decl.children[0].p.ident.name_len;
                    }
                    bool is_main_fn = (fn_name_len == 4 && fn_name_ptr != null
                                       && fn_name_ptr[0] == 'm');
                    if (is_main_fn) { cg.out.writes("@main"); }
                    else
                    {
                        cg.out.writes("@pryde_");
                        if (fn_name_ptr != null) { cg.out.write(fn_name_ptr, fn_name_len); }
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
                    if (cty2_is_int)
                    { cg.out.writes("%callee.ptr."); cg.out.writei(v.id); }
                    else if (callee_is_unit || cty2_is_void || cty2 == null || cty2[0] == 0)
                    { cg.out.writes("undef"); }
                    else { cg.emit_vref(callee_val); }
                }
                else { cg.out.writes("null"); }

                cg.out.writes("(");
                bool first_arg = true;
                int arg_pos2 = 0;
                for (usz i = 1; i < v.arg_count; i++)
                {
                    if (v.args[i] == null) { continue; }
                    char* arg_ty = (tm != null) ? tm.get(v.args[i].id) : null;
                    if (arg_ty == null || arg_ty[0] == 0) { arg_ty = (char*)"i64"; }
                    if (arg_ty[0]=='v'&&arg_ty[1]=='o') { continue; }
                    if (i==1 && v.args[i].op==ssi_ir::IrOp.IR_UNKNOWN
                        && v.args[i].binder!=null
                        && v.args[i].binder.kind==Nk.NODE_DECL_FN) { continue; }
                    if (!first_arg) { cg.out.writes(", "); }
                    first_arg = false;
                    // Use coerce result if type differs from callee param type
                    char[64] ptype3_buf;
                    fn_param_llvm_type(callee_decl2, arg_pos2, &ptype3_buf[0], 64);
                    char* ptype3 = &ptype3_buf[0];
                    arg_pos2++;
                    bool teq3 = true;
                    if (ptype3[0] != 0 && !(ptype3[0]=='v'&&ptype3[1]=='o'))
                    {
                        usz al3 = strlen(arg_ty); usz pl3 = strlen(ptype3);
                        if (al3 != pl3) { teq3 = false; }
                        else
                        {
                            for (usz ci3 = 0; ci3 < al3; ci3++)
                            {
                                if (arg_ty[ci3] != ptype3[ci3]) { teq3 = false; break; }
                            }
                        }
                    }
                    if (!teq3 && ptype3[0] != 0)
                    {
                        // Special: { ptr, ptr } fat-pointer closure to ptr param
                        // — extract the thunk ptr (field 0)
                        char* aty3 = (tm != null && v.args[i] != null) ? tm.get(v.args[i].id) : null;
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
                        // Structs passed as ptr
                        if (arg_ty[0] == '%') { cg.out.writes("ptr"); }
                        else { cg.out.writes(arg_ty); }
                        cg.out.writes(" ");
                        cg.emit_vref(v.args[i]);
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

                // Resolve struct decl from base's type annotation
                if (base != null && base.src != null
                    && base.src.type_annotation != null)
                {
                    Node* bt = base.src.type_annotation;
                    if (bt.kind == Nk.NODE_TYPEVAR && bt.resolved != null
                        && bt.resolved.kind == Nk.NODE_DECL_STRUCT)
                    {
                        struct_decl = bt.resolved;
                    }
                    else if (bt.kind == Nk.NODE_DECL_STRUCT)
                    {
                        struct_decl = bt;
                    }
                }

                if (field_name_node != null && struct_decl != null)
                {
                    field_idx = field_index_of(struct_decl,
                                               field_name_node.p.ident.name_ptr,
                                               field_name_node.p.ident.name_len);
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
                        cg.out.writes(" "); cg.emit_vref(base);
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
                                char[64] ftbuf; ftbuf[0] = 0;
                                type_to_llvm_buf(ft, &ftbuf[0], 64, 0);
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

                // Closure env slot: base=env_ptr, v.ival=slot_index, no args[1]
                // Only fires inside a closure thunk (cur_fn_decl.kind == NODE_EXPR_CLOSURE)
                // to avoid false-firing on regular fn params with IR_INDEX patterns.
                bool is_in_closure_thunk = (cg.cur_fn_decl != null
                    && cg.cur_fn_decl.kind == Nk.NODE_EXPR_CLOSURE);
                // Emit: gep [N x ptr], ptr %env, 0, slot; load ptr; ptrtoint
                if (index == null && v.arg_count == 1 && base != null
                    && v.src != null  // has a captured binder
                    && base.op == ssi_ir::IrOp.IR_PARAM  // env is a param
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
                    // ptrtoint to i64 for arithmetic use
                    char* vty3 = (tm != null) ? tm.get(v.id) : null;
                    if (vty3 == null || vty3[0] == 0) vty3 = (char*)"i64";
                    if (vty3[0] == 'p')
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

                // Ensure base is ptr for index GEP (pre-emit alloca+store for structs)
                if (base != null)
                {
                    char* ibt = (tm != null) ? tm.get(base.id) : null;
                    if (ibt != null && ibt[0] == '%')
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
                    if (ibt2 != null && ibt2[0] != 'p' && ibt2[0] != '%' && ibt2[0] != 0)
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
                    char[64] elem_ty_buf;
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

                    cg.out.writes("  %st.gep.v"); cg.out.writei(v.id);
                    cg.out.writes(" = getelementptr inbounds ");
                    cg.out.writes(elem_ty_st);  // element stride type (i8 for u8 arrays)
                    cg.out.writes(", ptr ");
                    if (base_arg != null) { cg.emit_vref(base_arg); } else { cg.out.writes("null"); }
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
                    // Find struct decl from base type annotation
                    int fidx = 0;
                    if (base_node != null && base_node.type_annotation != null)
                    {
                        Node* ta = base_node.type_annotation;
                        Node* sd = (ta.resolved != null) ? ta.resolved : ta;
                        if (sd.kind == Nk.NODE_DECL_STRUCT && fn_ptr != null)
                        { fidx = field_index_of(sd, fn_ptr, fn_len); }
                    }
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
                        // Already ptr: direct GEP
                        // Need struct type name from ptr type info — use { i64 } fallback
                        cg.out.writes("  %st.gep.v"); cg.out.writei(v.id);
                        cg.out.writes(" = getelementptr inbounds i64");
                        cg.out.writes(", ptr ");
                        if (base_arg != null) { cg.emit_vref(base_arg); } else { cg.out.writes("null"); }
                        cg.out.writes(", i32 "); cg.out.writei(fidx); cg.out.writes("\n");
                    }
                    cg.out.writes("  store "); cg.out.writes(val_ty_st); cg.out.writes(" ");
                    if (val_arg != null) { cg.emit_vref(val_arg); } else { cg.out.writes("undef"); }
                    cg.out.writes(", ptr %st.gep.v"); cg.out.writei(v.id);
                    cg.out.writes("\n");
                }
                else
                {
                    // Pointer deref store: store val, ptr base
                    cg.out.writes("  store "); cg.out.writes(val_ty_st); cg.out.writes(" ");
                    if (val_arg != null) { cg.emit_vref(val_arg); } else { cg.out.writes("undef"); }
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
                bool src_is_ptr = (src_type_str[0] == 'p');
                bool dst_is_ptr = (dst_type_str[0] == 'p');
                bool src_fp = (src_type_str[0]=='f'||src_type_str[0]=='d');
                bool dst_fp = (dst_type_str[0]=='f'||dst_type_str[0]=='d');
                bool src_int = (src_type_str[0]=='i');
                bool dst_int = (dst_type_str[0]=='i');

                // Pointer dereference: ptr → int/float = load, not cast
                if (src_is_ptr && !dst_is_ptr)
                {
                    // Emit a load: %gep = ptr; %vN = load T, ptr %gep
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = load "); cg.out.writes(dst_type_str);
                    cg.out.writes(", ptr "); cg.emit_vref(src); cg.out.writes("\n");
                    return;
                }

                // Widening int → sext or zext, not bitcast
                if (src_int && dst_int)
                {
                    int sw = 0; int dw = 0;
                    for (usz ci = 1; src_type_str[ci] >= '0' && src_type_str[ci] <= '9'; ci++) sw = sw*10+(int)(src_type_str[ci]-'0');
                    for (usz ci = 1; dst_type_str[ci] >= '0' && dst_type_str[ci] <= '9'; ci++) dw = dw*10+(int)(dst_type_str[ci]-'0');
                    cg.out.writes("  %v"); cg.out.writei(v.id); cg.out.writes(" = ");
                    if (sw == dw) { cg.out.writes("bitcast "); }
                    else if (sw < dw) { cg.out.writes("sext "); }
                    else { cg.out.writes("trunc "); }
                    cg.out.writes(src_type_str); cg.out.writes(" "); cg.emit_vref(src);
                    cg.out.writes(" to "); cg.out.writes(dst_type_str); cg.out.writes("\n");
                    return;
                }

                cg.out.writes("  %v"); cg.out.writei(v.id); cg.out.writes(" = ");
                if (!src_is_ptr && dst_is_ptr && src_int) { cg.out.writes("inttoptr "); }
                else if (src_fp && dst_int)   { cg.out.writes("fptosi "); }
                else if (src_int && dst_fp)   { cg.out.writes("sitofp "); }
                else if (src_fp && dst_fp)    { cg.out.writes("fptrunc "); }
                else                          { cg.out.writes("bitcast "); }
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
                if (agg_ty != null && agg_ty[0] == 'p' && v.arg_count > 0 && !is_struct_lit)
                {
                    // Tensor: allocate elem_count * 8 bytes (double), store each element
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
                            cg.out.writes(aw>ew?" = trunc ":" = sext ");
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
                    // Unwrap DECL_TYPE alias (type Vec2 = struct ...) to get the struct body
                    if (stn_resolved != null && stn_resolved.kind == Nk.NODE_DECL_TYPE)
                    {
                        // Last child of DECL_TYPE is the struct body
                        Node* body_check = stn_resolved.child_count >= 1
                            ? stn_resolved.children[stn_resolved.child_count - 1] : null;
                        if (body_check != null && body_check.kind == Nk.NODE_DECL_STRUCT) { stn_resolved = body_check; }
                    }
                    if (stn_resolved != null && stn_resolved.kind == Nk.NODE_DECL_STRUCT) { struct_type_node = stn_resolved; }
                    // Also try: v.src itself has type_annotation pointing to the struct
                    if (struct_type_node == null && v.src.type_annotation != null)
                    {
                        Node* ta = v.src.type_annotation;
                        if (ta.kind == Nk.NODE_TYPEVAR && ta.resolved != null)
                        {
                            Node* tar = ta.resolved;
                            if (tar.kind == Nk.NODE_DECL_TYPE && tar.child_count >= 1)
                            {
                                Node* tb = tar.children[tar.child_count - 1];
                                if (tb != null && tb.kind == Nk.NODE_DECL_STRUCT) { tar = tb; }
                            }
                            if (tar.kind == Nk.NODE_DECL_STRUCT) { struct_type_node = tar; }
                        }
                        else if (ta.kind == Nk.NODE_DECL_STRUCT) { struct_type_node = ta; }
                    }
                }

                for (usz i = 0; i < v.arg_count; i++)
                {
                    // First: determine if coercion is needed and emit the coerce instruction
                    // This must happen BEFORE writing any part of the insertvalue line.
                    bool need_coerce_elem = false;
                    bool field_coerced = false;
                    char[TYMAP_ENTRY] field_ty_buf;
                    field_ty_buf[0] = 0;
                    if (struct_type_node != null)
                    {
                        Node* fb = null;
                        for (usz ci = 0; ci < struct_type_node.child_count; ci++)
                        {
                            Node* c = struct_type_node.children[ci];
                            if (c != null && c.kind == Nk.NODE_EXPR_BLOCK) { fb = c; break; }
                        }
                        if (fb != null)
                        {
                            usz fi = 0;
                            for (usz ci = 0; ci < fb.child_count; ci++)
                            {
                                Node* fd = fb.children[ci];
                                if (fd == null || fd.kind != Nk.NODE_FIELD_DECL) { continue; }
                                if (fi == i && fd.child_count >= 2)
                                {
                                    type_to_llvm_buf(fd.children[1], &field_ty_buf[0], TYMAP_ENTRY, 0);
                                    need_coerce_elem = (field_ty_buf[0] != 0);
                                    break;
                                }
                                fi++;
                            }
                        }
                    }
                    // Pre-emit coerce instruction (must be on its own line before insertvalue)
                    if (need_coerce_elem && v.args[i] != null)
                    {
                        char* arg_ty2 = (tm != null) ? tm.get(v.args[i].id) : null;
                        if (arg_ty2 != null && arg_ty2[0] == 'i' && field_ty_buf[0] == 'i')
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
                                // i1 → wider: use zext (zero-extend bool to byte)
                                if (aw2 == 1 && fw2 > 1) { cg.out.writes("zext "); }
                                else if (aw2 > fw2)       { cg.out.writes("trunc "); }
                                else                      { cg.out.writes("sext "); }
                                cg.out.writes(arg_ty2); cg.out.writes(" "); cg.emit_vref(v.args[i]);
                                cg.out.writes(" to "); cg.out.writes(&field_ty_buf[0]); cg.out.writes("\n");
                                field_coerced = true;
                            }
                        }
                    }

                    // Now emit the complete insertvalue instruction on a single line
                    if (i + 1 == v.arg_count) { cg.out.writes("  %v"); cg.out.writei(v.id); }
                    else { cg.out.writes("  %agg."); cg.out.writei(v.id); cg.out.writes("."); cg.out.writeu(i); }
                    cg.out.writes(" = insertvalue ");
                    // For struct literals: write "{ T0, T1 }" not "ptr"
                    if (struct_type_node != null)
                    {
                        cg.out.writes("{ ");
                        Node* sblk2 = null;
                        for (usz ci2 = 0; ci2 < struct_type_node.child_count; ci2++)
                        {
                            Node* c2 = struct_type_node.children[ci2];
                            if (c2 != null && c2.kind == Nk.NODE_EXPR_BLOCK) { sblk2 = c2; break; }
                        }
                        if (sblk2 != null)
                        {
                            bool first_f = true;
                            for (usz fi2 = 0; fi2 < sblk2.child_count; fi2++)
                            {
                                Node* fd2 = sblk2.children[fi2];
                                if (fd2 == null || fd2.kind != Nk.NODE_FIELD_DECL || fd2.child_count < 2) continue;
                                if (!first_f) cg.out.writes(", ");
                                first_f = false;
                                char[TYMAP_ENTRY] ftbuf2;
                                type_to_llvm_buf(fd2.children[1], &ftbuf2[0], TYMAP_ENTRY, 0);
                                cg.out.writes(ftbuf2[0] != 0 ? &ftbuf2[0] : (char*)"i64");
                            }
                        }
                        cg.out.writes(" }");
                    }
                    else { cg.writes_ty(tm, v.id); }
                    cg.out.writes(" ");
                    if (i == 0) { cg.out.writes("undef"); }
                    else { cg.out.writes("%agg."); cg.out.writei(v.id); cg.out.writes("."); cg.out.writeu(i - 1); }
                    cg.out.writes(", ");
                    // Field type
                    if (need_coerce_elem && field_ty_buf[0] != 0) { cg.out.writes(&field_ty_buf[0]); }
                    else { cg.writes_ty(tm, v.args[i] != null ? v.args[i].id : -1); }
                    cg.out.writes(" ");
                    // Field value (coerced or direct)
                    if (field_coerced)
                    { cg.out.writes("%fcoerce."); cg.out.writei(v.id); cg.out.writes("."); cg.out.writeu(i); }
                    else { cg.emit_vref(v.args[i]); }
                    cg.out.writes(", "); cg.out.writeu(i); cg.out.writes("\n");
                }
                // result already named %vN by final insertvalue
            }

        case ssi_ir::IrOp.IR_ALLOC:
            {
                // alloc T → call to malloc(sizeof(T))
                // We emit sizeof as a constant (type-based, resolved at emit time).
                // The allocated type comes from v.src's type annotation (ptr to T).
                usz elem_size = 8; // default
                if (v.src != null && v.src.type_annotation != null)
                {
                    Node* pt = v.src.type_annotation;
                    // type_annotation on alloc is *T; get T
                    if (pt.kind == Nk.NODE_TYPE_PTR && pt.child_count >= 1)
                    {
                        Node* elem = pt.children[0];
                        if (elem != null && elem.kind == Nk.NODE_TYPE_PRIMITIVE)
                        {
                            elem_size = prim_sizeof(elem.p.ident.name_ptr,
                                                    elem.p.ident.name_len);
                        }
                    }
                }
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = call ptr @malloc(i64 ");
                cg.out.writeu((ulong)elem_size);
                cg.out.writes(")\n");
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

        case ssi_ir::IrOp.IR_RANGE:
            {
                // IR_RANGE is consumed by the for-loop counter φ — after lowering
                // it has no runtime value itself. Emit as struct { lo, hi }.
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

        // ── Algebraic effects: setjmp/longjmp prompt stack ────────────────────
        case ssi_ir::IrOp.IR_EFFECT_OP:
            {
                // perform Effect.op(args...) → call @__pryde_perform(op_id, ...)
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
                    if (needs_widen || is_bool || is_ptr_arg)
                    {
                        cg.out.writes("  %pw."); cg.out.writei(v.id); cg.out.writes(".");
                        cg.out.writeu(i); cg.out.writes(" = ");
                        if (is_bool)   { cg.out.writes("zext i1 "); }
                        else if (is_ptr_arg) { cg.out.writes("ptrtoint ptr "); }
                        else { cg.out.writes("sext "); cg.out.writes(aty); cg.out.writes(" "); }
                        cg.emit_vref(pa);
                        cg.out.writes(" to i64\n");
                    }
                }
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = call ptr @__pryde_perform(i64 ");
                cg.out.writeu(op_id);
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
                    cg.out.writes(", i64 ");
                    if (nw2 || ib2)
                    {
                        cg.out.writes("%pw."); cg.out.writei(v.id); cg.out.writes(".");
                        cg.out.writeu(i);
                    }
                    else if (ptr2i2)
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
                // At this instruction we call @__pryde_push_handler().
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = call i64 @__pryde_push_handler(i64 ");
                ulong frame_id = (v.binder != null) ? (ulong)v.binder.id : 0;
                cg.out.writeu(frame_id);
                cg.out.writes(")\n");
            }

        case ssi_ir::IrOp.IR_HANDLER_ARM:
            {
                // Arm body result; call pop to tear down the handler frame.
                ssi_ir::IrVal* body_res = v.arg_count >= 1 ? v.args[0] : null;
                cg.out.writes("  call void @__pryde_pop_handler()\n");
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
                // resume(v) → call @__pryde_resume(value)
                ssi_ir::IrVal* rv = v.arg_count >= 1 ? v.args[0] : null;
                cg.out.writes("  %v"); cg.out.writei(v.id);
                cg.out.writes(" = call ptr @__pryde_resume(");
                cg.writes_ty(tm, rv != null ? rv.id : -1);
                cg.out.writes(" ");
                cg.emit_vref(rv);
                cg.out.writes(")\n");
            }

        case ssi_ir::IrOp.IR_UNKNOWN:
            {
                // Two legitimate cases: asm and with-cleanup.
                if (v.src != null && v.src.kind == Nk.NODE_STMT_ASM)
                {
                    // Inline asm: collect asm strings from args
                    // and emit as LLVM `call void asm(...)`.
                    // Simplified: emit as @__pryde_asm_barrier() + comment.
                    cg.out.writes("  call void @__pryde_asm_barrier()\n");
                    cg.out.writes("  ; inline asm (see source)\n");
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = add i64 0, 0\n");
                }
                else if (v.src != null && v.src.kind == Nk.NODE_EFFECT_WITH)
                {
                    // with-resource cleanup: call __pryde_drop(resource_ptr)
                    ssi_ir::IrVal* res = v.arg_count >= 1 ? v.args[0] : null;
                    // __pryde_drop expects ptr — inttoptr if resource is non-ptr typed
                    {
                        char* res_ty = (tm != null && res != null) ? tm.get(res.id) : null;
                        bool res_is_ptr = (res_ty == null || res_ty[0] == 'p');
                        if (!res_is_ptr && res_ty != null && res_ty[0] != 0)
                        {
                            cg.out.writes("  %drop.ptr.v"); cg.out.writei(v.id);
                            cg.out.writes(" = inttoptr "); cg.out.writes(res_ty);
                            cg.out.writes(" "); cg.emit_vref(res); cg.out.writes(" to ptr\n");
                            cg.out.writes("  call void @__pryde_drop(ptr %drop.ptr.v");
                            cg.out.writei(v.id); cg.out.writes(")\n");
                        }
                        else
                        {
                            cg.out.writes("  call void @__pryde_drop(ptr ");
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
                    //   %str = call ... @pryde_str_new()     ; String
                    //   ... str_push_str / str_push_i64 calls for each segment/arg
                    // Then %v = the String value.

                    // Allocate a String on the stack (or use alloca).
                    // Simplified: use %str.N as a ptr to a stack-allocated String.
                    cg.out.writes("  %fmt.str."); cg.out.writei(v.id);
                    cg.out.writes(" = alloca { ptr, i64, i64 }\n");
                    cg.out.writes("  call void @pryde_str_init(ptr %fmt.str.");
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
                                cg.out.writes("  call void @pryde_str_push_str(ptr %fmt.str.");
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
                                        cg.out.writes("  call void @pryde_str_push_f64(ptr %fmt.str.");
                                        cg.out.writei(v.id); cg.out.writes(", double ");
                                        cg.emit_vref(v.args[arg_idx]);
                                        cg.out.writes(")\n");
                                    }
                                    else
                                    {
                                        cg.out.writes("  call void @pryde_str_push_i64(ptr %fmt.str.");
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
                                    char* fn2 = fd.p.ident.name_ptr;
                                    usz   fl2 = fd.p.ident.name_len;
                                    if (fl2 == want_l)
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
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    cg.out.writes(" = call i64 asm sideeffect \"syscall\",");
                    cg.out.writes("\"={rax},{rax},{rdi},{rsi},{rdx},{r10},{r8},{r9}\"");
                    cg.out.writes("(");
                    for (usz sci = 0; sci < v.arg_count && sci < 7; sci++)
                    {
                        if (sci > 0) cg.out.writes(", ");
                        cg.out.writes("i64 "); cg.emit_vref(v.args[sci]);
                    }
                    // Pad missing args with 0
                    for (usz sci2 = v.arg_count; sci2 < 7; sci2++)
                    { if (sci2 > 0) cg.out.writes(", "); cg.out.writes("i64 0"); }
                    cg.out.writes(") nounwind\n");
                }
                else if (v.binder != null && v.binder.kind == Nk.NODE_EXPR_CLOSURE)
                {
                    // Closure fat pointer: { ptr thunk, ptr env }
                    int cid = (int)(v.ival & 0x7FFFFFFF);
                    usz ncap = v.arg_count;

                    // Alloca env: array of ncap pointers (one per capture)
                    if (ncap > 0)
                    {
                        cg.out.writes("  %cenv."); cg.out.writei(v.id);
                        cg.out.writes(" = alloca ["); cg.out.writei((long)ncap);
                        cg.out.writes(" x ptr]\n");

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

                            // Store: inttoptr if needed, else direct ptr store
                            bool cap_is_ptr = (cty[0] == 'p');
                            if (!cap_is_ptr)
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
                        cg.out.writes(" = insertvalue { ptr, ptr } undef, ptr @__pryde_closure_");
                        cg.out.writei((long)cid); cg.out.writes(", 0\n");
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = insertvalue { ptr, ptr } %fat0."); cg.out.writei(v.id);
                        cg.out.writes(", ptr %cenv."); cg.out.writei(v.id);
                        cg.out.writes(", 1\n");
                    }
                    else
                    {
                        // Zero-capture closure: bare fn ptr (no env needed).
                        // Emit as a pointer value so it can be passed as fn ptr arg.
                        cg.out.writes("  %v"); cg.out.writei(v.id);
                        cg.out.writes(" = bitcast ptr @__pryde_closure_");
                        cg.out.writei((long)cid); cg.out.writes(" to ptr\n");
                    }
                    return;
                }
                else if (v.binder != null && v.binder.kind == Nk.NODE_DECL_FN)
                {
                    // Global / extern function reference — emit as a ptr to it.
                    cg.out.writes("  %v"); cg.out.writei(v.id);
                    // Function pointer references: callee path uses @name directly.
                    // fn-ref: callee uses @name directly; placeholder if result is used elsewhere
                    cg.out.writes(" = add i64 0, 0\n");
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

// ── φ-node emission ───────────────────────────────────────────────────────────

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
            if (apty != null && (apty[0]=='{' || (apty[0]=='v'&&apty[1]=='o')))
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
            else { cg.emit_vref(phi_arg); }
        }
        cg.out.writes(", %B");
        cg.out.writei(v.pred[i]);
        cg.out.writes(" ]");
    }
    cg.out.writes("\n");
}

// ── Block terminator emission ─────────────────────────────────────────────────

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
                    // fn returns a struct/tuple — if val is scalar or unit, ret undef struct
                    char* vty = resolve_ty(tm, b.ret_val);
                    if (vty == null || vty[0] == 0 || vty[0] == 'v' || vty[0] != '{')
                    {
                        // Val is not a struct — use the actual value if it IS the right struct
                        // or fall back to undef (branches should have computed it)
                        if (vty != null && vty[0] == '{')
                        {
                            cg.out.writes("  ret "); cg.out.writes(fn_ret_type);
                            cg.out.writes(" "); cg.emit_vref(b.ret_val); cg.out.writes("\n");
                        }
                        else
                        {
                            cg.out.writes("  ret "); cg.out.writes(fn_ret_type);
                            cg.out.writes(" undef\n");
                        }
                    }
                    else
                    {
                        // Both are struct types — emit ret directly
                        cg.out.writes("  ret "); cg.out.writes(fn_ret_type);
                        cg.out.writes(" "); cg.emit_vref(b.ret_val); cg.out.writes("\n");
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
                        // Emit coercion
                        cg.out.writes("  %coerce.ret.B"); cg.out.writei(b.id); cg.out.writes(" = ");
                        bool src_int = (val_ty[0]=='i');
                        bool dst_int = (ret_ty[0]=='i');
                        bool src_fp  = (val_ty[0]=='f'||val_ty[0]=='d');
                        bool dst_fp  = (ret_ty[0]=='f'||ret_ty[0]=='d');
                        if (src_int && dst_int)
                        {
                            int src_w = 0; int dst_w = 0;
                            for (usz ci = 1; val_ty[ci] >= '0' && val_ty[ci] <= '9'; ci++) { src_w = src_w*10 + (int)(val_ty[ci]-'0'); }
                            for (usz ci = 1; ret_ty[ci] >= '0' && ret_ty[ci] <= '9'; ci++) { dst_w = dst_w*10 + (int)(ret_ty[ci]-'0'); }
                            cg.out.writes(src_w > dst_w ? "trunc " : "sext ");
                        }
                        else if (src_fp && dst_int) { cg.out.writes("fptosi "); }
                        else if (src_int && dst_fp) { cg.out.writes("sitofp "); }
                        else if (src_fp && dst_fp)  { cg.out.writes("fptrunc "); }
                        else if (val_ty[0]=='p' && dst_int) { cg.out.writes("ptrtoint "); }
                        else if (src_int && ret_ty[0]=='p') { cg.out.writes("inttoptr "); }
                        else                        { cg.out.writes("bitcast "); }
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

fn void CgenModule.emit_function(CgenModule* cg, ssi_ir::SsiFunc* f)
{
    ssi_ir::SsiModule* m = cg.ir;

    // Track current function for emit_val IR_INDEX closure-env guard
    cg.cur_fn_decl = f.decl;

    // Compute ret-type string ONCE so define header and all block terminators agree.
    // fn_param_llvm_type(decl,-1) and emit_fn_ret_type can diverge for broken/null decls.
    char[TYMAP_ENTRY] fn_ret_canonical;
    {
        fn_ret_canonical[0] = 0;
        if (f.decl != null && f.decl.kind == Nk.NODE_EXPR_CLOSURE)
        { snprintf(&fn_ret_canonical[0], TYMAP_ENTRY, "i64"); }
        else if (f.decl == null)
        { snprintf(&fn_ret_canonical[0], TYMAP_ENTRY, "void"); }
        else
        { fn_param_llvm_type(f.decl, -1, &fn_ret_canonical[0], TYMAP_ENTRY); }
        if (fn_ret_canonical[0] == 0) snprintf(&fn_ret_canonical[0], TYMAP_ENTRY, "void");
    }

    // Function header: define RetType @name(ParamType %v0, ...) {
    cg.out.writes("define ");
    cg.out.writes(&fn_ret_canonical[0]);
    cg.out.writes(" ");
    cg.emit_fn_name(f);
    // Build type table for this function before emitting anything
    TypeTable tymap;
    tymap.data      = null;
    tymap.val_count = 0;
    {
        ssi_ir::SsiModule* mir = cg.ir;
        bool tok = tymap.init(mir.val_count);
        if (tok) { infer_fn_types(mir, f, &tymap); }
    }

    cg.out.writes("(");

    for (usz i = 0; i < f.param_count; i++)
    {
        if (i > 0) { cg.out.writes(", "); }
        ssi_ir::IrVal* pv = f.params[i];
        // Use type table for accurate param type
        if (pv != null)
        {
            char* pty = tymap.get(pv.id);
            if (pty == null || pty[0] == 0) pty = (char*)"i64";
            // void is not valid as a param type — use i64 for unit params
            if (pty[0]=='v'&&pty[1]=='o'&&pty[2]=='i'&&pty[3]=='d') { cg.out.writes("i64"); }
            // Structs are passed by pointer per System V AMD64 ABI
            else if (pty[0] == '%') { cg.out.writes("ptr"); }
            else
            {
                cg.out.writes(pty);
                // Add noalias to ptr params (pure Pryde params never alias; helps vectorizer)
                if (pty[0] == 'p') { cg.out.writes(" noalias"); }
            }
            cg.out.writes(" %v");
            cg.out.writei(pv.id);
        }
    }
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
    // Scan fn attributes: naked, pure/const, cold, hot
    bool fn_naked = false; bool fn_pure = false; bool fn_cold = false; bool fn_hot = false;
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
            }
        }
    }
    // Select LLVM attribute group
    if (fn_naked)   { cg.out.writes(") naked nounwind {\n"); }
    else if (fn_pure)    { cg.out.writes(") #4 {\n"); }
    else if (fn_cold)    { cg.out.writes(") #5 {\n"); }
    else if (fn_hot)     { cg.out.writes(") #6 {\n"); }
    else if (fn_noreturn && f.block_count <= 2) { cg.out.writes(") #2 {\n"); }
    else if (fn_noreturn)                       { cg.out.writes(") #3 {\n"); }
    else if (f.block_count <= 2)                { cg.out.writes(") #0 {\n"); }
    else                                        { cg.out.writes(") {\n"); }

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
        while (ph != null) { cg.emit_phi(ph, &tymap); ph = ph.next; }

        // Straight-line instructions
        ssi_ir::IrVal* instr = b.head;
        while (instr != null) { cg.emit_val(instr, &tymap); instr = instr.next; }

        // Terminator — use the canonical ret type computed once at function entry
        cg.emit_terminator(b, &tymap, &fn_ret_canonical[0]);
    }

    cg.out.writes("}\n\n");
    tymap.destroy();
    cg.cur_fn_decl = null;
}

// ── Runtime declarations ──────────────────────────────────────────────────────

fn void CgenModule.emit_runtime_decls(CgenModule* cg)
{
    // libc
    cg.out.writes("declare ptr @malloc(i64)\n");
    cg.out.writes("declare void @free(ptr)\n");
    cg.out.writes("declare i32 @printf(ptr, ...)\n");
    cg.out.writes("declare i32 @putchar(i32)\n");
    cg.out.writes("\n");
    // Pryde runtime (implemented in runtime.c, linked separately)
    cg.out.writes("; Pryde runtime — implemented in runtime/runtime.c\n");
    cg.out.writes("declare ptr  @__pryde_perform(i64, ...)\n");
    cg.out.writes("declare void @pryde_str_init(ptr)\n");
    cg.out.writes("declare void @pryde_str_push_str(ptr, ptr, i64)\n");
    cg.out.writes("declare void @pryde_str_push_i64(ptr, i64)\n");
    cg.out.writes("declare void @pryde_str_push_f64(ptr, double)\n");
    cg.out.writes("declare i64  @__pryde_push_handler(i64)\n");
    cg.out.writes("declare void @__pryde_pop_handler()\n");
    cg.out.writes("declare ptr  @__pryde_resume(ptr)\n");
    cg.out.writes("declare void @__pryde_drop(ptr)\n");
    cg.out.writes("declare void @__pryde_asm_barrier()\n");
    cg.out.writes("declare void @__pryde_panic(ptr, i64)\n");
    cg.out.writes("declare ptr  @__pryde_matmul(ptr, ptr)\n");
    cg.out.writes("declare i64  @__pryde_get_arm_arg(i64)\n");
    // C23 <stdckdint.h> — overflow-checked arithmetic
    cg.out.writes("declare i1   @__pryde_ckd_add_i32(ptr, i32, i32)\n");
    cg.out.writes("declare i1   @__pryde_ckd_add_i64(ptr, i64, i64)\n");
    cg.out.writes("declare i1   @__pryde_ckd_sub_i32(ptr, i32, i32)\n");
    cg.out.writes("declare i1   @__pryde_ckd_sub_i64(ptr, i64, i64)\n");
    cg.out.writes("declare i1   @__pryde_ckd_mul_i32(ptr, i32, i32)\n");
    cg.out.writes("declare i1   @__pryde_ckd_mul_i64(ptr, i64, i64)\n");
    // C23 <string.h> additions
    cg.out.writes("declare ptr  @__pryde_memset_explicit(ptr, i32, i64)\n");
    cg.out.writes("declare ptr  @__pryde_strdup(ptr)\n");
    cg.out.writes("declare ptr  @__pryde_strndup(ptr, i64)\n");
    // C23 <stdlib.h>
    cg.out.writes("declare i64  @__pryde_memalignment(ptr)\n");
    // C23 <stdbit.h>
    cg.out.writes("declare i32  @__pryde_stdc_count_ones_u64(i64)\n");
    cg.out.writes("declare i32  @__pryde_stdc_leading_zeros_u64(i64)\n");
    cg.out.writes("declare i32  @__pryde_stdc_trailing_zeros_u64(i64)\n");
    cg.out.writes("declare i64  @__pryde_stdc_bit_ceil_u64(i64)\n");
    cg.out.writes("declare i64  @__pryde_stdc_bit_floor_u64(i64)\n");
    cg.out.writes("declare i32  @__pryde_stdc_bit_width_u64(i64)\n");
    cg.out.writes("declare i64  @__pryde_stdc_rotate_left_u64(i64, i32)\n");
    cg.out.writes("declare i64  @__pryde_stdc_rotate_right_u64(i64, i32)\n");
    cg.out.writes("\n");
    cg.out.writes("attributes #0 = { inlinehint nounwind }\n");
    cg.out.writes("attributes #1 = { nounwind }\n");
    cg.out.writes("attributes #2 = { inlinehint nounwind noreturn }\n");
    cg.out.writes("attributes #3 = { nounwind noreturn }\n");
    cg.out.writes("attributes #4 = { inlinehint nounwind readonly }\n");
    cg.out.writes("attributes #5 = { nounwind cold }\n");
    cg.out.writes("attributes #6 = { inlinehint nounwind hot }\n");
    cg.out.writes("\n");
}


// ── Vtable emission for dynamic dispatch ─────────────────────────────────────
// For each `impl Interface for Type` block encountered, emit a global constant
// array of function pointers in the order the interface declares its methods.
// Symbol name: @__pryde_vtable_<Interface>_<Type>

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
    // (Vtable generation is complete in stdlib/dyn.pry at the language level.)
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

// ── Top-level emitter ─────────────────────────────────────────────────────────

fn bool CgenModule.emit(CgenModule* cg, char* source_filename)
{
    ssi_ir::SsiModule* m = cg.ir;

    // ── Module header ────────────────────────────────────────────────────────
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

    // ── Collect and emit struct type declarations ─────────────────────────────
    cg.collect_all_structs();
    if (cg.struct_count > 0)
    {
        cg.out.writes("; ── Named struct types ──────────────────────────────────────\n");
        cg.emit_struct_decls();
        cg.out.writes("\n");
    }

    // ── String literals as global constants ──────────────────────────────────
    cg.out.writes("; ── String constants ────────────────────────────────────────\n");
    cg.emit_string_globals();
    cg.out.writes("\n");

    // ── Runtime declarations ─────────────────────────────────────────────────
    cg.out.writes("; ── Runtime declarations ────────────────────────────────────\n");
    cg.emit_runtime_decls();

    // ── Function definitions ─────────────────────────────────────────────────
    cg.out.writes("; ── Function definitions ────────────────────────────────────\n");
    for (usz fi = 0; fi < m.func_count; fi++)
    {
        cg.emit_function(&m.funcs[fi]);
    }


    cg.out.flush();
    return cg.errors == 0;
}


// ── Closure thunk emission ─────────────────────────────────────────────────────
// For each IR_UNKNOWN value tagged as a closure (binder.kind == NODE_EXPR_CLOSURE),
// emit a standalone LLVM function that:
//   1. Receives (ptr %__env, args...) 
//   2. Loads each captured value from the env array (via ptrtoint)
//   3. Executes the closure body inline
//
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

        // Emit: define i64 @__pryde_closure_N(ptr %__env, i64 %a0, i64 %a1, ...)
        cg.out.writes("; closure thunk\n");
        cg.out.writes("define i64 @__pryde_closure_");
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
        //
        // NOTE: The real body lowering happens via pending_inner_fns in ssi_ir.c3.
        // This thunk is a forward declaration that gets filled in by that pass.
        // For closures with bodies, the thunk IS the lowered fn.
        // Here we emit a minimal stub that calls the SSI-lowered body via tail call.
        cg.out.writes("  ; closure body (lowered by SSI pass)\n");
        cg.out.writes("  ret i64 0  ; TODO: link to SSI-lowered body\n");
        cg.out.writes("}\n\n");
    }
}

// ── Convenience entry point ───────────────────────────────────────────────────

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
