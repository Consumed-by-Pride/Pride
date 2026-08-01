// ============================================================================
// pfront_source.c3 — source maps, spans, UTF-8, rendered diagnostics (part 6)
// ----------------------------------------------------------------------------
// Professional front ends do not report "line 41, col 7" and stop. They own a
// SourceMap so that any byte offset can be turned back into a file, a line, a
// column measured in codepoints (not bytes), and a rendered snippet with a
// caret under the offending span.
//
// This module provides:
//   * SourceFile / SourceMap — global byte-offset space across all loaded files
//   * Line index             — binary search from offset to line, built once
//   * UTF-8 decoding         — correct column arithmetic for non-ASCII source
//   * Span                   — half-open [start, end) byte range, mergeable
//   * Renderer               — GCC/rustc-style diagnostic output with snippets
//   * Fix-it hints           — machine-applicable suggested edits
//
// Everything downstream (parser, resolver, analyses) records Spans; only this
// module knows how to turn them into human output. That separation is what
// makes the diagnostics reusable by an LSP server later.
// ============================================================================

module pfront_source;

import pfront_core;

extern fn void* malloc(usz size);
extern fn void  free(void* ptr);
extern fn int   printf(char* fmt, ...);

const usz MAX_SOURCE_FILES = 1024;
const usz MAX_LINES        = 262144;

// ── Span ────────────────────────────────────────────────────────────────────
// Half-open byte range in the SourceMap's global offset space. A zero-width
// span (start == end) is legal and marks an insertion point, which is what a
// "expected `)` here" fix-it needs.
struct Span
{
    uint start;
    uint end;
}

fn Span span_make(uint s, uint e)
{
    Span sp;
    sp.start = s;
    sp.end = e < s ? s : e;
    return sp;
}

fn Span span_empty()
{
    Span sp;
    sp.start = 0;
    sp.end = 0;
    return sp;
}

fn bool Span.is_empty(Span* s) { return s.end <= s.start; }
fn uint Span.len(Span* s) { return s.end > s.start ? s.end - s.start : 0; }

// Smallest span covering both operands. Used to give a compound expression a
// span that spans its whole subtree rather than just its operator token.
fn Span span_merge(Span a, Span b)
{
    if (a.start == 0 && a.end == 0) { return b; }
    if (b.start == 0 && b.end == 0) { return a; }
    Span r;
    r.start = a.start < b.start ? a.start : b.start;
    r.end   = a.end   > b.end   ? a.end   : b.end;
    return r;
}

fn bool Span.contains(Span* outer, Span inner)
{
    return inner.start >= outer.start && inner.end <= outer.end;
}

// ── UTF-8 ───────────────────────────────────────────────────────────────────
// Column numbers must count codepoints, not bytes, or every diagnostic in a
// file containing a comment with "→" or "σ" points at the wrong place. Pride
// source legitimately contains those: the lexer has unicode operators.
fn int utf8_seq_len(char c)
{
    uint b = (uint)(char)c;
    if ((b & 0x80u) == 0x00u) { return 1; }
    if ((b & 0xE0u) == 0xC0u) { return 2; }
    if ((b & 0xF0u) == 0xE0u) { return 3; }
    if ((b & 0xF8u) == 0xF0u) { return 4; }
    return 1;   // continuation byte or invalid lead: treat as one unit
}

fn bool utf8_is_continuation(char c)
{
    return ((uint)(char)c & 0xC0u) == 0x80u;
}

// Decode one codepoint; advances *pos. Returns 0xFFFD on malformed input so
// that a bad byte never desynchronises the whole render.
fn uint utf8_decode(char* s, usz len, usz* pos)
{
    if (*pos >= len) { return 0; }
    uint b0 = (uint)(char)s[*pos];
    int n = utf8_seq_len(s[*pos]);
    if (n == 1) { *pos = *pos + 1; return b0 & 0x7Fu; }
    if (*pos + (usz)n > len) { *pos = *pos + 1; return 0xFFFDu; }
    uint cp = 0;
    if (n == 2) { cp = b0 & 0x1Fu; }
    else if (n == 3) { cp = b0 & 0x0Fu; }
    else { cp = b0 & 0x07u; }
    for (int i = 1; i < n; i++)
    {
        char c = s[*pos + (usz)i];
        if (!utf8_is_continuation(c)) { *pos = *pos + 1; return 0xFFFDu; }
        cp = (cp << 6) | ((uint)(char)c & 0x3Fu);
    }
    *pos = *pos + (usz)n;
    return cp;
}

// Count codepoints in a byte range — this is the real column computation.
fn uint utf8_count(char* s, usz from, usz to)
{
    uint n = 0;
    usz i = from;
    while (i < to)
    {
        if (!utf8_is_continuation(s[i])) { n = n + 1; }
        i = i + 1;
    }
    return n;
}

// Display width: East Asian wide characters and emoji occupy two cells, which
// matters for caret alignment under a snippet.
fn int utf8_display_width(uint cp)
{
    if (cp == 0) { return 0; }
    if (cp < 0x20u) { return 0; }
    if (cp >= 0x1100u && cp <= 0x115Fu) { return 2; }     // Hangul Jamo
    if (cp >= 0x2E80u && cp <= 0xA4CFu) { return 2; }     // CJK radicals..Yi
    if (cp >= 0xAC00u && cp <= 0xD7A3u) { return 2; }     // Hangul syllables
    if (cp >= 0xF900u && cp <= 0xFAFFu) { return 2; }     // CJK compatibility
    if (cp >= 0xFE30u && cp <= 0xFE6Fu) { return 2; }     // CJK compat forms
    if (cp >= 0xFF00u && cp <= 0xFF60u) { return 2; }     // fullwidth forms
    if (cp >= 0xFFE0u && cp <= 0xFFE6u) { return 2; }
    if (cp >= 0x1F300u && cp <= 0x1F64Fu) { return 2; }   // emoji
    if (cp >= 0x1F900u && cp <= 0x1F9FFu) { return 2; }
    return 1;
}

// ── SourceFile ──────────────────────────────────────────────────────────────
struct SourceFile
{
    char*  path;
    char*  text;
    usz    len;
    uint   base_offset;     // where this file starts in the global space
    uint*  line_starts;     // byte offset of each line start, file-relative
    usz    line_count;
    usz    line_cap;
    bool   has_bom;
    bool   crlf;
}

// Build the line index once. Every later offset->line query is a binary
// search, which keeps diagnostic rendering O(log n) rather than O(n).
fn bool SourceFile.build_lines(SourceFile* f, pfront_core::Arena* arena)
{
    usz cap = 256;
    usz n = f.len / 24;
    if (n > cap) { cap = n; }
    if (cap > MAX_LINES) { cap = MAX_LINES; }
    f.line_starts = (uint*)arena.alloc(cap * 4, 8);
    if (f.line_starts == null) { return false; }
    f.line_cap = cap;
    f.line_count = 0;

    f.line_starts[0] = 0;
    f.line_count = 1;
    for (usz i = 0; i < f.len; i++)
    {
        if (f.text[i] == '\r') { f.crlf = true; }
        if (f.text[i] == '\n')
        {
            if (f.line_count >= f.line_cap)
            {
                usz ncap = f.line_cap * 2;
                if (ncap > MAX_LINES) { ncap = MAX_LINES; }
                if (ncap <= f.line_cap) { break; }
                uint* na = (uint*)arena.alloc(ncap * 4, 8);
                if (na == null) { break; }
                for (usz k = 0; k < f.line_count; k++) { na[k] = f.line_starts[k]; }
                f.line_starts = na;
                f.line_cap = ncap;
            }
            f.line_starts[f.line_count] = (uint)(i + 1);
            f.line_count = f.line_count + 1;
        }
    }
    return true;
}

// Binary search: file-relative byte offset -> 0-based line index.
fn usz SourceFile.line_of(SourceFile* f, uint off)
{
    if (f.line_count == 0) { return 0; }
    usz lo = 0;
    usz hi = f.line_count - 1;
    while (lo < hi)
    {
        usz mid = (lo + hi + 1) / 2;
        if (f.line_starts[mid] <= off) { lo = mid; } else { hi = mid - 1; }
    }
    return lo;
}

fn uint SourceFile.line_start(SourceFile* f, usz line)
{
    if (line >= f.line_count) { return (uint)f.len; }
    return f.line_starts[line];
}

fn uint SourceFile.line_end(SourceFile* f, usz line)
{
    if (line + 1 < f.line_count)
    {
        uint e = f.line_starts[line + 1];
        // Trim the newline (and a preceding CR) from the reported range.
        if (e > 0 && f.text[e - 1] == '\n') { e = e - 1; }
        if (e > 0 && f.text[e - 1] == '\r') { e = e - 1; }
        return e;
    }
    return (uint)f.len;
}

// ── SourceMap ───────────────────────────────────────────────────────────────
struct SourceMap
{
    SourceFile[MAX_SOURCE_FILES] files;
    usz                          file_count;
    uint                         next_offset;
    pfront_core::Arena*          arena;
}

fn void SourceMap.init(SourceMap* m, pfront_core::Arena* a)
{
    m.file_count = 0;
    m.next_offset = 1;      // offset 0 is reserved for "no location"
    m.arena = a;
}

fn int SourceMap.add_file(SourceMap* m, char* path, char* text, usz len)
{
    if (m.file_count >= MAX_SOURCE_FILES) { return -1; }
    SourceFile* f = &m.files[m.file_count];
    f.path = path;
    f.text = text;
    f.len = len;
    f.base_offset = m.next_offset;
    f.line_starts = null;
    f.line_count = 0;
    f.line_cap = 0;
    f.has_bom = len >= 3 && (uint)(char)text[0] == 0xEFu
                         && (uint)(char)text[1] == 0xBBu
                         && (uint)(char)text[2] == 0xBFu;
    f.crlf = false;
    f.build_lines(m.arena);
    m.next_offset = m.next_offset + (uint)len + 1;
    int id = (int)m.file_count;
    m.file_count = m.file_count + 1;
    return id;
}

fn SourceFile* SourceMap.file_of_offset(SourceMap* m, uint off)
{
    for (usz i = 0; i < m.file_count; i++)
    {
        SourceFile* f = &m.files[i];
        if (off >= f.base_offset && off <= f.base_offset + (uint)f.len)
        {
            return f;
        }
    }
    return null;
}

fn SourceFile* SourceMap.file_by_id(SourceMap* m, int id)
{
    if (id < 0 || (usz)id >= m.file_count) { return null; }
    return &m.files[id];
}

// Resolve a global offset into (file, 1-based line, 1-based codepoint column).
struct Loc
{
    SourceFile* file;
    usz  line;      // 0-based index into line_starts
    uint line_no;   // 1-based, for display
    uint col;       // 1-based, codepoints
    uint byte_col;  // 1-based, bytes (useful for LSP UTF-16 conversion)
}

fn Loc SourceMap.locate(SourceMap* m, uint off)
{
    Loc l;
    l.file = null;
    l.line = 0;
    l.line_no = 0;
    l.col = 0;
    l.byte_col = 0;
    SourceFile* f = m.file_of_offset(off);
    if (f == null) { return l; }
    uint rel = off - f.base_offset;
    if (rel > (uint)f.len) { rel = (uint)f.len; }
    usz line = f.line_of(rel);
    uint ls = f.line_start(line);
    l.file = f;
    l.line = line;
    l.line_no = (uint)line + 1;
    l.col = utf8_count(f.text, (usz)ls, (usz)rel) + 1;
    l.byte_col = rel - ls + 1;
    return l;
}

// ── Fix-it hints ────────────────────────────────────────────────────────────
// A machine-applicable edit. An editor can apply these without understanding
// the diagnostic text, which is the whole point of structured suggestions.
enum FixKind : int { FIX_INSERT, FIX_REPLACE, FIX_DELETE }

struct FixIt
{
    FixKind kind;
    Span    span;
    char*   text;       // replacement / insertion text
    char*   label;      // human description
}

const usz MAX_FIXITS = 2048;

struct FixItTable
{
    FixIt[MAX_FIXITS] items;
    usz               count;
}

fn void FixItTable.init(FixItTable* t) { t.count = 0; }

fn int FixItTable.add(FixItTable* t, FixKind k, Span sp, char* text, char* label)
{
    if (t.count >= MAX_FIXITS) { return -1; }
    FixIt* f = &t.items[t.count];
    f.kind = k;
    f.span = sp;
    f.text = text;
    f.label = label;
    int id = (int)t.count;
    t.count = t.count + 1;
    return id;
}

fn char* fix_kind_name(FixKind k)
{
    switch (k)
    {
        case FIX_INSERT:  return "insert";
        case FIX_REPLACE: return "replace";
        case FIX_DELETE:  return "delete";
    }
}

// ── Renderer ────────────────────────────────────────────────────────────────
// Produces the familiar three-part diagnostic:
//     path:line:col: error[E1234]: message
//        41 |     let x = foo(
//           |                ^ expected ')'
//           = help: ...
struct Renderer
{
    SourceMap* map;
    bool       show_snippets;
    bool       color;
    int        context_lines;
    usz        rendered;
    usz        suppressed;
    usz        max_render;
}

fn void Renderer.init(Renderer* r, SourceMap* m)
{
    r.map = m;
    r.show_snippets = true;
    r.color = false;
    r.context_lines = 0;
    r.rendered = 0;
    r.suppressed = 0;
    r.max_render = 200;
}

fn void print_line_text(SourceFile* f, usz line)
{
    uint s = f.line_start(line);
    uint e = f.line_end(line);
    for (uint i = s; i < e; i++)
    {
        char c = f.text[i];
        if (c == '\t') { printf("    "); continue; }
        printf("%c", c);
    }
}

// Caret row: pad with spaces matching the display width of the prefix, then
// draw '^' for the first column and '~' for the rest of the span.
fn void print_caret_row(SourceFile* f, usz line, uint col, uint width)
{
    uint s = f.line_start(line);
    usz i = (usz)s;
    uint printed = 0;
    while (printed + 1 < col && i < f.len)
    {
        char c = f.text[i];
        if (c == '\n') { break; }
        if (c == '\t') { printf("    "); i = i + 1; printed = printed + 1; continue; }
        usz save = i;
        uint cp = utf8_decode(f.text, f.len, &i);
        int w = utf8_display_width(cp);
        for (int k = 0; k < w; k++) { printf(" "); }
        printed = printed + 1;
    }
    printf("^");
    if (width > 1)
    {
        for (uint k = 1; k < width && k < 200; k++) { printf("~"); }
    }
}

fn void Renderer.render(Renderer* r, pfront_core::Diag* d, Span sp)
{
    if (r.rendered >= r.max_render) { r.suppressed = r.suppressed + 1; return; }
    r.rendered = r.rendered + 1;

    char* sev = pfront_core::sev_name(d.sev);
    char prefix = d.sev == pfront_core::Severity.SEV_ERROR ? 'E' : 'W';
    if (d.sev == pfront_core::Severity.SEV_NOTE) { prefix = 'N'; }

    Loc l = r.map.locate(sp.start);
    if (l.file == null)
    {
        char* fp = d.file == null ? (char*)"<input>" : d.file;
        printf("%s:%d:%d: %s[%c%04d]: %s\n", fp, d.line, d.col, sev, prefix, d.code, d.msg);
        if (d.hint != null) { printf("   = help: %s\n", d.hint); }
        return;
    }

    printf("%s:%d:%d: %s[%c%04d]: %s\n",
           l.file.path, (int)l.line_no, (int)l.col, sev, prefix, d.code, d.msg);

    if (r.show_snippets)
    {
        int start_line = (int)l.line - r.context_lines;
        if (start_line < 0) { start_line = 0; }
        for (int ln = start_line; ln < (int)l.line; ln++)
        {
            printf("%6d | ", ln + 1);
            print_line_text(l.file, (usz)ln);
            printf("\n");
        }
        printf("%6d | ", (int)l.line_no);
        print_line_text(l.file, l.line);
        printf("\n");
        printf("       | ");
        uint w = sp.len();
        if (w == 0) { w = 1; }
        print_caret_row(l.file, l.line, l.col, w);
        printf("\n");
    }
    if (d.hint != null) { printf("       = help: %s\n", d.hint); }
}

fn void Renderer.render_fixit(Renderer* r, FixIt* f)
{
    Loc l = r.map.locate(f.span.start);
    if (l.file == null) { return; }
    printf("       = fix (%s) at %s:%d:%d",
           fix_kind_name(f.kind), l.file.path, (int)l.line_no, (int)l.col);
    if (f.text != null) { printf(": `%s`", f.text); }
    if (f.label != null) { printf("  -- %s", f.label); }
    printf("\n");
}

fn void Renderer.summary(Renderer* r)
{
    if (r.suppressed > 0)
    {
        printf("       ... %d further diagnostics suppressed\n", (int)r.suppressed);
    }
}

// ── Source statistics ───────────────────────────────────────────────────────
struct SourceStats
{
    usz files;
    usz total_bytes;
    usz total_lines;
    usz longest_line;
    usz bom_files;
    usz crlf_files;
    usz non_ascii_files;
}

fn void SourceStats.collect(SourceStats* s, SourceMap* m)
{
    s.files = m.file_count;
    s.total_bytes = 0;
    s.total_lines = 0;
    s.longest_line = 0;
    s.bom_files = 0;
    s.crlf_files = 0;
    s.non_ascii_files = 0;
    for (usz i = 0; i < m.file_count; i++)
    {
        SourceFile* f = &m.files[i];
        s.total_bytes = s.total_bytes + f.len;
        s.total_lines = s.total_lines + f.line_count;
        if (f.has_bom) { s.bom_files = s.bom_files + 1; }
        if (f.crlf) { s.crlf_files = s.crlf_files + 1; }
        bool non_ascii = false;
        for (usz k = 0; k < f.len; k++)
        {
            if (((uint)(char)f.text[k] & 0x80u) != 0) { non_ascii = true; break; }
        }
        if (non_ascii) { s.non_ascii_files = s.non_ascii_files + 1; }
        for (usz ln = 0; ln < f.line_count; ln++)
        {
            uint a = f.line_start(ln);
            uint b = f.line_end(ln);
            usz w = (usz)(b - a);
            if (w > s.longest_line) { s.longest_line = w; }
        }
    }
}

fn void SourceStats.report(SourceStats* s)
{
    printf("  source files     : %d\n", (int)s.files);
    printf("  total bytes      : %d\n", (int)s.total_bytes);
    printf("  total lines      : %d\n", (int)s.total_lines);
    printf("  longest line     : %d bytes\n", (int)s.longest_line);
    printf("  BOM / CRLF / utf8: %d / %d / %d files\n",
           (int)s.bom_files, (int)s.crlf_files, (int)s.non_ascii_files);
}
