/*
 * test_lexer_main.c — C harness for the Pride self-hosted lexer (lexer.pie → lexer.o)
 *
 * LLVM lowers structs > 16 bytes via a hidden sret pointer (first hidden arg).
 * Token  { i32, ptr, i64, i32, i32 } = 32 bytes → sret
 * Lexer  { ptr, i64, i64, i32, i32, ptr, i32, i32, i32 } = 56 bytes → sret
 *
 * So the ABI becomes:
 *   pride_lexer_new(Lexer* sret, u8* src, i64 len)
 *   pride_lex_next (Token* sret, Lexer* lex)
 *   pride_lexer_destroy(Lexer* lex)   -- returns void, no sret
 *   pride_tok_name(i32 kind) -> ptr   -- returns ptr, no sret
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* ── Token struct: LLVM { i32, ptr, i64, i32, i32 } with natural alignment ─ */
typedef struct {
    int32_t  kind;          /* offset 0 */
    int32_t  _pad0;         /* offset 4 — natural alignment padding for ptr */
    uint8_t* start;         /* offset 8 */
    int64_t  len;           /* offset 16 */
    int32_t  line;          /* offset 24 */
    int32_t  col;           /* offset 28 */
} PrideToken;               /* sizeof = 32 */

/* ── Lexer struct: { ptr, i64, i64, i32, i32, ptr, i32, i32, i32 } ─────── */
typedef struct {
    uint8_t* src;           /* offset 0 */
    int64_t  src_len;       /* offset 8 */
    int64_t  pos;           /* offset 16 */
    int32_t  line;          /* offset 24 */
    int32_t  col;           /* offset 28 */
    uint8_t* indent_stack;  /* offset 32 */
    int32_t  indent_top;    /* offset 40 */
    int32_t  pending_kind;  /* offset 44 */
    int32_t  pending_count; /* offset 48 */
    int32_t  _pad1;         /* offset 52 */
} PrideLexer;               /* sizeof = 56 */

/* ── Pride-compiled function ABI (sret conventions) ─────────────────────── */
/* Token is > 16 bytes → returned via hidden sret pointer (first arg in C)  */
extern void pride_lexer_new   (PrideLexer* sret, const uint8_t* src, int64_t len);
extern void pride_lexer_destroy(PrideLexer* lex);
extern void pride_lex_next    (PrideToken* sret, PrideLexer* lex);
extern const char* pride_tok_name(int32_t kind);

#define TOK_EOF 1

int main(int argc, char** argv)
{
    const char* src_str = NULL;
    int         free_src = 0;

    if (argc >= 2) {
        FILE* f = fopen(argv[1], "rb");
        if (!f) { fprintf(stderr, "Cannot open: %s\n", argv[1]); return 1; }
        fseek(f, 0, SEEK_END);
        long fsz = ftell(f);
        rewind(f);
        char* buf = (char*)malloc((size_t)(fsz + 1));
        if (!buf) { fputs("OOM\n", stderr); return 1; }
        fread(buf, 1, (size_t)fsz, f);
        buf[fsz] = '\0';
        fclose(f);
        src_str  = buf;
        free_src = 1;
        fprintf(stderr, "[pride_lexer] source: %s  (%ld bytes)\n", argv[1], fsz);
    } else {
        src_str = "fn add : (i32, i32) -> i32\n  | (a, b) -> a + b\n\nlet x : i32 = 42i32\n";
        fprintf(stderr, "[pride_lexer] source: <inline test>\n");
    }

    int64_t src_len = (int64_t)strlen(src_str);

    /* Construct lexer */
    PrideLexer lex;
    memset(&lex, 0, sizeof(lex));
    pride_lexer_new(&lex, (const uint8_t*)src_str, src_len);

    fprintf(stderr, "[pride_lexer] lexer.src=%p src_len=%lld pos=%lld line=%d col=%d\n",
            (void*)lex.src, (long long)lex.src_len, (long long)lex.pos,
            lex.line, lex.col);

    /* Tokenise */
    int tok_count = 0;
    for (;;) {
        PrideToken tok;
        memset(&tok, 0, sizeof(tok));
        pride_lex_next(&tok, &lex);
        tok_count++;

        const char* name = pride_tok_name(tok.kind);

        char text[80] = {0};
        if (tok.start && tok.len > 0 && tok.len < 78) {
            memcpy(text, tok.start, (size_t)tok.len);
            text[tok.len] = '\0';
            for (int k = 0; k < (int)tok.len; k++)
                if ((unsigned char)text[k] < 32) text[k] = '.';
        }

        printf("[%4d]  %3d:%-3d  kind=%-3d  %-22s  `%s`\n",
               tok_count, tok.line, tok.col, tok.kind,
               name ? name : "???", text);

        if (tok.kind == TOK_EOF) break;
        if (tok_count > 100000) {
            fprintf(stderr, "Too many tokens\n"); break;
        }
    }

    pride_lexer_destroy(&lex);
    if (free_src) free((void*)src_str);
    fprintf(stderr, "[pride_lexer] total tokens: %d\n", tok_count);
    return 0;
}
