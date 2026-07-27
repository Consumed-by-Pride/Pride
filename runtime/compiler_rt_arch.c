/* compiler_rt_arch.c — Pride arch ABI stubs */
#include <stdint.h>
#include <stddef.h>
#define ABI __attribute__((weak)) __attribute__((visibility("hidden")))
ABI void __chkstk(void){__asm__ __volatile__("push %%rcx\npush %%rax\ncmp $0x1000,%%rax\nlea 24(%%rsp),%%rcx\njb 1f\n2: sub $0x1000,%%rcx\ntest %%rcx,(%%rcx)\nsub $0x1000,%%rax\ncmp $0x1000,%%rax\nja 2b\n1: sub %%rax,%%rcx\ntest %%rcx,(%%rcx)\npop %%rax\npop %%rcx\nret":::"memory");}
ABI void __chkstk_ms(void){__chkstk();}
ABI void __probestack(void){__asm__ __volatile__("sub %%rax,%%rsp\nmov %%rsp,%%rax\nret":::"memory");}
ABI void __zig_probe_stack(void){__asm__ __volatile__("ret":::"memory");}
ABI int __aeabi_idiv(int n,int d){return n/d;}
ABI unsigned __aeabi_uidiv(unsigned n,unsigned d){return n/d;}
ABI long long __aeabi_ldivmod(long long n,long long d){return n/d;}
ABI unsigned long long __aeabi_uldivmod(unsigned long long n,unsigned long long d){return n/d;}
ABI void*__aeabi_memcpy(void*d,const void*s,size_t n){return __builtin_memcpy(d,s,n);}
ABI void*__aeabi_memcpy4(void*d,const void*s,size_t n){return __builtin_memcpy(d,s,n);}
ABI void*__aeabi_memcpy8(void*d,const void*s,size_t n){return __builtin_memcpy(d,s,n);}
ABI void __aeabi_memset(void*d,size_t n,int c){__builtin_memset(d,c,n);}
ABI void __aeabi_memset4(void*d,size_t n,int c){__builtin_memset(d,c,n);}
ABI void __aeabi_memset8(void*d,size_t n,int c){__builtin_memset(d,c,n);}
ABI void*__aeabi_memmove(void*d,const void*s,size_t n){return __builtin_memmove(d,s,n);}
ABI void*__aeabi_memmove4(void*d,const void*s,size_t n){return __builtin_memmove(d,s,n);}
ABI void*__aeabi_memmove8(void*d,const void*s,size_t n){return __builtin_memmove(d,s,n);}
ABI void __aeabi_memclr(void*d,size_t n){__builtin_memset(d,0,n);}
ABI void __aeabi_memclr4(void*d,size_t n){__builtin_memset(d,0,n);}
ABI void __aeabi_memclr8(void*d,size_t n){__builtin_memset(d,0,n);}
ABI float __aeabi_i2f(int x){return(float)x;} ABI double __aeabi_i2d(int x){return(double)x;}
ABI float __aeabi_l2f(long long x){return(float)x;} ABI double __aeabi_l2d(long long x){return(double)x;}
ABI float __aeabi_ui2f(unsigned x){return(float)x;} ABI double __aeabi_ui2d(unsigned x){return(double)x;}
ABI float __aeabi_ul2f(unsigned long long x){return(float)x;} ABI double __aeabi_ul2d(unsigned long long x){return(double)x;}
ABI int __aeabi_f2iz(float x){return(int)x;} ABI int __aeabi_d2iz(double x){return(int)x;}
ABI long long __aeabi_f2lz(float x){return(long long)x;} ABI long long __aeabi_d2lz(double x){return(long long)x;}
ABI unsigned __aeabi_f2uiz(float x){return(unsigned)x;} ABI unsigned __aeabi_d2uiz(double x){return(unsigned)x;}
ABI unsigned long long __aeabi_f2ulz(float x){return(unsigned long long)x;} ABI unsigned long long __aeabi_d2ulz(double x){return(unsigned long long)x;}
ABI double __aeabi_f2d(float x){return(double)x;} ABI float __aeabi_d2f(double x){return(float)x;}
ABI float __aeabi_fadd(float a,float b){return a+b;} ABI float __aeabi_fsub(float a,float b){return a-b;}
ABI float __aeabi_fmul(float a,float b){return a*b;} ABI float __aeabi_fdiv(float a,float b){return a/b;}
ABI double __aeabi_dadd(double a,double b){return a+b;} ABI double __aeabi_dsub(double a,double b){return a-b;}
ABI double __aeabi_dmul(double a,double b){return a*b;} ABI double __aeabi_ddiv(double a,double b){return a/b;}
ABI int __aeabi_fcmpeq(float a,float b){return a==b;} ABI int __aeabi_fcmplt(float a,float b){return a<b;}
ABI int __aeabi_fcmple(float a,float b){return a<=b;} ABI int __aeabi_fcmpge(float a,float b){return a>=b;}
ABI int __aeabi_fcmpgt(float a,float b){return a>b;} ABI int __aeabi_fcmpun(float a,float b){return __builtin_isunordered(a,b);}
ABI int __aeabi_dcmpeq(double a,double b){return a==b;} ABI int __aeabi_dcmplt(double a,double b){return a<b;}
ABI int __aeabi_dcmple(double a,double b){return a<=b;} ABI int __aeabi_dcmpge(double a,double b){return a>=b;}
ABI int __aeabi_dcmpgt(double a,double b){return a>b;} ABI int __aeabi_dcmpun(double a,double b){return __builtin_isunordered(a,b);}
ABI long long __aeabi_lmul(long long a,long long b){return a*b;}
ABI long long __aeabi_llsl(long long a,int b){return(unsigned long long)a<<b;}
ABI long long __aeabi_llsr(long long a,int b){return(unsigned long long)a>>b;}
ABI long long __aeabi_lasr(long long a,int b){return a>>b;}
ABI int __aeabi_lcmp(long long a,long long b){return(a>b)-(a<b);}
ABI int __aeabi_ulcmp(unsigned long long a,unsigned long long b){return(a>b)-(a<b);}
typedef long double tf_t;
ABI tf_t __addkf3(tf_t a,tf_t b){return a+b;} ABI tf_t __subkf3(tf_t a,tf_t b){return a-b;}
ABI tf_t __mulkf3(tf_t a,tf_t b){return a*b;} ABI tf_t __divkf3(tf_t a,tf_t b){return a/b;}
ABI tf_t __negkf2(tf_t a){return -a;}
ABI int __eqkf2(tf_t a,tf_t b){return a==b?0:1;} ABI int __nekf2(tf_t a,tf_t b){return a!=b?1:0;}
ABI int __ltkf2(tf_t a,tf_t b){return a<b?-1:0;} ABI int __lekf2(tf_t a,tf_t b){return a<=b?0:1;}
ABI int __gtkf2(tf_t a,tf_t b){return a>b?1:0;} ABI int __gekf2(tf_t a,tf_t b){return a>=b?0:-1;}
ABI int __ungtkf2(tf_t a,tf_t b){return __builtin_isgreater(a,b)?1:0;}
ABI tf_t __extendsfkf2(float a){return(tf_t)a;} ABI tf_t __extenddfkf2(double a){return(tf_t)a;}
ABI float __trunckfsf2(tf_t a){return(float)a;} ABI double __trunckfdf2(tf_t a){return(double)a;}
ABI int __fixkfsi(tf_t a){return(int)a;} ABI long long __fixkfdi(tf_t a){return(long long)a;}
ABI unsigned __fixunskfsi(tf_t a){return(unsigned)a;} ABI unsigned long long __fixunskfdi(tf_t a){return(unsigned long long)a;}
ABI tf_t __floatsikf(int a){return(tf_t)a;} ABI tf_t __floatdikf(long long a){return(tf_t)a;}
ABI tf_t __floatunsikf(unsigned a){return(tf_t)a;} ABI tf_t __floatundikf(unsigned long long a){return(tf_t)a;}
ABI tf_t __powikf2(tf_t a,int b){tf_t r=1;int neg=b<0;if(neg)b=-b;while(b){if(b&1)r*=a;a*=a;b>>=1;}return neg?1.0L/r:r;}
ABI long long __divdi3(long long n,long long d){return n/d;} ABI unsigned long long __udivdi3(unsigned long long n,unsigned long long d){return n/d;}
ABI long long __moddi3(long long n,long long d){return n%d;} ABI unsigned long long __umoddi3(unsigned long long n,unsigned long long d){return n%d;}
ABI long long __muldi3(long long a,long long b){return a*b;} ABI long long __negdi2(long long a){return -a;}
ABI int __clzdi2(unsigned long long a){return a?__builtin_clzll(a):64;}
ABI int __ctzdi2(unsigned long long a){return a?__builtin_ctzll(a):64;}
ABI unsigned long long _aulldiv(unsigned long long n,unsigned long long d){return n/d;}
ABI unsigned long long _aullrem(unsigned long long n,unsigned long long d){return n%d;}
ABI long long _alldiv(long long n,long long d){return n/d;} ABI long long _allrem(long long n,long long d){return n%d;} ABI long long _allmul(long long a,long long b){return a*b;}
struct __wlpad{int f;void*p;}; ABI struct __wlpad __wasm_lpad_context={0,0};
ABI void __wasm_personality_v0(void){} ABI void __wasm_lpad_context_init(void){}
ABI int __mulsi3(int a,int b){return a*b;}
/* ── 128-bit ("ti") compiler-rt intrinsics ─────────────────────────────────
 * CRITICAL: these must operate on FULL 128-bit (__int128) values, matching
 * the real libgcc/compiler-rt ABI (`ti_int __divti3(ti_int, ti_int)` etc.
 * per LLVM's actual i128 lowering, which calls these directly for
 * div/rem/udiv/urem on `i128` — see llc's codegen for `udiv i128`/`urem i128`).
 * A prior version of this file declared these with `unsigned long long`
 * (64-bit) parameters/return, which silently TRUNCATES every 128-bit
 * operand to its low 64 bits before doing the division — this is not a
 * degraded fallback, it is SILENT DATA CORRUPTION for any Pride i128/u128
 * arithmetic whose value doesn't fit in 64 bits. Verified against a real
 * LLVM 22 `llc`-compiled `udiv i128`/`urem i128`/`sdiv i128`/`srem i128`
 * call boundary: the truncating stub returned hi=5 lo=0 for
 * (64<<64|5)/3, where the correct 128-bit answer is hi=21
 * lo=6148914691236517207 (cross-checked against Python's bignum division
 * and libgcc's own __udivti3/__divti3/__umodti3 as ground truth).
 *
 * IMPORTANT — do NOT implement these with the native `/` `%` operators on
 * __int128 operands: unlike 64-bit division (which lowers to the hardware
 * `divq`/`idivq` instruction directly), the x86-64 ISA has no 128-bit
 * divide instruction, so GCC/Clang lower a 128-bit `/`/`%` by calling
 * __udivti3/__divti3/__umodti3/__modti3/__udivmodti4 THEMSELVES — i.e. a
 * function named __udivti3 that computes its result via `n / d` on
 * __int128 operands recursively calls itself and stack-overflows
 * immediately. Verified empirically: `objdump`/`-S` of such a naive
 * definition shows a self-call, and running it segfaults on the very first
 * invocation. Implemented below as manual binary long division using only
 * 64-bit-safe operations (shift/compare/subtract), which never triggers
 * this libcall routing.
 *
 * `__multi3` is safe to implement natively (`a*b`) — 128-bit multiply DOES
 * have a native lowering (a pair of 64-bit `mul`/`imul` + adds), so it is
 * not actually reachable from LLVM's i128 codegen at all (`mul i128`
 * lowers inline, no libcall) and doesn't self-recurse either way; kept for
 * any other caller (e.g. GCC-compiled code) that expects the real ABI.
 */
typedef __int128 ti_int;
typedef unsigned __int128 tu_int;

ABI ti_int __multi3(ti_int a, ti_int b){return a*b;}

/* Unsigned 128/128 -> 128 binary long division (schoolbook, bit-serial).
 * Slow (128 iterations) but correct and immune to the self-recursion trap
 * described above. `d == 0` returns 0 (matches this file's existing
 * "never trap on bad input" convention elsewhere; real hardware division
 * would fault, but Pride's own codegen is expected to guard divisor-zero
 * upstream — see typecheck.c3's check_divisor). */
ABI tu_int __udivti3(tu_int n, tu_int d)
{
    if (d == 0) return 0;
    tu_int quotient = 0, remainder = 0;
    for (int i = 127; i >= 0; i--)
    {
        remainder = (remainder << 1) | ((n >> i) & 1);
        if (remainder >= d)
        {
            remainder -= d;
            quotient |= ((tu_int)1) << i;
        }
    }
    return quotient;
}

ABI tu_int __umodti3(tu_int n, tu_int d)
{
    if (d == 0) return 0;
    tu_int remainder = 0;
    for (int i = 127; i >= 0; i--)
    {
        remainder = (remainder << 1) | ((n >> i) & 1);
        if (remainder >= d) { remainder -= d; }
    }
    return remainder;
}

/* Quotient+remainder in one call (GCC/LLVM emit this instead of separate
 * __udivti3/__umodti3 calls when both are needed from the same operands in
 * one expression — e.g. compiler_rt.c's own __pride_div_u128_u64). `*rem`
 * receives the remainder; the quotient is returned. Built on __udivti3 (not
 * `/`) for the same self-recursion-avoidance reason as above. */
ABI tu_int __udivmodti4(tu_int n, tu_int d, tu_int* rem)
{
    tu_int q = __udivti3(n, d);
    if (rem) { *rem = n - q * d; }
    return q;
}

/* Signed division/modulo: reduce to the unsigned routines above (never uses
 * __int128 `/`/`%` directly, for the same reason). C truncates toward zero;
 * both operations here match that convention. */
ABI ti_int __divti3(ti_int n, ti_int d)
{
    int neg = 0;
    tu_int un = (tu_int)n, ud = (tu_int)d;
    if (n < 0) { un = (tu_int)(-n); neg = !neg; }
    if (d < 0) { ud = (tu_int)(-d); neg = !neg; }
    tu_int uq = __udivti3(un, ud);
    return neg ? -(ti_int)uq : (ti_int)uq;
}

ABI ti_int __modti3(ti_int n, ti_int d)
{
    int neg = 0;
    tu_int un = (tu_int)n, ud = (tu_int)d;
    if (n < 0) { un = (tu_int)(-n); neg = 1; }
    if (d < 0) { ud = (tu_int)(-d); }
    tu_int ur = __umodti3(un, ud);
    return neg ? -(ti_int)ur : (ti_int)ur;
}
ABI int __popcountsi2(unsigned int a){return __builtin_popcount(a);}
ABI int __popcountdi2(unsigned long long a){return __builtin_popcountll(a);}
ABI int __clzsi2(unsigned int a){return a?__builtin_clz(a):32;}
ABI int __ctzsi2(unsigned int a){return a?__builtin_ctz(a):32;}
ABI int __paritysi2(unsigned int a){return __builtin_parity(a);}
ABI int __paritydi2(unsigned long long a){return __builtin_parityll(a);}
ABI int __ffsi2(unsigned int a){return __builtin_ffs(a);}
ABI int __ffdi2(unsigned long long a){return __builtin_ffsll(a);}
ABI int __absvsi2(int a){return a<0?-a:a;} ABI long long __absvdi2(long long a){return a<0?-a:a;}
ABI unsigned int __bswapsi2(unsigned int a){return __builtin_bswap32(a);}
ABI unsigned long long __bswapdi2(unsigned long long a){return __builtin_bswap64(a);}
ABI int __ashlsi3(int a,int b){return(unsigned)a<<b;}
ABI long long __ashldi3(long long a,int b){return(unsigned long long)a<<b;}
ABI int __ashrsi3(int a,int b){return a>>b;} ABI long long __ashrdi3(long long a,int b){return a>>b;}
ABI unsigned int __lshrsi3(unsigned int a,int b){return a>>b;}
ABI unsigned long long __lshrdi3(unsigned long long a,int b){return a>>b;}
ABI double __floatsidf(int a){return(double)a;} ABI float __floatsisf(int a){return(float)a;}
ABI double __floatdidf(long long a){return(double)a;} ABI float __floatdisf(long long a){return(float)a;}
ABI double __floatunsidf(unsigned int a){return(double)a;} ABI float __floatunsisf(unsigned int a){return(float)a;}
ABI double __floatundidf(unsigned long long a){return(double)a;} ABI float __floatundisf(unsigned long long a){return(float)a;}
ABI int __fixsfsi(float a){return(int)a;} ABI int __fixdfsi(double a){return(int)a;}
ABI long long __fixsfdi(float a){return(long long)a;} ABI long long __fixdfdi(double a){return(long long)a;}
ABI unsigned int __fixunssfsi(float a){return(unsigned)a;} ABI unsigned int __fixunsdfsi(double a){return(unsigned)a;}
ABI unsigned long long __fixunssfdi(float a){return(unsigned long long)a;}
ABI unsigned long long __fixunsdfdi(double a){return(unsigned long long)a;}
ABI double __extendsfdf2(float a){return(double)a;} ABI float __truncdfsf2(double a){return(float)a;}
ABI double __adddf3(double a,double b){return a+b;} ABI double __subdf3(double a,double b){return a-b;}
ABI double __muldf3(double a,double b){return a*b;} ABI double __divdf3(double a,double b){return a/b;}
ABI double __negdf2(double a){return -a;}
ABI float __addsf3(float a,float b){return a+b;} ABI float __subsf3(float a,float b){return a-b;}
ABI float __mulsf3(float a,float b){return a*b;} ABI float __divsf3(float a,float b){return a/b;}
ABI float __negsf2(float a){return -a;}
ABI int __eqdf2(double a,double b){return a!=b;} ABI int __nedf2(double a,double b){return a!=b;}
ABI int __ltdf2(double a,double b){return a<b?-1:0;} ABI int __ledf2(double a,double b){return a>b?1:0;}
ABI int __gtdf2(double a,double b){return a>b?1:0;} ABI int __gedf2(double a,double b){return a<b?-1:0;}
ABI int __eqsf2(float a,float b){return a!=b;} ABI int __nesf2(float a,float b){return a!=b;}
ABI int __ltsf2(float a,float b){return a<b?-1:0;} ABI int __lesf2(float a,float b){return a>b?1:0;}
ABI int __gtsf2(float a,float b){return a>b?1:0;} ABI int __gesf2(float a,float b){return a<b?-1:0;}
ABI int __unorddf2(double a,double b){return __builtin_isunordered(a,b);}
ABI int __unordsf2(float a,float b){return __builtin_isunordered(a,b);}
