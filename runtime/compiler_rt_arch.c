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
ABI int __mulsi3(int a,int b){return a*b;} ABI long long __multi3(long long a,long long b){return a*b;}
ABI unsigned long long __udivti3(unsigned long long n,unsigned long long d){return n/d;}
ABI long long __divti3(long long n,long long d){return n/d;}
ABI unsigned long long __umodti3(unsigned long long n,unsigned long long d){return n%d;}
ABI long long __modti3(long long n,long long d){return n%d;}
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
