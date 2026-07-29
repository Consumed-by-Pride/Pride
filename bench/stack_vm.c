#include <stdint.h>
#include <time.h>
#include <stdio.h>

static int64_t push(int64_t *s, int64_t sp, int64_t v){s[sp]=v;return sp+1;}
static int64_t pop(int64_t *s, int64_t sp){return s[sp-1];}
static int64_t exec_add(int64_t *s, int64_t sp){
    int64_t a=s[sp-1],b=s[sp-2]; s[sp-2]=a+b; return sp-1;
}
int64_t run(int64_t *stack, int64_t n){
    int64_t sp=0,i=0;
    sp=push(stack,sp,0); sp=push(stack,sp,0);  // prime
    while(i<n){
        if(i%2==0) sp=push(stack,sp,i);
        else       sp=exec_add(stack,sp);
        i++;
    }
    return pop(stack,sp);
}
int main(void){
    const int N=10000, ITERS=1000;
    int64_t stack[N+8];
    volatile int64_t r=0;
    struct timespec t0,t1;
    clock_gettime(CLOCK_MONOTONIC,&t0);
    for(int k=0;k<ITERS;k++) r=run(stack,N);
    clock_gettime(CLOCK_MONOTONIC,&t1);
    long ns=((long)(t1.tv_sec-t0.tv_sec))*1000000000L+(t1.tv_nsec-t0.tv_nsec);
    printf("%ld\n", ns/ITERS);
    (void)r;
    return 0;
}
