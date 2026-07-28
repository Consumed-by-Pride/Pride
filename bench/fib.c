// Recursive fibonacci — measures call overhead + branch prediction
#include <stdint.h>
#include <time.h>
#include <stdio.h>
int64_t fib(int64_t n){ return n<=1?n:fib(n-1)+fib(n-2); }
int main(void){
    const int ITERS=1000;
    volatile int64_t r=0;
    struct timespec t0,t1;
    clock_gettime(CLOCK_MONOTONIC,&t0);
    for(int k=0;k<ITERS;k++) r=fib(35);
    clock_gettime(CLOCK_MONOTONIC,&t1);
    long ns=((long)(t1.tv_sec-t0.tv_sec))*1000000000L+(t1.tv_nsec-t0.tv_nsec);
    printf("%ld\n", ns/ITERS);
    (void)r;
    return 0;
}
