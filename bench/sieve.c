// Sieve of Eratosthenes — measures dense bit-array writes
#include <stdint.h>
#include <time.h>
#include <stdio.h>
#include <string.h>
#define LIMIT 1000000
static char sieve[LIMIT+1];
int64_t eratosthenes(int64_t n){
    memset(sieve,1,(size_t)(n+1));
    sieve[0]=sieve[1]=0;
    for(int64_t i=2;i*i<=n;i++) if(sieve[i]) for(int64_t j=i*i;j<=n;j+=i) sieve[j]=0;
    int64_t cnt=0; for(int64_t i=2;i<=n;i++) cnt+=sieve[i]; return cnt;
}
int main(void){
    const int ITERS=100;
    volatile int64_t r=0;
    struct timespec t0,t1;
    clock_gettime(CLOCK_MONOTONIC,&t0);
    for(int k=0;k<ITERS;k++) r=eratosthenes(LIMIT);
    clock_gettime(CLOCK_MONOTONIC,&t1);
    long ns=((long)(t1.tv_sec-t0.tv_sec))*1000000000L+(t1.tv_nsec-t0.tv_nsec);
    printf("%ld\n", ns/ITERS);
    (void)r;
    return 0;
}
