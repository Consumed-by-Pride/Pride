// Naive matrix multiply 64x64 — measures FP throughput
#include <stdint.h>
#include <time.h>
#include <stdio.h>
#define N 64
static double A[N][N], B[N][N], C[N][N];
void matmul(void){
    for(int i=0;i<N;i++) for(int k=0;k<N;k++){
        double a=A[i][k];
        for(int j=0;j<N;j++) C[i][j]+=a*B[k][j];
    }
}
int main(void){
    for(int i=0;i<N;i++) for(int j=0;j<N;j++){A[i][j]=i+j;B[i][j]=i-j;}
    const int ITERS=1000;
    struct timespec t0,t1;
    clock_gettime(CLOCK_MONOTONIC,&t0);
    for(int k=0;k<ITERS;k++) matmul();
    clock_gettime(CLOCK_MONOTONIC,&t1);
    long ns=((long)(t1.tv_sec-t0.tv_sec))*1000000000L+(t1.tv_nsec-t0.tv_nsec);
    printf("%ld\n", ns/ITERS);
    return 0;
}
