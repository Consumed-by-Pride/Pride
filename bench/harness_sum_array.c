#include <stdint.h>
#include <time.h>
#include <stdio.h>
#define N 65536

int64_t pride_sum_arr(int64_t *a, int64_t n);

static int64_t arr[N];
int main(void) {
    for (int i = 0; i < N; i++) arr[i] = i;
    const int ITERS = 100000;
    volatile int64_t r = 0;
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int k = 0; k < ITERS; k++) r = pride_sum_arr(arr, N);
    clock_gettime(CLOCK_MONOTONIC, &t1);
    long ns = ((long)(t1.tv_sec-t0.tv_sec))*1000000000L + (t1.tv_nsec-t0.tv_nsec);
    printf("%ld\n", ns / ITERS);
    (void)r;
    return 0;
}
