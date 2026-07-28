#include <stdint.h>
#include <time.h>
#include <stdio.h>

int64_t pride_run(int64_t *stack, int64_t n);

int main(void) {
    const int N = 10000, ITERS = 1000;
    int64_t stack[N + 8];   // generous padding
    volatile int64_t r = 0;
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int k = 0; k < ITERS; k++) r = pride_run(stack, N);
    clock_gettime(CLOCK_MONOTONIC, &t1);
    long ns = ((long)(t1.tv_sec-t0.tv_sec))*1000000000L + (t1.tv_nsec-t0.tv_nsec);
    printf("%ld\n", ns / ITERS);
    (void)r;
    return 0;
}
