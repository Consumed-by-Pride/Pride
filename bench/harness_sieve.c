#include <stdint.h>
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#define LIMIT 1000000

int64_t pride_eratosthenes(uint8_t *arr, int64_t n);

int main(void) {
    uint8_t *arr = malloc(LIMIT + 2);
    const int ITERS = 100;
    volatile int64_t r = 0;
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int k = 0; k < ITERS; k++) r = pride_eratosthenes(arr, LIMIT);
    clock_gettime(CLOCK_MONOTONIC, &t1);
    long ns = ((long)(t1.tv_sec-t0.tv_sec))*1000000000L + (t1.tv_nsec-t0.tv_nsec);
    printf("%ld\n", ns / ITERS);
    free(arr);
    (void)r;
    return 0;
}
