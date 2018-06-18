#define _GNU_SOURCE 1
#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>

#include "util.h"

#define BENCH_RPT_OUTER 35
#define BENCH_RPT_INNER 2500
#define EPSILON 1e-9

void unfused_alg(int n, double *a, int lda, double *b, int ldb) {
    // Cholesky
    for (int i = 0; i < n; i++) {
        // a11 = sqrt(a11)
        double *a1 = a + (i * lda);
        double a11 = sqrt(a1[i]);
        a[i * lda + i] = a11;

        // a21 = a21 / a11
        for (int i2 = i + 1; i2 < n; i2++) {
            a1[i2] /= a11;
        }

        // A22 = A22 - a21 * a21^T
        for (int j = i + 1; j < n; j++) {
            double* col = a + (j * lda);
            for (int i2 = i + 1; i2 < n; i2++) {
                col[i] -= a1[i2] * a1[j];
            }
        }
    }

    // Solve
    for (int i = 0; i < n; i++) {
        double a11 = a[i * lda + i];

        // b1t = b1t / alpha11
        double* row = b + i;
        for (int j = 0; j <= i; j++) {
            row[j * ldb] /= a11;
        }

        // B2 - B2 - a21 * b1t
        double *col = a + (lda * i);
        for (int j = 0; j < n; j++) {
            int i_init = min(j, i + 1);
            for (int i2 = i_init; i2 < n; i2++) {
                b[j * ldb + i2] = col[i2] * row[j * ldb];
            }
        }
    }
}

void fused_alg(int n, double *a, int lda, double *b, int ldb) {
    for (int i = 0; i < n; i++) {
        // a11 = sqrt(a11)
        double *a1 = a + (i * lda);
        double a11 = sqrt(a1[i]);
        a[i * lda + i] = a11;

        // a21 = a21 / a11
        for (int i2 = i + 1; i2 < n; i2++) {
            a1[i2] /= a11;
        }

        // A22 = A22 - a21 * a21^T
        for (int j = i + 1; j < n; j++) {
            double* col = a + (j * lda);
            for (int i2 = i + 1; i2 < n; i2++) {
                col[i] -= a1[i2] * a1[j];
            }
        }

        // b1t = b1t / alpha11
        double* row = b + i;
        for (int j = 0; j <= i; j++) {
            row[j * ldb] /= a11;
        }

        // B2 - B2 - a21 * b1t
        double *col = a + (lda * i);
        for (int j = 0; j < n; j++) {
            int i_init = min(j, i + 1);
            for (int i2 = i_init; i2 < n; i2++) {
                b[j * ldb + i2] = col[i2] * row[j * ldb];
            }
        }
    }
}

#define L2_CACHE_64S 8192
volatile uint64_t flusher[L2_CACHE_64S] = {0};
void cache_flush() {
    for (int i = 0; i < L2_CACHE_64S; i++) {
        flusher[i]++;
    }
}

void benchmark(int n) {
    double unfused_times[BENCH_RPT_OUTER];
    double fused_times[BENCH_RPT_OUTER];

    for (int i = 0; i < BENCH_RPT_OUTER; i++) {
        double *a = rand_symmetric_matrix(n);
        double *b = rand_matrix(n, n);

        double unfused_time = 0;
        double fused_time = 0;
        for (int j = 0; j < BENCH_RPT_INNER; j++) {
            double *a1 = copy_matrix(n, n, a);
            double *b1 = copy_matrix(n, n, b);
            double *a2 = copy_matrix(n, n, a);
            double *b2 = copy_matrix(n, n, b);

            cache_flush();

            double unfused_time_start = get_cpu_time();
            unfused_alg(n, a1, n, b1, n);
            double unfused_time_end = get_cpu_time();
            unfused_time += unfused_time_end - unfused_time_start;

            cache_flush();

            double fused_time_start = get_cpu_time();
            fused_alg(n, a2, n, b2, n);
            double fused_time_end = get_cpu_time();
            fused_time += fused_time_end - fused_time_start;

            double a_err = max_elem_diff(n, n, a1, n, a2, n);
            double b_err = max_elem_diff(n, n, b1, n, b2, n);
            if (a_err > EPSILON) {
                printf("Inaccuracy of A %e at n = %d_%d_%d\n", a_err, n, i, j);
            }
            if (b_err > EPSILON) {
                printf("Inaccuracy of B %e at n = %d_%d_%d\n", b_err, n, i, j);
            }

            free(a1);
            free(a2);
            free(b1);
            free(b2);
        }

        unfused_times[i] = unfused_time / BENCH_RPT_INNER;
        fused_times[i] = fused_time / BENCH_RPT_INNER;
    }

    printf("%d\tUnfused", n);
    for (int i = 0; i < BENCH_RPT_OUTER; i++) {
        printf("\t%e", unfused_times[i]);
    }
    printf("\n%d\tFused", n);
    for (int i = 0; i < BENCH_RPT_OUTER; i++) {
        printf("\t%e", fused_times[i]);
    }
    printf("\n");
}

int main() {
    srand(time(NULL));
    srand48(time(NULL) + 5000);

    for (int i = 4; i <= 64; i += 4) {
        benchmark(i);
    }
    return 0;
}
