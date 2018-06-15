#define _GNU_SOURCE 1
#include <mkl.h>
#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#include <time.h>

#include "util.h"

#define BLOCKSIZE 128

void unfused_alg(int n, double* a, int lda, double* b, int ldb) {
    for (int i = 0; i < n; i += BLOCKSIZE) {
        int blk = min(BLOCKSIZE, n - i);
        int chol_info = LAPACKE_dpotrf(LAPACK_COL_MAJOR, 'L',
                                       blk, a + (lda * i) + i, lda);
        if (chol_info) {
            printf("Unfused: Error at %d + %d in cholesky\n", i, chol_info);
            return;
        }

        if (i + BLOCKSIZE < n) {
            // A21 = A21 * inv( tril( A11 )' )
            int trsm_m = n - (i + BLOCKSIZE);
            cblas_dtrsm(CblasColMajor, CblasRight, CblasLower, CblasTrans, CblasNonUnit,
                        trsm_m , blk, 1.0, (a + (lda * i + i)), lda,
                        (a + (lda * i + i + BLOCKSIZE)), lda);

            // A22 = A22 - A21 * A21'
            cblas_dsyrk(CblasColMajor, CblasLower, CblasNoTrans,
                        trsm_m, blk, -1.0,
                        (a + (lda * i + i + BLOCKSIZE)), lda,
                        1.0, (a + (lda * (i + BLOCKSIZE) + (i + BLOCKSIZE))), lda);
        }
    }

    /** Solve **/
    for (int i = 0; i < n; i += BLOCKSIZE) {
        int blk = min(BLOCKSIZE, n - i);
        cblas_dtrsm(CblasColMajor, CblasLeft, CblasLower, CblasNoTrans, CblasNonUnit,
                    blk, n, 1.0, (a + (lda * i) + i), lda,
                    b + i, ldb);
        if (i + BLOCKSIZE < n) {
            /* B2 = B2 - A21 * B1 */
            int gemm_m = n - (i + BLOCKSIZE);
            cblas_dgemm(CblasColMajor, CblasNoTrans, CblasNoTrans, gemm_m, n, blk,
                   -1.0, a + ((lda * i) + (i + BLOCKSIZE)), lda,
                   b + i, ldb, 1.0, b + i + BLOCKSIZE, ldb);
        }
    }
}

void fused_alg(int n, double* a, int lda, double* b, int ldb) {
    for (int i = 0; i < n; i += BLOCKSIZE) {
        int blk = min(BLOCKSIZE, n - i);
        int chol_info = LAPACKE_dpotrf(LAPACK_COL_MAJOR, 'L',
                                       blk, a + (lda * i) + i, lda);
        if (chol_info) {
            printf("Unfused: Error at %d + %d in cholesky\n", i, chol_info);
            return;
        }

        cblas_dtrsm(CblasColMajor, CblasLeft, CblasLower, CblasNoTrans, CblasNonUnit,
                    blk, n, 1.0, (a + (lda * i) + i), lda,
                    b + i, ldb);

        if (i + BLOCKSIZE < n) {
            // A21 = A21 * inv( tril( A11 )' )
            int lower_m = n - (i + BLOCKSIZE);
            cblas_dtrsm(CblasColMajor, CblasRight, CblasLower, CblasTrans, CblasNonUnit,
                        lower_m , blk, 1.0, (a + (lda * i + i)), lda,
                        (a + (lda * i + i + BLOCKSIZE)), lda);

            /* B2 = B2 - A21 * B1 */
            cblas_dgemm(CblasColMajor, CblasNoTrans, CblasNoTrans, lower_m, n, blk,
                   -1.0, a + ((lda * i) + (i + BLOCKSIZE)), lda,
                   b + i, ldb, 1.0, b + i + BLOCKSIZE, ldb);

            // A22 = A22 - A21 * A21'
            cblas_dsyrk(CblasColMajor, CblasLower, CblasNoTrans,
                        lower_m, blk, -1.0,
                        (a + (lda * i + i + BLOCKSIZE)), lda,
                        1.0, (a + (lda * (i + BLOCKSIZE) + (i + BLOCKSIZE))), lda);
        }
    }
}

void benchmark(int n) {
    double unfused_secs = 1e50;
    double fused_secs = 1e50;
    double a_diff = -1;
    double b_diff = -1;

    for (int i = 0; i < 5; i++) {
        double *a1 = rand_symmetric_matrix(n);
        double *a2 = copy_matrix(n, n, a1);

        double *b1 = rand_matrix(n, n);
        double *b2 = copy_matrix(n, n, b1);

        double unfused_start = get_cpu_time();
        //unfused_alg(n, a1, n, b1, n);
        LAPACKE_dpotrf(LAPACK_COL_MAJOR, 'L', n, a1, n);
        cblas_dtrsm(CblasColMajor, CblasLeft, CblasLower, CblasNoTrans, CblasNonUnit,
                    n, n, 1, a1, n, b1, n);
        double unfused_end = get_cpu_time();
        unfused_secs = min(unfused_secs, unfused_end - unfused_start);

        double fused_start = get_cpu_time();
        fused_alg(n, a2, n, b2, n);
        double fused_end = get_cpu_time();
        fused_secs = min(fused_secs, fused_end - fused_start);

        double my_a_diff = max_elem_diff(n, n, a1, n, a2, n);
        double my_b_diff = max_elem_diff(n, n, b1, n, b2, n);
        a_diff = max(my_a_diff, a_diff);
        b_diff = max(my_b_diff, b_diff);

        free(a1);
        free(a2);
        free(b1);
        free(b2);
    }

    printf("%d\t%e\t%e\t%e\t%e\n", n, unfused_secs, fused_secs, a_diff, b_diff);
}

int main() {
    srand(time(NULL));
    srand48(time(NULL) + 5000);

    printf("N\tUnfused\tFused\tErr_A\tErr_B\n");
    for (int i = 1; i < 128; i++) {
        benchmark(i * 8);
    }
    return 0;
}
