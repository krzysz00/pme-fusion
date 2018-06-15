#define _GNU_SOURCE 1
#include <mkl.h>
//#include <flame/FLAME.h>
#include <stdio.h>
#include <math.h>
#include <time.h>
#include <string.h>
#include <stdlib.h>

#define BLOCKSIZE 64

#define min(x, y) (((x) < (y)) ? (x) : (y))
#define max(x, y) (((x) > (y)) ? (x) : (y))

double ONE = 1.0;
double MINUS_ONE = -1.0;
double ZERO = 0.0;
int ONE_I = 1;

// These functions compute L = L^T \* L for a lower-triangular and square matrix L
void trtrmm_unblocked(int n, double* a, int lda) {
    for (int i = 0; i < n; i++) {
        double *a10 = a + i;
        double *a11 = a + (lda * i) + i;

        if (i) {
            // A00 = A00 + a10' a10
            cblas_dsyr(CblasColMajor, CblasLower, i, 1.0, a10, lda, a, lda);
        }

        // a10 = a11 * a10
        cblas_dscal(i, *a11, a10, lda);

        // a11 = a11^2
        *a11 = pow(*a11, 2.0);
    }
}

void unfused_alg(int n, double* a, int lda) {
    for (int i = 0; i < n; i += BLOCKSIZE) {
        int blk = min(BLOCKSIZE, n - i);
        double *a11 = a + (lda * i + i);
        int chol_info = LAPACKE_dpotrf(LAPACK_COL_MAJOR, 'L', blk, a11, lda);
        if (chol_info) {
            printf("Unfused: Error at %d + %d in cholesky\n", i, chol_info);
            return;
        }

        if (i + BLOCKSIZE < n) {
            double *a21 = a + (lda * i + (i + BLOCKSIZE));
            double *a22 = a + (lda * (i + BLOCKSIZE) + (i + BLOCKSIZE));
            // A21 = A21 * inv( tril( A11 )'
            int lower_m = n - (i + BLOCKSIZE);
            cblas_dtrsm(CblasColMajor, CblasRight, CblasLower, CblasTrans,
                        CblasNonUnit, lower_m, blk, 1.0,
                        a11, lda,
                        a21, lda);

            // A22 = A22 - A21 * A21'
            cblas_dsyrk(CblasColMajor, CblasLower, CblasNoTrans, lower_m, blk,
                        -1.0, a21, lda, 1.0, a22, lda);
        }
    }

    /** inverse **/
    for (int i = 0; i < n; i += BLOCKSIZE) {
        int blk = min(BLOCKSIZE, n - i);
        double *a10 = a + i;
        double *a11 = a + (lda * i + i);
        if (i + BLOCKSIZE < n) {
            double *a21 = a + (lda * i) + (i + BLOCKSIZE);
            double *a20 = a + i + BLOCKSIZE;
            int lower_m = n - (i + BLOCKSIZE);

            // A21 = -A21 / tril( A11 );
            cblas_dtrsm(CblasColMajor, CblasRight, CblasLower, CblasNoTrans, CblasNonUnit,
                   lower_m, blk, -1.0, a11, lda, a21, lda);

            // A20 = A21 * A10 + A20;
            cblas_dgemm(CblasColMajor, CblasNoTrans, CblasNoTrans,
                        lower_m, i, blk, 1.0, a21, lda, a10, lda,
                        1.0, a20, lda);
        }

        // A10 = tril( A11 ) \ A10;
        cblas_dtrsm(CblasColMajor, CblasLeft, CblasLower, CblasNoTrans, CblasNonUnit,
                    blk, i, 1.0, a11, lda, a10, lda);

        // A11 = inv( A11 );
        int inv_info = LAPACKE_dtrtri(LAPACK_COL_MAJOR, 'L', 'N',
                                      blk, a11, lda);
        if (inv_info) {
            printf("Singular matrix at %d + %d\n", i, inv_info);
        }
    }

    /** trtrmm, or A = A^T * A **/
    for (int i = 0; i < n; i += BLOCKSIZE) {
        int blk = min(BLOCKSIZE, n - i);
        double *a10 = a + i;
        double *a11 = a + (lda * i) + i;

        if (i) {
            // A00 = A10^T * A10 + A00
            cblas_dsyrk(CblasColMajor, CblasLower, CblasTrans,
                        i, blk, 1.0, a10, lda,
                        1.0, a, lda);
        }

        // A10 = A11' * A10
        cblas_dtrmm(CblasColMajor, CblasLeft, CblasLower, CblasTrans, CblasNonUnit,
                    blk, i, 1.0, a11, lda, a10, lda);

        // A11 = A11^T * A11
        trtrmm_unblocked(blk, a11, lda);
    }
}

void fused_alg(int n, double* a, int lda) {
    for (int i = 0; i < n; i += BLOCKSIZE) {
        int blk = min(BLOCKSIZE, n - i);
        double *a10 = a + i;
        double *a11 = a + (lda * i + i);

        // A11 = CHOL(A11)
        int chol_info = LAPACKE_dpotrf(LAPACK_COL_MAJOR, 'L', blk, a11, lda);
        if (chol_info) {
            printf("Fused: Error at %d + %d in cholesky\n", i, chol_info);
            return;
        }

        if (i + BLOCKSIZE < n) {
            double *a21 = a + (lda * i + (i + BLOCKSIZE));
            double *a22 = a + (lda * (i + BLOCKSIZE)) + (i + BLOCKSIZE);
            double *a20 = a + i + BLOCKSIZE;

            // A21 = A21 * inv( tril( A11 )'
            int lower_m = n - (i + BLOCKSIZE);
            cblas_dtrsm(CblasColMajor, CblasRight, CblasLower, CblasTrans,
                        CblasNonUnit, lower_m, blk, 1.0,
                        a11, lda,
                        a21, lda);

            // A22 = A22 - A21 * A21'
            cblas_dsyrk(CblasColMajor, CblasLower, CblasNoTrans, lower_m, blk,
                        -1.0, a21, lda, 1.0, a22, lda);

            // inverse begins

            // A21 = -A21 / tril( A11 );
            cblas_dtrsm(CblasColMajor, CblasRight, CblasLower, CblasNoTrans, CblasNonUnit,
                        lower_m, blk, -1.0, a11, lda, a21, lda);

            // A20 = A21 * A10 + A20;
            cblas_dgemm(CblasColMajor, CblasNoTrans, CblasNoTrans,
                        lower_m, i, blk, 1.0, a21, lda, a10, lda,
                        1.0, a20, lda);
        }

        // A10 = tril( A11 ) \ A10;
        cblas_dtrsm(CblasColMajor, CblasLeft, CblasLower, CblasNoTrans, CblasNonUnit,
                    blk, i, 1.0, a11, lda, a10, lda);

        /** trtrmm, or A = A^T * A, interleaving **/
        if (i) {
            // A00 = A10^T * A10 + A00
            cblas_dsyrk(CblasColMajor, CblasLower, CblasTrans,
                        i, blk, 1.0, a10, lda,
                        1.0, a, lda);
        }

        // A11 = inv( A11 );
        int inv_info = LAPACKE_dtrtri(LAPACK_COL_MAJOR, 'L', 'N',
                                      blk, a11, lda);
        if (inv_info) {
            printf("Singular matrix at %d + %d\n", i, inv_info);
        }

        // A10 = A11' * A10
        cblas_dtrmm(CblasColMajor, CblasLeft, CblasLower, CblasTrans, CblasNonUnit,
                    blk, i, 1.0, a11, lda, a10, lda);

        // A11 = A11^T * A11
        trtrmm_unblocked(blk, a11, lda);
    }
}

double* alloc_mat(int m, int n) {
    void *m_raw;
    int _eh_itll_segfault = posix_memalign(&m_raw, 64, m * n * sizeof(double));
    bzero(m_raw, m * n * sizeof(double));
    return (double*)m_raw;
}

double* rand_symmetric_matrix(int n) {
    double *m = alloc_mat(n, n);
    for (int i = 0; i < n; i++) {
        for (int j = 0; j <= i; j++) {
            m[j * n + i] = drand48();
        }
    }
    // SPD-ize through L^T * L
    trtrmm_unblocked(n, m, n);
    for (int i = 0; i < n; i++) {
        m[i * n + i] += n;
    }
    return m;
}

double get_cpu_time() {
    struct timespec t;
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &t);
    return (double)t.tv_sec + ((double)t.tv_nsec / 1.0e9);
}

double max_elem_diff(int m, int n, double *a, int lda, double *b, int ldb) {
    double ret = 0.0;
    for (int j = 0; j < n; j++) {
        for (int i = 0; i < n; i++) {
            double diff = fabs(a[j * lda + i] - b[j * ldb + i]);
            ret = max(ret, diff);
        }
    }
    return ret;
}

void benchmark(int n) {
    double unfused_secs = 1e50;
    double fused_secs = 1e50;
    double a_diff = -1;

    for (int i = 0; i < 5; i++) {

        double *a1 = rand_symmetric_matrix(n);
        double *a2 = alloc_mat(n, n);
        memcpy(a2, a1, n * n * sizeof(double));

        double unfused_start = get_cpu_time();
        int inv_error = LAPACKE_dpotri(LAPACK_COL_MAJOR, 'L', (int)n, a1, (int)n);
        //unfused_alg(n, a1, n);
        double unfused_end = get_cpu_time();
        unfused_secs = min(unfused_secs, unfused_end - unfused_start);
        if (inv_error) {
            printf("Inverse failed in lapack on %d\n", n);
        }

        double fused_start = get_cpu_time();
        fused_alg(n, a2, n);
        double fused_end = get_cpu_time();
        fused_secs = min(fused_secs, fused_end - fused_start);

        double my_a_diff = max_elem_diff(n, n, a1, n, a2, n);
        a_diff = max(my_a_diff, a_diff);

        free(a1);
        free(a2);
    }

    printf("%d\t%e\t%e\t%e\n", n, unfused_secs, fused_secs, a_diff);
}

int main() {
    srand(time(NULL));
    srand48(time(NULL) + 5000);

    printf("N\tUnfused\tFused\tErr_A\n");
    for (int i = 1; i < 128; i++) {
        benchmark(i * 8);
    }
    return 0;
}
