#define _GNU_SOURCE 1
#include <mkl.h>
#include <time.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>

#include "util.h"

void _trtrmm_unblocked(int n, double* a, int lda) {
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
double* alloc_mat(int m, int n) {
    void *m_raw = NULL;
    int eh_itll_segfault = posix_memalign(&m_raw, 64, m * n * sizeof(double));
    (void)eh_itll_segfault;
    bzero(m_raw, m * n * sizeof(double));
    return (double*)m_raw;
}

double* rand_matrix(int m, int n) {
    double *a = alloc_mat(m, n);
    for (int j = 0; j < n; j++) {
        for (int i = 0; i < n; i++) {
            a[j * n + i] = drand48();
        }
    }
    return a;
}

double* rand_symmetric_matrix(int n) {
    double *m = alloc_mat(n, n);
    for (int i = 0; i < n; i++) {
        for (int j = 0; j <= i; j++) {
            m[j * n + i] = drand48();
        }
    }
    // SPD-ize through L^T * L
    _trtrmm_unblocked(n, m, n);
    for (int i = 0; i < n; i++) {
        m[i * n + i] += n;
    }
    return m;
}

double* copy_matrix(int m, int n, double *a) {
    double *b = alloc_mat(m, n);
    memcpy(b, a, m * n * sizeof(double));
    return b;
}

double get_cpu_time() {
    struct timespec t;
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &t);
    return (double)t.tv_sec + ((double)t.tv_nsec / 1.0e9);
}

double max_elem_diff(int m, int n, double *a, int lda, double *b, int ldb) {
    double ret = 0.0;
    for (int j = 0; j < n; j++) {
        for (int i = 0; i < m; i++) {
            double diff = fabs(a[j * lda + i] - b[j * ldb + i]);
            ret = max(ret, diff);
        }
    }
    return ret;
}
