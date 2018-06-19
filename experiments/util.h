#ifndef __UTIL_H
#define __UTIL_H

#define min(x, y) (((x) < (y)) ? (x) : (y))
#define max(x, y) (((x) > (y)) ? (x) : (y))

double* alloc_mat(int m, int n);

double* copy_matrix(int m, int n, double *a);

double* rand_matrix(int m, int n);

double* rand_symmetric_matrix(int n);

double get_cpu_time();

double max_elem_diff(int m, int n, double *a, int lda, double *b, int ldb);

#define SMALL_BENCH_RPT_OUTER 35
#define SMALL_BENCH_RPT_INNER 2500
#define EPSILON 1e-9
#define SMALL_BENCH_UPPER_BOUND 128
#endif // __UTIL_H
