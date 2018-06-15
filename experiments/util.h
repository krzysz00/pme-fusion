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
#endif // __UTIL_H
