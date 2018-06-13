#include <flame/FLAME.h>
#include <math.h>

#define BLOCKSIZE 64

double ONE = 1.0;
double MINUS_ONE = -1.0;

void unfused_alg(int n, double* a, int lda, double* b, int ldb) {
    for (int i = 0; i < n; i += BLOCKSIZE) {
        int blk = min(BLOCKSIZE, n - i);
        int chol_info = 0;
        dpotrf_("Lower triangular", &blk, (a + (lda * i + i)), &lda,
                &chol_info);
        if (chol_info) {
            printf("Unfused: Error at %d + %d in cholesky\n", i, chol_info);
            return;
        }

        if (i + BLOCKSIZE < n) {
            // A21 = A21 * inv( tril( A11 )' )
            int trsm_m = n - (i + BLOCKSIZE);
            dtrsm_("Right", "Lower", "Trans", "Nonunit", &trsm_m , &blk, &ONE,
                   (a + (lda * i + i)), &lda,
                   (a + (lda * i + i + BLOCKSIZE)), &lda);

            // A22 = A22 - A21 * A21'
            dsyrk_("Lower triangular", "No transpose", &trsm_m, &blk, &MINUS_ONE,
                   (a + (lda * i + i + BLOCKSIZE)), &lda, &ONE,
                   (a + (lda * (i + BLOCKSIZE) + (i + BLOCKSIZE))), &lda);
        }
    }

    /** Solve **/
    for (int i = 0; i < n; i += BLOCKSIZE) {
        int blk = min(BLOCKSIZE, n - i);
        dtrsm_("Left", "Lower", "No transpose", "Nonunit",
               &blk, &n, &ONE, (a + (lda * i) + i), &lda,
               b + i, &ldb);
        if (i + BLOCKSIZE < n) {
            /* B2 = B2 - A21 * B1 */
            int gemm_m = n - (i + BLOCKSIZE);
            dgemm_("No transpose", "No transpose", &gemm_m, &n, &blk,
                   &MINUS_ONE, a + ((lda * i) + (i + BLOCKSIZE)), &lda,
                   b + i, &ldb, &ONE, b + i + BLOCKSIZE, &ldb);
        }
    }
}

void fused_alg(int n, double* a, int lda, double* b, int ldb) {
    for (int i = 0; i < n; i += BLOCKSIZE) {
        int blk = min(BLOCKSIZE, n - i);
        int chol_info = 0;
        dpotrf_("Lower triangular", &blk, (a + (lda * i + i)), &lda,
                &chol_info);
        if (chol_info) {
            printf("Fused: Error at %d + %d in cholesky\n", i, chol_info);
            return;
        }


        dtrsm_("Left", "Lower", "No transpose", "Nonunit",
               &blk, &n, &ONE, (a + (lda * i) + i), &lda,
               b + i, &ldb);

        if (i + BLOCKSIZE < n) {
            // A21 = A21 * inv( tril( A11 )' )
            int trsm_m = n - (i + BLOCKSIZE);
            dtrsm_("Right", "Lower", "Trans", "Nonunit", &trsm_m , &blk, &ONE,
                   (a + (lda * i + i)), &lda,
                   (a + (lda * i + i + BLOCKSIZE)), &lda);

            /* B2 = B2 - A21 * B1 */
            int gemm_m = n - (i + BLOCKSIZE);
            dgemm_("No transpose", "No transpose", &gemm_m, &n, &blk,
                   &MINUS_ONE, a + ((lda * i) + (i + BLOCKSIZE)), &lda,
                   b + i, &ldb, &ONE, b + i + BLOCKSIZE, &ldb);

            // A22 = A22 - A21 * A21'
            dsyrk_("Lower triangular", "No transpose",
                   &trsm_m, &blk, &MINUS_ONE,
                   (a + (lda * i + i + BLOCKSIZE)), &lda, &ONE,
                   (a + (lda * (i + BLOCKSIZE) + (i + BLOCKSIZE))), &lda);
        }
    }
}

void benchmark(dim_t n) {
    double unfused_secs = 1e50;
    double fused_secs = 1e50;
    double a_diff = -1;
    double b_diff = -1;

    for (int i = 0; i < 5; i++) {
        FLA_Obj A1, A2, B1, B2;

        FLA_Obj_create(FLA_DOUBLE, n, n, 1, n, &A1);
        FLA_Obj_create(FLA_DOUBLE, n, n, 1, n, &B1);

        FLA_Random_symm_matrix(FLA_LOWER_TRIANGULAR, A1);
        FLA_Random_matrix(B1);

        FLA_Obj_create_copy_of(FLA_NO_TRANSPOSE, A1, &A2);
        FLA_Obj_create_copy_of(FLA_NO_TRANSPOSE, B1, &B2);

        double *a1 = (double*)FLA_Obj_base_buffer(A1);
        double *a2 = (double*)FLA_Obj_base_buffer(A2);
        double *b1 = (double*)FLA_Obj_base_buffer(B1);
        double *b2 = (double*)FLA_Obj_base_buffer(B2);

        double unfused_start = FLA_Clock();
        unfused_alg(n, a1, n, b1, n);
        double unfused_end = FLA_Clock();
        unfused_secs = min(unfused_secs, unfused_end - unfused_start);

        double fused_start = FLA_Clock();
        fused_alg(n, a2, n, b2, n);
        double fused_end = FLA_Clock();
        fused_secs = min(fused_secs, fused_end - fused_start);

        double my_a_diff = FLA_Max_elemwise_diff(A1, A2);
        double my_b_diff = FLA_Max_elemwise_diff(B1, B2);
        a_diff = max(my_a_diff, a_diff);
        b_diff = max(my_b_diff, b_diff);

        FLA_Obj_free(&A1);
        FLA_Obj_free(&A2);
        FLA_Obj_free(&B1);
        FLA_Obj_free(&B2);
    }

    printf("%lu\t%e\t%e\t%e\t%e\n", n, unfused_secs, fused_secs, a_diff, b_diff);
}

int main() {
    FLA_Init();
    srand(time(NULL));

    printf("N\tUnfused\tFused\tErr_A\tErr_B\n");
    for (dim_t i = 1; i < 128; i++) {
        benchmark(i * 8);
    }
    return 0;
}
