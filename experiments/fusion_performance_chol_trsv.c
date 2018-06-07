#include <flame/FLAME.h>

FLA_Error unfused_alg(FLA_Obj A, FLA_Obj B) {
    FLA_Obj ATL, ATR,  A00,  a01,     A02,
            ABL, ABR,  a10t, alpha11, a12t,
                       A20,  a21,     A22;

    FLA_Obj BT,  B0,
            BB,  b1t,
                 B2;

    /** Cholesky **/
    FLA_Part_2x2(A, &ATL, &ATR,
                    &ABL, &ABR,
                 0, 0, FLA_TL );

    while (FLA_Obj_length(ATL) < FLA_Obj_length(A)) {

        FLA_Repart_2x2_to_3x3( ATL, /**/ ATR,  &A00,  /**/ &a01,     &A02,
                              /* **************/ /****************************/
                                               &a10t, /**/ &alpha11, &a12t,
                               ABL, /**/ ABR,  &A20,  /**/ &a21,     &A22,
                               1, 1, FLA_BR );

        /*------------------------------------------------------------*/

        // alpha11 = sqrt( alpha11 )
        FLA_Error r_val = FLA_Sqrt( alpha11 );

        if (r_val != FLA_SUCCESS) {
            return FLA_Obj_length(A00);
        }

        // a21 = a21 / alpha11
        FLA_Inv_scal_external(alpha11, a21);

        // A22 = A22 - a21 * a21'
        FLA_Her_external(FLA_LOWER_TRIANGULAR, FLA_MINUS_ONE, a21, A22);

        /*------------------------------------------------------------*/

        FLA_Cont_with_3x3_to_2x2(&ATL, /**/ &ATR, A00,  a01,     /**/ A02,
                                                  a10t, alpha11, /**/ a12t,
                                /**************** *************************/
                                 &ABL, /**/ &ABR, A20,  a21,     /**/ A22,
                                  FLA_TL );

    }

    /** Solve **/
    FLA_Part_2x2(A, &ATL, &ATR,
                    &ABL, &ABR,
                 0, 0, FLA_TL );

    FLA_Part_2x1(B, &BT,
                    &BB,
                 0, FLA_TOP );

    while (FLA_Obj_length(ATL) < FLA_Obj_length(A)) {

        FLA_Repart_2x2_to_3x3( ATL, /**/ ATR,  &A00,  /**/ &a01,     &A02,
                              /* **************/ /****************************/
                                               &a10t, /**/ &alpha11, &a12t,
                               ABL, /**/ ABR,  &A20,  /**/ &a21,     &A22,
                               1, 1, FLA_BR );

        FLA_Repart_2x1_to_3x1( BT,   &B0,
                              /***/ /*****/
                                     &b1t,
                               BB,   &B2,
                               1, FLA_BOTTOM );

        /*------------------------------------------------------------*/

        /* b1t = b1t / alpha11 */
        FLA_Inv_scal_external( alpha11, b1t );

        /* B2 = B2 - a21 * b1t */
        FLA_Ger_external( FLA_MINUS_ONE, a21, b1t, B2 );

        /*------------------------------------------------------------*/

        FLA_Cont_with_3x3_to_2x2(&ATL, /**/ &ATR, A00,  a01,     /**/ A02,
                                                  a10t, alpha11, /**/ a12t,
                                /**************** *************************/
                                 &ABL, /**/ &ABR, A20,  a21,     /**/ A22,
                                  FLA_TL );

        FLA_Cont_with_3x1_to_2x1(&BT, B0,
                                      b1t,
                                 /*** ****/
                                 &BB, B2, FLA_TOP);

    }
    return FLA_SUCCESS;
}

FLA_Error fused_alg(FLA_Obj A, FLA_Obj B) {
    FLA_Obj ATL, ATR,  A00,  a01,     A02,
            ABL, ABR,  a10t, alpha11, a12t,
                       A20,  a21,     A22;

    FLA_Obj BT,  B0,
            BB,  b1t,
                 B2;


    FLA_Part_2x2(A, &ATL, &ATR,
                    &ABL, &ABR,
                 0, 0, FLA_TL );

    FLA_Part_2x1(B, &BT,
                    &BB,
                 0, FLA_TOP );

    while (FLA_Obj_length(ATL) < FLA_Obj_length(A)) {

        FLA_Repart_2x2_to_3x3( ATL, /**/ ATR,  &A00,  /**/ &a01,     &A02,
                              /* **************/ /****************************/
                                               &a10t, /**/ &alpha11, &a12t,
                               ABL, /**/ ABR,  &A20,  /**/ &a21,     &A22,
                               1, 1, FLA_BR );

        FLA_Repart_2x1_to_3x1( BT,   &B0,
                              /***/ /*****/
                                     &b1t,
                               BB,   &B2,
                               1, FLA_BOTTOM );

        /*------------------------------------------------------------*/

        // alpha11 = sqrt( alpha11 )
        FLA_Error r_val = FLA_Sqrt( alpha11 );

        if (r_val != FLA_SUCCESS) {
            return FLA_Obj_length(A00);
        }

        // a21 = a21 / alpha11
        FLA_Inv_scal_external(alpha11, a21);

        // A22 = A22 - a21 * a21'
        FLA_Her_external(FLA_LOWER_TRIANGULAR, FLA_MINUS_ONE, a21, A22);

        /* b1t = b1t / alpha11 */
        FLA_Inv_scal_external( alpha11, b1t );

        /* B2 = B2 - a21 * b1t */
        FLA_Ger_external(FLA_MINUS_ONE, a21, b1t, B2 );

        /*------------------------------------------------------------*/

        FLA_Cont_with_3x3_to_2x2(&ATL, /**/ &ATR, A00,  a01,     /**/ A02,
                                                  a10t, alpha11, /**/ a12t,
                                /**************** *************************/
                                 &ABL, /**/ &ABR, A20,  a21,     /**/ A22,
                                  FLA_TL );

        FLA_Cont_with_3x1_to_2x1(&BT, B0,
                                      b1t,
                                 /*** ****/
                                 &BB, B2, FLA_TOP);

    }
    return FLA_SUCCESS;
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

        double unfused_start = FLA_Clock();
        unfused_alg(A1, B1);
        double unfused_end = FLA_Clock();
        unfused_secs = min(unfused_secs, unfused_end - unfused_start);

        double fused_start = FLA_Clock();
        fused_alg(A2, B2);
        double fused_end = FLA_Clock();
        fused_secs = min(fused_secs, fused_end - fused_start);

        double my_a_diff = FLA_Max_elemwise_diff(A1, A2);
        double my_b_diff = FLA_Max_elemwise_diff(B1, B2);
        a_diff = max(my_a_diff, a_diff);
        b_diff = max(my_b_diff, b_diff);
    }

    printf("%lu\t%e\t%e\t%e\t%e\n", n, unfused_secs, fused_secs, a_diff, b_diff);
}

int main() {
    FLA_Init();
    srand(time(NULL));

    printf("N\tUnfused\tFused\tErr_A\tErr_B\n");
    for (dim_t i = 1; i < 100; i++) {
        benchmark(i * 8);
    }
    return 0;
}
