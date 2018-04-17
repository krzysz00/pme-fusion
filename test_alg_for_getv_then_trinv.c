#include <flame/FLAME.h>

/**
   This is a fused algoritm for y = Lx, L = L^{-1}.
   The loop invariats are (in order)
   1. (y_T = \hat{L_TL} * x_T
       ----------------
       y_b = \hat{L_BL} * x_T)
   2. (L_TL = \hat{L_TL}^-1     | 0
       L_BL = \hat{L_BL} * L_TL | \hat{L_BR})

   These two invariants are fused because my code says that should work
 */
FLA_Error my_alg(FLA_Obj L, FLA_Obj x, FLA_Obj y) {
    FLA_Obj Ltl, Ltr,   L00,  l01,   L02,
            Lbl, Lbr,   l10t, ell11, l12,
                        L20,  l21,   L22;
    FLA_Obj xt, x0,
            xb, x1,
                x2;

    FLA_Obj yt, y0,
            yb, y1,
                y2;

    FLA_Part_2x2(L, &Ltl, &Ltr,
                    &Lbl, &Lbr, 0, 0, FLA_TL);
    FLA_Part_2x1(x, &xt, &xb, 0, FLA_TOP);
    FLA_Part_2x1(y, &yt, &yb, 0, FLA_TOP);

    while (FLA_Obj_length(Ltl) < FLA_Obj_length(L)) {
        FLA_Repart_2x2_to_3x3(Ltl, /**/ Ltr, &L00,  /**/ &l01,   &L02,
                              /************/ /***********************/
                                             &l10t, /**/ &ell11, &l12,
                              Lbl, /**/ Lbr, &L20,  /**/ &l21,   &L22,
                              1, 1, FLA_BR);
        FLA_Repart_2x1_to_3x1(xt, &x0,
                              /******/
                                  &x1,
                              xb, &x2,
                              1, FLA_BOTTOM);
        FLA_Repart_2x1_to_3x1(yt, &y0,
                              /*******/
                                  &y1,
                              yb, &y2,
                              1, FLA_BOTTOM);

        // l01 is all zeros, so no need to update y0

        // y1 += ell11 * x1
        FLA_Mult_add(ell11, x1, y1);

        // y2 += l21 * x1
        FLA_Axpy(x1, l21, y2);

        // Borrowed from libflame's trinv ln, variant 1
        // l21 = -l21 / ell11;
        FLA_Scal(FLA_MINUS_ONE, l21);
        FLA_Inv_scal(ell11, l21);

        // A20 = a21 * a10t + A20;
        FLA_Ger(FLA_ONE, l21, l10t, L20);

        // a10t = a10t / alpha11;
        FLA_Inv_scal(ell11, l10t);

        // alpha11 = 1.0 / alpha11;
        FLA_Invert(FLA_NO_CONJUGATE, ell11);

        FLA_Cont_with_3x1_to_2x1(&yt, y0,
                                      y1,
                                 /******/
                                 &yb, y2,
                                 FLA_TOP);
        FLA_Cont_with_3x1_to_2x1(&xt, x0,
                                      x1,
                                 /******/
                                 &xb, x2,
                                 FLA_TOP);
        FLA_Cont_with_3x3_to_2x2(&Ltl, /**/ &Ltr, L00,  l01,   /**/  L02,
                                                  l10t, ell11, /**/ l12,
                                 /**************/ /********************/
                                 &Lbl, /**/ &Lbr, L20,  l21,   /**/ L22,
                                 FLA_TL);
    }
    return FLA_SUCCESS;
}

FLA_Error obvious_alg(FLA_Obj L, FLA_Obj x, FLA_Obj y) {
    FLA_Trmvsx(FLA_LOWER_TRIANGULAR, FLA_NO_TRANSPOSE, FLA_NONUNIT_DIAG,
               FLA_ONE, L, x,
               FLA_ONE, y);
    FLA_Trinv(FLA_LOWER_TRIANGULAR, FLA_NONUNIT_DIAG, L);
    return FLA_SUCCESS;
}

#define N 500
int main() {
    FLA_Obj L1, L2, x, y1, y2;

    FLA_Init();

    srand(time(NULL));

    FLA_Obj_create(FLA_DOUBLE, N, N, 1, N, &L1);
    FLA_Obj_create(FLA_DOUBLE, N, 1, 1, N, &x);
    FLA_Obj_create(FLA_DOUBLE, N, 1, 1, N, &y1);

    FLA_Random_tri_matrix(FLA_LOWER_TRIANGULAR, FLA_NONUNIT_DIAG, L1);
    FLA_Random_matrix(x);
    FLA_Set(FLA_ZERO, y1);

    FLA_Obj_create_copy_of(FLA_NO_TRANSPOSE, L1, &L2);
    FLA_Obj_create_copy_of(FLA_NO_TRANSPOSE, y1, &y2);

    // FLA_Obj_show("L:", L1, "%6.3e", "");

    my_alg(L1, x, y1);
    obvious_alg(L2, x, y2);

    // FLA_Obj_show("L^{-1}:", L1, "%6.3e", "");

    double l_diff = FLA_Max_elemwise_diff(L1, L2);
    double y_diff = FLA_Max_elemwise_diff(y1, y2);
    printf("L max diff: %e\ny max diff: %e\n", l_diff, y_diff);

    FLA_Obj_free(&L1);
    FLA_Obj_free(&L2);
    FLA_Obj_free(&x);
    FLA_Obj_free(&y1);
    FLA_Obj_free(&y2);

    FLA_Finalize();
    return 0;
}
