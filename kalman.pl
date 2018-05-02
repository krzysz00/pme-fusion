:- use_module(pme_fusion).

gemv_pme(OutT, MatTL, MatTR, InT,
         OutB, MatBL, MatBR, InB,
         Out) :-
    Out = [OutT-[op([in(InT), in(MatTL), any([in(OutT), during(OutT, 0, b)])], [during(OutT, 0, a)]),
                 op([in(InB), in(MatTR), any([in(OutT), during(OutT, 0, a)])], [during(OutT, 0, b)])],
           OutB-[op([in(InT), in(MatBL), any([in(OutB), during(OutB, 0, b)])], [during(OutB, 0, a)]),
                 op([in(InB), in(MatBR), any([in(OutB), during(OutB, 0, a)])], [during(OutB, 0, b)])]].

gemv_part_mn_pme(OutT, MatT, InT,
                 OutB, MatB, InB,
                 Out) :-
    Out = [OutT-[op([in(InT), in(InB), in(MatT)], [out(OutT)])],
           OutB-[op([in(InT), in(InB), in(MatB)], [out(OutB)])]].

gemm_part_m_pme(CT, AT, B,
                CB, AB,   Out) :-
    Out = [CT-[op([in(B), in(AT)], [out(CT)])],
           CB-[op([in(B), in(AB)], [out(CB)])]].

gemm_part_mn_sym_comp_ut_pme(CTL,      AT, BL, BR,
                             CBL, CBR, AB,        Out) :-
    Out = [CTL-[op([in(AT), in(BL)], [out(CTL)])],
           CBL-[op([in(AT), in(BR)], [out(CBL)])],
%           CBL-[op([in(AB), in(BL)], [out(CBL)])],
           CBR-[op([in(AB), in(BR)], [out(CBR)])]].

cholesky_pme(InTl,       OutTl,
             InBl, InBr, OutBl, OutBr, Out) :-
    Out = [OutTl-[op([in(InTl)], [out(OutTl)])],
           OutBl-[fn([in(InBl), out(OutTl)], [out(OutBl)])],
           OutBr-[fn([in(InBr), out(OutBl)], [during(OutBr, 0)]),
                  op([during(OutBr, 0)], [out(OutBr)])]].

vlower_tri_solve_pme(Atl,      Xt, Bt,
                     Abl, Abr, Xb, Bb, Out) :-
    Out = [Xt-[op([in(Atl), in(Bt)], [out(Xt)])],
           Xb-[fn([in(Abl), in(Bb), out(Xt)], [during(Xb, 0)]),
               op([in(Abr), during(Xb, 0)], [out(Xb)])]].

vupper_tri_solve_pme(Atl, Atr, Xt, Bt,
                          Abr, Xb, Bb, Out) :-
    Out = [Xb-[op([in(Abr), in(Bb)], [out(Xb)])],
           Xt-[fn([in(Atr), in(Bt), out(Xb)], [during(Xt, 0)]),
               op([in(Atl), during(Xt, 0)], [out(Xt)])]].

%% Steps: computation of y and Y is ignored because it's better to have it than to try to fuse with it
%% We can fuse v0, the Chol, and the solve - also M1 (M2), M3, and the solve for M4
%% Then the ut solves and gem[m/v]s

kalman_relevant :-
    gemm_part_m_pme(tt, ht, p,
                    tb, hb, T_PME),
    gemm_part_m_pme(vt, ht, x,
                    vb, hb, V_mul_PME),
    gemm_part_mn_sym_comp_ut_pme(ltl,      tt, ht, hb,
                                 lbl, lbr, tb,        L_mul_PME),
    cholesky_pme(ltl,      ltl,
                 lbl, lbr, lbl, lbr, Chol_PME),
    vlower_tri_solve_pme(ltl,      tt, tt,
                         lbl, lbr, tb, tb, Solve_M_PME),
    vlower_tri_solve_pme(ltl,      vt, vt,
                         lbl, lbr, vb, vb, Solve_v_PME),

    add_empty_regions([tt, tb, ht, hb, p, x,
                       ltl, lbl, lbr,
                       mt, mb, vt, vb],
                      [T_PME, V_mul_PME, L_mul_PME,
                       Chol_PME, Solve_M_PME, Solve_v_PME], PMEs),
    test_pmes(PMEs).

kalman_no_fusion :-
    gemm_part_m_pme(tt, ht, p,
                    tb, hb, T_PME),
    gemm_part_m_pme(vt, ht, x,
                    vb, hb, V_mul_PME),
    gemm_part_mn_sym_comp_ut_pme(ltl,      tt, ht, hb,
                                 lbl, lbr, tb,        L_mul_PME),
    cholesky_pme(ltl,      ltl,
                 lbl, lbr, lbl, lbr, Chol_PME),
    vlower_tri_solve_pme(ltl,      mt, tt,
                         lbl, lbr, mb, tb, Solve_M_PME),
    vlower_tri_solve_pme(ltl,      vt, vt,
                         lbl, lbr, vb, vb, Solve_v_PME),
    vupper_tri_solve_pme(ltl, lbl, mt, mt,
                              lbr, mb, mb, Solve_M2_PME),
    vupper_tri_solve_pme(ltl, lbl, vt, vt,
                              lbr, vb, vb, Solve_v2_PME),

    add_empty_regions([tt, tb, ht, hb, p, x,
                       ltl, lbl, lbr,
                       mt, mb, vt, vb],
                      [T_PME, V_mul_PME, L_mul_PME,
                       Chol_PME, Solve_M_PME, Solve_v_PME,
                       Solve_M2_PME, Solve_v2_PME], PMEs),
    test_pmes(PMEs).

%% Upper triangular solve must go bottom to top, so everything dies after this
