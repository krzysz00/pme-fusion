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
    Out = [OutT-[op([in(InT), in(InB), in(MatT), in(OutT)], [out(OutT)])],
           OutB-[op([in(InT), in(InB), in(MatB), in(OutB)], [out(OutB)])]].

gemm_part_m_pme(CT, A, BT,
                CB,    BB, Out) :-
    Out = [CT-[op([in(A), in(BT), in(CT)], [out(CT)])],
           CB-[op([in(A), in(BB), in(CB)], [out(CB)])]].

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



%% Steps: computation of y and Y is ignored because it's better to have it than to try to fuse with it
%% We can fuse v0, the Chol, and the solve - also M1 (M2), M3, and the solve for M4
%% Then the ut solves and gem[m/v]s

kalman_relevant :-
    gemm_part_m_pme(tt, ht, p,
                    tb, hb, T_PME),
    gemv_part_mn_pme(vt, ht, xt,
                     vb, hb, xb, V_mul_PME),
    gemm_part_mn_sym_comp_ut_pme(ltl,      tt, ht, hb,
                                 lbl, lbr, tb,        L_mul_PME),
    cholesky_pme(ltl,      ltl,
                 lbl, lbr, lbl, lbr, Chol_PME),
    vlower_tri_solve_pme(ltl,      mt, tt,
                         lbl, lbr, mb, tb, Solve_M_PME),
    vlower_tri_solve_pme(ltl,      vt, vt,
                         lbl, lbr, vb, vb, Solve_v_PME),

    add_empty_regions([tt, tb, ht, hb, p, xt, xb,
                       ltl, lbl, lbr,
                       mt, mb, vt, vb],
                      [T_PME, V_mul_PME, L_mul_PME,
                       Chol_PME, Solve_M_PME, Solve_v_PME], PMEs),
    test_pmes(PMEs).


%% Upper triangular solve must go bottom to top, so everything dies after this
