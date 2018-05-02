#!/usr/bin/env swipl
:- use_module(pme_fusion).

:- consult(pmes).

:- initialization(main, main).

gemv_part_mn_pme(OutT, MatT, InT,
                 OutB, MatB, InB,
                 Ret) :-
    Ret = [OutT-[op_eq(tilde(OutT), mul([hat(InT), hat(InB)], hat(MatT)))],
           OutT-[op_eq(tilde(OutB), mul([hat(InT), hat(InB)], hat(MatB)))]].

gemm_part_m_pme(CT, AT, B,
                CB, AB,   Ret) :-
    Ret = [CT-[op_eq(tilde(CT), mul(hat(AT), hat(B)))],
           CB-[op_eq(tilde(CB), mul(hat(AB), hat(B)))]].

gemm_part_mn_sym_comp_ut_pme(CTL,      AT, BL, BR,
                             CBL, CBR, AB,        Ret) :-
    Ret = [CTL-[op_eq(tilde(CTL), mul(hat(AT), hat(BL)))],
           CBL-[op_eq(tilde(CBL), mul(hat(AT), hat(BR)))],
           % CBL-[op_eq(tilde(CBL), mul(hat(AB), hat(BL)))],
           CBR-[op_eq(tilde(CBR), mul(hat(AB), hat(BR)))]].

vlower_tri_solve_pme(Atl,      Xt, Bt,
                     Abl, Abr, Xb, Bb, Ret) :-
    Ret = [Xt-[op_eq(tilde(Xt), trslv(hat(Atl), hat(Bt)))],
           Xb-[eq(during(Xb, 0), sub(hat(Bb), mul(hat(Abl), tilde(Xt)))),
               op_eq(tilde(Xb), trslv(hat(Abr), during(Xb, 0)))]].

vupper_tri_solve_pme(Atl, Atr, Xt, Bt,
                          Abr, Xb, Bb, Ret) :-
    Ret = [Xb-[op_eq(tilde(Xb), trslv(hat(Abr), hat(Bb)))],
           Xb-[eq(during(Xt, 0), sub(hat(Bt), mul(hat(Atr), tilde(Xt)))),
               op_eq(tilde(Xt), trslv(hat(Atl), during(Xt, 0)))]].

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
    gen_invariants(PMEs).

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
    gen_invariants(PMEs).

%% Upper triangular solve must go bottom to top, so everything dies after this
