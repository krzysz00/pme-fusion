#!/usr/bin/env swipl
:- use_module(pme_fusion).

:- consult(common_task_lists).

:- initialization(main, main).

gemv_part_mn_tasks(OutT, MatT, InT,
                   OutB, MatB, InB,
                   Ret) :-
    Ret = [op_eq(tilde(OutT), mul([hat(InT), hat(InB)], hat(MatT))),
           op_eq(tilde(OutB), mul([hat(InT), hat(InB)], hat(MatB)))].

gemm_part_m_tasks(CT, AT, B,
                  CB, AB,   Ret) :-
    Ret = [op_eq(tilde(CT), mul(hat(AT), hat(B))),
           op_eq(tilde(CB), mul(hat(AB), hat(B)))].

gemm_part_mn_sym_comp_ut_tasks(CTL,      AT, BL, BR,
                               CBL, CBR, AB,        Ret) :-
    Ret = [op_eq(tilde(CTL), mul(hat(AT), hat(BL))),
           op_eq(tilde(CBL), mul(hat(AT), hat(BR))),
           % op_eq(tilde(CBL), mul(hat(AB), hat(BL))),
           op_eq(tilde(CBR), mul(hat(AB), hat(BR)))].

vlower_tri_solve_tasks(Atl,      Xt, Bt,
                       Abl, Abr, Xb, Bb, Ret) :-
    Ret = [op_eq(tilde(Xt), trslv(hat(Atl), hat(Bt))),
           eq(during(Xb, 0), sub(hat(Bb), mul(hat(Abl), tilde(Xt)))),
           op_eq(tilde(Xb), trslv(hat(Abr), during(Xb, 0)))].

vupper_tri_solve_tasks(Atl, Atr, Xt, Bt,
                            Abr, Xb, Bb, Ret) :-
    Ret = [op_eq(tilde(Xb), trslv(hat(Abr), hat(Bb))),
           eq(during(Xt, 0), sub(hat(Bt), mul(hat(Atr), tilde(Xt)))),
           op_eq(tilde(Xt), trslv(hat(Atl), during(Xt, 0)))].

%% Steps: computation of y and Y is ignored because it's better to have it than to try to fuse with it
%% We can fuse v0, the Chol, and the solve - also M1 (M2), M3, and the solve for M4
%% Then the ut solves and gem[m/v]s

kalman_relevant :-
    gemm_part_m_tasks(tt, ht, p,
                      tb, hb, TTasks),
    gemm_part_m_tasks(vt, ht, x,
                      vb, hb, V_mulTasks),
    gemm_part_mn_sym_comp_ut_tasks(ltl,      tt, ht, hb,
                                   lbl, lbr, tb,        L_mulTasks),
    cholesky_tasks(ltl,      ltl,
                   lbl, lbr, lbl, lbr, CholTasks),
    vlower_tri_solve_tasks(ltl,      tt, tt,
                           lbl, lbr, tb, tb, Solve_MTasks),
    vlower_tri_solve_tasks(ltl,      vt, vt,
                           lbl, lbr, vb, vb, Solve_vTasks),


    gen_invariants([TTasks, V_mulTasks, L_mulTasks,
                    CholTasks, Solve_MTasks, Solve_vTasks]).

kalman_no_fusion :-
    gemm_part_m_tasks(tt, ht, p,
                      tb, hb, TTasks),
    gemm_part_m_tasks(vt, ht, x,
                      vb, hb, V_mulTasks),
    gemm_part_mn_sym_comp_ut_tasks(ltl,      tt, ht, hb,
                                   lbl, lbr, tb,        L_mulTasks),
    cholesky_tasks(ltl,      ltl,
                   lbl, lbr, lbl, lbr, CholTasks),
    vlower_tri_solve_tasks(ltl,      mt, tt,
                           lbl, lbr, mb, tb, Solve_MTasks),
    vlower_tri_solve_tasks(ltl,      vt, vt,
                           lbl, lbr, vb, vb, Solve_vTasks),
    vupper_tri_solve_tasks(ltl, lbl, mt, mt,
                                lbr, mb, mb, Solve_M2Tasks),
    vupper_tri_solve_tasks(ltl, lbl, vt, vt,
                                lbr, vb, vb, Solve_v2Tasks),

    gen_invariants([TTasks, V_mulTasks, L_mulTasks,
                    CholTasks, Solve_MTasks, Solve_vTasks,
                    Solve_M2Tasks, Solve_v2Tasks]).

%% Upper triangular solve must go bottom to top, so everything dies after this
