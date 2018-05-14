#!/usr/bin/env swipl
:- use_module('../pme_fusion').

:- consult(common_task_lists).

:- initialization(main, main).

lu_tasks(Out) :-
    Out = [% TL
        op_eq(tilde(ltl), lu(hat(atl))),
        comes_from(tilde(utl), tilde(ltl)),
        % BL
        eq(tilde(lbl), trsm(tilde(ltl), hat(lbl))),
        % TR
        eq(tilde(utr), trsm(tilde(ltl), hat(utr))),
        % BR
        eq(during(abr, 0), sub(hat(abr), mul(tilde(lbl), tilde(utr)))),
        op_eq(tilde(lbr), lu(during(abr, 0))),
        comes_from(tilde(ubr), tilde(lbr))].

lu_factorization :-
    lu_tasks(LUTasks),
    test_task_lists([LUTasks], 5).

lu_then_invert :-
    lu_tasks(LUTasks),
    trinv_tasks(ltl,      ltl,
                lbl, lbr, lbl, lbr, LInvTasks),
    trinv_tasks(utl,      utl,
                utr, ubr, utr, ubr, UInvTasks),
    test_task_lists([LUTasks, LInvTasks, UInvTasks], 5).

general_inverse :-
    lu_tasks(LUTasks),
    trinv_tasks(ltl,      ltl,
                lbl, lbr, lbl, lbr, LInvTasks),
    trinv_tasks(utl,      utl,
                utr, ubr, utr, ubr, UInvTasks),
    trtrmm_ul_tasks(atl, atr, utl, utr, ltl,
                    abl, abr,      ubr, lbl, lbr, TrTrMMTasks),
    test_task_lists([LUTasks, LInvTasks, UInvTasks, TrTrMMTasks], 5).

main :- general_inverse.
