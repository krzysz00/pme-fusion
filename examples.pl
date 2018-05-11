#!/usr/bin/env swipl

:- use_module(pme_fusion).

:- consult(common_task_lists).

:- initialization(main, main).

cholesky :-
    format("Cholesky:~n"),
    cholesky_tasks(ltl,      ltl,
                   lbl, lbr, lbl, lbr, Tasks),
    test_task_lists([Tasks], 3).

trinv :-
    format("Triangular inverse (mostly TL->BR):~n"),
    trinv_tasks(ltl,      ltl,
                lbl, lbr, lbl, lbr, Tasks),
    test_task_list(Tasks, 5).

chol_trinv :-
    format("CHOL + TrInv:~n"),
    cholesky_tasks(ltl,      ltl,
                 lbl, lbr, lbl, lbr, CholTasks),
    trinv_tasks(ltl,      ltl,
                lbl, lbr, lbl, lbr, InvTasks),
    test_task_lists([CholTasks, InvTasks], 3).

symm_inv :-
    format("CHOL + TrInv + TrTrMM (symmetric inverse):~n"),
    cholesky_tasks(ltl,      ltl,
                 lbl, lbr, lbl, lbr, CholTasks),
    trinv_tasks(ltl,      ltl,
                lbl, lbr, lbl, lbr, InvTasks),
    l_transpose_l_times_l_tasks(ltl,
                              lbl, lbr, MulTasks),
    test_task_lists([CholTasks, InvTasks, MulTasks], 1).

sylvester :-
    test_task_list([op_eq(tilde(c_bl), omega(a_bl, b_bl, hat(c_bl))),

                    eq(during(c_tl, 0), sub(hat(c_tl), mul(a_tr, tilde(c_bl)))),
                    op_eq(tilde(c_tl), omega(a_tl, b_tl, during(c_tl, 0))),

                    eq(during(c_br, 0), sub(hat(c_br), mul(tilde(c_bl), b_tr))),
                    op_eq(tilde(c_br), omega(a_br, b_br, during(c_br, 0))),

                    eq(during(c_tr, 0, a),
                       sub(any([hat(c_tr), during(c_tr, 0, b)]),
                           mul(a_tr, tilde(c_br)))),
                    eq(during(c_tr, 0, b),
                       sub(any([hat(c_tr), during(c_tr, 0, a)]),
                           mul(tilde(c_tl), b_tr))),
                    % All could have been omitted, or a list, or any other name
                    op_eq(tilde(c_tr), omega(a_tr, b_tr, all(during(c_tr, 0, a), during(c_tr, 0, b))))],
             16).

true_dependency :-
    format("True dependency check (Trinv + Trmv):~n"),
    trinv_tasks(ltl,      rtl,
                lbl, lbr, rbl, rbr, InvTasks),
    trmv_l_tasks(yt, rtl,      xt,
                 yb, rbl, rbr, xb, MulTasks),
    test_task_lists([InvTasks, MulTasks], 7).

anti_dependency :-
    format("Anti-dependency check (Trmv + Trinv):~n"),
    trmv_l_tasks(yt, ltl,      xt,
               yb, lbl, lbr, xb, MulTasks),
    trinv_tasks(ltl,      ltl,
                lbl, lbr, lbl, lbr, InvTasks),
    test_task_lists([MulTasks, InvTasks], 6).

main :-
    cholesky,
    trinv,
    chol_trinv,
    symm_inv,
    sylvester,
    true_dependency,
    anti_dependency.
