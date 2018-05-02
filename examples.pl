#!/usr/bin/env swipl

:- use_module(pme_fusion).

:- consult(pmes).

:- initialization(main, main).

cholesky :-
    format("Cholesky:~n"),
    cholesky_pme(ltl,      ltl,
                 lbl, lbr, lbl, lbr, PME),
    test_pmes([PME], 3).

trinv :-
    format("Triangular inverse (mostly TL->BR):~n"),
    trinv_l_pme(ltl,      ltl,
                lbl, lbr, lbl, lbr, PME),
    test_pme(PME, 5).

chol_trinv :-
    format("CHOL + TrInv:~n"),
    cholesky_pme(ltl,      ltl,
                 lbl, lbr, lbl, lbr, Chol_PME),
    trinv_l_pme(ltl,      ltl,
                lbl, lbr, lbl, lbr, Inv_PME),
    test_pmes([Chol_PME, Inv_PME], 3).

symm_inv :-
    format("CHOL + TrInv + TrTrMM (symmetric inverse):~n"),
    cholesky_pme(ltl,      ltl,
                 lbl, lbr, lbl, lbr, Chol_PME),
    trinv_l_pme(ltl,      ltl,
                lbl, lbr, lbl, lbr, Inv_PME),
    l_transpose_l_times_l_pme(ltl,
                              lbl, lbr, Mul_PME),
    test_pmes([Chol_PME, Inv_PME, Mul_PME], 1).

sylvester :-
    test_pme([c_bl-[op_eq(tilde(c_bl), omega(a_bl, b_bl, hat(c_bl)))],
              c_tl-[eq(during(c_tl, 0), sub(hat(c_tl), mul(a_tr, tilde(c_bl)))),
                    op_eq(tilde(c_tl), omega(a_tl, b_tl, during(c_tl, 0)))],
              c_br-[eq(during(c_br, 0), sub(hat(c_br), mul(tilde(c_bl), b_tr))),
                    op_eq(tilde(c_br), omega(a_br, b_br, during(c_br, 0)))],
              c_tr-[eq(during(c_tr, 0, a),
                       sub(any([hat(c_tr), during(c_tr, 0, b)]),
                           mul(a_tr, tilde(c_br)))),
                    eq(during(c_tr, 0, b),
                       sub(any([hat(c_tr), during(c_tr, 0, a)]),
                           mul(tilde(c_tl), b_tr))),
                    % All could have been omitted, or a list, or any other name
                    op_eq(out(c_tr), omega(a_tr, b_tr, all(during(c_tr, 0, a), during(c_tr, 0, b))))]],
             16).

true_dependency :-
    format("True dependency check (Trinv + Trmv):~n"),
    trinv_l_pme(ltl,      rtl,
                lbl, lbr, rbl, rbr, Inv_PME),
    trmv_l_pme(yt, rtl,      xt,
               yb, rbl, rbr, xb, Mul_PME),
    add_empty_regions([ltl, lbl, lbr, rtl, rbl, rbr,
                       xt, xb, yt, yb], [Inv_PME, Mul_PME], PMEs),
    test_pmes(PMEs, 8).

anti_dependency :-
    format("Anti-dependency check (Trmv + Trinv):~n"),
    trmv_l_pme(yt, ltl,      xt,
               yb, lbl, lbr, xb, Mul_PME),
    trinv_l_pme(ltl,      ltl,
                lbl, lbr, lbl, lbr, Inv_PME),
    add_empty_regions([ltl, lbl, lbr, xt, xb, yt, yb],
                      [Mul_PME, Inv_PME], PMEs),
    test_pmes(PMEs, 7).

main :-
    cholesky,
    trinv,
    chol_trinv,
    symm_inv,
    sylvester,
    true_dependency,
    anti_dependency.
