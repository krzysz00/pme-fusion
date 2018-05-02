#!/usr/bin/env swipl
:- use_module(pme_fusion).

:- consult(pmes).

:- initialization(main, main).

lu_pme(Out) :-
    Out = [ltl-[op_eq(tilde(ltl), lu(hat(atl)))],
           utl-[comes_with(tilde(utl), tilde(ltl))],
           lbl-[eq(tilde(lbl), trsm(tilde(ltl), hat(lbl)))],
           utr-[eq(tilde(utr), trsm(tilde(ltl), hat(utr)))],
           abr-[eq(during(abr, 0), sub(hat(abr), mul(tilde(lbl), tilde(utr))))],
           lbr-[op_eq(tilde(lbr), lu(during(abr, 0)))],
           ubr-[comes_with(tilde(ubr), tilde(lbr))]].


lu_factorization :-
    lu_pme(LU_PME),
    add_empty_regions(
        [atl, atr, abl, abr, ltl, lbl, lbr, utl, utr, ubr],
        [LU_PME], PMEs),
    test_pmes_dedup(PMEs, 5).

lu_then_invert :-
    lu_pme(LU_PME),
    trinv_pme(ltl,      ltl,
              lbl, lbr, lbl, lbr, LInv_PME),
    trinv_pme(utl,      utl,
              utr, ubr, utr, ubr, UInv_PME),
    add_empty_regions([atl, atr, abl, abr, ltl, lbl, lbr, utl, utr, ubr],
                      [LU_PME, LInv_PME, UInv_PME], PMEs),
    test_pmes_dedup(PMEs, 5).

general_inverse :-
    lu_pme(LU_PME),
    trinv_pme(ltl,      ltl,
              lbl, lbr, lbl, lbr, LInv_PME),
    trinv_pme(utl,      utl,
              utr, ubr, utr, ubr, UInv_PME),
    trtrmm_ul_pme(atl, atr, utl, utr, ltl,
                  abl, abr,      ubr, lbl, lbr, TrTrMM_PME),
    add_empty_regions([atl, atr, abl, abr, ltl, lbl, lbr, utl, utr, ubr],
                      [LU_PME, LInv_PME, UInv_PME, TrTrMM_PME], PMEs),
    test_pmes_dedup(PMEs, 5).

main :- general_inverse.
