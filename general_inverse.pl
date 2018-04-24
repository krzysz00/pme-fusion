#!/usr/bin/env swipl
:- use_module(pme_fusion).

:- initialization(main, main).

lu_pme(Out) :-
    Out = [ltl-[op([in(atl)], [out(ltl)])],
           utl-[noop([out(ltl)], [out(utl)])],
           lbl-[fn([in(abl), out(utl)], [out(lbl)])],
           utr-[fn([in(abr), out(ltl)], [out(utr)])],
           abr-[fn([in(abr), out(lbl), out(utr)], [during(abr, 0)])],
           lbr-[op([during(abr, 0)], [out(lbr)])],
           ubr-[noop([out(lbr)], [out(ubr)])],
           atl-[], atr-[], abl-[]].

lower_tri_inv_pme(Out) :-
    Out = [ltl-[op([in(ltl)], [out(ltl)])],
           lbl-[fn([any([in(ltl), out(ltl)]),
                    any([in(lbl), during(lbl, 0, b)])],
                   [during(lbl, 0, a)]),
                fn([any([in(lbr), out(lbr)]),
                    any([in(lbl), during(lbl, 0, a)])],
                   [during(lbl, 0, b)])],
           lbr-[op([in(lbr)], [out(lbr)])]].

upper_tri_inv_pme(Out) :-
    Out = [utl-[op([in(utl)], [out(utl)])],
           utr-[fn([any([in(utl), out(utl)]),
                    any([in(utr), during(utr, 0, b)])],
                   [during(utr, 0, a)]),
                fn([any([in(ubr), out(ubr)]),
                    any([in(utr), during(utr, 0, a)])],
                   [during(utr, 0, b)])],
           ubr-[op([in(ubr)], [out(ubr)])]].

trtrmm_pme(Out) :-
    Out = [atl-[op([in(ltl), in(utl)], [out(atl)])],
           atr-[op([in(ltl), in(utr)], [out(atr)])],
           abl-[op([in(lbl), in(utl)], [out(abl)])],
           abr-[op([in(lbl), in(utr)], [during(abr, 0, a)]),
                op([in(lbr), in(ubr)], [during(abr, 0, b)])]].

lu_factorization :-
    lu_pme(LU_PME),
    add_empty_regions(
        [atl, atr, abl, abr, ltl, lbl, lbr, utl, utr, ubr],
        [LU_PME], PMEs),
    test_pmes_dedup(PMEs).

lower_tri_inv :-
    lower_tri_inv_pme(Linv_PME),
    test_pmes_dedup([Linv_PME]).

lu_then_invert :-
    lu_pme(LU_PME), lower_tri_inv_pme(LInv_PME), upper_tri_inv_pme(UInv_PME),
    add_empty_regions([atl, atr, abl, abr, ltl, lbl, lbr, utl, utr, ubr],
                         [LU_PME, LInv_PME, UInv_PME], PMEs),
    test_pmes_dedup(PMEs).

general_inverse :-
    lu_pme(LU_PME),
    lower_tri_inv_pme(LInv_PME), upper_tri_inv_pme(UInv_PME),
    trtrmm_pme(TrTrMM_PME),
    add_empty_regions([atl, atr, abl, abr, ltl, lbl, lbr, utl, utr, ubr],
                         [LU_PME, LInv_PME, UInv_PME, TrTrMM_PME], PMEs),
    test_pmes_dedup(PMEs).

main :- general_inverse.
