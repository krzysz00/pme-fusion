:- use_module(pme_fusion).

cholesky_pme(Out) :-
    Out = [ltl-[op([in(mtl)], [out(ltl)])],
           lbl-[fn([in(mbl), out(ltl)], [out(lbl)])],
           lbr-[fn([in(mbr), out(lbl)], [during(lbr, 0)]),
                op([during(lbr, 0)], [out(lbr)])]].

lower_tri_solve_pme(Out) :-
    Out = [v1t-[op([in(ltl), in(v0t)], [out(v1t)])],
           v1b-[fn([in(v0b), in(lbl), out(v1t)], [during(v1b, 0)]),
                op([in(lbr), during(v1b, 0)], [out(v1b)])]].

kalman :-
    cholesky_pme(Cholesky_PME),
    lower_tri_solve_pme(LowerTriSolve_PME),
    add_empty_regions([mtl, mbl, mbr, ltl, lbl, lbr,
                       v0t, v0b, v1t, v1b],
                      [Cholesky_PME, LowerTriSolve_PME], PMEs),
    test_pmes_dedup(PMEs).

%% Upper triangular solve must go bottom to top, so everything dies after this
