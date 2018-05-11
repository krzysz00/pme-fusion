cholesky_tasks(InTl,       OutTl,
               InBl, InBr, OutBl, OutBr,
               Ret) :-
    Ret = [op_eq(tilde(OutTl), chol(hat(InTl))),

           eq(tilde(OutBl), trsm(tilde(OutTl), hat(InBl))),

           eq(during(OutBr, 0), sub(hat(InBr), mul(tilde(OutBl), tr(tilde(OutBl))))),
           op_eq(tilde(OutBr), chol(during(OutBr, 0)))].

%% NOTE: the hat(br) and tilde(tl) in the bl terms can be any([hat(X), tilde(X)])
%% which will ensure generality
%% Also works for upper triangular matrises
trinv_tasks(InTl,       OutTl,
            InBl, InBr, OutBl, OutBr,
            Ret) :-
    Ret = [op_eq(tilde(OutTl), inverse(hat(InTl))),

           eq(during(OutBl, 0, a),
              mul(any([during(OutBl, 0, b), hat(InBl)]), tilde(OutTl))),
           eq(during(OutBl, 0, b),
              mul(any([during(OutBl, 0, a), hat(InBl)]), hat(InBr))),

           op_eq(tilde(OutBr), inverse(hat(InBr)))].

l_transpose_l_times_l_tasks(Tl,
                            Bl, Br, Ret) :-
    Ret = [op_eq(during(Tl, 0), mul(tr(hat(Tl)), hat(Tl))),
           eq(tilde(Tl), add(during(Tl, 0), mul(tr(hat(Bl)), hat(Bl)))),

           eq(tilde(Bl), mul(hat(Bl), tr(hat(Br)))),

           op_eq(tilde(Br), mul(hat(Br), tr(hat(Br))))].

trtrmm_ul_tasks(ATl, ATr, UTl, UTr, LTl,
                ABl, ABr,      UBr, LBl, LBr,
                Ret) :-
    Ret = [op_eq(during(ATl, 0, a), add(mul(hat(UTl), hat(LTl)),
                                        any([hat(ATl), during(ATl, 0, b)]))),
           eq(during(ATl, 0, b), add(mul(hat(UTr), hat(LBl)),
                                     any([hat(ATl), during(ATl, 0, a)]))),

           eq(tilde(ATr), add(hat(ATr), mul(hat(UTr), hat(LBr)))),
           eq(tilde(ABl), add(hat(ABl), mul(hat(UBr), hat(LBl)))),

           op_eq(tilde(ABr), add(hat(ABr), mul(hat(UBr), hat(LBr))))].

trmv_l_tasks(YT, ATl,      XT,
             YB, ABl, ABr, XB, Ret) :-
    Ret = [op_eq(tilde(YT), mul(hat(XT), hat(ATl))),

           eq(during(YB, 0, a),
              gemm(hat(ABl), hat(XT),
                   any([hat(YB), during(YB, 0, b)]))),

           op_eq(during(YB, 0, b),
                 gemm(hat(ABr), hat(XB),
                      any([hat(YB), during(YB, 0, a)])))].
