cholesky_pme(InTl,       OutTl,
             InBl, InBr, OutBl, OutBr,
             Ret) :-
    Ret = [OutTl-[op_eq(tilde(OutTl), chol(hat(InTl)))],
           OutBl-[eq(tilde(OutBl), trsm(tilde(OutTl), hat(InBl)))],
           OutBr-[eq(during(OutBr, 0), sub(hat(InBr), mul(tilde(OutBl), tr(tilde(OutBl))))),
                  op_eq(tilde(OutBr), chol(during(OutBr, 0)))]].

%% NOTE: the hat(br) and tilde(tl) in the bl terms can be any([hat(X), tilde(X)])
%% which will ensure generality
trinv_l_pme(InTl,       OutTl,
            InBl, InBr, OutBl, OutBr,
            Ret) :-
    Ret = [OutTl-[op_eq(tilde(OutTl), inverse(hat(InTl)))],
           OutBl-[eq(during(OutBl, 0, a),
                      mul(any([during(OutBl, 0, b), hat(InBl)]), tilde(OutTl))),
                  eq(during(OutBl, 0, b),
                      mul(any([during(OutBl, 0, a), hat(InBl)]), hat(InBr)))],
           OutBr-[op_eq(tilde(OutBr), inverse(hat(InBr)))]].

l_transpose_l_times_l_pme(Tl,
                          Bl, Br, Ret) :-
    Ret = [Tl-[op_eq(during(Tl, 0), mul(tr(hat(Tl), hat(Tl)))),
               eq(tilde(Tl), add(during(Tl, 0), mul(tr(hat(Bl), hat(Bl)))))],
           Bl-[eq(tilde(Bl), mul(hat(Bl), tr(hat(Br))))],
           Br-[op_eq(tilde(Br), mul(hat(Br), tr(hat(Br))))]].

trmv_l_pme(YT, ATl,      XT,
       YB, ABl, ABr, XB, Ret) :-
    Ret = [YT-[op_eq(tilde(YT), mul(hat(XT), hat(ATl)))],
           YB-[op_eq(during(YB, 0, a),
                     gemm(hat(ABl), hat(XT),
                          any([hat(YB), during(YB, 0, b)]))),
               op_eq(during(YB, 0, b),
                     gemm(hat(ABr), hat(XB),
                          any([hat(YB), during(YB, 0, a)])))]].
