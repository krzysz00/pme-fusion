#!/usr/bin/env swipl
:- use_module('../pme_fusion').

:- consult(common_task_lists).

:- initialization(main, main).

%% PME section for M += (AB + CD) + (EF + GH)
%% Everything but M is a hatless constant
big_mul_clause(M, A, B, C, D, E, F, G, H, FirstIsOp, Out) :-
    (FirstIsOp == true -> Op1 = op_eq; Op1 = eq),
    Op1Args = [during(M, 0, a),
               add(any([hat(M), during(M, 0, b)]), add(mul(hat(A), hat(B)),
                                                       mul(hat(C), hat(D))))],
    compound_name_arguments(Task1, Op1, Op1Args),
    Task2 = eq(during(M, 0, b), add(any([hat(M), during(M, 0, a)]),
                                    add(mul(hat(E), hat(F)),
                                        mul(hat(G), hat(H))))),
    Out = [Task1, Task2].

op_1_tasks(Out) :-
    big_mul_clause(a_tl, a_tl, m_tl, m_tl, a_tl,
                   a_tr, m_tr, m_tr, a_tr, true, CTl),
    big_mul_clause(a_tr, a_tl, m_tr, m_tl, a_tr,
                   a_tr, m_br, m_tr, a_br, false, CTr),
    big_mul_clause(a_br, a_br, m_br, m_br, a_br,
                   a_tr, m_tr, m_tr, a_tr, true, CBr),
    flatten([CTl, CTr, CBr], Out).

%% PME section for M -= AB - CD
%% Everything but M is a hatless constant
mul_clause(M, A, B, C, D, FirstIsOp, Out) :-
    (FirstIsOp == true -> Op1 = op_eq; Op1 = eq),
    Op1Args = [during(M, 0, a),
               sub(any([hat(M), during(M, 0, b)]), mul(hat(A), hat(B)))],
    compound_name_arguments(Task1, Op1, Op1Args),
    Task2 = eq(during(M, 0, b), sub(any([hat(M), during(M, 0, a)]),
                                    mul(hat(C), hat(D)))),
    Out = [Task1, Task2].

op_2_tasks(Out) :-
    mul_clause(a_tl, m_tl, m_tl, m_tr, m_tr, true, CTl),
    mul_clause(a_tr, m_tl, m_tr, m_tr, m_br, false, CTr),
    mul_clause(a_br, m_br, m_br, m_tr, m_tr, true, CBr),
    flatten([CTl, CTr, CBr], Out).

solve :-
    op_1_tasks(Op1),
    op_2_tasks(Op2),
    gen_invariants([Op1, Op2]).

main :- solve.

