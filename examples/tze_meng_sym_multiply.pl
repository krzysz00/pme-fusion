#!/usr/bin/env swipl
:- use_module('../pme_fusion').

:- consult(common_task_lists).

:- initialization(main, main).

%% PME section for M += (AB + CD) + (EF + GH)
%% Everything but M is a hatless constant
big_mul_clause(M, A, B, C, D, E, F, G, H, FirstIsOp, Out) :-
    (FirstIsOp == true -> Op1 = op_eq; Op1 = eq),
    Op1Args = [during(M, 0, a),
               add(any([hat(M), during(M, 0, b)]), add(mul(A, B), mul(C, D)))],
    compound_name_arguments(Task1, Op1, Op1Args),
    Task2 = eq(during(M, 0, b), add(any([hat(M), during(M, 0, a)]),
                                    add(mul(E, F), mul(G, H)))),
    Out = [Task1, Task2].

op_1_tasks(Out) :-
    big_mul_clause(c_tl, a_tl, m_tl, m_tl, a_tl,
                   a_tr, tr(m_tr), m_tr, tr(a_tr), true, CTl),
    big_mul_clause(c_tr, a_tl, m_tr, m_tl, tr(a_tr),
                   a_tr, m_br, tr(m_tr), a_br, false, CTr),
    big_mul_clause(c_br, a_br, m_br, m_br, a_br,
                   tr(a_tr), m_tr, tr(m_tr), a_tr, true, CBr),
    flatten([CTl, CTr, CBr], Out).

%% PME section for M -= AB - CD
%% Everything but M is a hatless constant
mul_clause(M, A, B, C, D, FirstIsOp, Out) :-
    (FirstIsOp == true -> Op1 = op_eq; Op1 = eq),
    Op1Args = [during(M, 0, a),
               sub(any([hat(M), during(M, 0, b)]), mul(A, B))],
    compound_name_arguments(Task1, Op1, Op1Args),
    Task2 = eq(during(M, 0, b), sub(any([hat(M), during(M, 0, a)]),
                                    mul(C, D))),
    Out = [Task1, Task2].

op_2_tasks(Out) :-
    mul_clause(c_tl, m_tl, m_tl, m_tr, tr(m_tr), true, CTl),
    mul_clause(c_tr, m_tl, m_tr, m_tr, m_br, false, CTr),
    mul_clause(c_br, m_br, m_br, tr(m_tr), m_tr, true, CBr),
    flatten([CTl, CTr, CBr], Out).

solve :-
    op_1_tasks(Op1),
    op_2_tasks(Op2),
    gen_invariants([Op1, Op2]).

leaves_dont_contain(Atom, Term) :-
    is_list(Term) -> (maplist(leaves_dont_contain(Atom), Term));
    compound(Term) -> (compound_name_arguments(Term, _, Args),
                       maplist(leaves_dont_contain(Atom), Args));
    Atom \== Term.

past_doesnt_contain(Atom, Region) :-
    leaves_dont_contain(Atom, Region.past).

solve_no_br :-
    op_1_tasks(Op1),
    op_2_tasks(Op2),
    findall(Invariants,
            (make_pmes([Op1, Op2], Invariants),
             fused_invariants(Invariants),
             maplist(maplist(past_doesnt_contain(m_br)), Invariants),
             maplist(maplist(past_doesnt_contain(a_br)), Invariants)),
        Results),
    maplist(print_invariants_sep, Results),
    length(Results, ResLen),
    format("~d Invariants~n", [ResLen]).

main :- solve.
