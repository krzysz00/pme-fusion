#!/usr/bin/env swipl

:- initialization(main, main).

is_status(computed).
is_status(uncomputed).
is_status(X) :- functor(X, partial, 2).

valid_used_out_partials__([], _, _) :- fail.
valid_used_out_partials__([Val-MaybeIdx|T], Idx, Var) :-
    MaybeIdx is Idx, Var = partial(used_out, Val);
    valid_used_out_partials__(T, Idx, Var).

valid_used_out_partials_([], _, _).
valid_used_out_partials_([Var|Vars], Idx, Deps) :-
    valid_used_out_partials__(Deps, Idx, Var);
    valid_used_out_partials_(Vars, Idx + 1, Deps).

valid_used_out_partials(Vars, Deps) :- valid_used_out_partials_(Vars, 0, Deps).

valid_used_in_partials__([], _, _) :- fail.
valid_used_in_partials__([MaybeIdx-Val|T], Idx, Var) :-
    MaybeIdx is Idx, Var = partial(used_in, Val);
    valid_used_in_partials__(T, Idx, Var).

valid_used_in_partials_([], _, _).
valid_used_in_partials_([Var|Vars], Idx, Deps) :-
    valid_used_in_partials__(Deps, Idx, Var);
    valid_used_in_partials_(Vars, Idx + 1, Deps).

valid_used_in_partials(Vars, Deps) :- valid_used_in_partials_(Vars, 0, Deps).

status_gt_prim(computed, uncomputed).
status_gt_prim(computed, partial(A, B)) :- nonvar(A), nonvar(B).
status_gt_prim(partial(A, B), uncomputed) :- nonvar(A), nonvar(B).
status_gt(X, Y) :- status_gt_prim(X, Y).
status_gt(X, Y) :- status_gt_prim(X, Z), status_gt(Z, Y).

status_ge(X, X).
status_ge(X, Y) :- status_gt(X, Y).

dependency_valid(Elems, M-N) :-
    nth0(M, Elems, X),
    nth0(N, Elems, Y),
    X \= partial(_, _),
    status_ge(X, Y).

antidependency_valid(Elems, M-N) :-
    nth0(M, Elems, X),
    nth0(N, Elems, Y),
    Y == uncomputed,
    status_ge(X, Y).

is_computed(computed).
is_uncomputed(uncomputed).

loop_valid(Deps, AntiDeps, Elems) :- % deps are pairs of indices
    valid_used_out_partials(Elems, Deps),
    valid_used_in_partials(Elems, AntiDeps),
    maplist(is_status, Elems),
    maplist(dependency_valid(Elems), Deps),
    maplist(antidependency_valid(Elems), AntiDeps),
    \+ maplist(is_computed, Elems),
    \+ maplist(is_uncomputed, Elems).

no_trashed_data_in_loop1([], _).
no_trashed_data_in_loop1([computed|T1], [_|T2]) :- !, no_trashed_data_in_loop1(T1, T2).
no_trashed_data_in_loop1([_|T1], [uncomputed|T2]) :- !, no_trashed_data_in_loop1(T1, T2).


% Make sure nothing that needs reading is overwritten
loop1_dep_unbroken(_, computed, computed, _, _) :- !.
loop1_dep_unbroken(_, _, _, uncomputed, uncomputed) :- !.
loop1_dep_unbroken(N, computed, partial(used_out, N), _, _) :- !.
% Dependency hasn't happened yet
loop1_dep_unbroken(_, computed, partial(_, _), uncomputed, uncomputed).

loop1_deps_unbroken([], _, _).
loop1_deps_unbroken([Write-Read|T], Elems1, Elems2) :-
    nth0(Write, Elems1, Write1),
    nth0(Read, Elems1, Read1),
    nth0(Write, Elems2, Write2),
    nth0(Read, Elems2, Read2),
    loop1_dep_unbroken(Write, Write1, Read1, Write2, Read2),
    loop1_deps_unbroken(T, Elems1, Elems2).

% anti-dependencies in loop 1 are satisfied because there's a forced "uncomputed" in there

loop2_anti_dep_unbroken(_, _, _, uncomputed, uncomputed) :- !.
loop2_anti_dep_unbroken(_, computed, computed, computed, _) :- !.
loop2_anti_dep_unbroken(_, computed, _, partial(used_out, _), _) :- !.
loop2_anti_dep_unbroken(M, computed, _, partial(used_in, N), _) :- M =\= N, !.
loop2_anti_dep_unbroken(N, computed, computed, partial(used_in, N), _) :- ! . % Reading region read into write now

loop2_anti_deps_unbroken([], _, _).
loop2_anti_deps_unbroken([Read-Write|T], Elems1, Elems2) :-
    nth0(Read, Elems1, Read1),
    nth0(Write, Elems1, Write1),
    nth0(Read, Elems2, Read2),
    nth0(Write, Elems2, Write2),
    loop2_anti_dep_unbroken(Write, Read1, Write1, Read2, Write2),
    loop2_anti_deps_unbroken(T, Elems1, Elems2).

% out_deps in 2 are satisfied by either computed -> computed, uncomputed -> uncomputed, or computed -> partial(used_out)
% all of which are dealt with above (TODO, confim that)

fusable(Deps1, _AntiDeps1, Elems1,
        _Deps2, AntiDeps2, Elems2) :-
    no_trashed_data_in_loop1(Elems1, Elems2),
    loop1_deps_unbroken(Deps1, Elems1, Elems2),
    loop2_anti_deps_unbroken(AntiDeps2, Elems1, Elems2).

fusion_valid(Deps1, AntiDeps1, Elems1,
             Deps2, AntiDeps2, Elems2) :-
    loop_valid(Deps1, AntiDeps1, Elems1),
    loop_valid(Deps2, AntiDeps2, Elems2),
    fusable(Deps1, AntiDeps1, Elems1,
            Deps2, AntiDeps2, Elems2).

print_loop3(TL, BL, BR) :-
    format("~t~q~t~25+|~t*~t~25+~n", [TL]),
    format("~`-t~25+|~`-t~25+~n", []),
    format("~t~q~t~25+|~t~q~t~25+~n", [BL, BR]).

print_loop_solutions(Title, Deps, AntiDeps) :-
    format("Loop invariants for ~s~n", [Title]),
    forall(
        (loop_valid(Deps, AntiDeps, [A, B, C])),
        (print_loop3(A, B, C), format(",~n", []))),
    format("~n", []).

print_two_loop3(TL1, BL1, BR1, TL2, BL2, BR2) :-
    format("~t~q~t~25+|~t*~t~25+   ~t~q~t~25+|~t*~t~25+~n", [TL1, TL2]),
    format("~`-t~25+|~`-t~25+ + ~`-t~25+|~`-t~25+~n", []),
    format("~t~q~t~25+|~t~q~t~25+   ~t~q~t~25+|~t~q~t~25+~n", [BL1, BR1, BL2, BR2]).

print_fused_loops_solutions(Title, Deps1, AntiDeps1, Deps2, AntiDeps2) :-
    format("Fusable loop invariants for ~s~n", [Title]),
    forall(
        (fusion_valid(Deps1, AntiDeps1, [A, B, C],
                      Deps2, AntiDeps2, [D, E, F])),
        (print_two_loop3(A, B, C, D, E, F), format(",~n", []))),
    format("~n", []).

main(_) :-
    Loop1Deps = [0-1, 1-2],
    Loop1AntiDeps = [],
    Loop2Deps = [0-1],
    Loop2AntiDeps = [1-2],

    print_loop_solutions("first loop", Loop1Deps, Loop1AntiDeps),
    print_loop_solutions("second loop", Loop2Deps, Loop2AntiDeps),
    print_fused_loops_solutions("these loops", Loop1Deps, Loop1AntiDeps, Loop2Deps, Loop2AntiDeps).
