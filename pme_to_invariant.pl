#!/usr/bin/env swipl

:- initialization(main, main).

meta_predicate exists(1, +, -), exists_one(1, +),
               maplist2(2, +, +), maplist2_(2, +, +).

exists(_, [], _) :- fail.
exists(P, [H|T], Witness) :-
    call(P, H), Witness = H;
    exists(P, T, Witness).

exists_one(_, []) :- fail.
exists_one(P, [H|T]) :-
    (call(P, H), !);
    exists_one(P, T).

split_([], A, B, VarA, VarB) :- reverse(A, VarA), reverse(B, VarB).
split_([H|T], A, B, VarA, VarB) :-
    split_(T, [H|A], B, VarA, VarB);
    split_(T, A, [H|B], VarA, VarB).

split(List, A, B) :- split_(List, [], [], A, B).

productive_task(fn(_, _)).
productive_task(op(_, _)).

task(noop(_, _)).
task(X) :- productive_task(X).

task_split(noop(X, Y), In, Out) :- X = In, Y = Out.
task_split(fn(X, Y), In, Out) :- X = In, Y = Out.
task_split(op(X, Y), In, Out) :- X = In, Y = Out.

task_outputs(noop(_, X), Y) :- X = Y.
task_outputs(fn(_, X), Y) :- X = Y.
task_outputs(op(_, X), Y) :- X = Y.

make_region(Id, Tasks, Past, Future, Reg) :-
    maplist(task, Tasks),
    Reg = region{id:Id, tasks:Tasks, past:Past, future:Future}.

is_region(region{id:_, tasks:Tasks, past:Past, future:Future}) :-
    split(Tasks, Past, Future).

has_op(List) :-
    exists_one(=(op(_, _)), List).

has_fn(List) :-
    exists_one(=(fn(_, _)), List).

has_op_in_past(Region) :- has_op(Region.past).
has_op_in_future(Region) :- has_op(Region.future).

regions_make_progress(Regions) :-
    exists(has_op_in_past, Regions, PastReg),
    exists(has_op_in_future, Regions, FutureReg),
    PastReg.id \== FutureReg.id, !.

% Here we give the exceptions to the assumption of independence
before(out(X), in(Y)) :-  !, X \== Y.
before(out(X), during(Y, _)) :- !, X \== Y.
before(out(X), out(Y)) :- !, X \== Y.
before(during(X, _), in(Y)) :- !, X \== Y.
% These are before if they're on different regions or the first is before the second.
before(during(X, M), during(Y, N)) :- !, (X \== Y; M =< N), !.
before(_, _).

not_after(X, X) :- !.
not_after(during(X, M), during(X, N)) :- M is N, !.
not_after(X, Y) :- before(X, Y).

maplist2(Pred, L1, L2) :-
    maplist2_(L1, L2, Pred).

maplist2_([], _, _).
maplist2_([H|T], L2, Pred) :-
    maplist(call(Pred, H), L2),
    maplist2_(T, L2, Pred).

collect_field_([], _, Accum, Ret) :- Ret = Accum, !.
collect_field_([Region|T], Field, Accum, Ret) :-
    append(Region.get(Field), Accum, NewAccum),
    collect_field_(T, Field, NewAccum, Ret).

collect_field(Regions, Field, Ret) :-
    collect_field_(Regions, Field, [], Ret).

partition_task_ops([], AccumIn, AccumOut, Inputs, Outputs) :-
    Inputs = AccumIn, Outputs = AccumOut, !.
partition_task_ops([Task|Tasks], AccumIn, AccumOut, Inputs, Outputs) :-
    task_split(Task, TaskIn, TaskOut),
    append(TaskIn, AccumIn, NewAccumIn),
    append(TaskOut, AccumOut, NewAccumOut),
    partition_task_ops(Tasks, NewAccumIn, NewAccumOut, Inputs, Outputs).

partition_task_ops(Tasks, Inputs, Outputs) :-
    partition_task_ops(Tasks, [], [], Inputs, Outputs).

dependencies_preserved(Regions) :-
    collect_field(Regions, past, Pasts),
    collect_field(Regions, future, Futures),
    partition_task_ops(Pasts, PastIns, PastOuts),
    partition_task_ops(Futures, FutureIns, FutureOuts),
    maplist2(not_after, PastOuts, FutureIns),
    maplist2(before, PastIns, FutureOuts).

loop_invariant(Regions) :-
    maplist(is_region, Regions),
    regions_make_progress(Regions),
    dependencies_preserved(Regions).

% Searching for Sylvester invariants yields duplicates
% where there are algorithms that are identical
% up to the order the subtractions in the top right are performed.
% Find things that could not be such duplicates,
% so we can toss everything but them on search pt. 2
sylvester_tr_non_duplicate(_, _, true) :- !.
sylvester_tr_non_duplicate(Past, Future, false) :-
    has_fn(Past),
    has_fn(Future).

print_four(Args) :-
    format("Top left past: ~w~nTop left future: ~w~nTop right past: ~w~nTop right future: ~w~nBottom left past: ~w~nBottom left future: ~w~nBottom right past: ~w~nBottom right future: ~w~n~n", Args).

sylvester :-
    findall([PTl, FTl, PTr, FTr, PBl, FBl, PBr, FBr],
            ((
                    (BrInOp = in(tr), BrOutN = 0,
                     TlInOp = during(tr, 0), TlOutN = 1,
                     Initial = true);
                    (BrInOp = during(tr, 0), BrOutN = 1,
                     TlInOp = in(tr), TlOutN = 0,
                     Initial = false)
                ),
             make_region(bl, [op([in(bl)], [out(bl)])],
                         PBl, FBl, Bl),
             make_region(tl, [fn([in(tl), out(bl)], [during(tl, 0)]),
                              op([during(tl, 0)], [out(tl)])],
                         PTl, FTl, Tl),
             make_region(br, [fn([in(br), out(bl)], [during(br, 0)]),
                              op([during(br, 0)], [out(br)])],
                         PBr, FBr, Br),
             make_region(tr, [fn([BrInOp, out(br)], [during(tr, BrOutN)]),
                              fn([TlInOp, out(tl)], [during(tr, TlOutN)]),
                              op([during(tr, 1)], [out(tr)])],
                         PTr, FTr, Tr),
             loop_invariant([Bl, Tl, Br, Tr]),
             sylvester_tr_non_duplicate(PTr, FTr, Initial)),
            Results),
    length(Results, NumResults),
    maplist(print_four, Results),
    format("~d invariants~n", [NumResults]).

print_three(Args) :-
    format("Top left past: ~w~nTop left future: ~w~nBottom left past: ~w~nBottom left future: ~w~nBottom right past: ~w~nBottom right future: ~w~n~n", Args).

cholesky :-
    findall([PTl, FTl, PBl, FBl, PBr, FBr],
            (make_region(tl, [op([in(tl)], [out(tl)])],
                         PTl, FTl, Tl),
             make_region(bl, [fn([in(bl), out(tl)], [out(bl)])],
                         PBl, FBl, Bl),
             make_region(br, [fn([in(br), out(bl)], [during(br, 0)]),
                              op([during(br, 0)], [out(br)])],
                         PBr, FBr, Br),
             loop_invariant([Tl, Bl, Br])),
            Results),
    maplist(print_three, Results),
    length(Results, NumResults),
    format("~d invariants~n", [NumResults]).

inverse :-
    findall([PTl, FTl, PBl, FBl, PBr, FBr],
            (make_region(tl, [op([in(tl)], [out(tl)])],
                         PTl, FTl, Tl),
             make_region(bl, [fn([during(bl, 0), out(tl)], [during(bl, 0)]),
                              fn([during(bl, 0), in(br)], [during(bl, 0)])],
                         PBl, FBl, Bl),
             make_region(br, [op([in(br)], [out(br)])],
                         PBr, FBr, Br),
             loop_invariant([Tl, Bl, Br])),
            Results),
    maplist(print_three, Results),
    length(Results, NumResults),
    format("~d invariants~n", [NumResults]).

main(_) :- sylvester.
