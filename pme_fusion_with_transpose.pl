#!/usr/bin/env swipl

:- use_module(library(assoc)).
:- use_module(library(clpfd)).

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

maplist2(Pred, L1, L2) :-
    maplist2_(L1, L2, Pred).

maplist2_([], _, _).
maplist2_([H|T], L2, Pred) :-
    maplist(call(Pred, H), L2),
    maplist2_(T, L2, Pred).

operand_region(in(X), Y) :- X = Y.
operand_region(during(X, _), Y) :- X = Y.
operand_region(out(X), Y) :- X = Y.

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

has_op(List) :-
    exists_one(=(op(_, _)), List).

has_fn(List) :-
    exists_one(=(fn(_, _)), List).

make_region(Id, Tasks, Past, Future, Reg) :-
    maplist(task, Tasks),
    Reg = region{id:Id, tasks:Tasks, past:Past, future:Future}.

is_region(region{id:_, tasks:Tasks, past:Past, future:Future}) :-
    split(Tasks, Past, Future).

is_computed(Region) :-
    (Region.past = Region.tasks),
    (Region.future = []),
    !.

is_uncomputed(Region) :-
    (Region.past = []),
    (Region.future = Region.tasks),
    !.

get_assoc_default(Key, Assoc, Value, Default) :-
    (get_assoc(Key, Assoc, Value), !);
    (Value = Default, !).

transpose_invariants_([], Accum, Out) :- Out = Accum.
transpose_invariants_([Region|Future], Accum, Out) :-
    Id = Region.id,
    get_assoc_default(Id, Accum, Past, []),
    put_assoc(Id, Accum, [Region|Past], NewAccum),
    transpose_invariants_(Future, NewAccum, Out).

transpose_invariants([], Regions, Out) :-
    map_assoc(reverse, Regions, Out), !.
transpose_invariants([Invariant|Future], Regions, Out) :-
    transpose_invariants_(Invariant, Regions, NewRegions), !,
    transpose_invariants(Future, NewRegions, Out).

transpose_invariants(Invariants, Regions) :-
    empty_assoc(Accumulator),
    transpose_invariants(Invariants, Accumulator, Regions).

to_region_length_var(Region, Out) :-
    length(Region, Max),
    Out in -1..Max, !.

to_region_length_vars(Regions, Out) :-
    map_assoc(to_region_length_var, Regions, Out), !.

last_computed_delta(AnyRegion, Delta) :-
    is_computed(AnyRegion) -> (Delta = 0); (Delta = -1).
first_uncomputed_delta(AnyRegion, Delta) :-
    is_uncomputed(AnyRegion) -> (Delta = -1); (Delta = 0).

computable_order(Region, LastComputeds, FirstUncomputeds) :-
    append(Computed, [Any|Uncomputed], Region),
    maplist(is_computed, Computed),
    maplist(is_uncomputed, Uncomputed),
    is_region(Any),
    % We already did this case with that Computed being the Any
    \+ (is_uncomputed(Any), Computed \== []),

    (Id = Any.id),
    get_assoc(Id, LastComputeds, LastComputedConstraint),
    length(Computed, LenComputed),
    last_computed_delta(Any, LastComputedDelta),
    LastComputed is LenComputed + LastComputedDelta,
    LastComputedConstraint #= LastComputed,

    get_assoc(Id, FirstUncomputeds, FirstUncomputedConstraint),
    length(Uncomputed, LenUncomputed),
    length(Region, LenRegion),
    first_uncomputed_delta(Any, FirstUncomputedDelta),
    FirstUncomputed is LenRegion - LenUncomputed + FirstUncomputedDelta,
    FirstUncomputedConstraint #= FirstUncomputed.

partition_task_operands([], AccumIn, AccumOut, Inputs, Outputs) :-
    Inputs = AccumIn, Outputs = AccumOut, !.
partition_task_operands([Task|Tasks], AccumIn, AccumOut, Inputs, Outputs) :-
    task_split(Task, TaskIn, TaskOut),
    append(TaskIn, AccumIn, NewAccumIn),
    append(TaskOut, AccumOut, NewAccumOut),
    partition_task_operands(Tasks, NewAccumIn, NewAccumOut, Inputs, Outputs).

partition_task_operands(Tasks, Inputs, Outputs) :-
    partition_task_operands(Tasks, [], [], Inputs, Outputs).

collect_field_([], _, Accum, Ret) :- Ret = Accum, !.
collect_field_([Region|T], Field, Accum, Ret) :-
    append(Region.get(Field), Accum, NewAccum),
    collect_field_(T, Field, NewAccum, Ret).

collect_field(Regions, Field, Ret) :-
    collect_field_(Regions, Field, [], Ret).

regions_to_operands(Regions, PastIns, PastOuts, FutureIns, FutureOuts) :-
    collect_field(Regions, past, Pasts),
    collect_field(Regions, future, Futures),
    partition_task_operands(Pasts, PastIns, PastOuts),
    partition_task_operands(Futures, FutureIns, FutureOuts).


constrain_from_past_input(LoopNo, LastComputeds, Op) :-
    operand_region(Op, Region),
    get_assoc(Region, LastComputeds, Constraint),
    Constraint #>= LoopNo - 1.

constrain_from_future_input(LoopNo, FirstUncomputeds, Op) :-
    operand_region(Op, Region),
    get_assoc(Region, FirstUncomputeds, Constraint),
    Constraint #=< LoopNo + 1.

fusion_dependency_check(_, [], _, _).
fusion_dependency_check(N, [Region|Future], LastComputeds, FirstUncomputeds) :-
    partition_task_operands(Region.past, PastIns, _),
    partition_task_operands(Region.future, FutureIns, _),
    maplist(constrain_from_past_input(N, LastComputeds), PastIns),
    maplist(constrain_from_future_input(N, FirstUncomputeds), FutureIns),
    NewN is N + 1,
    fusion_dependency_check(NewN, Future, LastComputeds, FirstUncomputeds).
fusion_dependency_check(Region, LastComputeds, FirstUncomputeds) :-
    fusion_dependency_check(0, Region, LastComputeds, FirstUncomputeds).

fusable_region(LastComputeds, FirstUncomputeds, Region) :-
    computable_order(Region, LastComputeds, FirstUncomputeds),
    fusion_dependency_check(Region, LastComputeds, FirstUncomputeds).

fusable(Regions) :-
    to_region_length_vars(Regions, LastComputeds),
    to_region_length_vars(Regions, FirstUncomputeds),
    map_assoc(fusable_region(LastComputeds, FirstUncomputeds), Regions).


region_with_id(_, [], _) :- fail.
region_with_id(Id, [R|Tail], Region) :-
    (R.id == Id, !, R = Region);
    region_with_id(Id, Tail, Region).

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

dependencies_preserved(Regions) :-
    regions_to_operands(Regions, PastIns, PastOuts, FutureIns, FutureOuts),
    maplist2(not_after, PastOuts, FutureIns),
    maplist2(before, PastIns, FutureOuts).

valid_loop_invariant(Regions) :-
    regions_make_progress(Regions),
    dependencies_preserved(Regions).

fused_invariants(Invariants) :-
    transpose_invariants(Invariants, Regions),
    fusable(Regions),
    maplist(valid_loop_invariant, Invariants).

loop_invariant(Invariant) :-
    fused_invariants([Invariant]).

% Searching for Sylvester invariants yields duplicates
% where there are algorithms that are identical
% up to the order the subtractions in the top right are performed.
% Find things that could not be such duplicates,
% so we can toss everything but them on search pt. 2
region_non_duplicate(_, _, true) :- !.
region_non_duplicate(Past, Future, false) :-
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
             region_non_duplicate(PTr, FTr, Initial)),
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

print_three_twice(Result) :-
    length(ResultA, 6),
    length(ResultB, 6),
    append(ResultA, ResultB, Result),
    print_three(ResultA),
    format("then~n"),
    print_three(ResultB).

print_three_thrice(Result) :-
    length(ResultA, 6),
    length(ResultBC, 12),
    append(ResultA, ResultBC, Result),
    length(ResultB, 6),
    length(ResultC, 6),
    append(ResultB, ResultC, ResultBC),
    print_three(ResultA),
    format("then~n"),
    print_three(ResultB),
    format("then~n"),
    print_three(ResultC).

fused_loops() :-
    findall([PTlChol, FTlChol, PBlChol, FBlChol, PBrChol, FBrChol,
             PTlInv, FTlInv, PBlInv, FBlInv, PBrInv, FBrInv],
            (make_region(tl, [op([in(tl)], [out(tl)])],
                         PTlChol, FTlChol, TlChol),
             make_region(bl, [fn([in(bl), out(tl)], [out(bl)])],
                         PBlChol, FBlChol, BlChol),
             make_region(br, [fn([in(br), out(bl)], [during(br, 0)]),
                              op([during(br, 0)], [out(br)])],
                         PBrChol, FBrChol, BrChol),
             make_region(tl, [op([in(tl)], [out(tl)])],
                         PTlInv, FTlInv, TlInv),
             make_region(bl, [fn([during(bl, 0), out(tl)], [during(bl, 0)]),
                              fn([during(bl, 0), in(br)], [during(bl, 0)])],
                         PBlInv, FBlInv, BlInv),
             make_region(br, [op([in(br)], [out(br)])],
                         PBrInv, FBrInv, BrInv),
             fused_invariants([[TlChol, BlChol, BrChol], [TlInv, BlInv, BrInv]])),
            Results),
    maplist(print_three_twice, Results),
    length(Results, NumResults),
    format("~d invariants~n", [NumResults]).

fused_loops_ex2() :-
    findall([PTlInv, FTlInv, PBlInv, FBlInv, PBrInv, FBrInv,
             PTlTrmm, FTlTrmm, PBlTrmm, FBlTrmm, PBrTrmm, FBrTrmm],
            (make_region(tl, [op([in(tl)], [out(tl)])],
                         PTlInv, FTlInv, TlInv),
             make_region(bl, [fn([during(bl, 0), out(tl)], [during(bl, 0)]),
                              fn([during(bl, 0), in(br)], [during(bl, 0)])],
                         PBlInv, FBlInv, BlInv),
             make_region(br, [op([in(br)], [out(br)])],
                         PBrInv, FBrInv, BrInv),
             make_region(tl, [op([in(tl)], [during(tl, 0)]),
                              fn([in(bl), during(tl, 0)], [out(tl)])],
                         PTlTrmm, FTlTrmm, TlTrmm),
             make_region(bl, [fn([in(br), in(bl)], [out(bl)])],
                         PBlTrmm, FBlTrmm, BlTrmm),
             make_region(br, [op([in(br)], [out(br)])],
                         PBrTrmm, FBrTrmm, BrTrmm),
             fused_invariants([[TlInv, BlInv, BrInv], [TlTrmm, BlTrmm, BrTrmm]])),
            Results),
    maplist(print_three_twice, Results),
    length(Results, NumResults),
    format("~d invariants~n", [NumResults]).

three_fused_loops() :-
    findall([PTlChol, FTlChol, PBlChol, FBlChol, PBrChol, FBrChol,
             PTlInv, FTlInv, PBlInv, FBlInv, PBrInv, FBrInv,
             PTlTrmm, FTlTrmm, PBlTrmm, FBlTrmm, PBrTrmm, FBrTrmm],
            (make_region(tl, [op([in(tl)], [out(tl)])],
                         PTlChol, FTlChol, TlChol),
             make_region(bl, [fn([in(bl), out(tl)], [out(bl)])],
                         PBlChol, FBlChol, BlChol),
             make_region(br, [fn([in(br), out(bl)], [during(br, 0)]),
                              op([during(br, 0)], [out(br)])],
                         PBrChol, FBrChol, BrChol),
             make_region(tl, [op([in(tl)], [out(tl)])],
                         PTlInv, FTlInv, TlInv),
             make_region(bl, [fn([during(bl, 0), out(tl)], [during(bl, 0)]),
                              fn([during(bl, 0), in(br)], [during(bl, 0)])],
                         PBlInv, FBlInv, BlInv),
             make_region(br, [op([in(br)], [out(br)])],
                         PBrInv, FBrInv, BrInv),
             make_region(tl, [op([in(tl)], [during(tl, 0)]),
                              fn([in(bl), during(tl, 0)], [out(tl)])],
                         PTlTrmm, FTlTrmm, TlTrmm),
             make_region(bl, [fn([in(br), in(bl)], [out(bl)])],
                         PBlTrmm, FBlTrmm, BlTrmm),
             make_region(br, [op([in(br)], [out(br)])],
                         PBrTrmm, FBrTrmm, BrTrmm),
             fused_invariants([[TlChol, BlChol, BrChol],
                               [TlInv, BlInv, BrInv],
                               [TlTrmm, BlTrmm, BrTrmm]])),
            Results),
    maplist(print_three_thrice, Results),
    length(Results, NumResults),
    format("~d invariants~n", [NumResults]).

main :- three_fused_loops.
