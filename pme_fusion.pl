#!/usr/bin/env swipl
:- module(pme_fusion,
          [make_region/5, region_with_tasks/2, region_with_tasks/3,
           make_invariant/2, make_invariants/2,
           fused_invariants/1, loop_invariant/1,
           test_pme/1, test_pmes/1, main/0]).

:- use_module(library(assoc)).
:- use_module(library(clpfd)).

:- initialization(main, main).

meta_predicate exists(1, +, -), exists_one(1, +), exists_one(2, +, +),
               maplist2(2, +, +), maplist2_(2, +, +).

exists(_, [], _) :- fail.
exists(P, [H|T], Witness) :-
    call(P, H), Witness = H;
    exists(P, T, Witness).

exists_one(_, []) :- fail.
exists_one(P, [H|T]) :-
    (call(P, H), !);
    exists_one(P, T).

exists_one(_, [], _) :- fail.
exists_one(P, [H|T], L2) :-
    (exists_one(call(P, H), L2), !);
    exists_one(P, T, L2).

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

operand_region(any(Ops), Y) :-
    maplist(operand_region, Ops, OpRegionsWithDups),
    sort(OpRegionsWithDups, OpRegions),
    member(Y, OpRegions).
operand_region(in(X), Y) :- X = Y.
operand_region(during(X, _), Y) :- X = Y.
operand_region(during(X, _, _), Y) :- X = Y.
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

region_with_tasks(Id, Tasks, Reg) :-
    make_region(Id, Tasks, _Past, _Future, Reg).

region_with_tasks(Id-Tasks, Reg) :- region_with_tasks(Id, Tasks, Reg).

make_invariant(IdTasks, Regions) :-
    maplist(region_with_tasks, IdTasks, Regions).

make_invariants(IdTasks, Invariants) :-
    maplist(make_invariant, IdTasks, Invariants).

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

%% BUG: Lists of []s can result in massive duplication of effort
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

before_flip(Y, X) :- before(X, Y).
not_after_flip(Y, X) :- not_after(Y, X).

before(any(Ops1), any(Ops2)) :-
    !, exists_one(before, Ops1, Ops2).
before(any(Ops1), Y) :-
    !, exists_one(before_flip(Y), Ops1).
before(X, any(Ops2)) :-
    !, exists_one(before(X), Ops2).
% Here we give the exceptions to the assumption of independence
before(out(X), in(Y)) :-  !, X \== Y.
before(out(X), during(Y, _)) :- !, X \== Y.
before(out(X), during(Y, _, _)) :- !, X \== Y.
before(out(X), out(Y)) :- !, X \== Y.
before(during(X, _), in(Y)) :- !, X \== Y.
before(during(X, _, _), in(Y)) :- !, X \== Y.
% These are before if they're on different regions or the first is before the second.
before(during(X, M), during(Y, N)) :- !, (X \== Y; M < N), !.
before(during(X, M, _), during(Y, N)) :- !, (X \== Y; M < N), !.
before(during(X, M), during(Y, N, _)) :- !, (X \== Y; M < N), !.
before(during(X, M, A), during(Y, N, B)) :- !, (X \==Y; M < N; (M =:= N, A \== B)), !.
before(_, _).

% The obvious case
not_after(X, X) :- !.
% Handle any()
not_after(any(Ops1), any(Ops2)) :-
    !, exists_one(not_after, Ops1, Ops2).
not_after(any(Ops1), Y) :-
    !, exists_one(not_after_flip(Y), Ops1).
not_after(X, any(Ops2)) :-
    !, exists_one(not_after(X), Ops2).
% The special cases for during()
not_after(during(X, M), during(X, N)) :- M =:= N, !.
not_after(during(X, M, _), during(X, N)) :- M =:= N, !.
not_after(during(X, M), during(X, N, _)) :- M =:= N, !.
not_after(during(X, M, A), during(X, N, B)) :- M =:= N, A == B, !.
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

%% Test and example code

print_region(Region) :-
    (Region.tasks == [], !);
    format("~w past: ~w~n~w future: ~w~n", [Region.id, Region.past, Region.id, Region.future]).

print_invariant(Invariant) :-
    maplist(print_region, Invariant).

print_invariants([]).
print_invariants([Invariant|[]]) :-
    print_invariant(Invariant), !.
print_invariants([Invariant|Invariants]) :-
    print_invariant(Invariant),
    format("then~n"),
    print_invariants(Invariants).

print_invariant_sep(Invariant) :-
    print_invariant(Invariant),
    format("~n").

print_invariants_sep(Invariants) :-
    print_invariants(Invariants),
    format("~n").

test_pme(PME) :-
    findall(Invariant,
            (make_invariant(PME, Invariant),
             loop_invariant(Invariant)),
            Results),
    length(Results, NumResults),
    maplist(print_invariant_sep, Results),
    format("~d invariants~n", [NumResults]).

test_pmes(PMEs) :-
    findall(Invariants,
            (make_invariants(PMEs, Invariants),
             fused_invariants(Invariants)),
            Results),
    length(Results, NumResults),
    maplist(print_invariants_sep, Results),
    format("~d invariants~n", [NumResults]).

test_pmes_dedup(PMEs) :-
    findall(Invariants,
            (make_invariants(PMEs, Invariants),
             fused_invariants(Invariants)),
            Results),
    length(Results, NumResults),
    sort(Results, Invariants),
    length(Invariants, NumInvariants),
    maplist(print_invariants_sep, Invariants),
    format("~d results~n~d invariants", [NumResults, NumInvariants]).

sylvester :-
    test_pme([bl-[op([in(bl)], [out(bl)])],
              tl-[fn([in(tl), out(bl)], [during(tl, 0)]),
                  op([during(tl, 0)], [out(tl)])],
              br-[fn([in(br), out(bl)], [during(br, 0)]),
                  op([during(br, 0)], [out(br)])],
              tr-[fn([any([in(tr), during(tr, 0, b)]), out(br)], [during(tr, 0, a)]),
                  fn([any([in(tr), during(tr, 0, a)]), out(tl)], [during(tr, 0, b)]),
                  op([during(tr, 0, a), during(tr, 0, b)], [out(tr)])]]).


cholesky :-
    test_pme([tl-[op([in(tl)], [out(tl)])],
              bl-[fn([in(bl), out(tl)], [out(bl)])],
              br-[fn([in(br), out(bl)], [during(br, 0)]),
                  op([during(br, 0)], [out(br)])]]).

inverse :-
    %% NOTE: the in(br) and out(tl) in the bl terms can be any([in(...), out(...)])
    %% which will ensure generality
    test_pme([tl-[op([in(tl)], [out(tl)])],
              bl-[fn([any([in(bl), during(bl, 0, b)]), out(tl)], [during(bl, 0, a)]),
                  fn([any([in(bl), during(bl, 0, a)]), in(br)], [during(bl, 0, b)])],
              br-[op([in(br)], [out(br)])]]).

fused_loops() :-
    test_pmes([[tl-[op([in(tl)], [out(tl)])],
                bl-[fn([in(bl), out(tl)], [out(bl)])],
                br-[fn([in(br), out(bl)], [during(br, 0)]),
                    op([during(br, 0)], [out(br)])]],

               [tl-[op([in(tl)], [out(tl)])],
                bl-[fn([any([in(bl), during(bl, 0, b)]), out(tl)], [during(bl, 0, a)]),
                    fn([any([in(bl), during(bl, 0, a)]), in(br)], [during(bl, 0, b)])],
                br-[op([in(br)], [out(br)])]]]).

fused_loops_ex2() :-
   test_pmes(
       [[tl-[op([in(tl)], [out(tl)])],
         bl-[fn([any([in(bl), during(bl, 0, b)]), out(tl)], [during(bl, 0, a)]),
             fn([any([in(bl), during(bl, 0, a)]), in(br)], [during(bl, 0, b)])],
         br-[op([in(br)], [out(br)])]],

        [tl-[op([in(tl)], [during(tl, 0)]),
             fn([in(bl), during(tl, 0)], [out(tl)])],
         bl-[fn([in(br), in(bl)], [out(bl)])],
         br-[op([in(br)], [out(br)])]]]).

inv_true_dep() :-
    test_pmes_dedup(
        [[r_tl-[op([out(l_tl)], [out(r_tl)])],
          r_bl-[fn([any([out(l_bl), during(r_bl, 0, b)]), out(r_tl)], [during(r_bl, 0, a)]),
             fn([any([out(l_bl), during(r_bl, 0, a)]), out(l_br)], [during(r_bl, 0, b)])],
          r_br-[op([out(l_br)], [out(r_br)])],
          y_t-[], y_b-[], x_t-[], x_b-[], l_tl-[], l_bl-[], l_br-[]],

         [y_t-[op([out(r_tl), out(x_t), in(y_t)], [out(y_t)])],
          y_b-[op([out(r_bl), out(x_b), any([in(y_b), during(y_b, 0, b)])], [during(y_b, 0, a)]),
               op([out(r_br), out(x_b), any([in(y_b), during(y_b, 0, a)])], [during(y_b, 0, b)])],
          x_t-[], x_b-[], r_tl-[], r_bl-[], r_br-[], l_tl-[], l_bl-[], l_br-[]]]).

inv_anti_dep :-
    test_pmes_dedup(
        [[y_t-[op([out(l_tl), out(x_t), in(y_t)], [out(y_t)])],
          y_b-[op([out(l_bl), out(x_b), any([in(y_b), during(y_b, 0, b)])], [during(y_b, 0, a)]),
               op([out(l_br), out(x_b), any([in(y_b), during(y_b, 0, a)])], [during(y_b, 0, b)])],
          x_t-[], x_b-[], l_tl-[], l_bl-[], l_br-[]],

         [l_tl-[op([in(l_tl)], [out(l_tl)])],
          l_bl-[fn([any([in(l_bl), during(l_bl, 0, b)]), out(l_tl)], [during(l_bl, 0, a)]),
                fn([any([in(l_bl), during(l_bl, 0, a)]), in(l_br)], [during(l_bl, 0, b)])],
          l_br-[op([in(l_br)], [out(l_br)])],
          y_t-[], y_b-[], x_t-[], x_b-[]]]).

three_fused_loops() :-
    test_pmes(
        [[tl-[op([in(tl)], [out(tl)])],
          bl-[fn([in(bl), out(tl)], [out(bl)])],
          br-[fn([in(br), out(bl)], [during(br, 0)]),
              op([during(br, 0)], [out(br)])]],

         [tl-[op([in(tl)], [out(tl)])],
          bl-[fn([any([in(bl), during(bl, 0, b)]), out(tl)], [during(bl, 0, a)]),
              fn([any([in(bl), during(bl, 0, a)]), in(br)], [during(bl, 0, b)])],
          br-[op([in(br)], [out(br)])]],

         [tl-[op([in(tl)], [during(tl, 0)]),
              fn([in(bl), during(tl, 0)], [out(tl)])],
          bl-[fn([in(br), in(bl)], [out(bl)])],
          br-[op([in(br)], [out(br)])]]]).

main :- three_fused_loops.
