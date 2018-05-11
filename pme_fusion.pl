#!/usr/bin/env swipl
:- module(pme_fusion,
          [make_region/5, region_with_tasks/2, region_with_tasks/3,
           make_pme/2, make_pmes/2,
           fused_invariants/1, loop_invariant/1,
           print_invariant/1, print_invariants/1, print_invariants_sep/1,
           gen_invariant/1, gen_invariants/1, gen_invariants_dedup/1,
           test_task_list/2, test_task_lists/2, test_task_lists_dedup/2]).

:- use_module(library(assoc)).
:- use_module(library(clpfd)).

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

base_operand(hat(X)) :- atom(X).
base_operand(during(X, N)) :- atom(X), integer(N).
base_operand(during(X, N, V)) :- atom(X), integer(N), atom(V).
base_operand(tilde(X)) :- atom(X).

operand(any(Ops)) :- maplist(base_operand, Ops), !.
operand(X) :- base_operand(X).

operand_region(any(Ops), Y) :-
    maplist(operand_region, Ops, OpRegionsWithDups),
    sort(OpRegionsWithDups, OpRegions),
    member(Y, OpRegions).
operand_region(hat(X), Y) :- X = Y.
operand_region(during(X, _), Y) :- X = Y.
operand_region(during(X, _, _), Y) :- X = Y.
operand_region(tilde(X), Y) :- X = Y.

productive_task(eq(O, _)) :- base_operand(O).
productive_task(op_eq(O, _)) :- base_operand(O).

task(comes_from(O, I)) :- base_operand(O), base_operand(I), !.
task(X) :- productive_task(X).

extract_operands([], Accum, Out) :- Out = Accum, !.

extract_operands([Term|Terms], Accum, Out) :-
    extract_term_operands(Term, TermOps),
    append(TermOps, Accum, NewAccum),
    extract_operands(Terms, NewAccum, Out), !.

extract_operands(Term, Accum, Out) :-
    extract_term_operands(Term, TermOps),
    append(TermOps, Accum, Out).

extract_term_operands(Term, Out) :-
    operand(Term) -> Out = [Term];
    compound(Term) -> (compound_name_arguments(Term, _, Args),
                       extract_operands(Args, [], Out));
    Out = [].

extract_operands(Term, Out) :- extract_operands(Term, [], Out).

task_split(comes_from(O, I), In, Out) :- In = [I], Out = O.
task_split(eq(O, I), In, Out) :- extract_operands(I, InOps), In = InOps, Out = O.
task_split(op_eq(O, I), In, Out) :- extract_operands(I, InOps), In = InOps, Out = O.

task_output(op_eq(O, _), O) :- !.
task_output(eq(O, _), O) :- !.
task_output(comes_from(O, _), O) :- !.
task_output(Task) :-
    format("ERROR: ~w is not a task in task list~n", [Task]),
    fail.

task_input(op_eq(_, I), I) :- !.
task_input(eq(_, I), I) :- !.
task_input(comes_from(_, I), I) :- !.
task_input(Task) :-
    format("ERROR: ~w is not a task in task list~n", [Task]),
    fail.

task_output_region(Task, Out) :-
    task_output(Task, O),
    (comes_from(_, I) = Task ->
         ((base_operand(I), !);
          format("ERROR: Invalid input ~w to comes_from task ~w~n", [I, Task]));
     true),
    (base_operand(O) -> operand_region(O, Out);
     (format("ERROR, Invalid output ~w in task ~w~n", [O, Task]), fail)).

collect_extra_input_regions(_OutRegions, [], Acc, ExtraInRegions) :- !,
    ExtraInRegions = Acc.
collect_extra_input_regions(OutRegions, [Term|Terms], Acc, ExtraInRegions) :- !,
    collect_extra_input_regions(OutRegions, Term, [], InRegs),
    ord_union(Acc, InRegs, NewAcc),
    collect_extra_input_regions(OutRegions, Terms, NewAcc, ExtraInRegions).

collect_extra_input_regions(OutRegions, Term, Acc, ExtraInRegions) :-
    base_operand(Term) -> (operand_region(Term, Reg),
                         (ord_memberchk(Reg, OutRegions), ExtraInRegions = Acc, !;
                          format("WARNING: Region ~w (from ~w) doesn't appear as an output anywhere~n", [Reg, Term]),
                          ord_add_element(Acc, Reg, ExtraInRegions)));
    any(Ops) = Term -> (collect_extra_input_regions(OutRegions, Ops, [], SubAcc),
                        ord_union(Acc, SubAcc, ExtraInRegions));
    compound(Term) -> (compound_name_arguments(Term, _, Args),
                       collect_extra_input_regions(OutRegions, Args, [], SubAcc),
                       ord_union(Acc, SubAcc, ExtraInRegions));
    ord_memberchk(Term, OutRegions) -> (format("WARNING: ~w appears an input without an associated state~n", [Term]),
                                        ExtraInRegions = Acc);
    ExtraInRegions = Acc.

collect_extra_input_regions(OutRegions, Term, ExtraInRegions) :-
    collect_extra_input_regions(OutRegions, Term, [], ExtraInRegions).

has_op(List) :-
    exists_one(=(op_eq(_, _)), List).

make_region(Id, Tasks, Past, Future, Reg) :-
    ((maplist(task, Tasks), !);
     format("ERROR: Invalid output for assignment in region ~w (tasks ~w)~n", [Id, Tasks])),
    Reg = region{id:Id, tasks:Tasks, past:Past, future:Future}.

region_with_tasks(Id, Tasks, Reg) :-
    make_region(Id, Tasks, _Past, _Future, Reg).

region_with_tasks(Id-Tasks, Reg) :- region_with_tasks(Id, Tasks, Reg).

tasks_grouped_by_region(TaskList, IdTasks) :-
    map_list_to_pairs(task_output_region, TaskList, Pairs),
    keysort(Pairs, Sorted),
    group_pairs_by_key(Sorted, IdTasks).

add_empty_regions_([], IdTasks, NewIdTasks) :- IdTasks = NewIdTasks.
add_empty_regions_([Id|Ids], IdTasks, NewIdTasks) :-
    (exists_one(=(Id-_), IdTasks), !,
     add_empty_regions_(Ids, IdTasks, NewIdTasks));
    add_empty_regions_(Ids, [Id-[]|IdTasks], NewIdTasks).

add_empty_regions(Ids, IdTasks, NewIdTasks) :-
    maplist(add_empty_regions_(Ids), IdTasks, NewIdTasks).

make_pme(TaskList, Regions) :-
    make_pmes([TaskList], [Regions]).

make_pmes(TaskLists, PMEs) :-
    maplist(tasks_grouped_by_region, TaskLists, IdTasks),
    maplist(pairs_keys, IdTasks, RegionsByLoop), % Sorted by the gather
    ord_union(RegionsByLoop, AllOutRegions),
    maplist(maplist(task_input), TaskLists, TaskInputs),
    collect_extra_input_regions(AllOutRegions, TaskInputs, ExtraInRegions),
    ord_union(AllOutRegions, ExtraInRegions, AllRegions),
    add_empty_regions(AllRegions, IdTasks, FullIdTasks),
    maplist(maplist(region_with_tasks), FullIdTasks, PMEs).

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

is_partial(Region) :-
    (Region.past \= []),
    (Region.future \= []),
    !.

is_empty(Region) :-
    (Region.tasks = []), !.


get_assoc_default(Key, Assoc, Value, Default) :-
    (get_assoc(Key, Assoc, Value), !);
    (Value = Default, !).

transpose_invariants_([], Accum, Out) :- Out = Accum.
transpose_invariants_([Region|Others], Accum, Out) :-
    Id = Region.id,
    get_assoc_default(Id, Accum, Past, []),
    put_assoc(Id, Accum, [Region|Past], NewAccum),
    transpose_invariants_(Others, NewAccum, Out).

transpose_invariants([], StripAccum, Out) :-
    map_assoc(reverse, StripAccum, Out), !.
transpose_invariants([Invariant|Future], StripAccum, Out) :-
    transpose_invariants_(Invariant, StripAccum, NewAccum), !,
    transpose_invariants(Future, NewAccum, Out).

transpose_invariants(Invariants, Strips) :-
    empty_assoc(Accumulator),
    transpose_invariants(Invariants, Accumulator, Strips).

to_strip_length_var(Strip, Out) :-
    length(Strip, Max),
    Out in -1..Max, !.

to_strip_length_vars(Strips, Out) :-
    map_assoc(to_strip_length_var, Strips, Out), !.

last_computed_delta(AnyRegion, Delta) :-
    is_computed(AnyRegion) -> (Delta = 1); (Delta = 0).
first_uncomputed_delta(AnyRegion, Delta) :-
    is_uncomputed(AnyRegion) -> (Delta = -1); (Delta = 0).

extract_empty_prefix([], AccumEmptys, Emptys, Uncomputed) :-
    reverse(AccumEmptys, Emptys),
    Uncomputed = [].
extract_empty_prefix([Reg|Regs], AccumEmptys, Emptys, Uncomputed)  :-
    is_empty(Reg) ->
        extract_empty_prefix(Regs, [Reg|AccumEmptys], Emptys, Uncomputed);
    (reverse(AccumEmptys, Emptys), Uncomputed = [Reg|Regs]).

extract_empty_prefix(MaybeUncomp, Emptys, Uncomputed) :-
    extract_empty_prefix(MaybeUncomp, [], Emptys, Uncomputed).


computable_order(Strip, LastComputeds, FirstUncomputeds) :-
    append(Computed, [Any|EmptyAndUncomputed], Strip),
    extract_empty_prefix(EmptyAndUncomputed, Empty, Uncomputed),
    maplist(is_computed, Computed),
    maplist(is_uncomputed, Uncomputed),
    %% For independent iterations, replace next statement with
    %% (is_computed(Any); is_uncomputed(Any))
    is_region(Any),
    % We'll have tried this for the case where a previous Any was computed
    % This also gets rid of redundant checks for empty regions
    \+ (is_uncomputed(Any), Computed \== []),

    maplist(is_region, Empty),
    length(Empty, LenEmpty),
    NLikeAny is LenEmpty + 1,

    (Id = Any.id),
    get_assoc(Id, LastComputeds, LastComputedConstraint),
    length(Computed, LenComputed),
    last_computed_delta(Any, LastComputedDelta),
    LastComputed is (LenComputed - 1) + LastComputedDelta,
    LastComputedWithEmpty is (LenComputed - 1) + (LastComputedDelta * NLikeAny),
    LastComputedConstraint in (LastComputed..LastComputedWithEmpty),

    get_assoc(Id, FirstUncomputeds, FirstUncomputedConstraint),
    length(Uncomputed, LenUncomputed),
    length(Strip, LenStrip),
    first_uncomputed_delta(Any, FirstUncomputedDelta),
    FirstUncomputed is LenStrip - (LenUncomputed + LenEmpty) + FirstUncomputedDelta,
    FirstUncomputedWithEmpty is LenStrip - LenUncomputed + FirstUncomputedDelta,
    FirstUncomputedConstraint in (FirstUncomputed..FirstUncomputedWithEmpty).

partition_task_operands([], AccumIn, AccumOut, Inputs, Outputs) :-
    Inputs = AccumIn, Outputs = AccumOut, !.
partition_task_operands([Task|Tasks], AccumIn, AccumOut, Inputs, Outputs) :-
    task_split(Task, TaskIn, TaskOut),
    append(TaskIn, AccumIn, NewAccumIn),
    NewAccumOut = [TaskOut|AccumOut],
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
    maplist(constrain_from_future_input(N, FirstUncomputeds), FutureIns), !,
    NewN is N + 1,
    fusion_dependency_check(NewN, Future, LastComputeds, FirstUncomputeds).
fusion_dependency_check(Region, LastComputeds, FirstUncomputeds) :-
    fusion_dependency_check(0, Region, LastComputeds, FirstUncomputeds).

fusable_strip(LastComputeds, FirstUncomputeds, Strip) :-
    computable_order(Strip, LastComputeds, FirstUncomputeds),
    fusion_dependency_check(Strip, LastComputeds, FirstUncomputeds).

fusable(Strips) :-
    to_strip_length_vars(Strips, LastComputeds),
    to_strip_length_vars(Strips, FirstUncomputeds),
    map_assoc(fusable_strip(LastComputeds, FirstUncomputeds), Strips).

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

no_floating_noops(Regions, Region) :-
    (Region.tasks = [comes_from(_Out, In)]) ->
        (operand_region(In, InId),
         ((InId == Region.id, !);
          (region_with_id(InId, Regions, InReg),
           ((InReg.future == []) -> (Region.future == []);
            (Region.past == [])))));
    true.

no_floating_noops(Regions) :-
    maplist(no_floating_noops(Regions), Regions).

might_have_rank_k_update(Regions) :-
    exists_one(is_partial, Regions).

before_flip(Y, X) :- before(X, Y).
not_after_flip(Y, X) :- not_after(Y, X).

before(any(Ops1), any(Ops2)) :-
    !, exists_one(before, Ops1, Ops2).
before(any(Ops1), Y) :-
    !, exists_one(before_flip(Y), Ops1).
before(X, any(Ops2)) :-
    !, exists_one(before(X), Ops2).
% Here we give the exceptions to the assumption of independence
before(tilde(X), hat(Y)) :-  !, X \== Y.
before(tilde(X), during(Y, _)) :- !, X \== Y.
before(tilde(X), during(Y, _, _)) :- !, X \== Y.
before(tilde(X), tilde(Y)) :- !, X \== Y.
before(during(X, _), hat(Y)) :- !, X \== Y.
before(during(X, _, _), hat(Y)) :- !, X \== Y.
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

dependencies_preserved(Invariant) :-
    regions_to_operands(Invariant, PastIns, PastOuts, FutureIns, FutureOuts),
    %% For independent iterations, replace next statement with
    %% maplist2(before, PastOuts, FutureIns),
    maplist2(not_after, PastOuts, FutureIns),
    maplist2(before, PastIns, FutureOuts).

valid_loop_invariant(Invariant) :-
    %% Uncomment below to restrict to possible rank-k updates
    %% might_have_rank_k_update(Invariant),
    regions_make_progress(Invariant),
    no_floating_noops(Invariant),
    dependencies_preserved(Invariant).

fused_invariants(Invariants) :-
    transpose_invariants(Invariants, Strips),
    fusable(Strips),
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

test_task_list(TaskList, NInvariants) :-
    findall(Invariant,
            (make_pme(TaskList, Invariant),
             loop_invariant(Invariant)),
            Results),
    length(Results, NumResults),
    maplist(print_invariant_sep, Results),
    format("~d invariants~n", [NumResults]),
    ((NumResults #= NInvariants, !);
     (format("ERROR: expected ~d invariants~n", [NInvariants]), fail)).

test_task_lists(TaskLists, NInvariants) :-
    findall(Invariants,
            (make_pmes(TaskLists, Invariants),
             fused_invariants(Invariants)),
            Results),
    length(Results, NumResults),
    maplist(print_invariants_sep, Results),
    format("~d invariants~n", [NumResults]),
    ((NumResults #= NInvariants, !);
     (format("ERROR: expected ~d invariants~n", [NInvariants]), fail)).

test_task_lists_dedup(TaskLists, NInvariants) :-
    findall(Invariants,
            (make_pmes(TaskLists, Invariants),
             fused_invariants(Invariants)),
            Results),
    length(Results, NumResults),
    sort(Results, Invariants),
    length(Invariants, NumInvariants),
    maplist(print_invariants_sep, Invariants),
    format("~d results~n~d invariants~n", [NumResults, NumInvariants]),
    ((NumInvariants #= NInvariants, !);
     (format("ERROR: expected ~d invariants~n", [NInvariants]), fail)).

gen_invariant(TaskList) :- test_task_list(TaskList, _).
gen_invariants(TaskLists) :- test_task_lists(TaskLists, _).
gen_invariants_dedup(TaskLists) :- test_task_lists_dedup(TaskLists, _).
