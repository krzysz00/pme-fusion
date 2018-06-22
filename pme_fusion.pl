/*
 * Copyright ⓒ 2018 Krzysztof Drewniak
 *
 * This file is part of pme-fusion.

 * pme-fusion is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.

 * pme-fusion is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.

 * You should have received a copy of the GNU General Public License
 * along with pme-fusion. If not, see <http://www.gnu.org/licenses/>.
 */
:- module(pme_fusion,
          [make_region/5, region_with_tasks/3,
           make_pme/2, make_pmes/2,
           fused_invariants/1, loop_invariant/1,
           print_invariant/1, print_invariants/1, print_invariants_sep/1,
           gen_invariant/1, gen_invariants/1, gen_invariants_dedup/1,
           test_task_list/2, test_task_lists/2, test_task_lists_dedup/2]).

/** <module> Find fusable loop invariants from partitioned (matrix) expressions

This module contains the main algorithm for and interface to
partitioned-expression based fusion. The input format used by the
API is based on FLAME notation, but is not limited to linear
algebra.

A series of fusable loop invariants consists of a loop invariant for
each operation in the algoritm that is to be fused. If an algorithm
for each operation is derived from that operation's loop invariant,
the fusability guarantees that the loop bodies of these algorithms
can be concatentated without issue.

The system's inputs consists of a list of lists of tasks, which
represent the computations each operation being fused will need to
perform.

It should be noted that each operation being fused is specified as
if it were the only operation being performed.

# Usage
The main interface to the API is gen_invariants/1 (and its
relatives gen_invariant/1 and gen_invariants_dedup/1). These
functions take a list of lists of tasks (with the exception of the
convenience function gen_invariant/1, which strips the outer
list). They find and print all fusable loop invariants for the
series of operations specified by the task lists.

An alternate entry point is provided by make_pmes/2 and
fused_invariants/1. make_pmes/2 transforms a list of task
lists (like the input to gen_invariants/1) into a lists of lists
of `region` objects which have not yet been made into concrete loop
invariants. fused_invariants/1 takes such a list of list of
regions and binds every region's `past` and `future` fields to
values that create a series of fusable loop invariants. It will
succeed multiple times, once per set of loop invariants. (and so, it
can also be used to check an invariant for validity). A fully
determined (with no free variables) list of regions can be printed
with print_invariant/1 (and a list of those can be printed with
print_invariants/1).

# Types and syntax
We well specify the input format for our API in a bottom-up matter.

An `id` is an arbitrary atom representing a region in a FLAME-style
partitioning of an object. The algorithms whose loop invariants this
code generates operate by repeatedly repartitioning objects to move
their date between regions while maintaining the loop invariant.

Any region (with ID `Id`) can be in one of several `base_state`s,
which represent the current contents of the region in memory.
A `base_state` can be one of the following terms
  * hat(Id)
    The initial state of a region at the beginning of an operation
  * tilde(Id)
    The final state of a region, which occurs once that region has
    been fully overwritten with the results of the operation.
  * during(Id, N)
    The `N`th intermediate state of a region, representing partial
    computation. States with a higher `N` value within the same
    `Region` must come after those with lower values of `N`. `N` is
    an integer.
  * during(Id, N, Alt)
    An intermediate state, as above. The `Alt` parameter allows for
    specifying groups of states that may be in any order relative to
    each other. This feature, which is often combined with the `any`
    state may be needed in cases such as representing $A = A - B -
    C$, which we write as the two tasks `eq(during(a, 0, a),
    sub(any([hat(a), during(a, 0, b)]), b))` and `eq(during(a, 0,
    b), sub(any([hat(a), during(a, 0, a)]), c))`, which show that
    the subtractions can be rearranged relative to each other.

A `state` is either a `base_state` or `any([BaseState, ...,])`, which is used when specifying several possible `base_state`s that a task can read from.
An `any` state cannot be used as the output of a task.

An `input_term` is an arbitrary ground term (that is, an arbitrary collection of function symbols, lists, atoms, etc.) that may contain `state`s as subterms.
For example, `hat(a_tl)` is an `input_term`, as is `multiply(hat(a_tl), add(tilde(a_tr), hat(a_tl)))`, or `[cthulu(parrot), summon(any([hat(a_tl), during(a_tl, 0, a)]))]`.
The invariant finder only considers the extracted `state`s for the purposes of invariant finding.
However, the ability to use arbitrary terms to describe the inputs allows for more human-readable task lists (and output).

A `task` is one of the following:
  * eq(BaseState, InputTerm)
    This is a task that writes out `BaseState` by performing the
    computations in `InputTerm`. The `state`s in `InputTerm` and
    `BaseState` are used to track dependencies between tasks.
  * op_eq(BaseState, InputTerm)
    This is the same as `eq(BaseState, InputTerm)`, except that it
    signifies that the task represents the operation that loop
    invariants are being sought for.

    For example, in a task list for a lower-tirangular solve, we would
    need to write `op_eq(tilde(x_t), solve(l_tl, b_t))` but
    `eq(during(x_b, 0), sub(hat(x_b), mul(l_bl, tilde(x_t))))`, since
    the second operation is not a lower-triangular solve. Using
    `op_eq` is important, as it is used to ensure that the generated
    loops are capable of making progress towards computing an
    operation.
  * comes_from(OutBaseState, InputTerm) This is a special task used
    when the expression InputTerm also necessarily entails the
    computation of OutBaseState. purpose of this task is to connect
    the computation of the two states so that one cannot remain
    uncomputed while the other has been. This is useful in cases such
    as the LU factorization, where the tasks that generate `l_tl` also
    compute `u_tl`.
  * const(BaseState) this is a task that is generally automatically
    created, which represents a region that is a pure input - that is,
    one that is not ever updated by the algorithm. The purpose of this
    tasks is to allow maintaining a consistent direction of iteration
    when ensuring that requires analyzing such inputs. These tasks
    follow the typical fusion analysis, and have the additional
    restriction that they cannot be in the loop invariant unless one
    of the tasks that depends on them is.

On input, each of the operations that is to be fused is represented
as a list of tasks. Before the algorithms begins, these tasks are
organized into `region`s, which group together the tasks that create
output states in a given region, that is tasks with the same ID in
their output state.
The fields of a `region` areas
  * id
    The ID associated with that region.
  * tasks
    The list (though order is irrelevant) of all tasks associated
    with the region. In a fully-formed region, `tasks` is the union
    of the disjoint sets `past` and `future`
  * past
    The list of all tasks that are part of the loop invariant.
  * future
    The list of all tasks that are part of the remainder, that is,
    that are not in the loop invariant

Regions can be created by make_region/5 or
region_with_tasks/3, which leaves the `past` and `future` fields
bound to variables.

@author Krzysztof Drewniak
@license GPLv3 or later
*/

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

operands_regions_set([], Acc, Out) :- Acc = Out.
operands_regions_set([any(Ops)|Tl], Acc, Out) :- !,
    maplist(operand_region, Ops, OpRegionsWithDups),
    sort(OpRegionsWithDups, OpRegions),
    ord_union(OpRegions, Acc, NewAcc),
    operands_regions_set(Tl, NewAcc, Out).
operands_regions_set([Op|Tl], Acc, Out) :-
    operand_region(Op, OpReg),
    ord_add_element(Acc, OpReg, NewAcc),
    operands_regions_set(Tl, NewAcc, Out).

operands_regions_set(Ops, Out) :- operands_regions_set(Ops, [], Out).

productive_task(eq(O, _)) :- base_operand(O).
productive_task(op_eq(O, _)) :- base_operand(O).

task(comes_from(O, _)) :- base_operand(O).
task(const(O)) :- base_operand(O).
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

task_split(op_eq(O, I), In, Out) :- extract_operands(I, InOps), In = InOps, Out = O.
task_split(eq(O, I), In, Out) :- extract_operands(I, InOps), In = InOps, Out = O.
task_split(comes_from(O, I), In, Out) :- extract_operands(I, InOps), In = InOps, Out = O.
task_split(const(O), In, Out) :- Out = O, In = [].

task_output(op_eq(O, _), O) :- !.
task_output(eq(O, _), O) :- !.
task_output(comes_from(O, _), O) :- !.
task_output(const(O), O) :- !.
task_output(Task) :-
    format("ERROR: ~w is not a task in task list~n", [Task]),
    fail.

task_input(op_eq(_, I), I) :- !.
task_input(eq(_, I), I) :- !.
task_input(comes_from(_, I), I) :- !.
task_input(const(_), []) :- !.
task_input(Task) :-
    format("ERROR: ~w is not a task in task list~n", [Task]),
    fail.

task_output_region(Task, Out) :-
    task_output(Task, O),
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
                          format("INFO: Region ~w (from ~w) doesn't appear as an output anywhere. Pure input analysis is being applied.~n", [Reg, Term]),
                          ord_add_element(Acc, Reg, ExtraInRegions)));
    any(Ops) = Term -> (collect_extra_input_regions(OutRegions, Ops, [], SubAcc),
                        ord_union(Acc, SubAcc, ExtraInRegions));
    compound(Term) -> (compound_name_arguments(Term, _, Args),
                       collect_extra_input_regions(OutRegions, Args, [], SubAcc),
                       ord_union(Acc, SubAcc, ExtraInRegions));
    ord_memberchk(Term, OutRegions) -> (format("WARNING: ~w appears an input without an associated state~n", [Term]),
                                        ExtraInRegions = Acc);
    ExtraInRegions = Acc.

find_regions_as_constants(Regions, Parent, Term) :-
    (operand(Term), !);
    (atom(Term), ord_memberchk(Term, Regions),
     format("WARNING: The region ~w appears without a state specifier in ~w~n", [Term, Parent]), !);
    (is_list(Term), maplist(find_regions_as_constants(Regions, Term), Term), !);
    (compound(Term), compound_name_arguments(Term, Name, Args),
     (((Name == any, length(Args, ArgLen), ArgLen =\= 1) ->
           format("WARNING: Failure to put any argument in a list in ~w~n", [Term]); true),
      maplist(find_regions_as_constants(Regions, Term), Args), !));
    true.
find_regions_as_constants(Regions, Term) :-
    find_regions_as_constants(Regions, Term, Term).


collect_extra_input_regions(OutRegions, Term, ExtraInRegions) :-
    collect_extra_input_regions(OutRegions, Term, [], ExtraInRegions).

has_op(List) :-
    exists_one(=(op_eq(_, _)), List).

%! make_region(++Id:atom, +Tasks:task_list, ?Past:task_list, ?Future:task_list, -Reg:region) is semidet.
% The lowest-level constructor for a `region`.
%
% Fails if `Id` is not an atom or if `Tasks` are not all tasks. Does
% **not** enforce that `Tasks` is a union of `past` and `future`, or
% that all of the tasks target the same `Id`.
make_region(Id, Tasks, Past, Future, Reg) :-
    atom(Id),
    ((maplist(task, Tasks), !);
     (format("ERROR: Invalid output for assignment in region ~w (tasks ~w)~n", [Id, Tasks]), fail)),
    Reg = region{id:Id, tasks:Tasks, past:Past, future:Future}.

%! region_with_tasks(++Id:atom, +Tasks:task_list, -Reg:region) is semidet.
%
% Convenience wrapper that creates the region `Reg` with the given
% `Id` and `Tasks`.
%
% @see make_region/5
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

to_const_task(Symbol, Region) :- Region = Symbol-[const(hat(Symbol))].

add_const_tasks([], [], Acc, NewRegs) :- reverse(Acc, NewRegs).
add_const_tasks([Loop|Loops], [Extras|MoreExtras], Acc, NewRegs) :-
    maplist(to_const_task, Extras, ExtraRegions),
    append(ExtraRegions, Loop, NewLoop),
    add_const_tasks(Loops, MoreExtras, [NewLoop|Acc], NewRegs).

add_const_tasks(IdTasks, ExtraRegions, NewIdTasks) :-
    add_const_tasks(IdTasks, ExtraRegions, [], NewIdTasks).

%! make_pme(+TaskList:task_list, -Regions:region_list) is semidet.
%
% Convenience wrapper around make_pmes/2 for the case when there
% is one operation.
make_pme(TaskList, Regions) :-
    make_pmes([TaskList], [Regions]).

%! make_pmes(+TaskLists:task_list_list, -PMEs:region_list_list) is semidet.
%
% Transforms the list of lists of tasks (one task-list per operation
% being fused) into a list of list of regions, that is, a list of
% partitioned matrix expressions (PMEs). This transformation will
% create all necessary region objects, including the empty ones
% required to ensure loop fusion.
%
% Will fail if anything in `TaskLists` is not a valid task, and will
% warn for:
%   * Regions that are tagged with a state in an input but never used
%     as an output
%   * Regions that appear without state specifiers
%
% The output of this function is suitable as input for
% fused_invariants/1's search mode.
make_pmes(TaskLists, PMEs) :-
    maplist(tasks_grouped_by_region, TaskLists, IdTasks),
    maplist(pairs_keys, IdTasks, RegionsByLoop), % Sorted by the gather
    ord_union(RegionsByLoop, AllOutRegions),
    maplist(maplist(task_input), TaskLists, TaskInputs),
    % Find where we need a const() task in any loop
    maplist(collect_extra_input_regions(AllOutRegions), TaskInputs, ExtraInRegions),
    add_const_tasks(IdTasks, ExtraInRegions, IdTasksWithConst),
    ord_union(ExtraInRegions, FlatExtraInRegions),
    ord_union(AllOutRegions, FlatExtraInRegions, AllRegions),
    find_regions_as_constants(AllRegions, TaskInputs),
    add_empty_regions(AllRegions, IdTasksWithConst, FullIdTasks),
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

task_output_flip(Region, Task) :- task_output(Task, Region).

state_computed_in_past(Regions, any(States)) :- !,
    exists_one(state_in_past(Regions), States).
state_computed_in_past(Regions, State) :-
    operand_region(State, StateReg),
    region_with_id(StateReg, Regions, Region),
    exists_one(task_output_flip(State), Region.past).

no_floating_noops_future(Regions, comes_from(_, In)) :- !,
    extract_operands(In, InOps),
    \+ maplist(state_computed_in_past(Regions), InOps).
no_floating_noops_future(_, _).

no_pointless_const_computation_past(PastInSymbolSet, const(Out)) :- !,
    operand_region(Out, Reg),
    ord_memberchk(Reg, PastInSymbolSet).
no_pointless_const_computation_past(_, _).

no_pointless_const_computation_future(PastInSymbolSet, const(Out)) :- !,
    operand_region(Out, Reg),
    \+ ord_memberchk(Reg, PastInSymbolSet).
no_pointless_const_computation_future(_, _).

no_pointless_const_computation(Regions) :-
    collect_field(Regions, past, Pasts),
    collect_field(Regions, future, Futures),
    partition_task_operands(Pasts, PastInputs, _),
    operands_regions_set(PastInputs, OpSet),
    maplist(no_pointless_const_computation_past(OpSet), Pasts),
    maplist(no_pointless_const_computation_future(OpSet), Futures).

no_floating_noops(Regions, Region) :-
    maplist(no_floating_noops_future(Regions), Region.future).

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
    no_pointless_const_computation(Invariant),
    dependencies_preserved(Invariant).

%! fused_invariants(?Invariants:region_list_list) is nondet.
%! fused_invariants(+Invariants:region_list_list) is semidet.
%
% When at least one region's `past` and `future` fields are unbound,
% find loop invariants for each operation (represented by a list of
% regions) in the input, such that the loops can be fused - that is,
% if the loop invariants for each operation are used to generate an
% algorithm, the loop bodies of the algorithms can be concatentated
% without sacrificing the correctness of each invariant.
%
% This predicate will succeed once for each possible fusable loop
% invariant.
%
% If the `past` and `future` fields of all the input regions are
% bound, verify that the given input constitutes a series of fusable
% loop invariants.
%
% @see make_pmes/2
fused_invariants(Invariants) :-
    transpose_invariants(Invariants, Strips),
    fusable(Strips),
    maplist(valid_loop_invariant, Invariants).

%! loop_invariant(?Invariant) is nondet.
%! loop_invariant(+Invariant) is semidet.
%
% A converience wrapper around fused_invariants/1 that finds all
% loop invariants for a single operation.
loop_invariant(Invariant) :-
    fused_invariants([Invariant]).

%% Test and example code

print_region(Region) :-
    (Region.tasks == [], !);
    format("~w past: ~w~n~w future: ~w~n", [Region.id, Region.past, Region.id, Region.future]).

%! print_invariant(+Invariant:region_list) is det.
%
% Print all non-empty regions in the given loop invariant. The `past`
% and `future` lists in each `region` must be ground terms.
%
% Both the `past` (the loop invariant) and `future` (the remainder)
% for each region is printed.
print_invariant(Invariant) :-
    maplist(print_region, Invariant).

%! print_invariants(+Invariants:region_list_lists) is det.
%
% Prints each loop invariant in a list of loop invariants, separated by "then".
% @see print_invariant/1.
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

%! print_invariants_sep(+Invariants:region_list_list) is det.
%
% Convenience wrapper around print_invariants/1 that adds a blank
% line after the invariants. This is provided to allow
% maplist/2ing over a list of different loop invariants, such as
% one that would be produced by findall/3.
%
% @see print_invariants/1
print_invariants_sep(Invariants) :-
    print_invariants(Invariants),
    format("~n").

%! test_task_list(+TaskList:task_list, -NInvariants:int) is semidet.
%
% Like gen_invariant/1, but it will report the number of
% invariants found in `NInvariants`. If `NInvariants` fails to unify,
% a helpful error message is reported.
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

%! test_task_lists(+TaskLists:task_list_list, -NInvariants:int) is semidet.
%
% Like gen_invariants/1, but it will report the number of invariant series found in `NInvariants`.
% If `NInvariants` fails to unify, a helpful error message is reported.
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

%! test_task_lists_dedup(+TaskLists:task_list_list, -NInvariants:int) is semidet.
%
% Like gen_invariants_dedup/1, but it will report the number of
% unique invariant series found in `NInvariants`. If `NInvariants`
% fails to unify, a helpful error message is reported.
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

%! gen_invariant(+TaskList:task_list) is semidet.
%
% Finds and prints all loop invariants for a given list of tasks.
% @see gen_invariants/1
gen_invariant(TaskList) :- test_task_list(TaskList, _).

%! gen_invariants(+TaskLists:task_list_lists) is semidet.
%
% Find and print all fusable loop invariants for the given list of
% operations, each of which are specified as a list of tasks.
% @see make_pme/2
% @see fused_invariants/1
gen_invariants(TaskLists) :- test_task_lists(TaskLists, _).

%! gen_invariants_dedup(+TaskLists:task_list_list) is semidet.
%
% Like gen_invariants/1, but the results are deduplicated before
% printing. This should not be necessary, but it is provided in the
% event that excess nondeterminism affects your results.
gen_invariants_dedup(TaskLists) :- test_task_lists_dedup(TaskLists, _).
