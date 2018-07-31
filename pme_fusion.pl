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
          [fusion_constrained_system_for_tasks/2,
           fused_invariants_for_system/3,
           fused_invariants/3, loop_invariant/3,
           print_task/2,
           print_task_list/2, print_task_lists/2,
           solutions_print_helper/1,
           gen_invariant/1, gen_invariants/1,
           test_task_list/2, test_task_lists/2
          ]).
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
The main interface to the API is gen_invariants/1 (and its relative
gen_invariant/1). These functions take a list of lists of tasks or a
list of tasks, respectively. They find and print all (fusable) loop
invariants for the series of operations specified by the task lists.

An alternate interfare is provided by
fusion_constrained_system_for_tasks/2 and
fused_invariants_for_system/3.
`fusion_constrained_system_for_tasks(Tasks, System)` returns a
`system` dictionary (described in more detail below) that, among other
things, includes the system of indicator variables and constraints
that indicate what partitions of a task list into a `past` and a
`future` are valid. The `system` value can be modified to enforce
additional constraints before the search, which is performed by
fused_invariants_for_system/3. That function takes a `system`
dictionary and returns once for each valid split of the tasks that
created it into `Pasts` (a list of list of tasks in each loop's
invariant) and `Futures` (a list of lists tasks in each loop's
remainder). These lists can be passed to printing functions like
print_task_lists/2 or print_task_lists_sep/2 (which adds a newline
after the lists, which is useful when mapping over the set of possible
results) in order to present them.

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
  * const(BaseState) This is a task that is generally automatically
    created, which represents a region that is a pure input - that is,
    one that is not ever updated by the algorithm. The purpose of this
    tasks is to allow maintaining a consistent direction of iteration
    when ensuring that requires analyzing such inputs. These tasks
    follow the typical fusion analysis, and have the additional
    restriction that they cannot be in the loop invariant unless one
    of the tasks that depends on them is.

The `system` dictionary returned by
fusion_constrained_system_for_tasks/2 has the following four fields:
  * tasks This contains the list of lists of tasks that generated the
    system, with const tasks included
  * indicators A list of `assoc` structures, one per loop. The keys to
    these lists are the outputs of each task in that loop, while the
    values are variables with `clpfd` constrains applied and domain
    `0..1`. Having an indicator set to `1` indicates that the task
    with the associated output is in the loop invariant, `0` indicates
    it is in the remainder.
  * computed An `assoc` where the keys are regions (not states) that
    appear in the fusion problem with values whose domains are `-1..N
    - 1` (where `N` is the number of loops being fused). The values
    represent the index of the last loop in a fusion problem where the
    associated region is fully computed. These variables are not
    searched, but do participate in constraints.
  * uncomputed Like `computed`, except that each variable represents
    the index of the first loop where the associated region is
    uncomputed, and the variables have domain `0..N`.

It is safe to apply additional constraints to any of these variables before calling
fused_invariants_for_system/3.

@author Krzysztof Drewniak
@license GPLv3 or later
*/
:- use_module(library(assoc)).
:- use_module(library(clpfd)).
meta_predicate exists(1, +, -), exists_one(1, +), exists_one(2, +, +).

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

base_state(hat(X)) :- atom(X).
base_state(during(X, N)) :- atom(X), integer(N).
base_state(during(X, N, V)) :- atom(X), integer(N), atom(V).
base_state(tilde(X)) :- atom(X).

state(any(States)) :- maplist(base_state, States), !.
state(X) :- base_state(X).

state_region(any(States), Y) :-
    maplist(state_region, States, StateRegionsWithDups),
    sort(StateRegionsWithDups, StateRegions),
    member(Y, StateRegions).
state_region(hat(X), X).
state_region(during(X, _), X).
state_region(during(X, _, _), X).
state_region(tilde(X), X).

states_regions_set([], Acc, Acc).
states_regions_set([any(States)|Tl], Acc, Out) :- !,
    maplist(state_region, States, StateRegionsWithDups),
    sort(StateRegionsWithDups, StateRegions),
    ord_union(StateRegions, Acc, NewAcc),
    states_regions_set(Tl, NewAcc, Out).
states_regions_set([State|Tl], Acc, Out) :-
    state_region(State, StateReg),
    ord_add_element(Acc, StateReg, NewAcc),
    states_regions_set(Tl, NewAcc, Out).

states_regions_set(States, Out) :-
    states_regions_set(States, [], Out).

productive_task(eq(O, _)) :- base_state(O).
productive_task(op_eq(O, _)) :- base_state(O).

task(comes_from(O, _)) :- base_state(O).
task(const(O)) :- base_state(O).
task(X) :- productive_task(X).

task_split(op_eq(O, I), In, Out) :- extract_states(I, InOps), In = InOps, Out = O.
task_split(eq(O, I), In, Out) :- extract_states(I, InOps), In = InOps, Out = O.
task_split(comes_from(O, I), In, Out) :- extract_states(I, InOps), In = InOps, Out = O.
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

task_output_region(Task, Region) :-
    task_output(Task, Output),
    state_region(Output, Region).

extract_states(Term, Acc, Out) :-
    state(Term) -> ord_add_element(Acc, Term, Out);
    is_list(Term) -> foldl(extract_states, Term, Acc, Out);
    compound(Term) -> (compound_name_arguments(Term, _, Args),
                       foldl(extract_states, Args, Acc, Out));
    Out = Acc.

extract_states(Term, Out) :- extract_states(Term, [], Out).

extract_base_states(Term, Acc, Out) :-
    base_state(Term) -> ord_add_element(Acc, Term, Out);
    is_list(Term) -> foldl(extract_base_states, Term, Acc, Out);
    compound(Term) -> (compound_name_arguments(Term, _, Args),
                       foldl(extract_base_states, Args, Acc, Out));
    Out = Acc.

extract_base_states(Term, Out) :- extract_states(Term, [], Out).

tasks_grouped_by_region(TaskList, IdTasks) :-
    map_list_to_pairs(task_output_region, TaskList, Pairs),
    keysort(Pairs, Sorted),
    group_pairs_by_key(Sorted, IdTasks).

pair_with_domain(Lower, Upper, Key, Out) :-
    Var in Lower..Upper,
    Out = Key-Var.

assoc_with_domain(OrdKeys, Lower, Upper, Assoc) :-
    maplist(pair_with_domain(Lower, Upper), OrdKeys, Entries),
    ord_list_to_assoc(Entries, Assoc).

preceeds_flip(X, Y) :- preceeds(Y, X).

preceeds(hat(X), during(X, _)).
preceeds(hat(X), during(X, _, _)).
preceeds(hat(X), tilde(X)).
preceeds(during(X, M), during(X, N)) :- M < N.
preceeds(during(X, M, _), during(X, N)) :- M < N.
preceeds(during(X, M), during(X, N, _)) :- M < N.
preceeds(during(X, M, _), during(X, N, _)) :- M < N.
preceeds(during(X, _), tilde(X)).
preceeds(during(X, _, _), tilde(X)).

required_for_past_input(Input, Input) :- !.
required_for_past_input(State, Input) :- preceeds(State, Input).

required_for_past_input_flip(Input, State) :- required_for_past_input(State, Input).

required_for_future_input(State, Input) :- preceeds(Input, State).

required_for_future_input_flip(Input, State) :- required_for_future_input(State, Input).

out_states_of(Tasks, StateSet) :-
    maplist(task_output, Tasks, States),
    sort(States, StateSet),
    length(States, NRaw),
    length(StateSet, N),
    (NRaw =:= N, !; format("Error: multiple tasks for one memory state~n"), fail).

tasks_to_indicators(Tasks, Indicators, StateSet) :-
    out_states_of(Tasks, StateSet),
    assoc_with_domain(StateSet, 0, 1, Indicators).

states_needed_for_past_input(StateSet, InState, List) :-
    include(required_for_past_input_flip(InState), StateSet, List).

states_needed_for_future_input(StateSet, InState, List) :-
    include(required_for_future_input_flip(InState), StateSet, List).

build_base_dep_constraint_(_Type, _Indicators, [], 1) :- !.
build_base_dep_constraint_(Type, Indicators, [State], Constraint) :- !,
    get_assoc(State, Indicators, Var),
    Constraint = (Var #= Type).

build_base_dep_constraint_(Type, Indicators, [State|[Next|Tail]], Constraint) :- !,
    get_assoc(State, Indicators, Var),
    build_base_dep_constraint_(Type, Indicators, [Next|Tail], SubConstr),
    Constraint = ((Var #= Type) #/\ SubConstr).

build_base_dep_constraint(1, Indicators, StateSet, Input, Constraint) :- !,
    states_needed_for_past_input(StateSet, Input, RelevantStates),
    build_base_dep_constraint_(1, Indicators, RelevantStates, Constraint).

build_base_dep_constraint(0, Indicators, StateSet, Input, Constraint) :- !,
    states_needed_for_future_input(StateSet, Input, RelevantStates),
    build_base_dep_constraint_(0, Indicators, RelevantStates, Constraint).

build_any_dep_constraint(Type, Indicators, StateSet, [Input], Constraint) :- !,
    % Yes, this preserves 1s, that's intentional
    build_base_dep_constraint(Type, Indicators, StateSet, Input, Constraint).

build_any_dep_constraint(Type, Indicators, StateSet, [Input|[Next|Inputs]], Constraint) :- !,
    build_any_dep_constraint(Type, Indicators, StateSet, [Next|Inputs], SubConstraint),
    build_base_dep_constraint(Type, Indicators, StateSet, Input, NewConstraint),
    Constraint = (NewConstraint #\/ SubConstraint).

build_dep_constraint(_Type, _Indicators, _StateSet, any([]), _) :-
    format("ERROR: Empty any input~n"), fail.
build_dep_constraint(Type, Indicators, StateSet, any([State]), Constraint) :-
    build_dep_constraint(Type, Indicators, StateSet, State, Constraint).
build_dep_constraint(Type, Indicators, StateSet, any([State|[Next|Rest]]), Constraint) :-
    build_any_dep_constraint(Type, Indicators, StateSet, [State|[Next|Rest]], Constraint).

build_dep_constraint(Type, Indicators, StateSet, InState, Constraint) :- base_state(InState),
    build_base_dep_constraint(Type, Indicators, StateSet, InState, Constraint).

add_dep_constraint(Type, Indicators, OutTaskVar, StateSet, InState) :-
    build_dep_constraint(Type, Indicators, StateSet, InState, Constraint),
    ((Constraint \== 1) -> ((OutTaskVar #= Type) #==> Constraint); true).

add_past_dep_constraints(Indicators, StateSet, Task) :-
    task_split(Task, Inputs, Output),
    get_assoc(Output, Indicators, OutVar),
    maplist(add_dep_constraint(1, Indicators, OutVar, StateSet), Inputs).

add_future_dep_constraints(Indicators, StateSet, Task) :-
    task_split(Task, Inputs, Output),
    get_assoc(Output, Indicators, OutVar),
    maplist(add_dep_constraint(0, Indicators, OutVar, StateSet), Inputs).

gather_operation_task_vars(_, [], Acc, Acc) :- !.
gather_operation_task_vars(Indicators, [op_eq(Reg, _)|Tasks], Acc, Out) :- !,
    get_assoc(Reg, Indicators, Var),
    gather_operation_task_vars(Indicators, Tasks, [Var|Acc], Out).
gather_operation_task_vars(Indicators, [_|Tasks], Acc, Out) :- !,
    gather_operation_task_vars(Indicators, Tasks, Acc, Out).

gather_operation_task_vars(Indicators, Tasks, Vars) :-
    gather_operation_task_vars(Indicators, Tasks, [], Vars).

add_loop_progress_constraints(Indicators, Tasks) :-
    gather_operation_task_vars(Indicators, Tasks, Vars),
    length(Vars, NOps),
    sum(Vars, #\=, 0),
    sum(Vars, #\=, NOps).

and_constraints(1, Acc, Acc) :- !.
and_constraints(Constraint, Acc, Out) :-
    Out = (Constraint #/\ Acc).

add_comes_from_constraint(Indicators, StateSet, comes_from(Out, Expr)) :- !,
    get_assoc(Out, Indicators, OutVar),
    extract_states(Expr, InputSet),
    maplist(build_dep_constraint(1, Indicators, StateSet), InputSet, Constraints),
    foldl(and_constraints, Constraints, 1, Constraint),
    (Constraint \== 1 -> Constraint #==> (OutVar #= 1); true).
add_comes_from_constraint(_, _, _).

build_base_const_constraint(Indicators, Region, Task, Constraint) :-
    task_split(Task, Inputs, Output),
    states_regions_set(Inputs, Regions),
    ord_memberchk(Region, Regions),
    get_assoc(Output, Indicators, OutVar), !,
    Constraint = (OutVar #= 1);
    % Failure case
    Constraint = na.

build_const_constraint(_, _, [], na).
build_const_constraint(Indicators, Region, [Task|Tasks], Constraint) :-
    build_base_const_constraint(Indicators, Region, Task, NewConstraint),
    build_const_constraint(Indicators, Region, Tasks, SubConstraint),
    (SubConstraint \== na ->
         (NewConstraint \== na ->
              (Constraint = (NewConstraint #\/ SubConstraint));
          Constraint = SubConstraint);
    Constraint = NewConstraint).

add_const_constraint(Indicators, TaskList, const(State)) :- !,
    state_region(State, Region),
    build_const_constraint(Indicators, Region, TaskList, Constraint),
    ((Constraint \== na) ->
         (get_assoc(State, Indicators, Var),
          (Var #= 1) #<==> Constraint);
         true).
add_const_constraint(_, _, _).

constrained_indicators_for_tasks(Tasks, Indicators) :-
    tasks_to_indicators(Tasks, Indicators, StateSet),
    maplist(add_past_dep_constraints(Indicators, StateSet), Tasks),
    maplist(add_future_dep_constraints(Indicators, StateSet), Tasks),
    maplist(add_comes_from_constraint(Indicators, StateSet), Tasks),
    maplist(add_const_constraint(Indicators, Tasks), Tasks),
    add_loop_progress_constraints(Indicators, Tasks).

placed_in_past(Indicators, Task) :-
    task_output(Task, State),
    get_assoc(State, Indicators, Var),
    Var =:= 1.

read_indicators(Indicators, Tasks, Past, Future) :-
    partition(placed_in_past(Indicators), Tasks, Past, Future).

task_lists_to_fusion_vars(TaskLists, Computed, Uncomputed) :-
    extract_base_states(TaskLists, Ops),
    states_regions_set(Ops, RegSet),
    length(TaskLists, N),
    assoc_with_domain(RegSet, 0, N, Uncomputed),
    ComputedBound is N - 1,
    assoc_with_domain(RegSet, -1, ComputedBound, Computed).

build_integer_constraint(ge, Delta, Var, N, Constraint) :- !,
    Constraint = (Var #>= (N + Delta)).
build_integer_constraint(le, Delta, Var, N, Constraint) :- !,
    Constraint = (Var #=< (N + Delta)).

regions_for_fusion_use(Term, Acc, Out) :-
    base_state(Term) -> (state_region(Term, Region),
                         ord_add_element(Acc, Region, Out));
    (Term = any(States)) -> (regions_for_fusion_use(States, [], Sublist),
                             ord_add_element(Acc, Sublist, Out));
    is_list(Term) -> foldl(regions_for_fusion_use, Term, Acc, Out);
    compound(Term) -> (compound_name_arguments(Term, _, Args),
                       foldl(regions_for_fusion_use, Args, Acc, Out));
    Out = Acc.
regions_for_fusion_use(Term, Out) :- regions_for_fusion_use(Term, [], Out).

build_base_fusion_use_constraint_(Vars, Op, Delta, N, Region, Constraint) :- !,
    get_assoc(Region, Vars, Var),
    build_integer_constraint(Op, Delta, Var, N, Constraint).

build_base_fusion_use_constraint(_, _, _, _, [], 1) :- !.
build_base_fusion_use_constraint(Vars, Op, Delta, N, [Region], Constraint) :- !,
    (is_list(Region)) ->
        build_any_fusion_use_constraint(Vars, Op, Delta, N, Region, Constraint);
    (build_base_fusion_use_constraint_(Vars, Op, Delta, N, Region, Constraint)), !.

build_base_fusion_use_constraint(Vars, Op, Delta, N, [Region|[Next|Rest]], Constraint) :- !,
    (is_list(Region) ->
         build_any_fusion_use_constraint(Vars, Op, Delta, N, Region, NewConstr);
     build_base_fusion_use_constraint_(Vars, Op, Delta, N, Region, NewConstr)), !,
    build_base_fusion_use_constraint(Vars, Op, Delta, N, [Next|Rest], SubConstr),
    Constraint = (NewConstr #/\ SubConstr).

build_any_fusion_use_constraint(Vars, Op, Delta, N, [Region], Constraint) :- !,
    build_base_fusion_use_constraint_(Vars, Op, Delta, N, Region, Constraint).

build_any_fusion_use_constraint(Vars, Op, Delta, N, [Region|[Next|Rest]], Constraint) :- !,
    build_base_fusion_use_constraint_(Vars, Op, Delta, N, Region, NewConstr),
    build_any_fusion_use_constraint(Vars, Op, Delta, N, [Next|Rest], SubConstr),
    Constraint = (NewConstr #\/ SubConstr).

add_fusion_use_constraints_(Indicators, Computed, Uncomputed, N, Task) :-
    task_split(Task, Input, Output),
    get_assoc(Output, Indicators, OutVar),
    regions_for_fusion_use(Input, Regions), !,

    build_base_fusion_use_constraint(Computed, ge, -1, N, Regions, ComputedConstr),
    (OutVar #= 1) #==> ComputedConstr,

    build_base_fusion_use_constraint(Uncomputed, le, 1, N, Regions, UncomputedConstr),
    (OutVar #= 0) #==> UncomputedConstr.

add_fusion_use_constraints([], _, _, _, []) :- !.
add_fusion_use_constraints([Indicators|MoreIndicators], Computed, Uncomputed,
                           N, [TaskList|TaskLists]) :- !,
    maplist(add_fusion_use_constraints_(Indicators, Computed, Uncomputed, N), TaskList),
    NewN is N + 1,
    add_fusion_use_constraints(MoreIndicators, Computed, Uncomputed, NewN, TaskLists).

add_fusion_use_constraints(IndicatorList, Computed, Uncomputed, TaskLists) :- !,
    add_fusion_use_constraints(IndicatorList, Computed, Uncomputed, 0, TaskLists).

build_fusion_entailment_constraint(Type, Indicators, [Output], Constraint) :- !,
    get_assoc(Output, Indicators, Var),
    Constraint = (Var #= Type).
build_fusion_entailment_constraint(Type, Indicators, [Output|[Next|Rest]], Constraint) :- !,
    get_assoc(Output, Indicators, Var),
    build_fusion_entailment_constraint(Type, Indicators, [Next|Rest], SubConstraint),
    Constraint = ((Var #= Type) #/\ SubConstraint).

add_fusion_entailment_constraints(Indicators, Computed, Uncomputed, N, Reg-Tasks) :-
    maplist(task_output, Tasks, Outputs),
    get_assoc(Reg, Computed, ComputedVar),
    get_assoc(Reg, Uncomputed, UncomputedVar),

    build_fusion_entailment_constraint(1, Indicators, Outputs, ComputedConstr),
    ((ComputedVar #>= N) #<==> ComputedConstr),

    build_fusion_entailment_constraint(0, Indicators, Outputs, UncomputedConstr),
    ((UncomputedVar #=< N) #<==> UncomputedConstr).

add_fusion_entailment_constraints([], _, _, _, []).
add_fusion_entailment_constraints([Indicators|MoreIndicators], Computed, Uncomputed,
                                  N, [TaskList|TaskLists]) :-
    tasks_grouped_by_region(TaskList, RegionTasks),
    maplist(add_fusion_entailment_constraints(Indicators, Computed, Uncomputed, N), RegionTasks),
    NewN is N + 1,
    add_fusion_entailment_constraints(MoreIndicators, Computed, Uncomputed, NewN, TaskLists).

add_fusion_entailment_constraints(IndicatorList, Computed, Uncomputed, TaskLists) :-
    add_fusion_entailment_constraints(IndicatorList, Computed, Uncomputed, 0, TaskLists).

find_present_regions(RegionSet, Term, Acc, NewSet) :-
    base_state(Term) -> (state_region(Term, Region),
                         ord_memberchk(Region, RegionSet) ->
                             ord_add_element(Acc, Region, NewSet);
                         NewSet = Acc);
    is_list(Term) -> foldl(find_present_regions(RegionSet), Term, Acc, NewSet);
    % any() is in this case
    compound(Term) -> (compound_name_arguments(Term, _, Args),
                       foldl(find_present_regions(RegionSet), Args, Acc, NewSet));
    NewSet = Acc.
find_present_regions(RegionSet, Term, NewRegionSet) :-
    find_present_regions(RegionSet, Term, [], NewRegionSet).

const_task_for_region(Region, const(hat(Region))).

add_const_tasks(AllConstRegions, TaskList, NewTaskList) :-
    find_present_regions(AllConstRegions, TaskList, RegionsForConst),
    maplist(const_task_for_region, RegionsForConst, NewTasks),
    append(NewTasks, TaskList, NewTaskList).

add_const_tasks(TaskLists, NewTaskLists) :-
    extract_base_states(TaskLists, AllStates),
    states_regions_set(AllStates, AllRegions),
    maplist(out_states_of, TaskLists, TaskOutputSets),
    ord_union(TaskOutputSets, AllOutStates),
    states_regions_set(AllOutStates, AllOutRegions),
    ord_subtract(AllRegions, AllOutRegions, AllConstRegions),
    (AllConstRegions \== []) ->
        (format("INFO: treating the regions ~w as pure inputs~n", [AllConstRegions]),
         maplist(add_const_tasks(AllConstRegions), TaskLists, NewTaskLists));
    (NewTaskLists = TaskLists).

warn_malformed_any(Term) :-
    Term = any(Arg), is_list(Arg) -> true;
    is_list(Term) -> maplist(warn_malformed_any, Term);
    compound(Term) -> (compound_name_arguments(Term, Name, Args),
                       (Name == any -> format("WARNING: ~w is a malformed any() term. (any() terms must have one argument, which is a list)~n", [Term]); true),
                       maplist(warn_malformed_any, Args));
    true.

%! fusion_constrained_system_for_tasks(+TaskLists:task_lists, -System:system) is semidet.
%
% Generate the system of constraints for the loops described by the
% list of list of tasks in `TaskLists` and places the corresponding
% `system` dictionary into `System`. The format of this dictionary is
% described in the module-level documentation. It is safe to add
% constraints to the `indicators`, `computed` and `uncomputed` fields
% of this dictionary before passing them to
% fused_invariants_for_system/3.
fusion_constrained_system_for_tasks(TaskLists, System) :-
    (nonground(TaskLists, Var) -> (format("ERROR: Free variable ~w in task lists~n", [Var]), fail); true),
    warn_malformed_any(TaskLists),
    add_const_tasks(TaskLists, FullTaskLists),
    maplist(constrained_indicators_for_tasks, FullTaskLists, IndicatorList),
    task_lists_to_fusion_vars(FullTaskLists, Computed, Uncomputed),
    add_fusion_use_constraints(IndicatorList, Computed, Uncomputed, FullTaskLists),
    add_fusion_entailment_constraints(IndicatorList, Computed, Uncomputed, FullTaskLists),
    System = system{tasks:FullTaskLists, indicators:IndicatorList,
                    computed:Computed, uncomputed:Uncomputed}.

%! fused_invariants_for_system(+System:system, -Pasts:task_lists, -Futures:task_lists) is nondet.
%
% Given the system of constraints `System`, yield a list of loop
% invariants/pasts (each element of `Pasts` is a list of tasks, one
% per loop, in order), and the corresponding list of `Futures`. This
% procedure proceeds by a constraint-propagating search enabled by the
% `clpfd` library.
fused_invariants_for_system(System, Pasts, Futures) :-
    system{tasks:TaskLists, indicators:IndicatorList,
           computed:_, uncomputed:_} = System,
    maplist(assoc_to_values, IndicatorList, TaskIndicators),
    flatten(TaskIndicators, AllVars),
    labeling([ffc], AllVars),
    maplist(read_indicators, IndicatorList, TaskLists, Pasts, Futures).

%! fused_invariants(+TaskLists:task_lists, -Pasts:task_lists, -Futures:task_lists) is nondet.
%
% Split the tasks in each PME (specified as a list of tasks) in
% `TaskLists` into those that are part of each loop's invariant (the
% list of invariants is stored in `Pasts`) and those that are in the
% remainder (`Futures`). Succeeds once per valid collection of fusable
% invariants.
fused_invariants(TaskLists, Pasts, Futures) :-
    fusion_constrained_system_for_tasks(TaskLists, System),
    fused_invariants_for_system(System, Pasts, Futures).

%! loop_invariant(+TaskList:task_list, -Past:task_list, -Future:task_list) is nondet.
%
% Convenience wrapper around `fused_invariants([TaskList], [Past],
% [Future])` for the case when invariants are only needed for one
% loop. In this case, the fusion analysis in trivial and does not
% affect the results.
loop_invariant(TaskList, Past, Future) :-
    fused_invariants([TaskList], [Past], [Future]).

%! print_task(+Prefix:string, +Task:task) is det.
%
% Prints a representation of `Task` to standard output, preceeded by
% `Prefix`.
print_task(Prefix, op_eq(Out, In)) :- !,
    format("~w~w :=_O ~w~n", [Prefix, Out, In]).
print_task(Prefix, eq(Out, In)) :- !,
    format("~w~w := ~w~n", [Prefix, Out, In]).
print_task(Prefix, comes_from(Out, In)) :- !,
    format("~w~w <- ~w~n", [Prefix, Out, In]).
print_task(_Prefix, const(_Out)).% :- !,
%    format("~w DEBUG const(~w)~n", [Prefix, Out]).

%! print_task_list(+Prefix:string, +TaskList:task_list) is det.
%
% Prints the tasks from `TaskList` to standard output, one per line,
% where each task is prefixed by `Prefix`.
print_task_list(Prefix, TaskList) :-
    maplist(print_task(Prefix), TaskList).

%! print_task_lists(+Prefix:string, +TaskLists:task_lists) is det.
%
% Prints the tasks from each `TaskList` to standard output, one per
% line. where each task is prefixed by `Prefix`. The tasks are in each
% list are separated by a line contained "then", to indicate the
% sequencing between loops.
print_task_lists(_Prefix, []) :- !.
print_task_lists(Prefix, [Task|[]]) :- !,
    print_task_list(Prefix, Task).
print_task_lists(Prefix, [Task|Tasks]) :-
    print_task_list(Prefix, Task),
    write("then\n"),
    print_task_lists(Prefix, Tasks).

%! solutions_print_helper(PastsList:task_lists_list) is det.
%
% Takes a list of multiple fused invariants (lists of lists of tasks
% yielded into `Pasts` by fused_invaniants/3) and prints them using
% print_task_list/2, tagged as "Invariant: ". This is a helper method
% for gen_invariants/1 and its relatives that is exposed to enable
% variants of those methods.
solutions_print_helper([]) :- !.
solutions_print_helper([Pasts|[]]) :- !,
    print_task_lists("Invariant: ", Pasts).
solutions_print_helper([Pasts|Solutions]) :-
    print_task_lists("Invariant: ", Pasts),
    write("\n"),
    solutions_print_helper(Solutions).

singleton(X, [X]).

%! test_task_list(+TaskList:task_list, -NInvariants:int) is semidet.
%
% Like gen_invariant/1, but it will report the number of invariants
% found in `NInvariants`. If `NInvariants` fails to unify, an error
% message is output.
test_task_list(TaskList, NInvariants) :-
    findall(Past,
            (loop_invariant(TaskList, Past, _)),
            Results),
    length(Results, NumResults),
    maplist(singleton, Results, OtherResults),
    solutions_print_helper(OtherResults),
    format("~d invariants~n", [NumResults]),
    ((NumResults #= NInvariants, !);
     (format("ERROR: expected ~d invariants~n", [NInvariants]), fail)).

%! test_task_lists(+TaskLists:task_list_list, -NInvariants:int) is semidet.
%
% Like gen_invariants/1, but it will report the number of invariant
% collections found in `NInvariants`. If `NInvariants` fails to unify,
% a helpful error message is output.
test_task_lists(TaskLists, NInvariants) :-
    findall(Pasts,
            (fused_invariants(TaskLists, Pasts, _)),
            Results),
    length(Results, NumResults),
    solutions_print_helper(Results),
    format("~d invariants~n", [NumResults]),
    ((NumResults #= NInvariants, !);
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
% @see fused_invariants/3
gen_invariants(TaskLists) :- test_task_lists(TaskLists, _).
