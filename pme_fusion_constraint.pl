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

maplist2(Pred, L1, L2) :-
    maplist2_(L1, L2, Pred).

maplist2_([], _, _).
maplist2_([H|T], L2, Pred) :-
    maplist(call(Pred, H), L2),
    maplist2_(T, L2, Pred).

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

states_regions_set([], Acc, Out) :- Acc = Out.
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

extract_states(Term, Acc, Out) :-
    state(Term) -> ord_add_element(Acc, Term, Out);
    is_list(Term) -> foldl(extract_states, Term, Acc, Out);
    compound(Term) -> (compound_name_arguments(Term, _, Args),
                       foldl(extract_states, Args, Acc, Out));
    Out = Acc.

extract_states(Term, Out) :- extract_states(Term, [], Out).

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

indicator_pair(OutState, OutIndicatorPair) :-
    Var in 0..1,
    OutIndicatorPair = OutState-Var.

% TODO:
% - Pure inputs
% - Fusion
tasks_to_indicators(Tasks, Indicators, StateSet) :-
    out_states_of(Tasks, StateSet),
    maplist(indicator_pair, StateSet, Entries),
    ord_list_to_assoc(Entries, Indicators).

states_needed_for_past_input(StateSet, InState, List) :-
    include(required_for_past_input_flip(InState), StateSet, List).

states_needed_for_future_input(StateSet, InState, List) :-
    include(required_for_future_input_flip(InState), StateSet, List).

build_base_dep_constraint_(_Type, _Indicators, [], 1).
build_base_dep_constraint_(Type, Indicators, [State], Constraint) :-
    get_assoc(State, Indicators, Var),
    Constraint = (Var #= Type).

build_base_dep_constraint_(Type, Indicators, [State|[Next|Tail]], Constraint) :-
    get_assoc(State, Indicators, Var),
    build_base_dep_constraint_(Type, Indicators, [Next|Tail], SubConstr),
    Constraint = ((Var #= Type) #/\ SubConstr).

build_base_dep_constraint(1, Indicators, StateSet, Input, Constraint) :-
    states_needed_for_past_input(StateSet, Input, RelevantStates),
    build_base_dep_constraint_(1, Indicators, RelevantStates, Constraint).

build_base_dep_constraint(0, Indicators, StateSet, Input, Constraint) :-
    states_needed_for_future_input(StateSet, Input, RelevantStates),
    build_base_dep_constraint_(0, Indicators, RelevantStates, Constraint).

build_any_dep_constraint(Type, Indicators, StateSet, [Input], Constraint) :-
    % Yes, this preserves 1s, that's intentional
    build_base_dep_constraint(Type, Indicators, StateSet, Input, Constraint).

build_any_dep_constraint(Type, Indicators, StateSet, [Input|[Next|Inputs]], Constraint) :-
    build_any_dep_constraint(Type, Indicators, StateSet, [Next|Inputs], SubConstraint),
    build_base_dep_constraint(Type, Indicators, StateSet, Input, NewConstraint),
    Constraint = (NewConstraint #\/ SubConstraint).

add_dep_constraint(_Type, _Indicators, _OutTaskVar, _StateSet, any([])) :-
    format("ERROR: Empty any input~n"), fail.
add_dep_constraint(Type, Indicators, OutTaskVar, StateSet, any([State])) :-
    add_dep_constraint(Type, Indicators, OutTaskVar, StateSet, State).
add_dep_constraint(Type, Indicators, OutTaskVar, StateSet, any([State|[Next|Rest]])) :-
    build_any_dep_constraint(Type, Indicators, StateSet, [State|[Next|Rest]], Constraint),
    (OutTaskVar #= Type) #==> Constraint.

add_dep_constraint(Type, Indicators, OutTaskVar, StateSet, InState) :- base_state(InState),
    build_base_dep_constraint(Type, Indicators, StateSet, InState, Constraint),
    ((Constraint \== 1) -> ((OutTaskVar #= Type) #==> Constraint); true).

add_past_dep_constraints(Indicators, StateSet, Task) :-
    task_split(Task, Inputs, Output),
    get_assoc(Output, Indicators, OutVar),
    maplist(add_dep_constraint(1, Indicators, OutVar, StateSet), Inputs).

add_future_dep_constraints(Indicators, StateSet, Task) :-
    task_split(Task, Inputs, Output),
    get_assoc(Output, Indicators, OutVar),
    maplist(add_dep_constraint(0, Indicators, OutVar, StateSet), Inputs).

gather_operation_task_vars(_, [], Acc, Out) :- Out = Acc.
gather_operation_task_vars(Indicators, [op_eq(Reg, _)|Tasks], Acc, Out) :- !,
    get_assoc(Reg, Indicators, Var),
    gather_operation_task_vars(Indicators, Tasks, [Var|Acc], Out).
gather_operation_task_vars(Indicators, [_|Tasks], Acc, Out) :-
    gather_operation_task_vars(Indicators, Tasks, Acc, Out).

gather_operation_task_vars(Indicators, Tasks, Vars) :-
    gather_operation_task_vars(Indicators, Tasks, [], Vars).

add_loop_progress_constraints(Indicators, Tasks) :-
    gather_operation_task_vars(Indicators, Tasks, Vars),
    length(Vars, NOps),
    sum(Vars, #\=, 0),
    sum(Vars, #\=, NOps).

build_comes_from_constraint_lhs(_Indicators, [], 1).
build_comes_from_constraint_lhs(Indicators, [Input], Constraint) :-
    get_assoc(Input, Indicators, Var),
    Constraint = (Var #= 1).
build_comes_from_constraint_lhs(Indicators, [Input|[Next|Rest]], Constraint) :-
    get_assoc(Input, Indicators, Var),
    build_comes_from_constraint_lhs(Indicators, [Next|Rest], SubConstr),
    Constraint = ((Var #= 1) #/\ SubConstr).

add_comes_from_constraint(Indicators, StateSet, comes_from(Out, Expr)) :- !,
    get_assoc(Out, Indicators, OutVar),
    extract_states(Expr, InputSet),
    ord_intersection(StateSet, InputSet, RelevantInputs),
    build_comes_from_constraint_lhs(Indicators, RelevantInputs, Constraint),
    Constraint #==> (OutVar #= 1).
add_comes_from_constraint(_, _, _).

placed_in_past(Indicators, Task) :-
    task_output(Task, State),
    get_assoc(State, Indicators, Var),
    Var =:= 1.

loop_invariants(Tasks, Past, Future) :-
    tasks_to_indicators(Tasks, Indicators, StateSet),
    maplist(add_past_dep_constraints(Indicators, StateSet), Tasks),
    maplist(add_future_dep_constraints(Indicators, StateSet), Tasks),
    maplist(add_comes_from_constraint(Indicators, StateSet), Tasks),
    add_loop_progress_constraints(Indicators, Tasks),
    assoc_to_values(Indicators, AllVars),
    labeling([ffc], AllVars),
    partition(placed_in_past(Indicators), Tasks, Past, Future).

cholesky(Past, Future) :-
    loop_invariants(
        [op_eq(tilde(l_tl), chol(hat(l_tl))),

         eq(tilde(l_bl), trsm(tilde(l_tl), hat(l_bl))),

         eq(during(l_br, 0), sub(hat(l_br), mul(tilde(l_bl), tr(tilde(l_bl))))),
         op_eq(tilde(l_br), chol(during(l_br, 0)))
        ], Past, Future).

:- consult(examples/common_task_lists).

trinv(Past, Future) :-
    trinv_tasks(ltl,      ltl,
                lbl, lbr, lbl, lbr, Tasks),
    loop_invariants(Tasks, Past, Future).
