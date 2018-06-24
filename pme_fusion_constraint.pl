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
operand_region(hat(X), X).
operand_region(during(X, _), X).
operand_region(during(X, _, _), X).
operand_region(tilde(X), X).

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

extract_operands(Term, Acc, Out) :-
    operand(Term) -> ord_add_element(Acc, Term, Out);
    is_list(Term) -> foldl(extract_operands, Term, Acc, Out);
    compound(Term) -> (compound_name_arguments(Term, _, Args),
                       foldl(extract_operands, Args, Acc, Out));
    Out = Acc.

extract_operands(Term, Out) :- extract_operands(Term, [], Out).

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

preceeds(any(States1), any(States2)) :- !, exists_one(preceeds, States1, States2).
preceeds(any(States), Y) :- exists_one(preceeds_flip(Y), States).
preceeds(X, any(States)) :- exists_one(preceeds(X), States).

must_be_in_past_on_past_input(Input, Input) :- !.
must_be_in_past_on_past_input(State, Input) :- preceeds(State, Input).

must_be_in_future_on_future_input(State, Input) :- preceeds(Input, State).

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
% - any()
% - comes_from
% - Pure inputs
% - Fusion
tasks_to_indicators(Tasks, Indicators, StateSet) :-
    out_states_of(Tasks, StateSet),
    maplist(indicator_pair, StateSet, Entries),
    ord_list_to_assoc(Entries, Indicators).

add_past_constraints(Indicators, OutTaskVar, OtherState, InState) :-
    (must_be_in_past_on_past_input(OtherState, InState),
     get_assoc(OtherState, Indicators, OtherVar)) ->
        (format("  Constraining for ~w because of ~w~n", [OtherState, InState]),
         (OutTaskVar #= 1) #==> (OtherVar #= 1)); true.

add_past_constraints(Indicators, StateSet, Task) :-
    task_split(Task, Inputs, Output),
    get_assoc(Output, Indicators, OutVar),
    format("Constraining past for ~w~n", [Output]),
    maplist2(add_past_constraints(Indicators, OutVar), StateSet, Inputs).

add_future_constraints(Indicators, OutTaskVar, OtherState, InState) :-
    (must_be_in_future_on_future_input(OtherState, InState),
     get_assoc(OtherState, Indicators, OtherVar)) ->
        (format("  Constraining for ~w because of ~w~n", [OtherState, InState]),
         (OutTaskVar #= 0) #==> (OtherVar #= 0)); true.

add_future_constraints(Indicators, StateSet, Task) :-
    task_split(Task, Inputs, Output),
    get_assoc(Output, Indicators, OutVar),
    format("Constraining future for ~w~n", [Output]),
    maplist2(add_future_constraints(Indicators, OutVar), StateSet, Inputs).

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

placed_in_past(Indicators, Task) :-
    task_output(Task, State),
    get_assoc(State, Indicators, Var),
    Var =:= 1.

loop_invariants(Tasks, Past, Future) :-
    tasks_to_indicators(Tasks, Indicators, StateSet),
    maplist(add_past_constraints(Indicators, StateSet), Tasks),
    maplist(add_future_constraints(Indicators, StateSet), Tasks),
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
