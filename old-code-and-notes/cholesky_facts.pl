:- use_module(library(clpfd)).

% A general process for generating these constraints could look like this:
% - Conjure up a variable per state appearing in the PME
% - Constrain them all to be booleans
% - The list of states that are operation task outputs are passed to the sum()s
% - O in the invariant implies that all inputs to O and their in-memory predecessors
%   (counting only those that are outputs of a task) are computed in the invariant
% - If a task creating O is in the remainder, all successors to inputs to the task
%    must be in the remainder (here we consider strict successors only)
% - Noops get an if and only if on the invariant condition
% - any is handled with ors
%
% The fusion conditions can be built up into similar constraints

% 1 = In Invariant, 0 = In Remainder
% The labelling call preforms the search, taking into account domains
chol(TildeTl, TildeBl, Br0, TildeBr) :-
    Vars = [TildeTl, TildeBl, Br0, TildeBr],
    Vars ins 0..1,

    sum([TildeTl, TildeBr], #\=, 0),
    sum([TildeTl, TildeBr], #\=, 2),

    (TildeBr #= 1) #==> (Br0 #= 1),
    (Br0 #= 1) #==> (TildeBl #= 1),
    (Br0 #= 0) #==> (TildeBr #= 0),
    (TildeBl #= 1) #==> (TildeTl #= 1),

    labeling([ffc], Vars).
