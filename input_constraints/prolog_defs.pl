:- use_module(library(yall)).
:- use_module(library(apply)).
:- use_module(library(clpfd)).

%%% all/2
all([], 1).
all([0|_], 0).
all([1|T], R) :- all(T, 1) -> R #= 1 ; R #= 0.

%%% any/2
any([], 0).
any([1|_], 1).
any([0|T], R) :- any(T, 1) -> R #= 1 ; R #= 0.

%%% paths/2
paths(T, R) :- phrase(paths_dcg(T, []), R).

%%% paths_dcg/4.
paths_dcg([], _) --> [].

paths_dcg([Child|Tail], Path) -->
  {is_list(Child)},
  !,
  {last(Path, Last)},
  {NextChildPos #= Last + 1},
  {length(Path, Len)},
  {Len0 #= Len - 1},
  {list_replace(Len0, NextChildPos, Path, NextPath)},
  paths_dcg(Child, Path),
  paths_dcg(Tail, NextPath).

paths_dcg([Node, Children], Path) -->
  {neg(is_list(Node))},
  !,
  {append(Path, [0], NewPath)},
  [Path],
  paths_dcg(Children, NewPath).

%%% subtree_matches/3
subtree_matches(Tree, Path, Needle) :-
  get_subtree(Tree, Path, Subtree),
  [N1, _] = Needle,
  [N2, _] = Subtree,
  (atom(N1) -> (atom(N2) -> N1 == N2 ; fail) ;
  subsumes_term(Needle, Subtree)).

%%% find_subtrees/3
find_subtrees(Tree, Needle, Result) :-
  paths(Tree, Paths),
  include({Tree, Needle}/[Path]>>subtree_matches(Tree, Path, Needle), Paths, Result).

%%% find_subtrees_before/4
find_subtrees_before(Tree, Needle, BeforePath, Result) :-
  find_subtrees(Tree, Needle, Paths),
  include({BeforePath}/[Path]>>path_is_before(Path, BeforePath), Paths, Result).

%%% path_is_before/2
path_is_before([H1|T1], [H2|T2]) :- H1 #= H2 -> path_is_before(T1, T2) ; H1 #< H2.

%%% depth/2
depth([_, []], 1).
depth([_, C], Result) :-
  maplist(depth, C, ChildrenDepths),
  max_list(ChildrenDepths, CDepth),
  Result #= 1 + CDepth.

%%% list_replace/4
list_replace(_, _, [], []).
list_replace(Idx, Repl, [H|Tl1], [H|Tl2]) :-
  Idx \= 0,
  !,
  NewIdx #= Idx - 1,
  list_replace(NewIdx, Repl, Tl1, Tl2).
list_replace(0, Repl, [_|Tl], [Repl|Tl]).

%%% get_subtree/3
get_subtree([_, Children], [Head|Tail], Res) :-
  nth0(Head, Children, Child), !, get_subtree(Child, Tail, Res).
get_subtree(T, [], T).

%%% tcontains/2
tcontains(T, T).
tcontains(T, [T|_]).
tcontains(T, [C|_]) :- tcontains(T, C).
tcontains(T, [_|CS]) :- tcontains(T, CS).

%%% Stubs. Ensures tests can be run.
numeric_nonterminal('digit').
atomic_string_nonterminal('var').
fuzz('var', 0, "x").
fuzz('var', 1, "y").
fuzz('var', 2, "z").

%%% tree_to_string/2
tree_to_string([X, []], X) :- string(X), !.

tree_to_string([X, [[Y, []]]], S) :-
  atom(X),
  !,
  (numeric_nonterminal(X) ->
    number_string(Y, S) ;
    (atomic_string_nonterminal(X) ->
      fuzz(X, Y, S) ;
      S = Y
    )
  ).

tree_to_string([A, X], Y) :- atom(A), maplist(tree_to_string, X, Z), !, concat(Z, Y).

%%% concat/2
concat([], "").
concat([X|L], Z) :- concat(L, Y), !, string_concat(X, Y, Z).

:- begin_tests(helpers).
test(tree_to_string) :- tree_to_string(['var', [[0, []]]], "x").
test(tree_to_string) :- tree_to_string(['stmt', [['assgn', [['var', [[0, []]]], [" := ", []], ['assgn', [['var', [[0, []]]]]]]]]], "x := x").

test(get_subtree) :- get_subtree([var, [["y", []]]], [], [var, [["y", []]]]).
test(get_subtree) :- get_subtree([assgn, [[var, [["y", []]]], [" := ", []], [rhs, [[var, [["y", []]]]]]]], [0], [var, [["y", []]]]).

test(path_is_before) :- path_is_before([1, 0], [1, 1]).
test(path_is_before) :- path_is_before([1, 1, 0], [1, 2]).
test(path_is_before) :- path_is_before([1, 2, 0], [1, 3, 0, 0, 9]).

test(path_is_before, [fail]) :- path_is_before([1], [1, 0]).
test(path_is_before, [fail]) :- path_is_before([1, 2, 0], [1, 2]).
test(path_is_before, [fail]) :- path_is_before([1, 3], [1, 2]).

test(list_replace) :- list_replace(0, 1, [0], [1]).
test(list_replace) :- list_replace(1, 1, [0,0], [0,1]).

test(all) :- all([1], 1).
test(all, [fail]) :- all([1], 0).
test(all) :- all([], 1).
test(all, [fail]) :- all([], 0).
test(all) :- all([0], 0).
test(all, [fail]) :- all([0], 1).
test(all) :- all([1, 0, 1], 0).
test(all, [fail]) :- all([1, 0, 1], 1).
test(all) :- all([1, 1, 1], 1).
test(all, [fail]) :- all([1, 1, 1], 0).
:- end_tests(helpers).


neg(F) :- F, !, fail.
neg(_).
