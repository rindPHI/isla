:- use_module(library(yall)).
:- use_module(library(apply)).
:- use_module(library(clpfd)).

%%% findnsols_nobt/4:
findnsols_nobt(N, T, G, R) :- findnsols(N, T, G, R), !.

%%% equal/3
equal(X, Y, Result) :-
  [NT1, [[V1, []]]] = X,
  [NT2, [[V2, []]]] = Y,
  term_variables(V1, Vars1),
  term_variables(V2, Vars2),
  append([Vars1, Vars2], AllVars),
  ((((numeric_nonterminal(NT1), numeric_nonterminal(NT2)) ;
    (atomic_string_nonterminal(NT1), atomic_string_nonterminal(NT2))),
      var(V1), var(V2)
    ) ->
    ( % Constraints with CLP variables: Post CLP constraint
      (Result #= 1 -> V1 #= V2 ; V1 #\= V2), !
    );
    ( % At least one expression is already instantiated; label any remaining
      % variables and check standard term equality on unparsed tree.
      (AllVars \= [] -> 
        (sum(AllVars, #=, Sum),
          labeling([min(Sum)], AllVars));
          true),
      tree_to_string(X, Str1),
      tree_to_string(Y, Str2),
      ((Result #= 1, Str1 == Str2) ; (Result #= 0, Str1 \= Str2)))).

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

%%% product/2
product([], 1).
product([0|_], 0).
product([H|T], R) :- product(T, P), R #= H * P.

%%% eqsum/2
eqsum(L, R) :- sum(L, #=, R).

neg(F) :- F, !, fail.
neg(_).

% :- begin_tests(equal).
%test(equal) :- equal(['var', [[0, []]]], ['var', [[0, []]]], 1).
%test(equal) :- X in 0..10, equal(['var', [[X, []]]], ['var', [[X, []]]], 1).
%test(equal, all(X = [0, 1, 2])) :- X in 0..10, equal(['var', [[X, []]]], ['digit', [[X, []]]], 0).
%test(equal, [fail]) :- equal(['var', [[0, []]]], ['var', [[0, []]]], 0).
%test(equal) :- equal(['var', [[0, []]]], ['var', [[1, []]]], 0).
%test(equal) :- equal(['digit', [[0, []]]], ['digit', [[0, []]]], 1).
%test(equal) :- equal(['digit', [[0, []]]], ['digit', [[1, []]]], 0).
%test(equal) :- X #= 0, equal(['var', [[X, []]]], ['var', [[0, []]]], 1).
%test(equal) :- X #= 0, equal(['var', [[X, []]]], ['var', [["x", []]]], 1).
%test(equal) :- equal(['var', [[X, []]]], ['var', [[Y, []]]], 1), X #= Y.
%test(equal, [fail]) :- equal(['var', [[X, []]]], ['var', [[Y, []]]], 0), X #= Y.
%test(equal) :- equal(['var', [[X, []]]], ['var', [[Y, []]]], 0), X #\= Y.
%test(equal, [fail]) :- equal(['var', [[X, []]]], ['var', [[Y, []]]], 1), X #\= Y.
%test(equal, all(X = [0])) :- X in 0..10, equal(['var', [[X, []]]], ['var', [["x", []]]], 1).
%test(equal, all(X = [1, 2])) :- X in 0..10, equal(['var', [[X, []]]], ['var', [["x", []]]], 0).
% :- end_tests(equal).


