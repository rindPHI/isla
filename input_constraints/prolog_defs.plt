:- begin_tests(equal).
:- include(prolog_defs).
:- use_module(test_stubs).

test(equal) :- equal(['var', [[0, []]]], ['var', [[0, []]]], 1).
test(equal) :- X in 0..10, equal(['var', [[X, []]]], ['var', [[X, []]]], 1).
test(equal, all(X = [0, 1, 2])) :- X in 0..10, equal(['var', [[X, []]]], ['digit', [[X, []]]], 0).
test(equal, [fail]) :- equal(['var', [[0, []]]], ['var', [[0, []]]], 0).
test(equal) :- equal(['var', [[0, []]]], ['var', [[1, []]]], 0).
test(equal) :- equal(['digit', [[0, []]]], ['digit', [[0, []]]], 1).
test(equal) :- equal(['digit', [[0, []]]], ['digit', [[1, []]]], 0).
test(equal) :- X #= 0, equal(['var', [[X, []]]], ['var', [[0, []]]], 1).
test(equal) :- X #= 0, equal(['var', [[X, []]]], ['var', [["x", []]]], 1).
test(equal) :- equal(['var', [[X, []]]], ['var', [[Y, []]]], 1), X #= Y.
test(equal, [fail]) :- equal(['var', [[X, []]]], ['var', [[Y, []]]], 0), X #= Y.
test(equal) :- equal(['var', [[X, []]]], ['var', [[Y, []]]], 0), X #\= Y.
test(equal, [fail]) :- equal(['var', [[X, []]]], ['var', [[Y, []]]], 1), X #\= Y.
test(equal, all(X = [0])) :- X in 0..10, equal(['var', [[X, []]]], ['var', [["x", []]]], 1).
test(equal, all(X = [1, 2])) :- X in 0..10, equal(['var', [[X, []]]], ['var', [["x", []]]], 0).
:- end_tests(equal).

:- begin_tests(helpers).
:- include(prolog_defs).
:- use_module(test_stubs).

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
