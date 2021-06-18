:- module(test_stubs, [numeric_nonterminal/1, atomic_string_nonterminal/1, fuzz/3]).

numeric_nonterminal('digit').
atomic_string_nonterminal('var').
fuzz('var', 0, "x").
fuzz('var', 1, "y").
fuzz('var', 2, "z").

