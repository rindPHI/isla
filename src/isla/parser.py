# Most of the code in this file has literally been taken over from "The Fuzzing Book"
# project; I only applied small changes and copied this here to get rid of the
# dependency to the "fuzzingbook" Python package.
#
#   - Dominic Steinhoefel

# "Fuzzing: Breaking Things with Random Inputs" - a chapter of "The Fuzzing Book"
# Web site: https://www.fuzzingbook.org/html/Fuzzer.html
# Last change: 2021-11-09 14:01:19+01:00
#
# Copyright (c) 2021 CISPA Helmholtz Center for Information Security
# Copyright (c) 2018-2020 Saarland University, authors, and contributors
#
# Permission is hereby granted, free of charge, to any person obtaining a
# copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:
#
# The above copyright notice and this permission notice shall be included
# in all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
# OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
# IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
# CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
# TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
# SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

import itertools
import random
from functools import lru_cache
from typing import Tuple, Iterable, Generator, List, Dict, Collection

from isla.helpers import tree_to_string, RE_NONTERMINAL
from isla.type_defs import Grammar, ParseTree, CanonicalGrammar

START_SYMBOL = "<start>"


def single_char_tokens(grammar: Grammar) -> Dict[str, List[List[Collection[str]]]]:
    g_ = {}
    for key in grammar:
        rules_ = []
        for rule in grammar[key]:
            rule_ = []
            for token in rule:
                if token in grammar:
                    rule_.append(token)
                else:
                    rule_.extend(token)
            rules_.append(rule_)
        g_[key] = rules_
    return g_


def canonical(grammar: Grammar) -> CanonicalGrammar:
    def split(expansion):
        return [token for token in RE_NONTERMINAL.split(expansion) if token]

    return {
        k: [split(expression) for expression in alternatives]
        for k, alternatives in grammar.items()
    }


def non_canonical(grammar):
    new_grammar = {}
    for k in grammar:
        rules = grammar[k]
        new_rules = []
        for rule in rules:
            new_rules.append("".join(rule))
        new_grammar[k] = new_rules
    return new_grammar


class Parser:
    """Base class for parsing."""

    def __init__(self, grammar, **kwargs):
        self._start_symbol = kwargs.get("start_symbol", START_SYMBOL)
        self.log = kwargs.get("log", False)
        self.tokens = kwargs.get("tokens", set())
        self.coalesce_tokens = kwargs.get("coalesce", True)
        canonical_grammar = kwargs.get("canonical", False)
        if canonical_grammar:
            self.cgrammar = single_char_tokens(grammar)
            self._grammar = non_canonical(grammar)
        else:
            self._grammar = dict(grammar)
            self.cgrammar = single_char_tokens(canonical(grammar))
        # we do not require a single rule for the start symbol
        if len(grammar.get(self._start_symbol, [])) != 1:
            self.cgrammar["<>"] = [[self._start_symbol]]

    def grammar(self) -> Grammar:
        """Return the grammar of this parser."""
        return self._grammar

    def start_symbol(self) -> str:
        """Return the start symbol of this parser."""
        return self._start_symbol

    def parse_prefix(self, text: str) -> Tuple[int, Iterable[ParseTree]]:
        """Return pair (cursor, forest) for longest prefix of text.
        To be defined in subclasses."""
        raise NotImplementedError()

    def parse(self, text: str) -> List[ParseTree]:
        """Parse `text` using the grammar.
        Return an iterable of parse trees."""
        cursor, forest = self.parse_prefix(text)
        if cursor < len(text):
            raise SyntaxError("at " + repr(text[cursor:]))
        return [self.prune_tree(tree) for tree in forest]

    def parse_on(self, text: str, start_symbol: str) -> Generator:
        old_start = self._start_symbol
        try:
            self._start_symbol = start_symbol
            yield from self.parse(text)
        finally:
            self._start_symbol = old_start

    def coalesce(self, children: List[ParseTree]) -> List[ParseTree]:
        last = ""
        new_lst: List[ParseTree] = []
        for cn, cc in children:
            if cn not in self._grammar:
                last += cn
            else:
                if last:
                    new_lst.append((last, []))
                    last = ""
                new_lst.append((cn, cc))
        if last:
            new_lst.append((last, []))
        return new_lst

    def prune_tree(self, tree):
        name, children = tree
        if name == "<>":
            assert len(children) == 1
            return self.prune_tree(children[0])
        if self.coalesce_tokens:
            children = self.coalesce(children)
        if name in self.tokens:
            return (name, [(tree_to_string(tree), [])])
        else:
            return (name, [self.prune_tree(c) for c in children])


class Column:
    def __init__(self, index, letter):
        self.index, self.letter = index, letter
        self.states, self._unique = [], {}

    def __str__(self):
        return "%s chart[%d]\n%s" % (
            self.letter,
            self.index,
            "\n".join(str(state) for state in self.states if state.finished()),
        )

    def add(self, state):
        if state in self._unique:
            return self._unique[state]
        self._unique[state] = state
        self.states.append(state)
        state.e_col = self
        return self._unique[state]


class Item:
    def __init__(self, name, expr, dot):
        self.name, self.expr, self.dot = name, expr, dot

    def finished(self):
        return self.dot >= len(self.expr)

    def advance(self):
        return Item(self.name, self.expr, self.dot + 1)

    def at_dot(self):
        return self.expr[self.dot] if self.dot < len(self.expr) else None


class State(Item):
    def __init__(self, name, expr, dot, s_col, e_col=None):
        super().__init__(name, expr, dot)
        self.s_col, self.e_col = s_col, e_col

    def __str__(self):
        def idx(var):
            return var.index if var else -1

        return (
            self.name
            + ":= "
            + " ".join(
                [str(p) for p in [*self.expr[: self.dot], "|", *self.expr[self.dot :]]]
            )
            + "(%d,%d)" % (idx(self.s_col), idx(self.e_col))
        )

    def copy(self):
        return State(self.name, self.expr, self.dot, self.s_col, self.e_col)

    def _t(self):
        return (self.name, self.expr, self.dot, self.s_col.index)

    def __hash__(self):
        return hash(self._t())

    def __eq__(self, other):
        return self._t() == other._t()

    def advance(self):
        return State(self.name, self.expr, self.dot + 1, self.s_col)


def fixpoint(f):
    def helper(arg):
        while True:
            sarg = str(arg)
            arg_ = f(arg)
            if str(arg_) == sarg:
                return arg
            arg = arg_

    return helper


def rules(grammar):
    return [(key, choice) for key, choices in grammar.items() for choice in choices]


def nullable_expr(expr, nullables):
    return all(token in nullables for token in expr)


EPSILON = ""


def nullable(grammar):
    productions = rules(grammar)

    @fixpoint
    def nullable_(nullables):
        for A, expr in productions:
            if nullable_expr(expr, nullables):
                nullables |= {A}
        return nullables

    return nullable_({EPSILON})


class EarleyParser(Parser):
    def __init__(self, grammar, **kwargs):
        super().__init__(grammar, **kwargs)
        self.epsilon = nullable(self.cgrammar)

    def chart_parse(self, words, start):
        alt = tuple(*self.cgrammar[start])
        chart = [Column(i, tok) for i, tok in enumerate([None, *words])]
        chart[0].add(State(start, alt, 0, chart[0]))
        return self.fill_chart(chart)

    def scan(self, col, state, letter):
        if letter == col.letter:
            col.add(state.advance())

    def complete(self, col, state):
        return self.earley_complete(col, state)

    def earley_complete(self, col, state):
        parent_states = [st for st in state.s_col.states if st.at_dot() == state.name]
        for st in parent_states:
            col.add(st.advance())

    def fill_chart(self, chart):
        for i, col in enumerate(chart):
            for state in col.states:
                if state.finished():
                    self.complete(col, state)
                else:
                    sym = state.at_dot()
                    if sym in self.cgrammar:
                        self.predict(col, sym, state)
                    else:
                        if i + 1 >= len(chart):
                            continue
                        self.scan(chart[i + 1], state, sym)
            if self.log:
                print(col, "\n")
        return chart

    def parse_prefix(self, text):
        self.table = self.chart_parse(text, self.start_symbol())
        for col in reversed(self.table):
            states = [st for st in col.states if st.name == self.start_symbol()]
            if states:
                return col.index, states
        return -1, []

    def parse(self, text) -> Generator:
        cursor, states = self.parse_prefix(text)
        start = next((s for s in states if s.finished()), None)

        if cursor < len(text) or not start:
            raise SyntaxError("at " + repr(text[cursor:]))

        forest = self.parse_forest(self.table, start)
        for tree in self.extract_trees(forest):
            yield self.prune_tree(tree)

    def parse_paths(self, named_expr, chart, frm, til):
        def paths(state, start, k, e):
            if not e:
                return [[(state, k)]] if start == frm else []
            else:
                return [
                    [(state, k)] + r for r in self.parse_paths(e, chart, frm, start)
                ]

        *expr, var = named_expr
        if var not in self.cgrammar:
            starts = (
                [(var, til - len(var), "t")]
                if til > 0 and chart[til].letter == var
                else []
            )
        else:
            starts = [
                (s, s.s_col.index, "n")
                for s in chart[til].states
                if s.finished() and s.name == var
            ]

        return [p for s, start, k in starts for p in paths(s, start, k, expr)]

    def forest(self, s, kind, chart):
        return self.parse_forest(chart, s) if kind == "n" else (s, [])

    def parse_forest(self, chart, state):
        pathexprs = (
            self.parse_paths(state.expr, chart, state.s_col.index, state.e_col.index)
            if state.expr
            else []
        )
        return state.name, [
            [(v, k, chart) for v, k in reversed(pathexpr)] for pathexpr in pathexprs
        ]

    def extract_a_tree(self, forest_node):
        name, paths = forest_node
        if not paths:
            return name, []
        return name, [self.extract_a_tree(self.forest(*p)) for p in paths[0]]

    def extract_trees(self, forest_node):
        name, paths = forest_node
        if not paths:
            yield (name, [])

        for path in paths:
            ptrees = [self.extract_trees(self.forest(*p)) for p in path]
            for p in itertools.product(*ptrees):
                yield (name, p)

    def predict(self, col, sym, state):
        for alt in self.cgrammar[sym]:
            col.add(State(sym, tuple(alt), 0, col))
        if sym in self.epsilon:
            col.add(state.advance())


class SimpleExtractor:
    def __init__(self, parser, text):
        self.parser = parser
        cursor, states = parser.parse_prefix(text)
        start = next((s for s in states if s.finished()), None)
        if cursor < len(text) or not start:
            raise SyntaxError("at " + repr(cursor))
        self.my_forest = parser.parse_forest(parser.table, start)

    def extract_a_node(self, forest_node):
        name, paths = forest_node
        if not paths:
            return ((name, 0, 1), []), (name, [])
        cur_path, i, length = self.choose_path(paths)
        child_nodes = []
        pos_nodes = []
        for s, kind, chart in cur_path:
            f = self.parser.forest(s, kind, chart)
            postree, ntree = self.extract_a_node(f)
            child_nodes.append(ntree)
            pos_nodes.append(postree)

        return ((name, i, length), pos_nodes), (name, child_nodes)

    def choose_path(self, arr):
        length = len(arr)
        i = random.randrange(length)
        return arr[i], i, length

    def extract_a_tree(self):
        pos_tree, parse_tree = self.extract_a_node(self.my_forest)
        return self.parser.prune_tree(parse_tree)


class ChoiceNode:
    def __init__(self, parent, total):
        self._p, self._chosen = parent, 0
        self._total, self.next = total, None

    def chosen(self):
        assert not self.finished()
        return self._chosen

    def __str__(self):
        return "%d(%s/%s %s)" % (
            self._i,
            str(self._chosen),
            str(self._total),
            str(self.next),
        )

    def __repr__(self):
        return repr((self._i, self._chosen, self._total))

    def increment(self):
        # as soon as we increment, next becomes invalid
        self.next = None
        self._chosen += 1
        if self.finished():
            if self._p is None:
                return None
            return self._p.increment()
        return self

    def finished(self):
        return self._chosen >= self._total


class EnhancedExtractor(SimpleExtractor):
    def __init__(self, parser, text):
        super().__init__(parser, text)
        self.choices = ChoiceNode(None, 1)

    def choose_path(self, arr, choices):
        arr_len = len(arr)
        if choices.next is not None:
            if choices.next.finished():
                return None, None, None, choices.next
        else:
            choices.next = ChoiceNode(choices, arr_len)
        next_choice = choices.next.chosen()
        choices = choices.next
        return arr[next_choice], next_choice, arr_len, choices

    def extract_a_node(self, forest_node, seen, choices):
        name, paths = forest_node
        if not paths:
            return (name, []), choices

        cur_path, _i, _l, new_choices = self.choose_path(paths, choices)
        if cur_path is None:
            return None, new_choices
        child_nodes = []
        for s, kind, chart in cur_path:
            if kind == "t":
                child_nodes.append((s, []))
                continue
            nid = (s.name, s.s_col.index, s.e_col.index)
            if nid in seen:
                return None, new_choices
            f = self.parser.forest(s, kind, chart)
            ntree, newer_choices = self.extract_a_node(f, seen | {nid}, new_choices)
            if ntree is None:
                return None, newer_choices
            child_nodes.append(ntree)
            new_choices = newer_choices
        return (name, child_nodes), new_choices

    def extract_a_tree(self):
        while not self.choices.finished():
            parse_tree, choices = self.extract_a_node(
                self.my_forest, set(), self.choices
            )
            choices.increment()
            if parse_tree is not None:
                return self.parser.prune_tree(parse_tree)
        return None


class PEGParser(Parser):
    def parse_prefix(self, text):
        cursor, tree = self.unify_key(self.start_symbol(), text, 0)
        return cursor, [tree]

    def unify_rule(self, rule, text, at):
        if self.log:
            print("unify_rule: %s with %s" % (repr(rule), repr(text[at:])))
        results = []
        for token in rule:
            at, res = self.unify_key(token, text, at)
            if res is None:
                return at, None
            results.append(res)
        return at, results

    @lru_cache(maxsize=None)
    def unify_key(self, key, text, at=0):
        if key not in self.cgrammar:
            if text[at:].startswith(key):
                return at + len(key), (key, [])
            else:
                return at, None
        for rule in self.cgrammar[key]:
            to, res = self.unify_rule(rule, text, at)
            if res is not None:
                return (to, (key, res))
        return 0, None
