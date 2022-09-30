# Most of the code in this file has literally been taken over from "The Fuzzing Book"
# project. I applied some performance optimizations and use ISLa DerivationTree objects
# instead of the standard Fuzzing Book ParseTree structures to make use of caching
# and other optimizations such as iterative traversal.
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
import collections.abc
import random
import subprocess
from typing import Tuple, List, Any, Set, Callable, Optional, Iterable

from isla.helpers import RE_NONTERMINAL, is_nonterminal, nonterminals, is_valid_grammar
from isla.derivation_tree import DerivationTree
from isla.type_defs import Grammar

Expansion = str
Outcome = str


def all_terminals(tree: DerivationTree) -> str:
    return str(tree)


def expansion_key(
    symbol: str, expansion: Expansion | DerivationTree | Iterable[DerivationTree]
) -> str:
    """Convert (symbol, `expansion`) into a key "SYMBOL -> EXPRESSION".
    `expansion` can be an expansion string, a derivation tree, or a list of derivation trees."""

    if isinstance(expansion, DerivationTree):
        expansion = expansion.value
    elif not isinstance(expansion, str) and isinstance(
        expansion, collections.abc.Iterable
    ):
        # Iterable of derivation trees
        assert all(isinstance(elem, DerivationTree) for elem in expansion)
        expansion = "".join(map(lambda t: t.value, expansion))
    else:
        assert isinstance(expansion, str)

    return symbol + " -> " + expansion


class Runner:
    """Base class for testing inputs."""

    # Test outcomes
    PASS = "PASS"
    FAIL = "FAIL"
    UNRESOLVED = "UNRESOLVED"

    def __init__(self) -> None:
        """Initialize"""
        pass

    def run(self, inp: str) -> Any:
        """Run the runner with the given input"""
        return inp, Runner.UNRESOLVED


class PrintRunner(Runner):
    """Simple runner, printing the input."""

    def run(self, inp) -> Any:
        """Print the given input"""
        print(inp)
        return inp, Runner.UNRESOLVED


class Fuzzer:
    """Base class for fuzzers."""

    def __init__(self) -> None:
        pass

    def fuzz(self) -> str:
        """Return fuzz input"""
        return ""

    def run(
        self, runner: Runner = Runner()
    ) -> Tuple[subprocess.CompletedProcess, Outcome]:
        """Run `runner` with fuzz input"""
        return runner.run(self.fuzz())

    def runs(
        self, runner: Runner = PrintRunner(), trials: int = 10
    ) -> List[Tuple[subprocess.CompletedProcess, Outcome]]:
        """Run `runner` with fuzz input, `trials` times"""
        # Note: the list comprehension below does not invoke self.run() for subclasses
        # return [self.run(runner) for i in range(trials)]
        outcomes = []
        for i in range(trials):
            outcomes.append(self.run(runner))

        return outcomes


def exp_string(expansion: Expansion) -> str:
    """Return the string to be expanded"""
    if isinstance(expansion, str):
        return expansion
    return expansion[0]


class GrammarFuzzer(Fuzzer):
    """Produce strings from grammars efficiently, using derivation trees."""

    def __init__(
        self,
        grammar: Grammar,
        start_symbol: str = "<start>",
        min_nonterminals: int = 0,
        max_nonterminals: int = 10,
        disp: bool = False,
        log: bool | int = False,
    ) -> None:
        """Produce strings from `grammar`, starting with `start_symbol`.
        If `min_nonterminals` or `max_nonterminals` is given, use them as limits
        for the number of nonterminals produced.
        If `disp` is set, display the intermediate derivation trees.
        If `log` is set, show intermediate steps as text on standard output."""

        super().__init__()
        self.grammar = grammar
        self.start_symbol = start_symbol
        self.min_nonterminals = min_nonterminals
        self.max_nonterminals = max_nonterminals
        self.disp = disp
        self.log = log
        self.check_grammar()  # Invokes is_valid_grammar()

        self.derivation_tree: Optional[DerivationTree] = None

    def check_grammar(self) -> None:
        """Check the grammar passed"""
        assert self.start_symbol in self.grammar
        assert is_valid_grammar(self.grammar, _start_symbol=self.start_symbol)

    def init_tree(self) -> DerivationTree:
        return DerivationTree(self.start_symbol, None)

    def choose_node_expansion(
        self, node: DerivationTree, children_alternatives: List[List[DerivationTree]]
    ) -> int:
        """Return index of expansion in `children_alternatives` to be selected.
        'children_alternatives`: a list of possible children for `node`.
        Defaults to random. To be overloaded in subclasses."""
        return random.randrange(0, len(children_alternatives))

    def expansion_to_children(self, expansion: Expansion) -> List[DerivationTree]:
        expansion = exp_string(expansion)
        assert isinstance(expansion, str)

        if expansion == "":  # Special case: epsilon expansion
            return [DerivationTree("", [])]

        strings = RE_NONTERMINAL.split(expansion)
        return [
            DerivationTree(s, None) if is_nonterminal(s) else DerivationTree(s, [])
            for s in strings
            if len(s) > 0
        ]

    def possible_expansions(self, node: DerivationTree) -> int:
        if node.children is None:
            return 1

        return sum(self.possible_expansions(c) for c in node.children)

    def any_possible_expansions(self, node: DerivationTree) -> bool:
        return node.is_open()

    def symbol_cost(self, symbol: str, seen: Optional[Set[str]] = None) -> int | float:
        if seen is None:
            seen = set()

        expansions = self.grammar[symbol]
        return min(self.expansion_cost(e, seen | {symbol}) for e in expansions)

    def expansion_cost(
        self, expansion: Expansion, seen: Optional[Set[str]] = None
    ) -> int | float:
        if seen is None:
            seen = set()

        symbols = nonterminals(expansion)
        if len(symbols) == 0:
            return 1  # no symbol

        if any(s in seen for s in symbols):
            return float("inf")

        # the value of a expansion is the sum of all expandable variables
        return sum(self.symbol_cost(s, seen) for s in symbols) + 1

    def process_chosen_children(
        self, chosen_children: List[DerivationTree], expansion: Expansion
    ) -> List[DerivationTree]:
        """Process children after selection.  By default, does nothing."""
        return chosen_children

    def expand_node_by_cost(
        self, node: DerivationTree, choose: Callable = min
    ) -> DerivationTree:
        (symbol, children) = node
        assert children is None

        # Fetch the possible expansions from grammar...
        expansions = self.grammar[symbol]

        children_alternatives_with_cost = [
            (
                self.expansion_to_children(expansion),
                self.expansion_cost(expansion, {symbol}),
                expansion,
            )
            for expansion in expansions
        ]

        costs = [cost for (child, cost, expansion) in children_alternatives_with_cost]
        chosen_cost = choose(costs)
        children_with_chosen_cost = [
            child
            for (child, child_cost, _) in children_alternatives_with_cost
            if child_cost == chosen_cost
        ]
        expansion_with_chosen_cost = [
            expansion
            for (_, child_cost, expansion) in children_alternatives_with_cost
            if child_cost == chosen_cost
        ]

        index = self.choose_node_expansion(node, children_with_chosen_cost)

        chosen_children = children_with_chosen_cost[index]
        chosen_expansion = expansion_with_chosen_cost[index]
        chosen_children = self.process_chosen_children(
            chosen_children, chosen_expansion
        )

        # Return with a new list
        return DerivationTree(symbol, chosen_children)

    def expand_node_min_cost(self, node: DerivationTree) -> DerivationTree:
        if self.log:
            print("Expanding", all_terminals(node), "at minimum cost")

        return self.expand_node_by_cost(node, min)

    def expand_node_max_cost(self, node: DerivationTree) -> DerivationTree:
        if self.log:
            print("Expanding", all_terminals(node), "at maximum cost")

        return self.expand_node_by_cost(node, max)

    def expand_node(self, node: DerivationTree) -> DerivationTree:
        return self.expand_node_max_cost(node)

    def choose_tree_expansion(
        self, tree: DerivationTree, children: List[DerivationTree]
    ) -> int:
        """Return index of subtree in `children` to be selected for expansion.
        Defaults to random."""
        return random.randrange(0, len(children))

    def expand_tree_once(self, tree: DerivationTree) -> DerivationTree:
        """Choose an unexpanded symbol in tree; expand it.
        Can be overloaded in subclasses."""
        if tree.children is None:
            # Expand this node
            return self.expand_node(tree)

        # Find all children with possible expansions
        expandable_children = [
            c for c in tree.children if self.any_possible_expansions(c)
        ]

        # `index_map` translates an index in `expandable_children`
        # back into the original index in `children`
        index_map = [
            i for (i, c) in enumerate(tree.children) if c in expandable_children
        ]

        # Select a random child
        child_to_be_expanded = self.choose_tree_expansion(tree, expandable_children)

        return tree.replace_path(
            (index_map[child_to_be_expanded],),
            self.expand_tree_once(expandable_children[child_to_be_expanded]),
        )

    def log_tree(self, tree: DerivationTree) -> None:
        """Output a tree if self.log is set; if self.display is also set, show the tree structure"""
        if self.log:
            print("Tree:", all_terminals(tree))

    def expand_tree_with_strategy(
        self,
        tree: DerivationTree,
        expand_node_method: Callable,
        limit: Optional[int] = None,
    ):
        """Expand tree using `expand_node_method` as node expansion function
        until the number of possible expansions reaches `limit`."""
        self.expand_node = expand_node_method  # type: ignore
        while (
            limit is None or self.possible_expansions(tree) < limit
        ) and self.any_possible_expansions(tree):
            tree = self.expand_tree_once(tree)
            self.log_tree(tree)
        return tree

    def expand_node_randomly(self, node: DerivationTree) -> DerivationTree:
        """Choose a random expansion for `node` and return it"""
        assert node.children is None

        if self.log:
            print("Expanding", all_terminals(node), "randomly")

        # Fetch the possible expansions from grammar...
        expansions = self.grammar[node.value]
        children_alternatives: List[List[DerivationTree]] = [
            self.expansion_to_children(expansion) for expansion in expansions
        ]

        # ... and select a random expansion
        index = self.choose_node_expansion(node, children_alternatives)
        chosen_children = children_alternatives[index]

        # Process children (for subclasses)
        chosen_children = self.process_chosen_children(
            chosen_children, expansions[index]
        )

        # Return with new children
        return DerivationTree(node.value, chosen_children)

    def expand_tree(self, tree: DerivationTree) -> DerivationTree:
        """Expand `tree` in a three-phase strategy until all expansions are complete."""
        self.log_tree(tree)
        tree = self.expand_tree_with_strategy(
            tree, self.expand_node_max_cost, self.min_nonterminals
        )
        tree = self.expand_tree_with_strategy(
            tree, self.expand_node_randomly, self.max_nonterminals
        )
        tree = self.expand_tree_with_strategy(tree, self.expand_node_min_cost)

        assert self.possible_expansions(tree) == 0

        return tree

    def fuzz_tree(self) -> DerivationTree:
        """Produce a derivation tree from the grammar."""
        tree = self.init_tree()
        # print(tree)

        # Expand all nonterminals
        tree = self.expand_tree(tree)
        if self.log:
            print(repr(all_terminals(tree)))
        return tree

    def fuzz(self) -> str:
        """Produce a string from the grammar."""
        self.derivation_tree = self.fuzz_tree()
        return all_terminals(self.derivation_tree)


class GrammarCoverageFuzzer(GrammarFuzzer):
    """Track grammar coverage during production"""

    def __init__(self, *args, **kwargs) -> None:
        # invoke superclass __init__(), passing all arguments
        super().__init__(*args, **kwargs)
        self.covered_expansions: Set[str] = set()
        self._symbols_seen: Set[str] = set()

    def expansion_coverage(self) -> Set[str]:
        """Return the set of covered expansions as strings SYMBOL -> EXPANSION"""
        return self.covered_expansions

    def reset_coverage(self) -> None:
        """Clear coverage info tracked so far"""
        self.covered_expansions: Set[str] = set()

    def _max_expansion_coverage(self, symbol: str, max_depth: int | float) -> Set[str]:
        if max_depth <= 0:
            return set()

        self._symbols_seen.add(symbol)

        expansions = set()
        for expansion in self.grammar[symbol]:
            expansions.add(expansion_key(symbol, expansion))

            for nonterminal in nonterminals(expansion):
                if nonterminal not in self._symbols_seen:
                    expansions |= self._max_expansion_coverage(
                        nonterminal, max_depth - 1
                    )

        return expansions

    def max_expansion_coverage(
        self, symbol: Optional[str] = None, max_depth: int | float = float("inf")
    ) -> Set[str]:
        """Return set of all expansions in a grammar
        starting with `symbol` (default: start symbol).
        If `max_depth` is given, expand only to that depth."""
        if symbol is None:
            symbol = self.start_symbol

        self._symbols_seen: Set[str] = set()
        cov = self._max_expansion_coverage(symbol, max_depth)

        if symbol == "<start>":
            assert len(self._symbols_seen) == len(self.grammar)

        return cov

    def add_coverage(
        self, symbol: str, new_child: Expansion | Iterable[DerivationTree]
    ) -> None:
        key = expansion_key(symbol, new_child)

        if self.log and key not in self.covered_expansions:
            print("Now covered:", key)
        self.covered_expansions.add(key)

    def missing_expansion_coverage(self) -> Set[str]:
        """Return expansions not covered yet"""
        return self.max_expansion_coverage() - self.expansion_coverage()

    def choose_uncovered_node_expansion(
        self, node: DerivationTree, children_alternatives: List[List[DerivationTree]]
    ) -> int:
        return random.randrange(0, len(children_alternatives))

    def choose_covered_node_expansion(
        self, node: DerivationTree, children_alternatives: List[List[DerivationTree]]
    ) -> int:
        return random.randrange(0, len(children_alternatives))

    def new_coverages(
        self, node: DerivationTree, children_alternatives: List[List[DerivationTree]]
    ) -> Optional[List[Set[str]]]:
        """Return coverage to be obtained for each child at minimum depth"""

        (symbol, children) = node
        for max_depth in range(len(self.grammar)):
            new_coverages = [
                self.new_child_coverage(symbol, c, max_depth)
                for c in children_alternatives
            ]
            max_new_coverage = max(len(new_coverage) for new_coverage in new_coverages)
            if max_new_coverage > 0:
                # Uncovered node found
                return new_coverages

        # All covered
        return None

    def new_child_coverage(
        self,
        symbol: str,
        children: List[DerivationTree],
        max_depth: int | float = float("inf"),
    ) -> Set[str]:
        """Return new coverage that would be obtained
        by expanding (`symbol`, `children`)"""

        new_cov = self._new_child_coverage(children, max_depth)
        new_cov.add(expansion_key(symbol, children))
        new_cov -= self.expansion_coverage()  # -= is set subtraction
        return new_cov

    def _new_child_coverage(
        self, children: List[DerivationTree], max_depth: int | float
    ) -> Set[str]:
        new_cov: Set[str] = set()
        for (c_symbol, _) in children:
            if c_symbol in self.grammar:
                new_cov |= self.max_expansion_coverage(c_symbol, max_depth)

        return new_cov

    def choose_node_expansion(
        self, node: DerivationTree, children_alternatives: List[List[DerivationTree]]
    ) -> int:
        """Choose an expansion of `node` among `children_alternatives`.
        Return `n` such that expanding `children_alternatives[n]`
        yields the highest additional coverage."""

        (symbol, children) = node
        new_coverages = self.new_coverages(node, children_alternatives)

        if new_coverages is None:
            # All expansions covered - use superclass method
            return self.choose_covered_node_expansion(node, children_alternatives)

        max_new_coverage = max(len(cov) for cov in new_coverages)

        children_with_max_new_coverage = [
            c
            for (i, c) in enumerate(children_alternatives)
            if len(new_coverages[i]) == max_new_coverage
        ]
        index_map = [
            i
            for (i, c) in enumerate(children_alternatives)
            if len(new_coverages[i]) == max_new_coverage
        ]

        # Select a random expansion
        new_children_index = self.choose_uncovered_node_expansion(
            node, children_with_max_new_coverage
        )
        new_children = children_with_max_new_coverage[new_children_index]

        # Save the expansion as covered
        key = expansion_key(symbol, new_children)

        if self.log:
            print("Now covered:", key)
        self.covered_expansions.add(key)

        return index_map[new_children_index]
