import random
from typing import Tuple, Callable

from grammar_graph import gg

from isla.derivation_tree import DerivationTree
from isla.existential_helpers import paths_between, path_to_tree
from isla.fuzzer import GrammarCoverageFuzzer
from isla.helpers import (
    Maybe,
    Exceptional,
    parent_or_child,
    canonical,
    to_id,
)
from isla.type_defs import Grammar, Path


class Mutator:
    def __init__(
        self, grammar: Grammar, min_mutations: int = 2, max_mutations: int = 5
    ):
        self.fuzzer = GrammarCoverageFuzzer(grammar)
        self.graph = gg.GrammarGraph.from_grammar(grammar)
        self.canonical_grammar = canonical(grammar)

        self.min_mutations = min_mutations
        self.max_mutations = max_mutations

    def __get_mutator(self) -> Callable[[DerivationTree], Maybe[DerivationTree]]:
        mutators = [
            self.replace_subtree_randomly,
            self.generalize_subtree,
            self.swap_subtrees,
        ]

        return random.choices(
            mutators,
            weights=[2**i for i in range(1, len(mutators) + 1)],
            k=1,
        )[0]

    def mutate(self, inp: DerivationTree) -> DerivationTree:
        target_num_mutations = random.randint(self.min_mutations, self.max_mutations)

        applied_mutations = 0

        def inc_applied_mutations(_):
            nonlocal applied_mutations
            applied_mutations += 1

        while applied_mutations < target_num_mutations:
            inp = (
                self.__get_mutator()(inp)
                .map(to_id(inc_applied_mutations))
                .orelse(lambda: inp)
                .get()
            )

        return inp

    def replace_subtree_randomly(self, inp: DerivationTree) -> Maybe[DerivationTree]:
        candidate_paths = [
            (path, subtree) for path, subtree in inp.paths() if subtree.children
        ]

        num_candidate_paths = len(candidate_paths)

        # Decrease weights for paths with many children: Prefer local mutations.
        path, subtree = random.choices(
            candidate_paths,
            weights=[
                1
                + num_candidate_paths
                - len(
                    [
                        other_path
                        for other_path, _ in candidate_paths
                        if path == other_path[: len(path)]
                    ]
                )
                for path, _ in candidate_paths
            ],
            k=1,
        )[0]

        return Maybe(
            self.fuzzer.expand_tree(
                inp.replace_path(path, DerivationTree(subtree.value))
            )
        )

    def swap_subtrees(self, inp: DerivationTree) -> Maybe[DerivationTree]:
        def process(
            path_tree_pair: Tuple[
                Tuple[Path, DerivationTree], Tuple[Path, DerivationTree]
            ]
        ) -> DerivationTree:
            (path_1, tree_1), (path_2, tree_2) = path_tree_pair
            return inp.replace_path(path_1, tree_2).replace_path(path_2, tree_1)

        return (
            Exceptional.of(
                lambda: random.choice(
                    [
                        ((path_1, tree_1), (path_2, tree_2))
                        for path_idx_1, (path_1, tree_1) in enumerate(inp.paths())
                        for path_idx_2, (path_2, tree_2) in enumerate(inp.paths())
                        if path_idx_1 < path_idx_2
                        and not parent_or_child(path_1, path_2)
                        and tree_1.value == tree_2.value
                    ]
                )
            )
            .map(process)
            .map(Maybe)
            .recover(lambda _: Maybe.nothing(), IndexError)
            .reraise()
            .get()
        )

    def generalize_subtree(self, inp: DerivationTree) -> Maybe[DerivationTree]:
        candidate_paths = [
            (path, tree)
            for path, tree in inp.paths()
            if tree.children and paths_between(self.graph, tree.value, tree.value)
        ]

        if not candidate_paths:
            return Maybe.nothing()

        path, tree = random.choice(candidate_paths)
        self_embedding_tree = random.choice(
            path_to_tree(
                self.canonical_grammar,
                random.choice(paths_between(self.graph, tree.value, tree.value)),
            )
        )

        matching_leaf = random.choice(
            [p for p, t in self_embedding_tree.leaves() if t.value == tree.value]
        )

        return Maybe(
            self.fuzzer.expand_tree(
                inp.replace_path(
                    path, self_embedding_tree.replace_path(matching_leaf, tree)
                )
            )
        )
