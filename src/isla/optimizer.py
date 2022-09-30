# Copyright © 2022 CISPA Helmholtz Center for Information Security.
# Author: Dominic Steinhöfel.
#
# This file is part of ISLa.
#
# ISLa is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# ISLa is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with ISLa.  If not, see <http://www.gnu.org/licenses/>.

import copy
import datetime
import os

import math
import multiprocessing as mp
import random
import subprocess
import sys
from textwrap import wrap
from typing import Callable, List, Tuple, Optional, Union, Generator, Dict, Set

import matplotlib
from grammar_graph import gg
from matplotlib import pyplot as plt, ticker as mtick
from pathos import multiprocessing as pmp

import isla.derivation_tree
import isla.evaluator
from isla import language, solver
from isla.performance_evaluator import logger, generate_inputs
from isla.helpers import weighted_geometric_mean
from isla.solver import (
    CostWeightVector,
    ISLaSolver,
    CostSettings,
    GrammarBasedBlackboxCostComputer,
)
from isla.type_defs import Grammar


class PerformanceEvaluationResult:
    def __init__(
        self,
        accumulated_valid_inputs: Dict[float, int],
        accumulated_invalid_inputs: Dict[float, int],
        accumulated_k_path_coverage: Dict[float, int],
        accumulated_non_vacuous_index: Dict[float, float],
    ):
        self.accumulated_valid_inputs = accumulated_valid_inputs
        self.accumulated_invalid_inputs = accumulated_invalid_inputs
        self.accumulated_k_path_coverage = accumulated_k_path_coverage
        self.accumulated_non_vacuous_index = accumulated_non_vacuous_index

        self.max_time = max(
            [
                (
                    0.0
                    if not accumulated_valid_inputs
                    else list(accumulated_valid_inputs.keys())[-1]
                ),
                (
                    0.0
                    if not accumulated_invalid_inputs
                    else list(accumulated_invalid_inputs.keys())[-1]
                ),
            ]
        )

        if (
            accumulated_valid_inputs
            and accumulated_k_path_coverage
            and accumulated_non_vacuous_index
        ):
            self.final_product_value: float = self.single_product_value(
                max(accumulated_valid_inputs.keys())
            )
        else:
            self.final_product_value = -1

    def save_to_csv_file(self, dir: str, base_file_name: str):
        valid_input_file = os.path.join(dir, base_file_name + "_valid_inputs.csv")
        with open(valid_input_file, "w") as f:
            f.write(
                "\n".join(f"{t};{r}" for t, r in self.accumulated_valid_inputs.items())
            )
            print(f"Written valid input data to {valid_input_file}")

        invalid_input_file = os.path.join(dir, base_file_name + "_invalid_inputs.csv")
        with open(invalid_input_file, "w") as f:
            f.write(
                "\n".join(
                    f"{t};{r}" for t, r in self.accumulated_invalid_inputs.items()
                )
            )
            print(f"Written invalid input data to {invalid_input_file}")

        k_path_file = os.path.join(dir, base_file_name + "_k_paths.csv")
        with open(k_path_file, "w") as f:
            f.write(
                "\n".join(
                    f"{t};{r}" for t, r in self.accumulated_k_path_coverage.items()
                )
            )
            print(f"Written accumulated k-path data {k_path_file}")

        non_vacuous_file = os.path.join(dir, base_file_name + "_non_vacuous_index.csv")
        with open(non_vacuous_file, "w") as f:
            f.write(
                "\n".join(f"{t};{r}" for t, r in self.accumulated_valid_inputs.items())
            )
            print(f"Written non-vacuous index data to {k_path_file}")

    @staticmethod
    def load_from_csv_file(
        dir: str, base_file_name: str
    ) -> "PerformanceEvaluationResult":
        valid_input_file = os.path.join(dir, base_file_name + "_valid_inputs.csv")
        with open(valid_input_file, "r") as f:
            accumulated_valid_inputs = dict(
                [
                    (float(line.split(";")[0]), int(line.split(";")[1]))
                    for line in f.read().split("\n")
                    if line
                ]
            )

        invalid_input_file = os.path.join(dir, base_file_name + "_invalid_inputs.csv")
        with open(invalid_input_file, "r") as f:
            accumulated_invalid_inputs = dict(
                [
                    (float(line.split(";")[0]), int(line.split(";")[1]))
                    for line in f.read().split("\n")
                    if line
                ]
            )

        k_path_file = os.path.join(dir, base_file_name + "_k_paths.csv")
        with open(k_path_file, "r") as f:
            accumulated_k_path_coverage = dict(
                [
                    (float(line.split(";")[0]), int(line.split(";")[1]))
                    for line in f.read().split("\n")
                    if line
                ]
            )

        non_vacuous_file = os.path.join(dir, base_file_name + "_non_vacuous_index.csv")
        with open(non_vacuous_file, "r") as f:
            accumulated_non_vacuous_index = dict(
                [
                    (float(line.split(";")[0]), float(line.split(";")[1]))
                    for line in f.read().split("\n")
                    if line
                ]
            )

        return PerformanceEvaluationResult(
            accumulated_valid_inputs,
            accumulated_invalid_inputs,
            accumulated_k_path_coverage,
            accumulated_non_vacuous_index,
        )

    def valid_inputs_proportion_data(self) -> Dict[float, float]:
        result: Dict[float, float] = {}
        valid_inputs = 0
        invalid_inputs = 0

        for seconds in sorted(
            list(
                set(self.accumulated_valid_inputs.keys())
                | set(self.accumulated_invalid_inputs.keys())
            )
        ):
            if seconds in self.accumulated_valid_inputs:
                valid_inputs += 1
            if seconds in self.accumulated_invalid_inputs:
                invalid_inputs += 1

            result[seconds] = valid_inputs / (valid_inputs + invalid_inputs)

        return result

    def mean_data(self) -> Dict[float, float]:
        if not (
            self.accumulated_valid_inputs
            and self.accumulated_k_path_coverage
            and self.accumulated_non_vacuous_index
        ):
            return {}

        return {
            seconds: self.single_product_value(seconds)
            for seconds in self.accumulated_valid_inputs
        }

    def single_product_value(
        self, seconds: float, weights: tuple[float, ...] = (1, 1, 1)
    ) -> float:
        return weighted_geometric_mean(
            [
                self.accumulated_valid_inputs[seconds],
                self.accumulated_k_path_coverage[seconds],
                self.accumulated_non_vacuous_index[seconds],
            ],
            weights,
        )

    def plot(self, outfile_pdf: str, title: str = "Performance Data"):
        assert outfile_pdf.endswith(".pdf")
        matplotlib.use("PDF")

        fig, ax = plt.subplots()
        ax.plot(
            list(self.accumulated_valid_inputs.keys()),
            list(self.accumulated_valid_inputs.values()),
            label="Valid Inputs",
        )
        ax.plot(
            list(self.accumulated_invalid_inputs.keys()),
            list(self.accumulated_invalid_inputs.values()),
            label="Invalid Inputs",
        )
        ax.plot(
            list(self.accumulated_k_path_coverage.keys()),
            list(self.accumulated_k_path_coverage.values()),
            label="k-Path Coverage (%)",
        )

        mean = self.mean_data()
        ax.plot(list(mean.keys()), list(mean.values()), label="Geometric Mean")

        for values in [
            self.accumulated_valid_inputs.values(),
            self.accumulated_invalid_inputs.values(),
            self.accumulated_k_path_coverage.values(),
            mean.values(),
        ]:
            if values:
                plt.annotate(
                    max(values),
                    xy=(1, max(values)),
                    xytext=(8, 0),
                    xycoords=("axes fraction", "data"),
                    textcoords="offset points",
                )

        ax.set_xlabel("Seconds")
        ax.set_title(title)
        ax.legend()
        fig.tight_layout()
        plt.plot()

        print(f"Saving performance analysis plot to {outfile_pdf}")
        matplotlib.pyplot.savefig(outfile_pdf)

    def __repr__(self):
        return (
            f"PerformanceEvaluationResult("
            f"accumulated_valid_inputs={self.accumulated_valid_inputs}, "
            f"accumulated_invalid_inputs={self.accumulated_invalid_inputs}, "
            f"accumulated_k_path_coverage={self.accumulated_k_path_coverage}, "
            f"accumulated_non_vacuous_index={self.accumulated_non_vacuous_index})"
        )

    def __str__(self):
        return (
            f"Performance: {self.final_product_value} ("
            f"valid inputs: {(list(self.accumulated_valid_inputs.values()) or [0])[-1]}, "
            f"invalid inputs: {(list(self.accumulated_invalid_inputs.values()) or [0])[-1]}, "
            f"k-Path Coverage: {(list(self.accumulated_k_path_coverage.values()) or [0])[-1]}, "
            f"Non-Vacuity Index: {(list(self.accumulated_non_vacuous_index.values()) or [0])[-1]})"
        )


def auto_tune_weight_vector(
    grammar: Grammar,
    formula: language.Formula,
    validator: Callable[[isla.derivation_tree.DerivationTree], bool],
    timeout: int = 60,
    population_size: int = 10,
    generations: int = 10,
    k: int = 3,
    seed_population: List[CostWeightVector] = None,
    cpu_count: int = -1,
) -> Tuple[PerformanceEvaluationResult, CostWeightVector]:
    assert population_size >= 4
    assert population_size % 2 == 0

    if cpu_count < 1:
        cpu_count = mp.cpu_count()

    time_estimate = 2.5 * (
        timeout * population_size / cpu_count
        + (generations - 1) * (population_size // 2) * timeout / cpu_count
    )
    endtime = (
        datetime.datetime.now() + datetime.timedelta(seconds=time_estimate)
    ).strftime("%d/%m/%Y %H:%M:%S")
    print(
        f"Autotuning, estimated time > {time_estimate}s, end: {endtime}",
    )

    # Create initial population
    seed_population = seed_population or []
    if len(seed_population) < population_size:
        seed_population = seed_population + [
            CostWeightVector(
                tree_closing_cost=randno(),
                constraint_cost=randno(),
                derivation_depth_penalty=randno(),
                low_k_coverage_penalty=randno(),
                low_global_k_path_coverage_penalty=randno(),
            )
            for _ in range(population_size - len(seed_population))
        ]

    assert len(seed_population) == population_size

    current_population = sorted(
        zip(
            evaluate_cost_vectors_isla(
                seed_population,
                grammar,
                formula,
                validator,
                timeout,
                k=k,
                cpu_count=cpu_count,
            ),
            seed_population,
        ),
        key=lambda t: t[0].final_product_value,
    )

    print(
        "Initial population:\n"
        + "\n".join([f"{str(v)}, {str(r)}" for r, v in current_population])
        + "\n"
    )

    for generation in range(generations - 1):
        # Remove the five least fittest elements
        current_population = current_population[population_size // 2 :]

        # Crossover
        offspring: List[CostWeightVector] = []
        idx = 0
        while len(offspring) < population_size // 2:
            # first_parent, second_parent = random.sample(current_population, k=2)

            first_parent = current_population[idx % len(current_population)]
            second_parent = current_population[(idx + 1) % len(current_population)]

            all_features = list(set(first_parent[1].__dict__.keys()))

            # OPTION 1: Crossing using arithmetic mean
            child = CostWeightVector(
                **{
                    feature: (
                        first_parent[1].__dict__[feature]
                        + second_parent[1].__dict__[feature]
                    )
                    // 2
                    for feature in all_features
                }
            )

            # OPTION 2: Crossing with two features from the first, and three from the second parent
            # first_parent_features = random.sample(all_features, 2)
            # child = CostWeightVector(**{
            #     feature:
            #         first_parent[1].__dict__[feature]
            #         if feature in first_parent_features
            #         else second_parent[1].__dict__[feature]
            #     for feature in all_features
            # })

            logger.debug(
                f"Crossover of\n{first_parent[1]}\nand\n{second_parent[1]}:\n{child}"
            )

            # Mutate one child feature
            mutated_feature = random.choice(all_features)
            current_feature_value: int = getattr(child, mutated_feature)
            setattr(child, mutated_feature, mutate_cost_weight(current_feature_value))

            logger.debug("After Mutation: %s", child)

            offspring.append(child)

        eval_results = evaluate_cost_vectors_isla(
            offspring, grammar, formula, validator, timeout, k=k, cpu_count=cpu_count
        )
        current_population.extend(list(zip(eval_results, seed_population)))
        current_population = sorted(
            current_population, key=lambda t: t[0].final_product_value
        )

        print(
            f"Generation {generation + 1}:\n"
            + "\n".join([f"{str(v)}, {str(r)}" for r, v in current_population])
            + "\n"
        )

        idx += 1

    result = current_population[-1]
    print(f"Auto-tuning finished. Result: {result[1]}, {result[0]}")
    return result


def evaluate_cost_vectors_isla(
    population: List[CostWeightVector],
    grammar: Grammar,
    formula: language.Formula,
    validator: Callable[[isla.derivation_tree.DerivationTree], bool],
    timeout: int,
    cpu_count: int = -1,
    k=3,
) -> List[PerformanceEvaluationResult]:
    if cpu_count < 0:
        cpu_count = mp.cpu_count()

    if cpu_count < 2:
        return [
            evaluate_isla_generator(
                grammar, formula, vector, validator, timeout, None, k
            )
            for vector in population
        ]

    with pmp.Pool(processes=cpu_count) as pool:
        start_time = datetime.datetime.now()

        result = pool.starmap(
            evaluate_isla_generator,
            [
                (grammar, formula, vector, validator, timeout, None, k)
                for vector in population
            ],
        )
        logger.debug(
            "Time taken for evaluating population w/ parallel processing: %s",
            (datetime.datetime.now() - start_time),
        )
        return result


def evaluate_mutated_cost_vectors(
    grammar: Grammar,
    formula: language.Formula,
    base_vector: CostWeightVector,
    validator: Callable[[isla.derivation_tree.DerivationTree], bool],
    final_out_file_name: str,
    timeout: int = 60,
    rounds: int = 30,
    k: int = 3,
):
    for i in range(rounds):
        v = mutate_cost_vector(base_vector)

        print(f"Round {i + 1}, cost vector {v}")
        outfile_name = (
            f"/tmp/xml_perf_eval_{str((i + 1)).rjust(len(str(rounds)), '0')}.pdf"
        )

        evaluate_isla_generator(
            grammar, formula, v, validator, timeout, outfile_name, k
        )

    process = subprocess.run(
        ["pdfjam"]
        + [
            f"/tmp/xml_perf_eval_{str((i + 1)).rjust(len(str(rounds)), '0')}.pdf"
            for i in range(rounds)
        ]
        + ["--nup", "4x3", "--landscape", "--outfile", final_out_file_name],
        stderr=subprocess.PIPE,
    )

    if process.returncode != 0:
        print(
            f"Combining output PDFs did not work, error message: {process.stderr}",
            file=sys.stderr,
        )
    else:
        print("Saved combined output file at " + final_out_file_name)


def mutate_cost_vector(vector: CostWeightVector) -> CostWeightVector:
    args = {
        "tree_closing_cost": vector.tree_closing_cost,
        "constraint_cost": vector.constraint_cost,
        "derivation_depth_penalty": vector.derivation_depth_penalty,
        "low_k_coverage_penalty": vector.low_k_coverage_penalty,
        "low_global_k_path_coverage_penalty": vector.low_global_k_path_coverage_penalty,
    }

    num_mutated_elements = random.choices(
        range(1, 6), weights=[400, 200, 100, 50, 25], k=1
    )[0]
    mutated_elements = random.sample(args.keys(), k=num_mutated_elements)
    new_args = copy.copy(args)
    new_args.update({elem: mutate_cost_weight(args[elem]) for elem in mutated_elements})

    return CostWeightVector(**new_args)


def mutate_cost_weight(w: float, max_factor: int = 1.5) -> float:
    if w == 0:
        return random.random()

    factor = (random.random() + 1) * max_factor
    if factor == max_factor:
        return 0.0
    else:
        return (w * factor) if random.random() < 0.5 else w / factor


def randno(maxno: int = 40) -> int:
    return random.choices(
        range(maxno + 1),
        weights=list(reversed([n // 10 + 1 for n in range(maxno + 1)])),
    )[0]


def evaluate_isla_generator(
    grammar: Grammar,
    formula: language.Formula,
    v: CostWeightVector,
    validator: Callable[[isla.derivation_tree.DerivationTree], bool],
    timeout: int,
    outfile_name: Optional[str] = None,
    k=3,
) -> PerformanceEvaluationResult:
    print(f"Evaluating weight vector {v}")
    solver = ISLaSolver(
        grammar,
        formula,
        max_number_free_instantiations=1,
        max_number_smt_instantiations=1,
        timeout_seconds=timeout,
        cost_computer=GrammarBasedBlackboxCostComputer(
            CostSettings(v, k), gg.GrammarGraph.from_grammar(grammar)
        ),
    )

    return evaluate_producer(
        outfile_pdf=outfile_name,
        diagram_title="\n".join(wrap(str(v), 60)),
        producer=solver,
        formula=formula,
        graph=gg.GrammarGraph.from_grammar(grammar),
        validator=validator,
        timeout_seconds=timeout,
        k=k,
        jobname=str(v),
    )


def evaluate_producer(
    producer: Union[
        Generator[isla.derivation_tree.DerivationTree, None, None], ISLaSolver, Grammar
    ],
    formula: Optional[language.Formula],
    graph: gg.GrammarGraph,
    validator: Callable[[isla.derivation_tree.DerivationTree], bool],
    outfile_pdf: Optional[str] = None,
    timeout_seconds: int = 60,
    diagram_title: str = "Performance Data",
    k=3,
    jobname: str = "Unnamed",
    compute_kpath_coverage: bool = True,
    compute_vacuity: bool = True,
) -> PerformanceEvaluationResult:
    print(f"Collecting performance data, job: {jobname}")
    data = generate_inputs(producer, timeout_seconds=timeout_seconds)
    print(f"Evaluating Data, job: {jobname}")

    evaluation_result = evaluate_data(
        data,
        formula,
        graph,
        validator,
        k,
        jobname=jobname,
        compute_kpath_coverage=compute_kpath_coverage,
        compute_vacuity=compute_vacuity,
    )

    if outfile_pdf:
        print(f"Plotting result to {outfile_pdf}, job: {jobname}")
        evaluation_result.plot(outfile_pdf, title=diagram_title)

    return evaluation_result


def evaluate_generators(
    producers: List[Union[Grammar, ISLaSolver]],
    formula: Optional[language.Formula],
    graph: gg.GrammarGraph,
    validator: Callable[[isla.derivation_tree.DerivationTree], bool],
    timeout_seconds: int = 60,
    k=3,
    cpu_count: int = -1,
    jobnames: Optional[List[str]] = None,
    compute_kpath_coverage: bool = True,
    compute_vacuity: bool = True,
) -> List[PerformanceEvaluationResult]:
    assert jobnames is None or len(jobnames) == len(producers)
    if jobnames is None:
        jobnames = ["Unnamed" for _ in range(len(producers))]

    if cpu_count < 0:
        cpu_count = mp.cpu_count()

    if cpu_count < 2:
        return [
            evaluate_producer(
                producer,
                formula,
                graph,
                validator,
                timeout_seconds=timeout_seconds,
                k=k,
                jobname=jobname,
                compute_kpath_coverage=compute_kpath_coverage,
                compute_vacuity=compute_vacuity,
            )
            for jobname, producer in zip(jobnames, producers)
        ]

    with pmp.Pool(processes=cpu_count) as pool:
        return pool.starmap(
            evaluate_producer,
            [
                (
                    producer,
                    formula,
                    graph,
                    validator,
                    None,
                    timeout_seconds,
                    "",
                    k,
                    jobname,
                    compute_kpath_coverage,
                    compute_vacuity,
                )
                for jobname, producer in zip(jobnames, producers)
            ],
        )


def load_results(
    out_dir: str, base_name: str, jobnames: List[str]
) -> List[PerformanceEvaluationResult]:
    return [
        PerformanceEvaluationResult.load_from_csv_file(out_dir, base_name + jobname)
        for jobname in jobnames
    ]


def print_statistics(out_dir: str, base_name: str, jobnames: List[str]):
    results = load_results(out_dir, base_name, jobnames)
    for jobname, result in zip(jobnames, results):
        print(jobname + "\n" + "".join(["=" for _ in range(len(jobname))]) + "\n")

        valid_inputs = list(result.accumulated_valid_inputs.values() or [0])[-1]
        invalid_inputs = list(result.accumulated_invalid_inputs.values() or [0])[-1]
        max_kpath_cov = list(result.accumulated_k_path_coverage.values() or [0])[-1]

        # print("Seconds / input: " + "{:.1f}".format(result.max_time / (valid_inputs + invalid_inputs)))
        print(
            "Inputs / second:       "
            + "{:.1f}".format((valid_inputs + invalid_inputs) / result.max_time)
        )
        # print("Seconds / valid input: " + ("N/A" if not valid_inputs
        #                                    else "{:.1f}".format(result.max_time / valid_inputs)))
        print(
            "Precision:             "
            + "{:.0f}".format(100 * valid_inputs / (valid_inputs + invalid_inputs))
            + " %"
        )
        print("k-path Coverage:       " + str(max_kpath_cov) + " %")

        print("\n")


def plot_proportion_valid_inputs_graph(
    out_dir: str,
    base_name: str,
    jobnames: List[str],
    outfile_pdf: str,
    show_final_values=False,
):
    assert outfile_pdf.endswith(".pdf")
    matplotlib.use("PDF")
    results = load_results(out_dir, base_name, jobnames)

    highest_seconds = max([result.max_time for result in results])

    fig, ax = plt.subplots()
    for jobname, result in zip(jobnames, results):
        data = result.valid_inputs_proportion_data()
        ax.plot(
            [0.0] + list(data.keys()) + [highest_seconds],
            [list(data.values())[0]] + list(data.values()) + [list(data.values())[-1]],
            label=jobname,
        )

        if show_final_values:
            label_val = "{:.2f}".format(100 * max(data.values())) + " %"

            plt.annotate(
                label_val,
                xy=(1, list(data.values())[-1]),
                xytext=(8, 0),
                xycoords=("axes fraction", "data"),
                textcoords="offset points",
            )

    ax.yaxis.set_major_formatter(mtick.PercentFormatter(1.0))
    ax.set_xlabel("Seconds")
    ax.set_ylabel("% Valid Inputs")
    ax.legend()
    fig.tight_layout()
    plt.plot()

    matplotlib.pyplot.savefig(outfile_pdf)


def evaluate_data(
    data: Dict[float, isla.derivation_tree.DerivationTree],
    formula: Optional[language.Formula],
    graph: gg.GrammarGraph,
    validator: Callable[[isla.derivation_tree.DerivationTree], bool],
    k: int = 3,
    jobname: str = "Unnamed",
    compute_kpath_coverage: bool = True,
    compute_vacuity: bool = True,
) -> PerformanceEvaluationResult:
    accumulated_valid_inputs: Dict[float, int] = {}
    accumulated_invalid_inputs: Dict[float, int] = {}
    accumulated_k_path_coverage: Dict[float, int] = {}
    accumulated_non_vacuous_index: Dict[float, float] = {}

    quantifier_chains: List[Tuple[language.ForallFormula, ...]] = (
        []
        if (not compute_vacuity or formula is None)
        else [
            tuple([f for f in c if isinstance(f, language.ForallFormula)])
            for c in solver.get_quantifier_chains(formula)
        ]
    )

    valid_inputs: int = 0
    invalid_inputs: int = 0
    covered_kpaths: Set[Tuple[gg.Node, ...]] = set()
    chains_satisfied: Dict[Tuple[language.ForallFormula, ...], int] = {
        c: 0 for c in quantifier_chains
    }

    for seconds, inp in data.items():
        try:
            validation_result = validator(inp)
        except Exception as err:
            validation_result = False
            print(
                f"Exception {err} raise when validating input {inp}, tree: {repr(inp)}"
            )

        if validation_result is True:
            valid_inputs += 1
        else:
            invalid_inputs += 1
            accumulated_invalid_inputs[seconds] = invalid_inputs
            logger.debug("Input %s invalid", str(inp))
            continue

        if quantifier_chains:
            vacuously_matched_quantifiers = set()
            isla.evaluator.eliminate_quantifiers(
                language.instantiate_top_constant(formula, inp), graph.to_grammar()
            )

            non_vacuous_chains = {
                c
                for c in quantifier_chains
                if all(of.id != f.id for of in vacuously_matched_quantifiers for f in c)
            }

            for c in non_vacuous_chains:
                assert c in chains_satisfied
                chains_satisfied[c] += 1

        accumulated_valid_inputs[seconds] = valid_inputs

        if compute_kpath_coverage:
            covered_kpaths.update(
                graph.k_paths_in_tree(inp, k, include_terminals=False)
            )
            accumulated_k_path_coverage[seconds] = int(
                len(covered_kpaths)
                * 100
                / len(graph.k_paths(k, include_terminals=False))
            )

        if quantifier_chains and compute_vacuity:
            # Values in chains_satisfied range between 0 and `valid_inputs`, and thus the mean, too.
            chains_satisfied_mean = (
                math.prod([v + 1 for v in chains_satisfied.values()])
                ** (1 / len(chains_satisfied))
                - 1
            )
            assert 0 <= chains_satisfied_mean <= valid_inputs
            # We normalize to a percentage-like value between 0 and 100
            accumulated_non_vacuous_index[seconds] = (
                100 * chains_satisfied_mean / valid_inputs
            )
            assert 0 <= accumulated_non_vacuous_index[seconds] <= 100
        else:
            accumulated_non_vacuous_index[seconds] = 0

    result = PerformanceEvaluationResult(
        accumulated_valid_inputs,
        accumulated_invalid_inputs,
        accumulated_k_path_coverage,
        accumulated_non_vacuous_index,
    )

    print(
        f"Final evaluation values: "
        f"{valid_inputs} valid inputs, "
        f"{invalid_inputs} invalid inputs, "
        f"{int(len(covered_kpaths) * 100 / len(graph.k_paths(k, include_terminals=False)))}% coverage, "
        f"{(list(accumulated_non_vacuous_index.values()) or [0])[-1]} non-vacuous index, "
        f"final mean: {(list(result.mean_data().values()) or [0])[-1]}, job: {jobname}"
    )

    return result
