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

import argparse
import itertools
import json
import logging
import multiprocessing.pool
import os
import os.path
import re
import sqlite3
import statistics
import sys
import time
import traceback
from datetime import datetime
from sqlite3 import Cursor
from typing import List, Generator, Dict, Callable, Set, Tuple, Optional, cast, Sequence

import ijson
import pathos.multiprocessing as pmp
from grammar_graph import gg
from grammar_graph.gg import path_to_string

import isla.derivation_tree
from isla.fuzzer import GrammarCoverageFuzzer
from isla.helpers import tree_to_string
from isla.solver import ISLaSolver
from isla.type_defs import Grammar, ParseTree

logger = logging.getLogger("evaluator")


def std_db_file() -> str:
    return os.path.join(
        *os.path.split(os.path.dirname(os.path.realpath(__file__)))[:-1],
        "isla_evaluation.sqlite",
    )


# Non-Deamon solution from https://stackoverflow.com/questions/6974695/python-process-pool-non-daemonic#answer-53180921
# to enable spawning subprocesses inside spawned subprocesses.
class NoDaemonProcess(multiprocessing.Process):
    @property
    def daemon(self):
        return False

    @daemon.setter
    def daemon(self, value):
        pass


class NoDaemonContext(type(multiprocessing.get_context())):
    Process = NoDaemonProcess


# We sub-class multiprocessing.pool.Pool instead of multiprocessing.Pool
# because the latter is only a wrapper function, not a proper class.
class NestablePool(multiprocessing.pool.Pool):
    def __init__(self, *args, **kwargs):
        kwargs["context"] = NoDaemonContext()
        super(NestablePool, self).__init__(*args, **kwargs)


class Evaluator:
    def __init__(  # noqa: C901
        self,
        jobname_prefix: str,
        generators: List[Callable[[int], ISLaSolver] | Grammar],
        jobnames: List[str],
        # TODO: Make validators accept ParseTrees instead of DerivationTrees;
        #       there are ParseTrees in the database, and the conversion to
        #       DerivationTrees is expensive.
        validator: Callable[[isla.derivation_tree.DerivationTree], bool],
        graph: gg.GrammarGraph,
        db_file: str = std_db_file(),
        default_timeout: int = 60 * 60,
        default_sessions: int = 1,
    ):
        self.validator = validator
        self.graph = graph

        args, print_help = self.parse_command_line(
            jobname_prefix, db_file, jobnames, default_sessions, default_timeout
        )

        if args.listjobs:
            print(f"Available jobs for {jobname_prefix}: " + ", ".join(jobnames))
            exit(0)

        self.db_file: str = args.db

        if not args.generate:
            assert os.path.exists(args.db)

        chosen_jobs = [name.strip() for name in args.jobs.split(",")]
        if any(job not in jobnames for job in chosen_jobs):
            print("ERROR: Unknown job specified.", file=sys.stderr)
            print_help()
            exit(1)

        if not chosen_jobs:
            print("ERROR: You have to choose at least one job.", file=sys.stderr)
            print_help()
            exit(1)

        try:
            self.timeout: int = int(args.timeout)
        except ValueError:
            print("ERROR: timeout value must be an integer.", file=sys.stderr)
            print_help()
            exit(1)

        self.jobs_and_generators = {
            f"{jobname_prefix} {job}": generator
            if isinstance(generator, dict)
            else generator(self.timeout)
            for job, generator in zip(jobnames, generators)
            if job in chosen_jobs
        }

        try:
            self.num_sessions: int = int(args.numsessions)
        except ValueError:
            print("ERROR: numsessions value must be an integer.", file=sys.stderr)
            print_help()
            exit(1)

        self.do_clean: bool = args.clean
        self.do_analyze: bool = args.analyze
        self.do_print_missing_kpaths: bool = args.print_missing_kpaths
        self.do_generate: bool = args.generate
        self.do_evaluate_validity: bool = args.validity
        self.do_compute_kpaths: bool = args.kpaths
        self.dry_run: bool = args.dryrun

        max_ids = {
            jobname: (get_max_sid(jobname, self.db_file) or 0)
            for jobname in self.jobs_and_generators
        }
        session_out_of_bounds = [
            jobname
            for jobname in self.jobs_and_generators
            if (
                max_ids[jobname] < self.num_sessions
                and not self.do_generate
                and not (
                    self.do_clean
                    and not (
                        self.do_generate
                        or self.do_evaluate_validity
                        or self.do_compute_kpaths
                    )
                )
            )
        ]

        if session_out_of_bounds:
            print(
                f"ERROR: Too large numsessions value (for job(s) {', '.join(session_out_of_bounds)}).",
                file=sys.stderr,
            )
            print_help()
            exit(1)

        try:
            self.kvalues: List[int] = [
                int(val.strip()) for val in cast(str, args.kvalues).split(",")
            ]
        except ValueError:
            print(
                "ERROR: kvalues must be a comma-separated list of integers.",
                file=sys.stderr,
            )
            print_help()
            exit(1)

        if not (
            self.do_clean
            or self.do_analyze
            or self.do_generate
            or self.do_evaluate_validity
            or self.do_compute_kpaths
        ):
            print(
                "ERROR: You have to set at least one of -c, -a, -g, -v, or -p.",
                file=sys.stderr,
            )
            print_help()
            exit(1)

    def parse_command_line(
        self,
        jobname_prefix: str,
        db_file: str,
        jobnames: List[str],
        default_sessions: int,
        default_timeout: int,
    ) -> Tuple[argparse.Namespace, Callable[[], None]]:
        parser = argparse.ArgumentParser(
            description=f"Evaluating the ISLa producer with case study {jobname_prefix}.",
            formatter_class=argparse.ArgumentDefaultsHelpFormatter,
        )
        parser.add_argument(
            "--db", default=db_file, help="Path to the sqlite database file."
        )
        parser.add_argument(
            "-n",
            "--numsessions",
            default=default_sessions,
            help="The number of sessions to generate or analyze. "
            "For analysis, this can be set to -1; in this case, all sessions are analyzed.",
        )

        parser.add_argument(
            "-l",
            "--listjobs",
            action="store_true",
            default=False,
            help="Shows all jobs for this evaluator.",
        )
        parser.add_argument(
            "-g",
            "--generate",
            action="store_true",
            default=False,
            help="Generate inputs with a timeout of [timeout] seconds, [numsessions] times.",
        )
        parser.add_argument(
            "-v",
            "--validity",
            action="store_true",
            default=False,
            help="Compute validity of the inputs of the previous [numsessions] sessions.",
        )
        parser.add_argument(
            "-p",
            "--kpaths",
            action="store_true",
            default=False,
            help="Compute k-paths for the inputs of the previous [numsessions] sessions.",
        )
        parser.add_argument(
            "-a",
            "--analyze",
            action="store_true",
            default=False,
            help="Analyze the accumulated results of the previous [numsessions] sessions.",
        )
        parser.add_argument(
            "-m",
            "--print-missing-kpaths",
            action="store_true",
            default=False,
            help="Print the uncovered k-paths of the previous [numsessions] sessions.",
        )

        g = parser.add_mutually_exclusive_group()
        g.add_argument(
            "-c",
            "--clean",
            action="store_true",
            default=False,
            help="Removes all data related to the given job(s) from the database. WARNING: This cannot be undone!",
        )
        g.add_argument(
            "-d",
            "--dryrun",
            action="store_true",
            default=False,
            help="Does not write results to database when *generating* (-g). Does not affect -v and -p.",
        )

        parser.add_argument(
            "-j",
            "--jobs",
            default=", ".join(jobnames),
            help="Comma-separated list of jobs to run / evaluate.",
        )
        parser.add_argument(
            "-t",
            "--timeout",
            default=default_timeout,
            help="The timeout for test input generation. Useful with the '-g' option.",
        )
        parser.add_argument(
            "-k",
            "--kvalues",
            default="3,4",
            help="Comma-separated list of the values 'k' for which to compute k-path coverage. "
            "Useful with the '-p' option.",
        )
        args = parser.parse_args()

        return args, lambda: parser.print_help(file=sys.stderr)

    def run(self):
        if self.do_clean:
            truncate_db_tables(list(self.jobs_and_generators.keys()), self.db_file)

        if self.do_generate:
            self.generate()

        if self.do_evaluate_validity:
            self.evaluate_validity()

        if self.do_compute_kpaths:
            self.compute_kpaths()

        if self.do_analyze:
            self.analyze()

    def generate(self) -> None:
        assert self.num_sessions > 0
        for _ in range(self.num_sessions):
            # We do not run the actual test data generation in parallel (at least not if only one job
            # is specified) to not negatively affect the performance. Thus, one session at a time.
            if len(self.jobs_and_generators) == 1:
                for jobname, generator in self.jobs_and_generators.items():
                    inputs = generate_inputs(generator, self.timeout, jobname)
                    if not self.dry_run:
                        store_inputs(jobname, self.timeout, inputs, self.db_file)
                continue

            with pmp.Pool(processes=pmp.cpu_count()) as pool:
                pool.starmap(
                    lambda jobname, generator: generate_inputs(
                        generator, self.timeout, jobname
                    )
                    if self.dry_run
                    else store_inputs(
                        jobname,
                        self.timeout,
                        generate_inputs(generator, self.timeout, jobname),
                        self.db_file,
                    ),
                    list(self.jobs_and_generators.items()),
                )

    def evaluate_validity(self) -> None:
        sids: Dict[str, List[int]] = {
            jobname: get_all_sids(jobname, self.db_file)
            for jobname in self.jobs_and_generators
        }

        args: List[
            Tuple[
                List[str],
                List[Callable[[isla.derivation_tree.DerivationTree], bool]],
                List[str],
                List[int],
            ]
        ] = [
            (
                [jobname],
                [self.validator],
                [self.db_file],
                sids[jobname]
                if self.num_sessions < 0
                else sids[jobname][len(sids[jobname]) - self.num_sessions :],
            )
            for jobname in self.jobs_and_generators
        ]

        args: List[
            Tuple[str, Callable[[isla.derivation_tree.DerivationTree], bool], str, int]
        ] = [rt for t in args for rt in tuple(itertools.product(*t))]

        with NestablePool(processes=pmp.cpu_count()) as pool:
            pool.starmap(evaluate_validity, args)

    def compute_kpaths(self) -> None:
        sids: Dict[str, List[int]] = {
            jobname: get_all_sids(jobname, self.db_file)
            for jobname in self.jobs_and_generators
        }

        args: List[
            Tuple[List[str], List[gg.GrammarGraph], List[int], List[str], List[int]]
        ] = [
            (
                [jobname],
                [self.graph],
                [k],
                [self.db_file],
                sids[jobname]
                if self.num_sessions < 0
                else sids[jobname][len(sids[jobname]) - self.num_sessions :],
            )
            for jobname in self.jobs_and_generators
            for k in self.kvalues
        ]

        args: List[Tuple[str, gg.GrammarGraph, int, str, int]] = [
            rt for t in args for rt in tuple(itertools.product(*t))
        ]

        if len(args) > 1:
            with NestablePool(processes=pmp.cpu_count()) as pool:
                pool.starmap(evaluate_kpaths, args)
        else:
            evaluate_kpaths(*args[0])

    def analyze(self):
        con = sqlite3.connect(self.db_file)
        cur = con.cursor()

        efficiency: Dict[str, float] = {}
        precision: Dict[str, float] = {}
        diversity: Dict[str, float] = {}
        avg_inp_length: Dict[str, float] = {}
        median_inp_length: Dict[str, float] = {}

        job: str
        for job in self.jobs_and_generators:
            sids = tuple(get_all_sids(job, self.db_file))
            if self.num_sessions >= 0:
                sids = sids[len(sids) - self.num_sessions :]
            assert (
                sids
            ), f"There do not exist sufficient sessions for job {job}, found {len(sids)} sessions."
            sids_placeholder = ",".join("?" for _ in range(len(sids)))

            print(f"Analyzing sessions {', '.join(map(str, sids))} for {job}")

            # Analyze efficiency: Inputs / min
            cur.execute(
                f"SELECT COUNT(*) FROM inputs WHERE testId = ? AND sid IN ({sids_placeholder})",
                (job,) + sids,
            )
            total_inputs: int = cur.fetchone()[0]
            cur.execute(
                f"SELECT SUM(seconds) FROM session_lengths WHERE testId = ? AND sid IN ({sids_placeholder})",
                (job,) + sids,
            )
            time: int = cur.fetchone()[0]
            efficiency[job] = 60 * total_inputs / time

            # Analyze precision: Fraction of valid inputs
            cur.execute(
                f"SELECT COUNT(*) FROM inputs NATURAL JOIN valid WHERE testId = ? AND sid IN ({sids_placeholder})",
                (job,) + sids,
            )
            valid_inputs: int = cur.fetchone()[0]
            precision[job] = valid_inputs / total_inputs

            # Analyze diversity: Fraction of covered k-paths
            all_kpaths: Dict[int, Set[str]] = {
                k: {
                    path_to_string(p)
                    for p in self.graph.k_paths(k, include_terminals=False)
                }
                for k in self.kvalues
            }

            diversity[job] = self.__analyze_diversity(all_kpaths, cur, job, sids)

            # Analyze average / median String length
            cur.execute(
                f"SELECT inp FROM inputs NATURAL JOIN valid WHERE testId = ? AND sid IN ({sids_placeholder})",
                (job,) + sids,
            )
            valid_inputs: List[str] = cast(List[str], cur.fetchall())

            if valid_inputs:

                def get_input_length(row: Sequence[str]) -> int:
                    return len(
                        tree_to_string(next(ijson.items(row[0].encode("utf-8"), "")))
                    )

                with pmp.ProcessingPool(processes=pmp.cpu_count()) as pool:
                    input_lengths = pool.map(get_input_length, valid_inputs)

                # input_lengths = []
                # for row in cur:
                #     input_lengths.append(len(str(isla.derivation_tree.DerivationTree.from_parse_tree(
                #         next(ijson.items(row[0].encode('utf-8'), ''))))))

                avg_inp_length[job] = statistics.mean(input_lengths)
                median_inp_length[job] = statistics.median(input_lengths)
            else:
                avg_inp_length[job] = 0
                median_inp_length[job] = 0

        con.close()

        def perc(inp: float) -> str:
            return frac(inp * 100) + "%"

        def frac(inp: float) -> str:
            return "{:6.2f}".format(inp)

        print("\n")

        col_1_len = max([len(job) for job in self.jobs_and_generators])
        row_1 = f"| {'Job'.ljust(col_1_len)} | Efficiency |    Precision     | Diversity  | Mean/Median Input Length |"
        sepline = f"+-{'-'.ljust(col_1_len, '-')}-+------------+------------------+------------+--------------------------+"

        print(sepline)
        print(row_1)
        print(sepline)

        for job in self.jobs_and_generators:
            print(
                f"| {job.ljust(col_1_len)} |     {frac(efficiency[job])} | "
                f"{frac(precision[job] * efficiency[job])} ({perc(precision[job])}) |    {perc(diversity[job])} | "
                + (
                    frac(avg_inp_length[job]) + " / " + frac(median_inp_length[job])
                ).rjust(len("Mean/Median Input Length"))
                + " |"
            )

        print(sepline)

    def __analyze_diversity(
        self,
        all_kpaths: Dict[int, Set[str]],
        cur: Cursor,
        job: str,
        sids: Tuple[int, ...],
    ) -> float:
        # The custom TAR parser is inconsistent with the TAR grammar for the expansion of the `<content>`
        # nonterminal. This has been fixed by now. For existing evaluation data, we patch the k-paths
        # that are affected by the issue.
        tar_kpath_fix_map: Dict[str, Set[str]] = {
            "<content> <content>-choice-1 <characters> <characters>-choice-1 <character>": {
                "<content> <content>-choice-1 <maybe_characters> <maybe_characters>-choice-1 <characters>",
                "<maybe_characters> <maybe_characters>-choice-1 <characters> <characters>-choice-1 <character>",
            },
            "<content> <content>-choice-1 <characters> <characters>-choice-1 <characters>": {
                "<content> <content>-choice-1 <maybe_characters> <maybe_characters>-choice-1 <characters>",
                "<maybe_characters> <maybe_characters>-choice-1 <characters> <characters>-choice-1 <characters>",
            },
            "<content> <content>-choice-1 <nuls> <nuls>-choice-1 <NUL>": {
                "<content> <content>-choice-1 <maybe_nuls> <maybe_nuls>-choice-1 <nuls>",
                "<maybe_nuls> <maybe_nuls>-choice-1 <nuls> <nuls>-choice-1 <NUL>",
            },
            "<content> <content>-choice-1 <nuls> <nuls>-choice-1 <nuls>": {
                "<content> <content>-choice-1 <maybe_nuls> <maybe_nuls>-choice-1 <nuls>",
                "<maybe_nuls> <maybe_nuls>-choice-1 <nuls> <nuls>-choice-1 <nuls>",
            },
            "<entry> <entry>-choice-1 <content> <content>-choice-1 <characters>": {
                "<entry> <entry>-choice-1 <content> <content>-choice-1 <maybe_characters>",
                "<content> <content>-choice-1 <maybe_characters> <maybe_characters>-choice-1 <characters>",
            },
            "<entry> <entry>-choice-1 <content> <content>-choice-1 <nuls>": {
                "<entry> <entry>-choice-1 <content> <content>-choice-1 <maybe_nuls>",
                "<content> <content>-choice-1 <maybe_nuls> <maybe_nuls>-choice-1 <nuls>",
            },
            "<content> <content>-choice-1 <characters> <characters>-choice-1 "
            "<characters> <characters>-choice-1 <character>": {
                "<content> <content>-choice-1 <maybe_characters> <maybe_characters>-choice-1 "
                "<characters> <characters>-choice-1 <characters>",
                "<maybe_characters> <maybe_characters>-choice-1 <characters> <characters>-choice-1 "
                "<characters> <characters>-choice-1 <character>",
            },
            "<content> <content>-choice-1 <characters> <characters>-choice-1 "
            "<characters> <characters>-choice-1 <characters>": {
                "<content> <content>-choice-1 <maybe_characters> <maybe_characters>-choice-1 "
                "<characters> <characters>-choice-1 <characters>",
                "<maybe_characters> <maybe_characters>-choice-1 <characters> <characters>-choice-1 "
                "<characters> <characters>-choice-1 <characters>",
            },
            "<content> <content>-choice-1 <nuls> <nuls>-choice-1 <nuls> <nuls>-choice-1 <NUL>": {
                "<content> <content>-choice-1 <maybe_nuls> <maybe_nuls>-choice-1 <nuls> <nuls>-choice-1 <nuls>",
                "<maybe_nuls> <maybe_nuls>-choice-1 <nuls> <nuls>-choice-1 <nuls> <nuls>-choice-1 <NUL>",
            },
            "<content> <content>-choice-1 <nuls> <nuls>-choice-1 <nuls> <nuls>-choice-1 <nuls>": {
                "<content> <content>-choice-1 <maybe_nuls> <maybe_nuls>-choice-1 <nuls> <nuls>-choice-1 <nuls>",
                "<maybe_nuls> <maybe_nuls>-choice-1 <nuls> <nuls>-choice-1 <nuls> <nuls>-choice-1 <nuls>",
            },
            "<entries> <entries>-choice-1 <entry> <entry>-choice-1 <content> <content>-choice-1 <characters>": {
                "<entries> <entries>-choice-1 <entry> <entry>-choice-1 <content> <content>-choice-1 <maybe_characters>",
                "<entry> <entry>-choice-1 <content> <content>-choice-1 <maybe_characters> "
                "<maybe_characters>-choice-1 <characters>",
            },
            "<entries> <entries>-choice-1 <entry> <entry>-choice-1 <content> <content>-choice-1 <nuls>": {
                "<entries> <entries>-choice-1 <entry> <entry>-choice-1 <content> <content>-choice-1 <maybe_nuls>",
                "<entry> <entry>-choice-1 <content> <content>-choice-1 <maybe_nuls> <maybe_nuls>-choice-1 <nuls>",
            },
            "<entries> <entries>-choice-2 <entry> <entry>-choice-1 <content> <content>-choice-1 <characters>": {
                "<entries> <entries>-choice-2 <entry> <entry>-choice-1 <content> <content>-choice-1 <maybe_characters>",
                "<entry> <entry>-choice-1 <content> <content>-choice-1 <maybe_characters> "
                "<maybe_characters>-choice-1 <characters>",
            },
            "<entries> <entries>-choice-2 <entry> <entry>-choice-1 <content> <content>-choice-1 <nuls>": {
                "<entries> <entries>-choice-2 <entry> <entry>-choice-1 <content> <content>-choice-1 <maybe_nuls>",
                "<entry> <entry>-choice-1 <content> <content>-choice-1 <maybe_nuls> <maybe_nuls>-choice-1 <nuls>",
            },
            "<entry> <entry>-choice-1 <content> <content>-choice-1 <characters> <characters>-choice-1 <character>": {
                "<entry> <entry>-choice-1 <content> <content>-choice-1 <maybe_characters> "
                "<maybe_characters>-choice-1 <characters>",
                "<content> <content>-choice-1 <maybe_characters> <maybe_characters>-choice-1 "
                "<characters> <characters>-choice-1 <character>",
            },
            "<entry> <entry>-choice-1 <content> <content>-choice-1 <characters> <characters>-choice-1 <characters>": {
                "<entry> <entry>-choice-1 <content> <content>-choice-1 <maybe_characters> "
                "<maybe_characters>-choice-1 <characters>",
                "<content> <content>-choice-1 <maybe_characters> <maybe_characters>-choice-1 "
                "<characters> <characters>-choice-1 <characters>",
            },
            "<entry> <entry>-choice-1 <content> <content>-choice-1 <nuls> <nuls>-choice-1 <NUL>": {
                "<entry> <entry>-choice-1 <content> <content>-choice-1 <maybe_nuls> <maybe_nuls>-choice-1 <nuls>",
                "<content> <content>-choice-1 <maybe_nuls> <maybe_nuls>-choice-1 <nuls> <nuls>-choice-1 <NUL>",
            },
            "<entry> <entry>-choice-1 <content> <content>-choice-1 <nuls> <nuls>-choice-1 <nuls>": {
                "<entry> <entry>-choice-1 <content> <content>-choice-1 <maybe_nuls> <maybe_nuls>-choice-1 <nuls>",
                "<content> <content>-choice-1 <maybe_nuls> <maybe_nuls>-choice-1 <nuls> <nuls>-choice-1 <nuls>",
            },
        }

        diversity_by_sid: Dict[int, float] = {}
        for sid in sids:
            diversity_by_k: Dict[int, float] = {}
            for k in self.kvalues:
                cur.execute(
                    "SELECT paths FROM inputs NATURAL JOIN kpaths WHERE testId = ? AND sid = ? AND k = ?",
                    (job, sid, k),
                )

                paths: Set[str] = set()
                for row in cur:
                    for path in next(ijson.items(row[0].encode("utf-8"), "")):
                        if path not in all_kpaths[k]:
                            if path in tar_kpath_fix_map:
                                for fixed_path in tar_kpath_fix_map[path]:
                                    assert (
                                        fixed_path in all_kpaths[k]
                                    ), f"Fixed path {fixed_path} is broken"
                                    paths.add(fixed_path)
                            else:
                                print(
                                    f"For {job}, session {sid}, k={k}, found a covered path that is not "
                                    + f'in the list of all covered paths (SKIPPING): "{path}"',
                                    file=sys.stderr,
                                )

                            continue

                        paths.add(path)

                if self.do_print_missing_kpaths:
                    missing_paths = all_kpaths[k].difference(paths)
                    if missing_paths:
                        print(f'Missing {k}-paths for session {sid} of job "{job}":')
                        print("\n".join(map(lambda p: f"- {p}", missing_paths)))
                    else:
                        print(f'No missing {k}-paths for sesson {sid} of job "{job}"')

                diversity_by_k[k] = len(paths) / len(all_kpaths[k])

            diversity_by_sid[sid] = sum(diversity_by_k.values()) / len(diversity_by_k)

        return sum(diversity_by_sid.values()) / len(diversity_by_sid)


def strtime() -> str:
    return datetime.now().strftime("%H:%M:%S")


def generate_inputs(
    generator: Generator[isla.derivation_tree.DerivationTree, None, None]
    | ISLaSolver
    | Grammar,
    timeout_seconds: int = 60,
    jobname: Optional[str] = None,
) -> Dict[float, isla.derivation_tree.DerivationTree]:
    start_time = time.time()
    result: Dict[float, isla.derivation_tree.DerivationTree] = {}
    jobname = "" if not jobname else f" ({jobname})"
    print(f"[{strtime()}] Collecting data for {timeout_seconds} seconds{jobname}")

    generator = make_input_generator(generator)

    while int(time.time()) - int(start_time) <= timeout_seconds:
        try:
            inp = next(generator)
        except StopIteration:
            break
        except Exception as exp:
            print(
                f"{type(exp).__name__} occurred while executing solver; "
                + "I'll stop here:\n"
                + str(exp),
                file=sys.stderr,
            )
            print(traceback.format_exc())
            return result

        logger.debug("Input: %s", str(inp))
        curr_relative_time = time.time() - start_time
        assert curr_relative_time not in result
        result[curr_relative_time] = inp

    print(
        f"[{strtime()}] Collected {len(result)} inputs in {timeout_seconds} seconds{jobname}"
    )

    return result


def make_input_generator(
    generator: Generator[isla.derivation_tree.DerivationTree, None, None]
    | ISLaSolver
    | Grammar
) -> Generator[isla.derivation_tree.DerivationTree, None, None]:
    if isinstance(generator, ISLaSolver):

        def gen():
            while True:
                try:
                    yield generator.solve()
                except TimeoutError | StopIteration:
                    return

        return gen()

    elif isinstance(generator, dict):
        # grammar
        grammar = generator

        def gen():
            fuzzer = GrammarCoverageFuzzer(grammar)
            while True:
                yield fuzzer.expand_tree(
                    isla.derivation_tree.DerivationTree("<start>", None)
                )

        return gen()

    return generator


def create_db_tables(db_file: str = std_db_file()) -> None:
    inputs_table_sql = """CREATE TABLE IF NOT EXISTS inputs (
    inpId INTEGER PRIMARY KEY ASC,
    testId TEXT,
    sid INT,
    reltime REAL,
    inp TEXT
)"""
    valid_inputs_table_sql = (
        "CREATE TABLE IF NOT EXISTS valid(inpId INTEGER PRIMARY KEY ASC)"
    )
    kpaths_table_sql = "CREATE TABLE IF NOT EXISTS kpaths(inpId INT, k INT, paths TEXT, UNIQUE(inpId, k))"
    session_length_sql = (
        "CREATE TABLE IF NOT EXISTS session_lengths("
        "testId TEXT, sid INT, seconds INT, UNIQUE (testId, sid))"
    )

    tables = {
        "inputs": inputs_table_sql,
        "valid": valid_inputs_table_sql,
        "kpaths": kpaths_table_sql,
        "session_lengths": session_length_sql,
    }

    con = sqlite3.connect(db_file)

    for tbl_name, cmd in tables.items():
        with con:
            con.execute(cmd)

    def preprocess_sql(cmd: str) -> str:
        cmd = cmd.replace("\n", "")
        cmd = cmd.replace('"', "")
        cmd = re.sub(r"\s?\(\s?", "(", cmd)
        cmd = re.sub(r",\s", ",", cmd)
        cmd = cmd.replace(" IF NOT EXISTS", "")
        cmd = re.sub(r"\s+", " ", cmd)
        return cmd

    # Check integrity of table definitions (if could fail if tables already existed)
    cur = con.cursor()
    for tbl_name, cmd in tables.items():
        cur.execute("SELECT sql FROM sqlite_master WHERE name = ?", (tbl_name,))
        row = cur.fetchone()
        assert row
        sql: str = preprocess_sql(row[0])
        cmd = preprocess_sql(cmd)
        assert sql == cmd, (
            f"Table SQL\n---\n{sql}\n---\n"
            f"does not equal required definition\n---\n{cmd}\n---"
        )

    con.close()


def truncate_db_tables(jobs: List[str], db_file: str = std_db_file()) -> None:
    create_db_tables(db_file)
    con = sqlite3.connect(db_file)

    for job in jobs:
        with con:
            for row in con.execute("SELECT inpId FROM inputs WHERE testId = ?", (job,)):
                con.execute("DELETE FROM valid WHERE inpId = ?", (row[0],))
                con.execute("DELETE FROM kpaths WHERE inpId = ?", (row[0],))

            con.execute("DELETE FROM inputs WHERE testId = ?", (job,))

    con.close()


def get_all_sids(test_id: str, db_file: str = std_db_file()) -> List[int]:
    create_db_tables(db_file)
    con = sqlite3.connect(db_file)
    cur = con.cursor()

    cur.execute("SELECT DISTINCT sid FROM inputs WHERE testId = ?", (test_id,))
    result: List[int] = [row[0] for row in cur.fetchall()]
    con.close()

    return result


def get_max_sid(test_id: str, db_file: str = std_db_file()) -> Optional[int]:
    create_db_tables(db_file)
    con = sqlite3.connect(db_file)
    cur = con.cursor()

    cur.execute("SELECT MAX(sid) FROM inputs WHERE testId = ?", (test_id,))
    row = cur.fetchone()
    sid = None if not row else row[0]

    return sid


def get_session_length(test_id: str, sid: int, db_file: str = std_db_file()) -> int:
    create_db_tables(db_file)
    con = sqlite3.connect(db_file)
    result = None

    with con:
        result = None
        for row in con.execute(
            "SELECT seconds FROM session_lengths WHERE testId = ? AND sid = ?",
            (test_id, sid),
        ):
            result = row[0]
            break

    assert result is not None
    con.close()
    return result


def store_inputs(
    test_id: str,
    timeout: int,
    inputs: Dict[float, isla.derivation_tree.DerivationTree],
    db_file: str = std_db_file(),
) -> None:
    assert isinstance(inputs, dict), f"Expected dictionary, got: {type(inputs)}"
    assert all(isinstance(key, float) for key in inputs), "Expected float keys"
    assert all(
        isinstance(value, isla.derivation_tree.DerivationTree)
        for value in inputs.values()
    ), "Expected DerivationTree values keys"

    sid = (get_max_sid(test_id, db_file) or 0) + 1

    create_db_tables(db_file)
    con = sqlite3.connect(db_file)

    reltime: float
    inp: isla.derivation_tree.DerivationTree
    for reltime, inp in inputs.items():
        with con:
            con.execute(
                "INSERT INTO inputs(testId, sid, reltime, inp) VALUES (?, ?, ?, ?)",
                (test_id, sid, reltime, json.dumps(inp.to_parse_tree())),
            )

    with con:
        con.execute(
            "INSERT INTO session_lengths(testId, sid, seconds) VALUES (?, ?, ?)",
            (test_id, sid, timeout),
        )

    con.close()


def get_inputs_from_db(
    test_id: str,
    sid: Optional[int] = None,
    db_file: str = std_db_file(),
    only_valid: bool = False,
    only_unkown_validity: bool = False,
    convert_to_derivation_tree: bool = True,
) -> Dict[int, isla.derivation_tree.DerivationTree | ParseTree]:
    all_inputs_query = """
        SELECT inpId, inp FROM inputs
        WHERE testId = ? AND sid = ?
        """

    valid_inputs_query = """
        SELECT inpId, inp FROM inputs
        NATURAL JOIN valid
        WHERE testId = ? AND sid = ?
        """

    invalid_inputs_query = """
        SELECT inputs.inpId, inputs.inp
        FROM inputs LEFT JOIN valid
        ON inputs.inpId = valid.inpId
        WHERE valid.inpId IS NULL
              AND inputs.testId = ?
              AND inputs.sid = ?
        """

    # Get newest session ID if not present
    if sid is None:
        sid = get_max_sid(test_id, db_file)
        assert sid

    query = (
        valid_inputs_query
        if only_valid
        else (invalid_inputs_query if only_unkown_validity else all_inputs_query)
    )
    con = sqlite3.connect(db_file)
    cur = con.cursor()
    cur.execute(query, (test_id, sid))
    rows = cur.fetchall()
    con.close()

    if convert_to_derivation_tree:
        inputs: Dict[int, isla.derivation_tree.DerivationTree] = {
            row[0]: isla.derivation_tree.DerivationTree.from_parse_tree(
                next(ijson.items(row[1].encode("utf-8"), ""))
            )
            for row in rows
        }
    else:
        inputs: Dict[int, ParseTree] = {
            row[0]: next(ijson.items(row[1].encode("utf-8"), "")) for row in rows
        }

    return inputs


def evaluate_validity(
    test_id: str,
    validator: Callable[[isla.derivation_tree.DerivationTree], bool],
    db_file: str = std_db_file(),
    sid: Optional[int] = None,
    parallel: bool = True,
) -> None:
    create_db_tables(db_file)

    # Get newest session ID if not present
    if sid is None:
        sid = get_max_sid(test_id, db_file)
        assert sid

    print(f"[{strtime()}] Evaluating validity for session {sid} of {test_id}")

    # Obtain inputs from session
    print(f"Reading inputs for session {sid} of {test_id} from database...")
    inputs: Dict[int, isla.derivation_tree.DerivationTree] = get_inputs_from_db(
        test_id, sid, db_file, only_unkown_validity=True
    )

    print(f"Evaluating validity of inputs for session {sid} of {test_id}...")

    # Evaluate
    def evaluate(inp: isla.derivation_tree.DerivationTree) -> bool:
        try:
            return validator(inp) is True
        except Exception as err:
            print(
                f"Exception {err} raise when evaluating input {inp}, tree: {repr(inp)}"
            )
            print(f"Interpreting input '{inp}' as invalid.")
            return False

    valid_ids = [inp_id for inp_id, inp in inputs.items() if evaluate(inp)]

    print(
        f"Writing validity data for inputs from session {sid} of {test_id} to database..."
    )
    # Insert into DB
    con = sqlite3.connect(db_file)
    with con:
        con.executemany(
            "INSERT INTO valid(inpId) VALUES (?)", map(lambda x: (x,), valid_ids)
        )
    con.close()

    print(f"[{strtime()}] DONE Evaluating validity for session {sid} of {test_id}")


def evaluate_kpaths(
    test_id: str,
    graph: gg.GrammarGraph,
    k: int = 3,
    db_file: str = std_db_file(),
    sid: Optional[int] = None,
) -> None:
    if os.environ.get("PYTHONHASHSEED") is None:
        print(
            "WARNING: Environment variable PYTHONHASHSEED not set, "
            "should be set to 0 for deterministic hashing of k-paths",
            file=sys.stderr,
        )
    if (
        os.environ.get("PYTHONHASHSEED") is not None
        and os.environ["PYTHONHASHSEED"] != "0"
    ):
        print(
            "WARNING: Environment variable PYTHONHASHSEED not set, "
            "should be set to 0 for deterministic hashing of k-paths",
            file=sys.stderr,
        )

    create_db_tables(db_file)

    # Get newest session ID if not present
    if sid is None:
        sid = get_max_sid(test_id, db_file)
        assert sid

    print(f"[{strtime()}] Evaluating {k}-paths for session {sid} of {test_id}")

    # Obtain inputs from session
    inputs: Dict[int, ParseTree] = get_inputs_from_db(
        test_id, sid, db_file, only_valid=True, convert_to_derivation_tree=False
    )

    def kpaths_already_computed(inp_id: int) -> bool:
        con = sqlite3.connect(db_file)
        cur = con.cursor()
        cur.execute("SELECT * FROM kpaths WHERE inpId = ?", (inp_id,))
        result = cur.fetchone() is not None
        con.close()
        return result

    inputs = {
        inp_id: inp
        for inp_id, inp in inputs.items()
        if not kpaths_already_computed(inp_id)
    }

    def compute_k_paths(inp: ParseTree) -> List[str]:
        try:
            assert isinstance(inp, list), f"Expected a list, got: {type(inp).__name__}"
            assert (
                len(inp) == 2
            ), f"Expected a (node, children) pair, but tree has {len(inp)} items"
            assert isinstance(
                inp[0], str
            ), f"Node label should be a str, got {type(inp[0]).__name__}"
            assert inp[1] is None or isinstance(
                inp[1], list
            ), f"Children field should be None or list, is: {type(inp[1]).__name__}"
            return [
                path_to_string(path)
                for path in graph.k_paths_in_tree(inp, k, include_terminals=False)
            ]
        except SyntaxError as err:
            print(f"Could not compute {k}-paths, error: {err}")
            return []

    # We evaluate inputs in bundles of `bundle_size` inputs at a time
    bundle_size = 1

    def get2nd(t):
        return t[1]

    input_bundle: List[Tuple[int, Tuple[int, ParseTree]]]
    for input_bundle in map(
        list,
        map(
            get2nd,
            itertools.groupby(enumerate(inputs.items()), lambda p: p[0] // bundle_size),
        ),
    ):
        print(
            f"Evaluating {k}-paths for session {sid} of {test_id}: "
            f"{100 * input_bundle[0][0] / len(inputs):.2f}% done "
            f"({input_bundle[0][0]} of {len(inputs)} inputs)"
        )
        covered_k_paths = {
            inp_id: compute_k_paths(inp) for _, (inp_id, inp) in input_bundle
        }

        # Insert into DB
        con = sqlite3.connect(db_file)
        with con:
            con.executemany(
                "INSERT INTO kpaths(inpId, k, paths) VALUES (?, ?, ?)",
                [
                    (inp_id, k, json.dumps(kpaths))
                    for inp_id, kpaths in covered_k_paths.items()
                ],
            )
        con.close()

    print(f"[{strtime()}] DONE Evaluating {k}-paths for session {sid} of {test_id}")
