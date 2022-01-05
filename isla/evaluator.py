import argparse
import itertools
import json
import logging
import multiprocessing as mp
import multiprocessing.pool
import os
import os.path
import sqlite3
import sys
import time
from datetime import datetime
from typing import List, Generator, Dict, Callable, Set, Tuple, Optional, Union, cast

import math
import matplotlib
import matplotlib.pyplot as plt
import pathos.multiprocessing as pmp
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.Parser import EarleyParser
from grammar_graph import gg
from matplotlib import pyplot as plt, ticker as mtick

from isla import isla, solver
from isla.helpers import weighted_geometric_mean
from isla.solver import ISLaSolver
from isla.type_defs import Grammar

logger = logging.getLogger("evaluator")


def std_db_file() -> str:
    return os.path.join(
        *os.path.split(os.path.dirname(os.path.realpath(__file__)))[:-1],
        "isla_evaluation.sqlite")


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
        kwargs['context'] = NoDaemonContext()
        super(NestablePool, self).__init__(*args, **kwargs)


class Evaluator:
    def __init__(
            self,
            jobname_prefix: str,
            generators: List[Callable[[int], ISLaSolver] | Grammar],
            jobnames: List[str],
            validator: Callable[[isla.DerivationTree], bool],
            graph: gg.GrammarGraph,
            db_file: str = std_db_file(),
            default_timeout: int = 60 * 60,
            default_sessions: int = 1):
        self.validator = validator
        self.graph = graph

        args, print_help = self.parse_command_line(
            jobname_prefix, db_file, jobnames, default_sessions, default_timeout)

        if args.listjobs:
            print(f"Available jobs for {jobname_prefix}: " + ", ".join(jobnames))
            exit(0)

        self.db_file: str = args.db

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
            f"{jobname_prefix} {job}":
                generator if isinstance(generator, dict) else generator(self.timeout)
            for job, generator in
            zip(jobnames, generators) if job in chosen_jobs
        }

        try:
            self.num_sessions: int = int(args.numsessions)
        except ValueError:
            print("ERROR: numsessions value must be an integer.", file=sys.stderr)
            print_help()
            exit(1)

        self.do_clean: bool = args.clean
        self.do_analyze: bool = args.analyze
        self.do_generate: bool = args.generate
        self.do_evaluate_validity: bool = args.validity
        self.do_compute_kpaths: bool = args.kpaths

        max_ids = {jobname: (get_max_sid(jobname, self.db_file) or 0) for jobname in self.jobs_and_generators}
        session_out_of_bounds = [
            jobname for jobname in self.jobs_and_generators
            if (max_ids[jobname] < self.num_sessions
                and not self.do_generate
                and not (self.do_clean and
                         not (self.do_generate or self.do_evaluate_validity or self.do_compute_kpaths)))
        ]

        if session_out_of_bounds:
            print(f"ERROR: Too large numsessions value (for job(s) {', '.join(session_out_of_bounds)}).",
                  file=sys.stderr)
            print_help()
            exit(1)

        try:
            self.kvalues: List[int] = [int(val.strip()) for val in cast(str, args.kvalues).split(",")]
        except ValueError:
            print("ERROR: kvalues must be a comma-separated list of integers.", file=sys.stderr)
            print_help()
            exit(1)

        if not (self.do_clean or self.do_analyze or self.do_generate
                or self.do_evaluate_validity or self.do_compute_kpaths):
            print("ERROR: You have to set at least one of -c, -a, -g, -v, or -p.", file=sys.stderr)
            print_help()
            exit(1)

    def parse_command_line(
            self,
            jobname_prefix: str,
            db_file: str,
            jobnames: List[str],
            default_sessions: int, default_timeout: int
    ) -> Tuple[argparse.Namespace, Callable[[], None]]:
        parser = argparse.ArgumentParser(
            description=f"Evaluating the ISLa producer with case study {jobname_prefix}.",
            formatter_class=argparse.ArgumentDefaultsHelpFormatter)
        parser.add_argument("--db", default=db_file, help="Path to the sqlite database file.")
        parser.add_argument(
            "-n", "--numsessions", default=default_sessions,
            help="The number of sessions to generate or analyze.")

        parser.add_argument(
            "-l", "--listjobs", action="store_true", default=False,
            help="Shows all jobs for this evaluator.")
        parser.add_argument(
            "-c", "--clean", action="store_true", default=False,
            help="Removes all data related to the given job(s) from the database. WARNING: This cannot be undone!")
        parser.add_argument(
            "-g", "--generate", action="store_true", default=False,
            help="Generate inputs with a timeout of [timeout] seconds, [numsessions] times.")
        parser.add_argument(
            "-v", "--validity", action="store_true", default=False,
            help="Compute validity of the inputs of the previous [numsessions] sessions.")
        parser.add_argument(
            "-p", "--kpaths", action="store_true", default=False,
            help="Compute k-paths for the inputs of the previous [numsessions] sessions.")
        parser.add_argument(
            "-a", "--analyze", action="store_true", default=False,
            help="Analyze the accumulated results of the previous [numsessions] sessions.")

        parser.add_argument(
            "-j", "--jobs", default=", ".join(jobnames),
            help="Comma-separated list of jobs to run / evaluate.")
        parser.add_argument(
            "-t", "--timeout", default=default_timeout,
            help="The timeout for test input generation. Useful with the '-g' option.")
        parser.add_argument(
            "-k", "--kvalues", default="3,4",
            help="Comma-separated list of the values 'k' for which to compute k-path coverage. "
                 "Useful with the '-p' option.")
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
        for _ in range(self.num_sessions):
            # We do not run the actual test data generation in parallel (at least not if only one job
            # is specified) to not negatively affect the performance. Thus, one session at a time.
            if len(self.jobs_and_generators) == 1:
                for jobname, generator in self.jobs_and_generators.items():
                    inputs = generate_inputs(generator, self.timeout, jobname)
                    store_inputs(jobname, self.timeout, inputs, self.db_file)
                continue

            with pmp.Pool(processes=pmp.cpu_count()) as pool:
                pool.starmap(
                    lambda jobname, generator:
                    store_inputs(
                        jobname, self.timeout, generate_inputs(generator, self.timeout, jobname), self.db_file),
                    list(self.jobs_and_generators.items()))

    def evaluate_validity(self) -> None:
        args: List[Tuple[List[str], List[Callable[[isla.DerivationTree], bool]], List[str], List[int]]] = [
            (
                [jobname],
                [self.validator],
                [self.db_file],
                [i for i in range((get_max_sid(jobname, self.db_file) or 0) - self.num_sessions + 1,
                                  (get_max_sid(jobname, self.db_file) or 0) + 1)])
            for jobname in self.jobs_and_generators
        ]

        args: List[Tuple[str, Callable[[isla.DerivationTree], bool], str, int]] = [
            rt for t in args for rt in tuple(itertools.product(*t))]

        with NestablePool(processes=pmp.cpu_count()) as pool:
            pool.starmap(evaluate_validity, args)

    def compute_kpaths(self) -> None:
        args: List[Tuple[List[str], List[gg.GrammarGraph], List[int], List[str], List[int]]] = [
            (
                [jobname],
                [self.graph],
                [k],
                [self.db_file],
                [i for i in range((get_max_sid(jobname, self.db_file) or 0) - self.num_sessions + 1,
                                  (get_max_sid(jobname, self.db_file) or 0) + 1)])
            for jobname in self.jobs_and_generators
            for k in self.kvalues
        ]

        args: List[Tuple[str, gg.GrammarGraph, int, str, int]] = [
            rt for t in args for rt in tuple(itertools.product(*t))]

        with NestablePool(processes=pmp.cpu_count()) as pool:
            pool.starmap(evaluate_kpaths, args)

    def analyze(self):
        con = sqlite3.connect(self.db_file)
        cur = con.cursor()

        efficiency: Dict[str, float] = {}
        precision: Dict[str, float] = {}
        diversity: Dict[str, float] = {}

        for job in self.jobs_and_generators:
            maxsid = get_max_sid(job, self.db_file)
            assert maxsid > 0 and maxsid >= self.num_sessions

            # Analyze efficiency: Inputs / s
            cur.execute(
                "SELECT COUNT(*) FROM inputs WHERE testId = ? AND sid >= ? AND sid <= ?",
                (job, maxsid - self.num_sessions + 1, maxsid))
            total_inputs: int = cur.fetchone()[0]
            cur.execute(
                "SELECT SUM(seconds) FROM session_lengths WHERE testId = ? AND sid >= ? AND sid <= ?",
                (job, maxsid - self.num_sessions + 1, maxsid))
            time: int = cur.fetchone()[0]
            efficiency[job] = total_inputs / time

            # Analyze precision: Fraction of valid inputs
            cur.execute(
                "SELECT COUNT(*) FROM inputs NATURAL JOIN valid WHERE testId = ? AND sid >= ? AND sid <= ?",
                (job, maxsid - self.num_sessions + 1, maxsid))
            valid_inputs: int = cur.fetchone()[0]
            precision[job] = valid_inputs / total_inputs

            # Analyze diversity: Fraction of covered k-paths
            total_num_kpaths = {k: len(self.graph.k_paths(k)) for k in self.kvalues}
            diversity_by_sid: Dict[int, float] = {}
            for sid in range(maxsid - self.num_sessions + 1, maxsid + 1):
                diversity_by_k: Dict[int, float] = {}
                for k in self.kvalues:
                    cur.execute(
                        "SELECT paths FROM inputs NATURAL JOIN kpaths WHERE testId = ? AND sid = ? AND k = ?",
                        (job, sid, k))
                    path_hashes: Set[int] = set([])
                    for row in cur:
                        path_hashes.update({int(path_hash) for path_hash in json.loads(row[0])})

                    diversity_by_k[k] = len(path_hashes) / total_num_kpaths[k]
                    assert len(path_hashes) < total_num_kpaths[k]

                diversity_by_sid[sid] = sum(diversity_by_k.values()) / len(diversity_by_k)

            diversity[job] = sum(diversity_by_sid.values()) / len(diversity_by_sid)

        con.close()

        def perc(inp: float) -> str:
            return frac(inp * 100) + " %"

        def frac(inp: float) -> str:
            return "{:8.2f}".format(inp)

        col_1_len = max([len(job) for job in self.jobs_and_generators])
        row_1 = f"| {'Job'.ljust(col_1_len)} | Efficiency | Precision  | Diversity  |"
        sepline = f"+-{'-'.ljust(col_1_len, '-')}-+------------+------------+------------+"

        print(sepline)
        print(row_1)
        print(sepline)

        for job in self.jobs_and_generators:
            print(f"| {job.ljust(col_1_len)} |   {frac(efficiency[job])} | "
                  f"{perc(precision[job])} | {perc(diversity[job])} |")

        print(sepline)


class PerformanceEvaluationResult:
    def __init__(
            self,
            accumulated_valid_inputs: Dict[float, int],
            accumulated_invalid_inputs: Dict[float, int],
            accumulated_k_path_coverage: Dict[float, int],
            accumulated_non_vacuous_index: Dict[float, float]):
        self.accumulated_valid_inputs = accumulated_valid_inputs
        self.accumulated_invalid_inputs = accumulated_invalid_inputs
        self.accumulated_k_path_coverage = accumulated_k_path_coverage
        self.accumulated_non_vacuous_index = accumulated_non_vacuous_index

        self.max_time = max([
            (.0 if not accumulated_valid_inputs else list(accumulated_valid_inputs.keys())[-1]),
            (.0 if not accumulated_invalid_inputs else list(accumulated_invalid_inputs.keys())[-1]),
        ])

        if accumulated_valid_inputs and accumulated_k_path_coverage and accumulated_non_vacuous_index:
            self.final_product_value: float = self.single_product_value(max(accumulated_valid_inputs.keys()))
        else:
            self.final_product_value = -1

    def save_to_csv_file(self, dir: str, base_file_name: str):
        valid_input_file = os.path.join(dir, base_file_name + "_valid_inputs.csv")
        with open(valid_input_file, 'w') as f:
            f.write("\n".join(f"{t};{r}" for t, r in self.accumulated_valid_inputs.items()))
            print(f"Written valid input data to {valid_input_file}")

        invalid_input_file = os.path.join(dir, base_file_name + "_invalid_inputs.csv")
        with open(invalid_input_file, 'w') as f:
            f.write("\n".join(f"{t};{r}" for t, r in self.accumulated_invalid_inputs.items()))
            print(f"Written invalid input data to {invalid_input_file}")

        k_path_file = os.path.join(dir, base_file_name + "_k_paths.csv")
        with open(k_path_file, 'w') as f:
            f.write("\n".join(f"{t};{r}" for t, r in self.accumulated_k_path_coverage.items()))
            print(f"Written accumulated k-path data {k_path_file}")

        non_vacuous_file = os.path.join(dir, base_file_name + "_non_vacuous_index.csv")
        with open(non_vacuous_file, 'w') as f:
            f.write("\n".join(f"{t};{r}" for t, r in self.accumulated_valid_inputs.items()))
            print(f"Written non-vacuous index data to {k_path_file}")

    @staticmethod
    def load_from_csv_file(dir: str, base_file_name: str) -> 'PerformanceEvaluationResult':
        valid_input_file = os.path.join(dir, base_file_name + "_valid_inputs.csv")
        with open(valid_input_file, 'r') as f:
            accumulated_valid_inputs = dict([
                (float(line.split(";")[0]), int(line.split(";")[1]))
                for line in f.read().split("\n") if line])

        invalid_input_file = os.path.join(dir, base_file_name + "_invalid_inputs.csv")
        with open(invalid_input_file, 'r') as f:
            accumulated_invalid_inputs = dict([
                (float(line.split(";")[0]), int(line.split(";")[1]))
                for line in f.read().split("\n") if line
            ])

        k_path_file = os.path.join(dir, base_file_name + "_k_paths.csv")
        with open(k_path_file, 'r') as f:
            accumulated_k_path_coverage = dict([
                (float(line.split(";")[0]), int(line.split(";")[1]))
                for line in f.read().split("\n") if line])

        non_vacuous_file = os.path.join(dir, base_file_name + "_non_vacuous_index.csv")
        with open(non_vacuous_file, 'r') as f:
            accumulated_non_vacuous_index = dict([
                (float(line.split(";")[0]), float(line.split(";")[1]))
                for line in f.read().split("\n") if line])

        return PerformanceEvaluationResult(
            accumulated_valid_inputs,
            accumulated_invalid_inputs,
            accumulated_k_path_coverage,
            accumulated_non_vacuous_index)

    def valid_inputs_proportion_data(self) -> Dict[float, float]:
        result: Dict[float, float] = {}
        valid_inputs = 0
        invalid_inputs = 0

        for seconds in sorted(list(set(self.accumulated_valid_inputs.keys()) |
                                   set(self.accumulated_invalid_inputs.keys()))):
            if seconds in self.accumulated_valid_inputs:
                valid_inputs += 1
            if seconds in self.accumulated_invalid_inputs:
                invalid_inputs += 1

            result[seconds] = valid_inputs / (valid_inputs + invalid_inputs)

        return result

    def mean_data(self) -> Dict[float, float]:
        if not (self.accumulated_valid_inputs
                and self.accumulated_k_path_coverage
                and self.accumulated_non_vacuous_index):
            return {}

        return {
            seconds: self.single_product_value(seconds)
            for seconds in self.accumulated_valid_inputs}

    def single_product_value(self, seconds: float, weights: tuple[float, ...] = (1, 1, 1)) -> float:
        return weighted_geometric_mean(
            [self.accumulated_valid_inputs[seconds],
             self.accumulated_k_path_coverage[seconds],
             self.accumulated_non_vacuous_index[seconds]],
            weights)

    def plot(self, outfile_pdf: str, title: str = "Performance Data"):
        assert outfile_pdf.endswith(".pdf")
        matplotlib.use("PDF")

        fig, ax = plt.subplots()
        ax.plot(
            list(self.accumulated_valid_inputs.keys()),
            list(self.accumulated_valid_inputs.values()),
            label="Valid Inputs")
        ax.plot(
            list(self.accumulated_invalid_inputs.keys()),
            list(self.accumulated_invalid_inputs.values()),
            label="Invalid Inputs")
        ax.plot(
            list(self.accumulated_k_path_coverage.keys()),
            list(self.accumulated_k_path_coverage.values()),
            label="k-Path Coverage (%)")
        ax.plot(
            list(self.accumulated_non_vacuous_index.keys()),
            list(self.accumulated_non_vacuous_index.values()),
            label="Non-Vacuity Index")

        mean = self.mean_data()
        ax.plot(
            list(mean.keys()),
            list(mean.values()),
            label="Geometric Mean")

        for values in [
            self.accumulated_valid_inputs.values(),
            self.accumulated_invalid_inputs.values(),
            self.accumulated_k_path_coverage.values(),
            self.accumulated_non_vacuous_index.values(),
            mean.values()
        ]:
            plt.annotate(
                max(values),
                xy=(1, max(values)),
                xytext=(8, 0),
                xycoords=('axes fraction', 'data'),
                textcoords='offset points')

        ax.set_xlabel("Seconds")
        ax.set_title(title)
        ax.legend()
        fig.tight_layout()
        plt.plot()

        print("Saving performance analysis plot to %s", outfile_pdf)
        matplotlib.pyplot.savefig(outfile_pdf)

    def __repr__(self):
        return (f"PerformanceEvaluationResult("
                f"accumulated_valid_inputs={self.accumulated_valid_inputs}, "
                f"accumulated_invalid_inputs={self.accumulated_invalid_inputs}, "
                f"accumulated_k_path_coverage={self.accumulated_k_path_coverage}, "
                f"accumulated_non_vacuous_index={self.accumulated_non_vacuous_index})")

    def __str__(self):
        return f"Performance: {self.final_product_value} (" \
               f"valid inputs: {(list(self.accumulated_valid_inputs.values()) or [0])[-1]}, " \
               f"invalid inputs: {(list(self.accumulated_invalid_inputs.values()) or [0])[-1]}, " \
               f"k-Path Coverage: {(list(self.accumulated_k_path_coverage.values()) or [0])[-1]}, " \
               f"Non-Vacuity Index: {(list(self.accumulated_non_vacuous_index.values()) or [0])[-1]})"


def strtime() -> str:
    return datetime.now().strftime("%H:%M:%S")


def generate_inputs(
        generator: Generator[isla.DerivationTree, None, None] | ISLaSolver | Grammar,
        timeout_seconds: int = 60,
        jobname: Optional[str] = None) -> Dict[float, isla.DerivationTree]:
    start_time = time.time()
    result: Dict[float, isla.DerivationTree] = {}
    jobname = "" if not jobname else f" ({jobname})"
    print(f"[{strtime()}] Collecting data for {timeout_seconds} seconds{jobname}")

    if isinstance(generator, ISLaSolver):
        generator = generator.solve()
    elif isinstance(generator, dict):
        grammar = generator

        def gen():
            fuzzer = GrammarCoverageFuzzer(grammar)
            while True:
                yield isla.DerivationTree.from_parse_tree(
                    list(EarleyParser(grammar).parse(fuzzer.fuzz()))[0])

        generator = gen()

    while int(time.time()) - int(start_time) <= timeout_seconds:
        try:
            inp = next(generator)
        except StopIteration:
            break
        except Exception as exp:
            print("Exception occurred while executing solver; I'll stop here:\n" + str(exp), file=sys.stderr)
            return result

        logger.debug("Input: %s", str(inp))
        curr_relative_time = time.time() - start_time
        assert curr_relative_time not in result
        result[curr_relative_time] = inp

    print(f"[{strtime()}] Collected {len(result)} inputs in {timeout_seconds} seconds{jobname}")
    return result


def create_db_tables(db_file: str = std_db_file()) -> None:
    inputs_table_sql = \
        """CREATE TABLE IF NOT EXISTS inputs (
    inpId INTEGER PRIMARY KEY ASC, 
    testId TEXT,
    sid INT,
    reltime REAL,
    inp TEXT
)"""
    valid_inputs_table_sql = "CREATE TABLE IF NOT EXISTS valid(inpId INTEGER PRIMARY KEY ASC)"
    kpaths_table_sql = "CREATE TABLE IF NOT EXISTS kpaths(inpId INT, k INT, paths TEXT, UNIQUE(inpId, k))"
    session_length_sql = "CREATE TABLE IF NOT EXISTS session_lengths(testId TEXT, sid INT, seconds INT)"

    tables = {
        "inputs": inputs_table_sql,
        "valid": valid_inputs_table_sql,
        "kpaths": kpaths_table_sql,
        "session_lengths": session_length_sql
    }

    con = sqlite3.connect(db_file)

    with con:
        for tbl_name, cmd in tables.items():
            con.execute(cmd)

    with con:
        # Check integrity of table definitions (if could fail if tables already existed)
        for tbl_name, cmd in tables.items():
            for row in con.execute("SELECT sql FROM sqlite_master WHERE name = ?", (tbl_name,)):
                cmd = cmd.replace(" IF NOT EXISTS", "")
                sql: str = row[0]
                assert sql == cmd, f"Table SQL\n---\n{sql}\n---\n" \
                                   f"does not equal required definition\n---\n{cmd}\n---"

    con.close()


def truncate_db_tables(jobs: List[str], db_file: str = std_db_file()) -> None:
    create_db_tables(db_file)
    con = sqlite3.connect(db_file)

    with con:
        for job in jobs:
            for row in con.execute("SELECT inpId FROM inputs WHERE testId = ?", (job,)):
                con.execute("DELETE FROM valid WHERE inpId = ?", (row[0],))
                con.execute("DELETE FROM kpaths WHERE inpId = ?", (row[0],))

            con.execute("DELETE FROM inputs WHERE testId = ?", (job,))

    con.close()


def get_max_sid(test_id: str, db_file: str = std_db_file()) -> Optional[int]:
    create_db_tables(db_file)
    con = sqlite3.connect(db_file)

    with con:
        sid = None
        for row in con.execute("SELECT MAX(sid) FROM inputs WHERE testId = ?", (test_id,)):
            if row[0]:
                sid = row[0]
            break

    con.close()
    return sid


def get_session_length(test_id: str, sid: int, db_file: str = std_db_file()) -> int:
    create_db_tables(db_file)
    con = sqlite3.connect(db_file)
    result = None

    with con:
        result = None
        for row in con.execute("SELECT seconds FROM session_lengths WHERE testId = ? AND sid = ?", (test_id, sid)):
            result = row[0]
            break

    assert result is not None
    con.close()
    return result


def store_inputs(
        test_id: str,
        timeout: int,
        inputs: Dict[float, isla.DerivationTree],
        db_file: str = std_db_file()) -> None:
    sid = (get_max_sid(test_id, db_file) or 0) + 1

    create_db_tables(db_file)
    con = sqlite3.connect(db_file)

    with con:
        reltime: float
        inp: isla.DerivationTree
        for reltime, inp in inputs.items():
            con.execute(
                "INSERT INTO inputs(testId, sid, reltime, inp) VALUES (?, ?, ?, ?)",
                (test_id, sid, reltime, json.dumps(inp.to_parse_tree())))

        con.execute(
            "INSERT INTO session_lengths(testId, sid, seconds) VALUES (?, ?, ?)",
            (test_id, sid, timeout))

    con.close()


def get_inputs_from_db(
        test_id: str,
        sid: Optional[int] = None,
        db_file: str = std_db_file(),
        only_valid: bool = False
) -> Dict[int, isla.DerivationTree]:
    all_inputs_query = \
        """
        SELECT inpId, inp FROM inputs
        WHERE testId = ? AND sid = ?
        """

    valid_inputs_query = \
        """
        SELECT inpId, inp FROM inputs
        NATURAL JOIN valid
        WHERE testId = ? AND sid = ?
        """

    inputs: Dict[int, isla.DerivationTree] = {}

    # Get newest session ID if not present
    if sid is None:
        sid = get_max_sid(test_id, db_file)
        assert sid

    query = valid_inputs_query if only_valid else all_inputs_query
    con = sqlite3.connect(db_file)
    with con:
        for row in con.execute(query, (test_id, sid)):
            inputs[row[0]] = isla.DerivationTree.from_parse_tree(json.loads(row[1]))
    con.close()

    return inputs


def evaluate_validity(
        test_id: str,
        validator: Callable[[isla.DerivationTree], bool],
        db_file: str = std_db_file(),
        sid: Optional[int] = None) -> None:
    create_db_tables(db_file)

    # Get newest session ID if not present
    if sid is None:
        sid = get_max_sid(test_id, db_file)
        assert sid

    print(f"[{strtime()}] Evaluating validity for session {sid} of {test_id}")

    # Obtain inputs from session
    inputs = get_inputs_from_db(test_id, sid, db_file)

    # Evaluate (in parallel)
    def evaluate(inp_id: int, inp: isla.DerivationTree, queue: mp.Queue):
        try:
            if validator(inp) is True:
                queue.put(inp_id)
        except Exception as err:
            print(f"Exception {err} raise when validating input {inp}, tree: {repr(inp)}")

    manager = mp.Manager()
    queue = manager.Queue()
    with pmp.Pool(processes=pmp.cpu_count()) as pool:
        pool.starmap(evaluate, [(inp_id, inp, queue) for inp_id, inp in inputs.items()])

    # Insert into DB
    con = sqlite3.connect(db_file)
    with con:
        while not queue.empty():
            con.execute("INSERT INTO valid(inpId) VALUES (?)", (queue.get(),))
    con.close()

    print(f"[{strtime()}] DONE Evaluating validity for session {sid} of {test_id}")


def evaluate_kpaths(
        test_id: str,
        graph: gg.GrammarGraph,
        k: int = 3,
        db_file: str = std_db_file(),
        sid: Optional[int] = None) -> None:
    if os.environ.get("PYTHONHASHSEED") is None:
        print("WARNING: Environment variable PYTHONHASHSEED not set, "
              "should be set to 0 for deterministic hashing of k-paths", file=sys.stderr)
    if os.environ.get("PYTHONHASHSEED") is not None and os.environ["PYTHONHASHSEED"] != "0":
        print("WARNING: Environment variable PYTHONHASHSEED not set, "
              "should be set to 0 for deterministic hashing of k-paths", file=sys.stderr)

    create_db_tables(db_file)

    # Get newest session ID if not present
    if sid is None:
        sid = get_max_sid(test_id, db_file)
        assert sid

    print(f"[{strtime()}] Evaluating {k}-paths for session {sid} of {test_id}")

    # Obtain inputs from session
    inputs = get_inputs_from_db(test_id, sid, db_file, only_valid=True)

    # Evaluate (in parallel)
    def compute_k_paths(inp_id: int, inp: isla.DerivationTree, queue: mp.Queue):
        queue.put((inp_id, [hash(path) for path in graph.k_paths_in_tree(inp.to_parse_tree(), k)]))

    manager = mp.Manager()
    queue = manager.Queue()
    with pmp.Pool(processes=pmp.cpu_count()) as pool:
        pool.starmap(compute_k_paths, [(inp_id, inp, queue) for inp_id, inp in inputs.items()])

    # Insert into DB
    con = sqlite3.connect(db_file)
    with con:
        while not queue.empty():
            inp_id, path_hashes = queue.get()
            con.execute("INSERT INTO kpaths(inpId, k, paths) VALUES (?, ?, ?)", (inp_id, k, json.dumps(path_hashes)))
    con.close()

    print(f"[{strtime()}] DONE Evaluating {k}-paths for session {sid} of {test_id}")


def evaluate_data(
        data: Dict[float, isla.DerivationTree],
        formula: Optional[isla.Formula],
        graph: gg.GrammarGraph,
        validator: Callable[[isla.DerivationTree], bool],
        k: int = 3,
        jobname: str = "Unnamed",
        compute_kpath_coverage: bool = True,
        compute_vacuity: bool = True) -> PerformanceEvaluationResult:
    accumulated_valid_inputs: Dict[float, int] = {}
    accumulated_invalid_inputs: Dict[float, int] = {}
    accumulated_k_path_coverage: Dict[float, int] = {}
    accumulated_non_vacuous_index: Dict[float, float] = {}

    quantifier_chains: List[Tuple[isla.ForallFormula, ...]] = (
        [] if (not compute_vacuity or formula is None)
        else [tuple([f for f in c if isinstance(f, isla.ForallFormula)])
              for c in solver.get_quantifier_chains(formula)])

    valid_inputs: int = 0
    invalid_inputs: int = 0
    covered_kpaths: Set[Tuple[gg.Node, ...]] = set()
    chains_satisfied: Dict[Tuple[isla.ForallFormula, ...], int] = {c: 0 for c in quantifier_chains}

    for seconds, inp in data.items():
        try:
            validation_result = validator(inp)
        except Exception as err:
            validation_result = False
            print(f"Exception {err} raise when validating input {inp}, tree: {repr(inp)}")

        if validation_result is True:
            valid_inputs += 1
        else:
            invalid_inputs += 1
            accumulated_invalid_inputs[seconds] = invalid_inputs
            logger.debug("Input %s invalid", str(inp))
            continue

        if quantifier_chains:
            vacuously_matched_quantifiers = set()
            isla.eliminate_quantifiers(
                isla.instantiate_top_constant(formula, inp),
                vacuously_matched_quantifiers, graph.to_grammar())

            non_vacuous_chains = {
                c for c in quantifier_chains if
                all(of.id != f.id
                    for of in vacuously_matched_quantifiers
                    for f in c)}

            for c in non_vacuous_chains:
                assert c in chains_satisfied
                chains_satisfied[c] += 1

        accumulated_valid_inputs[seconds] = valid_inputs

        if compute_kpath_coverage:
            covered_kpaths.update(graph.k_paths_in_tree(inp.to_parse_tree(), k))
            accumulated_k_path_coverage[seconds] = int(len(covered_kpaths) * 100 / len(graph.k_paths(k)))

        if quantifier_chains and compute_vacuity:
            # Values in chains_satisfied range between 0 and `valid_inputs`, and thus the mean, too.
            chains_satisfied_mean = (
                    math.prod([v + 1 for v in chains_satisfied.values()]) ** (1 / len(chains_satisfied)) - 1)
            assert 0 <= chains_satisfied_mean <= valid_inputs
            # We normalize to a percentage-like value between 0 and 100
            accumulated_non_vacuous_index[seconds] = 100 * chains_satisfied_mean / valid_inputs
            assert 0 <= accumulated_non_vacuous_index[seconds] <= 100
        else:
            accumulated_non_vacuous_index[seconds] = 0

    result = PerformanceEvaluationResult(
        accumulated_valid_inputs,
        accumulated_invalid_inputs,
        accumulated_k_path_coverage,
        accumulated_non_vacuous_index)

    print(f"Final evaluation values: "
          f"{valid_inputs} valid inputs, "
          f"{invalid_inputs} invalid inputs, "
          f"{int(len(covered_kpaths) * 100 / len(graph.k_paths(k)))}% coverage, "
          f"{(list(accumulated_non_vacuous_index.values()) or [0])[-1]} non-vacuous index, "
          f"final mean: {(list(result.mean_data().values()) or [0])[-1]}, job: {jobname}")

    return result


def evaluate_producer(
        producer: Union[Generator[isla.DerivationTree, None, None], ISLaSolver, Grammar],
        formula: Optional[isla.Formula],
        graph: gg.GrammarGraph,
        validator: Callable[[isla.DerivationTree], bool],
        outfile_pdf: Optional[str] = None,
        timeout_seconds: int = 60,
        diagram_title: str = "Performance Data",
        k=3,
        jobname: str = "Unnamed",
        compute_kpath_coverage: bool = True,
        compute_vacuity: bool = True) -> PerformanceEvaluationResult:
    print(f"Collecting performance data, job: {jobname}")
    data = generate_inputs(producer, timeout_seconds=timeout_seconds)
    print(f"Evaluating Data, job: {jobname}")

    evaluation_result = evaluate_data(
        data, formula, graph, validator, k,
        jobname=jobname,
        compute_kpath_coverage=compute_kpath_coverage,
        compute_vacuity=compute_vacuity)

    if outfile_pdf:
        print(f"Plotting result to {outfile_pdf}, job: {jobname}")
        evaluation_result.plot(outfile_pdf, title=diagram_title)

    return evaluation_result


def evaluate_generators(
        producers: List[Union[Grammar, ISLaSolver]],
        formula: Optional[isla.Formula],
        graph: gg.GrammarGraph,
        validator: Callable[[isla.DerivationTree], bool],
        timeout_seconds: int = 60,
        k=3,
        cpu_count: int = -1,
        jobnames: Optional[List[str]] = None,
        compute_kpath_coverage: bool = True,
        compute_vacuity: bool = True) -> List[PerformanceEvaluationResult]:
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
                compute_vacuity=compute_vacuity
            )
            for jobname, producer in zip(jobnames, producers)]

    with pmp.Pool(processes=cpu_count) as pool:
        return pool.starmap(evaluate_producer, [
            (producer, formula, graph, validator, None, timeout_seconds, "", k,
             jobname, compute_kpath_coverage, compute_vacuity)
            for jobname, producer in zip(jobnames, producers)])


def load_results(out_dir: str, base_name: str, jobnames: List[str]) -> List[PerformanceEvaluationResult]:
    return [PerformanceEvaluationResult.load_from_csv_file(
        out_dir, base_name + jobname) for jobname in jobnames]


def print_statistics(out_dir: str, base_name: str, jobnames: List[str]):
    results = load_results(out_dir, base_name, jobnames)
    for jobname, result in zip(jobnames, results):
        print(jobname + "\n" + "".join(["=" for _ in range(len(jobname))]) + "\n")

        valid_inputs = list(result.accumulated_valid_inputs.values() or [0])[-1]
        invalid_inputs = list(result.accumulated_invalid_inputs.values() or [0])[-1]
        max_kpath_cov = list(result.accumulated_k_path_coverage.values() or [0])[-1]

        # print("Seconds / input: " + "{:.1f}".format(result.max_time / (valid_inputs + invalid_inputs)))
        print("Inputs / second:       " + "{:.1f}".format((valid_inputs + invalid_inputs) / result.max_time))
        # print("Seconds / valid input: " + ("N/A" if not valid_inputs
        #                                    else "{:.1f}".format(result.max_time / valid_inputs)))
        print("Precision:             " + "{:.0f}".format(100 * valid_inputs / (valid_inputs + invalid_inputs)) + " %")
        print("k-path Coverage:       " + str(max_kpath_cov) + " %")

        print("\n")


def plot_proportion_valid_inputs_graph(
        out_dir: str, base_name: str, jobnames: List[str], outfile_pdf: str, show_final_values=False):
    assert outfile_pdf.endswith(".pdf")
    matplotlib.use("PDF")
    results = load_results(out_dir, base_name, jobnames)

    highest_seconds = max([result.max_time for result in results])

    fig, ax = plt.subplots()
    for jobname, result in zip(jobnames, results):
        data = result.valid_inputs_proportion_data()
        ax.plot(
            [.0] + list(data.keys()) + [highest_seconds],
            [list(data.values())[0]] + list(data.values()) + [list(data.values())[-1]],
            label=jobname)

        if show_final_values:
            label_val = "{:.2f}".format(100 * max(data.values())) + " %"

            plt.annotate(
                label_val,
                xy=(1, list(data.values())[-1]),
                xytext=(8, 0),
                xycoords=('axes fraction', 'data'),
                textcoords='offset points')

    ax.yaxis.set_major_formatter(mtick.PercentFormatter(1.0))
    ax.set_xlabel("Seconds")
    ax.set_ylabel("% Valid Inputs")
    ax.legend()
    fig.tight_layout()
    plt.plot()

    matplotlib.pyplot.savefig(outfile_pdf)
