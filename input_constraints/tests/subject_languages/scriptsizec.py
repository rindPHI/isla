import string
import subprocess
import tempfile
from subprocess import PIPE
from typing import Union, Optional, IO

from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
from fuzzingbook.GrammarFuzzer import tree_to_string
from fuzzingbook.Grammars import srange

from input_constraints import isla

# Based on:
# Kartik Talwar. Tiny-C Compiler. https://gist.github.com/KartikTalwar/3095780.

SCRIPTSIZE_C_GRAMMAR = {
    "<start>": ["<statement>"],
    "<statement>": [
        "{<declarations><statements>}",
        "if<paren_expr> <statement>",
        "if<paren_expr> <statement> else <statement>",
        "while<paren_expr> <statement>",
        "do <statement> while<paren_expr>;",
        "<expr>;",
        ";"
    ],
    "<statements>": ["", "<statement><statements>"],
    "<declarations>": ["", "<declaration><declarations>"],
    "<declaration>": [
        "int <id> = <expr>;",
        "int <id>;"
    ],
    "<paren_expr>": ["(<expr>)"],
    "<expr>": [
        "<test>",
        "<id> = <expr>"
    ],
    "<test>": [
        "<sum>",
        "<sum> < <sum>"
    ],
    "<sum>": [
        "<term>",
        "<sum> + <term>",
        "<sum> - <term>"
    ],
    "<term>": [
        "<id>",
        "<int>",
        "<paren_expr>"
    ],
    "<id>": srange(string.ascii_lowercase),
    "<int>": [
        "<digit>",
        "<digit_nonzero><digits>"
    ],
    "<digits>": [
        "<digit>",
        "<digit><int>"
    ],
    "<digit>": srange(string.digits),
    "<digit_nonzero>": list(set(srange(string.digits)) - {"0"}),
}


def compile_scriptsizec_clang(tree: isla.DerivationTree, outfile: Optional[IO] = None) -> Union[bool, str]:
    contents = "int main() {\n"
    contents += "\n" + str(tree).replace("\n", "    \t")
    contents += "\n" + "}"

    with tempfile.NamedTemporaryFile(suffix=".c") as tmp, tempfile.NamedTemporaryFile(suffix=".out") as _outfile:
        the_outfile = outfile or _outfile
        tmp.write(contents.encode())
        tmp.flush()
        cmd = ["clang", tmp.name, "-o", the_outfile.name]
        process = subprocess.Popen(cmd, stderr=PIPE)
        (stdout, stderr) = process.communicate(timeout=2)
        exit_code = process.wait()

        return True if exit_code == 0 else stderr.decode("utf-8")


fuzzer = GrammarCoverageFuzzer(SCRIPTSIZE_C_GRAMMAR)
success = 0
for _ in range(1000):
    prog = fuzzer.expand_tree(("<start>", None))
    result = compile_scriptsizec_clang(isla.DerivationTree.from_parse_tree(prog))
    if result is True:
        success += 1
        print(tree_to_string(prog))
    else:
        assert "use of undeclared" in result

print(success)
