import string
import subprocess
import tempfile
from typing import Union

from fuzzingbook.Grammars import convert_ebnf_grammar, srange

from input_constraints import isla
from input_constraints.isla import parse_isla
from input_constraints.isla_predicates import COUNT_PREDICATE

CSV_EBNF_GRAMMAR = {
    "<start>": ["<csv-file>"],
    "<csv-file>": ["<csv-header><csv-record>*"],
    "<csv-header>": ["<csv-record>"],
    "<csv-record>": ["<csv-string-list>\n"],
    "<csv-string-list>": ["<raw-field>", "<raw-field>;<csv-string-list>"],
    "<raw-field>": ["<simple-field>", "<quoted-field>"],
    "<simple-field>": ["<spaces>?<simple-character>*<spaces>?"],
    "<simple-character>": [c for c in srange(string.printable) if c not in ["\n", ";", '"', " ", "\t", "\r", '"']],
    "<quoted-field>": ['"<escaped-field>"'],
    "<escaped-field>": ["<escaped-character>*"],
    "<escaped-character>": [c for c in srange(string.printable) if c not in ['"']],
    "<spaces>": [" ", " <spaces>"],
}

CSV_GRAMMAR = convert_ebnf_grammar(CSV_EBNF_GRAMMAR)


def csv_lint(tree: isla.DerivationTree) -> Union[bool, str]:
    with tempfile.NamedTemporaryFile(suffix=".csv") as tmp:
        tmp.write(str(tree).encode())
        tmp.flush()
        # csvlint from https://github.com/Clever/csvlint/releases
        cmd = ["csvlint", "-delimiter", ";", tmp.name]
        process = subprocess.Popen(cmd, stderr=subprocess.PIPE)
        (stdout, stderr) = process.communicate()
        exit_code = process.wait()

        err_msg = stderr.decode("utf-8")

        has_error = exit_code != 0 or (bool(err_msg) and not "valid" in err_msg)

        if has_error:
            print(err_msg)

        return True if not has_error else err_msg


csv_colno_property = """
const start: <start>;

vars {
  colno: NUM;
  hline: <csv-header>;
  line: <csv-record>;
}

constraint {
  forall hline in start:
    num colno:
      ((>= (str.to_int colno) 3) and 
      ((<= (str.to_int colno) 5) and 
       (count(hline, "<raw-field>", colno) and 
       forall line in start:
         count(line, "<raw-field>", colno))))
}
"""

CSV_COLNO_PROPERTY = parse_isla(csv_colno_property, semantic_predicates={COUNT_PREDICATE})
