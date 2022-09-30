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

import string
import subprocess
import tempfile
from typing import Union

import isla.derivation_tree
from isla.helpers import srange
from isla.isla_predicates import COUNT_PREDICATE
from isla.language import parse_isla

CSV_GRAMMAR = {
    "<start>": ["<csv-file>"],
    "<csv-file>": ["<csv-header><csv-records>"],
    "<csv-header>": ["<csv-record>"],
    "<csv-records>": ["<csv-record><csv-records>", ""],
    "<csv-record>": ["<csv-string-list>\n"],
    "<csv-string-list>": ["<raw-field>", "<raw-field>;<csv-string-list>"],
    "<raw-field>": ["<simple-field>", "<quoted-field>"],
    "<simple-field>": ["<spaces><simple-characters><spaces>"],
    "<simple-characters>": [
        "<simple-character><simple-characters>",
        "<simple-character>",
    ],
    "<simple-character>": [
        c
        for c in srange(string.printable)
        if c not in ["\n", ";", '"', " ", "\t", "\r", '"']
    ],
    "<quoted-field>": ['"<escaped-field>"'],
    "<escaped-field>": ["<escaped-characters>"],
    "<escaped-characters>": ["<escaped-character><escaped-characters>", ""],
    "<escaped-character>": [c for c in srange(string.printable) if c not in ['"']],
    "<spaces>": ["", " <spaces>"],
}

CSV_HEADERBODY_GRAMMAR = {
    "<start>": ["<csv-file>"],
    "<csv-file>": ["<csv-header><csv-body>"],
    "<csv-header>": ["<csv-record>"],
    "<csv-body>": ["<csv-records>"],
    "<csv-records>": ["<csv-record><csv-records>", ""],
    "<csv-record>": ["<csv-string-list>\n"],
    "<csv-string-list>": ["<raw-field>", "<raw-field>;<csv-string-list>"],
    "<raw-field>": ["<simple-field>", "<quoted-field>"],
    "<simple-field>": ["<spaces><simple-characters><spaces>"],
    "<simple-characters>": [
        "<simple-character><simple-characters>",
        "<simple-character>",
    ],
    "<simple-character>": [
        c
        for c in srange(string.printable)
        if c not in ["\n", ";", '"', " ", "\t", "\r", '"']
    ],
    "<quoted-field>": ['"<escaped-field>"'],
    "<escaped-field>": ["<escaped-characters>"],
    "<escaped-characters>": ["<escaped-character><escaped-characters>", ""],
    "<escaped-character>": [c for c in srange(string.printable) if c not in ['"']],
    "<spaces>": ["", " <spaces>"],
}


def csv_lint(tree: isla.derivation_tree.DerivationTree) -> Union[bool, str]:
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


# csv_colno_property = """
# forall <csv-header> hline in start:
#   exists int colno:
#     ((>= (str.to.int colno) 3) and
#     ((<= (str.to.int colno) 5) and
#      (count(hline, "<raw-field>", colno) and
#      forall <csv-record> line in start:
#        count(line, "<raw-field>", colno))))"""

csv_colno_property = """
exists int num:
  forall <csv-record> elem in start:
    (str.to.int(num) >= 1 and
     count(elem, "<raw-field>", num))"""

CSV_COLNO_PROPERTY = parse_isla(
    csv_colno_property, CSV_GRAMMAR, semantic_predicates={COUNT_PREDICATE}
)
