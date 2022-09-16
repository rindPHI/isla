# Here, we define the grammar for the assignment language as a Python program. While
# in general, definitions in BNF might be slightly better readable and have a well-known
# syntax, the Python variant allows creating expansion alternatives programmatically.
# This comes handy, e.g., if you want to include all ASCII lower-case characters, as
# in the example below, without typing them.
#
# Python grammars must assign a variable `grammar` of type `Dict[str, List[str]]`.
# Be aware that the ISLa CLI *executes* Python grammar files; consequently, make sure
# that no harmful code is included.

import string
from typing import List, Dict

grammar: Dict[str, List[str]] = {
    "<start>": ["<stmt>"],
    "<stmt>": ["<assgn> ; <stmt>", "<assgn>"],
    "<assgn>": ["<var> := <rhs>"],
    "<rhs>": ["<var>", "<digit>"],
    "<var>": list(string.ascii_lowercase),
    "<digit>": list(string.digits),
}
