# This partial grammar defines the nonterminals `<rhs>`, `<var>`, and `<digit>`. While
# in general, definitions in BNF might be slightly better readable and have a well-known
# syntax, the Python variant allows creating expansion alternatives programmatically.
# This comes handy, e.g., if you want to include all ASCII lower-case characters, as
# in the example below, without typing them.
#
# Python grammars need to assign a variable `grammar` of type `Dict[str, List[str]]`.
# Be aware that the ISLa CLI *executes* Python grammar files; consequently, make sure
# that no harmful code is included.

import string

grammar = {
    "<start>": ["<stmt>"],
    "<stmt>": ["<assgn> ; <stmt>", "<assgn>"],
    "<assgn>": ["<var> := <rhs>"],
    "<rhs>": ["<var>", "<digit>"],
    "<var>": list(string.ascii_lowercase),
    "<digit>": list(string.digits),
}
