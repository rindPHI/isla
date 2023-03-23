ISLa: *Inputs on Demand!*
=========================

.. note::
   This page is under construction.

ISLa is a *grammar-aware string constraint solver* with its own specification language.
With ISLa, it is possible to specify *input constraints* like "a variable has to be
defined before it is used," "the 'file name' block must be 100 bytes long," or "the
number of columns in all CSV rows must be identical."

Building on modern constraint solvers, ISLa provides you with a unique
flexibility to specify—and generate—the system inputs you need. ISLa can be
used for *precise fuzzing:* Keep adding input specifications until you are satisfied
with the number of inputs passing the tested system's parser. Furthermore, you can write
ISLa specifications to carve out specific inputs for testing a *particular program
functionality*.

Example
-------

Our running example is a simple "assignment language" consisting of strings such as
:code:`x := 1 ; y := x`. As a first step towards using ISLa, we formalize this language as
a context-free grammar in `BNF <https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form>`_:

.. code-block:: bnf

   <start> ::= <stmt>
   <stmt>  ::= <assgn> | <assgn> " ; " <stmt>
   <assgn> ::= <var> " := " <rhs>
   <rhs>   ::= <var> | <digit>
   <var>   ::= "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" |
               "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" |
               "u" | "v" | "w" | "x" | "y" | "z"
   <digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"

After saving this grammar to a file, say, :code:`assgn.bnf`, we can already generate inputs
from the assignment grammar using the ISLa command line interface:

.. code-block:: bash

   > isla solve assgn.bnf
   s := t

The following command creates 10 assignments:

.. code-block:: bash

   > isla solve -n 10 assgn.bnf
   a := 6 ; j := x
   q := u
   e := h ; o := l ; g := w
   s := i
   k := v ; d := m ; f := 1
   n := y ; t := 5
   z := 3 ; p := 7 ; b := 0
   c := 2 ; r := 4
   q := 8 ; l := 9
   u := 0

With ISLa, we can restrict the assignment language on-demand. For example, the ISLa
constraint :code:`<var> = "a"` results in assignment sequences only containing "a" variables:

.. code-block:: bash

   > isla solve assgn.bnf -n 10 -f 1 --constraint '<var> = "a"'
   a := 5 ; a := a ; a := 7
   a := 6
   a := a
   a := 0 ; a := a ; a := a
   a := a ; a := 1 ; a := 4
   a := a ; a := 3 ; a := a
   a := 8 ; a := 2
   a := 9 ; a := a
   a := a ; a := 9
   a := a ; a := a

.. note::

   The setting :code:`-f 1` restricts the number of times that ILSa randomly
   instantiates unconstrained input elements to one time. Here, this affects the
   :code:`<digit>` nonterminals: Without :code:`-f 1`, we would see 10 different variants of the
   first input with variying numbers in the first and third assignment.

Or do we prefer assignments where all digits can be divided by 2 without remainder? No
problem with ISLa:

.. code-block:: bash

   > isla solve assgn.bnf -n 10 -f 1 -s 2 --constraint "str.to.int(<digit>) mod 2 = 0"
   i := a ; x := 0 ; u := s
   p := l ; m := 8 ; b := y
   k := c ; t := d ; r := q
   j := z
   h := 0
   e := 4
   g := n ; v := f ; w := 4
   o := o ; j := a ; c := 0
   t := r ; k := 0 ; e := 0
   k := t ; f := 8 ; e := 8

.. note::

   The :code:`-s` flag specifies how many results for a single query should be obtained
   from the SMT solver Z3. We limited this number to 2 (the default is 10—the same
   default value is used for the :code:`-f` flag) to obtain a wider diversity of inputs within
   the first 10 results.

The constraints above talk over *all* :code:`<var>` and :code:`<digit>` grammar nonterminals in
any derivation tree derived from the assignment language grammar. In addition to such
simple constraints, ISLa allows to explicitly *quantify* over grammar elements using
the :code:`forall` and :code:`exists` keywords.

Assume that an interpreter for our assignment language rejects inputs where a variable
is accessed that has not been previously assigned a value. This "definition-use"
property, which is a *semantic input property* of the language, is expressed as follows:

.. code-block::

  forall <assgn> assgn_1:
    exists <assgn> assgn_2: (
      before(assgn_2, assgn_1) and
      assgn_1.<rhs>.<var> = assgn_2.<var>)

Since this is a more lengthy constraint, let us save it in a file :code:`defuse.isla`. The
following command line invocation uses this constraint:

.. code-block:: bash

   > isla solve -n 10 -f 1 -s 1 assgn.bnf defuse.isla
   q := 2 ; m := 1 ; c := 4
   p := 8 ; o := 3 ; l := p
   z := 7 ; p := 6 ; e := p
   d := 5 ; a := d ; h := 9
   s := 0 ; x := 0
   k := 8
   p := 4 ; r := p
   p := 6 ; u := p
   p := 5 ; v := p
   p := 3 ; p := 5 ; w := p

As we can see, all right-hand side variables occur at the left-hand side of a prior
assignment.

For more information on the command line interface, run :code:`isla -h`. Each sub command
comes with its own help text; for example, :code:`isla solve -h` provides details on how to
use the :code:`solve` command.

You can also use the ISLa solver via its Python API:

.. code-block:: python

   from isla.solver import ISLaSolver

   grammar = '''
   <start> ::= <stmt>
   <stmt>  ::= <assgn> | <assgn> " ; " <stmt>
   <assgn> ::= <var> " := " <rhs>
   <rhs>   ::= <var> | <digit>
   <var>   ::= "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" |
               "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" |
               "u" | "v" | "w" | "x" | "y" | "z"
   <digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
   '''

   constraint = """
   forall <assgn> assgn_1:
     exists <assgn> assgn_2: (
       before(assgn_2, assgn_1) and
       assgn_1.<rhs>.<var> = assgn_2.<var>)
   """

   solver = ISLaSolver(
       grammar=grammar,
       formula=constraint,
       max_number_free_instantiations=1,  # -f
       max_number_smt_instantiations=1,  # -s
   )

   for _ in range(10):
       print(solver.solve())

An example output of the above program snippet is:

.. code-block::

   q := 7 ; m := 1 ; c := 8
   p := 2 ; o := 2 ; l := p
   z := 9 ; p := 4 ; e := p
   d := 8 ; a := d ; h := 5
   s := 0 ; x := 0
   k := 7
   p := 8 ; r := p
   p := 9 ; u := p
   p := 4 ; v := p
   p := 2 ; p := 1 ; w := p

Useful Resources
----------------

You want to try ISLa out for your own examples, or need more inspiration? Then, we
recommend our
`interactive ISLa tutorial <https://www.fuzzingbook.org/beta/html/FuzzingWithConstraints.html>`_
providing an easily accessible introduction to the specification and generation of custom system
inputs using ISLa.

You might also like our :code:`isla create` command: :code:`isla create path` creates a set of
grammar and constraint files along with a README file at the path :code:`path`. All files are
contain explaining comments to help you getting started; we show different constraints
for the assignment language that you can experiment with.

For diving deeper into ISLa, we recommend the following resources.

* See :doc:`usage` to get started with ISLa.

* :doc:`/examples` provides additional examples of ISLa specifications.

* The :doc:`/developing/index` contains material to get you started with ISLa's code.

* :doc:`/islaspec` precisely specifies the syntax and semantics of ISLa constraints.
  The specification also contains a list of supported default predicates.

* Our `scientific paper on ISLa <https://publications.cispa.saarland/3596/7/Input%20Invariants.pdf>`_,
  published at ESEC/FSE 2022. The paper describes the ISLa language and solver more
  formally.

* In the directory
  `src/isla_formalizations/ <https://github.com/rindPHI/isla/tree/main/src/isla_formalizations>`_,
  you find our specifications for the subject languages of our experimental evaluation.

* The files :code:`run_eval_csv.fish`, :code:`run_eval_tar.fish`, and so on, are the scripts we used
  to collect and analyze our evaluation data. To analyze ISLa's current performance
  yourself, you can run the scripts with the :code:`-h` argument to obtain some guidance on
  their parameters (the fish shell is required to use these scripts).

Indices and tables
------------------

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`

.. toctree::
   :maxdepth: 2
   :caption: Contents

   usage
   examples
   islaspec
   developing/index
