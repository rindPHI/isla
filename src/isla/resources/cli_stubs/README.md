# Inputs to the ISLa Solver CLI

The ISLa solver/checker CLI accepts multiple grammar and constraint files to generate
or check inputs. In the presence of multiple grammar files, they are merged to a single
grammar; multiple constraints are combined to a conjunction.

This stub project defines grammar and constraint files for a simple assignment language,
which comprises words like `x := 1 ; y := x`. The project contains the following files:

- `{grammar_1_file.name}` contains the assignment grammar in
  standard [BNF](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form) notation.
- `{grammar_2_file.name}` specifies the assignment grammar as a Python
  program. This permits for more concise notations if you need to include many terminal
  values in your grammar. You find more information on this format in the
  [Fuzzing Book](https://www.fuzzingbook.org/html/Grammars.html).
- `{constraint_file.name}` contains examples of different types ISLa constraints one 
  can express over the assignment language. 

All the above files contain comments with additional explanations.

By running the command

```bash
isla solve \
  -s 1 -f 1 -t 10 -n -1 \
  {grammar_1_file.name} \
  {constraint_file.name}
```

you obtain as many solutions to the currently specified (and uncommented) constraints
as the solver can come up with within 10 seconds (because of the `-t 10` argument,
which imposes a 10 seconds timeout).
