ISLa TODOs
==========

* Enforce invariant: 
  - Disjunctive normal form 
  - No variable bound by two different quantifiers (even on the same level)
* Add semantic predicates (e.g., checksums)
* Add aggregations, e.g. sum, count.
* Add further structural predicates, e.g., "inside / below"
* Evaluate different heuristics for next state selection (or some randomization? Then, one could, e.g., earlier on
  explore longer derivations...)
* Evaluate how good it works to first generate a lot of trees and only then apply quantifiers etc. Is it quicker /
  leading to more diverse inputs?