# Nonvanishing on bounded factorial levels

The theorem `LeanReducer.factorial_critical_boxes_iff` states that zero-freeness of all Dirichlet L-functions to the right of the critical line, with the usual principal-character pole exception, is equivalent to a family of bounded critical-strip tests. At level `M(k) = 18480 (k+1)!`, test every character only on `1/2 + 1/(k+1) ≤ Re(s) < 1` and `|Im(s)| ≤ k`. The usual nonvanishing theorem handles real parts at least one. Finitely bounded height at each level still leaves an infinite sequence of tests.

Run `lake exe cache get`, `lake build`, `lake env leanchecker FactorialLevels` and `lake env leanchecker FactorialBoxes`. This project uses the original Lean 4.35 and Mathlib pins. [Workflow results](https://github.com/DomTheDeveloper/LeanReducer/actions/workflows/verify.yml) · [LeanReducer study](https://github.com/DomTheDeveloper/LeanReducer/blob/main/examples/grh/REDUCTION-STUDY.md)
