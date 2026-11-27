# RH and Dirichlet GRH from one fourth-power estimate per factorial level

The standalone theorem `SampledGRH.five_endpoints` takes one explicit arithmetic premise. For every natural k, let q = (k+1)! and M = 18480q. For every prime d congruent to 9240q−1 modulo M, the upstream weighted prime error at n⁴ is eventually bounded above by (n⁴) raised to the single exponent −1/2 + 1/(4(k+1)). The threshold may depend on k and d. From that family the theorem derives all five original public RH and Dirichlet GRH conclusions.

The entire local proof contains **985 code lines, 1348 physical lines and 19 modules**. Lean and the pinned Mathlib dependency sit outside both counts. The remaining missing part of a short unconditional proof is the arithmetic estimate itself. The proof uses slack between its sample exponent and the analytic exponent −1/2 + 1/(k+1), applies the one-sided prime-sum criterion, then passes from the factorial levels to every positive modulus.

Run `lake exe cache get`, `lake build`, and `lake env leanchecker SampledGRH`. The file `SOURCE.sha256` covers all local Lean modules. [Previous criterion with a family of exponents per level](https://github.com/DomTheDeveloper/LeanReducer/tree/e9e575e17cead892a1047ae30da86098ce967cc3) · [Complete unconditional source](https://github.com/DomTheDeveloper/LeanReducer/tree/41bbac1c78e806eced8fd373f6cb55e77a045af5)
