# Conditional RH and Dirichlet GRH from an unbounded set of factorial levels

The public statement is `SampledGRH.five_endpoints`. It takes one arithmetic premise and derives the five RH and Dirichlet GRH conclusions from the original challenge.

For a natural level k put q=(k+1)! and M=18480q. Call k good when, for every prime d congruent to 9240q−1 modulo M, the actual weighted prime error at n⁴ is at most (n⁴) raised to −1/2+1/(4(k+1)), for all sufficiently large natural n. The threshold may depend on k and d. The premise requires a good k above each natural threshold. It permits gaps of arbitrary size between good levels.

To handle a character of modulus m and a point with real part strictly above one half, choose a good k beyond m and beyond the size needed for 1/(k+1) to fit the real margin. The factorial is divisible by m. The sampled bound and the one-sided criterion give nonvanishing at the lifted character, and the Euler factors transfer it back to m.

The entire local source is **976 code lines, 1,338 physical lines and 19 modules** above the pinned Lean and Mathlib. The arithmetic premise still requires a proof in an unconditional version. Holding these 976 lines fixed leaves 49,024 code lines for additional arithmetic and its dependencies at the 50,000-line budget, or 24 at the 1,000-line budget.

Run `sha256sum -c SOURCE.sha256`, `lake exe cache get`, and `lake build`. The workflow also checks the explicit unbounded-level implication, requires the three standard axioms, and replays each local module. [Build and kernel replay](https://github.com/DomTheDeveloper/LeanReducer/actions?query=branch%3Acofinal-sampled-grh) · [Previous criterion using every factorial level](https://github.com/DomTheDeveloper/LeanReducer/tree/680cdffe8dca5e2f3de405a615318d0989f0f055) · [Complete unconditional candidate](https://github.com/DomTheDeveloper/LeanReducer/tree/41bbac1c78e806eced8fd373f6cb55e77a045af5)
