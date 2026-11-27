# Conditional RH and Dirichlet GRH from divergent sets of primes

Let M = 18480(k+1)!. For arbitrarily large natural k, suppose that there is a set S of natural numbers for which the sum of log(p)/p over the primes p in S diverges. Each such prime must satisfy p ≡ 7 mod 8, gcd(p,M) = 1, and the eventual fourth-power upper bound on the actual upstream prime error at exponent −1/2 + 1/(4(k+1)). The threshold in the sampled variable can depend on k and p. This is the arithmetic premise of the branch.

The proof uses a power-saving zero-density estimate for the exceptional quadratic twists. If every selected prime were exceptional at a given height, their log(p)/p sum would converge. A nonexceptional twist and Landau’s criterion give nonvanishing, and the factorial-level argument and functional equations give all five public statements. The code includes the zero-density derivation. The mathematical outline and references to the original strategy are retained in the source.

This branch contains the 950-code-line implication in 18 local modules and 975 physical Lean lines. The recorded build checks source digests, the explicit implication, the axioms and every local module on Lean 4.35.0 and the original Mathlib revision. [Verification run](https://github.com/DomTheDeveloper/LeanReducer/actions?query=branch%3Adivergent-prime-compact) · [Previously verified 976-line implication](https://github.com/DomTheDeveloper/LeanReducer/tree/ae21d67f172b180b660d9bfa2183e3f806ab0ef2)

Run `sha256sum -c SOURCE.sha256`, `lake exe cache get` and `lake build` from the repository root. The arithmetic premise still needs a short unconditional proof.

The annotated project has 1,304 physical lines. The compact edition preserves every line containing executable Lean and the original statement file. Standalone comments are in [SOURCE-NOTES.md](SOURCE-NOTES.md). [Annotated project and its completed kernel replay](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45994270811)
