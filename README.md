# A conditional RH and Dirichlet GRH proof in 982 physical source lines

The five original conclusions follow from a one-sided bound on the weighted prime error at fourth powers. At arbitrarily large factorial levels, it suffices to find a set of primes that are 7 modulo 8, coprime to the modulus, satisfy the prescribed bound, and have divergent sum of log(p)/p. The sample bound is an arithmetic hypothesis. [Exact statement](src/SampledGRH.lean) · [Divergence and the twist argument](src/Lib/Analytic/QuadraticTwist/ZeroFreeTwist.lean)

| What is counted | Lines |
| --- | ---: |
| Project Lean code, including imports | 957 |
| Physical lines in all 18 project source modules | 982 |
| Physical lines in the separate compatibility test | 18 |
| Physical lines in every checked-in Lean file | 1,000 |

The counts include every project dependency and exclude the pinned Lean and Mathlib. This edition retains every code-containing line from the [annotated source](https://github.com/DomTheDeveloper/LeanReducer/tree/9da2cf4778e7345398270c5a463313ae313432c6). Explanatory comments appear in [the module notes](SOURCE-NOTES.md). The four definitions in `Statements.lean` are byte-identical to the source edition.

Run `sha256sum -c SOURCE.sha256`, `lake exe cache get`, and `lake build`. The [verification workflow](https://github.com/DomTheDeveloper/LeanReducer/actions?query=branch%3Adivergent-primes-physical) checks the expanded arithmetic premise, all five conclusions, the three standard Lean axioms, every source module and the compatibility test against Dirichlet's theorem on primes in arithmetic progressions. [Full unconditional source](https://github.com/DomTheDeveloper/LeanReducer/tree/41bbac1c78e806eced8fd373f6cb55e77a045af5)
