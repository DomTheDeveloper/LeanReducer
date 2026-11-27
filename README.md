# A conditional proof using an auxiliary multiple of each conductor

For each positive conductor q and requested accuracy ε > 0, choose any positive multiple M of q and a number 0 < δ ≤ min(1,ε). At that modulus suppose a set of primes 7 modulo 8 and coprime to M has divergent sum of log(p)/p. For each prime d in this set, suppose the weighted prime error at n⁴ is at most (n⁴)^(−1/2+δ/4) for all sufficiently large n. This arithmetic hypothesis implies the five original RH and Dirichlet GRH statements. The multiple, exponent and prime set can depend on the conductor and requested accuracy. [Exact Lean statement](src/SampledGRH.lean)

The analytic proof finds a zero-free twist among a sufficiently large family of admissible primes. Interpolation recovers a bound between fourth powers. Choosing ε inside the distance of a proposed zero from the critical line permits a direct change of level from M to q. An independent Lean compatibility proof shows that unbounded good factorial levels imply this more flexible premise. [Compatibility proofs](verification/MassFromClass.lean) · [Source notes](SOURCE-NOTES.md)

| What is counted | Lines |
| --- | ---: |
| Project code in all 17 imported modules | 927 |
| Physical lines in the same project closure | 951 |
| Physical lines in the separate compatibility tests | 36 |
| Physical lines in every checked-in Lean file | 987 |

All project-owned dependencies are included. The pinned Lean toolchain and Mathlib are external. Explanatory comments have been moved to the module notes, preserving the code-containing lines. The short project takes the arithmetic estimates as hypotheses. The complete unconditional source obtains them through its covolume comparison. [Full unconditional source](https://github.com/DomTheDeveloper/LeanReducer/tree/41bbac1c78e806eced8fd373f6cb55e77a045af5) · [Earlier proof with fixed factorial levels](https://github.com/DomTheDeveloper/LeanReducer/tree/b95fc6679ddb55033c7d11a62bfbb832b7f1812b)

Run `sha256sum -c SOURCE.sha256`, `lake exe cache get`, and `lake build`. The workflow checks the expanded arithmetic premise and endpoint types, audits the permitted axioms, checks both compatibility theorems, and replays every project module. [Build status](https://github.com/DomTheDeveloper/LeanReducer/actions?query=branch%3Aauxiliary-multiples-grh)
