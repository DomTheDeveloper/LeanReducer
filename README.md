# Conditional RH and Dirichlet GRH from fourth-power estimates

This project proves `SampledGRH.Estimates →` the conjunction of the five public RH and Dirichlet GRH conclusions. The arithmetic hypothesis requires eventual upper bounds for the upstream weighted prime error on fourth powers of natural numbers in one auxiliary residue class at each factorial modulus. Proving that hypothesis remains open in the short project.

The closure contains **998 code lines and 1365 physical lines in 19 local modules** above the frozen Lean and Mathlib dependency. The source inventory covers every project-owned Lean file. The project removes algebraic and adelic declarations outside this conditional proof, retains its actual analytic definitions and proofs, and preserves the upstream licenses and attribution.

Run `lake exe cache get`, `lake build` and `lake env leanchecker SampledGRH`. The output of `#print axioms SampledGRH.five_endpoints` is audited in the workflow. Its public statements are defined in the original `Statements.lean`. Verification status is available in [the branch builds](https://github.com/DomTheDeveloper/LeanReducer/actions/workflows/conditional.yml). [Unconditional full source](https://github.com/DomTheDeveloper/LeanReducer/tree/41bbac1c78e806eced8fd373f6cb55e77a045af5)
