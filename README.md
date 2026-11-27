# A fourth-power sampling criterion for the Dirichlet weighted prime error

This standalone Lean project proves `PrimeErrorFourthPowers.bounds_iff` for the actual `primeError d M` in the compact GRH formalization. For every prime d and every positive modulus M, the family of eventual upper bounds with exponents strictly between −½ and 0 holds on natural fourth powers exactly when it holds for all sufficiently large positive real inputs.

The project contains **849 nonblank, noncomment code lines and 1,260 physical lines in 12 Lean modules**, above the pinned Lean 4.35.0 toolchain and Mathlib revision. Eight upstream modules (649 code lines) supply the prime-error definition, its finite-sum identity, and nonnegativity of its weights. Three modules (176 lines) prove the abstract interpolation and sampling results. One module (24 lines) applies them. The theorem gives a conditional analytic step. An unconditional RH or Dirichlet GRH proof also needs the arithmetic estimates.

## Build and replay

Run these commands from the project root.

```sh
lake exe cache get
lake build
lake env lean src/PrimeErrorFourthPowers.lean
lake env leanchecker PrimeErrorFourthPowers
sha256sum -c SOURCE.sha256
```

The expected axioms are `propext`, `Classical.choice` and `Quot.sound`. The source inventory covers every Lean file under `src`. The build configuration retains the exact upstream Mathlib pin and library declarations needed for the twelve included modules.

[Native build and check against the upstream declarations](https://github.com/DomTheDeveloper/LeanReducer/actions/runs/45984868143) · [Reduction study](https://github.com/DomTheDeveloper/LeanReducer/blob/595c94bd7d80764c31daffabb5f35d556f086f5a/examples/grh/RESULTS.md) · [Upstream compact proof](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact)
