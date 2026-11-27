import New.Main
-- The proof is Levent Alpöge's, with Claude.

-- LeanReducer change: use the public zeta and Dirichlet results from New.Main.
theorem riemannHypothesis : RiemannHypothesis := riemannZeta_eq_zero_re

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine :=
  fun N _ χ _ ↦ LFunction_eq_zero_re N χ
