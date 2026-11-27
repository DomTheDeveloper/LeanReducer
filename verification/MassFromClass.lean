import SampledGRH

open ArithmeticFunction ArithmeticFunction.vonMangoldt

/-- Dirichlet's theorem supplies the required divergent mass for every unit residue class. -/
theorem divergentPrimeMass_of_unit {M : ℕ} [NeZero M] {a : ZMod M} (unit : IsUnit a) :
    DivergentPrimeMass {n : ℕ | n.Prime ∧ (n : ZMod M) = a} := by
  classical
  intro summable
  apply not_summable_residueClass_prime_div unit
  apply summable.congr
  intro n
  by_cases prime : n.Prime
  · by_cases congruent : (n : ZMod M) = a <;>
      simp [prime, congruent, residueClass, Set.indicator, vonMangoldt_apply_prime]
  · simp [prime]

#print axioms divergentPrimeMass_of_unit
