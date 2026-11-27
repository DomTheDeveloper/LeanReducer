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

/-- The former factorial-level hypothesis supplies the free choice of modulus and precision. -/
theorem estimates_of_factorial_levels
    (old : ∀ lower : ℕ, ∃ k : ℕ, lower ≤ k ∧ ∃ positive : NeZero (18480*(k+1).factorial),
      @SampledGRH.EstimateAt (18480*(k+1).factorial) positive (1/((k:ℝ)+1))) :
    SampledGRH.Estimates := by
  intro q _ ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1/ε)
  obtain ⟨k, hk, positive, samples⟩ := old (max q n)
  have large := hk.trans (Nat.le_succ k)
  refine ⟨_, positive, dvd_mul_of_dvd_right
    (Nat.dvd_factorial (NeZero.pos q) ((le_max_left q n).trans large)) _, _, by positivity, ?_, ?_, samples⟩
  · rw [div_le_iff₀ (by positivity)]; simp
  · apply le_of_lt
    apply (one_div_lt (by positivity) hε).2
    exact hn.trans_le (by exact_mod_cast ((le_max_right q n).trans large))

#print axioms estimates_of_factorial_levels
