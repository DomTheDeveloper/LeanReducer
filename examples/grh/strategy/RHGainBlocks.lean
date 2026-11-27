import RHFiniteGain

open Finset

namespace FixedClassRH

/-- Terms before x have one common coefficient. Between x and y only the first
reciprocal depends on n. All terms past y vanish. -/
theorem gainTerm_eq_blocks (d M A n : ℕ) [Fact d.Prime] {x y : ℝ}
    (hA : 0 < A) (hn : 0 < n) (hx : 0 < x) (hxy : x ≤ y) :
    gainTerm d M A n x y = lambdaClass d M n *
      (if (n : ℝ) ≤ x then 1 / x - 1 / y else if (n : ℝ) ≤ y then 1 / (n : ℝ) - 1 / y else 0) := by
  have a0 : 0 < (A : ℝ) := by exact_mod_cast hA
  have n0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have y0 := hx.trans_le hxy
  have on {v : ℝ} (h : 0 ≤ v) : v⁺ = v := sup_eq_left.mpr h
  have off {v : ℝ} (h : v ≤ 0) : v⁺ = 0 := sup_eq_right.mpr h
  have xy := div_le_div_of_nonneg_left a0.le hx hxy
  unfold gainTerm
  by_cases nx : (n : ℝ) ≤ x
  · have lower := div_le_div_of_nonneg_left a0.le n0 nx
    rw [if_pos nx, on (sub_nonneg.mpr (xy.trans lower)), on (sub_nonneg.mpr lower)]
    field_simp [a0.ne', n0.ne', hx.ne', y0.ne'] <;> ring
  · have lower := div_le_div_of_nonneg_left a0.le hx (le_of_not_ge nx)
    rw [if_neg nx, off (sub_nonpos.mpr lower)]
    by_cases ny : (n : ℝ) ≤ y
    · rw [if_pos ny, on (sub_nonneg.mpr (div_le_div_of_nonneg_left a0.le n0 ny))]
      field_simp [a0.ne', n0.ne', y0.ne'] <;> ring
    · rw [if_neg ny, off (sub_nonpos.mpr (div_le_div_of_nonneg_left a0.le y0 (le_of_not_ge ny)))]
      ring

theorem weightedGain_eq_blocks (d M A : ℕ) [Fact d.Prime] {x y : ℝ}
    (hA : 0 < A) (hx : 0 < x) (hxy : x ≤ y) :
    weightedGain d M A x y = ∑ n ∈ Icc 1 A, lambdaClass d M n *
      (if (n : ℝ) ≤ x then 1 / x - 1 / y else if (n : ℝ) ≤ y then 1 / (n : ℝ) - 1 / y else 0) := by
  apply sum_congr rfl
  intro n hn
  exact gainTerm_eq_blocks d M A n hA (mem_Icc.mp hn).1 hx hxy

/-- A finite set of inert primes in the selected residue class gives an explicit lower bound.
The stage below x pays the same coefficient for every prime. -/
theorem inertPrimeBlocks_le (d M A : ℕ) [Fact d.Prime] {x y : ℝ}
    (hA : 0 < A) (hx : 0 < x) (hxy : x ≤ y) {S : Finset ℕ} (hS : S ⊆ Icc 1 A)
    (selected : ∀ p ∈ S, p.Prime ∧ (p : ZMod M) = 1 ∧ chiK d p = -1) :
    ∑ p ∈ S, 2 * Real.log p *
      (if (p : ℝ) ≤ x then 1 / x - 1 / y else if (p : ℝ) ≤ y then 1 / (p : ℝ) - 1 / y else 0) ≤
        weightedGain d M A x y := by
  apply lower_bound_from_subset d M A hx hxy hS
  intro p hp
  obtain ⟨prime, residue, inert⟩ := selected p hp
  rw [gainTerm_eq_blocks d M A p hA prime.pos hx hxy]
  have value : lambdaClass d M p = 2 * Real.log p := by
    simp [lambdaClass, ArithmeticFunction.vonMangoldt.residueClass, Set.indicator, residue,
      inert, ArithmeticFunction.vonMangoldt_apply_prime prime] <;> ring
  simp [value]

end FixedClassRH
