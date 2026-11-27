import RHNormalized

open Filter Real Finset

namespace FixedClassRH
open Cutoff

/-- Increase in the weighted prime count from x to y at a common cutoff A. -/
noncomputable def gainTerm (d M A n : ℕ) [Fact d.Prime] (x y : ℝ) : ℝ :=
  lambdaClass d M n * (((A : ℝ) / n - A / y)⁺ - ((A : ℝ) / n - A / x)⁺) / A

noncomputable def weightedGain (d M : ℕ) [Fact d.Prime] (A : ℕ) (x y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 A, gainTerm d M A n x y

theorem gainTerm_nonneg (d M A n : ℕ) [Fact d.Prime] {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    0 ≤ gainTerm d M A n x y := by
  have order : (A : ℝ) / y ≤ A / x := div_le_div_of_nonneg_left (Nat.cast_nonneg A) hx hxy
  have weight : ((A : ℝ) / n - A / x)⁺ ≤ ((A : ℝ) / n - A / y)⁺ :=
    sup_le_sup (sub_le_sub_left order _) le_rfl
  exact div_nonneg (mul_nonneg (lambdaClass_nonneg_and_abs_le d M n).1
    (sub_nonneg.mpr weight)) (Nat.cast_nonneg A)

theorem weightedGain_nonneg (d M A : ℕ) [Fact d.Prime] {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    0 ≤ weightedGain d M A x y :=
  sum_nonneg (fun n _ ↦ gainTerm_nonneg d M A n hx hxy)

/-- It suffices to lower-bound contributions on a chosen subset, for example disjoint blocks
of primes. The discarded terms contribute nonnegatively. -/
theorem lower_bound_from_subset (d M A : ℕ) [Fact d.Prime] {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    {S : Finset ℕ} (hS : S ⊆ Icc 1 A) {minorant : ℕ → ℝ}
    (leTerm : ∀ n ∈ S, minorant n ≤ gainTerm d M A n x y) :
    ∑ n ∈ S, minorant n ≤ weightedGain d M A x y :=
  (sum_le_sum leTerm).trans (sum_le_sum_of_subset_of_nonneg hS
    (fun n _ _ ↦ gainTerm_nonneg d M A n hx hxy))

/-- At the common cutoff, subtracting the two prime errors cancels the constant exactly. -/
theorem primeError_sub_eq_gain (d M A : ℕ) [Fact d.Prime] [NeZero M] {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hyA : y ≤ A) :
    primeError d M x - primeError d M y =
      (log y - log x) / M.totient - weightedGain d M A x y := by
  rw [primeError_eq_sum A hx (hxy.trans hyA), primeError_eq_sum A (hx.trans_le hxy) hyA]
  simp only [weightedGain, gainTerm, mul_sub, sub_div, sum_sub_distrib]
  ring

noncomputable def Cutoff.AuxiliaryData.requiredGain {P : Parameters} {cutoff : ℝ}
    (D : AuxiliaryData P cutoff) : ℝ :=
  (D.logX₁ - D.logX) / P.N₀.totient + D.weight * primeError P.d 1 (exp D.logX₁) -
    P.N₀.totient * D.weight * D.logB ^ 5 / D.m

/-- The comparison on a single window is exactly a lower bound on a nonnegative sum.
Windows with a nonpositive required gain are automatic. -/
theorem normalized_iff_gain {P : Parameters} {cutoff : ℝ} (D : AuxiliaryData P cutoff) :
    (primeError P.d P.N₀ (exp D.logX) -
        (primeError P.d P.N₀ (exp D.logX₁) - D.weight * primeError P.d 1 (exp D.logX₁)) ≤
        P.N₀.totient * D.weight * D.logB ^ 5 / D.m) ↔
    (0 < D.requiredGain → D.requiredGain ≤
      weightedGain P.d P.N₀ ⌈exp D.logX₁⌉₊ (exp D.logX) (exp D.logX₁)) := by
  have hx : 0 ≤ D.logX := by linarith only [D.s_le, (Nat.cast_nonneg D.s : (0 : ℝ) ≤ D.s)]
  have hxy : exp D.logX ≤ exp D.logX₁ :=
    exp_le_exp.mpr (by linarith only [hx, D.scale.2.2.1])
  have h := primeError_sub_eq_gain P.d P.N₀ _ (exp_pos D.logX) hxy (Nat.le_ceil _)
  simp only [log_exp] at h
  constructor
  · intro upper _
    unfold Cutoff.AuxiliaryData.requiredGain
    linarith only [upper, h]
  · intro lower
    have goalBound : D.requiredGain ≤ weightedGain P.d P.N₀ ⌈exp D.logX₁⌉₊
        (exp D.logX) (exp D.logX₁) := by
      by_cases positive : 0 < D.requiredGain
      · exact lower positive
      · exact (le_of_not_gt positive).trans (weightedGain_nonneg _ _ _ (exp_pos _) hxy)
    unfold Cutoff.AuxiliaryData.requiredGain at goalBound
    linarith only [goalBound, h]

/-- An arithmetic proof needs only supply the weighted gain on favorable, positive-target windows. -/
def FiniteGainEstimate : Prop :=
  ∀ P : Parameters, P.N₀ = 18480 → ∃ cutoff : ℝ, ∀ D : AuxiliaryData P cutoff,
    (towerDeg D.s : ℝ) / D.logB ≤ #D.thick →
    D.logX₁ ≤ (1e6 * D.logX) ^ 2 →
    primeError P.d P.N₀ (exp D.logX₁) - D.weight * primeError P.d 1 (exp D.logX₁) ≤
      exp (-(1e6 * D.logX)) →
    0 < D.requiredGain → D.requiredGain ≤
      weightedGain P.d P.N₀ ⌈exp D.logX₁⌉₊ (exp D.logX) (exp D.logX₁)

theorem finiteGain_iff_normalized : FiniteGainEstimate ↔ NormalizedEstimate := by
  constructor <;> intro h P level <;> obtain ⟨C, boundAt⟩ := h P level
  · exact ⟨C, fun D density window good ↦
      (normalized_iff_gain D).2 (boundAt D density window good)⟩
  · exact ⟨C, fun D density window good ↦
      (normalized_iff_gain D).1 (boundAt D density window good)⟩

theorem ofFiniteGain (gain : FiniteGainEstimate) : RiemannHypothesis :=
  ofNormalized (finiteGain_iff_normalized.mp gain)

end FixedClassRH
