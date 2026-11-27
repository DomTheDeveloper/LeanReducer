import New.Seesaw.IndexTypes

open Data Finset Real ArithmeticFunction ArithmeticFunction.vonMangoldt

namespace FixedClassRH

/-- A nominal weight only receives contributions from indices up to the second scale. -/
theorem nominal_primeSum_le {P} (D : Data P) (σ : D.Φ) :
    D.primeSum (D.nominalWeight σ) σ ≤
      2 * D.logX₁ * D.nominalWeight σ * (1 + D.logX₁) := by
  let y := D.nominalWeight σ
  have hy : 0 ≤ y := D.nominalWeight_nonneg σ
  have hx : 0 < D.logX₁ := HasLogBound.pos D
  let C := 2 * D.logX₁ * y
  have C0 : 0 ≤ C := by dsimp [C]; positivity
  have weight (n : ℕ) : lambdaClass P.d 1 n ≤ 2 * Real.log (n : ℝ) := by
    simp [lambdaClass, chiK, Set.indicator, quadraticCharFun, sub_ite] <;>
      grind [vonMangoldt_nonneg, vonMangoldt_le_log]
  have bound (n : ℕ) (hn : n ∈ Icc 1 D.a) :
      lambdaClass P.d 1 n * (y / n - D.nominalWeight (D.placeOfInt (-n) * σ))⁺ ≤
        if n ≤ ⌊D.x₁⌋₊ then C * (n : ℝ)⁻¹ else 0 := by
    have n0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from (mem_Icc.mp hn).1)
    have w0 := D.nominalWeight_nonneg (D.placeOfInt (-n) * σ)
    split_ifs with h
    · have ln : Real.log (n : ℝ) ≤ D.logX₁ := (log_le_log n0 ((Nat.le_floor_iff' (Nat.ne_of_gt (mem_Icc.mp hn).1)).mp h)).trans_eq (log_exp _)
      calc _ ≤ (2 * D.logX₁) * (y / n) :=
              mul_le_mul ((weight n).trans (by linarith))
                (max_le (sub_le_self _ w0) (div_nonneg hy n0.le))
                (by positivity) (by positivity)
           _ = _ := by simp [C, div_eq_mul_inv, mul_assoc]
    · have hw := (div_le_div₀ (Nat.cast_nonneg D.a) (D.le_of_hasLogBound : y ≤ D.a)
            D.logX₁.exp_pos (Nat.lt_of_floor_lt (Nat.lt_of_not_ge h)).le).trans
            (D.nominalWeight_mem_Icc (D.placeOfInt (-n) * σ)).1
      simp [posPart, sub_nonpos.mpr hw]
  calc _ ≤ ∑ n ∈ Icc 1 D.a, (if n ≤ ⌊D.x₁⌋₊ then C * (n : ℝ)⁻¹ else 0) :=
              Finset.sum_le_sum bound
       _ = ∑ n ∈ (Icc 1 D.a).filter (· ≤ ⌊D.x₁⌋₊), C * (n : ℝ)⁻¹ :=
              (Finset.sum_filter ..).symm
       _ ≤ ∑ n ∈ Icc 1 ⌊D.x₁⌋₊, C * (n : ℝ)⁻¹ :=
              Finset.sum_le_sum_of_subset_of_nonneg (fun n h ↦ mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp h).1).1, (mem_filter.mp h).2⟩) (by intros; positivity)
       _ ≤ _ := by
         rw [← Finset.mul_sum]
         apply mul_le_mul_of_nonneg_left _ C0
         simpa [harmonic_eq_sum_Icc] using harmonic_floor_le_one_add_log D.x₁ D.le_of_hasLogBound

/-- The logarithmic jet cost covers the prime loss at every infinite place. -/
theorem dirCost_nonneg {P} (D : Data P) : 0 ≤ D.dirCost := by
  unfold Data.dirCost
  apply Finset.sum_nonneg
  intro σ _
  apply sub_nonneg.mpr
  have W : D.nominalWeight σ ≤ D.w 0 σ :=
    (D.nominalWeight_le_w_sub 0 σ).trans (sub_le_self _ (by positivity))
  have coeff : 2 * D.logX₁ * (1 + D.logX₁) ≤ D.logB := D.le_of_hasLogBound
  have period : D.logB ≤ -log (P.bigOmega D.s / D.gProd) := by
    rw [← Real.log_inv, ← Real.log_exp D.logB]
    exact Real.log_le_log D.logB.exp_pos (by simpa [inv_div] using (D.le_of_hasLogBound : D.b ≤ D.gProd / P.bigOmega D.s))
  calc D.primeSum _ _ ≤ _ := nominal_primeSum_le D σ
       _ = D.nominalWeight σ * (2 * D.logX₁ * (1 + D.logX₁)) := by ring
       _ ≤ (D.w 0 σ : ℝ) * (-log (P.bigOmega D.s / D.gProd)) :=
             mul_le_mul W (coeff.trans period) (by have : 0 < D.logX₁ := HasLogBound.pos D; positivity) (Nat.cast_nonneg _)
       _ ≤ D.jetSize (D.w 0 σ) := by
             unfold Data.jetSize
             linarith [Real.log_nonneg (show (1 : ℝ) ≤ (D.w 0 σ).factorial by exact_mod_cast Nat.factorial_pos _)]

/-- When the main height is nonnegative, a half-dimensional family suffices for the scalar
comparison provided its adjusted covolume satisfies the displayed lower and upper bounds. -/
theorem half_rank_comparison {d n h r L B V : ℝ} (hd : 0 < d)
    (hn : d / 2 ≤ n) (nd : n ≤ d) (hh : 0 ≤ h) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (lower : d * (h - 3 * L) ≤ V)
    (upper : V ≤ n * (h - r + L) + d * B) : r ≤ 7 * L + 2 * B := by
  have pos : 0 < n := by linarith
  apply le_of_mul_le_mul_left _ pos
  nlinarith only [lower, upper, mul_le_mul_of_nonneg_right nd hh,
    mul_le_mul_of_nonneg_right hn hL,
    mul_le_mul_of_nonneg_right hn hB]

/-- Adding a cost for each missing row gives the same comparison if each such cost is
at most the main height. -/
theorem half_rank_with_completion {d n h c r L B V : ℝ} (hd : 0 < d)
    (hn : d / 2 ≤ n) (nd : n ≤ d) (hc : c ≤ h) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (lower : d * (h - 3 * L) ≤ V + (d - n) * c)
    (upper : V ≤ n * (h - r + L) + d * B) : r ≤ 7 * L + 2 * B := by
  apply half_rank_comparison (h := h - c) (V := V - n * c) hd hn nd (sub_nonneg.mpr hc) hL hB
  · linarith only [lower]
  · linarith only [upper]

end FixedClassRH
