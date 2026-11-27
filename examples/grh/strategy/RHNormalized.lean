import RHCutoffData
import RHWindow

open Filter Real Set Finset

namespace FixedClassRH
open Cutoff

noncomputable def Cutoff.AuxiliaryData.weight {P : Parameters} {cutoff : ℝ}
    (D : AuxiliaryData P cutoff) : ℝ :=
  (towerDeg D.s : ℝ) / #D.thick

/-- Only the fixed modulus, sufficiently dense auxiliary data and favorable second scales
enter the remaining arithmetic estimate. The cutoff may depend on the prime. -/
def NormalizedEstimate : Prop :=
  ∀ P : Parameters, P.N₀ = 18480 → ∃ cutoff : ℝ, ∀ D : AuxiliaryData P cutoff,
    (towerDeg D.s : ℝ) / D.logB ≤ #D.thick →
    D.logX₁ ≤ (1e6 * D.logX) ^ 2 →
    let aux := primeError P.d P.N₀ (exp D.logX₁) - D.weight * primeError P.d 1 (exp D.logX₁)
    aux ≤ exp (-(1e6 * D.logX)) →
      primeError P.d P.N₀ (exp D.logX) - aux ≤ P.N₀.totient * D.weight * D.logB ^ 5 / D.m

private theorem eventually_absorb (K ε : ℝ) (hε : 0 < ε) : ∀ᶠ x : ℝ in atTop,
    K * x ^ (6 * ε - 1 / 2) + exp (-(1e6 * log x)) ≤ x ^ (8 * ε + 2⁻¹ - 1) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by linarith : 0 < 2 * ε)).eventually_ge_atTop (K + 1)] with x hx big
  have xpos : 0 < x := zero_lt_one.trans_le hx
  have tiny : exp (-(1e6 * log x)) ≤ x ^ (6 * ε - 1 / 2) := by
    rw [rpow_def_of_pos xpos]
    have slope : 0 ≤ 6 * ε - 1 / 2 + 1e6 := by linarith
    apply exp_le_exp.mpr
    nlinarith only [mul_nonneg (log_nonneg hx) slope]
  calc
    _ ≤ (K + 1) * x ^ (6 * ε - 1 / 2) := by linarith only [tiny]
    _ ≤ x ^ (2 * ε) * x ^ (6 * ε - 1 / 2) :=
      mul_le_mul_of_nonneg_right big (rpow_nonneg xpos.le _)
    _ = _ := by rw [← rpow_add xpos]; congr 1; ring

private theorem budget_le {x ε K weight L m : ℝ} (hx : 0 < x) (hK : 0 ≤ K)
    (hw : weight ≤ L) (hL : L = x ^ ε) (hm : x ^ (1 / 2 : ℝ) ≤ m) :
    K * weight * L ^ 5 / m ≤ K * x ^ (6 * ε - 1 / 2) := by
  subst L
  calc
    _ ≤ K * x ^ ε * (x ^ ε) ^ 5 / x ^ (1 / 2 : ℝ) := by
      apply div_le_div₀ _ _ (rpow_pos_of_pos hx _) hm
      · positivity
      · gcongr
    _ = K * (x ^ ε * (x ^ ε) ^ 5 / x ^ (1 / 2 : ℝ)) := by ring
    _ = _ := by
      rw [← pow_succ' (x ^ ε) 5, ← rpow_natCast, ← rpow_mul hx.le, ← rpow_sub hx]
      congr 2
      ring

theorem window_of_normalized (boundAt : NormalizedEstimate) : WindowComparison := by
  intro ε hε d hd
  have hmod : d.val % 18480 = 9239 := congrArg ZMod.val hd
  let P : Parameters := ⟨18480, d.val, dvd_refl _, d.property, by omega⟩
  obtain ⟨cutoff, boundAt⟩ := boundAt P rfl
  filter_upwards [exists_auxiliary_data P cutoff hε.1 hε.2, eventually_gt_atTop (1 : ℝ),
    eventually_absorb P.N₀.totient ε (by linarith [hε.1])] with x ⟨D, scale, _, upper, hlog, mass⟩ hx absorb
  subst x
  simp only [log_exp] at *
  obtain ⟨base, first, low, high, sixth⟩ := D.scale
  have hxpos : 0 < D.logX := by simpa using hx
  have hL : 0 < D.logB := by linarith
  have L_eq : D.logB = D.logX.exp ^ ε := by
    rw [rpow_def_of_pos (exp_pos _), log_exp, mul_comm, ← hlog, exp_log hL]
  have totalPos : 0 < (towerDeg D.s : ℝ) := by
    first | exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (towerDeg D.s))
          | exact_mod_cast (show 0 < towerDeg D.s by unfold towerDeg; positivity)
  have thickPos : 0 < (#D.thick : ℝ) := (div_pos totalPos hL).trans_le mass
  have weight_le : D.weight ≤ D.logB :=
    (div_le_iff₀ thickPos).2 (by simpa [mul_comm] using (div_le_iff₀ hL).1 mass)
  have hm : D.logX.exp ^ (1 / 2 : ℝ) ≤ D.m := by
    simpa [rpow_def_of_pos (exp_pos _), div_eq_mul_inv] using D.m_mem.1
  refine ⟨D.weight, ⟨div_nonneg totalPos.le thickPos.le, weight_le.trans ?_⟩, ?_⟩
  · rw [L_eq, rpow_def_of_pos (exp_pos _), log_exp]
    apply exp_le_exp.mpr
    nlinarith only [mul_nonneg hxpos.le (show 0 ≤ 1e6 - ε by linarith [hε.2])]
  intro u hu good
  obtain ⟨lo, hi⟩ := hu
  have below : u ≤ D.logX₁ := hi.trans upper
  let D' : AuxiliaryData P cutoff := {D with logX₁ := u, scale := ⟨base, first, lo,
    (mul_le_mul_of_nonneg_left below (by norm_num)).trans high,
    (mul_le_mul_of_nonneg_left (log_le_log (by linarith) below) (by norm_num)).trans sixth⟩}
  have gap := boundAt D' mass hi good
  have budget := budget_le (exp_pos D.logX) (Nat.cast_nonneg P.N₀.totient) weight_le L_eq hm
  exact (add_le_add (gap.trans budget) (le_refl _)).trans absorb

theorem ofNormalized (boundAt : NormalizedEstimate) : RiemannHypothesis :=
  ofWindow (window_of_normalized boundAt)

end FixedClassRH
