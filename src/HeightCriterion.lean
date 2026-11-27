import RHWindow
import New.Data.DataExist
import New.Heights.Heights

open Real Finset Filter Data Parameters

namespace FixedClassRH

/-- Expand the prime remainder directly from the two scales and the two congruence classes. -/
noncomputable def primeRemainder {P} (D : Data P) : ℝ :=
  D.a * (#D.thick * (primeError P.d P.N₀ D.x - primeError P.d P.N₀ D.x₁) +
    #D.tops * primeError P.d 1 D.x₁)

/-- A nonzero family of twisted volume ratios with both height bounds. The budget for
completing the family is charged only on the missing dimensions. -/
def HasHeightCertificate {P} (D : Data P) : Prop :=
  let h := (D.m : ℝ) * D.k * D.dirCost
  let L := D.logB * D.budget
  let B := 10 * log (1 + D.b ^ 2) * D.budget
  let r := D.m * primeRemainder D
  ∃ d n : ℕ, 0 < n ∧ n ≤ d ∧ ∃ (c : ℝ) (z : PrimePadicIso → ℂ),
    (∀ ι, z ι ≠ 0) ∧ ((d : ℝ) - n) * (c + 2 * L + B - h) ≤ n * L ∧
    HeightLe (2 * d * (2 * L - h)) (fun ι ↦ (z ι ^ 2)⁻¹) ∧
    HeightLe (n * (h - r + L) + d * B + (d - n : ℝ) * c) z

/-- Multiply the twisted and untwisted bounds, then use the product formula. -/
theorem certificate_gain {P} {D : Data P} (cert : HasHeightCertificate D) :
    D.m * primeRemainder D ≤ D.logB ^ 2 * D.budget := by
  let h := (D.m : ℝ) * D.k * D.dirCost
  let L := D.logB * D.budget
  let B := 10 * log (1 + D.b ^ 2) * D.budget
  let r := D.m * primeRemainder D
  obtain ⟨d, n, hn, _, c, z, hz, charge, reverseH, forwardH⟩ := cert
  have formula : 0 ≤ 2 * (n * (h - r + L) + d * B + (d - n : ℝ) * c) + 2 * d * (2 * L - h) :=
    (((forwardH.pow 2).mul reverseH).mono le_rfl (by intro ι; simp [field, hz])).nonneg
  have paid : (d - n : ℝ) * (c + 2 * L + B - h) ≤ n * L := charge
  have gain : r ≤ 4 * L + B := by
    apply le_of_mul_le_mul_left _ (show 0 < (n : ℝ) by exact_mod_cast hn)
    nlinarith only [formula, paid]
  exact gain.trans D.le_of_hasLogBound

/-- Ordinary RH follows if the required data at modulus 18480 carry the volume certificates. -/
theorem ofHeightCertificates (supply : ∀ P : Parameters, P.N₀ = 18480 → ∀ D : Data P,
    towerDeg D.s / D.logB ≤ #D.thick → HasHeightCertificate D) : RiemannHypothesis := by
  apply ofWindow
  intro ε hε d hd
  have hmod := congrArg ZMod.val hd
  change d.val % 18480 = 9239 at hmod
  let P : Parameters := ⟨18480, d.val, dvd_refl _, d.property, by omega⟩
  filter_upwards [hε.elim (exists_data P)] with x ⟨D, hx, _, l, e, H⟩
  subst x
  simp only [log_exp, ← exp_mul] at *
  obtain := D.hasLogLower_of_le H, D.scale
  refine ⟨(towerDeg D.s : ℝ) / #D.thick, ⟨by bound, D.le_of_hasLogBound⟩, ?_⟩
  intro u hu _
  obtain ⟨lo, hi⟩ := hu
  let D' := {D with logX₁ := u, scale := by grw [hi, l] <;> grind}
  have := D'.hasLogLower_of_le H
  have cancel : primeError P.d P.N₀ D.x -
      (primeError P.d P.N₀ D'.x₁ - towerDeg D.s / #D.thick * primeError P.d 1 D'.x₁) =
      D'.m * (primeRemainder D') / D'.m / D'.a / #D.thick := by
    simp [primeRemainder, tops, card_placeClass_eq, field, HasLogBound.pos D', ne_of_gt]
    ring
  change primeError P.d P.N₀ D.x -
      (primeError P.d P.N₀ D'.x₁ - towerDeg D.s / #D.thick * primeError P.d 1 D'.x₁) +
      exp (-(1e6 * D.logX)) ≤ _
  rw [cancel]
  grw [certificate_gain (supply P rfl D' H)]
  exact D'.le_of_hasLogBound (by grind)

end FixedClassRH
