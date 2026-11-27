import RHWindow
import RHCovolume

open Real Finset Filter Data Parameters

namespace FixedClassRH

/-- The full covolume bound supplies the comparison directly at the chosen scale. -/
theorem window_of_covolume : WindowComparison := by
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
      D'.m * D'.remainder / D'.m / D'.a / #D.thick := by
    simp [remainder_eq, tops, card_placeClass_eq, field, HasLogBound.pos D', ne_of_gt] <;> ring
  change primeError P.d P.N₀ D.x -
      (primeError P.d P.N₀ D'.x₁ - towerDeg D.s / #D.thick * primeError P.d 1 D'.x₁) +
      exp (-(1e6 * D.logX)) ≤ _
  rw [cancel]
  grw [star_inequality]
  exact D'.le_of_hasLogBound (by grind)

theorem fromCovolumeWindow : RiemannHypothesis := ofWindow window_of_covolume

end FixedClassRH
