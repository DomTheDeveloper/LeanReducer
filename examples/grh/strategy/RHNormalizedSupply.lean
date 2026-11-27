import RHNormalized
import RHCutoffCompatibility
import RHCovolume

open Real Finset Data Parameters

namespace FixedClassRH
open Cutoff

/-- Cancel the positive order and the number of thick places in the covolume inequality,
then use the exact cyclotomic count of infinite places. -/
theorem normalized_of_covolume : NormalizedEstimate := by
  intro P _
  refine ⟨P.c, ?_⟩
  intro raw mass window
  dsimp only
  intro good
  let D : Data P := raw.toData
  have density : (towerDeg D.s : ℝ) / D.logB ≤ #D.thick := mass
  have := D.hasLogLower_of_le density
  have cancel : primeError P.d P.N₀ D.x -
      (primeError P.d P.N₀ D.x₁ - towerDeg D.s / #D.thick * primeError P.d 1 D.x₁) =
      D.m * D.remainder / D.m / D.a / #D.thick := by
    simp [remainder_eq, tops, card_placeClass_eq, field, HasLogBound.pos D, ne_of_gt]
    ring
  change primeError P.d P.N₀ D.x -
      (primeError P.d P.N₀ D.x₁ - towerDeg D.s / #D.thick * primeError P.d 1 D.x₁) ≤
      (P.N₀.totient : ℝ) * (towerDeg D.s / #D.thick) * D.logB ^ 5 / D.m
  rw [cancel]
  grw [star_inequality]
  simp [Data.budget, Data.f, card_infinitePlace_E, field]

theorem fromNormalizedCovolume : RiemannHypothesis := ofNormalized normalized_of_covolume

end FixedClassRH
