import HalfRank
import New.Endgame.ShortAndEnough

open Data Finset

namespace FixedClassRH

/-- The main height in the covolume argument is nonnegative. -/
theorem mainHeight_nonneg {P} (D : Data P) : 0 ≤ D.mainHeight := by
  unfold Data.mainHeight
  exact mul_nonneg (by positivity) (dirCost_nonneg D)

/-- The final scalar comparison only needs half the row dimension when the same height
and index estimates are available for the retained family. -/
theorem star_of_half_rank {P} (D : Data P) {n V : ℝ}
    (hn : D.rowDim / 2 ≤ n) (nd : n ≤ D.rowDim)
    (lower : D.rowDim * (D.mainHeight - 3 * (D.logB * D.budget)) ≤ V)
    (upper : V ≤ n * (D.mainHeight - D.m * D.remainder + D.logB * D.budget) +
      D.rowDim * (10 * Real.log (1 + D.b ^ 2) * D.budget)) :
    D.m * D.remainder ≤ D.logB ^ 2 * D.budget := by
  have d : (0 : ℝ) < D.rowDim := mod_cast D.finrank_rows_ne_zero.pos
  have L : 0 ≤ D.logB * D.budget := (HasLogBound.pos D).le
  have B : 0 ≤ 10 * Real.log (1 + D.b ^ 2) * D.budget :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [sq_nonneg D.b]))) (HasLogBound.pos D).le
  exact (half_rank_comparison d hn nd (mainHeight_nonneg D) L B lower upper).trans D.le_of_hasLogBound

/-- Data supplied for ordinary RH have enough thick places to dominate both scalar errors. -/
theorem mainHeight_margin {P} (D : Data P)
    (density : towerDeg D.s / D.logB ≤ #D.thick) :
    3 * (D.logB * D.budget) + 10 * Real.log (1 + D.b ^ 2) * D.budget ≤ D.mainHeight := by
  have := D.hasLogLower_of_le density
  calc _ ≤ ((D.m : ℝ) * D.k) * (#D.thick * (D.a / D.x * D.logB)) := D.le_of_hasLogBound
       _ ≤ _ := by simpa [Data.mainHeight, Nat.cast_mul] using
                     mul_le_mul_of_nonneg_left (thick_le_dirCost D) (by positivity : 0 ≤ (D.m : ℝ) * D.k)

/-- For the actual density used in RH, even one row suffices in the scalar comparison
if the adjusted covolume lower bound holds for that family. -/
theorem star_of_positive_rank {P} (D : Data P)
    (density : towerDeg D.s / D.logB ≤ #D.thick) {n V : ℝ} (hn : 0 < n) (nd : n ≤ D.rowDim)
    (lower : D.rowDim * (D.mainHeight - 3 * (D.logB * D.budget)) ≤ V)
    (upper : V ≤ n * (D.mainHeight - D.m * D.remainder + D.logB * D.budget) +
      D.rowDim * (10 * Real.log (1 + D.b ^ 2) * D.budget)) :
    D.m * D.remainder ≤ D.logB ^ 2 * D.budget := by
  have m := positive_rank_comparison (c := 0) hn nd (by simpa using mainHeight_margin D density)
    (by simpa using lower) upper
  exact m.trans D.le_of_hasLogBound

end FixedClassRH
