import HalfRank
import New.Endgame.ShortAndEnough

open Data

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

end FixedClassRH
