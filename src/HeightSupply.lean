import HeightCriterion
import RankFromCovolume
import CompletionHeight

open Data Finset Real LevelPlaces.LevelForm

namespace FixedClassRH

/-- The existing short family and the exact completion bound supply the two height estimates.
This compatibility check keeps the full geometric proof out of the criterion's import closure. -/
theorem heightCertificate_of_covolume {P} (D : Data P)
    (density : towerDeg D.s / D.logB ≤ #D.thick) : HasHeightCertificate D := by
  obtain ⟨n, y, i, rank, ⟨δ, index, I⟩, small⟩ := D.exists_family_covolumeSq_le
  obtain ⟨⟨θ, fit⟩, _, -, Z⟩ := exists_isFitFamily D, D.volume_iota_eq_prod_liftVolume
  let L := D.logB * D.budget
  let B := 10 * log (1 + D.b ^ 2) * D.budget
  have nd : (n : ℝ) ≤ D.rowDim := mod_cast Fintype.card_fin n ▸ i.fintype_card_le_finrank
  have Lpos : 0 < L := HasLogBound.pos D
  have eff : 4 / D.b ^ 2 ≤ (1/2 : ℝ) := by
    rw [div_le_iff₀ (sq_pos_of_pos D.logB.exp_pos)]
    linarith only [(D.le_of_hasLogBound : 8 ≤ D.b ^ 2)]
  have half : (D.rowDim : ℝ) / 2 ≤ n := by
    linarith only [rank, mul_le_mul_of_nonneg_right eff (Nat.cast_nonneg D.rowDim : (0 : ℝ) ≤ D.rowDim)]
  have dpos : (0 : ℝ) < D.rowDim := mod_cast D.finrank_rows_ne_zero.pos
  have npos : (0 : ℝ) < n := by linarith only [dpos, half]
  have relax := relaxed_rank_of_original rank
  have charge : (D.rowDim - (n : ℝ)) * completionCost D ≤ (D.rowDim : ℝ) * (2 * D.b) := calc
    _ ≤ (D.rowDim - (n : ℝ)) * (2 * (D.x₁ ^ 2 * D.b ^ 2)) :=
        mul_le_mul_of_nonneg_left (completionCost_le D) (sub_nonneg.mpr nd)
    _ = ((D.rowDim - (n : ℝ)) * (D.x₁ ^ 2 * D.b)) * (2 * D.b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right relax (by positivity)
  have margin : 2 * L + B ≤ D.mainHeight := by
    linarith only [(mainHeight_margin D density : 3 * L + B ≤ D.mainHeight), Lpos]
  have allowance : (D.rowDim : ℝ) * (2 * D.b) ≤ n * L := calc
    _ ≤ (2 * (n : ℝ)) * (2 * D.b) := mul_le_mul_of_nonneg_right (by linarith only [half]) (by positivity)
    _ = (n : ℝ) * (4 * D.b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (D.le_of_hasLogBound : 4 * D.b ≤ L) (Nat.cast_nonneg n)
  refine ⟨D.rowDim, n, by exact_mod_cast npos, by exact_mod_cast nd, completionCost D,
    (fun ι ↦ D.𝔷 (θ ι) / D.𝔷 (1 : D.MFoldTwist)), fun ι ↦ div_ne_zero (Z _).1 (Z _).1, ?_, ?_, ?_⟩
  · change (D.rowDim - (n : ℝ)) * (completionCost D + 2 * L + B - D.mainHeight) ≤ n * L
    nlinarith only [charge, allowance, mul_le_mul_of_nonneg_left margin (sub_nonneg.mpr nd)]
  · simpa only [Data.mainHeight, Nat.cast_mul, div_pow, inv_div] using Data.heightLe_volume_ratio_sq fit
  · apply (heightLe_with_completion i I small fit).mono _ fun _ ↦ le_rfl
    have prime : primeRemainder D = D.remainder := D.remainder_eq.symm
    rw [prime]
    change n * (D.mainHeight - D.m * D.remainder + L) + 2 * δ + _ ≤
      n * (D.mainHeight - D.m * D.remainder + L) + D.rowDim * B + _
    dsimp only [B]
    linarith only [index]

theorem ordinaryRH_from_height_certificates : RiemannHypothesis :=
  ofHeightCertificates fun _ _ D density ↦ heightCertificate_of_covolume D density

end FixedClassRH
