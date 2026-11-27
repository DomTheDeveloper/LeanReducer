import HeightCriterion

open Data Finset Filter Real

namespace FixedClassRH

/-- A nonzero untwisted Gram value provides the numerator-clearing factor in the height
bound. Each finite-place bound applies to the corresponding twisted Gram value. -/
theorem heightLe_one_volume {u₀ : ℂ} (hu₀ : u₀ ≠ 0) {u : PrimePadicIso → ℂ} {A δ : ℝ}
    {e : ℕ → ℝ} (arch : ∀ σ : ℂ ≃+* ℂ, ‖σ u₀‖ ≤ exp A)
    (finite : ∀ ι : PrimePadicIso, ‖ι.2 (u ι)‖ ≤ exp (e ι.1))
    (sum : ∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, e l ≤ δ) :
    HeightLe (A + δ) (fun ι ↦ u ι / u₀) := by
  refine ⟨u₀, A, e, hu₀, arch, fun ι ↦ ?_, .of_forall fun M ↦ ?_⟩
  · simpa [field, hu₀] using finite ι
  · exact add_le_add le_rfl (sum _ fun _ hl ↦ (mem_filter.mp hl).2)

/-- A single nonzero Gram value for each twist supplies the certificate when the local
integrality, conjugate-size and inverse-height estimates hold for these very same values. -/
theorem certificate_of_one_volume {P} (D : Data P) {u₀ : ℂ} (hu₀ : u₀ ≠ 0)
    {u : PrimePadicIso → ℂ} (hu : ∀ ι, u ι ≠ 0) {e : ℕ → ℝ}
    (arch : ∀ σ : ℂ ≃+* ℂ, ‖σ u₀‖ ≤ exp ((D.m : ℝ) * D.k * D.dirCost - D.m * primeRemainder D + D.logB * D.budget))
    (finite : ∀ ι : PrimePadicIso, ‖ι.2 (u ι)‖ ≤ exp (e ι.1))
    (sum : ∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, e l ≤ 10 * log (1 + D.b ^ 2) * D.budget)
    (reverseH : HeightLe (2 * (2 * (D.logB * D.budget) - (D.m : ℝ) * D.k * D.dirCost))
      (fun ι ↦ (u₀ / u ι) ^ 2)) : HasHeightCertificate D := by
  refine ⟨1, 1, by decide, le_rfl, 0, (fun ι ↦ u ι / u₀), fun ι ↦ div_ne_zero (hu ι) hu₀, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_one, sub_self, zero_mul, one_mul] using (HasLogBound.pos D : 0 < D.logB * D.budget).le
  · simpa only [Nat.cast_one, mul_one, div_pow, inv_div] using reverseH
  · simpa only [Nat.cast_one, sub_self, zero_mul, mul_one, one_mul, add_zero] using heightLe_one_volume hu₀ arch finite sum

end FixedClassRH
