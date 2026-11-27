module
public import ReciprocalInterpolation
public import FourthPowers

public section
namespace WeightedFourthPowers
open Filter Real

/-- A common finite cutoff and nonnegative weights suffice to transfer the entire
family of upper bounds from fourth powers to all large positive real arguments. -/
theorem bounds_iff {ι : Type*} (R : ℝ → ℝ) (s : ℕ → Finset ι) (w a : ℕ → ι → ℝ)
    (scale : ℕ → ℝ) {φ c : ℝ} (hφ : 1 ≤ φ) (hw : ∀ A i, i ∈ s A → 0 ≤ w A i)
    (formula : ∀ A : ℕ, ∀ z : ℝ, 0 < z → z ≤ A →
      R z = ReciprocalInterpolation.error (s A) (w A) (a A) (scale A) φ c z) :
    (∀ a : ℝ, -(1/2 : ℝ) < a → a < 0 → ∀ᶠ n : ℕ in atTop, R ((n:ℝ)^4) ≤ ((n:ℝ)^4)^a) ↔
      ∀ b : ℝ, -(1/2 : ℝ) < b → b < 0 → ∀ᶠ x : ℝ in atTop, R x ≤ x^b := by
  apply FourthPowers.bounds_iff
  intro u x v hu hux hxv huv
  let A := ⌈v⌉₊
  have hvA : v ≤ (A : ℝ) := Nat.le_ceil v
  have H := ReciprocalInterpolation.bound (s A) (w A) (a A) (hw A)
    (scale := scale A) (c := c) hu hux hxv huv (zero_lt_one.trans_le hφ)
  rw [formula A x (hu.trans_le hux) (hxv.trans hvA), formula A u hu (huv.le.trans hvA),
      formula A v (hu.trans huv) hvA]
  apply H.trans
  apply add_le_add le_rfl
  rw [← div_div]
  exact div_le_self (div_nonneg (mul_nonneg (sub_nonneg.mpr hux) (sub_nonneg.mpr hxv)) (sq_nonneg x)) hφ

end WeightedFourthPowers

#print axioms WeightedFourthPowers.bounds_iff
