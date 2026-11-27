-- Modified by LeanReducer. Module documentation is in SOURCE-NOTES.md.
module
public import ReciprocalInterpolation
public section
namespace WeightedFourthPowers
open Filter Real
theorem step {ι : Type*} (R : ℝ → ℝ) (s : ℕ → Finset ι) (w a : ℕ → ι → ℝ)
    (scale : ℕ → ℝ) {φ c : ℝ} (hφ : 1 ≤ φ) (hw : ∀ A i, i ∈ s A → 0 ≤ w A i)
    (formula : ∀ A : ℕ, ∀ z : ℝ, 0 < z → z ≤ A →
      R z = ReciprocalInterpolation.error (s A) (w A) (a A) (scale A) φ c z) :
    ∀ {u x v : ℝ}, 0 < u → u ≤ x → x ≤ v → u < v →
      R x ≤ max (R u) (R v) + (x-u)*(v-x)/x^2 := by
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
#print axioms WeightedFourthPowers.step
