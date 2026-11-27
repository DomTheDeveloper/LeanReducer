-- Modified by LeanReducer. Module documentation is in SOURCE-NOTES.md.
module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public section
namespace ReciprocalInterpolation
open Finset Real
@[expose] noncomputable def error {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (scale φ c x : ℝ) : ℝ :=
  (∑ i ∈ s, w i * max (a i - scale / x) 0) - log x / φ - c
theorem bound {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    {u x v scale φ c : ℝ} (hu : 0 < u) (hux : u ≤ x) (hxv : x ≤ v)
    (huv : u < v) (hφ : 0 < φ) :
    error s w a scale φ c x ≤ max (error s w a scale φ c u) (error s w a scale φ c v) +
      (x - u) * (v - x) / (x ^ 2 * φ) := by
  have hx := hu.trans_le hux
  have hv := hx.trans_le hxv
  let p := u * (v - x) / (x * (v - u))
  let q := v * (x - u) / (x * (v - u))
  have hp : 0 ≤ p := div_nonneg (mul_nonneg hu.le (sub_nonneg.mpr hxv))
    (mul_nonneg hx.le (sub_nonneg.mpr huv.le))
  have hq : 0 ≤ q := div_nonneg (mul_nonneg hv.le (sub_nonneg.mpr hux))
    (mul_nonneg hx.le (sub_nonneg.mpr huv.le))
  have hpq : p + q = 1 := by
    dsimp [p, q]; field_simp [hx.ne', (sub_pos.mpr huv).ne']; ring
  have ha (z : ℝ) : z - scale / x = p * (z - scale / u) + q * (z - scale / v) := by
    dsimp [p, q]; field_simp [hu.ne', hx.ne', hv.ne', (sub_pos.mpr huv).ne']; ring
  let F (y : ℝ) := ∑ i ∈ s, w i * max (a i - scale / y) 0
  have hF : F x ≤ p * F u + q * F v := by
    dsimp [F]; rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro i hi
    rw [mul_left_comm p, mul_left_comm q, ← mul_add]
    apply mul_le_mul_of_nonneg_left _ (hw i hi)
    apply max_le
    · rw [ha]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hp)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hq)
    · exact add_nonneg (mul_nonneg hp (le_max_right _ _)) (mul_nonneg hq (le_max_right _ _))
  have logu := log_le_sub_one_of_pos (div_pos hu hx)
  have logv := log_le_sub_one_of_pos (div_pos hv hx)
  rw [log_div hu.ne' hx.ne'] at logu
  rw [log_div hv.ne' hx.ne'] at logv
  have gap : p * (u / x - 1) + q * (v / x - 1) = (x-u)*(v-x)/x^2 := by
    dsimp [p, q]; field_simp [hx.ne', (sub_pos.mpr huv).ne']; ring
  have hlog := add_le_add (mul_le_mul_of_nonneg_left logu hp) (mul_le_mul_of_nonneg_left logv hq)
  rw [gap] at hlog
  let M := max (error s w a scale φ c u) (error s w a scale φ c v)
  have he := add_le_add (mul_le_mul_of_nonneg_left (le_max_left (error s w a scale φ c u) (error s w a scale φ c v)) hp)
    (mul_le_mul_of_nonneg_left (le_max_right (error s w a scale φ c u) (error s w a scale φ c v)) hq)
  change p * (F u - log u / φ - c) + q * (F v - log v / φ - c) ≤ p * M + q * M at he
  rw [← add_mul, hpq, one_mul] at he
  change F x - log x / φ - c ≤ M + _
  have hd := div_le_div_of_nonneg_right hlog hφ.le
  rw [div_div] at hd
  calc
    F x - log x / φ - c ≤ (p * F u + q * F v) - log x / φ - c := by linarith only [hF]
    _ = (p * (F u - log u / φ - c) + q * (F v - log v / φ - c)) +
        (p * (log u - log x) + q * (log v - log x)) / φ := by
      rw [show q = 1-p by linarith only [hpq]]; ring
    _ ≤ _ := add_le_add he hd
end ReciprocalInterpolation
#print axioms ReciprocalInterpolation.bound
