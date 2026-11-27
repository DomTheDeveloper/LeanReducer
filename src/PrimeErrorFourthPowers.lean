-- Modified by LeanReducer. Module documentation is in SOURCE-NOTES.md.
import New.Endgame.PrimeError
import WeightedFourthPowers
open Filter Real
namespace PrimeErrorFourthPowers
theorem step (d M : ℕ) [Fact d.Prime] [NeZero M] :
    ∀ {u x v : ℝ}, 0 < u → u ≤ x → x ≤ v → u < v →
      primeError d M x ≤ max (primeError d M u) (primeError d M v) + (x-u)*(v-x)/x^2 := by
  apply WeightedFourthPowers.step (primeError d M) (fun A ↦ Finset.Icc 1 A)
    (fun A n ↦ lambdaClass d M n / (A : ℝ)) (fun A n ↦ (A : ℝ) / (n : ℝ))
    (fun A ↦ (A : ℝ)) (φ := (M.totient : ℝ)) (c := (logDerivMean d M 1).re)
  · exact_mod_cast (Nat.succ_le_of_lt (Nat.totient_pos.mpr (NeZero.pos M)))
  · intro A n _
    exact div_nonneg (lambdaClass_nonneg_and_abs_le d M n).1 (Nat.cast_nonneg _)
  · intro A z hz hzA
    rw [primeError_eq_sum A hz hzA]
    unfold ReciprocalInterpolation.error
    apply congrArg (fun y : ℝ ↦ y - Real.log z / (M.totient : ℝ) - (logDerivMean d M 1).re)
    apply Finset.sum_congr rfl
    intro n _
    change _ * max _ 0 / _ = _ / _ * max _ 0
    ring
end PrimeErrorFourthPowers
#print axioms PrimeErrorFourthPowers.step
