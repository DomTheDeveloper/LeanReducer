module
public import ReciprocalInterpolation

public section
namespace SharpInterpolation

open Real

/-- In the nonnegative one-term finite-sum model, the endpoint values can both vanish
while the value at the midpoint in reciprocal coordinates is at least h²/2. -/
theorem quadratic_gap {h : ℝ} (h₀ : 0 < h) (h₁ : h < 1) :
    ∃ a m c : ℝ, 0 ≤ m ∧
      let R := ReciprocalInterpolation.error ({()} : Finset Unit) (fun _ ↦ 1) (fun _ ↦ a) m 1 c
      R (1 / (1 + h)) = 0 ∧ R (1 / (1 - h)) = 0 ∧ h^2 / 2 ≤ R 1 := by
  have hp : 0 < 1 + h := by linarith
  have hn : 0 < 1 - h := sub_pos.mpr h₁
  let m := (log (1 + h) - log (1 - h)) / (2*h)
  have hm : 0 ≤ m := div_nonneg (sub_nonneg.mpr (log_le_log hn (by linarith)))
    (by positivity)
  have hs : m * (2*h) = log (1+h) - log (1-h) := div_mul_cancel₀ _ (by positivity)
  refine ⟨m * (1+h), m, log (1+h), hm, ?_, ?_, ?_⟩
  · simp [ReciprocalInterpolation.error]
  · have hnneg : 0 ≤ m * (1+h) - m * (1-h) := by nlinarith [mul_nonneg hm h₀.le]
    simp [ReciprocalInterpolation.error, max_eq_left hnneg]
    nlinarith only [hs]
  · have hpos : 0 ≤ m*(1+h) - m := by nlinarith [mul_nonneg hm h₀.le]
    simp [ReciprocalInterpolation.error, max_eq_left hpos]
    have logbound := log_le_sub_one_of_pos (mul_pos hp hn)
    rw [log_mul hp.ne' hn.ne'] at logbound
    nlinarith only [hs, logbound]

end SharpInterpolation

#print axioms SharpInterpolation.quadratic_gap
