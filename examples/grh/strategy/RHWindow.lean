import FixedClass

open Filter Real Set

namespace FixedClassRH

/-- At scale x, choose one weight before choosing the second logarithmic scale u.
Only windows where the auxiliary error is small require a comparison. -/
def WindowComparison : Prop :=
  ∀ (ε : ℝ), 0 < ε / 6 ∧ ε < 1 / 100 →
    ∀ d : Nat.Primes, (d.val : ZMod 18480) = 9239 → ∀ᶠ x : ℝ in atTop,
      let t := 1e6 * log x
      ∃ weight ∈ Icc (0 : ℝ) (exp t), ∀ u ∈ Icc t (t ^ 2),
        let aux := primeError d.val 18480 (exp u) - weight * primeError d.val 1 (exp u)
        aux ≤ exp (-t) →
          primeError d.val 18480 x - aux + exp (-t) ≤ x ^ (8 * ε + 2⁻¹ - 1)

/-- The analytic window lemma eliminates the second scale. -/
theorem estimate_of_window (compare : WindowComparison) : Estimate := by
  intro ε hε d hd
  have hmod := congrArg ZMod.val hd
  change d.val % 18480 = 9239 at hmod
  have h7 : d.val % 8 = 7 := by omega
  have coprime : Nat.Coprime 18480 d.val := (Nat.gcd_rec 18480 d.val).trans (hmod ▸ rfl)
  have windows := (isPolar_primeError h7 coprime).exists_window_sub_mul_le
    (isPolar_primeError h7 d.val.coprime_one_left)
  filter_upwards [compare ε hε d hd, tendsto_log_atTop.const_mul_atTop (r := 1e6)
    (by norm_num) windows] with x ⟨weight, hw, compareAt⟩ win
  obtain ⟨u, hu, good⟩ := win weight hw
  linarith only [compareAt u hu good, good]

theorem ofWindow (compare : WindowComparison) : RiemannHypothesis :=
  ofEstimate (estimate_of_window compare)

end FixedClassRH
