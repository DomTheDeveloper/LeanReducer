-- Modified by LeanReducer. Module documentation is in SOURCE-NOTES.md.
import New.Endgame.PrimeError
import Lib.Analytic.QuadraticTwist.ZeroFreeTwist
open Complex Filter Nat Real Set MeasureTheory Topology
lemma entireL_ne_zero_of_primeError_le {M} [NeZero M] {S : Set ℕ} {β} (hβ : 1 / 2 < β)
    (mass : DivergentPrimeMass S) (primes : ∀ n ∈ S, n.Prime)
    (h : ∀ d : Primes, d.val ∈ S → (d.1 % 8 = 7 ∧ M.Coprime d) ∧ ∀ᶠ x in atTop, primeError
      d M x ≤ x ^ (β - 1)) ρ (hρ : β < ρ.re) (χ : DirichletCharacter ℂ M) : entireL χ ρ ≠ 0 := by
  let ⟨d, e, hZ⟩ := exists_entireL_quadTwist_ne_zero_of_mass |ρ.im| hβ mass primes (by grind)
  use by_cases (entireL_ne_zero χ) (flip ?_ (((h d e).1.elim isPolar_primeError).landau (by bound)
    (le_total · 1 |>.rec ?_ ?_) (.mono (tendsto_exp_atTop (h d e).2) (by simp [exp_mul, mul_comm]))
    hρ)) <;> simp +contextual (maxDischargeDepth := 3) [le_of_lt, div_re,
    (tendsto_sub_mul_logDeriv_entireL _).1.2, *, normSq, entireL_ne_zero, (hβ.trans hρ).trans',
    ← cast_sum, tendsto_sub_mul_logDeriv_entireL, ne_of_apply_ne re, ne_of_gt]; bound
