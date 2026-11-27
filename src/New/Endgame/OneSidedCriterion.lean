-- Modified by LeanReducer to retain only the conditional analytic argument.
import New.Endgame.PrimeError
import Lib.Analytic.QuadraticTwist.ZeroFreeTwist

/-! A good second scale in every long window. If E and E' are O(e^v) and their transforms
∫E(v)e^((1−s)v)dv continue with no pole in Re s ≥ 1, then for large t and any X in [0, e^t] some u
in [t, t²] has E(u) − X E'(u) ≤ e^(−t), which replaces a pointwise prime number theorem in
progressions when the second scale of (⋆) is chosen. Localised one-sided bounds and sign changes for
prime-sum errors are known. Related work: Pintz, On the sign changes of π(x) − li(x), 1976–78;
Kaczorowski, On sign-changes in the remainder-term of the prime-number formula, 1984.

One-sided bound for non-split primes gives a zero-free half-plane. If β > 1/2 and, for every prime d
of a unit class mod M forcing d ≡ 7 mod 8, the normalised error at x in the weighted count of
primes ≡ 1 mod M not split in Q(√−d) is eventually ≤ x^(β−1), then L(s,χ) has no zero in Re s > β
for χ mod M, and this takes (⋆) to GRH. It is known that a one-sided bound for a weighted sum over
primes 1 mod q gives a zero-free half-plane if there are no real zeros. Related work: M. Suzuki, On
variants of Chebyshev's conjecture, arXiv 2411.07436, 2024; Montgomery–Vaughan, Multiplicative
Number Theory I, §15.1–15.2, 2007; Landau, Über einen Satz von Tschebyschef, 1905.

This file: One-sided bound gives a zero-free half-plane; small value in every long window. -/

open Complex Filter Nat Real Set MeasureTheory Topology

/-- One-sided criterion: let β > 1/2 and a be a unit mod M such that every prime d ≡ a is ≡ 7 mod 8,
prime to M, with R_M(x) ≤ x^{β−1} for large x (`primeError`). Then `entireL` χ has no zero in Re
s > β for any χ mod M.

One-sided bound for non-split primes gives a zero-free half-plane. -/
lemma entireL_ne_zero_of_primeError_le {M} [NeZero M] {a : ZMod M} {β} (hβ : 1 / 2 < β)
  (ha : IsUnit a) (h : ∀ d : Primes, d = a → (d.1 % 8 = 7 ∧ M.Coprime d) ∧ ∀ᶠ x in atTop, primeError
  d M x ≤ x ^ (β - 1)) ρ (hρ : β < ρ.re) (χ : DirichletCharacter ℂ M) : entireL χ ρ ≠ 0 := by
  let ⟨d, e, hZ⟩ := exists_entireL_quadTwist_ne_zero |ρ.im| hβ ha (by grind)
  use by_cases (entireL_ne_zero χ) (flip ?_ (((h d e).1.elim isPolar_primeError).landau (by bound)
    (le_total · 1 |>.rec ?_ ?_) (.mono (tendsto_exp_atTop (h d e).2) (by simp [exp_mul, mul_comm]))
    hρ)) <;> simp +contextual (maxDischargeDepth := 3) [le_of_lt, div_re,
    (tendsto_sub_mul_logDeriv_entireL _).1.2, *, normSq, entireL_ne_zero, (hβ.trans hρ).trans',
    ← cast_sum, tendsto_sub_mul_logDeriv_entireL, ne_of_apply_ne re, ne_of_gt]; bound
