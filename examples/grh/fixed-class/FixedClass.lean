import New.Endgame.OneSidedCriterion

open DirichletCharacter Filter Real

namespace FixedClassRH

/-- The one-sided error estimate needed at the single modulus used for ordinary RH. -/
def Estimate : Prop :=
  ∀ (ε : ℝ), 0 < ε / 6 ∧ ε < 1 / 100 →
    ∀ d : Nat.Primes, (d.val : ZMod 18480) = 9239 →
      ∀ᶠ x : ℝ in atTop, primeError d.val 18480 x ≤ x ^ (8 * ε + 2⁻¹ - 1)

/-- Apply the fixed-class estimate to the lift of the trivial character. -/
theorem zetaRight (estimate : Estimate) (s : ℂ) (right : 1/2 < s.re) (hs : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  set ε := (s.re ⊓ 1 - 2⁻¹) / 51
  intro zero
  have induced : entireL (1 : DirichletCharacter ℂ 18480) s = 0 := by
    simp only [entireL, if_pos rfl, LFunctionTrivChar₁, Function.update_of_ne hs,
      LFunctionTrivChar_eq_mul_riemannZeta _ hs, zero, mul_zero]
  apply entireL_ne_zero_of_primeError_le (M := 18480) (a := 9239)
    (β := 8 * ε + 2⁻¹) (by grind) (by exact (ZMod.isUnit_iff_coprime 9239 18480).2 (by decide)) (fun d hd ↦ ?_) s (by grind) _ induced
  have hmod := congrArg ZMod.val hd
  change d.val % 18480 = 9239 at hmod
  exact ⟨⟨by omega, by
    rw [Nat.Coprime, Nat.gcd_rec 18480 d.val, hmod]
    decide⟩, estimate ε (by grind) d hd⟩

theorem ofEstimate (estimate : Estimate) : RiemannHypothesis := fun s ↦ by
  obtain _ := zetaRight estimate s, zetaRight estimate (1 - s),
    @Nat.or_exists_add_one, riemannZeta_zero
  simp_all
  grind [riemannZeta_def_of_ne_zero, completedRiemannZeta_one_sub, Complex.Gammaℝ_eq_zero_iff]

end FixedClassRH
#print axioms FixedClassRH.ofEstimate
