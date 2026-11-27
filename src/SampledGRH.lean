import Statements
import New.Endgame.OneSidedCriterion
import PrimeErrorFourthPowers
import AuxiliaryResidue
import FactorialLevels

open DirichletCharacter Filter Real

namespace SampledGRH

/-- One arithmetic hypothesis at factorial moduli, for a single residue class of
auxiliary primes at each level, and only at fourth powers of natural numbers. -/
def Estimates : Prop :=
  ∀ (k : ℕ) (d : Nat.Primes),
    d.val % LeanReducer.factorialLevel k = 9240 * (k+1).factorial - 1 →
    ∀ a : ℝ, -(1/2 : ℝ) < a → a < 0 → ∀ᶠ n : ℕ in atTop,
      primeError d.val (LeanReducer.factorialLevel k) ((n:ℝ)^4) ≤ ((n:ℝ)^4)^a

theorem nonvanishing (samples : Estimates) : DirichletLNonvanishingRightOfHalf := by
  change ∀ (q : ℕ) [NeZero q], LeanReducer.ZeroFreeAt q (1/2)
  apply LeanReducer.factorial_iff.mpr
  intro k χ s hs pole zero
  let q := (k+1).factorial
  let r := 9240*q-1
  have hq : 0 < q := Nat.factorial_pos _
  have hr : r < LeanReducer.factorialLevel k := by change 9240*q-1 < 18480*q; omega
  have unit : IsUnit (r : ZMod (LeanReducer.factorialLevel k)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr
      (AuxiliaryResidue.class_properties q r hq (Nat.mod_eq_of_lt hr)).2.symm
  have right : (1/2 : ℝ) < s.re :=
    lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hs
  obtain ⟨β, hβ, hb⟩ := exists_between (lt_min right (by norm_num : (1/2 : ℝ) < 1))
  have bounds (d : Nat.Primes) (hc : (d.val : ZMod (LeanReducer.factorialLevel k)) = r) :
      (d.val % 8 = 7 ∧ (LeanReducer.factorialLevel k).Coprime d.val) ∧
      ∀ᶠ x : ℝ in atTop, primeError d.val (LeanReducer.factorialLevel k) x ≤ x^(β-1) := by
    have congruent := ((ZMod.natCast_eq_natCast_iff' _ _ _).mp hc).trans (Nat.mod_eq_of_lt hr)
    refine ⟨AuxiliaryResidue.class_properties q d.val hq congruent, ?_⟩
    apply (PrimeErrorFourthPowers.bounds_iff d.val (LeanReducer.factorialLevel k)).mp
      (samples k d congruent) (β-1) (by linarith) (sub_neg.mpr (lt_min_iff.mp hb).2)
  apply entireL_ne_zero_of_primeError_le hβ unit bounds s (lt_min_iff.mp hb).1 χ
  rw [entireL]
  split_ifs with h
  · subst χ
    have hs1 := pole.resolve_left (fun h ↦ h rfl)
    simpa [LFunctionTrivChar₁, Function.update_of_ne hs1, LFunctionTrivChar, zero]
  · exact zero

/-- The final functional-equation arguments are adapted from Alpöge and Claude,
in Sernau and colleagues' Apache-2.0 compact edition, New/Main.lean. -/
theorem five_endpoints (samples : Estimates) :
    RiemannHypothesis ∧ RiemannZetaZerosOnLine ∧ DirichletLNonvanishingRightOfHalf ∧
      DirichletLZerosOnLine ∧ PrimitiveDirichletLZerosOnLine := by
  have H := nonvanishing samples
  have hz : RiemannZetaZerosOnLine := fun s ↦ by
    obtain _ := H 1 1 s, H 1 1 (1-s), @Nat.or_exists_add_one, riemannZeta_zero
    simp_all
    grind [riemannZeta_def_of_ne_zero, completedRiemannZeta_one_sub, Complex.Gammaℝ_eq_zero_iff]
  have hd : DirichletLZerosOnLine := fun N _ ↦ by
    grind [H N, Complex.one_re, Complex.sub_re, → LFunction_one_sub_eq_zero,
      Complex.ext_iff, DirichletCharacter.gammaFactor, Complex.Gammaℝ_ne_zero_of_re_pos]
  exact ⟨hz, hz, H, hd, fun N _ χ _ ↦ hd N χ⟩

end SampledGRH

#print axioms SampledGRH.five_endpoints
