import Statements
import New.Endgame.OneSidedCriterion
import PrimeErrorFourthPowers
import FourthPowers
import FactorialLevels

open DirichletCharacter Filter Real

namespace SampledGRH

/-- A divergent family of admissible primes satisfies the one prescribed fourth-power bound. -/
def EstimateAt (k : ℕ) : Prop :=
  ∃ S : Set ℕ, DivergentPrimeMass S ∧ (∀ n ∈ S, n.Prime) ∧
    ∀ d : Nat.Primes, d.val ∈ S →
      (d.val % 8 = 7 ∧ (LeanReducer.factorialLevel k).Coprime d.val) ∧
      ∀ᶠ n : ℕ in atTop, primeError d.val (LeanReducer.factorialLevel k) ((n:ℝ)^4) ≤
        ((n:ℝ)^4)^(-(1/2:ℝ) + (1/((k:ℝ)+1))/4)

/-- The good levels can be arbitrarily sparse as long as they are unbounded. -/
def Estimates : Prop := ∀ lower : ℕ, ∃ k, lower ≤ k ∧ EstimateAt k

theorem nonvanishing (samples : Estimates) : DirichletLNonvanishingRightOfHalf := by
  change ∀ (q : ℕ) [NeZero q], LeanReducer.ZeroFreeAt q (1/2)
  apply LeanReducer.of_unbounded_factorial (Good := EstimateAt) samples
  intro k atLevel χ s hs pole zero
  obtain ⟨S, mass, primes, samplesAt⟩ := atLevel
  let δ : ℝ := 1 / ((k:ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have h1 : δ ≤ 1 := by dsimp [δ]; rw [div_le_iff₀ (by positivity)]; simp
  have bounds (d : Nat.Primes) (hd : d.val ∈ S) :
      (d.val % 8 = 7 ∧ (LeanReducer.factorialLevel k).Coprime d.val) ∧
      ∀ᶠ x : ℝ in atTop, primeError d.val (LeanReducer.factorialLevel k) x ≤ x^(1/2+δ-1) :=
    ⟨(samplesAt d hd).1, FourthPowers.extend (PrimeErrorFourthPowers.step d.val (LeanReducer.factorialLevel k))
      (a := -(1/2:ℝ)+δ/4) (by linarith) (by linarith) (by linarith) (samplesAt d hd).2⟩
  apply entireL_ne_zero_of_primeError_le (M := LeanReducer.factorialLevel k) (β := 1/2+δ) (by linarith) mass primes bounds s hs χ
  rw [entireL]
  split_ifs with h
  · subst χ
    have hs1 := pole.resolve_left (fun h ↦ h rfl)
    simp [LFunctionTrivChar₁, Function.update_of_ne hs1, LFunctionTrivChar, zero]
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
