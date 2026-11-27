-- Modified by LeanReducer. Module documentation is in SOURCE-NOTES.md.
import Statements
import New.Endgame.OneSidedCriterion
import PrimeErrorFourthPowers
import FourthPowers
open DirichletCharacter Filter Real

namespace SampledGRH

def EstimateAt (M : ℕ) [NeZero M] (δ : ℝ) : Prop :=
  ∃ S : Set ℕ, DivergentPrimeMass S ∧ (∀ n ∈ S, n.Prime) ∧
    ∀ d : Nat.Primes, d.val ∈ S → (d.val % 8 = 7 ∧ M.Coprime d.val) ∧
      ∀ᶠ n : ℕ in atTop, primeError d.val M ((n:ℝ)^4) ≤ ((n:ℝ)^4)^(-(1/2:ℝ) + δ/4)
def Estimates : Prop :=
  ∀ (q : ℕ) [NeZero q] (ε : ℝ), 0 < ε → ∃ M : ℕ, ∃ positive : NeZero M,
    q ∣ M ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ ε ∧ @EstimateAt M positive δ

theorem nonvanishing (samples : Estimates) : DirichletLNonvanishingRightOfHalf := by
  intro q _ χ s right pole
  obtain ⟨M, positive, divides, δ, hδ, h1, small, S, mass, primes, samplesAt⟩ :=
    samples q ((s.re - 1/2)/2) (by linarith)
  letI : NeZero M := positive
  have bounds (d : Nat.Primes) (hd : d.val ∈ S) :
      (d.val % 8 = 7 ∧ M.Coprime d.val) ∧
      ∀ᶠ x : ℝ in atTop, primeError d.val M x ≤ x^(1/2+δ-1) :=
    ⟨(samplesAt d hd).1, FourthPowers.extend (PrimeErrorFourthPowers.step d.val M)
      (a := -(1/2:ℝ)+δ/4) (by linarith) (by linarith) (by linarith) (samplesAt d hd).2⟩
  have entire := entireL_ne_zero_of_primeError_le (M := M) (β := 1/2+δ)
    (by linarith) mass primes bounds s (by linarith) (changeLevel divides χ)
  have lifted : LFunction (changeLevel divides χ) s ≠ 0 := by
    intro zero
    apply entire
    have pole' := pole.imp (fun h ↦ h ∘ (changeLevel_eq_one_iff divides).mp) id
    rw [entireL]
    split_ifs with trivial
    · rw [trivial] at zero pole'
      have hs1 := pole'.resolve_left (fun ne ↦ ne rfl)
      simp [LFunctionTrivChar₁, Function.update_of_ne hs1, LFunctionTrivChar, zero]
    · exact zero
  rw [LFunction_changeLevel divides χ pole] at lifted
  exact left_ne_zero_of_mul lifted

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
