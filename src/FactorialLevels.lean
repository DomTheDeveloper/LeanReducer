module
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Data.Nat.Factorial.Basic

public section
namespace LeanReducer
open DirichletCharacter

/-- The nonvanishing statement at a single positive modulus. -/
abbrev ZeroFreeAt (q : ℕ) [NeZero q] (b : ℝ) : Prop :=
  ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), b < s.re →
    (χ ≠ 1 ∨ s ≠ 1) → LFunction χ s ≠ 0

abbrev factorialLevel (k : ℕ) : ℕ := 18480 * (k + 1).factorial

instance factorialLevel_neZero (k : ℕ) : NeZero (factorialLevel k) :=
  ⟨Nat.mul_ne_zero (by decide) (Nat.factorial_ne_zero _)⟩

/-- Any unbounded set of good factorial levels suffices, regardless of its gaps. -/
theorem of_unbounded_factorial {Good : ℕ → Prop}
    (unbounded : ∀ lower : ℕ, ∃ k, lower ≤ k ∧ Good k)
    (atLevel : ∀ k, Good k → ZeroFreeAt (factorialLevel k) (1 / 2 + 1 / ((k : ℝ) + 1))) :
    ∀ (q : ℕ) [NeZero q], ZeroFreeAt q (1 / 2) := by
  intro q _ χ s right pole
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (s.re - 1 / 2))
  obtain ⟨k, hk, good⟩ := unbounded (max q n)
  have large := hk.trans (Nat.le_succ k)
  have divides : q ∣ factorialLevel k :=
    dvd_mul_of_dvd_right (Nat.dvd_factorial (NeZero.pos q) ((le_max_left q n).trans large)) _
  have margin : 1 / 2 + 1 / ((k : ℝ) + 1) < s.re := by
    apply (lt_sub_iff_add_lt').mp
    apply (one_div_lt (by positivity) (sub_pos.mpr right)).2
    exact hn.trans_le (by exact_mod_cast ((le_max_right q n).trans large))
  have pole' : changeLevel divides χ ≠ 1 ∨ s ≠ 1 :=
    pole.imp (fun h => h ∘ (changeLevel_eq_one_iff divides).mp) id
  have lifted := atLevel k good (changeLevel divides χ) s margin pole'
  rw [LFunction_changeLevel divides χ pole] at lifted
  exact left_ne_zero_of_mul lifted

end LeanReducer

#print axioms LeanReducer.of_unbounded_factorial
