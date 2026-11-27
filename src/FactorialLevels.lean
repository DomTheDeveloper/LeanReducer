module
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Data.Nat.Factorial.Basic

public section
namespace LeanReducer
open DirichletCharacter

/-- The zero-free half-plane at one positive modulus, including the pole exception. -/
def ZeroFreeAt (q : ℕ) [NeZero q] (b : ℝ) : Prop :=
  ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), b < s.re →
    (χ ≠ 1 ∨ s ≠ 1) → LFunction χ s ≠ 0

/-- A cofinal sequence of levels suffices even with a different half-plane at each level. -/
theorem cofinal_iff (M : ℕ → ℕ) [∀ k, NeZero (M k)] (b : ℕ → ℝ)
    (above : ∀ k, 1 / 2 ≤ b k)
    (covers : ∀ (q : ℕ) [NeZero q] (σ : ℝ), 1 / 2 < σ → ∃ k, q ∣ M k ∧ b k < σ) :
    (∀ (q : ℕ) [NeZero q], ZeroFreeAt q (1 / 2)) ↔ ∀ k, ZeroFreeAt (M k) (b k) := by
  constructor
  · intro all k χ s hs pole
    exact all (M k) χ s ((above k).trans_lt hs) pole
  · intro sampled q _ χ s hs pole
    obtain ⟨k, hq, hk⟩ := covers q s.re hs
    have pole' : changeLevel hq χ ≠ 1 ∨ s ≠ 1 :=
      pole.imp (fun h => h ∘ (changeLevel_eq_one_iff hq).mp) id
    have lifted := sampled k (changeLevel hq χ) s hk pole'
    rw [LFunction_changeLevel hq χ pole] at lifted
    exact left_ne_zero_of_mul lifted

def factorialLevel (k : ℕ) : ℕ := 18480 * (k + 1).factorial

instance factorialLevel_neZero (k : ℕ) : NeZero (factorialLevel k) :=
  ⟨Nat.mul_ne_zero (by decide) (Nat.factorial_ne_zero _)⟩

/-- One positive margin 1/(k+1) at each factorial multiple of 18480 suffices for every modulus. -/
theorem factorial_iff :
    (∀ (q : ℕ) [NeZero q], ZeroFreeAt q (1 / 2)) ↔
      ∀ k : ℕ, ZeroFreeAt (factorialLevel k) (1 / 2 + 1 / ((k : ℝ) + 1)) := by
  apply cofinal_iff factorialLevel (fun k => 1 / 2 + 1 / ((k : ℝ) + 1))
  · intro k
    exact le_add_of_nonneg_right (by positivity)
  · intro q _ σ right
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (σ - 1 / 2))
    let k := max q n
    have hq : q ∣ (k + 1).factorial :=
      Nat.dvd_factorial (NeZero.pos q) ((le_max_left q n).trans (Nat.le_succ k))
    refine ⟨k, dvd_mul_of_dvd_right hq _, ?_⟩
    apply (lt_sub_iff_add_lt').mp
    apply (one_div_lt (by positivity) (sub_pos.mpr right)).2
    exact hn.trans_le (by exact_mod_cast (show n ≤ k + 1 from (le_max_right q n).trans (Nat.le_succ k)))

end LeanReducer

#print axioms LeanReducer.factorial_iff
