import FactorialLevels
import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace LeanReducer
open DirichletCharacter

/-- At each level test a bounded rectangle whose left edge approaches the critical line. -/
abbrev ZeroFreeRectangle (k : ℕ) : Prop :=
  ∀ (χ : DirichletCharacter ℂ (factorialLevel k)) (s : ℂ),
    1 / 2 + 1 / ((k : ℝ) + 1) ≤ s.re → s.re ≤ (k : ℝ) + 1 → |s.im| ≤ k →
    (χ ≠ 1 ∨ s ≠ 1) → LFunction χ s ≠ 0

/-- The rectangles cover every modulus and every point strictly right of the critical line. -/
theorem factorial_rectangles_iff :
    (∀ (q : ℕ) [NeZero q], ZeroFreeAt q (1 / 2)) ↔ ∀ k, ZeroFreeRectangle k := by
  constructor
  · intro all k χ s left _ _ pole
    have margin : 0 < 1 / ((k : ℝ) + 1) := by positivity
    exact all (factorialLevel k) χ s ((lt_add_of_pos_right _ margin).trans_le left) pole
  · intro boxes q _ χ s right pole
    obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / (s.re - 1 / 2)) (max s.re |s.im|))
    let k := max q n
    have hn' : max (1 / (s.re - 1 / 2)) (max s.re |s.im|) < (k : ℝ) :=
      hn.trans_le (by exact_mod_cast (le_max_right q n))
    have hq : q ∣ factorialLevel k :=
      dvd_mul_of_dvd_right (Nat.dvd_factorial (NeZero.pos q) ((le_max_left q n).trans (Nat.le_succ k))) _
    have inv : 1 / (s.re - 1 / 2) < (k : ℝ) + 1 := by
      linarith [(le_max_left _ _).trans_lt hn']
    have left : 1 / 2 + 1 / ((k : ℝ) + 1) < s.re :=
      (lt_sub_iff_add_lt').mp ((one_div_lt (by positivity) (sub_pos.mpr right)).2 inv)
    have reach : max s.re |s.im| < (k : ℝ) := (le_max_right _ _).trans_lt hn'
    have upper : s.re ≤ (k : ℝ) + 1 := by linarith [(le_max_left _ _).trans_lt reach]
    have height : |s.im| ≤ (k : ℝ) := ((le_max_right _ _).trans_lt reach).le
    have pole' : changeLevel hq χ ≠ 1 ∨ s ≠ 1 :=
      pole.imp (fun h => h ∘ (changeLevel_eq_one_iff hq).mp) id
    have lifted := boxes k (changeLevel hq χ) s left.le upper height pole'
    rw [LFunction_changeLevel hq χ pole] at lifted
    exact left_ne_zero_of_mul lifted

/-- A bounded critical-strip test with no pole exception in its statement. -/
abbrev CriticalBox (k : ℕ) : Prop :=
  ∀ (χ : DirichletCharacter ℂ (factorialLevel k)) (s : ℂ),
    1 / 2 + 1 / ((k : ℝ) + 1) ≤ s.re → s.re < 1 → |s.im| ≤ k → LFunction χ s ≠ 0

/-- Mathlib handles Re(s) ≥ 1. The remaining obligation is one box at each factorial level. -/
theorem factorial_critical_boxes_iff :
    (∀ (q : ℕ) [NeZero q], ZeroFreeAt q (1 / 2)) ↔ ∀ k, CriticalBox k := by
  rw [factorial_rectangles_iff]
  constructor
  · intro rect k χ s left upper height
    have top : s.re ≤ (k : ℝ) + 1 := by linarith [(show 0 ≤ (k : ℝ) by positivity)]
    have pole : s ≠ 1 := fun eq => (ne_of_lt upper) (by simp [eq])
    exact rect k χ s left top height (Or.inr pole)
  · intro critical k χ s left _ height pole
    rcases lt_or_ge s.re 1 with upper | right
    · exact critical k χ s left upper height
    · exact LFunction_ne_zero_of_one_le_re χ pole right

end LeanReducer

#print axioms LeanReducer.factorial_critical_boxes_iff
