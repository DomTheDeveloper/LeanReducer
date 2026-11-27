module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section
namespace FourthPowers
open Filter Real

/-- Endpoints of a fourth-power interval have a gap of at most 15 n³ once n ≥ 1. -/
private theorem fourth_gap {n : ℝ} (hn : 1 ≤ n) : (n+1)^4-n^4 ≤ 15*n^3 := by
  have h₁ : 0 ≤ n - 1 := by linarith
  nlinarith [mul_nonneg (sq_nonneg n) h₁, mul_nonneg (by linarith : 0 ≤ n) h₁]

/-- Quadratic reciprocal interpolation transfers fourth-power bounds to all large real inputs.
The small loss from a to b absorbs fixed constants. -/
theorem extend {R : ℝ → ℝ} {a b : ℝ}
    (step : ∀ {u x v : ℝ}, 0 < u → u ≤ x → x ≤ v → u < v →
      R x ≤ max (R u) (R v) + (x-u)*(v-x)/x^2)
    (ha : -(1/2 : ℝ) ≤ a) (ha0 : a ≤ 0) (hab : a < b)
    (samples : ∀ᶠ n : ℕ in atTop, R ((n : ℝ)^4) ≤ ((n : ℝ)^4)^a) :
    ∀ᶠ x : ℝ in atTop, R x ≤ x^b := by
  have tend : Tendsto (fun x : ℝ => ⌊√(√x)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_sqrt_atTop.comp tendsto_sqrt_atTop)
  have next := (tendsto_add_atTop_nat 1).eventually samples
  filter_upwards [tend.eventually samples, tend.eventually next,
    tend.eventually (eventually_ge_atTop (1 : ℕ)), eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop 241] with x hl hr hn hx hbig
  let n : ℝ := (⌊√(√x)⌋₊ : ℕ)
  have n1 : 1 ≤ n := by dsimp [n]; exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have nl : n ≤ √(√x) := Nat.floor_le (sqrt_nonneg _)
  have nr : √(√x) ≤ n+1 := (Nat.lt_floor_add_one _).le
  have rad : (√(√x))^4 = x := by rw [show (4 : ℕ) = 2*2 by decide, pow_mul,
    sq_sqrt (sqrt_nonneg _), sq_sqrt hx0.le]
  have hL : n^4 ≤ x := rad ▸ pow_le_pow_left₀ (by linarith : 0 ≤ n) nl 4
  have hR : x ≤ (n+1)^4 := rad ▸ pow_le_pow_left₀ (sqrt_nonneg _) nr 4
  have hl' : R (n^4) ≤ (n^4)^a := hl
  have hr' : R ((n+1)^4) ≤ ((n+1)^4)^a := by simpa [n, Nat.cast_add] using hr
  have u0 : 0 < n^4 := by positivity
  have uv : n^4 < (n+1)^4 := by nlinarith [fourth_gap n1, sq_nonneg n, (by positivity : 0 ≤ n^3)]
  have upper : x ≤ 16*n^4 := hR.trans (by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ n+1) (by linarith : n+1 ≤ 2*n) 4
    linarith only [h])
  have left : (n^4)^a ≤ 16*x^a := calc
    _ ≤ (x/16)^a := rpow_le_rpow_of_nonpos (by positivity : 0 < x/16) (by linarith only [upper] : x/16 ≤ n^4) ha0
    _ = x^a * (16:ℝ)^(-a) := by
      rw [div_rpow hx0.le (by norm_num), rpow_neg (by norm_num), div_eq_mul_inv]
    _ ≤ _ := by
      have H := rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 16) (by linarith : -a ≤ 1)
      rw [rpow_one] at H
      simpa [mul_comm] using mul_le_mul_of_nonneg_left H (rpow_nonneg hx0.le a)
  have right := hr'.trans (rpow_le_rpow_of_nonpos hx0 hR ha0)
  have gap := fourth_gap n1
  have prod : (x-n^4)*((n+1)^4-x) ≤ 225*n^6 := by
    calc
      _ ≤ (15*n^3)*(15*n^3) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
      _ = _ := by ring
  have n2 : n^2 ≤ √x := (pow_le_pow_left₀ (by linarith : 0 ≤ n) nl 2).trans_eq (sq_sqrt (sqrt_nonneg x))
  have h2 : n^2 * √x ≤ x := by nlinarith [mul_le_mul_of_nonneg_right n2 (sqrt_nonneg x), sq_sqrt hx0.le]
  have h6 : n^6 * √x ≤ x^2 := by
    nlinarith only [mul_le_mul hL h2 (by positivity : 0 ≤ n^2 * √x) hx0.le]
  have mesh : (x-n^4)*((n+1)^4-x)/x^2 ≤ 225*x^(-(1/2 : ℝ)) := by
    rw [rpow_neg hx0.le, ← sqrt_eq_rpow, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (sqrt_pos.2 hx0)]
    nlinarith only [mul_le_mul_of_nonneg_right prod (sqrt_nonneg x), h6]
  have pow := rpow_le_rpow_of_exponent_le hx ha
  have pos := rpow_nonneg hx0.le a
  calc
    R x ≤ max (R (n^4)) (R ((n+1)^4)) + (x-n^4)*((n+1)^4-x)/x^2 := step u0 hL hR uv
    _ ≤ 16*x^a + 225*x^a := add_le_add (max_le (hl'.trans left) (by linarith only [right, pos]))
        (mesh.trans (by linarith only [pow]))
    _ = x^a*241 := by ring
    _ ≤ x^a*x^(b-a) := mul_le_mul_of_nonneg_left hbig pos
    _ = x^b := by rw [← rpow_add hx0, show a+(b-a)=b by ring]

/-- Restriction and interpolation give an equivalence for the entire open interval of exponents. -/
theorem bounds_iff {R : ℝ → ℝ}
    (step : ∀ {u x v : ℝ}, 0 < u → u ≤ x → x ≤ v → u < v →
      R x ≤ max (R u) (R v) + (x-u)*(v-x)/x^2) :
    (∀ a : ℝ, -(1/2 : ℝ) < a → a < 0 → ∀ᶠ n : ℕ in atTop, R ((n:ℝ)^4) ≤ ((n:ℝ)^4)^a) ↔
      ∀ b : ℝ, -(1/2 : ℝ) < b → b < 0 → ∀ᶠ x : ℝ in atTop, R x ≤ x^b := by
  constructor
  · intro H b hb hb0
    obtain ⟨a, ha, hab⟩ := exists_between hb
    exact extend step ha.le (hab.trans hb0).le hab (H a ha (hab.trans hb0))
  · intro H a ha ha0
    exact ((tendsto_pow_atTop (by decide : 4 ≠ 0)).comp tendsto_natCast_atTop_atTop).eventually (H a ha ha0)

end FourthPowers

#print axioms FourthPowers.bounds_iff
