import SampledGRH

open Filter ArithmeticFunction ArithmeticFunction.vonMangoldt
open scoped Classical

namespace OldToDivergent

-- Residue calculation from the previously checked 976-line project.
private theorem class_properties (q d : Nat) (hq : 0 < q) (h : d % (18480*q) = 9240*q-1) :
    d % 8 = 7 ∧ Nat.Coprime (18480*q) d := by
  let r := 9240*q-1
  have evenLevel : 18480*q = 2 + 2*r := by dsimp [r]; omega
  have oddResidue : r % 2 = 1 := by dsimp [r]; omega
  constructor
  · have dv : 8 ∣ 18480*q := ⟨2310*q, by omega⟩
    rw [← Nat.mod_mod_of_dvd d dv, h]
    omega
  · change Nat.gcd (18480*q) d = 1
    rw [Nat.gcd_rec (18480*q) d, h]
    change Nat.gcd r (18480*q) = 1
    rw [evenLevel, Nat.gcd_add_mul_right_right, Nat.gcd_comm, Nat.gcd_rec 2 r, oddResidue]
    decide

theorem divergent_residue {M : ℕ} [NeZero M] (r : ZMod M) (unit : IsUnit r) :
    DivergentPrimes {n : ℕ | (n : ZMod M) = r} := by
  have weights (n : ℕ) : (if n.Prime then residueClass r n else 0) / n =
      (if n.Prime ∧ (n : ZMod M) = r then Real.log n else 0) / n := by
    by_cases prime : n.Prime <;> by_cases h : (n : ZMod M) = r <;>
      simp [prime, h, residueClass, Set.indicator, vonMangoldt_apply_prime]
  intro summable
  exact not_summable_residueClass_prime_div unit (summable.congr fun n ↦ (weights n).symm)

theorem old_level_implies_divergent (k : ℕ)
    (old : ∀ d : Nat.Primes,
      d.val % LeanReducer.factorialLevel k = 9240 * (k+1).factorial - 1 →
      ∀ᶠ n : ℕ in atTop, primeError d.val (LeanReducer.factorialLevel k) ((n:ℝ)^4) ≤
        ((n:ℝ)^4)^(-(1/2:ℝ) + (1/((k:ℝ)+1))/4)) : SampledGRH.EstimateAt k := by
  let q := (k+1).factorial
  let r := 9240*q-1
  have hq : 0 < q := Nat.factorial_pos _
  have hr : r < LeanReducer.factorialLevel k := by change 9240*q-1 < 18480*q; omega
  have unit : IsUnit (r : ZMod (LeanReducer.factorialLevel k)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr
      (class_properties q r hq (Nat.mod_eq_of_lt hr)).2.symm
  refine ⟨{n : ℕ | (n : ZMod (LeanReducer.factorialLevel k)) = r}, divergent_residue _ unit, ?_⟩
  intro d hd
  have eqn : (d.val : ZMod (LeanReducer.factorialLevel k)) = r := hd
  have h := ((ZMod.natCast_eq_natCast_iff' _ _ _).mp eqn).trans (Nat.mod_eq_of_lt hr)
  exact ⟨class_properties q d.val hq h, old d h⟩

end OldToDivergent

#print axioms OldToDivergent.old_level_implies_divergent
