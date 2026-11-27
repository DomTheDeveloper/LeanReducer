module
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Dvd
public import Std.Tactic

public section
namespace AuxiliaryResidue

/-- The residue used in the Dirichlet endgame is 7 mod 8 and is a unit for every level q. -/
theorem class_properties (q d : Nat) (hq : 0 < q) (h : d % (18480*q) = 9240*q-1) :
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

end AuxiliaryResidue

#print axioms AuxiliaryResidue.class_properties
