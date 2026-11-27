module
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Dvd

public section
namespace OrdinaryRH

/-- The auxiliary residue class is self-inverse at the modulus used at level one. -/
theorem residue_square : 9239 * 9239 % 18480 = 1 := by decide

/-- Every integer in the selected class has the congruence and coprimality needed in the criterion. -/
theorem class_properties (d : Nat) (h : d % 18480 = 9239) :
    d % 8 = 7 ∧ Nat.Coprime 18480 d := by
  exact ⟨(Nat.mod_mod_of_dvd d (by decide : 8 ∣ 18480)).symm.trans (h ▸ rfl),
    (Nat.gcd_rec 18480 d).trans (h ▸ rfl)⟩

end OrdinaryRH

#print axioms OrdinaryRH.residue_square
#print axioms OrdinaryRH.class_properties

