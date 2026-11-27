import FixedClass
import RHCovolume

namespace FixedClassRH

/-- The covolume proof supplies the fixed-class estimate without invoking its RH theorem. -/
theorem supplied : Estimate := by
  intro ε hε d hd
  have hmod := congrArg ZMod.val hd
  change d.val % 18480 = 9239 at hmod
  let P : Parameters := ⟨18480, d.val, dvd_refl _, d.property, by omega⟩
  exact eventually_primeError_le_rpow P hε

theorem unconditional : RiemannHypothesis := ofEstimate supplied

end FixedClassRH
#print axioms FixedClassRH.unconditional
