-- Modified by LeanReducer. Module documentation is in SOURCE-NOTES.md.
import Lib.General.LinearAlgebra.Base
lemma sum_eq_add_sum_units {N} [Fact N.Prime] {V} [AddCommMonoid V] (f : ZMod N → V) : ∑ c, f c =
  f 0 +
  ∑ c : _ˣ, f c.1 := by simp [Fintype.sum_eq_add_sum_subtype_ne f 0, ← unitsEquivNeZero.sum_comp]
