-- Modified by LeanReducer. Module documentation is in SOURCE-NOTES.md.
import Lib.General.LinearAlgebra.Base
noncomputable section
open NumberField Complex Polynomial InfinitePlace Module IntermediateField AddChar
instance (d : Nat.Primes) : Fact d.1.Prime := ⟨d.2⟩
variable {N} [NeZero N] (χ : DirichletCharacter ℂ N) (d : ℕ) [Fact d.Prime]
def chiK : DirichletCharacter ℤ d := open Calc in quadraticChar _
lemma chiK_eq_legendreSym (n : ℕ) : chiK d n = legendreSym d n := by simp [chiK, legendreSym]
def quadTwist :=
  χ.changeLevel ⟨d, rfl⟩ * .changeLevel (by simp) ((chiK d).ringHomComp (algebraMap ..))
def entireL := ite (χ = 1) (DirichletCharacter.LFunctionTrivChar₁ N) χ.LFunction
