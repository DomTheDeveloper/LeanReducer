-- Modified by LeanReducer to retain only the conditional analytic argument.
import Lib.General.LinearAlgebra.Base

noncomputable section

open NumberField Complex Polynomial InfinitePlace Module IntermediateField AddChar


instance (d : Nat.Primes) : Fact d.1.Prime := ⟨d.2⟩

variable {N} [NeZero N] (χ : DirichletCharacter ℂ N) (d : ℕ) [Fact d.Prime]

/-- The Legendre symbol (·/d) as an integer-valued Dirichlet character modulo the prime d; for d
≡ 3 mod 4 it is the character χ_K of K = ℚ(√−d). -/
def chiK : DirichletCharacter ℤ d := open Calc in quadraticChar _

lemma chiK_eq_legendreSym (n : ℕ) : chiK d n = legendreSym d n := by simp [chiK, legendreSym]

/-- For a Dirichlet character χ mod N and a prime d, the character mod Nd that is the product of
χ and the Legendre symbol (·/d). -/
def quadTwist :=
  χ.changeLevel ⟨d, rfl⟩ * .changeLevel (by simp) ((chiK d).ringHomComp (algebraMap ..))

/-- The entire function equal to L(s, χ) if χ is not principal, and to the continuation of (s −
1)L(s, χ) if χ is principal. -/
def entireL := ite (χ = 1) (DirichletCharacter.LFunctionTrivChar₁ N) χ.LFunction
