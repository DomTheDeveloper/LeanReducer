import New.Data.Different
import SampledGRH

open Filter Real

namespace UpstreamEstimate

/-- Convert the residue used in the sampling statement to the divisibility
conditions in the upstream geometric parameters. -/
private theorem congr_parameters (q d : ℕ) (hq : 0 < q)
    (h : d % (18480*q) = 9240*q-1) :
    18480*q ∣ 2*(d+1) ∧ ¬18480*q ∣ d+1 := by
  have divmod := Nat.mod_add_div d (18480*q)
  rw [h] at divmod
  have expand : d+1 = 9240*q+(18480*q)*(d/(18480*q)) := by omega
  constructor
  · refine ⟨1+2*(d/(18480*q)), ?_⟩
    rw [expand]
    ring
  · intro divides
    have eqmod := Nat.mod_eq_zero_of_dvd divides
    rw [expand, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : 9240*q < 18480*q)] at eqmod
    omega

/-- The exact geometric estimate stated by `eventually_primeError_le_rpow`
supplies every arithmetic hypothesis of the 998-code-line conditional proof. -/
theorem samples_of_geometric (estimate : ∀ (P : Parameters) {ε : ℝ}, 0 < ε/6 ∧ ε < 1/100 →
    ∀ᶠ x : ℝ in atTop, primeError P.d P.N₀ x ≤ x^(8*ε+2⁻¹-1)) : SampledGRH.Estimates := by
  intro k d hd a ha _
  let q := (k+1).factorial
  let P : Parameters := ⟨18480*q, d.val, ⟨q, rfl⟩, d.property,
    congr_parameters q d.val (Nat.factorial_pos _) hd⟩
  let ε := min ((a+1/2)/16) (1/200:ℝ)
  have epos : 0 < ε := lt_min (by linarith) (by norm_num)
  have eupper : ε ≤ 1/200 := min_le_right _ _
  have ea : ε ≤ (a+1/2)/16 := min_le_left _ _
  have ht := estimate P (ε := ε) ⟨by linarith, by linarith⟩
  have tend : Tendsto (fun n : ℕ ↦ (n:ℝ)^4) atTop atTop :=
    (tendsto_pow_atTop (by decide : 4 ≠ 0)).comp tendsto_natCast_atTop_atTop
  filter_upwards [tend.eventually ht, tend.eventually (eventually_ge_atTop (1:ℝ))] with n bound hn
  exact bound.trans (rpow_le_rpow_of_exponent_le hn (by norm_num at * <;> linarith))

end UpstreamEstimate

#print axioms UpstreamEstimate.samples_of_geometric
