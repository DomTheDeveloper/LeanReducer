import RHCutoffData
import New.Data.AdmissibleData

open Filter Real Finset

namespace FixedClassRH.Cutoff

/-- Specializing the cutoff recovers every field of the original admissible data. -/
def AuxiliaryData.toData {P : Parameters} (D : AuxiliaryData P P.c) : Data P :=
  ⟨D.logX, D.logB, D.logX₁, D.s, D.m, D.r, D.s_le, D.thick, D.g, D.piG,
    D.scale, D.m_mem, D.r_mem, D.m_pow, D.r_pow, D.thick_eq_neg_one_mod, D.three_term,
    D.g_prime, D.g_modEq_one, D.dvd_g_sub_one, D.g_injective, D.g_mem, D.norm_piG,
    D.exists_prime_window⟩

/-- The statement used by the existing RH proof, with its concrete theta cutoff. -/
theorem exists_data_of_cutoff (P : Parameters) {ε : ℝ} (h₀ : 0 < ε / 6) (h₁ : ε < 1 / 100) :
    ∀ᶠ x : ℝ in atTop, ∃ D : Data P, D.x = x ∧ log D.x₁ = x ^ (ε / 6) ∧
      (1e6 * log x) ^ 2 ≤ log D.x₁ ∧ log (log D.b) = ε * log x ∧
      towerDeg D.s / log D.b ≤ #D.thick := by
  filter_upwards [exists_auxiliary_data P P.c h₀ h₁] with x ⟨D, hx⟩
  exact ⟨D.toData, by simpa only [Data.x, Data.b, Data.x₁, Real.log_exp, AuxiliaryData.toData] using hx⟩

end FixedClassRH.Cutoff
