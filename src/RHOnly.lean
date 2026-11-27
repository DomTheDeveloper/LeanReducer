import RHCovolume

open DirichletCharacter Real

namespace FixedClassRH

/-- One admissible parameter supplies the congruence conditions and the prime bound. -/
private theorem zeta_right (s : ℂ) (right : 1 / 2 < s.re) (hs : s ≠ 1) : riemannZeta s ≠ 0 := by
  set ε := (min s.re 1 - 2⁻¹) / 51
  intro zero
  apply entireL_ne_zero_of_primeError_le (M := 18480) (a := 9239) (β := 8 * ε + 2⁻¹)
    (by grind) ((ZMod.isUnit_iff_coprime 9239 18480).2 (by decide)) _ s (by grind) 1
  · simp [entireL, LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar_eq_mul_riemannZeta hs, zero]
  · intro d hd
    have residue : d.val % 18480 = 9239 := congrArg ZMod.val hd
    let P : Parameters := ⟨18480, d.val, dvd_refl _, d.property, by omega⟩
    exact ⟨⟨P.instHeegD.2, (P.coprime_N₁_d 0).coprime_mul_right⟩,
      eventually_primeError_le_rpow P (ε := ε) (by grind)⟩

theorem ordinaryRH : RiemannHypothesis := fun s ↦ by
  obtain _ := zeta_right s, zeta_right (1 - s), @Nat.or_exists_add_one, riemannZeta_zero
  simp_all
  grind [riemannZeta_def_of_ne_zero, completedRiemannZeta_one_sub, Complex.Gammaℝ_eq_zero_iff]

end FixedClassRH
