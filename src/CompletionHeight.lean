import New.Endgame.LongForms

open Finset LinearMap Real Submodule LevelPlaces.LevelForm

namespace FixedClassRH

/-- The logarithmic size, projection and index costs paid for each auxiliary row. -/
noncomputable def completionCost {P} (D : Data P) : ℝ :=
  (D.x ^ 99 + D.x₁ ^ 2 * D.b ^ 2) + (2 * (D.m : ℝ) * D.m) * (2 * D.t * D.x ^ 999)

variable {P} {D : Data P} {n : ℕ} {y : Fin n → D.rows} {δ V : ℝ}
  (i : LinearIndependent ℂ y) (I : D.IndexLe y δ)
  (hV : ∀ σ, covolumeSq (D.Θ 1 ∘ y) σ ≤ exp V)

include i I hV

/-- For any independent family, charge only its exact number of missing basis vectors. -/
theorem heightLe_with_completion {θ} (o : D.IsFitFamily θ) :
    HeightLe (V + 2 * δ + (D.rowDim - (n : ℝ)) * completionCost D)
      fun ι ↦ D.𝔷 (θ ι) / D.𝔷 (1 : D.MFoldTwist) := by
  obtain ⟨⟨e, he, I⟩, γ, hγ, s⟩ := I, D.crude_rows
  -- the basis: `z a` is the good part of the auxiliary form `ψ a`
  choose k z ψ J c using exists_extend_basis_of_span_eq_top i ((s ▸ span_image
    (D.goodProjTranslate 1)).trans (by simp [range_smul, NeZero.ne, Module.End.one_eq_id]; rfl))
  choose ψ hψ ez using ψ
  -- size and completion; the matrices of the index, extended by the scalar of the auxiliary forms
  refine (one_determinant D.Θ (by simp) J (by simpa) (fun _ ↦ norm_map_det_gram_le fun σ ↦
    Sum.comp_elim .. ▸ covolumeSq_elim_le (ez · ▸ normSqAt_goodProjTranslate_le ((hψ _).2 σ))
    (hV σ)) (by simp) (hγ θ o) he (fun _ j ↦ (integralForms ⟨j⟩).carrier) k (fun ι j _ a _ b ↦ ?_)
    fun ι j ↦ (I _ ⟨j⟩ _ (o.1 ι)).imp' ((algebraMap ..).mapMatrix · |>.fromBlocks 0 0 ((γ (θ ι) /
    γ 1 : ℂ) • 1)) fun _ ↦ .imp (by grw [·]; simp [← RingHom.map_det, -RingHom.mapMatrix_apply])
    (by simpa [Matrix.one_apply] using! And.intro · fun a ↦ ez a ▸
    goodProjTranslate_mem_integralForms ⟨j⟩ ((hψ a).1 _ _ ⟨j⟩ (o.1 ι)) 1)).mono (by
    have dim : (D.rowDim : ℝ) = n + k := by exact_mod_cast c
    rw [dim, add_sub_cancel_left]
    push_cast
    unfold completionCost
    ring_nf
    exact le_rfl) fun _ ↦ le_rfl
  simpa using (norm_inner_le_one _ _ ⟨j⟩
    (fun g ↦ by erw [D.classAut_eq_bot_of_le_chosenLevel (Subgroup.map_mono fun _ h ↦
    funext fun _ ↦ (h (.inl _) ⟨⟩).2) (by bound [D.card_Y_le .refl])]) a b :)

/-- Product-formula lower bound for arbitrary retained rank and the explicit completion charge. -/
theorem lower_with_completion :
    D.rowDim * (D.mainHeight - 2 * (D.logB * D.budget)) ≤
      V + 2 * δ + (D.rowDim - (n : ℝ)) * completionCost D := by
  obtain ⟨⟨θ, o⟩, _, -, Z⟩ := exists_isFitFamily D, D.volume_iota_eq_prod_liftVolume
  have formula := ((((heightLe_with_completion i I hV o).pow 2).mul
    (Data.heightLe_volume_ratio_sq o)).mono le_rfl (by simp [field]; simp [(Z _).1])).nonneg
  linarith only [formula]

end FixedClassRH
