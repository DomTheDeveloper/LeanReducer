-- Modified by LeanReducer to retain only the conditional analytic argument.
import Mathlib

attribute [instance 1100] MonoidHomClass.toMulHomClass RingHomClass.toAddMonoidHomClass
attribute [instance 900] DivisionRing.toRing AddMonoidWithOne.toAddMonoid AddGroupWithOne.toAddGroup
attribute [instance high] Pi.locallyCompactSpace_of_finite Pi.borelSpace
  AddEquivClass.instAddMonoidHomClass secondCountableTopologyEither_of_left
instance : SecondCountableTopology ℂ := inferInstance
instance {n} [Fintype n] : BorelSpace (n → ℂ) := inferInstance
instance {n} [Fintype n] : SecondCountableTopology (n → ℂ) := inferInstance

-- Equality is classical: every proposition is decidable (by choice), and the instances that compute
-- equality on the types used as index sets rank below, so that each index set has one instance.
-- `open Calc` brings eight of these computing instances back.
attribute [instance low] Classical.propDecidable
attribute [instance 101] Classical.decEq
attribute [instance 20] instDecidableEqSum instDecidableEqProd instDecidableEqPUnit FinEnum.decEq
  instDecidableEqFin instDecidableEqSigma Sigma.instDecidableEqSigma Subtype.instDecidableEq
  instDecidableEqEmpty Fintype.decidablePiFintype LinearOrder.toDecidableEq ZMod.decidableEq
  Matrix.decidableEq
scoped[Calc] attribute [instance] instDecidableEqSum instDecidableEqProd instDecidableEqPUnit
  instDecidableEqFin Sigma.instDecidableEqSigma Subtype.instDecidableEq Fintype.decidablePiFintype
  ZMod.decidableEq
scoped[Fint] attribute [instance low] Fintype.ofFinite
-- erases these simp lemmas for every importer; the lemmas are only named in order to be erased
set_option warning.simp.varHead false in
attribute [simp ←, simp] Matrix.conjTranspose_eq_transpose_of_trivial MonoidHom.CompTriple.comp_eq
  LinearMap.identityMapOfZeroModuleIsZero LowerAdjoint.closure_le_closed_iff_le smul_left_cancel_iff
  PartialOrder.mkOfAddGroupCone_le_iff mul_cancel_left_mem_nonZeroDivisors IsAddKleinFour.card_four'
  MeasureTheory.lintegral_of_isEmpty PartialOrder.mkOfGroupCone_le_iff Nat.card_eq_zero_of_infinite
  IsRegular.smul_eq_zero_iff_right
  Unitary.star_mul_self_of_mem Representation.isTrivial_def inv_mul_cancel_of_invertible bot_eq_one'
  EmbeddingLike.map_eq_one_iff Submodule.smul_coe_torsionBy Valuation.IsUniformizer.val star_trivial
  SetLike.GradeZero.coe_ofNat Associates.coe_unit_eq_one inv_mul_cancel_comm_assoc nsmul_eq_zero_iff
  SetLike.GradeZero.coe_mul RingHomCompTriple.comp_eq Finset.Ioc_eq_empty_of_le Finset.univ_eq_empty
  IsRegular.smul_right_inj IsAddKleinFour.card_four RootPairing.indexNeg_neg BooleanRing.mul_add_mul
  Submodule.smul_mem_iff' IsKleinFour.card_four' Nat.sub_eq_zero_of_le IsUnit.inv_mul_cancel
  IsUnit.mul_inv_cancel GroupWithZero.dvd_iff Ring.inverse_non_unit ciSup_of_not_bddAbove tsum_empty
  inv_mul_cancel_comm mul_inv_cancel_comm Set.iInter_of_empty CharP.cast_eq_zero IsEmpty.exists_iff
  IsMin.finsetIio_eq Set.Icc_eq_empty RCLike.star_def map_one_eq_zero inf_of_le_right inf_of_le_left
  FunLike.coe_mul Nat.card_unique map_inv_eq_map map_neg_eq_map nhds_discrete smul_left_inj norm_map
  RKHS.coe_smul tsum_comp_neg Nat.sub_self conj_trivial bot_eq_zero'
attribute [simp] ZMod.natCast_self Finset.prod_mul_distrib Finset.sum_add_distrib
  MeasureTheory.integral_const_mul Matrix.mulVec_diagonal Matrix.mul_inv_rev
  MeasureTheory.integral_mul_const Ideal.map_span Complex.norm_exp Set.range_subset_iff
  Nat.factorial_ne_zero finrank_real_of_complex Subgroup.mem_subgroupOf Matrix.sub_mulVec
  Matrix.add_mulVec Matrix.blockTriangular_diagonal Matrix.mulVec_smul Matrix.smul_mulVec
  Module.finrank_pi_fintype Matrix.mulVec_add Pi.single_apply sub_eq_zero
  Subgroup.index_ne_zero_of_finite
-- directions of library equivalences, for dot notation; the adjoint of a matrix
alias ⟨_, Function.Injective.of_ker⟩ := injective_iff_map_eq_zero
alias ⟨_, Function.Bijective.of_existsUnique⟩ := Function.bijective_iff_existsUnique
alias ⟨IsCompact.compactSpace, _⟩ := isCompact_iff_compactSpace
alias ⟨_, Continuous.of_at⟩ := continuous_iff_continuousAt
alias ⟨_, Filter.Eventually.all⟩ := Filter.eventually_all
alias ⟨_, CharP.of_eq_zero⟩ := CharP.charP_iff_prime_eq_zero
