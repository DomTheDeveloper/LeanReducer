import RHCutoffCompatibility
import RHWindowSupply
import RHNormalizedSupply
import RHOnly
import RHGainBlocks

example : FixedClassRH.WindowComparison → RiemannHypothesis := FixedClassRH.ofWindow
example : RiemannHypothesis := FixedClassRH.fromCovolumeWindow
example : FixedClassRH.NormalizedEstimate → RiemannHypothesis := FixedClassRH.ofNormalized
example : RiemannHypothesis := FixedClassRH.fromNormalizedCovolume
example : RiemannHypothesis := FixedClassRH.ordinaryRH
example : FixedClassRH.FiniteGainEstimate → RiemannHypothesis := FixedClassRH.ofFiniteGain
example : FixedClassRH.FiniteGainEstimate :=
  FixedClassRH.finiteGain_iff_normalized.mpr FixedClassRH.normalized_of_covolume
example : RiemannHypothesis :=
  FixedClassRH.ofFiniteGain (FixedClassRH.finiteGain_iff_normalized.mpr FixedClassRH.normalized_of_covolume)

#print axioms FixedClassRH.Cutoff.exists_auxiliary_data
#print axioms FixedClassRH.Cutoff.exists_data_of_cutoff
#print axioms FixedClassRH.estimate_of_window
#print axioms FixedClassRH.ofWindow
#print axioms FixedClassRH.window_of_covolume
#print axioms FixedClassRH.fromCovolumeWindow
#print axioms FixedClassRH.ofNormalized
#print axioms FixedClassRH.fromNormalizedCovolume
#print axioms FixedClassRH.ordinaryRH
#print axioms FixedClassRH.finiteGain_iff_normalized
#print axioms FixedClassRH.ofFiniteGain
#print axioms FixedClassRH.lower_bound_from_subset
#print axioms FixedClassRH.weightedGain_eq_blocks
#print axioms FixedClassRH.inertPrimeBlocks_le
