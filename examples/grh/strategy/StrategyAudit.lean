import RHCutoffCompatibility
import RHWindowSupply
import RHNormalizedSupply
import RHOnly

example : FixedClassRH.WindowComparison → RiemannHypothesis := FixedClassRH.ofWindow
example : RiemannHypothesis := FixedClassRH.fromCovolumeWindow
example : FixedClassRH.NormalizedEstimate → RiemannHypothesis := FixedClassRH.ofNormalized
example : RiemannHypothesis := FixedClassRH.fromNormalizedCovolume
example : RiemannHypothesis := FixedClassRH.ordinaryRH

#print axioms FixedClassRH.Cutoff.exists_auxiliary_data
#print axioms FixedClassRH.Cutoff.exists_data_of_cutoff
#print axioms FixedClassRH.estimate_of_window
#print axioms FixedClassRH.ofWindow
#print axioms FixedClassRH.window_of_covolume
#print axioms FixedClassRH.fromCovolumeWindow
#print axioms FixedClassRH.ofNormalized
#print axioms FixedClassRH.fromNormalizedCovolume
#print axioms FixedClassRH.ordinaryRH
