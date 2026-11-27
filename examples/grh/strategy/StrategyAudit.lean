import RHCutoffCompatibility
import RHWindowSupply

example : FixedClassRH.WindowComparison → RiemannHypothesis := FixedClassRH.ofWindow
example : RiemannHypothesis := FixedClassRH.fromCovolumeWindow

#print axioms FixedClassRH.Cutoff.exists_auxiliary_data
#print axioms FixedClassRH.Cutoff.exists_data_of_cutoff
#print axioms FixedClassRH.estimate_of_window
#print axioms FixedClassRH.ofWindow
#print axioms FixedClassRH.window_of_covolume
#print axioms FixedClassRH.fromCovolumeWindow
