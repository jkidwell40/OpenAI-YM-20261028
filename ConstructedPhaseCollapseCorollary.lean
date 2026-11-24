import PhasewiseDiagonalBridge_v3

/-!
# Constructed hierarchy: uniform mixed clustering implies phase agreement

This is a short corollary of two separately kernel-checked results:
* `YangMills.phasewiseDiagonal_hierarchy`
* `YangMills.Hierarchy.phaseCollapseObligation_holds`

The corollary does NOT establish `UniformMixedClustering` or a mass gap.
This new file must itself be compiled before it is described as kernel-verified.
-/

set_option autoImplicit false

namespace YangMills

open YM YM.Spec YM.OPE.Orbits

variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S)
  (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

/-- For the constructed hierarchy, uniform mixed clustering and the public
    reconstruction properties imply agreement of phase and mixture correlations
    on separated configurations. The clustering hypothesis is not discharged. -/
theorem constructed_phaseCollapse_of_uniformMixedClustering
    (order : ℕ → ℕ)
    (hProps : (hierarchy F Q).Properties order)
    (hMix : (hierarchy F Q).UniformMixedClustering) :
    (hierarchy F Q).PhasesAgreeOnSeparated :=
  (Hierarchy.phaseCollapseObligation_holds (hierarchy F Q) order)
    hProps (phasewiseDiagonal_hierarchy F Q) hMix

end YangMills

#check @YangMills.constructed_phaseCollapse_of_uniformMixedClustering
#print axioms YangMills.constructed_phaseCollapse_of_uniformMixedClustering
