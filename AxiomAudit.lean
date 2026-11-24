import PhasewiseDiagonalBridge_v3

/-! Axiom audit. A clean result lists only `propext`, `Classical.choice`,
`Quot.sound`. Any `sorryAx` or other axiom must be investigated. -/

-- Step 4, variance argument (v4), conditional on its stated hypotheses
#print axioms YangMills.Hierarchy.diagonalToVariance
#print axioms YangMills.Hierarchy.phaseCollapseObligation_holds
-- OS level, one chamber
#print axioms YM.OS.Chamber.pair_limit
#print axioms YM.OS.Chamber.pair_bound
-- public ↔ OS identification
#print axioms YangMills.coupled_pair
-- assembly: no hypotheses beyond F, Q
#print axioms YangMills.phasewiseDiagonal_hierarchy
#check @YangMills.phasewiseDiagonal_hierarchy
