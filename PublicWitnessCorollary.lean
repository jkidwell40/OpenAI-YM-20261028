import Construction
import PhasewiseDiagonalBridge_v3

/-!
# The public witnesses satisfy the conditional phase collapse

Same proof skeleton as `YangMills.jointExistence` in `Solution.lean`: the
witnesses come from `YangMills.constructed`, the hierarchy is `hierarchy F Q`,
and `core` supplies `Properties`. The only addition is the conditional
conclusion, from `phaseCollapseObligation_holds` and
`phasewiseDiagonal_hierarchy`.

`UniformMixedClustering` remains a hypothesis. This is NOT a mass-gap result.
-/

set_option autoImplicit false

/-- `JointExistence`, strengthened: for the same witnesses, uniform mixed
clustering would imply that every phase agrees with the mixture. -/
theorem YangMills.jointExistence_with_conditional_phaseCollapse :
    ∀ g : YangMills.GaugeGroup, g.IsSimple →
      ∃ C : YangMills.WilsonFamily g, YangMills.WilsonRegularity C ∧
        ∀ p : ℕ → ℕ, StrictMono p →
          ∃ q : ℕ → ℕ, StrictMono q ∧
            ∃ T : YangMills.Hierarchy C, T.Properties (p ∘ q) ∧
              (T.UniformMixedClustering → T.PhasesAgreeOnSeparated) := by
  intro g hg
  obtain ⟨C, _, _, reg, orders⟩ := YangMills.constructed.{0,0} g hg 1 zero_lt_one
  refine ⟨YangMills.wilsonFamily C, reg, fun p hp => ?_⟩
  let a : YM.Extraction.Order := ⟨.full, ⟨p, hp⟩⟩
  obtain ⟨q, S, F, L, Q, M, X, core, _⟩ := orders a
  exact ⟨q.per, q.per.monotone, YangMills.hierarchy F Q, core,
    fun hMix => YangMills.Hierarchy.phaseCollapseObligation_holds
      (YangMills.hierarchy F Q) _ core (YangMills.phasewiseDiagonal_hierarchy F Q) hMix⟩

#check @YangMills.jointExistence_with_conditional_phaseCollapse
#print axioms YangMills.jointExistence_with_conditional_phaseCollapse
