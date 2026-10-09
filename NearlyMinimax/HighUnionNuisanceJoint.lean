module

public import NearlyMinimax.HighUnionNuisanceRegularity
public import NearlyMinimax.AffineNuisanceJoint


@[expose] public section

/-! Joint Borel dependence for the actual full marked union, before
specializing its possibly large dependent finite row family. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
section
variable {d k F n : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
  [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (R : HighUnionRowData d k F I E)
  (Q : LowSmoothnessTernaryConstants C) (η : ℝ) (j : HighWindowLabels d k)
  {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
include G

theorem highUnionNuisanceNumerator_joint_measurable (y : Fin n → Fin 3) :
    Measurable (fun zx : LocalNuisance (HighFrameIndex d F) n × (Fin n → Covariate d) =>
      highUnionNuisanceNumerator C R Q η j zx.1 zx.2 y) := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  letI := highUnionSourceLaw_probability C R G
  apply affineNuisanceNumerator_joint_measurable
  · exact highUnionActivation_measurable R G.activation_measurable _
  · intro i
    exact (highUnionSlope_joint_measurable R G.slope_measurable j).comp
      (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))
  · intro i
    exact (highUnionIntercept_measurable R G.intercept_measurable _).comp measurable_snd
  · exact highUnionResponseVector_measurable R G.vector_measurable
  · exact highUnionResponseTime_measurable R G.time_measurable
  · intro i
    exact (highPeriodicTensor_contDiff d k j).continuous.measurable.comp (measurable_pi_apply i)
  · intro i γ
    exact (highLocalFrameFeature_measurable k j γ).comp (measurable_pi_apply i)

end
end NearlyMinimax
