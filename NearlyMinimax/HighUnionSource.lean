module

public import NearlyMinimax.HighUnionHistory


@[expose] public section

/-! Source constant specialization for complete-row canonical histories.
The guard fields are primitive actual row-law identities and finite atomic
reset bounds; history expectations and original-model legality are outputs. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

structure HighUnionSourceGuards {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] (C : ModelConstants d) (M Cfr : ℝ)
    (R : HighUnionRowData d k F I E) : Prop where
  resolution : highCenterResolutionThreshold C ≤ M
  frame : 1 ≤ Cfr
  row_probability : ∀ i, IsProbabilityMeasure (R.rowLaw i)
  mass_nonneg : ∀ i, 0 ≤ R.rowMass i
  total_positive : 0 < highRowTotalMass R.rowMass
  activation_measurable : ∀ i, Measurable (R.rowActivation i)
  activation_bound : ∀ i e, |R.rowActivation i e| ≤ R.rowMass i
  activation_centered : ∀ i, (∫ e, R.rowActivation i e ∂(R.rowLaw i)) = 0
  slope_measurable : ∀ j i, Measurable (fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2)
  slope_integrable : ∀ j x i, Integrable (fun e => R.rowSlope j i e x) (R.rowLaw i)
  slope_centered : ∀ j x i, (∫ e, R.rowSlope j i e x ∂(R.rowLaw i)) = 0
  intercept_measurable : ∀ i, Measurable (R.rowIntercept i)
  intercept_interval : ∀ i e, R.rowIntercept i e ∈
    Icc (C.densityLower + 1/M) (C.densityUpper - 1/M)
  row_reset_interval : ∀ j i e x v, v ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) →
    R.rowSlope j i e x * v + R.rowIntercept i e ∈
      Icc (C.densityLower+1/M) (C.densityUpper-1/M)
  vector_measurable : ∀ i γ, Measurable (fun e => R.rowVector i e γ)
  time_measurable : ∀ i, Measurable (R.rowTime i)
  vector_ball : ∀ i e, (∑ γ, |R.rowVector i e γ|) ≤ Cfr⁻¹
  time_interval : ∀ i e, R.rowTime i e ∈ Icc (0 : ℝ) 1

section
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (R : HighUnionRowData d k F I E)

def highUnionVacuum : HighRawState d k F := ((fun _ => 1), 0)

def highUnionSourceState
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) :
    HighRawState d k F :=
  highUnionMarkedState R (fun i j => j ∈ highNeighborLabels d k i) (highCenterMix C)
    highUnionVacuum h

def highUnionSourceDensity
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Covariate d) : ℝ := (highUnionSourceState C R h).1 x

def highUnionSourceMass
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) : ℝ :=
  ∫ x, highUnionSourceDensity C R h x ∂cubeVolume d

variable {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
include G

theorem highUnionSourceLaw_probability : IsProbabilityMeasure (highUnionLaw R (highCenterMix C)) := by
  letI := G.row_probability
  exact highUnionLaw_probability R G.mass_nonneg G.total_positive _
    (highCenterMix_mem C).1.le (highCenterMix_mem C).2.le

theorem highUnionSource_reset_interval (j : HighWindowLabels d k) (e : HighUnionMark E)
    (x : Covariate d) (v : ℝ) (hv : v ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M)) :
    highUnionSlope R j e x * v + highUnionIntercept R (highCenterMix C) e ∈
      Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  letI := G.row_probability
  exact highCenteredRowUnion_reset_source_legal C R.rowLaw R.rowMass
    G.mass_nonneg G.total_positive (fun i e => R.rowSlope j i e x) R.rowIntercept
    G.intercept_measurable M G.resolution G.intercept_interval
    (fun i e v hv => G.row_reset_interval j i e x v hv) e v hv

theorem highUnionSource_vacuum_interval :
    (1 : ℝ) ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  have hm := highCenterResolution_guards C M G.resolution
  have hr := highCenterRadius_le_margins C
  constructor <;> linarith [highCenterRadius_pos C]

theorem highUnionSourceDensity_interval
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) (x : Covariate d) :
    highUnionSourceDensity C R h x ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) :=
  highUnionHistory_density_interval R (highCenterMix C) _ _
    (highUnionSource_reset_interval C R G) (historyShapeLength _ h.1)
    (historyShapeCanonicalLabels _ h.1) highUnionVacuum
    (fun _ => highUnionSource_vacuum_interval C R G) h.2 x

theorem highUnionSourceState_coefficient_ball
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) :
    ∀ j, (∑ γ, |(highUnionSourceState C R h).2 j γ|) ≤ Cfr⁻¹ := by
  exact highUnionHistory_coefficient_ball R (highCenterMix C) Cfr
    (by linarith [G.frame]) G.vector_ball G.time_interval (historyShapeLength _ h.1)
    (historyShapeCanonicalLabels _ h.1) highUnionVacuum
    (fun _ => by simpa [highUnionVacuum] using
      (inv_nonneg.mpr (by linarith [G.frame] : 0 ≤ Cfr))) h.2

theorem highUnionSourceDensity_joint_measurable [∀ i, StandardBorelSpace (E i)] :
    Measurable (fun hx : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark E) × Covariate d => highUnionSourceDensity C R hx.1 hx.2) :=
  highUnionMarkedDensity_joint_measurable R (fun i j => j ∈ highNeighborLabels d k i)
    G.slope_measurable G.intercept_measurable (highCenterMix C) highUnionVacuum measurable_const

theorem highUnionSourceMass_measurable [∀ i, StandardBorelSpace (E i)] :
    Measurable (highUnionSourceMass C R) :=
  highUnionMarkedMass_measurable R (fun i j => j ∈ highNeighborLabels d k i)
    G.slope_measurable G.intercept_measurable (highCenterMix C) highUnionVacuum measurable_const

theorem highUnionSourceDensity_fiber_mean_one
    (g : HistoryShape (fun i j : HighWindowLabels d k => j ∉ highNeighborLabels d k i))
    (x : Covariate d) :
    (∫ marks, highUnionSourceDensity C R ⟨g,marks⟩ x
      ∂Measure.pi (fun _ : Fin (historyShapeLength _ g) => highUnionLaw R (highCenterMix C))) = 1 := by
  letI := G.row_probability
  exact highUnionHistory_density_mean_one R G.mass_nonneg G.total_positive
    (fun j x i => (G.slope_measurable j i).comp (measurable_id.prodMk measurable_const))
    G.slope_integrable G.slope_centered G.intercept_measurable _ _ G.intercept_interval
    (highCenterMix C) (highCenterMix_mem C).1.le (highCenterMix_mem C).2
    (historyShapeLength _ g) (historyShapeCanonicalLabels _ g) highUnionVacuum (fun _ => rfl) x

theorem highUnionSourceMass_interval [∀ i, StandardBorelSpace (E i)]
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) :
    highUnionSourceMass C R h ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  letI := cubeVolume_isProbability d
  exact boundedIntercept_mean_mem (cubeVolume d) (highUnionSourceDensity C R h)
    ((highUnionSourceDensity_joint_measurable C R G).comp (measurable_const.prodMk measurable_id))
    _ _ (highUnionSourceDensity_interval C R G h)

theorem highUnionSourceMass_fiber_mean_one [∀ i, StandardBorelSpace (E i)]
    (g : HistoryShape (fun i j : HighWindowLabels d k => j ∉ highNeighborLabels d k i)) :
    (∫ marks, highUnionSourceMass C R ⟨g,marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength _ g) => highUnionLaw R (highCenterMix C))) = 1 := by
  letI := highUnionSourceLaw_probability C R G
  letI := cubeVolume_isProbability d
  let f := fun mx : (Fin (historyShapeLength _ g) → HighUnionMark E) × Covariate d =>
    highUnionSourceDensity C R ⟨g,mx.1⟩ mx.2
  have hm : Measurable f := highUnionHistory_density_joint_measurable R G.slope_measurable
    G.intercept_measurable (highCenterMix C) (historyShapeLength _ g)
    (historyShapeCanonicalLabels _ g) highUnionVacuum measurable_const
  have hM0 : 0 < M := by
    have := (highCenterResolution_guards C M G.resolution).1
    linarith
  have hi : Integrable f ((Measure.pi (fun _ : Fin (historyShapeLength _ g) =>
      highUnionLaw R (highCenterMix C))).prod (cubeVolume d)) := by
    apply (integrable_const C.densityUpper).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro mx
    have hb := highUnionSourceDensity_interval C R G ⟨g,mx.1⟩ mx.2
    change ‖f mx‖ ≤ C.densityUpper
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [f]; linarith [hb.1, C.densityLower_pos, one_div_pos.mpr hM0])]
    exact hb.2.trans (by linarith [one_div_pos.mpr hM0])
  change (∫ marks, ∫ x, f (marks,x) ∂cubeVolume d
    ∂Measure.pi (fun _ : Fin (historyShapeLength _ g) => highUnionLaw R (highCenterMix C))) = 1
  rw [integral_integral_swap hi]
  have he (x : Covariate d) :
      (∫ marks, f (marks,x) ∂Measure.pi (fun _ : Fin (historyShapeLength _ g) =>
        highUnionLaw R (highCenterMix C))) = 1 := highUnionSourceDensity_fiber_mean_one C R G g x
  simp_rw [he]
  simp

theorem highUnionSourceMass_block_oscillation [∀ i, StandardBorelSpace (E i)] (hk : 2 ≤ k)
    (g : HistoryShape (fun i j : HighWindowLabels d k => j ∉ highNeighborLabels d k i))
    (marks marks' : Fin (historyShapeLength _ g) → HighUnionMark E) (j : HighWindowLabels d k)
    (hMarks : ∀ i, historyShapeCanonicalLabels _ g i ≠ j → marks i = marks' i) :
    |highUnionSourceMass C R ⟨g,marks⟩ - highUnionSourceMass C R ⟨g,marks'⟩| ≤
      (2 / (k : ℝ))^d * (C.densityUpper-C.densityLower) := by
  have h := highAffineMarkedMass_block_oscillation d k hk
    (fun i j => j ∈ highNeighborLabels d k i) (highUnionSlope R)
    (fun _ e _ => highUnionIntercept R (highCenterMix C) e)
    (fun j e => (highUnionSlope_joint_measurable R G.slope_measurable j).comp
      (measurable_const.prodMk measurable_id)) (fun _ _ => measurable_const)
    (fun _ => highUnionResponseReset R) (C.densityLower+1/M) (C.densityUpper-1/M)
    (by linarith [(highUnionSource_vacuum_interval C R G).1,
      (highUnionSource_vacuum_interval C R G).2])
    (highUnionSource_reset_interval C R G) highUnionVacuum measurable_const
    (fun _ => highUnionSource_vacuum_interval C R G) g marks marks' j hMarks
  apply h.trans
  have hM0 : 0 < M := by
    have := (highCenterResolution_guards C M G.resolution).1
    linarith
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith [one_div_pos.mpr hM0]

end
end NearlyMinimax
