module

public import NearlyMinimax.HighUnionSource
public import NearlyMinimax.HighFrameEvaluation


@[expose] public section

/-! Actual original-model legality of complete-row canonical raw histories.
The density is normalized by its true integrated mass, and the regression
uses the actual periodic polynomial field of the history's reset coefficients. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
attribute [local instance] Classical.propDecidable

section
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (R : HighUnionRowData d k F I E)

def highUnionSourceRegression (η : ℝ)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Covariate d) : ℝ :=
  highFrameField d k η (fun j => highFramePolynomial ((highUnionSourceState C R h).2 j)) x

theorem highUnionSourceState_measurable [∀ i, StandardBorelSpace (E i)]
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R) :
    Measurable (highUnionSourceState C R) :=
  historyMarkedRawState_measurable (fun i j => j ∈ highNeighborLabels d k i)
    (highUnionRawUpdate R (highCenterMix C))
    (fun j => highUnionRawUpdate_measurable R G.slope_measurable G.intercept_measurable
      G.vector_measurable G.time_measurable (highCenterMix C) j) highUnionVacuum

theorem highUnionSourceRegression_joint_measurable [∀ i, StandardBorelSpace (E i)]
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R) (η : ℝ) :
    Measurable (fun hx : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark E) × Covariate d => highUnionSourceRegression C R η hx.1 hx.2) :=
by
  let Ω := HistoryMarked (fun i j : HighWindowLabels d k => j ∈ highNeighborLabels d k i)
    (HighUnionMark E)
  have hcoef : Measurable (fun h : Ω => (highUnionSourceState C R h).2) :=
    measurable_snd.comp (highUnionSourceState_measurable C R G)
  exact highFrameField_joint_measurable (Ω := Ω) d k F η
    (fun h : Ω => (highUnionSourceState C R h).2) hcoef

end

/-- A complete actual marked history on the mass-good event gives an
admissible member of the paper's original model. The Hölder norm, density
normalization, and true conditional error moments are proved from the
constructed field and reset legality. -/
theorem highUnionSource_original_model {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr η0 : ℝ, 1 ≤ Cfr ∧ 0 < η0 ∧
      ∀ k F : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)), 4 ≤ k →
      ∀ (I : Type*) (_ : Fintype I) (E : I → Type*) (_ : (i : I) → MeasurableSpace (E i))
        (_ : (i : I) → StandardBorelSpace (E i))
        (R : HighUnionRowData d k F I E) (M : ℝ),
      HighUnionSourceGuards C M Cfr R →
      ∀ cf : ℝ, 0 ≤ cf → highWindowHolderConstant C * cf ≤ C.holderBound →
        cf * (k : ℝ)^(-C.smoothness) ≤ η0 →
      ∀ cm : ℝ, 0 ≤ cm → cm ≤ 1/C.densityUpper →
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E),
        |highUnionSourceMass C R h-1| ≤ cm/M →
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ →
      let p := highUnionSourceDensity C R h
      let f := highUnionSourceRegression C R (cf * (k : ℝ)^(-C.smoothness)) h
      ∃ hq : ∀ x y, 0 ≤ ternaryMass Q.a (f x) V y,
        Admissible C (normalizedDensityTernaryParameter p f Q.a V
          (highFrameField_contDiff d k _ _).continuous.measurable Q.a_pos.ne' hq) := by
  obtain ⟨Cfr, η0, hCfr, hη0, hModel⟩ := highFrame_normalized_parameter_admissible C Q
  refine ⟨Cfr, η0, hCfr, hη0, ?_⟩
  intro k F hk0 horder hk I hI E hE hEB R M G cf hcf hcfH hη cm hcm hcmU h hmass V hV
  letI := hk0
  letI := horder
  letI := hI
  letI := hE
  letI := hEB
  exact hModel k hk0 hk cf hcf hcfH
    (fun j => highFramePolynomial ((highUnionSourceState C R h).2 j))
    (fun j => (highFramePolynomial_coefficientL1_le _).trans
      (highUnionSourceState_coefficient_ball C R G h j)) hη M cm
    (highCenterResolution_guards C M G.resolution).1 hcm hcmU
    (highUnionSourceDensity C R h)
    ((highUnionSourceDensity_joint_measurable C R G).comp (measurable_const.prodMk measurable_id))
    (Filter.Eventually.of_forall (fun x => highUnionSourceDensity_interval C R G h x)) hmass V hV

end NearlyMinimax
