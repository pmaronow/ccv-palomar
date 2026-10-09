module

public import NearlyMinimax.HighUnionSourceModel


@[expose] public section

/-! Genuine response probability floors on every raw history, including
mass-exceptional histories. The constants precede the extension domain. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- A larger frame constant imposes a smaller coefficient ball, and therefore
supplies every primitive guard for a smaller admissible frame constant. -/
theorem HighUnionSourceGuards.mono_frame {d k F : ℕ} {I : Type*} [Fintype I]
    {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    {C : ModelConstants d} {M Cfr Cfr' : ℝ} {R : HighUnionRowData d k F I E}
    (G : HighUnionSourceGuards C M Cfr R) (hfr : 1 ≤ Cfr') (hle : Cfr' ≤ Cfr) :
    HighUnionSourceGuards C M Cfr' R := by
  refine { G with frame := hfr, vector_ball := ?_ }
  intro i e
  exact (G.vector_ball i e).trans ((inv_le_inv₀ (by linarith : 0 < Cfr)
    (by linarith : 0 < Cfr')).mpr hle)

/-- The actual full-union polynomial regression gives a fixed strictly
positive ternary mass floor on all raw states, without a mass-good premise.
Thus mass-exceptional states still carry a genuine probability experiment. -/
theorem highUnionSource_ternary_floor_uniform {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr η0 : ℝ, 1 ≤ Cfr ∧ 0 < η0 ∧
      ∀ k F : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)), 4 ≤ k →
      ∀ (I : Type*) (_ : Fintype I) (E : I → Type*) (_ : (i : I) → MeasurableSpace (E i))
        (R : HighUnionRowData d k F I E) (M : ℝ),
      HighUnionSourceGuards C M Cfr R →
      ∀ cf : ℝ, 0 ≤ cf → cf * (k : ℝ)^(-C.smoothness) ≤ η0 →
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E),
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ →
      ∀ x y, Q.c ≤ ternaryMass Q.a
        (highUnionSourceRegression C R (cf * (k : ℝ)^(-C.smoothness)) h x) V y := by
  obtain ⟨Cfr,hCfr,hbound⟩ := highFrameField_original_model_bounds C
  obtain ⟨η0,hη0,hguard⟩ := highFrame_ternary_amplitude_guards Q
  refine ⟨Cfr,η0,hCfr,hη0,?_⟩
  intro k F hk0 horder hk I hI E hE R M G cf hcf hη h V hV x y
  letI := hk0
  letI := horder
  letI := hI
  letI := hE
  let η := cf * (k : ℝ)^(-C.smoothness)
  let P := fun j => highFramePolynomial ((highUnionSourceState C R h).2 j)
  have hP (j) : frameCoefficientL1 (P j) ≤ Cfr⁻¹ :=
    (highFramePolynomial_coefficientL1_le _).trans (highUnionSourceState_coefficient_ball C R G h j)
  have hηn : 0 ≤ η := by dsimp [η]; positivity
  obtain ⟨_, hηsup⟩ := hguard η hηn hη
  have hv := (hbound k hk0 hk cf hcf P hP).1 x
  have hf : |highUnionSourceRegression C R η h x| ≤ Q.ρ :=
    hv.trans (hηsup.trans (by linarith [Q.ρ_pos]))
  exact (Q.legal _ V hf hV).2.2.1 y

end NearlyMinimax
