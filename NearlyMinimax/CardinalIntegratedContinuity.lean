module

public import NearlyMinimax.CardinalBandSpatial
public import NearlyMinimax.SpatialCardinalContinuity


@[expose] public section

/-! Continuity of the actual integrated cardinal matrices and weights,
including every collision configuration. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem spatial_centered_cardinal_scale_joint_continuous {d n : ℕ} (i : Fin n) (lam : ℝ) :
    Continuous (fun z : (Fin n → Covariate d) × SpatialScaleVector i =>
      spatialCardinalScale lam (spatialScaleExtend i z.2) z.1 i) := by
  simp_rw [spatial_cardinal_scale_product]
  unfold spatialSquaredDistance
  fun_prop

theorem spatial_centered_cardinal_matrix_joint_continuous {d n D : ℕ} (i : Fin n) (lam : ℝ)
    (β β' : HighFrameIndex d D) :
    Continuous (fun z : (Fin n → Covariate d) × SpatialScaleVector i =>
      spatialCenteredCardinalMatrix i lam z.1 z.2 β β') := by
  have hc (γ : HighFrameIndex d D) : Continuous (fun z : (Fin n → Covariate d) × SpatialScaleVector i =>
      highFrameCoefficients (spatialCardinalPolynomial z.1 i) γ) :=
    (spatial_cardinal_polynomial_coefficients_continuous i (polynomialBoxExponent γ.val)).comp continuous_fst
  exact ((spatial_centered_cardinal_scale_joint_continuous i lam).mul (hc β)).mul (hc β')

theorem integrated_cardinal_matrix_continuous {d n D : ℕ} (lam : ℝ) {T : ℝ} (hT : 1 ≤ T)
    (β β' : HighFrameIndex d D) :
    Continuous (fun U : Fin n → Covariate d => integratedCardinalMatrix lam T U β β') := by
  unfold integratedCardinalMatrix spatialScaleMeasure
  apply continuous_finsetSum
  intro i hi
  exact continuous_parametric_integral_of_continuous
    (spatial_centered_cardinal_matrix_joint_continuous i lam β β')
    (spatial_scale_domain_isCompact i T hT)

theorem spatial_cardinal_weight_joint_continuous {d n : ℕ} (i : Fin n) (lam : ℝ) :
    Continuous (fun z : (Fin n → Covariate d) × SpatialScaleVector i =>
      spatialCardinalWeight lam (spatialScaleExtend i z.2) z.1 i) := by
  simp_rw [spatial_cardinal_weight_scale_product]
  unfold spatialUnaryWeight spatialSquaredDistance
  fun_prop

theorem integrated_cardinal_weight_continuous {d n : ℕ} (i : Fin n) (lam : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    Continuous (fun U : Fin n → Covariate d => integratedCardinalWeight lam T U i) := by
  unfold integratedCardinalWeight spatialScaleMeasure
  exact continuous_parametric_integral_of_continuous
    (spatial_cardinal_weight_joint_continuous i lam) (spatial_scale_domain_isCompact i T hT)

theorem integrated_cardinal_band_continuous {d n D : ℕ} (lam : ℝ) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T)
    (β β' : HighFrameIndex d D) :
    Continuous (fun U : Fin n → Covariate d =>
      integratedCardinalMatrix lam T U β β' - integratedCardinalMatrix lam L U β β') :=
  (integrated_cardinal_matrix_continuous lam hT β β').sub
    (integrated_cardinal_matrix_continuous lam hL β β')

end NearlyMinimax
