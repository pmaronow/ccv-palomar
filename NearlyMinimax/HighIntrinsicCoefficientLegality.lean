module

public import NearlyMinimax.HighIntrinsicFieldLegality
public import NearlyMinimax.HighFrameEvaluation


@[expose] public section

/-! Literal finite coefficient-state specialization of intrinsic frame legality. -/
noncomputable section
open Set
open scoped BigOperators ENNReal
namespace NearlyMinimax

 theorem highFrameCoefficientField_intrinsic_holderNorm {d D : ℕ}
    (C : ModelConstants d) (k : ℕ) [NeZero k] (hk : 4 ≤ k) (cf : ℝ) (hcf : 0 ≤ cf)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (hc : ∀ j, (∑ γ, |c j γ|) ≤ (highIntrinsicFrameConstant C)⁻¹)
    (U : Set (Covariate d)) :
    holderNorm U (highFrameField d k (cf*(k : ℝ)^(-C.smoothness))
      (fun j => highFramePolynomial (c j))) C.order C.alpha ≤
      ENNReal.ofReal (highWindowHolderConstant C*cf) :=
  (highFrameField_intrinsic_original_model_bounds C k hk cf hcf _
    (fun j => (highFramePolynomial_coefficientL1_le (c j)).trans (hc j))).2.2.2 U

 theorem highFrameCoefficientField_intrinsic_value {d D : ℕ}
    (C : ModelConstants d) (k : ℕ) [NeZero k] (hk : 4 ≤ k) (cf : ℝ) (hcf : 0 ≤ cf)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (hc : ∀ j, (∑ γ, |c j γ|) ≤ (highIntrinsicFrameConstant C)⁻¹)
    (x : Covariate d) :
    |highFrameField d k (cf*(k : ℝ)^(-C.smoothness))
      (fun j => highFramePolynomial (c j)) x| ≤
      (2 : ℝ)^d*(cf*(k : ℝ)^(-C.smoothness)) :=
  (highFrameField_intrinsic_original_model_bounds C k hk cf hcf _
    (fun j => (highFramePolynomial_coefficientL1_le (c j)).trans (hc j))).1 x

end NearlyMinimax
