module

public import NearlyMinimax.HighFrameLegality
public import NearlyMinimax.SpatialCardinalCovariance


@[expose] public section

/-! Exact bridge from the manuscript's finite total-degree coefficient
frame to the genuine polynomial fields used in original-model legality. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem frameCoefficientL1_sum_monomial_le {d : ℕ} {I : Type*} [Fintype I]
    (e : I → Fin d →₀ ℕ) (c : I → ℝ) :
    frameCoefficientL1 (∑ i, MvPolynomial.monomial (e i) (c i)) ≤ ∑ i, |c i| := by
  classical
  let P : MvPolynomial (Fin d) ℝ := ∑ i, MvPolynomial.monomial (e i) (c i)
  change (∑ β ∈ P.support, |P.coeff β|) ≤ _
  calc
    _ ≤ ∑ β ∈ P.support, ∑ i, |(MvPolynomial.monomial (e i) (c i)).coeff β| := by
      apply Finset.sum_le_sum
      intro β hβ
      change |(∑ i, MvPolynomial.monomial (e i) (c i)).coeff β| ≤ _
      rw [MvPolynomial.coeff_sum]
      simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ
        (fun i => (MvPolynomial.monomial (e i) (c i)).coeff β)
    _ = ∑ i, ∑ β ∈ P.support, |(MvPolynomial.monomial (e i) (c i)).coeff β| :=
      Finset.sum_comm
    _ ≤ ∑ i, |c i| := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [MvPolynomial.coeff_monomial, apply_ite abs, abs_zero]
      rw [Finset.sum_ite_eq]
      split_ifs
      · exact le_rfl
      · exact abs_nonneg _

def highFramePolynomial {d D : ℕ} (c : HighFrameIndex d D → ℝ) :
    MvPolynomial (Fin d) ℝ :=
  ∑ γ, MvPolynomial.monomial (polynomialBoxExponent γ.val) (c γ)

theorem highFramePolynomial_coefficientL1_le {d D : ℕ} (c : HighFrameIndex d D → ℝ) :
    frameCoefficientL1 (highFramePolynomial c) ≤ ∑ γ, |c γ| :=
  frameCoefficientL1_sum_monomial_le _ _

theorem highFramePolynomial_totalDegree_le {d D : ℕ} (c : HighFrameIndex d D → ℝ) :
    (highFramePolynomial c).totalDegree ≤ D - 1 := by
  classical
  unfold highFramePolynomial
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro γ hγ
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simpa only [polynomial_box_exponent_apply, Function.id_def] using γ.property

theorem highFramePolynomial_scaled_eval {d D : ℕ} (c : HighFrameIndex d D → ℝ)
    (x : Covariate d) :
    MvPolynomial.eval x (frameScaledPolynomial (highFramePolynomial c)) =
      ∑ γ, c γ * highFrameFeature x γ := by
  classical
  rw [frameScaledPolynomial_eval]
  simp only [highFramePolynomial, map_sum, MvPolynomial.eval_monomial,
    highFrameFeature]
  apply Finset.sum_congr rfl
  intro γ hγ
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp only [polynomial_box_exponent_apply]

theorem highFramePolynomial_coefficients {d D : ℕ} (c : HighFrameIndex d D → ℝ)
    (γ : HighFrameIndex d D) : highFrameCoefficients (highFramePolynomial c) γ = c γ := by
  classical
  unfold highFrameCoefficients highFramePolynomial
  rw [MvPolynomial.coeff_sum]
  have he (δ : HighFrameIndex d D) : polynomialBoxExponent δ.val = polynomialBoxExponent γ.val ↔
      δ = γ := by
    constructor
    · intro h
      exact Subtype.ext (polynomial_box_exponent_injective h)
    · rintro rfl
      rfl
  simp only [MvPolynomial.coeff_monomial, he]
  simp

end NearlyMinimax
