module

public import NearlyMinimax.HighFrameCoefficientBridge


@[expose] public section

/-! Coefficient norm estimates for the actual polynomial frame. These are
algebraic bounds on polynomial coefficients and do not assume an envelope. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem frameCoefficientL1_mul {d : ℕ} (P Q : MvPolynomial (Fin d) ℝ) :
    frameCoefficientL1 (P * Q) ≤ frameCoefficientL1 P * frameCoefficientL1 Q := by
  classical
  have hP : P = ∑ β : P.support, monomial β.val (P.coeff β.val) := by
    exact P.as_sum.trans (Finset.sum_coe_sort P.support
      (fun β => monomial β (P.coeff β))).symm
  have hQ : Q = ∑ β : Q.support, monomial β.val (Q.coeff β.val) := by
    exact Q.as_sum.trans (Finset.sum_coe_sort Q.support
      (fun β => monomial β (Q.coeff β))).symm
  have hprod : P * Q = ∑ β : P.support × Q.support,
      monomial (β.1.val + β.2.val) (P.coeff β.1.val * Q.coeff β.2.val) := by
    calc
      P * Q = (∑ β : P.support, monomial β.val (P.coeff β.val)) *
          (∑ β : Q.support, monomial β.val (Q.coeff β.val)) := congrArg₂ (· * ·) hP hQ
      _ = _ := by
        simp_rw [Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial]
        rw [Fintype.sum_prod_type]
  rw [hprod]
  apply (frameCoefficientL1_sum_monomial_le _ _).trans_eq
  simp_rw [Fintype.sum_prod_type, abs_mul]
  calc
    _ = ∑ β : P.support, |P.coeff β.val| * frameCoefficientL1 Q := by
      apply Finset.sum_congr rfl
      intro β _
      rw [← Finset.mul_sum Finset.univ
        (fun γ : Q.support => |Q.coeff γ.val|) |P.coeff β.val|]
      rw [Finset.sum_coe_sort Q.support (fun γ => |Q.coeff γ|)]
      rfl
    _ = frameCoefficientL1 P * frameCoefficientL1 Q := by
      rw [← Finset.sum_mul Finset.univ
        (fun β : P.support => |P.coeff β.val|) (frameCoefficientL1 Q)]
      rw [Finset.sum_coe_sort P.support (fun β => |P.coeff β|)]
      rfl

theorem frameCoefficientL1_one {d : ℕ} :
    frameCoefficientL1 (1 : MvPolynomial (Fin d) ℝ) = 1 := by
  classical
  simp [frameCoefficientL1, MvPolynomial.support_one]

theorem frameCoefficientL1_prod {d : ℕ} {I : Type*} (s : Finset I)
    (P : I → MvPolynomial (Fin d) ℝ) :
    frameCoefficientL1 (∏ i ∈ s, P i) ≤ ∏ i ∈ s, frameCoefficientL1 (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frameCoefficientL1_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (frameCoefficientL1_mul _ _).trans
      (mul_le_mul_of_nonneg_left ih (frameCoefficientL1_nonneg _))

theorem frameCoefficientL1_coeff_sum_le {d : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (s : Finset (Fin d →₀ ℕ)) :
    (∑ β ∈ s, |P.coeff β|) ≤ frameCoefficientL1 P := by
  classical
  calc
    _ = ∑ β ∈ s ∩ P.support, |P.coeff β| := by
      symm
      apply Finset.sum_subset (Finset.inter_subset_left)
      intro β hβ hnot
      have hn : β ∉ P.support := by
        intro hm
        exact hnot (Finset.mem_inter.mpr ⟨hβ, hm⟩)
      simp [MvPolynomial.notMem_support_iff.mp hn]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun _ _ _ => abs_nonneg _)

theorem highFrameCoefficients_sum_abs_le {d D : ℕ} (P : MvPolynomial (Fin d) ℝ) :
    (∑ γ : HighFrameIndex d D, |highFrameCoefficients P γ|) ≤ frameCoefficientL1 P := by
  classical
  let e : HighFrameIndex d D → Fin d →₀ ℕ := fun γ => polynomialBoxExponent γ.val
  have he : Function.Injective e := by
    intro γ δ h
    exact Subtype.ext (polynomial_box_exponent_injective h)
  calc
    _ = ∑ β ∈ Finset.univ.image e, |P.coeff β| := by
      rw [Finset.sum_image]
      · rfl
      · intro γ _ δ _ h
        exact he h
    _ ≤ _ := frameCoefficientL1_coeff_sum_le _ _

end NearlyMinimax
