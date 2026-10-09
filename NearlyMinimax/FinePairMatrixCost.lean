module

public import NearlyMinimax.FinePairResponseGeometry
public import NearlyMinimax.CardinalCoefficientBounds


@[expose] public section

/-! Fixed coefficient costs for the two actual fine-pair response matrices.
The caps depend only on d and are uniform in the frame truncation F. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem finePairCoordinatePolynomial_monomial {d : ℕ} (l : Fin d) :
    finePairCoordinatePolynomial l = monomial (Finsupp.single l 1) 8 := by
  exact C_mul_X_eq_monomial

theorem finePairSquarePolynomial_monomial_sum (d : ℕ) :
    finePairSquarePolynomial d = ∑ l : Fin d,
      monomial (Finsupp.single l 1 + Finsupp.single l 1) (64 : ℝ) := by
  unfold finePairSquarePolynomial
  simp only [finePairCoordinatePolynomial_monomial, pow_two, monomial_mul]
  norm_num

theorem finePairCoordinateCoefficients_l1_le {d F : ℕ} (l : Fin d) :
    (∑ β : HighFrameIndex d F, |highFrameCoefficients (finePairCoordinatePolynomial l) β|) ≤ 8 := by
  apply (highFrameCoefficients_sum_abs_le _).trans
  rw [finePairCoordinatePolynomial_monomial]
  simp [frameCoefficientL1, MvPolynomial.support_monomial]

theorem finePairSquareCoefficients_l1_le (d F : ℕ) :
    (∑ β : HighFrameIndex d F, |highFrameCoefficients (finePairSquarePolynomial d) β|) ≤ 64 * d := by
  apply (highFrameCoefficients_sum_abs_le _).trans
  rw [finePairSquarePolynomial_monomial_sum]
  apply (frameCoefficientL1_sum_monomial_le _ _).trans_eq
  simp only [show |(64 : ℝ)| = 64 by norm_num, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem finePairUnitCoefficients_l1_le (d F : ℕ) :
    (∑ β : HighFrameIndex d F, |highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β|) ≤ 1 :=
  (highFrameCoefficients_sum_abs_le _).trans_eq frameCoefficientL1_one

theorem spatial_matrix_l1_outer {d F : ℕ} (u v : HighFrameIndex d F → ℝ) :
    spatialMatrixL1 (fun β β' => u β * v β') =
      (∑ β, |u β|) * (∑ β, |v β|) := by
  simp only [spatialMatrixL1, abs_mul, ← Finset.mul_sum, ← Finset.sum_mul]

theorem spatial_matrix_l1_sub_le {d F : ℕ}
    (A B : HighFrameIndex d F → HighFrameIndex d F → ℝ) :
    spatialMatrixL1 (fun β β' => A β β' - B β β') ≤ spatialMatrixL1 A + spatialMatrixL1 B := by
  simp only [spatialMatrixL1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun β _ => Finset.sum_le_sum (fun β' _ => abs_sub _ _))

theorem spatial_matrix_l1_sum_le {d F : ℕ} {I : Type*} [Fintype I]
    (A : I → HighFrameIndex d F → HighFrameIndex d F → ℝ) :
    spatialMatrixL1 (fun β β' => ∑ i, A i β β') ≤ ∑ i, spatialMatrixL1 (A i) := by
  unfold spatialMatrixL1
  apply (Finset.sum_le_sum (fun β _ => Finset.sum_le_sum
    (fun β' _ => Finset.abs_sum_le_sum_abs _ _))).trans_eq
  simp_rw [Finset.sum_comm (f := fun β' i => |A i _ β'|)]
  rw [Finset.sum_comm]

theorem spatial_matrix_l1_scalar {d F : ℕ} (t : ℝ)
    (A : HighFrameIndex d F → HighFrameIndex d F → ℝ) :
    spatialMatrixL1 (fun β β' => t * A β β') = |t| * spatialMatrixL1 A := by
  simp only [spatialMatrixL1, abs_mul, ← Finset.mul_sum]

theorem finePairUnitMatrix_l1_le (d F : ℕ) :
    spatialMatrixL1 (finePairUnitMatrix d F) ≤ 1 := by
  unfold finePairUnitMatrix
  rw [spatial_matrix_l1_outer]
  simpa only [one_mul] using mul_le_mul (finePairUnitCoefficients_l1_le d F)
    (finePairUnitCoefficients_l1_le d F) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 1)

private def finePairMatrixEntryCost {κ : Type*} [Fintype κ] (A : κ → κ → ℝ) : ℝ :=
  ∑ i, ∑ j, |A i j|

private theorem fine_pair_entry_cost_outer {κ : Type*} [Fintype κ] (u v : κ → ℝ) :
    finePairMatrixEntryCost (fun i j => u i * v j) = (∑ i, |u i|) * (∑ j, |v j|) := by
  simp only [finePairMatrixEntryCost, abs_mul, ← Finset.mul_sum, ← Finset.sum_mul]

private theorem fine_pair_entry_cost_sub_le {κ : Type*} [Fintype κ] (A B : κ → κ → ℝ) :
    finePairMatrixEntryCost (fun i j => A i j - B i j) ≤ finePairMatrixEntryCost A + finePairMatrixEntryCost B := by
  simp only [finePairMatrixEntryCost, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => abs_sub _ _))

private theorem fine_pair_entry_cost_sum_le {κ I : Type*} [Fintype κ] [Fintype I]
    (A : I → κ → κ → ℝ) :
    finePairMatrixEntryCost (fun i j => ∑ l, A l i j) ≤ ∑ l, finePairMatrixEntryCost (A l) := by
  unfold finePairMatrixEntryCost
  apply (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
    (fun j _ => Finset.abs_sum_le_sum_abs _ _))).trans_eq
  simp_rw [Finset.sum_comm (f := fun j l => |A l _ j|)]
  rw [Finset.sum_comm]

private theorem fine_pair_entry_cost_scalar {κ : Type*} [Fintype κ] (t : ℝ) (A : κ → κ → ℝ) :
    finePairMatrixEntryCost (fun i j => t * A i j) = |t| * finePairMatrixEntryCost A := by
  simp only [finePairMatrixEntryCost, abs_mul, ← Finset.mul_sum]

private theorem finite_quadratic_matrix_cost {κ : Type*} [Fintype κ] (d : ℕ)
    (c0 cs : κ → ℝ) (cl : Fin d → κ → ℝ)
    (h0 : (∑ β, |c0 β|) ≤ 1) (hs : (∑ β, |cs β|) ≤ 64 * d)
    (hl : ∀ l, (∑ β, |cl l β|) ≤ 8) :
    finePairMatrixEntryCost (fun β β' => (∑ l, 2 * cl l β * cl l β') -
      cs β * c0 β' - c0 β * cs β') ≤ 256 * d := by
  let B (β β' : κ) : ℝ := ∑ l, 2 * cl l β * cl l β'
  have houterS : finePairMatrixEntryCost (fun β β' => cs β * c0 β') ≤ 64 * d := by
    rw [fine_pair_entry_cost_outer]
    exact (mul_le_mul hs h0
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)).trans_eq (mul_one _)
  have houterS' : finePairMatrixEntryCost (fun β β' => c0 β * cs β') ≤ 64 * d := by
    rw [fine_pair_entry_cost_outer, mul_comm]
    exact (mul_le_mul hs h0
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)).trans_eq (mul_one _)
  have hB : finePairMatrixEntryCost B ≤ 128 * d := by
    apply (fine_pair_entry_cost_sum_le (fun l β β' => 2 * cl l β * cl l β')).trans
    calc
      _ ≤ ∑ _l : Fin d, (128 : ℝ) := by
        apply Finset.sum_le_sum
        intro l _
        have he : (fun β β' : κ => 2 * cl l β * cl l β') =
            (fun β β' => 2 * (cl l β * cl l β')) := by funext β β'; ring
        rw [he, fine_pair_entry_cost_scalar, fine_pair_entry_cost_outer]
        have hh := mul_le_mul (hl l) (hl l)
          (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num : (0 : ℝ) ≤ 8)
        exact (mul_le_mul_of_nonneg_left hh (abs_nonneg (2 : ℝ))).trans_eq (by norm_num)
      _ = _ := by simp; ring
  change finePairMatrixEntryCost (fun β β' => B β β' - cs β * c0 β' - c0 β * cs β') ≤ _
  have hsub : finePairMatrixEntryCost (fun β β' => B β β' - cs β * c0 β') ≤
      finePairMatrixEntryCost B + finePairMatrixEntryCost (fun β β' => cs β * c0 β') :=
    fine_pair_entry_cost_sub_le B (fun β β' => cs β * c0 β')
  have hsub' : finePairMatrixEntryCost (fun β β' => B β β' - cs β * c0 β' - c0 β * cs β') ≤
      finePairMatrixEntryCost (fun β β' => B β β' - cs β * c0 β') +
        finePairMatrixEntryCost (fun β β' => c0 β * cs β') :=
    fine_pair_entry_cost_sub_le (fun β β' => B β β' - cs β * c0 β')
      (fun β β' => c0 β * cs β')
  have hh : finePairMatrixEntryCost (fun β β' => B β β' - cs β * c0 β' - c0 β * cs β') ≤
      (128 * d + 64 * d) + 64 * d :=
    (hsub'.trans (add_le_add hsub (le_refl _))).trans
      (add_le_add (add_le_add hB houterS) houterS')
  exact hh.trans_eq (by ring)


theorem spatial_matrix_l1_quadratic_three_le (d F : ℕ)
    (c0 cs : HighFrameIndex d F → ℝ) (cl : Fin d → HighFrameIndex d F → ℝ)
    (h0 : (∑ β, |c0 β|) ≤ 1) (hs : (∑ β, |cs β|) ≤ 64 * d)
    (hl : ∀ l, (∑ β, |cl l β|) ≤ 8) :
    spatialMatrixL1 (fun β β' => (∑ l, 2 * cl l β * cl l β') -
      cs β * c0 β' - c0 β * cs β') ≤ 256 * d :=
  finite_quadratic_matrix_cost d c0 cs cl h0 hs hl

theorem finePairDistanceMatrix_l1_le (d F : ℕ) :
    spatialMatrixL1 (finePairDistanceMatrix d F) ≤ 256 * d :=
  spatial_matrix_l1_quadratic_three_le d F _ _ _
    (finePairUnitCoefficients_l1_le d F) (finePairSquareCoefficients_l1_le d F)
    (fun l => finePairCoordinateCoefficients_l1_le l)


end NearlyMinimax
