module

public import NearlyMinimax.FinePairRowMass
public import NearlyMinimax.FinePairMatrixCost
public import NearlyMinimax.HigherBandActivity


@[expose] public section

/-! Activity bounds of all three genuine fine-pair rows. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

def sourceResponseCost (q : ℕ) (C : ℝ) : ℝ :=
  (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2)

theorem sourceResponseCost_nonneg (q : ℕ) (C : ℝ) : 0 ≤ sourceResponseCost q C := by
  unfold sourceResponseCost
  positivity

theorem finePairDensityWeight_le_base (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (M : ℕ) :
    (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) ≤
      2 * (ordinaryDensityActivityBase a b)^2 * Real.exp ((M : ℝ) * exteriorTau ((a+b)/(b-a))) := by
  have hp : |finePairDensityPrefactor a b| = |b / densityMargin a b 0|^2 := by
    simp only [finePairDensityPrefactor, abs_div, abs_pow, div_pow]
  have he : Real.exp (2 * exteriorTau ((a+b)/(b-a))) ≤
      Real.exp (1 + exteriorTau ((a+b)/(b-a)))^2 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num
  apply (finePairDensityWeight_exponential_cost a b ha hab M).trans
  rw [hp, ordinaryDensityActivityBase, mul_pow]
  have h0 := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * |b / densityMargin a b 0|^2)
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  nlinarith only [h0]

theorem finePairRowMass_unit_le (d D M q : ℕ) (hD : 1 ≤ D)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C ℓ N : ℝ) :
    finePairRowMass d D M q a b C ℓ N .unit ≤
      (ordinaryDensityActivityBase a b)^2 * (D : ℝ)^2 *
        Real.exp ((D : ℝ) * exteriorTau ((a+b)/(b-a))) * sourceResponseCost q C := by
  rw [finePairRowMass_unit]
  have hden := densityPacketWeight_exponential_cost a b ha hab D 2 D (by norm_num) hD
  have hmat := finePairUnitMatrix_l1_le d D
  have hc : 0 ≤ (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) := by positivity
  have hm := mul_le_mul hden hmat (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hm hc
  dsimp [ordinaryDensityActivityBase, sourceResponseCost, spatialMatrixL1] at *
  nlinarith only [hh]

theorem finePairRowMass_coarse_le (d : ℕ) [NeZero d] (D M q : ℕ) (hD : 1 ≤ D)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C ℓ N : ℝ) (hℓ : 0 ≤ ℓ) :
    finePairRowMass d D M q a b C ℓ N .coarse ≤
      (ordinaryDensityActivityBase a b)^2 * (D : ℝ)^2 *
        Real.exp ((D : ℝ) * exteriorTau ((a+b)/(b-a))) * sourceResponseCost q C *
          ((128 * (d : ℝ)) * ℓ^2) := by
  rw [finePairRowMass_coarse d D M q a b C ℓ N hℓ]
  have hden := densityPacketWeight_exponential_cost a b ha hab D 2 D (by norm_num) hD
  have hmat := mul_le_mul_of_nonneg_right (finePairDistanceMatrix_l1_le d D)
    (by positivity : 0 ≤ ℓ^2/2)
  have hc := sourceResponseCost_nonneg q C
  have hm := mul_le_mul hden hmat (by positivity : 0 ≤
    (∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * (ℓ^2/2)) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hm hc
  dsimp [ordinaryDensityActivityBase, sourceResponseCost, spatialMatrixL1] at *
  nlinarith only [hh]

theorem finePairRowMass_fine_le (d : ℕ) [NeZero d] (D M q : ℕ)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C ℓ N : ℝ) (hℓ : 0 ≤ ℓ) (hℓN : ℓ ≤ N) :
    finePairRowMass d D M q a b C ℓ N .fine ≤
      (ordinaryDensityActivityBase a b)^2 *
        Real.exp ((M : ℝ) * exteriorTau ((a+b)/(b-a))) * sourceResponseCost q C *
          ((256 * (d : ℝ)) * N^2) := by
  rw [finePairRowMass_fine d D M q a b C ℓ N hℓ hℓN]
  have hden := finePairDensityWeight_le_base a b ha hab M
  have hdiff : 0 ≤ (N^2-ℓ^2)/2 := by nlinarith
  have hmat := mul_le_mul_of_nonneg_right (finePairDistanceMatrix_l1_le d D) hdiff
  have hmat' : (∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * ((N^2-ℓ^2)/2) ≤
      (128 * (d : ℝ)) * N^2 := by
    apply hmat.trans
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [hd0, sq_nonneg ℓ]
  have hm := mul_le_mul hden hmat' (by positivity : 0 ≤
    (∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * ((N^2-ℓ^2)/2)) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hm (sourceResponseCost_nonneg q C)
  dsimp [ordinaryDensityActivityBase, sourceResponseCost, spatialMatrixL1] at *
  nlinarith only [hh]

end NearlyMinimax
