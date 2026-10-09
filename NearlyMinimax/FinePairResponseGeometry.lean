module

public import NearlyMinimax.HighCardinalScores


@[expose] public section

/-! Actual two-coordinate Hessian extraction of the finite response rule. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem high_response_matrix_two_general {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (hq : 2 ≤ q) (C a V η : ℝ) (A : ι → ι → ℝ)
    (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i)
    (g w : Fin 2 → ℝ) (φ : Fin 2 → ι → ℝ) (c : ι → ℝ) (y : Fin 2 → Fin 3) :
    responseMatrixAction q C A c (fun v => highResponseProduct a V η g w φ v y) =
      η ^ 2 * (w 0) ^ 2 * spatialFrameCovariance A φ 0 0 * highResponseVarianceTerm a V η g w φ c y 0 +
      η ^ 2 * (w 1) ^ 2 * spatialFrameCovariance A φ 1 1 * highResponseVarianceTerm a V η g w φ c y 1 +
      η ^ 2 * w 0 * w 1 * spatialFrameCovariance A φ 0 1 *
        ternaryMeanDerivative a (coefficientRegression η g w φ c 0) (y 0) *
        ternaryMeanDerivative a (coefficientRegression η g w φ c 1) (y 1) := by
  let δ := coefficientDirection η w φ c
  let f := coefficientRegression η g w φ c
  let m := fun i => ternaryMeanDerivative a (f i) (y i)
  let e := fun i => highResponseVarianceTerm a V η g w φ c y i
  have he0 : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
  have he1 : ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by decide
  have hs (v : ι → ℝ) : finiteProductSecond Finset.univ
      (fun i z => ternaryMass a (f i + z * δ v i) V (y i))
      (fun i z => δ v i * ternaryMeanDerivative a (f i + z * δ v i) (y i))
      (fun i _ => (δ v i) ^ 2 * ternaryMeanSecondDerivative a (y i)) 0 =
      (2 * e 0) * (δ v 0 * δ v 0) + (2 * e 1) * (δ v 1 * δ v 1) +
        (2 * m 0 * m 1) * (δ v 0 * δ v 1) := by
    simp [finiteProductSecond, Finset.univ_fin2, he0, he1, e, highResponseVarianceTerm,
      ternary_heat_identity, m, f]
    ring
  rw [high_response_matrix_second q hq C a V η A g w φ c y]
  change (1 / 2 : ℝ) * covarianceAction C A
    (fun v => finiteProductSecond Finset.univ
      (fun i z => ternaryMass a (f i + z * δ v i) V (y i))
      (fun i z => δ v i * ternaryMeanDerivative a (f i + z * δ v i) (y i))
      (fun i _ => (δ v i) ^ 2 * ternaryMeanSecondDerivative a (y i)) 0) = _
  simp_rw [hs]
  rw [covarianceAction_add, covarianceAction_add]
  simp_rw [covarianceAction_mul]
  rw [covariance_direction_product C η A hC hA w φ c 0 0,
    covariance_direction_product C η A hC hA w φ c 1 1,
    covariance_direction_product C η A hC hA w φ c 0 1]
  dsimp [m, f, e]
  ring

def finePairCoordinatePolynomial {d : ℕ} (l : Fin d) : MvPolynomial (Fin d) ℝ := C 8 * X l

def finePairSquarePolynomial (d : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ l, (finePairCoordinatePolynomial l) ^ 2

theorem finePairCoordinatePolynomial_degree {d : ℕ} (l : Fin d) :
    (finePairCoordinatePolynomial l).totalDegree ≤ 1 := by
  exact (totalDegree_mul _ _).trans (by simp [finePairCoordinatePolynomial])

theorem finePairSquarePolynomial_degree (d : ℕ) :
    (finePairSquarePolynomial d).totalDegree ≤ 2 := by
  unfold finePairSquarePolynomial
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro l _
  exact (totalDegree_pow _ _).trans (by nlinarith only [finePairCoordinatePolynomial_degree l])

theorem finePairCoordinatePolynomial_eval {d : ℕ} (l : Fin d) (x : Covariate d) :
    eval (fun r => x r / 8) (finePairCoordinatePolynomial l) = x l := by
  simp only [finePairCoordinatePolynomial, map_mul, eval_C, eval_X]
  ring

theorem finePairSquarePolynomial_eval (d : ℕ) (x : Covariate d) :
    eval (fun r => x r / 8) (finePairSquarePolynomial d) = ∑ r, (x r) ^ 2 := by
  simp only [finePairSquarePolynomial, map_sum, map_pow, finePairCoordinatePolynomial_eval]

def finePairUnitMatrix (d F : ℕ) (β β' : HighFrameIndex d F) : ℝ :=
  highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β * highFrameCoefficients 1 β'

def finePairDistanceMatrix (d F : ℕ) (β β' : HighFrameIndex d F) : ℝ :=
  (∑ l : Fin d, 2 * highFrameCoefficients (finePairCoordinatePolynomial l) β *
    highFrameCoefficients (finePairCoordinatePolynomial l) β') -
    highFrameCoefficients (finePairSquarePolynomial d) β * highFrameCoefficients 1 β' -
    highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β *
      highFrameCoefficients (finePairSquarePolynomial d) β'

theorem finePairUnitMatrix_symmetric (d F : ℕ) (β β' : HighFrameIndex d F) :
    finePairUnitMatrix d F β β' = finePairUnitMatrix d F β' β := mul_comm _ _

theorem finePairDistanceMatrix_symmetric (d F : ℕ) (β β' : HighFrameIndex d F) :
    finePairDistanceMatrix d F β β' = finePairDistanceMatrix d F β' β := by
  unfold finePairDistanceMatrix
  have hs : (∑ l : Fin d, 2 * highFrameCoefficients (finePairCoordinatePolynomial l) β *
      highFrameCoefficients (finePairCoordinatePolynomial l) β') =
      ∑ l : Fin d, 2 * highFrameCoefficients (finePairCoordinatePolynomial l) β' *
        highFrameCoefficients (finePairCoordinatePolynomial l) β :=
    Finset.sum_congr rfl (fun l _ => by ring)
  rw [hs]
  ring

theorem spatial_frame_covariance_outer {κ : Type*} [Fintype κ] [DecidableEq κ]
    {n : ℕ} (u v : κ → ℝ) (φ : Fin n → κ → ℝ) (i j : Fin n) :
    spatialFrameCovariance (fun β β' => u β * v β') φ i j =
      (∑ β, φ i β * u β) * (∑ β, φ j β * v β) := by
  simp only [spatialFrameCovariance, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro β' _
  ring

theorem spatial_frame_covariance_sub {κ : Type*} [Fintype κ] [DecidableEq κ]
    {n : ℕ} (A B : κ → κ → ℝ) (φ : Fin n → κ → ℝ) (i j : Fin n) :
    spatialFrameCovariance (fun β β' => A β β' - B β β') φ i j =
      spatialFrameCovariance A φ i j - spatialFrameCovariance B φ i j := by
  simp only [spatialFrameCovariance, mul_sub, Finset.sum_sub_distrib]

theorem finePairUnitMatrix_kernel {d n F : ℕ} (U : Fin n → Covariate d) (i j : Fin n) :
    spatialFrameCovariance (finePairUnitMatrix d F) (fun l => highFrameFeature (U l)) i j = 1 := by
  unfold finePairUnitMatrix
  rw [spatial_frame_covariance_outer]
  have he (x : Covariate d) : (∑ β : HighFrameIndex d F,
      highFrameFeature x β * highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β) = 1 := by
    simpa only [map_one] using (high_frame_polynomial_evaluation (1 : MvPolynomial (Fin d) ℝ)
      (by simp) x).symm
  rw [he, he, one_mul]

theorem finePairDistanceMatrix_kernel {d n F : ℕ} (hF : 3 ≤ F)
    (U : Fin n → Covariate d) (i j : Fin n) :
    spatialFrameCovariance (finePairDistanceMatrix d F) (fun l => highFrameFeature (U l)) i j =
      -spatialSquaredDistance (U i) (U j) := by
  have hc (x : Covariate d) : (∑ β : HighFrameIndex d F,
      highFrameFeature x β * highFrameCoefficients (1 : MvPolynomial (Fin d) ℝ) β) = 1 := by
    simpa only [map_one] using (high_frame_polynomial_evaluation (1 : MvPolynomial (Fin d) ℝ)
      (by simp) x).symm
  have hl (x : Covariate d) (l : Fin d) : (∑ β : HighFrameIndex d F,
      highFrameFeature x β * highFrameCoefficients (finePairCoordinatePolynomial l) β) = x l := by
    exact (high_frame_polynomial_evaluation (finePairCoordinatePolynomial l)
      ((finePairCoordinatePolynomial_degree l).trans (by omega)) x).symm.trans
        (finePairCoordinatePolynomial_eval l x)
  have hs (x : Covariate d) : (∑ β : HighFrameIndex d F,
      highFrameFeature x β * highFrameCoefficients (finePairSquarePolynomial d) β) = ∑ l, (x l) ^ 2 := by
    exact (high_frame_polynomial_evaluation (finePairSquarePolynomial d)
      ((finePairSquarePolynomial_degree d).trans (by omega)) x).symm.trans
        (finePairSquarePolynomial_eval d x)
  unfold finePairDistanceMatrix
  rw [spatial_frame_covariance_sub, spatial_frame_covariance_sub,
    spatial_frame_covariance_sum]
  simp_rw [spatial_frame_covariance_rank_one, spatial_frame_covariance_outer, hc, hl, hs]
  simp only [mul_one, one_mul, spatialSquaredDistance, Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

def finePairCombinedMatrix (d F : ℕ) (W : ℝ) (β β' : HighFrameIndex d F) : ℝ :=
  finePairUnitMatrix d F β β' + W * finePairDistanceMatrix d F β β'

theorem finePairCombinedMatrix_symmetric (d F : ℕ) (W : ℝ) (β β' : HighFrameIndex d F) :
    finePairCombinedMatrix d F W β β' = finePairCombinedMatrix d F W β' β := by
  simp only [finePairCombinedMatrix, finePairUnitMatrix_symmetric d F β β',
    finePairDistanceMatrix_symmetric d F β β']

theorem spatial_frame_covariance_scalar {κ : Type*} [Fintype κ] [DecidableEq κ]
    {n : ℕ} (A : κ → κ → ℝ) (W : ℝ) (φ : Fin n → κ → ℝ) (i j : Fin n) :
    spatialFrameCovariance (fun β β' => W * A β β') φ i j = W * spatialFrameCovariance A φ i j := by
  simp only [spatialFrameCovariance, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro β' _
  ring

theorem finePairCombinedMatrix_kernel {d n F : ℕ} (hF : 3 ≤ F) (W : ℝ)
    (U : Fin n → Covariate d) (i j : Fin n) :
    spatialFrameCovariance (finePairCombinedMatrix d F W) (fun l => highFrameFeature (U l)) i j =
      1 - W * spatialSquaredDistance (U i) (U j) := by
  unfold finePairCombinedMatrix
  rw [spatial_frame_covariance_add, spatial_frame_covariance_scalar,
    finePairUnitMatrix_kernel, finePairDistanceMatrix_kernel hF]
  ring

/-- Exact two-observation remainder after the single diagonal variance
correction, with the paper's concrete fixed coefficient matrices. -/
theorem finePairResponseCountTwo_numerator {d F : ℕ} (hF : 3 ≤ F)
    (q : ℕ) (hq : 2 ≤ q) (C a V η W : ℝ) (hC : C ≠ 0)
    (U : Fin 2 → Covariate d) (p g w : Fin 2 → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin 2 → Fin 3) :
    (p 0 * p 1) * responseMatrixAction q C (finePairCombinedMatrix d F W) c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
      η ^ 2 * (p 0 * p 1) * ∑ i, (w i) ^ 2 *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i =
      η ^ 2 * w 0 * w 1 * p 0 * p 1 *
        (1 - W * spatialSquaredDistance (U 0) (U 1)) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 0) (y 0) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 1) (y 1) := by
  rw [high_response_matrix_two_general q hq C a V η (finePairCombinedMatrix d F W) hC
    (finePairCombinedMatrix_symmetric d F W), Fin.sum_univ_two]
  simp only [finePairCombinedMatrix_kernel hF, spatialSquaredDistance, sub_self,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero, sub_zero, mul_one]
  ring

end NearlyMinimax
