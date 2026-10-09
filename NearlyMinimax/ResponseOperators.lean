module

public import NearlyMinimax.PairWindowMoments
public import Mathlib.Analysis.InnerProductSpace.Symmetric


@[expose] public section

/-! The actual three-coordinate quadratic response operators used by the
paper's normalized pair statistic. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

abbrev PairVector := EuclideanSpace ℝ (Fin 3)

def pairResponseVector (y y' : ℝ) : PairVector := WithLp.toLp 2 ![y', y, 1]

def pairCoordinateVector (i : Fin 3) : PairVector :=
  WithLp.toLp 2 (Pi.single i 1)

def pairNoiseOperator : PairVector →L[ℝ] PairVector :=
  InnerProductSpace.rankOne ℝ (pairCoordinateVector 0) (pairCoordinateVector 0) +
    InnerProductSpace.rankOne ℝ (pairCoordinateVector 1) (pairCoordinateVector 1)

def pairScoreOperator (V y y' : ℝ) : PairVector →L[ℝ] PairVector :=
  InnerProductSpace.rankOne ℝ (pairResponseVector y y') (pairResponseVector y y') -
    V • pairNoiseOperator

theorem pairResponseVector_norm_sq (y y' : ℝ) :
    ‖pairResponseVector y y'‖ ^ 2 = y' ^ 2 + y ^ 2 + 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [pairResponseVector, Fin.sum_univ_succ, add_assoc]

theorem pairCoordinateVector_norm (i : Fin 3) : ‖pairCoordinateVector i‖ = 1 := by
  have hs : ‖pairCoordinateVector i‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [pairCoordinateVector, Pi.single_apply, Finset.sum_ite_eq']
  nlinarith [norm_nonneg (pairCoordinateVector i)]

theorem pairNoiseOperator_norm_le : ‖pairNoiseOperator‖ ≤ 2 := by
  have h := norm_add_le
    (InnerProductSpace.rankOne ℝ (pairCoordinateVector 0) (pairCoordinateVector 0))
    (InnerProductSpace.rankOne ℝ (pairCoordinateVector 1) (pairCoordinateVector 1))
  norm_num only [InnerProductSpace.norm_rankOne, pairCoordinateVector_norm,
    one_mul] at h
  exact h

theorem pairScoreOperator_norm_sq_le (V y y' : ℝ) :
    ‖pairScoreOperator V y y'‖ ^ 2 ≤ 6 * (y ^ 4 + y' ^ 4 + 1) + 8 * V ^ 2 := by
  have hn : ‖pairScoreOperator V y y'‖ ≤ ‖pairResponseVector y y'‖ ^ 2 + 2 * |V| := by
    apply (norm_sub_le _ _).trans
    simp only [InnerProductSpace.norm_rankOne, norm_smul, Real.norm_eq_abs]
    have hp := mul_le_mul_of_nonneg_left pairNoiseOperator_norm_le (abs_nonneg V)
    change _ ≤ _
    nlinarith
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hr : ‖pairResponseVector y y'‖ ^ 4 ≤ 3 * (y ^ 4 + y' ^ 4 + 1) := by
    rw [show ‖pairResponseVector y y'‖ ^ 4 = (‖pairResponseVector y y'‖ ^ 2) ^ 2 by ring,
      pairResponseVector_norm_sq]
    nlinarith [sq_nonneg (y ^ 2 - y' ^ 2), sq_nonneg (y ^ 2 - 1),
      sq_nonneg (y' ^ 2 - 1)]
  have hv : |V| ^ 2 = V ^ 2 := sq_abs V
  nlinarith [sq_nonneg (‖pairResponseVector y y'‖ ^ 2 - 2 * |V|)]

theorem pairResponseVector_continuous :
    Continuous (fun z : ℝ × ℝ => pairResponseVector z.1 z.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp [pairResponseVector] <;> fun_prop

theorem pairScoreOperator_continuous (V : ℝ) :
    Continuous (fun z : ℝ × ℝ => pairScoreOperator V z.1 z.2) := by
  exact ((InnerProductSpace.rankOne ℝ).continuous.comp pairResponseVector_continuous).clm_apply
    pairResponseVector_continuous |>.sub continuous_const

theorem pairResponseVector_inner (a : PairVector) (y y' : ℝ) :
    ⟪a, pairResponseVector y y'⟫ = a 0 * y' + a 1 * y + a 2 := by
  simp only [PiLp.inner_apply, pairResponseVector, RCLike.inner_apply,
    conj_trivial]
  simp [Fin.sum_univ_succ]
  ring

theorem pairNoiseOperator_inner (a b : PairVector) :
    ⟪a, pairNoiseOperator b⟫ = a 0 * b 0 + a 1 * b 1 := by
  simp only [pairNoiseOperator, ContinuousLinearMap.add_apply, inner_add_right,
    InnerProductSpace.inner_right_rankOne_apply]
  simp [pairCoordinateVector, PiLp.inner_apply, RCLike.inner_apply]

theorem pairScoreOperator_inner_polynomial (V y y' : ℝ) (a b : PairVector) :
    ⟪a, pairScoreOperator V y y' b⟫ =
      (a 0 * b 0) * y' ^ 2 + (a 1 * b 1) * y ^ 2 +
      (a 0 * b 1 + a 1 * b 0) * (y * y') +
      (a 0 * b 2 + a 2 * b 0) * y' +
      (a 1 * b 2 + a 2 * b 1) * y + a 2 * b 2 -
      V * (a 0 * b 0 + a 1 * b 1) := by
  simp only [pairScoreOperator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, inner_sub_right, inner_smul_right,
    InnerProductSpace.inner_right_rankOne_apply, pairResponseVector_inner,
    pairNoiseOperator_inner]
  rw [real_inner_comm b (pairResponseVector y y'), pairResponseVector_inner]
  ring

end NearlyMinimax
