module

public import NearlyMinimax.ResponseOperators
public import NearlyMinimax.PairDesignMeasure
public import NearlyMinimax.ModelRegularity
public import NearlyMinimax.Risk


@[expose] public section

/-! Globally bounded versions of the population response operators, equal
to the original regression operators almost everywhere for the pair measure. -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

def boundedRegression {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (x : Covariate d) : ℝ := clip (-C.holderBound) C.holderBound (θ.regression x)

theorem boundedRegression_abs_le {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (x : Covariate d) : |boundedRegression C θ x| ≤ C.holderBound := by
  have h := clip_mem_Icc (x := θ.regression x)
    (show -C.holderBound ≤ C.holderBound by linarith [C.holderBound_pos])
  exact abs_le.2 h

theorem boundedRegression_measurable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) : Measurable (boundedRegression C θ) :=
  (clip_lipschitz _ _).continuous.measurable.comp hθ.2.1

theorem boundedRegression_eq_on_cube {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) {x : Covariate d}
    (hx : x ∈ unitCube d) : boundedRegression C θ x = θ.regression x := by
  have h := abs_le.mp (admissible_regression_value_bound C θ hθ x hx)
  exact clip_target h.1 h.2

def boundedPairRegressionOperator {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (w : Covariate d × Covariate d) : PairVector →L[ℝ] PairVector :=
  InnerProductSpace.rankOne ℝ
    (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2))
    (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2))

theorem boundedPairRegressionOperator_norm_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (w : Covariate d × Covariate d) :
    ‖boundedPairRegressionOperator C θ w‖ ≤ 2 * C.holderBound ^ 2 + 1 := by
  rw [boundedPairRegressionOperator, InnerProductSpace.norm_rankOne, ← pow_two,
    pairResponseVector_norm_sq]
  have h1 := pow_le_pow_left₀ (abs_nonneg _) (boundedRegression_abs_le C θ w.1) 2
  have h2 := pow_le_pow_left₀ (abs_nonneg _) (boundedRegression_abs_le C θ w.2) 2
  simp only [sq_abs] at h1 h2
  linarith

theorem boundedPairRegressionOperator_symmetric {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (w : Covariate d × Covariate d) (a b : PairVector) :
    ⟪a, boundedPairRegressionOperator C θ w b⟫ = ⟪boundedPairRegressionOperator C θ w a, b⟫ := by
  simp only [boundedPairRegressionOperator, InnerProductSpace.rankOne_apply,
    inner_smul_right, inner_smul_left, real_inner_comm, starRingEnd_apply, star_trivial]
  ring

theorem boundedPairRegressionOperator_measurable_apply {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    Measurable (fun z : (Covariate d × Covariate d) × PairVector =>
      boundedPairRegressionOperator C θ z.1 z.2) := by
  have hv : Measurable (fun w : Covariate d × Covariate d =>
      pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2)) :=
    pairResponseVector_continuous.measurable.comp
      (((boundedRegression_measurable C θ hθ).comp measurable_fst).prodMk
        ((boundedRegression_measurable C θ hθ).comp measurable_snd))
  simp only [boundedPairRegressionOperator, InnerProductSpace.rankOne_apply]
  have hi : Measurable (fun z : (Covariate d × Covariate d) × PairVector =>
      ⟪pairResponseVector (boundedRegression C θ z.1.1) (boundedRegression C θ z.1.2), z.2⟫) :=
    (hv.comp measurable_fst).inner measurable_snd
  have hs : Continuous (fun z : ℝ × PairVector => z.1 • z.2) :=
    continuous_fst.smul continuous_snd
  exact hs.measurable.comp (hi.prodMk (hv.comp measurable_fst))

theorem regularPairDesignMeasure_cube_ae {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (k : ℕ) (hk : 0 < k) :
    ∀ᵐ w ∂regularPairDesignMeasure θ k hk, w.1 ∈ unitCube d ∧ w.2 ∈ unitCube d := by
  let := designLaw_isProbability C θ hθ
  have h : regularPairDesignMeasure θ k hk ≪ (designLaw θ).prod (designLaw θ) :=
    Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict
  apply h.ae_le
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := designLaw θ) (ν := designLaw θ)).ae
      (designLaw_cube_ae θ),
    (Measure.quasiMeasurePreserving_snd (μ := designLaw θ) (ν := designLaw θ)).ae
      (designLaw_cube_ae θ)] with w hx hy
  exact ⟨hx, hy⟩

theorem boundedPairRegressionOperator_eq_ae {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    boundedPairRegressionOperator C θ =ᵐ[regularPairDesignMeasure θ k hk]
      (fun w => InnerProductSpace.rankOne ℝ (pairResponseVector (θ.regression w.1) (θ.regression w.2))
        (pairResponseVector (θ.regression w.1) (θ.regression w.2))) := by
  filter_upwards [regularPairDesignMeasure_cube_ae C θ hθ k hk] with w hw
  simp only [boundedPairRegressionOperator, boundedRegression_eq_on_cube C θ hθ hw.1,
    boundedRegression_eq_on_cube C θ hθ hw.2]

end NearlyMinimax
