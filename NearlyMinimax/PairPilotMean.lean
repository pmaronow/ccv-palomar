module

public import NearlyMinimax.PairOperatorMean
public import NearlyMinimax.PilotMeanLaw
public import NearlyMinimax.TwoStagePairRisk
public import NearlyMinimax.BoundedPairMeanOperators


@[expose] public section

/-! Actual same-cell pair conditional means and their two-pilot mean risk. -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω]

def pairPilotCoefficient {d : ℕ} (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω)
    (w : Covariate d × Covariate d) : PairVector := bar w + η x w

def pairPilotScoreKernel {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω × Ω) :
    Observation d × Observation d → ℝ :=
  pairScoreFieldKernel θ (pairPilotCoefficient bar η x.1) (pairPilotCoefficient bar η x.2)
    (sameLabelKernel (regularGridCell k hk))

def pairPilotNoiseKernel {d : ℕ} (k : ℕ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω × Ω) :
    Observation d × Observation d → ℝ :=
  pairNoiseFieldKernel (pairPilotCoefficient bar η x.1) (pairPilotCoefficient bar η x.2)
    (sameLabelKernel (regularGridCell k hk))

def pairPilotScoreMean {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω × Ω) : ℝ :=
  PairUStatistic.fieldPairMean (μ := observationLaw θ) ((k : ℝ) ^ d)
    (pairPilotScoreKernel θ k hk bar η) x

def pairPilotNoiseMean {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω × Ω) : ℝ :=
  PairUStatistic.fieldPairMean (μ := observationLaw θ) ((k : ℝ) ^ d)
    (pairPilotNoiseKernel k hk bar η) x

theorem pairPilotScoreMean_eq_half_pilotMean {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω × Ω)
    (hi : Integrable (pairPilotScoreKernel θ k hk bar η x)
      ((observationLaw θ).prod (observationLaw θ))) :
    pairPilotScoreMean θ k hk bar η x = (1 / 2) *
      PilotFields.pilotMean (M := regularPairDesignMeasure θ k hk) bar η
        (boundedPairRegressionOperator C θ) x := by
  let := observationLaw_isProbability C θ hθ
  rw [pairPilotScoreMean, PairUStatistic.fieldPairMean]
  have h := pairScoreFieldKernel_mean C θ hθ (pairPilotCoefficient bar η x.1)
    (pairPilotCoefficient bar η x.2) (sameLabelKernel (regularGridCell k hk)) hi
  change ((k : ℝ) ^ d / 2) * (∫ z, pairPilotScoreKernel θ k hk bar η x z
    ∂(observationLaw θ).prod (observationLaw θ)) = _
  unfold pairPilotScoreKernel
  rw [h]
  have hM := regularPairDesignMeasure_integral C θ hθ k hk (fun w =>
    ⟪pairPilotCoefficient bar η x.1 w,
      InnerProductSpace.rankOne ℝ (pairResponseVector (θ.regression w.1) (θ.regression w.2))
        (pairResponseVector (θ.regression w.1) (θ.regression w.2))
          (pairPilotCoefficient bar η x.2 w)⟫)
  rw [smul_eq_mul] at hM
  calc
    _ = (1 / 2) * ((k : ℝ) ^ d * ∫ w, sameLabelKernel (regularGridCell k hk) w *
      ⟪pairPilotCoefficient bar η x.1 w,
        InnerProductSpace.rankOne ℝ (pairResponseVector (θ.regression w.1) (θ.regression w.2))
          (pairResponseVector (θ.regression w.1) (θ.regression w.2))
            (pairPilotCoefficient bar η x.2 w)⟫ ∂(designLaw θ).prod (designLaw θ)) := by ring
    _ = (1 / 2) * (∫ w, ⟪pairPilotCoefficient bar η x.1 w,
      InnerProductSpace.rankOne ℝ (pairResponseVector (θ.regression w.1) (θ.regression w.2))
        (pairResponseVector (θ.regression w.1) (θ.regression w.2))
          (pairPilotCoefficient bar η x.2 w)⟫ ∂regularPairDesignMeasure θ k hk) := by
      rw [hM]; rfl
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [boundedPairRegressionOperator_eq_ae C θ hθ k hk] with w hw
      simp only [PilotFields.pilotMean, pairPilotCoefficient, hw]

theorem pairPilotNoiseMean_eq_half_pilotMean {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (x : Ω × Ω)
    (hi : Integrable (pairPilotNoiseKernel k hk bar η x)
      ((observationLaw θ).prod (observationLaw θ))) :
    pairPilotNoiseMean θ k hk bar η x = (1 / 2) *
      PilotFields.pilotMean (M := regularPairDesignMeasure θ k hk) bar η
        (fun _ => pairNoiseOperator) x := by
  let := observationLaw_isProbability C θ hθ
  rw [pairPilotNoiseMean, PairUStatistic.fieldPairMean]
  have h := pairNoiseFieldKernel_mean C θ hθ (pairPilotCoefficient bar η x.1)
    (pairPilotCoefficient bar η x.2) (sameLabelKernel (regularGridCell k hk)) hi
  change ((k : ℝ) ^ d / 2) * (∫ z, pairPilotNoiseKernel k hk bar η x z
    ∂(observationLaw θ).prod (observationLaw θ)) = _
  unfold pairPilotNoiseKernel
  rw [h]
  have hM := regularPairDesignMeasure_integral C θ hθ k hk (fun w =>
    ⟪pairPilotCoefficient bar η x.1 w, pairNoiseOperator (pairPilotCoefficient bar η x.2 w)⟫)
  simp only [smul_eq_mul, pairPilotCoefficient] at hM
  simp only [PilotFields.pilotMean, pairPilotCoefficient]
  rw [hM]
  ring

section HalfMean
variable {W H : Type*} [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]

theorem half_pilotMean_mean_eq (bar : W → H) (hbarMeas : Measurable bar) (hbar : MemLp bar 2 M)
    {η : Ω → W → H} (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
    {B : W → H →L[ℝ] H} (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {cB lam : ℝ} (hcB : 0 ≤ cB) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ cB)
    (hsym : ∀ w a b, ⟪a, B w b⟫ = ⟪B w a, b⟫)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, PilotFields.test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    (∫ x, (1 / 2) * PilotFields.pilotMean (M := M) bar η B x ∂μ.prod μ) =
      (1 / 2) * ∫ w, ⟪bar w, B w (bar w)⟫ ∂M := by
  rw [integral_const_mul,
    PilotFields.pilotMean_mean_eq bar hbarMeas hbar hmη hη hcenter hmB hcB hlam hbound hsym htest]

theorem half_pilotMean_centered_sq_le (bar : W → H) (hbarMeas : Measurable bar) (hbar : MemLp bar 2 M)
    {η : Ω → W → H} (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
    {B : W → H →L[ℝ] H} (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {cB lam : ℝ} (hcB : 0 ≤ cB) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ cB)
    (hsym : ∀ w a b, ⟪a, B w b⟫ = ⟪B w a, b⟫)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, PilotFields.test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M) :
    (∫ x, ((1 / 2) * PilotFields.pilotMean (M := M) bar η B x -
      ∫ z, (1 / 2) * PilotFields.pilotMean (M := M) bar η B z ∂μ.prod μ) ^ 2 ∂μ.prod μ) ≤
      (3 / 4) * lam * cB ^ 2 * (2 * (∫ w, ‖bar w‖ ^ 2 ∂M) +
        ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) := by
  rw [half_pilotMean_mean_eq bar hbarMeas hbar hmη hη hcenter hmB hcB hlam hbound hsym htest]
  have he : (fun x => ((1 / 2) * PilotFields.pilotMean (M := M) bar η B x -
      (1 / 2) * ∫ w, ⟪bar w, B w (bar w)⟫ ∂M) ^ 2) =
      (fun x => (1 / 4) * (PilotFields.pilotMean (M := M) bar η B x -
        ∫ w, ⟪bar w, B w (bar w)⟫ ∂M) ^ 2) := by funext x; ring
  rw [he, integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (PilotFields.pilotMean_centered_sq_le bar hbarMeas hbar hmη hη hmB hcB hlam hbound hsym htest)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  convert h using 1 <;> ring

theorem half_pilotMean_variance_transfer (bar : W → H) (hbarMeas : Measurable bar) (hbar : MemLp bar 2 M)
    {η : Ω → W → H} (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
    (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
    {B : W → H →L[ℝ] H} (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {cB lam : ℝ} (hcB : 0 ≤ cB) (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ cB)
    (hsym : ∀ w a b, ⟪a, B w b⟫ = ⟪B w a, b⟫)
    (htest : ∀ v : W → H, MemLp v 2 M →
      (∫ x, PilotFields.test (M := M) η v x ^ 2 ∂μ) ≤ lam * ∫ w, ‖v w‖ ^ 2 ∂M)
    (G : Ω × Ω → ℝ)
    (he : G =ᵐ[μ.prod μ] fun x => (1 / 2) * PilotFields.pilotMean (M := M) bar η B x) :
    MemLp G 2 (μ.prod μ) ∧
      (∫ x, (G x - ∫ z, G z ∂μ.prod μ) ^ 2 ∂μ.prod μ) ≤
        (3 / 4) * lam * cB ^ 2 * (2 * (∫ w, ‖bar w‖ ^ 2 ∂M) +
          ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) := by
  have hHalf := (PilotFields.pilotMean_memLp_two bar hbarMeas hbar hmη hη hmB
    hcB hlam hbound hsym htest).const_mul (1 / 2 : ℝ)
  refine ⟨hHalf.ae_eq he.symm, ?_⟩
  have hMean := integral_congr_ae he
  have hSq : (fun x => (G x - ∫ z, G z ∂μ.prod μ) ^ 2) =ᵐ[μ.prod μ]
      (fun x => ((1 / 2) * PilotFields.pilotMean (M := M) bar η B x -
        ∫ z, (1 / 2) * PilotFields.pilotMean (M := M) bar η B z ∂μ.prod μ) ^ 2) := by
    filter_upwards [he] with x hx
    rw [hx, hMean]
  rw [integral_congr_ae hSq]
  exact half_pilotMean_centered_sq_le bar hbarMeas hbar hmη hη hcenter hmB hcB hlam hbound hsym htest

end HalfMean

theorem pairNoiseOperator_symmetric (a b : PairVector) :
    ⟪a, pairNoiseOperator b⟫ = ⟪pairNoiseOperator a, b⟫ := by
  rw [← real_inner_comm (pairNoiseOperator a) b, pairNoiseOperator_inner, pairNoiseOperator_inner]
  ring

theorem pairNoiseOperator_measurable_apply {W : Type*} [MeasurableSpace W] :
    Measurable (fun z : W × PairVector => pairNoiseOperator z.2) := by
  have h := pairNoiseOperator.continuous.measurable.comp
    (show Measurable (fun z : W × PairVector => z.2) from measurable_snd)
  exact h

section ActualMean
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
variable (k : ℕ) (hk : 0 < k) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (bar : Covariate d × Covariate d → PairVector)
variable (η : Ω → Covariate d × Covariate d → PairVector)
include C hθ

theorem pairPilotNoiseMean_mean_eq
    (hbarMeas : Measurable bar) (R : ℝ)
    (hbarBound : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, ‖bar w‖ ≤ R)
    (hmη : Measurable (fun z : Ω × (Covariate d × Covariate d) => η z.1 z.2))
    (hη : MemLp (fun z : Ω × (Covariate d × Covariate d) => η z.1 z.2) 2
      (μ.prod (regularPairDesignMeasure θ k hk)))
    (hcenter : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, (∫ x, η x w ∂μ) = 0)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (htest : ∀ v : (Covariate d × Covariate d) → PairVector,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
      (∫ x, PilotFields.test (M := regularPairDesignMeasure θ k hk) η v x ^ 2 ∂μ) ≤
        lam * ∫ w, ‖v w‖ ^ 2 ∂regularPairDesignMeasure θ k hk)
    (hi : ∀ᵐ x ∂μ.prod μ, Integrable (pairPilotNoiseKernel k hk bar η x)
      ((observationLaw θ).prod (observationLaw θ))) :
    (∫ x, pairPilotNoiseMean θ k hk bar η x ∂μ.prod μ) =
      (1 / 2) * ∫ w, (bar w 0) ^ 2 + (bar w 1) ^ 2 ∂regularPairDesignMeasure θ k hk := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  have hbar : MemLp bar 2 (regularPairDesignMeasure θ k hk) :=
    MemLp.of_bound hbarMeas.aestronglyMeasurable R hbarBound
  have he : pairPilotNoiseMean θ k hk bar η =ᵐ[μ.prod μ]
      (fun x => (1 / 2) * PilotFields.pilotMean (M := regularPairDesignMeasure θ k hk)
        bar η (fun _ => pairNoiseOperator) x) := by
    filter_upwards [hi] with x hx
    exact pairPilotNoiseMean_eq_half_pilotMean C θ hθ k hk bar η x hx
  rw [integral_congr_ae he, half_pilotMean_mean_eq bar hbarMeas hbar hmη hη hcenter
    pairNoiseOperator_measurable_apply (by norm_num : (0 : ℝ) ≤ 2) hlam
    (fun _ => pairNoiseOperator_norm_le) (fun _ => pairNoiseOperator_symmetric) htest]
  simp only [pairNoiseOperator_inner, pow_two]

theorem pairPilotNoiseMean_mean_lower
    (hbarMeas : Measurable bar) (R : ℝ)
    (hbarBound : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, ‖bar w‖ ≤ R)
    (hfirst : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, bar w 0 = 1)
    (hmη : Measurable (fun z : Ω × (Covariate d × Covariate d) => η z.1 z.2))
    (hη : MemLp (fun z : Ω × (Covariate d × Covariate d) => η z.1 z.2) 2
      (μ.prod (regularPairDesignMeasure θ k hk)))
    (hcenter : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, (∫ x, η x w ∂μ) = 0)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (htest : ∀ v : (Covariate d × Covariate d) → PairVector,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
      (∫ x, PilotFields.test (M := regularPairDesignMeasure θ k hk) η v x ^ 2 ∂μ) ≤
        lam * ∫ w, ‖v w‖ ^ 2 ∂regularPairDesignMeasure θ k hk)
    (hi : ∀ᵐ x ∂μ.prod μ, Integrable (pairPilotNoiseKernel k hk bar η x)
      ((observationLaw θ).prod (observationLaw θ))) :
    (1 / 2 : ℝ) ≤ ∫ x, pairPilotNoiseMean θ k hk bar η x ∂μ.prod μ := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  have hbar : MemLp bar 2 (regularPairDesignMeasure θ k hk) :=
    MemLp.of_bound hbarMeas.aestronglyMeasurable R hbarBound
  have hOp := PilotFields.operatorField_memLp pairNoiseOperator_measurable_apply
    (fun _ => pairNoiseOperator_norm_le) hbarMeas hbar
  have hInt := PilotFields.inner_integrable hbar hOp
  have hLow : (regularPairDesignMeasure θ k hk).real univ ≤
      ∫ w, ⟪bar w, pairNoiseOperator (bar w)⟫ ∂regularPairDesignMeasure θ k hk := by
    have h := integral_mono_ae (integrable_const (1 : ℝ)) hInt (by
      filter_upwards [hfirst] with w hw
      rw [pairNoiseOperator_inner, hw]
      nlinarith [sq_nonneg (bar w 1)])
    simpa only [integral_const, smul_eq_mul, mul_one] using h
  rw [pairPilotNoiseMean_mean_eq C θ hθ k hk μ bar η hbarMeas R hbarBound hmη hη hcenter lam hlam htest hi]
  have hEq : (∫ w, (bar w 0) ^ 2 + (bar w 1) ^ 2 ∂regularPairDesignMeasure θ k hk) =
      ∫ w, ⟪bar w, pairNoiseOperator (bar w)⟫ ∂regularPairDesignMeasure θ k hk := by
    simp only [pairNoiseOperator_inner, pow_two]
  rw [hEq]
  linarith [(regularPairDesignMeasure_mass_bounds C θ hθ k hk).1]

end ActualMean

/-- Primitive measurable and moment conditions of the original two pilots.
No conditional mean, bias, variance, or statistical risk conclusion occurs
among these fields. -/
structure PairPilotMeanConditions {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    (μ : Measure Ω) (bar : Covariate d × Covariate d → PairVector)
    (η : Ω → Covariate d × Covariate d → PairVector) (R lam : ℝ) : Prop where
  barMeasurable : Measurable bar
  barBound : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, ‖bar w‖ ≤ R
  noiseMeasurable : Measurable (fun z : Ω × (Covariate d × Covariate d) => η z.1 z.2)
  noiseMemLp : MemLp (fun z : Ω × (Covariate d × Covariate d) => η z.1 z.2) 2
    (μ.prod (regularPairDesignMeasure θ k hk))
  noiseCentered : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, (∫ x, η x w ∂μ) = 0
  lamNonnegative : 0 ≤ lam
  linearTest : ∀ v : (Covariate d × Covariate d) → PairVector,
    MemLp v 2 (regularPairDesignMeasure θ k hk) →
    (∫ x, PilotFields.test (M := regularPairDesignMeasure θ k hk) η v x ^ 2 ∂μ) ≤
      lam * ∫ w, ‖v w‖ ^ 2 ∂regularPairDesignMeasure θ k hk
  scoreConditionalIntegrable : ∀ᵐ x ∂μ.prod μ, Integrable (pairPilotScoreKernel θ k hk bar η x)
    ((observationLaw θ).prod (observationLaw θ))
  noiseConditionalIntegrable : ∀ᵐ x ∂μ.prod μ, Integrable (pairPilotNoiseKernel k hk bar η x)
    ((observationLaw θ).prod (observationLaw θ))

section ConcreteBounds
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
variable (k : ℕ) (hk : 0 < k) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (bar : Covariate d × Covariate d → PairVector)
variable (η : Ω → Covariate d × Covariate d → PairVector) (R lam : ℝ)
variable (hp : PairPilotMeanConditions θ k hk μ bar η R lam)
include C hθ hp

theorem pairPilotScoreMean_mean_eq :
    (∫ x, pairPilotScoreMean θ k hk bar η x ∂μ.prod μ) =
      (1 / 2) * ∫ w, ⟪bar w, boundedPairRegressionOperator C θ w (bar w)⟫
        ∂regularPairDesignMeasure θ k hk := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  have hbar : MemLp bar 2 (regularPairDesignMeasure θ k hk) :=
    MemLp.of_bound hp.barMeasurable.aestronglyMeasurable R hp.barBound
  have he : pairPilotScoreMean θ k hk bar η =ᵐ[μ.prod μ]
      (fun x => (1 / 2) * PilotFields.pilotMean (M := regularPairDesignMeasure θ k hk)
        bar η (boundedPairRegressionOperator C θ) x) := by
    filter_upwards [hp.scoreConditionalIntegrable] with x hx
    exact pairPilotScoreMean_eq_half_pilotMean C θ hθ k hk bar η x hx
  rw [integral_congr_ae he]
  exact half_pilotMean_mean_eq bar hp.barMeasurable hbar hp.noiseMeasurable hp.noiseMemLp hp.noiseCentered
    (boundedPairRegressionOperator_measurable_apply C θ hθ) (by positivity) hp.lamNonnegative
    (boundedPairRegressionOperator_norm_le C θ) (boundedPairRegressionOperator_symmetric C θ) hp.linearTest

/-- The actual conditional numerator-minus-variance-denominator mean has
bias bounded by the squared pointwise deterministic residual. -/
theorem pairPilotScoreMean_bias_le (b : ℝ)
    (hresidual : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤ b) :
    (∫ x, pairPilotScoreMean θ k hk bar η x ∂μ.prod μ) ≤ (C.densityUpper / 2) * b ^ 2 := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  have hbar : MemLp bar 2 (regularPairDesignMeasure θ k hk) :=
    MemLp.of_bound hp.barMeasurable.aestronglyMeasurable R hp.barBound
  have hOp := PilotFields.operatorField_memLp (boundedPairRegressionOperator_measurable_apply C θ hθ)
    (boundedPairRegressionOperator_norm_le C θ) hp.barMeasurable hbar
  have hInt := PilotFields.inner_integrable hbar hOp
  have hPoint : (fun w => ⟪bar w, boundedPairRegressionOperator C θ w (bar w)⟫) ≤ᵐ[regularPairDesignMeasure θ k hk]
      (fun _ => b ^ 2) := by
    filter_upwards [boundedPairRegressionOperator_eq_ae C θ hθ k hk, hresidual] with w hw hr
    rw [hw, InnerProductSpace.inner_right_rankOne_apply,
      real_inner_comm (bar w) (pairResponseVector (θ.regression w.1) (θ.regression w.2))]
    have hSq := pow_le_pow_left₀ (abs_nonneg _) hr 2
    rw [sq_abs] at hSq
    simpa only [pow_two] using hSq
  have hUpper := integral_mono_ae hInt (integrable_const (b ^ 2)) hPoint
  simp only [integral_const, smul_eq_mul] at hUpper
  rw [pairPilotScoreMean_mean_eq C θ hθ k hk μ bar η R lam hp]
  calc
    _ ≤ (1 / 2) * ((regularPairDesignMeasure θ k hk).real univ * b ^ 2) :=
      mul_le_mul_of_nonneg_left hUpper (by norm_num)
    _ ≤ (1 / 2) * (C.densityUpper * b ^ 2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (regularPairDesignMeasure_mass_bounds C θ hθ k hk).2 (sq_nonneg b))
      (by norm_num)
    _ = _ := by ring

theorem pairPilotNoiseMean_denominator_lower
    (hfirst : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, bar w 0 = 1) :
    (1 / 2 : ℝ) ≤ ∫ x, pairPilotNoiseMean θ k hk bar η x ∂μ.prod μ :=
  pairPilotNoiseMean_mean_lower C θ hθ k hk μ bar η hp.barMeasurable R hp.barBound hfirst
    hp.noiseMeasurable hp.noiseMemLp hp.noiseCentered lam hp.lamNonnegative hp.linearTest hp.noiseConditionalIntegrable

/-- Genuine L² integrability and variance of the actual numerator score mean.
The universal pilot tests provide the variance; no fourth pilot moment is used. -/
theorem pairPilotScoreMean_variance_le :
    MemLp (pairPilotScoreMean θ k hk bar η) 2 (μ.prod μ) ∧
      (∫ x, (pairPilotScoreMean θ k hk bar η x -
        ∫ z, pairPilotScoreMean θ k hk bar η z ∂μ.prod μ) ^ 2 ∂μ.prod μ) ≤
      (3 / 4) * lam * (2 * C.holderBound ^ 2 + 1) ^ 2 *
        (2 * (∫ w, ‖bar w‖ ^ 2 ∂regularPairDesignMeasure θ k hk) +
          ∫ z : Ω × (Covariate d × Covariate d), ‖η z.1 z.2‖ ^ 2
            ∂μ.prod (regularPairDesignMeasure θ k hk)) := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  have hbar : MemLp bar 2 (regularPairDesignMeasure θ k hk) :=
    MemLp.of_bound hp.barMeasurable.aestronglyMeasurable R hp.barBound
  have he : pairPilotScoreMean θ k hk bar η =ᵐ[μ.prod μ]
      (fun x => (1 / 2) * PilotFields.pilotMean (M := regularPairDesignMeasure θ k hk)
        bar η (boundedPairRegressionOperator C θ) x) := by
    filter_upwards [hp.scoreConditionalIntegrable] with x hx
    exact pairPilotScoreMean_eq_half_pilotMean C θ hθ k hk bar η x hx
  exact half_pilotMean_variance_transfer bar hp.barMeasurable hbar hp.noiseMeasurable hp.noiseMemLp hp.noiseCentered
    (boundedPairRegressionOperator_measurable_apply C θ hθ) (by positivity) hp.lamNonnegative
    (boundedPairRegressionOperator_norm_le C θ) (boundedPairRegressionOperator_symmetric C θ)
    hp.linearTest _ he

theorem pairPilotNoiseMean_variance_le :
    MemLp (pairPilotNoiseMean θ k hk bar η) 2 (μ.prod μ) ∧
      (∫ x, (pairPilotNoiseMean θ k hk bar η x -
        ∫ z, pairPilotNoiseMean θ k hk bar η z ∂μ.prod μ) ^ 2 ∂μ.prod μ) ≤
      3 * lam * (2 * (∫ w, ‖bar w‖ ^ 2 ∂regularPairDesignMeasure θ k hk) +
        ∫ z : Ω × (Covariate d × Covariate d), ‖η z.1 z.2‖ ^ 2
          ∂μ.prod (regularPairDesignMeasure θ k hk)) := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  have hbar : MemLp bar 2 (regularPairDesignMeasure θ k hk) :=
    MemLp.of_bound hp.barMeasurable.aestronglyMeasurable R hp.barBound
  have he : pairPilotNoiseMean θ k hk bar η =ᵐ[μ.prod μ]
      (fun x => (1 / 2) * PilotFields.pilotMean (M := regularPairDesignMeasure θ k hk)
        bar η (fun _ => pairNoiseOperator) x) := by
    filter_upwards [hp.noiseConditionalIntegrable] with x hx
    exact pairPilotNoiseMean_eq_half_pilotMean C θ hθ k hk bar η x hx
  obtain ⟨hL2, hVar⟩ := half_pilotMean_variance_transfer bar hp.barMeasurable hbar
    hp.noiseMeasurable hp.noiseMemLp hp.noiseCentered pairNoiseOperator_measurable_apply
    (by norm_num : (0 : ℝ) ≤ 2) hp.lamNonnegative (fun _ => pairNoiseOperator_norm_le)
    (fun _ => pairNoiseOperator_symmetric) hp.linearTest _ he
  refine ⟨hL2, ?_⟩
  convert hVar using 1 <;> ring

/-- The genuine conditional score mean is nonnegative because its
deterministic population operator is a positive rank-one form. -/
theorem pairPilotScoreMean_mean_nonneg :
    0 ≤ ∫ x, pairPilotScoreMean θ k hk bar η x ∂μ.prod μ := by
  rw [pairPilotScoreMean_mean_eq C θ hθ k hk μ bar η R lam hp]
  apply mul_nonneg (by norm_num)
  apply integral_nonneg
  intro w
  change 0 ≤ ⟪bar w, InnerProductSpace.rankOne ℝ
    (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2))
    (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2)) (bar w)⟫
  rw [InnerProductSpace.inner_right_rankOne_apply,
    real_inner_comm (bar w)
      (pairResponseVector (boundedRegression C θ w.1) (boundedRegression C θ w.2))]
  exact mul_self_nonneg _

/-- The squared deterministic residual bounds the absolute actual score
mean, with no bias assumption on the pilot law. -/
theorem pairPilotScoreMean_abs_bias_le (b : ℝ)
    (hresidual : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤ b) :
    |∫ x, pairPilotScoreMean θ k hk bar η x ∂μ.prod μ| ≤
      (C.densityUpper / 2) * b ^ 2 := by
  rw [abs_of_nonneg (pairPilotScoreMean_mean_nonneg C θ hθ k hk μ bar η R lam hp)]
  exact pairPilotScoreMean_bias_le C θ hθ k hk μ bar η R lam hp b hresidual

end ConcreteBounds
end NearlyMinimax
