module

public import NearlyMinimax.PaperPairRisk
public import NearlyMinimax.SampleThirds


@[expose] public section

/-! A Borel pair estimator constructed directly from observable coefficient
fields, with its actual original-sample risk and minimax comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000

def coefficientPairNumeratorKernel {Ω : Type*} {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Ω → Covariate d × Covariate d → PairVector) (p : Ω × Ω)
    (z : Observation d × Observation d) : ℝ :=
  sameLabelKernel (regularObservationLabel k hk) z *
    ⟪c p.1 (pairCovariates z), InnerProductSpace.rankOne ℝ
      (pairResponseVector z.1.2 z.2.2) (pairResponseVector z.1.2 z.2.2)
        (c p.2 (pairCovariates z))⟫

theorem coefficientPairNumeratorKernel_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (k : ℕ) (hk : 0 < k) {c : Ω → Covariate d × Covariate d → PairVector}
    (hmc : Measurable (fun z : Ω × (Covariate d × Covariate d) => c z.1 z.2)) :
    Measurable (fun z : (Ω × Ω) × (Observation d × Observation d) =>
      coefficientPairNumeratorKernel k hk c z.1 z.2) := by
  have hm := PilotFields.maskedPilotKernel_measurable
    (c := fun x z => c x (pairCovariates z))
    (A := fun z : Observation d × Observation d => pairScoreOperator 0 z.1.2 z.2.2)
    (q := sameLabelKernel (regularObservationLabel (d := d) k hk))
    (pilotOnObservations_measurable hmc)
    (observationPairScoreOperator_measurable_apply (d := d) 0)
    (sameLabelKernel_measurable (regularObservationLabel (d := d) k hk)
      (regularObservationLabel_measurable (d := d) k hk))
  change Measurable (fun z : (Ω × Ω) × (Observation d × Observation d) =>
    sameLabelKernel (regularObservationLabel k hk) z.2 *
      ⟪c z.1.1 (pairCovariates z.2), pairScoreOperator 0 z.2.1.2 z.2.2.2
        (c z.1.2 (pairCovariates z.2))⟫) at hm
  simpa only [coefficientPairNumeratorKernel, pairScoreOperator,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, zero_smul, sub_zero] using hm

def coefficientPairStatistic {d : ℕ} (C : ModelConstants d) (m k : ℕ) (hk : 0 < k)
    (c : (Fin m → Observation d) → Covariate d × Covariate d → PairVector)
    (z : (((Fin m → Observation d) × (Fin m → Observation d)) × (Fin m → Observation d))) : ℝ :=
  stabilizedRatio C.varianceLower C.varianceUpper (1 / 4)
    (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (coefficientPairNumeratorKernel k hk c)
      (fun i x => x i))
    (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (rawModelPairNoise k hk c)
      (fun i x => x i)) z

theorem coefficientPairStatistic_measurable {d : ℕ} (C : ModelConstants d) (m k : ℕ)
    (hk : 0 < k) {c : (Fin m → Observation d) → Covariate d × Covariate d → PairVector}
    (hmc : Measurable (fun z : (Fin m → Observation d) × (Covariate d × Covariate d) => c z.1 z.2)) :
    Measurable (coefficientPairStatistic C m k hk c) := by
  have hN : Measurable (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d)
      (coefficientPairNumeratorKernel k hk c) (fun (i : Fin m) (x : Fin m → Observation d) => x i)) :=
    PairUStatistic.fieldPairAverage_measurable m ((k : ℝ) ^ d)
      (G := coefficientPairNumeratorKernel k hk c) (coefficientPairNumeratorKernel_measurable k hk hmc)
      (fun (i : Fin m) (x : Fin m → Observation d) => x i) (fun i => measurable_pi_apply i)
  have hD : Measurable (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d)
      (rawModelPairNoise k hk c) (fun (i : Fin m) (x : Fin m → Observation d) => x i)) :=
    PairUStatistic.fieldPairAverage_measurable m ((k : ℝ) ^ d)
      (G := rawModelPairNoise k hk c) (rawModelPairNoise_measurable k hk hmc)
      (fun (i : Fin m) (x : Fin m → Observation d) => x i) (fun i => measurable_pi_apply i)
  exact stabilizedRatio_measurable C.varianceLower C.varianceUpper (1 / 4) hN hD

def coefficientPairEstimator {d n : ℕ} (C : ModelConstants d) (k : ℕ) (hk : 0 < k)
    (c : (Fin (threeBlockSize n) → Observation d) → Covariate d × Covariate d → PairVector)
    (hmc : Measurable (fun z : (Fin (threeBlockSize n) → Observation d) ×
      (Covariate d × Covariate d) => c z.1 z.2)) : Estimator d n :=
  threeBlockEstimator (coefficientPairStatistic C (threeBlockSize n) k hk c)
    (coefficientPairStatistic_measurable C _ k hk hmc)

/-- Independent pilots and evaluation data arise from the original iid sample;
the coefficient field is observable and carries no unknown parameter. -/
theorem coefficientPairEstimator_rms_bound {d n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (hn : 6 ≤ n)
    (k : ℕ) (hk : 0 < k)
    (c : (Fin (threeBlockSize n) → Observation d) → Covariate d × Covariate d → PairVector)
    (hmc : Measurable (fun z : (Fin (threeBlockSize n) → Observation d) ×
      (Covariate d × Covariate d) => c z.1 z.2))
    (bar : Covariate d × Covariate d → PairVector)
    (η : (Fin (threeBlockSize n) → Observation d) → Covariate d × Covariate d → PairVector)
    (Cp W b : ℝ) (heq : c = pairPilotCoefficient bar η)
    (hp : PairPilotAssumptions θ k hk (sampleLaw θ (threeBlockSize n)) bar η
      Cp W (Cp ^ 2 * W / (n : ℝ)))
    (hfirst : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, bar w 0 = 1)
    (hresidual : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤ b) :
    meanSquaredRisk (coefficientPairEstimator C k hk c hmc) θ ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) *
        (b ^ 2 + pairFluctuationScale (d := d) n k * (1 + W))) := by
  let := observationLaw_isProbability C θ hθ
  let := sampleLaw_isProbability C θ hθ (threeBlockSize n)
  have hi := iIndepFun_pi (μ := fun _ : Fin (threeBlockSize n) => observationLaw θ)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  have hm := fun i => measurePreserving_eval (fun _ : Fin (threeBlockSize n) => observationLaw θ) i
  have h := paper_common_pair_rms (sampleLaw θ (threeBlockSize n)) (sampleLaw θ (threeBlockSize n))
    C θ hθ k hk bar η Cp W (by omega : 0 < n) (threeBlockSize_two_le hn)
    (by norm_num : (0 : ℝ) < 1 / 4) (threeBlockSize_fraction hn) hp hfirst
    (fun i x => x i) hi hm b hresidual
  unfold coefficientPairEstimator
  rw [threeBlockEstimator_risk_eq C θ hθ]
  have hnum : coefficientPairNumeratorKernel k hk (pairPilotCoefficient bar η) =
      pairPilotNumeratorKernel k hk bar η := rfl
  have hden : rawModelPairNoise k hk (pairPilotCoefficient bar η) =
      pairPilotNoiseKernel k hk bar η := rfl
  simp_rw [coefficientPairStatistic, heq, hnum, hden]
  exact h

theorem minimaxRMS_le_of_estimator_rms {d n : ℕ} (C : ModelConstants d)
    (T : Estimator d n) {B : ℝ≥0∞}
    (hT : ∀ θ : RegressionParameter d, Admissible C θ → meanSquaredRisk T θ ^ (1 / 2 : ℝ) ≤ B) :
    minimaxRMS C n ≤ B := by
  have h := ENNReal.rpow_le_rpow (minimaxRisk_le_worstCaseRisk C T)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply h.trans
  let φ := ENNReal.orderIsoRpow (1 / 2 : ℝ) (by norm_num)
  change φ (⨆ θ : {θ : RegressionParameter d // Admissible C θ}, meanSquaredRisk T θ.val) ≤ B
  rw [φ.map_iSup]
  exact iSup_le (fun θ => hT θ.val θ.property)

end NearlyMinimax
