module

public import NearlyMinimax.HighMassTilt
public import NearlyMinimax.HighSelectedScoreEnergy


@[expose] public section

/-! Exact raw-likelihood Fisher transfer. Integrability under the genuine
normalized experiment yields integrability of D²/L under the fixed raw
reference, and a uniform conditional budget survives mass-power tilting. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem normalized_likelihood_score_square_transfer {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (c : ℝ) (hc : 0 < c) (L D : Z → ℝ)
    (hL : Measurable L) (hpos : ∀ z, 0 < L z) :
    (Integrable (fun z => (D z / L z) ^ 2)
      (μ.withDensity (fun z => ENNReal.ofReal (L z / c))) ↔
        Integrable (fun z => D z ^ 2 / L z) μ) ∧
    (∫ z, (D z / L z) ^ 2 ∂μ.withDensity (fun z => ENNReal.ofReal (L z / c))) =
      c⁻¹ * ∫ z, D z ^ 2 / L z ∂μ := by
  have hf : Measurable (fun z => ENNReal.ofReal (L z / c)) :=
    ENNReal.measurable_ofReal.comp (hL.div_const c)
  have he (z : Z) : (ENNReal.ofReal (L z / c)).toReal * (D z / L z) ^ 2 =
      c⁻¹ * (D z ^ 2 / L z) := by
    rw [ENNReal.toReal_ofReal (div_nonneg (hpos z).le hc.le)]
    field_simp [(hpos z).ne', hc.ne']
  constructor
  · rw [integrable_withDensity_iff_integrable_smul' hf
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [smul_eq_mul, he]
    exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (inv_ne_zero hc.ne')) _
  · have hi := integral_withDensity_eq_integral_toReal_smul (μ := μ) hf
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (fun z => (D z / L z) ^ 2)
    change (∫ z, (D z / L z) ^ 2 ∂μ.withDensity (fun z => ENNReal.ofReal (L z / c))) =
      ∫ z, (ENNReal.ofReal (L z / c)).toReal * (D z / L z) ^ 2 ∂μ at hi
    rw [hi]
    simp_rw [he]
    exact integral_const_mul _ _

theorem raw_joint_fisher_integrable_bound {Ω Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z]
    (ν : Measure Ω) [IsFiniteMeasure ν] (μ : Measure Z) [SFinite μ]
    (c : Ω → ℝ) (hc : ∀ ω, 0 < c ω) (hci : Integrable c ν)
    (L D : Ω → Z → ℝ) (hL : Measurable (Function.uncurry L))
    (hD : Measurable (Function.uncurry D)) (hpos : ∀ ω z, 0 < L ω z)
    (B : ℝ) (hB : 0 ≤ B)
    (hscore : ∀ ω, Integrable (fun z => (D ω z / L ω z) ^ 2)
      (μ.withDensity (fun z => ENNReal.ofReal (L ω z / c ω))))
    (hbound : ∀ ω, (∫ z, (D ω z / L ω z) ^ 2
      ∂μ.withDensity (fun z => ENNReal.ofReal (L ω z / c ω))) ≤ B) :
    Integrable (fun z : Ω × Z => D z.1 z.2 ^ 2 / L z.1 z.2) (ν.prod μ) ∧
    (∫ z : Ω × Z, D z.1 z.2 ^ 2 / L z.1 z.2 ∂ν.prod μ) ≤ (∫ ω, c ω ∂ν) * B := by
  let W : Ω × Z → ℝ := fun z => D z.1 z.2 ^ 2 / L z.1 z.2
  have hW : Measurable W := (hD.pow_const 2).div hL
  have hWi (ω : Ω) : Integrable (fun z => W (ω, z)) μ :=
    (normalized_likelihood_score_square_transfer μ (c ω) (hc ω) (L ω) (D ω)
      hL.of_uncurry_left (hpos ω)).1.mp (hscore ω)
  have hWn (ω : Ω) (z : Z) : 0 ≤ W (ω, z) := div_nonneg (sq_nonneg _) (hpos ω z).le
  have he (ω : Ω) : (∫ z, W (ω, z) ∂μ) = c ω *
      (∫ z, (D ω z / L ω z) ^ 2 ∂μ.withDensity (fun z => ENNReal.ofReal (L ω z / c ω))) := by
    have hs := (normalized_likelihood_score_square_transfer μ (c ω) (hc ω) (L ω) (D ω)
      hL.of_uncurry_left (hpos ω)).2
    rw [hs]
    rw [← mul_assoc, mul_inv_cancel₀ (hc ω).ne', one_mul]
  have hnorm (ω : Ω) : (∫ z, ‖W (ω, z)‖ ∂μ) ≤ c ω * B := by
    have heNorm : (fun z => ‖W (ω, z)‖) = (fun z => W (ω, z)) := by
      funext z
      rw [Real.norm_eq_abs, abs_of_nonneg (hWn ω z)]
    rw [heNorm, he]
    exact mul_le_mul_of_nonneg_left (hbound ω) (hc ω).le
  have hnormMeas : AEStronglyMeasurable (fun ω => ∫ z, ‖W (ω, z)‖ ∂μ) ν :=
    hW.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
  have hnormI : Integrable (fun ω => ∫ z, ‖W (ω, z)‖ ∂μ) ν := by
    apply (hci.mul_const B).mono' hnormMeas
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hnorm ω
  have hWI : Integrable W (ν.prod μ) :=
    (integrable_prod_iff hW.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hWi, hnormI⟩
  refine ⟨hWI, ?_⟩
  rw [integral_prod _ hWI]
  calc
    _ ≤ ∫ ω, c ω * B ∂ν := by
      apply integral_mono_ae hWI.integral_prod_left (hci.mul_const B)
      apply Filter.Eventually.of_forall
      intro ω
      change (∫ z, W (ω, z) ∂μ) ≤ c ω * B
      rw [he]
      exact mul_le_mul_of_nonneg_left (hbound ω) (hc ω).le
    _ = _ := integral_mul_const _ _

theorem high_sample_kernel_score_square_transfer {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (ω : Ω) (D : ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ) :
    (Integrable (fun z => (D z / highRawSampleLikelihood n a V (p ω) (F ω) z) ^ 2)
      (highSampleIndexKernel n a V p F hp hF ω) ↔
        Integrable (fun z => D z ^ 2 / highRawSampleLikelihood n a V (p ω) (F ω) z)
          (highSampleReference d n)) ∧
    (∫ z, (D z / highRawSampleLikelihood n a V (p ω) (F ω) z) ^ 2
      ∂highSampleIndexKernel n a V p F hp hF ω) =
      (highRawDensityMass (p ω) ^ n)⁻¹ *
        ∫ z, D z ^ 2 / highRawSampleLikelihood n a V (p ω) (F ω) z ∂highSampleReference d n := by
  have hm : 0 < highRawDensityMass (p ω) := haRaw.trans_le
    (highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Filter.Eventually.of_forall (hraw ω))).1
  have hL : Measurable (highRawSampleLikelihood n a V (p ω) (F ω)) :=
    (highRawSampleLikelihood_joint_measurable n a V p F hp hF).comp
      (measurable_const.prodMk measurable_id)
  have hpos (z) : 0 < highRawSampleLikelihood n a V (p ω) (F ω) z :=
    Finset.prod_pos (fun i _ => mul_pos (haRaw.trans_le (hraw ω (z.1 i)).1) (hq ω _ _))
  have he (z) : highSampleLikelihood n a V (p ω) (F ω) z =
      highRawSampleLikelihood n a V (p ω) (F ω) z / highRawDensityMass (p ω) ^ n := by
    apply (eq_div_iff (pow_ne_zero n hm.ne')).mpr
    simpa only [mul_comm] using highSampleLikelihood_mass_cancellation n a V (p ω) (F ω) hm.ne' z
  rw [highSampleIndexKernel_apply]
  simp_rw [he]
  exact normalized_likelihood_score_square_transfer (highSampleReference d n)
    (highRawDensityMass (p ω) ^ n) (pow_pos hm n) _ D hL hpos

theorem high_raw_joint_fisher_integrable_bound {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (D : Ω → ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ)
    (hD : Measurable (Function.uncurry D)) (B : ℝ) (hB : 0 ≤ B)
    (hscore : ∀ ω, Integrable (fun z => (D ω z / highRawSampleLikelihood n a V (p ω) (F ω) z) ^ 2)
      (highSampleIndexKernel n a V p F hp hF ω))
    (hbound : ∀ ω, (∫ z, (D ω z / highRawSampleLikelihood n a V (p ω) (F ω) z) ^ 2
      ∂highSampleIndexKernel n a V p F hp hF ω) ≤ B) :
    Integrable (fun z => D z.1 z.2 ^ 2 / highRawSampleLikelihood n a V (p z.1) (F z.1) z.2)
      (ν.prod (highSampleReference d n)) ∧
    (∫ z, D z.1 z.2 ^ 2 / highRawSampleLikelihood n a V (p z.1) (F z.1) z.2
      ∂ν.prod (highSampleReference d n)) ≤
      massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n * B := by
  let c : Ω → ℝ := fun ω => highRawDensityMass (p ω) ^ n
  have hmBound (ω : Ω) : aRaw ≤ highRawDensityMass (p ω) ∧ highRawDensityMass (p ω) ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Filter.Eventually.of_forall (hraw ω))
  have hm (ω : Ω) : 0 < highRawDensityMass (p ω) := haRaw.trans_le (hmBound ω).1
  have hc : ∀ ω, 0 < c ω := fun ω => pow_pos (hm ω) n
  have hcm : Measurable c := (highRawDensityMass_joint_measurable p hp).pow_const n
  have hci : Integrable c ν := by
    apply (integrable_const (bRaw ^ n)).mono' hcm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hc ω).le]
    exact pow_le_pow_left₀ (hm ω).le (hmBound ω).2 n
  have he (ω : Ω) : highSampleIndexKernel n a V p F hp hF ω =
      (highSampleReference d n).withDensity (fun z =>
        ENNReal.ofReal (highRawSampleLikelihood n a V (p ω) (F ω) z / c ω)) := by
    rw [highSampleIndexKernel_apply]
    congr 1
    funext z
    congr 1
    apply (eq_div_iff (hc ω).ne').mpr
    simpa only [c, mul_comm] using
      highSampleLikelihood_mass_cancellation n a V (p ω) (F ω) (hm ω).ne' z
  exact raw_joint_fisher_integrable_bound ν (highSampleReference d n) c hc hci
    (fun ω => highRawSampleLikelihood n a V (p ω) (F ω)) D
    (highRawSampleLikelihood_joint_measurable n a V p F hp hF) hD
    (fun ω z => Finset.prod_pos (fun i _ => mul_pos
      (haRaw.trans_le (hraw ω (z.1 i)).1) (hq ω _ _))) B hB
    (fun ω => by rw [← he ω]; exact hscore ω)
    (fun ω => by rw [← he ω]; exact hbound ω)

end NearlyMinimax
