module

public import NearlyMinimax.HighLikelihoodDerivative


@[expose] public section

/-! Actual raw data observables and the mass-tilted original observation mean. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

def highRawObservable {d : ℕ} (n : ℕ) (a V : ℝ) (p F : Covariate d → ℝ)
    (H : (Fin n → Observation d) → ℝ) : ℝ :=
  ∫ z, H (encodeDesignResponse a z) * highRawSampleLikelihood n a V p F z
    ∂highSampleReference d n

def highRawObservableVarianceDerivative {d : ℕ} (n : ℕ) (a V : ℝ) (p F : Covariate d → ℝ)
    (H : (Fin n → Observation d) → ℝ) : ℝ :=
  ∫ z, H (encodeDesignResponse a z) * highRawSampleVarianceDerivative n a V p F z
    ∂highSampleReference d n

theorem highRawObservable_measurable {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (H : (Fin n → Observation d) → ℝ)
    (hH : Measurable H) : Measurable (fun ω => highRawObservable n a V (p ω) (F ω) H) := by
  have h : Measurable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      H (encodeDesignResponse a z.2) * highRawSampleLikelihood n a V (p z.1) (F z.1) z.2) :=
    ((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
      (highRawSampleLikelihood_joint_measurable n a V p F hp hF)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem highRawObservableVarianceDerivative_measurable {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (H : (Fin n → Observation d) → ℝ)
    (hH : Measurable H) :
    Measurable (fun ω => highRawObservableVarianceDerivative n a V (p ω) (F ω) H) := by
  have h : Measurable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      H (encodeDesignResponse a z.2) * highRawSampleVarianceDerivative n a V (p z.1) (F z.1) z.2) :=
    ((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
      (highRawSampleVarianceDerivative_joint_measurable n a V p F hp hF)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem highRawObservable_abs_le {d : ℕ} (n : ℕ) (a V P B : ℝ) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (p F : Covariate d → ℝ) (hp : ∀ x, |p x| ≤ P) (ha : a ≠ 0)
    (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (H : (Fin n → Observation d) → ℝ) (hHb : ∀ z, |H z| ≤ B) :
    |highRawObservable n a V p F H| ≤ B * P ^ n * (highSampleReference d n).real Set.univ := by
  rw [highRawObservable, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hHb _) (highRawSampleLikelihood_abs_le n a V P hP p F hp ha hq z)
      (abs_nonneg _) hB

theorem highRawObservableVarianceDerivative_abs_le {d : ℕ} (n : ℕ) (a V P B : ℝ)
    (ha : 0 < a) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (p F : Covariate d → ℝ) (hp : ∀ x, |p x| ≤ P)
    (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (H : (Fin n → Observation d) → ℝ) (hHb : ∀ z, |H z| ≤ B) :
    |highRawObservableVarianceDerivative n a V p F H| ≤
      B * (P ^ n * ((n : ℝ) / a ^ 2)) * (highSampleReference d n).real Set.univ := by
  rw [highRawObservableVarianceDerivative, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hHb _) (highRawSampleVarianceDerivative_abs_le n a V P ha hP p F hp hq z)
      (abs_nonneg _) hB

/-- The actual original real-data mean under the genuine mass tilt equals
G_n^-1 times the raw-likelihood observable mean. -/
theorem massPowerTilt_highReal_observable_mean {d : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B) :
    (∫ ω, ∫ z, H z ∂highRealSampleKernel n a V p F hp hF ω
      ∂massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ ω, highRawObservable n a V (p ω) (F ω) H ∂ν := by
  let m : Ω → ℝ := fun ω => highRawDensityMass (p ω)
  have hm : Measurable m := highRawDensityMass_joint_measurable p hp
  have hbound (ω : Ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Eventually.of_forall (hraw ω))
  let _ := massPowerTilt_isProbability ν m hm n aRaw bRaw haRaw hbound
  let _ := highSampleIndexKernel_markov n a V p F hp hF aRaw bRaw haRaw hraw ha hq
  have hM : Measurable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      H (encodeDesignResponse a z.2)) := (hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd
  have hInt : Integrable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      H (encodeDesignResponse a z.2))
      ((massPowerTilt ν m n).compProd (highSampleIndexKernel n a V p F hp hF)) := by
    apply Integrable.of_bound hM.aestronglyMeasurable B
    exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hHb _
  have hpabs (ω : Ω) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  have hIntRaw : Integrable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 * H (encodeDesignResponse a z.2))
      (ν.prod (highSampleReference d n)) := by
    apply Integrable.of_bound ((highRawSampleLikelihood_joint_measurable n a V p F hp hF).mul hM).aestronglyMeasurable
      (|bRaw| ^ n * B)
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul (highRawSampleLikelihood_abs_le n a V |bRaw| (abs_nonneg _) (p z.1) (F z.1)
        (hpabs z.1) ha (hq z.1) z.2) (hHb _) (abs_nonneg _) (pow_nonneg (abs_nonneg _) n)
  have he := massPowerTilt_highSample_integral ν n a V p F hp hF aRaw bRaw haRaw hraw hq
    (fun z => H (encodeDesignResponse a z.2))
  rw [Measure.integral_compProd hInt, MeasureTheory.integral_prod _ hIntRaw] at he
  convert he using 1
  · apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      dsimp only
      rw [highRealSampleKernel_apply,
        integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) hH.stronglyMeasurable]
  · congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      dsimp only [highRawObservable]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => mul_comm _ _

end NearlyMinimax
