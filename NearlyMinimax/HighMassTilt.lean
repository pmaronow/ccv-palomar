module

public import NearlyMinimax.HighObservationReal


@[expose] public section

/-! Genuine positive mass-power prior tilts and normalization cancellation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

def massPowerNormalizer (μ : Measure Ω) (m : Ω → ℝ) (n : ℕ) : ℝ :=
  ∫ ω, m ω ^ n ∂μ

def massPowerTilt (μ : Measure Ω) (m : Ω → ℝ) (n : ℕ) : Measure Ω :=
  μ.withDensity (fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer μ m n))

theorem massPower_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ ω, a ≤ m ω ∧ m ω ≤ b) : Integrable (fun ω => m ω ^ n) μ := by
  apply (integrable_const (b ^ n)).mono' (hm.pow_const n).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (ha.le.trans (hbound ω).1) n)]
  exact pow_le_pow_left₀ (ha.le.trans (hbound ω).1) (hbound ω).2 n

theorem massPowerNormalizer_mem_Icc (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ ω, a ≤ m ω ∧ m ω ≤ b) :
    massPowerNormalizer μ m n ∈ Icc (a ^ n) (b ^ n) := by
  have hi := massPower_integrable μ m hm n a b ha hbound
  constructor
  · simpa [massPowerNormalizer] using integral_mono_ae (integrable_const (a ^ n)) hi
      (Filter.Eventually.of_forall (fun ω => pow_le_pow_left₀ ha.le (hbound ω).1 n))
  · simpa [massPowerNormalizer] using integral_mono_ae hi (integrable_const (b ^ n))
      (Filter.Eventually.of_forall (fun ω =>
        pow_le_pow_left₀ (ha.le.trans (hbound ω).1) (hbound ω).2 n))

theorem massPowerNormalizer_pos (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ ω, a ≤ m ω ∧ m ω ≤ b) : 0 < massPowerNormalizer μ m n :=
  (pow_pos ha n).trans_le (massPowerNormalizer_mem_Icc μ m hm n a b ha hbound).1

theorem massPowerTilt_isProbability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ ω, a ≤ m ω ∧ m ω ≤ b) : IsProbabilityMeasure (massPowerTilt μ m n) := by
  have hi := massPower_integrable μ m hm n a b ha hbound
  have hG := massPowerNormalizer_pos μ m hm n a b ha hbound
  constructor
  rw [massPowerTilt, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
    (Filter.Eventually.of_forall (fun ω =>
      div_nonneg (pow_nonneg (ha.le.trans (hbound ω).1) n) hG.le)), integral_div]
  change ENNReal.ofReal (massPowerNormalizer μ m n / massPowerNormalizer μ m n) = 1
  rw [div_self hG.ne', ENNReal.ofReal_one]

/-- Equality of actual mass laws makes the power normalizer time independent. -/
theorem massPowerNormalizer_eq_of_massLaw (μ ν : Measure Ω) (m : Ω → ℝ)
    (hm : Measurable m) (n : ℕ) (hlaw : μ.map m = ν.map m) :
    massPowerNormalizer μ m n = massPowerNormalizer ν m n := by
  have hμ := integral_map_of_stronglyMeasurable (μ := μ) hm
    ((measurable_id.pow_const n : Measurable (fun x : ℝ => x ^ n)).stronglyMeasurable)
  have hν := integral_map_of_stronglyMeasurable (μ := ν) hm
    ((measurable_id.pow_const n : Measurable (fun x : ℝ => x ^ n)).stronglyMeasurable)
  rw [hlaw] at hμ
  exact hμ.symm.trans hν

/-- Pushing a pullback density forward gives the density of the pushed-forward law. -/
theorem map_withDensity_pullback {Α : Type*} [MeasurableSpace Α]
    (μ : Measure Ω) (m : Ω → Α) (hm : Measurable m)
    (f : Α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (fun ω => f (m ω))).map m = (μ.map m).withDensity f := by
  apply Measure.ext_of_lintegral
  intro G hG
  have hfm : Measurable (fun ω => f (m ω)) := hf.comp hm
  have hGm : Measurable (fun ω => G (m ω)) := hG.comp hm
  rw [lintegral_map hG hm,
    lintegral_withDensity_eq_lintegral_mul _ hfm hGm,
    lintegral_withDensity_eq_lintegral_mul _ hf hG,
    lintegral_map (hf.mul hG) hm]
  rfl

/-- The tilted mass law, hence its exceptional mass probabilities, depends
only on the original mass law. -/
theorem massPowerTilt_massLaw_eq (μ ν : Measure Ω) (m : Ω → ℝ)
    (hm : Measurable m) (n : ℕ) (hlaw : μ.map m = ν.map m) :
    (massPowerTilt μ m n).map m = (massPowerTilt ν m n).map m := by
  have hG := massPowerNormalizer_eq_of_massLaw μ ν m hm n hlaw
  unfold massPowerTilt
  rw [hG]
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ n / massPowerNormalizer ν m n)) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.pow_const n).div_const _)
  rw [map_withDensity_pullback μ m hm _ hf, map_withDensity_pullback ν m hm _ hf, hlaw]

/-- The unnormalized product likelihood appearing in the weak generator. -/
def highRawSampleLikelihood {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  ∏ i, p (z.1 i) * ternaryMass a (F (z.1 i)) V (z.2 i)

theorem highRawSampleLikelihood_joint_measurable {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highRawSampleLikelihood n a V (p z.1) (F z.1) z.2) := by
  have hx (i : Fin n) : Measurable
      (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => (z.1, z.2.1 i)) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hy (i : Fin n) : Measurable
      (fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => z.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  exact Finset.measurable_prod _ (fun i _ => (hp.comp (hx i)).mul
    ((ternaryMass_joint_measurable a V (Function.uncurry F) hF).comp ((hx i).prodMk (hy i))))

theorem highSampleLikelihood_mass_cancellation {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Covariate d → ℝ) (hm : highRawDensityMass p ≠ 0)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    highRawDensityMass p ^ n * highSampleLikelihood n a V p F z =
      highRawSampleLikelihood n a V p F z := by
  simp only [highSampleLikelihood, highRawSampleLikelihood, Finset.prod_mul_distrib]
  field_simp

instance highSampleIndexKernel_isSFinite {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) : IsSFiniteKernel (highSampleIndexKernel n a V p F hp hF) := by
  change IsSFiniteKernel ((Kernel.const Ω (highSampleReference d n)).withDensity
    (fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z)))
  exact Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel _ (fun _ _ => ENNReal.ofReal_ne_top)

/-- The actual tilted-prior/sample measure has the raw product likelihood
 divided only by the prior normalizer. -/
theorem massPowerTilt_highSample_compProd {d : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) :
    (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n).compProd
      (highSampleIndexKernel n a V p F hp hF) =
      (ν.prod (highSampleReference d n)).withDensity (fun z =>
        ENNReal.ofReal (highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 /
          massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)) := by
  let m : Ω → ℝ := fun ω => highRawDensityMass (p ω)
  have hm : Measurable m := highRawDensityMass_joint_measurable p hp
  have hbound (ω : Ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Filter.Eventually.of_forall (hraw ω))
  have hG := massPowerNormalizer_pos ν m hm n aRaw bRaw haRaw hbound
  have hd : Measurable (fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer ν m n)) :=
    ENNReal.measurable_ofReal.comp ((hm.pow_const n).div_const _)
  have hL : Measurable (Function.uncurry (fun ω z =>
      ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))) :=
    ENNReal.measurable_ofReal.comp (highSampleLikelihood_joint_measurable n a V p F hp hF)
  let _ := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    (f := fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))
    (Kernel.const Ω (highSampleReference d n)) (fun _ _ => ENNReal.ofReal_ne_top)
  change (ν.withDensity (fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer ν m n))).compProd
    ((Kernel.const Ω (highSampleReference d n)).withDensity
      (fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))) = _
  rw [Measure.withDensity_compProd_withDensity
    (f := fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer ν m n))
    (g := fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z)) hd hL,
    Measure.compProd_const]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (haRaw.le.trans (hbound z.1).1) n) hG.le)]
  congr 1
  calc
    (m z.1 ^ n / massPowerNormalizer ν m n) * highSampleLikelihood n a V (p z.1) (F z.1) z.2 =
        (m z.1 ^ n * highSampleLikelihood n a V (p z.1) (F z.1) z.2) / massPowerNormalizer ν m n := by ring
    _ = _ := by rw [highSampleLikelihood_mass_cancellation n a V (p z.1) (F z.1)
      (haRaw.trans_le (hbound z.1).1).ne']

end NearlyMinimax
