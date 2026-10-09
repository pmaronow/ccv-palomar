module

public import NearlyMinimax.HighTimeMarginal


@[expose] public section

/-! A genuine Borel time kernel for the observed high experiment and
measurability of its posterior Fisher-energy path. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
variable {J : Type*} [Fintype J] [LinearOrder J]

def highHistoryIndexTimeKernel {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Kernel ℝ ((Fin n → Covariate d) × (Fin n → Fin 3)) :=
  (Kernel.const ℝ (highSampleReference d n)).withDensity
    (fun t z => ENNReal.ofReal
      (highMarginalRawLikelihood (historyMarkedPrior dependent Δ t π activation) n a (v-η^2*t) p F z /
        massPowerNormalizer (historyMarkedPrior dependent Δ t π activation)
          (fun ω => highRawDensityMass (p ω)) n))


instance highHistoryIndexTimeKernel_isSFinite {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    IsSFiniteKernel (highHistoryIndexTimeKernel dependent Δ π activation ham n a v η p F hp hF) := by
  unfold highHistoryIndexTimeKernel
  exact Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel _ (fun _ _ => ENNReal.ofReal_ne_top)

def highHistoryRealTimeKernel {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Kernel ℝ (Fin n → Observation d) :=
  (highHistoryIndexTimeKernel dependent Δ π activation ham n a v η p F hp hF).map (encodeDesignResponse a)

instance highHistoryRealTimeKernel_isSFinite {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    IsSFiniteKernel (highHistoryRealTimeKernel dependent Δ π activation ham n a v η p F hp hF) := by
  unfold highHistoryRealTimeKernel
  infer_instance

theorem highHistoryIndexTimeKernel_apply {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) (t : ℝ) :
    highHistoryIndexTimeKernel dependent Δ π activation ham n a v η p F hp hF t =
      (highSampleReference d n).withDensity (fun z => ENNReal.ofReal
        (highMarginalRawLikelihood (historyMarkedPrior dependent Δ t π activation)
          n a (v-η^2*t) p F z /
          massPowerNormalizer (historyMarkedPrior dependent Δ t π activation)
            (fun ω => highRawDensityMass (p ω)) n)) := by
  have hd : Measurable (Function.uncurry (fun t z => ENNReal.ofReal
      (highMarginalRawLikelihood (historyMarkedPrior dependent Δ t π activation)
        n a (v-η^2*t) p F z /
        massPowerNormalizer (historyMarkedPrior dependent Δ t π activation)
          (fun ω => highRawDensityMass (p ω)) n))) :=
    ((highMarginalRawLikelihood_time_measurable dependent Δ π activation ham n a v η p F hp hF).div
      ((highMassPowerNormalizer_time_measurable dependent Δ π activation ham n p hp).comp measurable_fst)).ennreal_ofReal
  exact Kernel.withDensity_apply _ hd t

theorem highHistoryRealTimeKernel_eq_data {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (t : ℝ) [IsProbabilityMeasure (historyMarkedPrior dependent Δ t π activation)]
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw) (ha : a ≠ 0)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v-η^2*t) y) :
    highHistoryRealTimeKernel dependent Δ π activation ham n a v η p F hp hF t =
      (highRealSampleKernel n a (v-η^2*t) p F hp hF) ∘ₘ
        massPowerTilt (historyMarkedPrior dependent Δ t π activation)
          (fun ω => highRawDensityMass (p ω)) n := by
  rw [highHistoryRealTimeKernel, Kernel.map_apply _ (encodeDesignResponse_measurable a),
    highHistoryIndexTimeKernel_apply, ← highMassTilt_index_marginal_density
      (historyMarkedPrior dependent Δ t π activation) n a (v-η^2*t) p F hp hF aRaw bRaw haRaw ha hraw hq,
    Measure.map_comp _ _ (encodeDesignResponse_measurable a)]
  rfl

theorem highHistoryScoreEnergyProxy_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (π : Measure E) [SFinite π] [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun t => ∫ z,
      (highMarginalRealScore dependent hsymm (historyMarkedPrior dependent Δ t π activation)
        π activation n a (v-η^2*t) η p F z)^2
      ∂highHistoryRealTimeKernel dependent Δ π activation ham n a v η p F hp hF t) :=
  (((highMarginalRealScore_time_measurable dependent hsymm Δ π activation ham n a v η p F hp hF).pow_const 2).stronglyMeasurable.integral_kernel_prod_right'
    (κ := highHistoryRealTimeKernel dependent Δ π activation ham n a v η p F hp hF)).measurable

/-- Joint Borel dependence and a genuine energy bound imply the square-root
energy is interval integrable. -/
theorem intervalIntegrable_sqrt_of_measurable_bound (f : ℝ → ℝ)
    (hf : Measurable f) (T M : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ t ∈ Icc 0 T, f t ≤ M) :
    IntervalIntegrable (fun t => Real.sqrt (f t)) volume 0 T := by
  apply (intervalIntegrable_const (c := Real.sqrt M)).mono_fun'
    (Real.continuous_sqrt.measurable.comp hf).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [uIoc_of_le hT] at ht
  dsimp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (hbound t ⟨ht.1.le, ht.2⟩)

/-- The actual observed posterior Fisher-energy path is integrable on the
source time interval as a consequence of its uniform complete-likelihood
energy budget. No path-integrability premise is supplied. -/
theorem highHistoryScore_sqrt_energy_intervalIntegrable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (π : Measure E) [IsProbabilityMeasure π]
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a v η aRaw bRaw T M : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw) (hT : 0 ≤ T)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hprob : ∀ t ∈ Icc 0 T, IsProbabilityMeasure (historyMarkedPrior dependent Δ t π activation))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v-η^2*t) y)
    (hE : ∀ t ∈ Icc 0 T, Integrable
      (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
        (highHistoryLikelihoodDerivative dependent hsymm π activation n a (v-η^2*t) η p F z.1 z.2)^2 /
          highRawSampleLikelihood n a (v-η^2*t) (p z.1) (F z.1) z.2)
      ((historyMarkedPrior dependent Δ t π activation).prod (highSampleReference d n)))
    (hbudget : ∀ t ∈ Icc 0 T,
      (massPowerNormalizer (historyMarkedPrior dependent Δ t π activation)
        (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
          (highHistoryLikelihoodDerivative dependent hsymm π activation n a (v-η^2*t) η p F z.1 z.2)^2 /
            highRawSampleLikelihood n a (v-η^2*t) (p z.1) (F z.1) z.2
          ∂(historyMarkedPrior dependent Δ t π activation).prod (highSampleReference d n) ≤ M) :
    IntervalIntegrable (fun t => Real.sqrt (∫ z,
      (highMarginalRealScore dependent hsymm (historyMarkedPrior dependent Δ t π activation)
        π activation n a (v-η^2*t) η p F z)^2
      ∂(highRealSampleKernel n a (v-η^2*t) p F hp hF) ∘ₘ
        massPowerTilt (historyMarkedPrior dependent Δ t π activation)
          (fun ω => highRawDensityMass (p ω)) n)) volume 0 T := by
  have hb (t : ℝ) (ht : t ∈ Icc 0 T) :
      (∫ z, (highMarginalRealScore dependent hsymm (historyMarkedPrior dependent Δ t π activation)
        π activation n a (v-η^2*t) η p F z)^2
        ∂highHistoryRealTimeKernel dependent Δ π activation ham n a v η p F hp hF t) ≤ M := by
    letI := hprob t ht
    rw [highHistoryRealTimeKernel_eq_data dependent Δ π activation ham n a v η p F hp hF
      t aRaw bRaw haRaw ha.ne' hraw (fun ω x y => (hq t ht ω x y).le)]
    exact (highMarginalRealScore_memLp_energy dependent hsymm
      (historyMarkedPrior dependent Δ t π activation) π activation ham Ba hBa habound
      n a (v-η^2*t) η aRaw bRaw ha haRaw p F hp hF hraw (hq t ht) (hE t ht)).2.trans
      (hbudget t ht)
  have hi := intervalIntegrable_sqrt_of_measurable_bound _
    (highHistoryScoreEnergyProxy_measurable dependent hsymm Δ π activation ham n a v η p F hp hF)
    T M hT hb
  apply hi.congr
  intro t ht
  rw [uIoc_of_le hT] at ht
  letI := hprob t ⟨ht.1.le,ht.2⟩
  dsimp only
  rw [highHistoryRealTimeKernel_eq_data dependent Δ π activation ham n a v η p F hp hF
    t aRaw bRaw haRaw ha.ne' hraw (fun ω x y => (hq t ⟨ht.1.le,ht.2⟩ ω x y).le)]

end NearlyMinimax
