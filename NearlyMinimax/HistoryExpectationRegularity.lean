module

public import NearlyMinimax.HistoryPriorWeakTransport


@[expose] public section

/-!
# Endpoint regularity and absolute continuity of the actual history prior
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- The actual finite density has a Lipschitz constant uniform over unbounded histories. -/
theorem historyMarkedDensity_lipschitzOn (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ T B : ℝ) (hρ : 0 < ρ) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (a : E → ℝ) (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) (h : HistoryMarked dependent E) :
    LipschitzOnWith ⟨ρ⁻¹ * (Fintype.card J : ℝ) * B * (3 / 2 : ℝ) ^ Fintype.card J, by positivity⟩
      (fun t => historyMarkedDensity dependent ρ t a h) (Icc 0 T) := by
  apply (convex_Icc (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun u hu => (historyMarkedDensity_hasDerivAt dependent ρ u a h).hasDerivWithinAt)
  intro u hu
  apply NNReal.coe_le_coe.1
  change ‖historyMarkedDensityDerivative dependent ρ u a h‖ ≤ _
  rw [Real.norm_eq_abs]
  exact historyMarkedDensityDerivative_bound dependent hrefl hsymm Δ hlabels ρ u B hρ hu.1 hB a habound
    ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB) hρ.le).trans hsmall) h

/-- Every bounded observable-density product is integrable, including the endpoints. -/
theorem historyMarkedDensityObservable_integrable (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ t B : ℝ) (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) [IsFiniteMeasure μ]
    (a : E → ℝ) (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    Integrable (fun h => F h * historyMarkedDensity dependent ρ t a h) μ := by
  apply Integrable.of_bound (hF.mul (historyMarkedDensity_measurable dependent ρ t a ha)).aestronglyMeasurable
    (M * (3 / 2 : ℝ) ^ Fintype.card J)
  apply Eventually.of_forall
  intro h
  change ‖F h * historyMarkedDensity dependent ρ t a h‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul]
  have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ t B hρ ht hB a habound hsmall h
  have hp : 0 ≤ historyMarkedDensity dependent ρ t a h :=
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
  rw [abs_of_nonneg hp]
  exact mul_le_mul (hFbound h) hb.2 hp hM

/-- Actual history expectations are Lipschitz on the closed source interval. -/
theorem historyMarkedExpectation_lipschitzOn (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ T B : ℝ) (hρ : 0 < ρ) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure μ]
    (a : E → ℝ) (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    LipschitzOnWith ⟨M * (ρ⁻¹ * (Fintype.card J : ℝ) * B * (3 / 2 : ℝ) ^ Fintype.card J), by positivity⟩
      (historyMarkedExpectation dependent ρ μ a F) (Icc 0 T) := by
  let D : ℝ := ρ⁻¹ * (Fintype.card J : ℝ) * B * (3 / 2 : ℝ) ^ Fintype.card J
  have hs : ∀ u ∈ Icc 0 T, u * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) := by
    intro u hu
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB) hρ.le).trans hsmall
  have hi : ∀ u ∈ Icc 0 T, Integrable (fun h => F h * historyMarkedDensity dependent ρ u a h) μ :=
    fun u hu => historyMarkedDensityObservable_integrable dependent hrefl hsymm Δ hlabels ρ u B hρ hu.1 hB
      μ a ha habound (hs u hu) F hF M hM hFbound
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rw [Real.dist_eq, historyMarkedExpectation, historyMarkedExpectation, ← integral_sub (hi u hu) (hi v hv)]
  change ‖∫ h, F h * historyMarkedDensity dependent ρ u a h - F h * historyMarkedDensity dependent ρ v a h ∂μ‖ ≤
    M * D * dist u v
  have hb : ∀ᵐ h ∂μ, ‖F h * historyMarkedDensity dependent ρ u a h - F h * historyMarkedDensity dependent ρ v a h‖ ≤
      M * D * dist u v := by
    apply Eventually.of_forall
    intro h
    rw [← mul_sub, norm_mul, Real.norm_eq_abs]
    have hl := (historyMarkedDensity_lipschitzOn dependent hrefl hsymm Δ hlabels ρ T B hρ hB a habound hsmall h).dist_le_mul u hu v hv
    rw [dist_eq_norm] at hl
    change ‖historyMarkedDensity dependent ρ u a h - historyMarkedDensity dependent ρ v a h‖ ≤ D * dist u v at hl
    exact (mul_le_mul_of_nonneg_right (hFbound h) (norm_nonneg _)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hl hM)
  simpa using norm_integral_le_of_norm_le_const hb

/-- In particular, expectation regularity on the entire interval is proved, not assumed. -/
theorem historyMarkedExpectation_absolutelyContinuous (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ T B : ℝ) (hρ : 0 < ρ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure μ]
    (a : E → ℝ) (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    AbsolutelyContinuousOnInterval (historyMarkedExpectation dependent ρ μ a F) 0 T := by
  have hl := historyMarkedExpectation_lipschitzOn dependent hrefl hsymm Δ hlabels ρ T B hρ hB
    μ a ha habound hsmall F hF M hM hFbound
  rw [← uIcc_of_le hT] at hl
  exact hl.absolutelyContinuousOnInterval

end NearlyMinimax
