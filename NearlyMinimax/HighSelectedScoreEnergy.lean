module

public import NearlyMinimax.HighDesignEnergySeries


@[expose] public section

/-! True selected normalized-design score energies. The squared likelihood
ratio cancels against the genuine response and design density, leaving
the source fixed denominator constant and the raw spatial numerator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem fintype_probability_pi_withDensity {κ α : Type*} [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ≥0∞) (hf : Measurable f) (hprob : IsProbabilityMeasure (μ.withDensity f)) :
    Measure.pi (fun _ : κ => μ.withDensity f) =
      (Measure.pi (fun _ : κ => μ)).withDensity (fun x => ∏ i, f (x i)) := by
  let _ := hprob
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator]
  · have he (x : κ → α) :
        (Set.pi Set.univ s).indicator (fun x => ∏ i, f (x i)) x =
          ∏ i, (s i).indicator f (x i) := by
      by_cases h : ∀ i, x i ∈ s i
      · simp [Set.indicator_of_mem, Set.mem_pi, h]
      · obtain ⟨i, hi⟩ := not_forall.mp h
        have hz : ∏ j, (s j).indicator f (x j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f)
        rw [hz]
        apply Set.indicator_of_notMem
        simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
        exact not_forall.mpr ⟨i, hi⟩
    simp_rw [he]
    let G : κ → α → ℝ≥0∞ := fun i => (s i).indicator f
    have hG : ∀ i, Measurable (G i) := fun i => hf.indicator (hs i)
    change (∫⁻ x, ∏ i, G i (x i) ∂Measure.pi (fun _ : κ => μ)) = _
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _
      (iIndepFun_pi (fun i => (hG i).aemeasurable))
      (fun i => (hG i).comp (measurable_pi_apply i))]
    apply Finset.prod_congr rfl
    intro i _
    rw [(measurePreserving_eval (fun _ : κ => μ) i).lintegral_comp (hG i)]
    change (∫⁻ b, (s i).indicator f b ∂μ) = _
    rw [lintegral_indicator (hs i), withDensity_apply f (hs i)]
  · exact MeasurableSet.univ_pi hs

theorem fintype_probability_pi_restrict_withDensity {κ α : Type*} [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ≥0∞) (hf : Measurable f) (hprob : IsProbabilityMeasure (μ.withDensity f))
    (A : Set α) (hA : MeasurableSet A) :
    Measure.pi (fun _ : κ => (μ.withDensity f).restrict A) =
      (Measure.pi (fun _ : κ => μ.restrict A)).withDensity (fun x => ∏ i, f (x i)) := by
  rw [← Measure.restrict_pi_pi (fun _ : κ => μ.withDensity f) (fun _ => A),
    fintype_probability_pi_withDensity μ f hf hprob,
    restrict_withDensity (MeasurableSet.univ_pi (fun _ => hA)),
    Measure.restrict_pi_pi]

def selectedRawLikelihood {κ α : Type*} [Fintype κ]
    (p : α → ℝ) (q : α → Fin 3 → ℝ) (x : κ → α) (y : κ → Fin 3) : ℝ :=
  (∏ i, p (x i)) * ∏ i, q (x i) (y i)

def selectedConditionalScoreEnergy {κ α : Type*} [Fintype κ]
    (p : α → ℝ) (q : α → Fin 3 → ℝ)
    (R : (κ → α) → (κ → Fin 3) → ℝ) (x : κ → α) : ℝ :=
  ∑ y : κ → Fin 3, (∏ i, q (x i) (y i)) * (R x y / selectedRawLikelihood p q x y) ^ 2

def selectedRawSquareEnergy {κ α : Type*} [Fintype κ]
    (R : (κ → α) → (κ → Fin 3) → ℝ) (x : κ → α) : ℝ :=
  ∑ y : κ → Fin 3, (R x y) ^ 2

theorem selected_conditional_score_energy_nonneg {κ α : Type*} [Fintype κ]
    (p : α → ℝ) (q : α → Fin 3 → ℝ) (hq : ∀ x y, 0 ≤ q x y)
    (R : (κ → α) → (κ → Fin 3) → ℝ) (x : κ → α) :
    0 ≤ selectedConditionalScoreEnergy p q R x :=
  Finset.sum_nonneg (fun y _ => mul_nonneg (Finset.prod_nonneg (fun i _ => hq _ _)) (sq_nonneg _))

theorem selected_raw_likelihood_positive {κ α : Type*} [Fintype κ]
    (p : α → ℝ) (q : α → Fin 3 → ℝ) (x : κ → α) (y : κ → Fin 3)
    (hp : ∀ i, 0 < p (x i)) (hq : ∀ i, 0 < q (x i) (y i)) :
    0 < selectedRawLikelihood p q x y :=
  mul_pos (Finset.prod_pos (fun i _ => hp i)) (Finset.prod_pos (fun i _ => hq i))

theorem selected_score_density_cancel {κ α : Type*} [Fintype κ]
    (m : ℝ) (hm : 0 < m) (p : α → ℝ) (q : α → Fin 3 → ℝ)
    (R : (κ → α) → (κ → Fin 3) → ℝ) (x : κ → α)
    (hp : ∀ i, 0 < p (x i)) (hq : ∀ i y, 0 < q (x i) y) :
    (∏ i, p (x i) / m) * selectedConditionalScoreEnergy p q R x =
      ∑ y : κ → Fin 3,
        (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2 := by
  unfold selectedConditionalScoreEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  have hpP : (∏ i, p (x i)) ≠ 0 := ne_of_gt (Finset.prod_pos (fun i _ => hp i))
  have hqP : (∏ i, q (x i) (y i)) ≠ 0 := ne_of_gt (Finset.prod_pos (fun i _ => hq i (y i)))
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  unfold selectedRawLikelihood
  field_simp [hpP, hqP, hm.ne']
  <;> ring

theorem selected_raw_inverse_floor {κ α : Type*} [Fintype κ]
    (m pMinus cMass : ℝ) (hpMinus : 0 < pMinus) (hcMass : 0 < cMass)
    (hm : pMinus ≤ m) (p : α → ℝ) (q : α → Fin 3 → ℝ)
    (x : κ → α) (y : κ → Fin 3)
    (hp : ∀ i, pMinus ≤ p (x i)) (hq : ∀ i, cMass ≤ q (x i) (y i)) :
    (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ ≤
      highFixedScoreDenominator pMinus cMass ^ Fintype.card κ := by
  have hfac (i : κ) : pMinus ^ 2 * cMass ≤ m * (p (x i) * q (x i) (y i)) := by
    have hq0 : 0 ≤ q (x i) (y i) := hcMass.le.trans (hq i)
    have hp0 : 0 ≤ p (x i) := hpMinus.le.trans (hp i)
    have hpq := mul_le_mul (hp i) (hq i) hcMass.le hp0
    have hh := mul_le_mul hm hpq (mul_nonneg hpMinus.le hcMass.le) (hpMinus.le.trans hm)
    nlinarith
  have hprod : (pMinus ^ 2 * cMass) ^ Fintype.card κ ≤
      m ^ Fintype.card κ * selectedRawLikelihood p q x y := by
    calc
      _ = ∏ _i : κ, pMinus ^ 2 * cMass := by simp
      _ ≤ ∏ i, m * (p (x i) * q (x i) (y i)) :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hfac i)
      _ = _ := by unfold selectedRawLikelihood; rw [Finset.prod_mul_distrib]; simp [Finset.prod_mul_distrib]
  have hleft : 0 < (pMinus ^ 2 * cMass) ^ Fintype.card κ := by positivity
  have hright : 0 < m ^ Fintype.card κ * selectedRawLikelihood p q x y := hleft.trans_le hprod
  unfold highFixedScoreDenominator
  rw [inv_pow]
  exact (inv_le_inv₀ hright hleft).mpr hprod

theorem normalized_selected_score_density_cancel_ae {κ α : Type*} [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (A : Set α) (hA : MeasurableSet A) (m : ℝ) (hm : 0 < m)
    (p : α → ℝ) (q : α → Fin 3 → ℝ)
    (R : (κ → α) → (κ → Fin 3) → ℝ)
    (hp : ∀ x ∈ A, 0 < p x) (hq : ∀ x ∈ A, ∀ y, 0 < q x y) :
    (fun x => (∏ i, ENNReal.ofReal (p (x i) / m)).toReal *
      selectedConditionalScoreEnergy p q R x) =ᵐ[Measure.pi (fun _ : κ => μ.restrict A)]
      (fun x => ∑ y : κ → Fin 3,
        (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2) := by
  have hmem : ∀ᵐ x ∂Measure.pi (fun _ : κ => μ.restrict A), ∀ i, x i ∈ A :=
    ae_all_iff.mpr (fun i => Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem hA))
  filter_upwards [hmem] with x hx
  have he : (∏ i, ENNReal.ofReal (p (x i) / m)).toReal = ∏ i, p (x i) / m := by
    rw [ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i hi
    exact ENNReal.toReal_ofReal (div_nonneg (hp _ (hx i)).le hm.le)
  rw [he]
  exact selected_score_density_cancel m hm p q R x (fun i => hp _ (hx i))
    (fun i y => hq _ (hx i) y)

theorem normalized_selected_score_energy_integral_eq_raw {κ α : Type*} [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (A : Set α) (hA : MeasurableSet A) (m : ℝ) (hm : 0 < m)
    (p : α → ℝ) (hpMeas : Measurable p) (q : α → Fin 3 → ℝ)
    (R : (κ → α) → (κ → Fin 3) → ℝ)
    (hprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (p x / m))))
    (hp : ∀ x ∈ A, 0 < p x) (hq : ∀ x ∈ A, ∀ y, 0 < q x y) :
    (∫ x, selectedConditionalScoreEnergy p q R x
      ∂Measure.pi (fun _ : κ => (μ.withDensity (fun z => ENNReal.ofReal (p z / m))).restrict A)) =
      ∫ x, ∑ y : κ → Fin 3,
        (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2
          ∂Measure.pi (fun _ : κ => μ.restrict A) := by
  have hf : Measurable (fun x => ENNReal.ofReal (p x / m)) :=
    ENNReal.measurable_ofReal.comp (hpMeas.div_const m)
  rw [fintype_probability_pi_restrict_withDensity μ _ hf hprob A hA]
  have hfP : Measurable (fun x : κ → α => ∏ i, ENNReal.ofReal (p (x i) / m)) :=
    Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))
  have he := integral_withDensity_eq_integral_toReal_smul
    (μ := Measure.pi (fun _ : κ => μ.restrict A)) hfP
    (Filter.Eventually.of_forall (fun _ => ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)))
    (selectedConditionalScoreEnergy p q R)
  change (∫ x, selectedConditionalScoreEnergy p q R x
    ∂(Measure.pi (fun _ : κ => μ.restrict A)).withDensity (fun x => ∏ i, ENNReal.ofReal (p (x i) / m))) =
      ∫ x, (∏ i, ENNReal.ofReal (p (x i) / m)).toReal * selectedConditionalScoreEnergy p q R x
        ∂Measure.pi (fun _ : κ => μ.restrict A) at he
  rw [he]
  apply integral_congr_ae
  exact normalized_selected_score_density_cancel_ae μ A hA m hm p q R hp hq

theorem normalized_selected_score_energy_integrable_bound {κ α : Type*} [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (A : Set α) (hA : MeasurableSet A) (m pMinus cMass : ℝ)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hm : pMinus ≤ m)
    (p : α → ℝ) (hpMeas : Measurable p) (q : α → Fin 3 → ℝ)
    (hqMeas : ∀ y, Measurable (fun x => q x y))
    (R : (κ → α) → (κ → Fin 3) → ℝ) (hR : ∀ y, Measurable (fun x => R x y))
    (hprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (p x / m))))
    (hp : ∀ x ∈ A, pMinus ≤ p x) (hq : ∀ x ∈ A, ∀ y, cMass ≤ q x y)
    (hRaw : Integrable (selectedRawSquareEnergy R) (Measure.pi (fun _ : κ => μ.restrict A))) :
    Integrable (selectedConditionalScoreEnergy p q R)
      (Measure.pi (fun _ : κ => (μ.withDensity (fun z => ENNReal.ofReal (p z / m))).restrict A)) ∧
    (∫ x, selectedConditionalScoreEnergy p q R x
      ∂Measure.pi (fun _ : κ => (μ.withDensity (fun z => ENNReal.ofReal (p z / m))).restrict A)) ≤
      highFixedScoreDenominator pMinus cMass ^ Fintype.card κ *
        ∫ x, selectedRawSquareEnergy R x ∂Measure.pi (fun _ : κ => μ.restrict A) := by
  have hm0 : 0 < m := hpMinus.trans_le hm
  have hpp (x : α) (hx : x ∈ A) : 0 < p x := hpMinus.trans_le (hp x hx)
  have hqp (x : α) (hx : x ∈ A) (y : Fin 3) : 0 < q x y := hcMass.trans_le (hq x hx y)
  let W : (κ → α) → ℝ := fun x => ∑ y : κ → Fin 3,
    (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2
  have hWMeas : Measurable W := by
    apply Finset.measurable_sum
    intro y hy
    have hqm : Measurable (fun x : κ → α => ∏ i, q (x i) (y i)) :=
      Finset.measurable_prod _ (fun i _ => (hqMeas (y i)).comp (measurable_pi_apply i))
    have hpm : Measurable (fun x : κ → α => ∏ i, p (x i)) :=
      Finset.measurable_prod _ (fun i _ => hpMeas.comp (measurable_pi_apply i))
    unfold selectedRawLikelihood
    fun_prop
  have hmem : ∀ᵐ x ∂Measure.pi (fun _ : κ => μ.restrict A), ∀ i, x i ∈ A :=
    ae_all_iff.mpr (fun i => Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem hA))
  have hWbound : ∀ᵐ x ∂Measure.pi (fun _ : κ => μ.restrict A),
      0 ≤ W x ∧ W x ≤ highFixedScoreDenominator pMinus cMass ^ Fintype.card κ * selectedRawSquareEnergy R x := by
    filter_upwards [hmem] with x hx
    constructor
    · apply Finset.sum_nonneg
      intro y hy
      have hL := selected_raw_likelihood_positive p q x y (fun i => hpp _ (hx i))
        (fun i => hqp _ (hx i) (y i))
      exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (pow_nonneg hm0.le _) hL.le)) (sq_nonneg _)
    · unfold W selectedRawSquareEnergy
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_right
        (selected_raw_inverse_floor m pMinus cMass hpMinus hcMass hm p q x y
          (fun i => hp _ (hx i)) (fun i => hq _ (hx i) (y i))) (sq_nonneg _)
  have hJ := hRaw.const_mul (highFixedScoreDenominator pMinus cMass ^ Fintype.card κ)
  have hWI : Integrable W (Measure.pi (fun _ : κ => μ.restrict A)) := by
    apply hJ.mono' hWMeas.aestronglyMeasurable
    filter_upwards [hWbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  constructor
  · have hf : Measurable (fun x => ENNReal.ofReal (p x / m)) :=
      ENNReal.measurable_ofReal.comp (hpMeas.div_const m)
    have hfP : Measurable (fun x : κ → α => ∏ i, ENNReal.ofReal (p (x i) / m)) :=
      Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))
    rw [fintype_probability_pi_restrict_withDensity μ _ hf hprob A hA]
    apply (integrable_withDensity_iff_integrable_smul' hfP
      (Filter.Eventually.of_forall (fun _ => ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)))).mpr
    have he := normalized_selected_score_density_cancel_ae μ A hA m hm0 p q R hpp hqp
    exact hWI.congr he.symm
  rw [normalized_selected_score_energy_integral_eq_raw μ A hA m hm0 p hpMeas q R hprob hpp hqp]
  calc
    _ ≤ ∫ x, highFixedScoreDenominator pMinus cMass ^ Fintype.card κ * selectedRawSquareEnergy R x
        ∂Measure.pi (fun _ : κ => μ.restrict A) :=
      integral_mono_ae hWI hJ (hWbound.mono (fun x hx => hx.2))
    _ = _ := integral_const_mul _ _

end NearlyMinimax
