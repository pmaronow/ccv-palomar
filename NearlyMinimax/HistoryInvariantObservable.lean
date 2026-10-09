module

public import NearlyMinimax.HistoryExpectationRegularity


@[expose] public section

/-!
# Invariant observable laws derived from genuine conditional local annihilation
-/

noncomputable section
open MeasureTheory Filter Set
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- Conditional signed-mark annihilation kills the true append generator by Fubini. -/
theorem historyMarkedGeneratorExpectation_eq_zero (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M)
    (hkill : ∀ j h, ∫ e, F (historyMarkedAppend dependent hsymm j (h, e)) * a e ∂π = 0) :
    historyMarkedGeneratorExpectation dependent hsymm (historyReferenceRho Δ) t
      (historyMarkedReference dependent Δ π) π a F = 0 := by
  let μ := historyMarkedReference dependent Δ π
  let : IsProbabilityMeasure μ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  unfold historyMarkedGeneratorExpectation
  apply Finset.sum_eq_zero
  intro j hj
  let G := fun p : HistoryMarked dependent E × E =>
    F (historyMarkedAppend dependent hsymm j p) * a p.2 *
      historyMarkedDensity dependent (historyReferenceRho Δ) t a p.1
  have hG : Measurable G :=
    ((hF.comp (historyMarkedAppend_measurable dependent hsymm j)).mul (ha.comp measurable_snd)).mul
      ((historyMarkedDensity_measurable dependent _ t a ha).comp measurable_fst)
  have hInt : Integrable G (μ.prod π) := by
    apply Integrable.of_bound hG.aestronglyMeasurable (M * B * (3 / 2 : ℝ) ^ Fintype.card J)
    apply Eventually.of_forall
    intro p
    change ‖F (historyMarkedAppend dependent hsymm j p) * a p.2 *
      historyMarkedDensity dependent (historyReferenceRho Δ) t a p.1‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels
      (historyReferenceRho Δ) t B (historyReferenceRho_pos Δ) ht hB a habound hsmall p.1
    have hp : 0 ≤ historyMarkedDensity dependent (historyReferenceRho Δ) t a p.1 :=
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
    rw [abs_of_nonneg hp]
    exact mul_le_mul (mul_le_mul (hFbound _) (habound _) (abs_nonneg _) hM) hb.2 hp (mul_nonneg hM hB)
  change (∫ p, G p ∂μ.prod π) = 0
  rw [integral_prod G hInt]
  have hin : ∀ h, ∫ e, G (h, e) ∂π = 0 := by
    intro h
    dsimp only [G]
    rw [integral_mul_const, hkill j h, zero_mul]
  simp_rw [hin]
  exact integral_zero _ _

/-- An annihilated bounded observable has the same expectation throughout the closed source interval. -/
theorem historyMarkedPrior_invariant_observable (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M)
    (hkill : ∀ j h, ∫ e, F (historyMarkedAppend dependent hsymm j (h, e)) * a e ∂π = 0)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫ h, F h ∂historyMarkedPrior dependent Δ t π a) = ∫ h, F h ∂historyMarkedReference dependent Δ π := by
  let μ := historyMarkedReference dependent Δ π
  let : IsProbabilityMeasure μ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  let f := historyMarkedExpectation dependent (historyReferenceRho Δ) μ a F
  have hs : ∀ u ∈ Icc 0 T, u * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) := by
    intro u hu
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB)
      (historyReferenceRho_pos Δ).le).trans hsmall
  have hAC : AbsolutelyContinuousOnInterval f 0 T :=
    historyMarkedExpectation_absolutelyContinuous dependent hrefl hsymm Δ hlabels
      (historyReferenceRho Δ) T B (historyReferenceRho_pos Δ) hT hB μ a ha habound hsmall F hF M hM hFbound
  have hn0 : ∀ᵐ u : ℝ, u ≠ 0 := by rw [ae_iff]; simp
  have hnT : ∀ᵐ u : ℝ, u ≠ T := by rw [ae_iff]; simp
  have hzero : ∀ᵐ u : ℝ, u ∈ uIcc 0 T → HasDerivAt f 0 u := by
    filter_upwards [hn0, hnT] with u hu0 huT hu
    rw [uIcc_of_le hT] at hu
    have hd := historyMarkedExpectation_weak_transport dependent hrefl hsymm Δ hΔ hlabels
      T B u (lt_of_le_of_ne hu.1 (Ne.symm hu0)) (lt_of_le_of_ne hu.2 huT) hB
      π a ha habound hsmall F hF M hM hFbound
    rw [historyMarkedGeneratorExpectation_eq_zero dependent hrefl hsymm Δ hΔ hlabels u B hu.1 hB
      π a ha habound (hs u hu) F hF M hM hFbound hkill] at hd
    exact hd
  obtain ⟨C, hC⟩ := hAC.const_of_ae_hasDerivAt_zero hzero
  have hft : f t = f 0 := (hC t (by simpa only [uIcc_of_le hT] using ht)).trans
    (hC 0 (by simp only [uIcc_of_le hT, mem_Icc]; exact ⟨le_rfl, hT⟩)).symm
  rw [historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels
    t B ht.1 hB π a ha habound (hs t ht) F]
  change f t = _
  rw [hft]
  simp [f, μ, historyMarkedExpectation, historyMarkedDensity_zero]

end NearlyMinimax
