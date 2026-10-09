module

public import NearlyMinimax.HistoryWeakTransport


@[expose] public section

/-!
# Weak evolution under the actual positive history prior, rather than only its polynomial
-/

noncomputable section
open MeasureTheory Filter Set
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- A source-positive history prior expectation is exactly its actual polynomial integral. -/
theorem historyMarkedPrior_integral_eq_expectation (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) (a : E → ℝ) (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) :
    (∫ h, F h ∂historyMarkedPrior dependent Δ t π a) =
      historyMarkedExpectation dependent (historyReferenceRho Δ) (historyMarkedReference dependent Δ π) a F t := by
  rw [historyMarkedPrior_eq_withDensity dependent Δ t π a ha,
    integral_withDensity_eq_integral_toReal_smul
      (historyMarkedDensity_measurable dependent _ t a ha).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F]
  unfold historyMarkedExpectation
  apply integral_congr_ae
  apply Eventually.of_forall
  intro h
  have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels
    (historyReferenceRho Δ) t B (historyReferenceRho_pos Δ) ht hB a habound hsmall h
  have hp : 0 ≤ historyMarkedDensity dependent (historyReferenceRho Δ) t a h :=
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
  simp only [ENNReal.toReal_ofReal hp, smul_eq_mul]
  ring

/-- The signed local append expression evaluated under the actual positive prior. -/
def historyMarkedPriorGenerator (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (Δ : ℕ) (t : ℝ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) (a : E → ℝ)
    (F : HistoryMarked dependent E → ℝ) : ℝ :=
  ∑ j, ∫ p : HistoryMarked dependent E × E,
    F (historyMarkedAppend dependent hsymm j p) * a p.2
      ∂(historyMarkedPrior dependent Δ t π a).prod π

/-- The genuine prior generator equals the source reference polynomial generator. -/
theorem historyMarkedPriorGenerator_eq_reference (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) :
    historyMarkedPriorGenerator dependent hsymm Δ t π a F =
      historyMarkedGeneratorExpectation dependent hsymm (historyReferenceRho Δ) t
        (historyMarkedReference dependent Δ π) π a F := by
  unfold historyMarkedPriorGenerator historyMarkedGeneratorExpectation
  apply Finset.sum_congr rfl
  intro j hj
  have hm : Measurable (fun p : HistoryMarked dependent E × E =>
      ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a p.1)) :=
    (historyMarkedDensity_measurable dependent (historyReferenceRho Δ) t a ha).ennreal_ofReal.comp measurable_fst
  rw [historyMarkedPrior_eq_withDensity dependent Δ t π a ha,
    prod_withDensity_left (historyMarkedDensity_measurable dependent _ t a ha).ennreal_ofReal,
    integral_withDensity_eq_integral_toReal_smul hm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels
    (historyReferenceRho Δ) t B (historyReferenceRho_pos Δ) ht hB a habound hsmall p.1
  have hp : 0 ≤ historyMarkedDensity dependent (historyReferenceRho Δ) t a p.1 :=
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
  simp only [ENNReal.toReal_ofReal hp, smul_eq_mul]
  ring

/-- Actual positive marked-history prior expectations satisfy the source weak signed-update equation. -/
theorem historyMarkedPrior_weak_transport (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T B t : ℝ) (ht : 0 < t) (htT : t < T) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    HasDerivAt (fun u => ∫ h, F h ∂historyMarkedPrior dependent Δ u π a)
      (historyMarkedPriorGenerator dependent hsymm Δ t π a F) t := by
  have hs : ∀ u ∈ Ioo 0 T, u * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) := by
    intro u hu
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hB)
      (historyReferenceRho_pos Δ).le).trans hsmall
  have hd := historyMarkedExpectation_weak_transport dependent hrefl hsymm Δ hΔ hlabels
    T B t ht htT hB π a ha habound hsmall F hF M hM hFbound
  rw [← historyMarkedPriorGenerator_eq_reference dependent hrefl hsymm Δ hlabels
    t B ht.le hB π a ha habound (hs t ⟨ht, htT⟩) F] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht htT] with u hu
  exact historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels
    u B hu.1.le hB π a ha habound (hs u hu) F

end NearlyMinimax
