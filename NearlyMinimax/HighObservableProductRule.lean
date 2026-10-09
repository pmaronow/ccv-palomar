module

public import NearlyMinimax.HistoryPriorWeakTransport


@[expose] public section

/-! Actual time-dependent observable product rule under the constructed history prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

/-- Differentiation of a time-dependent bounded observable under the actual
positive marked-history law. The prior derivative is proved from its genuine
source polynomial and append generator. -/
theorem historyMarkedPrior_observable_product_rule (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T B t : ℝ) (ht : 0 < t) (htT : t < T) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (G G' : ℝ → HistoryMarked dependent E → ℝ)
    (hGM : ∀ u, Measurable (G u)) (hG'M : ∀ u, Measurable (G' u))
    (M M' : ℝ) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hGb : ∀ u ∈ Ioo 0 T, ∀ h, |G u h| ≤ M)
    (hG'b : ∀ u ∈ Ioo 0 T, ∀ h, |G' u h| ≤ M')
    (hGD : ∀ h u, u ∈ Ioo 0 T → HasDerivAt (fun v => G v h) (G' u h) u) :
    HasDerivAt (fun u => ∫ h, G u h ∂historyMarkedPrior dependent Δ u π a)
      ((∫ h, G' t h ∂historyMarkedPrior dependent Δ t π a) +
        historyMarkedPriorGenerator dependent hsymm Δ t π a (G t)) t := by
  let μ := historyMarkedReference dependent Δ π
  let _ : IsProbabilityMeasure μ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  let ρ := historyReferenceRho Δ
  let C : ℝ := (3 / 2 : ℝ) ^ Fintype.card J
  let D : ℝ := ρ⁻¹ * (Fintype.card J : ℝ) * B * C
  have hρ : 0 < ρ := historyReferenceRho_pos Δ
  have hC : 0 ≤ C := by positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hs (u : ℝ) (hu : u ∈ Ioo 0 T) : u * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hB)
      (historyReferenceRho_pos Δ).le).trans hsmall
  have hφ (u : ℝ) (hu : u ∈ Ioo 0 T) (h : HistoryMarked dependent E) :
      |historyMarkedDensity dependent ρ u a h| ≤ C := by
    have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ u B
      (historyReferenceRho_pos Δ) hu.1.le hB a habound (hs u hu) h
    have hn : 0 ≤ historyMarkedDensity dependent ρ u a h :=
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
    rw [abs_of_nonneg hn]
    exact hb.2
  have hφd (u : ℝ) (hu : u ∈ Ioo 0 T) (h : HistoryMarked dependent E) :
      |historyMarkedDensityDerivative dependent ρ u a h| ≤ D :=
    historyMarkedDensityDerivative_bound dependent hrefl hsymm Δ hlabels ρ u B
      (historyReferenceRho_pos Δ) hu.1.le hB a habound (hs u hu) h
  let H : ℝ → HistoryMarked dependent E → ℝ := fun u h =>
    G u h * historyMarkedDensity dependent ρ u a h
  let H' : ℝ → HistoryMarked dependent E → ℝ := fun u h =>
    G' u h * historyMarkedDensity dependent ρ u a h +
      G u h * historyMarkedDensityDerivative dependent ρ u a h
  have hHM (u : ℝ) : Measurable (H u) :=
    (hGM u).mul (historyMarkedDensity_measurable dependent ρ u a ha)
  have hH'M (u : ℝ) : Measurable (H' u) :=
    ((hG'M u).mul (historyMarkedDensity_measurable dependent ρ u a ha)).add
      ((hGM u).mul (historyMarkedDensityDerivative_measurable dependent ρ u a ha))
  have hHb (u : ℝ) (hu : u ∈ Ioo 0 T) (h : HistoryMarked dependent E) : ‖H u h‖ ≤ M * C := by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hGb u hu h) (hφ u hu h) (abs_nonneg _) hM
  have hH'b (u : ℝ) (hu : u ∈ Ioo 0 T) (h : HistoryMarked dependent E) :
      ‖H' u h‖ ≤ M' * C + M * D := by
    rw [Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul]; exact mul_le_mul (hG'b u hu h) (hφ u hu h) (abs_nonneg _) hM')
      (by rw [abs_mul]; exact mul_le_mul (hGb u hu h) (hφd u hu h) (abs_nonneg _) hM))
  have hi : Integrable (H t) μ := Integrable.of_bound (hHM t).aestronglyMeasurable
    (M * C) (Eventually.of_forall (hHb t ⟨ht, htT⟩))
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := H) (F' := H') (bound := fun _ => M' * C + M * D)
    (s := Ioo 0 T) (Ioo_mem_nhds ht htT)
    (Eventually.of_forall fun u => (hHM u).aestronglyMeasurable)
    hi (hH'M t).aestronglyMeasurable
    (Eventually.of_forall fun h u hu => hH'b u hu h)
    (integrable_const (M' * C + M * D))
    (Eventually.of_forall fun h u hu => (hGD h u hu).mul
      (historyMarkedDensity_hasDerivAt dependent ρ u a h))).2
  have hi1 : Integrable (fun h => G' t h * historyMarkedDensity dependent ρ t a h) μ := by
    apply Integrable.of_bound ((hG'M t).mul
      (historyMarkedDensity_measurable dependent ρ t a ha)).aestronglyMeasurable (M' * C)
    exact Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul (hG'b t ⟨ht, htT⟩ h) (hφ t ⟨ht, htT⟩ h) (abs_nonneg _) hM'
  have hi2 : Integrable (fun h => G t h * historyMarkedDensityDerivative dependent ρ t a h) μ := by
    apply Integrable.of_bound ((hGM t).mul
      (historyMarkedDensityDerivative_measurable dependent ρ t a ha)).aestronglyMeasurable (M * D)
    exact Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul (hGb t ⟨ht, htT⟩ h) (hφd t ⟨ht, htT⟩ h) (abs_nonneg _) hM
  have hfirst := historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels
    t B ht.le hB π a ha habound (hs t ⟨ht, htT⟩) (G' t)
  unfold historyMarkedExpectation at hfirst
  have hsecond := historyMarkedDensityDerivative_integral_eq_generator dependent hrefl hsymm Δ hΔ hlabels
    t B ht.le hB π a ha habound (hs t ⟨ht, htT⟩) (G t) (hGM t) M hM
      (hGb t ⟨ht, htT⟩)
  rw [← historyMarkedPriorGenerator_eq_reference dependent hrefl hsymm Δ hlabels
    t B ht.le hB π a ha habound (hs t ⟨ht, htT⟩) (G t)] at hsecond
  change HasDerivAt (fun u => ∫ h, H u h ∂μ) _ t at hd
  have he : (∫ h, H' t h ∂μ) =
      (∫ h, G' t h ∂historyMarkedPrior dependent Δ t π a) +
        historyMarkedPriorGenerator dependent hsymm Δ t π a (G t) := by
    rw [integral_add hi1 hi2, ← hfirst, hsecond]
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht htT] with u hu
  exact historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels
    u B hu.1.le hB π a ha habound (hs u hu) (G u)

end NearlyMinimax
