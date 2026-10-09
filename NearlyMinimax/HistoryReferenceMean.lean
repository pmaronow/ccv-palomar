module

public import NearlyMinimax.HistoryReferenceMeasure


@[expose] public section

/-! Conditional mean one on every genuine independent shape fiber implies
mean one under the actual normalized countable history reference law. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

theorem historyMarkedReference_integral_one {J E : Type*}
    [Fintype J] [LinearOrder J] [MeasurableSpace E]
    (dependent : J → J → Prop) (hrefl : ∀ j, dependent j j)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (π : Measure E) [IsProbabilityMeasure π]
    (F : HistoryMarked dependent E → ℝ) (hf : Measurable F)
    (hF0 : ∀ h, 0 ≤ F h) (M : ℝ) (hFM : ∀ h, ‖F h‖ ≤ M)
    (hmean : ∀ g, (∫ marks, F ⟨g, marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) = 1) :
    (∫ h, F h ∂historyMarkedReference dependent Δ π) = 1 := by
  letI := historyMarkedReferenceRaw_finite dependent hrefl hsymm Δ hΔ hlabels π
  letI := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  have hi : Integrable F (historyMarkedReference dependent Δ π) :=
    (integrable_const M).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hFM)
  have hraw : (∫⁻ h, ENNReal.ofReal (F h) ∂historyMarkedReferenceRaw dependent Δ π) =
      historyMarkedReferenceRaw dependent Δ π univ := by
    rw [historyMarkedReferenceRaw_univ, historyMarkedReferenceRaw, lintegral_sum_measure]
    apply tsum_congr
    intro g
    rw [lintegral_smul_measure, lintegral_map' (hf.ennreal_ofReal.aemeasurable)
      (historyMarked_measurable_mk dependent g).aemeasurable]
    have hif : Integrable (fun marks => F ⟨g, marks⟩)
        (Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) :=
      (integrable_const M).mono' (hf.comp (historyMarked_measurable_mk dependent g)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun marks => hFM ⟨g, marks⟩))
    rw [← ofReal_integral_eq_lintegral_ofReal hif (Filter.Eventually.of_forall
      (fun marks => hF0 ⟨g, marks⟩)), hmean g, ENNReal.ofReal_one, smul_eq_mul, mul_one]
  have hpos : historyMarkedReferenceRaw dependent Δ π univ ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (historyMarkedReferenceRaw_univ_one_le dependent Δ π))
  have hn : (∫⁻ h, ENNReal.ofReal (F h) ∂historyMarkedReference dependent Δ π) = 1 := by
    rw [historyMarkedReference, lintegral_smul_measure, hraw]
    exact ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)
  have he := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hF0)
  rw [hn] at he
  exact ENNReal.ofReal_eq_one.mp he

end NearlyMinimax
