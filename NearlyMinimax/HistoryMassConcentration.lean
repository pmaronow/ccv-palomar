module

public import NearlyMinimax.LabelBlockConcentration
public import NearlyMinimax.HistoryReferenceFiberIntegral


@[expose] public section

/-!
# Mass exponential moment from actual canonical-history label blocks
-/

noncomputable section
open MeasureTheory Filter
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- The genuine reference mean is one when every actual canonical mark fiber has mean one. -/
theorem historyMarkedReference_mean_one (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
    (m : HistoryMarked dependent E → ℝ) (hm : Measurable m) (R : ℝ) (hbound : ∀ h, |m h| ≤ R)
    (hmean : ∀ g, (∫ marks, m ⟨g, marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) = 1) :
    (∫ h, m h ∂historyMarkedReference dependent Δ π) = 1 := by
  have hu := historyMarkedReference_integral_le_of_fiber_bound dependent hrefl hsymm Δ hΔ hlabels
    π m hm R 1 hbound (fun g => (hmean g).le)
  have hl := historyMarkedReference_integral_le_of_fiber_bound dependent hrefl hsymm Δ hΔ hlabels
    π (fun h => -m h) hm.neg R (-1) (fun h => by simpa only [abs_neg] using hbound h)
    (fun g => by rw [integral_neg, hmean g])
  rw [integral_neg] at hl
  linarith

/-- Actual source mean-one and label-block oscillation prove the mass MGF under the true infinite reference.
The hypotheses describe the actual measurable mass function, its finite recursion mean, and geometric locality.
No mass concentration or statistical rate bound is a premise. -/
theorem historyMarkedReference_mass_mgf (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] [Nonempty E] (π : Measure E) [IsProbabilityMeasure π]
    (m : HistoryMarked dependent E → ℝ) (hm : Measurable m)
    (R c : ℝ) (hc : 0 ≤ c) (hbound : ∀ h, |m h| ≤ R)
    (hmean : ∀ g, (∫ marks, m ⟨g, marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) = 1)
    (hosc : ∀ g j (marks marks' : Fin (historyShapeLength dependent g) → E),
      (∀ i, historyShapeCanonicalLabels dependent g i ≠ j → marks i = marks' i) →
        |m ⟨g, marks⟩ - m ⟨g, marks'⟩| ≤ c) (u : ℝ) :
    (∫ h, Real.exp (u * (m h - 1)) ∂historyMarkedReference dependent Δ π) ≤
      Real.exp ((Fintype.card J : ℝ) * u ^ 2 * c ^ 2 / 8) := by
  let F := fun h : HistoryMarked dependent E => Real.exp (u * (m h - 1))
  have hF : Measurable F := Real.measurable_exp.comp (measurable_const.mul (hm.sub measurable_const))
  have hFb : ∀ h, |F h| ≤ Real.exp (|u| * (R + 1)) := by
    intro h
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    calc
      _ ≤ |u * (m h - 1)| := le_abs_self _
      _ = |u| * |m h - 1| := abs_mul _ _
      _ ≤ |u| * (R + 1) := mul_le_mul_of_nonneg_left
        (by have hh := abs_sub (m h) 1; norm_num only [abs_one] at hh; linarith [hbound h]) (abs_nonneg _)
  apply historyMarkedReference_integral_le_of_fiber_bound dependent hrefl hsymm Δ hΔ hlabels π F hF
    (Real.exp (|u| * (R + 1))) _ hFb
  intro g
  have hmf : Measurable (fun marks : Fin (historyShapeLength dependent g) → E => m ⟨g, marks⟩) :=
    hm.comp (historyMarked_measurable_mk dependent g)
  have hh := label_block_centered_mgf_le (historyShapeCanonicalLabels dependent g) π
    (fun marks => m ⟨g, marks⟩) hmf R c hc (fun marks => hbound ⟨g, marks⟩) (hosc g) u
  rw [hmean g] at hh
  exact hh

end NearlyMinimax
