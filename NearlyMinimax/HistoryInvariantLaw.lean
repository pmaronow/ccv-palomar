module

public import NearlyMinimax.HistoryInvariantObservable


@[expose] public section

/-!
# Invariant pushforward law from actual conditional signed update annihilation
-/

noncomputable section
open MeasureTheory Filter Set
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- Actual weak transport and local signed annihilation prove equality of pushforward laws.
The hypothesis is the local packet integral for indicators; law invariance is the conclusion. -/
theorem historyMarkedPrior_invariant_law (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    {E X : Type*} [MeasurableSpace E] [StandardBorelSpace E] [MeasurableSpace X]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (f : HistoryMarked dependent E → X) (hf : Measurable f)
    (hkill : ∀ j h S, MeasurableSet S →
      ∫ e, (S.indicator (fun _ : X => (1 : ℝ)))
        (f (historyMarkedAppend dependent hsymm j (h, e))) * a e ∂π = 0)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Measure.map f (historyMarkedPrior dependent Δ t π a) =
      Measure.map f (historyMarkedReference dependent Δ π) := by
  have hi : Integrable a π := Integrable.of_bound ha.aestronglyMeasurable B
    (Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e)
  have hs : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hB) (historyReferenceRho_pos Δ).le).trans hsmall
  let := historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels t B ht.1 hB π a hi hcenter habound hs
  let := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  ext S hS
  rw [Measure.map_apply hf hS, Measure.map_apply hf hS]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
  let F := (f ⁻¹' S).indicator (fun _ : HistoryMarked dependent E => (1 : ℝ))
  have hF : Measurable F := (measurable_const : Measurable (fun _ : HistoryMarked dependent E => (1 : ℝ))).indicator (hf hS)
  have hbound : ∀ h, |F h| ≤ 1 := by
    intro h
    by_cases hh : f h ∈ S <;> simp [F, hh]
  have hzero : ∀ j h, ∫ e, F (historyMarkedAppend dependent hsymm j (h, e)) * a e ∂π = 0 := by
    intro j h
    have hFi : ∀ h : HistoryMarked dependent E, F h = S.indicator (fun _ : X => (1 : ℝ)) (f h) := by
      intro h
      by_cases hh : f h ∈ S <;> simp [F, hh]
    simp_rw [hFi]
    exact hkill j h S hS
  have he := historyMarkedPrior_invariant_observable dependent hrefl hsymm Δ hΔ hlabels T B hT hB
    π a ha habound hsmall F hF 1 (by norm_num) hbound hzero t ht
  change (∫ h, (f ⁻¹' S).indicator (1 : HistoryMarked dependent E → ℝ) h
    ∂historyMarkedPrior dependent Δ t π a) =
      ∫ h, (f ⁻¹' S).indicator (1 : HistoryMarked dependent E → ℝ) h
        ∂historyMarkedReference dependent Δ π at he
  rw [integral_indicator_one (hf hS), integral_indicator_one (hf hS)] at he
  exact he

end NearlyMinimax
