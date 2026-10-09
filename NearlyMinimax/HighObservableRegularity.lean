module

public import NearlyMinimax.HighObservableProductRule
public import NearlyMinimax.HistoryExpectationRegularity


@[expose] public section

/-! Endpoint regularity of genuine time-dependent marked-prior observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedPrior_variable_observable_lipschitz (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T B : ℝ) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (G : ℝ → HistoryMarked dependent E → ℝ) (hGM : ∀ u, Measurable (G u))
    (M : ℝ) (hM : 0 ≤ M) (hGb : ∀ u ∈ Icc 0 T, ∀ h, |G u h| ≤ M)
    (K : NNReal) (hGlip : ∀ h, LipschitzOnWith K (fun u => G u h) (Icc 0 T)) :
    LipschitzOnWith
      ⟨(K : ℝ) * (3 / 2 : ℝ) ^ Fintype.card J +
        M * ((historyReferenceRho Δ)⁻¹ * (Fintype.card J : ℝ) * B * (3 / 2 : ℝ) ^ Fintype.card J),
        by have hρ := historyReferenceRho_pos Δ; positivity⟩
      (fun u => ∫ h, G u h ∂historyMarkedPrior dependent Δ u π a) (Icc 0 T) := by
  let μ := historyMarkedReference dependent Δ π
  let _ : IsProbabilityMeasure μ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  let ρ := historyReferenceRho Δ
  let C : ℝ := (3 / 2 : ℝ) ^ Fintype.card J
  let D : ℝ := ρ⁻¹ * (Fintype.card J : ℝ) * B * C
  have hρ : 0 < ρ := historyReferenceRho_pos Δ
  have hC : 0 ≤ C := by positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hs (u : ℝ) (hu : u ∈ Icc 0 T) : u * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hB) hρ.le).trans hsmall
  have hφ (u : ℝ) (hu : u ∈ Icc 0 T) (h : HistoryMarked dependent E) :
      ‖historyMarkedDensity dependent ρ u a h‖ ≤ C := by
    have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ u B hρ hu.1 hB a habound (hs u hu) h
    rw [Real.norm_eq_abs, abs_of_nonneg ((by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1)]
    exact hb.2
  let H : ℝ → HistoryMarked dependent E → ℝ := fun u h => G u h * historyMarkedDensity dependent ρ u a h
  have hi (u : ℝ) (hu : u ∈ Icc 0 T) : Integrable (H u) μ := by
    apply Integrable.of_bound ((hGM u).mul (historyMarkedDensity_measurable dependent ρ u a ha)).aestronglyMeasurable (M * C)
    exact Eventually.of_forall fun h => by
      rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hGb u hu h) (hφ u hu h) (norm_nonneg _) hM
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rw [historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels u B hu.1 hB π a ha habound (hs u hu),
    historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels v B hv.1 hB π a ha habound (hs v hv)]
  change dist (∫ h, H u h ∂μ) (∫ h, H v h ∂μ) ≤ ((K : ℝ) * C + M * D) * dist u v
  rw [dist_eq_norm, ← integral_sub (hi u hu) (hi v hv)]
  have hb : ∀ᵐ h ∂μ, ‖H u h - H v h‖ ≤ ((K : ℝ) * C + M * D) * dist u v := by
    apply Eventually.of_forall
    intro h
    have hGdiff := (hGlip h).dist_le_mul u hu v hv
    rw [dist_eq_norm] at hGdiff
    have hφdiff := (historyMarkedDensity_lipschitzOn dependent hrefl hsymm Δ hlabels ρ T B hρ hB a habound hsmall h).dist_le_mul u hu v hv
    rw [dist_eq_norm] at hφdiff
    have he : H u h - H v h = (G u h - G v h) * historyMarkedDensity dependent ρ u a h +
      G v h * (historyMarkedDensity dependent ρ u a h - historyMarkedDensity dependent ρ v a h) := by dsimp [H]; ring
    rw [he]
    calc
      _ ≤ ‖(G u h - G v h) * historyMarkedDensity dependent ρ u a h‖ +
          ‖G v h * (historyMarkedDensity dependent ρ u a h - historyMarkedDensity dependent ρ v a h)‖ := norm_add_le _ _
      _ ≤ ((K : ℝ) * dist u v) * C + M * (D * dist u v) := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul hGdiff (hφ u hu h) (norm_nonneg _) (by positivity))
          (mul_le_mul (by simpa only [Real.norm_eq_abs] using hGb v hv h) hφdiff (norm_nonneg _) hM)
      _ = _ := by ring
  simpa using norm_integral_le_of_norm_le_const hb

theorem historyMarkedPrior_variable_observable_absolutelyContinuous (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (G : ℝ → HistoryMarked dependent E → ℝ) (hGM : ∀ u, Measurable (G u))
    (M : ℝ) (hM : 0 ≤ M) (hGb : ∀ u ∈ Icc 0 T, ∀ h, |G u h| ≤ M)
    (K : NNReal) (hGlip : ∀ h, LipschitzOnWith K (fun u => G u h) (Icc 0 T)) :
    AbsolutelyContinuousOnInterval
      (fun u => ∫ h, G u h ∂historyMarkedPrior dependent Δ u π a) 0 T := by
  have hl := historyMarkedPrior_variable_observable_lipschitz dependent hrefl hsymm Δ hΔ hlabels
    T B hB π a ha habound hsmall G hGM M hM hGb K hGlip
  rw [← uIcc_of_le hT] at hl
  exact hl.absolutelyContinuousOnInterval

end NearlyMinimax
