module

public import NearlyMinimax.HighMarginalScoreDerivative


@[expose] public section

/-! Genuine observed-data score centering follows from the proved derivative
identity and actual probability normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedPrior_dataScore_centered (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T Ba : ℝ) (hBa : 0 ≤ Ba)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (hactivation : Measurable activation)
    (hcenter : ∫ e, activation e ∂π = 0) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    {d : ℕ} (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    (t : ℝ) (ht : 0 < t) (htT : t < T) :
    (∫ z, highMarginalRealScore dependent hsymm
      (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η^2*t) η p F z
      ∂(highRealSampleKernel n a (v - η^2*t) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
          (fun ω => highRawDensityMass (p ω)) n)) = 0 := by
  have hd := historyMarkedPrior_dataMean_score_hasDerivAt dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF
    hraw hq hmass (fun _ => 1) measurable_const 1 (by norm_num) (fun _ => by norm_num) t ht htT
  have he : (fun u => ∫ z, (1 : ℝ) ∂(highRealSampleKernel n a (v - η^2*u) p F hp hF) ∘ₘ
      (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
        (fun ω => highRawDensityMass (p ω)) n)) =ᶠ[𝓝 t] (fun _ => 1) := by
    filter_upwards [Ioo_mem_nhds ht htT] with u hu
    have hint : Integrable activation π := by
      apply Integrable.of_bound hactivation.aestronglyMeasurable Ba
      exact Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e
    have hs : u * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ)^2) :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hBa)
        (historyReferenceRho_pos Δ).le).trans hsmall
    let _ := historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels u Ba hu.1.le hBa π
      activation hint hcenter habound hs
    have hm := highRawDensityMass_joint_measurable p hp
    have hb (ω) : aRaw ≤ highRawDensityMass (p ω) ∧ highRawDensityMass (p ω) ≤ bRaw :=
      highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
        (Eventually.of_forall (hraw ω))
    let _ := massPowerTilt_isProbability (historyMarkedPrior dependent Δ u π activation)
      _ hm n aRaw bRaw haRaw hb
    let _ := highRealSampleKernel_markov n a (v - η^2*u) p F hp hF aRaw bRaw haRaw hraw ha.ne'
      (fun ω x y => (hq u ⟨hu.1.le,hu.2.le⟩ ω x y).le)
    simp
  have hc := (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq he
  simpa only [one_mul] using hd.unique hc

theorem historyMarkedPrior_dataScore_centered_ae (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T Ba : ℝ) (hBa : 0 ≤ Ba)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (hactivation : Measurable activation)
    (hcenter : ∫ e, activation e ∂π = 0) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    {d : ℕ} (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc 0 T →
      (∫ z, highMarginalRealScore dependent hsymm
        (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η^2*t) η p F z
        ∂(highRealSampleKernel n a (v - η^2*t) p F hp hF) ∘ₘ
          (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
            (fun ω => highRawDensityMass (p ω)) n)) = 0 := by
  have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (0 : ℝ) := by simp [ae_iff]
  have hT : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ T := by simp [ae_iff]
  filter_upwards [h0, hT] with t ht0 htT
  intro ht
  exact historyMarkedPrior_dataScore_centered dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF
    hraw hq hmass t (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (lt_of_le_of_ne ht.2 htT)

end NearlyMinimax
