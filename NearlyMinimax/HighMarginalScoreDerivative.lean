module

public import NearlyMinimax.HighTiltedDataMean


@[expose] public section

/-! Genuine observed-data score derivative for the actual high experiment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedPrior_dataMean_score_hasDerivAt (dependent : J → J → Prop)
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
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B)
    (t : ℝ) (ht : 0 < t) (htT : t < T) :
    HasDerivAt (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) p F hp hF) ∘ₘ
      (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
        (fun ω => highRawDensityMass (p ω)) n))
      (∫ z, H z * highMarginalRealScore dependent hsymm
        (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η^2*t) η p F z
        ∂(highRealSampleKernel n a (v - η^2*t) p F hp hF) ∘ₘ
          (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
            (fun ω => highRawDensityMass (p ω)) n)) t := by
  have hq0 (u : ℝ) (hu : u ∈ Icc 0 T) (ω : HistoryMarked dependent E) (x : Covariate d) (y : Fin 3) :=
    (hq u hu ω x y).le
  have hint : Integrable activation π := by
    apply Integrable.of_bound hactivation.aestronglyMeasurable Ba
    exact Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e
  have hprob (u : ℝ) (hu : u ∈ Icc 0 T) :
      IsProbabilityMeasure (historyMarkedPrior dependent Δ u π activation) := by
    have hs : u * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ)^2) :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hBa)
        (historyReferenceRho_pos Δ).le).trans hsmall
    exact historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels u Ba hu.1 hBa π
      activation hint hcenter habound hs
  let _ := hprob t ⟨ht.le, htT.le⟩
  have hd := historyMarkedPrior_tiltedObservable_hasDerivAt dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF
    hraw hq0 hmass H hH B hB hHb t ht htT
  have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  have he := highMarginalRealScore_integral dependent hsymm
    (historyMarkedPrior dependent Δ t π activation) π activation hactivation Ba hBa habound
    n a (v - η^2*t) η aRaw bRaw B ha haRaw hB p F hp hF hraw
    (hq t ⟨ht.le,htT.le⟩) H hH hHb
  have hi := highHistoryLikelihoodDerivative_observable π dependent hsymm
    (historyMarkedPrior dependent Δ t π activation) activation hactivation Ba hBa habound
    n a (v - η^2*t) η |bRaw| B (abs_nonneg _) hB ha p F hp hF hpb
    (hq0 t ⟨ht.le,htT.le⟩) H hH hHb
  rw [hi, massPowerNormalizer_eq_of_massLaw _ _ _ (highRawDensityMass_joint_measurable p hp)
    n (hmass t ⟨ht.le,htT.le⟩)] at he
  rw [he]
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht htT] with u hu
  let _ := hprob u ⟨hu.1.le,hu.2.le⟩
  exact (highTiltedObservableMean_eq_dataMean (historyMarkedPrior dependent Δ u π activation)
    n a (v - η^2*u) aRaw bRaw B ha.ne' haRaw hB p F hp hF hraw
    (hq0 u ⟨hu.1.le,hu.2.le⟩) H hH hHb).symm

theorem historyMarkedPrior_dataMean_absolutelyContinuous (dependent : J → J → Prop)
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
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B)
    (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval
      (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (fun ω => highRawDensityMass (p ω)) n)) 0 T := by
  obtain ⟨K, hK⟩ := historyMarkedPrior_tiltedObservable_exists_lipschitz dependent hrefl hsymm
    Δ hΔ hlabels T Ba hBa π activation hactivation hcenter habound hsmall
    n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass H hH B hB hHb
  have hint : Integrable activation π := by
    apply Integrable.of_bound hactivation.aestronglyMeasurable Ba
    exact Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e
  have he (u : ℝ) (hu : u ∈ Icc 0 T) :
      highTiltedObservableMean (historyMarkedPrior dependent Δ u π activation)
        n a (v - η^2*u) p F hp hF H =
      ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (fun ω => highRawDensityMass (p ω)) n) := by
    have hs : u * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ)^2) :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hBa)
        (historyReferenceRho_pos Δ).le).trans hsmall
    let _ := historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels u Ba hu.1 hBa π
      activation hint hcenter habound hs
    exact highTiltedObservableMean_eq_dataMean (historyMarkedPrior dependent Δ u π activation)
      n a (v - η^2*u) aRaw bRaw B ha.ne' haRaw hB p F hp hF hraw (hq u hu) H hH hHb
  have hKd : LipschitzOnWith K
      (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (fun ω => highRawDensityMass (p ω)) n)) (Icc 0 T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu w hw
    rw [← he u hu, ← he w hw]
    exact hK.dist_le_mul u hu w hw
  rw [← uIcc_of_le hT] at hKd
  exact hKd.absolutelyContinuousOnInterval

theorem historyMarkedPrior_dataMean_score_hasDerivAt_ae (dependent : J → J → Prop)
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
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B)
    : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc 0 T →
      HasDerivAt (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η^2*u) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (fun ω => highRawDensityMass (p ω)) n))
        (∫ z, H z * highMarginalRealScore dependent hsymm
          (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η^2*t) η p F z
          ∂(highRealSampleKernel n a (v - η^2*t) p F hp hF) ∘ₘ
            (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
              (fun ω => highRawDensityMass (p ω)) n)) t := by
  have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (0 : ℝ) := by simp [ae_iff]
  have hT : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ T := by simp [ae_iff]
  filter_upwards [h0, hT] with t ht0 htT
  intro ht
  exact historyMarkedPrior_dataMean_score_hasDerivAt dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF
    hraw hq hmass H hH B hB hHb t (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (lt_of_le_of_ne ht.2 htT)

end NearlyMinimax
