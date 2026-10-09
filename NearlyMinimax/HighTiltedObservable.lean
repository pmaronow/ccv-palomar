module

public import NearlyMinimax.HighPriorObservableDerivative
public import NearlyMinimax.HighRawObservableRegularity


@[expose] public section

/-! Actual mass-tilted original data means: normalization cancellation,
variance heat and the genuine marked append generator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def highTiltedObservableMean {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (ν : Measure Ω) (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (H : (Fin n → Observation d) → ℝ) : ℝ :=
  ∫ ω, ∫ z, H z ∂highRealSampleKernel n a V p F hp hF ω
    ∂massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n

variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedPrior_tiltedObservable_eq_raw (dependent : J → J → Prop)
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
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    highTiltedObservableMean (historyMarkedPrior dependent Δ t π activation)
      n a (v - η ^ 2 * t) p F hp hF H =
      (massPowerNormalizer (historyMarkedPrior dependent Δ 0 π activation)
        (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ ω, highRawObservable n a (v - η ^ 2 * t) (p ω) (F ω) H
          ∂historyMarkedPrior dependent Δ t π activation := by
  have hint : Integrable activation π := by
    apply Integrable.of_bound hactivation.aestronglyMeasurable Ba
    exact Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e
  have hs : t * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hBa)
      (historyReferenceRho_pos Δ).le).trans hsmall
  let _ := historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels t Ba ht.1 hBa π
    activation hint hcenter habound hs
  rw [highTiltedObservableMean, massPowerTilt_highReal_observable_mean
    (historyMarkedPrior dependent Δ t π activation) n a (v - η ^ 2 * t) p F hp hF
      aRaw bRaw haRaw hraw ha.ne' (hq t ht) H hH B hB hHb,
    massPowerNormalizer_eq_of_massLaw _ _ _ (highRawDensityMass_joint_measurable p hp) n (hmass t ht)]

theorem historyMarkedPrior_tiltedObservable_hasDerivAt (dependent : J → J → Prop)
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
    (t : ℝ) (ht : 0 < t) (htT : t < T) :
    HasDerivAt (fun u => highTiltedObservableMean (historyMarkedPrior dependent Δ u π activation)
      n a (v - η ^ 2 * u) p F hp hF H)
      ((massPowerNormalizer (historyMarkedPrior dependent Δ 0 π activation)
        (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ((-η ^ 2 * ∫ ω, highRawObservableVarianceDerivative n a (v - η ^ 2 * t) (p ω) (F ω) H
          ∂historyMarkedPrior dependent Δ t π activation) +
          historyMarkedPriorGenerator dependent hsymm Δ t π activation
            (fun ω => highRawObservable n a (v - η ^ 2 * t) (p ω) (F ω) H))) t := by
  have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  have hd := historyMarkedPrior_rawObservable_hasDerivAt dependent hrefl hsymm Δ hΔ hlabels
    T Ba t ht htT hBa π activation hactivation habound hsmall n a v η |bRaw| B ha
    (abs_nonneg _) hB p F hp hF hpb (fun u hu => hq u ⟨hu.1.le, hu.2.le⟩) H hH hHb
  have hc := hd.const_mul ((massPowerNormalizer (historyMarkedPrior dependent Δ 0 π activation)
    (fun ω => highRawDensityMass (p ω)) n)⁻¹)
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht htT] with u hu
  exact historyMarkedPrior_tiltedObservable_eq_raw dependent hrefl hsymm Δ hΔ hlabels T Ba hBa
    π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass
    H hH B hB hHb u ⟨hu.1.le, hu.2.le⟩

theorem historyMarkedPrior_tiltedObservable_exists_lipschitz (dependent : J → J → Prop)
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
    : ∃ K : NNReal, LipschitzOnWith K
      (fun u => highTiltedObservableMean (historyMarkedPrior dependent Δ u π activation)
        n a (v - η ^ 2 * u) p F hp hF H) (Icc 0 T) := by
  have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  obtain ⟨K, hK⟩ := historyMarkedPrior_rawObservable_exists_lipschitz dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation hactivation habound hsmall n a v η |bRaw| B ha (abs_nonneg _) hB
    p F hp hF hpb hq H hH hHb
  let c : ℝ := (massPowerNormalizer (historyMarkedPrior dependent Δ 0 π activation)
    (fun ω => highRawDensityMass (p ω)) n)⁻¹
  refine ⟨⟨|c| * K, mul_nonneg (abs_nonneg _) K.coe_nonneg⟩, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu w hw
  rw [historyMarkedPrior_tiltedObservable_eq_raw dependent hrefl hsymm Δ hΔ hlabels T Ba hBa
    π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass
    H hH B hB hHb u hu,
    historyMarkedPrior_tiltedObservable_eq_raw dependent hrefl hsymm Δ hΔ hlabels T Ba hBa
    π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass
    H hH B hB hHb w hw]
  change dist (c * _) (c * _) ≤ |c| * (K : ℝ) * dist u w
  rw [Real.dist_eq, ← mul_sub, abs_mul]
  have hh := hK.dist_le_mul u hu w hw
  rw [Real.dist_eq] at hh
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (abs_nonneg c)

theorem historyMarkedPrior_tiltedObservable_absolutelyContinuous (dependent : J → J → Prop)
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
      (fun u => highTiltedObservableMean (historyMarkedPrior dependent Δ u π activation)
        n a (v - η ^ 2 * u) p F hp hF H) 0 T := by
  obtain ⟨K, hK⟩ := historyMarkedPrior_tiltedObservable_exists_lipschitz dependent hrefl hsymm
    Δ hΔ hlabels T Ba hBa π activation hactivation hcenter habound hsmall
    n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass H hH B hB hHb
  rw [← uIcc_of_le hT] at hK
  exact hK.absolutelyContinuousOnInterval

end NearlyMinimax
