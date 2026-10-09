module

public import NearlyMinimax.HighHistoryLikelihoodScore


@[expose] public section

/-! Genuine original observable derivative against the actual likelihood score. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedPrior_tiltedObservable_score_hasDerivAt (dependent : J → J → Prop)
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
    HasDerivAt (fun u => highTiltedObservableMean (historyMarkedPrior dependent Δ u π activation)
      n a (v - η ^ 2 * u) p F hp hF H)
      (∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
        highHistoryLikelihoodScore dependent hsymm π activation n a (v - η^2*t) η p F z.1 z.2 *
          H (encodeDesignResponse a z.2)
        ∂(massPowerTilt (historyMarkedPrior dependent Δ t π activation)
          (fun ω => highRawDensityMass (p ω)) n).compProd
          (highSampleIndexKernel n a (v - η^2*t) p F hp hF)) t := by
  have hq0 (u : ℝ) (hu : u ∈ Icc 0 T) (ω : HistoryMarked dependent E) (x : Covariate d) (y : Fin 3) :=
    (hq u hu ω x y).le
  have hd := historyMarkedPrior_tiltedObservable_hasDerivAt dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF
    hraw hq0 hmass H hH B hB hHb t ht htT
  have hint : Integrable activation π := by
    apply Integrable.of_bound hactivation.aestronglyMeasurable Ba
    exact Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e
  have hs : t * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ)^2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htT.le hBa)
      (historyReferenceRho_pos Δ).le).trans hsmall
  let _ := historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels t Ba ht.le hBa π
    activation hint hcenter habound hs
  have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  have he := massPowerTilt_highHistoryLikelihoodScore_integral dependent hsymm
    (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η^2*t) η
    p F hp hF aRaw bRaw haRaw hraw (hq t ⟨ht.le,htT.le⟩) H
  have hi := highHistoryLikelihoodDerivative_observable π dependent hsymm
    (historyMarkedPrior dependent Δ t π activation) activation hactivation Ba hBa habound
    n a (v - η^2*t) η |bRaw| B (abs_nonneg _) hB ha p F hp hF hpb
    (hq0 t ⟨ht.le,htT.le⟩) H hH hHb
  rw [hi, massPowerNormalizer_eq_of_massLaw _ _ _ (highRawDensityMass_joint_measurable p hp)
    n (hmass t ⟨ht.le,htT.le⟩)] at he
  rw [he]
  exact hd

end NearlyMinimax
