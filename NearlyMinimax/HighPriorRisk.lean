module

public import NearlyMinimax.HighScoreTimeKernel
public import NearlyMinimax.PaperScorePath


@[expose] public section

/-! The source marked-history prior, its genuine normalized observation law,
and its observed posterior score imply the manuscript's path-risk comparison.
The analytical score assumptions are proved from the actual likelihood. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
variable {J : Type*} [Fintype J] [LinearOrder J]
attribute [local irreducible] highMarginalRealScore highRealSampleKernel historyMarkedPrior
  massPowerTilt massPowerNormalizer highRawDensityMass

theorem historyMarkedPrior_original_minimax_path_bound
    (dependent : J → J → Prop) (hrefl : ∀ j, dependent j j)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ)
    (ham : Measurable activation) (hact : ∫ e, activation e ∂π = 0)
    (Ba T : ℝ) (hBa : 0 ≤ Ba) (hT : 0 ≤ T) (hab : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ)^2))
    {d : ℕ} (C : ModelConstants d) (n : ℕ) (a v η aRaw bRaw M ε : ℝ)
    (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v-η^2*t) y)
    (hmass : ∀ t ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ t π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    (θ : ℝ → HistoryMarked dependent E → RegressionParameter d)
    (hθ : ∀ (t : ℝ) (ht : t ∈ Icc 0 T), ∀ ω, θ t ω =
      normalizedDensityTernaryParameter (p ω) (F ω) a (v-η^2*t) hF.of_uncurry_left
        ha.ne' (fun x y => (hq t ht ω x y).le))
    (hV : ∀ t ∈ Icc 0 T, v-η^2*t ∈ Icc C.varianceLower (effectiveVarianceUpper C))
    (bad : ℝ → Set (HistoryMarked dependent E))
    (hbad : ∀ t ∈ Icc 0 T, MeasurableSet (bad t))
    (hlegal : ∀ t ∈ Icc 0 T, ∀ ω ∉ bad t, Admissible C (θ t ω))
    (hbadmass : ∀ t ∈ Icc 0 T,
      (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
        (fun ω => highRawDensityMass (p ω)) n).real (bad t) ≤ ε)
    (hE : ∀ t ∈ Icc 0 T, Integrable
      (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
        (highHistoryLikelihoodDerivative dependent hsymm π activation n a (v-η^2*t) η p F z.1 z.2)^2 /
          highRawSampleLikelihood n a (v-η^2*t) (p z.1) (F z.1) z.2)
      ((historyMarkedPrior dependent Δ t π activation).prod (highSampleReference d n)))
    (hbudget : ∀ t ∈ Icc 0 T,
      (massPowerNormalizer (historyMarkedPrior dependent Δ t π activation)
        (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
          (highHistoryLikelihoodDerivative dependent hsymm π activation n a (v-η^2*t) η p F z.1 z.2)^2 /
            highRawSampleLikelihood n a (v-η^2*t) (p z.1) (F z.1) z.2
          ∂(historyMarkedPrior dependent Δ t π activation).prod (highSampleReference d n) ≤ M) :
    let P (t : ℝ) := (highRealSampleKernel n a (v-η^2*t) p F hp hF) ∘ₘ
      massPowerTilt (historyMarkedPrior dependent Δ t π activation)
        (fun ω => highRawDensityMass (p ω)) n
    let R (t : ℝ) := highMarginalRealScore dependent hsymm
      (historyMarkedPrior dependent Δ t π activation) π activation n a (v-η^2*t) η p F
    ENNReal.ofReal (η^4*T^2 /
      (2 + ∫ t in (0 : ℝ)..T, Real.sqrt (∫ z, (R t z)^2 ∂P t))^2 -
      (effectiveVarianceUpper C-C.varianceLower)^2*ε) ≤ minimaxRisk C n := by
  let ν (t : ℝ) := historyMarkedPrior dependent Δ t π activation
  let σ (t : ℝ) := massPowerTilt (ν t) (fun ω => highRawDensityMass (p ω)) n
  let L (t : ℝ) := highRealSampleKernel n a (v-η^2*t) p F hp hF
  let R (t : ℝ) := highMarginalRealScore dependent hsymm (ν t) π activation n a (v-η^2*t) η p F
  let _ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  have hai : Integrable activation π := Integrable.of_bound ham.aestronglyMeasurable Ba
    (Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using hab e)
  have hν (t : ℝ) (ht : t ∈ Icc 0 T) : IsProbabilityMeasure (ν t) := by
    have hs : t*Ba/historyReferenceRho Δ ≤ 1/(2+8*(Δ:ℝ)^2) :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hBa)
        (historyReferenceRho_pos Δ).le).trans hsmall
    exact historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels t Ba ht.1 hBa
      π activation hai hact hab hs
  have hσ (t : ℝ) (ht : t ∈ Icc 0 T) : IsProbabilityMeasure (σ t) := by
    let _ := hν t ht
    exact massPowerTilt_isProbability (ν t) _ (highRawDensityMass_joint_measurable p hp)
      n aRaw bRaw haRaw (fun ω => highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left
        aRaw bRaw haRaw (Eventually.of_forall (hraw ω)))
  have hL (t : ℝ) (ht : t ∈ Icc 0 T) : IsMarkovKernel (L t) :=
    highRealSampleKernel_markov n a (v-η^2*t) p F hp hF aRaw bRaw haRaw hraw ha.ne'
      (fun ω x y => (hq t ht ω x y).le)
  have hsample (t : ℝ) (ht : t ∈ Icc 0 T) (ω) : L t ω = sampleLaw (θ t ω) n := by
    rw [hθ t ht ω]
    exact highRealSampleKernel_eq_sampleLaw n a (v-η^2*t) p F hp hF aRaw bRaw haRaw hraw
      ha.ne' (fun ω x y => (hq t ht ω x y).le) ω
  have hvariance (t : ℝ) (ht : t ∈ Icc 0 T) (ω) : (θ t ω).variance = v-η^2*t := by
    rw [hθ t ht ω]
    rfl
  have hR : ∀ᵐ t ∂volume, t ∈ Icc 0 T → MemLp (R t) 2 (L t ∘ₘ σ t) :=
    Eventually.of_forall fun t ht => by
      let _ := hν t ht
      exact (highMarginalRealScore_memLp_energy dependent hsymm (ν t) π activation ham
        Ba hBa hab n a (v-η^2*t) η aRaw bRaw ha haRaw p F hp hF hraw (hq t ht) (hE t ht)).1
  have hc := historyMarkedPrior_dataScore_centered_ae dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation ham hact hab hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass
  have hB : 0 ≤ effectiveVarianceUpper C :=
    C.varianceLower_pos.le.trans (effective_variance_interval_nondegenerate C).le
  have hAC (S : BoundedEstimator C n) : AbsolutelyContinuousOnInterval
      (fun t => ∫ z, S.val.val z ∂(L t ∘ₘ σ t)) 0 T :=
    historyMarkedPrior_dataMean_absolutelyContinuous dependent hrefl hsymm Δ hΔ hlabels
      T Ba hBa π activation ham hact hab hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw
      (fun t ht ω x y => (hq t ht ω x y).le) hmass S.val.val S.val.property
      (effectiveVarianceUpper C) hB (fun z => by
        rw [abs_of_nonneg (C.varianceLower_pos.le.trans (S.property z).1)]
        exact (S.property z).2) hT
  have hd (S : BoundedEstimator C n) :=
    historyMarkedPrior_dataMean_score_hasDerivAt_ae dependent hrefl hsymm Δ hΔ hlabels
      T Ba hBa π activation ham hact hab hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass
      S.val.val S.val.property (effectiveVarianceUpper C) hB (fun z => by
        rw [abs_of_nonneg (C.varianceLower_pos.le.trans (S.property z).1)]
        exact (S.property z).2)
  have hi := highHistoryScore_sqrt_energy_intervalIntegrable dependent hsymm Δ π activation ham
    Ba hBa hab n a v η aRaw bRaw T M ha haRaw hT p F hp hF hν hraw hq hE hbudget
  have hh := paper_score_to_risk C σ L θ (fun t => v-η^2*t) R T ε hT hσ hL hsample hvariance
    hV bad hbad hlegal hbadmass hR hc hAC hd hi
  have he : ((v-η^2*T)-(v-η^2*0))^2 = η^4*T^2 := by ring
  dsimp only at hh ⊢
  rw [he] at hh
  exact hh

end NearlyMinimax
