module

public import NearlyMinimax.HighTimeLikelihood


@[expose] public section

/-! Actual time-varying source-prior averages and posterior scores are jointly Borel. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedPrior_integral_joint_measurable {E Z : Type*}
    [MeasurableSpace E] [MeasurableSpace Z]
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation)
    (G : ℝ × (HistoryMarked dependent E × Z) → ℝ) (hG : Measurable G) :
    Measurable (fun z : ℝ × Z =>
      ∫ ω, G (z.1,(ω,z.2)) ∂historyMarkedPrior dependent Δ z.1 π activation) := by
  let f : (ℝ × Z) × HistoryMarked dependent E → ℝ := fun z =>
    (ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) z.1.1 activation z.2)).toReal *
      G (z.1.1,(z.2,z.1.2))
  have hm : Measurable f :=
    (((historyMarkedDensity_joint_measurable dependent (historyReferenceRho Δ) activation ham).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal.ennreal_toReal).mul
      (hG.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hi : Measurable (fun z : ℝ × Z =>
      ∫ ω, f (z,ω) ∂historyMarkedReference dependent Δ π) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  have he : (fun z : ℝ × Z => ∫ ω, G (z.1,(ω,z.2))
      ∂historyMarkedPrior dependent Δ z.1 π activation) =
      fun z => ∫ ω, f (z,ω) ∂historyMarkedReference dependent Δ π := by
    funext z
    rw [historyMarkedPrior_eq_withDensity dependent Δ z.1 π activation ham,
      integral_withDensity_eq_integral_toReal_smul
        (historyMarkedDensity_measurable dependent _ z.1 activation ham).ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    rfl
  rw [he]
  exact hi

theorem highMarginalRawLikelihood_time_measurable {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : ℝ × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highMarginalRawLikelihood (historyMarkedPrior dependent Δ z.1 π activation)
        n a (v-η^2*z.1) p F z.2) :=
  historyMarkedPrior_integral_joint_measurable dependent Δ π activation ham _
    (highRawSampleLikelihood_time_measurable n a v η p F hp hF)

theorem highMarginalIndexScore_time_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (π : Measure E) [SFinite π] [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : ℝ × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highMarginalIndexScore dependent hsymm (historyMarkedPrior dependent Δ z.1 π activation)
        π activation n a (v-η^2*z.1) η p F z.2) :=
  (historyMarkedPrior_integral_joint_measurable dependent Δ π activation ham _
    (highHistoryLikelihoodDerivative_time_measurable dependent hsymm π activation ham n a v η p F hp hF)).div
    (highMarginalRawLikelihood_time_measurable dependent Δ π activation ham n a v η p F hp hF)

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] highMarginalIndexScore highMarginalRawLikelihood
  historyMarkedPrior highRawDensityMass massPowerNormalizer

theorem highMarginalRealScore_time_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (π : Measure E) [SFinite π] [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : ℝ × (Fin n → Observation d) =>
      highMarginalRealScore dependent hsymm (historyMarkedPrior dependent Δ z.1 π activation)
        π activation n a (v-η^2*z.1) η p F z.2) := by
  unfold highMarginalRealScore
  change Measurable ((fun z : ℝ × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
    highMarginalIndexScore dependent hsymm (historyMarkedPrior dependent Δ z.1 π activation)
      π activation n a (v-η^2*z.1) η p F z.2) ∘
    (fun z : ℝ × (Fin n → Observation d) => (z.1, decodeDesignResponse a z.2)))
  exact (highMarginalIndexScore_time_measurable dependent hsymm Δ π activation ham n a v η p F hp hF).comp
    (show Measurable (fun z : ℝ × (Fin n → Observation d) =>
      (z.1, decodeDesignResponse a z.2)) from
      measurable_fst.prodMk ((decodeDesignResponse_measurable a).comp measurable_snd))

theorem highMassPowerNormalizer_time_measurable {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ)
    (p : HistoryMarked dependent E → Covariate d → ℝ) (hp : Measurable (Function.uncurry p)) :
    Measurable (fun t => massPowerNormalizer (historyMarkedPrior dependent Δ t π activation)
      (fun ω => highRawDensityMass (p ω)) n) := by
  unfold massPowerNormalizer
  have hG : Measurable (fun z : ℝ × (HistoryMarked dependent E × Unit) =>
      highRawDensityMass (p z.2.1)^n) :=
    ((highRawDensityMass_joint_measurable p hp).pow_const n).comp (measurable_fst.comp measurable_snd)
  have hi : Measurable (fun z : ℝ × Unit =>
      ∫ ω, highRawDensityMass (p ω)^n ∂historyMarkedPrior dependent Δ z.1 π activation) :=
    historyMarkedPrior_integral_joint_measurable dependent Δ π activation ham _ hG
  exact hi.comp (show Measurable (fun t : ℝ => (t, ())) from
    measurable_id.prodMk measurable_const)

end NearlyMinimax
