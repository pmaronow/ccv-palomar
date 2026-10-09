module

public import NearlyMinimax.HighMarginalScoreEnergy
public import NearlyMinimax.HighMarginalScoreCenter


@[expose] public section

/-! Genuine joint time measurability of source priors and likelihood scores. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem historyMarkedDensity_joint_measurable {E : Type*} [MeasurableSpace E]
    (dependent : J → J → Prop) (ρ : ℝ) (activation : E → ℝ) (ham : Measurable activation) :
    Measurable (fun z : ℝ × HistoryMarked dependent E =>
      historyMarkedDensity dependent ρ z.1 activation z.2) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ) (ω : HistoryMarked dependent E) => historyMarkedDensity dependent ρ t activation ω)
  · intro ω
    exact continuous_iff_continuousAt.mpr (fun t =>
      (historyMarkedDensity_hasDerivAt dependent ρ t activation ω).continuousAt)
  · exact fun t => historyMarkedDensity_measurable dependent ρ t activation ham

theorem highRawSampleLikelihood_time_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (n : ℕ) (a v η : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : ℝ × (Ω × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highRawSampleLikelihood n a (v-η^2*z.1) (p z.2.1) (F z.2.1) z.2.2) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ) (z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highRawSampleLikelihood n a (v-η^2*t) (p z.1) (F z.1) z.2)
  · intro z
    exact continuous_iff_continuousAt.mpr (fun t =>
      (highRawSampleLikelihood_hasDerivAt_path n a v η t (p z.1) (F z.1) z.2).continuousAt)
  · exact fun t => highRawSampleLikelihood_joint_measurable n a (v-η^2*t) p F hp hF

theorem ternaryMass_continuous_variance (a f : ℝ) (y : Fin 3) :
    Continuous (fun V => ternaryMass a f V y) := by
  fin_cases y <;> simp only [ternaryMass, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  all_goals fun_prop

theorem highRawSampleVarianceDerivative_time_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (n : ℕ) (a v η : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : ℝ × (Ω × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highRawSampleVarianceDerivative n a (v-η^2*z.1) (p z.2.1) (F z.2.1) z.2.2) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ) (z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highRawSampleVarianceDerivative n a (v-η^2*t) (p z.1) (F z.1) z.2)
  · intro z
    unfold highRawSampleVarianceDerivative
    apply Continuous.mul continuous_const
    apply continuous_finset_sum
    intro i _
    apply Continuous.mul _ continuous_const
    apply continuous_finset_prod
    intro j _
    exact (ternaryMass_continuous_variance a _ _).comp (by fun_prop)
  · exact fun t => highRawSampleVarianceDerivative_joint_measurable n a (v-η^2*t) p F hp hF

theorem highAppendLikelihoodAction_time_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (ham : Measurable activation)
    (n : ℕ) (a v η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) (j : J) :
    Measurable (fun z : ℝ × (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highAppendLikelihoodAction dependent hsymm π activation n a (v-η^2*z.1) p F j z.2.1 z.2.2) := by
  have hc : Measurable (fun z :
      (ℝ × (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)))) × E =>
      (z.1.1,(historyMarkedAppend dependent hsymm j (z.1.2.1,z.2),z.1.2.2))) :=
    (measurable_fst.comp measurable_fst).prodMk
      (((historyMarkedAppend_measurable dependent hsymm j).comp
        ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have hj : Measurable (fun z :
      (ℝ × (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)))) × E =>
      activation z.2 * highRawSampleLikelihood n a (v-η^2*z.1.1)
        (p (historyMarkedAppend dependent hsymm j (z.1.2.1,z.2)))
        (F (historyMarkedAppend dependent hsymm j (z.1.2.1,z.2))) z.1.2.2) :=
    (ham.comp measurable_snd).mul
      ((highRawSampleLikelihood_time_measurable n a v η p F hp hF).comp hc)
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

theorem highHistoryLikelihoodDerivative_time_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (ham : Measurable activation)
    (n : ℕ) (a v η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : ℝ × (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highHistoryLikelihoodDerivative dependent hsymm π activation n a (v-η^2*z.1) η p F z.2.1 z.2.2) := by
  exact (Finset.measurable_sum _ (fun j _ =>
    highAppendLikelihoodAction_time_measurable dependent hsymm π activation ham n a v η p F hp hF j)).sub
      ((highRawSampleVarianceDerivative_time_measurable n a v η p F hp hF).const_mul (η^2))

end NearlyMinimax
