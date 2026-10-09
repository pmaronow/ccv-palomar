module

public import NearlyMinimax.HighTiltedObservable


@[expose] public section

/-! The genuine append likelihood action and its Fubini observable bridge. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

/-- Activation-weighted raw likelihood after the actual canonical marked append. -/
def highAppendLikelihoodAction {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) (activation : E → ℝ) (n : ℕ) (a V : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ) (j : J)
    (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  ∫ e, activation e * highRawSampleLikelihood n a V
    (p (historyMarkedAppend dependent hsymm j (ω,e)))
    (F (historyMarkedAppend dependent hsymm j (ω,e))) z ∂π

theorem highAppendLikelihoodAction_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (ha : Measurable activation) (n : ℕ) (a V : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) (j : J) :
    Measurable (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2) := by
  have hcoord : Measurable (fun z :
      (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))) × E =>
      (historyMarkedAppend dependent hsymm j (z.1.1,z.2),z.1.2)) :=
    ((historyMarkedAppend_measurable dependent hsymm j).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst)
  have hj : Measurable (fun z :
      (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))) × E =>
      activation z.2 * highRawSampleLikelihood n a V
        (p (historyMarkedAppend dependent hsymm j (z.1.1,z.2)))
        (F (historyMarkedAppend dependent hsymm j (z.1.1,z.2))) z.1.2) :=
    (ha.comp measurable_snd).mul
      ((highRawSampleLikelihood_joint_measurable n a V p F hp hF).comp hcoord)
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

theorem highAppendLikelihoodAction_abs_le {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (activation : E → ℝ) (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V P : ℝ) (hP : 0 ≤ P) (ha : a ≠ 0)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (j : J) (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    |highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z| ≤ Ba * P^n := by
  rw [highAppendLikelihoodAction, ← Real.norm_eq_abs]
  have hb : ∀ e, ‖activation e * highRawSampleLikelihood n a V
      (p (historyMarkedAppend dependent hsymm j (ω,e)))
      (F (historyMarkedAppend dependent hsymm j (ω,e))) z‖ ≤ Ba * P^n := by
    intro e
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (habound e) (highRawSampleLikelihood_abs_le n a V P hP
      (p (historyMarkedAppend dependent hsymm j (ω,e)))
      (F (historyMarkedAppend dependent hsymm j (ω,e)))
      (hp _) ha (hq _) z) (abs_nonneg _) hBa
  simpa using norm_integral_le_of_norm_le_const (μ := π) (Eventually.of_forall hb)


/-- Fubini converts the true append action on a data observable into the
actual append likelihood action; integrability follows from the source bounds. -/
theorem highAppendLikelihoodAction_observable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] (π : Measure E) [IsProbabilityMeasure π] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V P B : ℝ) (hP : 0 ≤ P) (hB : 0 ≤ B) (ha : a ≠ 0)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpb : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B)
    (j : J) (ω : HistoryMarked dependent E) :
    (∫ e, activation e * highRawObservable n a V
        (p (historyMarkedAppend dependent hsymm j (ω,e)))
        (F (historyMarkedAppend dependent hsymm j (ω,e))) H ∂π) =
      ∫ z, H (encodeDesignResponse a z) *
        highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z
          ∂highSampleReference d n := by
  have hcoord : Measurable (fun z : E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      (historyMarkedAppend dependent hsymm j (ω,z.1),z.2)) :=
    ((historyMarkedAppend_measurable dependent hsymm j).comp
      (measurable_const.prodMk measurable_fst)).prodMk measurable_snd
  have hM : Measurable (fun z : E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      activation z.1 * (H (encodeDesignResponse a z.2) * highRawSampleLikelihood n a V
        (p (historyMarkedAppend dependent hsymm j (ω,z.1)))
        (F (historyMarkedAppend dependent hsymm j (ω,z.1))) z.2)) :=
    (ham.comp measurable_fst).mul
      (((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
        ((highRawSampleLikelihood_joint_measurable n a V p F hp hF).comp hcoord))
  have hi : Integrable (fun z : E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      activation z.1 * (H (encodeDesignResponse a z.2) * highRawSampleLikelihood n a V
        (p (historyMarkedAppend dependent hsymm j (ω,z.1)))
        (F (historyMarkedAppend dependent hsymm j (ω,z.1))) z.2))
      (π.prod (highSampleReference d n)) := by
    apply Integrable.of_bound hM.aestronglyMeasurable (Ba * (B * P^n))
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (habound _) (mul_le_mul (hHb _) (highRawSampleLikelihood_abs_le n a V P hP
        _ _ (hpb _) ha (hq _) z.2) (abs_nonneg _) hB) (by positivity) hBa
  calc
    _ = ∫ e, ∫ z, activation e * (H (encodeDesignResponse a z) * highRawSampleLikelihood n a V
        (p (historyMarkedAppend dependent hsymm j (ω,e)))
        (F (historyMarkedAppend dependent hsymm j (ω,e))) z) ∂highSampleReference d n ∂π := by
      simp_rw [highRawObservable, integral_const_mul]
    _ = ∫ z, ∫ e, activation e * (H (encodeDesignResponse a z) * highRawSampleLikelihood n a V
        (p (historyMarkedAppend dependent hsymm j (ω,e)))
        (F (historyMarkedAppend dependent hsymm j (ω,e))) z) ∂π ∂highSampleReference d n :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only
        rw [highAppendLikelihoodAction, ← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun e => by ring

/-- The actual prior/product-mark append integral is the raw likelihood
append action tested against the data observable. -/
theorem highAppendLikelihoodAction_prior_observable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] (π : Measure E) [IsProbabilityMeasure π] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V P B : ℝ) (hP : 0 ≤ P) (hB : 0 ≤ B) (ha : a ≠ 0)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpb : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B)
    (j : J) :
    (∫ z : HistoryMarked dependent E × E, highRawObservable n a V
        (p (historyMarkedAppend dependent hsymm j z))
        (F (historyMarkedAppend dependent hsymm j z)) H * activation z.2 ∂ν.prod π) =
      ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
        H (encodeDesignResponse a z.2) *
          highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2
            ∂ν.prod (highSampleReference d n) := by
  have hg := (highRawObservable_measurable n a V p F hp hF H hH).comp
    (historyMarkedAppend_measurable dependent hsymm j)
  have hi : Integrable (fun z : HistoryMarked dependent E × E => highRawObservable n a V
      (p (historyMarkedAppend dependent hsymm j z))
      (F (historyMarkedAppend dependent hsymm j z)) H * activation z.2) (ν.prod π) := by
    apply Integrable.of_bound (hg.mul (ham.comp measurable_snd)).aestronglyMeasurable
      ((B * P^n * (highSampleReference d n).real univ) * Ba)
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply, Function.comp_apply, abs_mul]
      exact mul_le_mul (highRawObservable_abs_le n a V P B hP hB _ _ (hpb _) ha (hq _) H hHb)
        (habound _) (abs_nonneg _) (by positivity)
  have hi' : Integrable (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      H (encodeDesignResponse a z.2) *
        highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2)
      (ν.prod (highSampleReference d n)) := by
    apply Integrable.of_bound
      (((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
        (highAppendLikelihoodAction_measurable dependent hsymm π activation ham n a V p F hp hF j)).aestronglyMeasurable
      (B * (Ba * P^n))
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply, Function.comp_apply, abs_mul]
      exact mul_le_mul (hHb _) (highAppendLikelihoodAction_abs_le π dependent hsymm activation Ba hBa
        habound n a V P hP ha p F hpb hq j z.1 z.2) (abs_nonneg _) hB
  rw [MeasureTheory.integral_prod _ hi, MeasureTheory.integral_prod _ hi']
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    have he := highAppendLikelihoodAction_observable π dependent hsymm activation ham Ba hBa
      habound n a V P B hP hB ha p F hp hF hpb hq H hH hHb j ω
    convert he using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun e => mul_comm _ _

end NearlyMinimax
