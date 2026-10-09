module

public import NearlyMinimax.HighAppendLikelihood


@[expose] public section

/-! The genuine likelihood score of the constructed marked-history experiment.
The derivative numerator uses actual append likelihood actions and one variance
heat correction. This module does not assume a score derivative identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

def highHistoryLikelihoodDerivative {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) (activation : E → ℝ) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  (∑ j, highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z) -
    η^2 * highRawSampleVarianceDerivative n a V (p ω) (F ω) z

/-- A true score: the actual derivative numerator divided by the raw likelihood. -/
def highHistoryLikelihoodScore {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) (activation : E → ℝ) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F ω z /
    highRawSampleLikelihood n a V (p ω) (F ω) z

theorem highHistoryLikelihoodDerivative_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (ham : Measurable activation)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2) := by
  exact (Finset.measurable_sum _ (fun j _ =>
    highAppendLikelihoodAction_measurable dependent hsymm π activation ham n a V p F hp hF j)).sub
      ((highRawSampleVarianceDerivative_joint_measurable n a V p F hp hF).const_mul (η^2))

theorem highHistoryLikelihoodScore_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (ham : Measurable activation)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highHistoryLikelihoodScore dependent hsymm π activation n a V η p F z.1 z.2) := by
  exact (highHistoryLikelihoodDerivative_measurable dependent hsymm π activation ham n a V η p F hp hF).div
    (highRawSampleLikelihood_joint_measurable n a V p F hp hF)

theorem highRawSampleLikelihood_pos {Ω : Type*} {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : ∀ ω x, 0 < p ω x)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (ω : Ω) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    0 < highRawSampleLikelihood n a V (p ω) (F ω) z :=
  Finset.prod_pos (fun i _ => mul_pos (hp ω _) (hq ω _ _))

/-- Testing the actual score against the genuine tilted-prior sample law
cancels its likelihood denominator exactly. -/
theorem massPowerTilt_highHistoryLikelihoodScore_integral {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (π : Measure E) (activation : E → ℝ) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) :
    (∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
      highHistoryLikelihoodScore dependent hsymm π activation n a V η p F z.1 z.2 *
        H (encodeDesignResponse a z.2)
      ∂(massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n).compProd
        (highSampleIndexKernel n a V p F hp hF)) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
          H (encodeDesignResponse a z.2) *
            highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2
          ∂ν.prod (highSampleReference d n) := by
  rw [massPowerTilt_highSample_integral ν n a V p F hp hF aRaw bRaw haRaw hraw
    (fun ω x y => (hq ω x y).le)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    unfold highHistoryLikelihoodScore
    have hL := highRawSampleLikelihood_pos n a V p F
      (fun ω x => haRaw.trans_le (hraw ω x).1) hq z.1 z.2
    field_simp

/-- Integrability and Fubini for the actual score numerator derive from
bounded primitive likelihoods, including all reset states. -/
theorem highHistoryLikelihoodDerivative_observable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] (π : Measure E) [IsProbabilityMeasure π] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η P B : ℝ) (hP : 0 ≤ P) (hB : 0 ≤ B) (ha : 0 < a)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpb : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    (∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
      H (encodeDesignResponse a z.2) *
        highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2
      ∂ν.prod (highSampleReference d n)) =
      (-η^2 * ∫ ω, highRawObservableVarianceDerivative n a V (p ω) (F ω) H ∂ν) +
        ∑ j, ∫ z : HistoryMarked dependent E × E,
          highRawObservable n a V (p (historyMarkedAppend dependent hsymm j z))
            (F (historyMarkedAppend dependent hsymm j z)) H * activation z.2 ∂ν.prod π := by
  let Q := HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))
  let μ : Measure Q := ν.prod (highSampleReference d n)
  let test : Q → ℝ := fun z => H (encodeDesignResponse a z.2)
  let A : J → Q → ℝ := fun j z =>
    highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2
  let D : Q → ℝ := fun z => highRawSampleVarianceDerivative n a V (p z.1) (F z.1) z.2
  have htest : Measurable test := (hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd
  have hiA (j : J) : Integrable (fun z => test z * A j z) μ := by
    apply Integrable.of_bound (htest.mul
      (highAppendLikelihoodAction_measurable dependent hsymm π activation ham n a V p F hp hF j)).aestronglyMeasurable
      (B * (Ba * P^n))
    exact Eventually.of_forall fun z => by
      change ‖H (encodeDesignResponse a z.2) *
        highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hHb _) (highAppendLikelihoodAction_abs_le π dependent hsymm activation Ba hBa
        habound n a V P hP ha.ne' p F hpb hq j z.1 z.2) (abs_nonneg _) hB
  have hiD : Integrable (fun z => test z * D z) μ := by
    apply Integrable.of_bound (htest.mul
      (highRawSampleVarianceDerivative_joint_measurable n a V p F hp hF)).aestronglyMeasurable
      (B * (P^n * ((n : ℝ)/a^2)))
    exact Eventually.of_forall fun z => by
      change ‖H (encodeDesignResponse a z.2) * highRawSampleVarianceDerivative n a V (p z.1) (F z.1) z.2‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hHb _) (highRawSampleVarianceDerivative_abs_le n a V P ha hP _ _ (hpb _) (hq _) z.2)
        (abs_nonneg _) hB
  have heD : (∫ z, test z * D z ∂μ) =
      ∫ ω, highRawObservableVarianceDerivative n a V (p ω) (F ω) H ∂ν := by
    exact MeasureTheory.integral_prod _ hiD
  calc
    _ = ∫ z, ((∑ j, test z * A j z) - η^2 * (test z * D z)) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only [highHistoryLikelihoodDerivative, test, A, D]
        rw [mul_sub, Finset.mul_sum]
        ring
    _ = (∑ j, ∫ z, test z * A j z ∂μ) - η^2 * ∫ z, test z * D z ∂μ := by
      rw [integral_sub (integrable_finsetSum _ (fun j _ => hiA j)) (hiD.const_mul _),
        integral_finsetSum _ (fun j _ => hiA j), integral_const_mul]
    _ = _ := by
      rw [heD]
      have heA (j : J) := highAppendLikelihoodAction_prior_observable π dependent hsymm ν
        activation ham Ba hBa habound n a V P B hP hB ha.ne' p F hp hF hpb hq H hH hHb j
      have hs : (∑ j, ∫ z, test z * A j z ∂μ) =
          ∑ j, ∫ z : HistoryMarked dependent E × E,
            highRawObservable n a V (p (historyMarkedAppend dependent hsymm j z))
              (F (historyMarkedAppend dependent hsymm j z)) H * activation z.2 ∂ν.prod π := by
        apply Finset.sum_congr rfl
        intro j _
        exact (heA j).symm
      rw [hs]
      ring

theorem highHistoryLikelihoodDerivative_abs_le {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (activation : E → ℝ) (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η P : ℝ) (hP : 0 ≤ P) (ha : 0 < a)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hpb : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    |highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F ω z| ≤
      (Fintype.card J : ℝ) * (Ba * P^n) + η^2 * (P^n * ((n : ℝ)/a^2)) := by
  unfold highHistoryLikelihoodDerivative
  calc
    _ ≤ |∑ j, highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z| +
        |η^2 * highRawSampleVarianceDerivative n a V (p ω) (F ω) z| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (∑ j, highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z)
          (0 : ℝ) (η^2 * highRawSampleVarianceDerivative n a V (p ω) (F ω) z)
    _ ≤ (Fintype.card J : ℝ) * (Ba * P^n) + η^2 * (P^n * ((n : ℝ)/a^2)) := by
      apply add_le_add
      · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc
          _ ≤ ∑ j : J, Ba * P^n := Finset.sum_le_sum (fun j _ =>
            highAppendLikelihoodAction_abs_le π dependent hsymm activation Ba hBa habound n a V P hP
              ha.ne' p F hpb hq j ω z)
          _ = _ := by simp
      · rw [abs_mul, abs_of_nonneg (sq_nonneg η)]
        exact mul_le_mul_of_nonneg_left (highRawSampleVarianceDerivative_abs_le n a V P ha hP
          (p ω) (F ω) (hpb ω) (hq ω) z) (sq_nonneg η)

end NearlyMinimax
