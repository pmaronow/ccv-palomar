module

public import NearlyMinimax.HighMarkedDesignFactorial


@[expose] public section

/-! Borel complete-generator numerator arrays from the primitive genuine
mark law and legal Borel density/coefficient resets. This applies to the
entire source row union, with its one common heat correction. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

section
variable {α ι E : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

theorem highMarkedResponseMass_measurable (a V η : ℝ) (g w : α → ℝ)
    (hg : Measurable g) (hw : Measurable w) (φ : α → ι → ℝ)
    (hφ : ∀ γ, Measurable (fun x => φ x γ)) (c : ι → ℝ) (y : Fin 3) :
    Measurable (fun x => highMarkedResponseMass a V η g w φ c x y) := by
  apply ternaryMass_measurable_comp
  exact hg.add ((measurable_const.mul hw).mul
    (Finset.measurable_sum _ (fun γ _ => (hφ γ).mul_const (c γ))))

theorem highMarkedSampleNumerator_measurable (r : ℕ) (π : Measure E) [SFinite π]
    (activation : E → ℝ) (hAct : Measurable activation) (a V η : ℝ)
    (p : α → ℝ) (hp : Measurable p) (pReset : E → α → ℝ)
    (hpReset : Measurable (Function.uncurry pReset)) (cReset : E → ι → ℝ)
    (hcReset : ∀ γ, Measurable (fun e => cReset e γ))
    (g w : α → ℝ) (hg : Measurable g) (hw : Measurable w)
    (φ : α → ι → ℝ) (hφ : ∀ γ, Measurable (fun x => φ x γ))
    (c : ι → ℝ) (y : Fin r → Fin 3) :
    Measurable (fun x => highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c x y) := by
  have hReset (i : Fin r) : Measurable (fun z : E × (Fin r → α) => pReset z.1 (z.2 i)) :=
    hpReset.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hreg (i : Fin r) : Measurable (fun z : E × (Fin r → α) =>
      coefficientRegression η (g ∘ z.2) (w ∘ z.2) (φ ∘ z.2) (cReset z.1) i) := by
    unfold coefficientRegression
    exact (hg.comp ((measurable_pi_apply i).comp measurable_snd)).add
      ((measurable_const.mul (hw.comp ((measurable_pi_apply i).comp measurable_snd))).mul
        (Finset.measurable_sum _ (fun γ _ =>
          ((hφ γ).comp ((measurable_pi_apply i).comp measurable_snd)).mul
            ((hcReset γ).comp measurable_fst))))
  have hproduct : Measurable (fun z : E × (Fin r → α) =>
      highResponseProduct a V η (g ∘ z.2) (w ∘ z.2) (φ ∘ z.2) (cReset z.1) y) :=
    Finset.measurable_prod _ (fun i _ => ternaryMass_measurable_comp a V _ (hreg i) (y i))
  have hMarked : Measurable (fun z : E × (Fin r → α) =>
      activation z.1 * (∏ i, pReset z.1 (z.2 i)) *
        highResponseProduct a V η (g ∘ z.2) (w ∘ z.2) (φ ∘ z.2) (cReset z.1) y) :=
    ((hAct.comp measurable_fst).mul (Finset.measurable_prod _ (fun i _ => hReset i))).mul hproduct
  have hAction : Measurable (fun x : Fin r → α =>
      highMarkedResponseAction π activation a V η (fun z => pReset z ∘ x) cReset
        (g ∘ x) (w ∘ x) (φ ∘ x) y) :=
    hMarked.stronglyMeasurable.integral_prod_left'.measurable
  have hq (i : Fin r) : Measurable (fun x : Fin r → α =>
      ternaryMass a (coefficientRegression η (g ∘ x) (w ∘ x) (φ ∘ x) c i) V (y i)) :=
    (highMarkedResponseMass_measurable a V η g w hg hw φ hφ c (y i)).comp (measurable_pi_apply i)
  have hvar (i : Fin r) : Measurable (fun x : Fin r → α =>
      highResponseVarianceTerm a V η (g ∘ x) (w ∘ x) (φ ∘ x) c y i) := by
    unfold highResponseVarianceTerm
    exact measurable_const.mul (Finset.measurable_prod _ (fun l _ => hq l))
  exact hAction.sub ((measurable_const.mul
    (Finset.measurable_prod _ (fun i _ => hp.comp (measurable_pi_apply i)))).mul
      (Finset.measurable_sum _ (fun i _ =>
        ((hw.comp (measurable_pi_apply i)).pow_const 2).mul (hvar i))))

theorem highMarkedSampleConditionalEnergy_measurable (r : ℕ) (π : Measure E) [SFinite π]
    (activation : E → ℝ) (hAct : Measurable activation) (a V η : ℝ)
    (p : α → ℝ) (hp : Measurable p) (pReset : E → α → ℝ)
    (hpReset : Measurable (Function.uncurry pReset)) (cReset : E → ι → ℝ)
    (hcReset : ∀ γ, Measurable (fun e => cReset e γ))
    (g w : α → ℝ) (hg : Measurable g) (hw : Measurable w)
    (φ : α → ι → ℝ) (hφ : ∀ γ, Measurable (fun x => φ x γ)) (c : ι → ℝ) :
    Measurable (highMarkedSampleConditionalEnergy r π activation a V η p pReset cReset g w φ c) := by
  unfold highMarkedSampleConditionalEnergy selectedConditionalScoreEnergy
  apply Finset.measurable_sum
  intro y hy
  have hq : Measurable (fun x : Fin r → α =>
      ∏ i, highMarkedResponseMass a V η g w φ c (x i) (y i)) :=
    Finset.measurable_prod _ (fun i _ =>
      (highMarkedResponseMass_measurable a V η g w hg hw φ hφ c (y i)).comp (measurable_pi_apply i))
  have hL : Measurable (fun x : Fin r → α =>
      selectedRawLikelihood p (highMarkedResponseMass a V η g w φ c) x y) :=
    (Finset.measurable_prod _ (fun i _ => hp.comp (measurable_pi_apply i))).mul hq
  exact hq.mul (((highMarkedSampleNumerator_measurable r π activation hAct a V η p hp pReset hpReset
    cReset hcReset g w hg hw φ hφ c y).div hL).pow_const 2)

end
end NearlyMinimax
