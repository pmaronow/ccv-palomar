module

public import NearlyMinimax.HighMarkedSelection
public import NearlyMinimax.SpatialPairProductIntegration


@[expose] public section

/-! Actual response-product marginalization for the selected complete
marked score. Unused responses integrate to one under the true ternary
probability law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem finite_probability_pi_embedding_preserving {I J α : Type*}
    [Fintype I] [Fintype J] [MeasurableSpace α]
    (μ : J → Measure α) [∀ j, IsProbabilityMeasure (μ j)] (e : I ↪ J) :
    MeasurePreserving (fun y : J → α => fun l => y (e l))
      (Measure.pi μ) (Measure.pi (fun l => μ (e l))) := by
  have hc : iIndepFun (fun j (y : J → α) => y j) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ : J => (id : α → α)) (fun _ => aemeasurable_id)
  have hs := iIndepFun.precomp e.injective hc
  have hm : Measurable (fun y : J → α => fun l => y (e l)) :=
    measurable_pi_iff.mpr (fun l => measurable_pi_apply (e l))
  refine ⟨hm, ?_⟩
  have he := (iIndepFun_iff_map_fun_eq_pi_map
    (fun l => (measurable_pi_apply (e l)).aemeasurable)).mp hs
  simpa only [(measurePreserving_eval μ _).map_eq] using he

theorem high_marked_selected_response_energy {ι E : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace E] {n r : ℕ} (e : Fin r ↪ Fin n)
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ) (ha : a ≠ 0)
    (p : Fin n → ℝ) (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b)
    (hw : ∀ i, i ∉ Finset.univ.map e → w i = 0)
    (hReset : ∀ z i, i ∉ Finset.univ.map e → pReset z i = p i) :
    (∫ y, highMarkedLocalScore π activation a V η p pReset cReset g w φ c y ^ 2
      ∂Measure.pi (fun i => ternaryIndexMeasure a (coefficientRegression η g w φ c i) V ha
        (fun b => (hp i b).le))) =
    ∫ y, highMarkedLocalScore π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
      cReset (g ∘ e) (w ∘ e) (φ ∘ e) c y ^ 2
      ∂Measure.pi (fun l => ternaryIndexMeasure a
        (coefficientRegression η (g ∘ e) (w ∘ e) (φ ∘ e) c l) V ha (fun b => (hp (e l) b).le)) := by
  let μ (i : Fin n) := ternaryIndexMeasure a (coefficientRegression η g w φ c i) V ha
    (fun b => (hp i b).le)
  have hpres := finite_probability_pi_embedding_preserving μ e
  let H : (Fin r → Fin 3) → ℝ := fun y =>
    highMarkedLocalScore π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
      cReset (g ∘ e) (w ∘ e) (φ ∘ e) c y ^ 2
  have hHm : Measurable H := measurable_of_countable H
  calc
    _ = ∫ y, H (fun l => y (e l)) ∂Measure.pi μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      exact congrArg (fun z : ℝ => z ^ 2)
        (high_marked_local_score_selected e π activation a V η p pReset cReset g w φ c y hpd hp hw hReset)
    _ = ∫ y, H y ∂Measure.pi (fun l => μ (e l)) :=
      (integral_map hpres.measurable.aemeasurable hHm.aestronglyMeasurable).symm.trans
        (congrArg (fun M => ∫ y, H y ∂M) hpres.map_eq)
    _ = _ := rfl

end NearlyMinimax
