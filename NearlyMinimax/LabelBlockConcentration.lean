module

public import NearlyMinimax.LabelBlockMeasure


@[expose] public section

/-!
# Genuine label-block concentration for actual finite history marks
-/

noncomputable section
open MeasureTheory Set Filter
namespace NearlyMinimax

variable {J E : Type*} [Fintype J] [MeasurableSpace E] [Nonempty E]

/-- The genuine bounded-differences bound is independent of the chosen finite enumeration. -/
theorem fintype_product_centered_mgf_le [DecidableEq J] (π : J → Measure E)
    [∀ j, IsProbabilityMeasure (π j)]
    (F : (J → E) → ℝ) (hF : Measurable F) (R c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ x, |F x| ≤ R)
    (hosc : ∀ j x y, |F (Function.update x j y) - F x| ≤ c) (u : ℝ) :
    (∫ x, Real.exp (u * (F x - ∫ y, F y ∂Measure.pi π)) ∂Measure.pi π) ≤
      Real.exp ((Fintype.card J : ℝ) * u ^ 2 * c ^ 2 / 8) := by
  classical
  let f := (Fintype.equivFin J).symm
  let e := MeasurableEquiv.piCongrLeft (fun _ : J => E) f
  have hp : MeasurePreserving e (Measure.pi (fun i => π (f i))) (Measure.pi π) :=
    measurePreserving_piCongrLeft π f
  have he : ∀ (x : Fin (Fintype.card J) → E) i y,
      e (Function.update x i y) = Function.update (e x) (f i) y := by
    intro x i y
    funext j
    obtain ⟨k, rfl⟩ := f.surjective j
    change MeasurableEquiv.piCongrLeft (fun _ : J => E) f (Function.update x i y) (f k) = _
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    by_cases hk : k = i
    · subst k
      simp
    · have hfki : f k ≠ f i := fun h => hk (f.injective h)
      rw [Function.update_of_ne hk, Function.update_of_ne hfki]
      exact (MeasurableEquiv.piCongrLeft_apply_apply f (β := fun _ : J => E) x k).symm
  let G := F ∘ e
  have hGo : ∀ i x y, |G (Function.update x i y) - G x| ≤ c := by
    intro i x y
    dsimp only [G, Function.comp_apply]
    rw [he]
    exact hosc (f i) (e x) y
  have hh := product_centered_mgf_le (Fintype.card J) (fun i => π (f i)) G
    (hF.comp e.measurable) R c hc (fun x => hbound (e x)) hGo u
  have hm : (∫ x, G x ∂Measure.pi (fun i => π (f i))) = ∫ x, F x ∂Measure.pi π :=
    hp.integral_comp' F
  rw [hm] at hh
  change (∫ x, Real.exp (u * (F (e x) - ∫ y, F y ∂Measure.pi π))
    ∂Measure.pi (fun i => π (f i))) ≤ _ at hh
  rw [hp.integral_comp' (fun x => Real.exp (u * (F x - ∫ y, F y ∂Measure.pi π)))] at hh
  exact hh

/-- Actual independent occurrence marks concentrate in the number of labels, not occurrences.
Replacing all occurrences of one label is the only oscillation hypothesis. -/
theorem label_block_centered_mgf_le {I : Type*} [Fintype I] [DecidableEq J]
    (labels : I → J) (π : Measure E) [IsProbabilityMeasure π]
    (F : (I → E) → ℝ) (hF : Measurable F) (R c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ marks, |F marks| ≤ R)
    (hosc : ∀ j marks marks', (∀ i, labels i ≠ j → marks i = marks' i) → |F marks - F marks'| ≤ c)
    (u : ℝ) :
    (∫ marks, Real.exp (u * (F marks - ∫ marks', F marks' ∂Measure.pi (fun _ : I => π)))
      ∂Measure.pi (fun _ : I => π)) ≤ Real.exp ((Fintype.card J : ℝ) * u ^ 2 * c ^ 2 / 8) := by
  let ν := Measure.pi (fun _ : I => π)
  let μ := Measure.pi (fun _ : J => ν)
  let G := F ∘ labelBlockReconstruct labels
  have hp := labelBlockReconstruct_preserving labels π
  have hG : Measurable G := hF.comp (labelBlockReconstruct_measurable labels)
  have ho : ∀ j blocks new, |G (Function.update blocks j new) - G blocks| ≤ c := by
    intro j blocks new
    apply hosc j (labelBlockReconstruct labels (Function.update blocks j new)) (labelBlockReconstruct labels blocks)
    intro i hi
    exact labelBlockReconstruct_update_other labels blocks j new i hi
  have hh := fintype_product_centered_mgf_le (fun _ : J => ν) G hG R c hc
    (fun blocks => hbound (labelBlockReconstruct labels blocks)) ho u
  have hm : (∫ blocks, G blocks ∂μ) = ∫ marks, F marks ∂ν := by
    exact (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm.trans
      (congrArg (fun m : Measure (I → E) => ∫ marks, F marks ∂m) hp.map_eq)
  change (∫ blocks, Real.exp (u * (G blocks - ∫ blocks', G blocks' ∂μ)) ∂μ) ≤ _ at hh
  rw [hm] at hh
  have hi : (∫ blocks, Real.exp (u * (G blocks - ∫ marks, F marks ∂ν)) ∂μ) =
      ∫ marks, Real.exp (u * (F marks - ∫ marks', F marks' ∂ν)) ∂ν := by
    have hmeas : Measurable (fun marks => Real.exp (u * (F marks - ∫ marks', F marks' ∂ν))) :=
      Real.measurable_exp.comp (measurable_const.mul (hF.sub measurable_const))
    exact (integral_map hp.measurable.aemeasurable hmeas.aestronglyMeasurable).symm.trans
      (congrArg (fun m : Measure (I → E) => ∫ marks, Real.exp (u * (F marks - ∫ marks', F marks' ∂ν)) ∂m) hp.map_eq)
  rw [hi] at hh
  exact hh

end NearlyMinimax
