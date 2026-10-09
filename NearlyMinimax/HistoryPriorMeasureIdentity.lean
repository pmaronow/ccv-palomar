module

public import NearlyMinimax.HistoryPriorDensity


@[expose] public section

/-!
# The constructed path is the source density tilt of the reference law
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax

/-- A measurable image of a pulled-back density is the corresponding density tilt. -/
theorem historyMap_withDensity {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (f : A → B) (hf : Measurable f) (p : B → ℝ≥0∞) (hp : Measurable p) :
    Measure.map f (μ.withDensity (p ∘ f)) = (Measure.map f μ).withDensity p := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hs.preimage hf), withDensity_apply _ hs,
    Measure.restrict_map hf hs, lintegral_map hp hf]
  rfl

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- The actual unnormalized mixture is exactly the reference measure tilted by Phi. -/
theorem historyMarkedPriorRaw_eq_withDensity (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) (a : E → ℝ) (ha : Measurable a) :
    historyMarkedPriorRaw dependent Δ t π a =
      (historyMarkedReferenceRaw dependent Δ π).withDensity
        (fun h => ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a h)) := by
  let p : HistoryMarked dependent E → ℝ≥0∞ := fun h =>
    ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a h)
  have hp : Measurable p := (historyMarkedDensity_measurable dependent _ t a ha).ennreal_ofReal
  have hm : ∀ g, Measure.map (fun marks => (⟨g, marks⟩ : HistoryMarked dependent E))
      (historyMarkedFiberPrior dependent Δ t π a g) =
        (Measure.map (fun marks => (⟨g, marks⟩ : HistoryMarked dependent E))
          (Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π))).withDensity p := by
    intro g
    change Measure.map _ ((Measure.pi _).withDensity (p ∘ _)) = _
    exact historyMap_withDensity _ _ (historyMarked_measurable_mk dependent g) p hp
  change historyMarkedPriorRaw dependent Δ t π a = (historyMarkedReferenceRaw dependent Δ π).withDensity p
  unfold historyMarkedPriorRaw historyMarkedReferenceRaw
  rw [withDensity_sum]
  apply congrArg Measure.sum
  funext g
  rw [withDensity_smul_measure]
  exact congrArg (fun μ => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) • μ) (hm g)

/-- Thus the actual positive prior path uses precisely dnu_t = Phi_t d tau_0. -/
theorem historyMarkedPrior_eq_withDensity (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) (a : E → ℝ) (ha : Measurable a) :
    historyMarkedPrior dependent Δ t π a =
      (historyMarkedReference dependent Δ π).withDensity
        (fun h => ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a h)) := by
  unfold historyMarkedPrior historyMarkedReference
  rw [withDensity_smul_measure, historyMarkedPriorRaw_eq_withDensity dependent Δ t π a ha]

end NearlyMinimax
