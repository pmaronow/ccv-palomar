module

public import NearlyMinimax.HistoryMarkedAppend


@[expose] public section

/-!
# Joint measurability of the actual marked-history append operation
-/

noncomputable section
open MeasureTheory
namespace NearlyMinimax

/-- The sum sigma-algebra makes sectionwise measurable maps measurable. -/
theorem historySigma_measurable_iff {I : Type*} {X : I → Type*} {Y : Type*}
    [∀ i, MeasurableSpace (X i)] [MeasurableSpace Y] (f : Sigma X → Y) :
    Measurable f ↔ ∀ i, Measurable (fun x => f ⟨i, x⟩) := by
  constructor
  · intro hf i
    have hi : Measurable (fun x : X i => (⟨i, x⟩ : Sigma X)) :=
      Measurable.of_le_map (iInf_le _ i)
    exact hf.comp hi
  · intro hf s hs
    rw [MeasurableSpace.measurableSet_iInf]
    exact fun i => hf i hs

/-- Standard Borel fibers let a product and a countable disjoint union interchange measurably. -/
def historySigmaProdMeasurableEquiv {I : Type*} [Countable I] (X : I → Type*) (Y : Type*)
    [∀ i, MeasurableSpace (X i)] [∀ i, StandardBorelSpace (X i)]
    [MeasurableSpace Y] [StandardBorelSpace Y] : (Sigma X) × Y ≃ᵐ Sigma (fun i => X i × Y) := by
  let := fun i => upgradeStandardBorel (X i)
  let := upgradeStandardBorel Y
  let : BorelSpace (Sigma X) := historySigma_borelSpace
  let : BorelSpace (Sigma (fun i => X i × Y)) := historySigma_borelSpace
  exact (Homeomorph.sigmaProdDistrib (X := X) (Y := Y)).toMeasurableEquiv

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- Apply one independent marked local update and reorder into the genuine canonical append. -/
def historyMarkedAppend (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) {E : Type*} [MeasurableSpace E] (h : HistoryMarked dependent E × E) :
    HistoryMarked dependent E :=
  ⟨historyShapeAppend dependent j h.1.1,
    historyCanonicalMarkAppendEquiv dependent hsymm j h.1.1 (h.2, h.1.2)⟩

/-- Both the old history and fresh mark vary measurably in the actual append operation. -/
theorem historyMarkedAppend_measurable (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] :
    Measurable (historyMarkedAppend dependent hsymm j (E := E)) := by
  let X := fun g : HistoryShape (fun a b => ¬ dependent a b) => Fin (historyShapeLength dependent g) → E
  let e := historySigmaProdMeasurableEquiv X E
  let f : Sigma (fun g => X g × E) → HistoryMarked dependent E := fun h =>
    ⟨historyShapeAppend dependent j h.1,
      historyCanonicalMarkAppendEquiv dependent hsymm j h.1 (h.2.2, h.2.1)⟩
  have hf : Measurable f := by
    rw [historySigma_measurable_iff]
    intro g
    exact (historyMarked_measurable_mk dependent (historyShapeAppend dependent j g)).comp
      ((historyCanonicalMarkAppendEquiv dependent hsymm j g).measurable.comp
        MeasurableEquiv.prodComm.measurable)
  exact hf.comp e.measurable

end NearlyMinimax
