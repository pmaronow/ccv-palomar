module

public import NearlyMinimax.HistoryCanonicalDeletion


@[expose] public section

/-!
# Actual marked reference append change of variables
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

omit [Fintype J] [LinearOrder J] in
theorem historyMeasure_smul_sum {I X : Type*} [MeasurableSpace X]
    (c : ℝ≥0∞) (μ : I → Measure X) : c • Measure.sum μ = Measure.sum (fun i => c • μ i) := by
  ext s hs
  simp only [Measure.smul_apply, Measure.sum_apply _ hs, smul_eq_mul]
  exact ENNReal.tsum_mul_left.symm

/-- The actual marked reference law on the canonical append fiber is a fresh-mark pushforward. -/
theorem historyMarkedAppend_fiber_map (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b))
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    Measure.map (historyMarkedAppend dependent hsymm j (E := E))
      ((Measure.map (Sigma.mk g) (Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π))).prod π) =
      Measure.map (Sigma.mk (historyShapeAppend dependent j g))
        (Measure.pi (fun _ : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) => π)) := by
  let ν := Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)
  let f : (Fin (historyShapeLength dependent g) → E) × E → HistoryMarked dependent E :=
    fun p => historyMarkedAppend dependent hsymm j (⟨g, p.1⟩, p.2)
  have hf : Measurable f := (historyMarkedAppend_measurable dependent hsymm j).comp
    ((historyMarked_measurable_mk dependent g).prodMap measurable_id)
  have hm : (Measure.map (Sigma.mk g) ν).prod π =
      Measure.map (Prod.map (fun marks : Fin (historyShapeLength dependent g) → E =>
        (⟨g, marks⟩ : HistoryMarked dependent E)) id) (ν.prod π) := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map ν π (historyMarked_measurable_mk dependent g) measurable_id
  rw [hm, Measure.map_map (historyMarkedAppend_measurable dependent hsymm j)
    ((historyMarked_measurable_mk dependent g).prodMap measurable_id)]
  change Measure.map f (ν.prod π) = _
  let m := fun p : (Fin (historyShapeLength dependent g) → E) × E =>
    historyCanonicalMarkAppendEquiv dependent hsymm j g (p.2, p.1)
  have hp : MeasurePreserving m (ν.prod π)
      (Measure.pi (fun _ : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) => π)) :=
    (historyCanonicalMarkAppendEquiv_preserving dependent hsymm j g π).comp Measure.measurePreserving_swap
  change Measure.map ((fun marks : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) → E =>
    (⟨historyShapeAppend dependent j g, marks⟩ : HistoryMarked dependent E)) ∘ m) (ν.prod π) = _
  rw [← Measure.map_map (historyMarked_measurable_mk dependent _) hp.measurable, hp.map_eq]

/-- The actual countable reference component consisting of appended shapes. -/
def historyMarkedTerminalReferenceRaw (dependent : J → J → Prop)
    (Δ : ℕ) (j : J) {E : Type*} [MeasurableSpace E] (π : Measure E) :
    Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ (historyShapeAppend dependent j g)) •
    Measure.map (Sigma.mk (historyShapeAppend dependent j g))
      (Measure.pi (fun _ : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) => π))

/-- Exact source rho factor for the actual marked append, derived from both finite mark and shape laws. -/
theorem historyMarkedReferenceRaw_append (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (j : J) {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    ENNReal.ofReal (historyReferenceRho Δ) •
      Measure.map (historyMarkedAppend dependent hsymm j (E := E))
        ((historyMarkedReferenceRaw dependent Δ π).prod π) =
      historyMarkedTerminalReferenceRaw dependent Δ j π := by
  unfold historyMarkedReferenceRaw historyMarkedTerminalReferenceRaw
  rw [Measure.prod_sum_left, Measure.map_sum (historyMarkedAppend_measurable dependent hsymm j).aemeasurable]
  rw [historyMeasure_smul_sum]
  congr 1
  funext g
  rw [Measure.prod_smul_left, Measure.map_smul, smul_smul,
    historyMarkedAppend_fiber_map, historyShapeReferenceWeight_append,
    ENNReal.ofReal_mul (historyReferenceRho_pos Δ).le]
  exact (historyMarkedAppend_measurable dependent hsymm j).aemeasurable

/-- Shapes with a true appended maximal label, including all of their marks. -/
def historyMarkedTerminalSet (dependent : J → J → Prop) (j : J) {E : Type*} :
    Set (HistoryMarked dependent E) := {h | h.1 ∈ Set.range (historyShapeAppend dependent j)}

theorem historyMarkedTerminalSet_measurable (dependent : J → J → Prop) (j : J)
    {E : Type*} [MeasurableSpace E] : MeasurableSet (historyMarkedTerminalSet dependent j (E := E)) := by
  rw [MeasurableSpace.measurableSet_iInf]
  intro g
  change MeasurableSet {marks : Fin (historyShapeLength dependent g) → E |
    g ∈ Set.range (historyShapeAppend dependent j)}
  by_cases hg : g ∈ Set.range (historyShapeAppend dependent j) <;> simp [hg]

omit [Fintype J] [LinearOrder J] in
/-- Reindex a sum of measures on an actual subtype, with zero outside it. -/
theorem historyMeasure_sum_subtype {I X : Type*} [MeasurableSpace X]
    (S : Set I) [DecidablePred (fun i => i ∈ S)] (μ : I → Measure X) :
    Measure.sum (fun i => if i ∈ S then μ i else 0) = Measure.sum (fun i : S => μ i.val) := by
  classical
  ext s hs
  simp only [Measure.sum_apply _ hs]
  calc
    _ = ∑' i, if i ∈ S then μ i s else 0 := by
      apply tsum_congr
      intro i
      split_ifs <;> rfl
    _ = _ := by simpa [Set.indicator_apply] using (tsum_subtype S (fun i => μ i s)).symm

/-- The append component is exactly the actual reference measure restricted to appended shapes. -/
theorem historyMarkedTerminalReferenceRaw_eq_restrict (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (j : J) {E : Type*} [MeasurableSpace E] (π : Measure E) :
    historyMarkedTerminalReferenceRaw dependent Δ j π =
      (historyMarkedReferenceRaw dependent Δ π).restrict (historyMarkedTerminalSet dependent j) := by
  classical
  let G := Set.range (historyShapeAppend dependent j)
  let μ := fun g : HistoryShape (fun a b => ¬ dependent a b) =>
    ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) •
      Measure.map (fun marks : Fin (historyShapeLength dependent g) → E =>
        (⟨g, marks⟩ : HistoryMarked dependent E)) (Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π))
  have hr : ∀ g, (μ g).restrict (historyMarkedTerminalSet dependent j) =
      if g ∈ G then μ g else 0 := by
    intro g
    rw [Measure.restrict_smul, Measure.restrict_map (historyMarked_measurable_mk dependent g)
      (historyMarkedTerminalSet_measurable dependent j)]
    have hp : (fun marks : Fin (historyShapeLength dependent g) → E =>
        (⟨g, marks⟩ : HistoryMarked dependent E)) ⁻¹' historyMarkedTerminalSet dependent j =
        if g ∈ G then Set.univ else ∅ := by
      ext marks
      simp only [Set.mem_preimage, historyMarkedTerminalSet, Set.mem_ofPred_eq]
      by_cases hg : g ∈ G <;> simp [G, hg]
    rw [hp]
    by_cases hg : g ∈ G <;> simp [hg, μ]
  change _ = (Measure.sum μ).restrict _
  rw [Measure.restrict_sum _ (historyMarkedTerminalSet_measurable dependent j)]
  simp_rw [hr]
  rw [historyMeasure_sum_subtype]
  let e := Equiv.ofInjective (historyShapeAppend dependent j)
    (historyShapeAppend_injective dependent hrefl hsymm j)
  have he := Measure.sum_comp_equiv e (fun g : G => μ g.val)
  exact he

/-- Full marked append/delete change of variables for the actual reference measure. -/
theorem historyMarkedReferenceRaw_append_restrict (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (j : J) {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    ENNReal.ofReal (historyReferenceRho Δ) •
      Measure.map (historyMarkedAppend dependent hsymm j (E := E))
        ((historyMarkedReferenceRaw dependent Δ π).prod π) =
      (historyMarkedReferenceRaw dependent Δ π).restrict (historyMarkedTerminalSet dependent j) :=
  (historyMarkedReferenceRaw_append dependent hsymm Δ j π).trans
    (historyMarkedTerminalReferenceRaw_eq_restrict dependent hrefl hsymm Δ j π)

/-- The same exact append change of variables holds for the normalized reference probability. -/
theorem historyMarkedReference_append_restrict (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (j : J) {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    ENNReal.ofReal (historyReferenceRho Δ) •
      Measure.map (historyMarkedAppend dependent hsymm j (E := E))
        ((historyMarkedReference dependent Δ π).prod π) =
      (historyMarkedReference dependent Δ π).restrict (historyMarkedTerminalSet dependent j) := by
  let c := (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹
  change ENNReal.ofReal (historyReferenceRho Δ) •
      Measure.map (historyMarkedAppend dependent hsymm j) ((c • historyMarkedReferenceRaw dependent Δ π).prod π) =
        (c • historyMarkedReferenceRaw dependent Δ π).restrict _
  rw [Measure.prod_smul_left, Measure.map_smul, Measure.restrict_smul]
  swap
  · exact (historyMarkedAppend_measurable dependent hsymm j).aemeasurable
  rw [smul_smul, mul_comm, ← smul_smul,
    historyMarkedReferenceRaw_append_restrict dependent hrefl hsymm Δ j π]

end NearlyMinimax
