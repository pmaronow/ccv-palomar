module

public import NearlyMinimax.HistoryReferenceSum


@[expose] public section

/-!
# Actual marked-history reference probability measure

The countable shape law uses the source weight `rho^length`. Conditional on a
shape, all of its marks have the independent finite product law. The source
shape-count argument proves finiteness, and the empty shape proves nonzero
mass, so normalization constructs a probability measure without a finiteness
or positivity assumption on the desired law.
-/

noncomputable section
open MeasureTheory
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

instance historyShape_measurableSpace (independent : J → J → Prop) :
    MeasurableSpace (HistoryShape independent) := ⊤

abbrev HistoryMarked (dependent : J → J → Prop) (E : Type*) :=
  Σ g : HistoryShape (fun a b => ¬ dependent a b), Fin (historyShapeLength dependent g) → E

/-- Each canonical history fiber is measurably included in the marked-history space. -/
theorem historyMarked_measurable_mk (dependent : J → J → Prop) {E : Type*}
    [MeasurableSpace E] (g : HistoryShape (fun a b => ¬ dependent a b)) :
    Measurable (fun marks : Fin (historyShapeLength dependent g) → E => (⟨g, marks⟩ : HistoryMarked dependent E)) := by
  apply Measurable.of_le_map
  exact iInf_le _ g

/-- A map on histories is measurable exactly when it is measurable on every shape fiber. -/
theorem historyMarked_measurable_iff (dependent : J → J → Prop) {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] (f : HistoryMarked dependent E → X) :
    Measurable f ↔ ∀ g, Measurable (fun marks => f ⟨g, marks⟩) := by
  constructor
  · intro hf g
    exact hf.comp (historyMarked_measurable_mk dependent g)
  · intro hf s hs
    change MeasurableSet[⨅ g, MeasurableSpace.map (Sigma.mk g)
      (inferInstance : MeasurableSpace (Fin (historyShapeLength dependent g) → E))] (f ⁻¹' s)
    rw [MeasurableSpace.measurableSet_iInf]
    exact fun g => hf g hs

/-- A countable disjoint union of Borel fibers has exactly their sum sigma-algebra. -/
theorem historySigma_borelSpace {I : Type*} [Countable I] {X : I → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)] :
    BorelSpace (Sigma X) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hsec : ∀ i, MeasurableSet (Sigma.mk i ⁻¹' s) :=
      MeasurableSpace.measurableSet_iInf.1 hs
    let : MeasurableSpace (Sigma X) := borel (Sigma X)
    let : BorelSpace (Sigma X) := ⟨rfl⟩
    have hu : s = ⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' s) := by
      ext x
      constructor
      · intro hx; exact Set.mem_iUnion.2 ⟨x.1, x.2, hx, rfl⟩
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨i, y, hy, rfl⟩
        exact hy
    rw [hu]
    exact MeasurableSet.iUnion fun i =>
      (Topology.IsClosedEmbedding.sigmaMk (i := i)).measurableEmbedding.measurableSet_image' (hsec i)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    rw [MeasurableSpace.measurableSet_iInf]
    intro i
    exact (hs.preimage continuous_sigmaMk).measurableSet

/-- The actual history space is standard Borel whenever the mark space is. -/
theorem historyMarked_standardBorel (dependent : J → J → Prop) {E : Type*}
    [MeasurableSpace E] [StandardBorelSpace E] : StandardBorelSpace (HistoryMarked dependent E) := by
  let := upgradeStandardBorel E
  let : BorelSpace (HistoryMarked dependent E) := historySigma_borelSpace
  infer_instance

/-- The chosen representative has exactly the intrinsic number of pieces. -/
theorem historyShapeLength_out (dependent : J → J → Prop)
    (g : HistoryShape (fun a b => ¬ dependent a b)) :
    historyShapeLength dependent g = g.out.length := by
  have hh := congrArg (historyShapeLength dependent) (Quotient.out_eq g)
  rw [historyShapeLength_mk] at hh
  exact hh.symm

/-- Label evaluations in the canonical word of a shape. -/
def historyShapeCanonicalLabels (dependent : J → J → Prop)
    (g : HistoryShape (fun a b => ¬ dependent a b)) : Fin (historyShapeLength dependent g) → J :=
  fun i => g.out.get (Fin.cast (historyShapeLength_out dependent g) i)

omit [Fintype J] [LinearOrder J] in
/-- Finite marked update recursion is measurable for measurable local updates. -/
theorem historyMarked_indexFold_measurable {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] (update : J → E → X → X)
    (hu : ∀ j, Measurable (fun ex : E × X => update j ex.1 ex.2))
    (n : ℕ) (labels : Fin n → J) (indices : List (Fin n))
    (f : (Fin n → E) → X) (hf : Measurable f) :
    Measurable (fun marks => indices.foldl (fun state i => update (labels i) (marks i) state) (f marks)) := by
  induction indices generalizing f with
  | nil => exact hf
  | cons i indices ih =>
    exact ih (fun marks => update (labels i) (marks i) (f marks))
      ((hu (labels i)).comp ((measurable_pi_apply i).prodMk hf))

/-- The actual finite recursion on a canonical marked representative. -/
def historyMarkedRawState (dependent : J → J → Prop) {E X : Type*}
    (update : J → E → X → X) (initial : X) (h : HistoryMarked dependent E) : X :=
  (List.ofFn (fun i : Fin (historyShapeLength dependent h.1) => i)).foldl
    (fun state i => update (historyShapeCanonicalLabels dependent h.1 i) (h.2 i) state) initial

/-- No measurability of a desired law is assumed: it follows from the finite recursion. -/
theorem historyMarkedRawState_measurable (dependent : J → J → Prop) {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] (update : J → E → X → X)
    (hu : ∀ j, Measurable (fun ex : E × X => update j ex.1 ex.2)) (initial : X) :
    Measurable (historyMarkedRawState dependent update initial) := by
  rw [historyMarked_measurable_iff]
  intro g
  unfold historyMarkedRawState
  exact historyMarked_indexFold_measurable update hu (historyShapeLength dependent g)
    (historyShapeCanonicalLabels dependent g) (List.ofFn (fun i : Fin (historyShapeLength dependent g) => i))
    (fun _ => initial) measurable_const

/-- The unnormalized source measure: countably many shapes, independently marked. -/
def historyMarkedReferenceRaw (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) : Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) •
    Measure.map (Sigma.mk g) (Measure.pi fun _ : Fin (historyShapeLength dependent g) => π)

theorem historyMarkedReferenceRaw_univ (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    historyMarkedReferenceRaw dependent Δ π Set.univ =
      ∑' g, ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) := by
  unfold historyMarkedReferenceRaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  congr 1
  funext g
  rw [Measure.smul_apply, Measure.map_apply (historyMarked_measurable_mk dependent g) MeasurableSet.univ]
  simp

/-- The empty shape contributes exactly one unit of raw reference mass. -/
theorem historyMarkedReferenceRaw_univ_one_le (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    1 ≤ historyMarkedReferenceRaw dependent Δ π Set.univ := by
  rw [historyMarkedReferenceRaw_univ]
  let empty : HistoryShape (fun a b => ¬ dependent a b) := Quotient.mk _ []
  have he : ENNReal.ofReal (historyShapeReferenceWeight dependent Δ empty) = 1 := by
    simp [empty, historyShapeReferenceWeight, historyShapeLength_mk]
  rw [← he]
  exact ENNReal.le_tsum (f := fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g)) empty

theorem historyMarkedReferenceRaw_finite (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    IsFiniteMeasure (historyMarkedReferenceRaw dependent Δ π) := by
  constructor
  rw [historyMarkedReferenceRaw_univ]
  exact (historyShapeReferenceWeight_summable dependent hrefl hsymm Δ hΔ hlabels).tsum_ofReal_lt_top

/-- The normalized actual infinite marked-history reference law `tau_0`. -/
def historyMarkedReference (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) : Measure (HistoryMarked dependent E) :=
  (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹ • historyMarkedReferenceRaw dependent Δ π

theorem historyMarkedReference_probability (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (historyMarkedReference dependent Δ π) := by
  let : IsFiniteMeasure (historyMarkedReferenceRaw dependent Δ π) :=
    historyMarkedReferenceRaw_finite dependent hrefl hsymm Δ hΔ hlabels π
  have hpos : historyMarkedReferenceRaw dependent Δ π Set.univ ≠ 0 := by
    have hh := historyMarkedReferenceRaw_univ_one_le dependent Δ π
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hh)
  unfold historyMarkedReference
  constructor
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)

end NearlyMinimax
