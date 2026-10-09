module

public import NearlyMinimax.HistoryReferenceMeasure


@[expose] public section

/-!
# The actual positive polynomial density on independently marked histories

Each history is evaluated in its canonical word. Its signed weight is the
proved finite upper-set polynomial, not a prescribed prior density.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- The signed mark at an actual canonical heap occurrence. -/
def historyMarkedPieceWeight (dependent : J → J → Prop) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) (x : WordHeapPiece h.1.out dependent) : ℝ :=
  a (h.2 (Fin.cast (historyShapeLength_out dependent h.1).symm x.position))

/-- The source upper-set polynomial on the actual marked dependency heap. -/
def historyMarkedDensity (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) : ℝ :=
  historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ Finset.univ t

theorem historyMarkedDensity_fiber_measurable (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a)
    (g : HistoryShape (fun i j => ¬ dependent i j)) :
    Measurable (fun marks => historyMarkedDensity dependent ρ t a ⟨g, marks⟩) := by
  classical
  unfold historyMarkedDensity
  simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
  change Measurable (fun marks : Fin (historyShapeLength dependent g) → E =>
    ∑ P ∈ historyUpperSets (Finset.univ : Finset (WordHeapPiece g.out dependent)),
      (t / ρ) ^ P.card * historyOrderVolume P * ∏ x ∈ P,
        a (marks (Fin.cast (historyShapeLength_out dependent g).symm x.position)))
  apply Finset.measurable_fun_sum _
  intro P hP
  apply Measurable.const_mul
  apply Finset.measurable_fun_prod _
  intro x hx
  exact ha.comp (measurable_pi_apply _)

theorem historyMarkedDensity_measurable (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a) :
    Measurable (historyMarkedDensity dependent ρ t a) :=
  (historyMarked_measurable_iff dependent _).2
    (historyMarkedDensity_fiber_measurable dependent ρ t a ha)

/-- The source positivity interval is uniform over all shapes and all bounded marks. -/
theorem historyMarkedDensity_bounds (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ t B : ℝ) (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    {E : Type*} (a : E → ℝ) (ha : ∀ e, |a e| ≤ B)
    (hsmall : t * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) (h : HistoryMarked dependent E) :
    (1 / 2 : ℝ) ^ Fintype.card J ≤ historyMarkedDensity dependent ρ t a h ∧
      historyMarkedDensity dependent ρ t a h ≤ (3 / 2 : ℝ) ^ Fintype.card J :=
  wordHeap_density_bounds h.1.out dependent hrefl hsymm Δ hlabels
    (historyMarkedPieceWeight dependent a h) ρ t B hρ ht hB (fun _ => ha _) hsmall

/-- A finite product over selected independent coordinates factors into expectations. -/
theorem historyIntegral_pi_finset_prod {I E : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (S : Finset I) :
    (∫ marks : I → E, ∏ i ∈ S, a (marks i) ∂Measure.pi (fun _ => π)) =
      ∏ _i ∈ S, ∫ e, a e ∂π := by
  classical
  have hp : ∀ marks : I → E, (∏ i : I, if i ∈ S then a (marks i) else 1) =
      ∏ i ∈ S, a (marks i) := fun marks => Finset.prod_ite_mem_eq S _
  simp_rw [← hp]
  rw [integral_fintype_prod_eq_prod (fun (i : I) (e : E) => if i ∈ S then a e else 1)]
  calc
    _ = ∏ i : I, if i ∈ S then ∫ e, a e ∂π else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hS : i ∈ S <;> simp [hS]
    _ = _ := Finset.prod_ite_mem_eq S _

theorem historyIntegrable_pi_finset_prod {I E : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ)
    (ha : Integrable a π) (S : Finset I) :
    Integrable (fun marks : I → E => ∏ i ∈ S, a (marks i)) (Measure.pi (fun _ => π)) := by
  classical
  have hp := Integrable.fintype_prod (μ := fun _ : I => π)
    (f := fun i e => if i ∈ S then a e else 1)
    (fun i => by by_cases hi : i ∈ S <;> simp [hi, ha])
  simpa only [Finset.prod_ite_mem_eq] using hp

/-- Selected independent mark products factor even with an injective piece indexing. -/
theorem historyIntegral_pi_indexed_prod {I A E : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq A] [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
    (a : E → ℝ) (index : A → I) (hi : Function.Injective index) (P : Finset A) :
    (∫ marks : I → E, ∏ x ∈ P, a (marks (index x)) ∂Measure.pi (fun _ => π)) =
      ∏ _x ∈ P, ∫ e, a e ∂π := by
  have hp : ∀ marks : I → E, (∏ i ∈ P.image index, a (marks i)) =
      ∏ x ∈ P, a (marks (index x)) := fun marks => Finset.prod_image hi.injOn
  calc
    _ = ∫ marks : I → E, ∏ i ∈ P.image index, a (marks i) ∂Measure.pi (fun _ => π) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun marks => (hp marks).symm)
    _ = ∏ _i ∈ P.image index, ∫ e, a e ∂π := historyIntegral_pi_finset_prod π a _
    _ = _ := Finset.prod_image hi.injOn

theorem historyIntegrable_pi_indexed_prod {I A E : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq A] [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
    (a : E → ℝ) (ha : Integrable a π) (index : A → I)
    (hi : Function.Injective index) (P : Finset A) :
    Integrable (fun marks : I → E => ∏ x ∈ P, a (marks (index x))) (Measure.pi (fun _ => π)) := by
  have hp := historyIntegrable_pi_finset_prod π a ha (P.image index)
  simpa only [Finset.prod_image hi.injOn] using hp

/-- Occurrences in a canonical heap have distinct independent mark coordinates. -/
def historyMarkedPieceIndex (dependent : J → J → Prop)
    (g : HistoryShape (fun i j => ¬ dependent i j)) : WordHeapPiece g.out dependent → Fin (historyShapeLength dependent g) :=
  fun x => Fin.cast (historyShapeLength_out dependent g).symm x.position

theorem historyMarkedPieceIndex_injective (dependent : J → J → Prop)
    (g : HistoryShape (fun i j => ¬ dependent i j)) :
    Function.Injective (historyMarkedPieceIndex dependent g) := by
  intro x y hxy
  apply WordHeapPiece.ext
  exact Fin.cast_injective _ hxy

/-- Centering kills every nonempty upper-set monomial of the actual density. -/
theorem historyMarkedDensity_fiber_integral_one (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
    (a : E → ℝ) (ha : Integrable a π) (hcenter : ∫ e, a e ∂π = 0)
    (g : HistoryShape (fun i j => ¬ dependent i j)) :
    (∫ marks, historyMarkedDensity dependent ρ t a ⟨g, marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) = 1 := by
  classical
  let index := historyMarkedPieceIndex dependent g
  have hi : Function.Injective index := historyMarkedPieceIndex_injective dependent g
  have hterm : ∀ P : Finset (WordHeapPiece g.out dependent),
      Integrable (fun marks => (t / ρ) ^ P.card * historyOrderVolume P * ∏ x ∈ P, a (marks (index x)))
        (Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) := by
    intro P
    exact (historyIntegrable_pi_indexed_prod π a ha index hi P).const_mul _
  unfold historyMarkedDensity
  simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
  change (∫ marks, ∑ P ∈ historyUpperSets (Finset.univ : Finset (WordHeapPiece g.out dependent)),
    (t / ρ) ^ P.card * historyOrderVolume P * ∏ x ∈ P, a (marks (index x))
    ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) = 1
  rw [integral_finsetSum _ (fun P _ => hterm P)]
  simp_rw [integral_const_mul, historyIntegral_pi_indexed_prod π a index hi, hcenter]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro P hP hne
    rw [Finset.prod_const]
    simp [zero_pow (Finset.card_ne_zero.2 (Finset.nonempty_iff_ne_empty.2 hne))]
  · intro hnot
    exact (hnot (mem_historyUpperSets.2 ⟨Finset.empty_subset _, by simp⟩)).elim

@[simp] theorem historyMarkedDensity_zero (dependent : J → J → Prop) (ρ : ℝ) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) : historyMarkedDensity dependent ρ 0 a h = 1 := by
  unfold historyMarkedDensity historyScaledUpperDensity
  exact historyUpperDensity_at_zero _ _

/-- The actual polynomial tilts the independent marks within a shape. -/
def historyMarkedFiberPrior (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ)
    (g : HistoryShape (fun i j => ¬ dependent i j)) :
    Measure (Fin (historyShapeLength dependent g) → E) :=
  (Measure.pi (fun _ => π)).withDensity
    (fun marks => ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a ⟨g, marks⟩))

/-- Positivity is derived from the dependency heap, and normalization from centered marks. -/
theorem historyMarkedFiberPrior_probability (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Integrable a π)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (g : HistoryShape (fun i j => ¬ dependent i j)) :
    IsProbabilityMeasure (historyMarkedFiberPrior dependent Δ t π a g) := by
  have he := historyMarkedDensity_fiber_integral_one dependent (historyReferenceRho Δ) t π a ha hcenter g
  have hi := integrable_of_integral_eq_one he
  have hnonneg : ∀ marks, 0 ≤ historyMarkedDensity dependent (historyReferenceRho Δ) t a ⟨g, marks⟩ := by
    intro marks
    have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels _ t B
      (historyReferenceRho_pos Δ) ht hB a habound hsmall ⟨g, marks⟩
    exact (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
  constructor
  unfold historyMarkedFiberPrior
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnonneg), he]
  simp

/-- The actual positive marked-history prior before source reference normalization. -/
def historyMarkedPriorRaw (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ) : Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) •
    Measure.map (Sigma.mk g) (historyMarkedFiberPrior dependent Δ t π a g)

/-- The path uses exactly the same time-independent source normalizer. -/
def historyMarkedPrior (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ) : Measure (HistoryMarked dependent E) :=
  (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹ • historyMarkedPriorRaw dependent Δ t π a

theorem historyMarkedPriorRaw_univ (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Integrable a π)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) :
    historyMarkedPriorRaw dependent Δ t π a Set.univ = historyMarkedReferenceRaw dependent Δ π Set.univ := by
  rw [historyMarkedReferenceRaw_univ]
  unfold historyMarkedPriorRaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  congr 1
  funext g
  let : IsProbabilityMeasure (historyMarkedFiberPrior dependent Δ t π a g) :=
    historyMarkedFiberPrior_probability dependent hrefl hsymm Δ hlabels t B ht hB π a ha hcenter habound hsmall g
  rw [Measure.smul_apply, Measure.map_apply (historyMarked_measurable_mk dependent g) MeasurableSet.univ]
  simp

/-- The source path of positive prior measures is genuinely constructed for the whole interval. -/
theorem historyMarkedPrior_probability (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Integrable a π)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) :
    IsProbabilityMeasure (historyMarkedPrior dependent Δ t π a) := by
  let : IsFiniteMeasure (historyMarkedReferenceRaw dependent Δ π) :=
    historyMarkedReferenceRaw_finite dependent hrefl hsymm Δ hΔ hlabels π
  have hn : historyMarkedReferenceRaw dependent Δ π Set.univ ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (historyMarkedReferenceRaw_univ_one_le dependent Δ π))
  constructor
  unfold historyMarkedPrior
  rw [Measure.smul_apply, historyMarkedPriorRaw_univ dependent hrefl hsymm Δ hlabels t B ht hB π a ha hcenter habound hsmall,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hn (measure_ne_top _ _)

@[simp] theorem historyMarkedPrior_zero (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ) :
    historyMarkedPrior dependent Δ 0 π a = historyMarkedReference dependent Δ π := by
  unfold historyMarkedPrior historyMarkedReference historyMarkedPriorRaw historyMarkedReferenceRaw
  congr 1
  congr 1
  funext g
  unfold historyMarkedFiberPrior
  simp only [historyMarkedDensity_zero, ENNReal.ofReal_one]
  rw [show (fun _ : Fin (historyShapeLength dependent g) → E => (1 : ℝ≥0∞)) = 1 from rfl,
    withDensity_one]

end NearlyMinimax
