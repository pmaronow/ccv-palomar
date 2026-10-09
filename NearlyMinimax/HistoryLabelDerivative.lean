module

public import NearlyMinimax.HistoryExpectationDerivative


@[expose] public section

/-!
# Actual maximal-label decomposition of the history derivative
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- The actual maximal-deletion contribution of one spatial label. -/
def historyMarkedLabelTerm (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    (a : E → ℝ) (j : J) (h : HistoryMarked dependent E) : ℝ :=
  ∑ x ∈ historyMaximalPieces Finset.univ,
    if wordHeapLabel x = j then historyMarkedPieceWeight dependent a h x *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ (Finset.univ.erase x) t else 0

/-- Genuine finite maximal pieces partition by their actual labels. -/
theorem historyMarkedDensityDerivative_eq_labelSum (dependent : J → J → Prop) (ρ t : ℝ)
    {E : Type*} (a : E → ℝ) (h : HistoryMarked dependent E) :
    historyMarkedDensityDerivative dependent ρ t a h =
      ρ⁻¹ * ∑ j, historyMarkedLabelTerm dependent ρ t a j h := by
  classical
  unfold historyMarkedDensityDerivative historyMarkedLabelTerm
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  simp

/-- There is no contribution when the actual shape has no maximal piece of that label. -/
theorem historyMarkedLabelTerm_eq_zero (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (ρ t : ℝ)
    {E : Type*} (a : E → ℝ) (j : J) (h : HistoryMarked dependent E)
    (hn : h ∉ historyMarkedTerminalSet dependent j) : historyMarkedLabelTerm dependent ρ t a j h = 0 := by
  classical
  unfold historyMarkedLabelTerm
  apply Finset.sum_eq_zero
  intro x hx
  have hl : wordHeapLabel x ≠ j := by
    intro he
    apply hn
    exact (historyShape_terminal_iff_maximal dependent hsymm j h.1).2 ⟨x, hx, he⟩
  simp [hl]

/-- On a genuine append, the unique fresh maximal label has exactly the old deleted density. -/
theorem historyMarkedLabelTerm_append (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ρ t : ℝ) {E : Type*} [MeasurableSpace E] (a : E → ℝ) (j : J)
    (h : HistoryMarked dependent E) (fresh : E) :
    historyMarkedLabelTerm dependent ρ t a j (historyMarkedAppend dependent hsymm j (h, fresh)) =
      a fresh * historyMarkedDensity dependent ρ t a h := by
  classical
  rcases h with ⟨g, marks⟩
  let x := historyCanonicalAppendedPiece dependent hsymm j g
  unfold historyMarkedLabelTerm
  change (∑ y ∈ historyMaximalPieces (Finset.univ : Finset (WordHeapPiece (historyShapeAppend dependent j g).out dependent)),
    if wordHeapLabel y = j then historyMarkedPieceWeight dependent a
      ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩ y *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a
        ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩)
        ρ (Finset.univ.erase y) t else 0) = _
  rw [Finset.sum_eq_single x]
  · rw [ite_eq_left (historyCanonicalAppendedPiece_label dependent hsymm j g)]
    have hw : historyMarkedPieceWeight dependent a
        (historyMarkedAppend dependent hsymm j (⟨g, marks⟩, fresh)) x = a fresh :=
      congrArg a (historyCanonicalMarkAppendEquiv_fresh dependent hsymm j g fresh marks)
    exact congrArg₂ (fun u v : ℝ => u * v) hw
      (historyCanonicalAppend_density_delete dependent hsymm j g fresh marks a ρ t)
  · intro y hy hne
    have hn : wordHeapLabel y ≠ j := by
      intro hj
      apply hne
      exact wordHeap_maximal_label_injective hrefl hsymm Finset.univ hy
        (historyCanonicalAppendedPiece_maximal dependent hsymm j g)
        (hj.trans (historyCanonicalAppendedPiece_label dependent hsymm j g).symm)
    simp [hn]
  · intro hn
    exact (hn (historyCanonicalAppendedPiece_maximal dependent hsymm j g)).elim

/-- Every fixed maximal-label contribution is actually measurable. -/
theorem historyMarkedLabelTerm_measurable (dependent : J → J → Prop) (ρ t : ℝ)
    {E : Type*} [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a) (j : J) :
    Measurable (historyMarkedLabelTerm dependent ρ t a j) := by
  classical
  rw [historyMarked_measurable_iff]
  intro g
  unfold historyMarkedLabelTerm
  change Measurable (fun marks : Fin (historyShapeLength dependent g) → E =>
    ∑ x ∈ historyMaximalPieces (Finset.univ : Finset (WordHeapPiece g.out dependent)),
      if wordHeapLabel x = j then
        a (marks (Fin.cast (historyShapeLength_out dependent g).symm x.position)) *
        historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨g, marks⟩) ρ (Finset.univ.erase x) t else 0)
  apply Finset.measurable_fun_sum _
  intro x hx
  split_ifs
  · exact (ha.comp (measurable_pi_apply (Fin.cast (historyShapeLength_out dependent g).symm x.position))).mul
      (historyMarkedSubdensity_fiber_measurable dependent ρ t a ha g (Finset.univ.erase x))
  · exact measurable_const

/-- The label contribution is bounded uniformly over all finite histories. -/
theorem historyMarkedLabelTerm_bound (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ t B : ℝ) (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] (a : E → ℝ) (ha : ∀ e, |a e| ≤ B)
    (hsmall : t * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (j : J) (h : HistoryMarked dependent E) :
    |historyMarkedLabelTerm dependent ρ t a j h| ≤ B * (3 / 2 : ℝ) ^ Fintype.card J := by
  classical
  by_cases hn : h ∈ historyMarkedTerminalSet dependent j
  · rcases h with ⟨g, marks⟩
    obtain ⟨old, rfl⟩ := hn
    let p := (historyCanonicalMarkAppendEquiv dependent hsymm j old (E := E)).symm marks
    have hm : historyCanonicalMarkAppendEquiv dependent hsymm j old (p.1, p.2) = marks :=
      (historyCanonicalMarkAppendEquiv dependent hsymm j old).apply_symm_apply marks
    rw [← hm]
    change |historyMarkedLabelTerm dependent ρ t a j
      (historyMarkedAppend dependent hsymm j (⟨old, p.2⟩, p.1))| ≤ _
    rw [historyMarkedLabelTerm_append dependent hrefl hsymm, abs_mul]
    have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ t B hρ ht hB a ha hsmall ⟨old, p.2⟩
    have hp : 0 ≤ historyMarkedDensity dependent ρ t a ⟨old, p.2⟩ :=
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
    rw [abs_of_nonneg hp]
    exact mul_le_mul (ha _) hb.2 hp hB
  · rw [historyMarkedLabelTerm_eq_zero dependent hsymm ρ t a j h hn, abs_zero]
    positivity

end NearlyMinimax
