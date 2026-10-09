module

public import NearlyMinimax.HistoryMaximalDelete


@[expose] public section

/-!
# Actual shape-level append/delete change of variables

The append range is identified with a true maximal-label condition in the
canonical heap. The actual append bijection and source rho factor yield an
exact infinite weighted sum change of variables. Mark integration and weak
transport are separate subsequent steps.
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

abbrev HistoryMaximalLabelShape (dependent : J → J → Prop) (j : J) :=
  {g : HistoryShape (fun a b => ¬ dependent a b) // ∃ x : WordHeapPiece g.out dependent,
    x ∈ historyMaximalPieces Finset.univ ∧ wordHeapLabel x = j}

/-- The actual append bijection onto shapes having a true maximal piece with that label. -/
def historyShapeTerminalEquiv (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) : HistoryShape (fun a b => ¬ dependent a b) ≃ HistoryMaximalLabelShape dependent j :=
  (Equiv.ofInjective (historyShapeAppend dependent j)
    (historyShapeAppend_injective dependent hrefl hsymm j)).trans
      ((Equiv.refl _).subtypeEquiv (fun g => historyShape_terminal_iff_maximal dependent hsymm j g))

omit [Fintype J] in
@[simp] theorem historyShapeTerminalEquiv_val (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    (historyShapeTerminalEquiv dependent hrefl hsymm j g).val = historyShapeAppend dependent j g := rfl

omit [Fintype J] in
/-- Its inverse is actual canonical maximal-piece deletion, independently of the chosen witness. -/
theorem historyShapeTerminalEquiv_symm_delete (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryMaximalLabelShape dependent j)
    (x : WordHeapPiece g.val.out dependent) (hx : x ∈ historyMaximalPieces Finset.univ)
    (hlabel : wordHeapLabel x = j) :
    (historyShapeTerminalEquiv dependent hrefl hsymm j).symm g =
      Quotient.mk _ (historyWordDeletePiece g.val.out dependent x) := by
  apply historyShapeAppend_injective dependent hrefl hsymm j
  have hi := congrArg (fun h : HistoryMaximalLabelShape dependent j => h.val)
    ((historyShapeTerminalEquiv dependent hrefl hsymm j).apply_symm_apply g)
  rw [historyShapeTerminalEquiv_val] at hi
  rw [hi]
  have hd := wordHeap_maximal_delete_append g.val.out dependent x hx
  rw [hlabel] at hd
  exact (hd.trans (Quotient.out_eq g.val)).symm

/-- Exact shape-level change of variables, proved for the source weight and actual deletion. -/
theorem historyShape_terminal_weighted_tsum (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (j : J) (F : HistoryShape (fun a b => ¬ dependent a b) → ℝ) :
    (∑' h : HistoryMaximalLabelShape dependent j, historyShapeReferenceWeight dependent Δ h.val *
      F ((historyShapeTerminalEquiv dependent hrefl hsymm j).symm h)) =
        historyReferenceRho Δ * ∑' g, historyShapeReferenceWeight dependent Δ g * F g := by
  let e := historyShapeTerminalEquiv dependent hrefl hsymm j
  calc
    _ = ∑' g, historyShapeReferenceWeight dependent Δ (e g).val * F (e.symm (e g)) :=
      (e.tsum_eq _).symm
    _ = ∑' g, historyReferenceRho Δ * (historyShapeReferenceWeight dependent Δ g * F g) := by
      apply tsum_congr
      intro g
      rw [e.symm_apply_apply]
      change historyShapeReferenceWeight dependent Δ (historyShapeAppend dependent j g) * F g = _
      rw [historyShapeReferenceWeight_append]
      ring
    _ = _ := tsum_mul_left

/-- In particular, each actual maximal-label class has exactly rho times the full reference mass. -/
theorem historyShape_terminal_reference_tsum (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (j : J) :
    (∑' h : HistoryMaximalLabelShape dependent j, historyShapeReferenceWeight dependent Δ h.val) =
      historyReferenceRho Δ * ∑' g, historyShapeReferenceWeight dependent Δ g := by
  simpa only [mul_one] using historyShape_terminal_weighted_tsum dependent hrefl hsymm Δ j (fun _ => 1)

end NearlyMinimax
