module

public import NearlyMinimax.HistoryPrefixHeap
public import NearlyMinimax.HistoryAppendMeasurable


@[expose] public section

/-!
# Exact marked density after deleting the appended maximal occurrence
-/

noncomputable section
open MeasureTheory
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

@[simp] theorem historyFiniteMarkAppendEquiv_old (n : ℕ) {E : Type*} [MeasurableSpace E]
    (fresh : E) (marks : Fin n → E) (x : Fin n) :
    historyFiniteMarkAppendEquiv n (fresh, marks) x.castSucc = marks x := by
  have hh := congrArg (fun p : E × (Fin n → E) => p.2 x)
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) (Fin.last n)).apply_symm_apply (fresh, marks))
  change historyFiniteMarkAppendEquiv n (fresh, marks) ((Fin.last n).succAbove x) = marks x at hh
  simpa only [Fin.succAbove_last_apply] using hh

/-- Actual prefix occurrences have the old mark coordinates in the canonical append. -/
theorem historyCanonicalAppendCoordinates_old (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b))
    (x : WordHeapPiece g.out dependent) :
    historyCanonicalAppendCoordinates dependent hsymm j g
      (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc =
      Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
        (historyCanonicalAppendHeapIso dependent hsymm j g
          (historyPrefixHeapEmbedding g.out dependent j x)).position := by
  let hlen : historyShapeLength dependent g + 1 = (g.out ++ [j]).length := by
    rw [historyShapeLength_out]; simp
  have hp : (finCongr hlen)
      (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc =
        (historyPrefixHeapEmbedding g.out dependent j x).position := by
    apply Fin.ext
    rfl
  unfold historyCanonicalAppendCoordinates
  change Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
    (historyHeapCoordinateEquiv (historyCanonicalAppendHeapIso dependent hsymm j g)
      ((finCongr hlen) (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc)) = _
  rw [hp, historyHeapCoordinateEquiv_position]

/-- Every old occurrence in the canonical append carries exactly its original mark. -/
theorem historyCanonicalMarkAppendEquiv_old (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) {E : Type*} [MeasurableSpace E]
    (fresh : E) (marks : Fin (historyShapeLength dependent g) → E)
    (x : WordHeapPiece g.out dependent) :
    historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)
      (Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
        (historyCanonicalAppendHeapIso dependent hsymm j g
          (historyPrefixHeapEmbedding g.out dependent j x)).position) =
      marks (Fin.cast (historyShapeLength_out dependent g).symm x.position) := by
  rw [← historyCanonicalAppendCoordinates_old]
  have hh := MeasurableEquiv.piCongrLeft_apply_apply
    (historyCanonicalAppendCoordinates dependent hsymm j g)
    (β := fun _ => E) (historyFiniteMarkAppendEquiv _ (fresh, marks))
    (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc
  change MeasurableEquiv.piCongrLeft
    (fun _ : Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) => E)
    (historyCanonicalAppendCoordinates dependent hsymm j g)
    (historyFiniteMarkAppendEquiv _ (fresh, marks))
    (historyCanonicalAppendCoordinates dependent hsymm j g
      (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc) = _
  rw [hh, historyFiniteMarkAppendEquiv_old]

/-- The source deleted polynomial equals the original marked density, with no deletion-density premise. -/
theorem historyCanonicalAppend_density_delete (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) {E : Type*} [MeasurableSpace E]
    (fresh : E) (marks : Fin (historyShapeLength dependent g) → E)
    (a : E → ℝ) (ρ t : ℝ) :
    historyScaledUpperDensity
      (historyMarkedPieceWeight dependent a
        ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩)
      ρ (Finset.univ.erase (historyCanonicalAppendedPiece dependent hsymm j g)) t =
      historyMarkedDensity dependent ρ t a ⟨g, marks⟩ := by
  classical
  let e := historyCanonicalAppendHeapIso dependent hsymm j g
  let w := historyMarkedPieceWeight dependent a
    ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩
  have ht := historyScaledUpperDensity_orderIso_map e w ρ
    (Finset.univ.erase (wordHeapAppendedPiece g.out dependent j)) t
  rw [Finset.map_erase, Finset.map_univ_equiv] at ht
  have hw : (w ∘ e) ∘ historyPrefixHeapEmbedding g.out dependent j =
      historyMarkedPieceWeight dependent a ⟨g, marks⟩ := by
    funext x
    exact congrArg a (historyCanonicalMarkAppendEquiv_old dependent hsymm j g fresh marks x)
  rw [historyPrefixHeap_density_delete, hw] at ht
  exact ht

end NearlyMinimax
