module

public import NearlyMinimax.HistoryDensityTransport


@[expose] public section

/-!
# Actual canonical-coordinate transport for marked independent exchanges
-/

noncomputable section
namespace NearlyMinimax

variable {A : Type*} {n : ℕ}

theorem historyTuple_swap_take (f : Fin n → A) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    (List.ofFn (f ∘ Equiv.swap i j)).take i.val = (List.ofFn f).take i.val := by
  apply List.ext_getElem (by simp)
  intro k hk hk'
  simp only [List.getElem_take, List.getElem_ofFn, Function.comp_def]
  have hkbound : k < i.val := by
    simp only [List.length_take, List.length_ofFn] at hk
    exact hk.trans_le (Nat.min_le_left _ _)
  have hki : (⟨k, by omega⟩ : Fin n) ≠ i := by intro he; have hv : k = i.val := congrArg Fin.val he; omega
  have hkj : (⟨k, by omega⟩ : Fin n) ≠ j := by intro he; have hv : k = j.val := congrArg Fin.val he; omega
  rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem historyTuple_swap_drop (f : Fin n → A) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    (List.ofFn (f ∘ Equiv.swap i j)).drop (j.val + 1) = (List.ofFn f).drop (j.val + 1) := by
  apply List.ext_getElem (by simp)
  intro k hk hk'
  simp only [List.getElem_drop, List.getElem_ofFn, Function.comp_def]
  have hkbound : j.val + 1 + k < n := by simp only [List.length_drop, List.length_ofFn] at hk; omega
  have hki : (⟨j.val + 1 + k, hkbound⟩ : Fin n) ≠ i := by intro he; have hv : j.val + 1 + k = i.val := congrArg Fin.val he; omega
  have hkj : (⟨j.val + 1 + k, hkbound⟩ : Fin n) ≠ j := by intro he; have hv : j.val + 1 + k = j.val := congrArg Fin.val he; omega
  rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- The explicit word decomposition at two adjacent positions. -/
theorem historyTuple_adjacent_decomposition (f : Fin n → A) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    List.ofFn f = (List.ofFn f).take i.val ++ f i :: f j :: (List.ofFn f).drop (j.val + 1) := by
  have hi : i.val < (List.ofFn f).length := by simp
  have hj : j.val < (List.ofFn f).length := by simp
  calc
    _ = (List.ofFn f).take i.val ++ (List.ofFn f).drop i.val := (List.take_append_drop _ _).symm
    _ = _ := by
      rw [List.drop_eq_getElem_cons hi, hij, List.drop_eq_getElem_cons hj]
      simp only [List.getElem_ofFn, Fin.eta]

/-- The actual tuple words differ by precisely the independent adjacent exchange. -/
theorem historyTuple_swap_exchange (f : Fin n → A) (independent : A → A → Prop)
    (i j : Fin n) (hij : i.val + 1 = j.val) (hind : independent (f i) (f j)) :
    IndependentHistoryExchange independent (List.ofFn f) (List.ofFn (f ∘ Equiv.swap i j)) := by
  have hword := historyTuple_adjacent_decomposition f i j hij
  have hword' := historyTuple_adjacent_decomposition (f ∘ Equiv.swap i j) i j hij
  rw [historyTuple_swap_take f i j hij, historyTuple_swap_drop f i j hij] at hword'
  simp only [Function.comp_def, Equiv.swap_apply_left, Equiv.swap_apply_right] at hword'
  simp only [Function.comp_def]
  rw [hword, hword']
  exact IndependentHistoryExchange.swap _ _ (f i) (f j) hind

/-- Marked updates preserve the actual folded raw state under the transported coordinates. -/
theorem historyTuple_swap_state {J E X : Type*} (dependent : J → J → Prop)
    (update : J → E → X → X)
    (hcomm : ∀ j k, ¬ dependent j k → ∀ e f state,
      update k f (update j e state) = update j e (update k f state))
    (labels : Fin n → J) (marks : Fin n → E) (i j : Fin n)
    (hij : i.val + 1 = j.val) (hind : ¬ dependent (labels i) (labels j)) (initial : X) :
    historyWordState (fun p : J × E => update p.1 p.2) initial
      (List.ofFn (fun k => (labels k, marks k))) =
    historyWordState (fun p : J × E => update p.1 p.2) initial
      (List.ofFn (fun k => (labels (Equiv.swap i j k), marks (Equiv.swap i j k)))) := by
  exact historyWordState_exchange
    (independent := fun p q : J × E => ¬ dependent p.1 q.1)
    (fun p q h state => hcomm p.1 q.1 h p.2 q.2 state) initial
    (historyTuple_swap_exchange (fun k => (labels k, marks k)) _ i j hij hind)

/-- Independent finite product marks retain their law under the actual coordinate exchange. -/
theorem historyTuple_swap_marks_measurePreserving {E : Type*} [MeasurableSpace E]
    (π : MeasureTheory.Measure E) [MeasureTheory.IsProbabilityMeasure π] (i j : Fin n) :
    MeasureTheory.MeasurePreserving (fun marks : Fin n → E => marks ∘ Equiv.swap i j)
      (MeasureTheory.Measure.pi (fun _ => π)) (MeasureTheory.Measure.pi (fun _ => π)) := by
  convert MeasureTheory.measurePreserving_piCongrLeft (fun _ : Fin n => π) (Equiv.swap i j) using 1
  ext marks k
  have hh := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap i j) (β := fun _ : Fin n => E)
    (x := marks) (i := Equiv.swap i j k)
  simpa only [Equiv.swap_apply_self, Function.comp_def] using hh.symm

/-- Actual mark weights in the heap of a finite tuple word. -/
def historyTuplePieceWeight {J E : Type*} (dependent : J → J → Prop)
    (labels : Fin n → J) (marks : Fin n → E) (a : E → ℝ)
    (x : WordHeapPiece (List.ofFn labels) dependent) : ℝ :=
  a (marks (historyTuplePositionEquiv labels x.position))

/-- The actual source polynomial and its marks transport under the independent exchange. -/
theorem historyTuple_swap_density {J E : Type*} (dependent : J → J → Prop)
    (hsymm : ∀ ⦃a b⦄, dependent a b → dependent b a)
    (labels : Fin n → J) (marks : Fin n → E) (a : E → ℝ)
    (i j : Fin n) (hij : i.val + 1 = j.val) (hind : ¬ dependent (labels i) (labels j))
    (ρ t : ℝ) :
    historyScaledUpperDensity (historyTuplePieceWeight dependent labels marks a) ρ Finset.univ t =
      historyScaledUpperDensity
        (historyTuplePieceWeight dependent (labels ∘ Equiv.swap i j) (marks ∘ Equiv.swap i j) a)
        ρ Finset.univ t := by
  let e := historyTupleSwapHeapIso labels dependent hsymm i j hij hind
  let weight' := historyTuplePieceWeight dependent (labels ∘ Equiv.swap i j) (marks ∘ Equiv.swap i j) a
  have hw : weight' ∘ e = historyTuplePieceWeight dependent labels marks a := by
    funext x
    simp [weight', e, historyTuplePieceWeight, historyTupleSwapHeapIso,
      wordHeapOrderIsoPosition, historyTupleSwapPositions, Function.comp_def]
  have hu : (Finset.univ : Finset (WordHeapPiece (List.ofFn labels) dependent)).map e.toEquiv.toEmbedding = Finset.univ :=
    Finset.map_univ_equiv e.toEquiv
  have ht := historyScaledUpperDensity_orderIso_map e weight' ρ Finset.univ t
  rw [hu, hw] at ht
  exact ht.symm

end NearlyMinimax
