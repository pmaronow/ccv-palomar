module

public import NearlyMinimax.HistoryCanonicalDeletion


@[expose] public section

/-! Marked local updates have identical folded states along any two actual
linear extensions of one labelled dependency heap. -/
noncomputable section
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem historyFold_move_to_front {ι X : Type*} (update : ι → X → X)
    (before after : List ι) (x : ι)
    (hcomm : ∀ y ∈ before, ∀ state, update x (update y state) = update y (update x state))
    (initial : X) :
    (before ++ x :: after).foldl (fun state y => update y state) initial =
      (before ++ after).foldl (fun state y => update y state) (update x initial) := by
  have hfold : ∀ state, update x (before.foldl (fun s y => update y s) state) =
      before.foldl (fun s y => update y s) (update x state) := by
    induction before with
    | nil => intro state; rfl
    | cons y ys ih =>
      intro state
      simp only [List.foldl_cons]
      rw [ih (fun z hz => hcomm z (List.mem_cons_of_mem y hz))]
      rw [hcomm y List.mem_cons_self]
  simp only [List.foldl_append, List.foldl_cons]
  rw [hfold]

/-- Finite heap linear extensions preserve the actual marked update fold.
Only incomparable actions must commute. -/
theorem historyFold_linear_extension_invariant {ι X : Type*} [PartialOrder ι]
    (dependent : ι → ι → Prop) (update : ι → X → X)
    (hcomp : ∀ x y, dependent x y → x ≤ y ∨ y ≤ x)
    (hcomm : ∀ x y, ¬ dependent x y → ∀ state,
      update y (update x state) = update x (update y state))
    {l l' : List ι} (hperm : l.Perm l')
    (hl : l.Pairwise (fun x y => ¬ y ≤ x))
    (hl' : l'.Pairwise (fun x y => ¬ y ≤ x)) (initial : X) :
    l.foldl (fun state x => update x state) initial =
      l'.foldl (fun state x => update x state) initial := by
  induction l' generalizing l initial with
  | nil =>
    have he : l = [] := List.perm_nil.mp hperm
    subst l
    rfl
  | cons x xs ih =>
    have hx : x ∈ l := hperm.mem_iff.mpr List.mem_cons_self
    obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp hx
    obtain ⟨hbefore, hafter, hcross⟩ := List.pairwise_append.mp hl
    have htailperm : (before ++ after).Perm xs :=
      (List.perm_middle.symm.trans hperm).cons_inv
    have htail : (before ++ after).Pairwise (fun x y => ¬ y ≤ x) :=
      hl.sublist (List.Sublist.append (List.Sublist.refl before) (List.Sublist.cons x (List.Sublist.refl after)))
    have hmove : ∀ y ∈ before, ∀ state, update x (update y state) = update y (update x state) := by
      intro y hy state
      have hxy : ¬ x ≤ y := hcross y hy x List.mem_cons_self
      have hyne : y ≠ x := by intro h; subst y; exact hxy le_rfl
      have hymem : y ∈ xs := by
        have hm : y ∈ x :: xs := hperm.mem_iff.mp (List.mem_append_left _ hy)
        simpa only [List.mem_cons, hyne, false_or] using hm
      have hyx : ¬ y ≤ x := (List.pairwise_cons.mp hl').1 y hymem
      have hdep : ¬ dependent x y := fun hd => (hcomp x y hd).elim hxy hyx
      exact (hcomm x y hdep state).symm
    rw [historyFold_move_to_front update before after x hmove initial]
    exact ih htailperm htail hl'.of_cons (update x initial)

def historyWordMarkedState {J E X : Type*} (update : J → E → X → X)
    (initial : X) (word : List J) (marks : Fin word.length → E) : X :=
  historyWordState (fun p : J × E => update p.1 p.2) initial
    (List.ofFn (fun i => (word.get i, marks i)))

theorem historyWordMarkedState_eq_heapFold {J E X : Type*}
    (dependent : J → J → Prop) (update : J → E → X → X)
    (initial : X) (word : List J) (marks : Fin word.length → E) :
    historyWordMarkedState update initial word marks =
      (List.ofFn (fun i : Fin word.length => (⟨i⟩ : WordHeapPiece word dependent))).foldl
        (fun state x => update (wordHeapLabel x) (marks x.position) state) initial := by
  unfold historyWordMarkedState historyWordState
  have heq : (List.ofFn (fun i : Fin word.length => (word.get i, marks i))) =
      (List.ofFn (fun i : Fin word.length => (⟨i⟩ : WordHeapPiece word dependent))).map
        (fun x => (wordHeapLabel x, marks x.position)) := by
    rw [List.map_ofFn]
    rfl
  rw [heq, List.foldl_map]

/-- Any actual labelled heap isomorphism transports all marks and the raw
folded state exactly. Representative invariance is a proved conclusion. -/
theorem historyHeapMarkEquiv_state {J E X : Type*} [MeasurableSpace E]
    (dependent : J → J → Prop)
    (hsymm : ∀ ⦃a b⦄, dependent a b → dependent b a)
    (update : J → E → X → X)
    (hcomm : ∀ j k, ¬ dependent j k → ∀ e f state,
      update k f (update j e state) = update j e (update k f state))
    {u v : List J} (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent)
    (he : ∀ x, wordHeapLabel (e x) = wordHeapLabel x)
    (initial : X) (marks : Fin u.length → E) :
    historyWordMarkedState update initial v (historyHeapMarkEquiv e marks) =
      historyWordMarkedState update initial u marks := by
  classical
  let l := List.ofFn (fun i : Fin u.length => (⟨i⟩ : WordHeapPiece u dependent))
  let l' := List.ofFn (fun i : Fin v.length => e.symm (⟨i⟩ : WordHeapPiece v dependent))
  have hlnd : l.Nodup := List.nodup_ofFn.mpr (fun _ _ h => congrArg WordHeapPiece.position h)
  have hl'nd : l'.Nodup := List.nodup_ofFn.mpr (fun _ _ h =>
    congrArg WordHeapPiece.position (e.symm.injective h))
  have hp : l.Perm l' := (List.perm_ext_iff_of_nodup hlnd hl'nd).mpr (by
    intro x
    constructor
    · intro _
      apply List.mem_ofFn.mpr
      exact ⟨(e x).position, by
        have hx : (⟨(e x).position⟩ : WordHeapPiece v dependent) = e x := by cases e x; rfl
        rw [hx, e.symm_apply_apply]⟩
    · intro _
      apply List.mem_ofFn.mpr
      exact ⟨x.position, by cases x; rfl⟩)
  have hl : l.Pairwise (fun x y => ¬ y ≤ x) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij hle
    simp only [l, List.getElem_ofFn] at hle
    have hh := wordHeap_reachable_position_le hle
    exact (Nat.not_le_of_lt hij) hh
  have hl' : l'.Pairwise (fun x y => ¬ y ≤ x) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij hle
    simp only [l', List.getElem_ofFn] at hle
    have hh := wordHeap_reachable_position_le (e.monotone hle)
    simp only [OrderIso.apply_symm_apply] at hh
    exact (Nat.not_le_of_lt hij) hh
  let action := fun (x : WordHeapPiece u dependent) state =>
    update (wordHeapLabel x) (marks x.position) state
  have hfold := historyFold_linear_extension_invariant
    (fun x y : WordHeapPiece u dependent => dependent (wordHeapLabel x) (wordHeapLabel y)) action
    (fun _ _ => wordHeap_dependent_comparable hsymm)
    (fun x y h state => hcomm _ _ h _ _ state) hp hl hl' initial
  rw [historyWordMarkedState_eq_heapFold dependent update initial u marks]
  rw [hfold]
  rw [historyWordMarkedState_eq_heapFold dependent update initial v (historyHeapMarkEquiv e marks)]
  have hmap : l' = (List.ofFn (fun i : Fin v.length => (⟨i⟩ : WordHeapPiece v dependent))).map e.symm := by
    rw [List.map_ofFn]
    rfl
  rw [hmap, List.foldl_map]
  congr 1
  funext state x
  have hlabel := he (e.symm x)
  have hmark := historyHeapMarkEquiv_position e marks (e.symm x)
  simp only [OrderIso.apply_symm_apply] at hlabel hmark
  simp only [action, hlabel, hmark]

end NearlyMinimax
