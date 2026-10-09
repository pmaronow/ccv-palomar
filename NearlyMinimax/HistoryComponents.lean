module

public import NearlyMinimax.HistoryUpperSets
public import NearlyMinimax.HistoryGas


@[expose] public section

/-!
# Connected upper-subset components

Connectivity is the equivalence closure of comparability edges inside the
finite subset. This is a concrete finite construction. Components of an upper
set are upper, pairwise disjoint and incomparable, and their order weights
multiply. The separate cover-chain bridge identifies these with components of
the heap's bounded-degree cover graph.
-/

noncomputable section
namespace NearlyMinimax

variable {α : Type*} [PartialOrder α] [DecidableEq α]

def historyComparableEdge (U : Finset α) (a b : α) : Prop :=
  a ∈ U ∧ b ∈ U ∧ (a ≤ b ∨ b ≤ a)

def HistoryConnected (U : Finset α) (a b : α) : Prop :=
  Relation.EqvGen (historyComparableEdge U) a b

def historyComponent (U : Finset α) (a : α) : Finset α := by
  classical
  exact U.filter (HistoryConnected U a)

omit [DecidableEq α] in
theorem mem_historyComponent {U : Finset α} {a b : α} :
    b ∈ historyComponent U a ↔ b ∈ U ∧ HistoryConnected U a b := by
  classical
  exact Finset.mem_filter

omit [DecidableEq α] in
theorem historyComponent_subset (U : Finset α) (a : α) : historyComponent U a ⊆ U :=
  fun _ h => (mem_historyComponent.1 h).1

omit [DecidableEq α] in
theorem self_mem_historyComponent {U : Finset α} {a : α} (ha : a ∈ U) :
    a ∈ historyComponent U a := mem_historyComponent.2 ⟨ha, .refl _⟩

omit [DecidableEq α] in
theorem historyComponent_eq_of_connected {U : Finset α} {a b : α}
    (h : HistoryConnected U a b) : historyComponent U a = historyComponent U b := by
  ext x
  rw [mem_historyComponent, mem_historyComponent]
  constructor
  · rintro ⟨hx, hax⟩
    exact ⟨hx, .trans _ _ _ (.symm _ _ h) hax⟩
  · rintro ⟨hx, hbx⟩
    exact ⟨hx, .trans _ _ _ h hbx⟩

theorem historyComponent_eq_of_inter {U : Finset α} {a b : α}
    (h : (historyComponent U a ∩ historyComponent U b).Nonempty) :
    historyComponent U a = historyComponent U b := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨hxa, hxb⟩ := Finset.mem_inter.1 hx
  apply historyComponent_eq_of_connected
  exact .trans _ _ _ (mem_historyComponent.1 hxa).2 (.symm _ _ (mem_historyComponent.1 hxb).2)

omit [DecidableEq α] in
omit [DecidableEq α] in
theorem historyComponent_connected_lift {U : Finset α} {r a b : α}
    (h : HistoryConnected U a b) :
    HistoryConnected U r a → HistoryConnected (historyComponent U r) a b := by
  induction h with
  | rel a b hab =>
    intro hra
    apply Relation.EqvGen.rel
    exact ⟨mem_historyComponent.2 ⟨hab.1, hra⟩,
      mem_historyComponent.2 ⟨hab.2.1, .trans _ _ _ hra (.rel _ _ hab)⟩, hab.2.2⟩
  | refl a => intro _; exact .refl _
  | symm a b hab ih =>
    intro hrb
    exact .symm _ _ (ih (.trans _ _ _ hrb (.symm _ _ hab)))
  | trans a b c hab hbc ihab ihbc =>
    intro hra
    exact .trans _ _ _ (ihab hra) (ihbc (.trans _ _ _ hra hab))

def IsConnectedHistorySubset (U : Finset α) : Prop :=
  U.Nonempty ∧ ∀ a ∈ U, ∀ b ∈ U, HistoryConnected U a b

omit [DecidableEq α] in
theorem historyComponent_connected {U : Finset α} {r : α} (hr : r ∈ U) :
    IsConnectedHistorySubset (historyComponent U r) := by
  refine ⟨⟨r, self_mem_historyComponent hr⟩, ?_⟩
  intro a ha b hb
  have hra := (mem_historyComponent.1 ha).2
  have hrb := (mem_historyComponent.1 hb).2
  exact historyComponent_connected_lift (.trans _ _ _ (.symm _ _ hra) hrb) hra

omit [DecidableEq α] in
theorem historyComponent_upper {S U : Finset α} (hU : IsHistoryUpper S U) (r : α) :
    IsHistoryUpper S (historyComponent U r) := by
  refine ⟨(historyComponent_subset U r).trans hU.1, ?_⟩
  intro a ha b hb hab
  obtain ⟨haU, hra⟩ := mem_historyComponent.1 ha
  have hbU := hU.2 a haU b hb hab
  exact mem_historyComponent.2 ⟨hbU, .trans _ _ _ hra (.rel _ _ ⟨haU, hbU, Or.inl hab⟩)⟩

def historyComponents (U : Finset α) : Finset (Finset α) := U.image (historyComponent U)

theorem mem_historyComponents {U P : Finset α} :
    P ∈ historyComponents U ↔ ∃ r ∈ U, historyComponent U r = P := Finset.mem_image

theorem historyComponents_nonempty {U P : Finset α} (hP : P ∈ historyComponents U) : P.Nonempty := by
  obtain ⟨r, hr, rfl⟩ := mem_historyComponents.1 hP
  exact ⟨r, self_mem_historyComponent hr⟩

theorem historyComponents_subset {U P : Finset α} (hP : P ∈ historyComponents U) : P ⊆ U := by
  obtain ⟨r, _, rfl⟩ := mem_historyComponents.1 hP
  exact historyComponent_subset U r

theorem historyComponents_connected {U P : Finset α} (hP : P ∈ historyComponents U) :
    IsConnectedHistorySubset P := by
  obtain ⟨r, hr, rfl⟩ := mem_historyComponents.1 hP
  exact historyComponent_connected hr

theorem historyComponents_upper {S U P : Finset α} (hU : IsHistoryUpper S U)
    (hP : P ∈ historyComponents U) : IsHistoryUpper S P := by
  obtain ⟨r, _, rfl⟩ := mem_historyComponents.1 hP
  exact historyComponent_upper hU r

theorem historyComponents_pairwise_disjoint (U : Finset α) :
    ∀ P ∈ historyComponents U, ∀ Q ∈ historyComponents U, P ≠ Q → Disjoint P Q := by
  intro P hP Q hQ hpq
  obtain ⟨p, _, rfl⟩ := mem_historyComponents.1 hP
  obtain ⟨q, _, rfl⟩ := mem_historyComponents.1 hQ
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
  exact fun hi => hpq (historyComponent_eq_of_inter hi)

theorem historyComponents_biUnion (U : Finset α) : (historyComponents U).biUnion id = U := by
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨P, hP, hx⟩
    exact historyComponents_subset hP hx
  · intro hx
    exact ⟨historyComponent U x, mem_historyComponents.2 ⟨x, hx, rfl⟩, self_mem_historyComponent hx⟩

theorem historyComponents_incomparable {S U : Finset α} (hU : IsHistoryUpper S U) :
    ∀ P ∈ historyComponents U, ∀ Q ∈ historyComponents U, P ≠ Q → IncomparableHistoryParts P Q := by
  intro P hP Q hQ hpq
  exact historyUpper_disjoint_incomparable (historyComponents_upper hU hP) (historyComponents_upper hU hQ)
    (historyComponents_pairwise_disjoint U P hP Q hQ hpq)

theorem historyUpper_biUnion {S : Finset α} {F : Finset (Finset α)}
    (hF : ∀ P ∈ F, IsHistoryUpper S P) : IsHistoryUpper S (F.biUnion id) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hx
    exact (hF P hP).1 hxP
  · intro x hx y hy hxy
    obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hx
    exact Finset.mem_biUnion.2 ⟨P, hP, (hF P hP).2 x hxP y hy hxy⟩

theorem historyComponentWeight_biUnion (weight : α → ℝ) (ρ t : ℝ)
    {S : Finset α} (F : Finset (Finset α)) (hF : ∀ P ∈ F, IsHistoryUpper S P)
    (hdis : ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → Disjoint P Q) :
    historyComponentWeight weight ρ t (F.biUnion id) = ∏ P ∈ F, historyComponentWeight weight ρ t P := by
  induction F using Finset.induction_on with
  | empty => simp [historyComponentWeight]
  | @insert P F hPF ih =>
    have hFin : ∀ Q ∈ F, IsHistoryUpper S Q := fun Q hQ => hF Q (Finset.mem_insert_of_mem hQ)
    have hFinDis : ∀ Q ∈ F, ∀ R ∈ F, Q ≠ R → Disjoint Q R :=
      fun Q hQ R hR hQR => hdis Q (Finset.mem_insert_of_mem hQ) R (Finset.mem_insert_of_mem hR) hQR
    have hPdis : Disjoint P (F.biUnion id) := by
      apply Finset.disjoint_left.2
      intro x hxP hxF
      obtain ⟨Q, hQ, hxQ⟩ := Finset.mem_biUnion.1 hxF
      have hPQ : P ≠ Q := fun heq => hPF (heq ▸ hQ)
      exact Finset.disjoint_left.1 (hdis P (Finset.mem_insert_self _ _) Q
        (Finset.mem_insert_of_mem hQ) hPQ) hxP hxQ
    have hinc := historyUpper_disjoint_incomparable (hF P (Finset.mem_insert_self _ _))
      (historyUpper_biUnion hFin) hPdis
    rw [Finset.biUnion_insert, id_eq, historyComponentWeight_union weight ρ t hinc,
      Finset.prod_insert hPF, ih hFin hFinDis]

/-- The actual weight of an upper set is the product of its connected weights. -/
theorem historyComponentWeight_eq_component_prod (weight : α → ℝ) (ρ t : ℝ)
    {S U : Finset α} (hU : IsHistoryUpper S U) :
    historyComponentWeight weight ρ t U =
      ∏ P ∈ historyComponents U, historyComponentWeight weight ρ t P := by
  calc
    _ = historyComponentWeight weight ρ t ((historyComponents U).biUnion id) := by
      rw [historyComponents_biUnion]
    _ = _ := historyComponentWeight_biUnion weight ρ t (historyComponents U)
      (fun _ hP => historyComponents_upper hU hP) (historyComponents_pairwise_disjoint U)

def historyUpperPolymers (S : Finset α) : Finset (Finset α) := by
  classical
  exact (historyUpperSets S).filter IsConnectedHistorySubset

omit [DecidableEq α] in
theorem mem_historyUpperPolymers {S P : Finset α} :
    P ∈ historyUpperPolymers S ↔ IsHistoryUpper S P ∧ IsConnectedHistorySubset P := by
  classical
  simp only [historyUpperPolymers, Finset.mem_filter, mem_historyUpperSets]

theorem historyUpperPolymer_support_nonempty {S P : Finset α} (hP : P ∈ historyUpperPolymers S) :
    (historyMaximalPieces P).Nonempty :=
  historyUpper_nonempty_maximal (mem_historyUpperPolymers.1 hP).1 (mem_historyUpperPolymers.1 hP).2.1

theorem historyComponents_mem_gas {S U : Finset α} (hU : IsHistoryUpper S U) :
    historyComponents U ∈ historyGasFamilies (historyUpperPolymers S) historyMaximalPieces (historyMaximalPieces U) := by
  rw [mem_historyGasFamilies]
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    exact mem_historyUpperPolymers.2 ⟨historyComponents_upper hU hP, historyComponents_connected hP⟩
  · intro P hP Q hQ hpq
    exact (historyUpper_disjoint_iff (historyComponents_upper hU hP)
      (historyComponents_upper hU hQ)).1 (historyComponents_pairwise_disjoint U P hP Q hQ hpq)
  · intro P hP
    obtain ⟨r, _, rfl⟩ := mem_historyComponents.1 hP
    exact historyUpper_maximal_subset (historyComponent_upper ⟨Finset.Subset.refl _,
      fun _ _ _ hy _ => hy⟩ r)

omit [DecidableEq α] in
theorem historyConnected_mono {P U : Finset α} (hsub : P ⊆ U) {a b : α}
    (h : HistoryConnected P a b) : HistoryConnected U a b :=
  Relation.EqvGen.mono (r := historyComparableEdge P) (p := historyComparableEdge U)
    (fun _ _ hab => ⟨hsub hab.1, hsub hab.2.1, hab.2.2⟩) a b h

theorem historyConnected_preserves_incomparable_part {P Q : Finset α}
    (hinc : IncomparableHistoryParts P Q) {a b : α} (h : HistoryConnected (P ∪ Q) a b) :
    a ∈ P ↔ b ∈ P := by
  induction h with
  | rel a b hab =>
    constructor
    · intro haP
      rcases Finset.mem_union.1 hab.2.1 with hbP | hbQ
      · exact hbP
      · exact hab.2.2.elim
          (fun hab => ((hinc a haP b hbQ).1 hab).elim)
          (fun hba => ((hinc a haP b hbQ).2 hba).elim)
    · intro hbP
      rcases Finset.mem_union.1 hab.1 with haP | haQ
      · exact haP
      · exact hab.2.2.elim
          (fun hab => ((hinc b hbP a haQ).2 hab).elim)
          (fun hba => ((hinc b hbP a haQ).1 hba).elim)
  | refl a => exact Iff.rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

theorem historyComponent_incomparable_union {P Q : Finset α}
    (hinc : IncomparableHistoryParts P Q) (hP : IsConnectedHistorySubset P) {p : α} (hp : p ∈ P) :
    historyComponent (P ∪ Q) p = P := by
  ext x
  constructor
  · intro hx
    exact (historyConnected_preserves_incomparable_part hinc (mem_historyComponent.1 hx).2).1 hp
  · intro hx
    exact mem_historyComponent.2 ⟨Finset.mem_union_left _ hx,
      historyConnected_mono Finset.subset_union_left (hP.2 p hp x hx)⟩

theorem historyGasFamily_piece_disjoint {S R : Finset α} {F : Finset (Finset α)}
    (hF : F ∈ historyGasFamilies (historyUpperPolymers S) historyMaximalPieces R) :
    ∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → Disjoint P Q := by
  obtain ⟨hFP, hc, _⟩ := mem_historyGasFamilies.1 hF
  intro P hP Q hQ hpq
  exact (historyUpper_disjoint_iff (mem_historyUpperPolymers.1 (hFP hP)).1
    (mem_historyUpperPolymers.1 (hFP hQ)).1).2 (hc P hP Q hQ hpq)

theorem historyGasFamily_biUnion_upper {S R : Finset α} {F : Finset (Finset α)}
    (hF : F ∈ historyGasFamilies (historyUpperPolymers S) historyMaximalPieces R) :
    IsHistoryUpper S (F.biUnion id) := by
  exact historyUpper_biUnion (fun _ hP => (mem_historyUpperPolymers.1 ((mem_historyGasFamilies.1 hF).1 hP)).1)

theorem historyGasFamily_component_at {S R : Finset α} {F : Finset (Finset α)}
    (hF : F ∈ historyGasFamilies (historyUpperPolymers S) historyMaximalPieces R)
    {P : Finset α} (hP : P ∈ F) {p : α} (hp : p ∈ P) :
    historyComponent (F.biUnion id) p = P := by
  have hupper : ∀ Q ∈ F, IsHistoryUpper S Q :=
    fun _ hQ => (mem_historyUpperPolymers.1 ((mem_historyGasFamilies.1 hF).1 hQ)).1
  have hdis : Disjoint P ((F.erase P).biUnion id) := by
    apply Finset.disjoint_left.2
    intro x hxP hxF
    obtain ⟨Q, hQ, hxQ⟩ := Finset.mem_biUnion.1 hxF
    obtain ⟨hQP, hQF⟩ := Finset.mem_erase.1 hQ
    exact Finset.disjoint_left.1 (historyGasFamily_piece_disjoint hF P hP Q hQF hQP.symm) hxP hxQ
  have hinc := historyUpper_disjoint_incomparable (hupper P hP)
    (historyUpper_biUnion (fun Q hQ => hupper Q (Finset.mem_of_mem_erase hQ))) hdis
  have hUnion : F.biUnion id = P ∪ (F.erase P).biUnion id := by
    conv_lhs => rw [← Finset.insert_erase hP]
    rw [Finset.biUnion_insert, id_eq]
  rw [hUnion]
  exact historyComponent_incomparable_union hinc
    (mem_historyUpperPolymers.1 ((mem_historyGasFamilies.1 hF).1 hP)).2 hp

/-- Compatible connected upper families are exactly the components of their union. -/
theorem historyGasFamily_components_biUnion {S R : Finset α} {F : Finset (Finset α)}
    (hF : F ∈ historyGasFamilies (historyUpperPolymers S) historyMaximalPieces R) :
    historyComponents (F.biUnion id) = F := by
  ext P
  constructor
  · intro hP
    obtain ⟨p, hp, rfl⟩ := mem_historyComponents.1 hP
    obtain ⟨Q, hQ, hpQ⟩ := Finset.mem_biUnion.1 hp
    rw [historyGasFamily_component_at hF hQ hpQ]
    exact hQ
  · intro hP
    have hPP := (mem_historyUpperPolymers.1 ((mem_historyGasFamilies.1 hF).1 hP)).2.1
    obtain ⟨p, hp⟩ := hPP
    exact mem_historyComponents.2 ⟨p, Finset.mem_biUnion.2 ⟨P, hP, hp⟩,
      historyGasFamily_component_at hF hP hp⟩

def historyRestrictedUpperSets (S R : Finset α) : Finset (Finset α) := by
  classical
  exact (historyUpperSets S).filter (fun U => historyMaximalPieces U ⊆ R)

theorem mem_historyRestrictedUpperSets {S R U : Finset α} :
    U ∈ historyRestrictedUpperSets S R ↔ IsHistoryUpper S U ∧ historyMaximalPieces U ⊆ R := by
  classical
  simp only [historyRestrictedUpperSets, Finset.mem_filter, mem_historyUpperSets]

theorem historyRestrictedUpperSets_components_gas {S R U : Finset α}
    (hU : U ∈ historyRestrictedUpperSets S R) :
    historyComponents U ∈ historyGasFamilies (historyUpperPolymers S) historyMaximalPieces R := by
  obtain ⟨hupper, hmax⟩ := mem_historyRestrictedUpperSets.1 hU
  obtain ⟨hcP, hcompat, hcSupport⟩ := mem_historyGasFamilies.1 (historyComponents_mem_gas hupper)
  exact mem_historyGasFamilies.2 ⟨hcP, hcompat, fun P hP => (hcSupport P hP).trans hmax⟩

theorem historyGasFamily_biUnion_restricted {S R : Finset α} {F : Finset (Finset α)}
    (hF : F ∈ historyGasFamilies (historyUpperPolymers S) historyMaximalPieces R) :
    F.biUnion id ∈ historyRestrictedUpperSets S R := by
  apply mem_historyRestrictedUpperSets.2
  refine ⟨historyGasFamily_biUnion_upper hF, ?_⟩
  intro x hx
  obtain ⟨hxU, hm⟩ := mem_historyMaximalPieces.1 hx
  obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hxU
  have hxmaxP : x ∈ historyMaximalPieces P := mem_historyMaximalPieces.2 ⟨hxP, fun y hy hxy =>
    hm y (Finset.mem_biUnion.2 ⟨P, hP, hy⟩) hxy⟩
  exact (mem_historyGasFamilies.1 hF).2.2 P hP hxmaxP

def historyRestrictedUpperDensity (weight : α → ℝ) (ρ t : ℝ) (S R : Finset α) : ℝ :=
  ∑ U ∈ historyRestrictedUpperSets S R, historyComponentWeight weight ρ t U

/-- The actual restricted upper-set density equals the concrete finite component gas. -/
theorem historyRestrictedUpperDensity_eq_gas (weight : α → ℝ) (ρ t : ℝ) (S R : Finset α) :
    historyRestrictedUpperDensity weight ρ t S R =
      historyGasPartition (historyUpperPolymers S) historyMaximalPieces
        (historyComponentWeight weight ρ t) R := by
  unfold historyRestrictedUpperDensity historyGasPartition
  apply Finset.sum_bij (fun U _ => historyComponents U)
  · intro U hU
    exact historyRestrictedUpperSets_components_gas hU
  · intro U hU V hV hUV
    have hh := congrArg (fun F : Finset (Finset α) => F.biUnion id) hUV
    simpa only [historyComponents_biUnion] using hh
  · intro F hF
    exact ⟨F.biUnion id, historyGasFamily_biUnion_restricted hF, historyGasFamily_components_biUnion hF⟩
  · intro U hU
    exact historyComponentWeight_eq_component_prod weight ρ t (mem_historyRestrictedUpperSets.1 hU).1

theorem historyRestrictedUpperSets_full (S : Finset α) :
    historyRestrictedUpperSets S (historyMaximalPieces S) = historyUpperSets S := by
  ext U
  rw [mem_historyRestrictedUpperSets, mem_historyUpperSets]
  exact ⟨fun h => h.1, fun h => ⟨h, historyUpper_maximal_subset h⟩⟩

/-- The unrestricted source density is the actual connected-upper component gas. -/
theorem historyScaledUpperDensity_eq_gas (weight : α → ℝ) (ρ t : ℝ) (S : Finset α) :
    historyScaledUpperDensity weight ρ S t =
      historyGasPartition (historyUpperPolymers S) historyMaximalPieces
        (historyComponentWeight weight ρ t) (historyMaximalPieces S) := by
  rw [← historyRestrictedUpperDensity_eq_gas, historyRestrictedUpperDensity,
    historyRestrictedUpperSets_full, historyScaledUpperDensity_eq_components]

/-- The actual source restricted sum satisfies deletion by its actual connected upper subsets. -/
theorem historyRestrictedUpperDensity_deletion (weight : α → ℝ) (ρ t : ℝ) (S R : Finset α) (x : α) :
    historyRestrictedUpperDensity weight ρ t S R =
      historyRestrictedUpperDensity weight ρ t S (R.erase x) +
        ∑ P ∈ historyGasRows (historyUpperPolymers S) historyMaximalPieces R x,
          historyComponentWeight weight ρ t P * historyRestrictedUpperDensity weight ρ t S (R \ historyMaximalPieces P) := by
  simp_rw [historyRestrictedUpperDensity_eq_gas]
  exact historyGasPartition_deletion (historyUpperPolymers S) historyMaximalPieces
    (historyComponentWeight weight ρ t) R x

/-- Positivity of the actual upper-set density follows from its explicit connected-set activity sum. -/
theorem historyRestrictedUpperDensity_positive (weight : α → ℝ) (ρ t : ℝ) (S : Finset α)
    (hactivity : ∀ R x, x ∈ R →
      (∑ P ∈ historyGasRows (historyUpperPolymers S) historyMaximalPieces R x,
        |historyComponentWeight weight ρ t P| * (2 : ℝ) ^ ((historyMaximalPieces P).card - 1)) ≤ 1 / 2) :
    ∀ R, 0 < historyRestrictedUpperDensity weight ρ t S R ∧ ∀ x ∈ R,
      historyRestrictedUpperDensity weight ρ t S (R.erase x) / 2 ≤ historyRestrictedUpperDensity weight ρ t S R ∧
      historyRestrictedUpperDensity weight ρ t S R ≤ 3 / 2 * historyRestrictedUpperDensity weight ρ t S (R.erase x) := by
  simp_rw [historyRestrictedUpperDensity_eq_gas]
  exact historyGasPartition_positive (historyUpperPolymers S) historyMaximalPieces
    (historyComponentWeight weight ρ t) (fun _ hP => historyUpperPolymer_support_nonempty hP) hactivity

end NearlyMinimax
