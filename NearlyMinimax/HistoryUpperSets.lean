module

public import NearlyMinimax.HistoryOrderVolume


@[expose] public section

/-!
# Upper subsets of a finite history

The actual finite upper-subset sum uses the combinatorial order-volume
coefficients from `HistoryOrderVolume`. Maximal deletion is reindexed by a
proved insertion/erasure bijection. No density derivative is assumed.
-/

noncomputable section
namespace NearlyMinimax

variable {α : Type*} [PartialOrder α] [DecidableEq α]

def IsHistoryUpper (S U : Finset α) : Prop :=
  U ⊆ S ∧ ∀ x ∈ U, ∀ y ∈ S, x ≤ y → y ∈ U

def historyUpperSets (S : Finset α) : Finset (Finset α) := by
  classical
  exact S.powerset.filter (IsHistoryUpper S)

omit [DecidableEq α] in
theorem mem_historyUpperSets {S U : Finset α} :
    U ∈ historyUpperSets S ↔ IsHistoryUpper S U := by
  classical
  simp only [historyUpperSets, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

omit [DecidableEq α] in
@[simp] theorem empty_historyUpper (S : Finset α) : IsHistoryUpper S ∅ := by
  simp [IsHistoryUpper]

omit [DecidableEq α] in
@[simp] theorem empty_mem_historyUpperSets (S : Finset α) : ∅ ∈ historyUpperSets S :=
  mem_historyUpperSets.2 (empty_historyUpper S)

theorem historyUpper_maximal_subset {S U : Finset α} (hU : IsHistoryUpper S U) :
    historyMaximalPieces U ⊆ historyMaximalPieces S := by
  intro x hx
  obtain ⟨hxU, hmax⟩ := mem_historyMaximalPieces.1 hx
  apply mem_historyMaximalPieces.2
  exact ⟨hU.1 hxU, fun y hy hxy => hmax y (hU.2 x hxU y hy hxy) hxy⟩

theorem historyUpper_maximal_eq_inter {S U : Finset α} (hU : IsHistoryUpper S U) :
    historyMaximalPieces U = U ∩ historyMaximalPieces S := by
  ext x
  constructor
  · intro hx
    exact Finset.mem_inter.2 ⟨historyMaximalPieces_subset U hx, historyUpper_maximal_subset hU hx⟩
  · intro hx
    obtain ⟨hxU, hxS⟩ := Finset.mem_inter.1 hx
    exact mem_historyMaximalPieces.2 ⟨hxU, fun y hy hxy =>
      (mem_historyMaximalPieces.1 hxS).2 y (hU.1 hy) hxy⟩

theorem historyUpper_erase {S U : Finset α} (hU : IsHistoryUpper S U) {x : α}
    (_hx : x ∈ historyMaximalPieces U) : IsHistoryUpper (S.erase x) (U.erase x) := by
  refine ⟨Finset.erase_subset_erase _ hU.1, ?_⟩
  intro a ha b hb hab
  exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hb).1,
    hU.2 a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab⟩

theorem historyUpper_insert {S U : Finset α} {x : α}
    (hx : x ∈ historyMaximalPieces S) (hU : IsHistoryUpper (S.erase x) U) :
    IsHistoryUpper S (insert x U) := by
  obtain ⟨hxS, hmax⟩ := mem_historyMaximalPieces.1 hx
  refine ⟨Finset.insert_subset hxS (hU.1.trans (Finset.erase_subset _ _)), ?_⟩
  intro a ha b hb hab
  rcases Finset.mem_insert.1 ha with rfl | haU
  · rw [hmax b hb hab]
    exact Finset.mem_insert_self _ _
  · by_cases hbx : b = x
    · subst b; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hU.2 a haU b (Finset.mem_erase.2 ⟨hbx, hb⟩) hab)

theorem historyUpper_maximal_insert {S U : Finset α} {x : α}
    (hx : x ∈ historyMaximalPieces S) (hU : IsHistoryUpper (S.erase x) U) :
    x ∈ historyMaximalPieces (insert x U) := by
  apply mem_historyMaximalPieces.2
  refine ⟨Finset.mem_insert_self _ _, ?_⟩
  intro y hy hxy
  exact (mem_historyMaximalPieces.1 hx).2 y ((historyUpper_insert hx hU).1 hy) hxy

theorem historyUpper_not_mem_deleted {S U : Finset α} {x : α}
    (hU : IsHistoryUpper (S.erase x) U) : x ∉ U := by
  intro hxU
  exact Finset.notMem_erase x S (hU.1 hxU)

omit [DecidableEq α] in
theorem historyUpper_disjoint_incomparable {S P Q : Finset α}
    (hP : IsHistoryUpper S P) (hQ : IsHistoryUpper S Q) (hdis : Disjoint P Q) :
    IncomparableHistoryParts P Q := by
  intro p hp q hq
  refine ⟨?_, ?_⟩
  · intro hpq
    exact Finset.disjoint_left.1 hdis (hP.2 p hp q (hQ.1 hq) hpq) hq
  · intro hqp
    exact Finset.disjoint_left.1 hdis hp (hQ.2 q hq p (hP.1 hp) hqp)

theorem historyUpper_nonempty_maximal {S U : Finset α} (_hU : IsHistoryUpper S U)
    (hne : U.Nonempty) : (historyMaximalPieces U).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := U.exists_maximal hne
  refine ⟨x, mem_historyMaximalPieces.2 ⟨hx, ?_⟩⟩
  intro y hy hxy
  exact le_antisymm (hmax hy hxy) hxy

theorem historyUpper_inter_iff_maximal_inter {S P Q : Finset α}
    (hP : IsHistoryUpper S P) (hQ : IsHistoryUpper S Q) :
    (P ∩ Q).Nonempty ↔ (historyMaximalPieces P ∩ historyMaximalPieces Q).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hxP, hxQ⟩ := Finset.mem_inter.1 hx
    obtain ⟨y, hxy, hyS, hmax⟩ := S.exists_le_maximal (hP.1 hxP)
    have hyP := hP.2 x hxP y hyS hxy
    have hyQ := hQ.2 x hxQ y hyS hxy
    have hymax : y ∈ historyMaximalPieces S :=
      mem_historyMaximalPieces.2 ⟨hyS, fun z hz hyz => le_antisymm (hmax hz hyz) hyz⟩
    refine ⟨y, Finset.mem_inter.2 ⟨?_, ?_⟩⟩
    · rw [historyUpper_maximal_eq_inter hP]; exact Finset.mem_inter.2 ⟨hyP, hymax⟩
    · rw [historyUpper_maximal_eq_inter hQ]; exact Finset.mem_inter.2 ⟨hyQ, hymax⟩
  · rintro ⟨x, hx⟩
    obtain ⟨hxP, hxQ⟩ := Finset.mem_inter.1 hx
    exact ⟨x, Finset.mem_inter.2 ⟨historyMaximalPieces_subset P hxP,
      historyMaximalPieces_subset Q hxQ⟩⟩

theorem historyUpper_disjoint_iff {S P Q : Finset α}
    (hP : IsHistoryUpper S P) (hQ : IsHistoryUpper S Q) :
    Disjoint P Q ↔ Disjoint (historyMaximalPieces P) (historyMaximalPieces Q) := by
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_iff_inter_eq_empty,
    ← Finset.not_nonempty_iff_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
  exact not_congr (historyUpper_inter_iff_maximal_inter hP hQ)

/-- The upper-subset maximal-deletion sum is an actual finite bijection. -/
theorem historyUpper_maximal_sum (S : Finset α) (F : Finset α → α → ℝ) :
    (∑ U ∈ historyUpperSets S, ∑ x ∈ historyMaximalPieces U, F U x) =
      ∑ x ∈ historyMaximalPieces S, ∑ U ∈ historyUpperSets (S.erase x), F (insert x U) x := by
  classical
  suffices hh :
      (∑ i ∈ (historyUpperSets S).sigma historyMaximalPieces, F i.1 i.2) =
        ∑ i ∈ (historyMaximalPieces S).sigma (fun x => historyUpperSets (S.erase x)),
          F (insert i.1 i.2) i.1 by
    simpa only [Finset.sum_sigma] using hh
  apply Finset.sum_bij (fun i _ => ⟨i.2, i.1.erase i.2⟩)
  · intro i hi
    obtain ⟨hiU, hix⟩ := Finset.mem_sigma.1 hi
    have hU := mem_historyUpperSets.1 hiU
    exact Finset.mem_sigma.2 ⟨historyUpper_maximal_subset hU hix,
      mem_historyUpperSets.2 (historyUpper_erase hU hix)⟩
  · intro i hi j hj heq
    obtain ⟨hiU, hix⟩ := Finset.mem_sigma.1 hi
    obtain ⟨hjU, hjx⟩ := Finset.mem_sigma.1 hj
    have hx : i.2 = j.2 := congrArg Sigma.fst heq
    have hrest : i.1.erase i.2 = j.1.erase j.2 :=
      congrArg (fun z : Sigma (fun _ : α => Finset α) => z.2) heq
    have hwhole : i.1 = j.1 := by
      rw [← Finset.insert_erase (historyMaximalPieces_subset i.1 hix),
        ← Finset.insert_erase (historyMaximalPieces_subset j.1 hjx), hrest, hx]
    cases i
    cases j
    dsimp at hx hwhole
    subst_vars
    rfl
  · intro i hi
    obtain ⟨hix, hiU⟩ := Finset.mem_sigma.1 hi
    have hU := mem_historyUpperSets.1 hiU
    refine ⟨⟨insert i.1 i.2, i.1⟩, Finset.mem_sigma.2 ⟨?_, ?_⟩, ?_⟩
    · exact mem_historyUpperSets.2 (historyUpper_insert hix hU)
    · exact historyUpper_maximal_insert hix hU
    · simp only [Finset.erase_insert (historyUpper_not_mem_deleted hU)]
  · intro i hi
    have hx := historyMaximalPieces_subset i.1 (Finset.mem_sigma.1 hi).2
    rw [Finset.insert_erase hx]

def historyUpperDensity (weight : α → ℝ) (S : Finset α) (t : ℝ) : ℝ :=
  ∑ U ∈ historyUpperSets S, t ^ U.card * historyOrderVolume U * ∏ x ∈ U, weight x

@[simp] theorem historyUpperDensity_at_zero (weight : α → ℝ) (S : Finset α) :
    historyUpperDensity weight S 0 = 1 := by
  unfold historyUpperDensity
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro U hU hne
    simp only [zero_pow (Finset.card_ne_zero.2 (Finset.nonempty_iff_ne_empty.2 hne)), zero_mul]
  · simp

theorem historyUpperDensity_derivative_formula (weight : α → ℝ) (S : Finset α) (t : ℝ) :
    HasDerivAt (historyUpperDensity weight S)
      (∑ U ∈ historyUpperSets S,
        ((U.card : ℝ) * t ^ (U.card - 1)) * historyOrderVolume U * ∏ x ∈ U, weight x) t := by
  apply HasDerivAt.fun_sum
  intro U hU
  simpa only [id_eq, mul_one] using! ((hasDerivAt_id t).pow U.card).mul_const
    (historyOrderVolume U) |>.mul_const (∏ x ∈ U, weight x)

theorem historyUpperDensity_term_derivative (weight : α → ℝ) (U : Finset α) (t : ℝ) :
    ((U.card : ℝ) * t ^ (U.card - 1)) * historyOrderVolume U * (∏ x ∈ U, weight x) =
      ∑ x ∈ historyMaximalPieces U,
        weight x * (t ^ (U.erase x).card * historyOrderVolume (U.erase x) *
          ∏ y ∈ U.erase x, weight y) := by
  calc
    _ = t ^ (U.card - 1) * ((U.card : ℝ) * historyOrderVolume U) *
        (∏ x ∈ U, weight x) := by ring
    _ = t ^ (U.card - 1) * (∑ x ∈ historyMaximalPieces U, historyOrderVolume (U.erase x)) *
        (∏ x ∈ U, weight x) := by rw [historyOrderVolume_recursion]
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hxU := historyMaximalPieces_subset U hx
      rw [Finset.card_erase_of_mem hxU, ← Finset.mul_prod_erase U weight hxU]
      ring

/-- The actual finite upper-set sum satisfies the source deletion derivative. -/
theorem historyUpperDensity_hasDerivAt (weight : α → ℝ) (S : Finset α) (t : ℝ) :
    HasDerivAt (historyUpperDensity weight S)
      (∑ x ∈ historyMaximalPieces S, weight x * historyUpperDensity weight (S.erase x) t) t := by
  have hh := historyUpperDensity_derivative_formula weight S t
  simp_rw [historyUpperDensity_term_derivative] at hh
  rw [historyUpper_maximal_sum] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro x hx
  unfold historyUpperDensity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.erase_insert (historyUpper_not_mem_deleted (mem_historyUpperSets.1 hU))]

/-- The deletion enumeration is exactly the finite upper-subset volume sum. -/
theorem historyUpperDensity_eq_deletionPolynomial (weight : α → ℝ) (S : Finset α) (t : ℝ) :
    historyUpperDensity weight S t = historyDeletionPolynomial weight S t := by
  induction S using Finset.strongInductionOn generalizing t
  rename_i S ih
  have hd : ∀ u, HasDerivAt (fun v => historyUpperDensity weight S v -
      historyDeletionPolynomial weight S v) 0 u := by
    intro u
    have hh := (historyUpperDensity_hasDerivAt weight S u).sub
      (historyDeletionPolynomial_hasDerivAt weight S u)
    have hsum : (∑ x ∈ historyMaximalPieces S, weight x * historyUpperDensity weight (S.erase x) u) =
        ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionPolynomial weight (S.erase x) u := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [ih (S.erase x) (Finset.erase_ssubset (historyMaximalPieces_subset S hx)) u]
    rw [hsum, sub_self] at hh
    exact hh
  have hh := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t 0
  simp only [historyUpperDensity_at_zero, historyDeletionPolynomial_at_zero, sub_self] at hh
  exact sub_eq_zero.1 hh

def historyScaledUpperDensity (weight : α → ℝ) (ρ : ℝ) (S : Finset α) (t : ℝ) : ℝ :=
  historyUpperDensity (fun x => weight x / ρ) S t

/-- The source's finite density formula with `rho^{-|U|}` component weights. -/
theorem historyScaledUpperDensity_eq_components (weight : α → ℝ) (ρ : ℝ) (S : Finset α) (t : ℝ) :
    historyScaledUpperDensity weight ρ S t =
      ∑ U ∈ historyUpperSets S, historyComponentWeight weight ρ t U := by
  unfold historyScaledUpperDensity historyUpperDensity historyComponentWeight
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.prod_div_distrib, Finset.prod_const, div_pow]
  ring

/-- Exact finite source deletion equation, including the reference-weight factor. -/
theorem historyScaledUpperDensity_hasDerivAt (weight : α → ℝ) (ρ : ℝ) (S : Finset α) (t : ℝ) :
    HasDerivAt (historyScaledUpperDensity weight ρ S)
      (ρ⁻¹ * ∑ x ∈ historyMaximalPieces S, weight x * historyScaledUpperDensity weight ρ (S.erase x) t) t := by
  unfold historyScaledUpperDensity
  have hh := historyUpperDensity_hasDerivAt (fun x => weight x / ρ) S t
  convert hh using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

end NearlyMinimax
