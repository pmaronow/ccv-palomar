module

public import NearlyMinimax.HistoryPolynomial


@[expose] public section

/-!
# Combinatorial order volumes of finite heap pieces

The normalized maximal-deletion count is the combinatorial order-volume
coefficient. This module proves its finite recursion, positivity bounds, and
factorization across disjoint incomparable parts. The Lebesgue chamber
identification with the paper's geometric definition is a separate bridge.
-/

noncomputable section
namespace NearlyMinimax

variable {α : Type*} [PartialOrder α] [DecidableEq α]

def IncomparableHistoryParts (P Q : Finset α) : Prop :=
  ∀ p ∈ P, ∀ q ∈ Q, ¬ p ≤ q ∧ ¬ q ≤ p

omit [DecidableEq α] in
theorem IncomparableHistoryParts.disjoint {P Q : Finset α} (h : IncomparableHistoryParts P Q) :
    Disjoint P Q := by
  apply Finset.disjoint_left.2
  intro x hxP hxQ
  exact (h x hxP x hxQ).1 le_rfl

omit [DecidableEq α] in
theorem IncomparableHistoryParts.symm {P Q : Finset α} (h : IncomparableHistoryParts P Q) :
    IncomparableHistoryParts Q P := by
  intro q hq p hp
  exact ⟨(h p hp q hq).2, (h p hp q hq).1⟩

theorem historyMaximalPieces_union {P Q : Finset α} (h : IncomparableHistoryParts P Q) :
    historyMaximalPieces (P ∪ Q) = historyMaximalPieces P ∪ historyMaximalPieces Q := by
  classical
  ext x
  rw [mem_historyMaximalPieces, Finset.mem_union]
  constructor
  · rintro ⟨hx, hm⟩
    rcases hx with hxP | hxQ
    · exact Finset.mem_union.2 (Or.inl (mem_historyMaximalPieces.2 ⟨hxP, fun y hy hxy => hm y (Finset.mem_union_left _ hy) hxy⟩))
    · exact Finset.mem_union.2 (Or.inr (mem_historyMaximalPieces.2 ⟨hxQ, fun y hy hxy => hm y (Finset.mem_union_right _ hy) hxy⟩))
  · intro hx
    rcases Finset.mem_union.1 hx with hxP | hxQ
    · obtain ⟨hxP, hm⟩ := mem_historyMaximalPieces.1 hxP
      refine ⟨Or.inl hxP, ?_⟩
      intro y hy hxy
      rcases Finset.mem_union.1 hy with hyP | hyQ
      · exact hm y hyP hxy
      · exact ((h x hxP y hyQ).1 hxy).elim
    · obtain ⟨hxQ, hm⟩ := mem_historyMaximalPieces.1 hxQ
      refine ⟨Or.inr hxQ, ?_⟩
      intro y hy hxy
      rcases Finset.mem_union.1 hy with hyP | hyQ
      · exact ((h y hyP x hxQ).2 hxy).elim
      · exact hm y hyQ hxy

def historyOrderCount (S : Finset α) : ℝ := historyDeletionCoefficient (fun _ : α => (1 : ℝ)) S.card S

def historyOrderVolume (S : Finset α) : ℝ := historyOrderCount S / (S.card.factorial : ℝ)

@[simp] theorem historyOrderCount_empty : historyOrderCount (∅ : Finset α) = 1 := by
  simp [historyOrderCount]

@[simp] theorem historyOrderVolume_empty : historyOrderVolume (∅ : Finset α) = 1 := by
  simp [historyOrderVolume]

theorem historyOrderCount_recursion (S : Finset α) (hS : S.Nonempty) :
    historyOrderCount S = ∑ x ∈ historyMaximalPieces S, historyOrderCount (S.erase x) := by
  have hpos := Finset.card_pos.2 hS
  have hc : S.card = (S.card - 1) + 1 := by omega
  unfold historyOrderCount
  rw [hc, historyDeletionCoefficient_succ]
  apply Finset.sum_congr rfl
  intro x hx
  have hxS := historyMaximalPieces_subset S hx
  rw [Finset.card_erase_of_mem hxS, one_mul]

theorem historyOrderCount_nonneg (S : Finset α) : 0 ≤ historyOrderCount S := by
  have hh : ∀ k (T : Finset α), 0 ≤ historyDeletionCoefficient (fun _ : α => (1 : ℝ)) k T := by
    intro k
    induction k with
    | zero => intro T; simp
    | succ k ih =>
      intro T
      rw [historyDeletionCoefficient_succ]
      apply Finset.sum_nonneg
      intro x hx
      simpa only [one_mul] using ih (T.erase x)
  exact hh S.card S

theorem historyOrderCount_le_factorial (S : Finset α) : historyOrderCount S ≤ (S.card.factorial : ℝ) := by
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases he : S = ∅
  · subst S; simp
  · have hS := Finset.nonempty_iff_ne_empty.2 he
    have hn := Finset.card_pos.2 hS
    rw [historyOrderCount_recursion S hS]
    calc
      _ ≤ ∑ x ∈ historyMaximalPieces S, ((S.card - 1).factorial : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        have hxS := historyMaximalPieces_subset S hx
        simpa only [Finset.card_erase_of_mem hxS] using ih (S.erase x) (Finset.erase_ssubset hxS)
      _ = (historyMaximalPieces S).card * ((S.card - 1).factorial : ℝ) := by simp
      _ ≤ (S.card : ℝ) * ((S.card - 1).factorial : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Finset.card_le_card (historyMaximalPieces_subset S)
      _ = (S.card.factorial : ℝ) := by
        have hc : S.card = (S.card - 1) + 1 := by omega
        conv_rhs => rw [hc, Nat.factorial_succ]
        push_cast
        congr 1
        exact_mod_cast hc

theorem historyOrderVolume_nonneg (S : Finset α) : 0 ≤ historyOrderVolume S :=
  div_nonneg (historyOrderCount_nonneg S) (by positivity)

theorem historyOrderVolume_le_one (S : Finset α) : historyOrderVolume S ≤ 1 := by
  exact (div_le_one (by positivity : 0 < (S.card.factorial : ℝ))).2 (historyOrderCount_le_factorial S)

theorem historyOrderVolume_recursion (S : Finset α) :
    (S.card : ℝ) * historyOrderVolume S = ∑ x ∈ historyMaximalPieces S, historyOrderVolume (S.erase x) := by
  classical
  by_cases he : S = ∅
  · subst S
    simp [historyMaximalPieces]
  · have hS := Finset.nonempty_iff_ne_empty.2 he
    have hn := Finset.card_pos.2 hS
    have hc : S.card = (S.card - 1) + 1 := by omega
    unfold historyOrderVolume
    rw [historyOrderCount_recursion S hS]
    conv_lhs => arg 2; arg 2; rw [hc, Nat.factorial_succ]
    push_cast
    calc
      _ = (∑ x ∈ historyMaximalPieces S, historyOrderCount (S.erase x)) /
          ((S.card - 1).factorial : ℝ) := by
        have hr : (S.card : ℝ) = ((S.card - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast hc
        rw [hr]
        field_simp [show (((S.card - 1 : ℕ) : ℝ) + 1) ≠ 0 by positivity]
      _ = _ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.card_erase_of_mem (historyMaximalPieces_subset S hx)]

/-- Order-volume coefficients multiply across disjoint incomparable history parts. -/
theorem historyOrderVolume_union {P Q : Finset α} (hinc : IncomparableHistoryParts P Q) :
    historyOrderVolume (P ∪ Q) = historyOrderVolume P * historyOrderVolume Q := by
  classical
  have hmain : ∀ n : ℕ, ∀ P Q : Finset α, (P ∪ Q).card = n → IncomparableHistoryParts P Q →
      historyOrderVolume (P ∪ Q) = historyOrderVolume P * historyOrderVolume Q := by
    intro n
    induction n using Nat.strong_induction_on
    rename_i n ih
    intro P Q hn hinc
    by_cases he : P ∪ Q = ∅
    · have hP : P = ∅ := (Finset.union_eq_empty.1 he).1
      have hQ : Q = ∅ := (Finset.union_eq_empty.1 he).2
      simp [hP, hQ]
    · have hdis := hinc.disjoint
      have hmaxdis : Disjoint (historyMaximalPieces P) (historyMaximalPieces Q) :=
        hdis.mono (historyMaximalPieces_subset P) (historyMaximalPieces_subset Q)
      have hleft : (∑ x ∈ historyMaximalPieces P, historyOrderVolume ((P ∪ Q).erase x)) =
          (P.card : ℝ) * historyOrderVolume P * historyOrderVolume Q := by
        calc
          _ = ∑ x ∈ historyMaximalPieces P, historyOrderVolume (P.erase x) * historyOrderVolume Q := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxP := historyMaximalPieces_subset P hx
            have hxQ : x ∉ Q := fun hxQ => Finset.disjoint_left.1 hdis hxP hxQ
            have hU : (P ∪ Q).erase x = P.erase x ∪ Q := by
              rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hxQ]
            have hlt : (P.erase x ∪ Q).card < n := by
              rw [← hU, ← hn]
              exact Finset.card_lt_card (Finset.erase_ssubset (Finset.mem_union_left _ hxP))
            have hinc' : IncomparableHistoryParts (P.erase x) Q :=
              fun p hp q hq => hinc p (Finset.mem_of_mem_erase hp) q hq
            rw [hU]
            exact ih _ hlt (P.erase x) Q rfl hinc'
          _ = (∑ x ∈ historyMaximalPieces P, historyOrderVolume (P.erase x)) * historyOrderVolume Q :=
            (Finset.sum_mul _ _ _).symm
          _ = _ := by rw [← historyOrderVolume_recursion]
      have hright : (∑ x ∈ historyMaximalPieces Q, historyOrderVolume ((P ∪ Q).erase x)) =
          (Q.card : ℝ) * historyOrderVolume P * historyOrderVolume Q := by
        calc
          _ = ∑ x ∈ historyMaximalPieces Q, historyOrderVolume P * historyOrderVolume (Q.erase x) := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxQ := historyMaximalPieces_subset Q hx
            have hxP : x ∉ P := fun hxP => Finset.disjoint_left.1 hdis hxP hxQ
            have hU : (P ∪ Q).erase x = P ∪ Q.erase x := by
              rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hxP]
            have hlt : (P ∪ Q.erase x).card < n := by
              rw [← hU, ← hn]
              exact Finset.card_lt_card (Finset.erase_ssubset (Finset.mem_union_right _ hxQ))
            have hinc' : IncomparableHistoryParts P (Q.erase x) :=
              fun p hp q hq => hinc p hp q (Finset.mem_of_mem_erase hq)
            rw [hU]
            exact ih _ hlt P (Q.erase x) rfl hinc'
          _ = historyOrderVolume P * (∑ x ∈ historyMaximalPieces Q, historyOrderVolume (Q.erase x)) :=
            (Finset.mul_sum _ _ _).symm
          _ = _ := by rw [← historyOrderVolume_recursion]; ring
      have hrec := historyOrderVolume_recursion (P ∪ Q)
      rw [historyMaximalPieces_union hinc, Finset.sum_union hmaxdis, hleft, hright] at hrec
      have hcard : (P ∪ Q).card = P.card + Q.card := Finset.card_union_of_disjoint hdis
      have hpos : 0 < ((P ∪ Q).card : ℝ) := by
        exact_mod_cast Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 he)
      apply (mul_left_cancel₀ hpos.ne')
      rw [hrec, hcard]
      push_cast
      ring
  exact hmain (P ∪ Q).card P Q rfl hinc

def historyComponentWeight (weight : α → ℝ) (ρ t : ℝ) (P : Finset α) : ℝ :=
  (t / ρ) ^ P.card * historyOrderVolume P * ∏ x ∈ P, weight x

/-- The exact signed polynomial component weights multiply on incomparable parts. -/
theorem historyComponentWeight_union (weight : α → ℝ) (ρ t : ℝ) {P Q : Finset α}
    (hinc : IncomparableHistoryParts P Q) :
    historyComponentWeight weight ρ t (P ∪ Q) =
      historyComponentWeight weight ρ t P * historyComponentWeight weight ρ t Q := by
  have hdis := hinc.disjoint
  unfold historyComponentWeight
  rw [Finset.card_union_of_disjoint hdis, pow_add, historyOrderVolume_union hinc, Finset.prod_union hdis]
  ring

/-- The actual finite component coefficient has the source's `epsilon^|P|` bound. -/
theorem historyComponentWeight_abs_le {weight : α → ℝ} {ρ t B : ℝ} (P : Finset α)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (_hB : 0 ≤ B) (hw : ∀ x ∈ P, |weight x| ≤ B) :
    |historyComponentWeight weight ρ t P| ≤ (t * B / ρ) ^ P.card := by
  have hp : 0 ≤ t / ρ := div_nonneg ht hρ.le
  have hprod : (∏ x ∈ P, |weight x|) ≤ B ^ P.card := by
    calc
      _ ≤ ∏ _x ∈ P, B := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hw
      _ = _ := by simp
  unfold historyComponentWeight
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hp _),
    abs_of_nonneg (historyOrderVolume_nonneg P), Finset.abs_prod]
  calc
    _ ≤ (t / ρ) ^ P.card * 1 * (B ^ P.card) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (historyOrderVolume_le_one P) (pow_nonneg hp _))
        hprod (by positivity) (by positivity)
    _ = _ := by rw [mul_one, ← mul_pow]; congr 1; ring

end NearlyMinimax
