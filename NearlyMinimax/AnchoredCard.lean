module

public import NearlyMinimax.AnchoredBasis


@[expose] public section

/-! The exact stars-and-bars cardinality of the paper's nonconstant features. -/

noncomputable section
open scoped BigOperators
namespace NearlyMinimax

abbrev TotalDegreeIndex (d ℓ : ℕ) :=
  {γ : PolynomialBox d ℓ // (∑ i, (γ i).val) ≤ ℓ}

def totalDegreeSlackEquiv (d ℓ : ℕ) :
    TotalDegreeIndex d ℓ ≃ {v : Option (Fin d) → ℕ // ∑ i, v i = ℓ} where
  toFun γ := ⟨fun i => i.casesOn (ℓ - ∑ j, (γ.val j).val) (fun j => (γ.val j).val), by
    rw [Fintype.sum_option]
    exact Nat.sub_add_cancel γ.property⟩
  invFun v := ⟨fun i => ⟨v.val (some i), by
    have hi : v.val (some i) ≤ ∑ j, v.val j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ _)
    rw [v.property] at hi
    omega⟩, by
      have h := v.property
      rw [Fintype.sum_option] at h
      exact Nat.le.intro (by simpa [Nat.add_comm] using h)⟩
  left_inv γ := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl
  right_inv v := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
      change ℓ - ∑ j, v.val (some j) = v.val none
      have h := v.property
      rw [Fintype.sum_option] at h
      omega
    | some i => rfl

theorem totalDegreeIndex_card (d ℓ : ℕ) :
    Fintype.card (TotalDegreeIndex d ℓ) = (d + ℓ).choose d := by
  let e := (totalDegreeSlackEquiv d ℓ).trans (Sym.equivNatSumOfFintype (Option (Fin d)) ℓ).symm
  rw [Fintype.card_congr e, Sym.card_sym_eq_choose]
  simp only [Fintype.card_option, Fintype.card_fin]
  have h : d + 1 + ℓ - 1 = d + ℓ := by omega
  rw [h]
  have hc := Nat.choose_symm (show ℓ ≤ d + ℓ by omega)
  simpa only [Nat.add_sub_cancel] using hc.symm

def anchoredNonzeroEquiv (d ℓ : ℕ) : AnchoredIndex d ℓ ≃
    {γ : TotalDegreeIndex d ℓ // ¬ (∑ i, (γ.val i).val) = 0} where
  toFun γ := ⟨⟨γ.val, γ.property.2⟩, ne_of_gt γ.property.1⟩
  invFun γ := ⟨γ.val.val, Nat.pos_of_ne_zero γ.property, γ.val.property⟩
  left_inv γ := by rfl
  right_inv γ := by rfl

/-- The concrete feature dimension is exactly the manuscript's `q_s - 1`. -/
theorem anchoredIndex_card (d ℓ : ℕ) :
    Fintype.card (AnchoredIndex d ℓ) = (d + ℓ).choose d - 1 := by
  classical
  let z : {γ : TotalDegreeIndex d ℓ // (∑ i, (γ.val i).val) = 0} :=
    ⟨⟨fun _ => 0, by simp⟩, by simp⟩
  letI : Unique {γ : TotalDegreeIndex d ℓ // (∑ i, (γ.val i).val) = 0} :=
    { default := z
      uniq := fun γ => by
        apply Subtype.ext
        apply Subtype.ext
        funext i
        apply Fin.ext
        have hi : (γ.val.val i).val ≤ ∑ j, (γ.val.val j).val :=
          Finset.single_le_sum (f := fun j => (γ.val.val j).val)
            (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        rw [γ.property] at hi
        exact Nat.eq_zero_of_le_zero hi }
  rw [Fintype.card_congr (anchoredNonzeroEquiv d ℓ),
    Fintype.card_subtype_compl, totalDegreeIndex_card]
  have hz : Fintype.card {γ : TotalDegreeIndex d ℓ // (∑ i, (γ.val i).val) = 0} = 1 :=
    Fintype.card_unique
  rw [hz]

end NearlyMinimax
