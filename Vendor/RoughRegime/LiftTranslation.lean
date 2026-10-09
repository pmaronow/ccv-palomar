module

public import Mathlib
public import RoughRegime.UpperCovariance
public import RoughRegime.PolynomialDerivatives


@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory

namespace RoughRegime.LiftTranslation
set_option maxHeartbeats 800000

/-- Marginalizing an ordered injective tuple over unused slots gives the exact
remaining falling-factorial multiplicity. -/
lemma sum_embedding_restriction {A B : Type*} [Fintype A] [Fintype B]
    (n : ℕ) (f : (A ↪ Fin n) → ℝ) :
    (∑ e : A ⊕ B ↪ Fin n, f (Function.Embedding.inl.trans e)) =
      ((n - Fintype.card A).descFactorial (Fintype.card B) : ℝ) *
        ∑ e : A ↪ Fin n, f e := by
  classical
  let E := Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted (α := A) (β := B) (γ := Fin n)
  have hfirst (e : A ⊕ B ↪ Fin n) : (E e).1 = Function.Embedding.inl.trans e := rfl
  calc
    _ = ∑ e : A ⊕ B ↪ Fin n, f (E e).1 := by simp only [hfirst]
    _ = ∑ u : Σ e : A ↪ Fin n, B ↪ ↥(Set.range e)ᶜ, f u.1 := E.sum_comp (fun u : Σ e : A ↪ Fin n, B ↪ ↥(Set.range e)ᶜ => f u.1)
    _ = ∑ e : A ↪ Fin n, ((n - Fintype.card A).descFactorial (Fintype.card B) : ℝ) * f e := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro e _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_embedding_eq]
      have hcard : Fintype.card ↥(Set.range e)ᶜ = n - Fintype.card A := by
        change Fintype.card {j : Fin n // ¬j ∈ Set.range e} = _
        rw [Fintype.card_subtype_compl]
        rw [← Fintype.card_congr e.toEquivRange, Fintype.card_fin]
      rw [hcard]
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma sum_embedding_subtype_restriction {A : Type*} [Fintype A]
    (n : ℕ) (S : Finset A) (f : (↥S ↪ Fin n) → ℝ) :
    (∑ e : A ↪ Fin n, f ((Function.Embedding.subtype (fun i => i ∈ S)).trans e)) =
      ((n - S.card).descFactorial (Fintype.card A - S.card) : ℝ) *
        ∑ e : ↥S ↪ Fin n, f e := by
  classical
  let C := (S : Set A)ᶜ
  let E : (↥S ⊕ C ↪ Fin n) ≃ (A ↪ Fin n) :=
    Equiv.embeddingCongr (Equiv.Set.sumCompl (S : Set A)) (Equiv.refl (Fin n))
  calc
    _ = ∑ e : ↥S ⊕ C ↪ Fin n,
        f ((Function.Embedding.subtype (fun i => i ∈ S)).trans (E e)) :=
      (E.sum_comp (fun e : A ↪ Fin n =>
        f ((Function.Embedding.subtype (fun i => i ∈ S)).trans e))).symm
    _ = ∑ e : ↥S ⊕ C ↪ Fin n, f (Function.Embedding.inl.trans e) := by
      apply Finset.sum_congr rfl
      intro e _
      congr 1
      apply Function.Embedding.ext
      intro i
      change e ((Equiv.Set.sumCompl (S : Set A)).symm (i : A)) = e (Sum.inl i)
      rw [Equiv.Set.sumCompl_symm_apply_of_mem (show (i : A) ∈ (S : Set A) from i.property)]
      rfl
    _ = ((n - Fintype.card ↥S).descFactorial (Fintype.card C) : ℝ) *
        ∑ e : ↥S ↪ Fin n, f e := sum_embedding_restriction n f
    _ = _ := by
      have hcard : Fintype.card C = Fintype.card A - S.card := by
        change Fintype.card {i : A // ¬i ∈ S} = _
        rw [Fintype.card_subtype_compl]
        simp
      rw [hcard]
      simp

/-- Normalization cancels precisely the multiplicity of unused sample slots. -/
lemma normalized_embedding_subtype_restriction {A : Type*} [Fintype A]
    (n : ℕ) (hn : Fintype.card A ≤ n) (S : Finset A) (f : (↥S ↪ Fin n) → ℝ) :
    (n.descFactorial (Fintype.card A) : ℝ)⁻¹ *
        (∑ e : A ↪ Fin n, f ((Function.Embedding.subtype (fun i => i ∈ S)).trans e)) =
      (n.descFactorial S.card : ℝ)⁻¹ * ∑ e : ↥S ↪ Fin n, f e := by
  classical
  rw [sum_embedding_subtype_restriction]
  have hq : (n.descFactorial (Fintype.card A) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hn))
  have hr : (n.descFactorial S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr (S.card_le_univ.trans hn)))
  have hprod : ((n - S.card).descFactorial (Fintype.card A - S.card) : ℝ) *
      (n.descFactorial S.card : ℝ) = n.descFactorial (Fintype.card A) := by
    exact_mod_cast (Nat.descFactorial_mul_descFactorial S.card_le_univ)
  have hcoeff : (n.descFactorial (Fintype.card A) : ℝ)⁻¹ *
      ((n - S.card).descFactorial (Fintype.card A - S.card) : ℝ) =
        (n.descFactorial S.card : ℝ)⁻¹ := by
    field_simp
    exact hprod
  rw [← mul_assoc, hcoeff]

/-- Exact centering expansion of one monomial lift. Every subset records the slots
in which a centered observation is used. -/
theorem monomialLift_centering {Ω : Type*} {n p q : ℕ}
    (σ : Fin q → Fin p) (Y : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hqn : q ≤ n) (ω : Ω) :
    RoughRegime.Upper.monomialLift σ (fun j ω => Y j ω + m) ω =
      ∑ S : Finset (Fin q), (∏ i ∈ Sᶜ, m (σ i)) *
        ((n.descFactorial S.card : ℝ)⁻¹ *
          ∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) ω (σ i)) := by
  classical
  unfold RoughRegime.Upper.monomialLift
  simp only [Pi.add_apply]
  simp_rw [Fintype.prod_add (fun i => Y _ ω (σ i)) (fun i => m (σ i))]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  have hprod (e : Fin q ↪ Fin n) :
      (∏ i ∈ S, Y (e i) ω (σ i)) =
        ∏ i : ↥S, Y (e i) ω (σ i) := by
    exact (Finset.prod_coe_sort S (fun i => Y (e i) ω (σ i))).symm
  simp_rw [hprod]
  rw [← Finset.sum_mul]
  have h : (n.descFactorial q : ℝ)⁻¹ * (∑ e : Fin q ↪ Fin n, ∏ i : ↥S, Y (e i) ω (σ i)) =
      (n.descFactorial S.card : ℝ)⁻¹ * (∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) ω (σ i)) :=
    by
      simpa using (normalized_embedding_subtype_restriction n (by simpa using hqn) S
        (fun e : ↥S ↪ Fin n => ∏ i : ↥S, Y (e i) ω (σ i)))
  linear_combination (∏ i ∈ Sᶜ, m (σ i)) * h

lemma range_embedding_of_subset_equiv {A B : Type*} [Fintype A] [Fintype B]
    (S : Finset B) (a : A ≃ ↥S) :
    Set.range (a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))) = S := by
  ext j
  constructor
  · rintro ⟨i, rfl⟩
    exact (a i).property
  · intro hj
    obtain ⟨i, hi⟩ := a.surjective ⟨j, hj⟩
    exact ⟨i, congrArg Subtype.val hi⟩

/-- An ordered injective tuple consists of its unordered range and an ordering of that range. -/
lemma sum_embeddings_by_range {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (f : (A ↪ B) → ℝ) :
    (∑ e : A ↪ B, f e) =
      ∑ S : Finset B, ∑ a : A ≃ ↥S,
        f (a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))) := by
  classical
  let g : (Σ S : Finset B, A ≃ ↥S) → (A ↪ B) :=
    fun u => u.2.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ u.1))
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨S, a⟩ ⟨T, b⟩ h
      have hST : S = T := by
        apply Finset.coe_injective
        rw [← range_embedding_of_subset_equiv S a, ← range_embedding_of_subset_equiv T b]
        exact congrArg (fun e : A ↪ B => Set.range (e : A → B)) h
      subst T
      have hab : a = b := by
        apply Equiv.ext
        intro i
        apply Subtype.ext
        exact congrArg (fun e : A ↪ B => e i) h
      subst b
      rfl
    · intro e
      let S := Finset.univ.map e
      have hS : Set.range e = (S : Set B) := by ext j; simp [S]
      let a : A ≃ ↥S := e.toEquivRange.trans (Set.equivOfEq hS)
      refine ⟨⟨S, a⟩, ?_⟩
      apply Function.Embedding.ext
      intro i
      rfl
  calc
    _ = ∑ u : Σ S : Finset B, A ≃ ↥S, f (g u) :=
      ((Equiv.ofBijective g hg).sum_comp f).symm
    _ = _ := by rw [Fintype.sum_sigma]

/-- The sample sum does not depend on which ordering is chosen for a fixed slot set. -/
lemma sum_samples_subset_equiv {n p r : ℕ} (S : Finset (Fin p))
    (a : Fin r ≃ ↥S) (Y : Fin n → Fin p → ℝ) :
    (∑ e : Fin r ↪ Fin n, ∏ i : Fin r, Y (e i) (a i)) =
      ∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) i := by
  classical
  let E : (Fin r ↪ Fin n) ≃ (↥S ↪ Fin n) :=
    Equiv.embeddingCongr a (Equiv.refl (Fin n))
  calc
    _ = ∑ e : Fin r ↪ Fin n, ∏ i : ↥S, Y ((E e) i) i := by
      apply Finset.sum_congr rfl
      intro e _
      rw [← a.prod_comp]
      apply Finset.prod_congr rfl
      intro i _
      simp [E, Equiv.embeddingCongr, Function.Embedding.congr_apply]
    _ = _ := E.sum_comp (fun e : ↥S ↪ Fin n => ∏ i : ↥S, Y (e i) i)

lemma monomial_replacement_by_subset {p q r : ℕ} (σ : Fin q → Fin p)
    (S : Finset (Fin q)) (a : Fin r ≃ ↥S) (m : Fin p → ℝ)
    (v : Fin r → Fin p → ℝ) :
    (∏ j : Fin q, if h : j ∈ Set.range
        (a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))) then
      v ((a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))).toEquivRange.symm ⟨j, h⟩)
        (σ j) else m (σ j)) =
      (∏ i : Fin r, v i (σ (a i))) * ∏ j ∈ Sᶜ, m (σ j) := by
  classical
  let b : Fin r ↪ Fin q := a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))
  let f : Fin q → ℝ := fun j => if h : j ∈ Set.range b then v (b.toEquivRange.symm ⟨j, h⟩) (σ j)
    else m (σ j)
  have hb : Set.range b = (S : Set (Fin q)) := range_embedding_of_subset_equiv S a
  change (∏ j : Fin q, f j) = _
  rw [← Finset.prod_mul_prod_compl S f]
  congr 1
  · calc
      _ = ∏ j : ↥S, f j := (Finset.prod_coe_sort S f).symm
      _ = ∏ i : Fin r, f (a i) := (a.prod_comp (fun j : ↥S => f j)).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        have hi : (a i : Fin q) ∈ Set.range b := ⟨i, rfl⟩
        simp only [f, dite_eq_left hi]
        change v (b.toEquivRange.symm ⟨b i, _⟩) (σ (a i)) = _
        simp
  · apply Finset.prod_congr rfl
    intro j hj
    have hjb : j ∉ Set.range b := by
      rw [hb]
      simpa using Finset.mem_compl.mp hj
    exact dite_eq_right hjb

/-- Grouping the derivative injections by their range removes all dependence on
how the selected monomial slots are ordered. -/
lemma monomial_derivative_sample_sum {n p q r : ℕ} (σ : Fin q → Fin p)
    (m : Fin p → ℝ) (Y : Fin n → Fin p → ℝ) :
    (∑ e : Fin r ↪ Fin n,
      iteratedFDeriv ℝ r (RoughRegime.PolynomialDerivatives.monomial σ) m (fun i => Y (e i))) =
      ∑ S : Finset (Fin q), (Fintype.card (Fin r ≃ ↥S) : ℝ) *
        ((∏ j ∈ Sᶜ, m (σ j)) * (∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) (σ i))) := by
  classical
  simp_rw [RoughRegime.PolynomialDerivatives.monomial_iteratedFDeriv]
  rw [Finset.sum_comm]
  rw [sum_embeddings_by_range]
  apply Finset.sum_congr rfl
  intro S _
  have hsamp (a : Fin r ≃ ↥S) :
      (∑ e : Fin r ↪ Fin n,
        ∏ j : Fin q, if h : j ∈ Set.range
            (a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))) then
          Y (e ((a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))).toEquivRange.symm
            ⟨j, h⟩)) (σ j) else m (σ j)) =
        (∏ j ∈ Sᶜ, m (σ j)) * (∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) (σ i)) := by
    calc
      _ = ∑ e : Fin r ↪ Fin n, (∏ i : Fin r, Y (e i) (σ (a i))) * (∏ j ∈ Sᶜ, m (σ j)) := by
        apply Finset.sum_congr rfl
        intro e _
        exact monomial_replacement_by_subset σ S a m (fun i => Y (e i))
      _ = _ := by
        rw [← Finset.sum_mul]
        rw [sum_samples_subset_equiv S a (fun j i => Y j (σ i))]
        exact mul_comm _ _
  simp_rw [hsamp]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma card_equiv_fin_subset {q r : ℕ} (S : Finset (Fin q)) :
    Fintype.card (Fin r ≃ ↥S) = if S.card = r then r.factorial else 0 := by
  classical
  split_ifs with h
  · let a : Fin r ≃ ↥S := Fintype.equivOfCardEq (by simpa using h.symm)
    rw [Fintype.card_equiv a]
    simp
  · have hempty : IsEmpty (Fin r ≃ ↥S) := ⟨fun a => h (by simpa using (Fintype.card_congr a).symm)⟩
    exact Fintype.card_eq_zero

lemma normalized_monomial_derivative_sample_sum {n p q r : ℕ} (σ : Fin q → Fin p)
    (m : Fin p → ℝ) (Y : Fin n → Fin p → ℝ) (hrn : r ≤ n) :
    (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ * ∑ e : Fin r ↪ Fin n,
      iteratedFDeriv ℝ r (RoughRegime.PolynomialDerivatives.monomial σ) m (fun i => Y (e i))) =
      ∑ S : Finset (Fin q), if S.card = r then
        (∏ j ∈ Sᶜ, m (σ j)) *
          ((n.descFactorial S.card : ℝ)⁻¹ * ∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) (σ i))
        else 0 := by
  classical
  rw [monomial_derivative_sample_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [card_equiv_fin_subset]
  split_ifs with h
  · rw [h]
    have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
    have hdesc : (n.descFactorial r : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hrn))
    field_simp
  · simp

/-- The derivative-defined distinct-sample expression at any expansion point. -/
def derivativeLiftAt {Ω : Type*} {n p : ℕ} (R : ℕ) (f : (Fin p → ℝ) → ℝ)
    (m : Fin p → ℝ) (Y : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  ∑ r ∈ Finset.range (R + 1),
    (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ * ∑ e : Fin r ↪ Fin n,
      iteratedFDeriv ℝ r f m (fun i => Y (e i) ω))

/-- A monomial lift agrees exactly with the centered derivative expansion at its degree. -/
theorem monomialLift_eq_derivativeLiftAt {Ω : Type*} {n p q : ℕ}
    (σ : Fin q → Fin p) (Y : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hqn : q ≤ n) (ω : Ω) :
    RoughRegime.Upper.monomialLift σ (fun j ω => Y j ω + m) ω =
      derivativeLiftAt q (RoughRegime.PolynomialDerivatives.monomial σ) m Y ω := by
  classical
  rw [monomialLift_centering σ Y m hqn ω]
  unfold derivativeLiftAt
  have hexp (r : ℕ) (hr : r ∈ Finset.range (q + 1)) :=
    normalized_monomial_derivative_sample_sum σ m (fun j => Y j ω)
      ((Nat.le_of_lt_succ (Finset.mem_range.mp hr)).trans hqn)
  calc
    _ = ∑ r ∈ Finset.range (q + 1), ∑ S : Finset (Fin q),
        if S.card = r then (∏ j ∈ Sᶜ, m (σ j)) *
          ((n.descFactorial S.card : ℝ)⁻¹ * ∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) ω (σ i)) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      have hS : S.card ∈ Finset.range (q + 1) := by
        apply Finset.mem_range.mpr
        have hcard := S.card_le_univ
        simp only [Fintype.card_fin] at hcard
        omega
      simp [hS]
    _ = _ := Finset.sum_congr rfl (fun r hr => (hexp r hr).symm)

lemma derivativeLiftAt_monomial_stable {Ω : Type*} {n p q R : ℕ}
    (σ : Fin q → Fin p) (Y : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hqR : q ≤ R) (ω : Ω) :
    derivativeLiftAt R (RoughRegime.PolynomialDerivatives.monomial σ) m Y ω =
      derivativeLiftAt q (RoughRegime.PolynomialDerivatives.monomial σ) m Y ω := by
  classical
  unfold derivativeLiftAt
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hqR 1))
  intro r _ hr
  have hqr : q < r := by
    have hr' : ¬r < q + 1 := fun h => hr (Finset.mem_range.mpr h)
    omega
  have hzero (e : Fin r ↪ Fin n) :=
    RoughRegime.PolynomialDerivatives.monomial_iteratedFDeriv_above_degree σ m
      (fun i => Y (e i) ω) hqr
  simp only [hzero, Finset.sum_const_zero, mul_zero]

lemma derivativeLiftAt_polynomial_monomial_sum {Ω : Type*} {n p : ℕ}
    (R : ℕ) (F : MvPolynomial (Fin p) ℝ) (Y : Fin n → Ω → Fin p → ℝ)
    (m : Fin p → ℝ) (ω : Ω) :
    derivativeLiftAt R (fun x => MvPolynomial.eval x F) m Y ω =
      ∑ α ∈ F.support, F.coeff α * derivativeLiftAt R
        (RoughRegime.PolynomialDerivatives.monomial (RoughRegime.Upper.exponentCoordinates α)) m Y ω := by
  classical
  unfold derivativeLiftAt
  have hstep (r : ℕ) :
      (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ * ∑ e : Fin r ↪ Fin n,
        iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m (fun i => Y (e i) ω)) =
      ∑ α ∈ F.support, F.coeff α *
        ((((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ * ∑ e : Fin r ↪ Fin n,
          iteratedFDeriv ℝ r (RoughRegime.PolynomialDerivatives.monomial
            (RoughRegime.Upper.exponentCoordinates α)) m (fun i => Y (e i) ω))) := by
    simp_rw [RoughRegime.PolynomialDerivatives.polynomial_iteratedFDeriv_monomial_sum]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    ring
  simp_rw [hstep]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  exact (Finset.mul_sum _ _ _).symm

/-- The monomial-defined unbiased lift equals the exact derivative-defined lift at
every expansion point. In particular it is invariant under centering the observations. -/
theorem polynomialLift_eq_derivativeLiftAt {Ω : Type*} {n p R : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (Y : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n) (ω : Ω) :
    RoughRegime.Upper.polynomialLift F (fun j ω => Y j ω + m) ω =
      derivativeLiftAt R (fun x => MvPolynomial.eval x F) m Y ω := by
  classical
  rw [derivativeLiftAt_polynomial_monomial_sum]
  unfold RoughRegime.Upper.polynomialLift
  apply Finset.sum_congr rfl
  intro α hα
  congr 1
  have hqR : Fintype.card (RoughRegime.Upper.ExponentSlots α) ≤ R := by
    rw [RoughRegime.Upper.exponentSlots_card]
    exact (MvPolynomial.le_totalDegree hα).trans hdeg
  rw [derivativeLiftAt_monomial_stable _ Y m hqR ω]
  exact monomialLift_eq_derivativeLiftAt _ Y m (hqR.trans hRn) ω

lemma derivativeLiftAt_eq_centeredDerivativeLift {Ω : Type*} {n p : ℕ}
    (R : ℕ) (F : MvPolynomial (Fin p) ℝ) (Y : Fin n → Ω → Fin p → ℝ)
    (m : Fin p → ℝ) (ω : Ω) :
    derivativeLiftAt R (fun x => MvPolynomial.eval x F) m Y ω =
      RoughRegime.UpperCovariance.centeredDerivativeLift R F m Y ω := by
  classical
  unfold derivativeLiftAt RoughRegime.UpperCovariance.centeredDerivativeLift
    RoughRegime.UpperCovariance.centeredKernelExpansion
    RoughRegime.UpperCovariance.kernelStatistic RoughRegime.UpperCovariance.kernelSum
  rw [Finset.sum_range_succ']
  simp only [iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.descFactorial_zero, Nat.cast_one,
    one_mul, inv_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_embedding_eq,
    Fintype.card_fin, Nat.cast_one, one_mul]
  rw [add_comm]
  congr 1
  exact (Fin.sum_univ_eq_sum_range
    (fun r => (((r + 1).factorial : ℝ) * (n.descFactorial (r + 1) : ℝ))⁻¹ *
      ∑ e : Fin (r + 1) ↪ Fin n,
        iteratedFDeriv ℝ (r + 1) (fun x => MvPolynomial.eval x F) m (fun i => Y (e i) ω)) R).symm

/-- Complete algebraic identity identifying the original coefficient lift with its
centered derivative expansion. The center is arbitrary; no population identity is assumed. -/
theorem polynomialLift_eq_centeredDerivativeLift {Ω : Type*} {n p R : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n) :
    RoughRegime.Upper.polynomialLift F X =
      RoughRegime.UpperCovariance.centeredDerivativeLift R F m (fun j ω => X j ω - m) := by
  funext ω
  have hX : (fun j ω => (X j ω - m) + m) = X := by
    funext j ω
    exact sub_add_cancel (X j ω) m
  rw [← derivativeLiftAt_eq_centeredDerivativeLift]
  rw [← polynomialLift_eq_derivativeLiftAt F (fun j ω => X j ω - m) m hdeg hRn ω, hX]

/-- The derivative notation at zero and the coefficient-defined lift are exactly
identical, completing the definition bridge for Lemma 7. -/
theorem polynomialLift_eq_paperLift {Ω : Type*} {n p R : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n) :
    RoughRegime.Upper.polynomialLift F X =
      derivativeLiftAt R (fun x => MvPolynomial.eval x F) 0 X := by
  funext ω
  have hX : (fun j ω => X j ω + (0 : Fin p → ℝ)) = X := by simp
  rw [← polynomialLift_eq_derivativeLiftAt F X 0 hdeg hRn ω, hX]

/-- Full covariance assertion of Lemma 7 for the actual coefficient/derivative lift.
The finite sum runs through `n`; terms beyond either polynomial degree vanish. -/
theorem polynomialLift_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p : ℕ}
    (F G : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ)
    (hF : F.totalDegree ≤ n) (hG : G.totalDegree ≤ n)
    (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (m : Fin p → ℝ) (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = m i) :
    covariance (RoughRegime.Upper.polynomialLift F X) (RoughRegime.Upper.polynomialLift G X) μ =
      ∑ r : Fin n, (((r.val + 1).factorial : ℝ) * (n.descFactorial (r.val + 1) : ℝ))⁻¹ *
        ∫ ω,
          iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m
            (fun i => X (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt) i) ω - m) *
          iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x G) m
            (fun i => X (Fin.castLEEmb (Nat.succ_le_of_lt r.isLt) i) ω - m) ∂μ := by
  rw [polynomialLift_eq_centeredDerivativeLift F X m hF le_rfl,
    polynomialLift_eq_centeredDerivativeLift G X m hG le_rfl]
  obtain ⟨hYind, hYmeas, hYid, hYbound, hYmean⟩ :=
    RoughRegime.UpperCovariance.centerObservations_properties μ X m hi hm hid M hM hb hmean
  exact RoughRegime.UpperCovariance.covariance_centeredDerivativeLift μ F G m
    (fun j ω => X j ω - m) le_rfl hYind hYmeas hYid (M + ‖m‖)
    (add_nonneg hM (norm_nonneg m)) hYbound hYmean

/-- The covariance series really stops at the smaller degree, as stated in Lemma 7. -/
lemma covariance_derivative_term_zero_above_smaller_degree {p r : ℕ}
    (F G : MvPolynomial (Fin p) ℝ) (m : Fin p → ℝ) (v : Fin r → Fin p → ℝ)
    (hr : min F.totalDegree G.totalDegree < r) :
    iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m v *
      iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x G) m v = 0 := by
  rcases min_lt_iff.mp hr with h | h
  · rw [RoughRegime.PolynomialDerivatives.polynomial_iteratedFDeriv_above_degree F m v
      h, zero_mul]
  · rw [RoughRegime.PolynomialDerivatives.polynomial_iteratedFDeriv_above_degree G m v
      h, mul_zero]

end RoughRegime.LiftTranslation
