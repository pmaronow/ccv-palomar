module

public import Mathlib
public import RoughRegime.Upper


@[expose] public section

/-!
Centered-kernel orthogonality and covariance ingredients for Lemma 7.
No covariance identity or centering contraction is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace RoughRegime.UpperCovariance

lemma multilinear_coordinate_expansion {r p : ℕ}
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (v : Fin r → Fin p → ℝ) :
    H v = ∑ σ : Fin r → Fin p,
      H (fun i => Pi.single (σ i) 1) * ∏ i, v i (σ i) := by
  classical
  have hv : v = fun i => ∑ a : Fin p, v i a • Pi.single a (1 : ℝ) := by
    funext i a
    simp [Pi.single_apply]
  calc
    H v = H (fun i => ∑ a : Fin p, v i a • Pi.single a (1 : ℝ)) := congrArg H hv
    _ = ∑ σ : Fin r → Fin p, H (fun i => v i (σ i) • Pi.single (σ i) (1 : ℝ)) := H.map_sum _
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro σ _
  rw [H.map_smul_univ]
  simp only [smul_eq_mul]
  exact mul_comm _ _

lemma coordinate_product_integrable {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p : ℕ}
    (s : A → Fin n) (σ : A → Fin p) (X : Fin n → Ω → Fin p → ℝ)
    (hm : ∀ j, Measurable (X j)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ j ω i, |X j ω i| ≤ M) :
    Integrable (fun ω => ∏ i, X (s i) ω (σ i)) μ := by
  classical
  apply (integrable_const (M ^ Fintype.card A)).mono'
  · exact (Finset.measurable_prod _ (fun i _ => (measurable_pi_apply (σ i)).comp (hm (s i)))).aestronglyMeasurable
  · filter_upwards [] with ω
    rw [Real.norm_eq_abs, Finset.abs_prod]
    calc
      (∏ i : A, |X (s i) ω (σ i)|) ≤ ∏ _i : A, M :=
        Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hb (s i) ω (σ i))
      _ = M ^ Fintype.card A := by simp

/-- Grouping factors by observation reduces any finite coordinate product to a product
of single-observation expectations. The coordinates may repeat. -/
lemma integral_coordinate_product_fiberwise {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p : ℕ}
    (s : A → Fin n) (σ : A → Fin p) (X : Fin n → Ω → Fin p → ℝ)
    (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j)) :
    (∫ ω, ∏ i, X (s i) ω (σ i) ∂μ) =
      ∏ j : Fin n, ∫ ω, ∏ i : A with s i = j, X j ω (σ i) ∂μ := by
  classical
  let f : Fin n → (Fin p → ℝ) → ℝ := fun j v => ∏ i : A with s i = j, v (σ i)
  have hf : ∀ j, Measurable (f j) := fun j =>
    Finset.measurable_prod _ (fun i _ => measurable_pi_apply (σ i))
  have hind : iIndepFun (fun j ω => f j (X j ω)) μ := hi.comp f hf
  have hfun : (fun ω => ∏ i, X (s i) ω (σ i)) =
      (fun ω => ∏ j, f j (X j ω)) := by
    funext ω
    dsimp [f]
    rw [← Finset.prod_fiberwise (Finset.univ : Finset A) s (fun i => X (s i) ω (σ i))]
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [hfun]
  exact hind.integral_fun_prod_eq_prod_integral
    (fun j => ((hf j).comp (hm j)).aestronglyMeasurable)

/-- A centered coordinate appearing at a sample index used just once annihilates the
expectation of the whole coordinate product. -/
lemma integral_coordinate_product_eq_zero {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p : ℕ}
    (s : A → Fin n) (σ : A → Fin p) (X : Fin n → Ω → Fin p → ℝ)
    (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = 0)
    (k : A) (hk : ∀ i, s i = s k → i = k) :
    (∫ ω, ∏ i, X (s i) ω (σ i) ∂μ) = 0 := by
  classical
  rw [integral_coordinate_product_fiberwise μ s σ X hi hm]
  apply Finset.prod_eq_zero (Finset.mem_univ (s k))
  have hfilter : (Finset.univ.filter (fun i : A => s i = s k)) = {k} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hk i, fun h => by rw [h]⟩
  rw [hfilter]
  simpa using hmean (s k) (σ k)

lemma integral_monomial_pair_eq_zero_left {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r t : ℕ}
    (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (σ : Fin r → Fin p) (τ : Fin t → Fin p)
    (X : Fin n → Ω → Fin p → ℝ)
    (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = 0)
    (k : Fin r) (hk : e k ∉ Set.range f) :
    (∫ ω, (∏ i, X (e i) ω (σ i)) * (∏ i, X (f i) ω (τ i)) ∂μ) = 0 := by
  classical
  have h := integral_coordinate_product_eq_zero μ (Sum.elim e f) (Sum.elim σ τ)
    X hi hm hmean (Sum.inl k) ?_
  · simpa [Fintype.prod_sum_type] using h
  · intro i hi
    cases i with
    | inl i => exact congrArg Sum.inl (e.injective hi)
    | inr i => exact (hk ⟨i, hi⟩).elim

lemma monomial_pair_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r t : ℕ}
    (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (σ : Fin r → Fin p) (τ : Fin t → Fin p)
    (X : Fin n → Ω → Fin p → ℝ)
    (hm : ∀ j, Measurable (X j)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ j ω i, |X j ω i| ≤ M) :
    Integrable (fun ω => (∏ i, X (e i) ω (σ i)) * (∏ i, X (f i) ω (τ i))) μ := by
  simpa [Fintype.prod_sum_type] using
    coordinate_product_integrable μ (Sum.elim e f) (Sum.elim σ τ) X hm M hM hb

lemma multilinear_pair_coordinate_expansion {n p r t : ℕ}
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : MultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n) (v : Fin n → Fin p → ℝ) :
    H (fun i => v (e i)) * G (fun i => v (f i)) =
      ∑ σ : Fin r → Fin p, ∑ τ : Fin t → Fin p,
        (H (fun i => Pi.single (σ i) 1) * G (fun i => Pi.single (τ i) 1)) *
        ((∏ i, v (e i) (σ i)) * (∏ i, v (f i) (τ i))) := by
  classical
  rw [multilinear_coordinate_expansion H, multilinear_coordinate_expansion G,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  ring

lemma multilinear_pair_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r t : ℕ}
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : MultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ)
    (hm : ∀ j, Measurable (X j)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ j ω i, |X j ω i| ≤ M) :
    Integrable (fun ω => H (fun i => X (e i) ω) * G (fun i => X (f i) ω)) μ := by
  classical
  have hexp (ω : Ω) := multilinear_pair_coordinate_expansion H G e f (fun j => X j ω)
  simp_rw [hexp]
  apply integrable_finsetSum
  intro σ _
  apply integrable_finsetSum
  intro τ _
  exact (monomial_pair_integrable μ e f σ τ X hm M hM hb).const_mul _

/-- Degenerate multilinear kernels on different observation sets are exactly orthogonal. -/
lemma integral_multilinear_pair_eq_zero_left {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r t : ℕ}
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : MultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ)
    (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = 0)
    (k : Fin r) (hk : e k ∉ Set.range f) :
    (∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ) = 0 := by
  classical
  have hexp (ω : Ω) := multilinear_pair_coordinate_expansion H G e f (fun j => X j ω)
  simp_rw [hexp]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro σ _
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro τ _
      rw [integral_const_mul, integral_monomial_pair_eq_zero_left μ e f σ τ X hi hm hmean k hk,
        mul_zero]
    · intro τ _
      exact (monomial_pair_integrable μ e f σ τ X hm M hM hb).const_mul _
  · intro σ _
    exact integrable_finsetSum _ fun τ _ =>
      (monomial_pair_integrable μ e f σ τ X hm M hM hb).const_mul _

lemma integral_multilinear_pair_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r t : ℕ}
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : MultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ)
    (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = 0)
    (hef : Set.range e ≠ Set.range f) :
    (∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ) = 0 := by
  classical
  by_cases hsub : Set.range e ⊆ Set.range f
  · have hnot : ¬Set.range f ⊆ Set.range e := fun h => hef (Set.Subset.antisymm hsub h)
    obtain ⟨j, hj, hje⟩ := Set.not_subset.mp hnot
    obtain ⟨k, rfl⟩ := hj
    simpa only [mul_comm] using
      integral_multilinear_pair_eq_zero_left μ G H f e X hi hm M hM hb hmean k hje
  · obtain ⟨j, hj, hjf⟩ := Set.not_subset.mp hsub
    obtain ⟨k, rfl⟩ := hj
    exact integral_multilinear_pair_eq_zero_left μ H G e f X hi hm M hM hb hmean k hjf

lemma same_range_exists_perm {n r : ℕ} (e f : Fin r ↪ Fin n)
    (hef : Set.range f = Set.range e) :
    ∃ σ : Equiv.Perm (Fin r), ∀ i, e (σ i) = f i := by
  let σ := (Equiv.ofInjective f f.injective).trans
    ((Set.equivOfEq hef).trans (Equiv.ofInjective e e.injective).symm)
  refine ⟨σ, fun i => ?_⟩
  change e ((Equiv.ofInjective e e.injective).symm
    ((Set.equivOfEq hef) ((Equiv.ofInjective f f.injective) i))) = f i
  exact Equiv.apply_ofInjective_symm e.injective _

lemma embedding_range_comp_perm {n r : ℕ} (e : Fin r ↪ Fin n)
    (σ : Equiv.Perm (Fin r)) : Set.range (σ.toEmbedding.trans e) = Set.range e := by
  ext j
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨σ i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨σ.symm i, by simp⟩

/-- Exactly `r!` distinct ordered tuples have the same observation set as a given tuple. -/
lemma card_same_range_embeddings {n r : ℕ} (e : Fin r ↪ Fin n) :
    Fintype.card {f : Fin r ↪ Fin n // Set.range f = Set.range e} = r.factorial := by
  classical
  let g : Equiv.Perm (Fin r) → {f : Fin r ↪ Fin n // Set.range f = Set.range e} :=
    fun σ => ⟨σ.toEmbedding.trans e, embedding_range_comp_perm e σ⟩
  have hg : Function.Bijective g := by
    constructor
    · intro σ τ h
      apply Equiv.ext
      intro i
      apply e.injective
      exact congrArg (fun f => f.val i) h
    · intro f
      obtain ⟨σ, hσ⟩ := same_range_exists_perm e f.val f.property
      refine ⟨σ, ?_⟩
      apply Subtype.ext
      apply Function.Embedding.ext
      exact hσ
  rw [← Fintype.card_congr (Equiv.ofBijective g hg), Fintype.card_perm, Fintype.card_fin]

lemma same_range_card_eq {n r t : ℕ} (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (hef : Set.range e = Set.range f) : r = t := by
  have h := Fintype.card_congr ((Equiv.ofInjective e e.injective).trans
    ((Set.equivOfEq hef).trans (Equiv.ofInjective f f.injective).symm))
  simpa using h

lemma integral_multilinear_pair_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r : ℕ}
    (H G : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (e f : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hi : iIndepFun X μ) (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ) :
    (∫ ω, H (fun i => X (e i) ω) * G (fun i => X (e i) ω) ∂μ) =
      ∫ ω, H (fun i => X (f i) ω) * G (fun i => X (f i) ω) ∂μ := by
  have h := IdentDistrib.pi (fun i => hid (e i) (f i))
    (hi.precomp e.injective) (hi.precomp f.injective)
  exact (h.comp (H.cont.mul G.cont).measurable).integral_eq

lemma integral_multilinear_same_range {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r : ℕ}
    (H G : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin r)) v, G (fun i => v (σ i)) = G v)
    (e f e₀ : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hi : iIndepFun X μ) (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hef : Set.range f = Set.range e) :
    (∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ) =
      ∫ ω, H (fun i => X (e₀ i) ω) * G (fun i => X (e₀ i) ω) ∂μ := by
  obtain ⟨σ, hσ⟩ := same_range_exists_perm e f hef
  have hG (ω : Ω) : G (fun i => X (f i) ω) = G (fun i => X (e i) ω) := by
    calc
      G (fun i => X (f i) ω) = G (fun i => X (e (σ i)) ω) :=
        congrArg G (funext fun i => congrArg (fun j => X j ω) (hσ i).symm)
      _ = _ := hsym σ (fun i => X (e i) ω)
  simp_rw [hG]
  exact integral_multilinear_pair_identDistrib μ H G e e₀ X hi hid

def kernelSum {Ω : Type*} {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  ∑ e : Fin r ↪ Fin n, H (fun i => X (e i) ω)

lemma kernelSum_pair_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r t : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : ContinuousMultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ)
    (hm : ∀ j, Measurable (X j)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ j ω i, |X j ω i| ≤ M) :
    Integrable (fun ω => kernelSum H X ω * kernelSum G X ω) μ := by
  classical
  simp_rw [kernelSum, Finset.sum_mul, Finset.mul_sum]
  apply integrable_finsetSum
  intro e _
  apply integrable_finsetSum
  intro f _
  exact multilinear_pair_integrable μ H.toMultilinearMap G.toMultilinearMap e f X hm M hM hb

/-- Summing all ordered distinct tuples gives exactly `(n)_r r!` surviving pairs. -/
lemma integral_kernelSum_pair {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r : ℕ}
    (H G : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin r)) v, G (fun i => v (σ i)) = G v)
    (e₀ : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = 0) :
    (∫ ω, kernelSum H X ω * kernelSum G X ω ∂μ) =
      (n.descFactorial r : ℝ) * (r.factorial : ℝ) *
        ∫ ω, H (fun i => X (e₀ i) ω) * G (fun i => X (e₀ i) ω) ∂μ := by
  classical
  let J := ∫ ω, H (fun i => X (e₀ i) ω) * G (fun i => X (e₀ i) ω) ∂μ
  have hval (e f : Fin r ↪ Fin n) :
      (∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ) =
        if Set.range f = Set.range e then J else 0 := by
    split_ifs with hef
    · exact integral_multilinear_same_range μ H G hsym e f e₀ X hi hid hef
    · exact integral_multilinear_pair_eq_zero μ H.toMultilinearMap G.toMultilinearMap e f X
        hi hm M hM hb hmean (Ne.symm hef)
  simp_rw [kernelSum, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · calc
      _ = ∑ e : Fin r ↪ Fin n, ∑ f : Fin r ↪ Fin n,
          if Set.range f = Set.range e then J else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        rw [integral_finsetSum]
        · exact Finset.sum_congr rfl (fun f _ => hval e f)
        · intro f _
          exact multilinear_pair_integrable μ H.toMultilinearMap G.toMultilinearMap e f X hm M hM hb
      _ = ∑ _e : Fin r ↪ Fin n, (r.factorial : ℝ) * J := by
        apply Finset.sum_congr rfl
        intro e _
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Fintype.card_subtype, card_same_range_embeddings e]
      _ = _ := by simp [Fintype.card_embedding_eq, J, mul_assoc]
  · intro e _
    exact integrable_finsetSum _ fun f _ =>
      multilinear_pair_integrable μ H.toMultilinearMap G.toMultilinearMap e f X hm M hM hb

lemma integral_kernelSum_pair_different_orders {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r t : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : ContinuousMultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ)
    (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = 0) (hrt : r ≠ t) :
    (∫ ω, kernelSum H X ω * kernelSum G X ω ∂μ) = 0 := by
  classical
  simp_rw [kernelSum, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro e _
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro f _
      exact integral_multilinear_pair_eq_zero μ H.toMultilinearMap G.toMultilinearMap e f X
        hi hm M hM hb hmean (fun h => hrt (same_range_card_eq e f h))
    · intro f _
      exact multilinear_pair_integrable μ H.toMultilinearMap G.toMultilinearMap e f X hm M hM hb
  · intro e _
    exact integrable_finsetSum _ fun f _ =>
      multilinear_pair_integrable μ H.toMultilinearMap G.toMultilinearMap e f X hm M hM hb

lemma multilinear_kernel_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hm : ∀ j, Measurable (X j)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ j ω i, |X j ω i| ≤ M) :
    Integrable (fun ω => H (fun i => X (e i) ω)) μ := by
  classical
  have hexp (ω : Ω) : H (fun i => X (e i) ω) =
      ∑ σ : Fin r → Fin p, H (fun i => Pi.single (σ i) 1) * ∏ i, X (e i) ω (σ i) :=
    multilinear_coordinate_expansion H.toMultilinearMap (fun i => X (e i) ω)
  simp_rw [hexp]
  exact integrable_finsetSum _ fun σ _ =>
    (coordinate_product_integrable μ e σ X hm M hM hb).const_mul _

lemma integral_multilinear_kernel_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hr : 0 < r) (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = 0) :
    (∫ ω, H (fun i => X (e i) ω) ∂μ) = 0 := by
  classical
  have hexp (ω : Ω) : H (fun i => X (e i) ω) =
      ∑ σ : Fin r → Fin p, H (fun i => Pi.single (σ i) 1) * ∏ i, X (e i) ω (σ i) :=
    multilinear_coordinate_expansion H.toMultilinearMap (fun i => X (e i) ω)
  simp_rw [hexp]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro σ _
    rw [integral_const_mul, integral_coordinate_product_eq_zero μ e σ X hi hm hmean
      ⟨0, hr⟩ (fun _ h => e.injective h), mul_zero]
  · intro σ _
    exact (coordinate_product_integrable μ e σ X hm M hM hb).const_mul _

lemma kernelSum_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ)
    (hm : ∀ j, Measurable (X j)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ j ω i, |X j ω i| ≤ M) : Integrable (kernelSum H X) μ := by
  classical
  exact integrable_finsetSum _ fun e _ => multilinear_kernel_integrable μ H e X hm M hM hb

lemma integral_kernelSum_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ)
    (hr : 0 < r) (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = 0) :
    (∫ ω, kernelSum H X ω ∂μ) = 0 := by
  classical
  simp only [kernelSum]
  rw [integral_finsetSum]
  · exact Finset.sum_eq_zero fun e _ =>
      integral_multilinear_kernel_eq_zero μ H e X hr hi hm M hM hb hmean
  · intro e _
    exact multilinear_kernel_integrable μ H e X hm M hM hb

/-- The normalization in the centered expansion of the manuscript's lift. -/
def kernelStatistic {Ω : Type*} {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  ((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ * kernelSum H X ω

lemma kernelStatistic_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ)
    (hm : ∀ j, Measurable (X j)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ j ω i, |X j ω i| ≤ M) : Integrable (kernelStatistic H X) μ :=
  (kernelSum_integrable μ H X hm M hM hb).const_mul _

lemma integral_kernelStatistic_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ)
    (hr : 0 < r) (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = 0) :
    (∫ ω, kernelStatistic H X ω ∂μ) = 0 := by
  simp only [kernelStatistic]
  rw [integral_const_mul,
    integral_kernelSum_eq_zero μ H X hr hi hm M hM hb hmean, mul_zero]

/-- Exact covariance for one symmetric centered multilinear kernel order. -/
theorem covariance_kernelStatistic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r : ℕ}
    (H G : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin r)) v, G (fun i => v (σ i)) = G v)
    (X : Fin n → Ω → Fin p → ℝ) (hr : 0 < r) (hrn : r ≤ n)
    (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = 0) :
    covariance (kernelStatistic H X) (kernelStatistic G X) μ =
      ((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ *
        ∫ ω, H (fun i => X (Fin.castLEEmb hrn i) ω) *
          G (fun i => X (Fin.castLEEmb hrn i) ω) ∂μ := by
  unfold covariance
  rw [integral_kernelStatistic_eq_zero μ H X hr hi hm M hM hb hmean,
    integral_kernelStatistic_eq_zero μ G X hr hi hm M hM hb hmean]
  simp only [sub_zero, kernelStatistic]
  simp_rw [mul_mul_mul_comm]
  rw [integral_const_mul,
    integral_kernelSum_pair μ H G hsym (Fin.castLEEmb hrn) X hi hm hid M hM hb hmean]
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hdesc : (n.descFactorial r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hrn))
  field_simp

lemma kernelStatistic_pair_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r t : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : ContinuousMultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ)
    (hm : ∀ j, Measurable (X j)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ j ω i, |X j ω i| ≤ M) :
    Integrable (fun ω => kernelStatistic H X ω * kernelStatistic G X ω) μ := by
  convert (kernelSum_pair_integrable μ H G X hm M hM hb).const_mul
    (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ *
      ((t.factorial : ℝ) * (n.descFactorial t : ℝ))⁻¹) using 1
  funext ω
  simp only [kernelStatistic]
  ring

lemma integral_kernelStatistic_pair_different_orders {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p r t : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : ContinuousMultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ)
    (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = 0) (hrt : r ≠ t) :
    (∫ ω, kernelStatistic H X ω * kernelStatistic G X ω ∂μ) = 0 := by
  simp only [kernelStatistic]
  simp_rw [mul_mul_mul_comm]
  rw [integral_const_mul,
    integral_kernelSum_pair_different_orders μ H G X hi hm M hM hb hmean hrt, mul_zero]

/-- Finite centered expansion, with the exact coefficients from the paper's Taylor lift. -/
def centeredKernelExpansion {Ω : Type*} {n p R : ℕ} (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  c + ∑ r : Fin R, kernelStatistic (H r) X ω

lemma integral_centeredKernelExpansion {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p R : ℕ} (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ)
    (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = 0) :
    (∫ ω, centeredKernelExpansion c H X ω ∂μ) = c := by
  classical
  simp only [centeredKernelExpansion]
  rw [integral_add (integrable_const c)
    (integrable_finsetSum _ fun r _ => kernelStatistic_integrable μ (H r) X hm M hM hb),
    integral_finsetSum]
  · simp only [integral_const, probReal_univ, one_smul]
    rw [Finset.sum_eq_zero (fun r _ =>
      integral_kernelStatistic_eq_zero μ (H r) X (Nat.succ_pos _) hi hm M hM hb hmean), add_zero]
  · intro r _
    exact kernelStatistic_integrable μ (H r) X hm M hM hb

/-- The full orthogonal sum identity for the centered Taylor kernels. This theorem proves
all probabilistic and tuple-counting steps of the covariance formula of Lemma 7; the
algebraic equality with the polynomial lift is a separate obligation. -/
theorem covariance_centeredKernelExpansion {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p R : ℕ} (c d : ℝ)
    (H G : (r : Fin R) → ContinuousMultilinearMap ℝ (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (hsym : ∀ r (σ : Equiv.Perm (Fin (r.val + 1))) v, G r (fun i => v (σ i)) = G r v)
    (X : Fin n → Ω → Fin p → ℝ) (hR : R ≤ n)
    (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = 0) :
    covariance (centeredKernelExpansion c H X) (centeredKernelExpansion d G X) μ =
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * (n.descFactorial (r.val + 1) : ℝ))⁻¹ *
        ∫ ω, H r (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) *
          G r (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ∂μ := by
  classical
  let J (r : Fin R) := (((r.val + 1).factorial : ℝ) * (n.descFactorial (r.val + 1) : ℝ))⁻¹ *
    ∫ ω, H r (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) *
      G r (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ∂μ
  have hval (r t : Fin R) :
      (∫ ω, kernelStatistic (H r) X ω * kernelStatistic (G t) X ω ∂μ) =
        if r = t then J r else 0 := by
    split_ifs with hrt
    · subst t
      have hc := covariance_kernelStatistic μ (H r) (G r) (hsym r) X (Nat.succ_pos _)
        ((Nat.succ_le_of_lt r.isLt).trans hR) hi hm hid M hM hb hmean
      unfold covariance at hc
      rw [integral_kernelStatistic_eq_zero μ (H r) X (Nat.succ_pos _) hi hm M hM hb hmean,
        integral_kernelStatistic_eq_zero μ (G r) X (Nat.succ_pos _) hi hm M hM hb hmean] at hc
      simpa only [sub_zero] using hc
    · exact integral_kernelStatistic_pair_different_orders μ (H r) (G t) X hi hm M hM hb hmean
        (fun h => hrt (Fin.ext (Nat.add_right_cancel h)))
  unfold covariance
  rw [integral_centeredKernelExpansion μ c H X hi hm M hM hb hmean,
    integral_centeredKernelExpansion μ d G X hi hm M hM hb hmean]
  simp only [centeredKernelExpansion, add_sub_cancel_left]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · calc
      _ = ∑ r : Fin R, ∑ t : Fin R, if r = t then J r else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [integral_finsetSum]
        · exact Finset.sum_congr rfl (fun t _ => hval r t)
        · intro t _
          exact kernelStatistic_pair_integrable μ (H r) (G t) X hm M hM hb
      _ = ∑ r : Fin R, J r := by simp
      _ = _ := rfl
  · intro r _
    exact integrable_finsetSum _ fun t _ =>
      kernelStatistic_pair_integrable μ (H r) (G t) X hm M hM hb

/-- The centered derivative expression appearing in the proof of Lemma 7. -/
def centeredDerivativeLift {Ω : Type*} {n p : ℕ} (R : ℕ)
    (F : MvPolynomial (Fin p) ℝ) (m : Fin p → ℝ)
    (Y : Fin n → Ω → Fin p → ℝ) : Ω → ℝ :=
  centeredKernelExpansion (MvPolynomial.eval m F)
    (fun r : Fin R => iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m) Y

/-- Exact centered derivative covariance, including derivative symmetry proved from
polynomial analyticity. Equality to the original distinct-sample polynomial lift remains
an algebraic translation identity. -/
theorem covariance_centeredDerivativeLift {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p R : ℕ}
    (F G : MvPolynomial (Fin p) ℝ) (m : Fin p → ℝ)
    (Y : Fin n → Ω → Fin p → ℝ) (hR : R ≤ n)
    (hi : iIndepFun Y μ) (hm : ∀ j, Measurable (Y j))
    (hid : ∀ i j, IdentDistrib (Y i) (Y j) μ μ)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |Y j ω i| ≤ M)
    (hmean : ∀ j i, ∫ ω, Y j ω i ∂μ = 0) :
    covariance (centeredDerivativeLift R F m Y) (centeredDerivativeLift R G m Y) μ =
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * (n.descFactorial (r.val + 1) : ℝ))⁻¹ *
        ∫ ω,
          iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m
            (fun i => Y (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) *
          iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x G) m
            (fun i => Y (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ∂μ := by
  apply covariance_centeredKernelExpansion μ (MvPolynomial.eval m F) (MvPolynomial.eval m G)
    _ _ ?_ Y hR hi hm hid M hM hb hmean
  intro r σ v
  exact (AnalyticOnNhd.eval_mvPolynomial G).analyticOn.iteratedFDeriv_comp_perm v σ

lemma integral_centeredDerivativeLift {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p R : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (m : Fin p → ℝ)
    (Y : Fin n → Ω → Fin p → ℝ)
    (hi : iIndepFun Y μ) (hm : ∀ j, Measurable (Y j))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |Y j ω i| ≤ M)
    (hmean : ∀ j i, ∫ ω, Y j ω i ∂μ = 0) :
    (∫ ω, centeredDerivativeLift R F m Y ω ∂μ) = MvPolynomial.eval m F :=
  integral_centeredKernelExpansion μ _ _ Y hi hm M hM hb hmean

/-- Subtraction of the actual population mean preserves independence and identical
laws, and yields bounded centered observations. -/
lemma centerObservations_properties {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p : ℕ}
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = m i) :
    iIndepFun (fun j ω => X j ω - m) μ ∧
      (∀ j, Measurable (fun ω => X j ω - m)) ∧
      (∀ i j, IdentDistrib (fun ω => X i ω - m) (fun ω => X j ω - m) μ μ) ∧
      (∀ j ω i, |X j ω i - m i| ≤ M + ‖m‖) ∧
      (∀ j i, ∫ ω, X j ω i - m i ∂μ = 0) := by
  have hsub : Measurable (fun v : Fin p → ℝ => v - m) := measurable_id.sub measurable_const
  refine ⟨hi.comp (fun _ => fun v : Fin p → ℝ => v - m) (fun _ => hsub),
    fun j => (hm j).sub measurable_const, fun i j => (hid i j).comp hsub, ?_, ?_⟩
  · intro j ω i
    exact (abs_sub (X j ω i) (m i)).trans
      (add_le_add (hb j ω i) (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm m i))
  · intro j i
    have hint : Integrable (fun ω => X j ω i) μ := by
      apply (integrable_const M).mono' (((measurable_pi_apply i).comp (hm j)).aestronglyMeasurable)
      filter_upwards [] with ω
      change |X j ω i| ≤ M
      exact hb j ω i
    rw [integral_sub hint (integrable_const (m i)), hmean,
      integral_const, probReal_univ, one_smul, sub_self]

end RoughRegime.UpperCovariance
