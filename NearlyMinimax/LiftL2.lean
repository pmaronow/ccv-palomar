module

public import Mathlib
public import RoughRegime.LiftTranslation


@[expose] public section

/-!
# Unbounded square-integrable coordinates in factorial lifts

These lemmas replace pointwise boundedness by genuine `MemLp _ 2` assumptions.
The finite coordinate expansion and the unused-index argument follow the
mathematical construction in the supplied RoughRegime/UpperCovariance.lean;
all integrability here is proved for unbounded independent observations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace NearlyMinimax.LiftL2

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Integrable independent factors have an integrable finite product. -/
theorem independent_finset_product_integrable [IsProbabilityMeasure μ]
    {ι : Type*} [DecidableEq ι] {Y : ι → Ω → ℝ}
    (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (hint : ∀ i, Integrable (Y i) μ) (s : Finset ι) :
    Integrable (fun ω => ∏ i ∈ s, Y i ω) μ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hpfun : (∏ j ∈ s, Y j) = (fun ω => ∏ j ∈ s, Y j ω) := by
      funext ω
      simp
    have hpi : Integrable (∏ j ∈ s, Y j) μ := by rw [hpfun]; exact ih
    have hprod := (hind.indepFun_finsetProd_of_notMem hmeas hi).symm.integrable_mul
      (hint i) hpi
    rw [hpfun] at hprod
    have hp : (Y i * (fun ω => ∏ j ∈ s, Y j ω)) =
        (fun ω => Y i ω * ∏ j ∈ s, Y j ω) := by funext ω; rfl
    rw [hp] at hprod
    simpa only [Finset.prod_insert hi] using hprod

/-- The product of independent `L²` factors remains in `L²`. Independence
prevents the need for higher moments as the number of factors grows. -/
theorem independent_finset_product_memLp_two [IsProbabilityMeasure μ]
    {ι : Type*} [DecidableEq ι] {Y : ι → Ω → ℝ}
    (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (hL2 : ∀ i, MemLp (Y i) 2 μ) (s : Finset ι) :
    MemLp (fun ω => ∏ i ∈ s, Y i ω) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (Finset.measurable_prod s (fun i _ => hmeas i)).aestronglyMeasurable).2
  have hsqind : iIndepFun (fun i ω => Y i ω ^ 2) μ :=
    hind.comp (fun _ => fun y : ℝ => y ^ 2) (fun _ => measurable_id.pow_const 2)
  have hsq := independent_finset_product_integrable hsqind
    (fun i => (hmeas i).pow_const 2) (fun i => (hL2 i).integrable_sq) s
  simpa only [Finset.prod_pow] using hsq

/-- A coordinate monomial uses one square-integrable coordinate from each
of distinct independent observations. -/
theorem coordinate_monomial_memLp_two [IsProbabilityMeasure μ]
    {n p r : ℕ} (e : Fin r ↪ Fin n) (σ : Fin r → Fin p)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (fun ω => ∏ i, X (e i) ω (σ i)) 2 μ := by
  have heind := hind.precomp e.injective
  have hcoord : iIndepFun (fun i ω => X (e i) ω (σ i)) μ :=
    heind.comp (fun i => fun v : Fin p → ℝ => v (σ i))
      (fun i => measurable_pi_apply (σ i))
  exact independent_finset_product_memLp_two hcoord
    (fun i => (measurable_pi_apply (σ i)).comp (hmeas (e i)))
    (fun i => hL2 (e i) (σ i)) Finset.univ

/-- Products of two coordinate monomials are integrable even when their
observation index sets overlap: each observation contributes at most twice. -/
theorem coordinate_monomial_pair_integrable [IsProbabilityMeasure μ]
    {n p r t : ℕ} (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (σ : Fin r → Fin p) (τ : Fin t → Fin p)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    Integrable (fun ω => (∏ i, X (e i) ω (σ i)) *
      (∏ i, X (f i) ω (τ i))) μ := by
  exact ((coordinate_monomial_memLp_two e σ X hind hmeas hL2).integrable_mul
      (coordinate_monomial_memLp_two f τ X hind hmeas hL2)).congr
    (Filter.Eventually.of_forall fun ω => rfl)

/-- Group coordinate factors by their observation index before using independence. -/
theorem coordinate_product_integral_fiberwise [IsProbabilityMeasure μ]
    {A : Type*} [Fintype A] {n p : ℕ}
    (s : A → Fin n) (σ : A → Fin p) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j)) :
    (∫ ω, ∏ i, X (s i) ω (σ i) ∂μ) =
      ∏ j : Fin n, ∫ ω, ∏ i : A with s i = j, X j ω (σ i) ∂μ := by
  classical
  let F : Fin n → (Fin p → ℝ) → ℝ := fun j v => ∏ i : A with s i = j, v (σ i)
  have hF : ∀ j, Measurable (F j) := fun j =>
    Finset.measurable_prod _ (fun i _ => measurable_pi_apply (σ i))
  have hfind : iIndepFun (fun j ω => F j (X j ω)) μ := hind.comp F hF
  have hfun : (fun ω => ∏ i, X (s i) ω (σ i)) =
      (fun ω => ∏ j, F j (X j ω)) := by
    funext ω
    dsimp [F]
    rw [← Finset.prod_fiberwise (Finset.univ : Finset A) s
      (fun i => X (s i) ω (σ i))]
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [hfun]
  exact hfind.integral_fun_prod_eq_prod_integral
    (fun j => ((hF j).comp (hmeas j)).aestronglyMeasurable)

/-- A centered coordinate used at just one observation slot annihilates the
whole expectation. Pair integrability is provided by the previous theorem. -/
theorem coordinate_product_integral_eq_zero [IsProbabilityMeasure μ]
    {A : Type*} [Fintype A] {n p : ℕ}
    (s : A → Fin n) (σ : A → Fin p) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0)
    (k : A) (hk : ∀ i, s i = s k → i = k) :
    (∫ ω, ∏ i, X (s i) ω (σ i) ∂μ) = 0 := by
  classical
  rw [coordinate_product_integral_fiberwise s σ X hind hmeas]
  apply Finset.prod_eq_zero (Finset.mem_univ (s k))
  have hfilter : (Finset.univ.filter (fun i : A => s i = s k)) = {k} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hk i, fun h => by rw [h]⟩
  rw [hfilter]
  simpa using hmean (s k) (σ k)

/-- Coordinate products of two distinct-index tuples are orthogonal if one
tuple contains an observation absent from the other. -/
theorem coordinate_monomial_pair_integral_eq_zero [IsProbabilityMeasure μ]
    {n p r t : ℕ} (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (σ : Fin r → Fin p) (τ : Fin t → Fin p)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0)
    (k : Fin r) (hk : e k ∉ Set.range f) :
    (∫ ω, (∏ i, X (e i) ω (σ i)) * (∏ i, X (f i) ω (τ i)) ∂μ) = 0 := by
  have h := coordinate_product_integral_eq_zero (Sum.elim e f) (Sum.elim σ τ)
    X hind hmeas hmean (Sum.inl k) (by
      intro i hi
      cases i with
      | inl i => exact congrArg Sum.inl (e.injective hi)
      | inr i => exact (hk ⟨i, hi⟩).elim)
  simpa [Fintype.prod_sum_type] using h

/-- Finite coordinate expansion of any multilinear map. -/
theorem multilinear_coordinate_expansion {p r : ℕ}
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (v : Fin r → Fin p → ℝ) :
    H v = ∑ σ : Fin r → Fin p,
      H (fun i => Pi.single (σ i) 1) * ∏ i, v i (σ i) := by
  classical
  have hv : v = fun i => ∑ a : Fin p, v i a • (Pi.single a (1 : ℝ) : Fin p → ℝ) := by
    funext i a
    simp [Pi.single_apply]
  calc
    H v = H (fun i => ∑ a : Fin p, v i a • (Pi.single a (1 : ℝ) : Fin p → ℝ)) := congrArg H hv
    _ = ∑ σ : Fin r → Fin p, H (fun i => v i (σ i) • (Pi.single (σ i) (1 : ℝ) : Fin p → ℝ)) := H.map_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [H.map_smul_univ]
      simp only [smul_eq_mul]
      exact mul_comm _ _

/-- A multilinear kernel applied to distinct independent `L²` observations
is itself square integrable, with no pointwise bound on the observations. -/
theorem multilinear_kernel_memLp_two [IsProbabilityMeasure μ]
    {n p r : ℕ} (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (fun ω => H (fun i => X (e i) ω)) 2 μ := by
  have hexp : (fun ω => H (fun i => X (e i) ω)) =
      fun ω => ∑ σ : Fin r → Fin p,
        H (fun i => Pi.single (σ i) 1) * ∏ i, X (e i) ω (σ i) := by
    funext ω
    exact multilinear_coordinate_expansion H _
  rw [hexp]
  exact memLp_finsetSum Finset.univ (fun σ _ =>
    (coordinate_monomial_memLp_two e σ X hind hmeas hL2).const_mul _)

/-- Two such kernels have an integrable product, including all possible
index overlaps. This discharges the integrability needed to expand covariance. -/
theorem multilinear_kernel_pair_integrable [IsProbabilityMeasure μ]
    {n p r t : ℕ}
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : MultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    Integrable (fun ω => H (fun i => X (e i) ω) * G (fun i => X (f i) ω)) μ := by
  exact ((multilinear_kernel_memLp_two H e X hind hmeas hL2).integrable_mul
      (multilinear_kernel_memLp_two G f X hind hmeas hL2)).congr
    (Filter.Eventually.of_forall fun ω => rfl)

/-- The product of two multilinear kernels expands into coordinate products. -/
theorem multilinear_pair_coordinate_expansion {n p r t : ℕ}
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

/-- Exact orthogonality of degenerate kernels on different observation sets,
with genuine finite second moments in place of pointwise boundedness. -/
theorem multilinear_kernel_pair_integral_eq_zero_left [IsProbabilityMeasure μ]
    {n p r t : ℕ}
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : MultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0)
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
      rw [integral_const_mul,
        coordinate_monomial_pair_integral_eq_zero e f σ τ X hind hmeas hmean k hk,
        mul_zero]
    · intro τ _
      exact (coordinate_monomial_pair_integrable e f σ τ X hind hmeas hL2).const_mul _
  · intro σ _
    exact integrable_finsetSum _ fun τ _ =>
      (coordinate_monomial_pair_integrable e f σ τ X hind hmeas hL2).const_mul _

/-- Range inequality suffices for orthogonality, even at different kernel orders. -/
theorem multilinear_kernel_pair_integral_eq_zero [IsProbabilityMeasure μ]
    {n p r t : ℕ}
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : MultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0)
    (hef : Set.range e ≠ Set.range f) :
    (∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ) = 0 := by
  classical
  by_cases hsub : Set.range e ⊆ Set.range f
  · have hnot : ¬ Set.range f ⊆ Set.range e := fun h => hef (Set.Subset.antisymm hsub h)
    obtain ⟨j, hj, hje⟩ := Set.not_subset.mp hnot
    obtain ⟨k, rfl⟩ := hj
    simpa only [mul_comm] using
      multilinear_kernel_pair_integral_eq_zero_left G H f e X hind hmeas hL2 hmean k hje
  · obtain ⟨j, hj, hjf⟩ := Set.not_subset.mp hsub
    obtain ⟨k, rfl⟩ := hj
    exact multilinear_kernel_pair_integral_eq_zero_left H G e f X hind hmeas hL2 hmean k hjf

/-- Every positive-order multilinear kernel is centered under independent,
coordinatewise centered observations. -/
theorem multilinear_kernel_integral_eq_zero [IsProbabilityMeasure μ]
    {n p r : ℕ} (hr : 0 < r)
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    (∫ ω, H (fun i => X (e i) ω) ∂μ) = 0 := by
  have hexp (ω : Ω) := multilinear_coordinate_expansion H (fun i => X (e i) ω)
  simp_rw [hexp]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro σ _
    rw [integral_const_mul,
      coordinate_product_integral_eq_zero e σ X hind hmeas hmean ⟨0, hr⟩
        (fun i hi => e.injective hi), mul_zero]
  · intro σ _
    exact ((coordinate_monomial_memLp_two e σ X hind hmeas hL2).integrable
      (by norm_num)).const_mul _

/-- Ordered distinct-observation kernel sum. -/
def kernelSum {n p r : ℕ}
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) : Ω → ℝ :=
  fun ω => ∑ e : Fin r ↪ Fin n, H (fun i => X (e i) ω)

/-- Distinct-observation kernel sums are genuinely square integrable. -/
theorem kernelSum_memLp_two [IsProbabilityMeasure μ]
    {n p r : ℕ} (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (kernelSum H X) 2 μ :=
  memLp_finsetSum Finset.univ (fun e _ => multilinear_kernel_memLp_two H e X hind hmeas hL2)

/-- Positive-order kernel sums have mean zero. -/
theorem kernelSum_integral_eq_zero [IsProbabilityMeasure μ]
    {n p r : ℕ} (hr : 0 < r)
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    (∫ ω, kernelSum H X ω ∂μ) = 0 := by
  unfold kernelSum
  rw [integral_finsetSum]
  · exact Finset.sum_eq_zero (fun e _ => multilinear_kernel_integral_eq_zero
      hr H e X hind hmeas hL2 hmean)
  · exact fun e _ => (multilinear_kernel_memLp_two H e X hind hmeas hL2).integrable
      (by norm_num)

/-- Exact covariance expansion into the pairs with equal observation ranges.
This is the probabilistic foundation of the factorial-lift variance identity. -/
theorem kernelSum_covariance_same_range [IsProbabilityMeasure μ]
    {n p r t : ℕ} (hr : 0 < r) (ht : 0 < t)
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : MultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    covariance (kernelSum H X) (kernelSum G X) μ =
      ∑ e : Fin r ↪ Fin n, ∑ f : Fin t ↪ Fin n with Set.range e.toFun = Set.range f.toFun,
        ∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ := by
  classical
  unfold covariance
  rw [kernelSum_integral_eq_zero hr H X hind hmeas hL2 hmean,
    kernelSum_integral_eq_zero ht G X hind hmeas hL2 hmean]
  simp only [sub_zero]
  unfold kernelSum
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro e _
    rw [integral_finsetSum]
    · symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro f _ hf
      have hef : Set.range e ≠ Set.range f := by simpa using hf
      exact multilinear_kernel_pair_integral_eq_zero H G e f X hind hmeas hL2 hmean hef
    · exact fun f _ => multilinear_kernel_pair_integrable H G e f X hind hmeas hL2
  · exact fun e _ => integrable_finsetSum _ (fun f _ =>
      multilinear_kernel_pair_integrable H G e f X hind hmeas hL2)

/-- Equal observation ranges differ by a permutation of the kernel slots. -/
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

/-- Exactly `r!` ordered distinct tuples represent one observation set. -/
lemma card_same_range_embeddings {n r : ℕ} (e : Fin r ↪ Fin n) :
    Fintype.card {f : Fin r ↪ Fin n // Set.range f.toFun = Set.range e.toFun} = r.factorial := by
  classical
  let g : Equiv.Perm (Fin r) → {f : Fin r ↪ Fin n // Set.range f.toFun = Set.range e.toFun} :=
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

/-- Independent identically distributed observations give the same diagonal
kernel integral for every injective tuple. -/
lemma multilinear_pair_integral_identDistrib [IsProbabilityMeasure μ]
    {n p r : ℕ}
    (H G : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (e f : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ) :
    (∫ ω, H (fun i => X (e i) ω) * G (fun i => X (e i) ω) ∂μ) =
      ∫ ω, H (fun i => X (f i) ω) * G (fun i => X (f i) ω) ∂μ := by
  have h := IdentDistrib.pi (fun i => hid (e i) (f i))
    (hind.precomp e.injective) (hind.precomp f.injective)
  exact (h.comp (H.cont.mul G.cont).measurable).integral_eq

lemma multilinear_pair_integral_same_range [IsProbabilityMeasure μ]
    {n p r : ℕ}
    (H G : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin r)) v, G (fun i => v (σ i)) = G v)
    (e f e₀ : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
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
  exact multilinear_pair_integral_identDistrib H G e e₀ X hind hid

/-- The exact factorial covariance of the unnormalized kernel sum, for
square-integrable unbounded i.i.d. observations. -/
theorem kernelSum_covariance [IsProbabilityMeasure μ]
    {n p r : ℕ} (hr : 0 < r)
    (H G : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin r)) v, G (fun i => v (σ i)) = G v)
    (e₀ : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    covariance (kernelSum H.toMultilinearMap X) (kernelSum G.toMultilinearMap X) μ =
      (n.descFactorial r : ℝ) * (r.factorial : ℝ) *
        ∫ ω, H (fun i => X (e₀ i) ω) * G (fun i => X (e₀ i) ω) ∂μ := by
  rw [kernelSum_covariance_same_range hr hr H.toMultilinearMap G.toMultilinearMap
    X hind hmeas hL2 hmean]
  let J := ∫ ω, H (fun i => X (e₀ i) ω) * G (fun i => X (e₀ i) ω) ∂μ
  have hs (e : Fin r ↪ Fin n) :
      (∑ f : Fin r ↪ Fin n with Set.range e.toFun = Set.range f.toFun,
        ∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ) =
      (r.factorial : ℝ) * J := by
    have hsame : (fun f : Fin r ↪ Fin n => Set.range e.toFun = Set.range f.toFun) =
        (fun f : Fin r ↪ Fin n => Set.range f.toFun = Set.range e.toFun) := by
      funext f
      exact propext eq_comm
    have hfilterEq : Finset.univ.filter (fun f : Fin r ↪ Fin n =>
        Set.range e.toFun = Set.range f.toFun) =
        Finset.univ.filter (fun f : Fin r ↪ Fin n =>
        Set.range f.toFun = Set.range e.toFun) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact eq_comm
    rw [hfilterEq]
    calc
      _ = ∑ f : Fin r ↪ Fin n with Set.range f.toFun = Set.range e.toFun, J := by
        apply Finset.sum_congr rfl
        intro f hf
        exact multilinear_pair_integral_same_range H G hsym e f e₀ X hind hid
          (Finset.mem_filter.mp hf).2
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Fintype.card_subtype, card_same_range_embeddings e]
  change (∑ e : Fin r ↪ Fin n,
    ∑ f : Fin r ↪ Fin n with Set.range e.toFun = Set.range f.toFun,
      ∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ) = _
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_embedding_eq, Fintype.card_fin]
  dsimp [J]
  ring

/-- Kernel sums of different positive orders are exactly orthogonal. -/
theorem kernelSum_covariance_different_orders [IsProbabilityMeasure μ]
    {n p r t : ℕ} (hr : 0 < r) (ht : 0 < t) (hrt : r ≠ t)
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : MultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    covariance (kernelSum H X) (kernelSum G X) μ = 0 := by
  rw [kernelSum_covariance_same_range hr ht H G X hind hmeas hL2 hmean]
  apply Finset.sum_eq_zero
  intro e _
  have hfilter : Finset.univ.filter (fun f : Fin t ↪ Fin n =>
      Set.range e.toFun = Set.range f.toFun) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    exact hrt (same_range_card_eq e f (Finset.mem_filter.mp hf).2)
  rw [hfilter, Finset.sum_empty]

/-- The normalization appearing in the centered Taylor lift. -/
def kernelStatistic {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) : Ω → ℝ :=
  fun ω => (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹) *
    kernelSum H.toMultilinearMap X ω

/-- Exact variance of one centered symmetric factorial-lift term, with finite
second moments and no pointwise boundedness restriction. -/
theorem kernelStatistic_variance [IsProbabilityMeasure μ]
    {n p r : ℕ} (hr : 0 < r) (hrn : r ≤ n)
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin r)) v, H (fun i => v (σ i)) = H v)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    variance (kernelStatistic H X) μ =
      (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹) *
        ∫ ω, H (fun i => X (Fin.castLEEmb hrn i) ω) ^ 2 ∂μ := by
  unfold kernelStatistic
  rw [variance_const_mul, ← covariance_self
    (kernelSum_memLp_two H.toMultilinearMap X hind hmeas hL2).aemeasurable,
    kernelSum_covariance hr H H hsym (Fin.castLEEmb hrn) X hind hmeas hid hL2 hmean]
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hdesc : (n.descFactorial r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hrn))
  simp only [← pow_two]
  field_simp

/-- The finite centered-kernel expansion of a polynomial lift. -/
def centeredKernelExpansion {n p R : ℕ} (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ
      (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) : Ω → ℝ :=
  fun ω => c + ∑ r, kernelStatistic (H r) X ω

theorem kernelStatistic_memLp_two [IsProbabilityMeasure μ]
    {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (kernelStatistic H X) 2 μ :=
  (kernelSum_memLp_two H.toMultilinearMap X hind hmeas hL2).const_mul _

theorem centeredKernelExpansion_memLp_two [IsProbabilityMeasure μ]
    {n p R : ℕ} (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ
      (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (centeredKernelExpansion c H X) 2 μ :=
  (memLp_const c).add (memLp_finsetSum Finset.univ (fun r _ =>
    kernelStatistic_memLp_two (H r) X hind hmeas hL2))

theorem kernelStatistic_integral_eq_zero [IsProbabilityMeasure μ]
    {n p r : ℕ} (hr : 0 < r)
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    (∫ ω, kernelStatistic H X ω ∂μ) = 0 := by
  unfold kernelStatistic
  rw [integral_const_mul,
    kernelSum_integral_eq_zero hr H.toMultilinearMap X hind hmeas hL2 hmean, mul_zero]

theorem centeredKernelExpansion_expectation [IsProbabilityMeasure μ]
    {n p R : ℕ} (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ
      (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    (∫ ω, centeredKernelExpansion c H X ω ∂μ) = c := by
  unfold centeredKernelExpansion
  have hs : Integrable (fun ω => ∑ r, kernelStatistic (H r) X ω) μ :=
    (memLp_finsetSum Finset.univ (fun r _ =>
      kernelStatistic_memLp_two (H r) X hind hmeas hL2)).integrable (by norm_num)
  rw [integral_add (integrable_const c) hs, integral_const,
    integral_finsetSum Finset.univ (fun r _ =>
      (kernelStatistic_memLp_two (H r) X hind hmeas hL2).integrable (by norm_num))]
  have hz : (∑ r : Fin R, ∫ ω, kernelStatistic (H r) X ω ∂μ) = 0 :=
    Finset.sum_eq_zero (fun r _ => kernelStatistic_integral_eq_zero
      (Nat.succ_pos r.val) (H r) X hind hmeas hL2 hmean)
  simp [hz]

/-- Exact centered Taylor variance series under the original paper's finite
second-moment hypothesis, without restricting the responses to a bounded set. -/
theorem centeredKernelExpansion_variance [IsProbabilityMeasure μ]
    {n p R : ℕ} (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ
      (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (hsym : ∀ r (σ : Equiv.Perm (Fin (r.val + 1))) v,
      H r (fun i => v (σ i)) = H r v)
    (X : Fin n → Ω → Fin p → ℝ) (hR : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    variance (centeredKernelExpansion c H X) μ =
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) *
        (n.descFactorial (r.val + 1) : ℝ))⁻¹ *
        ∫ ω, H r (fun i => X
          (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ^ 2 ∂μ := by
  have hstats (r : Fin R) := kernelStatistic_memLp_two (H r) X hind hmeas hL2
  have hsum : MemLp (fun ω => ∑ r, kernelStatistic (H r) X ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun r _ => hstats r)
  unfold centeredKernelExpansion
  rw [variance_const_add hsum.aestronglyMeasurable c, variance_fun_sum hstats]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_eq_single r]
  · rw [covariance_self (hstats r).aemeasurable]
    exact kernelStatistic_variance (by omega)
      ((Nat.succ_le_of_lt r.isLt).trans hR) (H r) (hsym r) X hind hmeas hid hL2 hmean
  · intro t _ htr
    unfold kernelStatistic
    rw [covariance_const_mul_left, covariance_const_mul_right]
    have hrt : r.val + 1 ≠ t.val + 1 := by
      intro h
      apply htr
      apply Fin.ext
      omega
    rw [kernelSum_covariance_different_orders (by omega) (by omega) hrt
      (H r).toMultilinearMap (H t).toMultilinearMap X hind hmeas hL2 hmean]
    ring
  · exact fun h => (h (Finset.mem_univ r)).elim

/-- Centering preserves all the actual probability and moment hypotheses. -/
theorem centerObservations_l2 [IsProbabilityMeasure μ]
    {n p : ℕ} (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a) :
    iIndepFun (fun j ω => X j ω - m) μ ∧
      (∀ j, Measurable (fun ω => X j ω - m)) ∧
      (∀ i j, IdentDistrib (fun ω => X i ω - m) (fun ω => X j ω - m) μ μ) ∧
      (∀ j a, MemLp (fun ω => X j ω a - m a) 2 μ) ∧
      (∀ j a, ∫ ω, X j ω a - m a ∂μ = 0) := by
  refine ⟨hind.comp (fun _ => fun v : Fin p → ℝ => v - m)
      (fun _ => measurable_id.sub_const m),
    fun j => (hmeas j).sub_const m,
    fun i j => (hid i j).comp (measurable_id.sub_const m),
    fun j a => (hL2 j a).sub (memLp_const (m a)), ?_⟩
  intro j a
  rw [integral_sub ((hL2 j a).integrable (by norm_num)) (integrable_const (m a)),
    integral_const, hmean]
  simp

/-- The supplied coefficient lift is the centered Taylor expansion. This
uses only the imported algebraic lift identity, which has no boundedness premise. -/
theorem polynomialLift_centering_l2 {n p R : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n) :
    RoughRegime.Upper.polynomialLift F X =
      centeredKernelExpansion (MvPolynomial.eval m F)
        (fun r : Fin R => iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m)
        (fun j ω => X j ω - m) := by
  rw [RoughRegime.LiftTranslation.polynomialLift_eq_centeredDerivativeLift F X m hdeg hRn]
  rfl

/-- Original `lem:U6` exact variance identity for the actual unbiased polynomial
lift on unbounded i.i.d. `L²` features. -/
theorem polynomialLift_variance_l2 [IsProbabilityMeasure μ]
    {n p R : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a) :
    variance (RoughRegime.Upper.polynomialLift F X) μ =
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) *
        (n.descFactorial (r.val + 1) : ℝ))⁻¹ *
        ∫ ω, (iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m
          (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hRn) i) ω - m)) ^ 2 ∂μ := by
  obtain ⟨hi, hm, hid', hlp, hzero⟩ := centerObservations_l2 X m hind hmeas hid hL2 hmean
  rw [polynomialLift_centering_l2 F X m hdeg hRn]
  apply centeredKernelExpansion_variance _ _ ?_ _ hRn hi hm hid' hlp hzero
  intro r σ v
  exact (AnalyticOnNhd.eval_mvPolynomial F).analyticOn.iteratedFDeriv_comp_perm v σ

/-- Coordinatewise `L²` gives an integrable vector with the coordinate means. -/
theorem vector_integral_of_coordinate_moments [IsProbabilityMeasure μ]
    {p : ℕ} (X : Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hL2 : ∀ a, MemLp (fun ω => X ω a) 2 μ)
    (hmean : ∀ a, ∫ ω, X ω a ∂μ = m a) :
    Integrable X μ ∧ (∫ ω, X ω ∂μ) = m := by
  have hi : Integrable X μ := integrable_pi_iff.mpr fun a =>
    (hL2 a).integrable (by norm_num)
  refine ⟨hi, ?_⟩
  funext a
  exact ((ContinuousLinearMap.proj a : (Fin p → ℝ) →L[ℝ] ℝ).integral_comp_comm hi).symm.trans (hmean a)

/-- Subtracting the mean contracts the scalar `L²` norm of every linear functional. -/
theorem linear_centering_square_le_l2 [IsProbabilityMeasure μ]
    {p : ℕ} (X : Ω → Fin p → ℝ) (hm : Measurable X)
    (hL2 : ∀ a, MemLp (fun ω => X ω a) 2 μ)
    (m : Fin p → ℝ) (hmean : ∀ a, ∫ ω, X ω a ∂μ = m a)
    (L : (Fin p → ℝ) →L[ℝ] ℝ) :
    (∫ ω, L (X ω - m) ^ 2 ∂μ) ≤ ∫ ω, L (X ω) ^ 2 ∂μ := by
  obtain ⟨hi, hvector⟩ := vector_integral_of_coordinate_moments X m hL2 hmean
  have hLX : Measurable (fun ω => L (X ω)) := L.continuous.measurable.comp hm
  have hml : (∫ ω, L (X ω) ∂μ) = L m := by
    rw [L.integral_comp_comm hi, hvector]
  have hv := variance_le_expectation_sq (μ := μ) hLX.aestronglyMeasurable
  rw [variance_eq_integral hLX.aemeasurable, hml] at hv
  simpa only [map_sub, Pi.pow_apply] using hv

/-- Independent copies of possibly different coordinatewise `L²` vectors have
an integrable squared multilinear kernel. -/
theorem product_kernel_square_integrable_l2 [IsProbabilityMeasure μ]
    {p r : ℕ} (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (A : Fin r → Ω → Fin p → ℝ) (hm : ∀ i, Measurable (A i))
    (hL2 : ∀ i a, MemLp (fun ω => A i ω a) 2 μ) :
    Integrable (fun ω : Fin r → Ω => H (fun i => A i (ω i)) ^ 2)
      (Measure.pi (fun _ => μ)) := by
  let X : Fin r → (Fin r → Ω) → Fin p → ℝ := fun i ω => A i (ω i)
  have hind : iIndepFun X (Measure.pi (fun _ : Fin r => μ)) :=
    iIndepFun_pi (fun i => (hm i).aemeasurable)
  have hmeas : ∀ i, Measurable (X i) := fun i => (hm i).comp (measurable_pi_apply i)
  have hlp : ∀ i a, MemLp (fun ω => X i ω a) 2 (Measure.pi (fun _ : Fin r => μ)) := by
    intro i a
    exact (hL2 i a).comp_measurePreserving (measurePreserving_eval (fun _ : Fin r => μ) i)
  exact (multilinear_kernel_memLp_two H.toMultilinearMap (Function.Embedding.refl _) X
    hind hmeas hlp).integrable_sq

lemma integral_pi_succ_l2 [IsProbabilityMeasure μ] {r : ℕ}
    (f : (Fin (r + 1) → Ω) → ℝ) (hf : Integrable f (Measure.pi (fun _ => μ))) :
    (∫ x, f x ∂Measure.pi (fun _ : Fin (r + 1) => μ)) =
      ∫ x, ∫ y, f (Fin.cons x y) ∂Measure.pi (fun _ : Fin r => μ) ∂μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => Ω) 0
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => μ) 0
  have hf' : Integrable (f ∘ e.symm) (μ.prod (Measure.pi (fun _ : Fin r => μ))) :=
    (he.symm e).integrable_comp_of_integrable hf
  rw [← (he.symm e).integral_comp' f]
  change (∫ x, (f ∘ e.symm) x ∂μ.prod (Measure.pi (fun _ : Fin r => μ))) = _
  rw [integral_prod _ hf']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      apply congrArg f
      funext i
      cases i using Fin.cases <;> simp [e]

lemma kernel_cons_square_integrable_l2 [IsProbabilityMeasure μ] {p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin (r + 1) => Fin p → ℝ) ℝ)
    (A B : Ω → Fin p → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hL2A : ∀ a, MemLp (fun ω => A ω a) 2 μ)
    (hL2B : ∀ a, MemLp (fun ω => B ω a) 2 μ) :
    Integrable (fun xy : Ω × (Fin r → Ω) =>
      H (Fin.cons (A xy.1) (fun j => B (xy.2 j))) ^ 2)
      (μ.prod (Measure.pi (fun _ : Fin r => μ))) := by
  let C : Fin (r + 1) → Ω → Fin p → ℝ := Fin.cons A (fun _ => B)
  have hC : ∀ i, Measurable (C i) := by
    intro i
    cases i using Fin.cases <;> simp [C, hA, hB]
  have hlpC : ∀ i a, MemLp (fun ω => C i ω a) 2 μ := by
    intro i a
    cases i using Fin.cases
    · simpa [C] using hL2A a
    · simpa [C] using hL2B a
  have hf := product_kernel_square_integrable_l2 H C hC hlpC
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => Ω) 0
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => μ) 0
  have hf' := (he.symm e).integrable_comp_of_integrable hf
  apply hf'.congr
  exact Filter.Eventually.of_forall fun xy => by
    change (H (fun i => C i (e.symm xy i))) ^ 2 = _
    apply congrArg (fun z : ℝ => z ^ 2)
    apply congrArg H
    funext i
    cases i using Fin.cases <;> simp [C, e]

/-- Centering each slot of an independent multilinear kernel contracts its
squared norm. Only finite second moments are required. -/
theorem multilinear_iid_centering_square_le_l2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Ω → Fin p → ℝ) (hm : Measurable X)
    (hL2 : ∀ a, MemLp (fun ω => X ω a) 2 μ)
    (m : Fin p → ℝ) (hmean : ∀ a, ∫ ω, X ω a ∂μ = m a) :
    (∫ ω, H (fun j => X (ω j) - m) ^ 2 ∂Measure.pi (fun _ : Fin r => μ)) ≤
      ∫ ω, H (fun j => X (ω j)) ^ 2 ∂Measure.pi (fun _ : Fin r => μ) := by
  induction r with
  | zero =>
    apply le_of_eq
    congr 1
    funext ω
    congr 2
    funext j
    exact Fin.elim0 j
  | succ r ih =>
    let Y : Ω → Fin p → ℝ := fun ω => X ω - m
    have hY : Measurable Y := hm.sub measurable_const
    have hYlp : ∀ a, MemLp (fun ω => Y ω a) 2 μ := fun a =>
      (hL2 a).sub (memLp_const (m a))
    have hc := kernel_cons_square_integrable_l2 H Y Y hY hY hYlp hYlp
    have hmix := kernel_cons_square_integrable_l2 H X Y hm hY hL2 hYlp
    have hu := kernel_cons_square_integrable_l2 H X X hm hm hL2 hL2
    have hiCenter := product_kernel_square_integrable_l2 H (fun _ => Y) (fun _ => hY) (fun _ => hYlp)
    have hiUncenter := product_kernel_square_integrable_l2 H (fun _ => X) (fun _ => hm) (fun _ => hL2)
    calc
      _ = ∫ x, ∫ y, H (Fin.cons (Y x) (fun j => Y (y j))) ^ 2
          ∂Measure.pi (fun _ : Fin r => μ) ∂μ := by
        rw [integral_pi_succ_l2 _ hiCenter]
        congr 1
        funext x
        congr 1
        funext y
        congr 2
        funext j
        cases j using Fin.cases <;> simp
      _ = ∫ y, ∫ x, H (Fin.cons (Y x) (fun j => Y (y j))) ^ 2
          ∂μ ∂Measure.pi (fun _ : Fin r => μ) := integral_integral_swap hc
      _ ≤ ∫ y, ∫ x, H (Fin.cons (X x) (fun j => Y (y j))) ^ 2
          ∂μ ∂Measure.pi (fun _ : Fin r => μ) := by
        apply integral_mono_ae hc.integral_prod_right hmix.integral_prod_right
        exact Filter.Eventually.of_forall fun y => by
          let L : (Fin p → ℝ) →L[ℝ] ℝ :=
            (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Fin p → ℝ) ℝ
              (fun j => Y (y j))).comp H.curryLeft
          simpa only [L, ContinuousLinearMap.comp_apply,
            ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.curryLeft_apply]
            using linear_centering_square_le_l2 X hm hL2 m hmean L
      _ = ∫ x, ∫ y, H (Fin.cons (X x) (fun j => Y (y j))) ^ 2
          ∂Measure.pi (fun _ : Fin r => μ) ∂μ := (integral_integral_swap hmix).symm
      _ ≤ ∫ x, ∫ y, H (Fin.cons (X x) (fun j => X (y j))) ^ 2
          ∂Measure.pi (fun _ : Fin r => μ) ∂μ := by
        apply integral_mono_ae hmix.integral_prod_left hu.integral_prod_left
        exact Filter.Eventually.of_forall fun x => by
          simpa only [ContinuousMultilinearMap.curryLeft_apply] using ih (H.curryLeft (X x))
      _ = _ := by
        rw [integral_pi_succ_l2 _ hiUncenter]
        congr 1
        funext x
        congr 1
        funext y
        congr 2
        funext j
        cases j using Fin.cases <;> simp


/-- The `L²` contraction transfers from independent product copies to actual
i.i.d. observations on an arbitrary probability space. -/
theorem independent_centering_square_le_l2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin r → Ω → Fin p → ℝ) (hm : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ i a, MemLp (fun ω => X i ω a) 2 μ)
    (m : Fin p → ℝ) (hmean : ∀ i a, ∫ ω, X i ω a ∂μ = m a) :
    (∫ ω, H (fun i => X i ω - m) ^ 2 ∂μ) ≤ ∫ ω, H (fun i => X i ω) ^ 2 ∂μ := by
  by_cases hr : r = 0
  · subst r
    apply le_of_eq
    congr 1
    funext ω
    congr 2
    funext i
    exact Fin.elim0 i
  · let j : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    have hcopy : Measurable (fun ω : Fin r → Ω => fun i => X j (ω i)) :=
      measurable_pi_iff.mpr fun i => (hm j).comp (measurable_pi_apply i)
    have hjoint : Measurable (fun ω => fun i => X i ω) :=
      measurable_pi_iff.mpr hm
    have hjointLaw : IdentDistrib (fun ω => fun i => X i ω)
        (fun ω : Fin r → Ω => fun i => X j (ω i)) μ (Measure.pi (fun _ => μ)) := by
      refine ⟨hjoint.aemeasurable, hcopy.aemeasurable, ?_⟩
      rw [hind.map_fun_eq_pi_map (fun i => (hm i).aemeasurable),
        Measure.pi_map_pi (fun _ => (hm j).aemeasurable)]
      congr 1
      funext i
      exact (hid i j).map_eq
    have hc : Measurable (fun v : Fin r → Fin p → ℝ => H (fun i => v i - m) ^ 2) :=
      (H.coe_continuous.measurable.comp
        (measurable_pi_iff.mpr fun i => (measurable_pi_apply i).sub measurable_const)).pow_const 2
    have hu : Measurable (fun v : Fin r → Fin p → ℝ => H v ^ 2) :=
      H.coe_continuous.measurable.pow_const 2
    have hcEq : (∫ ω, H (fun i => X i ω - m) ^ 2 ∂μ) =
        ∫ ω, H (fun i => X j (ω i) - m) ^ 2 ∂Measure.pi (fun _ : Fin r => μ) := by
      simpa only [Function.comp_def] using (hjointLaw.comp hc).integral_eq
    have huEq : (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) =
        ∫ ω, H (fun i => X j (ω i)) ^ 2 ∂Measure.pi (fun _ : Fin r => μ) := by
      simpa only [Function.comp_def] using (hjointLaw.comp hu).integral_eq
    rw [hcEq, huEq]
    exact multilinear_iid_centering_square_le_l2 μ H (X j) (hm j) (hL2 j) m (hmean j)


/-- The actual coefficient lift is square integrable under coordinatewise `L²`. -/
theorem polynomialLift_memLp_two_l2 [IsProbabilityMeasure μ]
    {n p R : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (RoughRegime.Upper.polynomialLift F X) 2 μ := by
  rw [polynomialLift_centering_l2 F X m hdeg hRn]
  exact centeredKernelExpansion_memLp_two _ _ _
    (hind.comp (fun _ => fun v : Fin p → ℝ => v - m)
      (fun _ => measurable_id.sub_const m))
    (fun j => (hmeas j).sub_const m)
    (fun j a => (hL2 j a).sub (memLp_const (m a)))

/-- The coefficient lift is unbiased at the actual population mean. -/
theorem polynomialLift_expectation_l2 [IsProbabilityMeasure μ]
    {n p R : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a) :
    (∫ ω, RoughRegime.Upper.polynomialLift F X ω ∂μ) = MvPolynomial.eval m F := by
  obtain ⟨hi, hm, _, hlp, hzero⟩ := centerObservations_l2 X m hind hmeas hid hL2 hmean
  rw [polynomialLift_centering_l2 F X m hdeg hRn]
  exact centeredKernelExpansion_expectation _ _ _ hi hm hlp hzero

/-- Original U6 comparison with the true descending-factorial denominators. -/
theorem polynomialLift_variance_le_raw_l2 [IsProbabilityMeasure μ]
    {n p R : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a) :
    variance (RoughRegime.Upper.polynomialLift F X) μ ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) *
        (n.descFactorial (r.val + 1) : ℝ))⁻¹ *
        ∫ ω, (iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m
          (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hRn) i) ω)) ^ 2 ∂μ := by
  rw [polynomialLift_variance_l2 F X m hdeg hRn hind hmeas hid hL2 hmean]
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  let e := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hRn)
  exact independent_centering_square_le_l2 μ _ (fun i => X (e i))
    (fun i => hmeas (e i)) (hind.precomp e.injective)
    (fun i j => hid (e i) (e j)) (fun i a => hL2 (e i) a) m
    (fun i a => hmean (e i) a)

/-- A positive lower bound on each available observation count bounds the
whole descending factorial. -/
theorem descFactorial_lower_bound {n R k : ℕ} (hRn : R ≤ n) (hkR : k ≤ R)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    Λ ^ k ≤ (n.descFactorial k : ℝ) := by
  have hkn : k ≤ n + 1 := by omega
  have hcast : ((n + 1 - k : ℕ) : ℝ) = (n : ℝ) + 1 - k := by
    rw [Nat.cast_sub hkn, Nat.cast_add, Nat.cast_one]
  have hRk : (k : ℝ) ≤ R := by exact_mod_cast hkR
  have hbase : Λ ≤ ((n + 1 - k : ℕ) : ℝ) := by rw [hcast]; linarith
  calc
    Λ ^ k ≤ (((n + 1 - k : ℕ) : ℝ)) ^ k := pow_le_pow_left₀ hΛ hbase k
    _ ≤ (n.descFactorial k : ℝ) := by exact_mod_cast Nat.pow_sub_le_descFactorial n k

/-- The denominator comparison in U6 for every `0 < Λ ≤ n - degree + 1`. -/
theorem polynomialLift_variance_le_raw_power_l2 [IsProbabilityMeasure μ]
    {n p R : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    variance (RoughRegime.Upper.polynomialLift F X) μ ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
        ∫ ω, (iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m
          (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hRn) i) ω)) ^ 2 ∂μ := by
  apply (polynomialLift_variance_le_raw_l2 F X m hdeg hRn hind hmeas hid hL2 hmean).trans
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun _ => sq_nonneg _)
  have hb := descFactorial_lower_bound hRn (Nat.succ_le_of_lt r.isLt) hΛ.le hΛn
  have hfac : 0 < ((r.val + 1).factorial : ℝ) := by positivity
  have hpow : 0 < Λ ^ (r.val + 1) := pow_pos hΛ _
  exact (inv_le_inv₀ (mul_pos hfac (hpow.trans_le hb)) (mul_pos hfac hpow)).2
    (mul_le_mul_of_nonneg_left hb hfac.le)

end NearlyMinimax.LiftL2




