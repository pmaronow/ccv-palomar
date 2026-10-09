module

public import NearlyMinimax.PairCounting


@[expose] public section

/-! Order-two kernel estimates for genuine independent observations. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace NearlyMinimax.PairUStatistic
set_option backward.isDefEq.respectTransparency false

variable {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
variable {ν : Measure Ω} {μ : Measure E} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] in
theorem integral_comp_measurePreserving (f : Ω → E)
    (hf : MeasurePreserving f ν μ) (g : E → ℝ) (hg : Measurable g) :
    (∫ x, g (f x) ∂ν) = ∫ y, g y ∂μ := by
  rw [← hf.map_eq]
  exact (integral_map hf.aemeasurable hg.aestronglyMeasurable).symm

omit [IsProbabilityMeasure μ] in
theorem pair_measurePreserving (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {i j : ι} (hij : i ≠ j) :
    MeasurePreserving (fun x => (X i x, X j x)) ν (μ.prod μ) := by
  refine ⟨(hX i).measurable.prodMk (hX j).measurable, ?_⟩
  rw [(hind.indepFun hij).map_prod_eq_prod_map_map (hX i).aemeasurable
    (hX j).aemeasurable, (hX i).map_eq, (hX j).map_eq]

theorem triple_measurePreserving (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    MeasurePreserving (fun x => ((X i x, X j x), X k x)) ν ((μ.prod μ).prod μ) := by
  refine ⟨((hX i).measurable.prodMk (hX j).measurable).prodMk (hX k).measurable, ?_⟩
  rw [(hind.indepFun_prodMk (fun i => (hX i).measurable) i j k hik hjk).map_prod_eq_prod_map_map
      ((hX i).aemeasurable.prodMk (hX j).aemeasurable) (hX k).aemeasurable,
    (pair_measurePreserving X hind hX hij).map_eq, (hX k).map_eq]

theorem kernel_pair_memLp (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ))
    {i j : ι} (hij : i ≠ j) : MemLp (fun x => K (X i x, X j x)) 2 ν :=
  hK.comp_measurePreserving (pair_measurePreserving X hind hX hij)

theorem kernel_pair_integral (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hK : Measurable K) {i j : ι} (hij : i ≠ j) :
    (∫ x, K (X i x, X j x) ∂ν) = ∫ z, K z ∂μ.prod μ :=
  integral_comp_measurePreserving _ (pair_measurePreserving X hind hX hij) K hK

theorem shared_product_integrable {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    Integrable (fun z : (E × E) × E => K z.1 * K (z.1.1, z.2))
      ((μ.prod μ).prod μ) := by
  have h₁ : MemLp (fun z : (E × E) × E => K z.1) 2 ((μ.prod μ).prod μ) :=
    hK.comp_measurePreserving measurePreserving_fst
  have hm : MeasurePreserving (fun z : (E × E) × E => (z.1.1, z.2))
      ((μ.prod μ).prod μ) (μ.prod μ) :=
    measurePreserving_fst.prod (MeasurePreserving.id μ)
  have h₂ : MemLp (fun z : (E × E) × E => K (z.1.1, z.2)) 2 ((μ.prod μ).prod μ) :=
    hK.comp_measurePreserving hm
  exact h₁.integrable_mul h₂

/-- A kernel centered in its second argument has zero covariance for two
pairs sharing their first observation. Fubini applies to the actual L² law. -/
theorem shared_product_integral_zero {K : E × E → ℝ}
    (hK : MemLp K 2 (μ.prod μ))
    (hcenter : ∀ x, (∫ y, K (x, y) ∂μ) = 0) :
    (∫ z : (E × E) × E, K z.1 * K (z.1.1, z.2) ∂(μ.prod μ).prod μ) = 0 := by
  rw [integral_prod _ (shared_product_integrable hK)]
  simp only [integral_const_mul, hcenter, mul_zero, integral_zero]

theorem kernel_shared_covariance_zero (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    (hcenter : ∀ x, (∫ y, K (x, y) ∂μ) = 0)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∫ x, K (X i x, X j x) * K (X i x, X k x) ∂ν) = 0 := by
  have hg : Measurable (fun z : (E × E) × E => K z.1 * K (z.1.1, z.2)) :=
    (hmK.comp measurable_fst).mul (hmK.comp (measurable_fst.fst.prodMk measurable_snd))
  exact (integral_comp_measurePreserving _
    (triple_measurePreserving X hind hX hij hik hjk) _ hg).trans
    (shared_product_integral_zero hK hcenter)

def rowIntegral (K : E × E → ℝ) (x : E) : ℝ := ∫ y, K (x, y) ∂μ

theorem rowIntegral_measurable {K : E × E → ℝ} (hmK : Measurable K) :
    Measurable (rowIntegral (μ := μ) K) :=
  hmK.stronglyMeasurable.integral_prod_right'.measurable

theorem row_product_integrable {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    Integrable (fun z : E × E => K z * rowIntegral (μ := μ) K z.1) (μ.prod μ) := by
  have hi := (shared_product_integrable hK).integral_prod_left
  simpa only [integral_const_mul, rowIntegral] using hi

theorem rowIntegral_sq_integrable {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    Integrable (fun x => rowIntegral (μ := μ) K x ^ 2) μ := by
  have hi := (row_product_integrable hK).integral_prod_left
  simpa only [integral_mul_const, rowIntegral, pow_two] using hi

theorem shared_product_integral {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    (∫ z : (E × E) × E, K z.1 * K (z.1.1, z.2) ∂(μ.prod μ).prod μ) =
      ∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ := by
  rw [integral_prod _ (shared_product_integrable hK)]
  simp only [integral_const_mul]
  change (∫ z : E × E, K z * rowIntegral (μ := μ) K z.1 ∂μ.prod μ) = _
  rw [integral_prod _ (row_product_integrable hK)]
  simp only [integral_mul_const, rowIntegral, pow_two]

theorem kernel_shared_product_integral (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∫ x, K (X i x, X j x) * K (X i x, X k x) ∂ν) =
      ∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ := by
  have hg : Measurable (fun z : (E × E) × E => K z.1 * K (z.1.1, z.2)) :=
    (hmK.comp measurable_fst).mul (hmK.comp (measurable_fst.fst.prodMk measurable_snd))
  exact (integral_comp_measurePreserving _
    (triple_measurePreserving X hind hX hij hik hjk) _ hg).trans
    (shared_product_integral hK)

theorem kernel_disjoint_product_integral (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K)
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    (∫ x, K (X i x, X j x) * K (X k x, X l x) ∂ν) =
      (∫ z, K z ∂μ.prod μ) ^ 2 := by
  have hd := (hind.indepFun_prodMk_prodMk (fun i => (hX i).measurable)
    i j k l hik hil hjk hjl).comp hmK hmK
  have he := hd.integral_fun_mul_eq_mul_integral
    (hmK.comp ((hX i).measurable.prodMk (hX j).measurable)).aestronglyMeasurable
    (hmK.comp ((hX k).measurable.prodMk (hX l).measurable)).aestronglyMeasurable
  simp only [Function.comp_def] at he
  rw [he, kernel_pair_integral X hind hX hmK hij, kernel_pair_integral X hind hX hmK hkl,
    pow_two]

/-- Ordered-pair U-statistic with its actual finite sample normalization. -/
def pairAverage (n : ℕ) (K : E × E → ℝ) (x : Fin n → E) : ℝ :=
  ((n : ℝ) * (n - 1 : ℕ))⁻¹ * ∑ i, ∑ j with j ≠ i, K (x i, x j)

theorem kernel_pair_sq_integral (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) {i j : ι} (hij : i ≠ j) :
    (∫ x, K (X i x, X j x) ^ 2 ∂ν) = ∫ z, K z ^ 2 ∂μ.prod μ :=
  kernel_pair_integral X hind hX (hmK.pow_const 2) hij

/-- Exact overlap classification for a symmetric kernel. -/
theorem kernel_pair_product_classification (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    (hsym : ∀ x y, K (x, y) = K (y, x))
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) :
    (∫ x, K (X i x, X j x) * K (X k x, X l x) ∂ν) =
      if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then ∫ z, K z ^ 2 ∂μ.prod μ
      else if i = k ∨ i = l ∨ j = k ∨ j = l then
        ∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ else (∫ z, K z ∂μ.prod μ) ^ 2 := by
  classical
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      simpa only [true_and, true_or, or_true, ite_true, pow_two] using
        kernel_pair_sq_integral X hind hX hmK hij
    · have hji : j ≠ i := Ne.symm hij
      simp only [true_and, hjl, and_false, hji, false_or, ite_false, true_or, ite_true]
      exact kernel_shared_product_integral X hind hX hmK hK hij hkl hjl
  · by_cases hil : i = l
    · subst l
      by_cases hjk : j = k
      · subst k
        have he : (fun x => K (X i x, X j x) * K (X j x, X i x)) =
            (fun x => K (X i x, X j x) ^ 2) := by
          funext x
          rw [hsym (X j x) (X i x), pow_two]
        rw [he]
        simp only [and_true, or_true, ite_true]
        exact kernel_pair_sq_integral X hind hX hmK hij
      · have hki : k ≠ i := hkl
        simp only [hik, false_and, true_and, hjk, or_false, ite_false, true_or,
          false_or, ite_true]
        have he : (fun x => K (X i x, X j x) * K (X k x, X i x)) =
            (fun x => K (X i x, X j x) * K (X i x, X k x)) := by
          funext x
          rw [hsym (X k x) (X i x)]
        rw [he]
        exact kernel_shared_product_integral X hind hX hmK hK hij hik hjk
    · by_cases hjk : j = k
      · subst k
        have he : (fun x => K (X i x, X j x) * K (X j x, X l x)) =
            (fun x => K (X j x, X i x) * K (X j x, X l x)) := by
          funext x
          rw [hsym (X i x) (X j x)]
        rw [he]
        simp only [hik, false_and, hil, false_or, true_or, ite_false, ite_true]
        exact kernel_shared_product_integral X hind hX hmK hK (Ne.symm hij) hkl hil
      · by_cases hjl : j = l
        · subst l
          have he : (fun x => K (X i x, X j x) * K (X k x, X j x)) =
              (fun x => K (X j x, X i x) * K (X j x, X k x)) := by
            funext x
            rw [hsym (X i x) (X j x), hsym (X k x) (X j x)]
          rw [he]
          simp only [hik, false_and, hil, hjk, false_or, false_and, ite_false,
            or_true, ite_true]
          exact kernel_shared_product_integral X hind hX hmK hK (Ne.symm hij)
            (Ne.symm hkl) hik
        · simp only [hik, hil, hjk, hjl, false_and, false_or, ite_false]
          exact kernel_disjoint_product_integral X hind hX hmK hij hkl hik hil hjk hjl

theorem kernel_pair_product_le (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    (hsym : ∀ x y, K (x, y) = K (y, x)) (hmean : (∫ z, K z ∂μ.prod μ) = 0)
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) :
    (∫ x, K (X i x, X j x) * K (X k x, X l x) ∂ν) ≤
      (∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ) *
        ((if k = i then 1 else 0) + (if l = i then 1 else 0) +
          (if k = j then 1 else 0) + (if l = j then 1 else 0)) +
      (∫ z, K z ^ 2 ∂μ.prod μ) *
        ((if (k, l) = (i, j) then 1 else 0) + (if (k, l) = (j, i) then 1 else 0)) := by
  have hA : 0 ≤ ∫ z, K z ^ 2 ∂μ.prod μ := integral_nonneg (fun _ => sq_nonneg _)
  have hB : 0 ≤ ∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  rw [kernel_pair_product_classification X hind hX hmK hK hsym hij hkl, hmean, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;>
    subst_vars <;>
    simp_all only [Prod.mk.injEq, ne_eq, eq_comm, not_true_eq_false, eq_self_iff_true, true_and,
      and_true, or_true, true_or, false_and, and_false, false_or, or_false,
      ite_true, ite_false, zero_add, add_zero, mul_zero, mul_one] <;> nlinarith

theorem kernel_pair_covariance_le [DecidableEq ι] (X : ι → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    (hsym : ∀ x y, K (x, y) = K (y, x))
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) :
    covariance (fun x => K (X i x, X j x)) (fun x => K (X k x, X l x)) ν ≤
      (∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ) *
        ((if k = i then 1 else 0) + (if l = i then 1 else 0) +
          (if k = j then 1 else 0) + (if l = j then 1 else 0)) +
      (∫ z, K z ^ 2 ∂μ.prod μ) *
        ((if (k, l) = (i, j) then 1 else 0) + (if (k, l) = (j, i) then 1 else 0)) := by
  have hA : 0 ≤ ∫ z, K z ^ 2 ∂μ.prod μ := integral_nonneg (fun _ => sq_nonneg _)
  have hB : 0 ≤ ∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hc : 0 ≤ (∫ z, K z ∂μ.prod μ) ^ 2 := sq_nonneg _
  rw [covariance_eq_sub (kernel_pair_memLp X hind hX hK hij)
    (kernel_pair_memLp X hind hX hK hkl)]
  simp only [Pi.mul_apply]
  rw [kernel_pair_integral X hind hX hmK hij, kernel_pair_integral X hind hX hmK hkl,
    ← pow_two, kernel_pair_product_classification X hind hX hmK hK hsym hij hkl]
  by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;>
    subst_vars <;>
    simp_all only [Prod.mk.injEq, ne_eq, eq_comm, not_true_eq_false, eq_self_iff_true,
      true_and, and_true, or_true, true_or, false_and, and_false, false_or, or_false,
      ite_true, ite_false, zero_add, add_zero, mul_zero, mul_one, sub_self] <;> nlinarith

theorem pairAverage_eq_orderedPairs {n : ℕ} (K : E × E → ℝ) (x : Fin n → E) :
    pairAverage n K x =
      ((n : ℝ) * (n - 1 : ℕ))⁻¹ * ∑ p ∈ orderedPairs n, K (x p.1, x p.2) := by
  rw [pairAverage, sum_orderedPairs]

theorem pairAverage_memLp_two {n : ℕ} (X : Fin n → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    MemLp (fun x => pairAverage n K (fun i => X i x)) 2 ν := by
  simp only [pairAverage_eq_orderedPairs]
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro p hp
  exact kernel_pair_memLp X hind hX hK (Finset.mem_filter.mp hp).2

theorem pairAverage_integral {n : ℕ} (hn : 2 ≤ n) (X : Fin n → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ)) :
    (∫ x, pairAverage n K (fun i => X i x) ∂ν) = ∫ z, K z ∂μ.prod μ := by
  simp only [pairAverage_eq_orderedPairs]
  rw [integral_const_mul, integral_finsetSum]
  · have he : (∑ p ∈ orderedPairs n, ∫ x, K (X p.1 x, X p.2 x) ∂ν) =
        ∑ _p ∈ orderedPairs n, ∫ z, K z ∂μ.prod μ := by
      apply Finset.sum_congr rfl
      intro p hp
      exact kernel_pair_integral X hind hX hmK (Finset.mem_filter.mp hp).2
    rw [he, Finset.sum_const, orderedPairs_card, nsmul_eq_mul, Nat.cast_mul]
    have hN : (n : ℝ) * (n - 1 : ℕ) ≠ 0 := by
      have hnp : 0 < n := by omega
      have hmp : 0 < n - 1 := by omega
      positivity
    exact inv_mul_cancel_left₀ hN _
  · intro p hp
    exact (kernel_pair_memLp X hind hX hK (Finset.mem_filter.mp hp).2).integrable (by norm_num)

/-- The order-two localized variance bound, valid for unbounded L² kernels.
The four shared slots cost the row energy; the two equal unordered pairs
cost the full kernel energy. -/
theorem pairAverage_variance_le {n : ℕ} (hn : 2 ≤ n) (X : Fin n → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    (hsym : ∀ x y, K (x, y) = K (y, x)) :
    variance (fun x => pairAverage n K (fun i => X i x)) ν ≤
      4 / (n : ℝ) * (∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ) +
      2 / ((n : ℝ) * (n - 1 : ℕ)) * (∫ z, K z ^ 2 ∂μ.prod μ) := by
  let A := ∫ z, K z ^ 2 ∂μ.prod μ
  let B := ∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ
  let Y : (Fin n × Fin n) → Ω → ℝ := fun p x => K (X p.1 x, X p.2 x)
  have hY : ∀ p ∈ orderedPairs n, MemLp (Y p) 2 ν := by
    intro p hp
    exact kernel_pair_memLp X hind hX hK (Finset.mem_filter.mp hp).2
  have hsum : (∑ p ∈ orderedPairs n, ∑ q ∈ orderedPairs n,
      covariance (Y p) (Y q) ν) ≤
      (n : ℝ) * (n - 1 : ℕ) * (4 * (n - 1 : ℕ) * B + 2 * A) := by
    calc
      _ ≤ ∑ p ∈ orderedPairs n, ∑ q ∈ orderedPairs n,
          overlapMajorant p q A B := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        simpa only [Y, overlapMajorant, A, B, Prod.mk.eta, Prod.swap] using
          kernel_pair_covariance_le X hind hX hmK hK hsym
            (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
      _ = ∑ _p ∈ orderedPairs n, (4 * (n - 1 : ℕ) * B + 2 * A) := by
        exact Finset.sum_congr rfl (fun p hp => overlap_majorant_sum hp A B)
      _ = _ := by
        simp only [Finset.sum_const, orderedPairs_card, nsmul_eq_mul, Nat.cast_mul]
  simp only [pairAverage_eq_orderedPairs]
  rw [variance_const_mul, variance_fun_sum' hY]
  calc
    _ ≤ (((n : ℝ) * (n - 1 : ℕ))⁻¹) ^ 2 *
        ((n : ℝ) * (n - 1 : ℕ) * (4 * (n - 1 : ℕ) * B + 2 * A)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hm0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : n - 1 ≠ 0)
      dsimp [A, B]
      field_simp
      <;> ring

/-- Mean-squared fluctuation form used by the ratio estimators. -/
theorem pairAverage_centered_sq_le {n : ℕ} (hn : 2 ≤ n) (X : Fin n → Ω → E)
    (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν μ)
    {K : E × E → ℝ} (hmK : Measurable K) (hK : MemLp K 2 (μ.prod μ))
    (hsym : ∀ x y, K (x, y) = K (y, x)) :
    (∫ x, (pairAverage n K (fun i => X i x) - ∫ z, K z ∂μ.prod μ) ^ 2 ∂ν) ≤
      4 / (n : ℝ) * (∫ x, rowIntegral (μ := μ) K x ^ 2 ∂μ) +
      2 / ((n : ℝ) * (n - 1 : ℕ)) * (∫ z, K z ^ 2 ∂μ.prod μ) := by
  have hv := pairAverage_variance_le hn X hind hX hmK hK hsym
  rw [variance_eq_integral (pairAverage_memLp_two X hind hX hK).aemeasurable,
    pairAverage_integral hn X hind hX hmK hK] at hv
  exact hv

theorem pairAverage_measurable (n : ℕ) {K : E × E → ℝ} (hmK : Measurable K) :
    Measurable (pairAverage n K) := by
  unfold pairAverage
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact hmK.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))

end NearlyMinimax.PairUStatistic
