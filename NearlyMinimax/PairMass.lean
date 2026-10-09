module

public import Mathlib


@[expose] public section

/-!
Finite partition form of (U7-mass), and actual product-measure integrals
underlying scalar factorial lifts.  The partition arguments expose the cell
probabilities and volumes, rather than postulating a bound on pair mass.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace NearlyMinimax

/-- Pair mass of an equal-volume partition with `K` cells. -/
def partitionPairMass {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ) * ∑ i, p i ^ 2

/-- Cauchy--Schwarz proves the lower bound in (U7-mass). -/
theorem partitionPairMass_lower {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hsum : ∑ i, p i = 1) : 1 ≤ partitionPairMass p := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := p)
  simpa [partitionPairMass, hsum] using h

/-- The density cap proves the upper bound in (U7-mass). -/
theorem partitionPairMass_upper {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (pplus : ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hcap : ∀ i, (Fintype.card ι : ℝ) * p i ≤ pplus) :
    partitionPairMass p ≤ pplus := by
  calc
    partitionPairMass p = ∑ i, (Fintype.card ι : ℝ) * p i ^ 2 := by
      simp [partitionPairMass, Finset.mul_sum]
    _ ≤ ∑ i, pplus * p i := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [mul_le_mul_of_nonneg_right (hcap i) (hp i)]
    _ = pplus := by rw [← Finset.mul_sum, hsum, mul_one]

/-- Both total-mass bounds, with the cap written as `pplus / K`. -/
theorem partitionPairMass_bounds {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (pplus : ℝ) (hK : 0 < Fintype.card ι) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1)
    (hcap : ∀ i, p i ≤ pplus / (Fintype.card ι : ℝ)) :
    1 ≤ partitionPairMass p ∧ partitionPairMass p ≤ pplus := by
  refine ⟨partitionPairMass_lower p hsum, partitionPairMass_upper p pplus hp hsum ?_⟩
  intro i
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hK
  have := (le_div_iff₀ hk).mp (hcap i)
  simpa [mul_comm] using this

/-- The localized assertion in (U7-mass): `a i` is the probability of
`A ∩ I_i`, and `v i` is its Lebesgue volume. -/
theorem partitionPairMass_localized {ι : Type*} [Fintype ι]
    (p a v : ι → ℝ) (pplus : ℝ) (hplus : 0 ≤ pplus)
    (ha : ∀ i, 0 ≤ a i)
    (hcap : ∀ i, (Fintype.card ι : ℝ) * p i ≤ pplus)
    (hacap : ∀ i, a i ≤ pplus * v i) :
    (Fintype.card ι : ℝ) * (∑ i, a i * p i) ≤ pplus ^ 2 * ∑ i, v i := by
  calc
    (Fintype.card ι : ℝ) * (∑ i, a i * p i) =
        ∑ i, a i * ((Fintype.card ι : ℝ) * p i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, (pplus * v i) * pplus := by
      apply Finset.sum_le_sum
      intro i _
      calc
        a i * ((Fintype.card ι : ℝ) * p i) ≤ a i * pplus :=
          mul_le_mul_of_nonneg_left (hcap i) (ha i)
        _ ≤ (pplus * v i) * pplus :=
          mul_le_mul_of_nonneg_right (hacap i) hplus
    _ = pplus ^ 2 * ∑ i, v i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Ordered tuples of distinct observations are embeddings. -/
theorem distinctTuple_count (n k : ℕ) :
    Fintype.card (Fin k ↪ Fin n) = n.descFactorial k := by
  simp

/-- The order-two count is the denominator in (U6-order-two). -/
theorem distinctPair_count (n : ℕ) :
    Fintype.card (Fin 2 ↪ Fin n) = n * (n - 1) := by
  rw [distinctTuple_count]
  simp [Nat.descFactorial_succ, mul_comm]

/-- Product kernel over a set of distinct observations. -/
def subsetProduct {ι Ω : Type*} [Fintype ι] (g : Ω → ℝ)
    (s : Finset ι) (x : ι → Ω) : ℝ := ∏ i ∈ s, g (x i)

/-- Scalar degree-`k` factorial lift, written using unordered subsets.
Every ordered tuple gives the same product for each of its `k!` reorderings. -/
def scalarFactorialLift {Ω : Type*} (n k : ℕ) (g : Ω → ℝ)
    (x : Fin n → Ω) : ℝ :=
  (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, subsetProduct g s x) /
    (n.choose k : ℝ)

theorem subsetProduct_integrable {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Integrable g μ) (s : Finset ι) :
    Integrable (subsetProduct g s) (Measure.pi (fun _ : ι => μ)) := by
  classical
  change Integrable (fun x : ι → Ω => ∏ i ∈ s, g (x i)) _
  have h := Integrable.fintype_prod (μ := fun _ : ι => μ)
    (f := fun i x => if i ∈ s then g x else 1)
    (fun i => by by_cases hi : i ∈ s <;> simp [hi, hg])
  simpa only [Fintype.prod_ite_mem] using h

/-- Independence is proved from the product measure; no expectation assumption
is imposed on the product kernel. -/
theorem subsetProduct_integral {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (s : Finset ι) :
    (∫ x : ι → Ω, subsetProduct g s x ∂Measure.pi (fun _ : ι => μ)) =
      (∫ x, g x ∂μ) ^ s.card := by
  classical
  have h := integral_fintype_prod_eq_prod (μ := fun _ : ι => μ)
    (fun i x => if i ∈ s then g x else (1 : ℝ))
  have heq (i : ι) : (∫ x, (if i ∈ s then g x else (1 : ℝ)) ∂μ) =
      if i ∈ s then (∫ x, g x ∂μ) else 1 := by
    by_cases hi : i ∈ s <;> simp [hi]
  simp_rw [heq] at h
  simpa [subsetProduct, Fintype.prod_ite_mem] using h

theorem scalarFactorialLift_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n k : ℕ)
    (g : Ω → ℝ) (hg : Integrable g μ) :
    Integrable (scalarFactorialLift n k g) (Measure.pi (fun _ : Fin n => μ)) := by
  apply Integrable.div_const
  exact integrable_finset_sum _ (fun s _ => subsetProduct_integrable μ g hg s)

/-- Unbiasedness of every scalar monomial lift (including degree zero). -/
theorem scalarFactorialLift_unbiased {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n k : ℕ) (hk : k ≤ n)
    (g : Ω → ℝ) (hg : Integrable g μ) :
    (∫ x : Fin n → Ω, scalarFactorialLift n k g x
      ∂Measure.pi (fun _ : Fin n => μ)) = (∫ x, g x ∂μ) ^ k := by
  classical
  change (∫ x : Fin n → Ω,
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, subsetProduct g s x) /
      (n.choose k : ℝ) ∂Measure.pi (fun _ : Fin n => μ)) = _
  rw [integral_div, integral_finset_sum]
  · have hcard : ((n.choose k : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.choose_pos hk |>.ne'
    have heq : (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        ∫ x : Fin n → Ω, subsetProduct g s x ∂Measure.pi (fun _ : Fin n => μ)) =
        (n.choose k : ℝ) * (∫ x, g x ∂μ) ^ k := by
      calc
        _ = ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (∫ x, g x ∂μ) ^ k := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [subsetProduct_integral, (Finset.mem_powersetCard.mp hs).2]
        _ = _ := by simp [Finset.card_powersetCard]
    rw [heq]
    exact mul_div_cancel_left₀ _ hcard
  · exact fun s _ => subsetProduct_integrable μ g hg s

/-- A scalar polynomial lift is computed coefficient by coefficient. -/
def scalarPolynomialLift {Ω : Type*} (n D : ℕ) (a : ℕ → ℝ) (g : Ω → ℝ)
    (x : Fin n → Ω) : ℝ :=
  ∑ k ∈ Finset.range (D + 1), a k * scalarFactorialLift n k g x

/-- Scalar polynomial unbiasedness is a consequence of actual integration of
the independent products, not a premise about the estimator. -/
theorem scalarPolynomialLift_unbiased {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n D : ℕ) (hD : D ≤ n)
    (a : ℕ → ℝ) (g : Ω → ℝ) (hg : Integrable g μ) :
    (∫ x : Fin n → Ω, scalarPolynomialLift n D a g x
      ∂Measure.pi (fun _ : Fin n => μ)) =
      ∑ k ∈ Finset.range (D + 1), a k * (∫ x, g x ∂μ) ^ k := by
  classical
  change (∫ x : Fin n → Ω,
    ∑ k ∈ Finset.range (D + 1), a k * scalarFactorialLift n k g x
      ∂Measure.pi (fun _ : Fin n => μ)) = _
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_const_mul, scalarFactorialLift_unbiased μ n k _ g hg]
    exact (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hD
  · intro k _
    exact (scalarFactorialLift_integrable μ n k g hg).const_mul (a k)

private theorem subsetProduct_mul_eq {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (g : Ω → ℝ) (s t : Finset ι) (x : ι → Ω) :
    subsetProduct g s x * subsetProduct g t x =
      ∏ i, (if i ∈ s then g (x i) else 1) * (if i ∈ t then g (x i) else 1) := by
  classical
  rw [Finset.prod_mul_distrib]
  simp only [subsetProduct, Fintype.prod_ite_mem]

/-- An L² input makes every covariance term integrable, including overlapping
observation sets. -/
theorem subsetProduct_cross_integrable {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Integrable g μ) (hg2 : Integrable (fun x => g x ^ 2) μ)
    (s t : Finset ι) :
    Integrable (fun x => subsetProduct g s x * subsetProduct g t x)
      (Measure.pi (fun _ : ι => μ)) := by
  classical
  have h := Integrable.fintype_prod (μ := fun _ : ι => μ)
    (f := fun i x => (if i ∈ s then g x else 1) * (if i ∈ t then g x else 1))
    (fun i => by
      by_cases hs : i ∈ s <;> by_cases ht : i ∈ t
      · simpa [hs, ht, pow_two] using hg2
      · simpa [hs, ht] using hg
      · simpa [hs, ht] using hg
      · simp [hs, ht])
  simpa only [← subsetProduct_mul_eq] using h

/-- Centered kernels on unequal observation subsets are orthogonal. An index
present in only one subset gives a zero factor in the product integral. -/
theorem subsetProduct_centered_orthogonal {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hmean : (∫ x, g x ∂μ) = 0) (s t : Finset ι) (hst : s ≠ t) :
    (∫ x : ι → Ω, subsetProduct g s x * subsetProduct g t x
      ∂Measure.pi (fun _ : ι => μ)) = 0 := by
  classical
  simp_rw [subsetProduct_mul_eq]
  rw [integral_fintype_prod_eq_prod
    (fun i x => (if i ∈ s then g x else (1 : ℝ)) * (if i ∈ t then g x else 1))]
  have hex : ∃ i, ¬ (i ∈ s ↔ i ∈ t) := by
    by_contra h
    push_neg at h
    exact hst (Finset.ext h)
  obtain ⟨i, hi⟩ := hex
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases hs : i ∈ s
  · have ht : i ∉ t := fun ht => hi (iff_of_true hs ht)
    simpa [hs, ht] using hmean
  · have ht : i ∈ t := by
      by_contra ht
      exact hi (iff_of_false hs ht)
    simpa [hs, ht] using hmean

/-- Equal observation subsets have squared norm equal to the product of the
input's second moments. -/
theorem subsetProduct_secondMoment {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (s : Finset ι) :
    (∫ x : ι → Ω, (subsetProduct g s x) ^ 2 ∂Measure.pi (fun _ : ι => μ)) =
      (∫ x, g x ^ 2 ∂μ) ^ s.card := by
  have h := subsetProduct_integral μ (fun x => g x ^ 2) s
  simpa [subsetProduct, Finset.prod_pow] using h

end NearlyMinimax
