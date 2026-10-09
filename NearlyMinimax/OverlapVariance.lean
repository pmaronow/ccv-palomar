module

public import NearlyMinimax.DesignCounts


@[expose] public section

/-! # Disjoint-support orthogonality and overlap variance

Product response measures give independence of disjoint coordinate patches.
A graph with bounded closed degree converts this orthogonality into an
energy bound for the sum of the patch scores.
-/

namespace NearlyMinimax

open MeasureTheory ProbabilityTheory

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem overlap_matrix_sum_bound {ι : Type*} [Fintype ι] (A : ι → ι → Prop)
    (hsym : ∀ i j, A i j ↔ A j i) (D : ℕ) (e : ι → ℝ) (c : ι → ι → ℝ)
    (he : ∀ i, 0 ≤ e i) (hdegree : ∀ i, (Finset.univ.filter (A i)).card ≤ D)
    (hzero : ∀ i j, ¬A i j → c i j = 0)
    (hpair : ∀ i j, c i j ≤ (1 / 2 : ℝ) * (e i + e j)) :
    (∑ i, ∑ j, c i j) ≤ D * ∑ i, e i := by
  have hpoint (i j : ι) : c i j ≤
      (1 / 2 : ℝ) * (if A i j then e i else 0) +
        (1 / 2 : ℝ) * (if A i j then e j else 0) := by
    by_cases h : A i j
    · simp only [if_pos h]
      nlinarith [hpair i j]
    · simp [h, hzero i j h]
  have htranspose : (∑ i, ∑ j, if A i j then e j else 0) =
      ∑ i, ∑ j, if A i j then e i else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have hrow : (∑ i, ∑ j, if A i j then e i else 0) ≤ D * ∑ i, e i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree i) (he i)
  calc
    _ ≤ ∑ i, ∑ j, ((1 / 2 : ℝ) * (if A i j then e i else 0) +
        (1 / 2 : ℝ) * (if A i j then e j else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun j _ => hpoint i j)
    _ = (1 / 2 : ℝ) * (∑ i, ∑ j, if A i j then e i else 0) +
        (1 / 2 : ℝ) * (∑ i, ∑ j, if A i j then e j else 0) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ D * ∑ i, e i := by rw [htranspose]; linarith

/-- Bounded-degree covariance aggregation for actual finite-measure expectations. -/
theorem finite_overlap_variance_bound {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (r : ι → Ω → ℝ) (A : ι → ι → Prop) (D : ℕ)
    (hsym : ∀ i j, A i j ↔ A j i) (hdegree : ∀ i, (Finset.univ.filter (A i)).card ≤ D)
    (hzero : ∀ i j, ¬A i j → (∫ x, r i x * r j x ∂μ) = 0) :
    (∫ x, (∑ i, r i x) ^ 2 ∂μ) ≤ D * ∑ i, ∫ x, (r i x) ^ 2 ∂μ := by
  have hpair (i j : ι) : (∫ x, r i x * r j x ∂μ) ≤
      (1 / 2 : ℝ) * ((∫ x, (r i x) ^ 2 ∂μ) + (∫ x, (r j x) ^ 2 ∂μ)) := by
    have h := integral_mono (μ := μ) (f := fun x => r i x * r j x)
      (g := fun x => (1 / 2 : ℝ) * ((r i x) ^ 2 + (r j x) ^ 2))
      Integrable.of_finite Integrable.of_finite (fun x => by nlinarith [sq_nonneg (r i x - r j x)])
    rw [integral_const_mul, integral_add Integrable.of_finite Integrable.of_finite] at h
    exact h
  calc
    _ = ∫ x, ∑ i, ∑ j, r i x * r j x ∂μ := by
      congr 1
      funext x
      rw [pow_two, Fintype.sum_mul_sum]
    _ = ∑ i, ∑ j, ∫ x, r i x * r j x ∂μ := by
      rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
    _ ≤ _ := overlap_matrix_sum_bound A hsym D (fun i => ∫ x, (r i x) ^ 2 ∂μ)
      (fun i j => ∫ x, r i x * r j x ∂μ) (fun i => integral_nonneg (fun x => sq_nonneg _))
      hdegree hzero hpair

/-- Local observables on disjoint response supports are independent under the
actual conditional product probability measure. -/
theorem finite_product_local_observables_independent (n : ℕ)
    (μ : Fin n → Measure (Fin 3)) [∀ i, IsProbabilityMeasure (μ i)]
    (S T : Finset (Fin n)) (hST : Disjoint S T)
    (R : (S → Fin 3) → ℝ) (Q : (T → Fin 3) → ℝ) :
    IndepFun (fun y : Fin n → Fin 3 => R (fun i : S => y i))
      (fun y : Fin n → Fin 3 => Q (fun i : T => y i)) (Measure.pi μ) := by
  have hi : iIndepFun (fun i (y : Fin n → Fin 3) => y i) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have h := hi.indepFun_finset S T hST (fun i => measurable_pi_apply i)
  exact h.comp (measurable_of_countable R) (measurable_of_countable Q)

/-- Centered local scores on disjoint supports are conditionally orthogonal.
Their independence is derived from the product response measure. -/
theorem finite_product_local_scores_orthogonal (n : ℕ)
    (μ : Fin n → Measure (Fin 3)) [∀ i, IsProbabilityMeasure (μ i)]
    (S T : Finset (Fin n)) (hST : Disjoint S T)
    (R : (S → Fin 3) → ℝ) (Q : (T → Fin 3) → ℝ)
    (hR : (∫ y : Fin n → Fin 3, R (fun i : S => y i) ∂Measure.pi μ) = 0) :
    (∫ y : Fin n → Fin 3, R (fun i : S => y i) * Q (fun i : T => y i) ∂Measure.pi μ) = 0 := by
  have hi := finite_product_local_observables_independent n μ S T hST R Q
  rw [hi.integral_fun_mul_eq_mul_integral
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable, hR, zero_mul]

/-- Bounded-overlap energy bound for actual centered local response scores. -/
theorem finite_product_patch_variance_bound (m n : ℕ)
    (μ : Fin n → Measure (Fin 3)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Fin m → Finset (Fin n)) (R : (j : Fin m) → (S j → Fin 3) → ℝ)
    (D : ℕ)
    (hcenter : ∀ j, (∫ y : Fin n → Fin 3, R j (fun i : S j => y i) ∂Measure.pi μ) = 0)
    (hdegree : ∀ j, (Finset.univ.filter fun k => ¬Disjoint (S j) (S k)).card ≤ D) :
    (∫ y : Fin n → Fin 3, (∑ j, R j (fun i : S j => y i)) ^ 2 ∂Measure.pi μ) ≤
      D * ∑ j, ∫ y : Fin n → Fin 3, (R j (fun i : S j => y i)) ^ 2 ∂Measure.pi μ := by
  apply finite_overlap_variance_bound (Measure.pi μ)
    (fun j y => R j (fun i : S j => y i)) (fun j k => ¬Disjoint (S j) (S k)) D
  · intro j k
    exact not_congr disjoint_comm
  · intro j
    convert hdegree j using 1
    congr 1
    ext k
    simp
  · intro j k hjk
    exact finite_product_local_scores_orthogonal n μ (S j) (S k) (not_not.mp hjk)
      (R j) (R k) (hcenter j)

/-- The ternary response masses as an actual probability mass function on indices. -/
def ternaryIndexPMF (a f V : ℝ) (ha : a ≠ 0) (hp : ∀ y, 0 ≤ ternaryMass a f V y) : PMF (Fin 3) :=
  PMF.ofFintype (fun y => ENNReal.ofReal (ternaryMass a f V y)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hp y), ternary_normalized a f V ha]
    norm_num)

/-- The corresponding genuine conditional response probability measure. -/
def ternaryIndexMeasure (a f V : ℝ) (ha : a ≠ 0) (hp : ∀ y, 0 ≤ ternaryMass a f V y) : Measure (Fin 3) :=
  (ternaryIndexPMF a f V ha hp).toMeasure

instance ternaryIndexMeasure_isProbability (a f V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) : IsProbabilityMeasure (ternaryIndexMeasure a f V ha hp) :=
  PMF.toMeasure.isProbabilityMeasure _

theorem ternary_index_measure_singleton (a f V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) (y : Fin 3) :
    (ternaryIndexMeasure a f V ha hp).real {y} = ternaryMass a f V y := by
  rw [measureReal_def, ternaryIndexMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)]
  exact ENNReal.toReal_ofReal (hp y)

/-- The conditional product measure has exactly the finite likelihood masses
used in the score construction. -/
theorem ternary_index_product_singleton (n : ℕ) (a V : ℝ) (f : Fin n → ℝ) (ha : a ≠ 0)
    (hp : ∀ i y, 0 ≤ ternaryMass a (f i) V y) (y : Fin n → Fin 3) :
    (Measure.pi (fun i => ternaryIndexMeasure a (f i) V ha (hp i))).real {y} =
      ∏ i, ternaryMass a (f i) V (y i) := by
  have heq : ({y} : Set (Fin n → Fin 3)) = Set.pi Set.univ (fun i => ({y i} : Set (Fin 3))) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h
      subst x
      simp
    · intro h
      funext i
      exact h i
  rw [measureReal_def, heq, Measure.pi_pi, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact ternary_index_measure_singleton a (f i) V ha (hp i) (y i)

/-- Finite score expectations agree exactly with integrals under the actual
conditional response product measure. -/
theorem ternary_index_product_integral (n : ℕ) (a V : ℝ) (f : Fin n → ℝ) (ha : a ≠ 0)
    (hp : ∀ i y, 0 ≤ ternaryMass a (f i) V y) (F : (Fin n → Fin 3) → ℝ) :
    (∫ y, F y ∂Measure.pi (fun i => ternaryIndexMeasure a (f i) V ha (hp i))) =
      ∑ y, (∏ i, ternaryMass a (f i) V (y i)) * F y := by
  rw [integral_fintype Integrable.of_finite]
  simp_rw [ternary_index_product_singleton, smul_eq_mul]

/-- The actual coordinate scores are centered under the genuine conditional
response product probability measure. -/
theorem ternary_coordinate_score_measure_centered (m n : ℕ) (a V η : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (w : Fin n → Fin m → ℝ)
    (ξ : Fin m → Fin 3) (j : Fin m) (ha : a ≠ 0)
    (hp : ∀ i y, 0 ≤ ternaryMass a (f ξ i) V y)
    (hpositive : ∀ y, 0 < finiteResponseLikelihood m n a V f ξ y) :
    (∫ y, finiteCoordinateScore m n a V η f w ξ y j
      ∂Measure.pi (fun i => ternaryIndexMeasure a (f ξ i) V ha (hp i))) = 0 := by
  rw [ternary_index_product_integral]
  exact finite_coordinate_score_centered m n a V η f w ξ j ha hpositive

end

end NearlyMinimax
