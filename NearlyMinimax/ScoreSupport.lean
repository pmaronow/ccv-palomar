module

public import NearlyMinimax.OverlapVariance


@[expose] public section

/-! # Local support of the actual observable scores

The other likelihood factors cancel from a patch score. Consequently its
value depends only on responses inside the window's support, and actual
coordinate scores on disjoint supports are orthogonal.
-/

namespace NearlyMinimax

open MeasureTheory ProbabilityTheory

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem patch_variance_ratio (n : ℕ) (a V η z : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3) (i : Fin n)
    (hp : ∀ k, 0 < ternaryMass a (g k + η * w k * z) V (y k)) :
    patchVarianceTerm n a V η g w y z i / patchResponseProduct n a V η g w y z =
      ternaryVarianceDerivative a (y i) / ternaryMass a (g i + η * w i * z) V (y i) := by
  unfold patchVarianceTerm patchResponseProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
      ternaryMass a (g k + η * w k * z) V (y k)) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun k _ => hp k))
  exact mul_div_mul_right _ _ hrest

private theorem patch_score_ratio_representation (n : ℕ) (a V η z : ℝ) (g w : Fin n → ℝ)
    (y : Fin n → Fin 3)
    (hp : ∀ k, 0 < ternaryMass a (g k + η * w k * z) V (y k)) :
    patchObservableScore n a V η g w y z =
      symmetricDifference (patchResponseProduct n a V η g w y) /
        patchResponseProduct n a V η g w y z -
      η ^ 2 * ∑ i, (w i) ^ 2 *
        (ternaryVarianceDerivative a (y i) / ternaryMass a (g i + η * w i * z) V (y i)) := by
  unfold patchObservableScore patchScoreNumerator
  rw [sub_div]
  simp_rw [mul_div_assoc, Finset.sum_div, mul_div_assoc, patch_variance_ratio n a V η z g w y _ hp]

/-- A patch score depends only on response coordinates in the support of its window. -/
theorem patch_score_depends_on_support (n : ℕ) (a V η z : ℝ) (g w : Fin n → ℝ)
    (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i = 0)
    (y y' : Fin n → Fin 3) (hyy : ∀ i ∈ S, y i = y' i)
    (hp : ∀ i b, 0 < ternaryMass a (g i + η * w i * z) V b) :
    patchObservableScore n a V η g w y z = patchObservableScore n a V η g w y' z := by
  let outside (v : Fin n → Fin 3) : ℝ :=
    ∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, ternaryMass a (g i) V (v i)
  let inside (v : Fin n → Fin 3) (u : ℝ) : ℝ :=
    ∏ i ∈ S, ternaryMass a (g i + η * w i * u) V (v i)
  have hfactor (v : Fin n → Fin 3) (u : ℝ) :
      patchResponseProduct n a V η g w v u = outside v * inside v u := by
    unfold patchResponseProduct
    rw [← Finset.prod_sdiff (Finset.subset_univ S)]
    dsimp [outside, inside]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    simp [hw i (Finset.mem_sdiff.mp hi).2]
  have hout (v : Fin n → Fin 3) : outside v ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro i hi
    simpa [hw i (Finset.mem_sdiff.mp hi).2] using hp i (v i)
  have hin (v : Fin n → Fin 3) : inside v z ≠ 0 := by
    exact ne_of_gt (Finset.prod_pos (fun i _ => hp i (v i)))
  have hs (u : ℝ) : inside y u = inside y' u := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hyy i hi]
  have hratio (u : ℝ) : patchResponseProduct n a V η g w y u /
      patchResponseProduct n a V η g w y z =
      patchResponseProduct n a V η g w y' u / patchResponseProduct n a V η g w y' z := by
    rw [hfactor y u, hfactor y z, hfactor y' u, hfactor y' z, hs u, hs z]
    field_simp [hout y, hout y', hin y']
  rw [patch_score_ratio_representation n a V η z g w y (fun i => hp i (y i)),
    patch_score_ratio_representation n a V η z g w y' (fun i => hp i (y' i))]
  congr 1
  · unfold symmetricDifference
    simp only [sub_div, add_div, mul_div_assoc]
    rw [hratio 1, hratio (-1), hratio 0]
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · rw [hyy i hi]
    · simp [hw i hi]

/-- The actual coordinate score agrees with its one-dimensional patch representation. -/
theorem latent_coordinate_score_eq_patch (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3)
    (j : Fin m) (y : Fin n → Fin 3) :
    finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j =
      patchObservableScore n a V η (latentRegressionWithout m n η base w ξ j)
        (fun i => w i j) y (ternaryValue 1 (ξ j)) := by
  unfold finiteCoordinateScore finiteCoordinateScoreNumerator patchObservableScore patchScoreNumerator
  rw [latent_regression_likelihood_difference]
  simp_rw [latent_regression_variance_term m n a V η base w ξ j]
  have hL : finiteResponseLikelihood m n a V (latentRegression m n η base w) ξ y =
      patchResponseProduct n a V η (latentRegressionWithout m n η base w ξ j)
        (fun i => w i j) y (ternaryValue 1 (ξ j)) := by
    simp [finiteResponseLikelihood, patchResponseProduct,
      latent_regression_decomposition m n η base w ξ j]
  rw [hL]

/-- Exact locality of the actual full-field coordinate score. -/
theorem latent_coordinate_score_depends_on_support (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3)
    (j : Fin m) (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i j = 0)
    (y y' : Fin n → Fin 3) (hyy : ∀ i ∈ S, y i = y' i)
    (hp : ∀ i b, 0 < ternaryMass a (latentRegression m n η base w ξ i) V b) :
    finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j =
      finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y' j := by
  rw [latent_coordinate_score_eq_patch, latent_coordinate_score_eq_patch]
  apply patch_score_depends_on_support n a V η (ternaryValue 1 (ξ j))
    (latentRegressionWithout m n η base w ξ j) (fun i => w i j) S hw y y' hyy
  intro i b
  simpa [latent_regression_decomposition m n η base w ξ j] using hp i b

/-- Extend a local response tuple by the zero response index outside its support. -/
def extendPatchResponses (n : ℕ) (S : Finset (Fin n)) (y : S → Fin 3) : Fin n → Fin 3 :=
  fun i => if hi : i ∈ S then y ⟨i, hi⟩ else 1

/-- Actual coordinate scores on disjoint supports are orthogonal under the
actual conditional ternary response product measure. -/
theorem latent_coordinate_scores_orthogonal (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3)
    (j k : Fin m) (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hwS : ∀ i, i ∉ S → w i j = 0) (hwT : ∀ i, i ∉ T → w i k = 0)
    (ha : a ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (latentRegression m n η base w ξ i) V b) :
    (∫ y : Fin n → Fin 3,
      finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j *
        finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y k
      ∂Measure.pi (fun i => ternaryIndexMeasure a (latentRegression m n η base w ξ i) V ha
        (fun b => (hp i b).le))) = 0 := by
  let r : Fin m → (Fin n → Fin 3) → ℝ :=
    fun j y => finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j
  let R : (S → Fin 3) → ℝ := fun y => r j (extendPatchResponses n S y)
  let Q : (T → Fin 3) → ℝ := fun y => r k (extendPatchResponses n T y)
  let μ : Fin n → Measure (Fin 3) := fun i =>
    ternaryIndexMeasure a (latentRegression m n η base w ξ i) V ha (fun b => (hp i b).le)
  have hR (y : Fin n → Fin 3) : r j y = R (fun i : S => y i) := by
    apply latent_coordinate_score_depends_on_support m n a V η base w ξ j S hwS
      y (extendPatchResponses n S (fun i : S => y i)) _ hp
    intro i hi
    simp [extendPatchResponses, hi]
  have hQ (y : Fin n → Fin 3) : r k y = Q (fun i : T => y i) := by
    apply latent_coordinate_score_depends_on_support m n a V η base w ξ k T hwT
      y (extendPatchResponses n T (fun i : T => y i)) _ hp
    intro i hi
    simp [extendPatchResponses, hi]
  have hL : ∀ y, 0 < finiteResponseLikelihood m n a V (latentRegression m n η base w) ξ y := by
    intro y
    exact Finset.prod_pos (fun i _ => hp i (y i))
  have hcenter : (∫ y : Fin n → Fin 3, R (fun i : S => y i) ∂Measure.pi μ) = 0 := by
    simp_rw [← hR]
    exact ternary_coordinate_score_measure_centered m n a V η (latentRegression m n η base w)
      w ξ j ha (fun i b => (hp i b).le) hL
  have horth := finite_product_local_scores_orthogonal n μ S T hST R Q hcenter
  change (∫ y, r j y * r k y ∂Measure.pi μ) = 0
  simp_rw [hR, hQ]
  exact horth

/-- Bounded-overlap aggregation for the actual full-field coordinate scores.
No orthogonality hypothesis is assumed: it follows from their local supports
and the actual conditional ternary response product measure. -/
theorem latent_coordinate_score_variance_bound (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3)
    (S : Fin m → Finset (Fin n)) (D : ℕ)
    (hw : ∀ j i, i ∉ S j → w i j = 0)
    (hdegree : ∀ j, (Finset.univ.filter fun k => ¬Disjoint (S j) (S k)).card ≤ D)
    (ha : a ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (latentRegression m n η base w ξ i) V b) :
    (∫ y : Fin n → Fin 3,
      (∑ j, finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j) ^ 2
      ∂Measure.pi (fun i => ternaryIndexMeasure a (latentRegression m n η base w ξ i) V ha
        (fun b => (hp i b).le))) ≤
      D * ∑ j, ∫ y : Fin n → Fin 3,
        (finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j) ^ 2
        ∂Measure.pi (fun i => ternaryIndexMeasure a (latentRegression m n η base w ξ i) V ha
          (fun b => (hp i b).le)) := by
  apply finite_overlap_variance_bound _ _ (fun j k => ¬Disjoint (S j) (S k)) D
  · intro j k
    exact not_congr disjoint_comm
  · intro j
    convert hdegree j using 1
    congr 1
    ext k
    simp
  · intro j k hjk
    exact latent_coordinate_scores_orthogonal m n a V η base w ξ j k (S j) (S k)
      (not_not.mp hjk) (hw j) (hw k) ha hp

/-- The full observable score inherits that bounded-overlap conditional energy bound. -/
theorem latent_full_score_variance_bound (m n : ℕ) (a V η : ℝ)
    (base : Fin n → ℝ) (w : Fin n → Fin m → ℝ) (ξ : Fin m → Fin 3)
    (S : Fin m → Finset (Fin n)) (D : ℕ)
    (hw : ∀ j i, i ∉ S j → w i j = 0)
    (hsquares : ∀ i, ∑ j, (w i j) ^ 2 = 1)
    (hdegree : ∀ j, (Finset.univ.filter fun k => ¬Disjoint (S j) (S k)).card ≤ D)
    (ha : a ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (latentRegression m n η base w ξ i) V b) :
    (∫ y : Fin n → Fin 3,
      (finiteExperimentScore m n a V η (latentRegression m n η base w) ξ y) ^ 2
      ∂Measure.pi (fun i => ternaryIndexMeasure a (latentRegression m n η base w ξ i) V ha
        (fun b => (hp i b).le))) ≤
      D * ∑ j, ∫ y : Fin n → Fin 3,
        (finiteCoordinateScore m n a V η (latentRegression m n η base w) w ξ y j) ^ 2
        ∂Measure.pi (fun i => ternaryIndexMeasure a (latentRegression m n η base w ξ i) V ha
          (fun b => (hp i b).le)) := by
  simp_rw [finite_experiment_score_decomposition m n a V η
    (latentRegression m n η base w) w ξ _ hsquares]
  exact latent_coordinate_score_variance_bound m n a V η base w ξ S D hw hdegree ha hp

end

end NearlyMinimax
