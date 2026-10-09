module

public import NearlyMinimax.IntegratedCardinalCovariance


@[expose] public section

/-! Exact permutation invariance of the actual truncated cardinal covariance,
including the dependent scale-coordinate change of variables. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def spatialScalePermutation {n : ℕ} (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    SpatialScaleIndex i ≃ SpatialScaleIndex (τ i) where
  toFun j := ⟨τ j.val, fun h => j.property (τ.injective h)⟩
  invFun j := ⟨τ.symm j.val, fun h => j.property
    ((τ.apply_symm_apply j.val).symm.trans (congrArg τ h))⟩
  left_inv j := Subtype.ext (τ.symm_apply_apply j.val)
  right_inv j := Subtype.ext (τ.apply_symm_apply j.val)

@[simp] theorem spatialScalePermutation_val {n : ℕ} (τ : Equiv.Perm (Fin n))
    (i : Fin n) (j : SpatialScaleIndex i) : (spatialScalePermutation τ i j).val = τ j.val := rfl

def spatialScaleReindex {n : ℕ} (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    SpatialScaleVector i ≃ᵐ SpatialScaleVector (τ i) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (spatialScalePermutation τ i)

@[simp] theorem spatialScaleReindex_apply {n : ℕ} (τ : Equiv.Perm (Fin n))
    (i : Fin n) (t : SpatialScaleVector i) (j : SpatialScaleIndex i) :
    spatialScaleReindex τ i t (spatialScalePermutation τ i j) = t j := by
  simpa only [spatialScaleReindex] using
    MeasurableEquiv.piCongrLeft_apply_apply (spatialScalePermutation τ i)
      (β := fun _ : SpatialScaleIndex (τ i) => ℝ) t j

theorem spatial_scale_log_sum_reindex {n : ℕ} (τ : Equiv.Perm (Fin n))
    (i : Fin n) (t : SpatialScaleVector i) :
    spatialScaleLogSum (τ i) (spatialScaleReindex τ i t) = spatialScaleLogSum i t := by
  have hs := (spatialScalePermutation τ i).sum_comp
    (fun j => Real.log (1 + max 0 (spatialScaleReindex τ i t j)))
  simpa only [spatialScaleLogSum, spatialScaleReindex_apply] using hs.symm

theorem spatial_scale_domain_reindex {n : ℕ} (τ : Equiv.Perm (Fin n))
    (i : Fin n) (T : ℝ) (t : SpatialScaleVector i) :
    spatialScaleReindex τ i t ∈ spatialScaleDomain (τ i) T ↔ t ∈ spatialScaleDomain i T := by
  have horthant : spatialScaleReindex τ i t ∈ Ici 0 ↔ t ∈ Ici 0 := by
    constructor
    · intro h j
      have hj := h (spatialScalePermutation τ i j)
      simpa only [Pi.zero_apply, spatialScaleReindex_apply] using hj
    · intro h j
      obtain ⟨j', rfl⟩ := (spatialScalePermutation τ i).surjective j
      simpa only [Pi.zero_apply, spatialScaleReindex_apply] using h j'
  simp only [spatialScaleDomain, mem_inter_iff, mem_setOf_eq,
    spatial_scale_log_sum_reindex, horthant]

theorem spatial_scale_reindex_measurePreserving {n : ℕ} (τ : Equiv.Perm (Fin n))
    (i : Fin n) (T : ℝ) :
    MeasurePreserving (spatialScaleReindex τ i) (spatialScaleMeasure i T) (spatialScaleMeasure (τ i) T) := by
  have hp : MeasurePreserving (spatialScaleReindex τ i) volume volume :=
    measurePreserving_piCongrLeft (fun _ : SpatialScaleIndex (τ i) => (volume : Measure ℝ))
      (spatialScalePermutation τ i)
  have hr := hp.restrict_preimage (spatial_scale_domain_isClosed (τ i) T).measurableSet
  have hpre : (spatialScaleReindex τ i) ⁻¹' spatialScaleDomain (τ i) T = spatialScaleDomain i T := by
    ext t
    exact spatial_scale_domain_reindex τ i T t
  rw [hpre] at hr
  exact hr

private theorem cardinal_polynomial_index_product {d n : ℕ} (U : Fin n → Covariate d) (i : Fin n) :
    spatialCardinalPolynomial U i = ∏ j : SpatialScaleIndex i, spatialCardinalAffine (U i) (U j.val) := by
  unfold spatialCardinalPolynomial
  rw [Finset.prod_subtype (p := fun j : Fin n => j ≠ i) ((Finset.univ : Finset (Fin n)).erase i)
    (fun j => by simp) (fun j : Fin n => spatialCardinalAffine (U i) (U j))]

private theorem cardinal_scale_index_product {d n : ℕ} (i : Fin n) (lam : ℝ)
    (U : Fin n → Covariate d) (t : SpatialScaleVector i) :
    spatialCardinalScale lam (spatialScaleExtend i t) U i =
      ∏ j : SpatialScaleIndex i, t j * lam ^ 2 *
        Real.exp (-(t j * lam * spatialSquaredDistance (U i) (U j.val))) := by
  unfold spatialCardinalScale
  rw [Finset.prod_subtype (p := fun j : Fin n => j ≠ i) ((Finset.univ : Finset (Fin n)).erase i)
    (fun j => by simp) (fun j : Fin n => spatialScaleExtend i t j * lam ^ 2 *
      Real.exp (-(spatialScaleExtend i t j * lam * spatialSquaredDistance (U i) (U j))))]
  apply Finset.prod_congr rfl
  intro j _
  simp only [spatialScaleExtend, dite_eq_left j.property]

theorem spatial_cardinal_polynomial_perm {d n : ℕ} (τ : Equiv.Perm (Fin n))
    (U : Fin n → Covariate d) (i : Fin n) :
    spatialCardinalPolynomial (U ∘ τ) i = spatialCardinalPolynomial U (τ i) := by
  rw [cardinal_polynomial_index_product, cardinal_polynomial_index_product]
  simpa only [Function.comp_def, spatialScalePermutation_val] using
    (spatialScalePermutation τ i).prod_comp
      (fun j => spatialCardinalAffine (U (τ i)) (U j.val))

theorem spatial_cardinal_scale_perm {d n : ℕ} (τ : Equiv.Perm (Fin n))
    (U : Fin n → Covariate d) (i : Fin n) (lam : ℝ) (t : SpatialScaleVector i) :
    spatialCardinalScale lam (spatialScaleExtend i t) (U ∘ τ) i =
      spatialCardinalScale lam (spatialScaleExtend (τ i) (spatialScaleReindex τ i t)) U (τ i) := by
  rw [cardinal_scale_index_product, cardinal_scale_index_product]
  simpa only [Function.comp_def, spatialScalePermutation_val, spatialScaleReindex_apply] using
    (spatialScalePermutation τ i).prod_comp (fun j => spatialScaleReindex τ i t j * lam ^ 2 *
      Real.exp (-(spatialScaleReindex τ i t j * lam * spatialSquaredDistance (U (τ i)) (U j.val))))

theorem spatial_centered_cardinal_matrix_perm {d n D : ℕ} (τ : Equiv.Perm (Fin n))
    (U : Fin n → Covariate d) (i : Fin n) (lam : ℝ) (t : SpatialScaleVector i)
    (β β' : HighFrameIndex d D) :
    spatialCenteredCardinalMatrix i lam (U ∘ τ) t β β' =
      spatialCenteredCardinalMatrix (τ i) lam U (spatialScaleReindex τ i t) β β' := by
  simp only [spatialCenteredCardinalMatrix, spatial_cardinal_polynomial_perm,
    spatial_cardinal_scale_perm]

theorem spatial_centered_cardinal_integral_perm {d n D : ℕ} (τ : Equiv.Perm (Fin n))
    (U : Fin n → Covariate d) (i : Fin n) (lam T : ℝ) (β β' : HighFrameIndex d D) :
    (∫ t, spatialCenteredCardinalMatrix i lam (U ∘ τ) t β β' ∂spatialScaleMeasure i T) =
      ∫ t, spatialCenteredCardinalMatrix (τ i) lam U t β β' ∂spatialScaleMeasure (τ i) T := by
  rw [← (spatial_scale_reindex_measurePreserving τ i T).integral_comp']
  exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
    spatial_centered_cardinal_matrix_perm τ U i lam t β β')

/-- The actual integrated cardinal coefficient covariance is invariant under
all observation permutations, with no separation or generic-position premise. -/
theorem integrated_cardinal_matrix_perm {d n D : ℕ} (τ : Equiv.Perm (Fin n))
    (lam T : ℝ) (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T (U ∘ τ) β β' = integratedCardinalMatrix lam T U β β' := by
  simp only [integratedCardinalMatrix, spatial_centered_cardinal_integral_perm]
  exact Equiv.sum_comp τ (fun i => ∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i T)

end NearlyMinimax
