module

public import NearlyMinimax.SpatialCardinalCovariance


@[expose] public section

/-! The actual logarithmically truncated scale integral in Appendix A.
Compactness proves genuine integrability before any matrix/response
interchange is used. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev SpatialScaleIndex {n : ℕ} (i : Fin n) := {j : Fin n // j ≠ i}
abbrev SpatialScaleVector {n : ℕ} (i : Fin n) := SpatialScaleIndex i → ℝ

def spatialScaleExtend {n : ℕ} (i : Fin n) (t : SpatialScaleVector i) (j : Fin n) : ℝ :=
  if h : j ≠ i then t ⟨j, h⟩ else 0

def spatialScaleLogSum {n : ℕ} (i : Fin n) (t : SpatialScaleVector i) : ℝ :=
  ∑ j, Real.log (1 + max 0 (t j))

/-- Equal to S≤2logT in the nonnegative scale orthant. The max only
makes the defining function globally continuous. -/
def spatialScaleDomain {n : ℕ} (i : Fin n) (T : ℝ) : Set (SpatialScaleVector i) :=
  Ici 0 ∩ {t | spatialScaleLogSum i t ≤ 2 * Real.log T}

theorem spatial_scale_log_sum_continuous {n : ℕ} (i : Fin n) :
    Continuous (spatialScaleLogSum i) := by
  apply continuous_finsetSum
  intro j _
  exact (continuous_const.add (continuous_const.max (continuous_apply j))).log (by intro t; positivity)

theorem spatial_scale_domain_isClosed {n : ℕ} (i : Fin n) (T : ℝ) :
    IsClosed (spatialScaleDomain i T) :=
  isClosed_Ici.inter (isClosed_le (spatial_scale_log_sum_continuous i) continuous_const)

theorem spatial_scale_domain_subset_box {n : ℕ} (i : Fin n) (T : ℝ) (hT : 1 ≤ T) :
    spatialScaleDomain i T ⊆ Icc 0 (fun _ => T ^ 2 - 1) := by
  intro t ht
  refine ⟨ht.1, fun j => ?_⟩
  have hT0 : 0 < T := by linarith
  have hlog0 (j : SpatialScaleIndex i) : 0 ≤ Real.log (1 + max 0 (t j)) :=
    Real.log_nonneg (by linarith [le_max_left (0 : ℝ) (t j)])
  have hlogj := (Finset.single_le_sum (fun j _ => hlog0 j) (Finset.mem_univ j)).trans ht.2
  have htj : (0 : ℝ) ≤ t j := ht.1 j
  rw [max_eq_right htj] at hlogj
  have he := Real.exp_le_exp.mpr hlogj
  rw [Real.exp_log (by linarith : 0 < 1 + t j)] at he
  have hpow : Real.exp (2 * Real.log T) = T ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hT0] using Real.exp_nat_mul (Real.log T) 2
  rw [hpow] at he
  linarith

theorem spatial_scale_domain_isCompact {n : ℕ} (i : Fin n) (T : ℝ) (hT : 1 ≤ T) :
    IsCompact (spatialScaleDomain i T) :=
  isCompact_Icc.of_isClosed_subset (spatial_scale_domain_isClosed i T)
    (spatial_scale_domain_subset_box i T hT)

def spatialScaleMeasure {n : ℕ} (i : Fin n) (T : ℝ) : Measure (SpatialScaleVector i) :=
  volume.restrict (spatialScaleDomain i T)

theorem spatial_scale_measure_finite {n : ℕ} (i : Fin n) (T : ℝ) (hT : 1 ≤ T) :
    IsFiniteMeasure (spatialScaleMeasure i T) := by
  apply isFiniteMeasure_restrict.mpr
  exact (spatial_scale_domain_isCompact i T hT).measure_ne_top

theorem spatial_scale_extend_continuous {n : ℕ} (i : Fin n) :
    Continuous (spatialScaleExtend i) := by
  apply continuous_pi
  intro j
  by_cases hji : j ≠ i
  · simpa only [spatialScaleExtend, dite_eq_left hji] using continuous_apply (⟨j, hji⟩ : SpatialScaleIndex i)
  · simp only [spatialScaleExtend, dite_eq_right hji]; exact continuous_const

def spatialCenteredCardinalMatrix {d n D : ℕ} (i : Fin n) (lam : ℝ)
    (U : Fin n → Covariate d) (t : SpatialScaleVector i) (β β' : HighFrameIndex d D) : ℝ :=
  spatialCardinalScale lam (spatialScaleExtend i t) U i *
    highFrameCoefficients (spatialCardinalPolynomial U i) β *
    highFrameCoefficients (spatialCardinalPolynomial U i) β'

theorem spatial_centered_cardinal_scale_continuous {d n : ℕ}
    (i : Fin n) (lam : ℝ) (U : Fin n → Covariate d) :
    Continuous (fun t : SpatialScaleVector i => spatialCardinalScale lam (spatialScaleExtend i t) U i) := by
  unfold spatialCardinalScale
  apply continuous_finsetProd
  intro j _
  have hj := (continuous_apply j).comp (spatial_scale_extend_continuous i)
  exact ((hj.mul continuous_const).mul
    (Real.continuous_exp.comp (((hj.mul continuous_const).mul continuous_const).neg)))

theorem spatial_centered_cardinal_matrix_integrable {d n D : ℕ}
    (i : Fin n) (lam T : ℝ) (hT : 1 ≤ T) (U : Fin n → Covariate d)
    (β β' : HighFrameIndex d D) :
    Integrable (fun t => spatialCenteredCardinalMatrix i lam U t β β') (spatialScaleMeasure i T) := by
  apply ContinuousOn.integrableOn_compact (spatial_scale_domain_isCompact i T hT)
  exact (((spatial_centered_cardinal_scale_continuous i lam U).mul continuous_const).mul
    continuous_const).continuousOn

/-- The exact E_(k,T) from the paper, as a genuine coefficientwise
Lebesgue integral of its explicit cardinal products. -/
def integratedCardinalMatrix {d n D : ℕ} (lam T : ℝ) (U : Fin n → Covariate d)
    (β β' : HighFrameIndex d D) : ℝ :=
  ∑ i, ∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i T

def integratedCardinalWeight {d n : ℕ} (lam T : ℝ) (U : Fin n → Covariate d) (i : Fin n) : ℝ :=
  ∫ t, spatialCardinalWeight lam (spatialScaleExtend i t) U i ∂spatialScaleMeasure i T

theorem spatial_frame_covariance_integral {κ α : Type*} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace α] {n : ℕ} (μ : Measure α) (A : α → κ → κ → ℝ)
    (hA : ∀ β β', Integrable (fun t => A t β β') μ)
    (φ : Fin n → κ → ℝ) (i l : Fin n) :
    spatialFrameCovariance (fun β β' => ∫ t, A t β β' ∂μ) φ i l =
      ∫ t, spatialFrameCovariance (A t) φ i l ∂μ := by
  unfold spatialFrameCovariance
  rw [integral_finsetSum _ (fun β _ => integrable_finsetSum _
    (fun β' _ => (hA β β').const_mul (φ i β * φ l β')))]
  apply Finset.sum_congr rfl
  intro β _
  rw [integral_finsetSum _ (fun β' _ => (hA β β').const_mul (φ i β * φ l β'))]
  apply Finset.sum_congr rfl
  intro β' _
  rw [integral_const_mul]

theorem spatial_centered_cardinal_matrix_diagonal {d n D : ℕ} (hn : n ≤ D)
    (j : Fin n) (lam : ℝ) (U : Fin n → Covariate d) (t : SpatialScaleVector j) (i l : Fin n) :
    spatialFrameCovariance (spatialCenteredCardinalMatrix (D := D) j lam U t)
      (fun r => highFrameFeature (U r)) i l =
      if j = i ∧ i = l then spatialCardinalWeight lam (spatialScaleExtend j t) U j else 0 := by
  unfold spatialCenteredCardinalMatrix
  rw [spatial_frame_covariance_rank_one]
  have hdegree := (spatial_cardinal_polynomial_degree U j).trans (Nat.sub_le_sub_right hn 1)
  rw [← high_frame_polynomial_evaluation _ hdegree, ← high_frame_polynomial_evaluation _ hdegree]
  by_cases hji : j = i
  · subst j
    by_cases hil : i = l
    · subst l
      rw [ite_eq_left ⟨rfl, rfl⟩, ← spatial_cardinal_weight_product]
      ring
    · rw [ite_eq_right (by tauto), spatial_cardinal_polynomial_eval_neighbor U i l (Ne.symm hil), mul_zero]
  · rw [ite_eq_right (by tauto), spatial_cardinal_polynomial_eval_neighbor U j i (Ne.symm hji),
      mul_zero, zero_mul]

/-- The integrated covariance matrix is genuinely symmetric. -/
theorem integrated_cardinal_matrix_symmetric {d n D : ℕ}
    (lam T : ℝ) (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T U β β' = integratedCardinalMatrix lam T U β' β := by
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with t
  unfold spatialCenteredCardinalMatrix
  ring

/-- Exact evaluated diagonal of the actual scale integral E_(k,T). -/
theorem integrated_cardinal_matrix_diagonal {d n D : ℕ} (hn : n ≤ D)
    (lam T : ℝ) (hT : 1 ≤ T) (U : Fin n → Covariate d) (i l : Fin n) :
    spatialFrameCovariance (integratedCardinalMatrix (D := D) lam T U)
      (fun j => highFrameFeature (U j)) i l =
      if i = l then integratedCardinalWeight lam T U i else 0 := by
  unfold integratedCardinalMatrix
  rw [spatial_frame_covariance_sum]
  simp_rw [spatial_frame_covariance_integral _ _
    (fun β β' => spatial_centered_cardinal_matrix_integrable _ lam T hT U β β')]
  simp_rw [spatial_centered_cardinal_matrix_diagonal hn]
  rw [Finset.sum_eq_single i]
  · by_cases hil : i = l
    · subst l
      simp only [and_self, ite_true, integratedCardinalWeight]
    · simp only [hil, and_false, ite_false, integral_zero]
  · intro j _ hji
    simp only [hji, false_and, ite_false, integral_zero]
  · simp

theorem integrated_cardinal_response_heat {d n D : ℕ} (hn : n ≤ D) (q : ℕ)
    (C a V η lam T : ℝ) (hC : C ≠ 0) (hT : 1 ≤ T) (U : Fin n → Covariate d)
    (g w : Fin n → ℝ) (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    responseMatrixAction q C (integratedCardinalMatrix lam T U) c
      (fun c => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) c y) =
      η ^ 2 * ∑ i, (w i) ^ 2 * integratedCardinalWeight lam T U i *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i +
      highResponseDefect q C a V η (integratedCardinalMatrix lam T U) g w
        (fun i => highFrameFeature (U i)) c y := by
  apply high_response_matrix_heat_with_defect q C a V η _ hC
  · exact integrated_cardinal_matrix_symmetric lam T U
  · exact integrated_cardinal_matrix_diagonal hn lam T hT U

end NearlyMinimax
