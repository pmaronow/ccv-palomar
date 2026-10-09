module

public import NearlyMinimax.CardinalScaleVolume
public import NearlyMinimax.GaussianTensorCost
public import NearlyMinimax.FiniteTensorPolynomialMoments


@[expose] public section

/-! Actual tensor Gaussian and compact-scale separated representation of the
integrated spatial cardinal covariance. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem spatial_cardinal_polynomial_scale_product {d n : ℕ} (i : Fin n) (U : Fin n → Covariate d) :
    spatialCardinalPolynomial U i = ∏ j : SpatialScaleIndex i, spatialCardinalAffine (U i) (U j.val) := by
  unfold spatialCardinalPolynomial
  rw [Finset.prod_subtype (p := fun j : Fin n => j ≠ i) ((Finset.univ : Finset (Fin n)).erase i)
    (fun j => by simp) (fun j : Fin n => spatialCardinalAffine (U i) (U j))]

theorem spatial_cardinal_scale_product {d n : ℕ} (i : Fin n) (lam : ℝ)
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

/-- Tensorization of the actual primitive Gaussian coefficient moments. -/
theorem gaussian_tensor_cardinal_moments {κ : Type*} [Fintype κ] {d : ℕ}
    (lam : ℝ) (hlam : 0 ≤ lam) (t : κ → ℝ) (ht : ∀ j, 0 ≤ t j)
    (x y : κ → Covariate d) (β β' : Fin d →₀ ℕ) :
    Integrable (fun e : GaussianTensorMark κ d => gaussianTensorObservable lam t x y e *
      gaussianTensorAmplitude lam e β β') (gaussianTensorMeasure κ d) ∧
      (∫ e, gaussianTensorObservable lam t x y e * gaussianTensorAmplitude lam e β β'
        ∂gaussianTensorMeasure κ d) =
        (∏ j, t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance (x j) (y j)))) *
          (∏ j, spatialCardinalAffine (x j) (y j)).coeff β *
          (∏ j, spatialCardinalAffine (x j) (y j)).coeff β' := by
  let w := fun (j : κ) (e : GaussianPrimitiveMark d) =>
    gaussianPrimitiveLeft lam (t j) e (x j) * gaussianPrimitiveRight lam (t j) e (y j) *
      gaussianPrimitiveScalar d lam e
  let P := fun (_j : κ) (e : GaussianPrimitiveMark d) => gaussianAffinePolynomial e.2.1.1 e.2.2.1.1
  let P' := fun (_j : κ) (e : GaussianPrimitiveMark d) => gaussianAffinePolynomial e.2.1.2 e.2.2.1.2
  let p := fun j : κ => spatialCardinalAffine (x j) (y j)
  let a := fun j : κ => t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance (x j) (y j)))
  have hpair (j : κ) (b b' : Fin d →₀ ℕ) :
      polynomialPairMoment (w j) (P j) (P' j) b b' =
        fun e => gaussianPrimitiveLeft lam (t j) e (x j) * gaussianPrimitiveRight lam (t j) e (y j) *
          gaussianPrimitiveAmplitude lam e b b' := by
    funext e
    dsimp [w, P, P', polynomialPairMoment, gaussianPrimitiveAmplitude, gaussianPrimitiveScalar]
    ring
  have hi (j : κ) (b b' : Fin d →₀ ℕ) :
      Integrable (polynomialPairMoment (w j) (P j) (P' j) b b') (gaussianPrimitiveMeasure d) := by
    rw [hpair]
    exact gaussianPrimitive_observable_integrable lam (t j) (x j) (y j) b b'
  have he (j : κ) (b b' : Fin d →₀ ℕ) :
      (∫ e, polynomialPairMoment (w j) (P j) (P' j) b b' e ∂gaussianPrimitiveMeasure d) =
        a j * (p j).coeff b * (p j).coeff b' := by
    rw [hpair]
    exact (gaussianPrimitive_separated_exact lam (t j) hlam (ht j) (x j) (y j) b b').symm
  have h := tensorPolynomialPairMoment_fintype_integral (gaussianPrimitiveMeasure d)
    w P P' p p a hi he β β'
  have hfun : tensorPolynomialPairMoment_fintype w P P' β β' =
      fun e : GaussianTensorMark κ d => gaussianTensorObservable lam t x y e *
        gaussianTensorAmplitude lam e β β' := by
    funext e
    unfold tensorPolynomialPairMoment_fintype gaussianTensorObservable gaussianTensorAmplitude
      gaussianTensorScalar gaussianTensorLeftPolynomial gaussianTensorRightPolynomial gaussianPolynomialProduct
    dsimp [w, P, P']
    rw [Finset.prod_mul_distrib]
    ring
  rw [hfun] at h
  exact h

/-- Genuine scale-and-Gaussian mark space for a fixed cardinal center. -/
abbrev CenteredCardinalMark (d n : ℕ) (i : Fin n) :=
  SpatialScaleVector i × GaussianTensorMark (SpatialScaleIndex i) d

def centeredCardinalMeasure {n : ℕ} (i : Fin n) (d : ℕ) (T : ℝ) :
    Measure (CenteredCardinalMark d n i) :=
  (spatialScaleMeasure i T).prod (gaussianTensorMeasure (SpatialScaleIndex i) d)

def centeredCardinalAmplitude {d n D : ℕ} (i : Fin n) (lam : ℝ)
    (z : CenteredCardinalMark d n i) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  gaussianTensorSymmetricAmplitude lam z.2

/-- Each observation receives one bounded spatial factor. The distinguished
observation receives the product of the left factors. -/
def centeredCardinalFactor {d n : ℕ} (i : Fin n) (lam : ℝ)
    (z : CenteredCardinalMark d n i) (l : Fin n) (x : Covariate d) : ℝ :=
  if h : l ≠ i then gaussianPrimitiveRight lam (z.1 ⟨l, h⟩) (z.2 ⟨l, h⟩) x
    else ∏ j : SpatialScaleIndex i, gaussianPrimitiveLeft lam (z.1 j) (z.2 j) x

theorem centered_cardinal_factor_abs_le_one {d n : ℕ} (i : Fin n) (lam : ℝ)
    (z : CenteredCardinalMark d n i) (l : Fin n) (x : Covariate d) (hx : ∀ r, |x r| ≤ 2) :
    |centeredCardinalFactor i lam z l x| ≤ 1 := by
  unfold centeredCardinalFactor
  split_ifs
  · exact gaussianPrimitiveRight_bound lam _ _ x hx
  · rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _j : SpatialScaleIndex i, (1 : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => gaussianPrimitiveLeft_bound lam _ _ x)
      _ = _ := by simp

theorem centered_cardinal_factor_measurable {d n : ℕ} (i : Fin n) (lam : ℝ)
    (l : Fin n) (x : Covariate d) :
    Measurable (fun z : CenteredCardinalMark d n i => centeredCardinalFactor i lam z l x) := by
  unfold centeredCardinalFactor
  split_ifs with h
  · have hm : Measurable (fun z : CenteredCardinalMark d n i => (z.1 ⟨l, h⟩, z.2 ⟨l, h⟩)) :=
      (((measurable_pi_apply (⟨l, h⟩ : SpatialScaleIndex i)).comp measurable_fst).prodMk
        ((measurable_pi_apply (⟨l, h⟩ : SpatialScaleIndex i)).comp measurable_snd))
    have hh := (gaussianPrimitiveRight_scale_measurable lam x).comp hm
    change Measurable (fun z : CenteredCardinalMark d n i =>
      gaussianPrimitiveRight lam (z.1 ⟨l, h⟩) (z.2 ⟨l, h⟩) x) at hh
    exact hh
  · apply Finset.measurable_fun_prod
    intro j _
    have hm : Measurable (fun z : CenteredCardinalMark d n i => (z.1 j, z.2 j)) :=
      (((measurable_pi_apply j).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd))
    have hh := (gaussianPrimitiveLeft_scale_measurable lam x).comp hm
    change Measurable (fun z : CenteredCardinalMark d n i =>
      gaussianPrimitiveLeft lam (z.1 j) (z.2 j) x) at hh
    exact hh

theorem centered_cardinal_amplitude_symmetric {d n D : ℕ} (i : Fin n) (lam : ℝ)
    (z : CenteredCardinalMark d n i) (β β' : HighFrameIndex d D) :
    centeredCardinalAmplitude i lam z β β' = centeredCardinalAmplitude i lam z β' β :=
  gaussianTensorSymmetricAmplitude_symmetric lam z.2 β β'

theorem centered_cardinal_amplitude_measurable {d n D : ℕ} (i : Fin n) (lam : ℝ)
    (β β' : HighFrameIndex d D) :
    Measurable (fun z : CenteredCardinalMark d n i => centeredCardinalAmplitude i lam z β β') :=
  (gaussianTensorSymmetricAmplitude_measurable lam β β').comp measurable_snd

theorem centered_cardinal_measure_finite {n : ℕ} (i : Fin n) (d : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    IsFiniteMeasure (centeredCardinalMeasure i d T) := by
  letI := spatial_scale_measure_finite i T hT
  letI := gaussianTensorMeasure_finite (SpatialScaleIndex i) d
  unfold centeredCardinalMeasure
  infer_instance

theorem centered_cardinal_cost_integrable {d n D : ℕ} (i : Fin n) (lam : ℝ)
    {T : ℝ} (hT : 1 ≤ T) :
    Integrable (separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam))
      (centeredCardinalMeasure i d T) := by
  letI := spatial_scale_measure_finite i T hT
  letI := gaussianTensorMeasure_finite (SpatialScaleIndex i) d
  have h := (integrable_const (1 : ℝ) (μ := spatialScaleMeasure i T)).mul_prod
    (gaussianTensorSymmetricAmplitude_cost_integrable (κ := SpatialScaleIndex i) (d := d) (D := D) lam)
  change Integrable (fun z : CenteredCardinalMark d n i =>
    separatedMatrixCost (gaussianTensorSymmetricAmplitude lam) z.2)
      ((spatialScaleMeasure i T).prod (gaussianTensorMeasure (SpatialScaleIndex i) d))
  simpa only [one_mul] using h

theorem centered_cardinal_entry_integrable {d n D : ℕ} (i : Fin n) (lam : ℝ)
    {T : ℝ} (hT : 1 ≤ T) (β β' : HighFrameIndex d D) :
    Integrable (fun z => centeredCardinalAmplitude i lam z β β') (centeredCardinalMeasure i d T) :=
  separatedMatrix_entry_integrable _ _ (centered_cardinal_amplitude_measurable i lam)
    (centered_cardinal_cost_integrable i lam hT) β β'

theorem centered_cardinal_cost_integral_eq {d n D : ℕ} (i : Fin n) (lam T : ℝ) :
    (∫ z, separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam) z ∂centeredCardinalMeasure i d T) =
      (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) *
        (∫ e, separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := SpatialScaleIndex i)
          (d := d) (D := D) lam) e ∂gaussianTensorMeasure (SpatialScaleIndex i) d) := by
  letI := gaussianTensorMeasure_finite (SpatialScaleIndex i) d
  letI : SFinite (spatialScaleMeasure i T) := by unfold spatialScaleMeasure; infer_instance
  have h := integral_prod_mul (μ := spatialScaleMeasure i T)
    (ν := gaussianTensorMeasure (SpatialScaleIndex i) d) (fun _ => (1 : ℝ))
    (separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := SpatialScaleIndex i) (d := d) (D := D) lam))
  simp only [one_mul, integral_const, smul_eq_mul, mul_one] at h
  simpa only [centeredCardinalMeasure, centeredCardinalAmplitude, separatedMatrixCost,
    spatialScaleMeasure, Measure.real, Measure.restrict_apply_univ] using h

/-- Actual representation cost, obtained from the actual Gaussian tensor
moment cost and actual logarithmic scale-domain volume. -/
theorem centered_cardinal_cost_integral_le {d n D : ℕ} (hn : 2 ≤ n) (i : Fin n) (lam : ℝ)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ z, separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam) z ∂centeredCardinalMeasure i d T) ≤
      (1024 * |lam| * (d : ℝ) ^ 2) ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
  rw [centered_cardinal_cost_integral_eq]
  have hcost := gaussianTensorSymmetricAmplitude_integrated_cost
    (κ := SpatialScaleIndex i) (d := d) (D := D) lam
  rw [spatial_scale_index_card] at hcost
  have hvol := spatial_scale_domain_volume_le_uniform hn i hT
  have hlog := Real.log_nonneg hT
  have hnn : 0 ≤ ∫ e, separatedMatrixCost (gaussianTensorSymmetricAmplitude
      (κ := SpatialScaleIndex i) (d := d) (D := D) lam) e ∂gaussianTensorMeasure (SpatialScaleIndex i) d :=
    integral_nonneg (fun e => Finset.sum_nonneg (fun β _ => Finset.sum_nonneg (fun β' _ => abs_nonneg _)))
  have h := mul_le_mul hvol hcost hnn (by positivity :
    0 ≤ (2 : ℝ) ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2))
  convert h using 1
  rw [show (1024 * |lam| * (d : ℝ) ^ 2) = 2 * (512 * |lam| * (d : ℝ) ^ 2) by ring, mul_pow]
  ring

theorem centered_cardinal_factor_product {d n : ℕ} (i : Fin n) (lam : ℝ)
    (z : CenteredCardinalMark d n i) (U : Fin n → Covariate d) :
    (∏ l, centeredCardinalFactor i lam z l (U l)) =
      gaussianTensorObservable lam z.1 (fun _ : SpatialScaleIndex i => U i) (fun j => U j.val) z.2 := by
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
    (fun l => centeredCardinalFactor i lam z l (U l)) (Finset.mem_univ i)]
  have he : centeredCardinalFactor i lam z i (U i) =
      ∏ j : SpatialScaleIndex i, gaussianPrimitiveLeft lam (z.1 j) (z.2 j) (U i) := by
    simp [centeredCardinalFactor]
  rw [he]
  rw [Finset.prod_subtype (p := fun l : Fin n => l ≠ i) ((Finset.univ : Finset (Fin n)).erase i)
    (fun l => by simp) (fun l : Fin n => centeredCardinalFactor i lam z l (U l))]
  have hr : (∏ j : SpatialScaleIndex i, centeredCardinalFactor i lam z j.val (U j.val)) =
      ∏ j : SpatialScaleIndex i, gaussianPrimitiveRight lam (z.1 j) (z.2 j) (U j.val) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [centeredCardinalFactor, dite_eq_left j.property]
  rw [hr, ← Finset.prod_mul_distrib]
  rfl

theorem centered_cardinal_raw_tensor_integrable {d n D : ℕ} (i : Fin n) (lam : ℝ) (hlam : 0 ≤ lam)
    (t : SpatialScaleVector i) (ht : t ∈ Ici 0) (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    Integrable (fun e : GaussianTensorMark (SpatialScaleIndex i) d =>
      gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorFrameAmplitude lam e β β') (gaussianTensorMeasure (SpatialScaleIndex i) d) :=
  (gaussian_tensor_cardinal_moments lam hlam t (fun j => ht j)
    (fun _ => U i) (fun j => U j.val) _ _).1

theorem centered_cardinal_raw_tensor_exact {d n D : ℕ} (i : Fin n) (lam : ℝ) (hlam : 0 ≤ lam)
    (t : SpatialScaleVector i) (ht : t ∈ Ici 0) (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    (∫ e : GaussianTensorMark (SpatialScaleIndex i) d,
      gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorFrameAmplitude lam e β β' ∂gaussianTensorMeasure (SpatialScaleIndex i) d) =
      spatialCenteredCardinalMatrix i lam U t β β' := by
  have h := (gaussian_tensor_cardinal_moments lam hlam t (fun j => ht j)
    (fun _ => U i) (fun j => U j.val) (polynomialBoxExponent β.val) (polynomialBoxExponent β'.val)).2
  simpa only [gaussianTensorFrameAmplitude, gaussianTensorAmplitude, spatialCenteredCardinalMatrix, highFrameCoefficients,
    spatial_cardinal_scale_product, spatial_cardinal_polynomial_scale_product] using h

theorem centered_cardinal_symmetric_tensor_exact {d n D : ℕ} (i : Fin n) (lam : ℝ) (hlam : 0 ≤ lam)
    (t : SpatialScaleVector i) (ht : t ∈ Ici 0) (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    (∫ e : GaussianTensorMark (SpatialScaleIndex i) d,
      gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorSymmetricAmplitude lam e β β' ∂gaussianTensorMeasure (SpatialScaleIndex i) d) =
      spatialCenteredCardinalMatrix i lam U t β β' := by
  have he : (fun e : GaussianTensorMark (SpatialScaleIndex i) d =>
      gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorSymmetricAmplitude lam e β β') =
      fun e => (gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorFrameAmplitude lam e β β' +
        gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorFrameAmplitude lam e β' β) / 2 := by
    funext e
    unfold gaussianTensorSymmetricAmplitude realMatrixSymmetrize
    ring
  rw [he, integral_div, integral_add
    (centered_cardinal_raw_tensor_integrable i lam hlam t ht U β β')
    (centered_cardinal_raw_tensor_integrable i lam hlam t ht U β' β),
    centered_cardinal_raw_tensor_exact i lam hlam t ht U β β',
    centered_cardinal_raw_tensor_exact i lam hlam t ht U β' β]
  unfold spatialCenteredCardinalMatrix
  ring

theorem centered_cardinal_product_entry_integrable {d n D : ℕ} (i : Fin n) (lam : ℝ)
    {T : ℝ} (hT : 1 ≤ T) (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    Integrable (fun z => (∏ l, centeredCardinalFactor i lam z l (U l)) *
      centeredCardinalAmplitude i lam z β β') (centeredCardinalMeasure i d T) := by
  have hm : Measurable (fun z : CenteredCardinalMark d n i => ∏ l, centeredCardinalFactor i lam z l (U l)) :=
    Finset.measurable_fun_prod _ (fun l _ => centered_cardinal_factor_measurable i lam l (U l))
  have hb : ∀ z : CenteredCardinalMark d n i, |∏ l, centeredCardinalFactor i lam z l (U l)| ≤ 1 := by
    intro z
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _l : Fin n, (1 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun l _ => centered_cardinal_factor_abs_le_one i lam z l (U l) (hU l))
      _ = _ := by simp
  have h := (centered_cardinal_entry_integrable i lam hT β β').mul_bdd hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs]; exact hb z))
  exact h.congr (Filter.Eventually.of_forall (fun z => mul_comm _ _))

/-- Exact positive separated representation of each centered, scale-integrated
term of the genuine cardinal covariance. -/
theorem centered_cardinal_integrated_separated_exact {d n D : ℕ} (i : Fin n)
    (lam : ℝ) (hlam : 0 ≤ lam) {T : ℝ} (hT : 1 ≤ T) (U : Fin n → Covariate d)
    (hU : ∀ l r, |U l r| ≤ 2) (β β' : HighFrameIndex d D) :
    (∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i T) =
      ∫ z, (∏ l, centeredCardinalFactor i lam z l (U l)) * centeredCardinalAmplitude i lam z β β'
        ∂centeredCardinalMeasure i d T := by
  letI := spatial_scale_measure_finite i T hT
  letI := gaussianTensorMeasure_finite (SpatialScaleIndex i) d
  symm
  rw [centeredCardinalMeasure, integral_prod _ (centered_cardinal_product_entry_integrable i lam hT U hU β β')]
  apply integral_congr_ae
  have hae : ∀ᵐ t ∂spatialScaleMeasure i T, t ∈ spatialScaleDomain i T :=
    ae_restrict_mem (spatial_scale_domain_isClosed i T).measurableSet
  filter_upwards [hae] with t ht
  simp_rw [centered_cardinal_factor_product]
  exact centered_cardinal_symmetric_tensor_exact i lam hlam t ht.1 U β β'

end NearlyMinimax
