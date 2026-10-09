module

public import NearlyMinimax.GaussianAffineRepresentation
public import NearlyMinimax.HighSeparatedRows
public import NearlyMinimax.ActualSeparatedPacket


@[expose] public section

/-! A genuine positive Gaussian separated representation of the exact
two-observation affine covariance building block, with bounded factors and
uniform integrated coefficient cost. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set MvPolynomial
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

abbrev GaussianPrimitiveIndex (d : ℕ) := (Fin d × Fin d) × (Bool × Bool) × Bool
abbrev GaussianPrimitiveMark (d : ℕ) := Covariate d × GaussianPrimitiveIndex d

def gaussianPrimitiveMeasure (d : ℕ) : Measure (GaussianPrimitiveMark d) :=
  (standardGaussianPi d).prod Measure.count

def gaussianTrig {d : ℕ} (lam t : ℝ) (Z x : Covariate d) (s : Bool) : ℝ :=
  if s then Real.sin (gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z)
  else Real.cos (gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z)

theorem gaussianTrig_abs_le_one {d : ℕ} (lam t : ℝ) (Z x : Covariate d) (s : Bool) :
    |gaussianTrig lam t Z x s| ≤ 1 := by
  cases s <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true]
  · exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  · exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

theorem gaussianTrig_cos_difference {d : ℕ} (lam t : ℝ) (Z x y : Covariate d) :
    Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) =
      ∑ s : Bool, gaussianTrig lam t Z x s * gaussianTrig lam t Z y s := by
  have he : gaussianPhase (gaussianSpatialFrequency lam t x y) Z =
      gaussianPhase (fun l => Real.sqrt (2 * lam * t) * y l) Z -
      gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z := by
    simp only [gaussianPhase, gaussianSpatialFrequency, Finset.sum_sub_distrib]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [he, Real.cos_sub]
  simp only [Fintype.sum_bool, gaussianTrig, Bool.false_eq_true, ite_false, ite_true]
  ring

def gaussianAffinePolynomial {d : ℕ} (a : Fin d) (s : Bool) : MvPolynomial (Fin d) ℝ :=
  if s then C (-8) * X a else C 2

def gaussianAffineFactor {d : ℕ} (a : Fin d) (s : Bool) (y : Covariate d) : ℝ :=
  if s then 1 else y a / 2

theorem gaussianAffineFactor_abs_le_one {d : ℕ} (a : Fin d) (s : Bool) (y : Covariate d)
    (hy : |y a| ≤ 2) : |gaussianAffineFactor a s y| ≤ 1 := by
  cases s
  · simp only [gaussianAffineFactor, Bool.false_eq_true, ite_false, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by simpa using hy)
  · simp [gaussianAffineFactor]

theorem spatialCardinalAffine_gaussian_expansion {d : ℕ} (x y : Covariate d) :
    spatialCardinalAffine x y =
      ∑ a : Fin d, C (y a - x a) *
        ∑ s : Bool, C (gaussianAffineFactor a s y) * gaussianAffinePolynomial a s := by
  unfold spatialCardinalAffine
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Fintype.sum_bool, gaussianAffineFactor, gaussianAffinePolynomial,
    Bool.false_eq_true, ite_false, ite_true]
  rw [← C_mul]
  have hy : y a / 2 * 2 = y a := by ring
  rw [hy]
  simp only [C_1, one_mul]
  simp only [map_mul, map_neg]
  ring

theorem spatialCardinalAffine_gaussian_coeff {d : ℕ} (x y : Covariate d) (β : Fin d →₀ ℕ) :
    (spatialCardinalAffine x y).coeff β =
      ∑ a : Fin d, (y a - x a) *
        ∑ s : Bool, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β := by
  rw [spatialCardinalAffine_gaussian_expansion]
  simp only [coeff_sum, coeff_C_mul]

def gaussianPrimitiveLeft {d : ℕ} (lam t : ℝ) (e : GaussianPrimitiveMark d) (x : Covariate d) : ℝ :=
  gaussianTrig lam t e.1 x e.2.2.2

def gaussianPrimitiveRight {d : ℕ} (lam t : ℝ) (e : GaussianPrimitiveMark d) (y : Covariate d) : ℝ :=
  gaussianTrig lam t e.1 y e.2.2.2 *
    gaussianAffineFactor e.2.1.1 e.2.2.1.1 y * gaussianAffineFactor e.2.1.2 e.2.2.1.2 y

def gaussianPrimitiveAmplitude {d : ℕ} (lam : ℝ) (e : GaussianPrimitiveMark d)
    (β β' : Fin d →₀ ℕ) : ℝ :=
  lam / 2 * gaussianHermite e.2.1.1 e.2.1.2 e.1 *
    (gaussianAffinePolynomial e.2.1.1 e.2.2.1.1).coeff β *
      (gaussianAffinePolynomial e.2.1.2 e.2.2.1.2).coeff β'

def gaussianPrimitiveFrameAmplitude {d D : ℕ} (lam : ℝ) (e : GaussianPrimitiveMark d)
    (β β' : HighFrameIndex d D) : ℝ :=
  gaussianPrimitiveAmplitude lam e (polynomialBoxExponent β.val) (polynomialBoxExponent β'.val)

theorem gaussianPrimitiveLeft_bound {d : ℕ} (lam t : ℝ) (e : GaussianPrimitiveMark d) (x : Covariate d) :
    |gaussianPrimitiveLeft lam t e x| ≤ 1 := gaussianTrig_abs_le_one _ _ _ _ _

theorem gaussianPrimitiveRight_bound {d : ℕ} (lam t : ℝ) (e : GaussianPrimitiveMark d)
    (y : Covariate d) (hy : ∀ a, |y a| ≤ 2) : |gaussianPrimitiveRight lam t e y| ≤ 1 := by
  unfold gaussianPrimitiveRight
  rw [abs_mul, abs_mul]
  have h1 := gaussianTrig_abs_le_one lam t e.1 y e.2.2.2
  have h2 := gaussianAffineFactor_abs_le_one e.2.1.1 e.2.2.1.1 y (hy _)
  have h3 := gaussianAffineFactor_abs_le_one e.2.1.2 e.2.2.1.2 y (hy _)
  exact (mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) h3
    (abs_nonneg _) (by norm_num)).trans_eq (by ring)

theorem gaussianPrimitiveLeft_measurable {d : ℕ} (lam t : ℝ) (x : Covariate d) :
    Measurable (fun e : GaussianPrimitiveMark d => gaussianPrimitiveLeft lam t e x) := by
  apply measurable_from_prod_countable_left
  intro h
  change Measurable (fun Z : Covariate d => gaussianTrig lam t Z x h.2.2)
  cases h.2.2 <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true] <;>
    unfold gaussianPhase <;> fun_prop

theorem gaussianPrimitiveRight_measurable {d : ℕ} (lam t : ℝ) (y : Covariate d) :
    Measurable (fun e : GaussianPrimitiveMark d => gaussianPrimitiveRight lam t e y) := by
  apply measurable_from_prod_countable_left
  intro h
  unfold gaussianPrimitiveRight
  dsimp only
  have hm : Measurable (fun Z : Covariate d => gaussianTrig lam t Z y h.2.2) := by
    cases h.2.2 <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true] <;>
      unfold gaussianPhase <;> fun_prop
  exact (hm.mul_const _).mul_const _

theorem gaussianPrimitiveAmplitude_measurable {d : ℕ} (lam : ℝ) (β β' : Fin d →₀ ℕ) :
    Measurable (fun e : GaussianPrimitiveMark d => gaussianPrimitiveAmplitude lam e β β') := by
  apply measurable_from_prod_countable_left
  intro h
  unfold gaussianPrimitiveAmplitude
  dsimp only
  have hm : Measurable (fun Z : Covariate d => gaussianHermite h.1.1 h.1.2 Z) :=
    measurable_const.sub ((measurable_pi_apply _).mul (measurable_pi_apply _))
  exact ((hm.const_mul _).mul_const _).mul_const _

theorem gaussianPrimitiveAmplitude_slice_integrable {d : ℕ} (lam : ℝ)
    (β β' : Fin d →₀ ℕ) (h : GaussianPrimitiveIndex d) :
    Integrable (fun Z => gaussianPrimitiveAmplitude lam (Z, h) β β') (standardGaussianPi d) := by
  change Integrable (fun Z => lam / 2 * gaussianHermite h.1.1 h.1.2 Z *
    (gaussianAffinePolynomial h.1.1 h.2.1.1).coeff β *
    (gaussianAffinePolynomial h.1.2 h.2.1.2).coeff β') (standardGaussianPi d)
  exact (((gaussianHermite_integrable h.1.1 h.1.2).const_mul _).mul_const _).mul_const _

theorem gaussianPrimitiveAmplitude_integrable {d : ℕ} (lam : ℝ) (β β' : Fin d →₀ ℕ) :
    Integrable (fun e : GaussianPrimitiveMark d => gaussianPrimitiveAmplitude lam e β β')
      (gaussianPrimitiveMeasure d) :=
  joint_finite_integrable _ _
    (fun h => (gaussianPrimitiveAmplitude_measurable lam β β').comp
      (measurable_id.prodMk measurable_const))
    (gaussianPrimitiveAmplitude_slice_integrable lam β β')

theorem finite_injective_indicator_sum_le_one {I X : Type*} [Fintype I] [DecidableEq X]
    (f : I → X) (hf : Function.Injective f) (x : X) :
    (∑ i, if x = f i then (1 : ℝ) else 0) ≤ 1 := by
  classical
  by_cases hx : ∃ i, f i = x
  · obtain ⟨i, hi⟩ := hx
    have he (j : I) : x = f j ↔ j = i := by
      rw [← hi]
      exact ⟨fun h => (hf h).symm, fun h => by rw [h]⟩
    simp_rw [he]
    simp
  · have he (j : I) : x ≠ f j := by intro h; exact hx ⟨j, h.symm⟩
    simp only [ite_eq_right (he _), Finset.sum_const_zero]
    norm_num

theorem gaussianAffinePolynomial_frame_cost {d D : ℕ} (a : Fin d) (s : Bool) :
    (∑ β : HighFrameIndex d D, |highFrameCoefficients (gaussianAffinePolynomial a s) β|) ≤ 8 := by
  classical
  have hinj : Function.Injective (fun β : HighFrameIndex d D => polynomialBoxExponent β.val) := by
    intro β β' h
    exact Subtype.ext (polynomial_box_exponent_injective h)
  cases s
  · have he (β : HighFrameIndex d D) : |highFrameCoefficients (gaussianAffinePolynomial a false) β| =
        2 * (if (0 : Fin d →₀ ℕ) = polynomialBoxExponent β.val then 1 else 0) := by
      simp only [gaussianAffinePolynomial, Bool.false_eq_true, ite_false,
        highFrameCoefficients, coeff_C]
      split_ifs <;> norm_num
    simp_rw [he]
    rw [← Finset.mul_sum]
    have h := finite_injective_indicator_sum_le_one _ hinj (0 : Fin d →₀ ℕ)
    linarith
  · have he (β : HighFrameIndex d D) : |highFrameCoefficients (gaussianAffinePolynomial a true) β| =
        8 * (if Finsupp.single a 1 = polynomialBoxExponent β.val then 1 else 0) := by
      simp only [gaussianAffinePolynomial, ite_true, highFrameCoefficients, coeff_C_mul, coeff_X]
      split_ifs <;> norm_num
    simp_rw [he]
    rw [← Finset.mul_sum]
    have h := finite_injective_indicator_sum_le_one _ hinj (Finsupp.single a 1)
    linarith

theorem gaussianPrimitiveFrameAmplitude_cost_bound {d D : ℕ} (lam : ℝ)
    (e : GaussianPrimitiveMark d) :
    separatedMatrixCost (gaussianPrimitiveFrameAmplitude (D := D) lam) e ≤
      32 * |lam| * |gaussianHermite e.2.1.1 e.2.1.2 e.1| := by
  have he : separatedMatrixCost (gaussianPrimitiveFrameAmplitude (D := D) lam) e =
      |lam / 2| * |gaussianHermite e.2.1.1 e.2.1.2 e.1| *
        (∑ β : HighFrameIndex d D, |highFrameCoefficients (gaussianAffinePolynomial e.2.1.1 e.2.2.1.1) β|) *
        (∑ β : HighFrameIndex d D, |highFrameCoefficients (gaussianAffinePolynomial e.2.1.2 e.2.2.1.2) β|) := by
    unfold separatedMatrixCost gaussianPrimitiveFrameAmplitude gaussianPrimitiveAmplitude highFrameCoefficients
    simp only [abs_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [he]
  have hprod := mul_le_mul (gaussianAffinePolynomial_frame_cost (D := D) e.2.1.1 e.2.2.1.1)
    (gaussianAffinePolynomial_frame_cost (D := D) e.2.1.2 e.2.2.1.2)
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num : (0 : ℝ) ≤ 8)
  have hh := mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (abs_nonneg (lam / 2)) (abs_nonneg (gaussianHermite e.2.1.1 e.2.1.2 e.1)))
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  convert hh using 1 <;> ring

theorem gaussianPrimitiveFrameAmplitude_cost_integrable {d D : ℕ} (lam : ℝ) :
    Integrable (separatedMatrixCost (gaussianPrimitiveFrameAmplitude (D := D) lam))
      (gaussianPrimitiveMeasure d) := by
  apply integrable_finsetSum _
  intro β hβ
  apply integrable_finsetSum _
  intro β' hβ'
  exact (gaussianPrimitiveAmplitude_integrable lam (polynomialBoxExponent β.val)
    (polynomialBoxExponent β'.val)).abs

theorem gaussianPrimitiveFrameAmplitude_integrated_cost {d D : ℕ} (lam : ℝ) :
    (∫ e, separatedMatrixCost (gaussianPrimitiveFrameAmplitude (D := D) lam) e
      ∂gaussianPrimitiveMeasure d) ≤ 512 * |lam| * (d : ℝ) ^ 2 := by
  have hslice (h : GaussianPrimitiveIndex d) :
      (∫ Z, separatedMatrixCost (gaussianPrimitiveFrameAmplitude (D := D) lam) (Z, h)
        ∂standardGaussianPi d) ≤ 64 * |lam| := by
    have hi : Integrable (fun Z => separatedMatrixCost (gaussianPrimitiveFrameAmplitude (D := D) lam) (Z, h))
        (standardGaussianPi d) := by
      apply integrable_finsetSum _
      intro β hβ
      apply integrable_finsetSum _
      intro β' hβ'
      exact (gaussianPrimitiveAmplitude_slice_integrable lam (polynomialBoxExponent β.val)
        (polynomialBoxExponent β'.val) h).abs
    have hm := integral_mono hi ((gaussianHermite_integrable h.1.1 h.1.2).abs.const_mul (32 * |lam|))
      (fun Z => gaussianPrimitiveFrameAmplitude_cost_bound lam (Z, h))
    rw [integral_const_mul] at hm
    have hc := mul_le_mul_of_nonneg_left (standardGaussian_hermite_abs_integral_le_two h.1.1 h.1.2)
      (by positivity : 0 ≤ 32 * |lam|)
    exact hm.trans (hc.trans_eq (by ring))
  rw [gaussianPrimitiveMeasure, integral_prod_symm _ (gaussianPrimitiveFrameAmplitude_cost_integrable lam),
    integral_count]
  have hm := Finset.sum_le_sum (s := Finset.univ) (fun h _ => hslice h)
  convert hm using 1 <;> simp [GaussianPrimitiveIndex, Fintype.card_prod, pow_two] <;> ring

theorem gaussianPrimitive_finite_action {d : ℕ} (lam t : ℝ) (x y Z : Covariate d)
    (β β' : Fin d →₀ ℕ) :
    (∑ h : GaussianPrimitiveIndex d,
      gaussianPrimitiveLeft lam t (Z, h) x * gaussianPrimitiveRight lam t (Z, h) y *
        gaussianPrimitiveAmplitude lam (Z, h) β β') =
      lam / 2 * ∑ a : Fin d, ∑ b : Fin d,
        gaussianHermite a b Z *
          (∑ s : Bool, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β) *
          (∑ s : Bool, gaussianAffineFactor b s y * (gaussianAffinePolynomial b s).coeff β') *
          Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) := by
  classical
  simp only [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hphase (s s' : Bool) :
      (∑ p : Bool, gaussianPrimitiveLeft lam t (Z, ((a, b), ((s, s'), p))) x *
        gaussianPrimitiveRight lam t (Z, ((a, b), ((s, s'), p))) y *
          gaussianPrimitiveAmplitude lam (Z, ((a, b), ((s, s'), p))) β β') =
      (lam / 2 * gaussianHermite a b Z * Real.cos
        (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) *
          (gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β) *
          (gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β') := by
    rw [gaussianTrig_cos_difference]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    unfold gaussianPrimitiveLeft gaussianPrimitiveRight gaussianPrimitiveAmplitude
    dsimp only
    ring
  simp_rw [hphase]
  have he := Fintype.sum_mul_sum
    (fun s : Bool => gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β)
    (fun s' : Bool => gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β')
  calc
    _ = (lam / 2 * gaussianHermite a b Z * Real.cos
        (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) *
        (∑ s : Bool, ∑ s' : Bool,
          (gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β) *
          (gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β')) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro s' hs'
      ring
    _ = _ := by rw [← he]; ring

theorem gaussianPrimitive_observable_integrable {d : ℕ} (lam t : ℝ) (x y : Covariate d)
    (β β' : Fin d →₀ ℕ) :
    Integrable (fun e : GaussianPrimitiveMark d => gaussianPrimitiveLeft lam t e x *
      gaussianPrimitiveRight lam t e y * gaussianPrimitiveAmplitude lam e β β')
      (gaussianPrimitiveMeasure d) := by
  let L := ∑ h : GaussianPrimitiveIndex d,
    |gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y|
  have hm : Measurable (fun e : GaussianPrimitiveMark d =>
      gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y) :=
    (gaussianPrimitiveLeft_measurable lam t x).mul (gaussianPrimitiveRight_measurable lam t y)
  have hb (e : GaussianPrimitiveMark d) :
      ‖gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y‖ ≤ L := by
    unfold gaussianPrimitiveLeft gaussianPrimitiveRight
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have htrig := mul_le_mul (gaussianTrig_abs_le_one lam t e.1 x e.2.2.2)
      (gaussianTrig_abs_le_one lam t e.1 y e.2.2.2) (abs_nonneg _) (by norm_num)
    have hl : |gaussianAffineFactor e.2.1.1 e.2.2.1.1 y| *
        |gaussianAffineFactor e.2.1.2 e.2.2.1.2 y| ≤ L := by
      dsimp [L]
      rw [← abs_mul]
      exact Finset.single_le_sum (fun h _ => abs_nonneg
        (gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y))
        (Finset.mem_univ e.2)
    calc
      _ = (|gaussianTrig lam t e.1 x e.2.2.2| * |gaussianTrig lam t e.1 y e.2.2.2|) *
          (|gaussianAffineFactor e.2.1.1 e.2.2.1.1 y| * |gaussianAffineFactor e.2.1.2 e.2.2.1.2 y|) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right htrig (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans
        (by simpa using hl)
  have hi := (gaussianPrimitiveAmplitude_integrable lam β β').mul_bdd hm.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  convert hi using 1
  funext e
  ring

theorem gaussianAffine_coefficient_bilinear {d : ℕ} (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (x y : Covariate d) (va vb : Fin d → ℝ) :
    t * lam ^ 2 * Real.exp (-(t * lam * spatialSquaredDistance x y)) *
      (∑ a, (y a - x a) * va a) * (∑ b, (y b - x b) * vb b) =
      lam / 2 * ∑ a : Fin d, ∑ b : Fin d,
        ∫ Z, gaussianHermite a b Z * va a * vb b *
          Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) ∂standardGaussianPi d := by
  simp_rw [standardGaussian_hermite_cos_integral_const,
    gaussianSpatialFrequency_squared lam t hlam ht x y]
  have he : -(2 * lam * t * spatialSquaredDistance x y) / 2 =
      -(t * lam * spatialSquaredDistance x y) := by ring
  rw [he]
  unfold gaussianSpatialFrequency
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * lam * t)
  calc
    _ = lam / 2 * (2 * lam * t) * (y a - x a) * (y b - x b) * va a * vb b *
        Real.exp (-(t * lam * spatialSquaredDistance x y)) := by ring
    _ = lam / 2 * (Real.sqrt (2 * lam * t) ^ 2) * (y a - x a) * (y b - x b) * va a * vb b *
        Real.exp (-(t * lam * spatialSquaredDistance x y)) := by rw [hs]
    _ = _ := by ring

/-- Exact coefficientwise positive separated representation of the original
G_t affine covariance. All Fourier, Fubini, and coefficient identities are
derived from the actual Gaussian product law. -/
theorem gaussianPrimitive_separated_exact {d : ℕ} (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (x y : Covariate d) (β β' : Fin d →₀ ℕ) :
    t * lam ^ 2 * Real.exp (-(t * lam * spatialSquaredDistance x y)) *
      (spatialCardinalAffine x y).coeff β * (spatialCardinalAffine x y).coeff β' =
      ∫ e, gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y *
        gaussianPrimitiveAmplitude lam e β β' ∂gaussianPrimitiveMeasure d := by
  rw [gaussianPrimitiveMeasure, integral_prod _ (gaussianPrimitive_observable_integrable lam t x y β β')]
  simp only [integral_count, gaussianPrimitive_finite_action]
  let va := fun a : Fin d => ∑ s : Bool, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β
  let vb := fun b : Fin d => ∑ s : Bool, gaussianAffineFactor b s y * (gaussianAffinePolynomial b s).coeff β'
  have hi (a b : Fin d) : Integrable (fun Z : Covariate d => gaussianHermite a b Z * va a * vb b *
      Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) (standardGaussianPi d) := by
    have hm : Measurable (fun Z : Covariate d => Real.cos
        (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) := by
      unfold gaussianPhase
      fun_prop
    exact (((gaussianHermite_integrable a b).mul_const (va a)).mul_const (vb b)).mul_bdd
      hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun Z => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩))
  change _ = ∫ Z, lam / 2 * ∑ a : Fin d, ∑ b : Fin d,
    gaussianHermite a b Z * va a * vb b * Real.cos
      (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) ∂standardGaussianPi d
  rw [integral_const_mul, integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  simp_rw [integral_finsetSum _ (fun b _ => hi _ b)]
  rw [spatialCardinalAffine_gaussian_coeff, spatialCardinalAffine_gaussian_coeff]
  exact gaussianAffine_coefficient_bilinear lam t hlam ht x y va vb

theorem gaussianPrimitiveMeasure_finite (d : ℕ) : IsFiniteMeasure (gaussianPrimitiveMeasure d) := by
  unfold gaussianPrimitiveMeasure
  infer_instance

theorem gaussianPrimitiveMark_standardBorel (d : ℕ) : StandardBorelSpace (GaussianPrimitiveMark d) := by
  infer_instance

theorem gaussianPrimitiveLeft_scale_measurable {d : ℕ} (lam : ℝ) (x : Covariate d) :
    Measurable (fun z : ℝ × GaussianPrimitiveMark d => gaussianPrimitiveLeft lam z.1 z.2 x) := by
  have hm : Measurable (fun z : (ℝ × Covariate d) × GaussianPrimitiveIndex d =>
      gaussianPrimitiveLeft lam z.1.1 (z.1.2, z.2) x) := by
    apply measurable_from_prod_countable_left
    intro h
    change Measurable (fun z : ℝ × Covariate d => gaussianTrig lam z.1 z.2 x h.2.2)
    cases h.2.2 <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true] <;>
      unfold gaussianPhase <;> fun_prop
  exact hm.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
    (measurable_snd.comp measurable_snd))

theorem gaussianPrimitiveRight_scale_measurable {d : ℕ} (lam : ℝ) (y : Covariate d) :
    Measurable (fun z : ℝ × GaussianPrimitiveMark d => gaussianPrimitiveRight lam z.1 z.2 y) := by
  have hm : Measurable (fun z : (ℝ × Covariate d) × GaussianPrimitiveIndex d =>
      gaussianPrimitiveRight lam z.1.1 (z.1.2, z.2) y) := by
    apply measurable_from_prod_countable_left
    intro h
    change Measurable (fun z : ℝ × Covariate d => gaussianTrig lam z.1 z.2 y h.2.2 *
      gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y)
    have ht : Measurable (fun z : ℝ × Covariate d => gaussianTrig lam z.1 z.2 y h.2.2) := by
      cases h.2.2 <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true] <;>
        unfold gaussianPhase <;> fun_prop
    exact (ht.mul_const _).mul_const _
  exact hm.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
    (measurable_snd.comp measurable_snd))

/-- The primitive representation in exactly the source finite-frame coefficients. -/
theorem gaussianPrimitive_frame_separated_exact {d D : ℕ} (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (x y : Covariate d) (β β' : HighFrameIndex d D) :
    t * lam ^ 2 * Real.exp (-(t * lam * spatialSquaredDistance x y)) *
      highFrameCoefficients (spatialCardinalAffine x y) β *
        highFrameCoefficients (spatialCardinalAffine x y) β' =
      ∫ e, gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y *
        gaussianPrimitiveFrameAmplitude lam e β β' ∂gaussianPrimitiveMeasure d :=
  gaussianPrimitive_separated_exact lam t hlam ht x y _ _

end NearlyMinimax
