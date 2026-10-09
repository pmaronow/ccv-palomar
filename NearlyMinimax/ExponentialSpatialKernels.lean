module

public import NearlyMinimax.GaussianSpatialDomination
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls


@[expose] public section

/-! Genuine Euclidean exponential spatial-kernel integrals. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The exact Euclidean distance in the source's actual coordinate space. -/
def exactEuclideanDistance {d : ℕ} (x y : Covariate d) : ℝ :=
  Real.sqrt (spatialSquaredDistance x y)

theorem exactEuclideanDistance_nonneg {d : ℕ} (x y : Covariate d) :
    0 ≤ exactEuclideanDistance x y := Real.sqrt_nonneg _

theorem exactEuclideanDistance_eq_norm {d : ℕ} (x y : Covariate d) :
    exactEuclideanDistance x y = ‖WithLp.toLp 2 (y-x)‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold exactEuclideanDistance spatialSquaredDistance
  simp [Real.norm_eq_abs, sq_abs]

theorem exactEuclideanDistance_continuous {d : ℕ} :
    Continuous (fun xy : Covariate d × Covariate d => exactEuclideanDistance xy.1 xy.2) := by
  unfold exactEuclideanDistance spatialSquaredDistance
  fun_prop

/-- A fixed genuine Haar/Gamma constant depending only on dimension. -/
def spatialExponentialConstant (d : ℕ) : ℝ :=
  (d : ℝ) * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) * Real.Gamma d

theorem euclidean_exponential_integrable {d : ℕ} (hd : 0 < d) {N : ℝ} (hN : 0 < N) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (-(N * ‖x‖))) volume := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  apply (integrable_fun_norm_addHaar volume (f := fun r : ℝ => Real.exp (-(N*r)))).2
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := ((d-1 : ℕ) : ℝ)) (p := 1) (b := N) (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _)) (by norm_num) hN
  simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
    Real.rpow_natCast, Real.rpow_one, neg_mul] using hi

/-- The actual Euclidean exponential kernel has exact inverse-volume scaling. -/
theorem euclidean_exponential_integral {d : ℕ} (hd : 0 < d) {N : ℝ} (hN : 0 < N) :
    (∫ x : EuclideanSpace ℝ (Fin d), Real.exp (-(N * ‖x‖))) =
      spatialExponentialConstant d / N^d := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [integral_fun_norm_addHaar volume (fun r : ℝ => Real.exp (-(N*r)))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he (r : ℝ) : r^(d-1) = r^((d : ℝ)-1) := by
    rw [← Real.rpow_natCast, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  simp_rw [he]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hdR hN, Real.rpow_natCast]
  unfold spatialExponentialConstant
  simp only [div_pow, one_pow]
  ring

/-- The source coordinate exponential kernel is genuinely integrable at every center. -/
theorem exactEuclideanDistance_exponential_integrable {d : ℕ} (hd : 0 < d)
    {N : ℝ} (hN : 0 < N) (x : Covariate d) :
    Integrable (fun y => Real.exp (-(N * exactEuclideanDistance x y))) volume := by
  have hi := euclidean_exponential_integrable hd hN
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding] at hi
  have hi0 : Integrable (fun z : Covariate d => Real.exp (-(N * ‖WithLp.toLp 2 z‖))) volume := by
    simpa only [Function.comp_def] using hi
  simpa only [exactEuclideanDistance_eq_norm] using hi0.comp_sub_right x

/-- Exact translated source-coordinate integral, using the true Euclidean measure equivalence. -/
theorem exactEuclideanDistance_exponential_integral {d : ℕ} (hd : 0 < d)
    {N : ℝ} (hN : 0 < N) (x : Covariate d) :
    (∫ y, Real.exp (-(N * exactEuclideanDistance x y))) = spatialExponentialConstant d / N^d := by
  simp_rw [exactEuclideanDistance_eq_norm]
  rw [integral_sub_right_eq_self (μ := volume) (fun z : Covariate d => Real.exp (-(N * ‖WithLp.toLp 2 z‖)))]
  exact ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding
    (fun z : EuclideanSpace ℝ (Fin d) => Real.exp (-(N * ‖z‖)))).trans
      (euclidean_exponential_integral hd hN)

/-- A true exponential-series estimate absorbs the quadratic pair defect. -/
theorem pair_defect_exponential_absorption (t : ℝ) (ht : 0 ≤ t) :
    (1+t)^2 * Real.exp (-(2*t)) ≤ 6 * Real.exp (-t) := by
  have hp := Real.pow_div_factorial_le_exp t ht 2
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, mul_one] at hp
  have h1 : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have hpoly : (1+t)^2 ≤ 6 * Real.exp t := by nlinarith [sq_nonneg (t-1)]
  have hh := mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg (-(2*t)))
  rw [mul_assoc, ← Real.exp_add, show t + -(2*t) = -t by ring] at hh
  exact hh

/-- The genuine count-two defect integral is bounded by a fixed dimension constant times N^-d. -/
theorem pair_defect_spatial_integral_le {d : ℕ} (hd : 0 < d) {N : ℝ} (hN : 0 < N)
    (x : Covariate d) :
    (∫ y, (1 + N * exactEuclideanDistance x y)^2 * Real.exp (-(2*N*exactEuclideanDistance x y))) ≤
      6 * spatialExponentialConstant d / N^d := by
  have hi := exactEuclideanDistance_exponential_integrable hd hN x
  have hm : Measurable (fun y : Covariate d =>
      (1 + N * exactEuclideanDistance x y)^2 * Real.exp (-(2*N*exactEuclideanDistance x y))) := by
    have hc : Continuous (fun y : Covariate d => exactEuclideanDistance x y) :=
      exactEuclideanDistance_continuous (d := d) |>.comp ((continuous_const : Continuous (fun _ : Covariate d => x)).prodMk continuous_id)
    exact ((continuous_const.add (continuous_const.mul hc)).pow 2 |>.mul
      (continuous_const.mul hc |>.neg |>.rexp)).measurable
  have hb (y : Covariate d) :
      (1 + N * exactEuclideanDistance x y)^2 * Real.exp (-(2*N*exactEuclideanDistance x y)) ≤
      6 * Real.exp (-(N*exactEuclideanDistance x y)) := by
    simpa only [mul_assoc] using pair_defect_exponential_absorption
      (N*exactEuclideanDistance x y) (mul_nonneg hN.le (exactEuclideanDistance_nonneg x y))
  have hfi : Integrable (fun y : Covariate d =>
      (1 + N * exactEuclideanDistance x y)^2 * Real.exp (-(2*N*exactEuclideanDistance x y))) volume :=
    (hi.const_mul 6).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hb y)
  calc
    _ ≤ ∫ y, 6 * Real.exp (-(N*exactEuclideanDistance x y)) := integral_mono hfi (hi.const_mul 6) hb
    _ = _ := by rw [integral_const_mul, exactEuclideanDistance_exponential_integral hd hN]; ring

theorem spatialExponentialConstant_nonneg (d : ℕ) : 0 ≤ spatialExponentialConstant d := by
  unfold spatialExponentialConstant
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg d) ENNReal.toReal_nonneg)
    (Real.Gamma_nonneg_of_nonneg (Nat.cast_nonneg d))

theorem spatialPatchBox_volume (d : ℕ) : volume (spatialPatchBox d) = (2 : ℝ≥0∞)^d := by
  simp only [spatialPatchBox, Real.volume_Icc_pi, sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem spatialPatchBox_real_volume (d : ℕ) : volume.real (spatialPatchBox d) = (2 : ℝ)^d := by
  rw [measureReal_def, spatialPatchBox_volume, ENNReal.toReal_pow]
  norm_num

instance spatialPatchBox_isFinite (d : ℕ) :
    IsFiniteMeasure (volume.restrict (spatialPatchBox d)) := by
  constructor
  rw [Measure.restrict_apply_univ, spatialPatchBox_volume]
  finiteness

/-- Actual bounded-domain pair integration loses only the first point's volume. -/
theorem exactEuclideanDistance_pair_exponential_integral_le {d : ℕ} (hd : 0 < d)
    {T : ℝ} (hT : 0 < T) (S : Set (Covariate d)) (hfinite : volume S < ∞) :
    (∫ xy : Covariate d × Covariate d, Real.exp (-(T * exactEuclideanDistance xy.1 xy.2))
      ∂(volume.restrict S).prod (volume.restrict S)) ≤ volume.real S * spatialExponentialConstant d / T^d := by
  let μ : Measure (Covariate d) := volume.restrict S
  let : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using hfinite⟩
  have hm : Measurable (fun xy : Covariate d × Covariate d =>
      Real.exp (-(T * exactEuclideanDistance xy.1 xy.2))) :=
    (exactEuclideanDistance_continuous (d := d) |>.const_mul T |>.neg |>.rexp).measurable
  have hi : Integrable (fun xy : Covariate d × Covariate d =>
      Real.exp (-(T * exactEuclideanDistance xy.1 xy.2))) (μ.prod μ) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun xy => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hT.le (exactEuclideanDistance_nonneg _ _))))
  rw [integral_prod _ hi]
  have hb (x : Covariate d) :
      (∫ y, Real.exp (-(T*exactEuclideanDistance x y)) ∂μ) ≤ spatialExponentialConstant d / T^d :=
    (integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
      (exactEuclideanDistance_exponential_integrable hd hT x)).trans_eq
        (exactEuclideanDistance_exponential_integral hd hT x)
  calc
    _ ≤ ∫ _x : Covariate d, spatialExponentialConstant d / T^d ∂μ :=
      integral_mono hi.integral_prod_left (integrable_const _) hb
    _ = _ := by simp only [integral_const, smul_eq_mul, μ, measureReal_def, Measure.restrict_apply_univ]; ring

/-- The source Q=[-1,1]^d pair integral has a genuine fixed spatial constant. -/
theorem spatialPatchBox_pair_exponential_integral_le {d : ℕ} (hd : 0 < d)
    {T : ℝ} (hT : 0 < T) :
    (∫ xy : Covariate d × Covariate d, Real.exp (-(T * exactEuclideanDistance xy.1 xy.2))
      ∂(volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) ≤
      (2 : ℝ)^d * spatialExponentialConstant d / T^d := by
  simpa only [spatialPatchBox_real_volume] using exactEuclideanDistance_pair_exponential_integral_le hd hT
    (spatialPatchBox d) (by rw [spatialPatchBox_volume]; finiteness)

end NearlyMinimax
