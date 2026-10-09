module

public import NearlyMinimax.ExponentialSpatialKernels
public import NearlyMinimax.GammaTailBounds


@[expose] public section

/-! Genuine scalar pair Laplace kernels and fine-tail spatial integrability. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The true scalar pair kernel from the source integral. -/
def pairLaplaceKernel (N r : ℝ) : ℝ := ∫ T in (0 : ℝ)..N, T * Real.exp (-(T*r))

/-- The true fine alias Laplace kernel. -/
def fineAliasLaplaceKernel (T0 N r : ℝ) : ℝ := ∫ T in T0..N, T * Real.exp (-(T*r))

theorem exactEuclideanDistance_eq_euclideanNorm {d : ℕ} (x y : Covariate d) :
    exactEuclideanDistance x y = euclideanNorm (fun i => x i - y i) := by
  unfold exactEuclideanDistance spatialSquaredDistance euclideanNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual complete positive-tail Laplace integral. -/
theorem laplace_linear_tail_integral {r : ℝ} (hr : 0 < r) (A : ℝ) :
    (∫ T : ℝ in Ici A, T * Real.exp (-(T*r))) =
      (1 + A*r) * Real.exp (-(A*r)) / r^2 := by
  have hh := gamma_polynomial_tail_integral hr A 1
  have he : (∫ T : ℝ in Ici A, T * Real.exp (-(T*r))) =
      Real.exp (-(r*A)) * (1/r^2 + A/r) := by
    simpa [Finset.sum_range_succ, mul_comm] using hh
  rw [he, mul_comm r A]
  field_simp

theorem laplace_linear_tail_integrable {r : ℝ} (hr : 0 < r) (A : ℝ) :
    IntegrableOn (fun T : ℝ => T * Real.exp (-(T*r))) (Ici A) := by
  simpa [mul_comm] using gamma_polynomial_tail_integrable hr A 1

/-- Actual finite Laplace integration, derived by subtracting two genuine complete tails. -/
theorem pairLaplaceKernel_formula {r : ℝ} (hr : 0 < r) (N : ℝ) :
    pairLaplaceKernel N r = (1 - (1+N*r)*Real.exp (-(N*r))) / r^2 := by
  unfold pairLaplaceKernel
  rw [← intervalIntegral.integral_Ici_sub_Ici'
    (laplace_linear_tail_integrable hr 0) (laplace_linear_tail_integrable hr N),
    laplace_linear_tail_integral hr 0, laplace_linear_tail_integral hr N]
  simp only [zero_mul, add_zero, neg_zero, Real.exp_zero, mul_one]
  ring

/-- The exact count-two cancellation identity, including zero distance. -/
theorem pairLaplaceKernel_defect (N r : ℝ) (hr : 0 ≤ r) :
    1 - r^2 * pairLaplaceKernel N r = (1+N*r) * Real.exp (-(N*r)) := by
  by_cases hr0 : r = 0
  · simp [hr0]
  · rw [pairLaplaceKernel_formula (lt_of_le_of_ne hr (Ne.symm hr0))]
    field_simp
    ring

/-- The actual finite fine tail equals a difference of its genuine endpoint tails. -/
theorem fineAliasLaplaceKernel_formula {r : ℝ} (hr : 0 < r) (T0 N : ℝ) :
    fineAliasLaplaceKernel T0 N r =
      ((1+T0*r)*Real.exp (-(T0*r)) - (1+N*r)*Real.exp (-(N*r))) / r^2 := by
  unfold fineAliasLaplaceKernel
  rw [← intervalIntegral.integral_Ici_sub_Ici'
    (laplace_linear_tail_integrable hr T0) (laplace_linear_tail_integrable hr N),
    laplace_linear_tail_integral hr T0, laplace_linear_tail_integral hr N]
  ring

/-- Fine Laplace integration is nonnegative and bounded by its complete tail. -/
theorem fineAliasLaplaceKernel_nonneg_le {r T0 N : ℝ} (hr : 0 < r) (hT0 : 0 ≤ T0) (hN : T0 ≤ N) :
    0 ≤ fineAliasLaplaceKernel T0 N r ∧
      fineAliasLaplaceKernel T0 N r ≤ (1+T0*r)*Real.exp (-(T0*r))/r^2 := by
  constructor
  · unfold fineAliasLaplaceKernel
    apply intervalIntegral.integral_nonneg hN
    intro T hT
    exact mul_nonneg (hT0.trans hT.1) (Real.exp_pos _).le
  · rw [fineAliasLaplaceKernel_formula hr]
    have hpos : 0 ≤ (1+N*r)*Real.exp (-(N*r)) := by
      have hn0 := hT0.trans hN
      positivity
    have hd : 0 ≤ r^2 := sq_nonneg _
    exact div_le_div_of_nonneg_right (sub_le_self _ hpos) hd

theorem fineAliasLaplaceKernel_measurable (T0 N : ℝ) (hN : T0 ≤ N) :
    Measurable (fineAliasLaplaceKernel T0 N) := by
  unfold fineAliasLaplaceKernel
  simp_rw [intervalIntegral.integral_of_le hN]
  have hm : Measurable (fun rt : ℝ × ℝ => rt.2 * Real.exp (-(rt.2*rt.1))) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- A true complete-space radial constant for the fine alias tail. -/
def spatialInverseFourConstant (d : ℕ) : ℝ :=
  (d : ℝ) * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) * ((d-5).factorial : ℝ)

private theorem radial_inverse_four_monomial {d : ℕ} (hd : 4 < d) {r : ℝ} (hr : r ≠ 0) (T : ℝ) :
    r^(d-1) * (Real.exp (-(T*r))/r^4) = r^(d-5) * Real.exp (-(T*r)) := by
  calc
    _ = (r^(d-1)/r^4) * Real.exp (-(T*r)) := by ring
    _ = _ := by
      rw [show d-1 = d-5+4 by omega, pow_add]
      field_simp

/-- The singular envelope is actually integrable exactly in the source dimension regime. -/
theorem euclidean_inverse_four_exponential_integrable {d : ℕ} (hd : 4 < d)
    {T : ℝ} (hT : 0 < T) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => Real.exp (-(T*‖z‖))/‖z‖^4) volume := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  apply (integrable_fun_norm_addHaar volume (f := fun r : ℝ => Real.exp (-(T*r))/r^4)).2
  have hi : IntegrableOn (fun r : ℝ => r^(d-5)*Real.exp (-(T*r))) (Ioi 0) :=
    (gamma_monomial_integrable hT (d-5)).mono_set Ioi_subset_Ici_self
  apply hi.congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  exact (radial_inverse_four_monomial hd hr.ne' T).symm

/-- Exact genuine fine-envelope scaling from the radial Gamma integral. -/
theorem euclidean_inverse_four_exponential_integral {d : ℕ} (hd : 4 < d)
    {T : ℝ} (hT : 0 < T) :
    (∫ z : EuclideanSpace ℝ (Fin d), Real.exp (-(T*‖z‖))/‖z‖^4) =
      spatialInverseFourConstant d / T^(d-4) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  rw [integral_fun_norm_addHaar volume (fun r : ℝ => Real.exp (-(T*r))/r^4)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  have he : (∫ r : ℝ in Ioi 0, r^(d-1)*(Real.exp (-(T*r))/r^4)) =
      ∫ r : ℝ in Ioi 0, r^(d-5)*Real.exp (-(T*r)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun r hr => radial_inverse_four_monomial hd hr.ne' T)
  rw [he, ← integral_Ici_eq_integral_Ioi, gamma_monomial_integral hT]
  rw [show d-5+1 = d-4 by omega]
  unfold spatialInverseFourConstant
  ring

/-- The actual finite fine alias kernel has the source complete-space squared L² bound. -/
theorem euclidean_fineAlias_squared_integrable_and_integral_le {d : ℕ} (hd : 4 < d)
    {T0 N : ℝ} (hT0 : 0 < T0) (hN : T0 ≤ N) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => (fineAliasLaplaceKernel T0 N ‖z‖)^2) volume ∧
      (∫ z : EuclideanSpace ℝ (Fin d), (fineAliasLaplaceKernel T0 N ‖z‖)^2) ≤
        6 * spatialInverseFourConstant d / T0^(d-4) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have henv := euclidean_inverse_four_exponential_integrable hd hT0
  have hm : Measurable (fun z : EuclideanSpace ℝ (Fin d) => (fineAliasLaplaceKernel T0 N ‖z‖)^2) :=
    ((fineAliasLaplaceKernel_measurable T0 N hN).comp continuous_norm.measurable).pow_const 2
  have hb : ∀ᵐ z : EuclideanSpace ℝ (Fin d) ∂volume,
      (fineAliasLaplaceKernel T0 N ‖z‖)^2 ≤ 6 * (Real.exp (-(T0*‖z‖))/‖z‖^4) := by
    filter_upwards [volume.ae_ne (0 : EuclideanSpace ℝ (Fin d))] with z hz
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hw := fineAliasLaplaceKernel_nonneg_le hr hT0.le hN
    have hp := pair_defect_exponential_absorption (T0*‖z‖) (mul_nonneg hT0.le hr.le)
    calc
      _ ≤ ((1+T0*‖z‖)*Real.exp (-(T0*‖z‖))/‖z‖^2)^2 := pow_le_pow_left₀ hw.1 hw.2 2
      _ = (1+T0*‖z‖)^2 * Real.exp (-(2*T0*‖z‖)) / ‖z‖^4 := by
        rw [div_pow, mul_pow, ← Real.exp_nat_mul,
          show (‖z‖^2)^2 = ‖z‖^4 by ring,
          show ((2 : ℕ) : ℝ) * -(T0*‖z‖) = -(2*T0*‖z‖) by ring]
      _ ≤ 6 * Real.exp (-(T0*‖z‖)) / ‖z‖^4 :=
        div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hp) (by positivity)
      _ = _ := by ring
  have hi : Integrable (fun z : EuclideanSpace ℝ (Fin d) => (fineAliasLaplaceKernel T0 N ‖z‖)^2) volume :=
    (henv.const_mul 6).mono' hm.aestronglyMeasurable (hb.mono fun z hz => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hz)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ z : EuclideanSpace ℝ (Fin d), 6 * (Real.exp (-(T0*‖z‖))/‖z‖^4) :=
      integral_mono_ae hi (henv.const_mul 6) hb
    _ = _ := by rw [integral_const_mul, euclidean_inverse_four_exponential_integral hd hT0]; ring

/-- The same genuine fine-alias squared bound in actual source coordinates and at every center. -/
theorem fineAlias_spatial_squared_integrable_and_integral_le {d : ℕ} (hd : 4 < d)
    {T0 N : ℝ} (hT0 : 0 < T0) (hN : T0 ≤ N) (x : Covariate d) :
    Integrable (fun y => (fineAliasLaplaceKernel T0 N (exactEuclideanDistance x y))^2) volume ∧
      (∫ y, (fineAliasLaplaceKernel T0 N (exactEuclideanDistance x y))^2) ≤
        6 * spatialInverseFourConstant d / T0^(d-4) := by
  have he := euclidean_fineAlias_squared_integrable_and_integral_le hd hT0 hN
  have hi := he.1
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding] at hi
  have hi0 : Integrable (fun z : Covariate d => (fineAliasLaplaceKernel T0 N ‖WithLp.toLp 2 z‖)^2) volume := by
    simpa only [Function.comp_def] using hi
  refine ⟨by simpa only [exactEuclideanDistance_eq_norm] using hi0.comp_sub_right x, ?_⟩
  simp_rw [exactEuclideanDistance_eq_norm]
  rw [integral_sub_right_eq_self (μ := volume) (fun z : Covariate d => (fineAliasLaplaceKernel T0 N ‖WithLp.toLp 2 z‖)^2)]
  exact ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding
    (fun z : EuclideanSpace ℝ (Fin d) => (fineAliasLaplaceKernel T0 N ‖z‖)^2)).trans_le he.2

end NearlyMinimax
