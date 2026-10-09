module

public import NearlyMinimax.LiftL2


@[expose] public section

/-! Genuine raw multilinear kernel energy under independent unbounded L²
features, and its factorial derivative majorant. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace NearlyMinimax.KernelEnergy

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem coordinate_memLp_of_vector {n p : ℕ}
    (X : Fin n → Ω → Fin p → ℝ) (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j, MemLp (X j) 2 μ) (j : Fin n) (a : Fin p) :
    MemLp (fun ω => X j ω a) 2 μ := by
  apply (hL2 j).of_le ((measurable_pi_apply a).comp (hmeas j)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => norm_le_pi_norm (X j ω) a)

/-- Independence factors the raw product energy. Only a second moment per
feature vector is used, irrespective of the multilinear order. -/
theorem multilinear_energy_le {n p k : ℕ} (e : Fin k ↪ Fin n)
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j)) (hL2 : ∀ j, MemLp (X j) 2 μ)
    (G : ℝ) (hG : 0 ≤ G) (hsecond : ∀ j, (∫ ω, ‖X j ω‖ ^ 2 ∂μ) ≤ G) :
    (∫ ω, H (fun i => X (e i) ω) ^ 2 ∂μ) ≤ ‖H‖ ^ 2 * G ^ k := by
  have hcoord := coordinate_memLp_of_vector X hmeas hL2
  have hkernel := (LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap e X
    hind hmeas hcoord).integrable_sq
  let Y (i : Fin k) (ω : Ω) := ‖X (e i) ω‖ ^ 2
  have hi : iIndepFun Y μ :=
    (hind.precomp e.injective).comp (fun _ => fun v : Fin p → ℝ => ‖v‖ ^ 2)
      (fun _ => measurable_norm.pow_const 2)
  have hm (i : Fin k) : Measurable (Y i) := (hmeas (e i)).norm.pow_const 2
  have hp := LiftL2.independent_finset_product_integrable hi hm
    (fun i => (hL2 (e i)).norm.integrable_sq) Finset.univ
  calc
    _ ≤ ∫ ω, ‖H‖ ^ 2 * ∏ i : Fin k, ‖X (e i) ω‖ ^ 2 ∂μ := by
      apply integral_mono hkernel (hp.const_mul _)
      intro ω
      change H (fun i => X (e i) ω) ^ 2 ≤ ‖H‖ ^ 2 * ∏ i : Fin k, ‖X (e i) ω‖ ^ 2
      have hbound := pow_le_pow_left₀ (norm_nonneg _) (H.le_opNorm (fun i => X (e i) ω)) 2
      simpa only [Real.norm_eq_abs, sq_abs, mul_pow, Finset.prod_pow] using hbound
    _ = ‖H‖ ^ 2 * ∏ i : Fin k, (∫ ω, ‖X (e i) ω‖ ^ 2 ∂μ) := by
      rw [integral_const_mul]
      exact congrArg (fun t => ‖H‖ ^ 2 * t)
        (hi.integral_fun_prod_eq_prod_integral (fun i => (hm i).aestronglyMeasurable))
    _ ≤ ‖H‖ ^ 2 * G ^ k := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      simpa using Finset.prod_le_prod₀ (s := Finset.univ)
        (fun i _ => integral_nonneg (fun _ => sq_nonneg _)) (fun i _ => hsecond (e i))

/-- A degree-independent derivative cap gives exactly the factorial series
term used in U7. This bound is proved from actual feature second moments. -/
theorem factorial_raw_energy_le {n p k : ℕ} (e : Fin k ↪ Fin n)
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j)) (hL2 : ∀ j, MemLp (X j) 2 μ)
    (G : ℝ) (hG : 0 ≤ G) (hsecond : ∀ j, (∫ ω, ‖X j ω‖ ^ 2 ∂μ) ≤ G)
    (M C Λ : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C) (hΛ : 0 < Λ)
    (hderiv : ‖H‖ ≤ M * (k.factorial : ℝ) * C ^ k) :
    (((k.factorial : ℝ) * Λ ^ k)⁻¹) * (∫ ω, H (fun i => X (e i) ω) ^ 2 ∂μ) ≤
      M ^ 2 * (k.factorial : ℝ) * ((C ^ 2 * G) / Λ) ^ k := by
  have henergy := multilinear_energy_le e H X hind hmeas hL2 G hG hsecond
  have hd := pow_le_pow_left₀ (norm_nonneg H) hderiv 2
  have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
  have hΛ0 : Λ ≠ 0 := ne_of_gt hΛ
  calc
    _ ≤ (((k.factorial : ℝ) * Λ ^ k)⁻¹) *
        ((M * (k.factorial : ℝ) * C ^ k) ^ 2 * G ^ k) :=
      mul_le_mul_of_nonneg_left
        (henergy.trans (mul_le_mul_of_nonneg_right hd (pow_nonneg hG _))) (by positivity)
    _ = _ := by
      rw [div_pow, mul_pow, ← pow_mul]
      field_simp
      ring

end NearlyMinimax.KernelEnergy
