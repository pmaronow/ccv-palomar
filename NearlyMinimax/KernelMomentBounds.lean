module

public import NearlyMinimax.LiftL2


@[expose] public section

/-! Raw multilinear kernel moment bounds under genuine independent L²
observations. Increasing lift order requires no higher response moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace NearlyMinimax.KernelMomentBounds

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem pi_norm_sq_le_sum_sq {p : ℕ} (v : Fin p → ℝ) : ‖v‖ ^ 2 ≤ ∑ a, (v a) ^ 2 := by
  have hS : 0 ≤ ∑ a : Fin p, (v a) ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hn : ‖v‖ ≤ Real.sqrt (∑ a : Fin p, (v a) ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro a
    have hs := Finset.single_le_sum (fun a _ => sq_nonneg (v a)) (Finset.mem_univ a)
    simpa only [Real.norm_eq_abs, Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hs
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hS)

/-- Coordinatewise L² gives genuine vector L² and a sharp dimension-free
comparison with the sum of coordinate energies. -/
theorem vector_memLp_two {p : ℕ} (X : Ω → Fin p → ℝ) (hm : Measurable X)
    (hL2 : ∀ a, MemLp (fun ω => X ω a) 2 μ) : MemLp X 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hi := integrable_finsetSum Finset.univ (fun a _ => (hL2 a).integrable_sq)
  apply hi.mono' (hm.norm.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pi_norm_sq_le_sum_sq (X ω)

theorem vector_second_le_sum_coordinates {p : ℕ} (X : Ω → Fin p → ℝ) (hm : Measurable X)
    (hL2 : ∀ a, MemLp (fun ω => X ω a) 2 μ) :
    (∫ ω, ‖X ω‖ ^ 2 ∂μ) ≤ ∑ a, ∫ ω, X ω a ^ 2 ∂μ := by
  have hi := (vector_memLp_two X hm hL2).norm.integrable_sq
  have hsum := integrable_finsetSum Finset.univ (fun a _ => (hL2 a).integrable_sq)
  have h := integral_mono hi hsum (fun ω => pi_norm_sq_le_sum_sq (X ω))
  rwa [integral_finsetSum _ (fun a _ => (hL2 a).integrable_sq)] at h

/-- Independence makes the raw order-k kernel energy at most its squared
operator norm times the k-th power of a single-observation energy cap. -/
theorem multilinear_second_le {p k : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ)
    (X : Fin k → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (hL2 : ∀ i a, MemLp (fun ω => X i ω a) 2 μ)
    (E : ℝ) (hE : 0 ≤ E) (henergy : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂μ) ≤ E) :
    (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) ≤ ‖H‖ ^ 2 * E ^ k := by
  classical
  have hnorm (i : Fin k) := (vector_memLp_two (X i) (hm i) (hL2 i)).norm
  have hind' : iIndepFun (fun i ω => ‖X i ω‖ ^ 2) μ :=
    hind.comp (fun _ => fun v : Fin p → ℝ => ‖v‖ ^ 2)
      (fun _ => measurable_norm.pow_const 2)
  have hmeas' (i : Fin k) : Measurable (fun ω => ‖X i ω‖ ^ 2) := (hm i).norm.pow_const 2
  have hd := LiftL2.independent_finset_product_integrable hind' hmeas'
    (fun i => (hnorm i).integrable_sq) Finset.univ
  have hraw := (LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap
    (Function.Embedding.refl (Fin k)) X hind hm hL2).integrable_sq
  have hcomp : (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) ≤
      ‖H‖ ^ 2 * ∫ ω, ∏ i : Fin k, ‖X i ω‖ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hraw (hd.const_mul (‖H‖ ^ 2))
    intro ω
    change H (fun i => X i ω) ^ 2 ≤ ‖H‖ ^ 2 * ∏ i : Fin k, ‖X i ω‖ ^ 2
    simpa only [Real.norm_eq_abs, sq_abs, mul_pow, Finset.prod_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (H.le_opNorm (fun i => X i ω)) 2
  have heq := hind'.integral_fun_prod_eq_prod_integral (fun i => (hmeas' i).aestronglyMeasurable)
  rw [heq] at hcomp
  apply hcomp.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ ∏ _i : Fin k, E := Finset.prod_le_prod₀
      (fun i _ => integral_nonneg (fun _ => sq_nonneg _)) (fun i _ => henergy i)
    _ = E ^ k := by simp

/-- A factorial derivative cap produces the precise factorial power series
used in the pilot budget, proved from actual independent feature moments. -/
theorem factorial_kernel_budget {p k : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ)
    (X : Fin k → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (hL2 : ∀ i a, MemLp (fun ω => X i ω a) 2 μ)
    (E a c Λ : ℝ) (hE : 0 ≤ E) (ha : 0 ≤ a) (hc : 0 ≤ c) (hΛ : 0 < Λ)
    (henergy : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂μ) ≤ E)
    (hderiv : ‖H‖ ≤ a * (k.factorial : ℝ) * c ^ k) :
    (((k.factorial : ℝ) * Λ ^ k)⁻¹) * (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) ≤
      a ^ 2 * (k.factorial : ℝ) * (c ^ 2 * E / Λ) ^ k := by
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have he := multilinear_second_le H X hind hm hL2 E hE henergy
  have hd := pow_le_pow_left₀ (norm_nonneg _) hderiv 2
  have h := mul_le_mul_of_nonneg_left
    (he.trans (mul_le_mul_of_nonneg_right hd (pow_nonneg hE k)))
    (show 0 ≤ ((k.factorial : ℝ) * Λ ^ k)⁻¹ by positivity)
  apply h.trans_eq
  simp only [div_pow, mul_pow, pow_mul, Nat.mul_comm]
  field_simp [ne_of_gt hfac, ne_of_gt hΛ] <;> ring

end NearlyMinimax.KernelMomentBounds
