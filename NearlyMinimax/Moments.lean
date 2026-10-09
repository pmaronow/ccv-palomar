module

public import Mathlib


@[expose] public section

/-!
# Moment identities used in variance estimation

This file uses genuine Bochner expectations and mathlib variance on probability
spaces. Square integrability is explicit, so no theorem uses the default value
of the integral for a nonintegrable squared loss.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NearlyMinimax

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A centered square-integrable error has variance equal to its second moment. -/
theorem centered_variance_eq_second_moment [IsProbabilityMeasure μ]
    {ε : Ω → ℝ} (hε : MemLp ε 2 μ) (hmean : ∫ ω, ε ω ∂μ = 0) :
    variance ε μ = ∫ ω, ε ω ^ 2 ∂μ := by
  simpa [hmean] using variance_eq_sub hε

/-- The conditional second-moment identity, on a fixed conditional probability
space: an error of mean zero and second moment `V` gives `E Y² = f² + V`. -/
theorem response_second_moment_of_centered_error [IsProbabilityMeasure μ]
    {ε : Ω → ℝ} (hε : MemLp ε 2 μ) (hmean : ∫ ω, ε ω ∂μ = 0)
    {V : ℝ} (hsecond : ∫ ω, ε ω ^ 2 ∂μ = V) (f : ℝ) :
    (∫ ω, (f + ε ω) ^ 2 ∂μ) = f ^ 2 + V := by
  have hY : MemLp (fun ω => f + ε ω) 2 μ := (memLp_const f).add hε
  have hmY : (∫ ω, f + ε ω ∂μ) = f := by
    rw [integral_add (integrable_const f) (hε.integrable (by norm_num)),
      integral_const, hmean]
    simp
  have hvε : variance ε μ = V := by
    rw [centered_variance_eq_second_moment hε hmean, hsecond]
  have hvY : variance (fun ω => f + ε ω) μ = V := by
    rw [variance_const_add hε.aestronglyMeasurable f, hvε]
  have heq := variance_eq_sub hY
  change variance (fun ω => f + ε ω) μ =
    (∫ ω, (f + ε ω) ^ 2 ∂μ) - (∫ ω, f + ε ω ∂μ) ^ 2 at heq
  rw [hvY, hmY] at heq
  linarith

/-- For two independent centered errors with common variance, averaging half
of the squared response difference introduces exactly the squared mean increment. -/
theorem pair_difference_second_moment [IsProbabilityMeasure μ]
    {ε₁ ε₂ : Ω → ℝ} (h₁ : MemLp ε₁ 2 μ) (h₂ : MemLp ε₂ 2 μ)
    (hind : IndepFun ε₁ ε₂ μ)
    (hm₁ : ∫ ω, ε₁ ω ∂μ = 0) (hm₂ : ∫ ω, ε₂ ω ∂μ = 0)
    {V : ℝ} (hv₁ : ∫ ω, ε₁ ω ^ 2 ∂μ = V)
    (hv₂ : ∫ ω, ε₂ ω ^ 2 ∂μ = V) (f₁ f₂ : ℝ) :
    (∫ ω, ((f₁ + ε₁ ω) - (f₂ + ε₂ ω)) ^ 2 / 2 ∂μ) =
      V + (f₁ - f₂) ^ 2 / 2 := by
  have hdiff : MemLp (fun ω => ε₁ ω - ε₂ ω) 2 μ := h₁.sub h₂
  have hmdiff : (∫ ω, ε₁ ω - ε₂ ω ∂μ) = 0 := by
    rw [integral_sub (h₁.integrable (by norm_num)) (h₂.integrable (by norm_num)), hm₁, hm₂]
    ring
  have hvdiff : variance (fun ω => ε₁ ω - ε₂ ω) μ = 2 * V := by
    rw [variance_fun_sub h₁ h₂, hind.covariance_eq_zero h₁ h₂,
      centered_variance_eq_second_moment h₁ hm₁,
      centered_variance_eq_second_moment h₂ hm₂, hv₁, hv₂]
    ring
  have hsecdiff : (∫ ω, (ε₁ ω - ε₂ ω) ^ 2 ∂μ) = 2 * V := by
    rw [← centered_variance_eq_second_moment hdiff hmdiff]
    exact hvdiff
  have hresp := response_second_moment_of_centered_error hdiff hmdiff hsecdiff (f₁ - f₂)
  have heq : (fun ω => ((f₁ + ε₁ ω) - (f₂ + ε₂ ω)) ^ 2) =
      (fun ω => ((f₁ - f₂) + (ε₁ ω - ε₂ ω)) ^ 2) := by
    funext ω
    congr 1
    ring
  rw [integral_div, heq, hresp]
  ring

/-- The fourth-moment Jensen inequality. The `MemLp` hypothesis on the square
is exactly square integrability of the second-moment random variable. -/
theorem second_moment_sq_le_fourth_moment [IsProbabilityMeasure μ]
    {ε : Ω → ℝ} (hεsq : MemLp (fun ω => ε ω ^ 2) 2 μ) :
    (∫ ω, ε ω ^ 2 ∂μ) ^ 2 ≤ ∫ ω, ε ω ^ 4 ∂μ := by
  have hn := variance_nonneg (fun ω => ε ω ^ 2) μ
  rw [variance_eq_sub hεsq] at hn
  have heq : (fun ω => (ε ω ^ 2) ^ 2) = (fun ω => ε ω ^ 4) := by
    funext ω
    ring
  change 0 ≤ (∫ ω, (ε ω ^ 2) ^ 2 ∂μ) - (∫ ω, ε ω ^ 2 ∂μ) ^ 2 at hn
  rw [heq] at hn
  linarith

/-- Constant conditional variance is bounded by the square root of the fourth-
moment bound, in its algebraic squared form. -/
theorem variance_sq_le_fourth_bound [IsProbabilityMeasure μ]
    {ε : Ω → ℝ} (hεsq : MemLp (fun ω => ε ω ^ 2) 2 μ)
    {V C₄ : ℝ} (hv : ∫ ω, ε ω ^ 2 ∂μ = V)
    (hfourth : ∫ ω, ε ω ^ 4 ∂μ ≤ C₄) : V ^ 2 ≤ C₄ := by
  have h := second_moment_sq_le_fourth_moment hεsq
  rw [hv] at h
  exact h.trans hfourth

/-- A fourth-integrable error has a square-integrable square. -/
theorem square_memLp_two_of_memLp_four {ε : Ω → ℝ} (hε : MemLp ε 4 μ) :
    MemLp (fun ω => ε ω ^ 2) 2 μ := by
  apply (memLp_two_iff_integrable_sq (hε.aestronglyMeasurable.pow 2)).2
  have hfourth : Integrable (fun ω => ε ω ^ 4) μ := by
    simpa [show ∀ a : ℝ, |a| ^ 4 = a ^ 4 from fun a => by
      calc |a| ^ 4 = (|a| ^ 2) ^ 2 := by ring
           _ = (a ^ 2) ^ 2 := by rw [sq_abs]
           _ = a ^ 4 := by ring] using
      hε.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  convert hfourth using 1
  funext ω
  change (ε ω ^ 2) ^ 2 = ε ω ^ 4
  ring

/-- Fourth-moment Jensen directly from the usual `L⁴` moment hypothesis. -/
theorem variance_sq_le_fourth_bound_of_memLp_four [IsProbabilityMeasure μ]
    {ε : Ω → ℝ} (hε : MemLp ε 4 μ)
    {V C₄ : ℝ} (hv : ∫ ω, ε ω ^ 2 ∂μ = V)
    (hfourth : ∫ ω, ε ω ^ 4 ∂μ ≤ C₄) : V ^ 2 ≤ C₄ :=
  variance_sq_le_fourth_bound (square_memLp_two_of_memLp_four hε) hv hfourth

/-- The empirical average of a finite sample of real random variables. -/
def empiricalMean {n : ℕ} (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => (n : ℝ)⁻¹ * ∑ i, X i ω

/-- The empirical average is unbiased when each observation has mean `m`. -/
theorem empiricalMean_expectation [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Integrable (X i) μ) {m : ℝ}
    (hm : ∀ i, ∫ ω, X i ω ∂μ = m) :
    (∫ ω, empiricalMean X ω ∂μ) = m := by
  simp only [empiricalMean, integral_const_mul]
  rw [integral_finset_sum Finset.univ (fun i _ => hX i)]
  simp only [hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- Square integrability of the empirical average. -/
theorem empiricalMean_memLp_two [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) :
    MemLp (empiricalMean X) 2 μ := by
  exact (memLp_finset_sum Finset.univ (fun i _ => hX i)).const_mul (n : ℝ)⁻¹

/-- The exact `variance / n` formula for an independent, common-variance sample.
Only pairwise independence is needed by the variance calculation. -/
theorem empiricalMean_variance [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (hind : iIndepFun X μ)
    {σ2 : ℝ} (hvar : ∀ i, variance (X i) μ = σ2) :
    variance (empiricalMean X) μ = σ2 / (n : ℝ) := by
  unfold empiricalMean
  rw [variance_const_mul]
  have hs : variance (∑ i, X i) μ = ∑ i, variance (X i) μ :=
    IndepFun.variance_sum (fun i _ => hX i)
      (fun _ _ _ _ hij => hind.indepFun hij)
  have hsum : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
    funext ω
    simp
  have hs' : variance (fun ω => ∑ i, X i ω) μ = ∑ i, variance (X i) μ := by
    rw [hsum]
    exact hs
  rw [hs']
  simp only [hvar, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- Exact mean squared error, and thus the root-`n` stochastic term, of an
independent unbiased empirical average. -/
theorem empiricalMean_mse [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (hind : iIndepFun X μ)
    {m σ2 : ℝ} (hm : ∀ i, ∫ ω, X i ω ∂μ = m)
    (hvar : ∀ i, variance (X i) μ = σ2) :
    (∫ ω, (empiricalMean X ω - m) ^ 2 ∂μ) = σ2 / (n : ℝ) := by
  have hmean := empiricalMean_expectation hn
    (fun i => (hX i).integrable (by norm_num)) hm
  have hmem := empiricalMean_memLp_two hX
  have h := variance_eq_integral hmem.aemeasurable
  rw [hmean] at h
  rw [← h, empiricalMean_variance hn hX hind hvar]

/-- The unconditional regression second-moment decomposition once the
conditional mean-zero error gives orthogonality to the regression function. -/
theorem response_second_moment_of_orthogonality [IsProbabilityMeasure μ]
    {F ε : Ω → ℝ} (hF : MemLp F 2 μ) (hε : MemLp ε 2 μ)
    (horth : ∫ ω, F ω * ε ω ∂μ = 0)
    {V : ℝ} (hsecond : ∫ ω, ε ω ^ 2 ∂μ = V) :
    (∫ ω, (F ω + ε ω) ^ 2 ∂μ) = (∫ ω, F ω ^ 2 ∂μ) + V := by
  have hmul : Integrable (fun ω => F ω * ε ω) μ := by
    convert hF.integrable_mul hε using 1
  have hsum : Integrable (fun ω => F ω ^ 2 + 2 * (F ω * ε ω)) μ :=
    hF.integrable_sq.add (hmul.const_mul 2)
  calc
    _ = ∫ ω, (F ω ^ 2 + 2 * (F ω * ε ω)) + ε ω ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by ring)
    _ = ((∫ ω, F ω ^ 2 ∂μ) + 2 * (∫ ω, F ω * ε ω ∂μ)) +
          (∫ ω, ε ω ^ 2 ∂μ) := by
      rw [integral_add hsum hε.integrable_sq,
        integral_add hF.integrable_sq (hmul.const_mul 2), integral_const_mul]
    _ = (∫ ω, F ω ^ 2 ∂μ) + V := by rw [horth, hsecond]; ring

/-- Equation `eq:variance-quadratic-identity` with the regression second
moment written as an expectation on the observation probability space. -/
theorem variance_quadratic_identity [IsProbabilityMeasure μ]
    {F ε : Ω → ℝ} (hF : MemLp F 2 μ) (hε : MemLp ε 2 μ)
    (horth : ∫ ω, F ω * ε ω ∂μ = 0)
    {V : ℝ} (hsecond : ∫ ω, ε ω ^ 2 ∂μ = V) :
    V = (∫ ω, (F ω + ε ω) ^ 2 ∂μ) - (∫ ω, F ω ^ 2 ∂μ) := by
  rw [response_second_moment_of_orthogonality hF hε horth hsecond]
  ring

/-- An explicit root mean squared error formula for a finite independent sample. -/
theorem empiricalMean_rmse [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (hind : iIndepFun X μ)
    {m σ2 : ℝ} (hm : ∀ i, ∫ ω, X i ω ∂μ = m)
    (hvar : ∀ i, variance (X i) μ = σ2) :
    Real.sqrt (∫ ω, (empiricalMean X ω - m) ^ 2 ∂μ) =
      Real.sqrt σ2 / Real.sqrt (n : ℝ) := by
  have hσ : 0 ≤ σ2 := by
    rw [← hvar ⟨0, hn⟩]
    exact variance_nonneg _ _
  rw [empiricalMean_mse hn hX hind hm hvar, Real.sqrt_div hσ]

end NearlyMinimax
