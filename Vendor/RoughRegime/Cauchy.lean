module

public import Mathlib


@[expose] public section

/-!
Cauchy bounds needed for Lemma 5(c). No bounds on derivatives are assumed.
The bounds follow from the function's holomorphicity and its supremum bound.
-/
noncomputable section
open Complex Metric
namespace RoughRegime.Cauchy

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A Banach-valued first derivative Cauchy estimate obtained on complex lines. -/
theorem norm_fderiv_le_div (f : E → F) (hf : Differentiable ℂ f)
    (x : E) (R A : ℝ) (hR : 0 < R)
    (hbound : ∀ y ∈ closedBall x R, ‖f y‖ ≤ A) :
    ‖fderiv ℂ f x‖ ≤ A / R := by
  have hA : 0 ≤ A := (norm_nonneg (f x)).trans (hbound x (mem_closedBall_self hR.le))
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hA hR.le)
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let g : ℂ → F := fun z => f (x + z • v)
  have hg : Differentiable ℂ g := by
    exact hf.comp ((differentiable_const x).add (differentiable_id.smul_const v))
  have hd : deriv g 0 = (fderiv ℂ f x) v := by
    have hline : HasDerivAt (fun z : ℂ => x + z • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
    have hfx : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by
      simpa using (hf x).hasFDerivAt
    have hh := hfx.comp_hasDerivAt 0 hline
    simpa [g, Function.comp_def] using hh.deriv
  have hc : ‖deriv g 0‖ ≤ A / (R / ‖v‖) := by
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos hR hvpos) hg.diffContOnCl
    intro z hz
    apply hbound
    rw [mem_closedBall, dist_eq_norm]
    change ‖x + z • v - x‖ ≤ R
    rw [add_sub_cancel_left, norm_smul]
    have hz' : ‖z‖ = R / ‖v‖ := by simpa [mem_sphere, dist_eq_norm] using hz
    rw [hz']
    exact le_of_eq (div_mul_cancel₀ R (ne_of_gt hvpos))
  rw [hd] at hc
  convert hc using 1
  field_simp

/-- Iterating the first derivative estimate on equal-width nested balls. -/
theorem iteratedFDeriv_closedBall_aux {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (n : ℕ) (f : E → F) (hf : AnalyticOnNhd ℂ f Set.univ)
    (x : E) (δ A : ℝ) (hδ : 0 < δ)
    (hbound : ∀ y ∈ closedBall x ((n : ℝ) * δ), ‖f y‖ ≤ A) :
    ‖iteratedFDeriv ℂ n f x‖ ≤ A / δ ^ n := by
  induction n generalizing F A with
  | zero =>
    simp only [norm_iteratedFDeriv_zero, pow_zero, div_one]
    apply hbound
    simp
  | succ n ih =>
    have hdiff : Differentiable ℂ f := fun y => (hf y (Set.mem_univ y)).differentiableAt
    have hgbound : ∀ y ∈ closedBall x ((n : ℝ) * δ), ‖fderiv ℂ f y‖ ≤ A / δ := by
      intro y hy
      apply norm_fderiv_le_div f hdiff y δ A hδ
      intro z hz
      apply hbound
      rw [mem_closedBall] at *
      have htri := dist_triangle z y x
      push_cast
      linarith
    have h := ih (A := A / δ) (fderiv ℂ f) hf.fderiv hgbound
    rw [norm_iteratedFDeriv_fderiv] at h
    convert h using 1
    rw [pow_succ]
    field_simp

/-- The degree-independent norm estimate on an open ball, before the factorial comparison. -/
theorem iteratedFDeriv_openBall {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (n : ℕ) (hn : 0 < n) (f : E → F) (hf : AnalyticOnNhd ℂ f Set.univ)
    (x : E) (ε A : ℝ) (hε : 0 < ε)
    (hbound : ∀ y ∈ ball x ε, ‖f y‖ ≤ A) :
    ‖iteratedFDeriv ℂ n f x‖ ≤ A * ((n : ℝ) / ε) ^ n := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hinner (R : ℝ) (hR : 0 < R) (hRε : R < ε) :
      ‖iteratedFDeriv ℂ n f x‖ ≤ A * ((n : ℝ) / R) ^ n := by
    have hδ : 0 < R / (n : ℝ) := div_pos hR hnreal
    have h := iteratedFDeriv_closedBall_aux n f hf x (R / n) A hδ (by
      intro y hy
      apply hbound
      rw [mem_closedBall] at hy
      rw [mem_ball]
      have heq : (n : ℝ) * (R / n) = R := by field_simp
      rw [heq] at hy
      exact hy.trans_lt hRε)
    convert h using 1
    simp_rw [div_pow]
    field_simp
  have hc : ContinuousAt (fun R : ℝ => A * ((n : ℝ) / R) ^ n) ε := by
    fun_prop (disch := positivity)
  have hl : Filter.Tendsto (fun R : ℝ => A * ((n : ℝ) / R) ^ n)
      (nhdsWithin ε (Set.Iio ε)) (nhds (A * ((n : ℝ) / ε) ^ n)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hl
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hε),
    (self_mem_nhdsWithin : Set.Iio ε ∈ nhdsWithin ε (Set.Iio ε))] with R hR hRε
  exact hinner R hR hRε

/-- The elementary factorial comparison used in Lemma 5(c). -/
lemma pow_le_factorial_exp (n : ℕ) :
    (n : ℝ) ^ n ≤ (n.factorial : ℝ) * Real.exp 1 ^ n := by
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n)
  have he : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    simpa using Real.exp_nat_mul 1 n
  rw [he] at h
  simpa [mul_comm] using h

/-- Lemma 5(c) for arbitrary entire analytic maps of complex normed spaces. -/
theorem iteratedFDeriv_direction_bound {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (n : ℕ) (hn : 0 < n) (f : E → F) (hf : AnalyticOnNhd ℂ f Set.univ)
    (x : E) (ε A : ℝ) (hε : 0 < ε)
    (hbound : ∀ y ∈ ball x ε, ‖f y‖ ≤ A) (v : Fin n → E) :
    ‖iteratedFDeriv ℂ n f x v‖ ≤
      A * (n.factorial : ℝ) * (Real.exp 1 / ε) ^ n * ∏ i, ‖v i‖ := by
  have hA : 0 ≤ A := (norm_nonneg (f x)).trans (hbound x (mem_ball_self hε))
  have hnorm := iteratedFDeriv_openBall n hn f hf x ε A hε hbound
  have hfactor : A * ((n : ℝ) / ε) ^ n ≤
      A * (n.factorial : ℝ) * (Real.exp 1 / ε) ^ n := by
    have h := mul_le_mul_of_nonneg_left (pow_le_factorial_exp n)
      (div_nonneg hA (pow_nonneg hε.le n))
    convert h using 1 <;> rw [div_pow] <;> ring
  exact (ContinuousMultilinearMap.le_opNorm _ v).trans
    (mul_le_mul_of_nonneg_right (hnorm.trans hfactor) (Finset.prod_nonneg (fun i _ => norm_nonneg _)))

/-- Full polynomial statement of Lemma 5(c). The norm on `Fin p → ℂ` is its coordinate
supremum norm, and complex directions include the real directions in the manuscript. -/
theorem polynomial_derivative_bound {p : ℕ} (P : MvPolynomial (Fin p) ℂ)
    (x : Fin p → ℂ) (ε A : ℝ) (hε : 0 < ε)
    (hbound : ∀ y : Fin p → ℂ, ‖y - x‖ < ε → ‖MvPolynomial.eval y P‖ ≤ A)
    (n : ℕ) (hn : 0 < n) (v : Fin n → (Fin p → ℂ)) :
    ‖iteratedFDeriv ℂ n (fun y => MvPolynomial.eval y P) x v‖ ≤
      A * (n.factorial : ℝ) * (Real.exp 1 / ε) ^ n * ∏ i, ‖v i‖ := by
  apply iteratedFDeriv_direction_bound n hn _ (AnalyticOnNhd.eval_mvPolynomial P) x ε A hε
  intro y hy
  exact hbound y (by simpa [mem_ball, dist_eq_norm] using hy)

end RoughRegime.Cauchy
