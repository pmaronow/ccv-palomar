module

public import NearlyMinimax.ScoreSupport
public import NearlyMinimax.ParametricConstants
public import NearlyMinimax.TernaryMeasure
public import NearlyMinimax.ModelRegularity
public import NearlyMinimax.PathRisk


@[expose] public section

/-! # The actual low-smoothness ternary prior

This file connects the finite likelihood construction to the original model.
In the order-zero regime a globally bounded Hölder regression gives an
admissible extension on every extension domain in `ModelConstants`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace NearlyMinimax

theorem ternaryMass_measurable_comp {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (y : Fin 3) :
    Measurable (fun x => ternaryMass a (F x) V y) := by
  fin_cases y <;> simp [ternaryMass] <;> fun_prop

/-- The errors have actual values `-a-f(x)`, `-f(x)`, and `a-f(x)`. -/
def ternaryErrorKernel {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) : Kernel α ℝ where
  toFun x := ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a (F x) V y) •
    Measure.dirac (ternaryValue a y - F x)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hs]
    apply Finset.measurable_sum
    intro y _
    exact (ENNReal.measurable_ofReal.comp (ternaryMass_measurable_comp a V F hF y)).mul
      (measurable_const.indicator (((measurable_const.sub hF) hs)))

theorem ternaryErrorKernel_apply {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : α) :
    ternaryErrorKernel a V F hF x = ∑ y : Fin 3,
      ENNReal.ofReal (ternaryMass a (F x) V y) •
        Measure.dirac (ternaryValue a y - F x) := rfl

theorem ternaryErrorKernel_markov {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    IsMarkovKernel (ternaryErrorKernel a V F hF) := by
  constructor
  intro x
  constructor
  simp only [ternaryErrorKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hp x y), ternary_normalized a (F x) V ha]
  simp

theorem ternary_error_integrable {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : α) (G : ℝ → ℝ) :
    Integrable G (ternaryErrorKernel a V F hF x) := by
  rw [ternaryErrorKernel_apply]
  apply integrable_finsetSum_measure.mpr
  intro y _
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem ternary_error_integral {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : α)
    (hp : ∀ y, 0 ≤ ternaryMass a (F x) V y) (G : ℝ → ℝ) :
    (∫ u, G u ∂ternaryErrorKernel a V F hF x) =
      ∑ y, ternaryMass a (F x) V y * G (ternaryValue a y - F x) := by
  rw [ternaryErrorKernel_apply, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (hp _)]
  · intro y _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem ternary_error_mean {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : α)
    (ha : a ≠ 0) (hp : ∀ y, 0 ≤ ternaryMass a (F x) V y) :
    (∫ u, u ∂ternaryErrorKernel a V F hF x) = 0 := by
  rw [ternary_error_integral a V F hF x hp]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hm := ternary_mean a (F x) V ha
  change (∑ y, ternaryMass a (F x) V y * ternaryValue a y) = F x at hm
  rw [hm, ternary_normalized a (F x) V ha]
  ring

theorem ternary_error_variance {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : α)
    (ha : a ≠ 0) (hp : ∀ y, 0 ≤ ternaryMass a (F x) V y) :
    (∫ u, u ^ 2 ∂ternaryErrorKernel a V F hF x) = V := by
  rw [ternary_error_integral a V F hF x hp]
  exact ternary_variance a (F x) V ha

theorem ternary_error_fourth {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) (x : α)
    (ha : a ≠ 0) (hp : ∀ y, 0 ≤ ternaryMass a (F x) V y) :
    (∫ u, u ^ 4 ∂ternaryErrorKernel a V F hF x) =
      a ^ 2 * V + (6 * V - 3 * a ^ 2) * (F x) ^ 2 + 3 * (F x) ^ 4 := by
  rw [ternary_error_integral a V F hF x hp]
  exact ternary_fourth_central_moment a (F x) V ha

/-- Global bounds imply the paper's exact order-zero norm bound on any domain. -/
theorem holderNorm_order_zero_of_global_bounds {d : ℕ} (U : Set (Covariate d))
    (F : Covariate d → ℝ) (α M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hsup : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |F x - F y| ≤ H * euclideanNorm (x - y) ^ α) :
    holderNorm U F 0 α ≤ ENNReal.ofReal (M + H) := by
  have hs : derivativeSup U F ≤ ENNReal.ofReal M := by
    apply iSup_le
    intro x
    exact ENNReal.ofReal_le_ofReal (hsup x)
  have hh : holderSeminorm U F α ≤ ENNReal.ofReal H := by
    apply iSup_le
    intro x
    apply iSup_le
    intro y
    by_cases hxy : (x : Covariate d) = y
    · simp [hxy]
    · simp only [ite_eq_right_iff.mpr (fun h => False.elim (hxy h))]
      apply ENNReal.ofReal_le_ofReal
      exact (div_le_iff₀ (Real.rpow_pos_of_pos
        (euclideanNorm_pos_of_ne_zero (x.val - y.val) (sub_ne_zero.mpr hxy)) α)).mpr
          (hmod x y)
  rw [holderNorm_order_zero, ENNReal.ofReal_add hM hH]
  exact add_le_add hs hh

/-- The genuine original-model parameter with uniform design and ternary errors. -/
def uniformTernaryParameter {d : ℕ} (a V : ℝ) (F : Covariate d → ℝ)
    (hF : Measurable F) (ha : a ≠ 0) (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    RegressionParameter d := {
  density := fun _ => 1
  regression := F
  variance := V
  errors := ternaryErrorKernel a V F hF
  errors_markov := ternaryErrorKernel_markov a V F hF ha hp }

/-- Order-zero legality uses global bounds, so it is independent of the
size or shape of the model's prescribed extension domain. -/
theorem uniformTernaryParameter_admissible_order_zero {d : ℕ} (C : ModelConstants d)
    (a V : ℝ) (F : Covariate d → ℝ) (hF : Continuous F) (horder : C.order = 0)
    (ha : a ≠ 0) (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (hVlo : C.varianceLower ≤ V) (hVhi : V ≤ C.varianceUpper)
    (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H) (hbudget : M + H ≤ C.holderBound)
    (hsup : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |F x - F y| ≤ H * euclideanNorm (x - y) ^ C.smoothness)
    (hfourth : ∀ x, a ^ 2 * V + (6 * V - 3 * a ^ 2) * (F x) ^ 2 +
      3 * (F x) ^ 4 ≤ C.fourthBound) :
    Admissible C (uniformTernaryParameter a V F hF.measurable ha hp) := by
  refine ⟨measurable_const, hF.measurable, ?_, ?_, ?_, hVlo, hVhi, ?_⟩
  · exact Filter.Eventually.of_forall (fun _ =>
      ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩)
  · simp only [uniformTernaryParameter, ENNReal.ofReal_one, lintegral_const, one_mul]
    exact cubeVolume_univ d
  · refine ⟨F, fun _ _ => rfl, ?_, ?_⟩
    · simpa [horder] using
        (contDiffOn_zero.mpr hF.continuousOn : ContDiffOn ℝ 0 F C.domain)
    · have hα : C.alpha = C.smoothness := by simp [ModelConstants.alpha, horder]
      rw [horder, hα]
      exact (holderNorm_order_zero_of_global_bounds C.domain F C.smoothness M H hM hH
        hsup hmod).trans (ENNReal.ofReal_le_ofReal hbudget)
  · apply Filter.Eventually.of_forall
    intro x
    refine ⟨ternary_error_integrable a V F hF.measurable x _,
      ternary_error_integrable a V F hF.measurable x _,
      ternary_error_integrable a V F hF.measurable x _,
      ternary_error_mean a V F hF.measurable x ha (hp x),
      ternary_error_variance a V F hF.measurable x ha (hp x), ?_⟩
    exact (ternary_error_fourth a V F hF.measurable x ha (hp x)).trans_le (hfourth x)

/-- Uniform interior margins for nonzero regression fields and the variance path. -/
structure LowSmoothnessTernaryConstants {d : ℕ} (C : ModelConstants d) where
  a : ℝ
  v : ℝ
  ρ : ℝ
  c : ℝ
  a_pos : 0 < a
  ρ_pos : 0 < ρ
  c_pos : 0 < c
  legal : ∀ f V, |f| ≤ ρ → |V - v| ≤ ρ →
    C.varianceLower < V ∧ V < C.varianceUpper ∧
      (∀ y, c ≤ ternaryMass a f V y) ∧
      ternaryExpectation a f V (fun y => (y - f) ^ 4) ≤ C.fourthBound

theorem lowSmoothnessTernaryConstants_exists {d : ℕ} (C : ModelConstants d) :
    Nonempty (LowSmoothnessTernaryConstants C) := by
  obtain ⟨P⟩ := parametricTernaryConstants_exists C
  let v := (P.l + P.r) / 2
  have hv : 0 < v := by dsimp [v]; linarith [P.l_pos, P.interval]
  have hVl : C.varianceLower < v := by dsimp [v]; linarith [P.lower_le, P.interval]
  have hVr : v < C.varianceUpper := by dsimp [v]; linarith [P.upper_le, P.interval]
  have hva : v < P.a ^ 2 := by dsimp [v]; linarith [P.variance_lt_square, P.interval]
  have hfourth : P.a ^ 2 * v < C.fourthBound := by
    have hmid : v < P.r := by dsimp [v]; linarith [P.interval]
    exact (mul_lt_mul_of_pos_left hmid (sq_pos_of_pos P.a_pos)).trans_le P.fourth_le
  obtain ⟨ρ, c, hρ, hc, hlegal⟩ := ternary_admissible_neighborhood P.a v
    C.varianceLower C.varianceUpper C.fourthBound P.a_pos hv hva hVl hVr hfourth
  exact ⟨⟨P.a, v, ρ, c, P.a_pos, hρ, hc, hlegal⟩⟩

namespace LowSmoothnessTernaryConstants

variable {d : ℕ} {C : ModelConstants d} (P : LowSmoothnessTernaryConstants C)

def variancePath (η t : ℝ) : ℝ := P.v - η ^ 2 * t

theorem variance_path_distance (η t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |P.variancePath η t - P.v| ≤ η ^ 2 := by
  simp only [variancePath, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg η),
    abs_of_nonneg ht.1]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 (sq_nonneg η)

theorem variance_path_separation (η : ℝ) :
    |P.variancePath η 1 - P.variancePath η 0| = η ^ 2 := by
  simp [variancePath, abs_of_nonneg (sq_nonneg η)]

theorem path_legality (η t f : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hη : η ^ 2 ≤ P.ρ) (hf : |f| ≤ P.ρ) :
    C.varianceLower < P.variancePath η t ∧ P.variancePath η t < C.varianceUpper ∧
      (∀ y, P.c ≤ ternaryMass P.a f (P.variancePath η t) y) ∧
      ternaryExpectation P.a f (P.variancePath η t) (fun y => (y - f) ^ 4) ≤ C.fourthBound :=
  P.legal f (P.variancePath η t) hf ((P.variance_path_distance η t ht).trans hη)

/-- A canonical actual-model parameter along the variance path. -/
def pathParameter (F : Covariate d → ℝ) (hF : Continuous F) (η t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hη : η ^ 2 ≤ P.ρ) (hf : ∀ x, |F x| ≤ P.ρ) :
    RegressionParameter d :=
  uniformTernaryParameter P.a (P.variancePath η t) F hF.measurable P.a_pos.ne'
    (fun x y => P.c_pos.le.trans ((P.path_legality η t (F x) ht hη (hf x)).2.2.1 y))

theorem pathParameter_regression (F : Covariate d → ℝ) (hF : Continuous F) (η t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hη : η ^ 2 ≤ P.ρ) (hf : ∀ x, |F x| ≤ P.ρ) :
    (P.pathParameter F hF η t ht hη hf).regression = F := rfl

theorem pathParameter_variance (F : Covariate d → ℝ) (hF : Continuous F) (η t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hη : η ^ 2 ≤ P.ρ) (hf : ∀ x, |F x| ≤ P.ρ) :
    (P.pathParameter F hF η t ht hη hf).variance = P.variancePath η t := rfl

theorem pathParameter_errors (F : Covariate d → ℝ) (hF : Continuous F) (η t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hη : η ^ 2 ≤ P.ρ) (hf : ∀ x, |F x| ≤ P.ρ) :
    (P.pathParameter F hF η t ht hη hf).errors =
      ternaryErrorKernel P.a (P.variancePath η t) F hF.measurable := rfl

theorem pathParameter_admissible_order_zero (F : Covariate d → ℝ) (hF : Continuous F)
    (η t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hη : η ^ 2 ≤ P.ρ) (hf : ∀ x, |F x| ≤ P.ρ)
    (horder : C.order = 0) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hbudget : M + H ≤ C.holderBound) (hsup : ∀ x, |F x| ≤ M)
    (hmod : ∀ x y, |F x - F y| ≤ H * euclideanNorm (x - y) ^ C.smoothness) :
    Admissible C (P.pathParameter F hF η t ht hη hf) := by
  have hlegal (x : Covariate d) := P.path_legality η t (F x) ht hη (hf x)
  apply uniformTernaryParameter_admissible_order_zero C P.a (P.variancePath η t) F hF horder P.a_pos.ne'
    _ (hlegal 0).1.le (hlegal 0).2.1.le M H hM hH hbudget hsup hmod
  intro x
  have hf4 := (hlegal x).2.2.2
  rw [ternary_fourth_central_moment P.a (F x) (P.variancePath η t) P.a_pos.ne'] at hf4
  exact hf4

end LowSmoothnessTernaryConstants

end NearlyMinimax
