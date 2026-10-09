module

public import NearlyMinimax.LowSmoothnessPrior


@[expose] public section

/-! Raw-density normalization for the manuscript's high-smoothness prior.
The mass-concentration guard is a scalar event; density normalization and
original density bounds are consequences proved here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem high_raw_mass_lower {d : ℕ} (C : ModelConstants d) (M cm m : ℝ)
    (hM : 2 ≤ M) (hcm : 0 ≤ cm) (hcmU : cm ≤ 1 / C.densityUpper)
    (hm : |m - 1| ≤ cm / M) : 1 / 2 ≤ m := by
  have hU : 0 < C.densityUpper := lt_trans (by norm_num) C.one_lt_densityUpper
  have hcm1 : cm ≤ 1 := by
    apply hcmU.trans
    exact (div_le_one hU).mpr C.one_lt_densityUpper.le
  have hM0 : 0 < M := by linarith
  have hhalf : cm / M ≤ 1 / 2 := by
    apply (div_le_iff₀ hM0).mpr
    nlinarith
  have := (abs_le.mp hm).1
  linarith

theorem high_normalized_density_interval {d : ℕ} (C : ModelConstants d)
    (M cm m p : ℝ) (hM : 2 ≤ M) (hcm : 0 ≤ cm)
    (hcmU : cm ≤ 1 / C.densityUpper) (hm : |m - 1| ≤ cm / M)
    (hp : C.densityLower + 1 / M ≤ p ∧ p ≤ C.densityUpper - 1 / M) :
    C.densityLower ≤ p / m ∧ p / m ≤ C.densityUpper := by
  have hU : 0 < C.densityUpper := lt_trans (by norm_num) C.one_lt_densityUpper
  have hM0 : 0 < M := by linarith
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) (high_raw_mass_lower C M cm m hM hcm hcmU hm)
  have hcmprod : C.densityUpper * cm ≤ 1 := by
    have h := (le_div_iff₀ hU).mp hcmU
    nlinarith
  have hLcm : C.densityLower * cm ≤ 1 := by
    have hLU : C.densityLower ≤ C.densityUpper :=
      C.densityLower_lt_one.le.trans C.one_lt_densityUpper.le
    exact (mul_le_mul_of_nonneg_right hLU hcm).trans hcmprod
  have hmass := abs_le.mp hm
  have hmulU : C.densityUpper * (cm / M) ≤ 1 / M := by
    have h := div_le_div_of_nonneg_right hcmprod hM0.le
    simpa only [mul_div_assoc, one_div] using h
  have hmulL : C.densityLower * (cm / M) ≤ 1 / M := by
    have h := div_le_div_of_nonneg_right hLcm hM0.le
    simpa only [mul_div_assoc, one_div] using h
  constructor
  · apply (le_div_iff₀ hm0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmass.2 C.densityLower_pos.le]
  · apply (div_le_iff₀ hm0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmass.1 hU.le]

def highRawDensityMass {d : ℕ} (p : Covariate d → ℝ) : ℝ :=
  ∫ x, p x ∂cubeVolume d

def highNormalizedDensity {d : ℕ} (p : Covariate d → ℝ) (x : Covariate d) : ℝ :=
  p x / highRawDensityMass p

theorem highNormalizedDensity_measurable {d : ℕ} (p : Covariate d → ℝ)
    (hp : Measurable p) : Measurable (highNormalizedDensity p) := hp.div_const _

theorem highRawDensity_integrable {d : ℕ} (C : ModelConstants d) (M : ℝ)
    (hM : 0 < M) (p : Covariate d → ℝ) (hp : Measurable p)
    (hb : ∀ᵐ x ∂cubeVolume d,
      C.densityLower + 1 / M ≤ p x ∧ p x ≤ C.densityUpper - 1 / M) :
    Integrable p (cubeVolume d) := by
  have hfin : IsFiniteMeasure (cubeVolume d) := by
    constructor
    rw [cubeVolume_univ]
    exact ENNReal.one_lt_top
  have hbound : ∀ᵐ x ∂cubeVolume d, ‖p x‖ ≤ C.densityUpper := by
    filter_upwards [hb] with x hx
    have hp0 : 0 ≤ p x := by linarith [C.densityLower_pos, one_div_pos.mpr hM]
    rw [Real.norm_eq_abs, abs_of_nonneg hp0]
    linarith [one_div_pos.mpr hM]
  exact (integrable_const C.densityUpper).mono' hp.aestronglyMeasurable hbound

theorem highNormalizedDensity_normalized {d : ℕ} (p : Covariate d → ℝ)
    (hp : Integrable p (cubeVolume d)) (hp0 : 0 ≤ᵐ[cubeVolume d] p)
    (hm : 0 < highRawDensityMass p) :
    (∫⁻ x, ENNReal.ofReal (highNormalizedDensity p x) ∂cubeVolume d) = 1 := by
  unfold highNormalizedDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (hp.div_const _) (hp0.mono
    (fun x hx => div_nonneg hx hm.le))]
  rw [integral_div]
  change ENNReal.ofReal (highRawDensityMass p / highRawDensityMass p) = 1
  simp only [div_self hm.ne', ENNReal.ofReal_one]

theorem highNormalizedDensity_bounds {d : ℕ} (C : ModelConstants d) (M cm : ℝ)
    (hM : 2 ≤ M) (hcm : 0 ≤ cm) (hcmU : cm ≤ 1 / C.densityUpper)
    (p : Covariate d → ℝ)
    (hb : ∀ᵐ x ∂cubeVolume d,
      C.densityLower + 1 / M ≤ p x ∧ p x ≤ C.densityUpper - 1 / M)
    (hm : |highRawDensityMass p - 1| ≤ cm / M) :
    ∀ᵐ x ∂cubeVolume d,
      C.densityLower ≤ highNormalizedDensity p x ∧
        highNormalizedDensity p x ≤ C.densityUpper := by
  filter_upwards [hb] with x hx
  exact high_normalized_density_interval C M cm (highRawDensityMass p) (p x)
    hM hcm hcmU hm hx

/-- Actual ternary regression model with a normalized, nonuniform design. -/
def normalizedDensityTernaryParameter {d : ℕ} (p F : Covariate d → ℝ)
    (a V : ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) : RegressionParameter d where
  density := highNormalizedDensity p
  regression := F
  variance := V
  errors := ternaryErrorKernel a V F hF
  errors_markov := ternaryErrorKernel_markov a V F hF ha hp

/-- Pointwise mixed-derivative and Euclidean modulus bounds imply the
original sum-over-distinct-multi-indices norm on any extension domain. -/
theorem holderNorm_of_global_mixed_bounds {d : ℕ} (U : Set (Covariate d))
    (F : Covariate d → ℝ) (ℓ : ℕ) (α B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hsup : ∀ γ : Fin d → Fin (ℓ + 1), (∑ i, (γ i).val) ≤ ℓ →
      ∀ x, |multiPartial F (fun i => (γ i).val) x| ≤ B)
    (hmod : ∀ γ : Fin d → Fin (ℓ + 1), (∑ i, (γ i).val) = ℓ → ∀ x y,
      |multiPartial F (fun i => (γ i).val) x - multiPartial F (fun i => (γ i).val) y| ≤
        L * euclideanNorm (x - y) ^ α) :
    holderNorm U F ℓ α ≤ ENNReal.ofReal (((ℓ + 1 : ℕ) : ℝ) ^ d * B + L) := by
  have hs (γ : Fin d → Fin (ℓ + 1)) (hγ : (∑ i, (γ i).val) ≤ ℓ) :
      derivativeSup U (multiPartial F (fun i => (γ i).val)) ≤ ENNReal.ofReal B := by
    apply iSup_le
    intro x
    exact ENNReal.ofReal_le_ofReal (hsup γ hγ x)
  have hh (γ : Fin d → Fin (ℓ + 1)) (hγ : (∑ i, (γ i).val) = ℓ) :
      holderSeminorm U (multiPartial F (fun i => (γ i).val)) α ≤ ENNReal.ofReal L := by
    apply iSup_le
    intro x
    apply iSup_le
    intro y
    by_cases hxy : (x : Covariate d) = y
    · simp [hxy]
    · simp only [ite_eq_right_iff.mpr (fun h => False.elim (hxy h))]
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (Real.rpow_pos_of_pos
        (euclideanNorm_pos_of_ne_zero (x.val - y.val) (sub_ne_zero.mpr hxy)) α)).mpr
      exact hmod γ hγ x y
  have hsum : (∑ γ : Fin d → Fin (ℓ + 1),
      if (∑ i, (γ i).val) ≤ ℓ then
        derivativeSup U (multiPartial F (fun i => (γ i).val)) else 0) ≤
      ENNReal.ofReal (((ℓ + 1 : ℕ) : ℝ) ^ d * B) := by
    calc
      _ ≤ ∑ _γ : Fin d → Fin (ℓ + 1), ENNReal.ofReal B := by
        apply Finset.sum_le_sum
        intro γ hγ
        split_ifs with h
        · exact hs γ h
        · exact bot_le
      _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hB)]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  have hsem : (⨆ γ : Fin d → Fin (ℓ + 1), if (∑ i, (γ i).val) = ℓ then
      holderSeminorm U (multiPartial F (fun i => (γ i).val)) α else 0) ≤ ENNReal.ofReal L := by
    apply iSup_le
    intro γ
    split_ifs with h
    · exact hh γ h
    · exact bot_le
  unfold holderNorm
  rw [ENNReal.ofReal_add (mul_nonneg (by positivity) hB) hL]
  exact add_le_add hsum hsem

/-- Original-model legality after the actual raw-density normalization.
The norm estimate is derived from explicit mixed-partial bounds above;
the error kernel has its genuine first, second and fourth moments. -/
theorem normalizedDensityTernaryParameter_admissible {d : ℕ} (C : ModelConstants d)
    (M cm : ℝ) (hM : 2 ≤ M) (hcm : 0 ≤ cm) (hcmU : cm ≤ 1 / C.densityUpper)
    (p F : Covariate d → ℝ) (hp : Measurable p) (hF : ContDiff ℝ ∞ F)
    (hraw : ∀ᵐ x ∂cubeVolume d,
      C.densityLower + 1 / M ≤ p x ∧ p x ≤ C.densityUpper - 1 / M)
    (hmass : |highRawDensityMass p - 1| ≤ cm / M)
    (a V : ℝ) (ha : a ≠ 0) (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (hVlo : C.varianceLower ≤ V) (hVhi : V ≤ C.varianceUpper)
    (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hbudget : ((C.order + 1 : ℕ) : ℝ) ^ d * B + L ≤ C.holderBound)
    (hsup : ∀ γ : Fin d → Fin (C.order + 1), (∑ i, (γ i).val) ≤ C.order →
      ∀ x, |multiPartial F (fun i => (γ i).val) x| ≤ B)
    (hmod : ∀ γ : Fin d → Fin (C.order + 1), (∑ i, (γ i).val) = C.order → ∀ x y,
      |multiPartial F (fun i => (γ i).val) x - multiPartial F (fun i => (γ i).val) y| ≤
        L * euclideanNorm (x - y) ^ C.alpha)
    (hfourth : ∀ x, a ^ 2 * V + (6 * V - 3 * a ^ 2) * (F x) ^ 2 +
      3 * (F x) ^ 4 ≤ C.fourthBound) :
    Admissible C (normalizedDensityTernaryParameter p F a V hF.continuous.measurable ha hq) := by
  have hM0 : 0 < M := by linarith
  have hint := highRawDensity_integrable C M hM0 p hp hraw
  have hp0 : 0 ≤ᵐ[cubeVolume d] p := by
    filter_upwards [hraw] with x hx
    change 0 ≤ p x
    linarith [C.densityLower_pos, one_div_pos.mpr hM0]
  have hmass0 : 0 < highRawDensityMass p := lt_of_lt_of_le (by norm_num)
    (high_raw_mass_lower C M cm (highRawDensityMass p) hM hcm hcmU hmass)
  refine ⟨highNormalizedDensity_measurable p hp, hF.continuous.measurable,
    highNormalizedDensity_bounds C M cm hM hcm hcmU p hraw hmass,
    highNormalizedDensity_normalized p hint hp0 hmass0, ?_, hVlo, hVhi, ?_⟩
  · refine ⟨F, fun _ _ => rfl, (hF.of_le (by simp)).contDiffOn, ?_⟩
    exact (holderNorm_of_global_mixed_bounds C.domain F C.order C.alpha B L hB hL
      hsup hmod).trans (ENNReal.ofReal_le_ofReal hbudget)
  · apply Filter.Eventually.of_forall
    intro x
    refine ⟨ternary_error_integrable a V F hF.continuous.measurable x _,
      ternary_error_integrable a V F hF.continuous.measurable x _,
      ternary_error_integrable a V F hF.continuous.measurable x _,
      ternary_error_mean a V F hF.continuous.measurable x ha (hq x),
      ternary_error_variance a V F hF.continuous.measurable x ha (hq x), ?_⟩
    exact (ternary_error_fourth a V F hF.continuous.measurable x ha (hq x)).trans_le (hfourth x)

end NearlyMinimax
