module

public import NearlyMinimax.PaperSharpUpper
public import NearlyMinimax.PaperParametric


@[expose] public section

/-! The elementary high-smoothness estimator bound for every sample size,
obtained from the proved sharp construction and an explicit small-sample
constant statistic. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem eventually_paperUpperScale_le_plain {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    ∀ᶠ n : ℕ in atTop, paperUpperScale C n ≤ (n : ℝ) ^ (-rateExponent C.smoothness d) := by
  have ht := (tendsto_stretched_log_factor (paper_stretchConstant_pos C hreg)
    (lowerLogPower C.smoothness d + paperLogGap C)).comp tendsto_natCast_atTop_atTop
  have he := ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [paperUpperScale_eq_rateScale C hn2, rateScale_eq_base_mul_correction]
  calc
    _ ≤ Real.exp (-rateExponent C.smoothness d * Real.log n) * 1 :=
      mul_le_mul_of_nonneg_left hn.le (Real.exp_pos _).le
    _ = _ := by rw [mul_one, Real.rpow_def_of_pos hn0]; congr 1; ring

theorem paper_plain_upper_estimator {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (U : ExtensionDomain d) (n : ℕ), 1 ≤ n →
      ∃ T : Estimator d n, ∀ θ, Admissible (C.withDomain U) θ →
        meanSquaredRisk T θ ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (A * (n : ℝ) ^ (-rateExponent C.smoothness d)) := by
  obtain ⟨K, hK, n₁, hn₁, hlarge⟩ := paper_upper_sharp_estimator C hreg
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.mp (eventually_paperUpperScale_le_plain C hreg)
  let n₀ := max n₁ n₂
  have hn₀ : 2 ≤ n₀ := hn₁.trans (le_max_left _ _)
  let lam := rateExponent C.smoothness d
  let D := C.varianceUpper - C.varianceLower
  let A := max K (D * (n₀ : ℝ) ^ lam)
  have hD : 0 < D := sub_pos.mpr C.variance_interval
  have hA : 0 < A := hK.trans_le (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro U n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hscale : 0 ≤ (n : ℝ) ^ (-lam) := Real.rpow_nonneg hn0.le _
  by_cases hnn : n₀ ≤ n
  · obtain ⟨T, hT⟩ := hlarge U n ((le_max_left _ _).trans hnn)
    refine ⟨T, ?_⟩
    intro θ hθ
    apply (hT θ hθ).trans
    apply ENNReal.ofReal_mono
    have hsc := hn₂ n ((le_max_right _ _).trans hnn)
    exact (mul_le_mul_of_nonneg_left hsc hK.le).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hscale)
  · refine ⟨constantEstimator d n C.varianceLower, ?_⟩
    intro θ hθ
    have hconst := ENNReal.rpow_le_rpow
      (constantEstimator_risk_bound (n := n) (C.withDomain U) θ hθ)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num)] at hconst
    change meanSquaredRisk (constantEstimator d n C.varianceLower) θ ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (((C.varianceUpper - C.varianceLower) ^ 2) ^ (1 / 2 : ℝ)) at hconst
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (sub_nonneg.mpr C.variance_interval.le)] at hconst
    apply hconst.trans
    apply ENNReal.ofReal_mono
    have hl : 0 ≤ lam := (rateExponent_pos hreg.1 hreg.2).le
    have hmon : (n : ℝ) ^ lam ≤ (n₀ : ℝ) ^ lam :=
      Real.rpow_le_rpow hn0.le (by exact_mod_cast (by omega : n ≤ n₀)) hl
    have hid : (n : ℝ) ^ lam * (n : ℝ) ^ (-lam) = 1 := by
      rw [← Real.rpow_add hn0]
      simp
    have hunit : 1 ≤ (n₀ : ℝ) ^ lam * (n : ℝ) ^ (-lam) := by
      simpa only [hid] using mul_le_mul_of_nonneg_right hmon hscale
    have hsmall : D ≤ (D * (n₀ : ℝ) ^ lam) * (n : ℝ) ^ (-lam) := by
      have hh := mul_le_mul_of_nonneg_left hunit hD.le
      simpa only [mul_one, mul_assoc] using hh
    exact hsmall.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hscale)

end NearlyMinimax
