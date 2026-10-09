module

public import NearlyMinimax.PaperPlainUpper
public import NearlyMinimax.ElementaryUpper


@[expose] public section

/-! The full elementary upper proposition, with an actual Borel estimator
for every positive sample size and a constant uniform over extension domains. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

def paperElementaryUpperScale {d : ℕ} (C : ModelConstants d) (n : ℕ) : ℝ :=
  max ((n : ℝ) ^ (-(1 / 2 : ℝ)))
    ((n : ℝ) ^ (-(2 * (C.smoothness + min C.smoothness 1) /
      ((d : ℝ) + 4 * min C.smoothness 1))))

theorem estimator_l2_sup_le_of_point_rms {d n : ℕ} (C : ModelConstants d)
    (T : Estimator d n) (b : ℝ)
    (h : ∀ θ, Admissible C θ → meanSquaredRisk T θ ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal b) :
    (⨆ θ : {θ : RegressionParameter d // Admissible C θ},
      eLpNorm (fun z => T.val z - θ.val.variance) 2 (sampleLaw θ.val n)) ≤ ENNReal.ofReal b := by
  apply iSup_le
  intro θ
  rw [← meanSquaredRisk_rpow_eq_eLpNorm]
  exact h θ.val θ.property

theorem paper_elementary_upper {d : ℕ} (C : ModelConstants d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (U : ExtensionDomain d) (n : ℕ), 1 ≤ n →
      ∃ T : Estimator d n,
        (⨆ θ : {θ : RegressionParameter d // Admissible (C.withDomain U) θ},
          eLpNorm (fun z => T.val z - θ.val.variance) 2 (sampleLaw θ.val n)) ≤
            ENNReal.ofReal (A * paperElementaryUpperScale C n) := by
  by_cases hs : C.smoothness ≤ 1
  · refine ⟨elementaryRMSConstant C, elementaryRMSConstant_pos C, ?_⟩
    intro U n hn
    let T := elementaryEstimator (C.withDomain U) n
    refine ⟨T, ?_⟩
    apply estimator_l2_sup_le_of_point_rms (C.withDomain U) T
    intro θ hθ
    have hh := (ENNReal.rpow_le_rpow
      (meanSquaredRisk_le_worstCaseRisk (C.withDomain U) T θ hθ)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
      (elementary_upper_low_smoothness (C.withDomain U) hs (by omega : 0 < n))
    have hexp : -(2 * (C.smoothness + C.smoothness) /
        ((d : ℝ) + 4 * C.smoothness)) = -4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness) := by ring
    change meanSquaredRisk T θ ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal
      (elementaryRMSConstant C * max ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        ((n : ℝ) ^ (-4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)))) at hh
    simpa only [paperElementaryUpperScale, min_eq_left hs, hexp] using hh
  · have hs1 : 1 < C.smoothness := lt_of_not_ge hs
    by_cases hd : (d : ℝ) ≤ 4 * C.smoothness
    · let A := Real.sqrt (2 * projectionUpperConstant C)
      have hA : 0 < A := Real.sqrt_pos.mpr
        (mul_pos (by norm_num) (projectionUpperConstant_pos C))
      refine ⟨A, hA, ?_⟩
      intro U n hn
      let T := clippedEstimator (C.withDomain U) (projectionUpperEstimator (C.withDomain U) n)
      refine ⟨T, ?_⟩
      have hh := projection_estimator_l2_bound (C.withDomain U) (by omega : 0 < n)
      apply hh.trans
      apply ENNReal.ofReal_mono
      change A * projectionRMSScale C n ≤ A * paperElementaryUpperScale C n
      apply mul_le_mul_of_nonneg_left _ hA.le
      have hd0 : 0 < (d : ℝ) := by exact_mod_cast C.dimension_pos
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have he : -(2 * C.smoothness / d) ≤ -(1 / 2 : ℝ) := by
        apply neg_le_neg
        apply (le_div_iff₀ hd0).mpr
        nlinarith only [hd]
      have hp := Real.rpow_le_rpow_of_exponent_le hn1 he
      rw [projectionRMSScale, max_eq_left hp]
      exact le_max_left _ _
    · have hreg : highSmoothnessRegime C := ⟨hs1, lt_of_not_ge hd⟩
      obtain ⟨A, hA, hT⟩ := paper_plain_upper_estimator C hreg
      refine ⟨A, hA, ?_⟩
      intro U n hn
      obtain ⟨T, hr⟩ := hT U n hn
      refine ⟨T, ?_⟩
      apply estimator_l2_sup_le_of_point_rms (C.withDomain U) T
      intro θ hθ
      apply (hr θ hθ).trans
      apply ENNReal.ofReal_mono
      apply mul_le_mul_of_nonneg_left _ hA.le
      dsimp only [paperElementaryUpperScale, rateExponent]
      rw [min_eq_right hs1.le]
      norm_num only [mul_one]
      exact le_max_right _ _

end NearlyMinimax
