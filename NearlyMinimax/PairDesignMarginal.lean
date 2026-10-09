module

public import NearlyMinimax.PairDesignMeasure


@[expose] public section

/-! Actual marginal localization of the weighted design-pair measure. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem partitionPairMeasure_fst_le {X I : Type*}
    [MeasurableSpace X] [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] [MeasurableEq I]
    (μ : Measure X) [IsProbabilityMeasure μ] (label : X → I) (hlabel : Measurable label)
    {weight cap : ℝ} (hw : 0 ≤ weight) (hcap : 0 ≤ cap)
    (hmass : ∀ i, μ.real (label ⁻¹' {i}) ≤ cap) :
    (partitionPairMeasure μ label weight).map Prod.fst ≤ ENNReal.ofReal (weight * cap) • μ := by
  apply Measure.le_iff.2
  intro A hA
  have hC : MeasurableSet {z : X × X | label z.1 = label z.2} :=
    measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd)
  rw [Measure.map_apply measurable_fst hA, partitionPairMeasure,
    Measure.smul_apply, Measure.restrict_apply (measurable_fst hA),
    Measure.prod_apply ((measurable_fst hA).inter hC), Measure.smul_apply,
    ENNReal.ofReal_mul hw]
  change ENNReal.ofReal weight *
    (∫⁻ x, μ (Prod.mk x ⁻¹' (Prod.fst ⁻¹' A ∩ {z : X × X | label z.1 = label z.2})) ∂μ) ≤
      (ENNReal.ofReal weight * ENNReal.ofReal cap) * μ A
  have hi : (∫⁻ x, μ (Prod.mk x ⁻¹'
      (Prod.fst ⁻¹' A ∩ {z : X × X | label z.1 = label z.2})) ∂μ) ≤
      ENNReal.ofReal cap * μ A := by
    calc
      _ ≤ ∫⁻ x, A.indicator (fun _ => ENNReal.ofReal cap) x ∂μ := by
        apply lintegral_mono
        intro x
        change μ (Prod.mk x ⁻¹' (Prod.fst ⁻¹' A ∩ {z : X × X | label z.1 = label z.2})) ≤ _
        by_cases hx : x ∈ A
        · have he : Prod.mk x ⁻¹'
              (Prod.fst ⁻¹' A ∩ {z : X × X | label z.1 = label z.2}) =
              label ⁻¹' {label x} := by
            ext y
            simp [hx, eq_comm]
          rw [he, Set.indicator_of_mem hx]
          have hb := ENNReal.ofReal_le_ofReal (hmass (label x))
          simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)] using hb
        · have he : Prod.mk x ⁻¹'
              (Prod.fst ⁻¹' A ∩ {z : X × X | label z.1 = label z.2}) = ∅ := by
            ext y
            simp [hx]
          rw [he, measure_empty, Set.indicator_of_notMem hx]
      _ = _ := lintegral_indicator_const hA _
  calc
    _ ≤ ENNReal.ofReal weight * (ENNReal.ofReal cap * μ A) := by gcongr
    _ = _ := (mul_assoc _ _ _).symm

theorem regularPairDesignMeasure_fst_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (regularPairDesignMeasure θ k hk).map Prod.fst ≤ ENNReal.ofReal C.densityUpper • designLaw θ := by
  let := designLaw_isProbability C θ hθ
  have hkp : 0 < (k : ℝ) ^ d := pow_pos (by exact_mod_cast hk) d
  have h := partitionPairMeasure_fst_le (designLaw θ) (regularGridCell k hk)
    (regular_grid_cell_measurable k hk) hkp.le
    (div_nonneg (by linarith [C.one_lt_densityUpper]) hkp.le)
    (regularGridProbability_cap C θ hθ k hk)
  simpa only [regularPairDesignMeasure, partitionPairMeasure,
    mul_div_cancel₀ _ hkp.ne'] using h

theorem regularPairDesignMeasure_fst_cube_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (regularPairDesignMeasure θ k hk).map Prod.fst ≤
      ENNReal.ofReal (C.densityUpper ^ 2) • cubeVolume d := by
  have hp : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
  calc
    _ ≤ ENNReal.ofReal C.densityUpper • designLaw θ :=
      regularPairDesignMeasure_fst_le C θ hθ k hk
    _ ≤ ENNReal.ofReal C.densityUpper • (ENNReal.ofReal C.densityUpper • cubeVolume d) := by
      gcongr
      exact admissible_designLaw_le_cubeVolume C θ hθ
    _ = _ := by rw [smul_smul, ← ENNReal.ofReal_mul hp, ← pow_two]

end NearlyMinimax
