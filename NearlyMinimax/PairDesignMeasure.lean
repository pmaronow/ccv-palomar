module

public import NearlyMinimax.FinitePartitionMoments


@[expose] public section

/-! The actual weighted same-cell design-pair measure. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

section Partition
variable {X I : Type*} [MeasurableSpace X] [Fintype I] [MeasurableSpace I]
  [MeasurableSingletonClass I] [MeasurableEq I]
variable (μ : Measure X) [IsProbabilityMeasure μ] (label : X → I)

def partitionPairMeasure (weight : ℝ) : Measure (X × X) :=
  ENNReal.ofReal weight • (μ.prod μ).restrict {z | label z.1 = label z.2}

instance partitionPairMeasure_isFinite (weight : ℝ) :
    IsFiniteMeasure (partitionPairMeasure μ label weight) := by
  unfold partitionPairMeasure
  exact ((μ.prod μ).restrict {z | label z.1 = label z.2}).smul_finite ENNReal.ofReal_ne_top

theorem partitionPairMeasure_integral (hlabel : Measurable label)
    {weight : ℝ} (hw : 0 ≤ weight) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : X × X → E) :
    (∫ z, f z ∂partitionPairMeasure μ label weight) =
      weight • ∫ z, sameLabelKernel label z • f z ∂μ.prod μ := by
  have hC : MeasurableSet {z : X × X | label z.1 = label z.2} :=
    measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd)
  have he : (fun z : X × X => sameLabelKernel label z • f z) =
      {z : X × X | label z.1 = label z.2}.indicator f := by
    funext z
    by_cases hz : label z.1 = label z.2
    · simp [sameLabelKernel, Set.indicator_apply, hz]
    · simp [sameLabelKernel, Set.indicator_apply, hz]
  rw [partitionPairMeasure, integral_smul_measure, ENNReal.toReal_ofReal hw, he,
    integral_indicator hC]

theorem partitionPairMeasure_real_univ (hlabel : Measurable label)
    {weight : ℝ} (hw : 0 ≤ weight) :
    (partitionPairMeasure μ label weight).real univ =
      weight * ∑ i : I, μ.real (label ⁻¹' {i}) ^ 2 := by
  have hi := partitionPairMeasure_integral μ label hlabel hw (fun _ => (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at hi
  rwa [sameLabelKernel_integral μ label hlabel] at hi

end Partition

def regularPairDesignMeasure {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k) :
    Measure (Covariate d × Covariate d) :=
  ENNReal.ofReal ((k : ℝ) ^ d) • ((designLaw θ).prod (designLaw θ)).restrict
    {z | regularGridCell k hk z.1 = regularGridCell k hk z.2}

theorem regularPairDesignMeasure_isFinite {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    IsFiniteMeasure (regularPairDesignMeasure θ k hk) := by
  let := designLaw_isProbability C θ hθ
  change IsFiniteMeasure (partitionPairMeasure (designLaw θ) (regularGridCell k hk) ((k : ℝ) ^ d))
  infer_instance

theorem regularPairDesignMeasure_integral {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Covariate d × Covariate d → E) :
    (∫ z, f z ∂regularPairDesignMeasure θ k hk) =
      (k : ℝ) ^ d • ∫ z, sameLabelKernel (regularGridCell k hk) z • f z
        ∂(designLaw θ).prod (designLaw θ) := by
  let := designLaw_isProbability C θ hθ
  exact partitionPairMeasure_integral (designLaw θ) (regularGridCell k hk)
    (regular_grid_cell_measurable k hk) (pow_nonneg (Nat.cast_nonneg k) d) f

theorem regularPairDesignMeasure_mass {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (regularPairDesignMeasure θ k hk).real univ =
      (k : ℝ) ^ d * regularGridCollisionMass θ k hk := by
  let := designLaw_isProbability C θ hθ
  exact partitionPairMeasure_real_univ (designLaw θ) (regularGridCell k hk)
    (regular_grid_cell_measurable k hk) (pow_nonneg (Nat.cast_nonneg k) d)

theorem regularPairDesignMeasure_mass_bounds {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    1 ≤ (regularPairDesignMeasure θ k hk).real univ ∧
      (regularPairDesignMeasure θ k hk).real univ ≤ C.densityUpper := by
  rw [regularPairDesignMeasure_mass C θ hθ k hk]
  have hkp : 0 < (k : ℝ) ^ d := pow_pos (by exact_mod_cast hk) d
  constructor
  · have h := mul_le_mul_of_nonneg_left (regularGridCollisionMass_lower C θ hθ k hk) hkp.le
    simpa [hkp.ne', mul_div_cancel₀] using h
  · have h := mul_le_mul_of_nonneg_left (regularGridCollisionMass_upper C θ hθ k hk) hkp.le
    simpa [hkp.ne', mul_comm, mul_div_cancel₀] using h

end NearlyMinimax
