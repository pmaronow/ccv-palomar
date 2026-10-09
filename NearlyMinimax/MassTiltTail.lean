module

public import NearlyMinimax.HighMassTilt


@[expose] public section

/-!
# Genuine mass-power tilt tail from an exponential moment bound
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace NearlyMinimax

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The source mean-one power normalizer is at least one, by the actual tangent inequality. -/
theorem massPowerNormalizer_one_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (l b : ℝ) (hl : 0 < l)
    (hbound : ∀ ω, l ≤ m ω ∧ m ω ≤ b) (hmean : ∫ ω, m ω ∂μ = 1) :
    1 ≤ massPowerNormalizer μ m n := by
  have hi := massPower_integrable μ m hm 1 l b hl hbound
  have him : Integrable m μ := by simpa only [pow_one] using hi
  have hip := massPower_integrable μ m hm n l b hl hbound
  have hh : (∫ ω, 1 + (n : ℝ) * (m ω - 1) ∂μ) ≤ ∫ ω, m ω ^ n ∂μ :=
    integral_mono ((integrable_const 1).add ((him.sub (integrable_const 1)).const_mul (n : ℝ))) hip
      (fun ω => one_add_mul_sub_le_pow ((by norm_num : (-1 : ℝ) ≤ 0).trans (hl.le.trans (hbound ω).1)) n)
  have he : (∫ ω, 1 + (n : ℝ) * (m ω - 1) ∂μ) = 1 := by
    calc
      _ = (∫ _ : Ω, (1 : ℝ) ∂μ) + ∫ ω, (n : ℝ) * (m ω - 1) ∂μ :=
        integral_add (integrable_const 1) ((him.sub (integrable_const 1)).const_mul (n : ℝ))
      _ = 1 := by rw [integral_const_mul, integral_sub him (integrable_const 1), hmean]; simp
  rw [he] at hh
  exact hh

/-- The true mass-power tilt of a measurable event is its normalized weighted indicator integral. -/
theorem massPowerTilt_real_apply (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (l b : ℝ) (hl : 0 < l)
    (hbound : ∀ ω, l ≤ m ω ∧ m ω ≤ b) (S : Set Ω) (hS : MeasurableSet S) :
    (massPowerTilt μ m n).real S =
      ∫ ω, S.indicator (fun ω => m ω ^ n / massPowerNormalizer μ m n) ω ∂μ := by
  let := massPowerTilt_isProbability μ m hm n l b hl hbound
  have hG := massPowerNormalizer_pos μ m hm n l b hl hbound
  rw [← integral_indicator_one hS, massPowerTilt,
    integral_withDensity_eq_integral_toReal_smul ((hm.pow_const n).div_const _).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ω
  have hp : 0 ≤ m ω ^ n / massPowerNormalizer μ m n :=
    div_nonneg (pow_nonneg (hl.le.trans (hbound ω).1) _) hG.le
  by_cases hω : ω ∈ S <;> simp [hω, ENNReal.toReal_ofReal hp, smul_eq_mul]

/-- A positive bounded mass has an integrable exponential at every real parameter. -/
theorem boundedMass_exp_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (l b : ℝ) (hl : 0 < l)
    (hbound : ∀ ω, l ≤ m ω ∧ m ω ≤ b) (u : ℝ) :
    Integrable (fun ω => Real.exp (u * (m ω - 1))) μ := by
  apply Integrable.of_bound (Real.measurable_exp.comp (measurable_const.mul (hm.sub measurable_const))).aestronglyMeasurable
    (Real.exp (|u| * (|b| + 1)))
  apply Eventually.of_forall
  intro ω
  change ‖Real.exp (u * (m ω - 1))‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  have hmabs : |m ω| ≤ |b| := by
    rw [abs_of_pos (hl.trans_le (hbound ω).1)]
    exact (hbound ω).2.trans (le_abs_self b)
  have hz : |m ω - 1| ≤ |b| + 1 := by
    have hh := abs_sub (m ω) 1
    norm_num only [abs_one] at hh
    linarith
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hz (abs_nonneg u))

/-- The positive-side event under a true mass-power tilt satisfies a genuine Chernoff bound. -/
theorem massPowerTilt_right_chernoff (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (l b : ℝ) (hl : 0 < l)
    (hbound : ∀ ω, l ≤ m ω ∧ m ω ≤ b) (hmean : ∫ ω, m ω ∂μ = 1)
    (ε u : ℝ) (hu : 0 ≤ u) :
    (massPowerTilt μ m n).real {ω | ε < m ω - 1} ≤
      Real.exp (-u * ε) * ∫ ω, Real.exp (((n : ℝ) + u) * (m ω - 1)) ∂μ := by
  let S := {ω | ε < m ω - 1}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (hm.sub measurable_const)
  have hG := massPowerNormalizer_one_le μ m hm n l b hl hbound hmean
  have hGpos := massPowerNormalizer_pos μ m hm n l b hl hbound
  have hI := massPower_integrable μ m hm n l b hl hbound
  rw [massPowerTilt_real_apply μ m hm n l b hl hbound S hS, ← integral_const_mul]
  apply integral_mono ((hI.div_const _).indicator hS)
    ((boundedMass_exp_integrable μ m hm l b hl hbound ((n : ℝ) + u)).const_mul _)
  intro ω
  by_cases hω : ω ∈ S
  · simp only [Set.indicator_of_mem hω]
    have hm0 : 0 ≤ m ω := hl.le.trans (hbound ω).1
    have hpow : m ω ^ n ≤ Real.exp ((n : ℝ) * (m ω - 1)) := by
      have hbase : m ω ≤ Real.exp (m ω - 1) := by
        have hh := Real.add_one_le_exp (m ω - 1)
        linarith
      calc
        _ ≤ Real.exp (m ω - 1) ^ n := pow_le_pow_left₀ hm0 hbase n
        _ = _ := (Real.exp_nat_mul _ _).symm
    calc
      _ ≤ m ω ^ n := div_le_self (pow_nonneg hm0 n) hG
      _ ≤ Real.exp ((n : ℝ) * (m ω - 1)) := hpow
      _ ≤ _ := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have hh : ε ≤ m ω - 1 := hω.le
        nlinarith [mul_nonneg hu (sub_nonneg.2 hh)]
  · simp only [Set.indicator_of_notMem hω]
    positivity

/-- The negative-side Chernoff bound uses the true mass-power tilt and m^n≤1 on the lower event. -/
theorem massPowerTilt_left_chernoff (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (l b : ℝ) (hl : 0 < l)
    (hbound : ∀ ω, l ≤ m ω ∧ m ω ≤ b) (hmean : ∫ ω, m ω ∂μ = 1)
    (ε u : ℝ) (hε : 0 ≤ ε) (hu : 0 ≤ u) :
    (massPowerTilt μ m n).real {ω | m ω - 1 < -ε} ≤
      Real.exp (-u * ε) * ∫ ω, Real.exp ((-u) * (m ω - 1)) ∂μ := by
  let S := {ω | m ω - 1 < -ε}
  have hS : MeasurableSet S := measurableSet_lt (hm.sub measurable_const) measurable_const
  have hG := massPowerNormalizer_one_le μ m hm n l b hl hbound hmean
  have hI := massPower_integrable μ m hm n l b hl hbound
  rw [massPowerTilt_real_apply μ m hm n l b hl hbound S hS, ← integral_const_mul]
  apply integral_mono ((hI.div_const _).indicator hS)
    ((boundedMass_exp_integrable μ m hm l b hl hbound (-u)).const_mul _)
  intro ω
  by_cases hω : ω ∈ S
  · simp only [Set.indicator_of_mem hω]
    have hm0 : 0 ≤ m ω := hl.le.trans (hbound ω).1
    have hm1 : m ω ≤ 1 := by have hh : m ω - 1 < -ε := hω; linarith
    calc
      _ ≤ m ω ^ n := div_le_self (pow_nonneg hm0 n) hG
      _ ≤ 1 := pow_le_one₀ hm0 hm1
      _ ≤ _ := by
        rw [← Real.exp_add]
        apply Real.one_le_exp_iff.2
        have hh : m ω - 1 ≤ -ε := hω.le
        nlinarith [mul_nonneg hu (sub_nonneg.2 hh)]
  · simp only [Set.indicator_of_notMem hω]
    positivity

/-- The exact source ε≥8an guard controls the positive-side tilted exponent. -/
theorem massTilt_exponent_right (a ε : ℝ) (n : ℕ) (ha : 0 < a)
    (hε : 8 * a * (n : ℝ) ≤ ε) :
    0 ≤ ε / (2 * a) - (n : ℝ) ∧
      -(ε / (2 * a) - (n : ℝ)) * ε + a * ((n : ℝ) + (ε / (2 * a) - (n : ℝ))) ^ 2 ≤
        -ε ^ 2 / (8 * a) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have he0 : 0 ≤ ε := (by positivity : (0 : ℝ) ≤ 8 * a * (n : ℝ)).trans hε
  have hu : 0 ≤ ε / (2 * a) - (n : ℝ) := by
    apply sub_nonneg.2
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * a)).2
    nlinarith
  have he : (n : ℝ) * ε ≤ ε ^ 2 / (8 * a) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * a)).2
    nlinarith [mul_nonneg he0 (sub_nonneg.2 hε)]
  have hid : -(ε / (2 * a) - (n : ℝ)) * ε + a * ((n : ℝ) + (ε / (2 * a) - (n : ℝ))) ^ 2 =
      (n : ℝ) * ε - 2 * (ε ^ 2 / (8 * a)) := by field_simp; ring
  exact ⟨hu, by rw [hid]; simp only [neg_div]; linarith⟩

/-- The exact source lower-tail exponent before weakening its constant. -/
theorem massTilt_exponent_left (a ε : ℝ) (ha : 0 < a) :
    -(ε / (2 * a)) * ε + a * (-(ε / (2 * a))) ^ 2 ≤ -ε ^ 2 / (8 * a) := by
  have hid : -(ε / (2 * a)) * ε + a * (-(ε / (2 * a))) ^ 2 =
      -2 * (ε ^ 2 / (8 * a)) := by field_simp; ring
  rw [hid]
  simp only [neg_div]
  have hn : 0 ≤ ε ^ 2 / (8 * a) := div_nonneg (sq_nonneg _) (by positivity)
  linarith

/-- The source mass-power tilted exceptional tail follows from its actual mean-one MGF.
This is a probability lemma; the history MGF is established independently from finite label blocks. -/
theorem massPowerTilt_abs_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (l b : ℝ) (hl : 0 < l)
    (hbound : ∀ ω, l ≤ m ω ∧ m ω ≤ b) (hmean : ∫ ω, m ω ∂μ = 1)
    (a ε : ℝ) (ha : 0 < a)
    (hmgf : ∀ u : ℝ, (∫ ω, Real.exp (u * (m ω - 1)) ∂μ) ≤ Real.exp (a * u ^ 2))
    (hε : 8 * a * (n : ℝ) ≤ ε) :
    (massPowerTilt μ m n).real {ω | ε < |m ω - 1|} ≤ 2 * Real.exp (-ε ^ 2 / (8 * a)) := by
  let := massPowerTilt_isProbability μ m hm n l b hl hbound
  have he0 : 0 ≤ ε := (by positivity : (0 : ℝ) ≤ 8 * a * (n : ℝ)).trans hε
  have hr : (massPowerTilt μ m n).real {ω | ε < m ω - 1} ≤ Real.exp (-ε ^ 2 / (8 * a)) := by
    have hs := massTilt_exponent_right a ε n ha hε
    calc
      _ ≤ Real.exp (-(ε / (2 * a) - (n : ℝ)) * ε) *
          ∫ ω, Real.exp (((n : ℝ) + (ε / (2 * a) - (n : ℝ))) * (m ω - 1)) ∂μ :=
        massPowerTilt_right_chernoff μ m hm n l b hl hbound hmean ε _ hs.1
      _ ≤ Real.exp (-(ε / (2 * a) - (n : ℝ)) * ε) *
          Real.exp (a * ((n : ℝ) + (ε / (2 * a) - (n : ℝ))) ^ 2) :=
        mul_le_mul_of_nonneg_left (hmgf _) (Real.exp_pos _).le
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.2 hs.2
  have hlower : (massPowerTilt μ m n).real {ω | m ω - 1 < -ε} ≤ Real.exp (-ε ^ 2 / (8 * a)) := by
    calc
      _ ≤ Real.exp (-(ε / (2 * a)) * ε) * ∫ ω, Real.exp ((-(ε / (2 * a))) * (m ω - 1)) ∂μ :=
        massPowerTilt_left_chernoff μ m hm n l b hl hbound hmean ε _ he0 (div_nonneg he0 (by positivity))
      _ ≤ Real.exp (-(ε / (2 * a)) * ε) * Real.exp (a * (-(ε / (2 * a))) ^ 2) :=
        mul_le_mul_of_nonneg_left (hmgf _) (Real.exp_pos _).le
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.2 (massTilt_exponent_left a ε ha)
  have hset : {ω | ε < |m ω - 1|} = {ω | ε < m ω - 1} ∪ {ω | m ω - 1 < -ε} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, lt_abs]
    constructor <;> intro h <;> rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [hset]
  exact (measureReal_union_le _ _).trans (by linarith)

end NearlyMinimax
