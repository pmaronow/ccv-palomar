module

public import NearlyMinimax.Clipping
public import NearlyMinimax.RiskIdentity
public import RoughRegime.LowerMeasure
public import NearlyMinimax.ParametricConstants


@[expose] public section

/-! Two-point testing for the actual ternary-response regression submodel.
This file constructs probability densities and transfers testing to the
original observation space.  No minimax rate is an assumed premise.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
open RoughRegime.GeneralTesting RoughRegime.LowerMeasure

def labelBase : Measure (Fin 3) := ENNReal.ofReal (1 / 3 : ℝ) • Measure.count

instance labelBase_isProbability : IsProbabilityMeasure labelBase := by
  constructor
  simp [labelBase, Measure.smul_apply, Measure.count_univ]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

def ternaryDensityLaw (a V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) : DensityLaw labelBase where
  density y := 3 * ternaryMass a 0 V y
  measurable := measurable_of_countable _
  integrable := Integrable.of_finite
  nonneg := Filter.Eventually.of_forall (fun y => mul_nonneg (by norm_num) (hp y))
  integral_one := by
    rw [labelBase, integral_smul_measure, integral_count]
    norm_num only [ENNReal.toReal_ofReal, smul_eq_mul]
    rw [← Finset.mul_sum, ternary_normalized a 0 V ha]
    norm_num

theorem ternaryDensityLaw_measure (a V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) :
    (ternaryDensityLaw a V ha hp).measure =
      Measure.count.withDensity (fun y => ENNReal.ofReal (ternaryMass a 0 V y)) := by
  unfold DensityLaw.measure ternaryDensityLaw labelBase
  rw [withDensity_smul_measure, ← withDensity_smul]
  · congr 1
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    congr 1
    ring
  · exact ENNReal.measurable_ofReal.comp (measurable_of_countable _)

theorem ternaryDensityLaw_map (a V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) :
    (ternaryDensityLaw a V ha hp).measure.map (ternaryValue a) = ternaryMeasure a 0 V := by
  rw [ternaryDensityLaw_measure, count_withDensity,
    Measure.map_sum (measurable_of_countable _).aemeasurable, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro y _
  rw [Measure.map_smul _ (measurable_of_countable _).aemeasurable, Measure.map_dirac]

theorem ternary_submodel_admissible {d : ℕ} (C : ModelConstants d)
    (a V : ℝ) (ha : 0 < a) (hV : C.varianceLower ≤ V)
    (hVupper : V ≤ C.varianceUpper) (_hVa : V < a ^ 2)
    (hfourth : a ^ 2 * V ≤ C.fourthBound)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) :
    Admissible C (uniformZeroParameter d a V ha.ne' hp) := by
  let θ := uniformZeroParameter d a V ha.ne' hp
  change Admissible C θ
  refine ⟨measurable_const, measurable_const, ?_, ?_, ?_, hV, hVupper, ?_⟩
  · exact Filter.Eventually.of_forall (fun x =>
      ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩)
  · simp only [θ, uniformZeroParameter, ENNReal.ofReal_one, lintegral_const, one_mul]
    exact cubeVolume_univ d
  · refine ⟨fun _ => 0, fun _ _ => rfl, contDiffOn_const, ?_⟩
    rw [holderNorm_zero]
    exact zero_le
  · apply Filter.Eventually.of_forall
    intro x
    simp only [θ, uniformZeroParameter, Kernel.const_apply]
    refine ⟨ternaryMeasure_integrable a 0 V _, ternaryMeasure_integrable a 0 V _,
      ternaryMeasure_integrable a 0 V _, ternaryMeasure_mean a 0 V ha.ne' hp, ?_, ?_⟩
    · simpa using ternaryMeasure_variance a 0 V ha.ne' hp
    · have he := ternaryMeasure_fourthMoment a 0 V ha.ne' hp
      simp only [sub_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0),
        mul_zero, add_zero] at he
      exact he.trans_le hfourth

def encodeResponse {d n : ℕ} (a : ℝ) :
    (Fin n → Fin 3) × (Fin n → Covariate d) → (Fin n → Observation d) :=
  fun z i => (z.2 i, ternaryValue a (z.1 i))

theorem encodeResponse_measurable {d n : ℕ} (a : ℝ) :
    Measurable (encodeResponse (d := d) (n := n) a) := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_pi_apply i).comp measurable_snd).prodMk
    ((measurable_of_countable (ternaryValue a)).comp
      ((measurable_pi_apply i).comp measurable_fst))

theorem ternary_label_design_map {d : ℕ} (a V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) :
    (((ternaryDensityLaw a V ha hp).measure).prod (cubeVolume d)).map
      (fun z => (z.2, ternaryValue a z.1)) =
        observationLaw (uniformZeroParameter d a V ha hp) := by
  let _ := cubeVolume_isProbability d
  let _ := ternaryMeasure_isProbability a 0 V ha hp
  rw [uniformZeroParameter_observationLaw]
  have h := Measure.map_prod_map (ternaryDensityLaw a V ha hp).measure (cubeVolume d)
    (measurable_of_countable (ternaryValue a)) measurable_id
  rw [ternaryDensityLaw_map, Measure.map_id] at h
  calc
    _ = ((((ternaryDensityLaw a V ha hp).measure).prod (cubeVolume d)).map
        (Prod.map (ternaryValue a) id)).map Prod.swap := by
      rw [Measure.map_map measurable_swap
        ((measurable_of_countable (ternaryValue a)).prodMap measurable_id)]
      rfl
    _ = ((ternaryMeasure a 0 V).prod (cubeVolume d)).map Prod.swap := by rw [← h]
    _ = _ := Measure.prod_swap

theorem encodeResponse_measurePreserving {d n : ℕ} (a V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) :
    MeasurePreserving (encodeResponse (d := d) (n := n) a)
      ((Measure.pi (fun _ : Fin n => (ternaryDensityLaw a V ha hp).measure)).prod
        (Measure.pi (fun _ : Fin n => cubeVolume d)))
      (sampleLaw (uniformZeroParameter d a V ha hp) n) := by
  let _ := cubeVolume_isProbability d
  let _ := ternaryMeasure_isProbability a 0 V ha hp
  let _ : IsProbabilityMeasure (observationLaw (uniformZeroParameter d a V ha hp)) := by
    rw [uniformZeroParameter_observationLaw]
    infer_instance
  have hsingle : MeasurePreserving (fun z : Fin 3 × Covariate d =>
      (z.2, ternaryValue a z.1))
      (((ternaryDensityLaw a V ha hp).measure).prod (cubeVolume d))
      (observationLaw (uniformZeroParameter d a V ha hp)) :=
    ⟨measurable_snd.prodMk ((measurable_of_countable _).comp measurable_fst),
      ternary_label_design_map a V ha hp⟩
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin 3) (Covariate d) (Fin n)
  have he := (measurePreserving_arrowProdEquivProdArrow (Fin 3) (Covariate d) (Fin n)
    (fun _ => (ternaryDensityLaw a V ha hp).measure) (fun _ => cubeVolume d)).symm e
  have hm := (measurePreserving_pi _ _ (fun _ : Fin n => hsingle)).comp he
  exact hm

def ternaryDensitySlope (a : ℝ) : Fin 3 → ℝ :=
  ![3 / (2 * a ^ 2), -3 / a ^ 2, 3 / (2 * a ^ 2)]

theorem ternary_density_affine (a V : ℝ) (y : Fin 3) :
    3 * ternaryMass a 0 V y = ![0, 3, 0] y + V * ternaryDensitySlope a y := by
  fin_cases y <;> simp [ternaryMass, ternaryDensitySlope, div_eq_mul_inv] <;> ring

/-- Actual two-point testing lower bound for the original regression minimax
problem.  The premises are numerical legality and one-observation mass bounds,
not statistical risk or estimator assumptions. -/
theorem ternary_two_point_minimax_lower {d : ℕ} (C : ModelConstants d) (n : ℕ)
    (a V₀ V₁ cf Cf : ℝ) (ha : 0 < a) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (hV₀ : C.varianceLower ≤ V₀) (hV₀upper : V₀ ≤ C.varianceUpper)
    (hV₁ : C.varianceLower ≤ V₁) (hV₁upper : V₁ ≤ C.varianceUpper)
    (hVa₀ : V₀ < a ^ 2) (hVa₁ : V₁ < a ^ 2)
    (hfourth₀ : a ^ 2 * V₀ ≤ C.fourthBound)
    (hfourth₁ : a ^ 2 * V₁ ≤ C.fourthBound)
    (hmass₀ : ∀ y, cf ≤ 3 * ternaryMass a 0 V₀ y)
    (hmass₁ : ∀ y, cf ≤ 3 * ternaryMass a 0 V₁ y)
    (hslope : ∀ y, |ternaryDensitySlope a y| ≤ Cf)
    (hsmall : (n : ℝ) * Cf ^ 2 * (V₀ - V₁) ^ 2 / (4 * cf) ≤ 1 / 4) :
    ENNReal.ofReal (|V₁ - V₀| / 4) ≤ minimaxRMS C n := by
  have hp₀ : ∀ y, 0 ≤ ternaryMass a 0 V₀ y := by
    intro y
    linarith [hmass₀ y]
  have hp₁ : ∀ y, 0 ≤ ternaryMass a 0 V₁ y := by
    intro y
    linarith [hmass₁ y]
  let θ₀ := uniformZeroParameter d a V₀ ha.ne' hp₀
  let θ₁ := uniformZeroParameter d a V₁ ha.ne' hp₁
  have hθ₀ : Admissible C θ₀ :=
    ternary_submodel_admissible C a V₀ ha hV₀ hV₀upper hVa₀ hfourth₀ hp₀
  have hθ₁ : Admissible C θ₁ :=
    ternary_submodel_admissible C a V₁ ha hV₁ hV₁upper hVa₁ hfourth₁ hp₁
  let P₀ := ternaryDensityLaw a V₀ ha.ne' hp₀
  let P₁ := ternaryDensityLaw a V₁ ha.ne' hp₁
  let ν := Measure.pi (fun _ : Fin n => cubeVolume d)
  let _ := cubeVolume_isProbability d
  let _ : IsProbabilityMeasure ν := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => cubeVolume d)))
  let L := densityLawWithSeed ν (iidDensityLaw P₀ n)
  let R := densityLawWithSeed ν (iidDensityLaw P₁ n)
  have hH : hellingerSquared L R ≤ 1 / 4 := by
    have hone := affine_hellinger_bound P₀ P₁ ![0, 3, 0] (ternaryDensitySlope a)
      V₀ V₁ cf Cf hcf hCf
      (Filter.Eventually.of_forall (ternary_density_affine a V₀))
      (Filter.Eventually.of_forall (ternary_density_affine a V₁))
      (Filter.Eventually.of_forall (fun y => by rw [← ternary_density_affine]; exact hmass₀ y))
      (Filter.Eventually.of_forall (fun y => by rw [← ternary_density_affine]; exact hmass₁ y))
      (Filter.Eventually.of_forall hslope)
    change hellingerSquared (densityLawWithSeed ν (iidDensityLaw P₀ n))
      (densityLawWithSeed ν (iidDensityLaw P₁ n)) ≤ _
    rw [hellinger_with_seed]
    exact (hellinger_iid_le P₀ P₁ n).trans
      ((mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg n)).trans (by
        convert hsmall using 1; ring))
  have hL : L.measure = (Measure.pi (fun _ : Fin n => P₀.measure)).prod ν := by
    dsimp [L]
    rw [densityLawWithSeed_measure, iidDensityLaw_measure]
  have hR : R.measure = (Measure.pi (fun _ : Fin n => P₁.measure)).prod ν := by
    dsimp [R]
    rw [densityLawWithSeed_measure, iidDensityLaw_measure]
  rw [minimaxRMS_eq_inf_sup_eLpNorm]
  apply le_iInf
  intro T
  have ht := two_point_rmse_lower L R (T.val ∘ encodeResponse (d := d) (n := n) a)
    (T.property.comp (encodeResponse_measurable a)) V₀ V₁ hH
  rw [hL, hR] at ht
  have he₀ : eLpNorm (fun z => T.val (encodeResponse a z) - V₀) 2
      ((Measure.pi (fun _ : Fin n => P₀.measure)).prod ν) =
      eLpNorm (fun z => T.val z - θ₀.variance) 2 (sampleLaw θ₀ n) := by
    exact eLpNorm_comp_measurePreserving (T.property.sub measurable_const).aestronglyMeasurable
      (encodeResponse_measurePreserving a V₀ ha.ne' hp₀)
  have he₁ : eLpNorm (fun z => T.val (encodeResponse a z) - V₁) 2
      ((Measure.pi (fun _ : Fin n => P₁.measure)).prod ν) =
      eLpNorm (fun z => T.val z - θ₁.variance) 2 (sampleLaw θ₁ n) := by
    exact eLpNorm_comp_measurePreserving (T.property.sub measurable_const).aestronglyMeasurable
      (encodeResponse_measurePreserving a V₁ ha.ne' hp₁)
  change _ ≤ eLpNorm (fun z => T.val (encodeResponse a z) - V₀) 2 _ ∨
    _ ≤ eLpNorm (fun z => T.val (encodeResponse a z) - V₁) 2 _ at ht
  rw [he₀, he₁] at ht
  rcases ht with ht | ht
  · exact ht.trans (le_iSup (fun θ : {θ // Admissible C θ} =>
      eLpNorm (fun z => T.val z - θ.val.variance) 2 (sampleLaw θ.val n)) ⟨θ₀, hθ₀⟩)
  · exact ht.trans (le_iSup (fun θ : {θ // Admissible C θ} =>
      eLpNorm (fun z => T.val z - θ.val.variance) 2 (sampleLaw θ.val n)) ⟨θ₁, hθ₁⟩)

theorem ternaryDensitySlope_eq (a : ℝ) (y : Fin 3) :
    ternaryDensitySlope a y = 3 * ternaryVarianceDerivative a y := by
  fin_cases y <;> simp [ternaryDensitySlope, ternaryVarianceDerivative] <;> ring

/-- The original statistical class has a positive root-n minimax RMS lower
bound for every sample size n>=1 and every smoothness/dimension regime.
The constants and the actual iid submodel are constructed, not assumed. -/
theorem parametric_minimax_lower {d : ℕ} (C : ModelConstants d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ minimaxRMS C n := by
  obtain ⟨P⟩ := parametricTernaryConstants_exists C
  refine ⟨P.delta / 2, div_pos P.delta_pos (by norm_num), ?_⟩
  intro n hn
  have hm := P.varianceMinus_mem n hn
  have hp := P.variancePlus_mem n hn
  have hb₀ := P.model_variance_bounds _ hm
  have hb₁ := P.model_variance_bounds _ hp
  have htest := ternary_two_point_minimax_lower C n P.a (P.varianceMinus n)
    (P.variancePlus n) P.cf P.Cf P.a_pos P.cf_pos P.Cf_pos.le
    hb₀.1 hb₀.2 hb₁.1 hb₁.2
    (P.variance_lt_square_of_mem _ hm) (P.variance_lt_square_of_mem _ hp)
    (P.fourth_le_of_mem _ hm) (P.fourth_le_of_mem _ hp)
    (P.density_lower _ hm) (P.density_lower _ hp)
    (fun y => by rw [ternaryDensitySlope_eq]; exact P.derivative_bound y)
    (P.score_budget_reverse n hn)
  have hinv : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
  have hscale : |P.variancePlus n - P.varianceMinus n| / 4 =
      (P.delta / 2) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [abs_of_pos (P.separation_pos n hn), P.separation n, hinv]
    ring
  rw [hscale] at htest
  exact htest

end NearlyMinimax
