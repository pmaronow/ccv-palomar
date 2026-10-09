module

public import NearlyMinimax.ExponentialSpatialKernels
public import Mathlib.Probability.Independence.Integration


@[expose] public section

/-! Actual independent spatial-coordinate projections and pair integrations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Actual projection onto any distinct finite spatial coordinates preserves the true independent law. -/
theorem spatialPi_projection_preserving {I J E : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] (e : I ↪ J) :
    MeasurePreserving (fun U : J → E => fun i => U (e i))
      (Measure.pi (fun _ : J => π)) (Measure.pi (fun _ : I => π)) := by
  have hc : iIndepFun (fun j (U : J → E) => U j) (Measure.pi (fun _ : J => π)) :=
    iIndepFun_pi (X := fun _ : J => (id : E → E)) (fun _ => aemeasurable_id)
  have hs := iIndepFun.precomp e.injective hc
  have hm : Measurable (fun U : J → E => fun i => U (e i)) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i))
  refine ⟨hm, ?_⟩
  have he := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable)).mp hs
  simpa only [(measurePreserving_eval (fun _ : J => π) _).map_eq] using he

/-- Scaling each genuine finite coordinate measure scales its product by the cardinal power. -/
theorem spatialPi_const_smul {J E : Type*} [Fintype J] [MeasurableSpace E]
    (π : Measure E) [SigmaFinite π] (c : ℝ≥0∞) [SigmaFinite (c • π)] :
    Measure.pi (fun _ : J => c • π) = c^(Fintype.card J) • Measure.pi (fun _ : J => π) := by
  classical
  apply Measure.pi_eq (μ := fun _ : J => c • π)
  intro S hS
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- The actual uniform probability law on the source local cube. -/
def spatialPatchProbability (d : ℕ) : Measure (Covariate d) :=
  ((2 : ℝ≥0∞)^d)⁻¹ • volume.restrict (spatialPatchBox d)

instance spatialPatchProbability_isProbability (d : ℕ) : IsProbabilityMeasure (spatialPatchProbability d) := by
  constructor
  rw [spatialPatchProbability, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ, spatialPatchBox_volume]
  exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)

theorem spatialPatchProbability_le_volume (d : ℕ) : spatialPatchProbability d ≤ volume := by
  have hc : ((2 : ℝ≥0∞)^d)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr (one_le_pow₀ (by norm_num))
  intro S
  rw [spatialPatchProbability, Measure.smul_apply, smul_eq_mul]
  exact (mul_le_of_le_one_left (show 0 ≤ (volume.restrict (spatialPatchBox d)) S from zero_le) hc).trans (Measure.restrict_le_self S)

/-- Actual distinct-coordinate pair evaluation preserves the true independent product law. -/
theorem spatialPi_pair_preserving {J E : Type*} [Fintype J] [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (i j : J) (hij : i ≠ j) :
    MeasurePreserving (fun U : J → E => (U i, U j))
      (Measure.pi (fun _ : J => π)) (π.prod π) := by
  classical
  let e : Fin 2 ↪ J := ⟨![i,j], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩
  convert (measurePreserving_finTwoArrow π).comp (spatialPi_projection_preserving π e) using 1
  funext U
  simp [MeasurableEquiv.finTwoArrow, e]

/-- Genuine integration through an actual pair projection. -/
theorem spatialPi_pair_integral {J E : Type*} [Fintype J] [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (i j : J) (hij : i ≠ j)
    (F : E × E → ℝ) (hF : Measurable F) :
    (∫ U : J → E, F (U i, U j) ∂Measure.pi (fun _ : J => π)) = ∫ z, F z ∂π.prod π := by
  have hp := spatialPi_pair_preserving π i j hij
  exact (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm.trans
    (congrArg (fun μ : Measure (E × E) => ∫ z, F z ∂μ) hp.map_eq)

/-- A true probability spatial law dominated by volume has the dimension-scaled pair exponential integral. -/
theorem spatial_probability_pair_exponential_integral_le {d : ℕ} (hd : 0 < d)
    (π : Measure (Covariate d)) [IsProbabilityMeasure π] (hπ : π ≤ volume)
    {T : ℝ} (hT : 0 < T) :
    (∫ xy : Covariate d × Covariate d, Real.exp (-(T * exactEuclideanDistance xy.1 xy.2)) ∂π.prod π) ≤
      spatialExponentialConstant d / T^d := by
  have hm : Measurable (fun xy : Covariate d × Covariate d =>
      Real.exp (-(T * exactEuclideanDistance xy.1 xy.2))) :=
    (exactEuclideanDistance_continuous (d := d) |>.const_mul T |>.neg |>.rexp).measurable
  have hi : Integrable (fun xy : Covariate d × Covariate d =>
      Real.exp (-(T * exactEuclideanDistance xy.1 xy.2))) (π.prod π) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun xy => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hT.le (exactEuclideanDistance_nonneg _ _))))
  rw [integral_prod _ hi]
  have hb (x : Covariate d) :
      (∫ y, Real.exp (-(T*exactEuclideanDistance x y)) ∂π) ≤ spatialExponentialConstant d / T^d :=
    (integral_mono_measure hπ (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
      (exactEuclideanDistance_exponential_integrable hd hT x)).trans_eq
        (exactEuclideanDistance_exponential_integral hd hT x)
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono hi.integral_prod_left (integrable_const _) hb

/-- Genuine factorization of functions of two disjoint iid coordinate pairs. -/
theorem spatialPi_two_pair_functions_factor {J E : Type*} [Fintype J] [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (q : Fin 4 ↪ J)
    (F : E × E → ℝ) (hF : Measurable F) :
    (∫ U : J → E, F (U (q 0), U (q 1)) * F (U (q 2), U (q 3))
      ∂Measure.pi (fun _ : J => π)) = (∫ xy, F xy ∂π.prod π)^2 := by
  have hc : iIndepFun (fun j (U : J → E) => U j) (Measure.pi (fun _ : J => π)) :=
    iIndepFun_pi (X := fun _ : J => (id : E → E)) (fun _ => aemeasurable_id)
  have hne (i j : Fin 4) (h : i ≠ j) : q i ≠ q j := fun he => h (q.injective he)
  have hind0 := hc.indepFun_prodMk_prodMk (fun j => measurable_pi_apply j)
    (q 0) (q 1) (q 2) (q 3)
    (hne 0 2 (by decide)) (hne 0 3 (by decide))
    (hne 1 2 (by decide)) (hne 1 3 (by decide))
  have hind := hind0.comp hF hF
  have hfm : Measurable (fun U : J → E => F (U (q 0), U (q 1))) :=
    hF.comp ((measurable_pi_apply (q 0)).prodMk (measurable_pi_apply (q 1)))
  have hgm : Measurable (fun U : J → E => F (U (q 2), U (q 3))) :=
    hF.comp ((measurable_pi_apply (q 2)).prodMk (measurable_pi_apply (q 3)))
  have he := hind.integral_mul_eq_mul_integral hfm.aestronglyMeasurable hgm.aestronglyMeasurable
  change (∫ U : J → E, F (U (q 0), U (q 1)) * F (U (q 2), U (q 3))
    ∂Measure.pi (fun _ : J => π)) = _ at he
  simp only [Function.comp_def] at he
  rw [spatialPi_pair_integral π (q 0) (q 1) (hne 0 1 (by decide)) F hF,
    spatialPi_pair_integral π (q 2) (q 3) (hne 2 3 (by decide)) F hF] at he
  simpa only [pow_two] using he

/-- Exact independence of the two actual disjoint spatial exponential pair kernels. -/
theorem spatialPi_two_pairs_integral_factor {J : Type*} [Fintype J]
    {d : ℕ} (π : Measure (Covariate d)) [IsProbabilityMeasure π]
    (q : Fin 4 ↪ J) (T : ℝ) :
    (∫ U : J → Covariate d,
      Real.exp (-(T * (exactEuclideanDistance (U (q 0)) (U (q 1)) +
        exactEuclideanDistance (U (q 2)) (U (q 3))))) ∂Measure.pi (fun _ : J => π)) =
      (∫ xy : Covariate d × Covariate d, Real.exp (-(T * exactEuclideanDistance xy.1 xy.2)) ∂π.prod π)^2 := by
  have hpair : Measurable (fun xy : Covariate d × Covariate d => Real.exp (-(T*exactEuclideanDistance xy.1 xy.2))) :=
    (exactEuclideanDistance_continuous (d := d) |>.const_mul T |>.neg |>.rexp).measurable
  have he := spatialPi_two_pair_functions_factor π q _ hpair
  simp_rw [← Real.exp_add] at he
  simp_rw [show ∀ a b : ℝ, -(T*a) + -(T*b) = -(T*(a+b)) by intros; ring] at he
  exact he

end NearlyMinimax
