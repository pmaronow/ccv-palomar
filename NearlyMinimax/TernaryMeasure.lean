module

public import NearlyMinimax.Model
public import NearlyMinimax.Ternary
public import NearlyMinimax.Moments


@[expose] public section

/-! The finite response calculations are genuine integrals against an actual
probability measure on the real response space, and instantiate the model. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace NearlyMinimax

def ternaryMeasure (a f V : ℝ) : Measure ℝ :=
  ∑ y : Fin 3, ENNReal.ofReal (ternaryMass a f V y) •
    Measure.dirac (ternaryValue a y)

theorem ternaryMeasure_integrable (a f V : ℝ) (g : ℝ → ℝ) :
    Integrable g (ternaryMeasure a f V) := by
  unfold ternaryMeasure
  apply integrable_finset_sum_measure.mpr
  intro y hy
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem ternaryMeasure_isProbability (a f V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) :
    IsProbabilityMeasure (ternaryMeasure a f V) := by
  constructor
  simp only [ternaryMeasure, Measure.finset_sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hp y), ternary_normalized a f V ha]
  simp

theorem ternaryMeasure_integral (a f V : ℝ)
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) (g : ℝ → ℝ) :
    (∫ y, g y ∂ternaryMeasure a f V) = ternaryExpectation a f V g := by
  unfold ternaryMeasure
  rw [integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (hp _), ternaryExpectation]
  · intro y hy
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem ternaryMeasure_mean (a f V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) :
    (∫ y, y ∂ternaryMeasure a f V) = f := by
  rw [ternaryMeasure_integral a f V hp]
  exact ternary_mean a f V ha

theorem ternaryMeasure_variance (a f V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) :
    (∫ y, (y - f) ^ 2 ∂ternaryMeasure a f V) = V := by
  rw [ternaryMeasure_integral a f V hp]
  exact ternary_variance a f V ha

theorem ternaryMeasure_fourthMoment (a f V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a f V y) :
    (∫ y, (y - f) ^ 4 ∂ternaryMeasure a f V) =
      a ^ 2 * V + (6 * V - 3 * a ^ 2) * f ^ 2 + 3 * f ^ 4 := by
  rw [ternaryMeasure_integral a f V hp]
  exact ternary_fourth_central_moment a f V ha

theorem unitCube_eq_pi (d : ℕ) :
    unitCube d = Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
  ext x
  simp only [unitCube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc]

theorem cubeVolume_univ (d : ℕ) : cubeVolume d Set.univ = 1 := by
  rw [cubeVolume, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, unitCube_eq_pi,
    volume_pi, Measure.pi_pi]
  simp

theorem cubeVolume_isProbability (d : ℕ) : IsProbabilityMeasure (cubeVolume d) :=
  ⟨cubeVolume_univ d⟩

theorem multiPartial_zero {d : ℕ} (γ : Fin d → ℕ) :
    multiPartial (fun _ : Covariate d => (0 : ℝ)) γ = 0 := by
  have hc (i : Fin d) : coordinatePartial i (fun _ : Covariate d => (0 : ℝ)) = 0 := by
    funext x
    simp [coordinatePartial]
  unfold multiPartial
  generalize ((List.finRange d).flatMap (fun i => List.replicate (γ i) i)) = xs
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      rw [List.foldl_cons, hc]
      convert ih using 1

theorem holderNorm_zero {d : ℕ} (U : Set (Covariate d)) (ℓ : ℕ) (α : ℝ) :
    holderNorm U (fun _ : Covariate d => (0 : ℝ)) ℓ α = 0 := by
  simp [holderNorm, multiPartial_zero, derivativeSup, holderSeminorm]

def uniformZeroParameter (d : ℕ) (a V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) : RegressionParameter d := by
  letI := ternaryMeasure_isProbability a 0 V ha hp
  exact {
    density := fun _ => 1
    regression := fun _ => 0
    variance := V
    errors := Kernel.const _ (ternaryMeasure a 0 V)
    errors_markov := inferInstance }

theorem uniformZeroParameter_admissible {d : ℕ} (C : ModelConstants d)
    (a V : ℝ) (ha : 0 < a) (hV : C.varianceLower ≤ V)
    (hVupper : V ≤ C.varianceUpper) (hVa : V < a ^ 2)
    (hfourth : a ^ 2 * V ≤ C.fourthBound) :
    ∃ θ : RegressionParameter d, Admissible C θ ∧ θ.variance = V := by
  have hVp : 0 < V := C.varianceLower_pos.trans_le hV
  have hp : ∀ y, 0 ≤ ternaryMass a 0 V y := by
    apply fun y => (ternary_mass_positive a 0 V ha (by simpa using hVa)
      (by simpa using hVp) y).le
  let θ := uniformZeroParameter d a V ha.ne' hp
  refine ⟨θ, ?_, rfl⟩
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

/-- The paper's numerical assumptions ensure the parameter class is nonempty. -/
theorem admissible_nonempty {d : ℕ} (C : ModelConstants d) :
    ∃ θ : RegressionParameter d, Admissible C θ := by
  let v := C.varianceLower
  let t := (v + C.fourthBound / v) / 2
  have hv : 0 < v := C.varianceLower_pos
  have hdiv : v < C.fourthBound / v := by
    apply (lt_div_iff₀ hv).mpr
    simpa [v, pow_two] using C.fourth_margin
  have ht : 0 < t := by dsimp [t]; linarith
  have hvt : v < t := by dsimp [t]; linarith
  have htv : t * v ≤ C.fourthBound := by
    have he : t * v = (v ^ 2 + C.fourthBound) / 2 := by
      dsimp [t]
      field_simp
    rw [he]
    nlinarith [C.fourth_margin]
  obtain ⟨θ, hθ, _⟩ := uniformZeroParameter_admissible C (Real.sqrt t) v
    (Real.sqrt_pos.mpr ht) le_rfl C.variance_interval.le
    (by simpa [Real.sq_sqrt ht.le] using hvt)
    (by simpa [Real.sq_sqrt ht.le] using htv)
  exact ⟨θ, hθ⟩

/-- The conditional fourth-moment constraint gives the effective variance bound. -/
theorem admissible_variance_sq_le_fourth {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    θ.variance ^ 2 ≤ C.fourthBound := by
  letI := designLaw_isProbability C θ hθ
  obtain ⟨x, hx⟩ := hθ.2.2.2.2.2.2.2.exists
  obtain ⟨_, _, hi4, _, hi2, hbound⟩ := hx
  have hi4' : Integrable (fun u : ℝ => (u ^ 2) ^ 2) (θ.errors x) := by
    convert hi4 using 1
    funext u
    ring
  have hl2 : MemLp (fun u : ℝ => u ^ 2) 2 (θ.errors x) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr hi4'
  have hj := second_moment_sq_le_fourth_moment hl2
  rw [hi2] at hj
  exact hj.trans hbound

theorem admissible_variance_effective_interval {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    θ.variance ∈ Icc C.varianceLower (min C.varianceUpper (Real.sqrt C.fourthBound)) := by
  exact ⟨hθ.2.2.2.2.2.1, le_min hθ.2.2.2.2.2.2.1
    (Real.le_sqrt_of_sq_le (admissible_variance_sq_le_fourth C θ hθ))⟩

theorem effective_variance_interval_nondegenerate {d : ℕ} (C : ModelConstants d) :
    C.varianceLower < min C.varianceUpper (Real.sqrt C.fourthBound) := by
  apply lt_min C.variance_interval
  have h4pos : 0 < C.fourthBound := (sq_nonneg _).trans_lt C.fourth_margin
  have he := Real.sq_sqrt h4pos.le
  nlinarith [Real.sqrt_nonneg C.fourthBound, C.varianceLower_pos, C.fourth_margin]

/-- The admissible submodel used for the parametric lower bound is a genuine
continuous uniform design independent of the ternary response. -/
theorem uniformZeroParameter_observationLaw (d : ℕ) (a V : ℝ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) :
    observationLaw (uniformZeroParameter d a V ha hp) =
      (cubeVolume d).prod (ternaryMeasure a 0 V) := by
  letI := cubeVolume_isProbability d
  letI := ternaryMeasure_isProbability a 0 V ha hp
  unfold observationLaw designLaw uniformZeroParameter
  simp only [ENNReal.ofReal_one, withDensity_const, one_smul, zero_add]
  change ((cubeVolume d).compProd (Kernel.const _ (ternaryMeasure a 0 V))).map id = _
  rw [Measure.map_id, Measure.compProd_const]

end NearlyMinimax
