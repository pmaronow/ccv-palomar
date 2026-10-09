module

public import NearlyMinimax.PairWindowMoments


@[expose] public section

/-! Same-cell score moments specialized to the original statistical model. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

def regularObservationLabel {d : ℕ} (k : ℕ) (hk : 0 < k) :
    Observation d → (Fin d → Fin k) := fun z => regularGridCell k hk z.1

theorem regularObservationLabel_measurable {d : ℕ} (k : ℕ) (hk : 0 < k) :
    Measurable (regularObservationLabel (d := d) k hk) :=
  (regular_grid_cell_measurable k hk).comp measurable_fst

theorem regularObservationLabel_fiber {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) :
    (regularObservationLabel (d := d) k hk) ⁻¹' {c} =
      Prod.fst ⁻¹' ((regularGridCell k hk) ⁻¹' {c}) := rfl

theorem regularObservationLabel_mass {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) :
    (observationLaw θ).real ((regularObservationLabel k hk) ⁻¹' {c}) =
      regularGridProbability θ k hk c := by
  have hA : MeasurableSet ((regularGridCell k hk) ⁻¹' {c}) :=
    (measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk)
  exact (observationLaw_fst_measurePreserving C θ hθ).measureReal_preimage
    hA.nullMeasurableSet

def regularPairScore {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k) :
    Observation d × Observation d → ℝ :=
  pairWindowScore (regularObservationLabel k hk) Prod.snd θ.variance

theorem regularPairScore_memLp {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    MemLp (regularPairScore θ k hk) 2 ((observationLaw θ).prod (observationLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  exact pairWindowScore_memLp (observationLaw θ) _
    (regularObservationLabel_measurable k hk) Prod.snd measurable_snd θ.variance
    (observationLaw_response_fourth_integrable C θ hθ)

theorem regularPairScore_kernel_energy_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (∫ z, regularPairScore θ k hk z ^ 2
      ∂(observationLaw θ).prod (observationLaw θ)) ≤
      (8 * responseFourthBound C + 2 * θ.variance ^ 2) *
        regularGridCollisionMass θ k hk := by
  let := observationLaw_isProbability C θ hθ
  have hh := pairWindowScore_energy_le (observationLaw θ) _
    (regularObservationLabel_measurable k hk) Prod.snd measurable_snd
    θ.variance (responseFourthBound C)
    (observationLaw_response_fourth_integrable C θ hθ) (fun c => by
      rw [regularObservationLabel_mass C θ hθ k hk c,
        regularObservationLabel_fiber k hk c]
      have hm := observationLaw_localized_fourth_integral_le C θ hθ
        ((regularGridCell k hk) ⁻¹' {c})
        ((measurableSet_singleton _).preimage (regular_grid_cell_measurable k hk))
      exact hm)
  simpa only [regularObservationLabel_mass C θ hθ k hk,
    regularPairScore, regularGridCollisionMass] using hh

theorem regularPairScore_row_energy_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (∫ x, (∫ y, regularPairScore θ k hk (x, y) ∂observationLaw θ) ^ 2
      ∂observationLaw θ) ≤
      2 * (C.densityUpper / (k : ℝ) ^ d) ^ 2 *
        (responseFourthBound C + (|θ.variance| + responseSecondBound C) ^ 2) := by
  let := observationLaw_isProbability C θ hθ
  let := designLaw_isProbability C θ hθ
  have hρ : 0 < C.densityUpper := (by norm_num : (0 : ℝ) < 1).trans C.one_lt_densityUpper
  have hg : (∫ z : Observation d, z.2 ^ 4 ∂observationLaw θ) ≤ responseFourthBound C := by
    simpa using observationLaw_localized_fourth_integral_le C θ hθ Set.univ MeasurableSet.univ
  apply pairWindowScore_row_energy_le (observationLaw θ) _
    (regularObservationLabel_measurable k hk) Prod.snd measurable_snd
    θ.variance (responseSecondBound C) (responseFourthBound C)
    (C.densityUpper / (k : ℝ) ^ d) (responseSecondBound_pos C).le
    (by positivity) (observationLaw_response_memLp_two C θ hθ).integrable_sq
    (observationLaw_response_fourth_integrable C θ hθ) hg
  · intro c
    rw [regularObservationLabel_mass C θ hθ k hk c,
      regularObservationLabel_fiber k hk c]
    have hm := observationLaw_localized_second_integral_le C θ hθ
      ((regularGridCell k hk) ⁻¹' {c})
      ((measurableSet_singleton _).preimage (regular_grid_cell_measurable k hk))
    exact hm
  · intro c
    rw [regularObservationLabel_mass C θ hθ k hk c]
    exact regularGridProbability_cap C θ hθ k hk c

/-- The regression, evaluated at the observed covariate, is genuinely L². -/
theorem observationLaw_regression_memLp_two {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    MemLp (fun z : Observation d => θ.regression z.1) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  apply MemLp.of_bound (hθ.2.1.comp measurable_fst).aestronglyMeasurable C.holderBound
  filter_upwards [(observationLaw_fst_measurePreserving C θ hθ).quasiMeasurePreserving.ae
    (designLaw_cube_ae θ)] with z hz
  simpa only [Real.norm_eq_abs, Function.comp_def] using
    admissible_regression_value_bound C θ hθ z.1 hz

theorem designLaw_regression_memLp_two {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    MemLp θ.regression 2 (designLaw θ) := by
  let := designLaw_isProbability C θ hθ
  apply MemLp.of_bound hθ.2.1.aestronglyMeasurable C.holderBound
  filter_upwards [designLaw_cube_ae θ] with x hx
  simpa only [Real.norm_eq_abs] using admissible_regression_value_bound C θ hθ x hx

theorem observationLaw_covariate_integral {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (g : Covariate d → ℝ) (hg : Measurable g) :
    (∫ z, g z.1 ∂observationLaw θ) = ∫ x, g x ∂designLaw θ := by
  have hh := integral_map (μ := observationLaw θ) measurable_fst.aemeasurable
    hg.aestronglyMeasurable
  rw [(observationLaw_fst_measurePreserving C θ hθ).map_eq] at hh
  exact hh.symm

theorem observationLaw_localized_regression_first {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (A : Set (Covariate d)) (hA : MeasurableSet A) :
    (∫ z, (Prod.fst ⁻¹' A).indicator (Prod.snd : Observation d → ℝ) z
      ∂observationLaw θ) =
      ∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => θ.regression z.1) z
        ∂observationLaw θ := by
  rw [observationLaw_localized_first_integral C θ hθ A hA]
  have hh := observationLaw_covariate_integral C θ hθ (A.indicator θ.regression)
    (hθ.2.1.indicator hA)
  have heq : (fun z : Observation d => (Prod.fst ⁻¹' A).indicator
      (fun z => θ.regression z.1) z) = (fun z => A.indicator θ.regression z.1) := by
    funext z
    by_cases hz : z.1 ∈ A <;> simp [Set.indicator, hz]
  rw [heq]
  exact hh.symm

theorem observationLaw_localized_regression_second {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (A : Set (Covariate d)) (hA : MeasurableSet A) :
    (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ 2) z
      ∂observationLaw θ) =
      (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => θ.regression z.1 ^ 2) z
        ∂observationLaw θ) + θ.variance * (designLaw θ).real A := by
  rw [observationLaw_localized_second_integral C θ hθ A hA]
  have hh := observationLaw_covariate_integral C θ hθ
    (A.indicator (fun x => θ.regression x ^ 2)) ((hθ.2.1.pow_const 2).indicator hA)
  have hc : (∫ z : Observation d, (Prod.fst ⁻¹' A).indicator
      (fun z => θ.regression z.1 ^ 2) z ∂observationLaw θ) =
      ∫ x, A.indicator (fun x => θ.regression x ^ 2) x ∂designLaw θ := by
    have heq : (fun z : Observation d => (Prod.fst ⁻¹' A).indicator
        (fun z => θ.regression z.1 ^ 2) z) =
        (fun z => A.indicator (fun x => θ.regression x ^ 2) z.1) := by
      funext z
      by_cases hz : z.1 ∈ A <;> simp [Set.indicator, hz]
    rw [heq]
    exact hh
  rw [hc, integral_indicator hA, integral_indicator hA]
  let := designLaw_isProbability C θ hθ
  rw [integral_add (designLaw_regression_memLp_two C θ hθ).integrable_sq.restrict
      (integrable_const θ.variance), integral_const]
  simp only [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul]
  ring

/-- Conditional centering makes the score's population mean exactly the
same-cell squared regression increment. -/
theorem regularPairScore_mean_eq_signal {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (∫ z, regularPairScore θ k hk z
      ∂(observationLaw θ).prod (observationLaw θ)) =
      ∫ z, pairWindowScore (regularObservationLabel k hk)
        (fun z : Observation d => θ.regression z.1) 0 z
        ∂(observationLaw θ).prod (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  rw [regularPairScore,
    pairWindowScore_integral (observationLaw θ) _
      (regularObservationLabel_measurable k hk) Prod.snd measurable_snd θ.variance
      (observationLaw_response_memLp_two C θ hθ),
    pairWindowScore_integral (observationLaw θ) _
      (regularObservationLabel_measurable k hk)
      (fun z : Observation d => θ.regression z.1) (hθ.2.1.comp measurable_fst) 0
      (observationLaw_regression_memLp_two C θ hθ)]
  apply Finset.sum_congr rfl
  intro c hc
  let A := (regularGridCell k hk) ⁻¹' {c}
  have hA : MeasurableSet A :=
    (measurableSet_singleton _).preimage (regular_grid_cell_measurable k hk)
  have hfirst := observationLaw_localized_regression_first C θ hθ A hA
  have hsecond := observationLaw_localized_regression_second C θ hθ A hA
  rw [regularObservationLabel_mass C θ hθ k hk c,
    regularObservationLabel_fiber k hk c, hfirst, hsecond]
  dsimp [A, regularGridProbability]
  ring

def regularGridOscillation {d : ℕ} (C : ModelConstants d) (k : ℕ) : ℝ :=
  (2 * ((d : ℝ) + 1) * C.holderBound) *
    (Real.sqrt d * (1 / (k : ℝ))) ^ elementarySmoothness C

theorem regularPairScore_mean_nonneg {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    0 ≤ ∫ z, regularPairScore θ k hk z
      ∂(observationLaw θ).prod (observationLaw θ) := by
  rw [regularPairScore_mean_eq_signal C θ hθ k hk]
  apply integral_nonneg
  intro z
  unfold pairWindowScore
  split_ifs <;> simp only [sub_zero] <;> positivity

theorem regularPairSignal_integrable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    Integrable (pairWindowScore (regularObservationLabel k hk)
      (fun z : Observation d => θ.regression z.1) 0)
      ((observationLaw θ).prod (observationLaw θ)) := by
  let := observationLaw_isProbability C θ hθ
  let R := fun z : Observation d => θ.regression z.1
  have h2 := (observationLaw_regression_memLp_two C θ hθ).integrable_sq
  have hd : Integrable (fun z : Observation d × Observation d =>
      R z.1 ^ 2 + R z.2 ^ 2) ((observationLaw θ).prod (observationLaw θ)) :=
    (h2.comp_fst _).add (h2.comp_snd _)
  apply hd.mono'
    (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk)
      R (hθ.2.1.comp measurable_fst) 0).aestronglyMeasurable
  filter_upwards [] with z
  simpa only [abs_zero, add_zero, Real.norm_eq_abs] using
    pairWindowScore_abs_le (regularObservationLabel k hk) R 0 z

theorem regularPairScore_mean_le {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) :
    (∫ z, regularPairScore θ k hk z
      ∂(observationLaw θ).prod (observationLaw θ)) ≤
      (regularGridOscillation C k ^ 2 / 2) * regularGridCollisionMass θ k hk := by
  let := observationLaw_isProbability C θ hθ
  have hcube := (observationLaw_fst_measurePreserving C θ hθ).quasiMeasurePreserving.ae
    (designLaw_cube_ae θ)
  rw [regularPairScore_mean_eq_signal C θ hθ k hk]
  have hD := (sameLabelKernel_memLp (observationLaw θ) _
    (regularObservationLabel_measurable k hk)).integrable (by norm_num)
  have hb : (∫ z, pairWindowScore (regularObservationLabel k hk)
      (fun z : Observation d => θ.regression z.1) 0 z
      ∂(observationLaw θ).prod (observationLaw θ)) ≤
      ∫ z, (regularGridOscillation C k ^ 2 / 2) *
        sameLabelKernel (regularObservationLabel k hk) z
        ∂(observationLaw θ).prod (observationLaw θ) := by
    apply integral_mono_ae (regularPairSignal_integrable C θ hθ k hk)
      (hD.const_mul _)
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcube,
      Measure.quasiMeasurePreserving_snd.ae hcube] with z hz1 hz2
    by_cases he : regularObservationLabel k hk z.1 = regularObservationLabel k hk z.2
    · have hm := regular_grid_same_cell_regression_difference C θ hθ k hk
        z.1.1 z.2.1 hz1 hz2 he
      have hs := pow_le_pow_left₀ (abs_nonneg _) hm 2
      simp only [sq_abs] at hs
      simp only [pairWindowScore, sameLabelKernel, ite_eq_left he, sub_zero, mul_one]
      exact div_le_div_of_nonneg_right hs (by norm_num)
    · simp [pairWindowScore, sameLabelKernel, he]
  rw [integral_const_mul, sameLabelKernel_integral (observationLaw θ) _
    (regularObservationLabel_measurable k hk)] at hb
  simpa only [regularObservationLabel_mass C θ hθ k hk, regularGridCollisionMass] using hb

end NearlyMinimax
