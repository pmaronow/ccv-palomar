module

public import NearlyMinimax.PairWindowModel
public import NearlyMinimax.StabilizedRatioRisk
public import NearlyMinimax.PairGridChoice


@[expose] public section

/-! Actual Borel pair-difference estimators for the original model.
The low-smoothness branch of Proposition elementary-upper is proved from
the actual sampling measure, rather than an assumed risk envelope. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def elementaryDenominatorKernel {d : ℕ} (k : ℕ) (hk : 0 < k) :
    Observation d × Observation d → ℝ := sameLabelKernel (regularObservationLabel k hk)

def elementaryNumeratorKernel {d : ℕ} (k : ℕ) (hk : 0 < k) :
    Observation d × Observation d → ℝ :=
  pairWindowScore (regularObservationLabel k hk) Prod.snd 0

def elementaryNumerator {d : ℕ} (n k : ℕ) (hk : 0 < k) :
    (Fin n → Observation d) → ℝ :=
  PairUStatistic.pairAverage n (elementaryNumeratorKernel k hk)

def elementaryDenominator {d : ℕ} (n k : ℕ) (hk : 0 < k) :
    (Fin n → Observation d) → ℝ :=
  PairUStatistic.pairAverage n (elementaryDenominatorKernel k hk)

def elementaryFloor (d k : ℕ) : ℝ := 1 / (2 * (k : ℝ) ^ d)

def elementaryGridEstimator {d : ℕ} (C : ModelConstants d) (n k : ℕ) (hk : 0 < k) :
    Estimator d n :=
  ⟨stabilizedRatio C.varianceLower C.varianceUpper (elementaryFloor d k)
      (elementaryNumerator n k hk) (elementaryDenominator n k hk),
    stabilizedRatio_measurable _ _ _
      (PairUStatistic.pairAverage_measurable n
        (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk)
          Prod.snd measurable_snd 0))
      (PairUStatistic.pairAverage_measurable n
        (sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk)))⟩

theorem pairAverage_sub_mul {E : Type*} [MeasurableSpace E] (n : ℕ)
    (K L : E × E → ℝ) (c : ℝ) (x : Fin n → E) :
    PairUStatistic.pairAverage n (fun z => K z - c * L z) x =
      PairUStatistic.pairAverage n K x - c * PairUStatistic.pairAverage n L x := by
  unfold PairUStatistic.pairAverage
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem elementary_score_identity {d : ℕ} (θ : RegressionParameter d)
    (n k : ℕ) (hk : 0 < k) (z : Fin n → Observation d) :
    elementaryNumerator n k hk z - θ.variance * elementaryDenominator n k hk z =
      PairUStatistic.pairAverage n (regularPairScore θ k hk) z := by
  have he : regularPairScore θ k hk =
      (fun z => elementaryNumeratorKernel k hk z - θ.variance *
        elementaryDenominatorKernel k hk z) := by
    funext z
    unfold regularPairScore elementaryNumeratorKernel elementaryDenominatorKernel
      pairWindowScore sameLabelKernel
    split_ifs <;> ring
  rw [he, pairAverage_sub_mul]
  rfl

theorem elementary_denominator_mean {d n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (hn : 2 ≤ n)
    (k : ℕ) (hk : 0 < k) :
    (∫ z, elementaryDenominator n k hk z ∂sampleLaw θ n) =
      regularGridCollisionMass θ k hk := by
  let := observationLaw_isProbability C θ hθ
  let := sampleLaw_isProbability C θ hθ n
  have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  have hp := fun i => measurePreserving_eval (fun _ : Fin n => observationLaw θ) i
  have he := PairUStatistic.pairAverage_integral hn
    (fun i (z : Fin n → Observation d) => z i) hi hp
    (sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk))
    (sameLabelKernel_memLp (observationLaw θ) _ (regularObservationLabel_measurable k hk))
  rw [sameLabelKernel_integral (observationLaw θ) _
    (regularObservationLabel_measurable k hk)] at he
  simpa only [elementaryDenominator, elementaryDenominatorKernel, sampleLaw,
    regularObservationLabel_mass C θ hθ k hk, regularGridCollisionMass] using he

theorem elementary_denominator_fluctuation_le {d n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (hn : 2 ≤ n)
    (k : ℕ) (hk : 0 < k) :
    (∫ z, (elementaryDenominator n k hk z - regularGridCollisionMass θ k hk) ^ 2
      ∂sampleLaw θ n) ≤
      4 / (n : ℝ) * (C.densityUpper / (k : ℝ) ^ d) ^ 2 +
      2 / ((n : ℝ) * (n - 1 : ℕ)) * (C.densityUpper / (k : ℝ) ^ d) := by
  let := observationLaw_isProbability C θ hθ
  let := sampleLaw_isProbability C θ hθ n
  have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  have hp := fun i => measurePreserving_eval (fun _ : Fin n => observationLaw θ) i
  have he := PairUStatistic.pairAverage_centered_sq_le hn
    (fun i (z : Fin n → Observation d) => z i) hi hp
    (sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk))
    (sameLabelKernel_memLp (observationLaw θ) _ (regularObservationLabel_measurable k hk))
    (fun x y => by exact (sameLabelKernel_symmetric _
      (regularObservationLabel_measurable k hk) (x, y)).symm)
  change (∫ z, (elementaryDenominator n k hk z -
      ∫ p, sameLabelKernel (regularObservationLabel k hk) p
        ∂(observationLaw θ).prod (observationLaw θ)) ^ 2 ∂sampleLaw θ n) ≤ _ at he
  rw [sameLabelKernel_integral (observationLaw θ) _
    (regularObservationLabel_measurable k hk)] at he
  simp only [PairUStatistic.rowIntegral] at he
  rw [sameLabelKernel_row_square_integral (observationLaw θ) _
      (regularObservationLabel_measurable k hk),
    sameLabelKernel_square_integral (observationLaw θ) _
      (regularObservationLabel_measurable k hk)] at he
  simp only [regularObservationLabel_mass C θ hθ k hk] at he
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hr := regularGridCollisionRowEnergy_upper C θ hθ k hk
  have hm := regularGridCollisionMass_upper C θ hθ k hk
  exact he.trans (add_le_add
    (mul_le_mul_of_nonneg_left hr (by positivity))
    (mul_le_mul_of_nonneg_left hm (by positivity)))

def elementaryRowBound {d : ℕ} (C : ModelConstants d) : ℝ :=
  responseFourthBound C + (C.varianceUpper + responseSecondBound C) ^ 2

def elementaryKernelBound {d : ℕ} (C : ModelConstants d) : ℝ :=
  8 * responseFourthBound C + 2 * C.varianceUpper ^ 2

theorem elementaryRowBound_pos {d : ℕ} (C : ModelConstants d) :
    0 < elementaryRowBound C := by
  unfold elementaryRowBound
  exact add_pos_of_pos_of_nonneg (responseFourthBound_pos C) (sq_nonneg _)

theorem elementaryKernelBound_pos {d : ℕ} (C : ModelConstants d) :
    0 < elementaryKernelBound C := by
  unfold elementaryKernelBound
  have hh := responseFourthBound_pos C
  positivity

theorem elementary_score_fluctuation_le {d n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (hn : 2 ≤ n)
    (k : ℕ) (hk : 0 < k) :
    (∫ z, (PairUStatistic.pairAverage n (regularPairScore θ k hk) z -
      ∫ p, regularPairScore θ k hk p ∂(observationLaw θ).prod (observationLaw θ)) ^ 2
      ∂sampleLaw θ n) ≤
      8 / (n : ℝ) * (C.densityUpper / (k : ℝ) ^ d) ^ 2 * elementaryRowBound C +
      2 / ((n : ℝ) * (n - 1 : ℕ)) * elementaryKernelBound C *
        (C.densityUpper / (k : ℝ) ^ d) := by
  let := observationLaw_isProbability C θ hθ
  let := sampleLaw_isProbability C θ hθ n
  have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  have hp := fun i => measurePreserving_eval (fun _ : Fin n => observationLaw θ) i
  have he := PairUStatistic.pairAverage_centered_sq_le hn
    (fun i (z : Fin n → Observation d) => z i) hi hp
    (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk)
      Prod.snd measurable_snd θ.variance) (regularPairScore_memLp C θ hθ k hk)
    (pairWindowScore_symmetric _ Prod.snd θ.variance)
  have hV0 : 0 ≤ θ.variance := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hVU : θ.variance ≤ C.varianceUpper := hθ.2.2.2.2.2.2.1
  have hU0 : 0 ≤ C.varianceUpper := hV0.trans hVU
  have hC4 : 0 ≤ responseFourthBound C := (responseFourthBound_pos C).le
  have hC2 : 0 ≤ responseSecondBound C := (responseSecondBound_pos C).le
  have hr : (∫ x, (∫ y, regularPairScore θ k hk (x, y) ∂observationLaw θ) ^ 2
      ∂observationLaw θ) ≤
      2 * (C.densityUpper / (k : ℝ) ^ d) ^ 2 * elementaryRowBound C := by
    apply (regularPairScore_row_energy_le C θ hθ k hk).trans
    unfold elementaryRowBound
    rw [abs_of_nonneg hV0]
    gcongr
  have hq := regularGridCollisionMass_upper C θ hθ k hk
  have hq0 : 0 ≤ regularGridCollisionMass θ k hk := by
    unfold regularGridCollisionMass
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hker : (∫ z, regularPairScore θ k hk z ^ 2
      ∂(observationLaw θ).prod (observationLaw θ)) ≤
      elementaryKernelBound C * (C.densityUpper / (k : ℝ) ^ d) := by
    apply (regularPairScore_kernel_energy_le C θ hθ k hk).trans
    unfold elementaryKernelBound
    have hVsq : θ.variance ^ 2 ≤ C.varianceUpper ^ 2 :=
      pow_le_pow_left₀ hV0 hVU 2
    gcongr
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hb := he.trans (add_le_add
    (mul_le_mul_of_nonneg_left hr (by positivity))
    (mul_le_mul_of_nonneg_left hker (by positivity)))
  convert hb using 1 <;> first | rfl | ring

theorem elementary_score_second_moment_le {d n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (hn : 2 ≤ n)
    (k : ℕ) (hk : 0 < k) :
    (∫ z, (elementaryNumerator n k hk z - θ.variance * elementaryDenominator n k hk z) ^ 2
      ∂sampleLaw θ n) ≤
      8 / (n : ℝ) * (C.densityUpper / (k : ℝ) ^ d) ^ 2 * elementaryRowBound C +
      2 / ((n : ℝ) * (n - 1 : ℕ)) * elementaryKernelBound C *
        (C.densityUpper / (k : ℝ) ^ d) +
      ((regularGridOscillation C k ^ 2 / 2) * (C.densityUpper / (k : ℝ) ^ d)) ^ 2 := by
  let := observationLaw_isProbability C θ hθ
  let := sampleLaw_isProbability C θ hθ n
  have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  have hp := fun i => measurePreserving_eval (fun _ : Fin n => observationLaw θ) i
  have hS := PairUStatistic.pairAverage_memLp_two
    (fun i (z : Fin n → Observation d) => z i) hi hp (regularPairScore_memLp C θ hθ k hk)
  have hmean := PairUStatistic.pairAverage_integral hn
    (fun i (z : Fin n → Observation d) => z i) hi hp
    (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk)
      Prod.snd measurable_snd θ.variance) (regularPairScore_memLp C θ hθ k hk)
  let b := ∫ p, regularPairScore θ k hk p ∂(observationLaw θ).prod (observationLaw θ)
  change (∫ z, PairUStatistic.pairAverage n (regularPairScore θ k hk) z
    ∂sampleLaw θ n) = b at hmean
  have hEq : (∫ z, PairUStatistic.pairAverage n (regularPairScore θ k hk) z ^ 2
      ∂sampleLaw θ n) =
      (∫ z, (PairUStatistic.pairAverage n (regularPairScore θ k hk) z - b) ^ 2
        ∂sampleLaw θ n) + b ^ 2 := by
    have hv := variance_eq_sub hS
    have hc := variance_eq_integral hS.aemeasurable
    change variance (fun z => PairUStatistic.pairAverage n (regularPairScore θ k hk) z)
      (sampleLaw θ n) = (∫ z, PairUStatistic.pairAverage n (regularPairScore θ k hk) z ^ 2
        ∂sampleLaw θ n) - (∫ z, PairUStatistic.pairAverage n (regularPairScore θ k hk) z
          ∂sampleLaw θ n) ^ 2 at hv
    change variance (fun z => PairUStatistic.pairAverage n (regularPairScore θ k hk) z)
      (sampleLaw θ n) = ∫ z, (PairUStatistic.pairAverage n (regularPairScore θ k hk) z -
        ∫ z, PairUStatistic.pairAverage n (regularPairScore θ k hk) z ∂sampleLaw θ n) ^ 2
        ∂sampleLaw θ n at hc
    rw [hmean] at hv hc
    dsimp [b]
    linarith
  have hb0 : 0 ≤ b := regularPairScore_mean_nonneg C θ hθ k hk
  have hbm : b ≤ (regularGridOscillation C k ^ 2 / 2) *
      (C.densityUpper / (k : ℝ) ^ d) :=
    (regularPairScore_mean_le C θ hθ k hk).trans
      (mul_le_mul_of_nonneg_left (regularGridCollisionMass_upper C θ hθ k hk)
        (by positivity))
  have hbsq := pow_le_pow_left₀ hb0 hbm 2
  simp_rw [elementary_score_identity θ n k hk]
  rw [hEq]
  exact add_le_add (elementary_score_fluctuation_le C θ hθ hn k hk) hbsq

theorem elementary_grid_mse_explicit {d n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (hn : 2 ≤ n)
    (k : ℕ) (hk : 0 < k) :
    (∫ z, ((elementaryGridEstimator C n k hk).val z - θ.variance) ^ 2
      ∂sampleLaw θ n) ≤
      (64 * C.densityUpper ^ 2 * elementaryRowBound C +
        32 * C.densityUpper ^ 2 * C.varianceUpper ^ 2) / (n : ℝ) +
      (16 * C.densityUpper * (elementaryKernelBound C + C.varianceUpper ^ 2)) *
        (k : ℝ) ^ d / ((n : ℝ) * (n - 1 : ℕ)) +
      2 * C.densityUpper ^ 2 * regularGridOscillation C k ^ 4 := by
  let := observationLaw_isProbability C θ hθ
  let := sampleLaw_isProbability C θ hθ n
  have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  have hp := fun i => measurePreserving_eval (fun _ : Fin n => observationLaw θ) i
  have hmN : Measurable (elementaryNumerator (d := d) n k hk) :=
    PairUStatistic.pairAverage_measurable n
      (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk)
        Prod.snd measurable_snd 0)
  have hmD : Measurable (elementaryDenominator (d := d) n k hk) :=
    PairUStatistic.pairAverage_measurable n
      (sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk))
  have hS2 : MemLp (fun z => elementaryNumerator n k hk z -
      θ.variance * elementaryDenominator n k hk z) 2 (sampleLaw θ n) := by
    simp_rw [elementary_score_identity θ n k hk]
    exact PairUStatistic.pairAverage_memLp_two
      (fun i (z : Fin n → Observation d) => z i) hi hp (regularPairScore_memLp C θ hθ k hk)
  have hD2 : MemLp (elementaryDenominator n k hk) 2 (sampleLaw θ n) :=
    PairUStatistic.pairAverage_memLp_two
      (fun i (z : Fin n → Observation d) => z i) hi hp
      (sameLabelKernel_memLp (observationLaw θ) _ (regularObservationLabel_measurable k hk))
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
  have ha : 0 < elementaryFloor d k := by unfold elementaryFloor; positivity
  have hED : 2 * elementaryFloor d k ≤ regularGridCollisionMass θ k hk := by
    convert regularGridCollisionMass_lower C θ hθ k hk using 1
    unfold elementaryFloor
    field_simp
  have hV0 : 0 ≤ θ.variance := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hM := stabilized_ratio_mse_le (sampleLaw θ n) hmN hmD hS2 hD2
    ha hθ.2.2.2.2.2.1 hθ.2.2.2.2.2.2.1 hV0 hED
  have hS := elementary_score_second_moment_le C θ hθ hn k hk
  have hD := elementary_denominator_fluctuation_le C θ hθ hn k hk
  have hb := hM.trans (mul_le_mul_of_nonneg_left
    (add_le_add hS (mul_le_mul_of_nonneg_left hD (sq_nonneg _)))
    (by positivity : 0 ≤ 2 / elementaryFloor d k ^ 2))
  change (∫ z, ((elementaryGridEstimator C n k hk).val z - θ.variance) ^ 2
    ∂sampleLaw θ n) ≤ _ at hb
  convert hb using 1
  unfold elementaryFloor
  field_simp [hk0.ne', hn0.ne', hn1.ne', pow_ne_zero d hk0.ne']
  <;> ring

def elementaryBiasFactor {d : ℕ} (C : ModelConstants d) : ℝ :=
  (2 * ((d : ℝ) + 1) * C.holderBound) ^ 4 * (Real.sqrt d) ^ (4 * elementarySmoothness C)

theorem regularGridOscillation_fourth {d : ℕ} (C : ModelConstants d)
    (k : ℕ) (hk : 0 < k) :
    regularGridOscillation C k ^ 4 = elementaryBiasFactor C *
      (k : ℝ) ^ (-4 * elementarySmoothness C) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have he : ((Real.sqrt d * (1 / (k : ℝ))) ^ elementarySmoothness C) ^ 4 =
      (Real.sqrt d) ^ (4 * elementarySmoothness C) *
        (k : ℝ) ^ (-4 * elementarySmoothness C) := by
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (by positivity), mul_pow,
      ← Real.rpow_mul_natCast (Real.sqrt_nonneg _),
      ← Real.rpow_mul_natCast (by positivity : 0 ≤ 1 / (k : ℝ)),
      one_div, Real.inv_rpow hk0.le, ← Real.rpow_neg hk0.le]
    congr 2 <;> ring
  unfold regularGridOscillation elementaryBiasFactor
  rw [mul_pow, he]
  ring

def elementaryUpperConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  (64 * C.densityUpper ^ 2 * elementaryRowBound C +
    32 * C.densityUpper ^ 2 * C.varianceUpper ^ 2) +
    (16 * C.densityUpper * (elementaryKernelBound C + C.varianceUpper ^ 2)) +
    (2 * C.densityUpper ^ 2 * elementaryBiasFactor C)

theorem elementaryUpperConstant_pos {d : ℕ} (C : ModelConstants d) :
    0 < elementaryUpperConstant C := by
  have hU : 0 < C.densityUpper := (by norm_num : (0 : ℝ) < 1).trans C.one_lt_densityUpper
  have hR := elementaryRowBound_pos C
  have hK := elementaryKernelBound_pos C
  have hB : 0 ≤ elementaryBiasFactor C := by unfold elementaryBiasFactor; positivity
  unfold elementaryUpperConstant
  positivity

theorem elementary_grid_mse_le {d n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (hn : 2 ≤ n)
    (k : ℕ) (hk : 0 < k) :
    (∫ z, ((elementaryGridEstimator C n k hk).val z - θ.variance) ^ 2
      ∂sampleLaw θ n) ≤ elementaryUpperConstant C *
      (1 / (n : ℝ) + (k : ℝ) ^ d / ((n : ℝ) * (n - 1 : ℕ)) +
        (k : ℝ) ^ (-4 * elementarySmoothness C)) := by
  have hb := elementary_grid_mse_explicit C θ hθ hn k hk
  rw [regularGridOscillation_fourth C k hk] at hb
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hU : 0 < C.densityUpper := (by norm_num : (0 : ℝ) < 1).trans C.one_lt_densityUpper
  have hR := (elementaryRowBound_pos C).le
  have hK := (elementaryKernelBound_pos C).le
  have hB : 0 ≤ elementaryBiasFactor C := by unfold elementaryBiasFactor; positivity
  apply hb.trans
  let A := 64 * C.densityUpper ^ 2 * elementaryRowBound C +
    32 * C.densityUpper ^ 2 * C.varianceUpper ^ 2
  let B := 16 * C.densityUpper * (elementaryKernelBound C + C.varianceUpper ^ 2)
  let E := 2 * C.densityUpper ^ 2 * elementaryBiasFactor C
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have h1 := mul_le_mul_of_nonneg_right (show A ≤ A + B + E by linarith)
    (show 0 ≤ 1 / (n : ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_right (show B ≤ A + B + E by linarith)
    (show 0 ≤ (k : ℝ) ^ d / ((n : ℝ) * (n - 1 : ℕ)) by positivity)
  have h3 := mul_le_mul_of_nonneg_right (show E ≤ A + B + E by linarith)
    (Real.rpow_pos_of_pos hk0 (-4 * elementarySmoothness C)).le
  dsimp [A, B, E] at h1 h2 h3
  unfold elementaryUpperConstant
  convert add_le_add (add_le_add h1 h2) h3 using 1 <;> ring

theorem elementary_grid_risk_le {d n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (hn : 2 ≤ n)
    (k : ℕ) (hk : 0 < k) :
    meanSquaredRisk (elementaryGridEstimator C n k hk) θ ≤
      ENNReal.ofReal (elementaryUpperConstant C *
      (1 / (n : ℝ) + (k : ℝ) ^ d / ((n : ℝ) * (n - 1 : ℕ)) +
        (k : ℝ) ^ (-4 * elementarySmoothness C))) := by
  let := sampleLaw_isProbability C θ hθ n
  have hmN : Measurable (elementaryNumerator (d := d) n k hk) :=
    PairUStatistic.pairAverage_measurable n
      (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk)
        Prod.snd measurable_snd 0)
  have hmD : Measurable (elementaryDenominator (d := d) n k hk) :=
    PairUStatistic.pairAverage_measurable n
      (sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk))
  have hT := (stabilizedRatio_error_memLp (sampleLaw θ n)
    (a := elementaryFloor d k) hmN hmD hθ.2.2.2.2.2.1 hθ.2.2.2.2.2.2.1).integrable_sq
  change Integrable (fun z => ((elementaryGridEstimator C n k hk).val z - θ.variance) ^ 2)
    (sampleLaw θ n) at hT
  rw [meanSquaredRisk, ← ofReal_integral_eq_lintegral_ofReal hT
    (Eventually.of_forall (fun z => sq_nonneg _))]
  exact ENNReal.ofReal_mono (elementary_grid_mse_le C θ hθ hn k hk)

theorem elementary_grid_worstCaseRisk_le {d n : ℕ} (C : ModelConstants d)
    (hn : 2 ≤ n) (k : ℕ) (hk : 0 < k) :
    worstCaseRisk C (elementaryGridEstimator C n k hk) ≤
      ENNReal.ofReal (elementaryUpperConstant C *
      (1 / (n : ℝ) + (k : ℝ) ^ d / ((n : ℝ) * (n - 1 : ℕ)) +
        (k : ℝ) ^ (-4 * elementarySmoothness C))) := by
  apply iSup_le
  intro θ
  exact elementary_grid_risk_le C θ.val θ.property hn k hk

def elementaryChosenGrid {d : ℕ} (C : ModelConstants d) (n : ℕ) : ℕ :=
  lowSmoothnessGrid d (elementarySmoothness C) n

theorem elementaryChosenGrid_pos {d n : ℕ} (C : ModelConstants d) (hn : 0 < n) :
    0 < elementaryChosenGrid C n := by
  have hh := lowSmoothnessGrid_ge_four (d := d) (elementarySmoothness_pos C)
    (show 1 ≤ (n : ℝ) by exact_mod_cast hn)
  unfold elementaryChosenGrid
  omega

def elementaryEstimator {d : ℕ} (C : ModelConstants d) (n : ℕ) : Estimator d n :=
  if hn : 2 ≤ n then
    elementaryGridEstimator C n (elementaryChosenGrid C n)
      (elementaryChosenGrid_pos C (by omega))
  else constantEstimator d n C.varianceLower

def elementaryRMSConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  2 * Real.sqrt (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1)) +
    (C.varianceUpper - C.varianceLower)

theorem elementaryRMSConstant_pos {d : ℕ} (C : ModelConstants d) :
    0 < elementaryRMSConstant C := by
  unfold elementaryRMSConstant
  have hh : 0 < C.varianceUpper - C.varianceLower := sub_pos.mpr C.variance_interval
  have hs : 0 ≤ Real.sqrt (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1)) :=
    Real.sqrt_nonneg _
  linarith

theorem elementary_rms_upper_of_two_le {d n : ℕ} (C : ModelConstants d) (hn : 2 ≤ n) :
    (worstCaseRisk C (elementaryEstimator C n)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1)) *
        ((n : ℝ) ^ (-(1 / 2 : ℝ)) +
          (n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C)))) := by
  have hn0 : 0 < n := by omega
  have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR0 : 0 < (n : ℝ) := by positivity
  have hC := (elementaryUpperConstant_pos C).le
  let M := elementaryUpperConstant C *
    pairGridMSEEnvelope d (elementarySmoothness C) n
  have hM0 : 0 ≤ M := by
    dsimp [M, pairGridMSEEnvelope]
    have hnp : 0 < (n : ℝ) - 1 := by linarith
    positivity
  have he : worstCaseRisk C (elementaryEstimator C n) ≤ ENNReal.ofReal M := by
    unfold elementaryEstimator
    rw [dif_pos hn]
    have hh := elementary_grid_worstCaseRisk_le C hn (elementaryChosenGrid C n)
      (elementaryChosenGrid_pos C hn0)
    convert hh using 1
    dsimp [M, pairGridMSEEnvelope, elementaryChosenGrid]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hh := ENNReal.rpow_le_rpow he (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.ofReal_rpow_of_nonneg hM0 (by norm_num), ← Real.sqrt_eq_rpow] at hh
  have hs : Real.sqrt M ≤ Real.sqrt (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1)) *
      ((n : ℝ) ^ (-(1 / 2 : ℝ)) +
        (n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C))) := by
    apply pairGrid_rms_of_mse_bound (elementarySmoothness_pos C) hnR hC (Real.sqrt_nonneg M)
    exact le_of_eq (Real.sq_sqrt hM0)
  exact hh.trans (ENNReal.ofReal_mono hs)

/-- All sample sizes, including the one-observation constant estimator.
This gives the full low-smoothness branch of the paper's elementary upper. -/
theorem elementary_rms_upper {d n : ℕ} (C : ModelConstants d) (hn : 0 < n) :
    (worstCaseRisk C (elementaryEstimator C n)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (elementaryRMSConstant C * max
        ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        ((n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C)))) := by
  by_cases hn2 : 2 ≤ n
  · apply (elementary_rms_upper_of_two_le C hn2).trans
    apply ENNReal.ofReal_mono
    have hA : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    have hB : 0 ≤ (n : ℝ) ^
        (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C)) := by positivity
    have hs : 0 ≤ Real.sqrt (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1)) :=
      Real.sqrt_nonneg _
    have hdiam : 0 ≤ C.varianceUpper - C.varianceLower := sub_nonneg.mpr C.variance_interval.le
    have hmax := le_max_left ((n : ℝ) ^ (-(1 / 2 : ℝ)))
      ((n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C)))
    have hmax' := le_max_right ((n : ℝ) ^ (-(1 / 2 : ℝ)))
      ((n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C)))
    have hm0 := hA.trans hmax
    unfold elementaryRMSConstant
    nlinarith [mul_nonneg hdiam hm0]
  · have hn1 : n = 1 := by omega
    subst n
    unfold elementaryEstimator
    rw [dif_neg (by decide : ¬2 ≤ (1 : ℕ))]
    have he : worstCaseRisk C (constantEstimator d 1 C.varianceLower) ≤
        ENNReal.ofReal ((C.varianceUpper - C.varianceLower) ^ 2) := by
      apply iSup_le
      intro θ
      exact constantEstimator_risk_bound C θ.val θ.property
    have hh := ENNReal.rpow_le_rpow he (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (sub_nonneg.mpr C.variance_interval.le)] at hh
    apply hh.trans
    apply ENNReal.ofReal_mono
    simp only [Nat.cast_one, Real.one_rpow, max_self, mul_one]
    unfold elementaryRMSConstant
    have hs := Real.sqrt_nonneg (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1))
    linarith

theorem elementary_upper_low_smoothness {d n : ℕ} (C : ModelConstants d)
    (hs : C.smoothness ≤ 1) (hn : 0 < n) :
    (worstCaseRisk C (elementaryEstimator C n)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (elementaryRMSConstant C * max ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        ((n : ℝ) ^ (-4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)))) := by
  simpa only [elementarySmoothness, min_eq_left hs] using elementary_rms_upper C hn

end NearlyMinimax
