module

public import NearlyMinimax.PairWindowModel
public import NearlyMinimax.Risk
public import NearlyMinimax.PairGridChoice


@[expose] public section

/-! The actual Borel, stabilized same-cell pair-difference estimator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal
namespace NearlyMinimax.ElementaryPairSupport
set_option backward.isDefEq.respectTransparency false

def elementaryDenominator {d : ℕ} (n k : ℕ) (hk : 0 < k) :
    (Fin n → Observation d) → ℝ :=
  PairUStatistic.pairAverage n (sameLabelKernel (regularObservationLabel k hk))

def elementaryNumerator {d : ℕ} (n k : ℕ) (hk : 0 < k) :
    (Fin n → Observation d) → ℝ :=
  PairUStatistic.pairAverage n
    (pairWindowScore (regularObservationLabel k hk) Prod.snd 0)

def elementaryFloor (d k : ℕ) : ℝ := 1 / (2 * (k : ℝ) ^ d)

def elementaryPairEstimator {d : ℕ} (C : ModelConstants d) (n k : ℕ) (hk : 0 < k) :
    Estimator d n :=
  ⟨fun z => clip C.varianceLower C.varianceUpper
      (elementaryNumerator n k hk z / max (elementaryDenominator n k hk z)
        (elementaryFloor d k)), by
    apply (clip_lipschitz _ _).continuous.measurable.comp
    apply Measurable.div
    · exact PairUStatistic.pairAverage_measurable n
        (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk)
          Prod.snd measurable_snd 0)
    · exact (PairUStatistic.pairAverage_measurable n
        (sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk))).max
        measurable_const⟩

theorem pairAverage_sub_scaled {E : Type*} (n : ℕ) (K L : E × E → ℝ)
    (V : ℝ) (z : Fin n → E) :
    PairUStatistic.pairAverage n K z - V * PairUStatistic.pairAverage n L z =
      PairUStatistic.pairAverage n (fun w => K w - V * L w) z := by
  simp only [PairUStatistic.pairAverage, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem elementary_score_average {d : ℕ} (θ : RegressionParameter d)
    (n k : ℕ) (hk : 0 < k) (z : Fin n → Observation d) :
    elementaryNumerator n k hk z - θ.variance * elementaryDenominator n k hk z =
      PairUStatistic.pairAverage n (regularPairScore θ k hk) z := by
  rw [elementaryNumerator, elementaryDenominator, pairAverage_sub_scaled]
  congr 1
  funext w
  unfold regularPairScore pairWindowScore sameLabelKernel
  split_ifs <;> ring

/-- The ratio loss is controlled by two centered pair averages and its
population bias. The formula is pointwise and uses no probability premises. -/
theorem stabilized_ratio_sq_le {lo hi V N D q a b : ℝ}
    (ha : 0 < a) (hlo : lo ≤ V) (hhi : V ≤ hi)
    (hV : 0 ≤ V) (hq : 2 * a ≤ q) :
    (clip lo hi (N / max D a) - V) ^ 2 ≤
      4 * a⁻¹ ^ 2 * ((N - V * D - b) ^ 2 + b ^ 2) +
      2 * a⁻¹ ^ 2 * hi ^ 2 * (D - q) ^ 2 := by
  have hh := stabilized_ratio_error ha hlo hhi hV hq
    (N := N) (D := D)
  have hh2 := pow_le_pow_left₀ (abs_nonneg _) hh 2
  rw [sq_abs, mul_pow] at hh2
  have hsum : (|N - V * D| + hi * |D - q|) ^ 2 ≤
      2 * ((N - V * D) ^ 2 + hi ^ 2 * (D - q) ^ 2) := by
    simpa only [mul_pow, sq_abs] using
      (add_sq_le (a := |N - V * D|) (b := hi * |D - q|))
  have hb : (N - V * D) ^ 2 ≤ 2 * ((N - V * D - b) ^ 2 + b ^ 2) := by
    have h := add_sq_le (a := N - V * D - b) (b := b)
    convert h using 1 <;> ring
  calc
    _ ≤ a⁻¹ ^ 2 * (|N - V * D| + hi * |D - q|) ^ 2 := hh2
    _ ≤ a⁻¹ ^ 2 * (2 * ((N - V * D) ^ 2 + hi ^ 2 * (D - q) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ ≤ a⁻¹ ^ 2 * (2 * (2 * ((N - V * D - b) ^ 2 + b ^ 2) +
        hi ^ 2 * (D - q) ^ 2)) := by gcongr
    _ = _ := by ring

theorem elementaryPairEstimator_error_memLp {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n k : ℕ) (hk : 0 < k) :
    MemLp (fun z => (elementaryPairEstimator C n k hk).val z - θ.variance)
      2 (sampleLaw θ n) := by
  let := sampleLaw_isProbability C θ hθ n
  apply MemLp.of_bound
    ((elementaryPairEstimator C n k hk).property.sub measurable_const).aestronglyMeasurable
    (C.varianceUpper - C.varianceLower)
  filter_upwards [] with z
  change ‖clip C.varianceLower C.varianceUpper _ - θ.variance‖ ≤ _
  rw [Real.norm_eq_abs]
  exact clip_error_le_diameter hθ.2.2.2.2.2.1 hθ.2.2.2.2.2.2.1

theorem elementaryPairEstimator_risk_eq_integral {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n k : ℕ) (hk : 0 < k) :
    meanSquaredRisk (elementaryPairEstimator C n k hk) θ =
      ENNReal.ofReal (∫ z, ((elementaryPairEstimator C n k hk).val z - θ.variance) ^ 2
        ∂sampleLaw θ n) := by
  symm
  exact ofReal_integral_eq_lintegral_ofReal
    (elementaryPairEstimator_error_memLp C θ hθ n k hk).integrable_sq
    (Eventually.of_forall (fun z => sq_nonneg _))

end NearlyMinimax.ElementaryPairSupport
