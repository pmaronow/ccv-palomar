module

public import NearlyMinimax.PilotAnalyticToStatistics
public import NearlyMinimax.UniformPilotDerivatives


@[expose] public section

/-! Domain-uniform actual statistical pilot bounds. Analytic witnesses are
chosen before the extension domain, then transferred through the genuine
L² factorial kernel calculations and multilevel aggregation. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem dyadicPilotErrorField_point_second_of_variance {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (D A : ℝ) (hD : 0 < D) (hA : 0 < A)
    (hv : ∀ n j : ℕ,
      ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : ℕ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ,
      m + anchoredDimension d C.order + 1 ≤ n →
      ∀ Λ : ℝ, 0 < Λ → Λ ≤ (n : ℝ) - (m + anchoredDimension d C.order + 1) + 1 →
        variance (dyadicPolynomialPilot C n j x y m row) (sampleLaw θ n) ≤
          ((∑ i, |row i|) * D) ^ 2 *
            ∑ t : Fin (m + anchoredDimension d C.order + 1),
              ((t.val + 1).factorial : ℝ) *
                (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
                  preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ (t.val + 1)) :
    ∀ n j L : ℕ, j ≤ L → ∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
      regularGridCell ((2 : ℕ) ^ L) (by positivity) x =
        regularGridCell ((2 : ℕ) ^ L) (by positivity) z →
      ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : ℕ,
      m + anchoredDimension d C.order + 1 ≤ n → ∀ Λ : ℝ, 0 < Λ →
      Λ ≤ (n : ℝ) - (m + anchoredDimension d C.order + 1) + 1 →
      (∫ t, dyadicPilotErrorField C θ n j y m t (x, z) ^ 2 ∂sampleLaw θ n) ≤
        (dyadicPilotRowCap d C.order j L * D) ^ 2 * dyadicPilotSeries C A Λ j m := by
  intro n j L hj x hx z hz hc y hy m hdegree Λ hΛ hΛn
  obtain ⟨hL2, hmean⟩ := dyadicPolynomialPilot_moment_facts C θ hθ n j x hx y m
    (dyadicPilotRow j x z) hdegree
  have h := hv n j x hx y hy m (dyadicPilotRow j x z) hdegree Λ hΛ hΛn
  rw [variance_eq_integral hL2.aemeasurable, hmean] at h
  have hr := dyadicPilotRow_sum_abs_le_fine_cell (ℓ := C.order) j L hj x z hx hz hc.symm
  apply h.trans
  change ((∑ i, |dyadicPilotRow j x z i|) * D) ^ 2 * dyadicPilotSeries C A Λ j m ≤ _
  apply mul_le_mul_of_nonneg_right _ (dyadicPilotSeries_nonneg C A Λ hΛ.le _ _)
  apply pow_le_pow_left₀ (mul_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hD.le)
  exact mul_le_mul_of_nonneg_right hr hD.le


theorem dyadicMultilevelErrorField_point_second_of_variance {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (D A : ℝ) (hD : 0 < D) (hA : 0 < A)
    (hv : ∀ n j : ℕ,
      ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : ℕ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ,
      m + anchoredDimension d C.order + 1 ≤ n →
      ∀ Λ : ℝ, 0 < Λ → Λ ≤ (n : ℝ) - (m + anchoredDimension d C.order + 1) + 1 →
        variance (dyadicPolynomialPilot C n j x y m row) (sampleLaw θ n) ≤
          ((∑ i, |row i|) * D) ^ 2 *
            ∑ t : Fin (m + anchoredDimension d C.order + 1),
              ((t.val + 1).factorial : ℝ) *
                (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
                  preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ (t.val + 1)) :
    ∀ n J L : ℕ, J ≤ L → ∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
      regularGridCell ((2 : ℕ) ^ L) (by positivity) x =
        regularGridCell ((2 : ℕ) ^ L) (by positivity) z →
      ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : ℕ → ℕ,
      (∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) →
      ∀ Λ : ℝ, 0 < Λ →
      (∀ j : Fin (J + 1), Λ ≤ (n : ℝ) - (m j.val + anchoredDimension d C.order + 1) + 1) →
      (∫ t, dyadicMultilevelErrorField C θ n J y m t (x, z) ^ 2 ∂sampleLaw θ n) ≤
        4 * ((anchoredDimension d C.order : ℝ) * D) ^ 2 * (d : ℝ) *
          dyadicMultilevelBudget (dyadicSeriesEnvelope C A Λ J m) J L := by
  have hpoint := dyadicPilotErrorField_point_second_of_variance C θ hθ D A hD hA hv
  intro n J L hJL x hx z hz hc y hy m hdegree Λ hΛ hΛn
  let H := dyadicSeriesEnvelope C A Λ J m
  have hH : 0 ≤ H := dyadicSeriesEnvelope_nonneg C A Λ hΛ.le J m
  let B := ((anchoredDimension d C.order : ℝ) * D) ^ 2 * (d : ℝ) *
    (((2 : ℝ) ^ L)⁻¹) ^ 2 * H
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let X (j : Fin (J + 1)) (t : Fin n → Observation d) :=
    dyadicPilotErrorField C θ n j.val y (m j.val) t (x, z)
  have hX (j : Fin (J + 1)) : MemLp (X j) 2 (sampleLaw θ n) :=
    (dyadicPilotErrorField_point_moment_facts C θ hθ n j.val x hx z y (m j.val) (hdegree j)).1
  have hE (j : Fin (J + 1)) : (∫ t, X j t ^ 2 ∂sampleLaw θ n) ≤ B * ((2 : ℝ) ^ j.val) ^ 2 := by
    have h := hpoint n j.val L ((Nat.le_of_lt_succ j.isLt).trans hJL)
      x hx z hz hc y hy (m j.val) (hdegree j) Λ hΛ (hΛn j)
    apply h.trans
    rw [dyadicPilotRowCap_square]
    calc
      _ ≤ (((anchoredDimension d C.order : ℝ) * D) ^ 2 * (d : ℝ) *
          (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ j.val) ^ 2) * H :=
        mul_le_mul_of_nonneg_left (dyadicPilotSeries_le_envelope C A Λ hΛ.le J m j) (by positivity)
      _ = _ := by dsimp [B]; ring
  have h := secondMoment_dyadic_sum_le (sampleLaw θ n) J X hX B hB hE
  apply h.trans_eq
  dsimp [B, dyadicMultilevelBudget]
  ring


theorem dyadicMultilevelErrorField_test_second_of_variance {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (D A : ℝ) (hD : 0 < D) (hA : 0 < A)
    (htest :     ∀ n j J : ℕ, j ≤ J →
      ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : ℕ,
      m + anchoredDimension d C.order + 1 ≤ n →
      ∀ Λ : ℝ, 0 < Λ → Λ ≤ (n : ℝ) - (m + anchoredDimension d C.order + 1) + 1 →
      ∀ ν : Covariate d × Covariate d → ℝ,
      MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)) →
      variance (fun z => ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w
        ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)) (sampleLaw θ n) ≤
      (C.densityUpper ^ 2 / dyadicPilotScale d (j - 1)) *
        ((dyadicPilotRowCap d C.order j J * D) ^ 2 *
          ∑ r : Fin (m + anchoredDimension d C.order + 1),
            ((r.val + 1).factorial : ℝ) *
              (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
                preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ (r.val + 1)) *
        (∫ w, ν w ^ 2 ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity))) :
    ∀ n J L : ℕ, J ≤ L → ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m : ℕ → ℕ,
      (∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) →
      ∀ Λ : ℝ, 0 < Λ →
      (∀ j : Fin (J + 1), Λ ≤ (n : ℝ) - (m j.val + anchoredDimension d C.order + 1) + 1) →
      ∀ ν : Covariate d × Covariate d → ℝ,
      MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) →
      (∫ t, (∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
        ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) ^ 2 ∂sampleLaw θ n) ≤
        (4 * C.densityUpper ^ 2 * (2 : ℝ) ^ d *
          ((anchoredDimension d C.order : ℝ) * D) ^ 2 * (d : ℝ) *
            dyadicMultilevelBudget (dyadicSeriesEnvelope C A Λ J m) J L / Λ) *
          (∫ w, ν w ^ 2 ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) := by
  intro n J L hJL y hy m hdegree Λ hΛ hΛn ν hν
  let := sampleLaw_isProbability C θ hθ n
  let M := regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)
  let H := dyadicSeriesEnvelope C A Λ J m
  have hH : 0 ≤ H := dyadicSeriesEnvelope_nonneg C A Λ hΛ.le J m
  let I := ∫ w, ν w ^ 2 ∂M
  have hI : 0 ≤ I := integral_nonneg (fun _ => sq_nonneg _)
  let B := C.densityUpper ^ 2 * (2 : ℝ) ^ d *
    ((anchoredDimension d C.order : ℝ) * D) ^ 2 * (d : ℝ) *
      (((2 : ℝ) ^ L)⁻¹) ^ 2 * (H / Λ) * I
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let X (j : Fin (J + 1)) (t : Fin n → Observation d) :=
    ∫ w, ν w * dyadicPilotErrorField C θ n j.val y (m j.val) t w ∂M
  have hf (j : Fin (J + 1)) := dyadicPilotErrorField_test_moment_facts C θ hθ n j.val L
    ((Nat.le_of_lt_succ j.isLt).trans hJL) y hy (m j.val) (hdegree j) ν hν
  have hE (j : Fin (J + 1)) : (∫ t, X j t ^ 2 ∂sampleLaw θ n) ≤ B * ((2 : ℝ) ^ j.val) ^ 2 := by
    have h := htest n j.val L ((Nat.le_of_lt_succ j.isLt).trans hJL) y hy
      (m j.val) (hdegree j) Λ hΛ (hΛn j) ν hν
    rw [variance_of_integral_eq_zero (hf j).1.aemeasurable (hf j).2] at h
    apply h.trans
    change (C.densityUpper ^ 2 / dyadicPilotScale d (j.val - 1)) *
      ((dyadicPilotRowCap d C.order j.val L * D) ^ 2 * dyadicPilotSeries C A Λ j.val (m j.val)) * I ≤ _
    rw [dyadicPilotRowCap_square]
    have hratio : dyadicPilotScale d j.val / dyadicPilotScale d (j.val - 1) ≤ (2 : ℝ) ^ d :=
      (div_le_iff₀ (dyadicPilotScale_pos _ _)).mpr dyadicPilotScale_parent_ratio_le
    have hs := dyadicPilotSeries_div_scale_le_envelope C A Λ hΛ J m j
    have hsnon := div_nonneg (dyadicPilotSeries_nonneg C A Λ hΛ.le j.val (m j.val))
      (dyadicPilotScale_pos d j.val).le
    calc
      _ = (C.densityUpper ^ 2 * ((anchoredDimension d C.order : ℝ) * D) ^ 2 *
          (d : ℝ) * (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ j.val) ^ 2) *
          (dyadicPilotScale d j.val / dyadicPilotScale d (j.val - 1)) *
          (dyadicPilotSeries C A Λ j.val (m j.val) / dyadicPilotScale d j.val) * I := by
        field_simp [(dyadicPilotScale_pos d j.val).ne', (dyadicPilotScale_pos d (j.val - 1)).ne']
        <;> ring
      _ ≤ (C.densityUpper ^ 2 * ((anchoredDimension d C.order : ℝ) * D) ^ 2 *
          (d : ℝ) * (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ j.val) ^ 2) *
          ((2 : ℝ) ^ d) * (H / Λ) * I := by
        apply mul_le_mul_of_nonneg_right _ hI
        exact mul_le_mul (mul_le_mul_of_nonneg_left hratio (by positivity)) hs hsnon (by positivity)
      _ = _ := by dsimp [B]; ring
  have h := secondMoment_dyadic_sum_le (sampleLaw θ n) J X (fun j => (hf j).1) B hB hE
  have heq : (fun t => ∑ j, X j t) =
      (fun t => ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w ∂M) := by
    funext t
    exact (dyadicMultilevelErrorField_test_integral_sum C θ hθ n J L hJL y hy m hdegree ν hν t).symm
  have heqpoint (t : Fin n → Observation d) := congrFun heq t
  simp_rw [heqpoint] at h
  apply h.trans_eq
  dsimp [B, dyadicMultilevelBudget]
  ring


theorem uniform_domain_common_dyadicMultilevel_bounds {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧ ∀ U : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain U) θ →
      ∀ n J L : ℕ, J ≤ L → ∀ y : ℝ, |y| ≤ max C.holderBound 1 → ∀ m : ℕ → ℕ,
      (∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) →
      ∀ Λ : ℝ, 0 < Λ →
      (∀ j : Fin (J + 1), Λ ≤ (n : ℝ) - (m j.val + anchoredDimension d C.order + 1) + 1) →
      (∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
        regularGridCell ((2 : ℕ) ^ L) (by positivity) x =
          regularGridCell ((2 : ℕ) ^ L) (by positivity) z →
        (∫ t, dyadicMultilevelErrorField C θ n J y m t (x, z) ^ 2 ∂sampleLaw θ n) ≤
          4 * ((anchoredDimension d C.order : ℝ) * D) ^ 2 * (d : ℝ) *
            dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L) ∧
      (∀ ν : Covariate d × Covariate d → ℝ,
        MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) →
        (∫ t, (∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
          ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) ^ 2 ∂sampleLaw θ n) ≤
          (4 * C.densityUpper ^ 2 * (2 : ℝ) ^ d *
            ((anchoredDimension d C.order : ℝ) * D) ^ 2 * (d : ℝ) *
              dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L / Λ) *
            (∫ w, ν w ^ 2 ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity))) := by
  letI : Nonempty (AnchoredIndex d (pilotModelConstants C).order) :=
    inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  obtain ⟨D, A, hD, hA, hder⟩ := uniform_domain_admissible_dyadic_increment_all_derivative_bound
    (pilotModelConstants C) (pilotModelConstants C).holderBound (pilotModelConstants C).holderBound_pos.le
  refine ⟨D, A, hD, hA, ?_⟩
  intro U θ hθ n J L hJL y hy m hdegree Λ hΛ hΛn
  let CE := (pilotModelConstants C).withDomain U
  letI : Nonempty (AnchoredIndex d CE.order) := inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  have hθe : Admissible CE θ := by
    simpa only [pilotModelConstants_withDomain] using admissible_pilotModelConstants (C.withDomain U) θ hθ
  have hd := hder U θ hθe
  have hr := dyadicIncrementKernel_raw_budget_of_derivative CE θ hθe D A hD hA hd
  have hv := dyadicPolynomialPilot_variance_of_derivative CE θ hθe D A hD hA hd
  have ht := dyadicPilotErrorField_test_variance_of_raw_budget CE θ hθe D A hD hA hr
  constructor
  · intro x hx z hz hc
    exact dyadicMultilevelErrorField_point_second_of_variance CE θ hθe D A hD hA hv
      n J L hJL x hx z hz hc y hy m hdegree Λ hΛ hΛn
  · intro ν hν
    exact dyadicMultilevelErrorField_test_second_of_variance CE θ hθe D A hD hA ht
      n J L hJL y hy m hdegree Λ hΛ hΛn ν hν

end NearlyMinimax
