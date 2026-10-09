module

public import NearlyMinimax.DyadicPilotMultilevel
public import NearlyMinimax.PilotModelEnvelope


@[expose] public section

/-! One genuine model envelope and one factorial series simultaneously
control both scalar coefficient families of the actual estimator. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem dyadicPilotSeries_mono_A {d : ℕ} (C : ModelConstants d)
    {A B Λ : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hΛ : 0 ≤ Λ) (j m : ℕ) :
    dyadicPilotSeries C A Λ j m ≤ dyadicPilotSeries C B Λ j m := by
  have hcp := preconditionedPilotMomentConstant_pos C C.order
  have hk := dyadicPilotScale_pos d j
  unfold dyadicPilotSeries
  apply Finset.sum_le_sum
  intro k _
  gcongr

theorem dyadicSeriesEnvelope_mono_A {d : ℕ} (C : ModelConstants d)
    {A B Λ : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hΛ : 0 ≤ Λ)
    (J : ℕ) (m : ℕ → ℕ) :
    dyadicSeriesEnvelope C A Λ J m ≤ dyadicSeriesEnvelope C B Λ J m := by
  unfold dyadicSeriesEnvelope
  apply Finset.sup'_le
  intro j _
  apply le_trans _ (dyadicSeriesEnvelope_level_le C B Λ J m j)
  exact mul_le_mul_of_nonneg_right (dyadicPilotSeries_mono_A C hA hAB hΛ _ _)
    (zero_le_one.trans (le_max_left _ _))

theorem dyadicMultilevelErrorField_envelope_test_moment_facts {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n J L : ℕ) (hJL : J ≤ L) (y : ℝ) (hy : |y| ≤ max C.holderBound 1) (m : ℕ → ℕ)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n)
    (ν : Covariate d × Covariate d → ℝ)
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity))) :
    MemLp (fun t => ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) 2 (sampleLaw θ n) ∧
    (∫ t, ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity) ∂sampleLaw θ n) = 0 := by
  letI : Nonempty (AnchoredIndex d (pilotModelConstants C).order) :=
    inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  exact dyadicMultilevelErrorField_test_moment_facts (pilotModelConstants C) θ
    (admissible_pilotModelConstants C θ hθ) n J L hJL y hy m hdegree ν hν

/-- The same true maximum series controls both pointwise pilot error and
every L² spatial test, including the evaluations 0 and 1 that encode the
response coefficient. No stochastic risk bound is assumed. -/
theorem admissible_common_dyadicMultilevel_bounds {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧ ∀ θ : RegressionParameter d, Admissible C θ →
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
  obtain ⟨Dp, Ap, hDp, hAp, hp⟩ :=
    admissible_dyadicMultilevelErrorField_point_second (pilotModelConstants C)
  obtain ⟨Dt, At, hDt, hAt, ht⟩ :=
    admissible_dyadicMultilevelErrorField_test_second (pilotModelConstants C)
  refine ⟨max Dp Dt, max Ap At, hDp.trans_le (le_max_left _ _), hAp.trans_le (le_max_left _ _), ?_⟩
  intro θ hθ n J L hJL y hy m hdegree Λ hΛ hΛn
  have hθe := admissible_pilotModelConstants C θ hθ
  have hHp := dyadicSeriesEnvelope_mono_A (pilotModelConstants C) hAp.le (le_max_left Ap At) hΛ.le J m
  have hHt := dyadicSeriesEnvelope_mono_A (pilotModelConstants C) hAt.le (le_max_right Ap At) hΛ.le J m
  have hnp := dyadicSeriesEnvelope_nonneg (pilotModelConstants C) Ap Λ hΛ.le J m
  have hnt := dyadicSeriesEnvelope_nonneg (pilotModelConstants C) At Λ hΛ.le J m
  constructor
  · intro x hx z hz hc
    have h := hp θ hθe n J L hJL x hx z hz hc y hy m hdegree Λ hΛ hΛn
    apply h.trans
    change 4 * ((anchoredDimension d C.order : ℝ) * Dp) ^ 2 * (d : ℝ) *
      dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) Ap Λ J m) J L ≤ _
    unfold dyadicMultilevelBudget
    gcongr
    exact le_max_left Dp Dt
  · intro ν hν
    have h := ht θ hθe n J L hJL y hy m hdegree Λ hΛ hΛn ν hν
    apply h.trans
    change (4 * C.densityUpper ^ 2 * (2 : ℝ) ^ d *
      ((anchoredDimension d C.order : ℝ) * Dt) ^ 2 * (d : ℝ) *
        dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) At Λ J m) J L / Λ) *
      (∫ w, ν w ^ 2 ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) ≤ _
    have hI : 0 ≤ ∫ w, ν w ^ 2 ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity) :=
      integral_nonneg (fun _ => sq_nonneg _)
    unfold dyadicMultilevelBudget
    gcongr
    exact le_max_right Dp Dt

theorem dyadicMultilevelErrorField_envelope_weighted_integrable {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n J L : ℕ) (hJL : J ≤ L) (y : ℝ) (hy : |y| ≤ max C.holderBound 1) (m : ℕ → ℕ)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n)
    (ν : Covariate d × Covariate d → ℝ)
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)))
    (t : Fin n → Observation d) :
    Integrable (fun w => ν w * dyadicMultilevelErrorField C θ n J y m t w)
      (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) := by
  letI : Nonempty (AnchoredIndex d (pilotModelConstants C).order) :=
    inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  have hi (j : Fin (J + 1)) := dyadicPilotErrorField_weighted_integrable (pilotModelConstants C) θ
    (admissible_pilotModelConstants C θ hθ) n j.val L ((Nat.le_of_lt_succ j.isLt).trans hJL)
      y hy (m j.val) (hdegree j) ν hν t
  have hsum := integrable_finsetSum Finset.univ (fun j _ => hi j)
  convert hsum using 1
  funext w
  simp only [dyadicMultilevelErrorField, Finset.mul_sum]
  rfl

end NearlyMinimax
