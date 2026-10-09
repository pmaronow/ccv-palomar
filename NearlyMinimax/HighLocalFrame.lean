module

public import NearlyMinimax.HighFrameEvaluation
public import NearlyMinimax.HighSeparatedScores
public import Mathlib.MeasureTheory.Function.Floor


@[expose] public section

/-! Genuine Borel local coordinates and exact local regression decomposition
for the original periodic polynomial frame. Coordinates are bounded globally;
on an active window they are the actual affine torus chart coordinates. -/
noncomputable section
open Set MeasureTheory Function MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

/-- The nearest representative of the residue j in the scaled coordinate. -/
def highChartLift (k : ℕ) (j : ZMod k) (x : ℝ) : ℤ :=
  (j.val : ℤ) + (k : ℤ) * Int.floor (x - (j.val : ℝ) / k + 1 / 2)

theorem highChartLift_measurable (k : ℕ) (j : ZMod k) : Measurable (highChartLift k j) := by
  unfold highChartLift
  exact measurable_const.add (measurable_const.mul
    (Int.measurable_floor.comp (by fun_prop)))

theorem highChartLift_residue (k : ℕ) [NeZero k] (j : ZMod k) (x : ℝ) :
    (highChartLift k j x : ZMod k) = j := by
  simp [highChartLift]

/-- Every point inside the source patch selects the unique nearby lift. -/
theorem highChartLift_eq_of_close (k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : ZMod k) (x : ℝ) (z : ℤ) (hz : (z : ZMod k) = j)
    (hclose : |(k : ℝ) * x - z| < 1) : highChartLift k j x = z := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_iff k z j).mp hz
  have htR : (z : ℝ) = (j.val : ℝ) + (k : ℝ) * t := by exact_mod_cast ht
  have harg : (k : ℝ) * (x - (j.val : ℝ) / k + 1/2) =
      (k : ℝ) * x - j.val + k/2 := by field_simp
  have hbounds := abs_lt.mp hclose
  have hf : Int.floor (x - (j.val : ℝ) / k + 1/2) = t := by
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (mul_le_mul_iff_right₀ hkR).mp
      nlinarith
    · apply (mul_lt_mul_iff_right₀ hkR).mp
      nlinarith
  simp only [highChartLift, hf]
  exact ht.symm

theorem highPeriodicWindow_eq_chart_lift (k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : ZMod k) (x : ℝ) :
    highPeriodicWindow k j x = highWindowProfile ((k : ℝ) * x - highChartLift k j x) := by
  unfold highPeriodicWindow
  rw [finsum_eq_single _ (highChartLift k j x)]
  · simp only [ite_eq_left (highChartLift_residue k j x)]
  · intro z hz
    by_cases hj : (z : ZMod k) = j
    · simp only [ite_eq_left hj]
      by_contra hp
      have hclose : |(k : ℝ) * x - z| < 1 := by
        have hc : |(k : ℝ) * x - z| < 3/4 := by
          by_contra h
          exact hp (highWindowProfile_eq_zero _ (not_lt.mp h))
        linarith
      exact hz (highChartLift_eq_of_close k hk j x z hj hclose).symm
    · simp only [ite_eq_right hj]

def highRawChartCoordinate (k : ℕ) (j : ZMod k) (x : ℝ) : ℝ :=
  (k : ℝ) * x - highChartLift k j x

def highLocalCoordinate (k : ℕ) (j : ZMod k) (x : ℝ) : ℝ :=
  if |highRawChartCoordinate k j x| ≤ 1 then highRawChartCoordinate k j x else 0

def highLocalCoordinates (d k : ℕ) (j : HighWindowLabels d k) (x : Covariate d) : Covariate d :=
  fun r => highLocalCoordinate k (j r) (x r)

theorem highRawChartCoordinate_measurable (k : ℕ) (j : ZMod k) :
    Measurable (highRawChartCoordinate k j) := by
  exact (measurable_const.mul measurable_id).sub
    ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp (highChartLift_measurable k j))

theorem highLocalCoordinate_measurable (k : ℕ) (j : ZMod k) :
    Measurable (highLocalCoordinate k j) := by
  unfold highLocalCoordinate
  apply Measurable.ite
  · exact measurableSet_le (highRawChartCoordinate_measurable k j).abs measurable_const
  · exact highRawChartCoordinate_measurable k j
  · exact measurable_const

theorem highLocalCoordinate_abs_le_one (k : ℕ) (j : ZMod k) (x : ℝ) :
    |highLocalCoordinate k j x| ≤ 1 := by
  unfold highLocalCoordinate
  split_ifs with h
  · exact h
  · norm_num

theorem highLocalCoordinates_measurable (d k : ℕ) (j : HighWindowLabels d k) :
    Measurable (highLocalCoordinates d k j) := by
  apply measurable_pi_iff.mpr
  intro r
  exact (highLocalCoordinate_measurable k (j r)).comp (measurable_pi_apply r)

theorem highLocalCoordinates_abs_le_one (d k : ℕ) (j : HighWindowLabels d k)
    (x : Covariate d) (r : Fin d) : |highLocalCoordinates d k j x r| ≤ 1 :=
  highLocalCoordinate_abs_le_one k (j r) (x r)

def highRawChartCoordinates (d k : ℕ) (j : HighWindowLabels d k) (x : Covariate d) : Covariate d :=
  fun r => highRawChartCoordinate k (j r) (x r)

theorem highPeriodicTensor_eq_chart_lift (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (x : Covariate d) :
    highPeriodicTensor d k j x = highWindowTensor d (highRawChartCoordinates d k j x) := by
  unfold highPeriodicTensor highWindowTensor highRawChartCoordinates highRawChartCoordinate
  simp_rw [highPeriodicWindow_eq_chart_lift k hk]

theorem highPeriodizedChart_eq_chart_lift (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (G : Covariate d → ℝ)
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) (x : Covariate d) :
    highPeriodizedChart d k j G x = G (highRawChartCoordinates d k j x) := by
  unfold highPeriodizedChart
  rw [finsum_eq_single _ (fun r => highChartLift k (j r) (x r))]
  · simp only [highChartLift_residue, implies_true, ite_true]
    rfl
  · intro z hz
    by_cases hres : ∀ r, (z r : ZMod k) = j r
    · simp only [ite_eq_left hres]
      by_contra hG
      have hprof : highWindowTensor d (fun r => (k : ℝ) * x r - z r) ≠ 0 :=
        fun hp => hG (hG0 _ hp)
      apply hz
      funext r
      have hpr : highWindowProfile ((k : ℝ) * x r - z r) ≠ 0 := by
        intro hp
        exact hprof (Finset.prod_eq_zero (Finset.mem_univ r) hp)
      have hclose : |(k : ℝ) * x r - z r| < 1 := by
        have hpclose : |(k : ℝ) * x r - z r| < 3/4 := by
          by_contra hp
          exact hpr (highWindowProfile_eq_zero _ (not_lt.mp hp))
        linarith
      exact (highChartLift_eq_of_close k hk (j r) (x r) (z r) (hres r) hclose).symm
    · simp only [ite_eq_right hres]

theorem highRawChartCoordinates_abs_lt_of_active (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (x : Covariate d)
    (hw : highPeriodicTensor d k j x ≠ 0) (r : Fin d) :
    |highRawChartCoordinates d k j x r| < 3/4 := by
  rw [highPeriodicTensor_eq_chart_lift d k hk j x] at hw
  have hp : highWindowProfile (highRawChartCoordinates d k j x r) ≠ 0 := by
    intro hp
    exact hw (Finset.prod_eq_zero (Finset.mem_univ r) hp)
  by_contra h
  exact hp (highWindowProfile_eq_zero _ (not_lt.mp h))

theorem highLocalCoordinates_eq_raw_of_active (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (x : Covariate d) (hw : highPeriodicTensor d k j x ≠ 0) :
    highLocalCoordinates d k j x = highRawChartCoordinates d k j x := by
  funext r
  have hbound : |highRawChartCoordinate k (j r) (x r)| ≤ 1 := by
    have h := highRawChartCoordinates_abs_lt_of_active d k hk j x hw r
    change |highRawChartCoordinate k (j r) (x r)| < 3/4 at h
    linarith
  exact if_pos hbound

def highLocalFrameFeature {d D : ℕ} (k : ℕ) (j : HighWindowLabels d k)
    (x : Covariate d) (γ : HighFrameIndex d D) : ℝ :=
  highFrameFeature (highLocalCoordinates d k j x) γ

theorem highLocalFrameFeature_measurable {d D : ℕ} (k : ℕ)
    (j : HighWindowLabels d k) (γ : HighFrameIndex d D) :
    Measurable (fun x => highLocalFrameFeature k j x γ) := by
  unfold highLocalFrameFeature highFrameFeature
  apply Finset.measurable_fun_prod
  intro r _
  exact (((measurable_pi_apply r).comp (highLocalCoordinates_measurable d k j)).div_const 8).pow_const _

theorem highLocalFrameFeature_abs_le_one {d D : ℕ} (k : ℕ)
    (j : HighWindowLabels d k) (x : Covariate d) (γ : HighFrameIndex d D) :
    |highLocalFrameFeature k j x γ| ≤ 1 := by
  unfold highLocalFrameFeature highFrameFeature
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · intro r _
    exact abs_nonneg _
  · intro r _
    rw [abs_pow]
    apply pow_le_one₀ (abs_nonneg _)
    rw [abs_div]
    norm_num
    linarith [highLocalCoordinates_abs_le_one d k j x r]

theorem highFrameMonomial_scaled_eval {d D : ℕ} (γ : HighFrameIndex d D) (u : Covariate d) :
    MvPolynomial.eval u (frameScaledPolynomial (highFrameMonomial γ)) = highFrameFeature u γ := by
  rw [frameScaledPolynomial_eval]
  unfold highFrameMonomial highFrameFeature
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [polynomial_box_exponent_apply]

/-- The true periodized monomial chart equals its actual window times the
bounded Borel local monomial feature, including window zeros. -/
theorem highPeriodizedFrameMonomial_local_feature {d D : ℕ} (k : ℕ) [NeZero k]
    (hk : 4 ≤ k) (j : HighWindowLabels d k) (x : Covariate d) (γ : HighFrameIndex d D) :
    highPeriodizedChart d k j (highFrameProfile (highFrameMonomial γ)) x =
      highPeriodicTensor d k j x * highLocalFrameFeature k j x γ := by
  rw [highPeriodizedChart_eq_chart_lift d k hk j _
    (highFrameProfile_zero_of_window_zero (highFrameMonomial γ))]
  unfold highFrameProfile
  rw [highFrameMonomial_scaled_eval, ← highPeriodicTensor_eq_chart_lift d k hk j x]
  by_cases hw : highPeriodicTensor d k j x = 0
  · simp only [hw, zero_mul]
  · rw [highLocalFrameFeature, highLocalCoordinates_eq_raw_of_active d k hk j x hw]

theorem highPeriodizedFrame_local_feature {d D : ℕ} (k : ℕ) [NeZero k]
    (hk : 4 ≤ k) (j : HighWindowLabels d k) (x : Covariate d)
    (c : HighFrameIndex d D → ℝ) :
    highPeriodizedChart d k j (highFrameProfile (highFramePolynomial c)) x =
      highPeriodicTensor d k j x * ∑ γ, highLocalFrameFeature k j x γ * c γ := by
  rw [highPeriodizedFrame_evaluation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [highPeriodizedFrameMonomial_local_feature k hk j x γ]
  ring

/-- The actual regression field with one window coefficient block removed. -/
def highLocalFieldWithout (d k D : ℕ) [NeZero k] (η : ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (j : HighWindowLabels d k)
    (x : Covariate d) : ℝ :=
  η * ∑ l ∈ (Finset.univ : Finset (HighWindowLabels d k)).erase j,
    highPeriodizedChart d k l (highFrameProfile (highFramePolynomial (c l))) x

theorem highFrameField_local_decomposition (d k D : ℕ) [NeZero k] (hk : 4 ≤ k)
    (η : ℝ) (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (j : HighWindowLabels d k) (x : Covariate d) :
    highFrameField d k η (fun l => highFramePolynomial (c l)) x =
      highLocalFieldWithout d k D η c j x + η * highPeriodicTensor d k j x *
        ∑ γ, highLocalFrameFeature k j x γ * c j γ := by
  have hs := Finset.sum_erase_add (Finset.univ : Finset (HighWindowLabels d k))
    (fun l => highPeriodizedChart d k l (highFrameProfile (highFramePolynomial (c l))) x)
    (Finset.mem_univ j)
  rw [highPeriodizedFrame_local_feature k hk j x (c j)] at hs
  unfold highFrameField highLocalFieldWithout
  rw [← hs]
  ring

/-- The source's local coefficient regression representation is a theorem
about the actual periodic field, not an additional model premise. -/
theorem highFrameField_coefficientRegression (d k D n : ℕ) [NeZero k] (hk : 4 ≤ k)
    (η : ℝ) (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (j : HighWindowLabels d k) (x : Fin n → Covariate d) :
    coefficientRegression η (fun i => highLocalFieldWithout d k D η c j (x i))
      (fun i => highPeriodicTensor d k j (x i))
      (fun i => highLocalFrameFeature k j (x i)) (c j) =
      fun i => highFrameField d k η (fun l => highFramePolynomial (c l)) (x i) := by
  funext i
  exact (highFrameField_local_decomposition d k D hk η c j (x i)).symm

theorem highLocalFieldWithout_continuous (d k D : ℕ) [NeZero k] (η : ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (j : HighWindowLabels d k) :
    Continuous (highLocalFieldWithout d k D η c j) := by
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro l _
  exact (highPeriodizedChart_contDiff d k l _
    (highFrameProfile_contDiff (highFramePolynomial (c l)))
    (highFrameProfile_zero_of_window_zero (highFramePolynomial (c l)))).continuous

/-- The coefficient ball gives the actual uniformly bounded local profile. -/
theorem highLocalFrameFeature_linear_abs_bound {d D : ℕ} (k : ℕ)
    (j : HighWindowLabels d k) (x : Covariate d) (c : HighFrameIndex d D → ℝ) :
    |∑ γ, highLocalFrameFeature k j x γ * c γ| ≤ ∑ γ, |c γ| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro γ _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (highLocalFrameFeature_abs_le_one k j x γ)
    (abs_nonneg (c γ))).trans_eq (one_mul _)

theorem highLocalFrameFeature_ball_abs_le_one {d D : ℕ} (k : ℕ)
    (j : HighWindowLabels d k) (x : Covariate d) (C : ℝ) (hC : 1 ≤ C)
    (c : HighFrameIndex d D → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹) :
    |∑ γ, highLocalFrameFeature k j x γ * c γ| ≤ 1 := by
  apply (highLocalFrameFeature_linear_abs_bound k j x c).trans
  exact hc.trans ((inv_le_one₀ (by linarith : 0 < C)).mpr hC)

end NearlyMinimax
