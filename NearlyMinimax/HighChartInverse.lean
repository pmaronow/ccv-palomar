module

public import NearlyMinimax.HighLocalFrame


@[expose] public section

/-! A genuine affine inverse of each torus chart on the full closed source
cube. This transfers actual observed-coordinate nuisance maps to literal
spatial patch variables, including chart boundary points. -/
noncomputable section
open Set MeasureTheory
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

def highChartInverse (d k : ℕ) (j : HighWindowLabels d k) (U : Covariate d) : Covariate d :=
  fun r => ((j r).val + U r)/(k : ℝ)

theorem highChartInverse_continuous (d k : ℕ) (j : HighWindowLabels d k) :
    Continuous (highChartInverse d k j) := by
  unfold highChartInverse
  fun_prop

theorem highChartInverse_measurable (d k : ℕ) (j : HighWindowLabels d k) :
    Measurable (highChartInverse d k j) := (highChartInverse_continuous d k j).measurable

theorem highChartInverse_joint_continuous (d k : ℕ) :
    Continuous (fun t : HighWindowLabels d k × Covariate d => highChartInverse d k t.1 t.2) := by
  apply continuous_pi
  intro r
  have hj : Continuous (fun j : HighWindowLabels d k => ((j r).val : ℝ)) :=
    continuous_of_discreteTopology
  exact ((hj.comp continuous_fst).add ((continuous_apply r).comp continuous_snd)).div_const _

theorem highChartInverse_joint_measurable (d k : ℕ) [NeZero k] :
    Measurable (fun t : HighWindowLabels d k × Covariate d => highChartInverse d k t.1 t.2) := by
  apply measurable_pi_iff.mpr
  intro r
  have hj : Measurable (fun j : HighWindowLabels d k => ((j r).val : ℝ)) :=
    measurable_of_countable _
  exact ((hj.comp measurable_fst).add ((measurable_pi_apply r).comp measurable_snd)).div_const _

theorem highChartLift_inverse_scalar (k : ℕ) (hk : 4 ≤ k) (j : ZMod k)
    (u : ℝ) (hu : |u| ≤ 1) : highChartLift k j (((j.val : ℝ)+u)/(k : ℝ)) = (j.val : ℤ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have harg : (((j.val : ℝ)+u)/(k : ℝ) - (j.val : ℝ)/k + 1/2) = u/k+1/2 := by ring
  have hmul : (u/k+1/2)*(k : ℝ) = u+(k : ℝ)/2 := by field_simp
  have hf : Int.floor (u/k+1/2) = 0 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (mul_le_mul_iff_right₀ hkR).mp
      simp only [Int.cast_zero]
      nlinarith only [hmul, (abs_le.mp hu).1, hk4]
    · apply (mul_lt_mul_iff_right₀ hkR).mp
      simp only [Int.cast_zero, zero_add]
      nlinarith only [hmul, (abs_le.mp hu).2, hk4]
  simp only [highChartLift, harg, hf, mul_zero, add_zero]

theorem highRawChartCoordinate_inverse_scalar (k : ℕ) (hk : 4 ≤ k) (j : ZMod k)
    (u : ℝ) (hu : |u| ≤ 1) :
    highRawChartCoordinate k j (((j.val : ℝ)+u)/(k : ℝ)) = u := by
  rw [highRawChartCoordinate, highChartLift_inverse_scalar k hk j u hu]
  push_cast
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  field_simp
  ring

theorem highRawChartCoordinates_inverse (d k : ℕ) (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (U : Covariate d) (hU : ∀ r, |U r| ≤ 1) :
    highRawChartCoordinates d k j (highChartInverse d k j U) = U := by
  funext r
  exact highRawChartCoordinate_inverse_scalar k hk (j r) (U r) (hU r)

theorem highLocalCoordinates_inverse (d k : ℕ) (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (U : Covariate d) (hU : ∀ r, |U r| ≤ 1) :
    highLocalCoordinates d k j (highChartInverse d k j U) = U := by
  funext r
  change (if |highRawChartCoordinate k (j r) (((j r).val+U r)/(k : ℝ))| ≤ 1 then
    highRawChartCoordinate k (j r) (((j r).val+U r)/(k : ℝ)) else 0) = U r
  rw [highRawChartCoordinate_inverse_scalar k hk (j r) (U r) (hU r), ite_eq_left (hU r)]

theorem highPeriodicTensor_inverse (d k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (U : Covariate d) (hU : ∀ r, |U r| ≤ 1) :
    highPeriodicTensor d k j (highChartInverse d k j U) = highWindowTensor d U := by
  rw [highPeriodicTensor_eq_chart_lift d k hk, highRawChartCoordinates_inverse d k hk j U hU]

theorem highLocalFrameFeature_inverse {d D : ℕ} (k : ℕ) (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (U : Covariate d) (hU : ∀ r, |U r| ≤ 1)
    (γ : HighFrameIndex d D) :
    highLocalFrameFeature k j (highChartInverse d k j U) γ = highFrameFeature U γ := by
  rw [highLocalFrameFeature, highLocalCoordinates_inverse d k hk j U hU]

def highChartConfigurationInverse {n : ℕ} (d k : ℕ) (j : HighWindowLabels d k)
    (U : Fin n → Covariate d) : Fin n → Covariate d := fun i => highChartInverse d k j (U i)

theorem highChartConfigurationInverse_continuous {n : ℕ} (d k : ℕ) (j : HighWindowLabels d k) :
    Continuous (highChartConfigurationInverse (n := n) d k j) := by
  apply continuous_pi
  intro i
  exact (highChartInverse_continuous d k j).comp (continuous_apply i)

theorem highChartConfigurationInverse_measurable {n : ℕ} (d k : ℕ) (j : HighWindowLabels d k) :
    Measurable (highChartConfigurationInverse (n := n) d k j) :=
  (highChartConfigurationInverse_continuous d k j).measurable

theorem highChartConfigurationInverse_localCoordinates {n : ℕ} (d k : ℕ) (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (U : Fin n → Covariate d) (hU : ∀ i r, |U i r| ≤ 1) :
    (fun i => highLocalCoordinates d k j (highChartConfigurationInverse d k j U i)) = U := by
  funext i
  exact highLocalCoordinates_inverse d k hk j (U i) (hU i)

theorem highChartConfigurationInverse_rawCoordinates {n : ℕ} (d k : ℕ) (hk : 4 ≤ k)
    (j : HighWindowLabels d k) (U : Fin n → Covariate d) (hU : ∀ i r, |U i r| ≤ 1) :
    (fun i => highRawChartCoordinates d k j (highChartConfigurationInverse d k j U i)) = U := by
  funext i
  exact highRawChartCoordinates_inverse d k hk j (U i) (hU i)

end NearlyMinimax
