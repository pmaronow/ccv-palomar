module

public import NearlyMinimax.LowerActivityHierarchy
public import NearlyMinimax.CardinalGlobalBandL2


@[expose] public section

/-! Fixed-constant scale reduction for actual active fine interpolation bands.
Only the alias factorial tail receives exp(L*M); the local activity exponent
is unaffected. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

def cardinalBandDimensionConstant (d : ℕ) : ℝ :=
  (100 * (d : ℝ))^2 * 16 * spatialScaleIntegralConstant d

theorem cardinalBandDimensionConstant_nonneg (d : ℕ) :
    0 ≤ cardinalBandDimensionConstant d := by
  unfold cardinalBandDimensionConstant spatialScaleIntegralConstant
  positivity

def lowerAliasSpatialA (d R : ℕ) : ℝ :=
  (R : ℝ)^2 * (2 : ℝ)^d * (1+cardinalBandDimensionConstant d)^R

def lowerAliasSpatialL (d : ℕ) (R : ℕ) (c0 K : ℝ) : ℝ :=
  c0*K*((d : ℝ)-4) + R

theorem lowerAliasSpatialA_nonneg (d R : ℕ) : 0 ≤ lowerAliasSpatialA d R := by
  unfold lowerAliasSpatialA
  have := cardinalBandDimensionConstant_nonneg d
  positivity

theorem lowerAliasSpatialL_nonneg {d R : ℕ} (hd : 4 ≤ d) {c0 K : ℝ}
    (hc0 : 0 ≤ c0) (_hK : 0 ≤ K) : 0 ≤ lowerAliasSpatialL d R c0 K := by
  unfold lowerAliasSpatialL
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  positivity

/-- Exact scalar reduction for any bounded-order band with the source cutoff. -/
theorem cardinalBandSquareBudget_cutoff_le {d r R : ℕ} {M D K c0 N : ℝ}
    (hd : 4 ≤ d) (hr : r ≤ R) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hK : 0 ≤ K) (hc0 : 0 ≤ c0) (hDK : D ≤ K*M) (hN : 0 < N)
    (hell : 1 ≤ N*Real.exp (-c0*D))
    (hH : Real.log (1+Real.log N) ≤ M) :
    (r : ℝ)^2 * (2 : ℝ)^d * cardinalBandSquareBudget d r (N*Real.exp (-c0*D)) ≤
      lowerAliasSpatialA d R * N^(4-(d : ℝ)) * Real.exp (lowerAliasSpatialL d R c0 K * M) := by
  have hC := cardinalBandDimensionConstant_nonneg d
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have he1 : Real.exp (-c0*D) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hellN : N*Real.exp (-c0*D) ≤ N := by nlinarith
  have hN1 : 1 ≤ N := hell.trans hellN
  have hHp : 0 < 1+Real.log N := by linarith [Real.log_nonneg hN1]
  have hlog : 1+Real.log (N*Real.exp (-c0*D)) ≤ 1+Real.log N :=
    add_le_add_right (Real.log_le_log (by positivity) hellN) 1
  have hlog0 : 0 ≤ 1+Real.log (N*Real.exp (-c0*D)) := by linarith [Real.log_nonneg hell]
  have hHexp : 1+Real.log N ≤ Real.exp M := by
    simpa only [Real.exp_log hHp] using Real.exp_le_exp.mpr hH
  have hexp1 : 1 ≤ Real.exp M := Real.one_le_exp_iff.mpr hM
  have hlogpower : (1+Real.log (N*Real.exp (-c0*D)))^(r-2) ≤ Real.exp ((R : ℝ)*M) := by
    calc
      _ ≤ (Real.exp M)^(r-2) := pow_le_pow_left₀ hlog0 (hlog.trans hHexp) _
      _ ≤ (Real.exp M)^R := pow_le_pow_right₀ hexp1 (by omega)
      _ = _ := (Real.exp_nat_mul M R).symm
  have hCpower : (cardinalBandDimensionConstant d)^(r-1) ≤ (1+cardinalBandDimensionConstant d)^R := by
    exact (pow_le_pow_left₀ hC (by linarith) (r-1)).trans
      (pow_le_pow_right₀ (by linarith) (by omega))
  have hr2 : (r : ℝ)^2 ≤ (R : ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left hr 2
  have hscale : (N*Real.exp (-c0*D))^(4-(d : ℝ)) ≤
      N^(4-(d : ℝ)) * Real.exp ((c0*K*((d : ℝ)-4))*M) := by
    rw [Real.mul_rpow hN.le (Real.exp_pos _).le, ← Real.exp_mul]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN.le _)
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonneg_left hDK (show 0 ≤ c0*((d : ℝ)-4) by positivity)
    nlinarith
  have hbound := mul_le_mul (mul_le_mul (mul_le_mul hr2 (le_refl ((2 : ℝ)^d)) (by positivity) (sq_nonneg _))
      hCpower (by positivity) (by positivity))
    (mul_le_mul hscale hlogpower (by positivity) (by positivity)) (by positivity) (by positivity)
  unfold cardinalBandSquareBudget cardinalBandDimensionConstant at hbound
  calc
    _ = ((r : ℝ)^2 * (2 : ℝ)^d * (cardinalBandDimensionConstant d)^(r-1)) *
        ((N*Real.exp (-c0*D))^(4-(d : ℝ)) * (1+Real.log (N*Real.exp (-c0*D)))^(r-2)) := by
      unfold cardinalBandSquareBudget cardinalBandDimensionConstant
      ring
    _ ≤ _ := hbound
    _ = _ := by
      unfold lowerAliasSpatialA lowerAliasSpatialL cardinalBandDimensionConstant
      rw [show Real.exp ((c0*K*((d : ℝ)-4)+(R : ℝ))*M) =
        Real.exp ((c0*K*((d : ℝ)-4))*M) * Real.exp ((R : ℝ)*M) by rw [← Real.exp_add]; congr 1; ring]
      ring


def lowerAliasSpatialFixedA (d : ℕ) (θ c0 : ℝ) : ℝ :=
  lowerAliasSpatialA d (lowerAliasFineTargetBound d θ c0)

def lowerAliasSpatialFixedL (d : ℕ) (θ c0 : ℝ) : ℝ :=
  lowerAliasSpatialL d (lowerAliasFineTargetBound d θ c0) c0 (((d : ℝ)+8)/4+1)

theorem lowerSaddleD_le_fixed_linear {d m x : ℝ} (hd : 0 < d)
    (hM : 1 ≤ (lowerSaddleM m x : ℝ)) :
    (lowerSaddleD d m x : ℝ) ≤ ((d+8)/4+1) * lowerSaddleM m x := by
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (d+8)/4*(lowerSaddleM m x : ℝ) by positivity)
  change (lowerSaddleD d m x : ℝ) < (d+8)/4*(lowerSaddleM m x : ℝ)+1 at hceil
  nlinarith

theorem lowerAliasSpatialFixedA_nonneg (d : ℕ) (θ c0 : ℝ) :
    0 ≤ lowerAliasSpatialFixedA d θ c0 := lowerAliasSpatialA_nonneg _ _

theorem lowerAliasSpatialFixedL_nonneg {d : ℕ} (hd : 4 ≤ d) (θ : ℝ)
    {c0 : ℝ} (hc0 : 0 ≤ c0) : 0 ≤ lowerAliasSpatialFixedL d θ c0 :=
  lowerAliasSpatialL_nonneg hd hc0 (by positivity)

/-- The actual active fine matrix bands satisfy the source's fixed-constant
alias scale estimate; their full spatial integral is derived from the
constructed cardinal matrix, never supplied as a premise. -/
theorem eventually_lowerAlias_globalBandL2_scale {s m θ τ Cτ c0 : ℝ} {d : ℕ}
    {τM : ℕ → ℝ} (hs : 1 < s) (hd : 4*s < (d : ℝ)) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (hc0 : 0 < c0) (hτc0 : τ < c0) (C : ℝ) :
    ∀ᶠ x in atTop, ∀ (r F : ℕ), 2 ≤ r →
      lowerAliasCutoff s d m θ C c0 τM x < lowerAliasTargetScale s d m θ C τM r x →
      (∫ U : Fin r → Covariate d,
        spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d)
          (lowerAliasCutoff s d m θ C c0 τM x) (lowerAliasTargetScale s d m θ C τM r x) U)^2
        ∂fullSpatialPatchDesign d r) ≤
      lowerAliasSpatialFixedA d θ c0 * (lowerSaddleN s d m θ C τM x)^(4-(d : ℝ)) *
        Real.exp (lowerAliasSpatialFixedL d θ c0 * lowerSaddleM m x) := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hd5 : 5 ≤ d := by
    have hdR : (4 : ℝ) < d := by linarith
    have hdNat : 4 < d := by exact_mod_cast hdR
    omega
  filter_upwards [eventually_lowerAlias_cutoff_guards hs hd hm hθ hcontrol hτc0 C,
    eventually_lowerAlias_row_smallness hs hd hm hθ hcontrol (Cact := 1) (by norm_num) C,
    eventually_lowerAlias_fine_targets hs hd hm hθ hcontrol hc0 C,
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_ge_atTop (1 : ℝ))]
    with x hcut hrow hfine hM
  intro r F hr2 hactive
  have hL : 1 ≤ lowerAliasCutoff s d m θ C c0 τM x := hcut.1.le
  have hT : 1 ≤ lowerAliasTargetScale s d m θ C τM r x := hL.trans hactive.le
  have hi := globalCardinalBandMatrix_square_integral_le (D := F) hd5 hr2 hL hT hactive.le
  apply hi.trans
  exact cardinalBandSquareBudget_cutoff_le (by omega) (hfine.2 r hactive) (by linarith)
    (Nat.cast_nonneg _) (by positivity) hc0.le (lowerSaddleD_le_fixed_linear hd0 hM)
    (lowerSaddleN_positive _ _ _ _ _ _ _) hL hrow.2.1

/-- The interpolation alias scale reduction for the actual canonical saddle
and actual shrunk density endpoints, with the paper's c0=tau+1. -/
theorem actual_lowerAlias_globalBandL2_scale {s a b : ℝ} {d : ℕ}
    (hs : 1 < s) (hd : 4*s < (d : ℝ)) (ha : 0 < a) (hab : a < b) (C : ℝ) :
    ∀ᶠ x in atTop,
      let m := lowerSaddleCoefficient s d (densityIntervalExponent a b)
      let θ := lowerSaddleTheta s d (densityIntervalExponent a b)
      let c0 := densityIntervalExponent a b + 1
      let τM := shrunkDensityExponent a b
      ∀ (r F : ℕ), 2 ≤ r →
        lowerAliasCutoff s d m θ C c0 τM x < lowerAliasTargetScale s d m θ C τM r x →
        (∫ U : Fin r → Covariate d,
          spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d)
            (lowerAliasCutoff s d m θ C c0 τM x) (lowerAliasTargetScale s d m θ C τM r x) U)^2
          ∂fullSpatialPatchDesign d r) ≤
        lowerAliasSpatialFixedA d θ c0 * (lowerSaddleN s d m θ C τM x)^(4-(d : ℝ)) *
          Real.exp (lowerAliasSpatialFixedL d θ c0 * lowerSaddleM m x) := by
  have hτ := densityIntervalExponent_pos ha hab
  obtain ⟨Cτ,_,hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  exact eventually_lowerAlias_globalBandL2_scale hs hd (lowerSaddleCoefficient_pos hs hd hτ)
    (lowerSaddleTheta_pos hs hd hτ) hcontrol (by linarith) (by linarith) C

end NearlyMinimax
