module

public import NearlyMinimax.SourceActivationActivity


@[expose] public section

/-! Actual global one-dummy activation at the canonical saddle. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

def SourceSaddleMark (d q : ℕ) (s a b C lam shift x : ℝ) : Type :=
  let tau := densityIntervalExponent a b
  let m := lowerSaddleCoefficient s (d : ℝ) tau
  let theta := lowerSaddleTheta s (d : ℝ) tau
  let M := lowerSaddleM m x
  let D := lowerSaddleD (d : ℝ) m x
  let N := lowerSaddleN s (d : ℝ) m theta shift (shrunkDensityExponent a b) x
  let mu := lowerSaddleMu (d : ℝ) m theta shift x
  let ell := lowerAliasCutoff s (d : ℝ) m theta shift (tau+1) (shrunkDensityExponent a b) x
  HighUnionMark (SourceRowMark d D M q (a+(M : ℝ)⁻¹) (b-(M : ℝ)⁻¹) C lam ell N mu)

def sourceSaddleUnionActivation (d k q : ℕ) (s a b C lam shift δ x : ℝ) :
    SourceSaddleMark d q s a b C lam shift x → ℝ :=
  let tau := densityIntervalExponent a b
  let m := lowerSaddleCoefficient s (d : ℝ) tau
  let theta := lowerSaddleTheta s (d : ℝ) tau
  let M := lowerSaddleM m x
  let D := lowerSaddleD (d : ℝ) m x
  let N := lowerSaddleN s (d : ℝ) m theta shift (shrunkDensityExponent a b) x
  let mu := lowerSaddleMu (d : ℝ) m theta shift x
  let ell := lowerAliasCutoff s (d : ℝ) m theta shift (tau+1) (shrunkDensityExponent a b) x
  highUnionActivation (sourceRowData d k D M q (a+(M : ℝ)⁻¹) (b-(M : ℝ)⁻¹) C lam ell N mu) δ

/-- The actual globally balanced complete-source activation has the fixed
canonical activity budget, for every mark and every spatial grid. -/
theorem sourceSaddleUnionActivation_eventually_bound (d q : ℕ) [NeZero d] (hq : 1 ≤ q)
    (s a b C lam shift δ : ℝ) (hs : 1 < s) (hd : 4*s < (d : ℝ))
    (ha : 0 < a) (hab : a < b) (hC : 0 < C) (hδ : 0 < δ) :
    ∀ᶠ x in atTop, ∀ k : ℕ, ∀ e : SourceSaddleMark d q s a b C lam shift x,
      |sourceSaddleUnionActivation d k q s a b C lam shift δ x e| ≤
        (sourceSaddleActivityConstant d q a b C lam / δ) *
          (lowerSaddleN s (d : ℝ) (lowerSaddleCoefficient s (d : ℝ) (densityIntervalExponent a b))
            (lowerSaddleTheta s (d : ℝ) (densityIntervalExponent a b)) shift (shrunkDensityExponent a b) x)^2 *
          Real.exp (shrunkDensityExponent a b (lowerSaddleM (lowerSaddleCoefficient s (d : ℝ) (densityIntervalExponent a b)) x)*
            (lowerSaddleM (lowerSaddleCoefficient s (d : ℝ) (densityIntervalExponent a b)) x : ℝ)) := by
  let m := lowerSaddleCoefficient s (d : ℝ) (densityIntervalExponent a b)
  let theta := lowerSaddleTheta s (d : ℝ) (densityIntervalExponent a b)
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd (densityIntervalExponent_pos ha hab)
  have hsmall := (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop.eventually
    (gt_mem_nhds (by linarith : (0 : ℝ) < (b-a)/2))
  filter_upwards [sourceSaddleTotalMass_eventually_bound d q s a b C lam shift hs hd ha hab, hsmall]
    with x hx hsh
  intro k e
  let M := lowerSaddleM m x
  let D := lowerSaddleD (d : ℝ) m x
  let N := lowerSaddleN s (d : ℝ) m theta shift (shrunkDensityExponent a b) x
  let mu := lowerSaddleMu (d : ℝ) m theta shift x
  let ell := lowerAliasCutoff s (d : ℝ) m theta shift (densityIntervalExponent a b+1) (shrunkDensityExponent a b) x
  have ht : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hap : 0 < a+(M : ℝ)⁻¹ := by linarith
  have hshrink : a+(M : ℝ)⁻¹ < b-(M : ℝ)⁻¹ := by change (M : ℝ)⁻¹ < (b-a)/2 at hsh; linarith
  have hb := sourceUnionActivation_bound d k D M q hq (a+(M : ℝ)⁻¹) (b-(M : ℝ)⁻¹) C lam ell N mu δ hap hshrink hC hδ e
  apply hb.trans
  have hc := div_le_div_of_nonneg_right (hx k) hδ.le
  dsimp [sourceSaddleTotalMass] at hc
  convert hc using 1 <;> ring

end NearlyMinimax
