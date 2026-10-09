module

public import NearlyMinimax.HighCardinalSpatialEnergy
public import NearlyMinimax.TargetDefectBudget


@[expose] public section

/-! Geometric count envelopes for the actual matched cardinal component
budgets, with fixed density upper bound before the density shrinking. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 def cardinalAliasSpatialComponent (d n : ℕ) (bd a η T : ℝ) : ℝ :=
  2*cardinalRawAliasCoefficient n bd a η^2 * (n : ℝ)^2*(2 : ℝ)^d*cardinalDefectSquareBudget d n T

 def cardinalTaylorSpatialComponent (d n q : ℕ) (bd C a ρ η : ℝ) : ℝ :=
  2*cardinalRawTaylorCoefficient n q bd C a ρ η^2 * (n : ℝ)^2*(2 : ℝ)^d*
    ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)^(n-1)

 theorem cardinalRawSpatialEnergyBudget_split (d n q : ℕ) (bd C a ρ η T : ℝ) :
    cardinalRawSpatialEnergyBudget d n q bd C a ρ η T =
      cardinalAliasSpatialComponent d n bd a η T + cardinalTaylorSpatialComponent d n q bd C a ρ η := by
  unfold cardinalRawSpatialEnergyBudget cardinalAliasSpatialComponent cardinalTaylorSpatialComponent
  ring

 def cardinalSpatialGeometricBase (B κ : ℝ) : ℝ := 1+B^2*max 1 κ

 theorem cardinalSpatialGeometricBase_nonneg (B κ : ℝ) : 0 ≤ cardinalSpatialGeometricBase B κ := by
  unfold cardinalSpatialGeometricBase
  have h : 0 ≤ max (1 : ℝ) κ := zero_le_one.trans (le_max_left _ _)
  positivity

 theorem cardinal_monomial_geometric_le {b B κ : ℝ} (hb : 0 ≤ b) (hbB : b ≤ B) (hκ : 0 ≤ κ) (n : ℕ) :
    (b^2)^n*κ^(n-1) ≤ cardinalSpatialGeometricBase B κ^n := by
  have hM : 1 ≤ max (1 : ℝ) κ := le_max_left _ _
  have hκp := (pow_le_pow_left₀ hκ (le_max_right (1 : ℝ) κ) (n-1)).trans
    (pow_le_pow_right₀ hM (Nat.sub_le n 1))
  have hbp := pow_le_pow_left₀ (sq_nonneg b) (pow_le_pow_left₀ hb hbB 2) n
  have h := mul_le_mul hbp hκp (pow_nonneg hκ (n-1)) (pow_nonneg (sq_nonneg B) n)
  have h2 : (B^2*max 1 κ)^n ≤ cardinalSpatialGeometricBase B κ^n :=
    pow_le_pow_left₀ (mul_nonneg (sq_nonneg B) (zero_le_one.trans hM))
      (by unfold cardinalSpatialGeometricBase; linarith only []) n
  exact h.trans (by simpa only [mul_pow] using h2)

 def cardinalInterpolationEnergyPrefactor (d : ℕ) (a : ℝ) : ℝ := 2*(2 : ℝ)^d/a^4
 def cardinalTaylorEnergyPrefactor (d q : ℕ) (C a ρ : ℝ) : ℝ :=
  2*(2 : ℝ)^d*highResponseRemainderConstant q C a ρ^2

 theorem cardinalAliasSpatialComponent_geometric_le {bd B : ℝ} (hbd : 0 ≤ bd) (hB : bd ≤ B)
    (d n : ℕ) (a η T : ℝ) (ha : 0 < a) (hT : 1 ≤ T) :
    cardinalAliasSpatialComponent d n bd a η T ≤
      cardinalInterpolationEnergyPrefactor d a * cardinalSpatialGeometricBase B (16*spatialUnaryIntegralConstant d)^n *
        (n : ℝ)^2*η^4*T^(-(d : ℝ))*(1+Real.log T)^(n-2) := by
  have hκ : 0 ≤ 16*spatialUnaryIntegralConstant d := by unfold spatialUnaryIntegralConstant; positivity
  have hp := cardinal_monomial_geometric_le hbd hB hκ n
  have hA : 0 ≤ cardinalInterpolationEnergyPrefactor d a := by unfold cardinalInterpolationEnergyPrefactor; positivity
  have hlog : 0 ≤ 1+Real.log T := by linarith [Real.log_nonneg hT]
  have h := mul_le_mul_of_nonneg_right hp
    (by positivity : 0 ≤ cardinalInterpolationEnergyPrefactor d a*(n : ℝ)^2*η^4*T^(-(d : ℝ))*(1+Real.log T)^(n-2))
  convert h using 1 <;> dsimp only [cardinalAliasSpatialComponent, cardinalRawAliasCoefficient, cardinalDefectSquareBudget, cardinalInterpolationEnergyPrefactor]
  · simp only [mul_pow, ← pow_mul]
    field_simp
    ring
  · ring

 theorem cardinalTaylorSpatialComponent_geometric_le {bd B : ℝ} (hbd : 0 ≤ bd) (hB : bd ≤ B)
    (d n q : ℕ) (C a ρ η : ℝ) :
    cardinalTaylorSpatialComponent d n q bd C a ρ η ≤
      cardinalTaylorEnergyPrefactor d q C a ρ *
        cardinalSpatialGeometricBase B ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)^n *
          (n : ℝ)^(4*q+6)*η^(4*q+4) := by
  have hκ : 0 ≤ (100*(d : ℝ))^2*16*spatialScaleIntegralConstant d := by
    unfold spatialScaleIntegralConstant
    positivity
  have hp := cardinal_monomial_geometric_le hbd hB hκ n
  have hA : 0 ≤ cardinalTaylorEnergyPrefactor d q C a ρ := by unfold cardinalTaylorEnergyPrefactor; positivity
  have hη : 0 ≤ η^(4*q+4) := by rw [show 4*q+4 = 2*(2*q+2) by omega, pow_mul]; positivity
  have h := mul_le_mul_of_nonneg_right hp
    (by positivity : 0 ≤ cardinalTaylorEnergyPrefactor d q C a ρ*(n : ℝ)^(4*q+6)*η^(4*q+4))
  convert h using 1 <;> dsimp only [cardinalTaylorSpatialComponent, cardinalRawTaylorCoefficient, cardinalTaylorEnergyPrefactor]
  · simp only [mul_pow, ← pow_mul]
    ring_nf
  · ring

end NearlyMinimax
