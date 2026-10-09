module

public import NearlyMinimax.CardinalEnergyGeometric


@[expose] public section

/-! Actual computed matched-row interpolation and Taylor budgets at the
paper's cutoffs, including omitted cutoffs below one. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 theorem target_max_one_defect_budget_le {d : ℕ} (hd : 0 < d)
    {N μ : ℝ} (hN : 1 ≤ N) (hμ : 0 < μ) (hsmall : μ*(1+Real.log N) ≤ 1) (j : ℕ) :
    (max 1 (N*(μ*(1+Real.log N))^((j : ℝ)/d)))^(-(d : ℝ)) *
      (1+Real.log (max 1 (N*(μ*(1+Real.log N))^((j : ℝ)/d))))^j ≤ N^(-(d : ℝ))/μ^j := by
  have hNpos := lt_of_lt_of_le zero_lt_one hN
  have hH : 0 < 1+Real.log N := by linarith [Real.log_nonneg hN]
  let T := N*(μ*(1+Real.log N))^((j : ℝ)/d)
  by_cases hT : 1 ≤ T
  · rw [max_eq_right hT]
    exact target_cutoff_defect_budget_le (Nat.ne_of_gt hd) hNpos hμ j hT
      (target_cutoff_le_base hd hNpos.le (mul_nonneg hμ.le hH.le) hsmall j)
  · rw [max_eq_left (le_of_not_ge hT), Real.one_rpow, Real.log_one, add_zero, one_pow, mul_one]
    exact omitted_target_inverse_budget_ge_one (Nat.ne_of_gt hd) hN hμ j (lt_of_not_ge hT)

 def matchedCardinalTargetCutoff (d j : ℕ) (N μ : ℝ) : ℝ := max 1 (N*(μ*(1+Real.log N))^((j : ℝ)/d))

 theorem cardinalAliasSpatialComponent_allocated_le {bd B : ℝ} (hbd : 0 ≤ bd) (hB : bd ≤ B)
    {d : ℕ} (hd : 0 < d) (j : ℕ) (a η : ℝ) (ha : 0 < a)
    {N μ : ℝ} (hN : 1 ≤ N) (hμ : 0 < μ) (hsmall : μ*(1+Real.log N) ≤ 1) :
    cardinalAliasSpatialComponent d (2+j) bd a η (matchedCardinalTargetCutoff d j N μ) ≤
      cardinalInterpolationEnergyPrefactor d a *
        cardinalSpatialGeometricBase B (16*spatialUnaryIntegralConstant d)^(2+j) *
          (2+j : ℕ)^2 * η^4*N^(-(d : ℝ))/μ^j := by
  have h := cardinalAliasSpatialComponent_geometric_le hbd hB d (2+j) a η (matchedCardinalTargetCutoff d j N μ) ha (le_max_left _ _)
  have hi := target_max_one_defect_budget_le hd hN hμ hsmall j
  have hA : 0 ≤ cardinalInterpolationEnergyPrefactor d a := by unfold cardinalInterpolationEnergyPrefactor; positivity
  have hBase := cardinalSpatialGeometricBase_nonneg B (16*spatialUnaryIntegralConstant d)
  have hh := mul_le_mul_of_nonneg_left hi
    (by positivity : 0 ≤ cardinalInterpolationEnergyPrefactor d a *
      cardinalSpatialGeometricBase B (16*spatialUnaryIntegralConstant d)^(2+j)*(2+j : ℕ)^2*η^4)
  apply h.trans
  convert hh using 1 <;> (try dsimp [matchedCardinalTargetCutoff]) <;> (try simp only [show 2+j-2=j by omega]) <;> ring

 theorem cardinalTaylorSpatialComponent_allocated_le {bd B : ℝ} (hbd : 0 ≤ bd) (hB : bd ≤ B)
    (d n q : ℕ) (C a ρ η : ℝ) {N : ℝ} (hN : 0 < N) (hsmall : η^(4*q)*N^d ≤ 1) :
    cardinalTaylorSpatialComponent d n q bd C a ρ η ≤
      cardinalTaylorEnergyPrefactor d q C a ρ *
        cardinalSpatialGeometricBase B ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)^n *
          (n : ℝ)^(4*q+6)*η^4*N^(-(d : ℝ)) := by
  have h := cardinalTaylorSpatialComponent_geometric_le hbd hB d n q C a ρ η
  have hi := response_taylor_budget_absorption hN q d hsmall
  have hA : 0 ≤ cardinalTaylorEnergyPrefactor d q C a ρ := by unfold cardinalTaylorEnergyPrefactor; positivity
  have hBase := cardinalSpatialGeometricBase_nonneg B ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)
  have hh := mul_le_mul_of_nonneg_left hi
    (by positivity : 0 ≤ cardinalTaylorEnergyPrefactor d q C a ρ *
      cardinalSpatialGeometricBase B ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)^n*(n : ℝ)^(4*q+6))
  apply h.trans
  apply hh.trans_eq
  rw [Real.rpow_neg hN.le, Real.rpow_natCast]
  ring

 def cardinalInterpolationFactorialConstant (d : ℕ) (B a Csharp : ℝ) : ℝ :=
  cardinalInterpolationEnergyPrefactor d a *
    defectTailConstant Csharp (cardinalSpatialGeometricBase B (16*spatialUnaryIntegralConstant d)*2^2)

 theorem finite_cardinal_interpolation_budget_le {bd B : ℝ} (hbd : 0 ≤ bd) (hB : bd ≤ B)
    {d : ℕ} (hd : 0 < d) (J : ℕ) (a η Csharp : ℝ) (ha : 0 < a) (hCs : 0 ≤ Csharp)
    {N μ : ℝ} (hN : 1 ≤ N) (hμ : 0 < μ) (hsmall : μ*(1+Real.log N) ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp*μ) (2+j) *
      cardinalAliasSpatialComponent d (2+j) bd a η (matchedCardinalTargetCutoff d j N μ)) ≤
      cardinalInterpolationFactorialConstant d B a Csharp * η^4*N^(-(d : ℝ))*μ^2 := by
  let P := cardinalInterpolationEnergyPrefactor d a * η^4*N^(-(d : ℝ))
  have hP : 0 ≤ P := by dsimp [P, cardinalInterpolationEnergyPrefactor]; positivity [lt_of_lt_of_le zero_lt_one hN]
  have hBase := cardinalSpatialGeometricBase_nonneg B (16*spatialUnaryIntegralConstant d)
  have h := finite_interpolation_defect_tail_le hP hCs
    (by positivity : 0 ≤ cardinalSpatialGeometricBase B (16*spatialUnaryIntegralConstant d)*2^2) hμ J
    (fun n => cardinalAliasSpatialComponent d n bd a η (matchedCardinalTargetCutoff d (n-2) N μ)) (by
      intro j hj
      have hb := cardinalAliasSpatialComponent_allocated_le hbd hB hd j a η ha hN hμ hsmall
      have hp := polynomial_count_factor_le (2+j) 2
      have hm := mul_le_mul_of_nonneg_left hp
        (by positivity [lt_of_lt_of_le zero_lt_one hN] : 0 ≤ P*cardinalSpatialGeometricBase B (16*spatialUnaryIntegralConstant d)^(2+j)/μ^j)
      rw [show 2+j-2=j by omega]
      apply hb.trans
      convert hm using 1 <;> dsimp [P] <;> (try simp only [mul_pow, show 2+j-2=j by omega]) <;> ring)
  simpa only [show ∀ j : ℕ, 2+j-2=j from fun j => by omega] using
    h.trans_eq (by unfold cardinalInterpolationFactorialConstant; dsimp [P]; ring)

 def cardinalTaylorFactorialConstant (d q : ℕ) (B C a ρ Csharp : ℝ) : ℝ :=
  cardinalTaylorEnergyPrefactor d q C a ρ * defectTailConstant Csharp
    (cardinalSpatialGeometricBase B ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)*2^(4*q+6))

 theorem finite_cardinal_taylor_budget_le {bd B : ℝ} (hbd : 0 ≤ bd) (hB : bd ≤ B)
    (d q J : ℕ) (C a ρ η Csharp : ℝ) (hCs : 0 ≤ Csharp)
    {N μ : ℝ} (hN : 0 < N) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hsmall : η^(4*q)*N^d ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp*μ) (2+j) *
      cardinalTaylorSpatialComponent d (2+j) q bd C a ρ η) ≤
      cardinalTaylorFactorialConstant d q B C a ρ Csharp * η^4*N^(-(d : ℝ))*μ^2 := by
  let P := cardinalTaylorEnergyPrefactor d q C a ρ * η^4*N^(-(d : ℝ))
  have hP : 0 ≤ P := by dsimp [P, cardinalTaylorEnergyPrefactor]; positivity
  have h := finite_taylor_count_energy_tail_le hP hCs
    (cardinalSpatialGeometricBase_nonneg B ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)) hμ hμ1 (4*q+6) J
    (fun n => cardinalTaylorSpatialComponent d n q bd C a ρ η)
    (fun j _ => (cardinalTaylorSpatialComponent_allocated_le hbd hB d (2+j) q C a ρ η hN hsmall).trans_eq
      (by dsimp [P]; ring))
  exact h.trans_eq (by unfold cardinalTaylorFactorialConstant; dsimp [P]; ring)

end NearlyMinimax
