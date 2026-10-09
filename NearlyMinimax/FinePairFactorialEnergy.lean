module

public import NearlyMinimax.FinePairEnergyUniform


@[expose] public section

/-! Genuine finite factorial sums of the computed pair spatial budgets.
Every constant is fixed before the degree, count cutoff and density shrinking. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 def finePairFieldFactorialConstant (d q : ℕ) (aD bD C a ρ c0 Csharp : ℝ) : ℝ :=
  finePairUniformSpatialPrefactor d q aD bD C a ρ c0 *
    fieldTailConstant Csharp (finePairFieldGeometricBase d bD * 2^12)

 theorem finite_fine_pair_field_budget_le {aD bD ad bd c0 : ℝ}
    (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0) (d M q J : ℕ)
    (C a ρ η T0 Csharp μ : ℝ) (hCs : 0 ≤ Csharp) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp*μ) (4+j) *
      finePairEvenActionSpatialBudget d (4+j) M q ad bd C a ρ η T0) ≤
      finePairFieldFactorialConstant d q aD bD C a ρ c0 Csharp * η^4 *
        Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) * (T0^(2-(d : ℝ)))^2 * μ^4 := by
  let P := finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * η^4 *
    Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) * (T0^(2-(d : ℝ)))^2
  have hP : 0 ≤ P := by dsimp [P]; positivity [finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0]
  have h := finite_polynomial_field_count_tail_le hP hCs (finePairFieldGeometricBase_nonneg d bD)
    hμ hμ1 12 J (fun n => finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0)
    (fun j _ => (finePairEvenActionSpatialBudget_uniform_geometric_le haD ha hb hab htau d (4+j) M q C a ρ η T0).trans_eq
      (by dsimp [P]; ring))
  exact h.trans_eq (by unfold finePairFieldFactorialConstant; dsimp [P]; ring)

 def finePairAliasFactorialConstant (d q : ℕ) (aD bD C a ρ c0 Csharp : ℝ) : ℝ :=
  aliasTailConstant
    (finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * 6*(2 : ℝ)^d*spatialInverseFourConstant d)
    Csharp (finePairAliasGeometricBase d bD * 2^8) (2*c0)

 theorem finite_fine_pair_alias_budget_le {aD bD ad bd c0 : ℝ}
    (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0) (hc0 : 0 ≤ c0) (d M q J : ℕ)
    (C a ρ η T0 Csharp μ : ℝ) (hT0 : 0 < T0) (hCs : 0 ≤ Csharp) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp*μ) (M+1+j) *
      finePairAliasActionSpatialBudget d (M+1+j) M q ad bd C a ρ η T0) ≤
      finePairAliasFactorialConstant d q aD bD C a ρ c0 Csharp * (η^4 / T0^(d-4)) *
        poissonCountWeight (finePairAliasFactorialConstant d q aD bD C a ρ c0 Csharp * μ) (M+1) := by
  let A := finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * 6*(2 : ℝ)^d*spatialInverseFourConstant d
  have hA : 0 ≤ A := by dsimp [A]; positivity [finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0, spatialInverseFourConstant_nonneg d]
  have hP : 0 ≤ η^4 / T0^(d-4) := by positivity
  have hBase := finePairAliasGeometricBase_nonneg d bD
  apply finite_alias_energy_tail_le hA hP hCs (by positivity : 0 ≤ finePairAliasGeometricBase d bD * 2^8)
    (by positivity : 0 ≤ 2*c0) hμ hμ1 M J (fun n => finePairAliasActionSpatialBudget d n M q ad bd C a ρ η T0)
  intro j hj
  let n := M+1+j
  have h := finePairAliasActionSpatialBudget_uniform_geometric_le haD ha hb hab htau d n M q C a ρ η T0 hT0
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left htau (by norm_num : (0 : ℝ) ≤ 2)) (Nat.cast_nonneg M))
  have hp := polynomial_count_factor_le n 8
  have hmul := mul_le_mul hp he (Real.exp_pos _).le (by positivity : 0 ≤ ((2 : ℝ)^8)^n)
  have hh := mul_le_mul_of_nonneg_left hmul
    (by positivity : 0 ≤ A*finePairAliasGeometricBase d bD ^ n*η^4/T0^(d-4))
  apply h.trans
  convert hh using 1 <;> dsimp [A, n] <;> (try simp only [mul_pow]) <;> ring

end NearlyMinimax
