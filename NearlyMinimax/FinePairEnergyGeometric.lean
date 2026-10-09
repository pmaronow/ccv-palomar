module

public import NearlyMinimax.FinePairAliasSpatialEnergy
public import NearlyMinimax.FieldTailSummation


@[expose] public section

/-! Fixed geometric count envelopes for the actual pair component budgets.
Constants are chosen before the exterior degree and the selected count. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 def finePairSpatialEnergyPrefactor (d q : ℕ) (ad bd C a ρ : ℝ) : ℝ :=
  |finePairDensityPrefactor ad bd|^2 * finePairResponseActionBudget d q C a ρ ^ 2 *
    Real.exp (4*exteriorTau ((ad+bd)/(bd-ad)))

 theorem finePairSpatialEnergyPrefactor_nonneg (d q : ℕ) (ad bd C a ρ : ℝ) :
    0 ≤ finePairSpatialEnergyPrefactor d q ad bd C a ρ := by
  unfold finePairSpatialEnergyPrefactor
  positivity

 theorem finePairResponseCoefficient_square_le (d n M q : ℕ) (ad bd C a ρ η : ℝ)
    (haD : 0 < ad) (hab : ad < bd) :
    (finePairDensityCoefficientBudget ad bd M n *
      (finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2))^2 ≤
      finePairSpatialEnergyPrefactor d q ad bd C a ρ * (bd^2)^n * (n : ℝ)^4 * η^4 *
        Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) := by
  let tau := exteriorTau ((ad+bd)/(bd-ad))
  have hc : Real.cosh ((M+2 : ℕ)*tau) ≤ Real.exp ((M+2 : ℕ)*tau) := by
    dsimp [tau]
    rw [← exterior_rule_variation ad bd haD hab (M+2) (by omega)]
    exact exterior_rule_variation_le_exp ad bd haD hab (M+2) (by omega)
  have hsq := (sq_le_sq₀ (Real.cosh_pos _).le (Real.exp_pos _).le).mpr hc
  have hb := (haD.trans hab).le
  have h := mul_le_mul_of_nonneg_left hsq
    (sq_nonneg (|finePairDensityPrefactor ad bd| *bd^n*
      (finePairResponseActionBudget d q C a ρ*(n : ℝ)^2*η^2)))
  calc
    _ = (|finePairDensityPrefactor ad bd| *bd^n*
      (finePairResponseActionBudget d q C a ρ*(n : ℝ)^2*η^2))^2 * Real.cosh ((M+2 : ℕ)*tau)^2 := by
      unfold finePairDensityCoefficientBudget
      dsimp [tau]
      ring
    _ ≤ (|finePairDensityPrefactor ad bd| *bd^n*
      (finePairResponseActionBudget d q C a ρ*(n : ℝ)^2*η^2))^2 * Real.exp ((M+2 : ℕ)*tau)^2 := h
    _ = _ := by
      rw [← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [Nat.cast_add, Nat.cast_ofNat]
      have he : 2*(((M : ℝ)+2)*tau) = 4*tau + 2*tau*M := by ring
      rw [he, Real.exp_add]
      unfold finePairSpatialEnergyPrefactor
      dsimp [tau]
      simp only [mul_pow, ← pow_mul]
      ring

 def finePairFieldGeometricBase (d : ℕ) (bd : ℝ) : ℝ :=
  1 + bd^2 * fineFieldSubsetEnergyBase d

 theorem finePairFieldGeometricBase_nonneg (d : ℕ) (bd : ℝ) :
    0 ≤ finePairFieldGeometricBase d bd := by
  unfold finePairFieldGeometricBase fineFieldSubsetEnergyBase
  positivity

 theorem finePairEvenActionSpatialBudget_geometric_le (d n M q : ℕ)
    (ad bd C a ρ η T0 : ℝ) (haD : 0 < ad) (hab : ad < bd) :
    finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0 ≤
      finePairSpatialEnergyPrefactor d q ad bd C a ρ * finePairFieldGeometricBase d bd ^ n *
        (n : ℝ)^12 * η^4 * Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) *
          (T0^(2-(d : ℝ)))^2 := by
  have h := mul_le_mul_of_nonneg_right (finePairResponseCoefficient_square_le d n M q ad bd C a ρ η haD hab)
    (by unfold fineFieldSubsetEnergyBase; positivity : 0 ≤ fineFieldSubsetEnergyBase d ^ n * (n : ℝ)^8*(T0^(2-(d : ℝ)))^2)
  have hpow : (bd^2*fineFieldSubsetEnergyBase d)^n ≤ finePairFieldGeometricBase d bd ^ n :=
    pow_le_pow_left₀ (by unfold fineFieldSubsetEnergyBase; positivity)
      (by unfold finePairFieldGeometricBase; linarith only []) n
  have hm := mul_le_mul_of_nonneg_right hpow
    (by positivity [finePairSpatialEnergyPrefactor_nonneg d q ad bd C a ρ] :
      0 ≤ finePairSpatialEnergyPrefactor d q ad bd C a ρ * (n : ℝ)^12 * η^4 *
        Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M)*(T0^(2-(d : ℝ)))^2)
  unfold finePairEvenActionSpatialBudget
  have hh := h.trans (by
    convert hm using 1 <;> simp only [mul_pow] <;> ring)
  convert hh using 1 <;> ring

 theorem spatialInverseFourConstant_nonneg (d : ℕ) : 0 ≤ spatialInverseFourConstant d := by
  unfold spatialInverseFourConstant
  positivity

 def finePairAliasGeometricBase (d : ℕ) (bd : ℝ) : ℝ := 1 + bd^2*(2 : ℝ)^d

 theorem finePairAliasGeometricBase_nonneg (d : ℕ) (bd : ℝ) :
    0 ≤ finePairAliasGeometricBase d bd := by unfold finePairAliasGeometricBase; positivity

 theorem finePairAliasActionSpatialBudget_geometric_le (d n M q : ℕ)
    (ad bd C a ρ η T0 : ℝ) (haD : 0 < ad) (hab : ad < bd) (hT0 : 0 < T0) :
    finePairAliasActionSpatialBudget d n M q ad bd C a ρ η T0 ≤
      (finePairSpatialEnergyPrefactor d q ad bd C a ρ * 6*(2 : ℝ)^d*spatialInverseFourConstant d) *
        finePairAliasGeometricBase d bd ^ n * (n : ℝ)^8 * η^4 *
          Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) / T0^(d-4) := by
  have hPref := finePairSpatialEnergyPrefactor_nonneg d q ad bd C a ρ
  have hCoeff := finePairResponseCoefficient_square_le d n M q ad bd C a ρ η haD hab
  have hc : (n.choose 2 : ℝ)^2 ≤ (n : ℝ)^4 := by
    have h : (n.choose 2 : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast Nat.choose_le_pow n 2
    have h2 := pow_le_pow_left₀ (Nat.cast_nonneg (n.choose 2)) h 2
    simpa only [← pow_mul] using h2
  have hv : (2 : ℝ)^(d*(n-2)) ≤ (2 : ℝ)^(d*n) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left d (Nat.sub_le _ _))
  have hk : 0 ≤ 6*(2 : ℝ)^d*spatialInverseFourConstant d / T0^(d-4) := by
    have hi := spatialInverseFourConstant_nonneg d
    positivity

  have h := mul_le_mul (mul_le_mul hCoeff hc (sq_nonneg _) (by positivity)) hv (by positivity)
    (by positivity [finePairSpatialEnergyPrefactor_nonneg d q ad bd C a ρ])
  have h' := mul_le_mul_of_nonneg_right h hk
  have hpow : (bd^2*(2 : ℝ)^d)^n ≤ finePairAliasGeometricBase d bd ^ n :=
    pow_le_pow_left₀ (by positivity) (by unfold finePairAliasGeometricBase; linarith only []) n
  have hpow' := mul_le_mul_of_nonneg_right hpow
    (by positivity [finePairSpatialEnergyPrefactor_nonneg d q ad bd C a ρ, spatialInverseFourConstant_nonneg d] :
      0 ≤ finePairSpatialEnergyPrefactor d q ad bd C a ρ*(n : ℝ)^8*η^4*
        Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M)*
          (6*(2 : ℝ)^d*spatialInverseFourConstant d/T0^(d-4)))
  apply h'.trans
  convert hpow' using 1 <;> (try simp only [mul_pow, ← pow_mul]) <;> ring

end NearlyMinimax
