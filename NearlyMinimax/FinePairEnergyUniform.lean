module

public import NearlyMinimax.FinePairEnergyGeometric


@[expose] public section

/-! The constants in the genuine pair energy bounds are uniform over all
legal interior density intervals and therefore precede M and its shrinking. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem finePairDensityPrefactor_eq {ad bd : ℝ} (haD : 0 < ad) (hab : ad < bd) :
    finePairDensityPrefactor ad bd = ((bd-ad)/ad)^2 := by
  unfold finePairDensityPrefactor densityMargin
  field_simp [haD.ne', (haD.trans hab).ne', (sub_pos.mpr hab).ne']
  ring

 def finePairUniformSpatialPrefactor (d q : ℕ) (aD bD C a ρ c0 : ℝ) : ℝ :=
  ((bD-aD)/aD)^4 * finePairResponseActionBudget d q C a ρ ^ 2 * Real.exp (4*c0)

 theorem finePairUniformSpatialPrefactor_nonneg (d q : ℕ) (aD bD C a ρ c0 : ℝ) :
    0 ≤ finePairUniformSpatialPrefactor d q aD bD C a ρ c0 := by
  unfold finePairUniformSpatialPrefactor
  positivity

 theorem finePairSpatialEnergyPrefactor_uniform_le {aD bD ad bd c0 : ℝ}
    (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0) (d q : ℕ) (C a ρ : ℝ) :
    finePairSpatialEnergyPrefactor d q ad bd C a ρ ≤
      finePairUniformSpatialPrefactor d q aD bD C a ρ c0 := by
  have had : 0 < ad := haD.trans_le ha
  have hratio0 : 0 ≤ (bd-ad)/ad := div_nonneg (sub_nonneg.mpr hab.le) had.le
  have hratio : (bd-ad)/ad ≤ (bD-aD)/aD := by
    apply (div_le_div_iff₀ had haD).mpr
    have hbD : 0 < bD := (had.trans hab).trans_le hb
    nlinarith only [ha, hb, haD, had, hbD, mul_nonneg (sub_nonneg.mpr ha) hbD.le,
      mul_nonneg (sub_nonneg.mpr hb) haD.le]
  have hp := pow_le_pow_left₀ hratio0 hratio 4
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htau (by norm_num : (0 : ℝ) ≤ 4))
  have h := mul_le_mul (mul_le_mul_of_nonneg_right hp
    (sq_nonneg (finePairResponseActionBudget d q C a ρ))) hexp (Real.exp_pos _).le
      (by positivity : 0 ≤ ((bD-aD)/aD)^4*finePairResponseActionBudget d q C a ρ^2)
  unfold finePairSpatialEnergyPrefactor finePairUniformSpatialPrefactor
  rw [finePairDensityPrefactor_eq had hab, abs_of_nonneg (sq_nonneg _)]
  simpa only [← pow_mul] using h

 theorem finePairFieldGeometricBase_mono {bd bD : ℝ} (hbd : 0 ≤ bd) (hb : bd ≤ bD) (d : ℕ) :
    finePairFieldGeometricBase d bd ≤ finePairFieldGeometricBase d bD := by
  have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbd hb 2)
    (by unfold fineFieldSubsetEnergyBase; positivity : 0 ≤ fineFieldSubsetEnergyBase d)
  unfold finePairFieldGeometricBase
  linarith only [h]

 theorem finePairAliasGeometricBase_mono {bd bD : ℝ} (hbd : 0 ≤ bd) (hb : bd ≤ bD) (d : ℕ) :
    finePairAliasGeometricBase d bd ≤ finePairAliasGeometricBase d bD := by
  have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbd hb 2) (by positivity : 0 ≤ (2 : ℝ)^d)
  unfold finePairAliasGeometricBase
  linarith only [h]

 theorem finePairEvenActionSpatialBudget_uniform_geometric_le {aD bD ad bd c0 : ℝ}
    (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0) (d n M q : ℕ) (C a ρ η T0 : ℝ) :
    finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0 ≤
      finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * finePairFieldGeometricBase d bD ^ n *
        (n : ℝ)^12 * η^4 * Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) * (T0^(2-(d : ℝ)))^2 := by
  have had := haD.trans_le ha
  have h := finePairEvenActionSpatialBudget_geometric_le d n M q ad bd C a ρ η T0 had hab
  have hp := finePairSpatialEnergyPrefactor_uniform_le haD ha hb hab htau d q C a ρ
  have hbase := pow_le_pow_left₀ (finePairFieldGeometricBase_nonneg d bd)
    (finePairFieldGeometricBase_mono (had.trans hab).le hb d) n
  have hmul := mul_le_mul hp hbase (pow_nonneg (finePairFieldGeometricBase_nonneg d bd) n)
    (finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0)
  have hh := mul_le_mul_of_nonneg_right hmul
    (by positivity : 0 ≤ (n : ℝ)^12*η^4*Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M)*(T0^(2-(d : ℝ)))^2)
  exact h.trans (by convert hh using 1 <;> ring)

 theorem finePairAliasActionSpatialBudget_uniform_geometric_le {aD bD ad bd c0 : ℝ}
    (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0) (d n M q : ℕ) (C a ρ η T0 : ℝ) (hT0 : 0 < T0) :
    finePairAliasActionSpatialBudget d n M q ad bd C a ρ η T0 ≤
      (finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * 6*(2 : ℝ)^d*spatialInverseFourConstant d) *
        finePairAliasGeometricBase d bD ^ n * (n : ℝ)^8 * η^4 *
          Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) / T0^(d-4) := by
  have had := haD.trans_le ha
  have h := finePairAliasActionSpatialBudget_geometric_le d n M q ad bd C a ρ η T0 had hab hT0
  have hp := finePairSpatialEnergyPrefactor_uniform_le haD ha hb hab htau d q C a ρ
  have hbase := pow_le_pow_left₀ (finePairAliasGeometricBase_nonneg d bd)
    (finePairAliasGeometricBase_mono (had.trans hab).le hb d) n
  have hmul := mul_le_mul hp hbase (pow_nonneg (finePairAliasGeometricBase_nonneg d bd) n)
    (finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0)
  have hi := spatialInverseFourConstant_nonneg d
  have hh := mul_le_mul_of_nonneg_right hmul
    (by positivity : 0 ≤ 6*(2 : ℝ)^d*spatialInverseFourConstant d*(n : ℝ)^8*η^4*
      Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M)/T0^(d-4))
  exact h.trans (by convert hh using 1 <;> ring)

end NearlyMinimax
