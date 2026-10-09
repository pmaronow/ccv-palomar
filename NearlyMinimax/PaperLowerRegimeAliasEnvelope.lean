module

public import NearlyMinimax.PaperLowerRegimeSource
public import NearlyMinimax.OrdinaryFineAliasGeometryEnvelope
public import NearlyMinimax.HighSpatialEnvelopes
public import NearlyMinimax.FinePairEnergyUniform


@[expose] public section

/-! True universal ordinary-plus-pair alias geometry in every Reg(K),
with fixed spatial exponential/count constants before the tuple. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable

def paperRegimeAliasGeometryEnvelope {d : ℕ} (C : ModelConstants d)
    (K Cfr a rho : ℝ) (M D q n F : ℕ) (N mu eta : ℝ)
    (U : Fin n → Covariate d) : ℝ :=
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  let ell := N*Real.exp (-c0*(D : ℝ))
  2*(ordinaryFineAliasFamilyResponseSquareEnvelope (F := F)
      (ordinaryFineAliasTargetSet d D ell N mu) M (paperRegimeFineTargetBound d K c0) q
      C.densityLower C.densityUpper c0 Cfr a rho eta ell
      (fun r => higherBandTargetScale d r N mu) U +
    finePairAliasGeometryEnvelope (C.densityLower+(M : ℝ)⁻¹) (C.densityUpper-(M : ℝ)⁻¹)
      ell N M q Cfr a rho eta U)

def paperRegimeAliasSpatialPrefactor {d : ℕ} (C : ModelConstants d)
    (K Cfr a rho : ℝ) (q : ℕ) : ℝ :=
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  2*(ordinaryAliasFamilySpatialPrefactor d q (paperRegimeFineTargetBound d K c0)
      C.densityLower C.densityUpper c0 Cfr a rho +
    finePairUniformSpatialPrefactor d q C.densityLower C.densityUpper Cfr a rho c0*
      6*(2 : ℝ)^d*spatialInverseFourConstant d)

def paperRegimeAliasSpatialBase {d : ℕ} (C : ModelConstants d) : ℝ :=
  1+ordinaryAliasSpatialResponseBase d C.densityUpper+
    3*finePairAliasGeometricBase d C.densityUpper*2^8

def paperRegimeAliasSpatialExponent {d : ℕ} (C : ModelConstants d) (K : ℝ) : ℝ :=
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  lowerAliasSpatialL d (paperRegimeFineTargetBound d K c0) c0 (paperLowerRegimeDegreeSlope d+1)+
    c0*(paperLowerRegimeDegreeSlope d+1)*((d : ℝ)-4)

theorem paperRegimeAliasGeometryEnvelope_nonneg {d : ℕ} (C : ModelConstants d)
    (K Cfr a rho : ℝ) (M D q n F : ℕ) (N mu eta : ℝ)
    (U : Fin n → Covariate d) : 0 ≤ paperRegimeAliasGeometryEnvelope C K Cfr a rho M D q n F N mu eta U := by
  unfold paperRegimeAliasGeometryEnvelope
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  apply add_nonneg
  · exact ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg (F := F) _ _ _ _ _ _ _ _ _ _ _ _ _ U
  · exact finePairAliasGeometryEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ U

theorem paperRegimeAliasSpatialPrefactor_nonneg {d : ℕ} (C : ModelConstants d)
    (K Cfr a rho : ℝ) (q : ℕ) : 0 ≤ paperRegimeAliasSpatialPrefactor C K Cfr a rho q := by
  unfold paperRegimeAliasSpatialPrefactor
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  apply add_nonneg
  · exact ordinaryAliasFamilySpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _
  · have hp := finePairUniformSpatialPrefactor_nonneg d q C.densityLower C.densityUpper Cfr a rho
      (densityIntervalExponent C.densityLower C.densityUpper+1)
    positivity [spatialInverseFourConstant_nonneg d]

theorem paperRegimeAliasSpatialBase_nonneg {d : ℕ} (C : ModelConstants d) :
    0 ≤ paperRegimeAliasSpatialBase C := by
  unfold paperRegimeAliasSpatialBase ordinaryAliasSpatialResponseBase ordinaryAliasSpatialCountBase
  positivity [finePairAliasGeometricBase_nonneg d C.densityUpper]

theorem paperRegimeAliasSpatialExponent_nonneg {d : ℕ} (hd : 5 ≤ d)
    (C : ModelConstants d) (K : ℝ) : 0 ≤ paperRegimeAliasSpatialExponent C K := by
  have hab : C.densityLower < C.densityUpper := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have hc0 : 0 ≤ densityIntervalExponent C.densityLower C.densityUpper+1 := by
    linarith [densityIntervalExponent_pos C.densityLower_pos hab]
  have hAD : 0 ≤ paperLowerRegimeDegreeSlope d+1 := by linarith [paperLowerRegimeDegreeSlope_positive d]
  have hdR : (0 : ℝ) ≤ (d : ℝ)-4 := by
    have hh : (5 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold paperRegimeAliasSpatialExponent
  exact add_nonneg (lowerAliasSpatialL_nonneg (by omega) hc0 hAD) (by positivity)

theorem paperRegime_cutoff_inverse_power {d : ℕ} {N c0 : ℝ} (hN : 0 < N) (D : ℕ) :
    1/(N*Real.exp (-c0*(D : ℝ)))^((d : ℝ)-4) =
      N^(4-(d : ℝ))*Real.exp (c0*(D : ℝ)*((d : ℝ)-4)) := by
  rw [Real.mul_rpow hN.le (Real.exp_pos _).le,← Real.exp_mul,one_div,mul_inv,
    ← Real.rpow_neg hN.le,← Real.exp_neg]
  congr 1 <;> congr 1 <;> ring

theorem paperLowerRegime_alias_geometry_integrable_and_bound {d : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (K Cfr a rho : ℝ) (M D q : ℕ) (N mu eta : ℝ)
    (R : PaperLowerRegime C Q K M D N mu eta)
    (H : PaperRegimeHierarchy d K (densityIntervalExponent C.densityLower C.densityUpper+1) 1 1 M D N mu)
    (hresolution : highCenterResolutionThreshold C ≤ (M : ℝ))
    (htau : shrunkDensityExponent C.densityLower C.densityUpper M ≤
      densityIntervalExponent C.densityLower C.densityUpper+1) (n F : ℕ) :
    Integrable (paperRegimeAliasGeometryEnvelope C K Cfr a rho M D q n F N mu eta)
      (fullSpatialPatchDesign d n) ∧
    (∫ U, paperRegimeAliasGeometryEnvelope C K Cfr a rho M D q n F N mu eta U
      ∂fullSpatialPatchDesign d n) ≤ paperRegimeAliasSpatialPrefactor C K Cfr a rho q*
        (eta^4*Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ))*N^(4-(d : ℝ)))*
        Real.exp (paperRegimeAliasSpatialExponent C K*(M : ℝ))*(paperRegimeAliasSpatialBase C)^n := by
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  let ell := N*Real.exp (-c0*(D : ℝ))
  let I := ordinaryFineAliasTargetSet d D ell N mu
  let Rt := paperRegimeFineTargetBound d K c0
  let A := paperLowerRegimeDegreeSlope d+1
  let O := ordinaryAliasFamilySpatialPrefactor d q Rt C.densityLower C.densityUpper c0 Cfr a rho
  let P := finePairUniformSpatialPrefactor d q C.densityLower C.densityUpper Cfr a rho c0*
    6*(2 : ℝ)^d*spatialInverseFourConstant d
  let L1 := lowerAliasSpatialL d Rt c0 A
  let L2 := c0*A*((d : ℝ)-4)
  let W := eta^4*Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ))*N^(4-(d : ℝ))
  have hab : C.densityLower < C.densityUpper := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have hc0 : 0 ≤ c0 := by dsimp [c0]; linarith [densityIntervalExponent_pos C.densityLower_pos hab]
  have hA : 0 ≤ A := by dsimp [A]; linarith [paperLowerRegimeDegreeSlope_positive d]
  have hdR : (0 : ℝ) ≤ (d : ℝ)-4 := by
    have hh : (5 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one R.scale
  have hell : 1 ≤ ell := H.cutoff.le
  have hellN : ell ≤ N := by
    have he : Real.exp (-c0*(D : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
      (by nlinarith [show (0 : ℝ) ≤ D from Nat.cast_nonneg D])
    exact (mul_le_mul_of_nonneg_left he hN.le).trans_eq (mul_one N)
  have hI (r : ℕ) (hr : r ∈ I) : 2 ≤ r ∧ r ≤ Rt := by
    have hh := (Finset.mem_filter.mp hr).2
    exact ⟨by omega,H.target_count r hh.2⟩
  have hLT (r : ℕ) (hr : r ∈ I) : ell ≤ higherBandTargetScale d r N mu :=
    (Finset.mem_filter.mp hr).2.2.le
  have ho := ordinaryFineAliasFamilyResponseSquareEnvelope_integrable_and_scale_le (n := n) (F := F)
    hd I hI C.densityLower C.densityUpper c0 Cfr a rho eta D A N
    (C.densityLower_pos.trans hab).le (Nat.cast_nonneg D) hA hc0 (R.degree_linear H.resolution)
    hN hell H.logarithm _ hLT q
  have hp := finePairAliasGeometryEnvelope_integrable_and_le (n := n) (by omega : 4 < d)
    (C.densityLower+(M : ℝ)⁻¹) (C.densityUpper-(M : ℝ)⁻¹) ell N
    (lt_of_lt_of_le zero_lt_one hell) hellN M q Cfr a rho eta
  refine ⟨(ho.1.add hp.1).const_mul 2,?_⟩
  change (∫ U, 2*(_+_) ∂fullSpatialPatchDesign d n) ≤ _
  rw [integral_const_mul,integral_add ho.1 hp.1]
  have hO : 0 ≤ O := ordinaryAliasFamilySpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _
  have hP : 0 ≤ P := by
    have hpref := finePairUniformSpatialPrefactor_nonneg d q C.densityLower C.densityUpper Cfr a rho c0
    dsimp [P]
    positivity [spatialInverseFourConstant_nonneg d]
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hL1 : 0 ≤ L1 := lowerAliasSpatialL_nonneg (by omega) hc0 hA
  have hL2 : 0 ≤ L2 := by dsimp [L2]; positivity
  have hpairbase : 0 ≤ finePairAliasGeometricBase d C.densityUpper := finePairAliasGeometricBase_nonneg _ _
  have hordbase : 0 ≤ ordinaryAliasSpatialResponseBase d C.densityUpper := by
    unfold ordinaryAliasSpatialResponseBase ordinaryAliasSpatialCountBase
    positivity
  obtain ⟨haD,hinterval⟩ := high_source_interval_numeric C (M : ℝ) hresolution
  have hshrink : C.densityLower+(M : ℝ)⁻¹ < C.densityUpper-(M : ℝ)⁻¹ := by simpa only [one_div] using hinterval
  have hinv : 0 ≤ (M : ℝ)⁻¹ := by positivity
  have had : 0 < C.densityLower+(M : ℝ)⁻¹ := by linarith [C.densityLower_pos]
  have hamin : C.densityLower ≤ C.densityLower+(M : ℝ)⁻¹ := by linarith
  have hbmax : C.densityUpper-(M : ℝ)⁻¹ ≤ C.densityUpper := by linarith
  have htau' : exteriorTau (((C.densityLower+(M : ℝ)⁻¹)+(C.densityUpper-(M : ℝ)⁻¹))/
      ((C.densityUpper-(M : ℝ)⁻¹)-(C.densityLower+(M : ℝ)⁻¹))) ≤ c0 := by
    rw [exteriorTau_sqrt_ratio _ _ had hshrink]
    exact htau
  have hu := finePairAliasActionSpatialBudget_uniform_geometric_le
    (ad := C.densityLower+(M : ℝ)⁻¹) (bd := C.densityUpper-(M : ℝ)⁻¹) C.densityLower_pos
    hamin hbmax
    hshrink htau' d n M q Cfr a rho eta ell (lt_of_lt_of_le zero_lt_one hell)
  have hscale : 1/ell^((d : ℝ)-4) ≤ N^(4-(d : ℝ))*Real.exp (L2*(M : ℝ)) := by
    rw [paperRegime_cutoff_inverse_power hN D]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN.le _)
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (R.degree_linear H.resolution) (mul_nonneg hc0 hdR)
    dsimp [L2,A]
    nlinarith only [hh]
  have hpbound : (3 : ℝ)^n*finePairAliasActionSpatialBudget d n M q
      (C.densityLower+(M : ℝ)⁻¹) (C.densityUpper-(M : ℝ)⁻¹) Cfr a rho eta ell ≤
      P*W*Real.exp (L2*(M : ℝ))*(3*finePairAliasGeometricBase d C.densityUpper*2^8)^n := by
    have hn := polynomial_count_factor_le n 8
    have ht := mul_le_mul hn hscale (by positivity) (by positivity : 0 ≤ ((2 : ℝ)^8)^n)
    have hh := mul_le_mul_of_nonneg_left ht
      (show 0 ≤ (3 : ℝ)^n*P*(finePairAliasGeometricBase d C.densityUpper)^n*eta^4*
        Real.exp (2*shrunkDensityExponent C.densityLower C.densityUpper M*M) by positivity)
    have hb := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ (3 : ℝ)^n)
    rw [exteriorTau_sqrt_ratio _ _ had hshrink] at hb
    have hdcast : ((d-4 : ℕ) : ℝ) = (d : ℝ)-4 := Nat.cast_sub (by omega)
    have hden : ell^(d-4) = ell^((d : ℝ)-4) := by rw [← hdcast,Real.rpow_natCast]
    rw [hden] at hb
    apply hb.trans
    convert hh using 1 <;> dsimp [P,W,shrunkDensityExponent,densityIntervalExponent] <;>
      simp only [div_eq_mul_inv,mul_pow] <;> ring
  have hB : 0 ≤ paperRegimeAliasSpatialBase C := paperRegimeAliasSpatialBase_nonneg C
  have hbo : ordinaryAliasSpatialResponseBase d C.densityUpper ≤ paperRegimeAliasSpatialBase C := by
    unfold paperRegimeAliasSpatialBase
    linarith [finePairAliasGeometricBase_nonneg d C.densityUpper]
  have hbp : 3*finePairAliasGeometricBase d C.densityUpper*2^8 ≤ paperRegimeAliasSpatialBase C := by
    unfold paperRegimeAliasSpatialBase
    linarith
  have hL : paperRegimeAliasSpatialExponent C K = L1+L2 := rfl
  have heb1 : Real.exp (L1*(M : ℝ)) ≤ Real.exp (paperRegimeAliasSpatialExponent C K*(M : ℝ)) :=
    Real.exp_le_exp.mpr (by rw [hL]; nlinarith)
  have heb2 : Real.exp (L2*(M : ℝ)) ≤ Real.exp (paperRegimeAliasSpatialExponent C K*(M : ℝ)) :=
    Real.exp_le_exp.mpr (by rw [hL]; nlinarith)
  have hob : O*W*Real.exp (L1*(M : ℝ))*(ordinaryAliasSpatialResponseBase d C.densityUpper)^n ≤
      O*W*Real.exp (paperRegimeAliasSpatialExponent C K*M)*(paperRegimeAliasSpatialBase C)^n := by
    gcongr
  have hpb : P*W*Real.exp (L2*(M : ℝ))*(3*finePairAliasGeometricBase d C.densityUpper*2^8)^n ≤
      P*W*Real.exp (paperRegimeAliasSpatialExponent C K*M)*(paperRegimeAliasSpatialBase C)^n := by
    gcongr <;> positivity
  have hobs : (∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) I M Rt q
      C.densityLower C.densityUpper c0 Cfr a rho eta ell
      (fun r => higherBandTargetScale d r N mu) U ∂fullSpatialPatchDesign d n) ≤
      O*W*Real.exp (L1*(M : ℝ))*(ordinaryAliasSpatialResponseBase d C.densityUpper)^n := by
    convert ho.2 using 1 <;> dsimp [O,W,L1] <;> ring
  have hh := add_le_add (hobs.trans hob) ((hp.2.trans hpbound).trans hpb)
  have hfin := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)
  exact hfin.trans_eq (by change _ = 2*(O+P)*W*_*_; ring)

end NearlyMinimax
