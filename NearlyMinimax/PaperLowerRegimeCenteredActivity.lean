module

public import NearlyMinimax.PaperLowerRegimeSource
public import NearlyMinimax.CompleteSourceInvariantMass


@[expose] public section

/-! The actual centered-reference activation budget B_loc, uniformly
for every tuple in Reg(K), with the original activity exponent. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def paperRegimeLocalActivityConstant {d : ℕ} (C : ModelConstants d)
    (Cfr lam : ℝ) (q : ℕ) : ℝ :=
  sourceSaddleActivityConstant d q C.densityLower C.densityUpper Cfr lam/highCenterMix C

theorem paperRegimeLocalActivityConstant_pos {d : ℕ} (C : ModelConstants d)
    (Cfr lam : ℝ) (q : ℕ) : 0<paperRegimeLocalActivityConstant C Cfr lam q :=
  div_pos (sourceSaddleActivityConstant_positive d q C.densityLower C.densityUpper Cfr lam
    C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)) (highCenterMix_mem C).1

theorem paperLowerRegime_uniform_centered_activity {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (K Cfr lam : ℝ) (hK : 1≤K) (hCfr : 1≤Cfr) (q : ℕ) (hq : 1≤q) :
    ∃ M0 : ℕ, ∀ M D : ℕ, M0≤M → ∀ N mu eta : ℝ,
      PaperLowerRegime C Q K M D N mu eta → ∀ k : ℕ,
      let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
      let ell := N*Real.exp (-c0*(D : ℝ))
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      highRowTotalMass R.rowMass/highCenterMix C ≤
        paperRegimeLocalActivityConstant C Cfr lam q*N^2*
          Real.exp (shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ)) ∧
      ∀ e : HighUnionMark (SourceRowMark d D M q
        (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) Cfr lam ell N mu),
        |highUnionActivation R (highCenterMix C) e| ≤
          paperRegimeLocalActivityConstant C Cfr lam q*N^2*
            Real.exp (shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ)) := by
  obtain ⟨M1,hM1⟩ := paperLowerRegime_uniform_activity C Q K Cfr lam hK q
  obtain ⟨M2,hM2⟩ := paperLowerRegime_uniform_source_guards C Q K Cfr lam hK hCfr q hq
  let M0 := max M1 (max M2 2)
  refine ⟨M0,?_⟩
  intro M D hm N mu eta R k
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  let ell := N*Real.exp (-c0*(D : ℝ))
  have h1 : M1≤M := (le_max_left _ _).trans hm
  have h2 : M2≤M := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm2 : 2≤M := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have GS := (hM2 M D h2 N mu eta R k).1
  have hb := div_le_div_of_nonneg_right (hM1 M D h1 N mu eta R k) (highCenterMix_mem C).1.le
  have hb' : highRowTotalMass (completeSourceRows C k D M q Cfr lam ell N mu).rowMass/highCenterMix C ≤
      paperRegimeLocalActivityConstant C Cfr lam q*N^2*
        Real.exp (shrunkDensityExponent C.densityLower C.densityUpper M*(M : ℝ)) := by
    convert hb using 1 <;> unfold paperRegimeLocalActivityConstant <;> ring
  refine ⟨hb',?_⟩
  intro e
  have hD : 3≤D := by
    have hmr : (2 : ℝ)≤M := by exact_mod_cast hm2
    have hslope : 2≤paperLowerRegimeDegreeSlope d := by
      unfold paperLowerRegimeDegreeSlope
      linarith [show (0 : ℝ)≤d from Nat.cast_nonneg d]
    have hdr : (3 : ℝ)≤D := by nlinarith [R.degree_lower]
    exact_mod_cast hdr
  have hab : C.densityLower<C.densityUpper := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have hc0 : 0<c0 := by dsimp [c0]; linarith [densityIntervalExponent_pos C.densityLower_pos hab]
  have hN : 0<N := zero_lt_one.trans_le R.scale
  have hell : 0<ell := by dsimp [ell]; positivity
  have hellN : ell<N := by
    have hDpos : (0 : ℝ)<D := by exact_mod_cast (by omega : 0<D)
    have he : Real.exp (-c0*(D : ℝ))<1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    exact (mul_lt_mul_of_pos_left he hN).trans_eq (mul_one N)
  obtain ⟨had,hinterval⟩ := high_source_interval_numeric C (M : ℝ) GS.resolution
  have hp := sourceRowMass_positive_actual d k D M q hD hq _ _ had hinterval Cfr
    (zero_lt_one.trans_le hCfr) lam ell N mu hell hellN
  exact (highCenteredRowUnionActivation_bound
    (completeSourceRows C k D M q Cfr lam ell N mu).rowMass hp GS.total_positive
    (completeSourceRows C k D M q Cfr lam ell N mu).rowActivation GS.activation_bound
    (highCenterMix C) (highCenterMix_mem C).1 e).trans hb'

end NearlyMinimax
