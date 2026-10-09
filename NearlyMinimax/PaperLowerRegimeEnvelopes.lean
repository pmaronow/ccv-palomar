module

public import NearlyMinimax.PaperLowerRegime
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


@[expose] public section

/-! Uniform polynomial/exponential envelopes for every Reg(K) tuple.
They yield a single threshold in M, independent of N,mu,D and eta. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def paperRegimeSmallBase (K t : ℝ) : ℝ :=
  (K+1)*t^2*Real.exp (-t/K)

def paperRegimeRatioEnvelope (d : ℕ) (K Cact a t : ℝ) : ℝ :=
  Cact*(paperLowerRegimeDegreeSlope d+1)*(K+1)*(K+1)^(a/(d : ℝ))*
    t^(3+2*a/(d : ℝ))*Real.exp (-(a/(K*(d : ℝ)))*t)

theorem paperRegimeSmallBase_tends_zero {K : ℝ} (hK : 0 < K) :
    Tendsto (paperRegimeSmallBase K) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 K⁻¹ (inv_pos.mpr hK)).const_mul (K+1)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [] with t
  unfold paperRegimeSmallBase
  rw [Real.rpow_ofNat t 2]
  rw [show -K⁻¹*t = -t/K by ring]
  ring

theorem paperRegimeRatioEnvelope_tends_zero {d : ℕ} (hd : 0 < d)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a) (Cact : ℝ) :
    Tendsto (paperRegimeRatioEnvelope d K Cact a) atTop (𝓝 0) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (3+2*a/(d : ℝ)) (a/(K*(d : ℝ))) (div_pos ha (mul_pos hK hdR))).const_mul
      (Cact*(paperLowerRegimeDegreeSlope d+1)*(K+1)*(K+1)^(a/(d : ℝ)))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [] with t
  unfold paperRegimeRatioEnvelope
  ring

theorem paperRegimeRatioEnvelope_identity {d : ℕ} (K Cact a t : ℝ)
    (hK : 0 < K) (ht : 0 < t) :
    paperRegimeRatioEnvelope d K Cact a t =
      Cact*((paperLowerRegimeDegreeSlope d+1)*t)*((K+1)*t^2)*
        (paperRegimeSmallBase K t)^(a/(d : ℝ)) := by
  have hK1 : 0 ≤ K+1 := by linarith
  have ht2 : (t^2)^(a/(d : ℝ)) = t^(2*a/(d : ℝ)) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le]
    congr 1
    norm_num
    ring
  unfold paperRegimeSmallBase paperRegimeRatioEnvelope
  rw [Real.mul_rpow (mul_nonneg hK1 (sq_nonneg _)) (Real.exp_pos _).le,
    Real.mul_rpow hK1 (sq_nonneg _), ht2, ← Real.exp_mul]
  have he : (-t/K)*(a/(d : ℝ)) = -(a/(K*(d : ℝ)))*t := by ring
  rw [he, show 3+2*a/(d : ℝ) = 3+(2*a/(d : ℝ)) by rfl,
    Real.rpow_add ht]
  rw [Real.rpow_ofNat t 3]
  ring

theorem PaperLowerRegime.ratio_envelope {d : ℕ} {C : ModelConstants d}
    {Q : LowSmoothnessTernaryConstants C} {K N mu eta Cact a : ℝ} {M D : ℕ}
    (R : PaperLowerRegime C Q K M D N mu eta) (hd : 0 < d) (hM : 1 ≤ M)
    (hCact : 0 ≤ Cact) (ha : 0 ≤ a) :
    higherBandGeometricRatio d D Cact (1+Real.log N) (mu*(1+Real.log N)) a ≤
      paperRegimeRatioEnvelope d K Cact a (M : ℝ) := by
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one R.regularity
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hAD : 0 ≤ paperLowerRegimeDegreeSlope d+1 := by
    linarith [paperLowerRegimeDegreeSlope_positive d]
  have hAH : 0 ≤ K+1 := by linarith
  rw [paperRegimeRatioEnvelope_identity K Cact a (M : ℝ) hK hMr]
  unfold higherBandGeometricRatio
  apply mul_le_mul
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (R.degree_linear hM) hCact
    · exact R.H_polynomial hM
    · exact R.H_positive.le
    · exact mul_nonneg hCact (mul_nonneg hAD hMr.le)
  · exact Real.rpow_le_rpow (mul_nonneg R.occupancy_positive.le R.H_positive.le)
      (R.occupancy_H_envelope hM) (div_nonneg ha hdR.le)
  · exact Real.rpow_nonneg (mul_nonneg R.occupancy_positive.le R.H_positive.le) _
  · exact mul_nonneg (mul_nonneg hCact (mul_nonneg hAD hMr.le))
      (mul_nonneg hAH (sq_nonneg _))

theorem paperRegimeRatioEnvelope_square_tends_zero {d : ℕ} (hd : 0 < d)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a) (Cact : ℝ) :
    Tendsto (fun t : ℝ => ((paperLowerRegimeDegreeSlope d+1)*t)^2*
      paperRegimeRatioEnvelope d K Cact a t) atTop (𝓝 0) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (5+2*a/(d : ℝ)) (a/(K*(d : ℝ))) (div_pos ha (mul_pos hK hdR))).const_mul
      ((paperLowerRegimeDegreeSlope d+1)^2*
        (Cact*(paperLowerRegimeDegreeSlope d+1)*(K+1)*(K+1)^(a/(d : ℝ))))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  unfold paperRegimeRatioEnvelope
  rw [show 5+2*a/(d : ℝ) = 2+(3+2*a/(d : ℝ)) by ring,
    Real.rpow_add ht]
  rw [Real.rpow_ofNat t 2]
  ring

end NearlyMinimax
