module

public import NearlyMinimax.SourceRowActivity
public import NearlyMinimax.FinePairRowActivity
public import NearlyMinimax.HighActivitySummation
public import NearlyMinimax.HigherBandActivityConversion


@[expose] public section

/-! Summation of the actual selected higher rows under elementary source
scale inequalities. All component cap estimates come from actual measures. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

theorem finite_activity_fin_tail_le {K q : ℝ} (hK : 0 ≤ K) (hq : 0 ≤ q)
    (hqh : q ≤ 1/2) (m : ℕ) (B : Fin m → ℝ)
    (hB : ∀ j, B j ≤ K*q^(j.val+1)) :
    (∑ j, B j) ≤ 2*K*q := by
  calc
    _ ≤ ∑ j : Fin m, K*q^(j.val+1) := Finset.sum_le_sum fun j _ => hB j
    _ = K * ∑ j : Fin m, q^(j.val+1) := (Finset.mul_sum _ _ _).symm
    _ = K * ∑ j ∈ Finset.range m, q^(j+1) := by
      exact congrArg (fun t : ℝ => K*t) (Fin.sum_univ_eq_sum_range (fun j => q^(j+1)) m)
    _ ≤ K*(2*q) := mul_le_mul_of_nonneg_left (finite_geometric_tail_le_two_mul hq hqh m) hK
    _ = _ := by ring

theorem higherBandCoarseActivity_geometric_le {d D M q : ℕ} (hd : 0 < d) (hD : 1 ≤ D)
    (a b C lam ℓ N μ B : ℝ) (ha : 0 < a) (hab : a < b)
    (hℓ : 0 ≤ ℓ) (hN : 1 ≤ N) (hμ : 0 ≤ μ) (hbase1 : μ*(1+Real.log N) ≤ 1)
    (hB : 0 ≤ B) (hbB : ordinaryDensityActivityBase a b ≤ B) (j : Fin (D-2)) :
    higherBandCoarseActivity d D M q a b C lam ℓ N μ j ≤
      higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C) *
      (D : ℝ)^2 * Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a))) * (N*ℓ) *
      (higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam))
        (1+Real.log N) (μ*(1+Real.log N)) 1)^(j.val+1) := by
  unfold higherBandCoarseActivity higherBandFilteredMass
  split_ifs with hi
  · have hmass := higherBandRowMass_le_activityCap_of_fine d (j.val+3) D D q (by omega) hD
      a b ha hab C lam ℓ (min ℓ (higherBandTargetScale d (j.val+3) N μ)) hi.1 false (by intro h; cases h)
    have hcap := higherBandRowActivityCap_coarse_geometric_le (r := j.val+3) (D := D) (q := q)
      hd (by omega) a b C lam N μ ℓ B hN hμ hbase1 hi.1 hB hbB
    simpa [higherBandFamilyTarget, higherBandFamilyGuardDegree, higherBandFamilyUpper,
      sourceResponseCost] using hmass.trans hcap
  · have hH : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
    unfold higherBandGeometricPrefactor higherBandInterpolationBase higherBandGeometricRatio
      higherBandGeometricConstant sourceResponseCost
    positivity

theorem higherBandFineActivity_geometric_le {d D M q : ℕ} (hd : 0 < d) (hD : 1 ≤ D)
    (a b C lam ℓ N μ B : ℝ) (ha : 0 < a) (hab : a < b)
    (hN : 1 ≤ N) (hμ : 0 ≤ μ) (hbase1 : μ*(1+Real.log N) ≤ 1)
    (hB : 0 ≤ B) (hbB : ordinaryDensityActivityBase a b ≤ B) (j : Fin (D-2)) :
    higherBandFineActivity d D M q a b C lam ℓ N μ j ≤
      higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C) *
      (D : ℝ)^2 * Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a))) * N^2 *
      (higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam))
        (1+Real.log N) (μ*(1+Real.log N)) 2)^(j.val+1) := by
  unfold higherBandFineActivity higherBandFilteredMass
  split_ifs with hi
  · have hLT : ℓ ≤ higherBandTargetScale d (j.val+3) N μ := by
      simpa [higherBandFamilyTarget] using (hi.2.1 rfl).le
    have hmass := higherBandRowMass_le_activityCap_of_fine d (j.val+3) M D q (by omega) hD
      a b ha hab C lam ℓ (higherBandTargetScale d (j.val+3) N μ) hi.1 true (by intro _; exact hLT)
    have hcap := higherBandRowActivityCap_fine_geometric_le (r := j.val+3) (M := M) (D := D) (q := q)
      hd (by omega) a b C lam N μ B hN hμ hbase1 hi.1 hB hbB
    simpa [higherBandFamilyTarget, higherBandFamilyGuardDegree, higherBandFamilyUpper,
      sourceResponseCost] using hmass.trans hcap
  · have hH : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
    unfold higherBandGeometricPrefactor higherBandInterpolationBase higherBandGeometricRatio
      higherBandGeometricConstant sourceResponseCost
    positivity

/-- The entire actual selected higher family obeys the paper's geometric
activity estimate. Only elementary inequalities on the computed source scales
are inputs; every component measure estimate is derived above. -/
theorem higherBandFamily_activity_bound {d k D M q : ℕ} (hd : 0 < d) (hD : 1 ≤ D)
    (a b C lam ℓ N μ B q1 q2 : ℝ) (ha : 0 < a) (hab : a < b)
    (hℓ : 0 ≤ ℓ) (hN : 1 ≤ N) (hμ : 0 ≤ μ) (hbase1 : μ*(1+Real.log N) ≤ 1)
    (hB : 0 ≤ B) (hbB : ordinaryDensityActivityBase a b ≤ B)
    (hq1 : q1 = higherBandGeometricRatio d D
      (higherBandGeometricConstant B (higherBandInterpolationBase d lam)) (1+Real.log N) (μ*(1+Real.log N)) 1)
    (hq2 : q2 = higherBandGeometricRatio d D
      (higherBandGeometricConstant B (higherBandInterpolationBase d lam)) (1+Real.log N) (μ*(1+Real.log N)) 2)
    (hq1h : q1 ≤ 1/2) (hq21 : q2 ≤ q1) (hsmall : (D : ℝ)^2*q1 ≤ 1)
    (hcoarse : Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))*ℓ ≤ N) :
    highRowTotalMass (higherBandFamilyData d k D M q a b C lam ℓ N μ).rowMass ≤
      4 * higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C) *
        N^2 * Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a))) := by
  let K := higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C)
  let ED := Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))
  let EM := Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a)))
  have hK : 0 ≤ K := by
    dsimp [K, higherBandGeometricPrefactor, higherBandInterpolationBase, sourceResponseCost]
    positivity
  have hH : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  have hq10 : 0 ≤ q1 := by rw [hq1]; unfold higherBandGeometricRatio higherBandGeometricConstant higherBandInterpolationBase; positivity
  have hq20 : 0 ≤ q2 := by rw [hq2]; unfold higherBandGeometricRatio higherBandGeometricConstant higherBandInterpolationBase; positivity
  have hτ : 0 ≤ exteriorTau ((a+b)/(b-a)) := by
    apply exteriorTau_nonneg
    apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
    linarith
  have hEM : 1 ≤ EM := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg M) hτ)
  have hc := finite_activity_fin_tail_le (K := K*(D : ℝ)^2*ED*N*ℓ) (by positivity)
    hq10 hq1h (D-2) (higherBandCoarseActivity d D M q a b C lam ℓ N μ) (fun j => by
      have hh := higherBandCoarseActivity_geometric_le (M := M) (q := q) hd hD a b C lam ℓ N μ B ha hab hℓ hN hμ hbase1 hB hbB j
      simpa only [← hq1, K, ED, mul_assoc] using hh)
  have hf := finite_activity_fin_tail_le (K := K*(D : ℝ)^2*EM*N^2) (by positivity)
    hq20 (hq21.trans hq1h) (D-2) (higherBandFineActivity d D M q a b C lam ℓ N μ) (fun j => by
      have hh := higherBandFineActivity_geometric_le (M := M) (q := q) hd hD a b C lam ℓ N μ B ha hab hN hμ hbase1 hB hbB j
      simpa only [← hq2, K, EM] using hh)
  have hsmall2 : (D : ℝ)^2*q2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left hq21 (sq_nonneg _)).trans hsmall
  have hc' : (∑ j, higherBandCoarseActivity d D M q a b C lam ℓ N μ j) ≤ 2*K*N^2 := by
    apply hc.trans
    calc
      _ = (2*K*N)*(ED*ℓ)*((D : ℝ)^2*q1) := by ring
      _ ≤ (2*K*N)*N*1 := mul_le_mul (mul_le_mul_of_nonneg_left hcoarse (by positivity))
        hsmall (by positivity) (by positivity)
      _ = _ := by ring
  have hf' : (∑ j, higherBandFineActivity d D M q a b C lam ℓ N μ j) ≤ 2*K*N^2*EM := by
    apply hf.trans
    calc
      _ = (2*K*N^2*EM)*((D : ℝ)^2*q2) := by ring
      _ ≤ (2*K*N^2*EM)*1 := mul_le_mul_of_nonneg_left hsmall2 (by positivity)
      _ = _ := mul_one _
  rw [higherBandFamily_totalMass_eq]
  have hm := mul_le_mul_of_nonneg_left hEM (by positivity : 0 ≤ 2*K*N^2)
  change _ ≤ 4*K*N^2*EM
  nlinarith only [hc', hf', hm]

/-- The fixed higher-row constant is uniform over every legal source shrunk
interval. In particular it is chosen before M and the finite family. -/
theorem higherBandFamily_shrunk_activity_bound {d k D M q : ℕ} (hd : 0 < d) (hD : 1 ≤ D)
    (a b C lam ℓ N μ c0 q1 q2 : ℝ) (ha : 0 < a)
    (hshrink : a+(M : ℝ)⁻¹ < b-(M : ℝ)⁻¹) (htau : shrunkDensityExponent a b M ≤ c0)
    (hℓ : 0 ≤ ℓ) (hN : 1 ≤ N) (hμ : 0 ≤ μ) (hbase1 : μ*(1+Real.log N) ≤ 1)
    (hq1 : q1 = higherBandGeometricRatio d D (higherBandSourceCact d a b c0 lam)
      (1+Real.log N) (μ*(1+Real.log N)) 1)
    (hq2 : q2 = higherBandGeometricRatio d D (higherBandSourceCact d a b c0 lam)
      (1+Real.log N) (μ*(1+Real.log N)) 2)
    (hq1h : q1 ≤ 1/2) (hq21 : q2 ≤ q1) (hsmall : (D : ℝ)^2*q1 ≤ 1)
    (hcoarse : Real.exp (shrunkDensityExponent a b M*(D : ℝ))*ℓ ≤ N) :
    highRowTotalMass (higherBandFamilyData d k D M q (a+(M : ℝ)⁻¹) (b-(M : ℝ)⁻¹) C lam ℓ N μ).rowMass ≤
      4 * higherBandSourceK d q a b c0 C lam * N^2 * Real.exp (shrunkDensityExponent a b M*(M : ℝ)) := by
  have ht : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg M)
  have hap : 0 < a+(M : ℝ)⁻¹ := by linarith
  have hab : a < b := by linarith
  have hB : 0 ≤ uniformOrdinaryDensityActivityBase a b c0 := by
    unfold uniformOrdinaryDensityActivityBase
    exact mul_nonneg (Real.exp_pos _).le (div_nonneg (sub_pos.mpr hab).le ha.le)
  have hbB := ordinaryDensityActivityBase_shrunk_le ha ht hshrink htau
  have he : exteriorTau (((a+(M : ℝ)⁻¹)+(b-(M : ℝ)⁻¹))/((b-(M : ℝ)⁻¹)-(a+(M : ℝ)⁻¹))) =
      shrunkDensityExponent a b M := by
    rw [exteriorTau_sqrt_ratio _ _ hap hshrink]
    rfl
  have hc : Real.exp ((D : ℝ)*exteriorTau
      (((a+(M : ℝ)⁻¹)+(b-(M : ℝ)⁻¹))/((b-(M : ℝ)⁻¹)-(a+(M : ℝ)⁻¹))))*ℓ ≤ N := by
    simpa only [he, mul_comm (D : ℝ) (shrunkDensityExponent a b M)] using hcoarse
  have hh := higherBandFamily_activity_bound (k := k) (M := M) (q := q) hd hD
    (a+(M : ℝ)⁻¹) (b-(M : ℝ)⁻¹) C lam ℓ N μ (uniformOrdinaryDensityActivityBase a b c0) q1 q2
    hap hshrink hℓ hN hμ hbase1 hB hbB hq1 hq2 hq1h hq21 hsmall hc
  simpa only [higherBandSourceK, sourceResponseCost, he,
    mul_comm (M : ℝ) (shrunkDensityExponent a b M)] using hh

end NearlyMinimax
