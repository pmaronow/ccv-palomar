module

public import NearlyMinimax.SourceActivitySummation


@[expose] public section

/-! Total activity of the actual finite source family, including singleton,
three genuine pair rows, and every selected higher target. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem source_exteriorTau_nonneg {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 ≤ exteriorTau ((a+b)/(b-a)) := by
  apply exteriorTau_nonneg
  apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
  linarith

theorem finePairTotalMass_activity_bound (d : ℕ) [NeZero d] (k D M q : ℕ) (hD : 1 ≤ D)
    (a b C ℓ N : ℝ) (ha : 0 < a) (hab : a < b) (hℓ : 0 ≤ ℓ) (hℓN : ℓ ≤ N)
    (hunit : (D : ℝ)^2*Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a))) ≤ N^2)
    (hcoarse : (D : ℝ)^2*Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))*ℓ^2 ≤ 2*N^2) :
    highRowTotalMass (finePairRowData d k D M q a b C ℓ N).rowMass ≤
      (ordinaryDensityActivityBase a b)^2 * sourceResponseCost q C * (1+512*(d : ℝ)) *
        N^2 * Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a))) := by
  let K := (ordinaryDensityActivityBase a b)^2 * sourceResponseCost q C
  let EM := Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a)))
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) (sourceResponseCost_nonneg q C)
  have hEM : 1 ≤ EM := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (source_exteriorTau_nonneg ha hab))
  have hu : finePairRowMass d D M q a b C ℓ N .unit ≤ K*N^2 := by
    apply (finePairRowMass_unit_le d D M q hD a b ha hab C ℓ N).trans
    calc
      _ = K*((D : ℝ)^2*Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))) := by dsimp [K]; ring
      _ ≤ K*N^2 := mul_le_mul_of_nonneg_left hunit hK
  have hc : finePairRowMass d D M q a b C ℓ N .coarse ≤ 256*(d : ℝ)*K*N^2 := by
    apply (finePairRowMass_coarse_le d D M q hD a b ha hab C ℓ N hℓ).trans
    calc
      _ = (128*(d : ℝ)*K)*((D : ℝ)^2*Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))*ℓ^2) := by dsimp [K]; ring
      _ ≤ (128*(d : ℝ)*K)*(2*N^2) := mul_le_mul_of_nonneg_left hcoarse (by positivity)
      _ = _ := by ring
  have hf := finePairRowMass_fine_le d D M q a b ha hab C ℓ N hℓ hℓN
  have hu' : finePairRowMass d D M q a b C ℓ N .unit ≤ K*N^2*EM := by
    apply hu.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hEM (by positivity : 0 ≤ K*N^2)
  have hc' : finePairRowMass d D M q a b C ℓ N .coarse ≤ 256*(d : ℝ)*K*N^2*EM := by
    apply hc.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hEM (by positivity : 0 ≤ 256*(d : ℝ)*K*N^2)
  have he : (Finset.univ : Finset FinePairRowTag) = {.unit, .coarse, .fine} := by
    ext i; cases i <;> simp
  change (∑ i, finePairRowMass d D M q a b C ℓ N i) ≤ _
  rw [he]
  rw [Finset.sum_insert (show FinePairRowTag.unit ∉ ({.coarse, .fine} : Finset FinePairRowTag) by decide),
    Finset.sum_insert (show FinePairRowTag.coarse ∉ ({.fine} : Finset FinePairRowTag) by decide), Finset.sum_singleton]
  change _ ≤ K*(1+512*(d : ℝ))*N^2*EM
  dsimp [K, EM] at hu' hc'
  nlinarith only [hu', hc', hf]

def sourceActivityConstant (d q : ℕ) (C B lam : ℝ) : ℝ :=
  B^2 * sourceResponseCost q C * (1+512*(d : ℝ)) + B * sourceResponseCost q C +
    4 * higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C)

theorem sourceActivityConstant_nonneg (d q : ℕ) (C B lam : ℝ) (hB : 0 ≤ B) :
    0 ≤ sourceActivityConstant d q C B lam := by
  unfold sourceActivityConstant higherBandGeometricPrefactor higherBandInterpolationBase sourceResponseCost
  positivity

/-- The actual complete finite row family has a fixed total activity constant.
The hypotheses are elementary inequalities on the computed source scales. -/
theorem sourceRows_activity_bound {d k D M q : ℕ} [NeZero d] (hd : 0 < d) (hD : 1 ≤ D)
    (a b C lam ℓ N μ B q1 q2 : ℝ) (ha : 0 < a) (hab : a < b)
    (hℓ : 0 ≤ ℓ) (hℓN : ℓ ≤ N) (hN : 1 ≤ N) (hμ : 0 ≤ μ) (hbase1 : μ*(1+Real.log N) ≤ 1)
    (hB : 0 ≤ B) (hbB : ordinaryDensityActivityBase a b ≤ B)
    (hq1 : q1 = higherBandGeometricRatio d D
      (higherBandGeometricConstant B (higherBandInterpolationBase d lam)) (1+Real.log N) (μ*(1+Real.log N)) 1)
    (hq2 : q2 = higherBandGeometricRatio d D
      (higherBandGeometricConstant B (higherBandInterpolationBase d lam)) (1+Real.log N) (μ*(1+Real.log N)) 2)
    (hq1h : q1 ≤ 1/2) (hq21 : q2 ≤ q1) (hsmall : (D : ℝ)^2*q1 ≤ 1)
    (hcoarse : Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))*ℓ ≤ N)
    (hsingle : (D : ℝ)*Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a))) ≤ N)
    (hpair : (D : ℝ)^2*Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))*ℓ^2 ≤ 2*N^2) :
    highRowTotalMass (sourceRowData d k D M q a b C lam ℓ N μ).rowMass ≤
      sourceActivityConstant d q C B lam * N^2 * Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a))) := by
  let A := ordinaryDensityActivityBase a b
  let EM := Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a)))
  let ED := Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))
  have hA : 0 ≤ A := by dsimp [A, ordinaryDensityActivityBase]; positivity
  have hED : 1 ≤ ED := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (source_exteriorTau_nonneg ha hab))
  have hEM : 1 ≤ EM := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (source_exteriorTau_nonneg ha hab))
  have hunit : (D : ℝ)^2*ED ≤ N^2 := by
    have h1 := mul_le_mul_of_nonneg_left hED (by positivity : 0 ≤ (D : ℝ)^2*ED)
    have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ (D : ℝ)*ED) hsingle 2
    nlinarith only [h1, h2]
  have hp := finePairTotalMass_activity_bound d k D M q hD a b C ℓ N ha hab hℓ hℓN hunit hpair
  have hbpow := pow_le_pow_left₀ hA hbB 2
  have hp' : highRowTotalMass (finePairRowData d k D M q a b C ℓ N).rowMass ≤
      B^2*sourceResponseCost q C*(1+512*(d : ℝ))*N^2*EM := by
    apply hp.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbpow (sourceResponseCost_nonneg q C))
        (by positivity)) (sq_nonneg N)) (Real.exp_pos _).le
  have hs := singletonRowMass_exponential_bound d D q hD a b ha hab C
  have hs' : singletonRowMass d D q a b C ≤ B*sourceResponseCost q C*N^2*EM := by
    apply hs.trans
    have h1 := mul_le_mul hbB hsingle (by positivity : 0 ≤ (D : ℝ)*ED) hB
    have h2 := mul_le_mul_of_nonneg_right h1 (sourceResponseCost_nonneg q C)
    have hN2 : N ≤ N^2*EM := by
      have hsq : N ≤ N^2 := by nlinarith
      apply hsq.trans
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hEM (sq_nonneg N)
    have h3 := mul_le_mul_of_nonneg_left hN2 (mul_nonneg hB (sourceResponseCost_nonneg q C))
    dsimp [A, ED, ordinaryDensityActivityBase, sourceResponseCost] at h2
    dsimp [sourceResponseCost] at h3
    dsimp [ordinaryDensityActivityBase, sourceResponseCost] at hs ⊢
    nlinarith only [h2, h3]
  have hh := higherBandFamily_activity_bound (k := k) (M := M) (q := q) hd hD
    a b C lam ℓ N μ B q1 q2 ha hab hℓ hN hμ hbase1 hB hbB hq1 hq2 hq1h hq21 hsmall hcoarse
  rw [sourceRowTotalMass_eq]
  dsimp [sourceActivityConstant]
  change _ ≤ _*N^2*EM
  nlinarith only [hp', hs', hh]

end NearlyMinimax
