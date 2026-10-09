module

public import NearlyMinimax.HighCompleteGeometry
public import NearlyMinimax.AliasTailSummation


@[expose] public section

/-! Actual count-two and exterior factorial blocks of the complete source
geometry. Every constant is fixed before the degrees and count cutoff. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def completeGeometryExteriorConstant (d : ℕ) (Cs Chi : ℝ) : ℝ :=
  max 1 (Cs * (3*(2 : ℝ)^d*Chi^2))

theorem completeGeometryExteriorConstant_ge_one (d : ℕ) (Cs Chi : ℝ) :
    1 ≤ completeGeometryExteriorConstant d Cs Chi := le_max_left _ _

theorem completeGeometryExteriorConstant_pos (d : ℕ) (Cs Chi : ℝ) :
    0 < completeGeometryExteriorConstant d Cs Chi :=
  zero_lt_one.trans_le (completeGeometryExteriorConstant_ge_one d Cs Chi)

theorem completeGeometryExteriorConstant_nonneg (d : ℕ) (Cs Chi : ℝ) :
    0 ≤ completeGeometryExteriorConstant d Cs Chi :=
  (completeGeometryExteriorConstant_pos d Cs Chi).le

theorem completeSourceGeometryEnvelope_exterior_integral_of_three_le {d : ℕ}
    (D M R q n : ℕ) (h3 : 3 ≤ n) (hn : D < n)
    (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ) :
    (∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl n U
      ∂fullSpatialPatchDesign d n) = (3*(2 : ℝ)^d*Chi^2)^n*eta^4*(Bl+1)^2 := by
  rcases n with _|_|_|n
  · omega
  · omega
  · omega
  · exact completeSourceGeometryEnvelope_exterior_integral D M R q n
      aD bD c0 ell N mu C a rho eta Chi Bl hn

/-- The true exterior integrals, including response and spatial volume,
give the source factorial tail with its fixed exponential constant. -/
theorem completeSourceGeometryEnvelope_exterior_factorial_le {d : ℕ}
    (D M R q J : ℕ) (hD : 2 ≤ D) (aD bD c0 ell N mu C a rho eta Chi Bl Cs : ℝ)
    (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Cs*mu) (D+1+j) *
      ∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu
        C a rho eta Chi Bl (D+1+j) U ∂fullSpatialPatchDesign d (D+1+j)) ≤
      Real.exp (completeGeometryExteriorConstant d Cs Chi) * eta^4*(Bl+1)^2 *
        poissonCountWeight (completeGeometryExteriorConstant d Cs Chi*mu) (D+1) := by
  let B := 3*(2 : ℝ)^d*Chi^2
  let P := eta^4*(Bl+1)^2
  let ch := completeGeometryExteriorConstant d Cs Chi
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hbase : Cs*B ≤ ch := le_max_right _ _
  have heq (j : ℕ) :
      (∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu
        C a rho eta Chi Bl (D+1+j) U ∂fullSpatialPatchDesign d (D+1+j)) =
      B^(D+1+j)*P := by
    have h := completeSourceGeometryEnvelope_exterior_integral_of_three_le (d := d) D M R q (D+1+j)
      (by omega) (by omega) aD bD c0 ell N mu C a rho eta Chi Bl
    simpa only [B, P, mul_assoc] using h
  simp_rw [heq]
  have hterm (j : ℕ) : poissonCountWeight (Cs*mu) (D+1+j) * (B^(D+1+j)*P) =
      P * poissonCountWeight (Cs*B*mu) (D+1+j) := by
    unfold poissonCountWeight
    rw [mul_pow, mul_pow, mul_pow]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have ht := finite_poissonCountWeight_tail_le (by positivity : 0 ≤ Cs*B*mu) (D+1) J
  apply (mul_le_mul_of_nonneg_left ht hP).trans
  have hexp : Real.exp (Cs*B*mu) ≤ Real.exp ch := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_of_le_one_right (mul_nonneg hCs hB) hmu1).trans hbase
  have hweight := poissonCountWeight_mono (by positivity : 0 ≤ Cs*B*mu)
    (mul_le_mul_of_nonneg_right hbase hmu) (D+1)
  have h := mul_le_mul hexp hweight (poissonCountWeight_nonneg (by positivity) _)
    (Real.exp_pos ch).le
  exact (mul_le_mul_of_nonneg_left h hP).trans_eq (by dsimp [P,ch]; ring)

def completeGeometryRadialConstant (d : ℕ) (B a rho Cs : ℝ) : ℝ :=
  27*Cs^2*B^4*((2*rho+a)/a^2)^4*(2 : ℝ)^d*spatialExponentialConstant d

theorem completeGeometryRadialConstant_nonneg (d : ℕ) (B a rho Cs : ℝ) :
    0 ≤ completeGeometryRadialConstant d B a rho Cs := by
  have := spatialExponentialConstant_nonneg d
  unfold completeGeometryRadialConstant
  positivity

/-- The actual pair envelope integrates the genuine radial defect. Its
count-two Poisson factor yields `η⁴ μ² N⁻ᵈ` with a fixed density-upper cap. -/
theorem completeSourceGeometryEnvelope_pair_factorial_le {d : ℕ}
    (D M R q : ℕ) (aD bD c0 ell N mu C a rho eta Chi Bl Cs B : ℝ)
    (hd : 0 < d) (hN : 0 < N) (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu)
    (hbd : 0 ≤ bD-(M : ℝ)⁻¹) (hbdB : bD-(M : ℝ)⁻¹ ≤ B) :
    poissonCountWeight (Cs*mu) 2 *
      (∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu
        C a rho eta Chi Bl 2 U ∂fullSpatialPatchDesign d 2) ≤
      completeGeometryRadialConstant d B a rho Cs * eta^4*mu^2*N^(-(d : ℝ)) := by
  have hi := completeSourceGeometryEnvelope_pair_integral_le (d := d) D M R q
    aD bD c0 ell N mu C a rho eta Chi Bl hd hN
  apply (mul_le_mul_of_nonneg_left hi (poissonCountWeight_nonneg (mul_nonneg hCs hmu) 2)).trans
  have hp : (bD-(M : ℝ)⁻¹)^4 ≤ B^4 := pow_le_pow_left₀ hbd hbdB 4
  let K := 27*Cs^2*((2*rho+a)/a^2)^4*(2 : ℝ)^d*spatialExponentialConstant d *
    eta^4*mu^2/(N^d)
  have hK : 0 ≤ K := by
    have := spatialExponentialConstant_nonneg d
    dsimp [K]
    positivity
  have h := mul_le_mul_of_nonneg_right hp hK
  rw [Real.rpow_neg hN.le, Real.rpow_natCast]
  convert h using 1 <;> simp only [poissonCountWeight, finePairCountTwoSpatialBudget, completeGeometryRadialConstant]
    <;> dsimp [K] <;> norm_num only [Nat.factorial, Nat.cast_ofNat] <;> ring

end NearlyMinimax
