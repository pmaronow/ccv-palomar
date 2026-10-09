module

public import NearlyMinimax.ResponseOperators
public import NearlyMinimax.PilotFields


@[expose] public section

/-! Honest assembly of the two scalar pilot fluctuations into the original
three-coordinate coefficient fluctuation. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000

def twoScalarPilotVector (a b : ℝ) : PairVector :=
  (a - b) • pairCoordinateVector 1 - a • pairCoordinateVector 2

theorem twoScalarPilotVector_coordinates (a b : ℝ) :
    twoScalarPilotVector a b = WithLp.toLp 2 ![0, a - b, -a] := by
  ext i
  fin_cases i <;> simp [twoScalarPilotVector, pairCoordinateVector]

theorem twoScalarPilotVector_norm_sq (a b : ℝ) :
    ‖twoScalarPilotVector a b‖ ^ 2 = (a - b) ^ 2 + a ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, twoScalarPilotVector_coordinates]
  simp [Fin.sum_univ_succ]

theorem twoScalarPilotVector_norm_sq_le (a b : ℝ) :
    ‖twoScalarPilotVector a b‖ ^ 2 ≤ 3 * a ^ 2 + 2 * b ^ 2 := by
  rw [twoScalarPilotVector_norm_sq]
  nlinarith only [sq_nonneg (a + b)]

theorem twoScalarPilotVector_inner (a b : ℝ) (v : PairVector) :
    ⟪twoScalarPilotVector a b, v⟫ = (v 1 - v 2) * a - v 1 * b := by
  rw [twoScalarPilotVector_coordinates]
  simp [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_succ]
  ring

section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {a b : Ω → ℝ}

theorem twoScalarPilotVector_aestronglyMeasurable
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ) :
    AEStronglyMeasurable (fun x => twoScalarPilotVector (a x) (b x)) μ :=
  ((ha.sub hb).smul_const _).sub (ha.smul_const _)

theorem twoScalarPilotVector_memLp (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    MemLp (fun x => twoScalarPilotVector (a x) (b x)) 2 μ := by
  have hs := twoScalarPilotVector_aestronglyMeasurable ha.aestronglyMeasurable hb.aestronglyMeasurable
  have hi : Integrable (fun x => 3 * a x ^ 2 + 2 * b x ^ 2) μ :=
    (ha.integrable_sq.const_mul 3).add (hb.integrable_sq.const_mul 2)
  apply (memLp_two_iff_integrable_sq_norm hs).2
  apply hi.mono' (hs.norm.pow 2)
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact twoScalarPilotVector_norm_sq_le _ _

theorem twoScalarPilotVector_mean_zero [IsFiniteMeasure μ]
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hma : (∫ x, a x ∂μ) = 0) (hmb : (∫ x, b x ∂μ) = 0) :
    (∫ x, twoScalarPilotVector (a x) (b x) ∂μ) = 0 := by
  have hai : Integrable a μ := ha.integrable (by norm_num)
  have hbi : Integrable b μ := hb.integrable (by norm_num)
  have hs1 : Integrable (fun x => (a x - b x) • pairCoordinateVector 1) μ := (hai.sub hbi).smul_const _
  have hs2 : Integrable (fun x => a x • pairCoordinateVector 2) μ := hai.smul_const _
  unfold twoScalarPilotVector
  rw [integral_sub hs1 hs2,
    integral_smul_const, integral_smul_const, integral_sub hai hbi, hma, hmb]
  simp

theorem twoScalarPilotVector_second_le (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    {E : ℝ} (hEa : (∫ x, a x ^ 2 ∂μ) ≤ E) (hEb : (∫ x, b x ^ 2 ∂μ) ≤ E) :
    (∫ x, ‖twoScalarPilotVector (a x) (b x)‖ ^ 2 ∂μ) ≤ 5 * E := by
  have h := integral_mono (twoScalarPilotVector_memLp ha hb).norm.integrable_sq
    ((ha.integrable_sq.const_mul 3).add (hb.integrable_sq.const_mul 2))
    (fun x => twoScalarPilotVector_norm_sq_le (a x) (b x))
  change (∫ x, ‖twoScalarPilotVector (a x) (b x)‖ ^ 2 ∂μ) ≤
    (∫ x, 3 * a x ^ 2 + 2 * b x ^ 2 ∂μ) at h
  rw [integral_add (f := fun x => 3 * a x ^ 2) (g := fun x => 2 * b x ^ 2)
    (ha.integrable_sq.const_mul 3) (hb.integrable_sq.const_mul 2),
    integral_const_mul, integral_const_mul] at h
  linarith only [h, hEa, hEb]

end

theorem twoScalarPilotVector_measurable {Ω : Type*} [MeasurableSpace Ω]
    {a b : Ω → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => twoScalarPilotVector (a x) (b x)) :=
  ((ha.sub hb).smul measurable_const).sub (ha.smul measurable_const)

theorem pairVector_coordinate_memLp {W : Type*} [MeasurableSpace W]
    {M : Measure W} {v : W → PairVector} (hv : MemLp v 2 M) (i : Fin 3) :
    MemLp (fun w => v w i) 2 M := by
  apply hv.mono ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp_aestronglyMeasurable hv.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun w => PiLp.norm_apply_le (v w) i

/-- A universal scalar covariance estimate for each of the two fields yields
the actual vector covariance estimate, with its dimension-free factor six. -/
theorem twoScalarPilotVector_test_second_le
    {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
    (μ : Measure Ω) (M : Measure W) (a b : Ω → W → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hinta : ∀ v : W → ℝ, MemLp v 2 M → ∀ x, Integrable (fun w => v w * a x w) M)
    (hintb : ∀ v : W → ℝ, MemLp v 2 M → ∀ x, Integrable (fun w => v w * b x w) M)
    (hLa : ∀ v : W → ℝ, MemLp v 2 M →
      MemLp (fun x => ∫ w, v w * a x w ∂M) 2 μ)
    (hLb : ∀ v : W → ℝ, MemLp v 2 M →
      MemLp (fun x => ∫ w, v w * b x w ∂M) 2 μ)
    (hEa : ∀ v : W → ℝ, MemLp v 2 M →
      (∫ x, (∫ w, v w * a x w ∂M) ^ 2 ∂μ) ≤ c * ∫ w, v w ^ 2 ∂M)
    (hEb : ∀ v : W → ℝ, MemLp v 2 M →
      (∫ x, (∫ w, v w * b x w ∂M) ^ 2 ∂μ) ≤ c * ∫ w, v w ^ 2 ∂M)
    (v : W → PairVector) (hv : MemLp v 2 M) :
    (∫ x, PilotFields.test (M := M) (fun x w => twoScalarPilotVector (a x w) (b x w)) v x ^ 2 ∂μ) ≤
      6 * c * ∫ w, ‖v w‖ ^ 2 ∂M := by
  let vA (w : W) := v w 1 - v w 2
  let vB (w : W) := v w 1
  have hvA : MemLp vA 2 M := (pairVector_coordinate_memLp hv 1).sub (pairVector_coordinate_memLp hv 2)
  have hvB : MemLp vB 2 M := pairVector_coordinate_memLp hv 1
  let A (x : Ω) := ∫ w, vA w * a x w ∂M
  let B (x : Ω) := ∫ w, vB w * b x w ∂M
  have hA : MemLp A 2 μ := hLa vA hvA
  have hB : MemLp B 2 μ := hLb vB hvB
  have heq (x : Ω) : PilotFields.test (M := M)
      (fun x w => twoScalarPilotVector (a x w) (b x w)) v x = A x - B x := by
    unfold PilotFields.test
    simp_rw [twoScalarPilotVector_inner]
    exact integral_sub (hinta vA hvA x) (hintb vB hvB x)
  have hsq := integral_mono (hA.sub hB).integrable_sq
    ((hA.integrable_sq.const_mul 2).add (hB.integrable_sq.const_mul 2))
    (fun x => show (A x - B x) ^ 2 ≤ 2 * A x ^ 2 + 2 * B x ^ 2 by
      nlinarith only [sq_nonneg (A x + B x)])
  change (∫ x, (A x - B x) ^ 2 ∂μ) ≤ (∫ x, 2 * A x ^ 2 + 2 * B x ^ 2 ∂μ) at hsq
  rw [integral_add (f := fun x => 2 * A x ^ 2) (g := fun x => 2 * B x ^ 2)
    (hA.integrable_sq.const_mul 2) (hB.integrable_sq.const_mul 2),
    integral_const_mul, integral_const_mul] at hsq
  have hweights : (∫ w, vA w ^ 2 + vB w ^ 2 ∂M) ≤ 3 * ∫ w, ‖v w‖ ^ 2 ∂M := by
    have hp (w : W) : vA w ^ 2 + vB w ^ 2 ≤ 3 * ‖v w‖ ^ 2 := by
      have hn : ‖v w‖ ^ 2 = v w 0 ^ 2 + v w 1 ^ 2 + v w 2 ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [Fin.sum_univ_succ, add_assoc]
      rw [hn]
      dsimp [vA, vB]
      nlinarith only [sq_nonneg (v w 1 + v w 2), sq_nonneg (v w 0), sq_nonneg (v w 2)]
    have hh := integral_mono (hvA.integrable_sq.add hvB.integrable_sq)
      (hv.norm.integrable_sq.const_mul 3) hp
    rwa [integral_const_mul] at hh
  rw [integral_add hvA.integrable_sq hvB.integrable_sq] at hweights
  simp_rw [heq]
  have hca := hEa vA hvA
  have hcb := hEb vB hvB
  have hm := mul_le_mul_of_nonneg_left hweights hc
  dsimp only [A, B] at hsq
  nlinarith only [hsq, hca, hcb, hm]

end NearlyMinimax
