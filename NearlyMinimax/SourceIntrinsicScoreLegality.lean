module

public import NearlyMinimax.SourceIntrinsicNormalizedLegality
public import NearlyMinimax.HighIntrinsicLocalBounds
public import NearlyMinimax.HighUnionSourceModel
public import NearlyMinimax.HighFrameLocalBounds


@[expose] public section

/-! Original source-row legality and response floors with the literal frame
constant and amplitude cap. The coefficient radius is exactly the reciprocal
of the intrinsic profile constant, and eta0 is exactly rho/2^(d+1). No frame
enlargement or smaller amplitude cutoff is introduced. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

theorem sourceIntrinsicAmplitude_overlap_le_half {d : ℕ} {eta rho : ℝ}
    (hcap : eta ≤ rho/(2 : ℝ)^(d+1)) :
    (2 : ℝ)^d*eta ≤ rho/2 := by
  have h := (le_div_iff₀ (by positivity : (0 : ℝ)<(2 : ℝ)^(d+1))).mp hcap
  rw [pow_succ] at h
  nlinarith only [h]

theorem sourceIntrinsicAmplitude_le_half {d : ℕ} {eta rho : ℝ}
    (heta : 0 ≤ eta) (hcap : eta ≤ rho/(2 : ℝ)^(d+1)) : eta ≤ rho/2 := by
  have h := sourceIntrinsicAmplitude_overlap_le_half hcap
  have hp : (1 : ℝ) ≤ (2 : ℝ)^d := one_le_pow₀ (by norm_num)
  nlinarith only [h,hp,heta]

section IntrinsicState
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
  (R : HighUnionRowData d k F I E) {M : ℝ}
  (G : HighUnionSourceGuards C M (highIntrinsicFrameConstant C) R)
include G

theorem highUnionSource_intrinsic_regression_abs_le_half (hk : 4 ≤ k)
    (eta : ℝ) (heta : 0 ≤ eta) (hcap : eta ≤ Q.ρ/(2 : ℝ)^(d+1))
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Covariate d) : |highUnionSourceRegression C R eta h x| ≤ Q.ρ/2 := by
  let P := fun j => highFramePolynomial ((highUnionSourceState C R h).2 j)
  have hP (j) : frameCoefficientL1 (P j) ≤ (highIntrinsicFrameConstant C)⁻¹ :=
    (highFramePolynomial_coefficientL1_le _).trans
      (highUnionSourceState_coefficient_ball C R G h j)
  have hb := highFrameField_multiPartial_intrinsic_bound C k hk eta P hP
    (fun _ => (0 : Fin (C.order+1))) (by simp) x
  simp only [Fin.val_zero, Finset.sum_const_zero, multiPartial_zero_index,
    pow_zero, mul_one, abs_of_nonneg heta] at hb
  exact hb.trans (by simpa only [mul_comm] using sourceIntrinsicAmplitude_overlap_le_half hcap)

theorem highUnionSource_intrinsic_without_offset (hk : 4 ≤ k)
    (eta : ℝ) (heta : 0 ≤ eta) (hcap : eta ≤ Q.ρ/(2 : ℝ)^(d+1))
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (j : HighWindowLabels d k) (x : Covariate d) :
    |highLocalFieldWithout d k F eta (highUnionSourceState C R h).2 j x| ≤ Q.ρ/2 :=
  highLocalFieldWithout_intrinsic_offset_guard C k hk (highIntrinsicFrameConstant C) eta Q.ρ
    le_rfl heta hcap _ (highUnionSourceState_coefficient_ball C R G h) j x

end IntrinsicState

/-- The true local regression factors also have the source ternary floor on
the whole compact nuisance range, independently at every spatial tuple. -/
theorem sourceIntrinsicLocal_ternary_floor {d n F : ℕ}
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (eta : ℝ) (heta : 0 ≤ eta) (hcap : eta ≤ Q.ρ/(2 : ℝ)^(d+1))
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (g w : Fin n → ℝ) (hg : ∀ i, |g i| ≤ Q.ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ gamma, |c gamma| ≤ (highIntrinsicFrameConstant C)⁻¹)
    (V : ℝ) (hV : |V-Q.v| ≤ Q.ρ) (i : Fin n) (y : Fin 3) :
    Q.c ≤ ternaryMass Q.a (coefficientRegression eta g w (fun i => highFrameFeature (U i)) c i) V y := by
  have hf := highFrameCoefficientRegression_abs_le (highIntrinsicFrameConstant C) eta Q.ρ
    (highIntrinsicFrameConstant_ge_one C) heta (sourceIntrinsicAmplitude_le_half heta hcap)
    U hU g w hg hw c hc i
  exact (Q.legal _ V hf hV).2.2.1 y

/-- This interface matches the source path's response-floor call, with the
two source constants specified exactly rather than chosen existentially. -/
theorem highUnionSource_intrinsic_ternary_floor {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) :
    ∀ k F : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)), 4 ≤ k →
      ∀ (I : Type*) (_ : Fintype I) (E : I → Type*) (_ : (i : I) → MeasurableSpace (E i))
        (R : HighUnionRowData d k F I E) (M : ℝ),
      HighUnionSourceGuards C M (highIntrinsicFrameConstant C) R →
      ∀ cf : ℝ, 0 ≤ cf → cf*(k : ℝ)^(-C.smoothness) ≤ Q.ρ/(2 : ℝ)^(d+1) →
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E),
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ →
      ∀ x y, Q.c ≤ ternaryMass Q.a
        (highUnionSourceRegression C R (cf*(k : ℝ)^(-C.smoothness)) h x) V y := by
  intro k F hk0 horder hk I hI E hE R M G cf hcf hcap h V hV x y
  letI := hk0
  letI := horder
  letI := hI
  letI := hE
  have heta : 0 ≤ cf*(k : ℝ)^(-C.smoothness) := by positivity
  have hf := highUnionSource_intrinsic_regression_abs_le_half C Q R G hk _ heta hcap h x
  exact (Q.legal _ V (hf.trans (by linarith [Q.ρ_pos])) hV).2.2.1 y

/-- Original-model legality of every mass-good history at the exact source
frame and amplitude cap, uniformly over all extension domains. -/
theorem highUnionSource_intrinsic_original_model_uniform {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) :
    ∀ U : ExtensionDomain d,
    ∀ k F : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)), 4 ≤ k →
      ∀ (I : Type*) (_ : Fintype I) (E : I → Type*) (_ : (i : I) → MeasurableSpace (E i))
        (_ : (i : I) → StandardBorelSpace (E i))
        (R : HighUnionRowData d k F I E) (M : ℝ),
      HighUnionSourceGuards C M (highIntrinsicFrameConstant C) R →
      ∀ cf : ℝ, 0 ≤ cf → highWindowHolderConstant C*cf ≤ C.holderBound →
        cf*(k : ℝ)^(-C.smoothness) ≤ Q.ρ/(2 : ℝ)^(d+1) →
      ∀ cm : ℝ, 0 ≤ cm → cm ≤ 1/C.densityUpper →
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E),
        |highUnionSourceMass C R h-1| ≤ cm/M →
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ →
      let p := highUnionSourceDensity C R h
      let f := highUnionSourceRegression C R (cf*(k : ℝ)^(-C.smoothness)) h
      ∃ hq : ∀ x y, 0 ≤ ternaryMass Q.a (f x) V y,
        Admissible (C.withDomain U) (normalizedDensityTernaryParameter p f Q.a V
          (highFrameField_contDiff d k _ _).continuous.measurable Q.a_pos.ne' hq) := by
  intro U k F hk0 horder hk I hI E hE hEB R M G cf hcf hbudget hcap cm hcm hcmU h hmass V hV
  letI := hk0
  letI := horder
  letI := hI
  letI := hE
  letI := hEB
  exact highFrame_intrinsic_source_cap_admissible C Q U k hk0 hk cf hcf hbudget
    (fun j => highFramePolynomial ((highUnionSourceState C R h).2 j))
    (fun j => (highFramePolynomial_coefficientL1_le _).trans
      (highUnionSourceState_coefficient_ball C R G h j)) hcap M cm
    (highCenterResolution_guards C M G.resolution).1 hcm hcmU
    (highUnionSourceDensity C R h)
    ((highUnionSourceDensity_joint_measurable C R G).comp (measurable_const.prodMk measurable_id))
    (Filter.Eventually.of_forall (fun x => highUnionSourceDensity_interval C R G h x)) hmass V hV

/-- The same strictly positive response floor holds throughout the actual
variance path, on all histories including the mass-exceptional ones. -/
theorem highUnionSource_intrinsic_ternary_floor_atTime {d k F : ℕ}
    {I : Type*} [Fintype I] {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (R : HighUnionRowData d k F I E) (M : ℝ)
    (G : HighUnionSourceGuards C M (highIntrinsicFrameConstant C) R) (hk : 4 ≤ k)
    (cf : ℝ) (hcf : 0 ≤ cf) (hcap : cf*(k : ℝ)^(-C.smoothness) ≤ Q.ρ/(2 : ℝ)^(d+1))
    (T : ℝ) (hbudget : (cf*(k : ℝ)^(-C.smoothness))^2*T ≤ Q.ρ)
    (t : ℝ) (ht : t ∈ Icc 0 T)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Covariate d) (y : Fin 3) :
    Q.c ≤ ternaryMass Q.a (highUnionSourceRegression C R (cf*(k : ℝ)^(-C.smoothness)) h x)
      (Q.v-(cf*(k : ℝ)^(-C.smoothness))^2*t) y := by
  have hV : |(Q.v-(cf*(k : ℝ)^(-C.smoothness))^2*t)-Q.v| ≤ Q.ρ := by
    simp only [sub_sub_cancel_left,abs_neg,abs_mul,
      abs_of_nonneg (sq_nonneg (cf*(k : ℝ)^(-C.smoothness))),abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg _)).trans hbudget
  exact highUnionSource_intrinsic_ternary_floor C Q k F inferInstance inferInstance hk
    I inferInstance E inferInstance R M G cf hcf hcap h _ hV x y

end NearlyMinimax
