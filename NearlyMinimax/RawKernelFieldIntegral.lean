module

public import NearlyMinimax.RawKernelFieldMeasurability


@[expose] public section

/-! Scalar weighted kernel integrals agree with their genuine Bochner L²
integrals. Product integrability is derived from a uniform section L² bound. -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

section
variable {W O : Type*} [MeasurableSpace W] [MeasurableSpace O]
  (M : Measure W) (μ : Measure O) [IsFiniteMeasure M] [IsFiniteMeasure μ] [IsSeparable μ]

omit [IsSeparable μ] in
theorem integral_norm_mul_le_L2_norms {f g : O → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ o, ‖f o * g o‖ ∂μ) ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have h := PilotFields.inner_integral_sq_le hf.norm hg.norm
  simp only [Real.inner_apply, norm_norm, ← norm_mul] at h
  rw [← PilotFields.toLp_norm_sq hf, ← PilotFields.toLp_norm_sq hg] at h
  apply (sq_le_sq₀ (integral_nonneg (fun _ => norm_nonneg _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow] using h

omit [IsSeparable μ] in
/-- A finite spatial measure and a uniform section norm bound yield actual
joint square integrability of a merely Borel scalar kernel. -/
theorem rawKernel_memLp_prod_of_uniform_bound (K : W → O → ℝ)
    (hm : Measurable (Function.uncurry K)) (hK : ∀ w, MemLp (K w) 2 μ)
    (C : ℝ) (_hC : 0 ≤ C) (hbound : ∀ w, ‖rawKernelSection μ K hK w‖ ≤ C) :
    MemLp (Function.uncurry K) 2 (M.prod μ) := by
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
  have hsq : Measurable (fun z : W × O => K z.1 z.2 ^ 2) := hm.pow_const 2
  apply (integrable_prod_iff hsq.aestronglyMeasurable).2
  refine ⟨Filter.Eventually.of_forall (fun w => (hK w).integrable_sq), ?_⟩
  have hmI : AEStronglyMeasurable (fun w => ∫ o, ‖K w o ^ 2‖ ∂μ) M :=
    hsq.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
  apply (integrable_const (C^2)).mono' hmI
  apply Filter.Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  simp only [Real.norm_eq_abs, abs_sq]
  have hnorm := PilotFields.toLp_norm_sq (hK w)
  simp only [Real.norm_eq_abs, sq_abs] at hnorm
  rw [← hnorm]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound w) 2

def weightedRawKernel (ν : W → ℝ) (K : W → O → ℝ) : O → ℝ :=
  fun o => ∫ w, ν w * K w o ∂M

omit [IsFiniteMeasure M] in
/-- Genuine Bochner integrability follows from the scalar weight's L¹
integrability and the actual uniform L² section bound. -/
theorem rawKernelSection_weighted_integrable (ν : W → ℝ) (hν : Integrable ν M)
    (K : W → O → ℝ) (hm : Measurable (Function.uncurry K)) (hK : ∀ w, MemLp (K w) 2 μ)
    (C : ℝ) (hbound : ∀ w, ‖rawKernelSection μ K hK w‖ ≤ C) :
    Integrable (fun w => ν w • rawKernelSection μ K hK w) M := by
  apply (hν.norm.mul_const C).mono'
    (hν.aestronglyMeasurable.smul (rawKernelSection_aestronglyMeasurable μ M K hm hK))
  exact Filter.Eventually.of_forall (fun w => by
    change ‖ν w • rawKernelSection μ K hK w‖ ≤ ‖ν w‖*C
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hbound w) (norm_nonneg _))

omit [IsSeparable μ] in
/-- The ordinary scalar integral is L² under the original sample law. -/
theorem weightedRawKernel_memLp (ν : W → ℝ) (hν : MemLp ν 2 M)
    (K : W → O → ℝ) (hm : Measurable (Function.uncurry K)) (hK : ∀ w, MemLp (K w) 2 μ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ w, ‖rawKernelSection μ K hK w‖ ≤ C) :
    MemLp (weightedRawKernel M ν K) 2 μ := by
  have hjoint := rawKernel_memLp_prod_of_uniform_bound M μ K hm hK C hC hbound
  have hcolumn : ∀ᵐ o ∂μ, MemLp (fun w => K w o) 2 M := by
    filter_upwards [hjoint.aestronglyMeasurable.prodMk_right,
      hjoint.integrable_sq.prod_left_ae] with o ho hi
    exact (memLp_two_iff_integrable_sq ho).2 hi
  have hmWeighted : AEStronglyMeasurable (fun z : W × O => ν z.1*K z.1 z.2) (M.prod μ) :=
    hν.aestronglyMeasurable.comp_fst.mul hm.aestronglyMeasurable
  have hmF : AEStronglyMeasurable (weightedRawKernel M ν K) μ :=
    hmWeighted.prod_swap.integral_prod_right'
  apply (memLp_two_iff_integrable_sq hmF).2
  have hi := hjoint.integrable_sq.integral_prod_right.const_mul (∫ w, ‖ν w‖^2 ∂M)
  apply hi.mono' (hmF.pow 2)
  filter_upwards [hcolumn] with o ho
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [weightedRawKernel, Real.inner_apply, Real.norm_eq_abs, sq_abs,
    Pi.pow_apply, Function.uncurry_apply_pair] using
    PilotFields.inner_integral_sq_le hν ho

/-- The scalar weighted kernel is exactly its Bochner integral in L²,
not just a weak integral supplied as an assumption. -/
theorem weightedRawKernel_toLp_eq_integral (ν : W → ℝ) (hν : MemLp ν 2 M)
    (K : W → O → ℝ) (hm : Measurable (Function.uncurry K)) (hK : ∀ w, MemLp (K w) 2 μ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ w, ‖rawKernelSection μ K hK w‖ ≤ C) :
    (weightedRawKernel_memLp M μ ν hν K hm hK C hC hbound).toLp (weightedRawKernel M ν K) =
      ∫ w, ν w • rawKernelSection μ K hK w ∂M := by
  let F := weightedRawKernel M ν K
  let hF := weightedRawKernel_memLp M μ ν hν K hm hK C hC hbound
  have hνInt : Integrable ν M := hν.integrable (by norm_num)
  have hBochner := rawKernelSection_weighted_integrable M μ ν hνInt K hm hK C hbound
  apply ext_inner_left ℝ
  intro u
  have hTestMeas : AEStronglyMeasurable
      (fun z : W × O => ν z.1 * (K z.1 z.2 * u z.2)) (M.prod μ) :=
    hν.aestronglyMeasurable.comp_fst.mul
      (hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u).comp_snd)
  have hTest : Integrable (fun z : W × O => ν z.1 * (K z.1 z.2 * u z.2)) (M.prod μ) := by
    apply (integrable_prod_iff hTestMeas).2
    refine ⟨Filter.Eventually.of_forall (fun w => ((hK w).integrable_mul (Lp.memLp u)).const_mul (ν w)), ?_⟩
    have hmI := hTestMeas.norm.integral_prod_right'
    apply ((hνInt.norm.mul_const C).mul_const ‖u‖).mono' hmI
    apply Filter.Eventually.of_forall
    intro w
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simp_rw [norm_mul]
    rw [integral_const_mul]
    have hprod := integral_norm_mul_le_L2_norms μ (hK w) (Lp.memLp u)
    rw [Lp.toLp_coeFn] at hprod
    change (∫ o, ‖K w o*u o‖ ∂μ) ≤ ‖rawKernelSection μ K hK w‖*‖u‖ at hprod
    simp only [norm_mul] at hprod
    apply (mul_le_mul_of_nonneg_left hprod (norm_nonneg (ν w))).trans
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hbound w) (norm_nonneg u))
      (norm_nonneg (ν w))).trans_eq (by ring)
  have hInner (w : W) : ⟪u, rawKernelSection μ K hK w⟫ = ∫ o, K w o * u o ∂μ := by
    have hi := PilotFields.toLp_inner (Lp.memLp u) (hK w)
    rw [Lp.toLp_coeFn] at hi
    simpa only [rawKernelSection, Real.inner_apply, mul_comm] using hi
  rw [← integral_inner hBochner u]
  simp_rw [real_inner_smul_right, hInner, ← integral_const_mul]
  rw [← integral_prod _ hTest, integral_prod_symm _ hTest]
  have hFi := PilotFields.toLp_inner (Lp.memLp u) hF
  rw [Lp.toLp_coeFn] at hFi
  rw [hFi]
  apply integral_congr_ae
  filter_upwards [hTest.prod_left_ae] with o ho
  rw [Real.inner_apply]
  dsimp [F, weightedRawKernel]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => by ring)

/-- The weighted scalar integral has the same genuine norm bound as its
Bochner representation. -/
theorem weightedRawKernel_toLp_norm_le (ν : W → ℝ) (hν : MemLp ν 2 M)
    (K : W → O → ℝ) (hm : Measurable (Function.uncurry K)) (hK : ∀ w, MemLp (K w) 2 μ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ w, ‖rawKernelSection μ K hK w‖ ≤ C) :
    ‖(weightedRawKernel_memLp M μ ν hν K hm hK C hC hbound).toLp (weightedRawKernel M ν K)‖ ≤
      C * ∫ w, ‖ν w‖ ∂M := by
  rw [weightedRawKernel_toLp_eq_integral M μ ν hν K hm hK C hC hbound]
  have hνInt := hν.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hBochner := rawKernelSection_weighted_integrable M μ ν hνInt K hm hK C hbound
  apply (norm_integral_le_integral_norm (fun w => ν w • rawKernelSection μ K hK w)).trans
  apply (integral_mono hBochner.norm (hνInt.norm.mul_const C)
    (fun w => by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hbound w) (norm_nonneg _))).trans_eq
  rw [integral_mul_const]
  ring

omit [IsSeparable μ] in
/-- A centered raw scalar field yields a centered weighted scalar integral.
The genuine joint L¹/Fubini premise is derived from its uniform L² bound. -/
theorem weightedRawKernel_integral_zero (ν : W → ℝ) (hν : MemLp ν 2 M)
    (K : W → O → ℝ) (hm : Measurable (Function.uncurry K)) (hK : ∀ w, MemLp (K w) 2 μ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ w, ‖rawKernelSection μ K hK w‖ ≤ C)
    (hzero : ∀ w, (∫ o, K w o ∂μ) = 0) :
    (∫ o, weightedRawKernel M ν K o ∂μ) = 0 := by
  have hjoint := rawKernel_memLp_prod_of_uniform_bound M μ K hm hK C hC hbound
  have hνJoint : MemLp (fun z : W × O => ν z.1) 2 (M.prod μ) := by
    exact hν.comp_fst μ
  have hi : Integrable (fun z : W × O => ν z.1*K z.1 z.2) (M.prod μ) :=
    hνJoint.integrable_mul hjoint
  unfold weightedRawKernel
  rw [← integral_prod_symm _ hi, integral_prod _ hi]
  simp only [integral_const_mul, hzero, mul_zero, integral_zero]

end
end NearlyMinimax
