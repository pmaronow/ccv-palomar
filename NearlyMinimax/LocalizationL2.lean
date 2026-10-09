module

public import Mathlib


@[expose] public section

/-! Hilbert-space localization for unbounded square-integrable kernel fields. -/
noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace NearlyMinimax.LocalizationL2

set_option backward.isDefEq.respectTransparency false

variable {W E : Type*} [MeasurableSpace W]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {M : Measure W} [IsFiniteMeasure M]

/-- The finite-measure Cauchy bound, proved by integrating a nonnegative square. -/
theorem integral_sq_le_mass_mul_integral_sq {f : W → ℝ} (hf : MemLp f 2 M) :
    (∫ w, f w ∂M) ^ 2 ≤ M.real Set.univ * ∫ w, f w ^ 2 ∂M := by
  let a := ∫ w, f w ∂M
  let b := M.real Set.univ
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  by_cases hb0 : b = 0
  · have hM0 : M = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      exact (measureReal_eq_zero_iff).mp hb0
    simp [hM0]
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hi : Integrable f M := hf.integrable (by norm_num)
    have hi2 := hf.integrable_sq
    have hic : Integrable (fun w => f w ^ 2 - (2 * (a / b)) * f w + (a / b) ^ 2) M :=
      (hi2.sub (hi.const_mul _)).add (integrable_const _)
    have heq : (∫ w, (f w - a / b) ^ 2 ∂M) =
        (∫ w, f w ^ 2 ∂M) - (2 * (a / b)) * a + b * (a / b) ^ 2 := by
      have hfalg : (fun w => (f w - a / b) ^ 2) =
          (fun w => f w ^ 2 - (2 * (a / b)) * f w + (a / b) ^ 2) := by
        funext w
        ring
      rw [hfalg]
      have ha := integral_add (hi2.sub (hi.const_mul (2 * (a / b))))
        (integrable_const ((a / b) ^ 2) : Integrable (fun _ : W => (a / b) ^ 2) M)
      have hs := integral_sub hi2 (hi.const_mul (2 * (a / b)))
      simp only [Pi.sub_apply] at ha hs
      rw [ha, hs, integral_const_mul, integral_const]
      rfl
    have hnon : 0 ≤ (∫ w, f w ^ 2 ∂M) - (2 * (a / b)) * a + b * (a / b) ^ 2 := by
      rw [← heq]
      exact integral_nonneg fun _ => sq_nonneg _
    have hid : b * ((∫ w, f w ^ 2 ∂M) - (2 * (a / b)) * a + b * (a / b) ^ 2) =
        b * (∫ w, f w ^ 2 ∂M) - a ^ 2 := by
      field_simp
      ring
    have hmul := mul_nonneg hb hnon
    rw [hid] at hmul
    exact sub_nonneg.mp hmul

/-- Integration of a Hilbert-valued `L²` field is bounded by its mass and energy. -/
theorem norm_integral_sq_le_mass_mul_integral_norm_sq {f : W → E} (hf : MemLp f 2 M) :
    ‖∫ w, f w ∂M‖ ^ 2 ≤ M.real Set.univ * ∫ w, ‖f w‖ ^ 2 ∂M := by
  have hn := norm_integral_le_integral_norm (f := f) (μ := M)
  have hsq : ‖∫ w, f w ∂M‖ ^ 2 ≤ (∫ w, ‖f w‖ ∂M) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact hsq.trans (integral_sq_le_mass_mul_integral_sq hf.norm)

section Hilbert

lemma inner_integral_right (x : E) {N : Measure W} {f : W → E}
    (hf : Integrable f N) :
    ⟪x, ∫ w, f w ∂N⟫ = ∫ w, ⟪x, f w⟫ ∂N :=
  ((innerSL ℝ x).integral_comp_comm hf).symm

/-- Pointwise orthogonality of two fields implies orthogonality of their
actual Bochner integrals. -/
theorem integral_inner_eq_zero_of_pointwise {N P : Measure W} {f g : W → E}
    (hf : Integrable f N) (hg : Integrable g P)
    (horth : ∀ w v, ⟪f w, g v⟫ = 0) :
    ⟪∫ w, f w ∂N, ∫ v, g v ∂P⟫ = 0 := by
  rw [inner_integral_right _ hg]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun v => by
    calc
      ⟪∫ w, f w ∂N, g v⟫ = ⟪g v, ∫ w, f w ∂N⟫ := real_inner_comm _ _
      _ = ∫ w, ⟪g v, f w⟫ ∂N := inner_integral_right _ hf
      _ = 0 := integral_eq_zero_of_ae (Filter.Eventually.of_forall fun w => by
        change ⟪g v, f w⟫ = 0
        rw [real_inner_comm, horth w v])

/-- Almost-everywhere cross-block orthogonality is sufficient. -/
theorem integral_inner_eq_zero_of_ae {N P : Measure W} {f g : W → E}
    (hf : Integrable f N) (hg : Integrable g P)
    (horth : ∀ᵐ v ∂P, ∀ᵐ w ∂N, ⟪f w, g v⟫ = 0) :
    ⟪∫ w, f w ∂N, ∫ v, g v ∂P⟫ = 0 := by
  rw [inner_integral_right _ hg]
  apply integral_eq_zero_of_ae
  filter_upwards [horth] with v hv
  calc
    ⟪∫ w, f w ∂N, g v⟫ = ⟪g v, ∫ w, f w ∂N⟫ := real_inner_comm _ _
    _ = ∫ w, ⟪g v, f w⟫ ∂N := inner_integral_right _ hf
    _ = 0 := integral_eq_zero_of_ae (hv.mono fun w hw => by
      change ⟪g v, f w⟫ = 0
      rw [real_inner_comm, hw])

/-- The localization inequality for finitely many orthogonal blocks. The
block measures may be restrictions of one finite parameter measure. -/
theorem finite_block_integral_bound {q : ℕ}
    (N : Fin q → Measure W) [∀ c, IsFiniteMeasure (N c)]
    (F : Fin q → W → E) (hF : ∀ c, MemLp (F c) 2 (N c))
    (horth : ∀ c d, c ≠ d → ∀ᵐ v ∂N d, ∀ᵐ w ∂N c, ⟪F c w, F d v⟫ = 0)
    (L : ℝ) (hL : ∀ c, (N c).real Set.univ ≤ L) :
    ‖∑ c : Fin q, ∫ w, F c w ∂N c‖ ^ 2 ≤
      L * ∑ c : Fin q, ∫ w, ‖F c w‖ ^ 2 ∂N c := by
  let I : Fin q → E := fun c => ∫ w, F c w ∂N c
  have hIorth : ∀ c d, c ≠ d → ⟪I c, I d⟫ = 0 := fun c d hcd =>
    integral_inner_eq_zero_of_ae ((hF c).integrable (by norm_num))
      ((hF d).integrable (by norm_num)) (horth c d hcd)
  have hsum : ‖∑ c : Fin q, I c‖ ^ 2 = ∑ c : Fin q, ‖I c‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    apply Finset.sum_congr rfl
    intro c _
    rw [inner_sum, Finset.sum_eq_single c]
    · exact real_inner_self_eq_norm_sq _
    · intro d _ hdc
      exact hIorth c d (Ne.symm hdc)
    · exact fun h => (h (Finset.mem_univ c)).elim
  change ‖∑ c : Fin q, I c‖ ^ 2 ≤ _
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  exact (norm_integral_sq_le_mass_mul_integral_norm_sq (hF c)).trans
    (mul_le_mul_of_nonneg_right (hL c) (integral_nonneg fun _ => sq_nonneg _))

/-- Integrating over a measurable finite partition is summing the block integrals. -/
theorem integral_eq_sum_fibers {q : ℕ} (b : W → Fin q) (hb : Measurable b)
    {f : W → E} (hf : Integrable f M) :
    (∫ w, f w ∂M) = ∑ c : Fin q, ∫ w in {v | b v = c}, f w ∂M := by
  classical
  have hB : ∀ c, MeasurableSet {v | b v = c} := fun c => measurableSet_eq_fun hb measurable_const
  have hi : ∀ c, Integrable (({v | b v = c} : Set W).indicator f) M :=
    fun c => hf.indicator (hB c)
  calc
    _ = ∫ w, ∑ c : Fin q, ({v | b v = c} : Set W).indicator f w ∂M := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => by
        change f w = ∑ c : Fin q, ({v | b v = c} : Set W).indicator f w
        rw [Finset.sum_eq_single (b w)]
        · simp
        · intro c _ hc
          simp [Set.indicator, Ne.symm hc]
        · exact fun h => (h (Finset.mem_univ (b w))).elim
    _ = ∑ c : Fin q, ∫ w, ({v | b v = c} : Set W).indicator f w ∂M :=
      integral_finsetSum _ (fun c _ => hi c)
    _ = _ := Finset.sum_congr rfl (fun c _ => integral_indicator (hB c))

/-- A finite partition with mutually orthogonal kernel blocks gains the largest
block mass instead of the total mass in the integral Cauchy bound. -/
theorem partition_localization_bound {q : ℕ} (b : W → Fin q) (hb : Measurable b)
    (K : W → E) (hK : MemLp K 2 M)
    (horth : ∀ w v, b w ≠ b v → ⟪K w, K v⟫ = 0)
    (L : ℝ) (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    ‖∫ w, K w ∂M‖ ^ 2 ≤ L * ∫ w, ‖K w‖ ^ 2 ∂M := by
  have hB : ∀ c, MeasurableSet {w | b w = c} := fun c => measurableSet_eq_fun hb measurable_const
  have hKint : Integrable K M := hK.integrable (by norm_num)
  have hnormint : Integrable (fun w => ‖K w‖ ^ 2) M := hK.norm.integrable_sq
  have hsum := finite_block_integral_bound (fun c => M.restrict {w | b w = c})
    (fun _ => K) (fun c => hK.restrict _) (fun c d hcd => by
      filter_upwards [ae_restrict_mem (hB d)] with v hv
      filter_upwards [ae_restrict_mem (hB c)] with w hw
      exact horth w v (by
        change b w = c at hw
        change b v = d at hv
        rw [hw, hv]
        exact hcd))
    L (fun c => by simpa only [measureReal_restrict_apply_univ] using hL c)
  rw [← integral_eq_sum_fibers b hb hKint] at hsum
  have hscalar : (∑ c : Fin q, ∫ w in {v | b v = c}, ‖K w‖ ^ 2 ∂M) =
      ∫ w, ‖K w‖ ^ 2 ∂M := by
    -- The same partition identity for real-valued energy.
    exact (integral_eq_sum_fibers (E := ℝ) b hb hnormint).symm
  rw [hscalar] at hsum
  exact hsum

/-- A uniformly `L²` bounded kernel field times an `L²` weight is an `L²`
Bochner field. Here the Hilbert norm is the kernel's observation `L²` norm. -/
theorem weighted_field_memLp_two (ν : W → ℝ) (hν : MemLp ν 2 M)
    (K : W → E) (hK : AEStronglyMeasurable K M)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᵐ w ∂M, ‖K w‖ ≤ C) :
    MemLp (fun w => ν w • K w) 2 M := by
  apply (hν.const_mul C).of_le (hν.aestronglyMeasurable.smul hK)
  filter_upwards [hbound] with w hw
  calc
    ‖ν w • K w‖ = ‖ν w‖ * ‖K w‖ := norm_smul _ _
    _ ≤ ‖ν w‖ * C := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = ‖C * ν w‖ := by rw [norm_mul, Real.norm_of_nonneg hC]; ring

/-- The weighted localization estimate of original U6, with actual Bochner
integration and unbounded observation kernels represented in a Hilbert space. -/
theorem weighted_partition_localization_bound {q : ℕ}
    (b : W → Fin q) (hb : Measurable b)
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (K : W → E) (hK : AEStronglyMeasurable K M)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᵐ w ∂M, ‖K w‖ ≤ C)
    (horth : ∀ w v, b w ≠ b v → ⟪K w, K v⟫ = 0)
    (L : ℝ) (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    ‖∫ w, ν w • K w ∂M‖ ^ 2 ≤ L * ∫ w, ν w ^ 2 * ‖K w‖ ^ 2 ∂M := by
  have hlp := weighted_field_memLp_two ν hν K hK C hC hbound
  have hweightedorth : ∀ w v, b w ≠ b v → ⟪ν w • K w, ν v • K v⟫ = 0 := by
    intro w v hwv
    rw [real_inner_smul_left, real_inner_smul_right, horth w v hwv]
    ring
  have h := partition_localization_bound b hb _ hlp hweightedorth L hL
  simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using h

end Hilbert

section ObservationKernels
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The genuine Hilbert `L²` norm is the integral second moment. -/
theorem toLp_norm_sq_eq_integral_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with ω hω
  rw [hω]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Disjoint raw observation supports imply orthogonality of the actual `L²`
kernel elements; the supports need only be disjoint almost everywhere. -/
theorem toLp_inner_eq_zero_of_disjoint {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hdisjoint : ∀ᵐ ω ∂μ, f ω * g ω = 0) :
    ⟪hf.toLp f, hg.toLp g⟫ = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp, hdisjoint] with ω hfω hgω hω
  change inner ℝ ((hf.toLp f) ω) ((hg.toLp g) ω) = 0
  rw [hfω, hgω]
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using hω

/-- U6's block localization inequality for raw kernels on any observation
space, with the true second moments on the right. -/
theorem raw_kernel_partition_localization_bound {q : ℕ}
    (b : W → Fin q) (hb : Measurable b)
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (K : W → Ω → ℝ) (hK : ∀ w, MemLp (K w) 2 μ)
    (hfield : AEStronglyMeasurable (fun w => (hK w).toLp (K w)) M)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᵐ w ∂M, ‖(hK w).toLp (K w)‖ ≤ C)
    (hdisjoint : ∀ w v, b w ≠ b v → ∀ᵐ ω ∂μ, K w ω * K v ω = 0)
    (L : ℝ) (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    ‖∫ w, ν w • (hK w).toLp (K w) ∂M‖ ^ 2 ≤
      L * ∫ w, ν w ^ 2 * (∫ ω, K w ω ^ 2 ∂μ) ∂M := by
  have h := weighted_partition_localization_bound b hb ν hν _ hfield C hC hbound
    (fun w v hwv => toLp_inner_eq_zero_of_disjoint (hK w) (hK v) (hdisjoint w v hwv)) L hL
  simpa only [toLp_norm_sq_eq_integral_sq] using h

end ObservationKernels
/-- The block estimate summed over kernel orders, allowing each order to live
in its own observation Hilbert space. This is U6's second localized inequality. -/
theorem weighted_kernel_series_localization_bound {D q : ℕ}
    {H : Fin D → Type*} [∀ r, NormedAddCommGroup (H r)]
    [∀ r, InnerProductSpace ℝ (H r)] [∀ r, CompleteSpace (H r)]
    (b : W → Fin q) (hb : Measurable b)
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (K : (r : Fin D) → W → H r)
    (hK : ∀ r, AEStronglyMeasurable (K r) M)
    (C : Fin D → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r, ∀ᵐ w ∂M, ‖K r w‖ ≤ C r)
    (horth : ∀ r w v, b w ≠ b v → inner ℝ (K r w) (K r v) = 0)
    (δ : Fin D → ℝ) (hδ : ∀ r, 0 ≤ δ r)
    (L : ℝ) (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    (∑ r : Fin D, δ r * ‖∫ w, ν w • K r w ∂M‖ ^ 2) ≤
      L * ∫ w, ν w ^ 2 * ∑ r : Fin D, δ r * ‖K r w‖ ^ 2 ∂M := by
  have hi : ∀ r, Integrable (fun w => ν w ^ 2 * ‖K r w‖ ^ 2) M := by
    intro r
    have hlp := weighted_field_memLp_two ν hν (K r) (hK r) (C r) (hC r) (hbound r)
    simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using hlp.norm.integrable_sq
  have heq : (∫ w, ν w ^ 2 * ∑ r : Fin D, δ r * ‖K r w‖ ^ 2 ∂M) =
      ∑ r : Fin D, δ r * ∫ w, ν w ^ 2 * ‖K r w‖ ^ 2 ∂M := by
    simp_rw [Finset.mul_sum]
    have hfalg : (fun w => ∑ r : Fin D, ν w ^ 2 * (δ r * ‖K r w‖ ^ 2)) =
        (fun w => ∑ r : Fin D, δ r * (ν w ^ 2 * ‖K r w‖ ^ 2)) := by
      funext w
      apply Finset.sum_congr rfl
      intro r _
      ring
    rw [hfalg, integral_finsetSum _ (fun r _ => (hi r).const_mul (δ r))]
    simp_rw [integral_const_mul]
  calc
    _ ≤ ∑ r : Fin D, δ r * (L * ∫ w, ν w ^ 2 * ‖K r w‖ ^ 2 ∂M) := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_left
        (weighted_partition_localization_bound b hb ν hν (K r) (hK r)
          (C r) (hC r) (hbound r) (horth r) L hL) (hδ r)
    _ = _ := by rw [heq, Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

end NearlyMinimax.LocalizationL2


