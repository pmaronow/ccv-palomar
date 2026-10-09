module

public import NearlyMinimax.RawLiftHilbert
public import NearlyMinimax.RawKernelFieldIntegral
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated


@[expose] public section

/-!
The measurable-field inequalities of U6 in raw observation L² spaces.
Feature counts and feature maps may vary with the field parameter. All
integrability comes from the actual raw-kernel bounds and an L² scalar weight.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace NearlyMinimax.RawLiftHilbert
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {O W : Type*} [MeasurableSpace O] [MeasurableSpace W]
  (μ : Measure O) [IsProbabilityMeasure μ] (M : Measure W) [IsFiniteMeasure M]

instance rawKernelSpace_completeSpace (k : ℕ) : CompleteSpace (rawKernelSpace μ k) := by
  unfold rawKernelSpace
  infer_instance

theorem centeredLiftSeries_integral_commute {R n : ℕ}
    (K : (r : Fin R) → W → rawKernelSpace μ (r.val + 1))
    (ν : W → ℝ) (hK : ∀ r, Integrable (fun w => ν w • K r w) M) :
    (∫ w, ν w • centeredLiftSeries μ n (fun r => K r w) ∂M) =
      centeredLiftSeries μ n (fun r => ∫ w, ν w • K r w ∂M) := by
  classical
  have hi (r : Fin R) : Integrable
      (fun w => ν w • centeredLiftOperator μ (r.val + 1) n (K r w)) M := by
    simpa only [map_smul] using
      (centeredLiftOperator μ (r.val + 1) n).integrable_comp (hK r)
  simp only [centeredLiftSeries, Finset.smul_sum]
  rw [integral_finsetSum _ (fun r _ => hi r)]
  apply Finset.sum_congr rfl
  intro r _
  rw [← (centeredLiftOperator μ (r.val + 1) n).integral_comp_comm (hK r)]
  congr 1
  funext w
  exact (map_smul _ _ _).symm

/-- U6's first Hilbert-field inequality, without a support partition or
coefficient integrability assumption. -/
theorem integrated_centeredLiftSeries_norm_sq_le {R n : ℕ} (hRn : R ≤ n)
    (K : (r : Fin R) → W → rawKernelSpace μ (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hK : ∀ r, AEStronglyMeasurable (K r) M)
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r, ∀ᵐ w ∂M, ‖K r w‖ ≤ C r)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    ‖∫ w, ν w • centeredLiftSeries μ n (fun r => K r w) ∂M‖ ^ 2 ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
        ‖∫ w, ν w • K r w ∂M‖ ^ 2 := by
  have hi (r : Fin R) : Integrable (fun w => ν w • K r w) M :=
    (LocalizationL2.weighted_field_memLp_two ν hν (K r) (hK r) (C r) (hC r)
      (hbound r)).integrable (by norm_num)
  rw [centeredLiftSeries_integral_commute μ M K ν hi]
  exact centeredLiftSeries_norm_sq_le_power μ hRn _ Λ hΛ hΛn

/-- The second U6 inequality follows from genuine raw Hilbert orthogonality
between different spatial blocks. -/
theorem integrated_centeredLiftSeries_localized {R n q : ℕ} (hRn : R ≤ n)
    (K : (r : Fin R) → W → rawKernelSpace μ (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hK : ∀ r, AEStronglyMeasurable (K r) M)
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r, ∀ᵐ w ∂M, ‖K r w‖ ≤ C r)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1)
    (b : W → Fin q) (hb : Measurable b)
    (horth : ∀ r w v, b w ≠ b v → inner ℝ (K r w) (K r v) = 0)
    (L : ℝ) (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    ‖∫ w, ν w • centeredLiftSeries μ n (fun r => K r w) ∂M‖ ^ 2 ≤
      L * ∫ w, ν w ^ 2 * ∑ r : Fin R,
        (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ * ‖K r w‖ ^ 2 ∂M := by
  apply (integrated_centeredLiftSeries_norm_sq_le μ M hRn K ν hν hK C hC hbound
    Λ hΛ hΛn).trans
  exact LocalizationL2.weighted_kernel_series_localization_bound b hb ν hν K hK C hC
    hbound horth _ (fun r => by positivity) L hL

variable [MeasurableSpace.CountablyGenerated O]

instance finiteSample_countablyGenerated (n : ℕ) :
    MeasurableSpace.CountablyGenerated (Fin n → O) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
    letI := ih
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => O) 0
    have h := MeasurableSpace.CountablyGenerated.comap e
    rwa [e.measurableEmbedding.comap_eq] at h

def packetFieldRaw {R : ℕ} (P : W → (r : Fin R) → Packet μ (r.val + 1))
    (r : Fin R) : W → (Fin (r.val + 1) → O) → ℝ :=
  fun w => packetRaw μ (P w r)

def packetFieldCentered {R : ℕ} (P : W → (r : Fin R) → Packet μ (r.val + 1))
    (n : ℕ) : W → (Fin n → O) → ℝ :=
  fun w o => ∑ r : Fin R, packetStatistic μ (P w r) n o

theorem packetFieldCentered_memLp {R : ℕ}
    (P : W → (r : Fin R) → Packet μ (r.val + 1)) (n : ℕ) (w : W) :
    MemLp (packetFieldCentered μ P n w) 2 (SampleLaw μ n) :=
  memLp_finsetSum Finset.univ (fun r _ => packetStatistic_memLp μ (P w r) n)

theorem packetFieldCentered_toLp {R : ℕ}
    (P : W → (r : Fin R) → Packet μ (r.val + 1)) (n : ℕ) (w : W) :
    (packetFieldCentered_memLp μ P n w).toLp (packetFieldCentered μ P n w) =
      ∑ r : Fin R, packetStatisticLp μ (P w r) n := by
  classical
  apply Lp.ext
  have ht : ∀ᵐ o ∂SampleLaw μ n, ∀ r : Fin R,
      packetStatisticLp μ (P w r) n o = packetStatistic μ (P w r) n o :=
    Filter.eventually_all.mpr fun r => (packetStatistic_memLp μ (P w r) n).coeFn_toLp
  filter_upwards [(packetFieldCentered_memLp μ P n w).coeFn_toLp,
    Lp.coeFn_fun_finsetSum Finset.univ (fun r : Fin R => packetStatisticLp μ (P w r) n), ht]
    with o ho hs hr
  rw [ho, hs]
  exact Finset.sum_congr rfl fun r _ => (hr r).symm

theorem packetFieldRaw_subspace_measurable {R : ℕ}
    (P : W → (r : Fin R) → Packet μ (r.val + 1))
    (hm : ∀ r, Measurable (Function.uncurry (packetFieldRaw μ P r))) (r : Fin R) :
    AEStronglyMeasurable (fun w => packetInRawSpace μ (P w r)) M := by
  apply (Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).mp
  exact rawKernelSection_aestronglyMeasurable (SampleLaw μ (r.val + 1)) M
    (packetFieldRaw μ P r) (hm r) (fun w => packetRaw_memLp μ (P w r))

theorem packetFieldCentered_norm_bound {R n : ℕ} (hRn : R ≤ n)
    (P : W → (r : Fin R) → Packet μ (r.val + 1))
    (C : Fin R → ℝ) (hbound : ∀ r w, ‖packetRawLp μ (P w r)‖ ≤ C r) (w : W) :
    ‖(packetFieldCentered_memLp μ P n w).toLp (packetFieldCentered μ P n w)‖ ≤
      ∑ r : Fin R, Real.sqrt (((r.val + 1).factorial : ℝ) *
        (n.descFactorial (r.val + 1) : ℝ))⁻¹ * C r := by
  rw [packetFieldCentered_toLp]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r _
  rw [← centeredLiftOperator_packet μ (by omega)
    ((Nat.succ_le_of_lt r.isLt).trans hRn)]
  exact (centeredLiftOperator_norm_le μ (by omega)
    ((Nat.succ_le_of_lt r.isLt).trans hRn) _).trans
      (mul_le_mul_of_nonneg_left (hbound r w) (Real.sqrt_nonneg _))

def packetFieldCenteredBound {R : ℕ} (n : ℕ) (C : Fin R → ℝ) : ℝ :=
  ∑ r : Fin R, Real.sqrt (((r.val + 1).factorial : ℝ) *
    (n.descFactorial (r.val + 1) : ℝ))⁻¹ * C r

theorem packetFieldCenteredBound_nonneg {R : ℕ} (n : ℕ)
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r) : 0 ≤ packetFieldCenteredBound n C := by
  exact Finset.sum_nonneg (fun r _ => mul_nonneg (Real.sqrt_nonneg _) (hC r))

/-- Square integrability of the actual integrated centered scalar field is
derived from the raw bounds, rather than supplied as a field premise. -/
theorem packetField_integrated_centered_memLp {R n : ℕ} (hRn : R ≤ n)
    (P : W → (r : Fin R) → Packet μ (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hmZ : Measurable (Function.uncurry (packetFieldCentered μ P n)))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖packetRawLp μ (P w r)‖ ≤ C r) :
    MemLp (fun o => ∫ w, ν w * packetFieldCentered μ P n w o ∂M) 2 (SampleLaw μ n) :=
  weightedRawKernel_memLp M (SampleLaw μ n) ν hν (packetFieldCentered μ P n)
    hmZ (packetFieldCentered_memLp μ P n) (packetFieldCenteredBound n C)
    (packetFieldCenteredBound_nonneg n C hC) (packetFieldCentered_norm_bound μ hRn P C hbound)

theorem packetFieldCentered_mean_zero {R : ℕ}
    (P : W → (r : Fin R) → Packet μ (r.val + 1)) (n : ℕ) (w : W) :
    (∫ o, packetFieldCentered μ P n w o ∂SampleLaw μ n) = 0 := by
  unfold packetFieldCentered
  rw [integral_finsetSum _ (fun r _ =>
    (packetStatistic_memLp μ (P w r) n).integrable (by norm_num))]
  exact Finset.sum_eq_zero (fun r _ => packetStatistic_mean_zero μ (by omega) (P w r) n)

theorem packetField_integrated_centered_mean_zero {R n : ℕ} (hRn : R ≤ n)
    (P : W → (r : Fin R) → Packet μ (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hmZ : Measurable (Function.uncurry (packetFieldCentered μ P n)))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖packetRawLp μ (P w r)‖ ≤ C r) :
    (∫ o, ∫ w, ν w * packetFieldCentered μ P n w o ∂M ∂SampleLaw μ n) = 0 :=
  weightedRawKernel_integral_zero M (SampleLaw μ n) ν hν (packetFieldCentered μ P n)
    hmZ (packetFieldCentered_memLp μ P n) (packetFieldCenteredBound n C)
    (packetFieldCenteredBound_nonneg n C hC) (packetFieldCentered_norm_bound μ hRn P C hbound)
    (packetFieldCentered_mean_zero μ P n)

theorem packetFieldCentered_toLp_eq_series {R n : ℕ} (hRn : R ≤ n)
    (P : W → (r : Fin R) → Packet μ (r.val + 1)) (w : W) :
    (packetFieldCentered_memLp μ P n w).toLp (packetFieldCentered μ P n w) =
      centeredLiftSeries μ n (fun r => packetInRawSpace μ (P w r)) := by
  rw [packetFieldCentered_toLp]
  unfold centeredLiftSeries
  apply Finset.sum_congr rfl
  intro r _
  exact (centeredLiftOperator_packet μ (by omega)
    ((Nat.succ_le_of_lt r.isLt).trans hRn) _).symm

theorem packetField_weighted_centered_integral_norm_sq {R n : ℕ} (hRn : R ≤ n)
    (P : W → (r : Fin R) → Packet μ (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hmZ : Measurable (Function.uncurry (packetFieldCentered μ P n)))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖packetRawLp μ (P w r)‖ ≤ C r) :
    (∫ o, (∫ w, ν w * packetFieldCentered μ P n w o ∂M) ^ 2 ∂SampleLaw μ n) =
      ‖∫ w, ν w • centeredLiftSeries μ n
        (fun r => packetInRawSpace μ (P w r)) ∂M‖ ^ 2 := by
  have hb : ∀ w, ‖rawKernelSection (SampleLaw μ n) (packetFieldCentered μ P n)
      (packetFieldCentered_memLp μ P n) w‖ ≤ packetFieldCenteredBound n C :=
    packetFieldCentered_norm_bound μ hRn P C hbound
  have hf := weightedRawKernel_memLp M (SampleLaw μ n) ν hν (packetFieldCentered μ P n)
    hmZ (packetFieldCentered_memLp μ P n) (packetFieldCenteredBound n C)
    (packetFieldCenteredBound_nonneg n C hC) hb
  change (∫ o, weightedRawKernel M ν (packetFieldCentered μ P n) o ^ 2 ∂SampleLaw μ n) = _
  rw [← LocalizationL2.toLp_norm_sq_eq_integral_sq hf,
    weightedRawKernel_toLp_eq_integral M (SampleLaw μ n) ν hν (packetFieldCentered μ P n)
      hmZ (packetFieldCentered_memLp μ P n) (packetFieldCenteredBound n C)
      (packetFieldCenteredBound_nonneg n C hC) hb]
  congr 2
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  exact congrArg (fun z => ν w • z) (packetFieldCentered_toLp_eq_series μ hRn P w)

theorem packetField_weighted_raw_integral_norm_sq {R : ℕ}
    (P : W → (r : Fin R) → Packet μ (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hm : ∀ r, Measurable (Function.uncurry (packetFieldRaw μ P r)))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖packetRawLp μ (P w r)‖ ≤ C r) (r : Fin R) :
    (∫ o, (∫ w, ν w * packetFieldRaw μ P r w o ∂M) ^ 2 ∂SampleLaw μ (r.val + 1)) =
      ‖∫ w, ν w • packetInRawSpace μ (P w r) ∂M‖ ^ 2 := by
  have hi : Integrable (fun w => ν w • packetInRawSpace μ (P w r)) M :=
    (LocalizationL2.weighted_field_memLp_two ν hν _
      (packetFieldRaw_subspace_measurable μ M P hm r) (C r) (hC r)
      (Filter.Eventually.of_forall (hbound r))).integrable (by norm_num)
  have he := (rawKernelSpace μ (r.val + 1)).subtypeL.integral_comp_comm hi
  have hb : ∀ w, ‖rawKernelSection (SampleLaw μ (r.val + 1)) (packetFieldRaw μ P r)
      (fun w => packetRaw_memLp μ (P w r)) w‖ ≤ C r := hbound r
  have hf := weightedRawKernel_memLp M (SampleLaw μ (r.val + 1)) ν hν
    (packetFieldRaw μ P r) (hm r) (fun w => packetRaw_memLp μ (P w r)) (C r) (hC r) hb
  change (∫ o, weightedRawKernel M ν (packetFieldRaw μ P r) o ^ 2
    ∂SampleLaw μ (r.val + 1)) = _
  rw [← LocalizationL2.toLp_norm_sq_eq_integral_sq hf,
    weightedRawKernel_toLp_eq_integral M (SampleLaw μ (r.val + 1)) ν hν
      (packetFieldRaw μ P r) (hm r) (fun w => packetRaw_memLp μ (P w r)) (C r) (hC r) hb]
  change (∫ w, ν w • rawKernelSection (SampleLaw μ (r.val + 1)) (packetFieldRaw μ P r)
      (fun w => packetRaw_memLp μ (P w r)) w ∂M) =
    (((∫ w, ν w • packetInRawSpace μ (P w r) ∂M) : rawKernelSpace μ (r.val + 1)) :
      Lp ℝ 2 (SampleLaw μ (r.val + 1))) at he
  exact congrArg (fun z : Lp ℝ 2 (SampleLaw μ (r.val + 1)) => ‖z‖ ^ 2) he

/-- The literal first measurable-field inequality of U6. Each spatial point
and each order may use different features and a different feature dimension.
Only joint scalar measurability and the actual uniform raw L² bounds are
required. The scalar integrals are the actual integrals in the manuscript. -/
theorem packetField_integrated_centered_energy_le_raw {R n : ℕ} (hRn : R ≤ n)
    (P : W → (r : Fin R) → Packet μ (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hm : ∀ r, Measurable (Function.uncurry (packetFieldRaw μ P r)))
    (hmZ : Measurable (Function.uncurry (packetFieldCentered μ P n)))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖packetRawLp μ (P w r)‖ ≤ C r)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    (∫ o, (∫ w, ν w * packetFieldCentered μ P n w o ∂M) ^ 2 ∂SampleLaw μ n) ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
        (∫ o, (∫ w, ν w * packetFieldRaw μ P r w o ∂M) ^ 2
          ∂SampleLaw μ (r.val + 1)) := by
  rw [packetField_weighted_centered_integral_norm_sq μ M hRn P ν hν hmZ C hC hbound]
  simp_rw [packetField_weighted_raw_integral_norm_sq μ M P ν hν hm C hC hbound]
  exact integrated_centeredLiftSeries_norm_sq_le μ M hRn
    (fun r w => packetInRawSpace μ (P w r)) ν hν
    (packetFieldRaw_subspace_measurable μ M P hm) C hC
    (fun r => Filter.Eventually.of_forall (hbound r)) Λ hΛ hΛn

/-- U6's localized measurable-field conclusion. Raw support separation is
used before centering, so the gain is the spatial block mass. -/
theorem packetField_integrated_centered_energy_localized {R n q : ℕ} (hRn : R ≤ n)
    (P : W → (r : Fin R) → Packet μ (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hm : ∀ r, Measurable (Function.uncurry (packetFieldRaw μ P r)))
    (hmZ : Measurable (Function.uncurry (packetFieldCentered μ P n)))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖packetRawLp μ (P w r)‖ ≤ C r)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1)
    (b : W → Fin q) (hb : Measurable b)
    (hdisjoint : ∀ r w v, b w ≠ b v → ∀ᵐ o ∂SampleLaw μ (r.val + 1),
      packetFieldRaw μ P r w o * packetFieldRaw μ P r v o = 0)
    (L : ℝ) (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    (∫ o, (∫ w, ν w * packetFieldCentered μ P n w o ∂M) ^ 2 ∂SampleLaw μ n) ≤
      L * ∫ w, ν w ^ 2 * ∑ r : Fin R,
        (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
          (∫ o, packetFieldRaw μ P r w o ^ 2 ∂SampleLaw μ (r.val + 1)) ∂M := by
  rw [packetField_weighted_centered_integral_norm_sq μ M hRn P ν hν hmZ C hC hbound]
  have horth : ∀ r w v, b w ≠ b v →
      inner ℝ (packetInRawSpace μ (P w r)) (packetInRawSpace μ (P v r)) = 0 := by
    intro r w v hwv
    exact LocalizationL2.toLp_inner_eq_zero_of_disjoint
      (packetRaw_memLp μ (P w r)) (packetRaw_memLp μ (P v r)) (hdisjoint r w v hwv)
  have h := integrated_centeredLiftSeries_localized μ M hRn
    (fun r w => packetInRawSpace μ (P w r)) ν hν
    (packetFieldRaw_subspace_measurable μ M P hm) C hC
    (fun r => Filter.Eventually.of_forall (hbound r)) Λ hΛ hΛn b hb horth L hL
  have hnorm (r : Fin R) (w : W) : ‖packetInRawSpace μ (P w r)‖ ^ 2 =
      ∫ o, packetFieldRaw μ P r w o ^ 2 ∂SampleLaw μ (r.val + 1) := by
    change ‖packetRawLp μ (P w r)‖ ^ 2 = _
    exact LocalizationL2.toLp_norm_sq_eq_integral_sq (packetRaw_memLp μ (P w r))
  simpa only [hnorm] using h

end NearlyMinimax.RawLiftHilbert
