module

public import NearlyMinimax.RawLiftField
public import NearlyMinimax.RawLiftPacketRealization


@[expose] public section

/-!
U6 for the original scalar fields and their actual feature representatives.
The dimension and feature map may vary at every spatial point and order.
Joint measurability is imposed on the original scalar raw kernels and lifts,
never on the arbitrary pointwise representatives chosen by the Lp quotient.
-/
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace NearlyMinimax.RawLiftHilbert
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {O W : Type*} [MeasurableSpace O] [MeasurableSpace W]
  (μ : Measure O) [IsProbabilityMeasure μ]

structure OriginalPacket (k : ℕ) where
  featureCount : ℕ
  feature : O → Fin featureCount → ℝ
  squareIntegrable : ∀ a, MemLp (fun o => feature o a) 2 μ
  coefficient : FieldLiftCovariance.KernelMap featureCount k
  symmetric : ∀ (σ : Equiv.Perm (Fin k)) v,
    coefficient (fun i => v (σ i)) = coefficient v

def OriginalPacket.toPacket {k : ℕ} (P : OriginalPacket μ k) : Packet μ k :=
  packetOfFeatures μ P.feature P.squareIntegrable P.coefficient P.symmetric

def OriginalPacket.raw {k : ℕ} (P : OriginalPacket μ k) : (Fin k → O) → ℝ :=
  fun o => P.coefficient (fun i => P.feature (o i))

def OriginalPacket.statistic {k : ℕ} (P : OriginalPacket μ k) (n : ℕ) : (Fin n → O) → ℝ :=
  LiftL2.kernelStatistic P.coefficient
    (fun j o => P.feature (o j) - originalFeatureMean μ P.feature)

theorem OriginalPacket.raw_ae {k : ℕ} (P : OriginalPacket μ k) :
    packetRaw μ (P.toPacket μ) =ᵐ[SampleLaw μ k] P.raw μ :=
  packetOfFeatures_raw_ae μ P.feature P.squareIntegrable P.coefficient P.symmetric

theorem OriginalPacket.statistic_ae {k n : ℕ} (P : OriginalPacket μ k) :
    packetStatistic μ (P.toPacket μ) n =ᵐ[SampleLaw μ n] P.statistic μ n :=
  packetOfFeatures_statistic_ae μ P.feature P.squareIntegrable P.coefficient P.symmetric

theorem OriginalPacket.raw_memLp {k : ℕ} (P : OriginalPacket μ k) :
    MemLp (P.raw μ) 2 (SampleLaw μ k) :=
  (packetRaw_memLp μ (P.toPacket μ)).ae_eq (P.raw_ae μ)

def OriginalPacket.rawLp {k : ℕ} (P : OriginalPacket μ k) : Lp ℝ 2 (SampleLaw μ k) :=
  (P.raw_memLp μ).toLp (P.raw μ)

theorem OriginalPacket.rawLp_eq {k : ℕ} (P : OriginalPacket μ k) :
    P.rawLp μ = packetRawLp μ (P.toPacket μ) := by
  apply Lp.ext
  exact (P.raw_memLp μ).coeFn_toLp.trans
    ((P.raw_ae μ).symm.trans (packetRaw_memLp μ (P.toPacket μ)).coeFn_toLp.symm)

variable [MeasurableSpace.CountablyGenerated O]

def originalFieldRaw {R : ℕ} (P : W → (r : Fin R) → OriginalPacket μ (r.val + 1))
    (r : Fin R) : W → (Fin (r.val + 1) → O) → ℝ := fun w => (P w r).raw μ

def originalFieldCentered {R : ℕ} (P : W → (r : Fin R) → OriginalPacket μ (r.val + 1))
    (n : ℕ) : W → (Fin n → O) → ℝ := fun w o => ∑ r : Fin R, (P w r).statistic μ n o

theorem originalFieldCentered_ae {R : ℕ}
    (P : W → (r : Fin R) → OriginalPacket μ (r.val + 1)) (n : ℕ) (w : W) :
    packetFieldCentered μ (fun w r => (P w r).toPacket μ) n w =ᵐ[SampleLaw μ n]
      originalFieldCentered μ P n w := by
  have hh : ∀ᵐ o ∂SampleLaw μ n, ∀ r : Fin R,
      packetStatistic μ ((P w r).toPacket μ) n o = (P w r).statistic μ n o :=
    Filter.eventually_all.mpr (fun r => (P w r).statistic_ae μ)
  filter_upwards [hh] with o ho
  exact Finset.sum_congr rfl (fun r _ => ho r)

theorem originalFieldCentered_memLp {R : ℕ}
    (P : W → (r : Fin R) → OriginalPacket μ (r.val + 1)) (n : ℕ) (w : W) :
    MemLp (originalFieldCentered μ P n w) 2 (SampleLaw μ n) :=
  (packetFieldCentered_memLp μ (fun w r => (P w r).toPacket μ) n w).ae_eq
    (originalFieldCentered_ae μ P n w)

theorem originalFieldCentered_toLp_eq {R n : ℕ} (hRn : R ≤ n)
    (P : W → (r : Fin R) → OriginalPacket μ (r.val + 1)) (w : W) :
    (originalFieldCentered_memLp μ P n w).toLp (originalFieldCentered μ P n w) =
      centeredLiftSeries μ n (fun r => packetInRawSpace μ ((P w r).toPacket μ)) := by
  rw [← packetFieldCentered_toLp_eq_series μ hRn (fun w r => (P w r).toPacket μ) w]
  apply Lp.ext
  exact (originalFieldCentered_memLp μ P n w).coeFn_toLp.trans
    ((originalFieldCentered_ae μ P n w).symm.trans
      (packetFieldCentered_memLp μ (fun w r => (P w r).toPacket μ) n w).coeFn_toLp.symm)

variable (M : Measure W) [IsFiniteMeasure M]

theorem originalFieldRaw_subspace_measurable {R : ℕ}
    (P : W → (r : Fin R) → OriginalPacket μ (r.val + 1))
    (hm : ∀ r, Measurable (Function.uncurry (originalFieldRaw μ P r))) (r : Fin R) :
    AEStronglyMeasurable (fun w => packetInRawSpace μ ((P w r).toPacket μ)) M := by
  apply (Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).mp
  have h := rawKernelSection_aestronglyMeasurable (SampleLaw μ (r.val + 1)) M
    (originalFieldRaw μ P r) (hm r) (fun w => (P w r).raw_memLp μ)
  exact h.congr (Filter.Eventually.of_forall (fun w => (P w r).rawLp_eq μ))

theorem originalFieldCentered_norm_bound {R n : ℕ} (hRn : R ≤ n)
    (P : W → (r : Fin R) → OriginalPacket μ (r.val + 1))
    (C : Fin R → ℝ) (hbound : ∀ r w, ‖(P w r).rawLp μ‖ ≤ C r) (w : W) :
    ‖(originalFieldCentered_memLp μ P n w).toLp (originalFieldCentered μ P n w)‖ ≤
      packetFieldCenteredBound n C := by
  rw [originalFieldCentered_toLp_eq μ hRn]
  rw [← packetFieldCentered_toLp_eq_series μ hRn (fun w r => (P w r).toPacket μ) w]
  exact packetFieldCentered_norm_bound μ hRn _ C
    (fun r w => by simpa only [OriginalPacket.rawLp_eq] using hbound r w) w

theorem originalField_weighted_centered_integral_norm_sq {R n : ℕ} (hRn : R ≤ n)
    (P : W → (r : Fin R) → OriginalPacket μ (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hmZ : Measurable (Function.uncurry (originalFieldCentered μ P n)))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖(P w r).rawLp μ‖ ≤ C r) :
    (∫ o, (∫ w, ν w * originalFieldCentered μ P n w o ∂M) ^ 2 ∂SampleLaw μ n) =
      ‖∫ w, ν w • centeredLiftSeries μ n
        (fun r => packetInRawSpace μ ((P w r).toPacket μ)) ∂M‖ ^ 2 := by
  have hb := originalFieldCentered_norm_bound μ hRn P C hbound
  have hf := weightedRawKernel_memLp M (SampleLaw μ n) ν hν (originalFieldCentered μ P n)
    hmZ (originalFieldCentered_memLp μ P n) (packetFieldCenteredBound n C)
    (packetFieldCenteredBound_nonneg n C hC) hb
  change (∫ o, weightedRawKernel M ν (originalFieldCentered μ P n) o ^ 2 ∂SampleLaw μ n) = _
  rw [← LocalizationL2.toLp_norm_sq_eq_integral_sq hf,
    weightedRawKernel_toLp_eq_integral M (SampleLaw μ n) ν hν (originalFieldCentered μ P n)
      hmZ (originalFieldCentered_memLp μ P n) (packetFieldCenteredBound n C)
      (packetFieldCenteredBound_nonneg n C hC) hb]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w =>
    congrArg (fun z => ν w • z) (originalFieldCentered_toLp_eq μ hRn P w))

theorem originalField_weighted_raw_integral_norm_sq {R : ℕ}
    (P : W → (r : Fin R) → OriginalPacket μ (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hm : ∀ r, Measurable (Function.uncurry (originalFieldRaw μ P r)))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖(P w r).rawLp μ‖ ≤ C r) (r : Fin R) :
    (∫ o, (∫ w, ν w * originalFieldRaw μ P r w o ∂M) ^ 2 ∂SampleLaw μ (r.val + 1)) =
      ‖∫ w, ν w • packetInRawSpace μ ((P w r).toPacket μ) ∂M‖ ^ 2 := by
  have hb : ∀ w, ‖packetInRawSpace μ ((P w r).toPacket μ)‖ ≤ C r := by
    intro w
    change ‖packetRawLp μ ((P w r).toPacket μ)‖ ≤ C r
    simpa only [OriginalPacket.rawLp_eq] using hbound r w
  have hi : Integrable (fun w => ν w • packetInRawSpace μ ((P w r).toPacket μ)) M :=
    (LocalizationL2.weighted_field_memLp_two ν hν _
      (originalFieldRaw_subspace_measurable μ M P hm r) (C r) (hC r)
      (Filter.Eventually.of_forall hb)).integrable (by norm_num)
  have he := (rawKernelSpace μ (r.val + 1)).subtypeL.integral_comp_comm hi
  have hf := weightedRawKernel_memLp M (SampleLaw μ (r.val + 1)) ν hν
    (originalFieldRaw μ P r) (hm r) (fun w => (P w r).raw_memLp μ) (C r) (hC r) (hbound r)
  change (∫ o, weightedRawKernel M ν (originalFieldRaw μ P r) o ^ 2
    ∂SampleLaw μ (r.val + 1)) = _
  rw [← LocalizationL2.toLp_norm_sq_eq_integral_sq hf,
    weightedRawKernel_toLp_eq_integral M (SampleLaw μ (r.val + 1)) ν hν
      (originalFieldRaw μ P r) (hm r) (fun w => (P w r).raw_memLp μ) (C r) (hC r) (hbound r)]
  have he' : (∫ w, ν w • (P w r).rawLp μ ∂M) =
      (((∫ w, ν w • packetInRawSpace μ ((P w r).toPacket μ) ∂M) :
        rawKernelSpace μ (r.val + 1)) : Lp ℝ 2 (SampleLaw μ (r.val + 1))) := by
    change (∫ w, ν w • (P w r).rawLp μ ∂M) =
      (rawKernelSpace μ (r.val + 1)).subtypeL
        (∫ w, ν w • packetInRawSpace μ ((P w r).toPacket μ) ∂M)
    rw [← he]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun w =>
      congrArg (fun z => ν w • z) ((P w r).rawLp_eq μ))
  exact congrArg (fun z : Lp ℝ 2 (SampleLaw μ (r.val + 1)) => ‖z‖ ^ 2) he'

/-- U6's first inequality for the actual original scalar fields, permitting
arbitrary point-dependent finite features. No coefficient integrability or
measurability of canonical Lp representatives is a premise. -/
theorem originalField_integrated_centered_energy_le_raw {R n : ℕ} (hRn : R ≤ n)
    (P : W → (r : Fin R) → OriginalPacket μ (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hm : ∀ r, Measurable (Function.uncurry (originalFieldRaw μ P r)))
    (hmZ : Measurable (Function.uncurry (originalFieldCentered μ P n)))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖(P w r).rawLp μ‖ ≤ C r)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    (∫ o, (∫ w, ν w * originalFieldCentered μ P n w o ∂M) ^ 2 ∂SampleLaw μ n) ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
        (∫ o, (∫ w, ν w * originalFieldRaw μ P r w o ∂M) ^ 2
          ∂SampleLaw μ (r.val + 1)) := by
  rw [originalField_weighted_centered_integral_norm_sq μ M hRn P ν hν hmZ C hC hbound]
  simp_rw [originalField_weighted_raw_integral_norm_sq μ M P ν hν hm C hC hbound]
  exact integrated_centeredLiftSeries_norm_sq_le μ M hRn
    (fun r w => packetInRawSpace μ ((P w r).toPacket μ)) ν hν
    (originalFieldRaw_subspace_measurable μ M P hm) C hC
    (fun r => Filter.Eventually.of_forall (fun w => by
      change ‖packetRawLp μ ((P w r).toPacket μ)‖ ≤ C r
      simpa only [OriginalPacket.rawLp_eq] using hbound r w)) Λ hΛ hΛn

/-- The localized U6 inequality with true original raw support separation. -/
theorem originalField_integrated_centered_energy_localized {R n q : ℕ} (hRn : R ≤ n)
    (P : W → (r : Fin R) → OriginalPacket μ (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hm : ∀ r, Measurable (Function.uncurry (originalFieldRaw μ P r)))
    (hmZ : Measurable (Function.uncurry (originalFieldCentered μ P n)))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖(P w r).rawLp μ‖ ≤ C r)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1)
    (b : W → Fin q) (hb : Measurable b)
    (hdisjoint : ∀ r w v, b w ≠ b v → ∀ᵐ o ∂SampleLaw μ (r.val + 1),
      originalFieldRaw μ P r w o * originalFieldRaw μ P r v o = 0)
    (L : ℝ) (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    (∫ o, (∫ w, ν w * originalFieldCentered μ P n w o ∂M) ^ 2 ∂SampleLaw μ n) ≤
      L * ∫ w, ν w ^ 2 * ∑ r : Fin R,
        (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
          (∫ o, originalFieldRaw μ P r w o ^ 2 ∂SampleLaw μ (r.val + 1)) ∂M := by
  rw [originalField_weighted_centered_integral_norm_sq μ M hRn P ν hν hmZ C hC hbound]
  have horth : ∀ r w v, b w ≠ b v →
      inner ℝ (packetInRawSpace μ ((P w r).toPacket μ))
        (packetInRawSpace μ ((P v r).toPacket μ)) = 0 := by
    intro r w v hwv
    change inner ℝ (packetRawLp μ ((P w r).toPacket μ))
      (packetRawLp μ ((P v r).toPacket μ)) = 0
    rw [← OriginalPacket.rawLp_eq, ← OriginalPacket.rawLp_eq]
    exact LocalizationL2.toLp_inner_eq_zero_of_disjoint
      ((P w r).raw_memLp μ) ((P v r).raw_memLp μ) (hdisjoint r w v hwv)
  have h := integrated_centeredLiftSeries_localized μ M hRn
    (fun r w => packetInRawSpace μ ((P w r).toPacket μ)) ν hν
    (originalFieldRaw_subspace_measurable μ M P hm) C hC
    (fun r => Filter.Eventually.of_forall (fun w => by
      change ‖packetRawLp μ ((P w r).toPacket μ)‖ ≤ C r
      simpa only [OriginalPacket.rawLp_eq] using hbound r w)) Λ hΛ hΛn b hb horth L hL
  have hnorm (r : Fin R) (w : W) : ‖packetInRawSpace μ ((P w r).toPacket μ)‖ ^ 2 =
      ∫ o, originalFieldRaw μ P r w o ^ 2 ∂SampleLaw μ (r.val + 1) := by
    change ‖packetRawLp μ ((P w r).toPacket μ)‖ ^ 2 = _
    rw [← OriginalPacket.rawLp_eq]
    exact LocalizationL2.toLp_norm_sq_eq_integral_sq ((P w r).raw_memLp μ)
  simpa only [hnorm] using h

end NearlyMinimax.RawLiftHilbert
