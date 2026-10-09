module

public import NearlyMinimax.PolynomialLiftField


@[expose] public section

/-! The middle-to-final inequality in U6's displayed chain, for original
jointly Borel scalar raw kernels of a varying-feature polynomial field. -/
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace NearlyMinimax.RawLiftHilbert
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {O W : Type*} [MeasurableSpace O] [MeasurableSpace W]
  [MeasurableSpace.CountablyGenerated O]
  (μ : Measure O) [IsProbabilityMeasure μ] (M : Measure W) [IsFiniteMeasure M]

/-- The actual raw-energy sum itself satisfies block localization. This
completes the middle-to-final step of the literal U6 inequality chain. -/
theorem PolynomialField.integrated_raw_energy_localized {R q : ℕ}
    (F : PolynomialField (W := W) μ) (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hm : ∀ r : Fin R, Measurable (Function.uncurry (F.rawKernel μ (r.val + 1))))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖(F.packet μ w (r.val + 1)).rawLp μ‖ ≤ C r)
    (Λ : ℝ) (hΛ : 0 < Λ)
    (b : W → Fin q) (hb : Measurable b)
    (hdisjoint : ∀ r : Fin R, ∀ w v, b w ≠ b v →
      ∀ᵐ o ∂SampleLaw μ (r.val + 1),
        F.rawKernel μ (r.val + 1) w o * F.rawKernel μ (r.val + 1) v o = 0)
    (L : ℝ) (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    (∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
      (∫ o, (∫ w, ν w * F.rawKernel μ (r.val + 1) w o ∂M) ^ 2
        ∂SampleLaw μ (r.val + 1))) ≤
      L * ∫ w, ν w ^ 2 * ∑ r : Fin R,
        (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
          (∫ o, F.rawKernel μ (r.val + 1) w o ^ 2 ∂SampleLaw μ (r.val + 1)) ∂M := by
  let P := fun w (r : Fin R) => F.packet μ w (r.val + 1)
  have hr (r : Fin R) :
      (∫ o, (∫ w, ν w * F.rawKernel μ (r.val + 1) w o ∂M) ^ 2
        ∂SampleLaw μ (r.val + 1)) =
      ‖∫ w, ν w • packetInRawSpace μ ((P w r).toPacket μ) ∂M‖ ^ 2 :=
    originalField_weighted_raw_integral_norm_sq μ M P ν hν hm C hC hbound r
  simp_rw [hr]
  have horth : ∀ r w v, b w ≠ b v →
      inner ℝ (packetInRawSpace μ ((P w r).toPacket μ))
        (packetInRawSpace μ ((P v r).toPacket μ)) = 0 := by
    intro r w v hwv
    change inner ℝ (packetRawLp μ ((P w r).toPacket μ))
      (packetRawLp μ ((P v r).toPacket μ)) = 0
    rw [← OriginalPacket.rawLp_eq, ← OriginalPacket.rawLp_eq]
    exact LocalizationL2.toLp_inner_eq_zero_of_disjoint
      ((P w r).raw_memLp μ) ((P v r).raw_memLp μ) (hdisjoint r w v hwv)
  have h := LocalizationL2.weighted_kernel_series_localization_bound b hb ν hν
    (fun r w => packetInRawSpace μ ((P w r).toPacket μ))
    (originalFieldRaw_subspace_measurable μ M P hm) C hC
    (fun r => Filter.Eventually.of_forall (fun w => by
      change ‖packetRawLp μ ((P w r).toPacket μ)‖ ≤ C r
      simpa only [OriginalPacket.rawLp_eq] using hbound r w)) horth
    (fun r => (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹)
    (fun _ => by positivity) L hL
  have hnorm (r : Fin R) (w : W) : ‖packetInRawSpace μ ((P w r).toPacket μ)‖ ^ 2 =
      ∫ o, F.rawKernel μ (r.val + 1) w o ^ 2 ∂SampleLaw μ (r.val + 1) := by
    change ‖packetRawLp μ ((P w r).toPacket μ)‖ ^ 2 = _
    rw [← OriginalPacket.rawLp_eq]
    exact LocalizationL2.toLp_norm_sq_eq_integral_sq ((P w r).raw_memLp μ)
  simpa only [hnorm] using h

end NearlyMinimax.RawLiftHilbert
