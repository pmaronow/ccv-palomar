module

public import NearlyMinimax.OriginalRawLiftField


@[expose] public section

/-!
The manuscript U6 measurable-field clause for actual polynomial scalar lifts.
Each field point has its own finite feature dimension, feature map and
polynomial. Only their actual scalar kernels/lifts need joint measurability.
The raw Hilbert-space proof handles degenerate features without assuming
integrability of polynomial derivatives in a coefficient-map norm.
-/
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace NearlyMinimax.RawLiftHilbert
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {O W : Type*} [MeasurableSpace O] [MeasurableSpace W]
  (μ : Measure O) [IsProbabilityMeasure μ]

/-- A field of actual finite-dimensional polynomial lifts; the dimension need
not be uniformly bounded, and the feature map may vary with the field point. -/
structure PolynomialField where
  featureCount : W → ℕ
  feature : (w : W) → O → Fin (featureCount w) → ℝ
  squareIntegrable : ∀ w a, MemLp (fun o => feature w o a) 2 μ
  polynomial : (w : W) → MvPolynomial (Fin (featureCount w)) ℝ

def PolynomialField.mean (F : PolynomialField (W := W) μ) (w : W) :=
  originalFeatureMean μ (F.feature w)

theorem PolynomialField.mean_eq_integral (F : PolynomialField (W := W) μ) (w : W) :
    F.mean μ w = ∫ o, F.feature w o ∂μ :=
  (LiftL2.vector_integral_of_coordinate_moments (F.feature w) (F.mean μ w)
    (F.squareIntegrable w) (fun _ => rfl)).2.symm

def PolynomialField.packet (F : PolynomialField (W := W) μ) (w : W) (k : ℕ) :
    OriginalPacket μ k where
  featureCount := F.featureCount w
  feature := F.feature w
  squareIntegrable := F.squareIntegrable w
  coefficient := iteratedFDeriv ℝ k (fun x => MvPolynomial.eval x (F.polynomial w))
    (F.mean μ w)
  symmetric := fun σ v =>
    (AnalyticOnNhd.eval_mvPolynomial (F.polynomial w)).analyticOn.iteratedFDeriv_comp_perm v σ

/-- The manuscript's raw, uncentered Taylor kernel, evaluated on independent
observations under the genuine product measure. -/
def PolynomialField.rawKernel (F : PolynomialField (W := W) μ) (k : ℕ) :
    W → (Fin k → O) → ℝ := fun w o =>
  iteratedFDeriv ℝ k (fun x => MvPolynomial.eval x (F.polynomial w)) (F.mean μ w)
    (fun i => F.feature w (o i))

/-- The actual scalar polynomial lift minus its expectation. -/
def PolynomialField.centeredLift (F : PolynomialField (W := W) μ) (n : ℕ) :
    W → (Fin n → O) → ℝ := fun w o =>
  RoughRegime.Upper.polynomialLift (F.polynomial w) (fun (j : Fin n) (o : Fin n → O) => F.feature w (o j)) o -
    MvPolynomial.eval (F.mean μ w) (F.polynomial w)

theorem PolynomialField.rawKernel_eq (F : PolynomialField (W := W) μ) (k : ℕ) (w : W) :
    F.rawKernel μ k w = (F.packet μ w k).raw μ := rfl

variable [MeasurableSpace.CountablyGenerated O]

theorem PolynomialField.centeredLift_eq {R n : ℕ}
    (F : PolynomialField (W := W) μ) (hdeg : ∀ w, (F.polynomial w).totalDegree ≤ R)
    (hRn : R ≤ n) :
    F.centeredLift μ n = originalFieldCentered μ
      (fun w (r : Fin R) => F.packet μ w (r.val + 1)) n := by
  funext w o
  have h := LiftL2.polynomialLift_centering_l2 (F.polynomial w)
    (fun (j : Fin n) (o : Fin n → O) => F.feature w (o j)) (F.mean μ w) (hdeg w) hRn
  change RoughRegime.Upper.polynomialLift (F.polynomial w)
      (fun (j : Fin n) (o : Fin n → O) => F.feature w (o j)) o -
      MvPolynomial.eval (F.mean μ w) (F.polynomial w) =
    ∑ r : Fin R, LiftL2.kernelStatistic
      (iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x (F.polynomial w))
        (F.mean μ w)) (fun (j : Fin n) (o : Fin n → O) => F.feature w (o j) - F.mean μ w) o
  rw [h]
  simp only [LiftL2.centeredKernelExpansion]
  ring

theorem PolynomialField.centeredLift_memLp {R n : ℕ}
    (F : PolynomialField (W := W) μ) (hdeg : ∀ w, (F.polynomial w).totalDegree ≤ R)
    (hRn : R ≤ n) (w : W) : MemLp (F.centeredLift μ n w) 2 (SampleLaw μ n) := by
  rw [F.centeredLift_eq μ hdeg hRn]
  exact originalFieldCentered_memLp μ _ n w

theorem PolynomialField.centeredLift_mean_zero {R n : ℕ}
    (F : PolynomialField (W := W) μ) (hdeg : ∀ w, (F.polynomial w).totalDegree ≤ R)
    (hRn : R ≤ n) (w : W) : ∫ o, F.centeredLift μ n w o ∂SampleLaw μ n = 0 := by
  rw [F.centeredLift_eq μ hdeg hRn]
  rw [← integral_congr_ae (originalFieldCentered_ae μ
    (fun w (r : Fin R) => F.packet μ w (r.val + 1)) n w)]
  exact packetFieldCentered_mean_zero μ _ n w

variable (M : Measure W) [IsFiniteMeasure M]

theorem PolynomialField.integrated_centered_memLp {R n : ℕ}
    (F : PolynomialField (W := W) μ) (hdeg : ∀ w, (F.polynomial w).totalDegree ≤ R)
    (hRn : R ≤ n) (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hmZ : Measurable (Function.uncurry (F.centeredLift μ n)))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖(F.packet μ w (r.val + 1)).rawLp μ‖ ≤ C r) :
    MemLp (fun o => ∫ w, ν w * F.centeredLift μ n w o ∂M) 2 (SampleLaw μ n) := by
  rw [F.centeredLift_eq μ hdeg hRn] at hmZ ⊢
  have hb := originalFieldCentered_norm_bound μ hRn
    (fun w (r : Fin R) => F.packet μ w (r.val + 1)) C hbound
  exact weightedRawKernel_memLp M (SampleLaw μ n) ν hν _ hmZ
    (originalFieldCentered_memLp μ _ n) (packetFieldCenteredBound n C)
    (packetFieldCenteredBound_nonneg n C hC) hb

theorem PolynomialField.integrated_centered_mean_zero {R n : ℕ}
    (F : PolynomialField (W := W) μ) (hdeg : ∀ w, (F.polynomial w).totalDegree ≤ R)
    (hRn : R ≤ n) (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hmZ : Measurable (Function.uncurry (F.centeredLift μ n)))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖(F.packet μ w (r.val + 1)).rawLp μ‖ ≤ C r) :
    (∫ o, (∫ w, ν w * F.centeredLift μ n w o ∂M) ∂SampleLaw μ n) = 0 := by
  have hz := F.centeredLift_mean_zero μ hdeg hRn
  rw [F.centeredLift_eq μ hdeg hRn] at hmZ hz ⊢
  have hb := originalFieldCentered_norm_bound μ hRn
    (fun w (r : Fin R) => F.packet μ w (r.val + 1)) C hbound
  exact weightedRawKernel_integral_zero M (SampleLaw μ n) ν hν _ hmZ
    (originalFieldCentered_memLp μ _ n) (packetFieldCenteredBound n C)
    (packetFieldCenteredBound_nonneg n C hC) hb hz

/-- The full U6 first field inequality for actual polynomial lifts. All field
measurability and uniform norm assumptions concern genuine scalar functions. -/
theorem PolynomialField.integrated_centered_energy_le_raw {R n : ℕ}
    (F : PolynomialField (W := W) μ) (hdeg : ∀ w, (F.polynomial w).totalDegree ≤ R)
    (hRn : R ≤ n) (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hm : ∀ r : Fin R, Measurable (Function.uncurry (F.rawKernel μ (r.val + 1))))
    (hmZ : Measurable (Function.uncurry (F.centeredLift μ n)))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖(F.packet μ w (r.val + 1)).rawLp μ‖ ≤ C r)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    (∫ o, (∫ w, ν w * F.centeredLift μ n w o ∂M) ^ 2 ∂SampleLaw μ n) ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
        (∫ o, (∫ w, ν w * F.rawKernel μ (r.val + 1) w o ∂M) ^ 2
          ∂SampleLaw μ (r.val + 1)) := by
  rw [F.centeredLift_eq μ hdeg hRn] at hmZ ⊢
  exact originalField_integrated_centered_energy_le_raw μ M hRn
    (fun w (r : Fin R) => F.packet μ w (r.val + 1)) ν hν hm hmZ C hC hbound Λ hΛ hΛn

/-- The full localized U6 clause: raw support separation across a measurable
block partition yields its actual maximal block mass as the prefactor. -/
theorem PolynomialField.integrated_centered_energy_localized {R n q : ℕ}
    (F : PolynomialField (W := W) μ) (hdeg : ∀ w, (F.polynomial w).totalDegree ≤ R)
    (hRn : R ≤ n) (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hm : ∀ r : Fin R, Measurable (Function.uncurry (F.rawKernel μ (r.val + 1))))
    (hmZ : Measurable (Function.uncurry (F.centeredLift μ n)))
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r w, ‖(F.packet μ w (r.val + 1)).rawLp μ‖ ≤ C r)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1)
    (b : W → Fin q) (hb : Measurable b)
    (hdisjoint : ∀ r : Fin R, ∀ w v, b w ≠ b v →
      ∀ᵐ o ∂SampleLaw μ (r.val + 1),
        F.rawKernel μ (r.val + 1) w o * F.rawKernel μ (r.val + 1) v o = 0)
    (L : ℝ) (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    (∫ o, (∫ w, ν w * F.centeredLift μ n w o ∂M) ^ 2 ∂SampleLaw μ n) ≤
      L * ∫ w, ν w ^ 2 * ∑ r : Fin R,
        (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
          (∫ o, F.rawKernel μ (r.val + 1) w o ^ 2 ∂SampleLaw μ (r.val + 1)) ∂M := by
  rw [F.centeredLift_eq μ hdeg hRn] at hmZ ⊢
  exact originalField_integrated_centered_energy_localized μ M hRn
    (fun w (r : Fin R) => F.packet μ w (r.val + 1)) ν hν hm hmZ C hC hbound
    Λ hΛ hΛn b hb hdisjoint L hL

end NearlyMinimax.RawLiftHilbert
