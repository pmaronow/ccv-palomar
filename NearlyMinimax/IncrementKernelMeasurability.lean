module

public import NearlyMinimax.IncrementPilotKernels
public import NearlyMinimax.IncrementCoordinateBounds


@[expose] public section

/-! Joint Borel derivative coefficient fields for actual dyadic pilots. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

instance finiteInputMultilinearMeasurableSpace {p k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    MeasurableSpace (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) F) := borel _

instance finiteInputMultilinearBorelSpace {p k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    BorelSpace (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) F) := ⟨rfl⟩

instance finiteInputScalarMultilinearFiniteDimensional (p k : ℕ) :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ) := by
  let e : (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ) →L[ℝ]
      ((Fin k → Fin p) → ℝ) := ContinuousLinearMap.pi (fun σ =>
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin p → ℝ) ℝ
      (fun i => Pi.single (σ i) 1))
  apply FiniteDimensional.of_injective e.toLinearMap
  intro H G he
  ext v
  change H.toMultilinearMap v = G.toMultilinearMap v
  rw [LiftL2.multilinear_coordinate_expansion H.toMultilinearMap,
    LiftL2.multilinear_coordinate_expansion G.toMultilinearMap]
  apply Finset.sum_congr rfl
  intro σ _
  have hc := congrFun he σ
  change H (fun i => Pi.single (σ i) 1) = G (fun i => Pi.single (σ i) 1) at hc
  exact congrArg (fun a => a * ∏ i, v i (σ i)) hc

theorem rowFunctional_continuous {r : ℕ} : Continuous (rowFunctional (r := r)) := by
  unfold rowFunctional
  exact continuous_finset_sum Finset.univ (fun i _ => (continuous_apply i).smul continuous_const)

theorem continuous_row_postcompose {p r k : ℕ} :
    Continuous (fun z : (Fin r → ℝ) ×
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) (Fin r → ℝ) =>
        (rowFunctional z.1).compContinuousMultilinearMap z.2) := by
  change Continuous (fun z : (Fin r → ℝ) ×
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) (Fin r → ℝ) =>
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => Fin p → ℝ)
      (Fin r → ℝ) ℝ (rowFunctional z.1)) z.2)
  exact ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => Fin p → ℝ)
    (Fin r → ℝ) ℝ).continuous.comp (rowFunctional_continuous.comp continuous_fst)).clm_apply continuous_snd

theorem continuous_multilinear_pullback {p q k : ℕ} :
    Continuous (fun z :
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ ×
        ((Fin q → ℝ) →L[ℝ] (Fin p → ℝ)) =>
        z.1.compContinuousLinearMap (fun _ => z.2)) := by
  change Continuous (fun z :
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ ×
        ((Fin q → ℝ) →L[ℝ] (Fin p → ℝ)) =>
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin k => Fin q → ℝ) (fun _ : Fin k => Fin p → ℝ) ℝ (fun _ => z.2)) z.1)
  exact ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin k => Fin q → ℝ) (fun _ : Fin k => Fin p → ℝ) ℝ).cont.comp
    (continuous_pi (fun _ => continuous_snd))).clm_apply continuous_fst

/-- The anchor and arbitrary measurable physical row determine a Borel
global derivative field under the original admissible population law. -/
theorem dyadicIncrementKernel_field_measurable {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (j : ℕ) (y : ℝ) (m k : ℕ)
    (row : Covariate d × Covariate d → Fin (anchoredDimension d C.order) → ℝ)
    (hrow : Measurable row) :
    Measurable (fun w : Covariate d × Covariate d =>
      dyadicIncrementKernel C θ j w.1 y m (row w) k) := by
  have hm : Measurable (fun w : Covariate d × Covariate d =>
      dyadicIncrementRawMean (ℓ := C.order) θ j w.1) :=
    (dyadicIncrementRawMean_measurable (ℓ := C.order) C θ hθ j).comp measurable_fst
  have hD := ((incrementFinVector_contDiff (anchoredDimension d C.order)
    C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m).continuous_iteratedFDeriv
      (show (k : WithTop ℕ∞) ≤ ⊤ from le_top)).measurable.comp hm
  have hscalar := continuous_row_postcompose.measurable.comp (hrow.prodMk hD)
  change Measurable (fun w : Covariate d × Covariate d =>
    (rowFunctional (row w)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ k (incrementFinVector (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m)
        (dyadicIncrementRawMean θ j w.1))) at hscalar
  have heq : (fun w : Covariate d × Covariate d =>
      (rowFunctional (row w)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (incrementFinVector (anchoredDimension d C.order)
          C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m)
          (dyadicIncrementRawMean θ j w.1))) =
      (fun w => iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m (row w))
        (dyadicIncrementRawMean θ j w.1)) := by
    funext w
    ext v
    exact (incrementFinScalar_iteratedFDeriv _ _ _ _ _ _ _ _ _ _).symm
  rw [heq] at hscalar
  exact continuous_multilinear_pullback.measurable.comp
    (hscalar.prodMk ((incrementPilotCoordinate_measurable (ℓ := C.order) j).comp measurable_fst))

/-- A finite level has a genuine bounded coefficient field on every
bounded-row, cube-supported parameter measure. This cap is used only to
justify Bochner integration; the sharper raw-energy estimate is separate. -/
theorem dyadicIncrementKernel_field_norm_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (j : ℕ) (y : ℝ) (hy : |y| ≤ C.holderBound) (m k : ℕ)
    (row : Covariate d × Covariate d → Fin (anchoredDimension d C.order) → ℝ)
    (M : Measure (Covariate d × Covariate d)) (R : ℝ) (hR : 0 ≤ R)
    (hcube : ∀ᵐ w ∂M, w.1 ∈ unitCube d)
    (hrow : ∀ᵐ w ∂M, (∑ i, |row w i|) ≤ R) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ w ∂M, ‖dyadicIncrementKernel C θ j w.1 y m (row w) k‖ ≤ B := by
  obtain ⟨D, A, hD, hA, hder⟩ := admissible_dyadic_increment_all_derivative_bound C
  obtain ⟨L, hL, hmap⟩ := incrementPilotCoordinate_uniform_bound (d := d) (ℓ := C.order) j
  let B := R * D * (k.factorial : ℝ) * A ^ k * L ^ k
  refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hcube, hrow] with w hw hr
  apply le_trans _ (le_max_right _ _)
  unfold dyadicIncrementKernel
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hlprod : (∏ _i : Fin k, ‖incrementPilotCoordinate (ℓ := C.order) j w.1‖) ≤ L ^ k := by
    exact (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hmap _ hw)).trans_eq (by simp)
  have hd : ‖iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m (row w))
      (dyadicIncrementRawMean θ j w.1)‖ ≤ R * D * (k.factorial : ℝ) * A ^ k := by
    apply (hder θ hθ j w.1 hw y hy m k (row w)).trans
    gcongr
  exact mul_le_mul hd hlprod (Finset.prod_nonneg (fun i _ => norm_nonneg _)) (by positivity)

theorem dyadicIncrementKernel_weighted_integrable {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (j : ℕ) (y : ℝ) (hy : |y| ≤ C.holderBound) (m k : ℕ)
    (row : Covariate d × Covariate d → Fin (anchoredDimension d C.order) → ℝ)
    (hrowMeas : Measurable row) (M : Measure (Covariate d × Covariate d)) [IsFiniteMeasure M]
    (R : ℝ) (hR : 0 ≤ R) (hcube : ∀ᵐ w ∂M, w.1 ∈ unitCube d)
    (hrow : ∀ᵐ w ∂M, (∑ i, |row w i|) ≤ R) (ν : Covariate d × Covariate d → ℝ)
    (hν : MemLp ν 2 M) :
    Integrable (fun w => ν w • dyadicIncrementKernel C θ j w.1 y m (row w) k) M := by
  obtain ⟨B, _, hcap⟩ := dyadicIncrementKernel_field_norm_bound C θ hθ j y hy m k row M R hR hcube hrow
  exact (hν.integrable (by norm_num)).smul_bdd B
    (dyadicIncrementKernel_field_measurable C θ hθ j y m k row hrowMeas).aestronglyMeasurable hcap

end NearlyMinimax
