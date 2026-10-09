module

public import NearlyMinimax.UniformPopulationPairBounds
public import NearlyMinimax.PilotModelEnvelope


@[expose] public section

/-! Genuine all-order inverse-pilot derivative witnesses chosen before every
extension domain, including the actual identity/zero virtual parent at root. -/
noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem pilotModelConstants_withDomain {d : ℕ} (C : ModelConstants d) (U : ExtensionDomain d) :
    pilotModelConstants (C.withDomain U) = (pilotModelConstants C).withDomain U := rfl

/-- A common genuine vector derivative bound at all actual population means. -/
theorem uniform_domain_dyadic_increment_vector_derivative_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (Y : ℝ) (hY : 0 ≤ Y) :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧
      ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ Y → ∀ m k : ℕ,
      ∀ directions : Fin k → Fin (Fintype.card (incrementVariables (anchoredDimension d C.order))) → ℝ,
        ‖iteratedFDeriv ℝ k
          (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) y m)
          (dyadicIncrementRawMean θ j x) directions‖ ≤
          D * (k.factorial : ℝ) * A ^ k * ∏ i, ‖directions i‖ := by
  obtain ⟨W, hW, hmom⟩ := uniform_domain_admissible_dyadicFinPilotMoments_uniform_bound C
  obtain ⟨B, A, hB, hA, hder⟩ := anchored_population_inverse_derivatives
    (d := d) (ℓ := C.order) C.densityLower C.densityUpper W Y C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper) hW.le hY
  refine ⟨B, A, hB, hA, ?_⟩
  intro Udom θ hθ j x hx y hy m k directions
  let q := if j = 0 then (fun _ : Covariate d => (1 : ℝ)) else dyadicNormalizedDensity θ (j - 1) x
  have hqm : Measurable q := by
    by_cases hj : j = 0
    · simpa [q, hj, ModelConstants.withDomain] using (measurable_const : Measurable (fun _ : Covariate d => (1 : ℝ)))
    · simpa [q, hj, ModelConstants.withDomain] using dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ (j - 1) x
  have hqb : ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ q w ∧ q w ≤ C.densityUpper := by
    by_cases hj : j = 0
    · exact Filter.Eventually.of_forall (fun _ => by
        simpa [q, hj, ModelConstants.withDomain] using And.intro C.densityLower_lt_one.le C.one_lt_densityUpper.le)
    · simpa [q, hj, ModelConstants.withDomain] using dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ (j - 1) x
  have hV (t : Bool) : ‖(if j = 0 then (0 : Bool → Fin (anchoredDimension d C.order) → ℝ)
      else dyadicFinPilotMoments θ (j - 1) x) t‖ ≤ W := by
    by_cases hj : j = 0
    · simpa [hj] using hW.le
    · simpa only [hj, ite_false] using hmom Udom θ hθ (j - 1) x hx t
  have hd := hder (dyadicNormalizedAnchor j x) (dyadicNormalizedAnchor (j - 1) x)
    (gridNormalizedAnchor_mem_cube ((2 : ℕ) ^ j) (by positivity) x hx)
    (gridNormalizedAnchor_mem_cube ((2 : ℕ) ^ (j - 1)) (by positivity) x hx)
    (dyadicNormalizedDensity θ j x) q
    (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x) hqm
    (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x) hqb
    (dyadicFinPilotMoments θ j x) (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x)
    (hmom Udom θ hθ j x hx) hV y hy m k directions
  rw [← dyadicIncrementRawMean_eq_with_virtual_parent (C.withDomain Udom) θ hθ j x hx] at hd
  exact hd

/-- Uniform-domain U5(4) after arbitrary scalar feature-row postcomposition.
The constants precede the domain and all polynomial/derivative orders. -/
theorem uniform_domain_admissible_dyadic_increment_all_derivative_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (Y : ℝ) (hY : 0 ≤ Y) :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧
      ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ Y → ∀ m k : ℕ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ,
        ‖iteratedFDeriv ℝ k
          (incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) y m row)
          (dyadicIncrementRawMean θ j x)‖ ≤
          (∑ i, |row i|) * D * (k.factorial : ℝ) * A ^ k := by
  obtain ⟨D, A, hD, hA, hder⟩ := uniform_domain_dyadic_increment_vector_derivative_bound C Y hY
  refine ⟨D, A, hD, hA, ?_⟩
  intro Udom θ hθ j x hx y hy m k row
  have hrow : 0 ≤ ∑ i, |row i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro directions
  rw [incrementFinScalar_iteratedFDeriv]
  calc
    _ ≤ ‖rowFunctional row‖ * ‖iteratedFDeriv ℝ k
        (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
          (anchoredFinTransport d C.order) y m)
        (dyadicIncrementRawMean θ j x) directions‖ := (rowFunctional row).le_opNorm _
    _ ≤ (∑ i, |row i|) * (D * (k.factorial : ℝ) * A ^ k * ∏ i, ‖directions i‖) :=
      mul_le_mul (rowFunctional_norm_le row) (hder Udom θ hθ j x hx y hy m k directions) (norm_nonneg _) hrow
    _ = ((∑ i, |row i|) * D * (k.factorial : ℝ) * A ^ k) * ∏ i, ‖directions i‖ := by ring

end NearlyMinimax
