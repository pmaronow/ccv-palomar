module

public import NearlyMinimax.PopulationMomentDerivatives


@[expose] public section

/-! Scalar feature-row derivative bounds for the actual population inverse pilots. -/

noncomputable section
namespace NearlyMinimax
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

def rowFunctional {r : ℕ} (row : Fin r → ℝ) : (Fin r → ℝ) →L[ℝ] ℝ :=
  ∑ i, row i • (ContinuousLinearMap.proj i : (Fin r → ℝ) →L[ℝ] ℝ)

@[simp] theorem rowFunctional_apply {r : ℕ} (row z : Fin r → ℝ) :
    rowFunctional row z = row ⬝ᵥ z := by
  simp [rowFunctional, dotProduct, ContinuousLinearMap.sum_apply, smul_eq_mul]

theorem rowFunctional_norm_le {r : ℕ} (row : Fin r → ℝ) :
    ‖rowFunctional row‖ ≤ ∑ i, |row i| := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  intro z
  rw [rowFunctional_apply, dotProduct]
  calc
    ‖∑ i, row i * z i‖ ≤ ∑ i, ‖row i * z i‖ := norm_sum_le _ _
    _ ≤ ∑ i, |row i| * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (abs_nonneg _)
    _ = (∑ i, |row i|) * ‖z‖ := by rw [Finset.sum_mul]

def incrementFinScalar (r : ℕ) (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (row : Fin r → ℝ) :
    (Fin (Fintype.card (incrementVariables r)) → ℝ) → ℝ :=
  fun x => row ⬝ᵥ incrementFinVector r lo hi T y m x

theorem incrementFinScalar_iteratedFDeriv (r : ℕ) [NeZero r] (lo hi : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m k : ℕ) (row : Fin r → ℝ)
    (x : Fin (Fintype.card (incrementVariables r)) → ℝ)
    (v : Fin k → Fin (Fintype.card (incrementVariables r)) → ℝ) :
    iteratedFDeriv ℝ k (incrementFinScalar r lo hi T y m row) x v =
      rowFunctional row (iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m) x v) := by
  have h := (rowFunctional row).iteratedFDeriv_comp_left (x := x)
    (incrementFinVector_contDiff r lo hi T y m).contDiffAt (show (k : WithTop ℕ∞) ≤ ⊤ from le_top)
  have hFun : (rowFunctional row) ∘ incrementFinVector r lo hi T y m =
      incrementFinScalar r lo hi T y m row := by
    funext z
    exact rowFunctional_apply row _
  rw [hFun] at h
  have he := congrArg (fun D => D v) h
  change iteratedFDeriv ℝ k (incrementFinScalar r lo hi T y m row) x v =
    rowFunctional row (iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m) x v) at he
  exact he

theorem incrementFinScalar_iteratedFDeriv_norm_le (r : ℕ) [NeZero r] (lo hi : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m k : ℕ) (row : Fin r → ℝ)
    (x : Fin (Fintype.card (incrementVariables r)) → ℝ)
    (v : Fin k → Fin (Fintype.card (incrementVariables r)) → ℝ) :
    ‖iteratedFDeriv ℝ k (incrementFinScalar r lo hi T y m row) x v‖ ≤
      (∑ i, |row i|) * ‖iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m) x v‖ := by
  rw [incrementFinScalar_iteratedFDeriv]
  exact ((rowFunctional row).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (rowFunctional_norm_le row) (norm_nonneg _))

/-- Passing to a scalar row and to the genuine derivative operator norm costs
only a fixed finite row factor. Constants still do not depend on polynomial
degree, derivative order, anchor, density, response, or the moment center. -/
theorem anchored_actual_population_row_derivative_operator_bound {d ℓ : ℕ}
    [Nonempty (AnchoredIndex d ℓ)] (a b F Y : ℝ)
    (ha : 0 < a) (hab : a < b) (hF : 0 ≤ F) (hY : 0 ≤ Y) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ u v : Covariate d, u ∈ unitCube d → v ∈ unitCube d →
      ∀ p q f g : Covariate d → ℝ, Measurable p → Measurable q →
      (∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) →
      (∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b) →
      (∀ w ∈ unitCube d, |f w| ≤ F) → (∀ w ∈ unitCube d, |g w| ≤ F) →
      ∀ y : ℝ, |y| ≤ Y → ∀ m k : ℕ,
      ∀ row : Fin (anchoredDimension d ℓ) → ℝ,
        ‖iteratedFDeriv ℝ k
          (incrementFinScalar (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) y m row)
          (fun j => incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q)
            (anchoredFinMomentFamilies u p f) (anchoredFinMomentFamilies v q g)
            ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm j))‖ ≤
          (∑ i, |row i|) * C * (k.factorial : ℝ) * A ^ k := by
  obtain ⟨C, A, hC, hA, hDer⟩ := anchored_actual_population_inverse_derivatives
    (d := d) (ℓ := ℓ) a b F Y ha hab hF hY
  refine ⟨C, A, hC, hA, ?_⟩
  intro u v hu hv p q f g hpmeas hqmeas hp hq hf hg y hy m k row
  have hRow : 0 ≤ ∑ i, |row i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro directions
  rw [incrementFinScalar_iteratedFDeriv]
  calc
    _ ≤ ‖rowFunctional row‖ * ‖iteratedFDeriv ℝ k
        (incrementFinVector (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) y m)
        (fun j => incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q)
          (anchoredFinMomentFamilies u p f) (anchoredFinMomentFamilies v q g)
          ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm j)) directions‖ :=
      (rowFunctional row).le_opNorm _
    _ ≤ (∑ i, |row i|) * (C * (k.factorial : ℝ) * A ^ k * ∏ j, ‖directions j‖) := by
      apply mul_le_mul (rowFunctional_norm_le row)
        (hDer u v hu hv p q f g hpmeas hqmeas hp hq hf hg y hy m k directions)
        (norm_nonneg _) hRow
    _ = ((∑ i, |row i|) * C * (k.factorial : ℝ) * A ^ k) * ∏ j, ‖directions j‖ := by ring

end NearlyMinimax
