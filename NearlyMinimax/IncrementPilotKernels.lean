module

public import NearlyMinimax.IncrementPilotCoordinates
public import NearlyMinimax.IncrementPilotLocalization


@[expose] public section

/-! Exact global derivative kernels for the actual unbiased dyadic pilot.
They preserve the actual local raw energies and parent support, and their
centered factorial expansion is exactly the original polynomial pilot error. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def dyadicIncrementKernel {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ)
    (row : Fin (anchoredDimension d C.order) → ℝ) (k : ℕ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin k => Fin (Fintype.card (IncrementGlobalIndex d C.order j)) → ℝ) ℝ :=
  (iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
    C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
      (dyadicIncrementRawMean θ j x)).compContinuousLinearMap
        (fun _ => incrementPilotCoordinate j x)

theorem dyadicIncrementKernel_raw {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ)
    (row : Fin (anchoredDimension d C.order) → ℝ) (k : ℕ) (z : Fin k → Observation d) :
    dyadicIncrementKernel C θ j x y m row k (fun i => incrementGlobalVector j (z i)) =
      iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
        (dyadicIncrementRawMean θ j x) (fun i => dyadicIncrementRawVector j x (z i)) := by
  simp [dyadicIncrementKernel, ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem dyadicIncrementKernel_symmetric {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ)
    (row : Fin (anchoredDimension d C.order) → ℝ) (k : ℕ)
    (σ : Equiv.Perm (Fin k)) (v : Fin k → Fin (Fintype.card (IncrementGlobalIndex d C.order j)) → ℝ) :
    dyadicIncrementKernel C θ j x y m row k (fun i => v (σ i)) =
      dyadicIncrementKernel C θ j x y m row k v := by
  let F := rowIncrementPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m row
  have hF : (fun z => eval z F) = incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row := by
    funext z
    exact rowIncrementPolynomial_eval _ _ _ _ _ _ _ _
  simp only [dyadicIncrementKernel, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [← hF]
  exact (AnalyticOnNhd.eval_mvPolynomial F).analyticOn.iteratedFDeriv_comp_perm
    (fun i => incrementPilotCoordinate j x (v i)) σ

theorem dyadicIncrementKernel_disjoint {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (j k : ℕ) (hk : 0 < k) (x v : Covariate d)
    (hxv : dyadicPilotLabel (j - 1) x ≠ dyadicPilotLabel (j - 1) v)
    (y t : ℝ) (m l : ℕ) (row s : Fin (anchoredDimension d C.order) → ℝ)
    (z : Fin k → Observation d) :
    dyadicIncrementKernel C θ j x y m row k (fun i => incrementGlobalVector j (z i)) *
      dyadicIncrementKernel C θ j v t l s k (fun i => incrementGlobalVector j (z i)) = 0 := by
  rw [dyadicIncrementKernel_raw, dyadicIncrementKernel_raw]
  exact dyadic_increment_raw_kernels_disjoint hk j x v hxv _ _ z

theorem dyadicIncrementKernel_centered {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (y : ℝ) (m : ℕ) (row : Fin (anchoredDimension d C.order) → ℝ) (k : ℕ)
    (z : Fin k → Observation d) :
    dyadicIncrementKernel C θ j x y m row k
      (fun i => incrementGlobalVector j (z i) - incrementGlobalMean θ j) =
      iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
        (dyadicIncrementRawMean θ j x)
        (fun i => dyadicIncrementRawVector j x (z i) - dyadicIncrementRawMean θ j x) := by
  simp [dyadicIncrementKernel, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    map_sub, incrementPilotCoordinate_mean C θ hθ]

/-- Exact translation of the original coefficient pilot to a single fixed
global feature vector, with no covariance or mean premise. -/
theorem dyadicPolynomialPilot_centered_global {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ)
    (row : Fin (anchoredDimension d C.order) → ℝ)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n) (z : Fin n → Observation d) :
    LiftL2.centeredKernelExpansion 0
      (fun r : Fin (m + anchoredDimension d C.order + 1) =>
        dyadicIncrementKernel C θ j x y m row (r.val + 1))
      (fun i z => incrementGlobalVector j (z i) - incrementGlobalMean θ j) z =
      dyadicPolynomialPilot C n j x y m row z -
        incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
          (anchoredFinTransport d C.order) y m row (dyadicIncrementRawMean θ j x) := by
  let F := rowIncrementPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m row
  have hF : (fun z => eval z F) = incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row := by
    funext z
    exact rowIncrementPolynomial_eval _ _ _ _ _ _ _ _
  have he := LiftL2.polynomialLift_centering_l2 F
    (fun i (z : Fin n → Observation d) => dyadicIncrementRawVector j x (z i))
    (dyadicIncrementRawMean θ j x) (rowIncrementPolynomial_degree _ _ _ _ _ _ _) hdegree
  change _ = RoughRegime.Upper.polynomialLift F
    (fun i (z : Fin n → Observation d) => dyadicIncrementRawVector j x (z i)) z - _
  rw [he]
  change _ = eval (dyadicIncrementRawMean θ j x) F + _ - _
  rw [rowIncrementPolynomial_eval, add_sub_cancel_left]
  simp only [LiftL2.centeredKernelExpansion, zero_add]
  apply Finset.sum_congr rfl
  intro r _
  unfold LiftL2.kernelStatistic LiftL2.kernelSum
  apply congrArg (fun a => (((r.val + 1).factorial : ℝ) *
    (n.descFactorial (r.val + 1) : ℝ))⁻¹ * a)
  apply Finset.sum_congr rfl
  intro e _
  rw [hF]
  exact dyadicIncrementKernel_centered C θ hθ j x y m row _ (fun i => z (e i))

/-- The global field kernel keeps the true local `K_j` energy scale. The
global coordinate map's crude norm cap is not used in this stochastic bound. -/
theorem admissible_dyadicIncrementKernel_raw_budget {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧
      ∀ θ : RegressionParameter d, Admissible C θ → ∀ n j : ℕ,
      ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ C.holderBound → ∀ m k : ℕ,
      ∀ row : Fin (anchoredDimension d C.order) → ℝ, ∀ hk : k ≤ n,
      ∀ Λ : ℝ, 0 < Λ →
        (((k.factorial : ℝ) * Λ ^ k)⁻¹) *
          (∫ z : Fin n → Observation d,
            dyadicIncrementKernel C θ j x y m row k
              (fun i => incrementGlobalVector j (z (Fin.castLEEmb hk i))) ^ 2 ∂sampleLaw θ n) ≤
          ((∑ i, |row i|) * D) ^ 2 * (k.factorial : ℝ) *
            (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
              preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ k := by
  obtain ⟨D, A, hD, hA, hder⟩ := admissible_dyadic_increment_all_derivative_bound C
  refine ⟨D, A, hD, hA, ?_⟩
  intro θ hθ n j x hx y hy m k row hk Λ hΛ
  let := sampleLaw_isProbability C θ hθ n
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := dyadicIncrementRawVector_sample_facts C θ hθ j x hx
  let X (i : Fin n) (z : Fin n → Observation d) := dyadicIncrementRawVector (ℓ := C.order) j x (z i)
  let e := Fin.castLEEmb hk
  let E := (Fintype.card (incrementVariables (anchoredDimension d C.order)) : ℝ) *
    preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j
  have hE : 0 ≤ E := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (preconditionedPilotMomentConstant_pos C _).le)
      (dyadicPilotScale_pos _ _).le
  have hrow : 0 ≤ (∑ i, |row i|) * D :=
    mul_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hD.le
  have hb := KernelMomentBounds.factorial_kernel_budget
    (iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row) (dyadicIncrementRawMean θ j x))
    (fun i => X (e i)) (hind.precomp e.injective) (fun i => hmeas (e i))
    (fun i a => hL2 (e i) a) E ((∑ i, |row i|) * D) A Λ hE hrow hA.le hΛ
    (fun i => dyadicIncrementRawVector_sample_second_le C θ hθ j x hx (e i))
    (hder θ hθ j x hx y hy m k row)
  have heq : (fun z : Fin n → Observation d =>
      dyadicIncrementKernel C θ j x y m row k
        (fun i => incrementGlobalVector j (z (Fin.castLEEmb hk i))) ^ 2) =
      (fun z => iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row) (dyadicIncrementRawMean θ j x)
        (fun i => X (e i) z) ^ 2) := by
    funext z
    rw [dyadicIncrementKernel_raw]
  rw [heq]
  exact hb

end NearlyMinimax
