module

public import NearlyMinimax.PilotCommonBounds
public import NearlyMinimax.PopulationPilotCoefficients
public import NearlyMinimax.TwoScalarPilotVector


@[expose] public section

/-! The actual coefficient estimator is Borel and independent of the
unknown regression, density, and variance. Its exact population-plus-noise
decomposition is proved by polynomial algebra. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def polynomialLiftLinearMap {Ω : Type*} {n p : ℕ}
    (X : Fin n → Ω → Fin p → ℝ) (z : Ω) : MvPolynomial (Fin p) ℝ →ₗ[ℝ] ℝ where
  toFun P := Finsupp.linearCombination ℝ (fun α =>
    RoughRegime.Upper.monomialLift (RoughRegime.Upper.exponentCoordinates α) X z) P.coeff
  map_add' P Q := by simp only [AddMonoidAlgebra.coeff_add, map_add]
  map_smul' a P := by simp only [AddMonoidAlgebra.coeff_smul, map_smul, RingHom.id_apply]

theorem polynomialLiftLinearMap_apply {Ω : Type*} {n p : ℕ}
    (X : Fin n → Ω → Fin p → ℝ) (z : Ω) (P : MvPolynomial (Fin p) ℝ) :
    polynomialLiftLinearMap X z P = RoughRegime.Upper.polynomialLift P X z := by
  simp only [polynomialLiftLinearMap, Finsupp.linearCombination_apply, Finsupp.sum,
    smul_eq_mul, RoughRegime.Upper.polynomialLift, MvPolynomial.finsupp_support_eq_support]
  rfl

theorem polynomialLift_joint_measurable {Ω : Type*} [MeasurableSpace Ω] {n p : ℕ}
    (P : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    Measurable (RoughRegime.Upper.polynomialLift P X) := by
  classical
  unfold RoughRegime.Upper.polynomialLift RoughRegime.Upper.monomialLift
  apply Finset.measurable_sum
  intro α _
  apply Measurable.const_mul
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro e _
  exact Finset.measurable_prod Finset.univ (fun i _ => (hX (e i)).eval)

theorem polynomialLift_parameter_eval {Ω Γ : Type*} {n p : ℕ}
    (P : MvPolynomial (Fin p) ℝ) (X : Fin n → Γ → Ω → Fin p → ℝ) (z : Ω) (w : Γ) :
    RoughRegime.Upper.polynomialLift P (fun i z => X i w z) z =
      RoughRegime.Upper.polynomialLift P (fun (i : Fin n) (t : Ω × Γ) => X i t.2 t.1) (z, w) := rfl

theorem rowIncrementPolynomial_lift {Ω : Type*} {n r : ℕ}
    (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ)
    (row : Fin r → ℝ)
    (X : Fin n → Ω → Fin (Fintype.card (incrementVariables r)) → ℝ) (z : Ω) :
    RoughRegime.Upper.polynomialLift (rowIncrementPolynomial r a b T y m row) X z =
      ∑ i, row i * RoughRegime.Upper.polynomialLift (incrementFinPolynomial r a b T y m i) X z := by
  simp only [← polynomialLiftLinearMap_apply, rowIncrementPolynomial, ← MvPolynomial.smul_eq_C_mul,
    map_sum, map_smul, smul_eq_mul]

attribute [local irreducible] dyadicIncrementRawVector

set_option backward.isDefEq.respectTransparency true in
theorem dyadicPolynomialPilot_raw_joint_measurable {d : ℕ} (C : ModelConstants d)
    (n j : ℕ) (y : ℝ) (m : ℕ)
    (row : Covariate d × Covariate d → Fin (anchoredDimension d C.order) → ℝ)
    (hrow : Measurable row) :
    Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicPolynomialPilot C n j t.2.1 y m (row t.2) t.1) := by
  have hX (i : Fin n) : Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicIncrementRawVector (d := d) (ℓ := C.order) j t.2.1 (t.1 i)) := by
    have hmarg : Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
        (t.2.1, t.1 i)) :=
      ((measurable_fst.comp measurable_snd).prodMk ((measurable_pi_apply i).comp measurable_fst))
    exact (dyadicIncrementRawVector_joint_measurable (d := d) (ℓ := C.order) j).comp hmarg
  let X : Fin n → (Fin n → Observation d) × (Covariate d × Covariate d) →
      Fin (Fintype.card (incrementVariables (anchoredDimension d C.order))) → ℝ :=
    fun i t => dyadicIncrementRawVector (d := d) (ℓ := C.order) j t.2.1 (t.1 i)
  have heq : (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicPolynomialPilot C n j t.2.1 y m (row t.2) t.1) =
      (fun t => ∑ i, row t.2 i * RoughRegime.Upper.polynomialLift
        (incrementFinPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
          (anchoredFinTransport d C.order) y m i) X t) := by
    funext t
    simp only [dyadicPolynomialPilot, rowIncrementPolynomial_lift]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  exact ((hrow.eval (a := i)).comp measurable_snd).mul
    (polynomialLift_joint_measurable (n := n)
      (p := Fintype.card (incrementVariables (anchoredDimension d C.order))) _ X hX)

def dyadicRawPilotSum {d : ℕ} (C : ModelConstants d) (n J : ℕ) (m : ℕ → ℕ)
    (y : ℝ) (z : Fin n → Observation d) (w : Covariate d × Covariate d) : ℝ :=
  ∑ j : Fin (J + 1), dyadicPolynomialPilot C n j.val w.1 y (m j.val)
    (dyadicPilotRow j.val w.1 w.2) z

def dyadicRawCoefficients {d : ℕ} (C : ModelConstants d) (n J : ℕ) (m : ℕ → ℕ)
    (z : Fin n → Observation d) (w : Covariate d × Covariate d) : PairVector :=
  WithLp.toLp 2 ![1, -1 + (dyadicRawPilotSum C n J m 0 z w - dyadicRawPilotSum C n J m 1 z w),
    -dyadicRawPilotSum C n J m 0 z w]

def dyadicNoiseCoefficients {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (n J : ℕ) (m : ℕ → ℕ) (z : Fin n → Observation d) (w : Covariate d × Covariate d) : PairVector :=
  twoScalarPilotVector (dyadicMultilevelErrorField C θ n J 0 m z w)
    (dyadicMultilevelErrorField C θ n J 1 m z w)

theorem dyadicRawPilotSum_joint_measurable {d : ℕ} (C : ModelConstants d)
    (n J : ℕ) (m : ℕ → ℕ) (y : ℝ) :
    Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicRawPilotSum C n J m y t.1 t.2) :=
  Finset.measurable_sum Finset.univ (fun j _ =>
    dyadicPolynomialPilot_raw_joint_measurable C n j.val y (m j.val)
      (fun w => dyadicPilotRow j.val w.1 w.2) (dyadicPilotRow_field_measurable j.val))

theorem dyadicRawCoefficients_joint_measurable {d : ℕ} (C : ModelConstants d)
    (n J : ℕ) (m : ℕ → ℕ) :
    Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicRawCoefficients C n J m t.1 t.2) := by
  have h0 := dyadicRawPilotSum_joint_measurable C n J m 0
  have h1 := dyadicRawPilotSum_joint_measurable C n J m 1
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact measurable_const
  · exact measurable_const.add (h0.sub h1)
  · exact h0.neg

theorem dyadicMultilevelErrorField_eq_raw_sub_population {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (n J : ℕ) (m : ℕ → ℕ) (y : ℝ)
    (z : Fin n → Observation d) (w : Covariate d × Covariate d) :
    dyadicMultilevelErrorField C θ n J y m z w = dyadicRawPilotSum C n J m y z w -
      (dyadicPopulationPilotSum C θ J m false w - y * dyadicPopulationPilotSum C θ J m true w) := by
  unfold dyadicMultilevelErrorField dyadicPilotErrorField dyadicRawPilotSum
  rw [Finset.sum_sub_distrib]
  congr 1
  unfold dyadicPopulationPilotSum
  rw [← Fin.sum_univ_eq_sum_range]
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [incrementFinScalar, incrementFinVector_affine]
  simp only [rowFunctional, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    dyadicPopulationRawPolynomial, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dyadicRawCoefficients_eq_population_add_noise {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (n J : ℕ) (m : ℕ → ℕ)
    (z : Fin n → Observation d) (w : Covariate d × Covariate d) :
    dyadicRawCoefficients C n J m z w = dyadicPopulationCoefficients C θ J m w +
      dyadicNoiseCoefficients C θ n J m z w := by
  ext i
  fin_cases i <;>
    simp [dyadicRawCoefficients, dyadicPopulationCoefficients, dyadicNoiseCoefficients,
      twoScalarPilotVector_coordinates, dyadicMultilevelErrorField_eq_raw_sub_population] <;> ring

end NearlyMinimax
