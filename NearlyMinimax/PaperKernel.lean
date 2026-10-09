module

public import NearlyMinimax.PaperInverse


@[expose] public section

/-! The Chebyshev coefficients used in `PaperInverse` satisfy the precise
formal rational generating identity from `upper_B.tex`, over a free polynomial
variable and hence after matrix evaluation. -/

noncomputable section
namespace NearlyMinimax
open Polynomial
open RoughRegime.Upper RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant
open scoped BigOperators

/-- Formal Chebyshev reciprocal-kernel coefficient, with constant term one. -/
def formalKernelCoefficient (ρ : ℝ) (U : ℝ[X]) (k : ℕ) : ℝ[X] :=
  C (if k = 0 then 1 else 2 * (-ρ) ^ k) * (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp U

/-- The formal reciprocal kernel before any scalar or matrix evaluation. -/
def formalReciprocalKernel (ρ : ℝ) (U : ℝ[X]) : PowerSeries ℝ[X] :=
  PowerSeries.mk (formalKernelCoefficient ρ U)

private theorem chebyshev_comp_recurrence (U : ℝ[X]) (k : ℕ) :
    (Polynomial.Chebyshev.T ℝ ((k + 2 : ℕ) : ℤ)).comp U =
      2 * U * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).comp U -
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp U := by
  have h := congrArg (Polynomial.compRingHom U) (Polynomial.Chebyshev.T_add_two ℝ (k : ℤ))
  simpa using h

private theorem formalKernelCoefficient_recurrence (ρ : ℝ) (U : ℝ[X]) (k : ℕ) :
    formalKernelCoefficient ρ U (k + 3) +
      C (2 * ρ) * U * formalKernelCoefficient ρ U (k + 2) +
      C (ρ ^ 2) * formalKernelCoefficient ρ U (k + 1) = 0 := by
  simp only [formalKernelCoefficient, show k + 3 ≠ 0 by omega,
    show k + 2 ≠ 0 by omega, show k + 1 ≠ 0 by omega,
    ↓reduceIte]
  have hT := chebyshev_comp_recurrence U (k + 1)
  have he : k + 1 + 2 = k + 3 := by omega
  have he1 : k + 1 + 1 = k + 2 := by omega
  rw [he, he1] at hT
  rw [hT]
  simp only [pow_succ, map_mul, map_neg, map_ofNat, map_one, map_pow]
  ring

/-- The kernel satisfies the exact denominator identity underlying `g_ζ`.
This proves the coefficient construction algebraically, independent of convergence. -/
theorem formalReciprocalKernel_identity (ρ : ℝ) (U : ℝ[X]) :
    (1 + PowerSeries.C (C (2 * ρ) * U) * PowerSeries.X +
      PowerSeries.C (C (ρ ^ 2)) * PowerSeries.X ^ 2) * formalReciprocalKernel ρ U =
        1 - PowerSeries.C (C (ρ ^ 2)) * PowerSeries.X ^ 2 := by
  have hlinear (k : ℕ) :
      PowerSeries.coeff k (PowerSeries.X * formalReciprocalKernel ρ U) =
        if 1 ≤ k then PowerSeries.coeff (k - 1) (formalReciprocalKernel ρ U) else 0 := by
    simpa only [pow_one] using PowerSeries.coeff_X_pow_mul' (formalReciprocalKernel ρ U) 1 k
  apply PowerSeries.ext
  intro k
  rw [add_mul, add_mul, one_mul]
  simp only [map_add, map_sub, mul_assoc, PowerSeries.coeff_C_mul, hlinear,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one, PowerSeries.coeff_X_pow,
    ]
  simp only [formalReciprocalKernel, PowerSeries.coeff_mk]
  rcases k with _ | _ | _ | k
  · simp [formalKernelCoefficient]
  · simp [formalKernelCoefficient]
  · simp [formalKernelCoefficient, Polynomial.Chebyshev.T_two, map_ofNat]
    ring
  · have h1 : 1 ≤ k + 3 := by omega
    have h2 : 2 ≤ k + 3 := by omega
    have hne0 : k + 3 ≠ 0 := by omega
    have hne2 : k + 3 ≠ 2 := by omega
    change (formalKernelCoefficient ρ U (k + 3) + C (2 * ρ) *
      (U * (if 1 ≤ k + 3 then formalKernelCoefficient ρ U (k + 3 - 1) else 0)) +
      C (ρ ^ 2) * (if 2 ≤ k + 3 then formalKernelCoefficient ρ U (k + 3 - 2) else 0)) =
        (if k + 3 = 0 then 1 else 0) - C (ρ ^ 2) * (if k + 3 = 2 then 1 else 0)
    rw [if_pos h1, if_pos h2, if_neg hne0, if_neg hne2]
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    simpa only [mul_zero, sub_self, mul_assoc] using formalKernelCoefficient_recurrence ρ U k

/-- The free-entry Chebyshev kernel uses exactly the formal coefficients just verified. -/
theorem kernelCoefficientPolynomial_eq_formal (a b : ℝ) (k : ℕ) :
    kernelCoefficientPolynomial a b k =
      formalKernelCoefficient (intervalRho a b)
        (C (intervalHalfWidth a b)⁻¹ * (X - C (intervalCenter a b))) k := rfl

open RoughRegime.CombinedAnalytic

/-- Matrix evaluation of the formal coefficients is exactly the implemented kernel series. -/
theorem matrixKernel_eq_formal_evaluation {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (A : Matrix n n ℝ) :
    matrixSeries (kernelSeries a b A) =
      PowerSeries.map (Polynomial.aeval A).toRingHom
        (formalReciprocalKernel (intervalRho a b)
          (C (intervalHalfWidth a b)⁻¹ * (X - C (intervalCenter a b)))) := by
  apply PowerSeries.ext
  intro k
  ext i j
  simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix, kernelSeries,
    PowerSeries.coeff_map, formalReciprocalKernel, PowerSeries.coeff_mk]
  rw [kernelCoefficientPolynomial_eq_formal]
  rfl

/-- The implemented matrix kernel obeys the manuscript's exact rational denominator identity. -/
theorem matrixKernel_generating_identity {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ) (A : Matrix n n ℝ) :
    let U := C (intervalHalfWidth a b)⁻¹ * (X - C (intervalCenter a b))
    let ρ := intervalRho a b
    (1 + PowerSeries.C (Polynomial.aeval A (C (2 * ρ) * U)) * PowerSeries.X +
      PowerSeries.C (Polynomial.aeval A (C (ρ ^ 2))) * PowerSeries.X ^ 2) *
        matrixSeries (kernelSeries a b A) =
      1 - PowerSeries.C (Polynomial.aeval A (C (ρ ^ 2))) * PowerSeries.X ^ 2 := by
  dsimp only
  rw [matrixKernel_eq_formal_evaluation]
  have h := congrArg (PowerSeries.map (Polynomial.aeval A).toRingHom)
    (formalReciprocalKernel_identity (intervalRho a b)
      (C (intervalHalfWidth a b)⁻¹ * (X - C (intervalCenter a b))))
  simpa using h

end NearlyMinimax
