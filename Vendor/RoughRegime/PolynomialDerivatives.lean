module

public import Mathlib
public import RoughRegime.Upper


@[expose] public section

/-! Exact Fréchet derivatives of monomials, including orders above the degree. -/

noncomputable section
open scoped BigOperators

namespace RoughRegime.PolynomialDerivatives

def monomial {p q : ℕ} (σ : Fin q → Fin p) (x : Fin p → ℝ) : ℝ := ∏ i, x (σ i)

def slotMap {p q : ℕ} (σ : Fin q → Fin p) : (Fin p → ℝ) →L[ℝ] (Fin q → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (σ i))

@[simp] theorem slotMap_apply {p q : ℕ} (σ : Fin q → Fin p) (x : Fin p → ℝ) (i : Fin q) :
    slotMap σ x i = x (σ i) := rfl

theorem monomial_iteratedFDeriv {p q r : ℕ} (σ : Fin q → Fin p)
    (m : Fin p → ℝ) (v : Fin r → Fin p → ℝ) :
    iteratedFDeriv ℝ r (monomial σ) m v =
      ∑ a : Fin r ↪ Fin q, ∏ j : Fin q,
        if h : j ∈ Set.range a then v (a.toEquivRange.symm ⟨j, h⟩) (σ j) else m (σ j) := by
  classical
  let H := ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin q) ℝ
  have he : monomial σ = H ∘ slotMap σ := by
    funext x
    simp [monomial, H]
  rw [he, (slotMap σ).iteratedFDeriv_comp_right H.contDiff m (show (r : WithTop ℕ∞) ≤ ⊤ from le_top),
    H.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.iteratedFDeriv, sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, H,
    ContinuousMultilinearMap.mkPiAlgebra_apply, slotMap_apply, Pi.compRightL_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro j _
  split_ifs with h
  · rcases h with ⟨k, rfl⟩
    simp
  · rfl

@[fun_prop] theorem monomial_contDiff {p q : ℕ} (σ : Fin q → Fin p) :
    ContDiff ℝ ⊤ (monomial σ) := by
  unfold monomial
  fun_prop

theorem monomial_iteratedFDeriv_above_degree {p q r : ℕ} (σ : Fin q → Fin p)
    (m : Fin p → ℝ) (v : Fin r → Fin p → ℝ) (hr : q < r) :
    iteratedFDeriv ℝ r (monomial σ) m v = 0 := by
  classical
  let : IsEmpty (Fin r ↪ Fin q) := ⟨fun a => by
    have hc := Fintype.card_le_of_injective a a.injective
    simp only [Fintype.card_fin] at hc
    omega⟩
  rw [monomial_iteratedFDeriv]
  exact Finset.sum_eq_zero (fun a _ => isEmptyElim a)

theorem monomial_derivative_const_mul {p q r : ℕ} (c : ℝ) (σ : Fin q → Fin p)
    (m : Fin p → ℝ) (v : Fin r → Fin p → ℝ) :
    iteratedFDeriv ℝ r (fun x => c * monomial σ x) m v =
      c * iteratedFDeriv ℝ r (monomial σ) m v := by
  have hf : ContDiffAt ℝ r (monomial σ) m :=
    (monomial_contDiff σ).contDiffAt.of_le (show (r : WithTop ℕ∞) ≤ ⊤ from le_top)
  change (iteratedFDeriv ℝ r (c • monomial σ) m) v =
    (c • iteratedFDeriv ℝ r (monomial σ) m) v
  rw [iteratedFDeriv_const_smul_apply hf]

theorem polynomial_eq_monomials {p : ℕ} (F : MvPolynomial (Fin p) ℝ) :
    (fun x => MvPolynomial.eval x F) =
      fun x => ∑ α ∈ F.support, F.coeff α * monomial (Upper.exponentCoordinates α) x := by
  funext x
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro α _
  rw [monomial, Upper.exponentCoordinates_prod]

@[fun_prop] theorem polynomial_contDiff {p : ℕ} (F : MvPolynomial (Fin p) ℝ) :
    ContDiff ℝ ⊤ (fun x => MvPolynomial.eval x F) := by
  rw [polynomial_eq_monomials]
  fun_prop

theorem polynomial_iteratedFDeriv_monomial_sum {p r : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (m : Fin p → ℝ) (v : Fin r → Fin p → ℝ) :
    iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m v =
      ∑ α ∈ F.support, F.coeff α *
        iteratedFDeriv ℝ r (monomial (Upper.exponentCoordinates α)) m v := by
  rw [polynomial_eq_monomials, iteratedFDeriv_fun_sum_apply]
  · simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro α _
    exact monomial_derivative_const_mul _ _ _ _
  · intro α _
    exact (contDiff_const.mul (monomial_contDiff (Upper.exponentCoordinates α))).contDiffAt.of_le
      (show (r : WithTop ℕ∞) ≤ ⊤ from le_top)

theorem polynomial_iteratedFDeriv_above_degree {p r : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (m : Fin p → ℝ) (v : Fin r → Fin p → ℝ) (hr : F.totalDegree < r) :
    iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m v = 0 := by
  rw [polynomial_iteratedFDeriv_monomial_sum]
  apply Finset.sum_eq_zero
  intro α hα
  rw [monomial_iteratedFDeriv_above_degree]
  · exact mul_zero _
  · rw [Upper.exponentSlots_card]
    exact (MvPolynomial.le_totalDegree hα).trans_lt hr

end RoughRegime.PolynomialDerivatives
