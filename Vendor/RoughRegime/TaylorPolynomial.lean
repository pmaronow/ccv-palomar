module

public import RoughRegime.HolderTensor


@[expose] public section

/-! Concrete multivariate Taylor polynomials in the original covariates. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace RoughRegime.Model

def multilinearPolynomial {d q : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin q => Covariate d) ℝ)
    (x : Covariate d) : MvPolynomial (Fin d) ℝ :=
  ∑ σ : Fin q → Fin d, C (L (fun i => EuclideanSpace.single (σ i) 1)) *
    ∏ i, (X (σ i) - C (x (σ i)))

theorem multilinearPolynomial_eval {d q : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin q => Covariate d) ℝ)
    (x y : Covariate d) :
    MvPolynomial.eval (fun i => y i) (multilinearPolynomial L x) = L (fun _ => y - x) := by
  classical
  simp only [multilinearPolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    map_prod, map_sub, MvPolynomial.eval_X]
  rw [multilinear_coordinate_expansion]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [PiLp.sub_apply]
  ring

theorem multilinearPolynomial_degree {d q : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin q => Covariate d) ℝ)
    (x : Covariate d) : (multilinearPolynomial L x).totalDegree ≤ q := by
  classical
  apply totalDegree_finsetSum_le
  intro σ _
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i : Fin q, 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_sub_C_le _ _).trans (by rw [totalDegree_X])
    _ = q := by simp

def holderTaylorPolynomial {d : ℕ} (f : Covariate d → ℝ) (k : ℕ)
    (x : Covariate d) : MvPolynomial (Fin d) ℝ :=
  ∑ q ∈ Finset.range (k + 1), C ((q.factorial : ℝ)⁻¹) *
    multilinearPolynomial (iteratedFDerivWithin ℝ q f (cube d) x) x

theorem holderTaylorPolynomial_degree {d : ℕ} (f : Covariate d → ℝ) (k : ℕ)
    (x : Covariate d) : (holderTaylorPolynomial f k x).totalDegree ≤ k := by
  classical
  apply totalDegree_finsetSum_le
  intro q hq
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  exact (multilinearPolynomial_degree _ _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hq))

theorem holderTaylorPolynomial_eval {d : ℕ} (f : Covariate d → ℝ) (k : ℕ)
    (x y : Covariate d) :
    MvPolynomial.eval (fun i => y i) (holderTaylorPolynomial f k x) =
      ∑ q ∈ Finset.range (k + 1), (q.factorial : ℝ)⁻¹ *
        iteratedFDerivWithin ℝ q f (cube d) x (fun _ => y - x) := by
  simp [holderTaylorPolynomial, multilinearPolynomial_eval]

end RoughRegime.Model
