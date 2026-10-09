module

public import Mathlib
public import RoughRegime.PolynomialDerivatives


@[expose] public section

/-! Exact polynomial and derivative structure of a sum of cell moment polynomials. -/
noncomputable section
namespace RoughRegime.PolynomialCells

/-- Cell coordinates as a continuous linear projection from the joint moment vector. -/
def cellProjection {K p : ℕ} (c : Fin K) :
    (Fin (K * p) → ℝ) →L[ℝ] (Fin p → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (finProdFinEquiv (c, j)))

@[simp] lemma cellProjection_apply {K p : ℕ} (c : Fin K) (x : Fin (K * p) → ℝ) (j : Fin p) :
    cellProjection c x j = x (finProdFinEquiv (c, j)) := rfl

/-- The paper's aggregate polynomial `K⁻¹ ∑C FC`, in actual disjoint cell variables. -/
def cellMomentPolynomial {K p : ℕ} (F : Fin K → MvPolynomial (Fin p) ℝ) :
    MvPolynomial (Fin (K * p)) ℝ :=
  MvPolynomial.C (K : ℝ)⁻¹ * ∑ c : Fin K,
    MvPolynomial.rename (fun j => finProdFinEquiv (c, j)) (F c)

lemma cellMomentPolynomial_eval {K p : ℕ} (F : Fin K → MvPolynomial (Fin p) ℝ)
    (x : Fin (K * p) → ℝ) :
    MvPolynomial.eval x (cellMomentPolynomial F) =
      (K : ℝ)⁻¹ * ∑ c : Fin K, MvPolynomial.eval (cellProjection c x) (F c) := by
  classical
  simp [cellMomentPolynomial, MvPolynomial.eval_rename, Function.comp_def, cellProjection]

lemma cellMomentPolynomial_degree {K p R : ℕ} (F : Fin K → MvPolynomial (Fin p) ℝ)
    (hdeg : ∀ c, (F c).totalDegree ≤ R) : (cellMomentPolynomial F).totalDegree ≤ R := by
  classical
  unfold cellMomentPolynomial
  calc
    _ ≤ (MvPolynomial.C (K : ℝ)⁻¹ : MvPolynomial (Fin (K * p)) ℝ).totalDegree +
      (∑ c : Fin K, MvPolynomial.rename (fun j => finProdFinEquiv (c, j)) (F c)).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + R := by
      apply Nat.add_le_add
      · exact (MvPolynomial.totalDegree_C _).le
      · exact (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le (fun c _ =>
          (MvPolynomial.totalDegree_rename_le _ _).trans (hdeg c)))
    _ = R := Nat.zero_add _

/-- The derivative of the aggregate polynomial splits exactly into the cell derivatives. -/
theorem cellMomentPolynomial_iteratedFDeriv {K p r : ℕ}
    (F : Fin K → MvPolynomial (Fin p) ℝ) (m : Fin (K * p) → ℝ)
    (v : Fin r → Fin (K * p) → ℝ) :
    iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x (cellMomentPolynomial F)) m v =
      (K : ℝ)⁻¹ * ∑ c : Fin K,
        iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x (F c)) (cellProjection c m)
          (fun i => cellProjection c (v i)) := by
  classical
  let f : Fin K → (Fin (K * p) → ℝ) → ℝ :=
    fun c x => MvPolynomial.eval (cellProjection c x) (F c)
  have hf : ∀ c, ContDiff ℝ ⊤ (f c) := fun c =>
    (RoughRegime.PolynomialDerivatives.polynomial_contDiff (F c)).comp (cellProjection c).contDiff
  have hs : ContDiff ℝ ⊤ (fun x => ∑ c : Fin K, f c x) := by fun_prop
  have heq : (fun x => MvPolynomial.eval x (cellMomentPolynomial F)) =
      (K : ℝ)⁻¹ • (fun x => ∑ c : Fin K, f c x) := by
    funext x
    exact cellMomentPolynomial_eval F x
  rw [heq, iteratedFDeriv_const_smul_apply (hs.contDiffAt.of_le (show (r : WithTop ℕ∞) ≤ ⊤ from le_top)),
    iteratedFDeriv_fun_sum_apply (fun c _ => (hf c).contDiffAt.of_le (show (r : WithTop ℕ∞) ≤ ⊤ from le_top))]
  simp only [smul_apply, smul_eq_mul, sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  have he : f c = (fun x => MvPolynomial.eval x (F c)) ∘ cellProjection c := rfl
  rw [he, (cellProjection c).iteratedFDeriv_comp_right
    (RoughRegime.PolynomialDerivatives.polynomial_contDiff (F c)) m (show (r : WithTop ℕ∞) ≤ ⊤ from le_top)]
  rfl

end RoughRegime.PolynomialCells
