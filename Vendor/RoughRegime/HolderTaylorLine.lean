module

public import RoughRegime.TaylorPolynomial


@[expose] public section

/-! Exact within derivatives and Taylor polynomials along cube segments. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.Model

def linePath {d : ℕ} (x y : Covariate d) : ℝ →ᴬ[ℝ] Covariate d :=
  ContinuousAffineMap.lineMap x y

lemma linePath_mem_cube {d : ℕ} (x y : Covariate d) (hx : x ∈ cube d)
    (hy : y ∈ cube d) (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : linePath x y z ∈ cube d := by
  exact (convex_cube d).segment_subset hx hy (lineMap_mem_segment ℝ x y hz)

@[simp] lemma linePath_zero {d : ℕ} (x y : Covariate d) : linePath x y 0 = x := by
  simp [linePath, ContinuousAffineMap.coe_lineMap_eq]

@[simp] lemma linePath_one {d : ℕ} (x y : Covariate d) : linePath x y 1 = y := by
  simp [linePath, ContinuousAffineMap.coe_lineMap_eq]

@[simp] lemma linePath_contLinear_one {d : ℕ} (x y : Covariate d) :
    (linePath x y).contLinear 1 = y - x := by
  simp [linePath, ContinuousAffineMap.coe_contLinear, AffineMap.lineMap_linear]

theorem linePath_iteratedDerivWithin {d k q : ℕ} (f : Covariate d → ℝ)
    (hf : ContDiffOn ℝ k f (cube d)) (hq : q ≤ k)
    (x y : Covariate d) (hx : x ∈ cube d) (hy : y ∈ cube d)
    (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin q (f ∘ linePath x y) (Icc (0 : ℝ) 1) z =
      iteratedFDerivWithin ℝ q f (cube d) (linePath x y z) (fun _ => y - x) := by
  have hseries := ((hf.ftaylorSeriesWithin (uniqueDiffOn_cube d)).comp_continuousAffineMap
    (linePath x y)).mono (fun z hz => linePath_mem_cube x y hx hy z hz)
  have he := hseries.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := q)
    (by exact_mod_cast hq) (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hz
  have hh := congrArg (fun L => L (fun _ : Fin q => (1 : ℝ))) he.symm
  simpa only [iteratedDerivWithin, ftaylorSeriesWithin,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, linePath_contLinear_one] using hh

theorem linePath_contDiffOn {d k : ℕ} (f : Covariate d → ℝ)
    (hf : ContDiffOn ℝ k f (cube d))
    (x y : Covariate d) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    ContDiffOn ℝ k (f ∘ linePath x y) (Icc (0 : ℝ) 1) := by
  exact hf.comp (linePath x y).contDiff.contDiffOn (fun z hz => linePath_mem_cube x y hx hy z hz)

theorem linePath_taylor_eq {d k : ℕ} (f : Covariate d → ℝ)
    (hf : ContDiffOn ℝ k f (cube d))
    (x y : Covariate d) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    taylorWithinEval (f ∘ linePath x y) k (Icc (0 : ℝ) 1) 0 1 =
      MvPolynomial.eval (fun i => y i) (holderTaylorPolynomial f k x) := by
  rw [taylor_within_apply, holderTaylorPolynomial_eval]
  apply Finset.sum_congr rfl
  intro q hq
  rw [linePath_iteratedDerivWithin f hf (Nat.le_of_lt_succ (Finset.mem_range.mp hq))
    x y hx hy 0 (by constructor <;> norm_num), linePath_zero]
  simp

end RoughRegime.Model
