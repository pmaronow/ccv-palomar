module

public import NearlyMinimax.CellProjection


@[expose] public section

open Matrix MeasureTheory MvPolynomial
open scoped BigOperators

noncomputable section
namespace NearlyMinimax

/-- A rectangular monomial index set; it contains every monomial of
bounded total degree and has `(order+1)^dimension` elements. -/
abbrev PolynomialBox (d ℓ : ℕ) := Fin d → Fin (ℓ + 1)

def polynomialBoxExponent {d ℓ : ℕ} (γ : PolynomialBox d ℓ) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (γ i).val)

@[simp] theorem polynomial_box_exponent_apply {d ℓ : ℕ}
    (γ : PolynomialBox d ℓ) (i : Fin d) : polynomialBoxExponent γ i = (γ i).val := by
  change Finsupp.equivFunOnFinite (Finsupp.equivFunOnFinite.symm (fun i => (γ i).val)) i = _
  simp

theorem polynomial_box_exponent_injective {d ℓ : ℕ} :
    Function.Injective (polynomialBoxExponent (d := d) (ℓ := ℓ)) := by
  intro γ δ he
  funext i
  apply Fin.ext
  simpa only [polynomial_box_exponent_apply] using congrArg (fun w : Fin d →₀ ℕ => w i) he

/-- Total degree bounds every coordinate of every nonzero coefficient. -/
theorem polynomial_coefficient_box_bound {d ℓ : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (hP : P.totalDegree ≤ ℓ) (w : Fin d →₀ ℕ) (hw : P.coeff w ≠ 0) :
    ∀ i, w i ≤ ℓ := by
  have hsupport : w ∈ P.support := mem_support_iff.mpr hw
  have hsum := (le_totalDegree hsupport).trans hP
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hsum
  intro i
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hsum

/-- Every bounded-degree polynomial has an exact expansion in the
finite rectangular monomial feature set. -/
theorem polynomial_as_box_sum {d ℓ : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (hP : P.totalDegree ≤ ℓ) :
    P = ∑ γ : PolynomialBox d ℓ,
      monomial (polynomialBoxExponent γ) (P.coeff (polynomialBoxExponent γ)) := by
  classical
  apply MvPolynomial.ext
  intro w
  simp only [coeff_sum, coeff_monomial]
  by_cases hw : ∀ i, w i ≤ ℓ
  · let γw : PolynomialBox d ℓ := fun i => ⟨w i, Nat.lt_succ_of_le (hw i)⟩
    have hencode : polynomialBoxExponent γw = w := by
      ext i
      simp only [polynomial_box_exponent_apply, γw]
    have heq : ∀ γ : PolynomialBox d ℓ, polynomialBoxExponent γ = w ↔ γ = γw := by
      intro γ
      rw [← hencode]
      exact ⟨fun h => polynomial_box_exponent_injective h, fun h => congrArg polynomialBoxExponent h⟩
    simp only [heq]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hencode]
  · have hz : P.coeff w = 0 := by
      by_contra hn
      exact hw (polynomial_coefficient_box_bound P hP w hn)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro γ hγ
    have hne : polynomialBoxExponent γ ≠ w := by
      intro he
      apply hw
      intro i
      rw [← he, polynomial_box_exponent_apply]
      exact Nat.le_of_lt_succ (γ i).isLt
    simp only [hne, ite_false]

/-- Polynomial evaluation is exactly finite feature-vector evaluation. -/
theorem polynomial_box_evaluation {d ℓ : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (hP : P.totalDegree ≤ ℓ) (x : Covariate d) :
    eval x P = ∑ γ : PolynomialBox d ℓ,
      (P.coeff (polynomialBoxExponent γ)) * ∏ i, (x i) ^ (γ i).val := by
  conv_lhs => rw [polynomial_as_box_sum P hP]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [polynomial_box_exponent_apply]

/-- The empirical design for cellwise polynomial approximation,
using the actual sample covariates and their actual cell labels. -/
def cellPolynomialDesign {d ℓ : ℕ} {ι κ : Type*} [DecidableEq κ]
    (cell : ι → κ) (x : ι → Covariate d) : Matrix ι (κ × PolynomialBox d ℓ) ℝ :=
  fun i j => if cell i = j.1 then ∏ r, (x i r) ^ (j.2 r).val else 0

/-- The actual design evaluates every cellwise bounded-degree polynomial. -/
theorem cell_polynomial_design_evaluation {d ℓ : ℕ} {ι κ : Type*}
    [Fintype κ] [DecidableEq κ] (cell : ι → κ) (x : ι → Covariate d)
    (P : κ → MvPolynomial (Fin d) ℝ) (hP : ∀ c, (P c).totalDegree ≤ ℓ) :
    cellPolynomialDesign (ℓ := ℓ) cell x *ᵥ
      (fun j => (P j.1).coeff (polynomialBoxExponent j.2)) =
      fun i => eval (x i) (P (cell i)) := by
  classical
  ext i
  simp only [cellPolynomialDesign, mulVec, dotProduct, Fintype.sum_prod_type, ite_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Finset.sum_eq_single (cell i)]
  · simp only [ite_true]
    rw [polynomial_box_evaluation (P (cell i)) (hP (cell i)) (x i)]
    apply Finset.sum_congr rfl
    intro γ hγ
    exact mul_comm _ _
  · intro c hc hne
    simp only [Ne.symm hne, ite_false]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- Every concrete cellwise polynomial fitted by this matrix is killed
by its exact residual projector, including irregular or deficient designs. -/
theorem cell_polynomial_residual_kills {d ℓ : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (cell : ι → κ) (x : ι → Covariate d)
    (P : κ → MvPolynomial (Fin d) ℝ) (hP : ∀ c, (P c).totalDegree ≤ ℓ) :
    (1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := ℓ) cell x)) *ᵥ
      (fun i => eval (x i) (P (cell i))) = 0 := by
  rw [← cell_polynomial_design_evaluation cell x P hP, sub_mulVec, one_mulVec,
    empirical_design_fixes_evaluation, sub_self]

/-- A genuine polynomial approximation error controls residual energy;
the fitting and projection steps are proved from matrix evaluation. -/
theorem cell_polynomial_residual_bound {d ℓ : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (cell : ι → κ) (x : ι → Covariate d) (f : ι → ℝ)
    (P : κ → MvPolynomial (Fin d) ℝ) (hP : ∀ c, (P c).totalDegree ≤ ℓ)
    (b : ℝ) (hb : 0 ≤ b) (herror : ∀ i, |f i - eval (x i) (P (cell i))| ≤ b) :
    projectionEnergy ((1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := ℓ) cell x)) *ᵥ f) ≤
      Fintype.card ι * b ^ 2 := by
  have hs := empirical_design_projection_spec (cellPolynomialDesign (ℓ := ℓ) cell x)
  have hA := projection_complement _ hs.1 hs.2.1
  exact projection_approximation_bound _ hA.1 hA.2 f _
    (cell_polynomial_residual_kills cell x P hP) b hb herror


/-- The box design has a fixed number of monomial columns per cell. -/
theorem cell_polynomial_residual_degrees {d ℓ : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (cell : ι → κ) (x : ι → Covariate d) :
    (Fintype.card ι : ℝ) - Fintype.card κ * (ℓ + 1 : ℕ) ^ d ≤
      (1 - empiricalDesignProjection (cellPolynomialDesign (ℓ := ℓ) cell x)).trace := by
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow] using
    empirical_design_residual_degrees (cellPolynomialDesign (ℓ := ℓ) cell x)

/-- Monomial evaluation and cell labels give a Borel polynomial design. -/
theorem cell_polynomial_design_measurable {X ι κ : Type*} {d ℓ : ℕ}
    [MeasurableSpace X] [Fintype ι] [Fintype κ] [DecidableEq κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (cell : X → ι → κ) (x : X → ι → Covariate d)
    (hcell : Measurable cell) (hx : Measurable x) :
    Measurable (fun ω => cellPolynomialDesign (ℓ := ℓ) (cell ω) (x ω)) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  apply Measurable.ite (((measurable_pi_apply i).comp hcell) (measurableSet_singleton j.1))
    _ measurable_const
  exact Finset.measurable_prod Finset.univ (fun r _ => by fun_prop)

end NearlyMinimax
