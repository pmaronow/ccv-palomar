module

public import NearlyMinimax.AnchoredFeatures


@[expose] public section

/-! Finite global-coordinate expansions for actual anchor-dependent raw features. -/

noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace NearlyMinimax

/-- The exact centered scaled feature as a polynomial in the observation covariates. -/
def dyadicFeaturePolynomial {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (γ : AnchoredIndex d ℓ) : MvPolynomial (Fin d) ℝ :=
  ∏ i, (C ((2 : ℝ) ^ j) * (X i - C (x i))) ^ (γ.val i).val

theorem dyadicFeaturePolynomial_eval {d ℓ : ℕ} (j : ℕ) (x z : Covariate d)
    (γ : AnchoredIndex d ℓ) :
    eval z (dyadicFeaturePolynomial j x γ) = dyadicAnchoredFeature j x z γ := by
  simp only [dyadicFeaturePolynomial, map_prod, map_pow, map_mul, map_sub, eval_C, eval_X,
    dyadicAnchoredFeature, anchoredMonomial]

theorem dyadicFeaturePolynomial_degree {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (γ : AnchoredIndex d ℓ) : (dyadicFeaturePolynomial j x γ).totalDegree ≤ ℓ := by
  unfold dyadicFeaturePolynomial
  apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
  apply (Finset.sum_le_sum _).trans γ.property.2
  intro i hi
  have hlinear : (C ((2 : ℝ) ^ j) * (X i - C (x i))).totalDegree ≤ 1 := by
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, zero_add]
    exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left _ hlinear)

/-- The global finite monomial expansion used to lift all spatial anchors
from one fixed coordinate family of observation features. -/
theorem dyadicAnchoredFeature_global_expansion {d ℓ : ℕ} (j : ℕ) (x z : Covariate d)
    (γ : AnchoredIndex d ℓ) :
    dyadicAnchoredFeature j x z γ =
      ∑ β : PolynomialBox d ℓ,
        (dyadicFeaturePolynomial j x γ).coeff (polynomialBoxExponent β) *
          ∏ i, (z i) ^ (β i).val := by
  rw [← dyadicFeaturePolynomial_eval]
  exact polynomial_box_evaluation _ (dyadicFeaturePolynomial_degree j x γ) z

/-- Products in matrix raw features also have a single fixed global family. -/
theorem dyadicAnchoredFeature_product_global_expansion {d ℓ : ℕ}
    (j : ℕ) (x z : Covariate d) (γ δ : AnchoredIndex d ℓ) :
    dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ =
      ∑ β : PolynomialBox d (2 * ℓ),
        (dyadicFeaturePolynomial j x γ * dyadicFeaturePolynomial j x δ).coeff
          (polynomialBoxExponent β) * ∏ i, (z i) ^ (β i).val := by
  rw [← dyadicFeaturePolynomial_eval, ← dyadicFeaturePolynomial_eval, ← map_mul]
  apply polynomial_box_evaluation
  exact (MvPolynomial.totalDegree_mul _ _).trans
    ((Nat.add_le_add (dyadicFeaturePolynomial_degree j x γ)
      (dyadicFeaturePolynomial_degree j x δ)).trans_eq (by omega))

/-- Cell indicators preserve the exact finite coefficient expansion. -/
theorem dyadicAnchoredFeature_indicator_expansion {d ℓ : ℕ}
    (I : Set (Covariate d)) (j : ℕ) (x z : Covariate d) (γ : AnchoredIndex d ℓ) :
    I.indicator (fun w => dyadicAnchoredFeature j x w γ) z =
      ∑ β : PolynomialBox d ℓ,
        (dyadicFeaturePolynomial j x γ).coeff (polynomialBoxExponent β) *
          I.indicator (fun w => ∏ i, (w i) ^ (β i).val) z := by
  classical
  by_cases hz : z ∈ I
  · simp only [Set.indicator_of_mem hz]
    exact dyadicAnchoredFeature_global_expansion j x z γ
  · simp only [Set.indicator_of_notMem hz, mul_zero, Finset.sum_const_zero]

/-- Coefficientwise continuity of a polynomial family; this does not require
choosing an auxiliary topology on the infinite polynomial ring. -/
def PolynomialCoefficientContinuous {X σ : Type*} [TopologicalSpace X]
    (P : X → MvPolynomial σ ℝ) : Prop := ∀ e, Continuous (fun x => (P x).coeff e)

theorem polynomialCoefficientContinuous_const {X σ : Type*} [TopologicalSpace X]
    (P : MvPolynomial σ ℝ) : PolynomialCoefficientContinuous (fun _ : X => P) :=
  fun _ => continuous_const

theorem polynomialCoefficientContinuous_C {X σ : Type*} [TopologicalSpace X]
    [DecidableEq σ] (g : X → ℝ) (hg : Continuous g) :
    PolynomialCoefficientContinuous (fun x => C (g x) : X → MvPolynomial σ ℝ) := by
  intro e
  simp only [coeff_C]
  by_cases he : 0 = e
  · simpa only [he, if_true] using hg
  · simp only [he, if_false]
    exact continuous_const

theorem polynomialCoefficientContinuous_mul {X σ : Type*} [TopologicalSpace X]
    [DecidableEq σ] (P Q : X → MvPolynomial σ ℝ)
    (hP : PolynomialCoefficientContinuous P) (hQ : PolynomialCoefficientContinuous Q) :
    PolynomialCoefficientContinuous (fun x => P x * Q x) := by
  intro e
  simp only [coeff_mul]
  apply continuous_finset_sum
  intro v hv
  exact (hP v.1).mul (hQ v.2)

theorem polynomialCoefficientContinuous_sub {X σ : Type*} [TopologicalSpace X]
    (P Q : X → MvPolynomial σ ℝ)
    (hP : PolynomialCoefficientContinuous P) (hQ : PolynomialCoefficientContinuous Q) :
    PolynomialCoefficientContinuous (fun x => P x - Q x) := by
  intro e
  simp only [coeff_sub]
  exact (hP e).sub (hQ e)

theorem polynomialCoefficientContinuous_pow {X σ : Type*} [TopologicalSpace X]
    [DecidableEq σ] (P : X → MvPolynomial σ ℝ)
    (hP : PolynomialCoefficientContinuous P) (n : ℕ) :
    PolynomialCoefficientContinuous (fun x => P x ^ n) := by
  induction n with
  | zero => exact polynomialCoefficientContinuous_const 1
  | succ n hn =>
    simp_rw [pow_succ]
    exact polynomialCoefficientContinuous_mul _ _ hn hP

theorem polynomialCoefficientContinuous_prod {X σ ι : Type*} [TopologicalSpace X]
    [DecidableEq σ] (s : Finset ι) (P : ι → X → MvPolynomial σ ℝ)
    (hP : ∀ i ∈ s, PolynomialCoefficientContinuous (P i)) :
    PolynomialCoefficientContinuous (fun x => ∏ i ∈ s, P i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polynomialCoefficientContinuous_const (X := X) (1 : MvPolynomial σ ℝ)
  | @insert i s hi hs =>
    simp_rw [Finset.prod_insert hi]
    exact polynomialCoefficientContinuous_mul _ _ (hP i (Finset.mem_insert_self i s))
      (hs (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

/-- All actual anchor-dependent coefficients used in a factorial lift are Borel. -/
theorem dyadicFeaturePolynomial_coeff_continuous {d ℓ : ℕ} (j : ℕ)
    (γ : AnchoredIndex d ℓ) (e : Fin d →₀ ℕ) :
    Continuous (fun x : Covariate d => (dyadicFeaturePolynomial j x γ).coeff e) := by
  unfold dyadicFeaturePolynomial
  apply polynomialCoefficientContinuous_prod Finset.univ
    (fun i (x : Covariate d) => (C ((2 : ℝ) ^ j) * (X i - C (x i))) ^ (γ.val i).val) ?_ e
  intro i hi
  apply polynomialCoefficientContinuous_pow
  apply polynomialCoefficientContinuous_mul
  · exact polynomialCoefficientContinuous_const _
  · apply polynomialCoefficientContinuous_sub
    · exact polynomialCoefficientContinuous_const _
    · exact polynomialCoefficientContinuous_C _ (continuous_apply i)

theorem dyadicFeatureProduct_coeff_continuous {d ℓ : ℕ} (j : ℕ)
    (γ δ : AnchoredIndex d ℓ) (e : Fin d →₀ ℕ) :
    Continuous (fun x : Covariate d =>
      (dyadicFeaturePolynomial j x γ * dyadicFeaturePolynomial j x δ).coeff e) :=
  polynomialCoefficientContinuous_mul _ _ (dyadicFeaturePolynomial_coeff_continuous j γ)
    (dyadicFeaturePolynomial_coeff_continuous j δ) e

end NearlyMinimax
