module

public import NearlyMinimax.AnchoredExpansion


@[expose] public section

/-! Exact spanning by nonconstant centered monomials, including scaled anchors. -/

noncomputable section
open MvPolynomial Matrix
open scoped BigOperators
namespace NearlyMinimax

/-- A bounded-degree polynomial with zero constant coefficient uses precisely
our concrete nonconstant monomial coordinates. -/
theorem polynomial_as_anchored_sum {d ℓ : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (hP : P.totalDegree ≤ ℓ) (hzero : P.coeff 0 = 0) :
    P = anchoredPolynomial (fun γ : AnchoredIndex d ℓ => P.coeff (anchoredExponent γ)) := by
  classical
  let pred : PolynomialBox d ℓ → Prop := fun γ =>
    0 < ∑ i, (γ i).val ∧ (∑ i, (γ i).val) ≤ ℓ
  let f : PolynomialBox d ℓ → MvPolynomial (Fin d) ℝ := fun γ =>
    monomial (polynomialBoxExponent γ) (P.coeff (polynomialBoxExponent γ))
  have hz : ∀ γ, ¬ pred γ → f γ = 0 := by
    intro γ hγ
    have hn : P.coeff (polynomialBoxExponent γ) = 0 := by
      by_contra hc
      have hs := (le_totalDegree (mem_support_iff.mpr hc)).trans hP
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hs
      simp only [polynomial_box_exponent_apply] at hs
      have hpos : 0 < ∑ i, (γ i).val := by
        by_contra hnot
        have hs0 : (∑ i, (γ i).val) = 0 := by omega
        have he : polynomialBoxExponent γ = 0 := by
          ext i
          have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (γ j).val) (Finset.mem_univ i)
          rw [hs0] at hi
          simp only [polynomial_box_exponent_apply, Finsupp.zero_apply]
          omega
        rw [he, hzero] at hc
        exact hc rfl
      exact hγ ⟨hpos, hs⟩
    simp only [f, hn, map_zero]
  have hsum := Fintype.sum_subtype_add_sum_subtype pred f
  have hc : (∑ γ : {γ : PolynomialBox d ℓ // ¬ pred γ}, f γ.val) = 0 := by
    apply Finset.sum_eq_zero
    intro γ hγ
    exact hz γ.val γ.property
  rw [hc, add_zero] at hsum
  calc
    P = ∑ γ : PolynomialBox d ℓ,
        monomial (polynomialBoxExponent γ) (P.coeff (polynomialBoxExponent γ)) :=
      polynomial_as_box_sum P hP
    _ = anchoredPolynomial (fun γ => P.coeff (anchoredExponent γ)) := hsum.symm

/-- A finite explicit polynomial pullback under `v ↦ a+h v`. -/
def affinePullbackPolynomial {d : ℕ} (ℓ : ℕ) (a : Covariate d) (h : ℝ)
    (P : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ γ : PolynomialBox d ℓ, C (P.coeff (polynomialBoxExponent γ)) *
    ∏ i, (C (a i) + C h * X i) ^ (γ i).val

theorem affinePullbackPolynomial_eval {d ℓ : ℕ} (a : Covariate d) (h : ℝ)
    (P : MvPolynomial (Fin d) ℝ) (hP : P.totalDegree ≤ ℓ) (v : Covariate d) :
    eval v (affinePullbackPolynomial ℓ a h P) = eval (fun i => a i + h * v i) P := by
  rw [polynomial_box_evaluation P hP]
  simp only [affinePullbackPolynomial, map_sum, map_mul, map_prod, map_pow, map_add,
    eval_C, eval_X]

theorem affinePullbackPolynomial_degree {d ℓ : ℕ} (a : Covariate d) (h : ℝ)
    (P : MvPolynomial (Fin d) ℝ) (hP : P.totalDegree ≤ ℓ) :
    (affinePullbackPolynomial ℓ a h P).totalDegree ≤ ℓ := by
  unfold affinePullbackPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro γ hγ
  by_cases hc : P.coeff (polynomialBoxExponent γ) = 0
  · simp [hc]
  have hs := (le_totalDegree (mem_support_iff.mpr hc)).trans hP
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hs
  simp only [polynomial_box_exponent_apply] at hs
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
  apply (Finset.sum_le_sum _).trans hs
  intro i hi
  have hl : (C (a i) + C h * X i).totalDegree ≤ 1 := by
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le (by simp)
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simp
  exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left _ hl)

/-- Every polynomial of the correct degree vanishing at its anchor has an
exact centered monomial representation on all of the ambient space. -/
theorem polynomial_centered_representation {d ℓ : ℕ} (u : Covariate d)
    (P : MvPolynomial (Fin d) ℝ) (hP : P.totalDegree ≤ ℓ) (hu : eval u P = 0) :
    ∃ c : AnchoredIndex d ℓ → ℝ, ∀ z : Covariate d,
      eval z P = ∑ γ, c γ * anchoredFeature u z γ := by
  let Q := affinePullbackPolynomial ℓ u 1 P
  have hQ : Q.totalDegree ≤ ℓ := affinePullbackPolynomial_degree u 1 P hP
  have hQ0 : Q.coeff 0 = 0 := by
    rw [← constantCoeff_eq, ← eval_zero]
    have he := affinePullbackPolynomial_eval u 1 P hP 0
    simpa only [Pi.zero_apply, mul_zero, add_zero, hu, Q] using he
  refine ⟨fun γ => Q.coeff (anchoredExponent γ), ?_⟩
  intro z
  have he := affinePullbackPolynomial_eval u 1 P hP (z - u)
  have hz : (fun i => u i + 1 * (z - u) i) = z := by
    funext i
    simp
  rw [hz] at he
  calc
    eval z P = eval (z - u) Q := he.symm
    _ = eval (z - u) (anchoredPolynomial (fun γ => Q.coeff (anchoredExponent γ))) :=
      congrArg (eval (z - u)) (polynomial_as_anchored_sum Q hQ hQ0)
    _ = _ := anchoredPolynomial_eval _ (z - u)

/-- Centered monomial coordinates are unique as functions on the ambient space. -/
theorem anchoredFeature_coefficient_unique {d ℓ : ℕ} (u : Covariate d)
    (c e : AnchoredIndex d ℓ → ℝ)
    (h : ∀ z : Covariate d, (∑ γ, c γ * anchoredFeature u z γ) =
      ∑ γ, e γ * anchoredFeature u z γ) : c = e := by
  have hp : anchoredPolynomial c = anchoredPolynomial e := by
    apply MvPolynomial.funext
    intro v
    have hv := h (v + u)
    have hs : v + u - u = v := by abel
    simpa only [anchoredFeature, hs, ← anchoredPolynomial_eval] using hv
  funext γ
  have hc := congrArg (fun Q => Q.coeff (anchoredExponent γ)) hp
  simpa only [anchoredPolynomial_coeff] using hc

/-- This is the concrete basis property from U1(1), in exact evaluation form. -/
theorem polynomial_centered_unique_representation {d ℓ : ℕ} (u : Covariate d)
    (P : MvPolynomial (Fin d) ℝ) (hP : P.totalDegree ≤ ℓ) (hu : eval u P = 0) :
    ∃! c : AnchoredIndex d ℓ → ℝ, ∀ z : Covariate d,
      eval z P = ∑ γ, c γ * anchoredFeature u z γ := by
  obtain ⟨c, hc⟩ := polynomial_centered_representation u P hP hu
  refine ⟨c, hc, ?_⟩
  intro e he
  exact anchoredFeature_coefficient_unique u e c (fun z => (he z).symm.trans (hc z))

end NearlyMinimax
