module

public import Mathlib
public import RoughRegime.Cauchy
public import RoughRegime.PolynomialDerivatives


@[expose] public section

/-! Real derivatives of a real polynomial obey the complex Cauchy bound of Lemma 5(c). -/
noncomputable section
namespace RoughRegime.ComplexDerivativeBridge

def complexMonomial {p q : ℕ} (σ : Fin q → Fin p) (x : Fin p → ℂ) : ℂ := ∏ i, x (σ i)

def complexSlotMap {p q : ℕ} (σ : Fin q → Fin p) : (Fin p → ℂ) →L[ℂ] (Fin q → ℂ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (σ i))

@[simp] lemma complexSlotMap_apply {p q : ℕ} (σ : Fin q → Fin p) (x : Fin p → ℂ) (i : Fin q) :
    complexSlotMap σ x i = x (σ i) := rfl

@[fun_prop] lemma complexMonomial_contDiff {p q : ℕ} (σ : Fin q → Fin p) :
    ContDiff ℂ ⊤ (complexMonomial σ) := by unfold complexMonomial; fun_prop

lemma complexMonomial_iteratedFDeriv {p q r : ℕ} (σ : Fin q → Fin p)
    (m : Fin p → ℂ) (v : Fin r → Fin p → ℂ) :
    iteratedFDeriv ℂ r (complexMonomial σ) m v =
      ∑ a : Fin r ↪ Fin q, ∏ j : Fin q,
        if h : j ∈ Set.range a then v (a.toEquivRange.symm ⟨j, h⟩) (σ j) else m (σ j) := by
  classical
  let H := ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin q) ℂ
  have he : complexMonomial σ = H ∘ complexSlotMap σ := by funext x; simp [complexMonomial, H]
  rw [he, (complexSlotMap σ).iteratedFDeriv_comp_right H.contDiff m
    (show (r : WithTop ℕ∞) ≤ ⊤ from le_top), H.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.iteratedFDeriv, sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, H,
    ContinuousMultilinearMap.mkPiAlgebra_apply, complexSlotMap_apply, Pi.compRightL_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro j _
  split_ifs with h
  · rcases h with ⟨k, rfl⟩
    simp
  · rfl

lemma monomial_derivative_ofReal {p q r : ℕ} (σ : Fin q → Fin p)
    (m : Fin p → ℝ) (v : Fin r → Fin p → ℝ) :
    iteratedFDeriv ℂ r (complexMonomial σ) (fun j => (m j : ℂ))
        (fun i j => (v i j : ℂ)) =
      (iteratedFDeriv ℝ r (RoughRegime.PolynomialDerivatives.monomial σ) m v : ℂ) := by
  classical
  rw [complexMonomial_iteratedFDeriv, RoughRegime.PolynomialDerivatives.monomial_iteratedFDeriv]
  simp only [Complex.ofReal_sum, Complex.ofReal_prod]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro j _
  split_ifs <;> rfl

lemma complex_exponentCoordinates_prod {p : ℕ} (α : Fin p →₀ ℕ) (x : Fin p → ℂ) :
    (∏ j, x (RoughRegime.Upper.exponentCoordinates α j)) = ∏ i : Fin p, x i ^ α i := by
  change (∏ j : Fin (Fintype.card (RoughRegime.Upper.ExponentSlots α)),
    x (((Fintype.equivFin (RoughRegime.Upper.ExponentSlots α)).symm j).1)) = _
  rw [Fintype.prod_equiv (Fintype.equivFin (RoughRegime.Upper.ExponentSlots α)).symm
    (fun j => x (((Fintype.equivFin (RoughRegime.Upper.ExponentSlots α)).symm j).1))
    (fun s : RoughRegime.Upper.ExponentSlots α => x s.1) (fun _ => rfl)]
  unfold RoughRegime.Upper.ExponentSlots
  rw [Fintype.prod_sigma]
  simp

/-- Canonical complexification of the paper's real polynomial. -/
def complexify {p : ℕ} (F : MvPolynomial (Fin p) ℝ) : MvPolynomial (Fin p) ℂ :=
  MvPolynomial.map Complex.ofRealHom F

lemma complexify_eval_monomials {p : ℕ} (F : MvPolynomial (Fin p) ℝ) :
    (fun x => MvPolynomial.eval x (complexify F)) =
      fun x => ∑ α ∈ F.support, (F.coeff α : ℂ) *
        complexMonomial (RoughRegime.Upper.exponentCoordinates α) x := by
  funext x
  rw [complexify, MvPolynomial.eval_map, MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro α _
  rw [complexMonomial, complex_exponentCoordinates_prod]
  rfl

lemma complexify_iteratedFDeriv {p r : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (m : Fin p → ℝ) (v : Fin r → Fin p → ℝ) :
    iteratedFDeriv ℂ r (fun x => MvPolynomial.eval x (complexify F))
        (fun j => (m j : ℂ)) (fun i j => (v i j : ℂ)) =
      (iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m v : ℂ) := by
  rw [complexify_eval_monomials, iteratedFDeriv_fun_sum_apply]
  · rw [RoughRegime.PolynomialDerivatives.polynomial_iteratedFDeriv_monomial_sum]
    simp only [sum_apply, Complex.ofReal_sum, Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro α _
    have hf : ContDiffAt ℂ r (complexMonomial (RoughRegime.Upper.exponentCoordinates α))
        (fun j => (m j : ℂ)) :=
      (complexMonomial_contDiff _).contDiffAt.of_le (show (r : WithTop ℕ∞) ≤ ⊤ from le_top)
    change (iteratedFDeriv ℂ r ((F.coeff α : ℂ) • complexMonomial
      (RoughRegime.Upper.exponentCoordinates α)) _ _) = _
    rw [iteratedFDeriv_const_smul_apply hf, smul_apply, smul_eq_mul, monomial_derivative_ofReal]
  · intro α _
    exact (contDiff_const.mul (complexMonomial_contDiff _)).contDiffAt.of_le
      (show (r : WithTop ℕ∞) ≤ ⊤ from le_top)

lemma norm_ofReal_pi {p : ℕ} (v : Fin p → ℝ) : ‖fun j => (v j : ℂ)‖ = ‖v‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg v)]
    intro j
    rw [Complex.norm_real]
    exact norm_le_pi_norm v j
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg (fun j => (v j : ℂ)))]
    intro j
    simpa only [Complex.norm_real] using norm_le_pi_norm (fun j => (v j : ℂ)) j

/-- Actual real polynomial derivatives satisfy the source Cauchy direction bound. -/
theorem real_polynomial_derivative_bound {p r : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (m : Fin p → ℝ) (ε A : ℝ) (hε : 0 < ε)
    (hbound : ∀ y : Fin p → ℂ, ‖y - (fun j => (m j : ℂ))‖ < ε →
      ‖MvPolynomial.eval y (complexify F)‖ ≤ A)
    (hr : 0 < r) (v : Fin r → Fin p → ℝ) :
    ‖iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m v‖ ≤
      A * (r.factorial : ℝ) * (Real.exp 1 / ε) ^ r * ∏ i, ‖v i‖ := by
  have hc := RoughRegime.Cauchy.polynomial_derivative_bound (complexify F)
    (fun j => (m j : ℂ)) ε A hε hbound r hr (fun i j => (v i j : ℂ))
  rw [complexify_iteratedFDeriv, Complex.norm_real] at hc
  simpa only [norm_ofReal_pi] using hc

/-- The corresponding operator norm bound used in Lemma 8. -/
theorem real_polynomial_derivative_norm_bound {p r : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (m : Fin p → ℝ) (ε A : ℝ) (hε : 0 < ε) (hA : 0 ≤ A)
    (hbound : ∀ y : Fin p → ℂ, ‖y - (fun j => (m j : ℂ))‖ < ε →
      ‖MvPolynomial.eval y (complexify F)‖ ≤ A) (hr : 0 < r) :
    ‖iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m‖ ≤
      A * (r.factorial : ℝ) * (Real.exp 1 / ε) ^ r := by
  apply ContinuousMultilinearMap.opNorm_le_bound
  · positivity
  · exact real_polynomial_derivative_bound F m ε A hε hbound hr

end RoughRegime.ComplexDerivativeBridge
