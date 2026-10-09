module

public import NearlyMinimax.PopulationRowDerivatives


@[expose] public section

/-! The three actual polynomial families in U5(4), including the formal-response
derivative, share a degree-independent population derivative bound. -/

noncomputable section
namespace NearlyMinimax
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

def incrementFinRawVector (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (response : Bool) (m : ℕ) :
    (Fin (Fintype.card (incrementVariables r)) → ℝ) → Fin r → ℝ :=
  fun x i => MvPolynomial.eval x
    (MvPolynomial.rename (Fintype.equivFin (incrementVariables r))
      (rawIncrementEntryPolynomial r a b T response m i))

theorem incrementFinVector_affine (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) :
    incrementFinVector r a b T y m = incrementFinRawVector r a b T false m -
      y • incrementFinRawVector r a b T true m := by
  funext x i
  simp only [incrementFinVector, incrementFinPolynomial, incrementFinRawVector,
    MvPolynomial.eval_rename, incrementEntryPolynomial_affine,
    map_sub, map_mul, MvPolynomial.eval_C, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem incrementFinRawVector_true_eq (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (m : ℕ) : incrementFinRawVector r a b T true m =
      incrementFinVector r a b T 0 m - incrementFinVector r a b T 1 m := by
  rw [incrementFinVector_affine, incrementFinVector_affine]
  simp only [zero_smul, sub_zero, one_smul]
  abel

theorem incrementFinVector_response_hasDerivAt (r : ℕ) (a b : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (m : ℕ)
    (x : Fin (Fintype.card (incrementVariables r)) → ℝ) (y : ℝ) :
    HasDerivAt (fun z => incrementFinVector r a b T z m x)
      (-incrementFinRawVector r a b T true m x) y := by
  have h := (hasDerivAt_const y (incrementFinRawVector r a b T false m x)).sub
    ((hasDerivAt_id y).smul_const (incrementFinRawVector r a b T true m x))
  have hFun : (fun z => incrementFinVector r a b T z m x) =
      (fun z => incrementFinRawVector r a b T false m x - z • incrementFinRawVector r a b T true m x) := by
    funext z
    exact congrFun (incrementFinVector_affine r a b T z m) x
  rw [hFun]
  convert h using 1 <;> simp only [one_smul, zero_sub, Pi.sub_apply, id_eq]
  funext z
  rfl

theorem incrementFinVector_minus_response_deriv (r : ℕ) (a b : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (m : ℕ)
    (x : Fin (Fintype.card (incrementVariables r)) → ℝ) (y : ℝ) :
    -deriv (fun z => incrementFinVector r a b T z m x) y = incrementFinRawVector r a b T true m x := by
  rw [(incrementFinVector_response_hasDerivAt r a b T m x y).deriv, neg_neg]

def inverseDerivativeFamily (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (tag : Fin 3) :
    (Fin (Fintype.card (incrementVariables r)) → ℝ) → Fin r → ℝ :=
  ![incrementFinVector r a b T 0 m,
    incrementFinRawVector r a b T true m,
    incrementFinVector r a b T y m] tag

/-- All three original U5(4) polynomial families have one common bound at the
genuine preconditioned population moments. The middle family is exactly
`-partial_y F`, as proved above, rather than an assumed coefficient function. -/
theorem anchored_actual_inverse_derivative_family_bound {d ℓ : ℕ}
    [Nonempty (AnchoredIndex d ℓ)] (a b F Y : ℝ)
    (ha : 0 < a) (hab : a < b) (hF : 0 ≤ F) (hY : 0 ≤ Y) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ u v : Covariate d, u ∈ unitCube d → v ∈ unitCube d →
      ∀ p q f g : Covariate d → ℝ, Measurable p → Measurable q →
      (∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) →
      (∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b) →
      (∀ w ∈ unitCube d, |f w| ≤ F) → (∀ w ∈ unitCube d, |g w| ≤ F) →
      ∀ y : ℝ, |y| ≤ Y → ∀ m k : ℕ, ∀ tag : Fin 3,
      ∀ directions : Fin k → Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ,
        ‖iteratedFDeriv ℝ k
          (inverseDerivativeFamily (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) y m tag)
          (fun j => incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q)
            (anchoredFinMomentFamilies u p f) (anchoredFinMomentFamilies v q g)
            ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm j)) directions‖ ≤
          C * (k.factorial : ℝ) * A ^ k * ∏ j, ‖directions j‖ := by
  obtain ⟨C, A, hC, hA, hDer⟩ := anchored_actual_population_inverse_derivatives
    (d := d) (ℓ := ℓ) a b F (max 1 Y) ha hab hF (zero_le_one.trans (le_max_left _ _))
  refine ⟨2 * C, A, mul_pos (by norm_num) hC, hA, ?_⟩
  intro u v hu hv p q f g hpmeas hqmeas hp hq hf hg y hy m k tag directions
  let x := fun j => incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q)
    (anchoredFinMomentFamilies u p f) (anchoredFinMomentFamilies v q g)
    ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm j)
  have h0 := hDer u v hu hv p q f g hpmeas hqmeas hp hq hf hg 0
    (by simpa using zero_le_one.trans (le_max_left 1 Y)) m k directions
  have h1 := hDer u v hu hv p q f g hpmeas hqmeas hp hq hf hg 1
    (by simpa using le_max_left 1 Y) m k directions
  have hBase : C * (k.factorial : ℝ) * A ^ k * ∏ j, ‖directions j‖ ≤
      (2 * C) * (k.factorial : ℝ) * A ^ k * ∏ j, ‖directions j‖ := by
    have hP : 0 ≤ ∏ j, ‖directions j‖ := Finset.prod_nonneg (fun j _ => norm_nonneg _)
    have hN := mul_nonneg (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg k.factorial))
      (pow_nonneg hA.le k)) hP
    nlinarith only [hN]
  fin_cases tag
  · change ‖iteratedFDeriv ℝ k
      (incrementFinVector (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) 0 m) x directions‖ ≤ _
    exact h0.trans hBase
  · change ‖iteratedFDeriv ℝ k
      (incrementFinRawVector (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) true m) x directions‖ ≤ _
    rw [incrementFinRawVector_true_eq]
    rw [iteratedFDeriv_sub_apply
      ((incrementFinVector_contDiff (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) 0 m).of_le le_top).contDiffAt
      ((incrementFinVector_contDiff (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) 1 m).of_le le_top).contDiffAt]
    calc
      _ ≤ ‖iteratedFDeriv ℝ k (incrementFinVector (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) 0 m) x directions‖ +
          ‖iteratedFDeriv ℝ k (incrementFinVector (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) 1 m) x directions‖ := norm_sub_le _ _
      _ ≤ (C * (k.factorial : ℝ) * A ^ k * ∏ j, ‖directions j‖) +
          (C * (k.factorial : ℝ) * A ^ k * ∏ j, ‖directions j‖) := add_le_add h0 h1
      _ = _ := by ring
  · have hy' : |y| ≤ max 1 Y := hy.trans (le_max_right _ _)
    have h := hDer u v hu hv p q f g hpmeas hqmeas hp hq hf hg y hy' m k directions
    change ‖iteratedFDeriv ℝ k
      (incrementFinVector (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) y m) x directions‖ ≤ _
    exact h.trans hBase

end NearlyMinimax
