module

public import NearlyMinimax.PaperPopulationFit
public import NearlyMinimax.DyadicPilotPointwise


@[expose] public section

/-! The true population increment in finite coordinates and its actual
inverse-polynomial approximation error. -/

noncomputable section
open Matrix MeasureTheory Set MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def anchoredFinVector {d ℓ : ℕ} (v : AnchoredIndex d ℓ → ℝ) :
    Fin (anchoredDimension d ℓ) → ℝ := fun i => v (anchoredFinIndex i)

theorem anchoredFinVector_norm {d ℓ : ℕ} (v : AnchoredIndex d ℓ → ℝ) :
    ‖(EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm (anchoredFinVector v)‖ =
      ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm v‖ := by
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin (AnchoredIndex d ℓ))
  have he : e ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm v) =
      (EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm (anchoredFinVector v) := by
    ext i
    rfl
  rw [← he]
  exact e.norm_map _

theorem anchoredFinReindex_mulVec {d ℓ : ℕ}
    (A : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ)
    (v : AnchoredIndex d ℓ → ℝ) :
    anchoredFinReindex d ℓ A *ᵥ anchoredFinVector v = anchoredFinVector (A *ᵥ v) := by
  ext i
  simp only [anchoredFinReindex, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
    anchoredFinVector, anchoredFinIndex, Matrix.mulVec, dotProduct]
  exact (Fintype.equivFin (AnchoredIndex d ℓ)).symm.sum_comp
    (fun γ : AnchoredIndex d ℓ => A (anchoredFinIndex i) γ * v γ)

theorem anchoredFinReindex_inv {d ℓ : ℕ}
    (A : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) :
    (anchoredFinReindex d ℓ A)⁻¹ = anchoredFinReindex d ℓ A⁻¹ :=
  Matrix.inv_reindex _ _ A

theorem anchoredFinVector_sub {d ℓ : ℕ} (v w : AnchoredIndex d ℓ → ℝ) :
    anchoredFinVector (v - w) = anchoredFinVector v - anchoredFinVector w := rfl

theorem anchoredFinVector_smul {d ℓ : ℕ} (a : ℝ) (v : AnchoredIndex d ℓ → ℝ) :
    anchoredFinVector (a • v) = a • anchoredFinVector v := rfl

theorem dyadicFinPilotMoments_eq_actual {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ)
    (x : Covariate d) (hx : x ∈ unitCube d) (t : Bool) :
    dyadicFinPilotMoments (ℓ := ℓ) θ j x t = anchoredFinVector
      ((dyadicKnownGram j x)⁻¹ *ᵥ (if t then dyadicConstantMoment θ j x else dyadicResponseMoment θ j x)) := by
  ext i
  cases t
  all_goals simp only [dyadicFinPilotMoments, Bool.false_eq_true, ↓reduceIte,
    anchoredFinVector]
  all_goals rw [preconditionedPilotPopulation_eq_sum C θ hθ j x hx]
  all_goals simp only [localPilotRow, localPilotReplaceRow, Matrix.mulVec, dotProduct,
    dyadicPilotPopulation_response C θ hθ j x hx, dyadicPilotPopulation_constant C θ hθ]

theorem dyadicFinPilot_fit {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ)
    (x : Covariate d) (hx : x ∈ unitCube d) :
    (dyadicFinPilotGram (ℓ := ℓ) θ j x)⁻¹ *ᵥ
      (dyadicFinPilotMoments θ j x false - θ.regression x • dyadicFinPilotMoments θ j x true) =
        anchoredFinVector (dyadicPopulationFit θ j x) := by
  rw [dyadicFinPilotMoments_eq_actual C θ hθ j x hx false,
    dyadicFinPilotMoments_eq_actual C θ hθ j x hx true]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← anchoredFinVector_smul, ← anchoredFinVector_sub,
    ← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
  rw [dyadicFinPilotGram, anchoredFinReindex_inv, anchoredFinReindex_mulVec,
    dyadicPopulationFit_preconditioner_cancels C θ hθ]

theorem dyadicFinite_increment_eq_actual {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ)
    (x : Covariate d) (hx : x ∈ unitCube d) :
    (dyadicFinPilotGram (ℓ := ℓ) θ j x)⁻¹ *ᵥ
      (dyadicFinPilotMoments θ j x false - θ.regression x • dyadicFinPilotMoments θ j x true) -
      anchoredFinTransport d ℓ *ᵥ
        ((if j = 0 then 1 else dyadicFinPilotGram θ (j - 1) x)⁻¹ *ᵥ
          ((if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x) false -
            θ.regression x • (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x) true)) =
        anchoredFinVector (dyadicPopulationIncrement θ x j) := by
  rw [dyadicFinPilot_fit C θ hθ j x hx]
  cases j with
  | zero => simp [dyadicPopulationIncrement, anchoredIncrement]
  | succ j =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel_right]
    rw [dyadicFinPilot_fit C θ hθ j x hx]
    rw [anchoredFinTransport, anchoredFinReindex_mulVec, ← anchoredFinVector_sub]
    rfl

theorem incrementFinVector_eval_population {r : ℕ} [NeZero r] (a b : ℝ)
    (A B T : Matrix (Fin r) (Fin r) ℝ) (U V : Bool → Fin r → ℝ)
    (y : ℝ) (m : ℕ) :
    incrementFinVector r a b T y m
      (fun i => incrementValuation A B U V ((Fintype.equivFin (incrementVariables r)).symm i)) =
        fun i => eval (incrementValuation A B U V) (incrementEntryPolynomial r a b T y m i) := by
  ext i
  simp only [incrementFinVector, incrementFinPolynomial, eval_rename, Function.comp_def,
    Equiv.symm_apply_apply]

/-- Density bounds yield the actual Hermitian charts used in the inverse
approximation. Only the explicitly displayed small increment enters this
generic deterministic helper. -/
theorem anchoredNormalized_increment_error {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)]
    (u v : Covariate d) (p q : Covariate d → ℝ) (hpmeas : Measurable p) (hqmeas : Measurable q)
    (a b χ ε : ℝ) (ha : 0 < a) (hab : a < b)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b)
    (hq : ∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b)
    (hχ : ‖(anchoredFinSimilarityUnit (ℓ := ℓ) u).val‖ *
      ‖((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ)
    (U V : Bool → Fin (anchoredDimension d ℓ) → ℝ)
    (y : ℝ) (T : Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ)
    (hδ : ‖(EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm
      ((anchoredFinNormalizedGram u p)⁻¹ *ᵥ (U false - y • U true) -
        T *ᵥ ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - y • V true)))‖ ≤ ε)
    (m : ℕ) :
    ‖(EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm
      ((fun i => eval (incrementValuation (anchoredFinNormalizedGram u p)
        (anchoredFinNormalizedGram v q) U V)
          (incrementEntryPolynomial (anchoredDimension d ℓ) a b T y m i)) -
        ((anchoredFinNormalizedGram u p)⁻¹ *ᵥ (U false - y • U true) -
          T *ᵥ ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - y • V true))))‖ ≤
      (χ ^ 2 * b ^ (anchoredDimension d ℓ + 1) * parentInverseErrorConstant a b (anchoredDimension d ℓ)) * ε *
        ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d ℓ * Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  let Q := anchoredFinSimilarityUnit (ℓ := ℓ) u
  let R := anchoredFinSimilarityUnit (ℓ := ℓ) v
  let G := anchoredFinNormalizedGram (ℓ := ℓ) u p
  let H := anchoredFinNormalizedGram (ℓ := ℓ) v q
  have hG : matrixSimilarity Q (matrixSimilarity Q⁻¹ G) = G := by
    simp [matrixSimilarity, Matrix.mul_assoc]
  have hH : matrixSimilarity R (matrixSimilarity R⁻¹ H) = H := by
    simp [matrixSimilarity, Matrix.mul_assoc]
  have he := incrementEntryPolynomial_error a b ha hab
    (matrixSimilarity Q⁻¹ G) (matrixSimilarity R⁻¹ H) T
    (anchoredFin_similarity_isHermitian u p) (anchoredFin_similarity_isHermitian v q)
    (anchoredFin_similarity_spectrum u p hpmeas a b ha.le hp)
    (anchoredFin_similarity_spectrum v q hqmeas a b ha.le hq)
    Q R χ hχ U V y ε (by simpa only [hG, hH] using hδ) m
  simpa only [hG, hH] using he

/-- Original U5(2) at the genuine observation-law population means. The
small-increment premise is proved by the actual U2 population fit theorem. -/
theorem admissible_dyadic_increment_polynomial_error {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ E : ℝ, 0 < E ∧ ∀ θ : RegressionParameter d, Admissible C θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ m : ℕ,
      ‖(EuclideanSpace.equiv (Fin (anchoredDimension d C.order)) ℝ).symm
        (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
          (anchoredFinTransport d C.order) (θ.regression x) m (dyadicIncrementRawMean θ j x) -
            anchoredFinVector (dyadicPopulationIncrement θ x j))‖ ≤
        E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
          Real.exp (-(m : ℝ) * exteriorTau ((C.densityLower + C.densityUpper) / (C.densityUpper - C.densityLower))) := by
  obtain ⟨χ, hχ, hcond⟩ := anchoredFinSimilarityUnit_uniform_condition (d := d) (ℓ := C.order)
  obtain ⟨D, hD, hinc⟩ := admissible_dyadicPopulationIncrement_bound C
  let E₀ := χ ^ 2 * C.densityUpper ^ (anchoredDimension d C.order + 1) *
    parentInverseErrorConstant C.densityLower C.densityUpper (anchoredDimension d C.order)
  let E := max 1 (E₀ * D)
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro θ hθ j x hx m
  let u := dyadicNormalizedAnchor j x
  let v := dyadicNormalizedAnchor (j - 1) x
  let p := dyadicNormalizedDensity θ j x
  let q := if j = 0 then (fun _ : Covariate d => (1 : ℝ)) else dyadicNormalizedDensity θ (j - 1) x
  let U := dyadicFinPilotMoments (ℓ := C.order) θ j x
  let V := if j = 0 then 0 else dyadicFinPilotMoments (ℓ := C.order) θ (j - 1) x
  have hqmeas : Measurable q := by
    by_cases hj : j = 0
    · simpa [q, hj] using (measurable_const : Measurable (fun _ : Covariate d => (1 : ℝ)))
    · simpa [q, hj] using dyadicNormalizedDensity_measurable C θ hθ (j - 1) x
  have hqb : ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ q w ∧ q w ≤ C.densityUpper := by
    by_cases hj : j = 0
    · exact Filter.Eventually.of_forall (fun _ => by
        simpa [q, hj] using And.intro C.densityLower_lt_one.le C.one_lt_densityUpper.le)
    · simpa [q, hj] using dyadicNormalizedDensity_bounds C θ hθ (j - 1) x
  have hparent : anchoredFinNormalizedGram (ℓ := C.order) v q =
      if j = 0 then 1 else dyadicFinPilotGram θ (j - 1) x := by
    by_cases hj : j = 0
    · simp [q, hj, anchoredFinNormalizedGram_one]
    · simp only [q, hj, ite_false]
      exact (dyadicFinPilotGram_eq_normalized C θ hθ (j - 1) x).symm
  have hactual : (anchoredFinNormalizedGram (ℓ := C.order) u p)⁻¹ *ᵥ
      (U false - θ.regression x • U true) - anchoredFinTransport d C.order *ᵥ
        ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - θ.regression x • V true)) =
        anchoredFinVector (dyadicPopulationIncrement θ x j) := by
    rw [hparent, ← dyadicFinPilotGram_eq_normalized C θ hθ j x]
    exact dyadicFinite_increment_eq_actual C θ hθ j x hx
  have hsmall : ‖(EuclideanSpace.equiv (Fin (anchoredDimension d C.order)) ℝ).symm
      ((anchoredFinNormalizedGram u p)⁻¹ *ᵥ (U false - θ.regression x • U true) -
        anchoredFinTransport d C.order *ᵥ
          ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - θ.regression x • V true)))‖ ≤
      D * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness := by
    rw [hactual, anchoredFinVector_norm]
    exact hinc θ hθ x hx j
  have he := anchoredNormalized_increment_error u v p q
    (dyadicNormalizedDensity_measurable C θ hθ j x) hqmeas
    C.densityLower C.densityUpper χ (D * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness)
    C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)
    (dyadicNormalizedDensity_bounds C θ hθ j x) hqb
    (hcond u (gridNormalizedAnchor_mem_cube _ (by positivity) x hx))
    U V (θ.regression x) (anchoredFinTransport d C.order) hsmall m
  rw [hactual] at he
  have hval : dyadicIncrementRawMean (ℓ := C.order) θ j x = fun a =>
      incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q) U V
        ((Fintype.equivFin (incrementVariables (anchoredDimension d C.order))).symm a) := by
    rw [dyadicIncrementRawMean_eq_population C θ hθ j x hx]
    have hcurrent : anchoredFinNormalizedGram (ℓ := C.order) u p = dyadicFinPilotGram θ j x :=
      (dyadicFinPilotGram_eq_normalized C θ hθ j x).symm
    simp only [dyadicIncrementPopulation, hparent, hcurrent]
    rfl
  rw [hval, incrementFinVector_eval_population]
  calc
    _ ≤ E₀ * (D * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness) * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
        Real.exp (-(m : ℝ) * exteriorTau ((C.densityLower + C.densityUpper) / (C.densityUpper - C.densityLower))) := he
    _ = (E₀ * D) * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
        Real.exp (-(m : ℝ) * exteriorTau ((C.densityLower + C.densityUpper) / (C.densityUpper - C.densityLower))) := by ring
    _ ≤ E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
        Real.exp (-(m : ℝ) * exteriorTau ((C.densityLower + C.densityUpper) / (C.densityUpper - C.densityLower))) := by
      gcongr
      exact le_max_right _ _

end NearlyMinimax
