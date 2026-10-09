module

public import NearlyMinimax.PaperInverse
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous


@[expose] public section

/-! Free-coordinate increment polynomials and their vector-moment structure in Lemma U5(3). -/

noncomputable section
namespace NearlyMinimax
open scoped BigOperators
open MvPolynomial

/-- Current and parent matrix entries together with their regression and density vector moments. -/
abbrev incrementVariables (r : ℕ) := parentInverseVariables r ⊕ (Bool × Bool × Fin r)

def currentVariableMatrix (r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial (parentInverseVariables r) ℝ) :=
  fun i j => X (Sum.inl (i, j))

def parentVariableMatrix (r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial (parentInverseVariables r) ℝ) :=
  fun i j => X (Sum.inr ⟨0, (i, j)⟩)

def vectorMoment (r : ℕ) (parent response : Bool) (i : Fin r) :
    MvPolynomial (incrementVariables r) ℝ := X (Sum.inr (parent, response, i))

def rawNumeratorPolynomial (r : ℕ) (T : Matrix (Fin r) (Fin r) ℝ)
    (response : Bool) (i : Fin r) : MvPolynomial (incrementVariables r) ℝ :=
  rename Sum.inl (parentVariableMatrix r).det * vectorMoment r false response i -
    ∑ j, ∑ k, ∑ l,
      rename Sum.inl (currentVariableMatrix r i j) * C (T j k) *
      rename Sum.inl ((parentVariableMatrix r).adjugate k l) * vectorMoment r true response l

/-- The exact determinant-cleared numerator, affine in the formal response `y`. -/
def numeratorPolynomial (r : ℕ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (i : Fin r) :
    MvPolynomial (incrementVariables r) ℝ :=
  rawNumeratorPolynomial r T false i - C y * rawNumeratorPolynomial r T true i

def incrementEntryPolynomial (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (i : Fin r) : MvPolynomial (incrementVariables r) ℝ :=
  ∑ j, rename Sum.inl (parentInverseEntryPolynomial a b r m i j) * numeratorPolynomial r T y j

private theorem determinant_degree_le {V n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (MvPolynomial V ℝ)) (hM : ∀ i j, (M i j).totalDegree ≤ 1) :
    M.det.totalDegree ≤ Fintype.card n := by
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ hσ
  simp only [Units.smul_def]
  apply (MvPolynomial.totalDegree_smul_le _ _).trans
  apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
  calc
    ∑ i, (M (σ i) i).totalDegree ≤ ∑ _i : n, 1 := Finset.sum_le_sum (fun i hi => hM _ _)
    _ = _ := by simp

private theorem adjugate_degree_le {V : Type*} (r : ℕ)
    (M : Matrix (Fin r) (Fin r) (MvPolynomial V ℝ))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (i j : Fin r) :
    (M.adjugate i j).totalDegree ≤ r - 1 := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ k =>
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have hz : ((-1 : MvPolynomial V ℝ) ^ (j.val + i.val)).totalDegree ≤ 0 := by
      simpa using MvPolynomial.totalDegree_pow (-1 : MvPolynomial V ℝ) (j.val + i.val)
    have hd := determinant_degree_le (M.submatrix j.succAbove i.succAbove) (fun i j => hM _ _)
    simpa using Nat.add_le_add hz hd

/-- The cleared numerator has total degree at most `r+1`. -/
theorem rawNumeratorPolynomial_degree (r : ℕ) [NeZero r]
    (T : Matrix (Fin r) (Fin r) ℝ) (response : Bool) (i : Fin r) :
    (rawNumeratorPolynomial r T response i).totalDegree ≤ r + 1 := by
  unfold rawNumeratorPolynomial
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    apply Nat.add_le_add
    · apply (MvPolynomial.totalDegree_rename_le _ _).trans
      simpa using determinant_degree_le (parentVariableMatrix r) (by simp [parentVariableMatrix])
    · simp [vectorMoment]
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    apply MvPolynomial.totalDegree_finsetSum_le
    intro l hl
    have hadj := adjugate_degree_le r (parentVariableMatrix r) (by simp [parentVariableMatrix]) k l
    have hadj' := (MvPolynomial.totalDegree_rename_le
      (Sum.inl : parentInverseVariables r → incrementVariables r) _).trans hadj
    have hA : (rename Sum.inl (currentVariableMatrix r i j) :
        MvPolynomial (incrementVariables r) ℝ).totalDegree ≤ 1 := by simp [currentVariableMatrix]
    have h1 := MvPolynomial.totalDegree_mul
      (rename Sum.inl (currentVariableMatrix r i j) : MvPolynomial (incrementVariables r) ℝ) (C (T j k))
    have h2 := MvPolynomial.totalDegree_mul
      (rename Sum.inl (currentVariableMatrix r i j) * C (T j k) : MvPolynomial (incrementVariables r) ℝ)
      (rename Sum.inl ((parentVariableMatrix r).adjugate k l))
    have h3 := MvPolynomial.totalDegree_mul
      (rename Sum.inl (currentVariableMatrix r i j) * C (T j k) *
        rename Sum.inl ((parentVariableMatrix r).adjugate k l)) (vectorMoment r true response l)
    simp only [MvPolynomial.totalDegree_C, add_zero] at h1
    have hv : (vectorMoment r true response l).totalDegree = 1 := by simp [vectorMoment]
    rw [hv] at h3
    have hr : r ≠ 0 := NeZero.ne r
    omega

theorem numeratorPolynomial_degree (r : ℕ) [NeZero r]
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (i : Fin r) :
    (numeratorPolynomial r T y i).totalDegree ≤ r + 1 := by
  unfold numeratorPolynomial
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le (rawNumeratorPolynomial_degree r T false i)
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simpa using rawNumeratorPolynomial_degree r T true i

/-- The complete free-moment increment has the paper's degree bound `m+r+1`. -/
theorem incrementEntryPolynomial_degree (r : ℕ) [NeZero r] (a b : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (i : Fin r) :
    (incrementEntryPolynomial r a b T y m i).totalDegree ≤ m + r + 1 := by
  unfold incrementEntryPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply (MvPolynomial.totalDegree_mul _ _).trans
  exact (Nat.add_le_add ((MvPolynomial.totalDegree_rename_le _ _).trans
    (parentInverseEntryPolynomial_degree a b r m i j))
    (numeratorPolynomial_degree r T y j)).trans_eq (by omega)

/-- Matrix coordinates have weight zero; all four vector-moment families have weight one. -/
def vectorMomentWeight (r : ℕ) : incrementVariables r → ℕ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

private theorem renamed_matrix_polynomial_homogeneous (r : ℕ)
    (P : MvPolynomial (parentInverseVariables r) ℝ) :
    IsWeightedHomogeneous (vectorMomentWeight r) (rename Sum.inl P) 0 := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using isWeightedHomogeneous_C (vectorMomentWeight r) c
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    simpa [vectorMomentWeight] using hp.mul
      (isWeightedHomogeneous_X ℝ (vectorMomentWeight r) (Sum.inl i))

private theorem vectorMoment_homogeneous (r : ℕ) (parent response : Bool) (i : Fin r) :
    IsWeightedHomogeneous (vectorMomentWeight r) (vectorMoment r parent response i) 1 := by
  exact isWeightedHomogeneous_X ℝ (vectorMomentWeight r) (Sum.inr (parent, response, i))

theorem rawNumeratorPolynomial_vector_homogeneous (r : ℕ)
    (T : Matrix (Fin r) (Fin r) ℝ) (response : Bool) (i : Fin r) :
    IsWeightedHomogeneous (vectorMomentWeight r) (rawNumeratorPolynomial r T response i) 1 := by
  unfold rawNumeratorPolynomial
  apply IsWeightedHomogeneous.sub
  · simpa using (renamed_matrix_polynomial_homogeneous r _).mul
      (vectorMoment_homogeneous r false response i)
  · apply IsWeightedHomogeneous.sum
    intro j hj
    apply IsWeightedHomogeneous.sum
    intro k hk
    apply IsWeightedHomogeneous.sum
    intro l hl
    simpa using (((renamed_matrix_polynomial_homogeneous r _).mul
      (isWeightedHomogeneous_C (vectorMomentWeight r) (T j k))).mul
      (renamed_matrix_polynomial_homogeneous r _)).mul
      (vectorMoment_homogeneous r true response l)

theorem numeratorPolynomial_vector_homogeneous (r : ℕ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (i : Fin r) :
    IsWeightedHomogeneous (vectorMomentWeight r) (numeratorPolynomial r T y i) 1 := by
  exact (rawNumeratorPolynomial_vector_homogeneous r T false i).sub
    ((rawNumeratorPolynomial_vector_homogeneous r T true i).C_mul y)

/-- Every monomial of the increment has total vector-moment degree exactly one. -/
theorem incrementEntryPolynomial_vector_homogeneous (r : ℕ) (a b : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (i : Fin r) :
    IsWeightedHomogeneous (vectorMomentWeight r) (incrementEntryPolynomial r a b T y m i) 1 := by
  apply IsWeightedHomogeneous.sum
  intro j hj
  simpa using (renamed_matrix_polynomial_homogeneous r _).mul
    (numeratorPolynomial_vector_homogeneous r T y j)

private theorem vectorMoment_weight_eq_sum (r : ℕ) (d : incrementVariables r →₀ ℕ) :
    Finsupp.weight (vectorMomentWeight r) d = ∑ v : Bool × Bool × Fin r, d (Sum.inr v) := by
  rw [Finsupp.weight_eq_sum]
  simp [Fintype.sum_sum_type, vectorMomentWeight]

/-- A supported monomial contains exactly one vector coordinate, and its exponent is one. -/
theorem incrementEntryPolynomial_vector_monomial (r : ℕ) (a b : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (i : Fin r)
    (d : incrementVariables r →₀ ℕ)
    (hd : (incrementEntryPolynomial r a b T y m i).coeff d ≠ 0) :
    ∃ v : Bool × Bool × Fin r, d (Sum.inr v) = 1 ∧
      ∀ w : Bool × Bool × Fin r, w ≠ v → d (Sum.inr w) = 0 := by
  have hs := incrementEntryPolynomial_vector_homogeneous r a b T y m i hd
  rw [vectorMoment_weight_eq_sum] at hs
  obtain ⟨v, hv, hv0⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (by rw [hs]; norm_num : (∑ v : Bool × Bool × Fin r, d (Sum.inr v)) ≠ 0)
  have hvle := Finset.single_le_sum (fun w hw => Nat.zero_le (d (Sum.inr w))) hv
  have hv1 : d (Sum.inr v) = 1 := by omega
  refine ⟨v, hv1, ?_⟩
  intro w hw
  have he := Finset.sum_erase_add (s := Finset.univ)
    (f := fun w : Bool × Bool × Fin r => d (Sum.inr w)) hv
  have herase : ∑ w ∈ (Finset.univ : Finset (Bool × Bool × Fin r)).erase v, d (Sum.inr w) = 0 := by
    rw [hs, hv1] at he
    omega
  have hwle := Finset.single_le_sum (fun w hw => Nat.zero_le (d (Sum.inr w)))
    (Finset.mem_erase.mpr ⟨hw, Finset.mem_univ w⟩)
  rw [herase] at hwle
  omega

def rawIncrementEntryPolynomial (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (response : Bool) (m : ℕ) (i : Fin r) : MvPolynomial (incrementVariables r) ℝ :=
  ∑ j, rename Sum.inl (parentInverseEntryPolynomial a b r m i j) *
    rawNumeratorPolynomial r T response j

/-- The response variable appears only affinely in the entire increment polynomial. -/
theorem incrementEntryPolynomial_affine (r : ℕ) (a b : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (i : Fin r) :
    incrementEntryPolynomial r a b T y m i =
      rawIncrementEntryPolynomial r a b T false m i - C y *
        rawIncrementEntryPolynomial r a b T true m i := by
  unfold incrementEntryPolynomial numeratorPolynomial rawIncrementEntryPolynomial
  have he (j : Fin r) :
      rename Sum.inl (parentInverseEntryPolynomial a b r m i j) *
        (C y * rawNumeratorPolynomial r T true j) =
      C y * (rename Sum.inl (parentInverseEntryPolynomial a b r m i j) *
        rawNumeratorPolynomial r T true j) := mul_left_comm _ _ _
  simp_rw [mul_sub, he]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- Consequently each monomial coefficient is constant or linear in `y`. -/
theorem incrementEntryPolynomial_coefficient_affine (r : ℕ) (a b : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (i : Fin r)
    (d : incrementVariables r →₀ ℕ) :
    (incrementEntryPolynomial r a b T y m i).coeff d =
      (rawIncrementEntryPolynomial r a b T false m i).coeff d -
        y * (rawIncrementEntryPolynomial r a b T true m i).coeff d := by
  rw [incrementEntryPolynomial_affine, coeff_sub, coeff_C_mul]

open RoughRegime.CombinedPolynomial

/-- Evaluation substitutes the current and parent Gram entries and the two vector families. -/
def incrementValuation {r : ℕ} (A C : Matrix (Fin r) (Fin r) ℝ)
    (U V : Bool → Fin r → ℝ) : incrementVariables r → ℝ
  | Sum.inl x => entryValuation A (fun _ : Fin 1 => C) x
  | Sum.inr (parent, response, i) => if parent then V response i else U response i

private theorem rawNumeratorPolynomial_eval {r : ℕ}
    (A C T : Matrix (Fin r) (Fin r) ℝ) (U V : Bool → Fin r → ℝ)
    (response : Bool) (i : Fin r) :
    eval (incrementValuation A C U V) (rawNumeratorPolynomial r T response i) =
      incrementNumerator A C T (U response) (V response) i := by
  let f := MvPolynomial.eval₂Hom (RingHom.id ℝ) (entryValuation A (fun _ : Fin 1 => C))
  have hm : f.mapMatrix (parentVariableMatrix r) = C := by
    ext j k
    simp [f, parentVariableMatrix, entryValuation, RingHom.mapMatrix_apply]
  have hd : eval (incrementValuation A C U V)
      (rename Sum.inl (parentVariableMatrix r).det) = C.det := by
    rw [MvPolynomial.eval_rename]
    change f (parentVariableMatrix r).det = C.det
    rw [f.map_det, hm]
  have ha (k l : Fin r) : eval (incrementValuation A C U V)
      (rename Sum.inl ((parentVariableMatrix r).adjugate k l)) = C.adjugate k l := by
    rw [MvPolynomial.eval_rename]
    change f ((parentVariableMatrix r).adjugate k l) = C.adjugate k l
    have h := congrArg (fun M => M k l) (f.map_adjugate (parentVariableMatrix r))
    rw [hm] at h
    exact h
  simp only [rawNumeratorPolynomial, eval_sub, eval_mul, eval_sum, eval_C, hd, ha]
  simp only [vectorMoment, eval_X, incrementValuation, Bool.false_eq_true, ↓reduceIte,
    currentVariableMatrix, rename_X, entryValuation]
  simp only [incrementNumerator, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]

/-- Evaluating the free polynomial gives exactly the paper's cleared numerator for `β-yμ`. -/
theorem numeratorPolynomial_eval {r : ℕ}
    (A C T : Matrix (Fin r) (Fin r) ℝ) (U V : Bool → Fin r → ℝ)
    (y : ℝ) (i : Fin r) :
    eval (incrementValuation A C U V) (numeratorPolynomial r T y i) =
      incrementNumerator A C T (U false - y • U true) (V false - y • V true) i := by
  rw [numeratorPolynomial, eval_sub, eval_mul, eval_C,
    rawNumeratorPolynomial_eval, rawNumeratorPolynomial_eval]
  simp only [incrementNumerator, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub, smul_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Evaluation recovers the actual fitted-increment polynomial for arbitrary free Gram matrices. -/
theorem incrementEntryPolynomial_eval {r : ℕ} (a b : ℝ)
    (A C T : Matrix (Fin r) (Fin r) ℝ) (U V : Bool → Fin r → ℝ)
    (y : ℝ) (m : ℕ) (i : Fin r) :
    eval (incrementValuation A C U V) (incrementEntryPolynomial r a b T y m i) =
      (parentInversePolynomial a b A C m).mulVec
        (incrementNumerator A C T (U false - y • U true) (V false - y • V true)) i := by
  simp only [incrementEntryPolynomial, eval_sum, eval_mul, numeratorPolynomial_eval]
  simp_rw [MvPolynomial.eval_rename]
  change ∑ j, eval (entryValuation A (fun _ : Fin 1 => C))
    (parentInverseEntryPolynomial a b r m i j) *
    incrementNumerator A C T (U false - y • U true) (V false - y • V true) j = _
  simp_rw [← parentInversePolynomial_eval]
  rfl

open scoped Matrix.Norms.L2Operator

/-- The exact polynomial propagates any explicitly supplied small-increment bound to U5(2). -/
theorem incrementEntryPolynomial_error {r : ℕ} [NeZero r]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A C T : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b)
    (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (χ : ℝ)
    (hχ : ‖(Q : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ)
    (U V : Bool → Fin r → ℝ) (y ε : ℝ)
    (hδ : ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
      ((matrixSimilarity Q A)⁻¹.mulVec (U false - y • U true) -
        T.mulVec ((matrixSimilarity R C)⁻¹.mulVec (V false - y • V true)))‖ ≤ ε)
    (m : ℕ) :
    let G := matrixSimilarity Q A
    let Cminus := matrixSimilarity R C
    ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
      ((fun i => eval (incrementValuation G Cminus U V)
          (incrementEntryPolynomial r a b T y m i)) -
        (G⁻¹.mulVec (U false - y • U true) -
          T.mulVec (Cminus⁻¹.mulVec (V false - y • V true))))‖ ≤
      (χ ^ 2 * b ^ (r + 1) * parentInverseErrorConstant a b r) * ε *
        ((m + 1 : ℕ) : ℝ) ^ r *
        Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  dsimp only
  simp_rw [incrementEntryPolynomial_eval]
  let β := U false - y • U true
  let βminus := V false - y • V true
  have hχ0 : 0 ≤ χ := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hχ
  have hb : 0 < b := ha.trans hab
  have hM := parentInverseErrorConstant_pos a b ha hab r
  have hn := increment_numerator_norm_le a b ha hab A C T hA hC hSpecA hSpecC Q R χ hχ β βminus
  dsimp only at hn
  have hsmall : ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
      (incrementNumerator (matrixSimilarity Q A) (matrixSimilarity R C) T β βminus)‖ ≤
      χ * b ^ (r + 1) * ε := hn.trans
        (mul_le_mul_of_nonneg_left hδ (by positivity))
  have he := increment_polynomial_error a b ha hab A C T hA hC hSpecA hSpecC Q R χ hχ β βminus m
  dsimp only at he
  apply he.trans
  apply (mul_le_mul_of_nonneg_left hsmall (by positivity)).trans_eq
  ring

end NearlyMinimax
