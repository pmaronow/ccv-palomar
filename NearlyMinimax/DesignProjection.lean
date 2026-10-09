module

public import NearlyMinimax.Projection


@[expose] public section

open Matrix MeasureTheory
open scoped BigOperators

noncomputable section
namespace NearlyMinimax

/-- Matrices use their finite product Borel structure. -/
instance designMatrixMeasurableSpace {ι κ : Type*} : MeasurableSpace (Matrix ι κ ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → κ → ℝ))

instance designMatrixMeasurableAdd {ι κ : Type*} : MeasurableAdd₂ (Matrix ι κ ℝ) :=
  inferInstanceAs (MeasurableAdd₂ (ι → κ → ℝ))

instance designMatrixMeasurableSub {ι κ : Type*} : MeasurableSub₂ (Matrix ι κ ℝ) :=
  inferInstanceAs (MeasurableSub₂ (ι → κ → ℝ))

instance designMatrixBorelSpace {ι κ : Type*} [Fintype ι] [Fintype κ] :
    BorelSpace (Matrix ι κ ℝ) := inferInstanceAs (BorelSpace (ι → κ → ℝ))

/-- An exact Gram–Schmidt projection update.  Real inversion returns
zero at a zero residual, so this also handles dependent columns. -/
def designProjectionUpdate {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (v : ι → ℝ) : Matrix ι ι ℝ :=
  let r := v - P *ᵥ v
  P + (projectionEnergy r)⁻¹ • vecMulVec r r

/-- A rank-safe Gram–Schmidt projection onto a list of design columns. -/
def designListProjection {ι : Type*} [Fintype ι] : List (ι → ℝ) → Matrix ι ι ℝ
  | [] => 0
  | v :: vs => designProjectionUpdate (designListProjection vs) v

/-- The new residual is in the kernel of the old projection. -/
theorem design_update_residual_killed {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hidem : P * P = P) (v : ι → ℝ) :
    P *ᵥ (v - P *ᵥ v) = 0 := by
  rw [mulVec_sub, mulVec_mulVec, hidem, sub_self]

/-- Every Gram–Schmidt update preserves symmetry. -/
theorem design_update_symmetric {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hsym : Pᵀ = P) (v : ι → ℝ) :
    (designProjectionUpdate P v)ᵀ = designProjectionUpdate P v := by
  simp only [designProjectionUpdate, transpose_add, transpose_smul, transpose_vecMulVec, hsym]

/-- The inverse coefficient is correct even when the residual vanishes. -/
theorem design_inverse_energy_identity (e : ℝ) : e⁻¹ * (e⁻¹ * e) = e⁻¹ := by
  by_cases he : e = 0
  · simp [he]
  · field_simp

/-- Every Gram–Schmidt update preserves idempotence, including a zero
or linearly dependent design column. -/
theorem design_update_idempotent {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hsym : Pᵀ = P) (hidem : P * P = P) (v : ι → ℝ) :
    designProjectionUpdate P v * designProjectionUpdate P v = designProjectionUpdate P v := by
  let r := v - P *ᵥ v
  have hr : P *ᵥ r = 0 := design_update_residual_killed P hidem v
  have hPr : P * vecMulVec r r = 0 := by rw [mul_vecMulVec, hr, zero_vecMulVec]
  have hrP : vecMulVec r r * P = 0 := by
    rw [vecMulVec_mul, ← mulVec_transpose, hsym, hr, vecMulVec_zero]
  have hrr : vecMulVec r r * vecMulVec r r = projectionEnergy r • vecMulVec r r := by
    rw [vecMulVec_mul_vecMulVec]
    ext i j
    simp only [vecMulVec_apply, projectionEnergy, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  change (P + (projectionEnergy r)⁻¹ • vecMulVec r r) *
    (P + (projectionEnergy r)⁻¹ • vecMulVec r r) = P + (projectionEnergy r)⁻¹ • vecMulVec r r
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hidem,
    Matrix.mul_smul, hPr, smul_zero, add_zero, Matrix.smul_mul, hrP, smul_zero,
    Matrix.smul_mul, Matrix.mul_smul, hrr, smul_smul, smul_smul]
  rw [zero_add, mul_assoc, design_inverse_energy_identity]

/-- Updating leaves every previously fitted vector fixed. -/
theorem design_update_preserves_fixed {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hsym : Pᵀ = P) (hidem : P * P = P)
    (v q : ι → ℝ) (hq : P *ᵥ q = q) : designProjectionUpdate P v *ᵥ q = q := by
  let r := v - P *ᵥ v
  have hr : P *ᵥ r = 0 := design_update_residual_killed P hidem v
  have hd : r ⬝ᵥ q = 0 := by
    calc
      r ⬝ᵥ q = r ⬝ᵥ (P *ᵥ q) := by rw [hq]
      _ = (P *ᵥ r) ⬝ᵥ q := by rw [dotProduct_mulVec, ← mulVec_transpose, hsym]
      _ = 0 := by rw [hr, zero_dotProduct]
  change (P + (projectionEnergy r)⁻¹ • vecMulVec r r) *ᵥ q = q
  rw [add_mulVec, hq, smul_mulVec, vecMulVec_mulVec, hd, MulOpposite.op_zero,
    zero_smul, smul_zero, add_zero]

/-- The updated projection fixes the newly supplied column as well. -/
theorem design_update_fixes_new {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hsym : Pᵀ = P) (hidem : P * P = P) (v : ι → ℝ) :
    designProjectionUpdate P v *ᵥ v = v := by
  let r := v - P *ᵥ v
  have hr : P *ᵥ r = 0 := design_update_residual_killed P hidem v
  have horth : r ⬝ᵥ (P *ᵥ v) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, hr, zero_dotProduct]
  have hv : v = P *ᵥ v + r := by dsimp [r]; abel
  have hd : r ⬝ᵥ v = projectionEnergy r := by
    conv_lhs => rw [hv]
    rw [dotProduct_add, horth, zero_add]
    rfl
  change (P + (projectionEnergy r)⁻¹ • vecMulVec r r) *ᵥ v = v
  rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, hd, smul_smul]
  by_cases he : projectionEnergy r = 0
  · have hrzero : r = 0 := dotProduct_self_eq_zero.mp he
    rw [hrzero, smul_zero]
    simpa [hrzero] using hv.symm
  · rw [inv_mul_cancel₀ he, one_smul]
    exact hv.symm

/-- Updating uses only vectors in the existing range and the newly
supplied column, so it preserves membership in their span. -/
theorem design_update_range {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (v : ι → ℝ) (K : Submodule ℝ (ι → ℝ))
    (hP : ∀ x, P *ᵥ x ∈ K) (hv : v ∈ K) :
    ∀ x, designProjectionUpdate P v *ᵥ x ∈ K := by
  intro x
  have hr : v - P *ᵥ v ∈ K := K.sub_mem hv (hP v)
  unfold designProjectionUpdate
  rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  exact K.add_mem (hP x) (K.smul_mem _ (K.smul_mem _ hr))

/-- Span of the supplied design vectors. -/
def designListSpan {ι : Type*} [Fintype ι] (vs : List (ι → ℝ)) : Submodule ℝ (ι → ℝ) :=
  Submodule.span ℝ {v | v ∈ vs}

/-- The recursively constructed matrix is the genuine orthogonal
projection onto the design span, including dependent or zero columns. -/
theorem design_list_projection_spec {ι : Type*} [Fintype ι]
    (vs : List (ι → ℝ)) :
    (designListProjection vs)ᵀ = designListProjection vs ∧
    designListProjection vs * designListProjection vs = designListProjection vs ∧
    (∀ v ∈ vs, designListProjection vs *ᵥ v = v) ∧
    (∀ x, designListProjection vs *ᵥ x ∈ designListSpan vs) := by
  induction vs with
  | nil =>
    refine ⟨by simp [designListProjection], by simp [designListProjection], ?_, ?_⟩
    · intro v hv
      simp at hv
    · intro x
      simp [designListProjection]
  | cons v vs ih =>
    obtain ⟨hsym, hidem, hfix, hrange⟩ := ih
    have hspan : designListSpan vs ≤ designListSpan (v :: vs) := by
      apply Submodule.span_mono
      intro w hw
      exact List.mem_cons_of_mem v hw
    have hvspan : v ∈ designListSpan (v :: vs) :=
      Submodule.subset_span (List.mem_cons_self)
    refine ⟨design_update_symmetric _ hsym v, design_update_idempotent _ hsym hidem v, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with heq | hq
      · subst q
        exact design_update_fixes_new _ hsym hidem v
      · exact design_update_preserves_fixed _ hsym hidem v q (hfix q hq)
    · exact design_update_range _ v _ (fun x => hspan (hrange x)) hvspan

/-- A canonical exact empirical projection constructed by rank-safe
Gram–Schmidt on the design columns. -/
def empiricalDesignProjection {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix ι κ ℝ) : Matrix ι ι ℝ :=
  designListProjection (Finset.univ.toList.map B.col)

/-- The vector span used by the construction is precisely the design
matrix's column range. -/
theorem empirical_design_span {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix ι κ ℝ) :
    designListSpan (Finset.univ.toList.map B.col) = LinearMap.range B.mulVecLin := by
  rw [Matrix.range_mulVecLin]
  unfold designListSpan
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    Set.mem_range]

/-- The measurable construction has all the algebraic projection
properties, and its range is exactly the design column range. -/
theorem empirical_design_projection_spec {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (B : Matrix ι κ ℝ) :
    (empiricalDesignProjection B)ᵀ = empiricalDesignProjection B ∧
    empiricalDesignProjection B * empiricalDesignProjection B = empiricalDesignProjection B ∧
    LinearMap.range (empiricalDesignProjection B).mulVecLin = LinearMap.range B.mulVecLin := by
  obtain ⟨hsym, hidem, hfix, hrange⟩ :=
    design_list_projection_spec (Finset.univ.toList.map B.col)
  refine ⟨hsym, hidem, le_antisymm ?_ ?_⟩
  · intro v hv
    rcases hv with ⟨x, rfl⟩
    rw [← empirical_design_span B]
    exact hrange x
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro v ⟨j, rfl⟩
    exact ⟨B.col j, hfix (B.col j) (List.mem_map.mpr ⟨j, by simp, rfl⟩)⟩

/-- The exact residual retains at least sample size minus design-column
count degrees of freedom even if the design matrix is rank deficient. -/
theorem empirical_design_residual_degrees {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (B : Matrix ι κ ℝ) :
    (Fintype.card ι : ℝ) - Fintype.card κ ≤ (1 - empiricalDesignProjection B).trace := by
  have hs := empirical_design_projection_spec B
  exact projection_degrees_of_freedom_bound _ B hs.2.1 hs.2.2.le

/-- Matrix-vector evaluation is measurable entry by entry. -/
theorem design_measurable_mulVec {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (P : X → Matrix ι ι ℝ) (v : X → ι → ℝ) (hP : Measurable P) (hv : Measurable v) :
    Measurable (fun x => P x *ᵥ v x) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold mulVec dotProduct
  apply Finset.measurable_sum
  intro j hj
  exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hP))).mul
    ((measurable_pi_apply j).comp hv)

/-- Euclidean squared length is a measurable statistic. -/
theorem design_measurable_energy {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (v : X → ι → ℝ) (hv : Measurable v) : Measurable (fun x => projectionEnergy (v x)) := by
  unfold projectionEnergy dotProduct
  apply Finset.measurable_sum
  intro i hi
  exact ((measurable_pi_apply i).comp hv).mul ((measurable_pi_apply i).comp hv)

/-- Rank-safe Gram–Schmidt is Borel at a vanishing residual: its scalar
inverse is the measurable real inverse, including its value zero at zero. -/
theorem design_update_measurable {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (P : X → Matrix ι ι ℝ) (v : X → ι → ℝ) (hP : Measurable P) (hv : Measurable v) :
    Measurable (fun x => designProjectionUpdate (P x) (v x)) := by
  have hr : Measurable (fun x => v x - P x *ᵥ v x) :=
    hv.sub (design_measurable_mulVec P v hP hv)
  have he := design_measurable_energy (fun x => v x - P x *ᵥ v x) hr
  have hout : Measurable (fun x => vecMulVec (v x - P x *ᵥ v x) (v x - P x *ᵥ v x)) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact ((measurable_pi_apply i).comp hr).mul ((measurable_pi_apply j).comp hr)
  exact hP.add (he.inv.smul hout)

/-- A finite sequence of measurable design columns produces a
measurable orthogonal projection without any constant-rank restriction. -/
theorem design_list_projection_measurable {X ι κ : Type*}
    [MeasurableSpace X] [Fintype ι] (vs : List κ) (v : κ → X → ι → ℝ)
    (hv : ∀ j, Measurable (v j)) :
    Measurable (fun x => designListProjection (vs.map (fun j => v j x))) := by
  induction vs with
  | nil => exact measurable_const
  | cons j vs ih =>
    exact design_update_measurable (fun x => designListProjection (vs.map (fun j => v j x)))
      (v j) ih (hv j)

/-- The actual empirical column-space projection is Borel even where
the design matrix changes rank. -/
theorem empirical_design_projection_measurable {X ι κ : Type*}
    [MeasurableSpace X] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : X → Matrix ι κ ℝ) (hB : Measurable B) :
    Measurable (fun x => empiricalDesignProjection (B x)) := by
  apply design_list_projection_measurable Finset.univ.toList
    (fun j x => (B x).col j)
  intro j
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hB)

/-- The corresponding real-valued residual estimator is Borel as a
function of both the design and response data, at every design rank. -/
theorem empirical_residual_estimator_measurable {X ι κ : Type*}
    [MeasurableSpace X] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : X → Matrix ι κ ℝ) (Y : X → ι → ℝ) (hB : Measurable B) (hY : Measurable Y) :
    Measurable (fun x => projectionEstimator (1 - empiricalDesignProjection (B x)) (Y x)) := by
  let A : X → Matrix ι ι ℝ := fun x => 1 - empiricalDesignProjection (B x)
  have hA : Measurable A := measurable_const.sub (empirical_design_projection_measurable B hB)
  have hAY := design_measurable_mulVec A Y hA hY
  have hnum : Measurable (fun x => projectionQuadratic (A x) (Y x)) := by
    unfold projectionQuadratic dotProduct
    apply Finset.measurable_sum
    intro i hi
    exact ((measurable_pi_apply i).comp hY).mul ((measurable_pi_apply i).comp hAY)
  have htrace : Measurable (fun x => (A x).trace) := by
    unfold trace diag
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hA)
  exact hnum.div htrace

end NearlyMinimax
