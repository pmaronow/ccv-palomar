module

public import NearlyMinimax.DyadicPilotFeatures


@[expose] public section

/-! Exact linear-coordinate representation of the actual local raw pilot
using one fixed finite global feature vector for all anchors at a level. -/

noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def pilotPolynomialLinear {q d ℓ : ℕ} (c : Fin q) (P : MvPolynomial (Fin d) ℝ)
    (response : Bool) : (Fin (Fintype.card (PilotBasisIndex q d ℓ)) → ℝ) →L[ℝ] ℝ :=
  ∑ β : PolynomialBox d ℓ, P.coeff (polynomialBoxExponent β) •
    ContinuousLinearMap.proj ((Fintype.equivFin (PilotBasisIndex q d ℓ)) ((c, β), response))

/-- A polynomial with a design-cell indicator and an optional response factor
is exactly a continuous linear function of the finite global coordinates. -/
theorem pilotPolynomialLinear_raw_apply {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (c : Fin q) (P : MvPolynomial (Fin d) ℝ) (hP : P.totalDegree ≤ ℓ)
    (response : Bool) (z : Observation d) :
    pilotPolynomialLinear (ℓ := ℓ) c P response (pilotRawVector cell z) =
      if cell z.1 = c then eval z.1 P * (if response then z.2 else 1) else 0 := by
  classical
  simp only [pilotPolynomialLinear, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, pilotRawVector, Equiv.symm_apply_apply, smul_eq_mul,
    pilotBasisFeature]
  by_cases h : cell z.1 = c
  · simp only [h, ite_true, ← mul_assoc, ← Finset.sum_mul]
    rw [polynomial_box_evaluation P hP]
    rfl
  · simp [h]

abbrev DyadicPilotLabelIndex (d j : ℕ) := Fin d → Fin ((2 : ℕ) ^ j)

def dyadicPilotLabel {d : ℕ} (j : ℕ) (x : Covariate d) :
    Fin (Fintype.card (DyadicPilotLabelIndex d j)) :=
  Fintype.equivFin (DyadicPilotLabelIndex d j)
    (regularGridCell ((2 : ℕ) ^ j) (by positivity) x)

theorem dyadicPilotLabel_measurable {d : ℕ} (j : ℕ) :
    Measurable (dyadicPilotLabel (d := d) j) :=
  (measurable_of_countable _).comp (regular_grid_cell_measurable _ _)

theorem dyadicPilotLabel_eq_iff {d : ℕ} (j : ℕ) (x z : Covariate d) :
    dyadicPilotLabel j z = dyadicPilotLabel j x ↔ z ∈ dyadicPilotCell j x :=
  (Fintype.equivFin (DyadicPilotLabelIndex d j)).injective.eq_iff

def dyadicPilotPolynomial {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) : MvPolynomial (Fin d) ℝ :=
  match a with
  | Sum.inl (γ, δ) => dyadicFeaturePolynomial j x γ * dyadicFeaturePolynomial j x δ
  | Sum.inr (Sum.inl γ) => dyadicFeaturePolynomial j x γ
  | Sum.inr (Sum.inr γ) => dyadicFeaturePolynomial j x γ

def dyadicPilotResponse {d ℓ : ℕ} (a : LocalPilotIndex d ℓ) : Bool :=
  match a with
  | Sum.inl _ => false
  | Sum.inr (Sum.inl _) => true
  | Sum.inr (Sum.inr _) => false

theorem dyadicPilotPolynomial_degree {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) : (dyadicPilotPolynomial j x a).totalDegree ≤ 2 * ℓ := by
  cases a with
  | inl a =>
    exact (MvPolynomial.totalDegree_mul _ _).trans
      ((Nat.add_le_add (dyadicFeaturePolynomial_degree j x a.1)
        (dyadicFeaturePolynomial_degree j x a.2)).trans_eq (by omega))
  | inr a =>
    cases a <;> exact (dyadicFeaturePolynomial_degree j x _).trans (by omega)

theorem dyadicPilotPolynomial_scalar {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) :
    eval z.1 (dyadicPilotPolynomial j x a) * (if dyadicPilotResponse a then z.2 else 1) =
      dyadicPilotScalar j x a z := by
  cases a with
  | inl a => simp [dyadicPilotPolynomial, dyadicPilotResponse, dyadicPilotScalar,
      dyadicFeaturePolynomial_eval]
  | inr a =>
    cases a <;> simp [dyadicPilotPolynomial, dyadicPilotResponse, dyadicPilotScalar,
      dyadicFeaturePolynomial_eval, mul_comm]

def dyadicPilotCoordinate {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) :
    (Fin (Fintype.card (PilotBasisIndex (Fintype.card (DyadicPilotLabelIndex d j)) d (2 * ℓ))) → ℝ) →L[ℝ] ℝ :=
  dyadicPilotScale d j • pilotPolynomialLinear (dyadicPilotLabel j x)
    (dyadicPilotPolynomial j x a) (dyadicPilotResponse a)

/-- The exact raw current-cell feature is represented for every anchor and
observation by the same global feature vector. No moment equality is assumed. -/
theorem dyadicPilotCoordinate_raw_apply {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) :
    dyadicPilotCoordinate j x a (pilotRawVector (dyadicPilotLabel j) z) =
      dyadicPilotFeature j x a z := by
  rw [dyadicPilotCoordinate, ContinuousLinearMap.smul_apply,
    pilotPolynomialLinear_raw_apply _ _ _ (dyadicPilotPolynomial_degree j x a)]
  simp only [smul_eq_mul, dyadicPilotLabel_eq_iff, dyadicPilotPolynomial_scalar,
    dyadicPilotFeature]
  by_cases h : z.1 ∈ dyadicPilotCell j x
  · have he := (dyadicPilotLabel_eq_iff j x z.1).mpr h
    simp [h, he]
  · have he : dyadicPilotLabel j z.1 ≠ dyadicPilotLabel j x :=
      fun he => h ((dyadicPilotLabel_eq_iff j x z.1).mp he)
    simp [h, he]

def dyadicPilotCoordinateMap {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    (Fin (Fintype.card (PilotBasisIndex (Fintype.card (DyadicPilotLabelIndex d j)) d (2 * ℓ))) → ℝ)
      →L[ℝ] (LocalPilotIndex d ℓ → ℝ) :=
  ContinuousLinearMap.pi (fun a => dyadicPilotCoordinate j x a)

theorem dyadicPilotCoordinateMap_raw_apply {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (z : Observation d) :
    dyadicPilotCoordinateMap j x (pilotRawVector (dyadicPilotLabel j) z) =
      fun a : LocalPilotIndex d ℓ => dyadicPilotFeature j x a z := by
  funext a
  exact dyadicPilotCoordinate_raw_apply j x a z

/-- The actual local population moments are the same linear image of the
genuine global-feature mean used by spatial covariance bounds. -/
theorem dyadicPilotCoordinate_population {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) :
    dyadicPilotCoordinate j x a (pilotRawMean θ (dyadicPilotLabel j)) =
      dyadicPilotPopulation θ j x a := by
  classical
  let := observationLaw_isProbability C θ hθ
  unfold dyadicPilotCoordinate pilotPolynomialLinear
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hi (β : PolynomialBox d (2 * ℓ)) :=
    pilotBasisFeature_memLp_two C θ hθ (dyadicPilotLabel j)
      (dyadicPilotLabel_measurable j) ((dyadicPilotLabel j x, β), dyadicPilotResponse a)
  have heq : (fun z : Observation d => dyadicPilotFeature j x a z) =
      (fun z => dyadicPilotScale d j * ∑ β : PolynomialBox d (2 * ℓ),
        (dyadicPilotPolynomial j x a).coeff (polynomialBoxExponent β) *
          pilotBasisFeature (dyadicPilotLabel j) ((dyadicPilotLabel j x, β), dyadicPilotResponse a) z) := by
    funext z
    rw [← dyadicPilotCoordinate_raw_apply j x a z]
    simp only [dyadicPilotCoordinate, pilotPolynomialLinear, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.proj_apply, pilotRawVector,
      Equiv.symm_apply_apply, smul_eq_mul]
  unfold dyadicPilotPopulation
  rw [heq, integral_const_mul, integral_finsetSum _ (fun β _ => (hi β).integrable
    (by norm_num) |>.const_mul _)]
  simp only [pilotRawMean, pilotRawVector, Equiv.symm_apply_apply, integral_const_mul]

end NearlyMinimax
