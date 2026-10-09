module

public import NearlyMinimax.HighUnionScore
public import NearlyMinimax.HighLocalFrame


@[expose] public section

/-! Disjoint-patch orthogonality and the exact torus overlap bound for the
complete marked local generator, with its variance correction counted once.
The final endpoint uses the actual polynomial field decomposition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

section GenericFamily
variable {J ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

theorem highMarkedLocalScores_orthogonal {n : ℕ}
    (π : J → Measure E) (activation : J → E → ℝ) (a V η : ℝ) (ha : a ≠ 0)
    (p : Fin n → ℝ) (pReset : J → E → Fin n → ℝ)
    (cReset : J → E → ι → ℝ) (g w : J → Fin n → ℝ)
    (φ : J → Fin n → ι → ℝ) (c : J → ι → ℝ) (f : Fin n → ℝ)
    (hreg : ∀ j, coefficientRegression η (g j) (w j) (φ j) (c j) = f)
    (S : J → Finset (Fin n)) (hw : ∀ j i, i ∉ S j → w j i = 0)
    (hpd : ∀ i, p i ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (f i) V b)
    (hInt : ∀ j y, Integrable (fun e => activation j e * (∏ i, pReset j e i) *
      highResponseProduct a V η (g j) (w j) (φ j) (cReset j e) y) (π j))
    (hDensity : ∀ j, (∫ e, activation j e * ∏ i, pReset j e i ∂π j) = 0)
    (j l : J) (hST : Disjoint (S j) (S l)) :
    (∫ y, highMarkedLocalScore (π j) (activation j) a V η p (pReset j) (cReset j)
      (g j) (w j) (φ j) (c j) y *
      highMarkedLocalScore (π l) (activation l) a V η p (pReset l) (cReset l)
        (g l) (w l) (φ l) (c l) y
      ∂Measure.pi (fun i => ternaryIndexMeasure a (f i) V ha (fun b => (hp i b).le))) = 0 := by
  let μ : Fin n → Measure (Fin 3) := fun i =>
    ternaryIndexMeasure a (f i) V ha (fun b => (hp i b).le)
  have hp' (j : J) (i : Fin n) (b : Fin 3) :
      0 < ternaryMass a (coefficientRegression η (g j) (w j) (φ j) (c j) i) V b := by
    rw [hreg j]
    exact hp i b
  apply local_response_scores_orthogonal μ _ _ (S j) (S l) hST
  · intro y y' hyy
    exact highMarkedLocalScore_depends_on_support (π j) (activation j) a V η p
      (pReset j) (cReset j) (g j) (w j) (φ j) (c j) (S j) (hw j) y y' hyy hpd (hp' j)
  · intro y y' hyy
    exact highMarkedLocalScore_depends_on_support (π l) (activation l) a V η p
      (pReset l) (cReset l) (g l) (w l) (φ l) (c l) (S l) (hw l) y y' hyy hpd (hp' l)
  · have h := highMarkedLocalScore_centered (π j) (activation j) a V η ha p
      (pReset j) (cReset j) (g j) (w j) (φ j) (c j) hpd (hp' j) (hInt j) (hDensity j)
    simpa only [hreg j] using h

end GenericFamily

section ActualField
variable {E : Type*} [MeasurableSpace E]

def highFrameMarkedScore (d k D n : ℕ) [NeZero k]
    (π : HighWindowLabels d k → Measure E)
    (activation : HighWindowLabels d k → E → ℝ) (a V η : ℝ) (p : Fin n → ℝ)
    (pReset : HighWindowLabels d k → E → Fin n → ℝ)
    (cReset : HighWindowLabels d k → E → HighFrameIndex d D → ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (x : Fin n → Covariate d)
    (j : HighWindowLabels d k) (y : Fin n → Fin 3) : ℝ :=
  highMarkedLocalScore (π j) (activation j) a V η p (pReset j) (cReset j)
    (fun i => highLocalFieldWithout d k D η c j (x i))
    (fun i => highPeriodicTensor d k j (x i))
    (fun i => highLocalFrameFeature k j (x i)) (c j) y

/-- Conditional orthogonality of the true complete signed-generator scores
is proved from actual response normalization, conditional density zero mass,
and the original window supports. -/
theorem highFrameMarkedScore_orthogonal (d k D n : ℕ) [NeZero k] (hk : 4 ≤ k)
    (π : HighWindowLabels d k → Measure E)
    (activation : HighWindowLabels d k → E → ℝ) (hAct : ∀ j, Integrable (activation j) (π j))
    (a V η pPlus : ℝ) (ha : a ≠ 0) (hpPlus : 0 ≤ pPlus) (p : Fin n → ℝ)
    (pReset : HighWindowLabels d k → E → Fin n → ℝ)
    (hReset : ∀ j i, Measurable (fun e => pReset j e i))
    (hBound : ∀ j e i, |pReset j e i| ≤ pPlus)
    (cReset : HighWindowLabels d k → E → HighFrameIndex d D → ℝ)
    (hcReset : ∀ j γ, Measurable (fun e => cReset j e γ))
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (x : Fin n → Covariate d)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a
      (highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)) V b)
    (hpReset : ∀ j e i b, 0 ≤ ternaryMass a
      (coefficientRegression η (fun i => highLocalFieldWithout d k D η c j (x i))
        (fun i => highPeriodicTensor d k j (x i))
        (fun i => highLocalFrameFeature k j (x i)) (cReset j e) i) V b)
    (hDensity : ∀ j, (∫ e, activation j e * ∏ i, pReset j e i ∂π j) = 0)
    (j l : HighWindowLabels d k) (hjl : l ∉ highNeighborLabels d k j) :
    (∫ y, highFrameMarkedScore d k D n π activation a V η p pReset cReset c x j y *
      highFrameMarkedScore d k D n π activation a V η p pReset cReset c x l y
      ∂Measure.pi (fun i => ternaryIndexMeasure a
        (highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)) V
        ha (fun b => (hp i b).le))) = 0 := by
  exact highMarkedLocalScores_orthogonal π activation a V η ha p pReset cReset
    (fun j i => highLocalFieldWithout d k D η c j (x i))
    (fun j i => highPeriodicTensor d k j (x i))
    (fun j i => highLocalFrameFeature k j (x i)) c
    (fun i => highFrameField d k η (fun l => highFramePolynomial (c l)) (x i))
    (fun j => highFrameField_coefficientRegression d k D n hk η c j x)
    (fun j => highPatchSampleIndices d k n j x)
    (fun j i hi => highPeriodicTensor_sample_zero_outside_patch d k n j x i hi)
    hpd hp (fun j y => highMarkedResponseAction_integrable (π j) (activation j) (hAct j)
      a V η ha pPlus hpPlus (pReset j) (hReset j) (hBound j) (cReset j) (hcReset j)
      _ _ _ (hpReset j) y) hDensity j l
    (highPatchSampleIndices_disjoint d k n x j l hjl)

/-- The exact source overlap factor is established for the complete union
score, after the single variance correction and the genuine local field
decomposition. No covariance or score-energy bound is a premise. -/
theorem highFrameMarkedScore_energy_bound (d k D n : ℕ) [NeZero k] (hk : 4 ≤ k)
    (π : HighWindowLabels d k → Measure E)
    (activation : HighWindowLabels d k → E → ℝ) (hAct : ∀ j, Integrable (activation j) (π j))
    (a V η pPlus : ℝ) (ha : a ≠ 0) (hpPlus : 0 ≤ pPlus) (p : Fin n → ℝ)
    (pReset : HighWindowLabels d k → E → Fin n → ℝ)
    (hReset : ∀ j i, Measurable (fun e => pReset j e i))
    (hBound : ∀ j e i, |pReset j e i| ≤ pPlus)
    (cReset : HighWindowLabels d k → E → HighFrameIndex d D → ℝ)
    (hcReset : ∀ j γ, Measurable (fun e => cReset j e γ))
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (x : Fin n → Covariate d)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a
      (highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)) V b)
    (hpReset : ∀ j e i b, 0 ≤ ternaryMass a
      (coefficientRegression η (fun i => highLocalFieldWithout d k D η c j (x i))
        (fun i => highPeriodicTensor d k j (x i))
        (fun i => highLocalFrameFeature k j (x i)) (cReset j e) i) V b)
    (hDensity : ∀ j, (∫ e, activation j e * ∏ i, pReset j e i ∂π j) = 0) :
    (∫ y, (∑ j, highFrameMarkedScore d k D n π activation a V η p pReset cReset c x j y)^2
      ∂Measure.pi (fun i => ternaryIndexMeasure a
        (highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)) V
        ha (fun b => (hp i b).le))) ≤
      (3^d : ℕ) * ∑ j, ∫ y,
        (highFrameMarkedScore d k D n π activation a V η p pReset cReset c x j y)^2
        ∂Measure.pi (fun i => ternaryIndexMeasure a
          (highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)) V
          ha (fun b => (hp i b).le)) := by
  apply finite_overlap_variance_bound _
    (highFrameMarkedScore d k D n π activation a V η p pReset cReset c x)
    (fun j l => l ∈ highNeighborLabels d k j) (3^d)
  · intro j l
    exact ⟨highNeighborLabels_symmetric d k j l, highNeighborLabels_symmetric d k l j⟩
  · intro j
    convert highNeighborLabels_card_le d k j using 1
    congr 1
    ext l
    simp
  · intro j l hjl
    exact highFrameMarkedScore_orthogonal d k D n hk π activation hAct a V η pPlus ha hpPlus
      p pReset hReset hBound cReset hcReset c x hpd hp hpReset hDensity j l hjl

end ActualField
end NearlyMinimax
