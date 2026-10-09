module

public import NearlyMinimax.HighScoreOrthogonality


@[expose] public section

/-! The actual high window graph yields disjoint-score orthogonality and
the manuscript's factor `3^d` under the genuine conditional response law.
Outer representation integrability is proved from matrix cost and legal
bounded density resets. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

section
variable {ι E Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [MeasurableSpace Z]

def highTorusIntegratedScore (d k n : ℕ) (σ : HighWindowLabels d k → Measure Z)
    (q : HighWindowLabels d k → ℕ) (C a V η : ℝ)
    (weights : HighWindowLabels d k → E → ℝ)
    (A : HighWindowLabels d k → Z → ι → ι → ℝ) (p : Fin n → ℝ)
    (pReset : HighWindowLabels d k → Z → E → Fin n → ℝ)
    (g : HighWindowLabels d k → Fin n → ℝ)
    (φ : HighWindowLabels d k → Fin n → ι → ℝ)
    (c : HighWindowLabels d k → ι → ℝ) (x : Fin n → Covariate d)
    (j : HighWindowLabels d k) (y : Fin n → Fin 3) : ℝ :=
  highIntegratedLocalScore (σ j) (q j) C a V η (fun _ => weights j)
    (fun ζ _ => A j ζ) p (pReset j) (g j)
    (fun i => highPeriodicTensor d k j (x i)) (φ j) (c j) y

theorem highTorusIntegratedScores_orthogonal (d k n : ℕ) [NeZero k]
    (σ : HighWindowLabels d k → Measure Z) (q : HighWindowLabels d k → ℕ)
    (C a V η pPlus : ℝ) (ha : a ≠ 0) (hpPlus : 0 ≤ pPlus)
    (weights : HighWindowLabels d k → E → ℝ)
    (A : HighWindowLabels d k → Z → ι → ι → ℝ) (p : Fin n → ℝ)
    (pReset : HighWindowLabels d k → Z → E → Fin n → ℝ)
    (g : HighWindowLabels d k → Fin n → ℝ)
    (φ : HighWindowLabels d k → Fin n → ι → ℝ)
    (c : HighWindowLabels d k → ι → ℝ) (x : Fin n → Covariate d)
    (f : Fin n → ℝ)
    (hreg : ∀ j, coefficientRegression η (g j)
      (fun i => highPeriodicTensor d k j (x i)) (φ j) (c j) = f)
    (hpd : ∀ i, p i ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (f i) V b)
    (hA : ∀ j i l, Measurable (fun ζ => A j ζ i l))
    (hcost : ∀ j, Integrable (separatedMatrixCost (A j)) (σ j))
    (hReset : ∀ j e i, Measurable (fun ζ => pReset j ζ e i))
    (hBound : ∀ j ζ e i, |pReset j ζ e i| ≤ pPlus)
    (j l : HighWindowLabels d k) (hjl : l ∉ highNeighborLabels d k j) :
    (∫ y, highTorusIntegratedScore d k n σ q C a V η weights A p pReset g φ c x j y *
      highTorusIntegratedScore d k n σ q C a V η weights A p pReset g φ c x l y
      ∂Measure.pi (fun i => ternaryIndexMeasure a (f i) V ha (fun b => (hp i b).le))) = 0 := by
  exact high_integrated_packet_scores_orthogonal σ q C a V η ha
    (fun j _ => weights j) (fun j ζ _ => A j ζ) p pReset g
    (fun j i => highPeriodicTensor d k j (x i)) φ c f hreg
    (fun j => highPatchSampleIndices d k n j x)
    (fun j i hi => highPeriodicTensor_sample_zero_outside_patch d k n j x i hi)
    hpd hp (fun j y => high_separated_density_response_action_integrable (σ j) (q j) C
      (weights j) (A j) (pReset j) (c j)
      (fun v => highResponseProduct a V η (g j)
        (fun i => highPeriodicTensor d k j (x i)) (φ j) v y)
      (hA j) (hcost j) (hReset j) pPlus hpPlus (hBound j)) j l
    (highPatchSampleIndices_disjoint d k n x j l hjl)

/-- The global conditional Fisher energy bound has the actual torus overlap
constant. Disjoint-score covariance is proved above from the response law. -/
theorem highTorusIntegratedScores_variance_bound (d k n : ℕ) [NeZero k]
    (σ : HighWindowLabels d k → Measure Z) (q : HighWindowLabels d k → ℕ)
    (C a V η pPlus : ℝ) (ha : a ≠ 0) (hpPlus : 0 ≤ pPlus)
    (weights : HighWindowLabels d k → E → ℝ)
    (A : HighWindowLabels d k → Z → ι → ι → ℝ) (p : Fin n → ℝ)
    (pReset : HighWindowLabels d k → Z → E → Fin n → ℝ)
    (g : HighWindowLabels d k → Fin n → ℝ)
    (φ : HighWindowLabels d k → Fin n → ι → ℝ)
    (c : HighWindowLabels d k → ι → ℝ) (x : Fin n → Covariate d)
    (f : Fin n → ℝ)
    (hreg : ∀ j, coefficientRegression η (g j)
      (fun i => highPeriodicTensor d k j (x i)) (φ j) (c j) = f)
    (hpd : ∀ i, p i ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (f i) V b)
    (hA : ∀ j i l, Measurable (fun ζ => A j ζ i l))
    (hcost : ∀ j, Integrable (separatedMatrixCost (A j)) (σ j))
    (hReset : ∀ j e i, Measurable (fun ζ => pReset j ζ e i))
    (hBound : ∀ j ζ e i, |pReset j ζ e i| ≤ pPlus) :
    (∫ y, (∑ j, highTorusIntegratedScore d k n σ q C a V η weights A p pReset g φ c x j y)^2
      ∂Measure.pi (fun i => ternaryIndexMeasure a (f i) V ha (fun b => (hp i b).le))) ≤
    (3^d : ℕ) * ∑ j, ∫ y,
      (highTorusIntegratedScore d k n σ q C a V η weights A p pReset g φ c x j y)^2
      ∂Measure.pi (fun i => ternaryIndexMeasure a (f i) V ha (fun b => (hp i b).le)) := by
  apply finite_overlap_variance_bound _
    (highTorusIntegratedScore d k n σ q C a V η weights A p pReset g φ c x)
    (fun j l => l ∈ highNeighborLabels d k j) (3^d)
  · intro j l
    exact ⟨highNeighborLabels_symmetric d k j l, highNeighborLabels_symmetric d k l j⟩
  · intro j
    convert highNeighborLabels_card_le d k j using 1
    congr 1
    ext l
    simp
  · intro j l hjl
    exact highTorusIntegratedScores_orthogonal d k n σ q C a V η pPlus ha hpPlus
      weights A p pReset g φ c x f hreg hpd hp hA hcost hReset hBound j l hjl

end
end NearlyMinimax
