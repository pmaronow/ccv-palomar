module

public import NearlyMinimax.HighLocalFrame


@[expose] public section

/-! Conditional Fisher energy for the actual source periodic polynomial field.
The local likelihood decomposition is proved by HighLocalFrame, so the final
endpoint has no decomposition or covariance conclusion among its hypotheses. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

section
variable {Z : Type*} [MeasurableSpace Z]

def highFrameXiScore (d k D n : ℕ) [NeZero k]
    (σ : HighWindowLabels d k → Measure Z) (ad bd : ℝ) (m r : ℕ)
    (q : HighWindowLabels d k → ℕ) (C a V η : ℝ)
    (A : HighWindowLabels d k → Z → HighFrameIndex d D → HighFrameIndex d D → ℝ)
    (p : Fin n → ℝ)
    (reset : HighWindowLabels d k → Z → ℝ → (Fin r → ℝ) → Fin n → ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (x : Fin n → Covariate d)
    (j : HighWindowLabels d k) (y : Fin n → Fin 3) : ℝ :=
  highSeparatedXiScore (σ j) ad bd m r D (q j) C a V η (A j) p (reset j)
    (fun i => highLocalFieldWithout d k D η c j (x i))
    (fun i => highPeriodicTensor d k j (x i))
    (fun i => highLocalFrameFeature k j (x i)) (c j) y

theorem highFrameXiScore_energy_bound (d k D n : ℕ) [NeZero k] (hk : 4 ≤ k)
    (σ : HighWindowLabels d k → Measure Z) [∀ j, IsFiniteMeasure (σ j)]
    (ad bd : ℝ) (m r : ℕ) (q : HighWindowLabels d k → ℕ)
    (C a V η pPlus : ℝ) (ha : a ≠ 0) (hpPlus : 0 ≤ pPlus)
    (A : HighWindowLabels d k → Z → HighFrameIndex d D → HighFrameIndex d D → ℝ)
    (p : Fin n → ℝ)
    (reset : HighWindowLabels d k → Z → ℝ → (Fin r → ℝ) → Fin n → ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (x : Fin n → Covariate d)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a
      (highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)) V b)
    (hA : ∀ j γ β, Measurable (fun ζ => A j ζ γ β))
    (hcost : ∀ j, Integrable (separatedMatrixCost (A j)) (σ j))
    (hReset : ∀ j z ε i, Measurable (fun ζ => reset j ζ z ε i))
    (hBound : ∀ j ζ (h : HighDensityMarkIndex m r D) i,
      |reset j ζ (densityPacketAtom ad bd m r D h).1 (densityPacketAtom ad bd m r D h).2 i| ≤ pPlus) :
    (∫ y, (∑ j, highFrameXiScore d k D n σ ad bd m r q C a V η A p reset c x j y)^2
      ∂Measure.pi (fun i => ternaryIndexMeasure a
        (highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)) V
        ha (fun b => (hp i b).le))) ≤
    (3^d : ℕ) * ∑ j, ∫ y,
      (highFrameXiScore d k D n σ ad bd m r q C a V η A p reset c x j y)^2
      ∂Measure.pi (fun i => ternaryIndexMeasure a
        (highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)) V
        ha (fun b => (hp i b).le)) := by
  exact highSeparatedXiScores_torus_variance_bound d k n σ ad bd m r D q C a V η pPlus
    ha hpPlus A p reset
    (fun j i => highLocalFieldWithout d k D η c j (x i))
    (fun j i => highLocalFrameFeature k j (x i)) c x
    (fun i => highFrameField d k η (fun l => highFramePolynomial (c l)) (x i))
    (fun j => highFrameField_coefficientRegression d k D n hk η c j x)
    hpd hp hA hcost hReset hBound

end
end NearlyMinimax
