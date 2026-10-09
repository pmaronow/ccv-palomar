module

public import NearlyMinimax.AnchoredMoments
public import NearlyMinimax.PopulationInverseDerivatives


@[expose] public section

/-! The inverse derivative chart evaluated at genuine bounded population moments. -/

noncomputable section
namespace NearlyMinimax
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

/-- The two population vector families are the density-feature moment and the
response-feature moment, with the known Lebesgue Gram preconditioner. -/
def anchoredFinMomentFamilies {d ℓ : ℕ} (u : Covariate d)
    (p f : Covariate d → ℝ) : Bool → Fin (anchoredDimension d ℓ) → ℝ :=
  fun t i => anchoredPreconditionedMoment u p (if t then fun _ => 1 else f)
    ((Fintype.equivFin (AnchoredIndex d ℓ)).symm i)

theorem anchoredFinMomentFamilies_uniform_bound {d ℓ : ℕ}
    (b F : ℝ) (hb : 0 ≤ b) (hF : 0 ≤ F) :
    ∃ W : ℝ, 0 < W ∧ ∀ u ∈ unitCube d, ∀ p f : Covariate d → ℝ,
      (∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) →
      (∀ w ∈ unitCube d, |f w| ≤ F) →
      ∀ t, ‖anchoredFinMomentFamilies (ℓ := ℓ) u p f t‖ ≤ W := by
  obtain ⟨W, hW, hm⟩ := anchoredPreconditionedMoment_uniform_bound
    (d := d) (ℓ := ℓ) b (max 1 F) hb (le_trans zero_le_one (le_max_left _ _))
  refine ⟨W, hW, ?_⟩
  intro u hu p f hp hf t
  have hg : ∀ w ∈ unitCube d, |(if t then fun _ => 1 else f) w| ≤ max 1 F := by
    intro w hw
    cases t
    · exact (hf w hw).trans (le_max_right _ _)
    · simp
  have h := hm u hu p _ hp hg
  apply (pi_norm_le_iff_of_nonneg hW.le).mpr
  intro i
  exact (norm_le_pi_norm _ ((Fintype.equivFin (AnchoredIndex d ℓ)).symm i)).trans h

/-- The paper's common all-order inverse derivative estimate, with all matrix
charts and vector-size bounds derived from actual density and response bounds. -/
theorem anchored_actual_population_inverse_derivatives {d ℓ : ℕ}
    [Nonempty (AnchoredIndex d ℓ)] (a b F Y : ℝ)
    (ha : 0 < a) (hab : a < b) (hF : 0 ≤ F) (hY : 0 ≤ Y) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ u v : Covariate d, u ∈ unitCube d → v ∈ unitCube d →
      ∀ p q f g : Covariate d → ℝ, Measurable p → Measurable q →
      (∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) →
      (∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b) →
      (∀ w ∈ unitCube d, |f w| ≤ F) →
      (∀ w ∈ unitCube d, |g w| ≤ F) →
      ∀ y : ℝ, |y| ≤ Y → ∀ m k : ℕ,
      ∀ directions : Fin k → Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ,
        ‖iteratedFDeriv ℝ k
          (incrementFinVector (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) y m)
          (fun j => incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q)
            (anchoredFinMomentFamilies u p f) (anchoredFinMomentFamilies v q g)
            ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm j)) directions‖ ≤
          C * (k.factorial : ℝ) * A ^ k * ∏ j, ‖directions j‖ := by
  have hb : 0 ≤ b := (ha.trans hab).le
  obtain ⟨W, hW, hmom⟩ := anchoredFinMomentFamilies_uniform_bound (d := d) (ℓ := ℓ) b F hb hF
  obtain ⟨C, A, hC, hA, hder⟩ := anchored_population_inverse_derivatives
    (d := d) (ℓ := ℓ) a b W Y ha hab hW.le hY
  refine ⟨C, A, hC, hA, ?_⟩
  intro u v hu hv p q f g hpmeas hqmeas hp hq hf hg y hy m k directions
  exact hder u v hu hv p q hpmeas hqmeas hp hq
    (anchoredFinMomentFamilies u p f) (anchoredFinMomentFamilies v q g)
    (hmom u hu p f (hp.mono (fun w hw => ⟨ha.le.trans hw.1, hw.2⟩)) hf)
    (hmom v hv q g (hq.mono (fun w hw => ⟨ha.le.trans hw.1, hw.2⟩)) hg)
    y hy m k directions

end NearlyMinimax
