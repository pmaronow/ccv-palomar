module

public import NearlyMinimax.Model


@[expose] public section

/-! Three disjoint blocks of the original sample law, with exact product law. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

 def sampleBlockIndexEquiv (a b c : ℕ) :
    ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin (a + b + c) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin c))).trans finSumFinEquiv

def sampleBlockSplitEquiv (d a b c : ℕ) :
    (Fin (a + b + c) → Observation d) ≃ᵐ
      (((Fin a → Observation d) × (Fin b → Observation d)) × (Fin c → Observation d)) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : (Fin a ⊕ Fin b) ⊕ Fin c => Observation d)
    (sampleBlockIndexEquiv a b c).symm).trans
  ((MeasurableEquiv.sumPiEquivProdPi
    (fun _ : (Fin a ⊕ Fin b) ⊕ Fin c => Observation d)).trans
  (MeasurableEquiv.prodCongr
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => Observation d))
    (MeasurableEquiv.refl (Fin c → Observation d))))

theorem sampleBlockSplit_measurePreserving {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (a b c : ℕ) :
    MeasurePreserving (sampleBlockSplitEquiv d a b c) (sampleLaw θ (a + b + c))
      (((sampleLaw θ a).prod (sampleLaw θ b)).prod (sampleLaw θ c)) := by
  let := observationLaw_isProbability C θ hθ
  let := sampleLaw_isProbability C θ hθ c
  have h1 := measurePreserving_piCongrLeft
    (fun _ : (Fin a ⊕ Fin b) ⊕ Fin c => observationLaw θ) (sampleBlockIndexEquiv a b c).symm
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : (Fin a ⊕ Fin b) ⊕ Fin c => observationLaw θ)
  have h3 := (measurePreserving_sumPiEquivProdPi
    (fun _ : Fin a ⊕ Fin b => observationLaw θ)).prod (MeasurePreserving.id (sampleLaw θ c))
  exact h3.comp (h2.comp h1)

/-- A measurable estimator on the independent block product is an actual
Borel estimator on the single original sample, with exactly the same risk. -/
def blockEstimator {d a b c : ℕ}
    (T : (((Fin a → Observation d) × (Fin b → Observation d)) × (Fin c → Observation d)) → ℝ)
    (hmT : Measurable T) : Estimator d (a + b + c) :=
  ⟨fun z => T (sampleBlockSplitEquiv d a b c z), hmT.comp (sampleBlockSplitEquiv d a b c).measurable⟩

theorem blockEstimator_risk_eq {d a b c : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (T : (((Fin a → Observation d) × (Fin b → Observation d)) × (Fin c → Observation d)) → ℝ)
    (hmT : Measurable T) :
    meanSquaredRisk (blockEstimator T hmT) θ =
      ∫⁻ z, ENNReal.ofReal ((T z - θ.variance) ^ 2)
        ∂((sampleLaw θ a).prod (sampleLaw θ b)).prod (sampleLaw θ c) := by
  unfold meanSquaredRisk blockEstimator
  exact (sampleBlockSplit_measurePreserving C θ hθ a b c).lintegral_comp
    (((hmT.sub measurable_const).pow_const 2).ennreal_ofReal)

end NearlyMinimax
