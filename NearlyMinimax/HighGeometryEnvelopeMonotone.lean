module

public import NearlyMinimax.HighCompleteGeometry
public import NearlyMinimax.CompleteSourceSaddleParameters


@[expose] public section

/-! The true source activation budget dominates its unbalanced row mass,
and the complete geometry H increases with this budget. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
attribute [local instance] Classical.propDecidable

 theorem completeSourceGeometryEnvelope_mono_total {d : ℕ} (D M R q : ℕ)
    (aD bD c0 ell N mu C a rho eta Chi : ℝ) {B1 B2 : ℝ}
    (hB1 : 0 ≤ B1) (hB : B1 ≤ B2) (n : ℕ) (U : Fin n → Covariate d) :
    completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu C a rho eta Chi B1 n U ≤
      completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu C a rho eta Chi B2 n U := by
  rcases n with _|_|_|n
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · change (if n+3 ≤ D then _ else (3*Chi^2)^(n+3)*eta^4*(B1+1)^2) ≤
      (if n+3 ≤ D then _ else (3*Chi^2)^(n+3)*eta^4*(B2+1)^2)
    split_ifs
    · exact le_rfl
    · have hs : (B1+1)^2 ≤ (B2+1)^2 :=
        (sq_le_sq₀ (by linarith) (by linarith)).mpr (by linarith)
      exact mul_le_mul_of_nonneg_left hs (by positivity)

 theorem rowMass_le_balanced_source_activity {d k F : ℕ} {I : Type*} [Fintype I]
    {E : I → Type*} [∀ i, MeasurableSpace (E i)] (C : ModelConstants d)
    (R : HighUnionRowData d k F I E) (hR : 0 ≤ highRowTotalMass R.rowMass) :
    highRowTotalMass R.rowMass ≤ highRowTotalMass R.rowMass/highCenterMix C := by
  apply (le_div_iff₀ (highCenterMix_mem C).1).mpr
  exact mul_le_of_le_one_right hR (highCenterMix_mem C).2.le

end NearlyMinimax
