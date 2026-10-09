module

public import NearlyMinimax.HighSourceHigherGeometry
public import NearlyMinimax.HighCompleteSourceMarkedTail


@[expose] public section

/-! A deterministic measurable integrable full-count spatial envelope for
complete source scores, including empty/singleton cancellation, the genuine
pair defect, matched higher counts, and the exterior-degree crude bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

 def completeSourceGeometryEnvelope {d : ℕ} (D M R q : ℕ)
    (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ) : (n : ℕ) → (Fin n → Covariate d) → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | 2, U => finePairCountTwoGeometryEnvelope (bD-(M : ℝ)⁻¹) a rho eta N U
  | n+3, U => if n+3 ≤ D then
      completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ell N mu M R q C a rho eta U
    else (3*Chi^2)^(n+3)*eta^4*(Bl+1)^2

 theorem completeSourceGeometryEnvelope_nonneg {d : ℕ} (D M R q : ℕ)
    (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ) (n : ℕ) (U : Fin n → Covariate d) :
    0 ≤ completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu C a rho eta Chi Bl n U := by
  rcases n with _|_|_|n
  · norm_num [completeSourceGeometryEnvelope]
  · norm_num [completeSourceGeometryEnvelope]
  · exact finePairCountTwoGeometryEnvelope_nonneg _ _ _ _ _ U
  · try simp only [completeSourceGeometryEnvelope]
    split_ifs
    · exact completeSourceHigherGeometryEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · positivity

 theorem completeSourceGeometryEnvelope_measurable {d : ℕ} [NeZero d] (D M R q : ℕ)
    (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ) (hell : 1 ≤ ell) (n : ℕ) :
    Measurable (completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl n) := by
  rcases n with _|_|_|n
  · exact measurable_const
  · exact measurable_const
  · exact finePairCountTwoGeometryEnvelope_measurable _ _ _ _ _
  · change Measurable (fun U : Fin (n+3) → Covariate d => if n+3 ≤ D then
      completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ell N mu M R q C a rho eta U
      else (3*Chi^2)^(n+3)*eta^4*(Bl+1)^2)
    split_ifs
    · exact completeSourceHigherGeometryEnvelope_measurable _ _ _ _ _ _ _ _ _ _ _ _ _ hell
    · exact measurable_const

 theorem completeSourceGeometryEnvelope_integrable {d : ℕ} [NeZero d] (hd : 5 ≤ d)
    (D M R q : ℕ) (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ)
    (hell : 1 ≤ ell) (hN : ell ≤ N) (n : ℕ) :
    Integrable (completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl n)
      (fullSpatialPatchDesign d n) := by
  rcases n with _|_|_|n
  · exact integrable_zero _ _ _
  · exact integrable_zero _ _ _
  · exact (finePairCountTwoGeometryEnvelope_integrable_and_le (by omega) _ _ _ _
      (lt_of_lt_of_le zero_lt_one (hell.trans hN))).1
  · change Integrable (fun U : Fin (n+3) → Covariate d => if n+3 ≤ D then
      completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ell N mu M R q C a rho eta U
      else (3*Chi^2)^(n+3)*eta^4*(Bl+1)^2) (fullSpatialPatchDesign d (n+3))
    split_ifs
    · exact completeSourceHigherGeometryEnvelope_integrable hd (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _ hell hN
    · exact integrable_const _

 theorem completeSourceGeometryEnvelope_pair_integral_le {d : ℕ} (D M R q : ℕ)
    (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ) (hd : 0 < d) (hN : 0 < N) :
    (∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl 2 U
      ∂fullSpatialPatchDesign d 2) ≤ 9*finePairCountTwoSpatialBudget d (bD-(M : ℝ)⁻¹) a rho eta N :=
    (finePairCountTwoGeometryEnvelope_integrable_and_le hd _ _ _ _ hN).2

 theorem completeSourceGeometryEnvelope_exterior_integral {d : ℕ} (D M R q n : ℕ)
    (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ) (hn : D < n+3) :
    (∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl (n+3) U
      ∂fullSpatialPatchDesign d (n+3)) =
      (3*(2 : ℝ)^d*Chi^2)^(n+3)*eta^4*(Bl+1)^2 := by
  simp only [completeSourceGeometryEnvelope, if_neg (not_le.mpr hn), integral_const,
    fullSpatialPatchDesign_real_univ, smul_eq_mul]
  rw [pow_mul, mul_pow]
  ring

 theorem fineFieldGeometryEnvelope_count_three {d : ℕ} (ad bd T0 N : ℝ)
    (M q : ℕ) (C a rho eta : ℝ) (U : Fin 3 → Covariate d) :
    fineFieldGeometryEnvelope ad bd T0 N M q C a rho eta U = 0 := by
  have hs : ((Finset.univ : Finset (Fin 3)).powerset).filter
      (fun S => 4 ≤ S.card ∧ Even S.card) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    have hcard := Finset.card_le_card ((Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1))
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    have h4 := (Finset.mem_filter.mp hS).2.1
    omega
  unfold fineFieldGeometryEnvelope
  rw [hs]
  simp

end NearlyMinimax
