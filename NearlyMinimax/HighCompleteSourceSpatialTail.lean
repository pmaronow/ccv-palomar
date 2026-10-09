module

public import NearlyMinimax.HighCompleteSourceFrameTail
public import NearlyMinimax.HighMarkedMeasurable
public import NearlyMinimax.ResponseConfigurationEnergy
public import NearlyMinimax.AliasTailSummation
public import NearlyMinimax.CardinalProductDesign


@[expose] public section

/-! Genuine spatial and factorial large-count bounds for the complete
canonical source. The raw uniform cap is proved from actual packet total
variation, and all response/spatial integrations are derived here. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

theorem fullSpatialPatchDesign_real_univ (d n : ℕ) :
    (fullSpatialPatchDesign d n).real univ = (2 : ℝ)^(d*n) := by
  simp only [fullSpatialPatchDesign, measureReal_def, Measure.pi_univ,
    Measure.restrict_apply_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_pow]
  change (volume.real (spatialPatchBox d))^n = _
  rw [spatialPatchBox_real_volume, pow_mul]

def completeSourceCrudeSpatialBase (d : ℕ) (Chi : ℝ) : ℝ :=
  3*(2 : ℝ)^d*Chi^2

theorem completeSourceCrudeSpatialBase_nonneg (d : ℕ) (Chi : ℝ) :
    0 ≤ completeSourceCrudeSpatialBase d Chi := by
  unfold completeSourceCrudeSpatialBase
  positivity

/-- True finite response sum and spatial integral of any measurable raw
numerator satisfying the actual uniform packet cap. -/
theorem crude_raw_spatial_response_energy {d n : ℕ} (Chi η B : ℝ)
    (hChi : 0 ≤ Chi) (hB : 0 ≤ B)
    (R : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ)
    (hR : ∀ y, Measurable (fun x => R x y))
    (hcap : ∀ x y, |R x y| ≤ Chi^n*η^2*(B+1)) :
    Integrable (selectedRawSquareEnergy R) (fullSpatialPatchDesign d n) ∧
      (∫ x, selectedRawSquareEnergy R x ∂fullSpatialPatchDesign d n) ≤
        (completeSourceCrudeSpatialBase d Chi)^n*η^4*(B+1)^2 := by
  let K := Chi^(2*n)*η^4*(B+1)^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hp (x y) : R x y ^ 2 ≤ K := by
    have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Chi^n*η^2*(B+1))).mpr
      (hcap x y)
    simp only [sq_abs] at hs
    convert hs using 1 <;> (try dsimp [K]) <;> (try rw [mul_pow, mul_pow, ← pow_mul]) <;> ring
  have hi (y) : Integrable (fun x => R x y ^ 2) (fullSpatialPatchDesign d n) :=
    (integrable_const K).mono' ((hR y).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (R x y))]
        exact hp x y))
  have hb (y) : (∫ x, R x y ^ 2 ∂fullSpatialPatchDesign d n) ≤ (2 : ℝ)^(d*n)*K := by
    have hh := integral_mono (hi y) (integrable_const K) (fun x => hp x y)
    simpa only [integral_const, smul_eq_mul, fullSpatialPatchDesign_real_univ] using hh
  have hh := selected_raw_square_integrable_bound (fullSpatialPatchDesign d n) R
    ((2 : ℝ)^(d*n)*K) hi hb
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  dsimp [K,completeSourceCrudeSpatialBase]
  simp only [Fintype.card_fin, mul_pow, pow_mul]
  ring

def completeSourceCrudeFactorialConstant (d : ℕ) (Chi Csharp : ℝ) : ℝ :=
  aliasTailConstant 1 Csharp (completeSourceCrudeSpatialBase d Chi) 0

theorem completeSourceCrudeFactorialConstant_ge_one (d : ℕ) (Chi Csharp : ℝ)
    (hCs : 0 ≤ Csharp) : 1 ≤ completeSourceCrudeFactorialConstant d Chi Csharp :=
  aliasTailConstant_ge_one (by norm_num) hCs (completeSourceCrudeSpatialBase_nonneg d Chi)

/-- Actual spatial energies on the finite count tail give the source's
factorial tail. The constant is independent of D, J, B and the raw arrays. -/
theorem crude_raw_spatial_factorial_tail (d D J : ℕ) (Chi Csharp η B μ : ℝ)
    (hChi : 0 ≤ Chi) (hCs : 0 ≤ Csharp) (hB : 0 ≤ B) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (R : (n : ℕ) → (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ)
    (hR : ∀ n y, Measurable (fun x => R n x y))
    (hcap : ∀ j ∈ Finset.range J, ∀ x y,
      |R (D+1+j) x y| ≤ Chi^(D+1+j)*η^2*(B+1)) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp*μ) (D+1+j) *
      ∫ x, selectedRawSquareEnergy (R (D+1+j)) x ∂fullSpatialPatchDesign d (D+1+j)) ≤
      completeSourceCrudeFactorialConstant d Chi Csharp * η^4*(B+1)^2 *
        poissonCountWeight (completeSourceCrudeFactorialConstant d Chi Csharp * μ) (D+1) := by
  unfold completeSourceCrudeFactorialConstant
  rw [mul_assoc _ (η^4) ((B+1)^2)]
  apply finite_alias_energy_tail_le (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : 0 ≤ η^4*(B+1)^2) hCs (completeSourceCrudeSpatialBase_nonneg d Chi)
    (by norm_num : (0 : ℝ) ≤ 0) hμ hμ1 D J
    (fun n => ∫ x, selectedRawSquareEnergy (R n) x ∂fullSpatialPatchDesign d n)
  intro j hj
  have hh := (crude_raw_spatial_response_energy Chi η B hChi hB (R (D+1+j))
    (hR (D+1+j)) (hcap j hj)).2
  simpa only [one_mul, zero_mul, mul_zero, Real.exp_zero, mul_one, mul_assoc, mul_comm, mul_left_comm] using hh

end NearlyMinimax
