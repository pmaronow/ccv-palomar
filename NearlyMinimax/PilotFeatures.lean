module

public import NearlyMinimax.AnchoredFeatures
public import NearlyMinimax.GridProjection
public import NearlyMinimax.ObservationMoments
public import NearlyMinimax.FieldLiftCovariance


@[expose] public section

/-! Actual finite global coordinates for local polynomial pilots. These are
functions of the original observation, with no bounded-response model. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev PilotBasisIndex (q d ℓ : ℕ) := (Fin q × PolynomialBox d ℓ) × Bool

def pilotGlobalMonomial {d ℓ : ℕ} (γ : PolynomialBox d ℓ) (x : Covariate d) : ℝ :=
  ∏ i, (x i) ^ (γ i).val

theorem pilotGlobalMonomial_continuous {d ℓ : ℕ} (γ : PolynomialBox d ℓ) :
    Continuous (pilotGlobalMonomial γ) :=
  continuous_finset_prod Finset.univ (fun i _ => (continuous_apply i).pow _)

theorem pilotGlobalMonomial_abs_le_one {d ℓ : ℕ} (γ : PolynomialBox d ℓ)
    (x : Covariate d) (hx : x ∈ unitCube d) : |pilotGlobalMonomial γ x| ≤ 1 := by
  unfold pilotGlobalMonomial
  rw [Finset.abs_prod]
  simp only [abs_pow]
  have hcoord (i : Fin d) : |x i| ≤ 1 := by
    rw [abs_of_nonneg (hx i).1]
    exact (hx i).2
  calc
    _ ≤ ∏ _i : Fin d, (1 : ℝ) ^ (γ _i).val :=
      Finset.prod_le_prod₀ (fun i _ => pow_nonneg (abs_nonneg _) _)
        (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hcoord i) _)
    _ = 1 := by simp

/-- A fixed global coordinate: a cell indicator times a monomial, optionally
multiplied by the observed response. Local anchored features are linear
combinations of this finite basis. -/
def pilotBasisFeature {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (a : PilotBasisIndex q d ℓ) (z : Observation d) : ℝ :=
  if cell z.1 = a.1.1 then pilotGlobalMonomial a.1.2 z.1 * (if a.2 then z.2 else 1) else 0

theorem pilotBasisFeature_measurable {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (hc : Measurable cell) (a : PilotBasisIndex q d ℓ) :
    Measurable (pilotBasisFeature cell a) := by
  unfold pilotBasisFeature
  apply Measurable.ite
  · exact measurableSet_eq_fun (hc.comp measurable_fst) measurable_const
  · exact ((pilotGlobalMonomial_continuous a.1.2).measurable.comp measurable_fst).mul
      (by cases a.2 <;> first | exact measurable_const | exact measurable_snd)
  · exact measurable_const

theorem pilotBasisFeature_abs_bound {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (a : PilotBasisIndex q d ℓ) (z : Observation d) (hz : z.1 ∈ unitCube d) :
    |pilotBasisFeature cell a z| ≤
      (Prod.fst ⁻¹' {x | cell x = a.1.1}).indicator
        (fun z : Observation d => 1 + |z.2|) z := by
  have hmono := pilotGlobalMonomial_abs_le_one a.1.2 z.1 hz
  by_cases h : cell z.1 = a.1.1
  · rw [pilotBasisFeature, if_pos h, abs_mul]
    simp only [mem_preimage, mem_setOf_eq, h, indicator_of_mem]
    cases a.2
    · simpa using hmono.trans (le_add_of_nonneg_right (abs_nonneg z.2))
    · simp only [Bool.true_eq_false, ↓reduceIte]
      exact (mul_le_mul_of_nonneg_right hmono (abs_nonneg z.2)).trans (by linarith)
  · simp [pilotBasisFeature, h]

theorem pilotBasisFeature_zero_off_cell {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (a : PilotBasisIndex q d ℓ) (z : Observation d) (hz : cell z.1 ≠ a.1.1) :
    pilotBasisFeature cell a z = 0 := by simp [pilotBasisFeature, hz]

/-- The actual covariate marginal proves cube membership for observations. -/
theorem observationLaw_cube_ae {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    ∀ᵐ z ∂observationLaw θ, z.1 ∈ unitCube d :=
  (observationLaw_fst_measurePreserving C θ hθ).quasiMeasurePreserving.ae
    (designLaw_cube_ae θ)

/-- Every global pilot coordinate is genuinely L² under the original model. -/
theorem pilotBasisFeature_memLp_two {q d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (cell : Covariate d → Fin q) (hc : Measurable cell) (a : PilotBasisIndex q d ℓ) :
    MemLp (pilotBasisFeature cell a) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  have hy : MemLp (fun z : Observation d => |z.2|) 2 (observationLaw θ) := by
    simpa only [Real.norm_eq_abs] using (observationLaw_response_memLp_two C θ hθ).norm
  have hbase : MemLp (fun z : Observation d => 1 + |z.2|) 2 (observationLaw θ) :=
    (memLp_const (1 : ℝ)).add hy
  apply hbase.mono' (pilotBasisFeature_measurable cell hc a).aestronglyMeasurable
  filter_upwards [observationLaw_cube_ae C θ hθ] with z hz
  rw [Real.norm_eq_abs]
  apply (pilotBasisFeature_abs_bound cell a z hz).trans
  by_cases h : cell z.1 = a.1.1 <;> simp [h] <;> positivity

/-- The localized second moment follows from the actual response energy
bound, rather than from a bounded-response assumption. -/
theorem pilotBasisFeature_second_le {q d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (cell : Covariate d → Fin q) (hc : Measurable cell) (a : PilotBasisIndex q d ℓ) :
    (∫ z, pilotBasisFeature cell a z ^ 2 ∂observationLaw θ) ≤
      (2 * (1 + responseSecondBound C)) * (designLaw θ).real {x | cell x = a.1.1} := by
  let := observationLaw_isProbability C θ hθ
  have hA : MeasurableSet {x | cell x = a.1.1} := measurableSet_eq_fun hc measurable_const
  have hy : MemLp (fun z : Observation d => |z.2|) 2 (observationLaw θ) := by
    simpa only [Real.norm_eq_abs] using (observationLaw_response_memLp_two C θ hθ).norm
  have hbase := ((memLp_const (1 : ℝ)).add hy).integrable_sq
  have hdom := hbase.indicator (measurable_fst hA)
  apply (integral_mono_ae (pilotBasisFeature_memLp_two C θ hθ cell hc a).integrable_sq hdom ?_).trans
    (observationLaw_localized_response_energy_le C θ hθ _ hA)
  filter_upwards [observationLaw_cube_ae C θ hθ] with z hz
  have ha := pilotBasisFeature_abs_bound cell a z hz
  by_cases h : cell z.1 = a.1.1
  · simp only [mem_preimage, mem_setOf_eq, h, indicator_of_mem] at ha ⊢
    change pilotBasisFeature cell a z ^ 2 ≤ (1 + |z.2|) ^ 2
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ha 2
  · simp [pilotBasisFeature, h]

/-- Coordinate indexing compatible with the paper's finite-dimensional
polynomial lift; this is an exact reindexing of the global basis. -/
def pilotRawVector {q d ℓ : ℕ} (cell : Covariate d → Fin q) (z : Observation d) :
    Fin (Fintype.card (PilotBasisIndex q d ℓ)) → ℝ :=
  fun a => pilotBasisFeature cell ((Fintype.equivFin (PilotBasisIndex q d ℓ)).symm a) z

theorem pilotRawVector_measurable {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (hc : Measurable cell) : Measurable (pilotRawVector (ℓ := ℓ) cell) := by
  apply measurable_pi_iff.mpr
  intro a
  exact pilotBasisFeature_measurable cell hc _

def pilotRawMean {q d ℓ : ℕ} (θ : RegressionParameter d) (cell : Covariate d → Fin q) :
    Fin (Fintype.card (PilotBasisIndex q d ℓ)) → ℝ :=
  fun a => ∫ z, pilotRawVector cell z a ∂observationLaw θ

/-- All iid/L²/mean hypotheses required by the actual lift theorem follow
from the original sample law and the concrete global pilot coordinates. -/
theorem pilotRawVector_sample_facts {q d ℓ n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (cell : Covariate d → Fin q) (hc : Measurable cell) :
    iIndepFun (fun j (z : Fin n → Observation d) => pilotRawVector (ℓ := ℓ) cell (z j)) (sampleLaw θ n) ∧
    (∀ j : Fin n, Measurable (fun z : Fin n → Observation d => pilotRawVector (ℓ := ℓ) cell (z j))) ∧
    (∀ i j : Fin n, IdentDistrib
      (fun z : Fin n → Observation d => pilotRawVector (ℓ := ℓ) cell (z i))
      (fun z : Fin n → Observation d => pilotRawVector (ℓ := ℓ) cell (z j)) (sampleLaw θ n) (sampleLaw θ n)) ∧
    (∀ (j : Fin n) a, MemLp (fun z : Fin n → Observation d => pilotRawVector (ℓ := ℓ) cell (z j) a)
      2 (sampleLaw θ n)) ∧
    (∀ (j : Fin n) a, (∫ z : Fin n → Observation d, pilotRawVector (ℓ := ℓ) cell (z j) a ∂sampleLaw θ n) =
      pilotRawMean θ cell a) := by
  let := observationLaw_isProbability C θ hθ
  have hm := pilotRawVector_measurable (ℓ := ℓ) cell hc
  have hp (j : Fin n) : MeasurePreserving (fun z : Fin n → Observation d => z j)
      (sampleLaw θ n) (observationLaw θ) := measurePreserving_eval _ j
  refine ⟨iIndepFun_pi (fun _ : Fin n => hm.aemeasurable),
    fun j => hm.comp (measurable_pi_apply j), ?_, ?_, ?_⟩
  · intro i j
    have hj : IdentDistrib (fun z : Fin n → Observation d => z i) (fun z : Fin n → Observation d => z j)
        (sampleLaw θ n) (sampleLaw θ n) :=
      ⟨(hp i).aemeasurable, (hp j).aemeasurable, (hp i).map_eq.trans (hp j).map_eq.symm⟩
    exact hj.comp hm
  · intro j a
    exact (pilotBasisFeature_memLp_two C θ hθ cell hc _).comp_measurePreserving (hp j)
  · intro j a
    exact integral_comp_eval (μ := fun _ : Fin n => observationLaw θ) (i := j)
      ((pilotBasisFeature_measurable cell hc
        ((Fintype.equivFin (PilotBasisIndex q d ℓ)).symm a)).aestronglyMeasurable)

end NearlyMinimax
