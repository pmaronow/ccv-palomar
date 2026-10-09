module

public import Mathlib


@[expose] public section

/-!
The statistical model from §1.1 of the current manuscript.  In particular,
the minimax loss uses `lintegral`: an infinite second moment is not zero.
These are definitions, not a proof of the paper's minimax rate theorems.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace NearlyMinimax

abbrev Covariate (d : ℕ) := Fin d → ℝ
abbrev Observation (d : ℕ) := Covariate d × ℝ

def unitCube (d : ℕ) : Set (Covariate d) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

/-- The Euclidean norm, independently of the sup norm on the function type. -/
def euclideanNorm {d : ℕ} (x : Covariate d) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

def coordinatePartial {d : ℕ} (i : Fin d) (F : Covariate d → ℝ) :
    Covariate d → ℝ := fun x => fderiv ℝ F x (Pi.single i 1)

/-- Ordered mixed partials; `ContDiffOn` on an open set supplies their usual meaning. -/
def multiPartial {d : ℕ} (F : Covariate d → ℝ) (γ : Fin d → ℕ) :
    Covariate d → ℝ :=
  ((List.finRange d).flatMap (fun i => List.replicate (γ i) i)).foldl
    (fun G i => coordinatePartial i G) F

def derivativeSup {d : ℕ} (U : Set (Covariate d)) (G : Covariate d → ℝ) : ℝ≥0∞ :=
  ⨆ x : U, ENNReal.ofReal |G x|

def holderSeminorm {d : ℕ} (U : Set (Covariate d)) (G : Covariate d → ℝ)
    (α : ℝ) : ℝ≥0∞ :=
  ⨆ x : U, ⨆ y : U, if (x : Covariate d) = y then 0 else
    ENNReal.ofReal (|G x - G y| / (euclideanNorm (x.val - y.val)) ^ α)

/-- Sum over distinct multi-indices, plus the maximum top-order seminorm. -/
def holderNorm {d : ℕ} (U : Set (Covariate d)) (F : Covariate d → ℝ)
    (ℓ : ℕ) (α : ℝ) : ℝ≥0∞ :=
  (∑ γ : Fin d → Fin (ℓ + 1),
    if (∑ i, (γ i).val) ≤ ℓ then
      derivativeSup U (multiPartial F (fun i => (γ i).val)) else 0) +
  ⨆ γ : Fin d → Fin (ℓ + 1),
    if (∑ i, (γ i).val) = ℓ then
      holderSeminorm U (multiPartial F (fun i => (γ i).val)) α else 0

/-- The open extension domain and all fixed model constants. -/
structure ModelConstants (d : ℕ) where
  dimension_pos : 0 < d
  smoothness : ℝ
  order : ℕ
  smoothness_pos : 0 < smoothness
  order_lt : (order : ℝ) < smoothness
  smoothness_le_order_add_one : smoothness ≤ order + 1
  domain : Set (Covariate d)
  domain_open : IsOpen domain
  cube_subset : unitCube d ⊆ domain
  densityLower : ℝ
  densityUpper : ℝ
  densityLower_pos : 0 < densityLower
  densityLower_lt_one : densityLower < 1
  one_lt_densityUpper : 1 < densityUpper
  holderBound : ℝ
  holderBound_pos : 0 < holderBound
  varianceLower : ℝ
  varianceUpper : ℝ
  varianceLower_pos : 0 < varianceLower
  variance_interval : varianceLower < varianceUpper
  fourthBound : ℝ
  fourth_margin : varianceLower ^ 2 < fourthBound

def ModelConstants.alpha {d : ℕ} (C : ModelConstants d) : ℝ :=
  C.smoothness - C.order

theorem ModelConstants.order_eq {d : ℕ} (C : ModelConstants d) :
    C.order = Nat.ceil C.smoothness - 1 := by
  have hc : Nat.ceil C.smoothness = C.order + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero C.order)).mpr
    simpa only [Nat.succ_sub_one, Nat.cast_succ, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using
      And.intro C.order_lt C.smoothness_le_order_add_one
  rw [hc, Nat.add_sub_cancel]

theorem ModelConstants.alpha_pos {d : ℕ} (C : ModelConstants d) : 0 < C.alpha := by
  exact sub_pos.mpr C.order_lt

theorem ModelConstants.alpha_le_one {d : ℕ} (C : ModelConstants d) : C.alpha ≤ 1 := by
  dsimp [ModelConstants.alpha]
  linarith [C.smoothness_le_order_add_one]

/-- Kernels are defined on the ambient space; values outside the cube are irrelevant. -/
structure RegressionParameter (d : ℕ) where
  density : Covariate d → ℝ
  regression : Covariate d → ℝ
  variance : ℝ
  errors : Kernel (Covariate d) ℝ
  errors_markov : IsMarkovKernel errors

attribute [instance] RegressionParameter.errors_markov

def cubeVolume (d : ℕ) : Measure (Covariate d) :=
  volume.restrict (unitCube d)

def designLaw {d : ℕ} (θ : RegressionParameter d) : Measure (Covariate d) :=
  (cubeVolume d).withDensity (fun x => ENNReal.ofReal (θ.density x))

def observationLaw {d : ℕ} (θ : RegressionParameter d) : Measure (Observation d) :=
  ((designLaw θ).compProd θ.errors).map
    (fun z => (z.1, θ.regression z.1 + z.2))

def sampleLaw {d : ℕ} (θ : RegressionParameter d) (n : ℕ) :
    Measure (Fin n → Observation d) := Measure.pi (fun _ => observationLaw θ)

/-- The fourth-moment and integrability constraints are on the error kernel,
not on a common error distribution independent of the covariate. -/
def Admissible {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) : Prop :=
  Measurable θ.density ∧ Measurable θ.regression ∧
  (∀ᵐ x ∂cubeVolume d, C.densityLower ≤ θ.density x ∧ θ.density x ≤ C.densityUpper) ∧
  (∫⁻ x, ENNReal.ofReal (θ.density x) ∂cubeVolume d) = 1 ∧
  (∃ F : Covariate d → ℝ,
    (∀ x ∈ unitCube d, F x = θ.regression x) ∧
    ContDiffOn ℝ C.order F C.domain ∧
    holderNorm C.domain F C.order C.alpha ≤ ENNReal.ofReal C.holderBound) ∧
  C.varianceLower ≤ θ.variance ∧ θ.variance ≤ C.varianceUpper ∧
  (∀ᵐ x ∂designLaw θ,
    Integrable (fun u : ℝ => u) (θ.errors x) ∧
    Integrable (fun u : ℝ => u ^ 2) (θ.errors x) ∧
    Integrable (fun u : ℝ => u ^ 4) (θ.errors x) ∧
    (∫ u : ℝ, u ∂θ.errors x) = 0 ∧
    (∫ u : ℝ, u ^ 2 ∂θ.errors x) = θ.variance ∧
    (∫ u : ℝ, u ^ 4 ∂θ.errors x) ≤ C.fourthBound)

abbrev Estimator (d n : ℕ) :=
  {T : (Fin n → Observation d) → ℝ // Measurable T}

def meanSquaredRisk {d n : ℕ} (T : Estimator d n) (θ : RegressionParameter d) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((T.val z - θ.variance) ^ 2) ∂sampleLaw θ n

def worstCaseRisk {d n : ℕ} (C : ModelConstants d) (T : Estimator d n) : ℝ≥0∞ :=
  ⨆ θ : {θ : RegressionParameter d // Admissible C θ}, meanSquaredRisk T θ.val

def minimaxRisk {d : ℕ} (C : ModelConstants d) (n : ℕ) : ℝ≥0∞ :=
  ⨅ T : Estimator d n, worstCaseRisk C T

def minimaxRMS {d : ℕ} (C : ModelConstants d) (n : ℕ) : ℝ≥0∞ :=
  (minimaxRisk C n) ^ (1 / 2 : ℝ)

theorem designLaw_isProbability {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    IsProbabilityMeasure (designLaw θ) := by
  refine ⟨?_⟩
  simpa [designLaw, withDensity_apply] using hθ.2.2.2.1

theorem observationLaw_isProbability {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    IsProbabilityMeasure (observationLaw θ) := by
  letI := designLaw_isProbability C θ hθ
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_fst.prodMk ((hθ.2.1.comp measurable_fst).add measurable_snd)).aemeasurable).mpr
      inferInstance

theorem sampleLaw_isProbability {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (n : ℕ) :
    IsProbabilityMeasure (sampleLaw θ n) := by
  letI := observationLaw_isProbability C θ hθ
  exact inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => observationLaw θ)))

def constantEstimator (d n : ℕ) (v : ℝ) : Estimator d n :=
  ⟨fun _ => v, measurable_const⟩

theorem constantEstimator_risk_bound {d n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    meanSquaredRisk (constantEstimator d n C.varianceLower) θ ≤
      ENNReal.ofReal ((C.varianceUpper - C.varianceLower) ^ 2) := by
  letI := sampleLaw_isProbability C θ hθ n
  obtain ⟨_, _, _, _, _, hlo, hhi, _⟩ := hθ
  have hs : (C.varianceLower - θ.variance) ^ 2 ≤
      (C.varianceUpper - C.varianceLower) ^ 2 := by
    nlinarith [sq_nonneg (C.varianceUpper - θ.variance),
      mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
  unfold meanSquaredRisk constantEstimator
  simp only [lintegral_const, measure_univ, mul_one]
  exact ENNReal.ofReal_le_ofReal hs

theorem minimaxRisk_le_worstCaseRisk {d n : ℕ} (C : ModelConstants d)
    (T : Estimator d n) : minimaxRisk C n ≤ worstCaseRisk C T :=
  iInf_le _ T

theorem meanSquaredRisk_le_worstCaseRisk {d n : ℕ} (C : ModelConstants d)
    (T : Estimator d n) (θ : RegressionParameter d) (hθ : Admissible C θ) :
    meanSquaredRisk T θ ≤ worstCaseRisk C T :=
  le_iSup (fun θ : {θ : RegressionParameter d // Admissible C θ} =>
    meanSquaredRisk T θ.val) ⟨θ, hθ⟩

theorem minimaxRisk_finite {d : ℕ} (C : ModelConstants d) (n : ℕ) :
    minimaxRisk C n < ∞ := by
  apply lt_of_le_of_lt (minimaxRisk_le_worstCaseRisk C
    (constantEstimator d n C.varianceLower))
  unfold worstCaseRisk
  apply lt_of_le_of_lt (iSup_le fun (θ : {θ : RegressionParameter d // Admissible C θ}) =>
    constantEstimator_risk_bound (n := n) C θ.val θ.property)
  exact ENNReal.ofReal_lt_top

end NearlyMinimax
