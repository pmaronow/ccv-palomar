module

public import Mathlib

@[expose] public section

/-!
# Nearly minimax variance estimation: submission statements

This module states Theorem 1.1, both conclusions of Corollary 1.2,
Theorem 1.3, and Theorem 1.4 of the accompanying paper. It imports only
Mathlib and gives the statistical model, loss, and rate scales concretely.
The five theorem placeholders are intentional; their proved counterparts
are in `Solution.lean`.

Observations are independent copies of `(X, f(X) + error)` on the unit
cube. The design density is unknown. The errors may depend on `X`, have
conditional mean zero, a common conditional variance, and a bounded
conditional fourth moment. The regression extends to an open neighborhood
of the cube with the displayed Euclidean Hölder norm bound.

The norm uses pointwise suprema on this open neighborhood and distinct
multi-indices. The development proves equivalence with the paper's
essential-supremum convention. The constraints on `order` force
`order = ceil(smoothness) - 1`, including integer smoothness.
The explicit moment integrability clauses give Lebesgue integrals their
intended meaning; finite fourth moments of the probability kernels entail
the lower moment integrability requirements.

Risk is the supremum of mean squared error over the admissible class,
minimized over measurable estimators, then square-rooted. Extended
nonnegative integrals retain infinite risks. Theorem 1.1 puts its constants
and threshold before the open-domain quantifier. The low-smoothness and
parametric statements fix the domain in `C`; they do not separately assert
uniformity over all extension domains. Corollary 1.2 retains constants
independent of epsilon, with an eventual threshold that may depend on it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators Topology

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

/-- The root-mean-square polynomial exponent. -/
def rateExponent (s d : ℝ) : ℝ := 2 * (s + 1) / (d + 4)

/-- The logarithmic power in the lower risk scale. -/
def lowerLogPower (s d : ℝ) : ℝ := (s - 1) / (d + 4)

/-- The common stretched-exponential constant in the paper. -/
def stretchConstant (s d τ : ℝ) : ℝ :=
  4 * Real.sqrt (2 * τ * (s - 1) * (d - 4 * s) / (d + 4) ^ 3)

/-- Only the open extension domain varies; the numerical model constants stay fixed. -/
structure ExtensionDomain (d : ℕ) where
  carrier : Set (Covariate d)
  isOpen : IsOpen carrier
  cube_subset : unitCube d ⊆ carrier

def ModelConstants.originalDomain {d : ℕ} (C : ModelConstants d) : ExtensionDomain d :=
  ⟨C.domain, C.domain_open, C.cube_subset⟩

def ModelConstants.withDomain {d : ℕ} (C : ModelConstants d)
    (U : ExtensionDomain d) : ModelConstants d :=
  { C with domain := U.carrier, domain_open := U.isOpen, cube_subset := U.cube_subset }

def highSmoothnessRegime {d : ℕ} (C : ModelConstants d) : Prop :=
  1 < C.smoothness ∧ 4 * C.smoothness < (d : ℝ)

/-- The density-ratio parameter in (main-constants). -/
def paperTau {d : ℕ} (C : ModelConstants d) : ℝ :=
  Real.log ((Real.sqrt C.densityUpper + Real.sqrt C.densityLower) /
    (Real.sqrt C.densityUpper - Real.sqrt C.densityLower))

def paperPolynomialDimension {d : ℕ} (C : ModelConstants d) : ℕ :=
  Nat.choose (d + C.order) d

def paperLogGap {d : ℕ} (C : ModelConstants d) : ℝ :=
  (d : ℝ) * ((paperPolynomialDimension C : ℝ) - 1 / 2) / ((d : ℝ) + 4)

/-- Exactly the displayed lower scale `Psi_n`. -/
def paperRiskScale {d : ℕ} (C : ModelConstants d) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-rateExponent C.smoothness d) *
    Real.exp (-stretchConstant C.smoothness d (paperTau C) * Real.sqrt (Real.log n)) *
    (Real.log n) ^ lowerLogPower C.smoothness d

def lowSmoothnessScale (s : ℝ) (d n : ℕ) : ℝ :=
  max ((n : ℝ) ^ (-(1 / 2 : ℝ))) ((n : ℝ) ^ (-(4 * s / ((d : ℝ) + 4 * s))))

namespace Submission

/-- Theorem 1.1: the near-matching lower and upper bounds in the regime
`1 < s < d/4`; constants and threshold are uniform over extension domains. -/
theorem paper_main {d : ℕ} (C : ModelConstants d) :
    highSmoothnessRegime C →
      ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
        ∀ (U : ExtensionDomain d) (n : ℕ), n₀ ≤ n →
          ENNReal.ofReal (c * paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n ∧
          minimaxRMS (C.withDomain U) n ≤
            ENNReal.ofReal (A * paperRiskScale C n * (Real.log n) ^ paperLogGap C) := by
  sorry

/-- Corollary 1.2: the root-mean-square minimax exponent equals `2(s+1)/(d+4)`. -/
theorem exponent_limit {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    Tendsto (fun n : ℕ => -Real.log (minimaxRMS C n).toReal / Real.log (n : ℝ))
      atTop (𝓝 (rateExponent C.smoothness d)) := by
  sorry

/-- Corollary 1.2: eventual polynomial brackets for every positive epsilon.
The two constants precede epsilon; the eventual threshold can depend on it. -/
theorem polynomial_bounds {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        c * (n : ℝ) ^ (-rateExponent C.smoothness d - epsilon) ≤ (minimaxRMS C n).toReal ∧
        (minimaxRMS C n).toReal ≤ A * (n : ℝ) ^ (-rateExponent C.smoothness d) := by
  sorry

/-- Theorem 1.3: for `0 < s ≤ 1`, the maximum of the parametric and
nonparametric RMS scales brackets minimax RMS for every `n ≥ 1`. -/
theorem low_smoothness {d : ℕ} (C : ModelConstants d) :
    C.smoothness ≤ 1 → ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (A⁻¹ * lowSmoothnessScale C.smoothness d n) ≤ minimaxRMS C n ∧
      minimaxRMS C n ≤ ENNReal.ofReal (A * lowSmoothnessScale C.smoothness d n) := by
  sorry

/-- Theorem 1.4: for `s > 1` and `d ≤ 4s`, parametric RMS brackets hold
for every `n ≥ 1`, including the boundary `d = 4s`. -/
theorem parametric {d : ℕ} (C : ModelConstants d) :
    1 < C.smoothness → (d : ℝ) ≤ 4 * C.smoothness →
      ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
        ENNReal.ofReal (A⁻¹ * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ minimaxRMS C n ∧
        minimaxRMS C n ≤ ENNReal.ofReal (A * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  sorry

end Submission
end NearlyMinimax
