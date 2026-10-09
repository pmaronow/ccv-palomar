module

public import Mathlib
public import RoughRegime.Rates


@[expose] public section

/-!
# The statistical model and main theorem statement

This module provides a model encoding on actual probability measures, with
Lebesgue random design, conditional expectations, coordinate derivatives,
and measurable randomized estimators. `PerModelUpperClaim`, `UniformUpperClaim`,
and `MainLowerClaim` record statements. `ModelUpper.lean` proves the uniform
upper bound with actual estimators. `ModelLower.lean` proves both lower
regimes from the original nondegeneracy condition, including the probability bound.

Coordinate derivatives are encoded by ordered lists of coordinate directions.
`MultiIndexHolder.lean` proves its exact equivalence to the paper's maximum
over classical multi-indices on the closed cube, using derivative symmetry
and boundary uniqueness. `KernelSeedBridge.lean` proves the representation of every real-output
randomized estimator by a uniform random seed, with equality of minimax risks.
`RiskBridge.lean` proves
the exact RMSE/squared-integral equivalence for the encoded experiment.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace RoughRegime.Model

abbrev Covariate (d : ℕ) := EuclideanSpace ℝ (Fin d)

def cube (d : ℕ) : Set (Covariate d) := {x | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1}

def cubeVolume (d : ℕ) : Measure (Covariate d) := volume.restrict (cube d)

def holderOrder (t : ℝ) : ℕ := Nat.ceil t - 1

def holderExponent (t : ℝ) : ℝ := t - holderOrder t

def coordinateDerivative {d : ℕ} (f : Covariate d → ℝ) (q : ℕ)
    (σ : Fin q → Fin d) (x : Covariate d) : ℝ :=
  iteratedFDerivWithin ℝ q f (cube d) x (fun j ↦ EuclideanSpace.single (σ j) 1)

def derivativeSup {d : ℕ} (f : Covariate d → ℝ) (k : ℕ) : ℝ≥0∞ :=
  ⨆ (q : ℕ) (_ : q ≤ k) (σ : Fin q → Fin d) (x : Covariate d) (_ : x ∈ cube d),
    ENNReal.ofReal |coordinateDerivative f q σ x|

def holderSeminorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (σ : Fin (holderOrder t) → Fin d) (x : Covariate d) (_ : x ∈ cube d)
    (y : Covariate d) (_ : y ∈ cube d) (_ : x ≠ y),
    ENNReal.ofReal (|coordinateDerivative f (holderOrder t) σ x -
      coordinateDerivative f (holderOrder t) σ y| / ‖x - y‖ ^ holderExponent t)

def holderNorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) : ℝ≥0∞ := by
  classical
  exact if 0 < t ∧ ContDiffOn ℝ (holderOrder t) f (cube d) then
    derivativeSup f (holderOrder t) + holderSeminorm f t else ∞

def holderBall {d : ℕ} (t H : ℝ) : Set (Covariate d → ℝ) :=
  {f | holderNorm f t ≤ ENNReal.ofReal H}

theorem holderNorm_bounds_values {d : ℕ} (f : Covariate d → ℝ) (t H : ℝ)
    (hH : 0 ≤ H) (hf : f ∈ holderBall t H) (x : Covariate d) (hx : x ∈ cube d) :
    |f x| ≤ H := by
  change holderNorm f t ≤ ENNReal.ofReal H at hf
  unfold holderNorm at hf
  split_ifs at hf with hreg
  · have hsup : derivativeSup f (holderOrder t) ≤ ENNReal.ofReal H :=
      le_trans le_self_add hf
    have hpoint : ENNReal.ofReal |f x| ≤ derivativeSup f (holderOrder t) := by
      unfold derivativeSup
      have hz : coordinateDerivative f 0 (Fin.elim0 : Fin 0 → Fin d) x = f x := rfl
      rw [← hz]
      exact le_iSup_of_le 0 (le_iSup_of_le (Nat.zero_le _)
        (le_iSup_of_le Fin.elim0 (le_iSup_of_le x (le_iSup_of_le hx le_rfl))))
    exact (ENNReal.ofReal_le_ofReal_iff hH).mp (hpoint.trans hsup)
  · exact False.elim ((ENNReal.ofReal_ne_top : ENNReal.ofReal H ≠ ∞) (top_le_iff.mp hf))

structure Parameters where
  d : ℕ
  α : ℝ
  β : ℝ
  H : ℝ
  δ : ℝ
  gminus : ℝ
  gplus : ℝ
  M0 : ℝ
  hd : 1 ≤ d
  hα : 0 < α
  hβ : 0 < β
  hH : 0 < H
  hδ : 0 < δ
  hgminus : 0 < gminus
  hgplus : gminus < gplus
  hM0 : 0 < M0

def Parameters.theta (A : Parameters) : ℝ := (A.α + A.β) / A.d

def Parameters.nu (A : Parameters) : ℕ :=
  (A.d + holderOrder A.α).choose A.d + (A.d + holderOrder A.β).choose A.d

structure Observables (Z : Type*) [MeasurableSpace Z] (A : Parameters) where
  D : Z → ℝ
  U : Z → ℝ
  V : Z → ℝ
  W : Z → ℝ
  lam : ℝ
  hlam : lam ≠ 0
  measurableD : Measurable D
  measurableU : Measurable U
  measurableV : Measurable V
  measurableW : Measurable W
  boundD : ∀ z, 0 ≤ D z ∧ D z ≤ A.M0
  boundU : ∀ z, |U z| ≤ A.M0
  boundV : ∀ z, |V z| ≤ A.M0
  boundW : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |W z| ≤ C

abbrev Observation (A : Parameters) (Z : Type*) := Covariate A.d × Z

abbrev covariateInformation (A : Parameters) (Z : Type*) [MeasurableSpace Z] :
    MeasurableSpace (Observation A Z) := MeasurableSpace.comap Prod.fst inferInstance

/-- A witness consists of the density and versions of the conditional ratios. -/
structure ModelWitness (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) where
  p : Covariate A.d → ℝ
  w : Covariate A.d → ℝ
  a : Covariate A.d → ℝ
  b : Covariate A.d → ℝ
  measurableP : Measurable p
  measurableW : Measurable w
  measurableA : Measurable a
  measurableB : Measurable b
  nonnegativeP : 0 ≤ᵐ[cubeVolume A.d] p
  marginal : (P : Measure (Observation A Z)).map Prod.fst =
    (cubeVolume A.d).withDensity (fun x ↦ ENNReal.ofReal (p x))
  momentD : (P : Measure (Observation A Z))[F.D ∘ Prod.snd | covariateInformation A Z] =ᵐ[(P : Measure (Observation A Z))]
    w ∘ Prod.fst
  momentU : (P : Measure (Observation A Z))[F.U ∘ Prod.snd | covariateInformation A Z] =ᵐ[(P : Measure (Observation A Z))]
    fun o ↦ w o.1 * a o.1
  momentV : (P : Measure (Observation A Z))[F.V ∘ Prod.snd | covariateInformation A Z] =ᵐ[(P : Measure (Observation A Z))]
    fun o ↦ w o.1 * b o.1
  overlap : ∀ᵐ x ∂cubeVolume A.d, A.δ ≤ w x
  smoothA : a ∈ holderBall A.α A.H
  smoothB : b ∈ holderBall A.β A.H
  densityBounds : ∀ᵐ x ∂cubeVolume A.d,
    A.gminus ≤ w x * p x ∧ w x * p x ≤ A.gplus

def modelClass (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A) :
    Set (ProbabilityMeasure (Observation A Z)) := {P | Nonempty (ModelWitness A F P)}

/-- The generic target is defined directly using conditional moments. -/
def target (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (P : ProbabilityMeasure (Observation A Z)) : ℝ :=
  (∫ o, F.W o.2 ∂(P : Measure (Observation A Z))) + F.lam * ∫ o,
    ((P : Measure (Observation A Z))[F.U ∘ Prod.snd | covariateInformation A Z]) o *
    ((P : Measure (Observation A Z))[F.V ∘ Prod.snd | covariateInformation A Z]) o /
    ((P : Measure (Observation A Z))[F.D ∘ Prod.snd | covariateInformation A Z]) o ∂(P : Measure (Observation A Z))

def randomizedExperiment {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (P : ProbabilityMeasure Ω) : Measure ((Fin n → Ω) × ℝ) :=
  (Measure.pi (fun _ : Fin n ↦ (P : Measure Ω))).prod (volume.restrict (Set.Icc (0 : ℝ) 1))

abbrev Estimator (Ω : Type*) [MeasurableSpace Ω] (n : ℕ) :=
  {f : (Fin n → Ω) × ℝ → ℝ // Measurable f}

def minimaxRMSE {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω)) : ℝ≥0∞ :=
  ⨅ f : Estimator Ω n, ⨆ (P : ProbabilityMeasure Ω) (_ : P ∈ C),
    eLpNorm (fun o ↦ f.1 o - T P) 2 (randomizedExperiment n P)

def minimaxTail {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω)) (t : ℝ) : ℝ≥0∞ :=
  ⨅ f : Estimator Ω n, ⨆ (P : ProbabilityMeasure Ω) (_ : P ∈ C),
    randomizedExperiment n P {o | t ≤ |f.1 o - T P|}

/-- The upper inequalities at specified constants. -/
def UpperBoundAt (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (C : ℝ) (n0 : ℕ) : Prop :=
  ∀ n : ℕ, n0 ≤ n →
    (modelClass A F).Nonempty →
      (1 / 2 ≤ A.theta → minimaxRMSE n (target A F) (modelClass A F) ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (-(1 / 2 : ℝ)))) ∧
      (0 < A.theta ∧ A.theta < 1 / 2 → minimaxRMSE n (target A F) (modelClass A F) ≤
        ENNReal.ofReal (C * RoughRegime.Rates.subcriticalScale n A.theta
          (RoughRegime.Rates.tau A.gminus A.gplus) *
          (Real.log n) ^ ((A.nu : ℝ) / 2 + 1 / 4)))

/-- The per-model consequence of Theorem 1(a). This does not assert
the theorem's uniformity over response functions or response spaces. -/
def PerModelUpperClaim (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧ UpperBoundAt A F C n0

/-- Uniform upper statement, over response spaces in a fixed universe
and all observables with the same magnitude of λ and the stated W bound. -/
def UniformUpperClaim (A : Parameters) (L MW : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
    ∀ (Z : Type*) (mZ : MeasurableSpace Z) (F : @Observables Z mZ A),
      |F.lam| = L → (∀ z, |F.W z| ≤ MW) → UpperBoundAt A F C n0

def baselineW (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (π : ProbabilityMeasure Z) : ℝ := ∫ z, F.D z ∂(π : Measure Z)

def baselineA (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (π : ProbabilityMeasure Z) : ℝ := (∫ z, F.U z ∂(π : Measure Z)) / baselineW A F π

def baselineB (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (π : ProbabilityMeasure Z) : ℝ := (∫ z, F.V z ∂(π : Measure Z)) / baselineW A F π

def Nondegenerate (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (π : ProbabilityMeasure Z) : Prop :=
  (∃ s : Finset Z, (π : Measure Z) (s : Set Z) = 1) ∧
  max A.δ A.gminus < baselineW A F π ∧ baselineW A F π < A.gplus ∧
  |baselineA A F π| < A.H ∧ |baselineB A F π| < A.H ∧
  (let rU := fun z ↦ F.U z - baselineA A F π * F.D z
   let rV := fun z ↦ F.V z - baselineB A F π * F.D z
   let uu := ∫ z, rU z ^ 2 ∂(π : Measure Z)
   let uv := ∫ z, rU z * rV z ∂(π : Measure Z)
   let vv := ∫ z, rV z ^ 2 ∂(π : Measure Z)
   (0 < uu ∧ 0 < uu * vv - uv ^ 2) ∨ (F.U = F.V ∧ A.α = A.β ∧ 0 < uu))

def localClass (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (π : ProbabilityMeasure Z) (r : ℝ) : Set (ProbabilityMeasure (Observation A Z)) :=
  {P | ∃ h : ModelWitness A F P, ∀ᵐ x ∂cubeVolume A.d,
    |h.w x - baselineW A F π| ≤ r ∧ |h.a x - baselineA A F π| ≤ r ∧
      |h.b x - baselineB A F π| ≤ r}

theorem localClass_subset (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π : ProbabilityMeasure Z) (r : ℝ) :
    localClass A F π r ⊆ modelClass A F := by
  intro P hP
  obtain ⟨h, _⟩ := hP
  exact ⟨h⟩

theorem minimaxRMSE_mono_class {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (T : ProbabilityMeasure Ω → ℝ) {C D : Set (ProbabilityMeasure Ω)} (hCD : C ⊆ D) :
    minimaxRMSE n T C ≤ minimaxRMSE n T D := by
  unfold minimaxRMSE
  apply iInf_mono
  intro f
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  exact le_iSup_of_le P (le_iSup_of_le (hCD hP) le_rfl)

theorem minimaxTail_mono_class {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (T : ProbabilityMeasure Ω → ℝ) (t : ℝ)
    {C D : Set (ProbabilityMeasure Ω)} (hCD : C ⊆ D) :
    minimaxTail n T C t ≤ minimaxTail n T D t := by
  unfold minimaxTail
  apply iInf_mono
  intro f
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  exact le_iSup_of_le P (le_iSup_of_le (hCD hP) le_rfl)

theorem marginal_integral (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z))
    (h : ModelWitness A F P) (f : Covariate A.d → ℝ) (hf : Measurable f) :
    (∫ o, f o.1 ∂(P : Measure (Observation A Z))) =
      ∫ x, h.p x * f x ∂cubeVolume A.d := by
  rw [← integral_map_of_stronglyMeasurable measurable_fst hf.stronglyMeasurable,
    h.marginal, integral_withDensity_eq_integral_toReal_smul
      (f := fun x ↦ ENNReal.ofReal (h.p x))
      (ENNReal.measurable_ofReal.comp h.measurableP)
      (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [h.nonnegativeP] with x hx
  simp [ENNReal.toReal_ofReal hx]

theorem witness_overlap_on_observations (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z))
    (h : ModelWitness A F P) :
    ∀ᵐ o ∂(P : Measure (Observation A Z)), A.δ ≤ h.w o.1 := by
  apply ae_of_ae_map (μ := (P : Measure (Observation A Z)))
    (f := Prod.fst) (p := fun x ↦ A.δ ≤ h.w x) measurable_fst.aemeasurable
  rw [h.marginal]
  apply (ae_withDensity_iff (ENNReal.measurable_ofReal.comp h.measurableP)).mpr
  filter_upwards [h.overlap] with x hx
  intro _
  exact hx

theorem witness_density_positive (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z))
    (h : ModelWitness A F P) : ∀ᵐ x ∂cubeVolume A.d, 0 < h.p x := by
  filter_upwards [h.nonnegativeP, h.densityBounds] with x hx hbounds
  have hn : h.p x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hbounds
    linarith [A.hgminus, hbounds.1]
  exact lt_of_le_of_ne hx (Ne.symm hn)

theorem witness_response_upper (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z))
    (h : ModelWitness A F P) : ∀ᵐ x ∂cubeVolume A.d, h.w x ≤ A.M0 := by
  let μ : Measure (Observation A Z) := P
  have : IsProbabilityMeasure μ := P.prop
  have hDi : Integrable (F.D ∘ Prod.snd) μ := by
    apply Integrable.of_bound (F.measurableD.comp measurable_snd).aestronglyMeasurable A.M0
    filter_upwards [] with o
    simpa [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (F.boundD o.2).1]
      using (F.boundD o.2).2
  have hm : covariateInformation A Z ≤ (inferInstance : MeasurableSpace (Observation A Z)) :=
    measurable_fst.comap_le
  have hc := condExp_mono (m := covariateInformation A Z) hDi (integrable_const A.M0)
    (Filter.Eventually.of_forall fun o ↦ (F.boundD o.2).2)
  rw [condExp_const hm A.M0] at hc
  have hw : ∀ᵐ o ∂μ, h.w o.1 ≤ A.M0 := by
    filter_upwards [hc, h.momentD] with o hco hwo
    change μ[F.D ∘ Prod.snd | covariateInformation A Z] o = h.w o.1 at hwo
    rw [hwo] at hco
    exact hco
  have hmap : ∀ᵐ x ∂μ.map Prod.fst, h.w x ≤ A.M0 :=
    (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_le h.measurableW measurable_const)).mpr hw
  change ∀ᵐ x ∂(P : Measure (Observation A Z)).map Prod.fst, h.w x ≤ A.M0 at hmap
  rw [h.marginal, ae_withDensity_iff
    (f := fun x ↦ ENNReal.ofReal (h.p x))
    (ENNReal.measurable_ofReal.comp h.measurableP)] at hmap
  filter_upwards [hmap, witness_density_positive A F P h] with x hx hp
  exact hx (ENNReal.ofReal_ne_zero_iff.mpr hp)

/-- The setting's asserted bounds on the unknown covariate density. -/
theorem covariate_density_bounds (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z))
    (h : ModelWitness A F P) : ∀ᵐ x ∂cubeVolume A.d,
      A.gminus / A.M0 ≤ h.p x ∧ h.p x ≤ A.gplus / A.δ := by
  filter_upwards [h.nonnegativeP, h.overlap, h.densityBounds,
    witness_response_upper A F P h] with x hp hw hg hwup
  constructor
  · apply (div_le_iff₀ A.hM0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hwup hp]
  · apply (le_div_iff₀ A.hδ).mpr
    nlinarith [mul_le_mul_of_nonneg_right hw hp]

/-- Equation (2): the conditional-ratio target equals the weighted integral. -/
theorem target_weighted_representation (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z))
    (h : ModelWitness A F P) :
    target A F P = (∫ o, F.W o.2 ∂(P : Measure (Observation A Z))) + F.lam *
      ∫ x, h.a x * h.b x * (h.w x * h.p x) ∂cubeVolume A.d := by
  unfold target
  congr 1
  congr 1
  calc
    _ = ∫ o, h.a o.1 * h.b o.1 * h.w o.1 ∂(P : Measure (Observation A Z)) := by
      apply integral_congr_ae
      filter_upwards [h.momentD, h.momentU, h.momentV,
        witness_overlap_on_observations A F P h] with o hD hU hV hw
      simp only [Function.comp_apply] at hD
      rw [hD, hU, hV]
      have hw0 : h.w o.1 ≠ 0 := ne_of_gt (lt_of_lt_of_le A.hδ hw)
      field_simp
    _ = _ := by
      rw [marginal_integral A F P h (fun x ↦ h.a x * h.b x * h.w x)
        ((h.measurableA.mul h.measurableB).mul h.measurableW)]
      apply integral_congr_ae
      filter_upwards [] with x
      ring

/-- Theorem 1(b)'s statement; `ModelLower.lean` proves it, including the probability bound. -/
def MainLowerClaim (A : Parameters) {Z : Type*} [MeasurableSpace Z] (F : Observables Z A)
    (π : ProbabilityMeasure Z) (r : ℝ) : Prop :=
  Nondegenerate A F π → 0 < r →
  ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
    ∀ C' : Set (ProbabilityMeasure (Observation A Z)),
      localClass A F π r ⊆ C' → C' ⊆ modelClass A F → ∀ n : ℕ, n0 ≤ n →
        (1 / 2 ≤ A.theta → ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
          minimaxRMSE n (target A F) C') ∧
        (0 < A.theta ∧ A.theta < 1 / 2 →
          let a := RoughRegime.Rates.subcriticalScale n A.theta
            (RoughRegime.Rates.tau A.gminus A.gplus)
          ENNReal.ofReal (c * a * Real.log n) ≤ minimaxRMSE n (target A F) C' ∧
          (1 / 4 : ℝ≥0∞) ≤ minimaxTail n (target A F) C' (2 * c * a * Real.log n))

end RoughRegime.Model
