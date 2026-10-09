module

public import NearlyMinimax.HighRawUpdates
public import NearlyMinimax.TernaryMeasure


@[expose] public section

/-! Pointwise locality of the actual affine masked history recursion.
Changing all marks at one label cannot affect density outside that label's
patch, even when later overlapping updates are applied. Consequently the
actual integrated raw mass has the source's label-block oscillation bound. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

section Recursion
variable {J X E C I : Type*} [DecidableEq J]

/-- A full density/coefficient history, allowing the affine density slope
to depend on the entire genuine mark (including its representation mark). -/
def affineRawHistory (patch : J → Set X) (slope intercept : J → E → X → ℝ)
    (response : J → E → C → C) (labels : I → J) (indices : List I)
    (marks : I → E) (initial : (X → ℝ) × (J → C)) : (X → ℝ) × (J → C) :=
  indices.foldl (fun state i => rawPatchUpdate (labels i) (patch (labels i))
    (slope (labels i) (marks i)) (intercept (labels i) (marks i))
    (response (labels i) (marks i)) state) initial

theorem affineRawHistory_density_eq_outside_label
    (patch : J → Set X) (slope intercept : J → E → X → ℝ)
    (response : J → E → C → C) (labels : I → J) (indices : List I)
    (marks marks' : I → E) (j : J) (hm : ∀ i, labels i ≠ j → marks i = marks' i)
    (initial initial' : (X → ℝ) × (J → C)) (x : X) (hx : x ∉ patch j)
    (hi : initial.1 x = initial'.1 x) :
    (affineRawHistory patch slope intercept response labels indices marks initial).1 x =
      (affineRawHistory patch slope intercept response labels indices marks' initial').1 x := by
  induction indices generalizing initial initial' with
  | nil => exact hi
  | cons i indices ih =>
    apply ih
    dsimp only
    by_cases hlabel : labels i = j
    · simp only [rawPatchUpdate, affinePatchUpdate, hlabel, ite_eq_right hx]
      exact hi
    · rw [hm i hlabel]
      change (if x ∈ patch (labels i) then
        slope (labels i) (marks' i) x * initial.1 x + intercept (labels i) (marks' i) x
        else initial.1 x) = (if x ∈ patch (labels i) then
        slope (labels i) (marks' i) x * initial'.1 x + intercept (labels i) (marks' i) x
        else initial'.1 x)
      rw [hi]

theorem affineRawHistory_density_difference_supported
    (patch : J → Set X) (slope intercept : J → E → X → ℝ)
    (response : J → E → C → C) (labels : I → J) (indices : List I)
    (marks marks' : I → E) (j : J) (hm : ∀ i, labels i ≠ j → marks i = marks' i)
    (initial : (X → ℝ) × (J → C)) :
    support (fun x =>
      (affineRawHistory patch slope intercept response labels indices marks initial).1 x -
      (affineRawHistory patch slope intercept response labels indices marks' initial).1 x) ⊆ patch j := by
  intro x hx
  by_contra h
  exact hx (sub_eq_zero.mpr (affineRawHistory_density_eq_outside_label patch slope intercept
    response labels indices marks marks' j hm initial initial x h rfl))

theorem affineRawHistory_density_interval (patch : J → Set X)
    (slope intercept : J → E → X → ℝ) (response : J → E → C → C)
    (labels : I → J) (indices : List I) (marks : I → E)
    (a b : ℝ)
    (hlegal : ∀ j e x v, v ∈ Icc a b → slope j e x * v + intercept j e x ∈ Icc a b)
    (initial : (X → ℝ) × (J → C)) (hi : ∀ x, initial.1 x ∈ Icc a b) :
    ∀ x, (affineRawHistory patch slope intercept response labels indices marks initial).1 x ∈ Icc a b := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih =>
    apply ih
    intro x
    dsimp only
    change (if x ∈ patch (labels i) then slope (labels i) (marks i) x * initial.1 x +
      intercept (labels i) (marks i) x else initial.1 x) ∈ Icc a b
    split_ifs
    · exact hlegal _ _ _ _ (hi x)
    · exact hi x

theorem affineRawHistory_density_measurable [MeasurableSpace X]
    (patch : J → Set X) (hpatch : ∀ j, MeasurableSet (patch j))
    (slope intercept : J → E → X → ℝ)
    (hSlope : ∀ j e, Measurable (slope j e)) (hIntercept : ∀ j e, Measurable (intercept j e))
    (response : J → E → C → C) (labels : I → J) (indices : List I) (marks : I → E)
    (initial : (X → ℝ) × (J → C)) (hi : Measurable initial.1) :
    Measurable (affineRawHistory patch slope intercept response labels indices marks initial).1 := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih =>
    apply ih
    dsimp only
    change Measurable (fun x => if x ∈ patch (labels i) then
      slope (labels i) (marks i) x * initial.1 x + intercept (labels i) (marks i) x else initial.1 x)
    exact Measurable.ite (hpatch _) (((hSlope _ _).mul hi).add (hIntercept _ _)) hi

end Recursion

theorem integral_mass_difference_le_patch {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (P : Set X) (hP : MeasurableSet P)
    (p p' : X → ℝ) (hpm : Measurable p) (hp'm : Measurable p')
    (a b : ℝ) (hab : a ≤ b) (hp : ∀ x, p x ∈ Icc a b) (hp' : ∀ x, p' x ∈ Icc a b)
    (hsupport : ∀ x, x ∉ P → p x = p' x) :
    |(∫ x, p x ∂μ) - ∫ x, p' x ∂μ| ≤ μ.real P * (b - a) := by
  let K : ℝ := max |a| |b|
  have hbound (q : X → ℝ) (hq : ∀ x, q x ∈ Icc a b) (x : X) : ‖q x‖ ≤ K := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have hKa : |a| ≤ K := le_max_left _ _
      linarith [(hq x).1, neg_abs_le a]
    · have hKb : |b| ≤ K := le_max_right _ _
      exact (hq x).2.trans ((le_abs_self b).trans hKb)
  have hi : Integrable p μ := (integrable_const K).mono' hpm.aestronglyMeasurable
    (Filter.Eventually.of_forall (hbound p hp))
  have hi' : Integrable p' μ := (integrable_const K).mono' hp'm.aestronglyMeasurable
    (Filter.Eventually.of_forall (hbound p' hp'))
  have hdiff (x : X) : |p x - p' x| ≤ P.indicator (fun _ => b-a) x := by
    by_cases hx : x ∈ P
    · rw [Set.indicator_of_mem hx]
      apply abs_le.mpr
      constructor <;> linarith [(hp x).1, (hp x).2, (hp' x).1, (hp' x).2]
    · rw [Set.indicator_of_notMem hx, hsupport x hx, sub_self, abs_zero]
  rw [← integral_sub hi hi']
  calc
    _ ≤ ∫ x, |p x-p' x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => p x-p' x)
    _ ≤ ∫ x, P.indicator (fun _ => b-a) x ∂μ :=
      integral_mono (hi.sub hi').abs ((integrable_const (b-a)).indicator hP) hdiff
    _ = _ := by rw [integral_indicator_const _ hP, smul_eq_mul]

theorem highTorusPatch_real_volume_le (d k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (j : HighWindowLabels d k) :
    (cubeVolume d).real (highTorusPatch d k j) ≤ (2 / (k : ℝ))^d := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have h := ENNReal.toReal_mono (by finiteness)
    (highTorusPatch_volume_le d k hk j)
  simpa only [measureReal_def, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 / (k : ℝ))] using h

theorem highAffineRawHistory_mass_block_oscillation {E C : Type*}
    (d k n : ℕ) [NeZero k] (hk : 2 ≤ k)
    (slope intercept : HighWindowLabels d k → E → Covariate d → ℝ)
    (hSlope : ∀ j e, Measurable (slope j e)) (hIntercept : ∀ j e, Measurable (intercept j e))
    (response : HighWindowLabels d k → E → C → C)
    (labels : Fin n → HighWindowLabels d k) (indices : List (Fin n))
    (marks marks' : Fin n → E) (j : HighWindowLabels d k)
    (hm : ∀ i, labels i ≠ j → marks i = marks' i)
    (a b : ℝ) (hab : a ≤ b)
    (hlegal : ∀ l e x v, v ∈ Icc a b → slope l e x * v + intercept l e x ∈ Icc a b)
    (initial : (Covariate d → ℝ) × (HighWindowLabels d k → C))
    (him : Measurable initial.1) (hi : ∀ x, initial.1 x ∈ Icc a b) :
    |(∫ x, (affineRawHistory (highTorusPatch d k) slope intercept response labels indices marks initial).1 x
        ∂cubeVolume d) -
      ∫ x, (affineRawHistory (highTorusPatch d k) slope intercept response labels indices marks' initial).1 x
        ∂cubeVolume d| ≤ (2 / (k : ℝ))^d * (b-a) := by
  let _ := cubeVolume_isProbability d
  apply (integral_mass_difference_le_patch (cubeVolume d) (highTorusPatch d k j)
    (highTorusPatch_measurableSet d k j) _ _
    (affineRawHistory_density_measurable (highTorusPatch d k) (highTorusPatch_measurableSet d k)
      slope intercept hSlope hIntercept response labels indices marks initial him)
    (affineRawHistory_density_measurable (highTorusPatch d k) (highTorusPatch_measurableSet d k)
      slope intercept hSlope hIntercept response labels indices marks' initial him)
    a b hab
    (affineRawHistory_density_interval (highTorusPatch d k) slope intercept response labels indices
      marks a b hlegal initial hi)
    (affineRawHistory_density_interval (highTorusPatch d k) slope intercept response labels indices
      marks' a b hlegal initial hi)
    (fun x hx => affineRawHistory_density_eq_outside_label (highTorusPatch d k) slope intercept response
      labels indices marks marks' j hm initial initial x hx rfl)).trans
  exact mul_le_mul_of_nonneg_right (highTorusPatch_real_volume_le d k hk j) (sub_nonneg.mpr hab)

def highAffineMarkedMass {E C : Type*} (d k : ℕ) [NeZero k]
    [LinearOrder (HighWindowLabels d k)] (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)
    (slope intercept : HighWindowLabels d k → E → Covariate d → ℝ)
    (response : HighWindowLabels d k → E → C → C)
    (initial : (Covariate d → ℝ) × (HighWindowLabels d k → C))
    (h : HistoryMarked dependent E) : ℝ :=
  ∫ x, (historyMarkedRawState dependent
    (fun j e state => rawPatchUpdate j (highTorusPatch d k j) (slope j e) (intercept j e)
      (response j e) state) initial h).1 x ∂cubeVolume d

/-- The actual canonical marked history mass has bounded differences when
an entire label block of independent marks is replaced. -/
theorem highAffineMarkedMass_block_oscillation {E C : Type*}
    (d k : ℕ) [NeZero k] [LinearOrder (HighWindowLabels d k)] (hk : 2 ≤ k)
    (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)
    (slope intercept : HighWindowLabels d k → E → Covariate d → ℝ)
    (hSlope : ∀ j e, Measurable (slope j e)) (hIntercept : ∀ j e, Measurable (intercept j e))
    (response : HighWindowLabels d k → E → C → C)
    (a b : ℝ) (hab : a ≤ b)
    (hlegal : ∀ l e x v, v ∈ Icc a b → slope l e x * v + intercept l e x ∈ Icc a b)
    (initial : (Covariate d → ℝ) × (HighWindowLabels d k → C))
    (him : Measurable initial.1) (hi : ∀ x, initial.1 x ∈ Icc a b)
    (g : HistoryShape (fun l j => ¬ dependent l j))
    (marks marks' : Fin (historyShapeLength dependent g) → E) (j : HighWindowLabels d k)
    (hm : ∀ i, historyShapeCanonicalLabels dependent g i ≠ j → marks i = marks' i) :
    |highAffineMarkedMass d k dependent slope intercept response initial ⟨g, marks⟩ -
      highAffineMarkedMass d k dependent slope intercept response initial ⟨g, marks'⟩| ≤
        (2 / (k : ℝ))^d * (b-a) := by
  exact highAffineRawHistory_mass_block_oscillation d k (historyShapeLength dependent g) hk
    slope intercept hSlope hIntercept response (historyShapeCanonicalLabels dependent g)
    (List.ofFn (fun i : Fin (historyShapeLength dependent g) => i)) marks marks' j hm
    a b hab hlegal initial him hi

end NearlyMinimax
