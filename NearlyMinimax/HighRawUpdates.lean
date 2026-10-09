module

public import NearlyMinimax.HighWindowGeometry
public import NearlyMinimax.HighFrameCoefficientBridge
public import NearlyMinimax.HighDensityUpdates
public import NearlyMinimax.HistoryReferenceMeasure


@[expose] public section

/-! Actual density/coefficient state maps for the high-regime marked prior. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

abbrev HighRawState (d k D : ℕ) :=
  (Covariate d → ℝ) × (HighWindowLabels d k → (HighFrameIndex d D → ℝ))

abbrev HighRawMark (d D r : ℕ) :=
  ℝ × ((Fin r → ℝ) × ((HighFrameIndex d D → ℝ) × ℝ))

def HighRawMarkValid (d D r : ℕ) (a b Cfr : ℝ) (e : HighRawMark d D r) : Prop :=
  e.1 ∈ Icc a b ∧ (∀ l, |e.2.1 l| ≤ 1) ∧
    (∑ γ, |e.2.2.1 γ| ≤ Cfr⁻¹) ∧ e.2.2.2 ∈ Icc (0 : ℝ) 1

def HighRawStateValid (d k D : ℕ) (a b Cfr : ℝ) (θ : HighRawState d k D) : Prop :=
  Measurable θ.1 ∧ (∀ x, θ.1 x ∈ Icc a b) ∧
    (∀ j, ∑ γ, |θ.2 j γ| ≤ Cfr⁻¹)

theorem highRawMarkValid_measurableSet (d D r : ℕ) (a b Cfr : ℝ) :
    MeasurableSet {e : HighRawMark d D r | HighRawMarkValid d D r a b Cfr e} := by
  unfold HighRawMarkValid
  have hz : MeasurableSet {e : HighRawMark d D r | e.1 ∈ Icc a b} :=
    measurableSet_Icc.preimage measurable_fst
  have hε : MeasurableSet {e : HighRawMark d D r | ∀ l, |e.2.1 l| ≤ 1} := by
    simp_rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro l
    exact measurableSet_le (by fun_prop) measurable_const
  have hv : MeasurableSet {e : HighRawMark d D r | ∑ γ, |e.2.2.1 γ| ≤ Cfr⁻¹} :=
    measurableSet_le (by fun_prop) measurable_const
  have hσ : MeasurableSet {e : HighRawMark d D r | e.2.2.2 ∈ Icc (0 : ℝ) 1} :=
    measurableSet_Icc.preimage (by fun_prop)
  exact hz.inter (hε.inter (hv.inter hσ))

def highRawSlope (a b : ℝ) (r : ℕ) {d D : ℕ}
    (B : Covariate d → Fin r → ℝ) (e : HighRawMark d D r) (x : Covariate d) : ℝ :=
  densityMargin a b e.1 / ((r : ℝ) * b) * ∑ l, e.2.1 l * B x l

def highRawUpdate (d k D r : ℕ) (a b : ℝ) (j : HighWindowLabels d k)
    (B : Covariate d → Fin r → ℝ) (e : HighRawMark d D r) (θ : HighRawState d k D) :
    HighRawState d k D :=
  rawPatchUpdate j (highTorusPatch d k j) (highRawSlope a b r B e) (fun _ => e.1)
    (fun c => coefficientReset c e.2.2.1 e.2.2.2) θ

theorem highRawUpdate_measurable (d k D r : ℕ) (a b : ℝ) (j : HighWindowLabels d k)
    (B : Covariate d → Fin r → ℝ) :
    Measurable (fun eθ : HighRawMark d D r × HighRawState d k D =>
      highRawUpdate d k D r a b j B eθ.1 eθ.2) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro x
    by_cases hx : x ∈ highTorusPatch d k j
    · simp only [highRawUpdate, rawPatchUpdate, affinePatchUpdate, ite_eq_left hx,
        highRawSlope, densityMargin]
      fun_prop
    · simp only [highRawUpdate, rawPatchUpdate, affinePatchUpdate, ite_eq_right hx]
      exact (measurable_pi_apply x).comp (measurable_fst.comp measurable_snd)
  · apply measurable_pi_lambda
    intro l
    apply measurable_pi_lambda
    intro γ
    by_cases hj : l = j
    · subst l
      simp only [highRawUpdate, rawPatchUpdate, responseCoordinateUpdate,
        Function.update_self, coefficientReset]
      fun_prop
    · simp only [highRawUpdate, rawPatchUpdate, responseCoordinateUpdate,
        Function.update_of_ne hj]
      fun_prop

theorem highRawUpdate_density_measurable (d k D r : ℕ) (a b : ℝ)
    (j : HighWindowLabels d k) (B : Covariate d → Fin r → ℝ)
    (hB : ∀ l, Measurable (fun x => B x l)) (e : HighRawMark d D r)
    (θ : HighRawState d k D) (hθ : Measurable θ.1) :
    Measurable (highRawUpdate d k D r a b j B e θ).1 := by
  change Measurable (fun x => if x ∈ highTorusPatch d k j then
    highRawSlope a b r B e x * θ.1 x + e.1 else θ.1 x)
  apply Measurable.ite (highTorusPatch_measurableSet d k j) _ hθ
  apply Measurable.add _ measurable_const
  apply Measurable.mul _ hθ
  unfold highRawSlope
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro l hl
  exact (hB l).const_mul _

theorem highRawUpdate_density_interval (d k D r : ℕ) (a b : ℝ) (ha : 0 < a)
    (hab : a < b) (hr : 1 ≤ r) (j : HighWindowLabels d k)
    (B : Covariate d → Fin r → ℝ) (hB : ∀ x l, |B x l| ≤ 1)
    (e : HighRawMark d D r) (hz : e.1 ∈ Icc a b) (hε : ∀ l, |e.2.1 l| ≤ 1)
    (θ : HighRawState d k D) (hθ : ∀ x, θ.1 x ∈ Icc a b) :
    ∀ x, (highRawUpdate d k D r a b j B e θ).1 x ∈ Icc a b := by
  intro x
  by_cases hx : x ∈ highTorusPatch d k j
  · change (if x ∈ highTorusPatch d k j then
      highRawSlope a b r B e x * θ.1 x + e.1 else θ.1 x) ∈ Icc a b
    rw [ite_eq_left hx]
    have hh := localDensityReset_mem_interval a b ha hab r hr e.1 hz e.2.1 hε
      θ.1 B x (hθ x) (hB x)
    convert hh using 1
    unfold highRawSlope localDensityReset
    ring
  · simpa only [highRawUpdate, rawPatchUpdate, affinePatchUpdate, ite_eq_right hx] using hθ x

theorem highRawUpdate_coefficient_ball (d k D r : ℕ) (a b Cfr : ℝ)
    (j : HighWindowLabels d k) (B : Covariate d → Fin r → ℝ)
    (e : HighRawMark d D r) (hσ : e.2.2.2 ∈ Icc (0 : ℝ) 1)
    (hv : ∑ γ, |e.2.2.1 γ| ≤ Cfr⁻¹) (θ : HighRawState d k D)
    (hθ : ∀ l, ∑ γ, |θ.2 l γ| ≤ Cfr⁻¹) :
    ∀ l, ∑ γ, |(highRawUpdate d k D r a b j B e θ).2 l γ| ≤ Cfr⁻¹ := by
  intro l
  by_cases hj : l = j
  · subst l
    change (∑ γ, |(Function.update θ.2 j (coefficientReset (θ.2 j) e.2.2.1 e.2.2.2)) j γ|) ≤ _
    rw [Function.update_self]
    exact coefficientReset_mem_ball Cfr _ _ _ hσ (hθ j) hv
  · simpa only [highRawUpdate, rawPatchUpdate, responseCoordinateUpdate,
      Function.update_of_ne hj] using hθ l

theorem highRawUpdate_commute (d k D r : ℕ) [NeZero k] (a b : ℝ)
    (i j : HighWindowLabels d k) (hij : j ∉ highNeighborLabels d k i)
    (B C : Covariate d → Fin r → ℝ) (e f : HighRawMark d D r)
    (θ : HighRawState d k D) :
    highRawUpdate d k D r a b j C f (highRawUpdate d k D r a b i B e θ) =
      highRawUpdate d k D r a b i B e (highRawUpdate d k D r a b j C f θ) := by
  apply rawPatchUpdate_commute
  · intro he
    exact hij (he ▸ highNeighborLabels_self_mem d k i)
  · exact highTorusPatch_disjoint_of_not_neighbor d k i j hij

theorem highRawUpdate_density_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    (d k D r : ℕ) (a b : ℝ) (j : HighWindowLabels d k)
    (B : Covariate d → Fin r → ℝ) (hB : ∀ l, Measurable (fun x => B x l))
    (e : Ω → HighRawMark d D r) (he : Measurable e) (θ : Ω → HighRawState d k D)
    (hθ : Measurable (fun ωx : Ω × Covariate d => (θ ωx.1).1 ωx.2)) :
    Measurable (fun ωx : Ω × Covariate d =>
      (highRawUpdate d k D r a b j B (e ωx.1) (θ ωx.1)).1 ωx.2) := by
  change Measurable (fun ωx : Ω × Covariate d => if ωx.2 ∈ highTorusPatch d k j then
    highRawSlope a b r B (e ωx.1) ωx.2 * (θ ωx.1).1 ωx.2 + (e ωx.1).1 else
      (θ ωx.1).1 ωx.2)
  apply Measurable.ite ((highTorusPatch_measurableSet d k j).preimage measurable_snd) _ hθ
  have he' : Measurable (fun ωx : Ω × Covariate d => e ωx.1) := he.comp measurable_fst
  apply Measurable.add _ he'.fst
  apply Measurable.mul _ hθ
  unfold highRawSlope densityMargin
  have hs : Measurable (fun ωx : Ω × Covariate d => ∑ l, (e ωx.1).2.1 l * B ωx.2 l) := by
    apply Finset.measurable_sum
    intro l hl
    exact ((measurable_pi_apply l).comp he'.snd.fst).mul ((hB l).comp measurable_snd)
  exact ((he'.fst.sub_const a).mul (he'.fst.const_sub b) |>.div_const (b - a) |>.div_const
    ((r : ℝ) * b)).mul hs

theorem highRawHistory_density_joint_measurable (d k D r : ℕ) (a b : ℝ)
    (B : HighWindowLabels d k → Covariate d → Fin r → ℝ)
    (hB : ∀ j l, Measurable (fun x => B j x l))
    (n : ℕ) (labels : Fin n → HighWindowLabels d k) (indices : List (Fin n))
    (θ : (Fin n → HighRawMark d D r) → HighRawState d k D)
    (hθ : Measurable (fun mx : (Fin n → HighRawMark d D r) × Covariate d =>
      (θ mx.1).1 mx.2)) :
    Measurable (fun mx : (Fin n → HighRawMark d D r) × Covariate d =>
      (indices.foldl (fun state i => highRawUpdate d k D r a b (labels i)
        (B (labels i)) (mx.1 i) state) (θ mx.1)).1 mx.2) := by
  induction indices generalizing θ with
  | nil => exact hθ
  | cons i indices ih =>
    exact ih (fun marks => highRawUpdate d k D r a b (labels i) (B (labels i))
      (marks i) (θ marks))
      (highRawUpdate_density_joint_measurable (Ω := Fin n → HighRawMark d D r)
        d k D r a b (labels i) (B (labels i))
        (hB (labels i)) (fun marks => marks i) (measurable_pi_apply i) θ hθ)

theorem highRawUpdate_valid (d k D r : ℕ) (a b Cfr : ℝ) (ha : 0 < a)
    (hab : a < b) (hr : 1 ≤ r) (j : HighWindowLabels d k)
    (B : Covariate d → Fin r → ℝ) (hBm : ∀ l, Measurable (fun x => B x l))
    (hB : ∀ x l, |B x l| ≤ 1) (e : HighRawMark d D r)
    (he : HighRawMarkValid d D r a b Cfr e) (θ : HighRawState d k D)
    (hθ : HighRawStateValid d k D a b Cfr θ) :
    HighRawStateValid d k D a b Cfr (highRawUpdate d k D r a b j B e θ) :=
  ⟨highRawUpdate_density_measurable d k D r a b j B hBm e θ hθ.1,
    highRawUpdate_density_interval d k D r a b ha hab hr j B hB e he.1 he.2.1 θ hθ.2.1,
    highRawUpdate_coefficient_ball d k D r a b Cfr j B e he.2.2.2 he.2.2.1 θ hθ.2.2⟩

theorem highRawHistory_valid (d k D r : ℕ) (a b Cfr : ℝ) (ha : 0 < a)
    (hab : a < b) (hr : 1 ≤ r) (B : HighWindowLabels d k → Covariate d → Fin r → ℝ)
    (hBm : ∀ j l, Measurable (fun x => B j x l)) (hB : ∀ j x l, |B j x l| ≤ 1)
    (n : ℕ) (labels : Fin n → HighWindowLabels d k) (indices : List (Fin n))
    (marks : Fin n → HighRawMark d D r)
    (hmarks : ∀ i, HighRawMarkValid d D r a b Cfr (marks i))
    (θ : HighRawState d k D) (hθ : HighRawStateValid d k D a b Cfr θ) :
    HighRawStateValid d k D a b Cfr
      (indices.foldl (fun state i => highRawUpdate d k D r a b (labels i)
        (B (labels i)) (marks i) state) θ) := by
  induction indices generalizing θ with
  | nil => exact hθ
  | cons i indices ih =>
    exact ih _ (highRawUpdate_valid d k D r a b Cfr ha hab hr (labels i)
      (B (labels i)) (hBm (labels i)) (hB (labels i)) (marks i) (hmarks i) θ hθ)

theorem highRawMarkedState_measurable (d k D r : ℕ) [NeZero k]
    [LinearOrder (HighWindowLabels d k)] (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)
    (a b : ℝ) (B : HighWindowLabels d k → Covariate d → Fin r → ℝ)
    (θ : HighRawState d k D) :
    Measurable (historyMarkedRawState dependent
      (fun j e state => highRawUpdate d k D r a b j (B j) e state) θ) :=
  historyMarkedRawState_measurable dependent _
    (fun j => highRawUpdate_measurable d k D r a b j (B j)) θ

/-- Joint design evaluation follows from the actual finite recursion.
Coordinate measurability of an uncountable density-function space alone
would not suffice for this conclusion. -/
theorem highRawMarkedState_density_joint_measurable (d k D r : ℕ) [NeZero k]
    [LinearOrder (HighWindowLabels d k)] (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)
    (a b : ℝ) (B : HighWindowLabels d k → Covariate d → Fin r → ℝ)
    (hB : ∀ j l, Measurable (fun x => B j x l))
    (θ : HighRawState d k D) (hθ : Measurable θ.1) :
    Measurable (fun hx : HistoryMarked dependent (HighRawMark d D r) × Covariate d =>
      (historyMarkedRawState dependent
        (fun j e state => highRawUpdate d k D r a b j (B j) e state) θ hx.1).1 hx.2) := by
  letI : BorelSpace (HighRawMark d D r) := by infer_instance
  letI : SecondCountableTopology (HighRawMark d D r) := by infer_instance
  letI (g : HistoryShape (fun a b => ¬ dependent a b)) :
      BorelSpace (Fin (historyShapeLength dependent g) → HighRawMark d D r) := by infer_instance
  letI : BorelSpace (HistoryMarked dependent (HighRawMark d D r)) := historySigma_borelSpace
  letI : BorelSpace (Σ g : HistoryShape (fun a b => ¬ dependent a b),
      (Fin (historyShapeLength dependent g) → HighRawMark d D r) × Covariate d) :=
    historySigma_borelSpace
  let F : (Σ g : HistoryShape (fun a b => ¬ dependent a b),
      (Fin (historyShapeLength dependent g) → HighRawMark d D r) × Covariate d) → ℝ :=
    fun q => (historyMarkedRawState dependent
      (fun j e state => highRawUpdate d k D r a b j (B j) e state) θ ⟨q.1, q.2.1⟩).1 q.2.2
  have hF : Measurable F := by
    intro s hs
    rw [MeasurableSpace.measurableSet_iInf]
    intro g
    exact (highRawHistory_density_joint_measurable d k D r a b B hB
      (historyShapeLength dependent g) (historyShapeCanonicalLabels dependent g)
      (List.ofFn (fun i : Fin (historyShapeLength dependent g) => i)) (fun _ => θ)
      (hθ.comp measurable_snd)) hs
  have hd : Measurable (Homeomorph.sigmaProdDistrib
      (X := fun g : HistoryShape (fun a b => ¬ dependent a b) =>
        Fin (historyShapeLength dependent g) → HighRawMark d D r)
      (Y := Covariate d)) := Homeomorph.sigmaProdDistrib.continuous.measurable
  exact hF.comp hd

end NearlyMinimax
