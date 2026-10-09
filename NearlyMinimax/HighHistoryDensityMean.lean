module

public import NearlyMinimax.FiniteAffineHistoryMean
public import NearlyMinimax.HighPacketBalancing
public import NearlyMinimax.HighRawUpdates
public import NearlyMinimax.HighRawDensityLocality


@[expose] public section

/-! The actual balanced packet retains the representation mark in its
spatial density reset. Its finite canonical histories have pointwise mean
one under their genuine independent reference mark laws. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem affinePatchFold_density_eq {J X E V I : Type*} [DecidableEq J]
    (patch : J → Set X) (slope offset : J → E → X → ℝ)
    (response : J → E → V → V) (labels : I → J) (marks : I → E)
    (indices : List I) (initial : (X → ℝ) × (J → V)) (x : X) :
    (indices.foldl (fun θ i => rawPatchUpdate (labels i) (patch (labels i))
      (slope (labels i) (marks i)) (offset (labels i) (marks i))
      (response (labels i) (marks i)) θ) initial).1 x =
      indices.foldl (fun v i =>
        (if x ∈ patch (labels i) then slope (labels i) (marks i) x else 1) * v +
        (if x ∈ patch (labels i) then offset (labels i) (marks i) x else 0)) (initial.1 x) := by
  induction indices generalizing initial with
  | nil => rfl
  | cons i indices ih =>
    simp only [List.foldl_cons]
    rw [ih]
    by_cases hx : x ∈ patch (labels i) <;>
      simp only [rawPatchUpdate, affinePatchUpdate, hx, ite_true, ite_false, one_mul, add_zero]

theorem affinePatchFold_density_joint_measurable {J X E V : Type*} [DecidableEq J]
    [MeasurableSpace X] [MeasurableSpace E]
    (patch : J → Set X) (hpatch : ∀ j, MeasurableSet (patch j))
    (slope offset : J → E → X → ℝ)
    (hs : ∀ j, Measurable (fun ex : E × X => slope j ex.1 ex.2))
    (ho : ∀ j, Measurable (fun ex : E × X => offset j ex.1 ex.2))
    (response : J → E → V → V) (n : ℕ) (labels : Fin n → J) (indices : List (Fin n))
    (initial : (Fin n → E) → (X → ℝ) × (J → V))
    (hi : Measurable (fun mx : (Fin n → E) × X => (initial mx.1).1 mx.2)) :
    Measurable (fun mx : (Fin n → E) × X =>
      (indices.foldl (fun θ i => rawPatchUpdate (labels i) (patch (labels i))
        (slope (labels i) (mx.1 i)) (offset (labels i) (mx.1 i))
        (response (labels i) (mx.1 i)) θ) (initial mx.1)).1 mx.2) := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih =>
    simp only [List.foldl_cons]
    apply ih (fun marks => rawPatchUpdate (labels i) (patch (labels i))
      (slope (labels i) (marks i)) (offset (labels i) (marks i))
      (response (labels i) (marks i)) (initial marks))
    change Measurable (fun mx : (Fin n → E) × X =>
      if mx.2 ∈ patch (labels i) then slope (labels i) (mx.1 i) mx.2 *
        (initial mx.1).1 mx.2 + offset (labels i) (mx.1 i) mx.2 else (initial mx.1).1 mx.2)
    have hcoord : Measurable (fun mx : (Fin n → E) × X => (mx.1 i, mx.2)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
    exact Measurable.ite ((hpatch _).preimage measurable_snd)
      (((hs (labels i)).comp hcoord).mul hi |>.add ((ho (labels i)).comp hcoord)) hi

section Packet
variable {Z : Type*} [MeasurableSpace Z] (d k F m r D q : ℕ)

abbrev HighCenteredPacketMark :=
  (Z × HighPacketMarkIndex (HighFrameIndex d F) m r D q) ⊕ Unit

def centeredPacketResponseVector (C : ℝ) : HighCenteredPacketMark (Z := Z) d F m r D q →
    HighFrameIndex d F → ℝ :=
  Sum.elim (fun e => (highResponseMarkAtom C q e.2.2).2) (fun _ => 0)

def centeredPacketResponseTime : HighCenteredPacketMark (Z := Z) d F m r D q → ℝ :=
  Sum.elim (fun e => (highResponseMarkAtom (ι := HighFrameIndex d F) 0 q e.2.2).1) (fun _ => 0)

def centeredPacketResponseReset (C : ℝ) (e : HighCenteredPacketMark (Z := Z) d F m r D q)
    (c : HighFrameIndex d F → ℝ) : HighFrameIndex d F → ℝ :=
  coefficientReset c (centeredPacketResponseVector d F m r D q C e)
    (centeredPacketResponseTime d F m r D q e)

def centeredPacketRawUpdate (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (j : HighWindowLabels d k) (e : HighCenteredPacketMark (Z := Z) d F m r D q)
    (θ : HighRawState d k F) : HighRawState d k F :=
  rawPatchUpdate j (highTorusPatch d k j)
    (fun x => centeredPacketSlope a b m r D q (fun ζ l => B j ζ x l) e)
    (fun _ => centeredPacketIntercept σ a b m r D q C δ A e)
    (centeredPacketResponseReset d F m r D q C e) θ

theorem centeredPacketRawUpdate_density_eq (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (j : HighWindowLabels d k) (e : HighCenteredPacketMark (Z := Z) d F m r D q)
    (θ : HighRawState d k F) (x : Covariate d) :
    (centeredPacketRawUpdate d k F m r D q σ a b C δ A B j e θ).1 x =
      if x ∈ highTorusPatch d k j then
        centeredPacketSlope a b m r D q (fun ζ l => B j ζ x l) e * θ.1 x +
        centeredPacketIntercept σ a b m r D q C δ A e else θ.1 x := rfl

theorem centeredPacketRawUpdate_density_outside (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (j : HighWindowLabels d k) (e : HighCenteredPacketMark (Z := Z) d F m r D q)
    (θ : HighRawState d k F) (x : Covariate d) (hx : x ∉ highTorusPatch d k j) :
    (centeredPacketRawUpdate d k F m r D q σ a b C δ A B j e θ).1 x = θ.1 x := by
  rw [centeredPacketRawUpdate_density_eq, if_neg hx]

theorem centeredPacketSlope_joint_measurable (a b : ℝ)
    (B : Z → Covariate d → Fin r → ℝ)
    (hB : ∀ l, Measurable (fun zx : Z × Covariate d => B zx.1 zx.2 l)) :
    Measurable (fun ex : HighCenteredPacketMark (Z := Z) d F m r D q × Covariate d =>
      centeredPacketSlope a b m r D q (fun ζ l => B ζ ex.2 l) ex.1) := by
  let G : (Z × HighPacketMarkIndex (HighFrameIndex d F) m r D q) × Covariate d → ℝ :=
    fun ex => highPacketSlope a b m r D q (fun ζ l => B ζ ex.2 l) ex.1
  have hmz : Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d F) m r D q) × Covariate d =>
      (densityPacketAtom a b m r D ex.1.2.1).1) :=
    (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d F) m r D q =>
      (densityPacketAtom a b m r D h.1).1)).comp (measurable_snd.comp measurable_fst)
  have hmε (l : Fin r) : Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d F) m r D q) × Covariate d =>
      (densityPacketAtom a b m r D ex.1.2.1).2 l) :=
    (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d F) m r D q =>
      (densityPacketAtom a b m r D h.1).2 l)).comp (measurable_snd.comp measurable_fst)
  have hmG : Measurable G := by
    unfold G highPacketSlope highPacketIntercept densityMargin
    exact ((hmz.sub measurable_const).mul (measurable_const.sub hmz) |>.div_const _ |>.div_const _).mul
      (Finset.measurable_fun_sum _ (fun l _ => (hmε l).mul
        ((hB l).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))))
  have hm := (hmG.sumElim (measurable_const (a := (0 : ℝ)))).comp
    (MeasurableEquiv.sumProdDistrib
      (Z × HighPacketMarkIndex (HighFrameIndex d F) m r D q) Unit (Covariate d)).measurable
  convert hm using 1
  funext ⟨e, x⟩
  cases e <;> rfl

theorem centeredPacketResponseVector_measurable (C : ℝ) (γ : HighFrameIndex d F) :
    Measurable (fun e : HighCenteredPacketMark (Z := Z) d F m r D q =>
      centeredPacketResponseVector d F m r D q C e γ) := by
  apply Measurable.sumElim _ measurable_const
  exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d F) m r D q =>
    (highResponseMarkAtom C q h.2).2 γ)).comp measurable_snd

theorem centeredPacketResponseTime_measurable :
    Measurable (centeredPacketResponseTime (Z := Z) d F m r D q) := by
  apply Measurable.sumElim _ measurable_const
  exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d F) m r D q =>
    (highResponseMarkAtom 0 q h.2).1)).comp measurable_snd

theorem centeredPacketRawUpdate_measurable (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (hB : ∀ j x l, Measurable (fun ζ => B j ζ x l)) (j : HighWindowLabels d k) :
    Measurable (fun eθ : HighCenteredPacketMark (Z := Z) d F m r D q × HighRawState d k F =>
      centeredPacketRawUpdate d k F m r D q σ a b C δ A B j eθ.1 eθ.2) := by
  have hz : Measurable (centeredPacketIntercept σ a b m r D q C δ A) :=
    balancedIntercept_measurable _ (highPacketIntercept_measurable a b m r D q) _ _
  have hs (x : Covariate d) : Measurable (centeredPacketSlope (ι := HighFrameIndex d F)
      a b m r D q (fun ζ l => B j ζ x l)) :=
    balancedSlope_measurable _ (highPacketSlope_measurable a b m r D q _ (hB j x))
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro x
    by_cases hx : x ∈ highTorusPatch d k j
    · simp only [centeredPacketRawUpdate, rawPatchUpdate, affinePatchUpdate, if_pos hx]
      exact ((hs x).comp measurable_fst).mul
        ((measurable_pi_apply x).comp (measurable_fst.comp measurable_snd)) |>.add
        (hz.comp measurable_fst)
    · simp only [centeredPacketRawUpdate, rawPatchUpdate, affinePatchUpdate, if_neg hx]
      exact (measurable_pi_apply x).comp (measurable_fst.comp measurable_snd)
  · apply measurable_pi_lambda
    intro l
    apply measurable_pi_lambda
    intro γ
    by_cases hl : l = j
    · subst l
      simp only [centeredPacketRawUpdate, rawPatchUpdate, responseCoordinateUpdate,
        Function.update_self, centeredPacketResponseReset, coefficientReset]
      exact ((measurable_const.sub ((centeredPacketResponseTime_measurable d F m r D q).comp
          measurable_fst)).mul (by fun_prop)).add
        (((centeredPacketResponseTime_measurable d F m r D q).comp measurable_fst).mul
          ((centeredPacketResponseVector_measurable d F m r D q C γ).comp measurable_fst))
    · simp only [centeredPacketRawUpdate, rawPatchUpdate, responseCoordinateUpdate,
        Function.update_of_ne hl]
      fun_prop

theorem centeredPacketRawHistory_density_mean_one (σ : Measure Z) [IsFiniteMeasure σ]
    (a b C δ : ℝ) (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (hmB : ∀ j x l, Measurable (fun ζ => B j ζ x l))
    (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1)
    (n : ℕ) (labels : Fin n → HighWindowLabels d k)
    (initial : HighRawState d k F) (hinit : ∀ x, initial.1 x = 1) (x : Covariate d) :
    (∫ marks, ((List.ofFn (fun i : Fin n => i)).foldl
      (fun θ i => centeredPacketRawUpdate d k F m r D q σ a b C δ A B
        (labels i) (marks i) θ) initial).1 x
      ∂Measure.pi (fun _ : Fin n => centeredPacketLaw σ a b m r D q C δ A)) = 1 := by
  let π := centeredPacketLaw σ a b m r D q C δ A
  letI : IsProbabilityMeasure π := centeredPacketLaw_probability σ a b m r D q C δ A
    hA hcost hpos hδ0 hδ1.le
  let s := fun (j : HighWindowLabels d k) (e : HighCenteredPacketMark (Z := Z) d F m r D q) =>
    if x ∈ highTorusPatch d k j then
    centeredPacketSlope a b m r D q (fun ζ l => B j ζ x l) e else 1
  let o := fun (j : HighWindowLabels d k) (e : HighCenteredPacketMark (Z := Z) d F m r D q) =>
    if x ∈ highTorusPatch d k j then
    centeredPacketIntercept σ a b m r D q C δ A e else 0
  have hs : ∀ j, Integrable (s j) π := by
    intro j
    by_cases hx : x ∈ highTorusPatch d k j
    · simp only [s, ite_eq_left hx]
      exact balancedReferenceLaw_integrable _ δ _
        (balancedSlope_measurable _ (highPacketSlope_measurable a b m r D q _ (hmB j x)))
        (highPacketSlope_integrable σ a b ha hab m r D q hr C A hA hcost hpos
          (fun ζ l => B j ζ x l) (hmB j x) (fun ζ l => hB j ζ x l))
    · simp only [s, ite_eq_right hx]
      exact integrable_const _
  have ho : ∀ j, Integrable (o j) π := by
    intro j
    by_cases hx : x ∈ highTorusPatch d k j
    · simp only [o, ite_eq_left hx]
      exact balancedReferenceLaw_integrable _ δ _
        (balancedIntercept_measurable _ (highPacketIntercept_measurable a b m r D q) _ _)
        (highPacketIntercept_integrable σ a b ha hab m r D q C A hA hcost hpos)
    · simp only [o, ite_eq_right hx]
      exact integrable_const _
  have hmean : ∀ j, (∫ e, s j e ∂π) + (∫ e, o j e ∂π) = 1 := by
    intro j
    by_cases hx : x ∈ highTorusPatch d k j
    · simp only [s, o, ite_eq_left hx]
      rw [centeredPacketSlope_integral_zero σ a b m r D q C δ A hA hcost hpos ha hab hr
        hδ0 hδ1.le _ (hmB j x) (fun ζ l => hB j ζ x l),
        centeredPacketIntercept_integral_one σ a b m r D q C δ A hA hcost hpos ha hab hδ0 hδ1]
      norm_num
    · simp only [s, o, ite_eq_right hx, integral_const, integral_zero,
        measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one, add_zero]
      norm_num
  convert finiteAffineHistory_integral_one π s o hs ho hmean n labels using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro marks
  dsimp only
  unfold centeredPacketRawUpdate
  exact (affinePatchFold_density_eq (highTorusPatch d k)
    (fun j e x => centeredPacketSlope a b m r D q (fun ζ l => B j ζ x l) e)
    (fun _ e _ => centeredPacketIntercept σ a b m r D q C δ A e)
    (fun _ e => centeredPacketResponseReset d F m r D q C e)
    labels marks (List.ofFn (fun i : Fin n => i)) initial x).trans (by rw [hinit x]; rfl)

theorem centeredPacketRawHistory_canonical_density_mean_one
    [NeZero k]
    [LinearOrder (HighWindowLabels d k)]
    (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)
    (σ : Measure Z) [IsFiniteMeasure σ] (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (hmB : ∀ j x l, Measurable (fun ζ => B j ζ x l)) (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1)
    (initial : HighRawState d k F) (hinit : ∀ x, initial.1 x = 1)
    (g : HistoryShape (fun i j => ¬ dependent i j)) (x : Covariate d) :
    (∫ marks, (historyMarkedRawState dependent
      (centeredPacketRawUpdate d k F m r D q σ a b C δ A B) initial ⟨g, marks⟩).1 x
      ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) =>
        centeredPacketLaw σ a b m r D q C δ A)) = 1 :=
  centeredPacketRawHistory_density_mean_one d k F m r D q σ a b C δ A hA hcost hpos
    ha hab hr hδ0 hδ1 B hmB hB (historyShapeLength dependent g)
    (historyShapeCanonicalLabels dependent g) initial hinit x

theorem centeredPacket_reset_interval (σ : Measure Z) [IsFiniteMeasure σ]
    (a b C δ : ℝ) (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
    (hW : b - a ≤ width) (hδW : δ * width ≤ radius / 2)
    (B : Z → Fin r → ℝ) (hB : ∀ ζ l, |B ζ l| ≤ 1)
    (e : HighCenteredPacketMark (Z := Z) d F m r D q) (v : ℝ) (hv : v ∈ Icc a b) :
    centeredPacketSlope a b m r D q B e * v +
      centeredPacketIntercept σ a b m r D q C δ A e ∈ Icc a b := by
  cases e with
  | inl e =>
    have hmem := densityPacketAtom_mem a b hab.le m r D e.2.1
    have hh := localDensityReset_mem_interval a b ha hab r hr _ hmem.1 _ hmem.2
      (fun _ : Unit => v) (fun _ : Unit => B e.1) () hv (hB e.1)
    convert hh using 1
    dsimp [centeredPacketSlope, centeredPacketIntercept, balancedSlope, balancedIntercept,
      highPacketSlope, highPacketIntercept, localDensityReset]
    ring
  | inr e =>
    simp only [centeredPacketSlope, centeredPacketIntercept, balancedSlope, balancedIntercept,
      Sum.elim_inr, zero_mul, zero_add]
    exact balancedResetAnchor_mem a b radius width δ _ hR hδ0 hδ1 ha1 hb1 hW hδW
      (highPacketAbsoluteLaw_intercept_mem σ a b ha hab m r D q C A hA hcost hpos)

theorem centeredPacketRawHistory_density_joint_measurable (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (hB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
    (n : ℕ) (labels : Fin n → HighWindowLabels d k)
    (initial : HighRawState d k F) (hi : Measurable initial.1) :
    Measurable (fun mx : (Fin n → HighCenteredPacketMark (Z := Z) d F m r D q) × Covariate d =>
      ((List.ofFn (fun i : Fin n => i)).foldl (fun θ i =>
        centeredPacketRawUpdate d k F m r D q σ a b C δ A B (labels i) (mx.1 i) θ) initial).1 mx.2) := by
  exact affinePatchFold_density_joint_measurable (highTorusPatch d k)
    (highTorusPatch_measurableSet d k)
    (fun j e x => centeredPacketSlope a b m r D q (fun ζ l => B j ζ x l) e)
    (fun _ e _ => centeredPacketIntercept σ a b m r D q C δ A e)
    (fun j => centeredPacketSlope_joint_measurable d F m r D q a b (B j) (hB j))
    (fun _ => (balancedIntercept_measurable _ (highPacketIntercept_measurable a b m r D q) _ _).comp
      measurable_fst)
    (fun _ e => centeredPacketResponseReset d F m r D q C e) n labels (List.ofFn (fun i : Fin n => i))
    (fun _ => initial) (hi.comp measurable_snd)

def centeredPacketHistoryMass (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (n : ℕ) (labels : Fin n → HighWindowLabels d k) (initial : HighRawState d k F)
    (marks : Fin n → HighCenteredPacketMark (Z := Z) d F m r D q) : ℝ :=
  ∫ x, ((List.ofFn (fun i : Fin n => i)).foldl (fun θ i =>
    centeredPacketRawUpdate d k F m r D q σ a b C δ A B (labels i) (marks i) θ) initial).1 x
    ∂cubeVolume d

theorem centeredPacketHistoryMass_measurable (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (hB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
    (n : ℕ) (labels : Fin n → HighWindowLabels d k)
    (initial : HighRawState d k F) (hi : Measurable initial.1) :
    Measurable (centeredPacketHistoryMass d k F m r D q σ a b C δ A B n labels initial) := by
  letI := cubeVolume_isProbability d
  exact (centeredPacketRawHistory_density_joint_measurable d k F m r D q σ a b C δ A B hB n labels
    initial hi).stronglyMeasurable.integral_prod_right'.measurable

theorem centeredPacketRawHistory_density_interval (σ : Measure Z) [IsFiniteMeasure σ]
    (a b C δ : ℝ) (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
    (hW : b - a ≤ width) (hδW : δ * width ≤ radius / 2)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1)
    (n : ℕ) (labels : Fin n → HighWindowLabels d k)
    (initial : HighRawState d k F) (hi : ∀ x, initial.1 x ∈ Icc a b)
    (marks : Fin n → HighCenteredPacketMark (Z := Z) d F m r D q) (x : Covariate d) :
    ((List.ofFn (fun i : Fin n => i)).foldl (fun θ i =>
      centeredPacketRawUpdate d k F m r D q σ a b C δ A B (labels i) (marks i) θ) initial).1 x ∈ Icc a b :=
  affineRawHistory_density_interval (highTorusPatch d k)
    (fun j e x => centeredPacketSlope a b m r D q (fun ζ l => B j ζ x l) e)
    (fun _ e _ => centeredPacketIntercept σ a b m r D q C δ A e)
    (fun _ e => centeredPacketResponseReset d F m r D q C e) labels
    (List.ofFn (fun i : Fin n => i)) marks a b
    (fun j e x v hv => centeredPacket_reset_interval d F m r D q σ a b C δ A hA hcost hpos
      ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW (fun ζ l => B j ζ x l)
      (fun ζ l => hB j ζ x l) e v hv) initial hi x

theorem centeredPacketHistoryMass_bound_and_mean (σ : Measure Z) [IsFiniteMeasure σ]
    (a b C δ : ℝ) (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
    (hW : b - a ≤ width) (hδW : δ * width ≤ radius / 2)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (hmB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
    (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1)
    (n : ℕ) (labels : Fin n → HighWindowLabels d k)
    (initial : HighRawState d k F) (hinit : ∀ x, initial.1 x = 1) :
    Measurable (centeredPacketHistoryMass d k F m r D q σ a b C δ A B n labels initial) ∧
    (∀ marks, |centeredPacketHistoryMass d k F m r D q σ a b C δ A B n labels initial marks| ≤ b) ∧
    (∫ marks, centeredPacketHistoryMass d k F m r D q σ a b C δ A B n labels initial marks
      ∂Measure.pi (fun _ : Fin n => centeredPacketLaw σ a b m r D q C δ A)) = 1 := by
  let π := centeredPacketLaw σ a b m r D q C δ A
  letI : IsProbabilityMeasure π := centeredPacketLaw_probability σ a b m r D q C δ A
    hA hcost hpos hδ0 hδ1.le
  letI := cubeVolume_isProbability d
  have hi0 : Measurable initial.1 := by
    rw [show initial.1 = (fun _ => 1) from funext hinit]
    exact measurable_const
  let f := fun mx : (Fin n → HighCenteredPacketMark (Z := Z) d F m r D q) × Covariate d =>
    ((List.ofFn (fun i : Fin n => i)).foldl (fun θ i =>
      centeredPacketRawUpdate d k F m r D q σ a b C δ A B (labels i) (mx.1 i) θ) initial).1 mx.2
  have hm : Measurable f := centeredPacketRawHistory_density_joint_measurable
    d k F m r D q σ a b C δ A B hmB n labels initial hi0
  have hint (marks : Fin n → HighCenteredPacketMark (Z := Z) d F m r D q) (x : Covariate d) :
      f (marks, x) ∈ Icc a b :=
    centeredPacketRawHistory_density_interval d k F m r D q σ a b C δ A hA hcost hpos
      ha hab hr hδ0 hδ1 radius width hR ha1 hb1 hW hδW B hB n labels initial
      (fun x => by rw [hinit x]; exact ⟨by linarith, by linarith⟩) marks x
  have hfi : Integrable f ((Measure.pi (fun _ : Fin n => π)).prod (cubeVolume d)) := by
    apply (integrable_const b).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro mx
    rcases mx with ⟨marks, x⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (ha.le.trans (hint marks x).1)]
    exact (hint marks x).2
  refine ⟨centeredPacketHistoryMass_measurable d k F m r D q σ a b C δ A B hmB n labels initial hi0,
    ?_, ?_⟩
  · intro marks
    have hm' : Measurable (fun x => f (marks, x)) := hm.comp (measurable_const.prodMk measurable_id)
    have hmean := boundedIntercept_mean_mem (cubeVolume d) _ hm' a b (hint marks)
    change |∫ x, f (marks, x) ∂cubeVolume d| ≤ b
    rw [abs_of_nonneg (ha.le.trans hmean.1)]
    exact hmean.2
  · change (∫ marks, ∫ x, f (marks, x) ∂cubeVolume d ∂Measure.pi (fun _ : Fin n => π)) = 1
    rw [integral_integral_swap hfi]
    have he (x : Covariate d) : (∫ marks, f (marks, x) ∂Measure.pi (fun _ : Fin n => π)) = 1 :=
      centeredPacketRawHistory_density_mean_one d k F m r D q σ a b C δ A hA hcost hpos
        ha hab hr hδ0 hδ1 B
        (fun j x l => (hmB j l).comp (measurable_id.prodMk measurable_const)) hB n labels initial hinit x
    simp_rw [he]
    simp

end Packet
end NearlyMinimax
