module

public import NearlyMinimax.HighCanonicalDensityMean
public import NearlyMinimax.HistoryPatchStateAppend
public import NearlyMinimax.CenteredPacketAnnihilation


@[expose] public section

/-! Conditional signed annihilation of the actual canonical-history mass.
The canonical append identity and response-independent density reset are
proved from the constructed full-mark update. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]

theorem centeredPacketMarkedRawState_append (d k F m r D q : ℕ) [NeZero k]
    [LinearOrder (HighWindowLabels d k)]
    (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (initial : HighRawState d k F) (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighCenteredPacketMark (Z := Z) d F m r D q))
    (e : HighCenteredPacketMark (Z := Z) d F m r D q) :
    historyMarkedRawState (fun i j => j ∈ highNeighborLabels d k i)
      (centeredPacketRawUpdate d k F m r D q σ a b C δ A B) initial
      (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, e)) =
    centeredPacketRawUpdate d k F m r D q σ a b C δ A B j e
      (historyMarkedRawState (fun i j => j ∈ highNeighborLabels d k i)
        (centeredPacketRawUpdate d k F m r D q σ a b C δ A B) initial h) := by
  exact highMarkedRawState_patch_append d k
    (fun j e x => centeredPacketSlope a b m r D q (fun ζ l => B j ζ x l) e)
    (fun _ e _ => centeredPacketIntercept σ a b m r D q C δ A e)
    (fun _ e => centeredPacketResponseReset d F m r D q C e) initial j h e

def ordinaryPacketDensityAfter (d k r : ℕ) (a b : ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (j : HighWindowLabels d k) (p : Covariate d → ℝ)
    (ζ : Z) (z : ℝ) (ε : Fin r → ℝ) (x : Covariate d) : ℝ :=
  if x ∈ highTorusPatch d k j then
    localDensityReset a b r z ε p (fun x l => B j ζ x l) x else p x

theorem ordinaryPacketDensityAfter_joint_measurable (d k r : ℕ) (a b : ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (hB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
    (j : HighWindowLabels d k) (p : Covariate d → ℝ) (hp : Measurable p)
    (z : ℝ) (ε : Fin r → ℝ) :
    Measurable (fun zx : Z × Covariate d => ordinaryPacketDensityAfter d k r a b B j p zx.1 z ε zx.2) := by
  have hp' : Measurable (fun zx : Z × Covariate d => p zx.2) := hp.comp measurable_snd
  have hreset : Measurable (fun zx : Z × Covariate d =>
      localDensityReset a b r z ε p (fun x l => B j zx.1 x l) zx.2) := by
    unfold localDensityReset
    exact (hp'.const_mul _ |>.mul
      (Finset.measurable_fun_sum _ (fun l _ => (hB j l).const_mul (ε l)))).const_add z
  exact hreset.ite ((highTorusPatch_measurableSet d k j).preimage measurable_snd) hp'

theorem centeredPacketRawUpdate_ordinary_density (d k F m r D q : ℕ)
    (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (j : HighWindowLabels d k) (state : HighRawState d k F)
    (e : Z × HighPacketMarkIndex (HighFrameIndex d F) m r D q) (x : Covariate d) :
    (centeredPacketRawUpdate d k F m r D q σ a b C δ A B j (Sum.inl e) state).1 x =
      ordinaryPacketDensityAfter d k r a b B j state.1 e.1
        (densityPacketAtom a b m r D e.2.1).1 (densityPacketAtom a b m r D e.2.1).2 x := by
  rw [centeredPacketRawUpdate_density_eq]
  unfold ordinaryPacketDensityAfter
  split_ifs
  · simp only [centeredPacketSlope, balancedSlope, Sum.elim_inl, highPacketSlope,
      highPacketIntercept, centeredPacketIntercept, balancedIntercept, localDensityReset]
    ring
  · rfl

theorem centeredPacketMarkedMass_append_ordinary (d k F m r D q : ℕ) [NeZero k]
    [LinearOrder (HighWindowLabels d k)]
    (σ : Measure Z) (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (initial : HighRawState d k F) (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighCenteredPacketMark (Z := Z) d F m r D q))
    (e : Z × HighPacketMarkIndex (HighFrameIndex d F) m r D q) :
    centeredPacketMarkedMass d k F m r D q (fun i j => j ∈ highNeighborLabels d k i)
      σ a b C δ A B initial
      (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, Sum.inl e)) =
      ∫ x, ordinaryPacketDensityAfter d k r a b B j
        (centeredPacketMarkedDensity d k F m r D q (fun i j => j ∈ highNeighborLabels d k i)
          σ a b C δ A B initial h) e.1
        (densityPacketAtom a b m r D e.2.1).1 (densityPacketAtom a b m r D e.2.1).2 x
        ∂cubeVolume d := by
  unfold centeredPacketMarkedMass
  apply integral_congr_ae
  filter_upwards [] with x
  change (historyMarkedRawState (fun i j => j ∈ highNeighborLabels d k i)
    (centeredPacketRawUpdate d k F m r D q σ a b C δ A B) initial
    (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, Sum.inl e))).1 x = _
  rw [centeredPacketMarkedRawState_append, centeredPacketRawUpdate_ordinary_density]
  rfl

/-- Every actual mass indicator has zero conditional signed activation
after canonical append. There is no law-invariance or score-equality premise. -/
theorem centeredPacketMarkedMass_append_indicator_zero (d k F m r D q : ℕ) [NeZero k]
    [LinearOrder (HighWindowLabels d k)]
    (σ : Measure Z) [IsFiniteMeasure σ] (a b C δ : ℝ)
    (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
    (hB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
    (initial : HighRawState d k F) (hi : Measurable initial.1)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighCenteredPacketMark (Z := Z) d F m r D q)) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ e, S.indicator (fun _ : ℝ => (1 : ℝ))
      (centeredPacketMarkedMass d k F m r D q (fun i j => j ∈ highNeighborLabels d k i)
        σ a b C δ A B initial
        (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
          (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, e))) *
      centeredPacketActivation σ a b m r D q C δ A e
      ∂centeredPacketLaw σ a b m r D q C δ A) = 0 := by
  letI := cubeVolume_isProbability d
  let p : Covariate d → ℝ := centeredPacketMarkedDensity d k F m r D q
    (fun i j => j ∈ highNeighborLabels d k i) σ a b C δ A B initial h
  have hp : Measurable p :=
    (centeredPacketMarkedDensity_joint_measurable d k F m r D q
      (fun i j => j ∈ highNeighborLabels d k i) σ a b C δ A B hB initial hi).comp
        (measurable_const.prodMk measurable_id)
  let G : Z → ℝ → (Fin r → ℝ) → ℝ := fun ζ z ε =>
    S.indicator (fun _ : ℝ => (1 : ℝ))
      (∫ x, ordinaryPacketDensityAfter d k r a b B j p ζ z ε x ∂cubeVolume d)
  have hG (z : ℝ) (ε : Fin r → ℝ) : Measurable (fun ζ => G ζ z ε) :=
    (measurable_const.indicator hS).comp
      (ordinaryPacketDensityAfter_joint_measurable d k r a b B hB j p hp z ε).stronglyMeasurable.integral_prod_right'.measurable
  have hGb : ∀ (ζ : Z) (e : HighDensityMarkIndex m r D),
      |G ζ (densityPacketAtom a b m r D e).1 (densityPacketAtom a b m r D e).2| ≤ 1 := by
    intro ζ e
    dsimp only [G]
    simpa only [Real.norm_eq_abs, norm_one] using
      (norm_indicator_le_norm_self (s := S) (fun _ : ℝ => (1 : ℝ))
        (∫ x, ordinaryPacketDensityAfter d k r a b B j p ζ
          (densityPacketAtom a b m r D e).1 (densityPacketAtom a b m r D e).2 x ∂cubeVolume d))
  let Fobs : HighCenteredPacketMark (Z := Z) d F m r D q → ℝ := fun e =>
    S.indicator (fun _ : ℝ => (1 : ℝ))
      (centeredPacketMarkedMass d k F m r D q (fun i j => j ∈ highNeighborLabels d k i)
        σ a b C δ A B initial
        (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
          (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, e)))
  have hfactor (e : Z × HighPacketMarkIndex (HighFrameIndex d F) m r D q) :
      Fobs (Sum.inl e) = highPacketObservable a b m r D q C (fun _ => 0) G
        (responseAffineObservable 1 (fun _ => 0)) e := by
    dsimp only [Fobs]
    simp only [highPacketObservable, responseAffineObservable, zero_mul,
      Finset.sum_const_zero, add_zero, mul_one]
    rw [centeredPacketMarkedMass_append_ordinary]
  have hz := centeredPacket_conditional_affine_zero_of_factor σ a b m r D q C δ A
    hA hcost hpos hδ hδ1 (fun _ => 0) G hG 1 (by norm_num) hGb 1 (fun _ => 0) Fobs hfactor
  change (∫ e, Fobs e * centeredPacketActivation σ a b m r D q C δ A e
    ∂centeredPacketLaw σ a b m r D q C δ A) = 0
  calc
    _ = ∫ e, centeredPacketActivation σ a b m r D q C δ A e * Fobs e
        ∂centeredPacketLaw σ a b m r D q C δ A :=
      integral_congr_ae (Filter.Eventually.of_forall (fun e => mul_comm _ _))
    _ = 0 := hz

end NearlyMinimax
