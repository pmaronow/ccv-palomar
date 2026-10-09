module

public import NearlyMinimax.HighPacketBalancing


@[expose] public section

/-! The genuine centered full-mark packet annihilates conditional density
factors times arbitrary affine response observables. Its spatial mark is
retained, and its zero action follows from the actual finite response rule. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def responseAffineObservable (β : ℝ) (c : ι → ℝ) (v : ι → ℝ) : ℝ :=
  β + ∑ i, c i * v i

theorem responseMatrixAction_affine_zero (q : ℕ) (C : ℝ)
    (A : ι → ι → ℝ) (c : ι → ℝ) (β : ℝ) (coeff : ι → ℝ) :
    responseMatrixAction q C A c (responseAffineObservable β coeff) = 0 := by
  have hconst : responseMatrixAction q C A c (fun _ => β) = 0 := by
    have h := responseMatrixAction_mul q C β A c (fun _ => 1)
    simpa only [mul_one, responseMatrixAction_zero_mass, mul_zero] using h
  have hsum : responseMatrixAction q C A c (fun v => ∑ i, coeff i * v i) = 0 := by
    rw [responseMatrixAction_sum Finset.univ]
    simp only [responseMatrixAction_mul, responseMatrixAction_zero_mean, mul_zero, Finset.sum_const_zero]
  change responseMatrixAction q C A c (fun v => β + ∑ i, coeff i * v i) = 0
  rw [responseMatrixAction_add, hconst, hsum, add_zero]

theorem highSeparatedPacketAction_affine_zero (σ : Measure Z)
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ) (c : ι → ℝ)
    (G : Z → ℝ → (Fin r → ℝ) → ℝ) (β : ℝ) (coeff : ι → ℝ) :
    highSeparatedPacketAction σ a b m r D q C A c G (responseAffineObservable β coeff) = 0 := by
  simp only [highSeparatedPacketAction, responseMatrixAction_affine_zero, mul_zero,
    densityPacketAction_zero, integral_zero]

def centeredConditionalPacketObservable (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (c : ι → ℝ) (G : Z → ℝ → (Fin r → ℝ) → ℝ) (Φ : (ι → ℝ) → ℝ) (dummy : ℝ) :
    (Z × HighPacketMarkIndex ι m r D q) ⊕ Unit → ℝ :=
  Sum.elim (highPacketObservable a b m r D q C c G Φ) (fun _ => dummy)

theorem highPacketObservable_measurable (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (c : ι → ℝ) (G : Z → ℝ → (Fin r → ℝ) → ℝ)
    (hG : ∀ z ε, Measurable (fun ζ => G ζ z ε)) (Φ : (ι → ℝ) → ℝ) :
    Measurable (highPacketObservable a b m r D q C c G Φ) := by
  apply measurable_from_prod_countable_left
  intro h
  change Measurable (fun ζ => G ζ (densityPacketAtom a b m r D h.1).1
    (densityPacketAtom a b m r D h.1).2 *
      Φ (coefficientReset c (highResponseMarkAtom C q h.2).2 (highResponseMarkAtom C q h.2).1))
  exact (hG _ _).mul_const _

theorem centeredConditionalPacketObservable_measurable (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (c : ι → ℝ) (G : Z → ℝ → (Fin r → ℝ) → ℝ)
    (hG : ∀ z ε, Measurable (fun ζ => G ζ z ε)) (Φ : (ι → ℝ) → ℝ) (dummy : ℝ) :
    Measurable (centeredConditionalPacketObservable a b m r D q C c G Φ dummy) :=
  (highPacketObservable_measurable a b m r D q C c G hG Φ).sumElim measurable_const

/-- The true balanced activation kills every conditional affine response
observable. The finite-node response bound is derived from its actual nodes. -/
theorem centeredPacket_conditional_affine_zero (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C δ : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (c : ι → ℝ) (G : Z → ℝ → (Fin r → ℝ) → ℝ)
    (hG : ∀ z ε, Measurable (fun ζ => G ζ z ε)) (L : ℝ) (hL : 0 ≤ L)
    (hGbound : ∀ (ζ : Z) (h : HighDensityMarkIndex m r D),
      |G ζ (densityPacketAtom a b m r D h).1 (densityPacketAtom a b m r D h).2| ≤ L)
    (β : ℝ) (coeff : ι → ℝ) (dummy : ℝ) :
    (∫ e, centeredPacketActivation σ a b m r D q C δ A e *
      centeredConditionalPacketObservable a b m r D q C c G
        (responseAffineObservable β coeff) dummy e
      ∂centeredPacketLaw σ a b m r D q C δ A) = 0 := by
  let Φ := responseAffineObservable β coeff
  let M : ℝ := ∑ h : HighResponseMarkIndex ι q,
    |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hΦ (h : HighResponseMarkIndex ι q) :
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤ M := by
    dsimp only [M]
    exact Finset.single_le_sum (f := fun h : HighResponseMarkIndex ι q =>
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ h)
  have hbound : ∀ e, ‖centeredConditionalPacketObservable a b m r D q C c G Φ dummy e‖ ≤ max (L * M) |dummy| := by
    intro e
    cases e with
    | inl e =>
      simp only [centeredConditionalPacketObservable, Sum.elim_inl, highPacketObservable,
        Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (hGbound e.1 e.2.1) (hΦ e.2.2) (abs_nonneg _) hL).trans (le_max_left _ _)
    | inr e =>
      simp only [centeredConditionalPacketObservable, Sum.elim_inr, Real.norm_eq_abs]
      exact le_max_right _ _
  rw [centeredPacket_signed_action σ a b m r D q C δ A hA hcost hpos hδ hδ1
    _ (centeredConditionalPacketObservable_measurable a b m r D q C c G hG Φ dummy)
    _ hbound]
  exact (highPacketSignedMeasure_factor_integral σ a b m r D q C A hA hcost
    c G hG L hL hGbound Φ M hΦ).trans (highSeparatedPacketAction_affine_zero _ _ _ _ _ _ _ _ _ _ _ _ _)

/-- A structural factorization of an actual full-mark observable suffices;
measurability and bounded finite-node response factors are proved above. -/
theorem centeredPacket_conditional_affine_zero_of_factor (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C δ : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (c : ι → ℝ) (G : Z → ℝ → (Fin r → ℝ) → ℝ)
    (hG : ∀ z ε, Measurable (fun ζ => G ζ z ε)) (L : ℝ) (hL : 0 ≤ L)
    (hGbound : ∀ (ζ : Z) (h : HighDensityMarkIndex m r D),
      |G ζ (densityPacketAtom a b m r D h).1 (densityPacketAtom a b m r D h).2| ≤ L)
    (β : ℝ) (coeff : ι → ℝ)
    (F : (Z × HighPacketMarkIndex ι m r D q) ⊕ Unit → ℝ)
    (hfactor : ∀ e, F (Sum.inl e) = highPacketObservable a b m r D q C c G
      (responseAffineObservable β coeff) e) :
    (∫ e, centeredPacketActivation σ a b m r D q C δ A e * F e
      ∂centeredPacketLaw σ a b m r D q C δ A) = 0 := by
  have heq : F = centeredConditionalPacketObservable a b m r D q C c G
      (responseAffineObservable β coeff) (F (Sum.inr ())) := by
    funext e
    cases e with
    | inl e => exact hfactor e
    | inr e => cases e; rfl
  rw [heq]
  exact centeredPacket_conditional_affine_zero σ a b m r D q C δ A hA hcost hpos hδ hδ1
    c G hG L hL hGbound β coeff _

end NearlyMinimax
