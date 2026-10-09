module

public import NearlyMinimax.HighTorusScores


@[expose] public section

/-! Genuine signed-Xi local scores. The bridge to conditional product-law
orthogonality is proved by evaluating the actual separated signed measure,
with outer integrability supplied by its matrix representation cost. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section
variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]

theorem densityPacketAction_eq_finite_response_action {n : ℕ}
    (ad bd : ℝ) (m r D q : ℕ) (C : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ)
    (reset : ℝ → (Fin r → ℝ) → Fin n → ℝ) (Φ : (ι → ℝ) → ℝ) :
    densityPacketAction ad bd m r D (fun z ε =>
      (∏ i, reset z ε i) * responseMatrixAction q C A c Φ) =
    highDensityResponseAction q C (densityPacketWeight ad bd m r D) (fun _ => A) c
      (fun e => ∏ i, reset (densityPacketAtom ad bd m r D e).1
        (densityPacketAtom ad bd m r D e).2 i) Φ := by
  have h := densityPacketSignedRule_integral ad bd m r D
    (fun z ε => (∏ i, reset z ε i) * responseMatrixAction q C A c Φ)
  rw [densityPacketSignedRule, atomicSignedRule_integral] at h
  rw [← h]
  unfold highDensityResponseAction
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- The actual source local score, using the signed separated Xi measure
on positive representation marks and genuine finite density/response atoms. -/
def highSeparatedXiScore {n : ℕ} (σ : Measure Z) (ad bd : ℝ) (m r D q : ℕ)
    (C a V η : ℝ) (A : Z → ι → ι → ℝ) (p : Fin n → ℝ)
    (reset : Z → ℝ → (Fin r → ℝ) → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (y : Fin n → Fin 3) : ℝ :=
  ((∫ᵛ e, highPacketObservable ad bd m r D q C c
      (fun ζ z ε => ∏ i, reset ζ z ε i)
      (fun v => highResponseProduct a V η g w φ v y) e
      ∂<•(highPacketSignedMeasure σ ad bd m r D q C A)) -
    η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
    ((∏ i, p i) * highResponseProduct a V η g w φ c y)

theorem highSeparatedXiScore_eq_integrated {n : ℕ} (σ : Measure Z) [IsFiniteMeasure σ]
    (ad bd : ℝ) (m r D q : ℕ) (C a V η pPlus : ℝ) (hpPlus : 0 ≤ pPlus)
    (A : Z → ι → ι → ℝ) (p : Fin n → ℝ)
    (reset : Z → ℝ → (Fin r → ℝ) → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hReset : ∀ z ε i, Measurable (fun ζ => reset ζ z ε i))
    (hBound : ∀ ζ (h : HighDensityMarkIndex m r D) i,
      |reset ζ (densityPacketAtom ad bd m r D h).1 (densityPacketAtom ad bd m r D h).2 i| ≤ pPlus)
    (y : Fin n → Fin 3) :
    highSeparatedXiScore σ ad bd m r D q C a V η A p reset g w φ c y =
      highIntegratedLocalScore σ q C a V η (fun _ => densityPacketWeight ad bd m r D)
        (fun ζ _ => A ζ) p (fun ζ h => reset ζ (densityPacketAtom ad bd m r D h).1
          (densityPacketAtom ad bd m r D h).2) g w φ c y := by
  let Φ (v : ι → ℝ) := highResponseProduct a V η g w φ v y
  let M : ℝ := ∑ h : HighResponseMarkIndex ι q,
    |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)|
  have hΦ (h : HighResponseMarkIndex ι q) :
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum (f := fun h : HighResponseMarkIndex ι q =>
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)|)
      (fun h _ => abs_nonneg _) (Finset.mem_univ h)
  have hG (z : ℝ) (ε : Fin r → ℝ) : Measurable (fun ζ => ∏ i, reset ζ z ε i) :=
    Finset.measurable_fun_prod _ (fun i _ => hReset z ε i)
  have hGbound (ζ : Z) (h : HighDensityMarkIndex m r D) :
      |∏ i, reset ζ (densityPacketAtom ad bd m r D h).1
        (densityPacketAtom ad bd m r D h).2 i| ≤ pPlus^n :=
    finite_density_product_abs_bound _ pPlus hpPlus (hBound ζ h)
  have hf := highPacketSignedMeasure_factor_integral σ ad bd m r D q C A hA hcost c
    (fun ζ z ε => ∏ i, reset ζ z ε i) hG (pPlus^n) (by positivity) hGbound Φ M hΦ
  have ha : highSeparatedPacketAction σ ad bd m r D q C A c
      (fun ζ z ε => ∏ i, reset ζ z ε i) Φ =
      highIntegratedResponseAction σ q C a V η (fun _ => densityPacketWeight ad bd m r D)
        (fun ζ _ => A ζ) (fun ζ h => reset ζ (densityPacketAtom ad bd m r D h).1
          (densityPacketAtom ad bd m r D h).2) g w φ c y := by
    unfold highSeparatedPacketAction highIntegratedResponseAction
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ζ =>
      densityPacketAction_eq_finite_response_action ad bd m r D q C (A ζ) c (reset ζ) Φ)
  unfold highSeparatedXiScore highIntegratedLocalScore
  rw [hf, ha]

/-- Conditional centering of the actual signed-Xi score is derived from
genuine response normalization and the finite rule's zero mass. -/
theorem highSeparatedXiScore_measure_centered {n : ℕ} (σ : Measure Z) [IsFiniteMeasure σ]
    (ad bd : ℝ) (m r D q : ℕ) (C a V η pPlus : ℝ) (ha : a ≠ 0)
    (hpPlus : 0 ≤ pPlus) (A : Z → ι → ι → ℝ) (p : Fin n → ℝ)
    (reset : Z → ℝ → (Fin r → ℝ) → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hReset : ∀ z ε i, Measurable (fun ζ => reset ζ z ε i))
    (hBound : ∀ ζ (h : HighDensityMarkIndex m r D) i,
      |reset ζ (densityPacketAtom ad bd m r D h).1 (densityPacketAtom ad bd m r D h).2 i| ≤ pPlus)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    (∫ y, highSeparatedXiScore σ ad bd m r D q C a V η A p reset g w φ c y
      ∂Measure.pi (fun i => ternaryIndexMeasure a (coefficientRegression η g w φ c i) V
        ha (fun b => (hp i b).le))) = 0 := by
  simp_rw [highSeparatedXiScore_eq_integrated σ ad bd m r D q C a V η pPlus hpPlus
    A p reset g w φ c hA hcost hReset hBound]
  exact high_integrated_local_score_measure_centered σ q C a V η ha _ _ p _ g w φ c
    hpd hp (fun y => high_separated_density_response_action_integrable σ q C
      (densityPacketWeight ad bd m r D) A _ c
      (fun v => highResponseProduct a V η g w φ v y) hA hcost
      (fun h i => hReset _ _ i) pPlus hpPlus hBound)

/-- Disjoint-patch orthogonality for the source's actual non-atomic signed
Xi packets, not an assumed score covariance identity. -/
theorem highSeparatedXiScores_torus_orthogonal (d k n : ℕ) [NeZero k]
    (σ : HighWindowLabels d k → Measure Z) [∀ j, IsFiniteMeasure (σ j)]
    (ad bd : ℝ) (m r D : ℕ) (q : HighWindowLabels d k → ℕ)
    (C a V η pPlus : ℝ) (ha : a ≠ 0) (hpPlus : 0 ≤ pPlus)
    (A : HighWindowLabels d k → Z → ι → ι → ℝ) (p : Fin n → ℝ)
    (reset : HighWindowLabels d k → Z → ℝ → (Fin r → ℝ) → Fin n → ℝ)
    (g : HighWindowLabels d k → Fin n → ℝ)
    (φ : HighWindowLabels d k → Fin n → ι → ℝ)
    (c : HighWindowLabels d k → ι → ℝ) (x : Fin n → Covariate d) (f : Fin n → ℝ)
    (hreg : ∀ j, coefficientRegression η (g j)
      (fun i => highPeriodicTensor d k j (x i)) (φ j) (c j) = f)
    (hpd : ∀ i, p i ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (f i) V b)
    (hA : ∀ j i l, Measurable (fun ζ => A j ζ i l))
    (hcost : ∀ j, Integrable (separatedMatrixCost (A j)) (σ j))
    (hReset : ∀ j z ε i, Measurable (fun ζ => reset j ζ z ε i))
    (hBound : ∀ j ζ (h : HighDensityMarkIndex m r D) i,
      |reset j ζ (densityPacketAtom ad bd m r D h).1 (densityPacketAtom ad bd m r D h).2 i| ≤ pPlus)
    (j l : HighWindowLabels d k) (hjl : l ∉ highNeighborLabels d k j) :
    (∫ y, highSeparatedXiScore (σ j) ad bd m r D (q j) C a V η (A j) p (reset j)
      (g j) (fun i => highPeriodicTensor d k j (x i)) (φ j) (c j) y *
      highSeparatedXiScore (σ l) ad bd m r D (q l) C a V η (A l) p (reset l)
        (g l) (fun i => highPeriodicTensor d k l (x i)) (φ l) (c l) y
      ∂Measure.pi (fun i => ternaryIndexMeasure a (f i) V ha (fun b => (hp i b).le))) = 0 := by
  simp_rw [highSeparatedXiScore_eq_integrated (σ j) ad bd m r D (q j) C a V η pPlus hpPlus
      (A j) p (reset j) (g j) (fun i => highPeriodicTensor d k j (x i))
      (φ j) (c j) (hA j) (hcost j) (hReset j) (hBound j),
    highSeparatedXiScore_eq_integrated (σ l) ad bd m r D (q l) C a V η pPlus hpPlus
      (A l) p (reset l) (g l) (fun i => highPeriodicTensor d k l (x i))
      (φ l) (c l) (hA l) (hcost l) (hReset l) (hBound l)]
  exact highTorusIntegratedScores_orthogonal d k n σ q C a V η pPlus ha hpPlus
    (fun _ => densityPacketWeight ad bd m r D) A p
    (fun j ζ h => reset j ζ (densityPacketAtom ad bd m r D h).1 (densityPacketAtom ad bd m r D h).2)
    g φ c x f hreg hpd hp hA hcost (fun j h i => hReset j _ _ i) hBound j l hjl

/-- The actual Xi score family inherits the exact manuscript graph factor.
All matrix and reset hypotheses concern genuine representation primitives. -/
theorem highSeparatedXiScores_torus_variance_bound (d k n : ℕ) [NeZero k]
    (σ : HighWindowLabels d k → Measure Z) [∀ j, IsFiniteMeasure (σ j)]
    (ad bd : ℝ) (m r D : ℕ) (q : HighWindowLabels d k → ℕ)
    (C a V η pPlus : ℝ) (ha : a ≠ 0) (hpPlus : 0 ≤ pPlus)
    (A : HighWindowLabels d k → Z → ι → ι → ℝ) (p : Fin n → ℝ)
    (reset : HighWindowLabels d k → Z → ℝ → (Fin r → ℝ) → Fin n → ℝ)
    (g : HighWindowLabels d k → Fin n → ℝ)
    (φ : HighWindowLabels d k → Fin n → ι → ℝ)
    (c : HighWindowLabels d k → ι → ℝ) (x : Fin n → Covariate d) (f : Fin n → ℝ)
    (hreg : ∀ j, coefficientRegression η (g j)
      (fun i => highPeriodicTensor d k j (x i)) (φ j) (c j) = f)
    (hpd : ∀ i, p i ≠ 0) (hp : ∀ i b, 0 < ternaryMass a (f i) V b)
    (hA : ∀ j i l, Measurable (fun ζ => A j ζ i l))
    (hcost : ∀ j, Integrable (separatedMatrixCost (A j)) (σ j))
    (hReset : ∀ j z ε i, Measurable (fun ζ => reset j ζ z ε i))
    (hBound : ∀ j ζ (h : HighDensityMarkIndex m r D) i,
      |reset j ζ (densityPacketAtom ad bd m r D h).1 (densityPacketAtom ad bd m r D h).2 i| ≤ pPlus) :
    (∫ y, (∑ j, highSeparatedXiScore (σ j) ad bd m r D (q j) C a V η (A j) p (reset j)
      (g j) (fun i => highPeriodicTensor d k j (x i)) (φ j) (c j) y)^2
      ∂Measure.pi (fun i => ternaryIndexMeasure a (f i) V ha (fun b => (hp i b).le))) ≤
    (3^d : ℕ) * ∑ j, ∫ y,
      (highSeparatedXiScore (σ j) ad bd m r D (q j) C a V η (A j) p (reset j)
        (g j) (fun i => highPeriodicTensor d k j (x i)) (φ j) (c j) y)^2
      ∂Measure.pi (fun i => ternaryIndexMeasure a (f i) V ha (fun b => (hp i b).le)) := by
  have he (j : HighWindowLabels d k) (y : Fin n → Fin 3) :=
    highSeparatedXiScore_eq_integrated (σ j) ad bd m r D (q j) C a V η pPlus hpPlus
      (A j) p (reset j) (g j) (fun i => highPeriodicTensor d k j (x i)) (φ j) (c j)
      (hA j) (hcost j) (hReset j) (hBound j) y
  simp_rw [he]
  exact highTorusIntegratedScores_variance_bound d k n σ q C a V η pPlus ha hpPlus
    (fun _ => densityPacketWeight ad bd m r D) A p
    (fun j ζ h => reset j ζ (densityPacketAtom ad bd m r D h).1 (densityPacketAtom ad bd m r D h).2)
    g φ c x f hreg hpd hp hA hcost (fun j h i => hReset j _ _ i) hBound

end
end NearlyMinimax
