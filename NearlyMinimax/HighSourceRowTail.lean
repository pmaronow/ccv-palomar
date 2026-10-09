module

public import NearlyMinimax.HighResponseTensorTail
public import NearlyMinimax.CompleteSourceMassAnnihilation


@[expose] public section

/-! All-count response bounds on every actual row of the complete source
family. The density factors may depend on the full spatial carrier and
density atom, and are independent only of the response atom. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem highPacket_reference_all_count_bound {n : ℕ}
    (σ : Measure Z) [IsFiniteMeasure σ] (ad bd : ℝ) (m r D q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2) (hpPlus : 0 ≤ pPlus)
    (A : Z → ι → ι → ℝ) (hA : ∀ γ δ, Measurable (fun ζ => A ζ γ δ))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ ad bd m r D q C A)
    (reset : Z × HighDensityMarkIndex m r D → Fin n → ℝ)
    (hmReset : ∀ i, Measurable (fun e => reset e i))
    (hReset : ∀ e i, |reset e i| ≤ pPlus)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ i, |∑ γ, φ i γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) (y : Fin n → Fin 3) :
    |highMarkedResponseAction (highPacketAbsoluteLaw σ ad bd m r D q C A)
      (highPacketActivation σ ad bd m r D q C A) a V η
      (fun e => reset (e.1,e.2.1))
      (fun e => coefficientReset c (highResponseMarkAtom C q e.2.2).2
        (highResponseMarkAtom 0 q e.2.2).1) g w φ y| ≤
      (pPlus^n*highSeparatedDerivativeBudget a ρ*(n : ℝ)^2*η^2)*
        highPacketMarkMass σ ad bd m r D q C A := by
  exact responseTensor_reference_all_count_bound σ q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
    (densityPacketWeight ad bd m r D) A
    (highPacketMarkWeight_measurable ad bd m r D q C A hA)
    (highPacketMarkWeight_integrable σ ad bd m r D q C A hA hcost) hpos
    (fun ζ e => reset (ζ,e))
    (fun e i => (hmReset i).comp (measurable_id.prodMk measurable_const))
    (fun ζ e i => hReset (ζ,e) i) g w φ c hc hg hw hφ hp y

theorem finePairPacket_reference_all_count_bound {n : ℕ}
    (σ : Measure Z) [IsFiniteMeasure σ] (ad bd : ℝ) (M q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2) (hpPlus : 0 ≤ pPlus)
    (A : Z → ι → ι → ℝ) (hA : ∀ γ δ, Measurable (fun ζ => A ζ γ δ))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < finePairPacketMarkMass σ ad bd M q C A)
    (reset : Z × FinePairDensityIndex M → Fin n → ℝ)
    (hmReset : ∀ i, Measurable (fun e => reset e i))
    (hReset : ∀ e i, |reset e i| ≤ pPlus)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ i, |∑ γ, φ i γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) (y : Fin n → Fin 3) :
    |highMarkedResponseAction (finePairPacketAbsoluteLaw σ ad bd M q C A)
      (finePairPacketActivation σ ad bd M q C A) a V η
      (fun e => reset (e.1,e.2.1))
      (fun e => coefficientReset c (finePairPacketResponseVector M q C e)
        (finePairPacketResponseTime M q e)) g w φ y| ≤
      (pPlus^n*highSeparatedDerivativeBudget a ρ*(n : ℝ)^2*η^2)*
        finePairPacketMarkMass σ ad bd M q C A := by
  exact responseTensor_reference_all_count_bound σ q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
    (finePairDensityWeight ad bd M) A
    (finePairPacketWeight_measurable ad bd M q C A hA)
    (finePairPacketWeight_integrable σ ad bd M q C A hA hcost) hpos
    (fun ζ e => reset (ζ,e))
    (fun e i => (hmReset i).comp (measurable_id.prodMk measurable_const))
    (fun ζ e i => hReset (ζ,e) i) g w φ c hc hg hw hφ hp y

end Packet

/-- All rows of the actual complete source satisfy the same Taylor cap,
with their own true variation masses. In particular this holds for sample
counts exceeding the exterior selector degree. -/
theorem sourceRow_reference_all_count_bound {n : ℕ}
    (d : ℕ) [NeZero d] (k D M q : ℕ) (hn : 1 ≤ n)
    (ad bd C lam ℓ N μ a V η ρ pPlus : ℝ)
    (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (hpPlus : 0 ≤ pPlus)
    (hpos : ∀ i, 0 < (sourceRowData d k D M q ad bd C lam ℓ N μ).rowMass i)
    (i : SourceRowIndex d D M q ad bd C lam ℓ N μ)
    (reset : SourceRowDensityMark d D M q ad bd C lam ℓ N μ i → Fin n → ℝ)
    (hmReset : ∀ u, Measurable (fun e => reset e u))
    (hReset : ∀ e u, |reset e u| ≤ pPlus)
    (g w : Fin n → ℝ) (φ : Fin n → HighFrameIndex d D → ℝ)
    (c : HighFrameIndex d D → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hg : ∀ u, |g u| ≤ ρ/2) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : HighFrameIndex d D → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ →
      ∀ u, |∑ γ, φ u γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) (y : Fin n → Fin 3) :
    |highMarkedResponseAction ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowLaw i)
      ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowActivation i) a V η
      (fun e => reset (sourceRowDensityProj d D M q ad bd C lam ℓ N μ i e))
      (fun e => coefficientReset c
        ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowVector i e)
        ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowTime i e)) g w φ y| ≤
      (pPlus^n*highSeparatedDerivativeBudget a ρ*(n : ℝ)^2*η^2)*
        (sourceRowData d k D M q ad bd C lam ℓ N μ).rowMass i := by
  cases i with
  | inl p =>
    cases p
    · exact highPacket_reference_all_count_bound (Measure.dirac ()) ad bd D 2 D q hn
        C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
        (hpos (.inl .unit)) reset hmReset hReset g w φ c hc hg hw hφ hp y
    · exact highPacket_reference_all_count_bound (finePairTimeFieldMeasure d 0 ℓ) ad bd D 2 D q hn
        C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        (finePairTimeMatrix d (finePairDistanceMatrix d D))
        (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 ℓ _)
        (hpos (.inl .coarse)) reset hmReset hReset g w φ c hc hg hw hφ hp y
    · exact finePairPacket_reference_all_count_bound (finePairTimeFieldMeasure d ℓ N) ad bd M q hn
        C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        (finePairTimeMatrix d (finePairDistanceMatrix d D))
        (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d ℓ N _)
        (hpos (.inl .fine)) reset hmReset hReset g w φ c hc hg hw hφ hp y
  | inr i =>
    cases i with
    | inl _ =>
      exact highPacket_reference_all_count_bound (Measure.dirac ()) ad bd D 1 D q hn
        C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
        (hpos (.inr (.inl ()))) reset hmReset hReset g w φ c hc hg hw hφ hp y
    | inr i =>
      let r := higherBandFamilyTarget i.val
      let m := higherBandFamilyGuardDegree M i.val
      let T := higherBandFamilyUpper d ℓ N μ i.val
      letI := higherBandCarrierMeasure_finite d r ℓ T i.property.1 i.val.2
      exact highPacket_reference_all_count_bound (higherBandCarrierMeasure d r ℓ T i.val.2)
        ad bd m r D q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        (higherBandCarrierAmplitude d r D lam i.val.2)
        (higherBandCarrierAmplitude_measurable d r D lam i.val.2)
        (higherBandCarrierAmplitude_cost_integrable d r D lam ℓ T i.property.1 i.val.2)
        (hpos (.inr (.inr i))) reset hmReset hReset g w φ c hc hg hw hφ hp y

end NearlyMinimax
