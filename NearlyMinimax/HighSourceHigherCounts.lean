module

public import NearlyMinimax.HighSourceCountCancellation


@[expose] public section

/-! The complete source's higher-count first action: ordinary pair and
singleton selectors vanish, leaving the actual higher family plus the
fine-pair alias and even field actions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section Pair
variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]

theorem ordinaryPairPacket_zero_other_count {n : ℕ} (hn : 3 ≤ n)
    (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m D q : ℕ) (hnm : n ≤ m) (hnD : n ≤ D) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin n → ℝ)
    (hmψ : ∀ i, Measurable (fun ζ => ψ ζ i)) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, highPacketObservable a b m 2 D q C c
      (fun ζ z eps => ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i) Φ e
      ∂<•highPacketSignedMeasure σ a b m 2 D q C A) = 0 := by
  rw [highPacketSignedMeasure_factor_integral σ a b m 2 D q C A hA hcost c
    (fun ζ z eps => ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i)
    (fun z eps => Finset.measurable_fun_prod _ (fun i _ => ordinaryPairReset_measurable a b p ψ hmψ z eps i))
    (b^n) (pow_nonneg (ha.trans hab).le n)
    (fun ζ e => finite_density_product_abs_bound _ b (ha.trans hab).le
      (ordinaryPairReset_atom_abs_le a b ha hab m D p hp (ψ ζ) (hbψ ζ) e))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
  have hh := highSeparatedPacketAction_count_selector σ a b ha hab m 2 D q
    (by omega) (by omega) (Finset.univ : Finset (Fin n)) (by simpa using hnD)
    (by simpa using hnm) (by simpa using (show 2 ≤ n by omega)) p
    (fun ζ i _ => ψ ζ i) (fun i _ => hmψ i) (fun ζ i _ => hbψ ζ i) C A hA hcost c Φ
  simpa only [Finset.card_univ, Fintype.card_fin, if_neg (show n ≠ 2 by omega)] using hh

end Pair

theorem finePairThreeRowFirstAction_higher {d n D : ℕ} [NeZero d]
    (hn : 3 ≤ n) (hnD : n ≤ D) (ad bd ℓ N : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (M q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Icc ad bd) (c : HighFrameIndex d D → ℝ)
    (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    finePairThreeRowFirstAction ad bd ℓ N D M q C U p c Φ =
      finePairPairAliasAction ad bd ℓ N M q C U p c Φ +
        finePairEvenFieldAction ad bd ℓ N M q C U p c Φ := by
  have hu : finePairUnitFirstAction ad bd D q C p c Φ = 0 :=
    ordinaryPairPacket_zero_other_count hn (Measure.dirac ()) ad bd ha hab D D q hnD hnD C
      (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _) c p hp
      (fun _ _ => 1) (fun _ => measurable_const) (by intro _ _; norm_num) Φ
  have hc : finePairCoarseFirstAction ad bd ℓ D q C U p c Φ = 0 :=
    ordinaryPairPacket_zero_other_count hn _ ad bd ha hab D D q hnD hnD C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 ℓ _) c p hp
      (fun ζ i => finePairTimeFieldValue ζ (U i))
      (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
      (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le) Φ
  rw [finePairThreeRowFirstAction, hu, hc,
    finePairFineFirstAction_alias_even_field ad bd ℓ N ha hab M q C U p hp c Φ]
  ring

theorem completeSourceSignedFirstAction_higher {d n : ℕ} [NeZero d]
    (ad bd lam ℓ N μ : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    completeSourceSignedFirstAction ad bd lam ℓ N μ D M q C U p c Φ =
      higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c Φ +
        finePairPairAliasAction ad bd ℓ N M q C U p c Φ +
        finePairEvenFieldAction ad bd ℓ N M q C U p c Φ := by
  rw [completeSourceSignedFirstAction_eq_family,
    singletonFirstAction_zero_other_count ad bd ha hab D q (by omega) hnD (by omega) C p hp c Φ,
    finePairThreeRowFirstAction_higher hn hnD ad bd ℓ N ha hab M q C U p hp c Φ]
  ring

theorem completeSourceRawNumerator_higher {d n : ℕ} [NeZero d]
    (ad bd lam ℓ N μ : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D) (C a V η : ℝ)
    (U : Fin n → Covariate d) (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    completeSourceRawNumerator ad bd lam ℓ N μ D M q C a V η U p g w c y =
      higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) +
      finePairPairAliasAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) +
      finePairEvenFieldAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
      η^2 * (∏ i, p i) * ∑ i, (w i)^2 *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i := by
  unfold completeSourceRawNumerator
  rw [completeSourceSignedFirstAction_higher ad bd lam ℓ N μ ha hab D M q hn hnD C U p hp c]

theorem completeSourceSignedFirstAction_higher_before_alias {d n : ℕ} [NeZero d]
    (ad bd lam ℓ N μ : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D) (hnM : n ≤ M) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    completeSourceSignedFirstAction ad bd lam ℓ N μ D M q C U p c Φ =
      higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c Φ +
        finePairEvenFieldAction ad bd ℓ N M q C U p c Φ := by
  rw [completeSourceSignedFirstAction_higher ad bd lam ℓ N μ ha hab D M q hn hnD C U p hp c Φ,
    finePairPairAliasAction_zero_selected_count ad bd ℓ N ha hab M q hn hnM C U p c Φ, add_zero]

end NearlyMinimax
