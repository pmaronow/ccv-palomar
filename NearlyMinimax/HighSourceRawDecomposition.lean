module

public import NearlyMinimax.CompleteSourceRows
public import NearlyMinimax.FinePairAllCounts
public import NearlyMinimax.HighCardinalScores
public import NearlyMinimax.CardinalGlobalBandL2
public import NearlyMinimax.SpatialSubsetIntegral
public import NearlyMinimax.FinePairUnionMassAnnihilation


@[expose] public section

/-! Exact count decomposition of the actual complete source packets.
The statements below evaluate genuine signed integrals; no local action
identity or count cancellation is supplied as a hypothesis. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
attribute [local instance] Classical.propDecidable

def higherBandFirstAction {d n : ℕ} (ad bd lam L T : ℝ) (r m D q : ℕ)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, highPacketObservable ad bd m r D q C c
    (fun ζ z eps => ∏ i, localDensityReset ad bd r z eps p
      (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i) Φ e
    ∂<•higherBandSignedRow d r m D q ad bd C lam L T fine

theorem higherBandFirstAction_eq_packet {d n : ℕ}
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hT : 1 ≤ T)
    (r m D q : ℕ) (hr : 1 ≤ r) (C : ℝ) (fine : Bool)
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ =
      highSeparatedPacketAction (higherBandCarrierMeasure d r L T fine)
        ad bd m r D q C (higherBandCarrierAmplitude d r D lam fine) c
        (fun ζ z eps => ∏ i, localDensityReset ad bd r z eps p
          (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i) Φ := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  have hm (i : Fin n) (l : Fin r) :
      Measurable (fun ζ => higherBandCarrierFactor d r lam fine ζ l (U i)) :=
    (higherBandCarrierFactor_joint_measurable d r lam fine l).comp
      (measurable_id.prodMk measurable_const)
  have hG (z : ℝ) (eps : Fin r → ℝ) : Measurable
      (fun ζ => ∏ i, localDensityReset ad bd r z eps p
        (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i) := by
    apply Finset.measurable_fun_prod
    intro i _
    unfold localDensityReset
    exact measurable_const.add ((Finset.measurable_fun_sum _
      (fun l _ => (hm i l).const_mul (eps l))).const_mul _)
  have hb (ζ : HigherBandCarrier d r fine) (e : HighDensityMarkIndex m r D)
      (i : Fin n) : |localDensityReset ad bd r
        (densityPacketAtom ad bd m r D e).1 (densityPacketAtom ad bd m r D e).2 p
        (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i| ≤ bd := by
    have he := densityPacketAtom_mem ad bd hab.le m r D e
    have hh := localDensityReset_mem_interval ad bd ha hab r hr _ he.1 _ he.2 p
      (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i (hp i)
      (fun l => higherBandCarrierFactor_bound d r lam fine ζ l (U i) (hU i))
    rw [abs_of_nonneg (ha.le.trans hh.1)]
    exact hh.2
  exact highPacketSignedMeasure_factor_integral _ ad bd m r D q C _
    (higherBandCarrierAmplitude_measurable d r D lam fine)
    (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine)
    c _ hG (bd^n) (pow_nonneg (ha.trans hab).le n)
    (fun ζ e => finite_density_product_abs_bound _ bd (ha.trans hab).le (hb ζ e))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)

theorem higherBandFirstAction_count_expansion {d n : ℕ}
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hT : 1 ≤ T)
    (r m D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ =
      densityCountCoefficient ad bd m r n *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, (∏ i ∈ S, p i) *
          responseMatrixAction q C
            (separatedSubsetMatrix (higherBandCarrierMeasure d r L T fine) r
              (fun ζ i l => higherBandCarrierFactor d r lam fine ζ l (U i))
              (higherBandCarrierAmplitude d r D lam fine) S) c Φ := by
  rw [higherBandFirstAction_eq_packet ad bd lam L T ha hab hT r m D q hr C fine U hU p hp c Φ]
  have hm (i : Fin n) (l : Fin r) :
      Measurable (fun ζ => higherBandCarrierFactor d r lam fine ζ l (U i)) :=
    (higherBandCarrierFactor_joint_measurable d r lam fine l).comp
      (measurable_id.prodMk measurable_const)
  simpa only [Finset.card_univ, Fintype.card_fin] using
    highSeparatedPacketAction_row (higherBandCarrierMeasure d r L T fine) ad bd ha hab
      m r D q hr hD Finset.univ (by simpa using hnD) p _ hm
      (fun ζ i l => higherBandCarrierFactor_bound d r lam fine ζ l (U i) (hU i)) C _
      (higherBandCarrierAmplitude_measurable d r D lam fine)
      (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine) c Φ

theorem higherBandFirstAction_zero_small_count {d n : ℕ}
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hT : 1 ≤ T)
    (r m D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D) (hnr : n < r)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ = 0 := by
  rw [higherBandFirstAction_count_expansion ad bd lam L T ha hab hT r m D q hr hD hnD
    C fine U hU p hp c Φ]
  have he : (Finset.univ : Finset (Fin n)).powersetCard r = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simpa using hnr)
  simp only [he, Finset.sum_empty, mul_zero]

theorem higherBandFirstAction_zero_other_count {d n : ℕ}
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hT : 1 ≤ T)
    (r m D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D)
    (hnm : n ≤ m) (hne : n ≠ r) (C : ℝ) (fine : Bool)
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ = 0 := by
  by_cases hnr : n < r
  · exact higherBandFirstAction_zero_small_count ad bd lam L T ha hab hT r m D q hr hD hnD
      hnr C fine U hU p hp c Φ
  rw [higherBandFirstAction_count_expansion ad bd lam L T ha hab hT r m D q hr hD hnD
    C fine U hU p hp c Φ,
    densityCountCoefficient_exact ad bd ha hab m r n hr (by omega) hnm, if_neg hne, zero_mul]

theorem cardinal_density_subset_sym_eq {d n : ℕ} (lam : ℝ)
    (S : Finset (Fin n)) (z : CardinalSeparatedMark d S.card)
    (U : Fin n → Covariate d) :
    densitySeparatedSym S.card (fun i l => cardinalSeparatedFactor lam z l (U i)) S =
      cardinalSeparatedSymmetricFactor lam z (spatialSubsetConfiguration S U) := by
  let e : Fin S.card ≃ S :=
    ((Fintype.equivFin S).trans (finCongr (Fintype.card_coe S))).symm
  rw [densitySeparatedSym_eq_permutation_average S.card _ S e]
  unfold cardinalSeparatedSymmetricFactor
  congr 1
  apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin S.card)))
  intro τ
  have h := Equiv.prod_comp τ
    (fun l => cardinalSeparatedFactor lam z l (U (e (τ.symm l)).val))
  simp only [Equiv.symm_apply_apply] at h
  convert h using 1
  apply Finset.prod_congr rfl
  intro l _
  rfl

def higherBandActualMatrix {d n D : ℕ} (lam L T : ℝ) (fine : Bool)
    (U : Fin n → Covariate d) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  if fine then globalCardinalBandMatrix lam L T U else integratedCardinalMatrix lam T U

theorem higherBand_subset_matrix_actual {d n D : ℕ} (lam : ℝ) (hlam : 0 ≤ lam)
    (L T : ℝ) (hL : 0 < L) (hT : 1 ≤ T) (fine : Bool)
    (S : Finset (Fin n)) (hS : 2 ≤ S.card) (U : Fin n → Covariate d)
    (hU : ∀ i j, |U i j| ≤ 2) :
    separatedSubsetMatrix (higherBandCarrierMeasure d S.card L T fine) S.card
      (fun ζ i l => higherBandCarrierFactor d S.card lam fine ζ l (U i))
      (higherBandCarrierAmplitude d S.card D lam fine) S =
      higherBandActualMatrix lam L T fine (spatialSubsetConfiguration S U) := by
  have hb : ∀ l j, |spatialSubsetConfiguration S U l j| ≤ 2 := fun l => hU _
  funext β β'
  cases fine
  · change (∫ z, densitySeparatedSym S.card
        (fun i l => cardinalSeparatedFactor lam z l (U i)) S *
        cardinalSeparatedAmplitude lam z β β' ∂cardinalSeparatedMeasure d S.card T) = _
    simp_rw [cardinal_density_subset_sym_eq]
    exact (integrated_cardinal_symmetric_separated_exact lam hlam hT _ hb β β').symm
  · change (∫ z, densitySeparatedSym S.card
        (fun i l => cardinalSeparatedFactor lam z.2 l (U i)) S *
        cardinalBandAmplitude lam z β β' ∂cardinalBandMeasure d S.card L T) = _
    simp_rw [cardinal_density_subset_sym_eq]
    exact (integrated_cardinal_actual_band_separated_exact hS lam hlam hL hT _ hb β β').symm

theorem higherBandFirstAction_actual_count_expansion {d n : ℕ}
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    (hL : 0 < L) (hT : 1 ≤ T) (r m D q : ℕ) (hr : 2 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ =
      densityCountCoefficient ad bd m r n *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, (∏ i ∈ S, p i) *
          responseMatrixAction q C
            (higherBandActualMatrix lam L T fine (spatialSubsetConfiguration S U)) c Φ := by
  rw [higherBandFirstAction_count_expansion ad bd lam L T ha hab hT r m D q (by omega)
    hD hnD C fine U hU p hp c Φ]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  have he := (Finset.mem_powersetCard.mp hS).2
  have hh := higherBand_subset_matrix_actual (D := D) lam hlam L T hL hT fine S
    (by omega) U hU
  subst r
  rw [hh]

def singletonFirstAction {d n : ℕ} (ad bd : ℝ) (D q : ℕ) (C : ℝ)
    (p : Fin n → ℝ) (c : HighFrameIndex d D → ℝ)
    (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, highPacketObservable ad bd D 1 D q C c
    (fun _ z eps => ∏ i, localDensityReset ad bd 1 z eps p (fun _ _ => 1) i) Φ e
    ∂<•highPacketSignedMeasure (Measure.dirac ()) ad bd D 1 D q C
      (fun _ => finePairUnitMatrix d D)

set_option maxHeartbeats 120000 in
theorem singletonFirstAction_eq_packet {d n : ℕ}
    (ad bd : ℝ) (ha : 0 < ad) (hab : ad < bd) (D q : ℕ) (C : ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    singletonFirstAction ad bd D q C p c Φ =
      highSeparatedPacketAction (Measure.dirac ()) ad bd D 1 D q C
        (fun _ => finePairUnitMatrix d D) c
        (fun _ z eps => ∏ i, localDensityReset ad bd 1 z eps p (fun _ _ => 1) i) Φ := by
  unfold singletonFirstAction
  have hb (e : HighDensityMarkIndex D 1 D) (i : Fin n) :
      |localDensityReset ad bd 1 (densityPacketAtom ad bd D 1 D e).1
        (densityPacketAtom ad bd D 1 D e).2 p (fun _ _ => 1) i| ≤ bd := by
    have he := densityPacketAtom_mem ad bd hab.le D 1 D e
    have hh := localDensityReset_mem_interval ad bd ha hab 1 (by norm_num) _ he.1 _ he.2 p
      (fun _ _ => 1) i (hp i) (by intro _; norm_num)
    rw [abs_of_nonneg (ha.le.trans hh.1)]
    exact hh.2
  exact highPacketSignedMeasure_factor_integral (Z := Unit) (ι := HighFrameIndex d D)
    (Measure.dirac ()) ad bd D 1 D q C
    (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
    c (fun (_ : Unit) z eps => ∏ i, localDensityReset ad bd 1 z eps p (fun _ _ => 1) i)
    (fun _ _ => measurable_const) (bd^n) (pow_nonneg (ha.trans hab).le n)
    (fun _ e => finite_density_product_abs_bound _ bd (ha.trans hab).le (hb e))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)

theorem singletonFirstAction_zero_other_count {d n : ℕ}
    (ad bd : ℝ) (ha : 0 < ad) (hab : ad < bd) (D q : ℕ) (hD : 1 ≤ D)
    (hnD : n ≤ D) (hne : n ≠ 1) (C : ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    singletonFirstAction ad bd D q C p c Φ = 0 := by
  rw [singletonFirstAction_eq_packet ad bd ha hab D q C p hp c Φ]
  by_cases hn : n = 0
  · subst n
    unfold highSeparatedPacketAction
    simp_rw [densityPacketAction_mul_right,
      density_packet_product_zero_of_small_count (Finset.univ : Finset (Fin 0))
        ad bd ha hab D 1 D (by norm_num) hD (by simp) (by simp) p (fun _ _ => 1), zero_mul]
    exact integral_zero _ _
  have hh := highSeparatedPacketAction_count_selector (Measure.dirac ()) ad bd ha hab D 1 D q
    (by norm_num) hD (Finset.univ : Finset (Fin n)) (by simpa using hnD)
    (by simpa using hnD) (by simpa using (show 1 ≤ n by omega)) p
    (fun _ : Unit => fun _ _ => (1 : ℝ)) (fun _ _ => measurable_const)
    (by intro _ _ _; norm_num) C (fun _ => finePairUnitMatrix d D)
    (fun _ _ => measurable_const) (integrable_const _) c Φ
  simpa only [Finset.card_univ, Fintype.card_fin, if_neg hne] using hh

theorem densitySeparatedSym_one {α : Type*} [DecidableEq α] (r : ℕ)
    (S : Finset α) (hS : S.card = r) : densitySeparatedSym r (fun _ _ => (1 : ℝ)) S = 1 := by
  let e : Fin r ≃ S :=
    ((Fintype.equivFin S).trans (finCongr ((Fintype.card_coe S).trans hS))).symm
  rw [densitySeparatedSym_eq_permutation_average r _ S e]
  simp only [Finset.prod_const_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_perm, Fintype.card_fin]
  exact div_self (by positivity)

theorem singletonFirstAction_count_one {d : ℕ}
    (ad bd : ℝ) (ha : 0 < ad) (hab : ad < bd) (D q : ℕ) (hD : 1 ≤ D) (C : ℝ)
    (p : Fin 1 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    singletonFirstAction ad bd D q C p c Φ =
      (∏ i, p i) * responseMatrixAction q C (finePairUnitMatrix d D) c Φ := by
  rw [singletonFirstAction_eq_packet ad bd ha hab D q C p hp c Φ]
  unfold highSeparatedPacketAction
  simp_rw [densityPacketAction_mul_right]
  have hh := density_packet_product_count_selector (Finset.univ : Finset (Fin 1))
    ad bd ha hab D 1 D (by norm_num) hD (by simpa using hD)
    (by simpa using hD) p (fun _ _ => 1)
  have hpow : (Finset.univ : Finset (Fin 1)).powersetCard 1 = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin 1))
  simp only [Finset.card_univ, Fintype.card_fin, ite_true, hpow, Finset.sum_singleton,
    densitySeparatedSym_one 1 (Finset.univ : Finset (Fin 1)) (by simp), mul_one] at hh
  simp_rw [hh]
  simp

def completeSourceSignedFirstAction {d n : ℕ} (ad bd lam ℓ N μ : ℝ)
    (D M q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  finePairThreeRowFirstAction ad bd ℓ N D M q C U p c Φ +
    singletonFirstAction ad bd D q C p c Φ +
    ∑ i : HigherBandFamilyIndex d D M q ad bd C lam ℓ N μ,
      higherBandFirstAction ad bd lam ℓ (higherBandFamilyUpper d ℓ N μ i.val)
        (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q C i.val.2 U p c Φ

/-- The raw complete-source numerator subtracts the global variance
derivative once, after adding every genuine row first action. -/
def completeSourceRawNumerator {d n : ℕ} (ad bd lam ℓ N μ : ℝ)
    (D M q : ℕ) (C a V η : ℝ) (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) : ℝ :=
  completeSourceSignedFirstAction ad bd lam ℓ N μ D M q C U p c
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
    η^2 * (∏ i, p i) * ∑ i, (w i)^2 *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i

end NearlyMinimax
