module

public import NearlyMinimax.FinePairHyperplanePacket
public import NearlyMinimax.FinePairResponseGeometry
public import NearlyMinimax.SpatialLaplaceTail


@[expose] public section

/-! Exact count-two action of the genuine three source fine-pair rows.
The density selectors and the Lebesgue/field carrier are evaluated before
the single response variance correction is applied. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem densitySeparatedSym_identical_columns (ψ : Fin 2 → ℝ) :
    densitySeparatedSym 2 (fun i _ => ψ i) Finset.univ = ψ 0 * ψ 1 := by
  classical
  let e : Fin 2 ≃ (Finset.univ : Finset (Fin 2)) :=
    (Equiv.subtypeUnivEquiv (fun i : Fin 2 => Finset.mem_univ i)).symm
  rw [densitySeparatedSym_eq_permutation_average 2 _ Finset.univ e]
  simp only [e, Equiv.subtypeUnivEquiv_symm_apply, Fin.prod_univ_two]
  simp [Fintype.card_perm]

theorem ordinaryPairDensity_action (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m D : ℕ) (hm : 2 ≤ m) (hD : 2 ≤ D) (p ψ : Fin 2 → ℝ) :
    densityPacketAction a b m 2 D (fun z eps =>
      ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ i) i) =
      p 0 * p 1 * ψ 0 * ψ 1 := by
  have hh := density_packet_product_count_selector (Finset.univ : Finset (Fin 2))
    a b ha hab m 2 D (by omega) (by omega) (by simpa using hD)
    (by simpa using hm) p (fun i _ => ψ i)
  have hpow : (Finset.univ : Finset (Fin 2)).powersetCard 2 = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin 2))
  simpa only [Finset.card_univ, Fintype.card_fin, ite_true, hpow, Finset.sum_singleton,
    Fin.prod_univ_two, densitySeparatedSym_identical_columns, mul_assoc] using hh

theorem ordinaryPairDensity_action_small_count {n : ℕ} (hn : n < 2)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m D : ℕ) (hD : 1 ≤ D)
    (p : Fin n → ℝ) (ψ : Fin n → ℝ) :
    densityPacketAction a b m 2 D (fun z eps =>
      ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ i) i) = 0 := by
  exact density_packet_product_zero_of_small_count Finset.univ a b ha hab m 2 D
    (by omega) hD (by simpa using (show n ≤ D by omega)) (by simpa using hn) p _

theorem finePairDensity_action_small_count {n : ℕ} (hn : n < 2)
    (a b : ℝ) (M : ℕ) (p ψ : Fin n → ℝ) :
    (∫ᵛ e, (∏ i, finePairDensityReset a b e.1 e.2 p ψ i)
      ∂<•finePairDensitySignedRule a b M) = 0 := by
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · simpa only [Finset.univ_eq_empty, Finset.prod_empty] using
      finePairDensitySignedRule_mass_zero a b M
  · simpa only [Fin.prod_univ_one] using
      finePairDensitySignedRule_linear_zero a b M p ψ (0 : Fin 1)

theorem finePairTime_response_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) [NeZero d] (lo hi : ℝ) (hlo : 0 ≤ lo)
    (u v : Covariate d) (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d)
    (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    (∫ e, finePairTimeFieldValue e u * finePairTimeFieldValue e v *
      responseMatrixAction q C (finePairTimeMatrix d A e) c Φ
      ∂finePairTimeFieldMeasure d lo hi) =
      (∫ T in Icc lo hi, T * Real.exp (-T * euclideanNorm (fun r => u r - v r))) *
        responseMatrixAction q C A c Φ := by
  change (∫ e, finePairTimeFieldValue e u * finePairTimeFieldValue e v *
    responseMatrixAction q C (fun i j => e.1 * A i j) c Φ
    ∂finePairTimeFieldMeasure d lo hi) = _
  simp_rw [responseMatrixAction_scalar_matrix]
  have he (e : ℝ × FinePairFieldMark d) : finePairTimeFieldValue e u * finePairTimeFieldValue e v *
      (e.1 * responseMatrixAction q C A c Φ) =
      (e.1 * (finePairTimeFieldValue e u * finePairTimeFieldValue e v)) *
        responseMatrixAction q C A c Φ := by ring
  simp_rw [he]
  rw [integral_mul_const, finePairTimeFieldValue_weighted_covariance d lo hi hlo u v hu hv]

theorem pairLaplaceKernel_Icc {N : ℝ} (hN : 0 ≤ N) (r : ℝ) :
    (∫ T in Icc 0 N, T * Real.exp (-(T*r))) = pairLaplaceKernel N r := by
  unfold pairLaplaceKernel
  rw [intervalIntegral.integral_of_le hN, integral_Icc_eq_integral_Ioc]

theorem pairLaplaceKernel_split {T0 N : ℝ} (hT0 : 0 ≤ T0) (hN : T0 ≤ N) (r : ℝ) :
    (∫ T in Icc 0 T0, T * Real.exp (-(T*r))) +
      (∫ T in Icc T0 N, T * Real.exp (-(T*r))) = pairLaplaceKernel N r := by
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hT0, ← intervalIntegral.integral_of_le hN]
  exact intervalIntegral.integral_add_adjacent_intervals
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)

section SignedPacket
variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]

def finePairResponseAtomBound (q : ℕ) (C : ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) : ℝ :=
  ∑ h : HighResponseMarkIndex ι q,
    |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)|

theorem finePairResponseAtomBound_le (q : ℕ) (C : ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ)
    (h : HighResponseMarkIndex ι q) :
    |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤
      finePairResponseAtomBound q C c Φ := by
  unfold finePairResponseAtomBound
  exact Finset.single_le_sum
    (f := fun h : HighResponseMarkIndex ι q =>
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ h)

theorem ordinaryPairReset_measurable {n : ℕ} (a b : ℝ) (p : Fin n → ℝ)
    (ψ : Z → Fin n → ℝ) (hψ : ∀ i, Measurable (fun ζ => ψ ζ i))
    (z : ℝ) (eps : Fin 2 → ℝ) (i : Fin n) :
    Measurable (fun ζ => localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i) := by
  unfold localDensityReset
  exact measurable_const.add ((Finset.measurable_fun_sum _
    (fun l _ => (hψ i).const_mul (eps l))).const_mul _)

theorem ordinaryPairReset_atom_abs_le {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m D : ℕ) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b)
    (ψ : Fin n → ℝ) (hψ : ∀ i, |ψ i| ≤ 1)
    (e : HighDensityMarkIndex m 2 D) (i : Fin n) :
    |localDensityReset a b 2 (densityPacketAtom a b m 2 D e).1
      (densityPacketAtom a b m 2 D e).2 p (fun i _ => ψ i) i| ≤ b := by
  have hz := densityPacketAtom_mem a b hab.le m 2 D e
  have hh := localDensityReset_mem_interval a b ha hab 2 (by omega) _ hz.1 _ hz.2 p
    (fun i _ => ψ i) i
    (hp i) (fun _ => hψ i)
  rw [abs_of_nonneg (ha.le.trans hh.1)]
  exact hh.2

theorem ordinaryPairPacket_pair_action (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m D q : ℕ) (hm : 2 ≤ m) (hD : 2 ≤ D)
    (C : ℝ) (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ)
    (p : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin 2 → ℝ)
    (hmψ : ∀ i, Measurable (fun ζ => ψ ζ i)) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, highPacketObservable a b m 2 D q C c
      (fun ζ z eps => ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i) Φ e
      ∂<•highPacketSignedMeasure σ a b m 2 D q C A) =
      (p 0 * p 1) * (∫ ζ, ψ ζ 0 * ψ ζ 1 * responseMatrixAction q C (A ζ) c Φ ∂σ) := by
  rw [highPacketSignedMeasure_factor_integral σ a b m 2 D q C A hA hcost c _
    (fun z eps => Finset.measurable_fun_prod _ (fun i _ => ordinaryPairReset_measurable a b p ψ hmψ z eps i))
    (b^2) (by positivity)
    (fun ζ e => finite_density_product_abs_bound _ b (ha.trans hab).le
      (ordinaryPairReset_atom_abs_le a b ha hab m D p hp (ψ ζ) (hbψ ζ) e))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
  unfold highSeparatedPacketAction
  simp_rw [densityPacketAction_mul_right, ordinaryPairDensity_action a b ha hab m D hm hD]
  have he (ζ : Z) : p 0 * p 1 * ψ ζ 0 * ψ ζ 1 * responseMatrixAction q C (A ζ) c Φ =
      (p 0 * p 1) * (ψ ζ 0 * ψ ζ 1 * responseMatrixAction q C (A ζ) c Φ) := by ring
  simp_rw [he]
  exact integral_const_mul _ _

theorem ordinaryPairPacket_small_count {n : ℕ} (hn : n < 2)
    (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m D q : ℕ) (hD : 1 ≤ D) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin n → ℝ)
    (hmψ : ∀ i, Measurable (fun ζ => ψ ζ i)) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, highPacketObservable a b m 2 D q C c
      (fun ζ z eps => ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i) Φ e
      ∂<•highPacketSignedMeasure σ a b m 2 D q C A) = 0 := by
  rw [highPacketSignedMeasure_factor_integral σ a b m 2 D q C A hA hcost c _
    (fun z eps => Finset.measurable_fun_prod _ (fun i _ => ordinaryPairReset_measurable a b p ψ hmψ z eps i))
    (b^n) (pow_nonneg (ha.trans hab).le n)
    (fun ζ e => finite_density_product_abs_bound _ b (ha.trans hab).le
      (ordinaryPairReset_atom_abs_le a b ha hab m D p hp (ψ ζ) (hbψ ζ) e))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
  unfold highSeparatedPacketAction
  simp_rw [densityPacketAction_mul_right, ordinaryPairDensity_action_small_count hn a b ha hab m D hD,
    zero_mul]
  exact integral_zero _ _

theorem finePairPacket_small_count {n : ℕ} (hn : n < 2)
    (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (M q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin n → ℝ)
    (hmψ : ∀ i, Measurable (fun ζ => ψ ζ i)) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, finePairPacketObservable a b M q C c
      (fun ζ z eps => ∏ i, finePairDensityReset a b z eps p (ψ ζ) i) Φ e
      ∂<•finePairPacketSignedMeasure σ a b M q C A) = 0 := by
  have hm (z eps : ℝ) (i : Fin n) :
      Measurable (fun ζ => finePairDensityReset a b z eps p (ψ ζ) i) := by
    unfold finePairDensityReset
    exact measurable_const.add ((hmψ i).const_mul _)
  rw [finePairPacketSignedMeasure_factor_integral σ a b M q C A hA hcost c _
    (fun z eps => Finset.measurable_fun_prod _ (fun i _ => hm z eps i))
    (b^n) (pow_nonneg (ha.trans hab).le n) (fun ζ e => finite_density_product_abs_bound _ b (ha.trans hab).le
      (fun i => finePairFieldReset_abs_le a b ha hab M p hp ψ hbψ (ζ,e) i))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
  simp_rw [finePairDensity_action_small_count hn a b M, zero_mul]
  exact integral_zero _ _

end SignedPacket

theorem responseMatrixAction_matrix_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) (C : ℝ) (A B : ι → ι → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C (fun i j => A i j + B i j) c Φ =
      responseMatrixAction q C A c Φ + responseMatrixAction q C B c Φ := by
  simp only [responseMatrixAction_entry_sum, add_mul, Finset.sum_add_distrib]

section ActualRows
variable {d F : ℕ} [NeZero d]

def finePairUnitFirstAction {n : ℕ} (ad bd : ℝ) (D q : ℕ) (C : ℝ)
    (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, highPacketObservable ad bd D 2 D q C c
    (fun _ z eps => ∏ i, localDensityReset ad bd 2 z eps p (fun _ _ => 1) i) Φ e
    ∂<•highPacketSignedMeasure (Measure.dirac ()) ad bd D 2 D q C (fun _ => finePairUnitMatrix d F)

def finePairCoarseFirstAction {n : ℕ} (ad bd T0 : ℝ) (D q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, highPacketObservable ad bd D 2 D q C c
    (fun ζ z eps => ∏ i, localDensityReset ad bd 2 z eps p
      (fun i _ => finePairTimeFieldValue ζ (U i)) i) Φ e
    ∂<•highPacketSignedMeasure (finePairTimeFieldMeasure d 0 T0) ad bd D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d F))

def finePairFineFirstAction {n : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, finePairPacketObservable ad bd M q C c
    (fun ζ z eps => ∏ i, finePairDensityReset ad bd z eps p
      (fun i => finePairTimeFieldValue ζ (U i)) i) Φ e
    ∂<•finePairPacketSignedMeasure (finePairTimeFieldMeasure d T0 N) ad bd M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d F))

def finePairThreeRowFirstAction {n : ℕ} (ad bd T0 N : ℝ) (D M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  finePairUnitFirstAction ad bd D q C p c Φ + finePairCoarseFirstAction ad bd T0 D q C U p c Φ +
    finePairFineFirstAction ad bd T0 N M q C U p c Φ

theorem finePairUnitFirstAction_pair (ad bd : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D q : ℕ) (hD : 2 ≤ D) (C : ℝ) (p : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairUnitFirstAction ad bd D q C p c Φ =
      p 0 * p 1 * responseMatrixAction q C (finePairUnitMatrix d F) c Φ := by
  rw [finePairUnitFirstAction, ordinaryPairPacket_pair_action (Measure.dirac ()) ad bd ha hab D D q hD hD C
    (fun _ => finePairUnitMatrix d F) (fun _ _ => measurable_const)
    (integrable_const _) c p hp (fun _ _ => 1) (fun _ => measurable_const) (by intro _ _; norm_num)]
  simp

theorem finePairCoarseFirstAction_pair (ad bd T0 : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D q : ℕ) (hD : 2 ≤ D) (C : ℝ) (U : Fin 2 → Covariate d)
    (hU : ∀ i, U i ∈ hyperplaneCube d) (p : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairCoarseFirstAction ad bd T0 D q C U p c Φ = (p 0 * p 1) *
      ((∫ T in Icc 0 T0, T * Real.exp (-T * euclideanNorm (fun r => U 0 r - U 1 r))) *
        responseMatrixAction q C (finePairDistanceMatrix d F) c Φ) := by
  rw [finePairCoarseFirstAction, ordinaryPairPacket_pair_action _ ad bd ha hab D D q hD hD C
    _ (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T0 _)
    c p hp (fun ζ i => finePairTimeFieldValue ζ (U i))
    (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
    (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le)]
  rw [finePairTime_response_integral d 0 T0 (le_refl 0) (U 0) (U 1) (hU 0) (hU 1)]

theorem finePairFineFirstAction_pair (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (hT0 : 0 ≤ T0) (M q : ℕ) (hM : 2 ≤ M) (C : ℝ) (U : Fin 2 → Covariate d)
    (hU : ∀ i, U i ∈ hyperplaneCube d) (p : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairFineFirstAction ad bd T0 N M q C U p c Φ = (p 0 * p 1) *
      ((∫ T in Icc T0 N, T * Real.exp (-T * euclideanNorm (fun r => U 0 r - U 1 r))) *
        responseMatrixAction q C (finePairDistanceMatrix d F) c Φ) := by
  unfold finePairFineFirstAction
  simp only [Fin.prod_univ_two]
  rw [finePairPacketSignedMeasure_pair_action _ ad bd ha hab M q hM C
    _ (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T0 N _)
    c p hp (fun ζ i => finePairTimeFieldValue ζ (U i))
    (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
    (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le) 0 1
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
  rw [finePairTime_response_integral d T0 N hT0 (U 0) (U 1) (hU 0) (hU 1)]

theorem finePairThreeRowFirstAction_pair (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (hT0 : 0 ≤ T0) (hN : T0 ≤ N) (D M q : ℕ) (hD : 2 ≤ D) (hM : 2 ≤ M)
    (C : ℝ) (U : Fin 2 → Covariate d) (hU : ∀ i, U i ∈ hyperplaneCube d)
    (p : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairThreeRowFirstAction ad bd T0 N D M q C U p c Φ = (p 0 * p 1) *
      responseMatrixAction q C
        (finePairCombinedMatrix d F (pairLaplaceKernel N (exactEuclideanDistance (U 0) (U 1)))) c Φ := by
  rw [finePairThreeRowFirstAction, finePairUnitFirstAction_pair ad bd ha hab D q hD C p hp,
    finePairCoarseFirstAction_pair ad bd T0 ha hab D q hD C U hU p hp,
    finePairFineFirstAction_pair ad bd T0 N ha hab hT0 M q hM C U hU p hp]
  change _ = (p 0 * p 1) * responseMatrixAction q C
    (fun i j => finePairUnitMatrix d F i j +
      pairLaplaceKernel N (exactEuclideanDistance (U 0) (U 1)) * finePairDistanceMatrix d F i j) c Φ
  rw [responseMatrixAction_matrix_add, responseMatrixAction_scalar_matrix]
  rw [exactEuclideanDistance_eq_euclideanNorm]
  have hsplit := pairLaplaceKernel_split hT0 hN (euclideanNorm (fun r => U 0 r - U 1 r))
  have he : (fun T : ℝ => T * Real.exp (-T * euclideanNorm (fun r => U 0 r - U 1 r))) =
      (fun T => T * Real.exp (-(T * euclideanNorm (fun r => U 0 r - U 1 r)))) := by
    funext T
    congr 2
    ring
  rw [he, ← hsplit]
  ring

theorem finePairThreeRow_count_two_numerator (hF : 3 ≤ F)
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (hT0 : 0 ≤ T0) (hN : T0 ≤ N)
    (D M q : ℕ) (hD : 2 ≤ D) (hM : 2 ≤ M) (hq : 2 ≤ q)
    (C a V η : ℝ) (hC : C ≠ 0)
    (U : Fin 2 → Covariate d) (hU : ∀ i, U i ∈ hyperplaneCube d)
    (p : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (g w : Fin 2 → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin 2 → Fin 3) :
    finePairThreeRowFirstAction ad bd T0 N D M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
      η^2 * (p 0 * p 1) * ∑ i, (w i)^2 *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i =
      η^2 * w 0 * w 1 * p 0 * p 1 *
        ((1 + N * exactEuclideanDistance (U 0) (U 1)) *
          Real.exp (-(N * exactEuclideanDistance (U 0) (U 1)))) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 0) (y 0) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 1) (y 1) := by
  rw [finePairThreeRowFirstAction_pair ad bd T0 N ha hab hT0 hN D M q hD hM C U hU p hp,
    finePairResponseCountTwo_numerator hF q hq C a V η _ hC U p g w c y]
  have hr : 0 ≤ exactEuclideanDistance (U 0) (U 1) := Real.sqrt_nonneg _
  have hsq : (exactEuclideanDistance (U 0) (U 1))^2 = spatialSquaredDistance (U 0) (U 1) :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [← hsq, mul_comm (pairLaplaceKernel _ _), pairLaplaceKernel_defect N _ hr]

theorem finePairThreeRowFirstAction_small_count {n : ℕ} (hn : n < 2)
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (D M q : ℕ) (hD : 1 ≤ D)
    (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairThreeRowFirstAction ad bd T0 N D M q C U p c Φ = 0 := by
  have hunit : finePairUnitFirstAction ad bd D q C p c Φ = 0 := by
    exact ordinaryPairPacket_small_count hn (Measure.dirac ()) ad bd ha hab D D q hD C
      (fun _ => finePairUnitMatrix d F) (fun _ _ => measurable_const) (integrable_const _) c p hp
      (fun _ _ => 1) (fun _ => measurable_const) (by intro _ _; norm_num) Φ
  have hcoarse : finePairCoarseFirstAction ad bd T0 D q C U p c Φ = 0 := by
    exact ordinaryPairPacket_small_count hn _ ad bd ha hab D D q hD C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T0 _) c p hp
      (fun ζ i => finePairTimeFieldValue ζ (U i))
      (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
      (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le) Φ
  have hfine : finePairFineFirstAction ad bd T0 N M q C U p c Φ = 0 := by
    exact finePairPacket_small_count hn _ ad bd ha hab M q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T0 N _) c p hp
      (fun ζ i => finePairTimeFieldValue ζ (U i))
      (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
      (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le) Φ
  simp only [finePairThreeRowFirstAction, hunit, hcoarse, hfine, add_zero]

end ActualRows

end NearlyMinimax
