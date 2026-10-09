module

public import NearlyMinimax.HighSeparatedScoreBounds
public import NearlyMinimax.CardinalSeparatedKernel


@[expose] public section

/-! The singleton ordinary row, instantiated with the genuine positive
separated representation of the spatial cardinal covariance. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem integrated_cardinal_weight_singleton {d : ℕ}
    (lam T : ℝ) (hT : 1 ≤ T) (U : Fin 1 → Covariate d) (i : Fin 1) :
    integratedCardinalWeight lam T U i = 1 := by
  have hi (j : Fin 1) : j = i := Subsingleton.elim _ _
  letI : IsEmpty (SpatialScaleIndex i) := ⟨fun j => j.2 (hi j.1)⟩
  have herase : (Finset.univ : Finset (Fin 1)).erase i = ∅ := by
    ext j
    simp [hi j]
  have hdomain : spatialScaleDomain i T = univ := by
    ext t
    simp only [spatialScaleDomain, spatialScaleLogSum, Fintype.sum_empty,
      Set.mem_inter_iff, Set.mem_Ici, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨fun j => isEmptyElim j, mul_nonneg (by norm_num) (Real.log_nonneg hT)⟩
  unfold integratedCardinalWeight spatialCardinalWeight spatialScaleMeasure
  simp only [herase, Finset.prod_empty, hdomain, Measure.restrict_univ]
  rw [Measure.volume_pi_eq_dirac]
  simp

def highCardinalDensityReset {d n : ℕ} (ad bd lam : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (ζ : CardinalSeparatedMark d n) (z : ℝ) (ε : Fin n → ℝ) (i : Fin n) : ℝ :=
  localDensityReset ad bd n z ε p (fun i l => cardinalSeparatedFactor lam ζ l (U i)) i

def highCardinalXiScore {d n F : ℕ} (ad bd lam T : ℝ) (m D q : ℕ)
    (C a V η : ℝ) (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) : ℝ :=
  highSeparatedXiScore (cardinalSeparatedMeasure d n T) ad bd m n D q C a V η
    (cardinalSeparatedAmplitude lam) p (highCardinalDensityReset ad bd lam U p)
    g w (fun i => highFrameFeature (U i)) c y

theorem cardinalSeparatedSubsetMatrix_univ {d n F : ℕ} (lam : ℝ) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2) :
    separatedSubsetMatrix (cardinalSeparatedMeasure d n T) n
      (fun ζ i l => cardinalSeparatedFactor lam ζ l (U i))
      (cardinalSeparatedAmplitude (D := F) lam) Finset.univ =
        integratedCardinalMatrix lam T U := by
  funext β β'
  unfold separatedSubsetMatrix
  simp_rw [cardinal_density_separated_sym_eq]
  exact (integrated_cardinal_symmetric_separated_exact lam hlam hT U hU β β').symm

/-- Exact selector for the genuine cardinal ordinary packet at its selected
count. Both the density selector and the matrix representation are evaluated. -/
theorem high_cardinal_packet_action_exact {d n F : ℕ}
    (ad bd lam : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hnD : n ≤ D)
    (C : ℝ) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    highSeparatedPacketAction (cardinalSeparatedMeasure d n T) ad bd m n D q C
      (cardinalSeparatedAmplitude lam) c
      (fun ζ z ε => ∏ i, highCardinalDensityReset ad bd lam U p ζ z ε i) Φ =
        (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam T U) c Φ := by
  have h := highSeparatedPacketAction_count_selector (cardinalSeparatedMeasure d n T) ad bd ha hab
    m n D q hn (hn.trans hnD) (Finset.univ : Finset (Fin n)) (by simpa using hnD)
    (by simpa using hnm) (by simp) p
    (fun ζ i l => cardinalSeparatedFactor lam ζ l (U i))
    (fun i l => cardinal_separated_factor_measurable lam l (U i))
    (fun ζ i l => cardinal_separated_factor_abs_le_one lam ζ l (U i) (hU i)) C
    (cardinalSeparatedAmplitude lam) (cardinal_separated_amplitude_measurable lam)
    (cardinal_separated_cost_integrable lam hT) c Φ
  simp only [highCardinalDensityReset] at ⊢
  rw [h]
  have hpow : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  simp only [Finset.card_univ, Fintype.card_fin, ite_true, hpow,
    Finset.sum_singleton, cardinalSeparatedSubsetMatrix_univ lam hlam hT U hU]

theorem high_cardinal_response_action_exact {d n F : ℕ}
    (ad bd lam : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hnD : n ≤ D)
    (C a V η : ℝ) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    highIntegratedResponseAction (cardinalSeparatedMeasure d n T) q C a V η
      (fun _ => densityPacketWeight ad bd m n D) (fun ζ _ => cardinalSeparatedAmplitude lam ζ)
      (fun ζ h => highCardinalDensityReset ad bd lam U p ζ
        (densityPacketAtom ad bd m n D h).1 (densityPacketAtom ad bd m n D h).2)
      g w (fun i => highFrameFeature (U i)) c y =
      (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam T U) c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) := by
  unfold highIntegratedResponseAction
  simp_rw [← densityPacketAction_eq_finite_response_action]
  exact high_cardinal_packet_action_exact ad bd lam ha hab hlam hT m D q hn hnm hnD
    C U hU p c _

/-- The actual ordinary signed score is exactly the cardinal alias term
plus the full response defect. No action or heat identity is assumed. -/
theorem highCardinalXiScore_eq_alias_defect {d n F : ℕ}
    (ad bd lam : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (C a V η : ℝ) (hC : C ≠ 0)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    highCardinalXiScore ad bd lam T m D q C a V η U p g w c y =
      (η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * (integratedCardinalWeight lam T U i - 1) *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i +
        (∏ i, p i) * highResponseDefect q C a V η (integratedCardinalMatrix lam T U) g w
          (fun i => highFrameFeature (U i)) c y) /
      ((∏ i, p i) * highResponseProduct a V η g w (fun i => highFrameFeature (U i)) c y) := by
  letI := cardinal_separated_measure_finite d n hT
  have hreset (z : ℝ) (ε : Fin n → ℝ) (i : Fin n) :
      Measurable (fun ζ : CardinalSeparatedMark d n => highCardinalDensityReset ad bd lam U p ζ z ε i) := by
    unfold highCardinalDensityReset localDensityReset
    exact (Finset.measurable_fun_sum _ (fun l _ =>
      (cardinal_separated_factor_measurable lam l (U i)).const_mul (ε l))).const_mul _ |>.const_add z
  have hbound (ζ : CardinalSeparatedMark d n) (h : HighDensityMarkIndex m n D) (i : Fin n) :
      |highCardinalDensityReset ad bd lam U p ζ (densityPacketAtom ad bd m n D h).1
        (densityPacketAtom ad bd m n D h).2 i| ≤ bd := by
    have hnode := densityPacketAtom_mem ad bd hab.le m n D h
    have hh := localDensityReset_mem_interval ad bd ha hab n hn _ hnode.1 _ hnode.2 p
      (fun i l => cardinalSeparatedFactor lam ζ l (U i)) i (hp i)
      (fun l => cardinal_separated_factor_abs_le_one lam ζ l (U i) (hU i))
    unfold highCardinalDensityReset
    rw [abs_of_nonneg (ha.le.trans hh.1)]
    exact hh.2
  unfold highCardinalXiScore
  rw [highSeparatedXiScore_eq_integrated (cardinalSeparatedMeasure d n T) ad bd m n D q C a V η bd
    (ha.trans hab).le (cardinalSeparatedAmplitude lam) p (highCardinalDensityReset ad bd lam U p)
    g w (fun i => highFrameFeature (U i)) c (cardinal_separated_amplitude_measurable lam)
    (cardinal_separated_cost_integrable lam hT) hreset hbound]
  unfold highIntegratedLocalScore
  rw [high_cardinal_response_action_exact ad bd lam ha hab hlam hT m D q hn hnm hnD
    C a V η U hU p g w c y,
    integrated_cardinal_response_heat hnF q C a V η lam T hC hT U g w c y]
  have hsum : (∑ i, (w i) ^ 2 * (integratedCardinalWeight lam T U i - 1) *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i) =
      (∑ i, (w i) ^ 2 * integratedCardinalWeight lam T U i *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i) -
      ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i := by
    simp_rw [mul_sub, sub_mul, mul_one]
    exact Finset.sum_sub_distrib
      (fun i => (w i) ^ 2 * integratedCardinalWeight lam T U i *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i)
      (fun i => (w i) ^ 2 * highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i)
  rw [hsum]
  ring

/-- Count one vanishes for the concrete ordinary cardinal signed row.
Its sole cardinal product and its zero-dimensional scale integral are both1. -/
theorem highCardinalXiScore_count_one_zero {d F : ℕ}
    (ad bd lam : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (hF : 1 ≤ F) (hq : 1 ≤ q) (C a V η : ℝ) (hC : C ≠ 0)
    (U : Fin 1 → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin 1 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (y : Fin 1 → Fin 3) :
    highCardinalXiScore ad bd lam T m D q C a V η U p g w c y = 0 := by
  rw [highCardinalXiScore_eq_alias_defect ad bd lam ha hab hlam hT m D q le_rfl hm hD hF
    C a V η hC U hU p g w hp c y]
  simp only [integrated_cardinal_weight_singleton lam T hT U,
    sub_self, mul_zero, zero_mul, Finset.sum_const_zero,
    high_response_defect_zero q hq, add_zero, zero_div]

end NearlyMinimax
