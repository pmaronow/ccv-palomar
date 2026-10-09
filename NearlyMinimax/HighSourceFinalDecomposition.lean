module

public import NearlyMinimax.HigherBandRawCollapse
public import NearlyMinimax.HighSourceHigherCounts


@[expose] public section

/-! The complete physical source, with its single heat correction, is
exactly the matched cardinal defect plus the genuine exterior aliases
and the fine-field action.  This also covers positive target scales
below one: their actual scale domain and covariance matrix are empty. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
attribute [local instance] Classical.propDecidable

theorem integrated_cardinal_weight_below_one_eq_zero {d n : ℕ}
    (lam T : ℝ) (hT : 0 < T) (hT1 : T < 1)
    (U : Fin n → Covariate d) (i : Fin n) :
    integratedCardinalWeight lam T U i = 0 := by
  unfold integratedCardinalWeight spatialScaleMeasure
  rw [spatial_scale_domain_empty_below_one i hT hT1,
    Measure.restrict_empty, integral_zero_measure]

theorem integrated_cardinal_matrix_diagonal_positive {d n D : ℕ}
    (hn : n ≤ D) (lam T : ℝ) (hT : 0 < T)
    (U : Fin n → Covariate d) (i l : Fin n) :
    spatialFrameCovariance (integratedCardinalMatrix (D := D) lam T U)
      (fun j => highFrameFeature (U j)) i l =
      if i = l then integratedCardinalWeight lam T U i else 0 := by
  by_cases hT1 : 1 ≤ T
  · exact integrated_cardinal_matrix_diagonal hn lam T hT1 U i l
  · have hlt : T < 1 := not_le.mp hT1
    have hm (β β' : HighFrameIndex d D) :
        integratedCardinalMatrix lam T U β β' = 0 :=
      integrated_cardinal_matrix_below_one_eq_zero i lam hT hlt U β β'
    rw [integrated_cardinal_weight_below_one_eq_zero lam T hT hlt U i]
    simp [spatialFrameCovariance, hm]

theorem integrated_cardinal_response_heat_positive {d n D : ℕ}
    (hn : n ≤ D) (q : ℕ) (C a V eta lam T : ℝ) (hC : C ≠ 0)
    (hT : 0 < T) (U : Fin n → Covariate d) (g w : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    responseMatrixAction q C (integratedCardinalMatrix lam T U) c
      (fun c => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) c y) =
      eta^2 * ∑ i, (w i)^2 * integratedCardinalWeight lam T U i *
        highResponseVarianceTerm a V eta g w (fun i => highFrameFeature (U i)) c y i +
      highResponseDefect q C a V eta (integratedCardinalMatrix lam T U) g w
        (fun i => highFrameFeature (U i)) c y := by
  apply high_response_matrix_heat_with_defect q C a V eta _ hC
  · exact integrated_cardinal_matrix_symmetric lam T U
  · exact integrated_cardinal_matrix_diagonal_positive hn lam T hT U

/-- Actual all-row source cancellation for every ordinary count up to
the degree cutoff. No packet-action or source decomposition identity
is assumed. The displayed heat correction occurs only once. -/
theorem completeSourceRawNumerator_refined_decomposition {d n : ℕ} [NeZero d]
    (ad bd lam ell N mu : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (hlam : 0 ≤ lam) (hell : 1 ≤ ell) (D M q : ℕ)
    (hn : 3 ≤ n) (hnD : n ≤ D)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2),
      ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (C a V eta : ℝ) (hC : C ≠ 0) (U : Fin n → Covariate d)
    (hU : ∀ i j, |U i j| ≤ 2) (p g w : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Icc ad bd) (c : HighFrameIndex d D → ℝ)
    (y : Fin n → Fin 3) :
    completeSourceRawNumerator ad bd lam ell N mu D M q C a V eta U p g w c y =
      eta^2 * (∏ i, p i) * ∑ i, (w i)^2 *
        (integratedCardinalWeight lam (higherBandTargetScale d n N mu) U i - 1) *
        highResponseVarianceTerm a V eta g w (fun i => highFrameFeature (U i)) c y i +
      (∏ i, p i) * highResponseDefect q C a V eta
        (integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U) g w
        (fun i => highFrameFeature (U i)) c y +
      (if M<n then ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ell N mu)
        ad bd lam ell (fun r => higherBandTargetScale d r N mu) M q C a V eta U p g w c y else 0) +
      finePairPairAliasAction ad bd ell N M q C U p c
        (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) +
      finePairEvenFieldAction ad bd ell N M q C U p c
        (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) := by
  let j : Fin (D-2) := ⟨n-3, by omega⟩
  have hj : j.val+3 = n := by dsimp [j]; omega
  have htarget : 0 < higherBandTargetScale d n N mu := by
    simpa only [hj] using hnu j
  rw [completeSourceRawNumerator_higher ad bd lam ell N mu ha hab D M q hn hnD C a V eta U p g w hp c y,
    higherBandFamilyFirstAction_matched_and_full_fine_alias ad bd lam ell N mu ha hab hlam hell
      D M q hn hnD hnu hFine C a V eta U hU p g w hp c y,
    integrated_cardinal_response_heat_positive hnD q C a V eta lam _ hC htarget U g w c y]
  have hs : (∑ i, (w i)^2 *
      (integratedCardinalWeight lam (higherBandTargetScale d n N mu) U i - 1) *
      highResponseVarianceTerm a V eta g w (fun i => highFrameFeature (U i)) c y i) =
      (∑ i, (w i)^2 * integratedCardinalWeight lam (higherBandTargetScale d n N mu) U i *
        highResponseVarianceTerm a V eta g w (fun i => highFrameFeature (U i)) c y i) -
      ∑ i, (w i)^2 * highResponseVarianceTerm a V eta g w (fun i => highFrameFeature (U i)) c y i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

end NearlyMinimax
