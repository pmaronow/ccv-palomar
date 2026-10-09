module

public import NearlyMinimax.HighSourceFinalDecomposition
public import NearlyMinimax.HighCardinalRawEnvelope


@[expose] public section

/-! The true matched source component is a genuine cardinal packet at
max(1,nu).  For counts at least two this does not alter the actual scale
integral; in particular no extra physical nu>=1 guard is needed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
attribute [local instance] Classical.propDecidable

theorem integrated_cardinal_weight_max_one {d n : ℕ} (hn : 2 ≤ n)
    (lam T : ℝ) (hT : 0 < T) (U : Fin n → Covariate d) (i : Fin n) :
    integratedCardinalWeight lam (max 1 T) U i = integratedCardinalWeight lam T U i := by
  have hm : integratedCardinalMatrix (D := n) lam (max 1 T) U =
      integratedCardinalMatrix lam T U := by
    funext β β'
    exact integrated_cardinal_matrix_max_one hn lam hT U β β'
  have hh := integrated_cardinal_matrix_diagonal (D := n) le_rfl lam (max 1 T)
    (le_max_left 1 T) U i i
  have hl := integrated_cardinal_matrix_diagonal_positive (D := n) le_rfl lam T hT U i i
  rw [hm] at hh
  simpa only [ite_true] using hh.symm.trans hl

/-- Full physical source, expressed using the actual matched cardinal
signed packet so that its proved spatial energy applies directly. -/
theorem completeSourceRawNumerator_eq_matched_packet_and_aliases {d n : ℕ} [NeZero d]
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
      highCardinalRawNumerator ad bd lam (max 1 (higherBandTargetScale d n N mu))
        D D q C a V eta U p g w c y +
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
  rw [completeSourceRawNumerator_refined_decomposition ad bd lam ell N mu ha hab hlam hell
    D M q hn hnD hnu hFine C a V eta hC U hU p g w hp c y,
    highCardinalRawNumerator_eq_alias_defect ad bd lam ha hab hlam
      (le_max_left 1 _) D D q (by omega) hnD hnD hnD C a V eta hC U hU p g w hp c y]
  have hm : integratedCardinalMatrix (D := D) lam (max 1 (higherBandTargetScale d n N mu)) U =
      integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U := by
    funext β β'
    exact integrated_cardinal_matrix_max_one (by omega) lam htarget U β β'
  simp_rw [integrated_cardinal_weight_max_one (by omega) lam _ htarget U, hm]

end NearlyMinimax
