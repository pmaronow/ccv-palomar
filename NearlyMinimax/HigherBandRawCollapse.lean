module

public import NearlyMinimax.HigherBandFamilyCollapse


@[expose] public section

/-! Exact finite-target reindexing and full-response ordinary-fine-alias
identification for the genuine selected higher family. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
attribute [local instance] Classical.propDecidable

theorem higherBand_alias_index_sum_eq (d D n : ℕ) (ell N mu : ℝ) (A : ℕ → ℝ) :
    (∑ j : Fin (D-2), if j.val+3 < n then
      (if ell < higherBandTargetScale d (j.val+3) N mu then A (j.val+3) else 0) else 0) =
      ∑ r ∈ (ordinaryFineAliasTargetSet d D ell N mu).filter (fun r => r<n), A r := by
  classical
  have hi (j : Fin (D-2)) :
      (if j.val+3 < n then (if ell < higherBandTargetScale d (j.val+3) N mu then A (j.val+3) else 0) else 0) =
      if j.val+3 < n ∧ ell < higherBandTargetScale d (j.val+3) N mu then A (j.val+3) else 0 := by
    by_cases hn : j.val+3 < n <;> by_cases ha : ell < higherBandTargetScale d (j.val+3) N mu <;> simp [hn,ha]
  simp_rw [hi]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => j.val+3)
  · intro j hj
    have hg := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by have hh := j.isLt; omega), by omega, hg.2⟩
    · exact hg.1
  · intro j hj j' hj' he
    apply Fin.ext
    omega
  · intro r hr
    have hr' := Finset.mem_filter.mp hr
    have hI := Finset.mem_filter.mp hr'.1
    have hrd := Finset.mem_range.mp hI.1
    let j : Fin (D-2) := ⟨r-3, by omega⟩
    have hj : j.val+3 = r := by dsimp [j]; omega
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, by simpa only [hj] using And.intro hr'.2 hI.2.2⟩, hj⟩
  · intro j hj
    rfl

theorem higherBandFine_below_eq_alias_family {d n : ℕ}
    (ad bd lam ell N mu : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam) (hell : 1 ≤ ell)
    (D M q : ℕ) (hD : 1 ≤ D) (hnD : n ≤ D) (C a V eta : ℝ)
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    (∑ j : Fin (D-2), if j.val+3 < n then
      higherBandFineFirstAction ad bd lam ell N mu (j.val+3) M D q C U p c
        (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) else 0) =
      ordinaryFineAliasFamilyRawAction ((ordinaryFineAliasTargetSet d D ell N mu).filter (fun r => r<n))
        ad bd lam ell (fun r => higherBandTargetScale d r N mu) M q C a V eta U p g w c y := by
  unfold higherBandFineFirstAction
  have he : (∑ j : Fin (D-2), if j.val+3 < n then
      (if ell < higherBandTargetScale d (j.val+3) N mu then
        higherBandFirstAction ad bd lam ell (higherBandTargetScale d (j.val+3) N mu) (j.val+3) M D q C true U p c
          (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) else 0) else 0) =
      ∑ j : Fin (D-2), if j.val+3 < n then
        (if ell < higherBandTargetScale d (j.val+3) N mu then
          ordinaryFineAliasRawAction ad bd lam ell (higherBandTargetScale d (j.val+3) N mu)
            M (j.val+3) q C a V eta U p g w c y else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hn ha'
    · exact higherBandFirstAction_fine_eq_aliasRawAction ad bd lam ell _ ha hab hlam (by linarith)
        (hell.trans ha'.le) (j.val+3) M D q (by omega) hD hnD C a V eta U hU p g w hp c y
    · rfl
    · rfl
  rw [he]
  exact higherBand_alias_index_sum_eq d D n ell N mu
    (fun r => ordinaryFineAliasRawAction ad bd lam ell (higherBandTargetScale d r N mu) M r q C a V eta U p g w c y)

theorem higherBandFamilyFirstAction_matched_and_alias_raw {d n : ℕ}
    (ad bd lam ell N mu : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam) (hell : 1 ≤ ell)
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (C a V eta : ℝ) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    higherBandFamilyFirstAction ad bd lam ell N mu D M q C U p c
      (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) =
      (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U) c
        (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) +
      ordinaryFineAliasFamilyRawAction ((ordinaryFineAliasTargetSet d D ell N mu).filter (fun r => r<n))
        ad bd lam ell (fun r => higherBandTargetScale d r N mu) M q C a V eta U p g w c y := by
  rw [higherBandFamilyFirstAction_matched_and_fine_below ad bd lam ell N mu ha hab hlam hell D M q hn hnD hnu hFine C U hU p hp c,
    higherBandFine_below_eq_alias_family ad bd lam ell N mu ha hab hlam hell D M q (by omega) hnD C a V eta U hU p g w hp c y]

theorem ordinaryFineAliasFamilyRawAction_below_eq_zero {d n F : ℕ}
    (ad bd lam ell N mu : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D M q : ℕ) (hnM : n ≤ M) (C a V eta : ℝ)
    (U : Fin n → Covariate d) (p g w : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (y : Fin n → Fin 3) :
    ordinaryFineAliasFamilyRawAction ((ordinaryFineAliasTargetSet d D ell N mu).filter (fun r => r<n))
      ad bd lam ell (fun r => higherBandTargetScale d r N mu) M q C a V eta U p g w c y = 0 := by
  unfold ordinaryFineAliasFamilyRawAction
  apply Finset.sum_eq_zero
  intro r hr
  have hfilter := Finset.mem_filter.mp hr
  have htarget := Finset.mem_filter.mp hfilter.1
  have hr1 : 1 ≤ r := by have hh := htarget.2.1; omega
  have hnr : r < n := hfilter.2
  unfold ordinaryFineAliasRawAction
  rw [densityCountCoefficient_exact ad bd ha hab M r n hr1 hnr.le hnM, if_neg (by omega : n ≠ r), zero_mul]

theorem ordinaryFineAliasTargetSet_below_eq (d D n M : ℕ) (ell N mu : ℝ) (hMn : M < n)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M) :
    (ordinaryFineAliasTargetSet d D ell N mu).filter (fun r => r<n) = ordinaryFineAliasTargetSet d D ell N mu := by
  apply Finset.filter_eq_self.mpr
  intro r hr
  have htarget := Finset.mem_filter.mp hr
  have hrd := Finset.mem_range.mp htarget.1
  let j : Fin (D-2) := ⟨r-3, by omega⟩
  have hj : j.val+3 = r := by dsimp [j]; omega
  have hactive : ell < higherBandTargetScale d (j.val+3) N mu := by simpa only [hj] using htarget.2.2
  have hm := hFine j hactive
  rw [hj] at hm
  omega

/-- Before M the ordinary fine aliases cancel exactly. Beyond M every
active fine target is strictly below the observed count, and its actual
signed action is precisely the full alias family used by the energy theorem. -/
theorem higherBandFamilyFirstAction_matched_and_full_fine_alias {d n : ℕ}
    (ad bd lam ell N mu : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam) (hell : 1 ≤ ell)
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (C a V eta : ℝ) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    higherBandFamilyFirstAction ad bd lam ell N mu D M q C U p c
      (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) =
      (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U) c
        (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) +
      (if M<n then ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ell N mu)
        ad bd lam ell (fun r => higherBandTargetScale d r N mu) M q C a V eta U p g w c y else 0) := by
  rw [higherBandFamilyFirstAction_matched_and_alias_raw ad bd lam ell N mu ha hab hlam hell D M q hn hnD
    hnu hFine C a V eta U hU p g w hp c y]
  by_cases hnM : M<n
  · rw [ite_eq_left hnM, ordinaryFineAliasTargetSet_below_eq d D n M ell N mu hnM hFine]
  · rw [ite_eq_right hnM, ordinaryFineAliasFamilyRawAction_below_eq_zero ad bd lam ell N mu ha hab D M q
      (le_of_not_gt hnM) C a V eta U p g w c y]

end NearlyMinimax
