module

public import NearlyMinimax.HighSourceRawDecomposition
public import NearlyMinimax.OrdinaryFineAliasSpatialEnergy


@[expose] public section

/-! Exact identification of every genuine ordinary fine signed packet
with the spatial all-count alias action used by the energy bounds. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem higherBandFirstAction_fine_eq_aliasRawAction {d n : ℕ}
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    (hL : 0 < L) (hT : 1 ≤ T) (r M D q : ℕ) (hr : 2 ≤ r)
    (hD : 1 ≤ D) (hnD : n ≤ D) (C a V η : ℝ)
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    higherBandFirstAction ad bd lam L T r M D q C true U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) =
      ordinaryFineAliasRawAction ad bd lam L T M r q C a V η U p g w c y := by
  rw [higherBandFirstAction_actual_count_expansion ad bd lam L T ha hab hlam hL hT
    r M D q hr hD hnD C true U hU p hp c]
  simp only [ordinaryFineAliasRawAction, higherBandActualMatrix, ite_true]

theorem higherBandFamilyFineFirstAction_eq_aliasRawAction {d n : ℕ}
    (ad bd lam ℓ N μ : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    (hℓ : 0 < ℓ) (D M q : ℕ) (hD : 1 ≤ D) (hnD : n ≤ D) (C a V η : ℝ)
    (i : HigherBandFamilyIndex d D M q ad bd C lam ℓ N μ) (hi : i.val.2 = true)
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    higherBandFirstAction ad bd lam ℓ (higherBandFamilyUpper d ℓ N μ i.val)
      (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q C i.val.2 U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) =
      ordinaryFineAliasRawAction ad bd lam ℓ
        (higherBandTargetScale d (higherBandFamilyTarget i.val) N μ)
        M (higherBandFamilyTarget i.val) q C a V η U p g w c y := by
  have hr := (higherBandFamily_target_bounds d D M q ad bd C lam ℓ N μ i).1
  have hT := i.property.1
  simp only [higherBandFamilyUpper, higherBandFamilyGuardDegree, hi, ite_true] at hT ⊢
  exact higherBandFirstAction_fine_eq_aliasRawAction ad bd lam ℓ _ ha hab hlam hℓ hT
    _ M D q (by omega) hD hnD C a V η U hU p g w hp c y

end NearlyMinimax
