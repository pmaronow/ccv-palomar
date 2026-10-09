module

public import NearlyMinimax.HighSourceRawDecomposition
public import NearlyMinimax.HigherBandOmissions


@[expose] public section

/-! Actual target-count evaluation and physical sum of the selected
higher signed rows. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def higherBandPhysicalFirstAction {d n : ℕ} (ad bd lam ell N mu : ℝ)
    (D M q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ)
    (i : Fin (D-2) × Bool) : ℝ :=
  if i.2 = true then
    if ell < higherBandTargetScale d (higherBandFamilyTarget i) N mu then
      higherBandFirstAction ad bd lam ell (higherBandFamilyUpper d ell N mu i)
        (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q C i.2 U p c Φ else 0
  else higherBandFirstAction ad bd lam ell (higherBandFamilyUpper d ell N mu i)
    (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q C i.2 U p c Φ

theorem higherBandFamilyFirstAction_eq_physical {d n : ℕ} (ad bd lam ell N mu : ℝ)
    (D M q : ℕ) (C : ℝ) (hell : 1 ≤ ell)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N mu)
    (hFine : ∀ j : Fin (D-2), ell < higherBandTargetScale d (j.val+3) N mu → j.val+3 ≤ M)
    (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    (∑ i : HigherBandFamilyIndex d D M q ad bd C lam ell N mu,
      higherBandFirstAction ad bd lam ell (higherBandFamilyUpper d ell N mu i.val)
        (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q C i.val.2 U p c Φ) =
      ∑ i : Fin (D-2) × Bool, higherBandPhysicalFirstAction ad bd lam ell N mu D M q C U p c Φ i := by
  let F := fun (i : Fin (D-2) × Bool)
      (e : HigherBandRowMark d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q i.2) =>
    highPacketObservable ad bd (higherBandFamilyGuardDegree M i) (higherBandFamilyTarget i) D q C c
      (fun ζ z eps => ∏ j, localDensityReset ad bd (higherBandFamilyTarget i) z eps p
        (fun j l => higherBandCarrierFactor d (higherBandFamilyTarget i) lam i.2 ζ l (U j)) j) Φ e
  exact higherBandFamily_signedIntegral_sum_eq_physical d D M q ad bd C lam ell N mu hell hnu hFine F

theorem integrated_cardinal_matrix_fin_cast {d n m D : ℕ} (h : m = n) (lam T : ℝ)
    (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T (U ∘ finCongr h) β β' = integratedCardinalMatrix lam T U β β' := by
  subst n
  rfl

theorem integrated_cardinal_matrix_full_subset {d n D : ℕ} (lam T : ℝ)
    (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T (spatialSubsetConfiguration Finset.univ U) β β' =
      integratedCardinalMatrix lam T U β β' := by
  let S : Finset (Fin n) := Finset.univ
  let h : S.card = n := by simp [S]
  let e : Fin S.card ≃ S := (finCongr (Fintype.card_coe S).symm).trans (Fintype.equivFin S).symm
  let v : S ≃ Fin n := ⟨Subtype.val, (fun j => ⟨j, Finset.mem_univ j⟩),
    (by intro j; rfl), (by intro j; rfl)⟩
  let τ : Equiv.Perm (Fin n) := ((finCongr h).symm.trans e).trans v
  have hc : spatialSubsetConfiguration S U = (U ∘ τ) ∘ finCongr h := by
    funext j
    change U (e j).val = U (τ (finCongr h j))
    dsimp [τ]
    rfl
  rw [hc, integrated_cardinal_matrix_fin_cast h]
  exact integrated_cardinal_matrix_perm τ lam T U β β'

theorem higherBandActualMatrix_full_subset {d n D : ℕ} (lam L T : ℝ) (fine : Bool)
    (U : Fin n → Covariate d) :
    (higherBandActualMatrix lam L T fine (spatialSubsetConfiguration Finset.univ U) : HighFrameIndex d D → _ → ℝ) =
      higherBandActualMatrix lam L T fine U := by
  funext β β'
  cases fine <;> simp only [higherBandActualMatrix, Bool.false_eq_true, ite_false, ite_true,
    globalCardinalBandMatrix, integrated_cardinal_matrix_full_subset]

theorem higherBandFirstAction_target_count {d n : ℕ} (ad bd lam L T : ℝ)
    (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam) (hL : 0 < L) (hT : 1 ≤ T)
    (m D q : ℕ) (hn : 2 ≤ n) (hD : 1 ≤ D) (hnD : n ≤ D) (hnm : n ≤ m)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T n m D q C fine U p c Φ =
      (∏ i, p i) * responseMatrixAction q C (higherBandActualMatrix lam L T fine U) c Φ := by
  rw [higherBandFirstAction_actual_count_expansion ad bd lam L T ha hab hlam hL hT n m D q hn hD hnD
    C fine U hU p hp c Φ]
  rw [densityCountCoefficient_exact ad bd ha hab m n n (by omega) le_rfl hnm]
  have hS : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  simp only [ite_true, hS, Finset.sum_singleton, one_mul, higherBandActualMatrix_full_subset]

end NearlyMinimax
