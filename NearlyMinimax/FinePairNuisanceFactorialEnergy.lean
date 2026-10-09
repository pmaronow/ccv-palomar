module

public import NearlyMinimax.FinePairNuisanceNorm
public import NearlyMinimax.SpatialGeometryFactorialEnergy


@[expose] public section

/-! Factorial bounds for the literal compact-nuisance norms of the actual
pair alias and higher field terms, derived from their spatial envelopes. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem finite_fine_pair_alias_nuisance_energy_le {d D : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    {aD bD ad bd c0 K : ℝ} (haD : 0 < aD) (had : aD ≤ ad) (hbd : bd ≤ bD)
    (hab : ad < bd) (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0)
    (hc0 : 0 ≤ c0) (hK : 0 ≤ K) (M q : ℕ) (Cfr eta ell N Cs mu : ℝ)
    (hCfr : 1 ≤ Cfr) (heta : 0 ≤ eta) (hetaRho : eta ≤ Q.ρ/2)
    (hN : 0 < N) (hell : ell=N*Real.exp (-c0*D)) (hell1 : 1 ≤ ell)
    (hellN : ell ≤ N) (hDM : (D : ℝ) ≤ K*M)
    (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (F : ℕ → ℕ) (w : ∀ n : ℕ, (Fin n → Covariate d) → Fin n → ℝ)
    (hw : ∀ n i, Measurable (fun U => w n U i)) (hwb : ∀ n U i, |w n U i| ≤ 1) :
    (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, finePairNuisanceEnergy (F := F (3+j)) false ad bd ell N M q Cfr Q.a Q.ρ Q.v eta (w (3+j)) U
        ∂fullSpatialPatchDesign d (3+j)) ≤
      finePairSaddleAliasFactorialConstant d q aD bD Cfr Q.a Q.ρ c0 K (3*Cs) *
        (eta^4*N^(4-(d : ℝ))) *
        poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD Cfr Q.a Q.ρ c0 K (3*Cs)*mu) (M+1) := by
  have had0 : 0 < ad := haD.trans_le had
  have hell0 : 0 < ell := zero_lt_one.trans_le hell1
  apply le_trans (Finset.sum_le_sum (fun j _ => ?_))
    (finite_fine_pair_alias_geometry_budget_le hd haD had hbd hab htau hc0 hK
      M q Cfr Q.a Q.ρ eta ell N Cs mu hN hell hell1 hellN hDM hCs hmu hmu1)
  apply mul_le_mul_of_nonneg_left _ (poissonCountWeight_nonneg (mul_nonneg hCs hmu) (3+j))
  by_cases hcount : M<3+j
  · simp only [if_pos hcount]
    exact (finePairNuisanceEnergy_integrable_and_le_geometry (F := F (3+j)) hd C Q false
      ad bd ell N had0 hab hell0 hellN M q (by omega) Cfr eta hCfr heta hetaRho
      (w (3+j)) (hw (3+j)) (hwb (3+j))).2
  · simp only [if_neg hcount]
    have he : (fun U : Fin (3+j) → Covariate d =>
        finePairNuisanceEnergy (F := F (3+j)) false ad bd ell N M q Cfr Q.a Q.ρ Q.v eta (w (3+j)) U) =
        (fun _ => 0) := by
      funext U
      exact finePairAliasNuisanceEnergy_zero_selected_count C Q ad bd ell N had0 hab
        M q (by omega) (by omega) Cfr eta hCfr (w (3+j)) U
    rw [he,integral_zero]

theorem finite_fine_field_nuisance_energy_le {d D : ℕ} [NeZero d]
    (hd : 5 ≤ d) (hD : 3 ≤ D) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    {aD bD ad bd c0 : ℝ} (haD : 0 < aD) (had : aD ≤ ad) (hbd : bd ≤ bD)
    (hab : ad < bd) (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0)
    (M q : ℕ) (Cfr eta ell N Cs mu : ℝ)
    (hCfr : 1 ≤ Cfr) (heta : 0 ≤ eta) (hetaRho : eta ≤ Q.ρ/2)
    (hell : 0 < ell) (hellN : ell ≤ N) (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (F : ℕ → ℕ) (w : ∀ n : ℕ, (Fin n → Covariate d) → Fin n → ℝ)
    (hw : ∀ n i, Measurable (fun U => w n U i)) (hwb : ∀ n U i, |w n U i| ≤ 1) :
    (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, finePairNuisanceEnergy (F := F (3+j)) true ad bd ell N M q Cfr Q.a Q.ρ Q.v eta (w (3+j)) U
        ∂fullSpatialPatchDesign d (3+j)) ≤
      finePairFieldFactorialConstant d q aD bD Cfr Q.a Q.ρ c0 (3*Cs) * eta^4 *
        Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) * (ell^(2-(d : ℝ)))^2 * mu^4 := by
  apply le_trans (Finset.sum_le_sum (fun j _ => ?_))
    (finite_fine_field_geometry_budget_le hd hD haD had hbd hab htau M q
      Cfr Q.a Q.ρ eta ell N Cs mu hell hCs hmu hmu1)
  apply mul_le_mul_of_nonneg_left _ (poissonCountWeight_nonneg (mul_nonneg hCs hmu) (3+j))
  exact (finePairNuisanceEnergy_integrable_and_le_geometry (F := F (3+j)) hd C Q true
    ad bd ell N (haD.trans_le had) hab hell hellN M q (by omega) Cfr eta hCfr heta hetaRho
    (w (3+j)) (hw (3+j)) (hwb (3+j))).2

end NearlyMinimax
