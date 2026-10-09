module

public import NearlyMinimax.PaperLowerRegimeAliasRaw
public import NearlyMinimax.HighSpatialEnvelopes


@[expose] public section

/-! Literal compact-nuisance norms of the actual fine pair alias and higher
 even field components. Spatial measurability and nuisance continuity follow
 from their finite response formulas; integrability follows from genuine
 nuisance-independent geometric envelopes. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def finePairNuisanceAction {d n F : ℕ} (isField : Bool)
    (ad bd T0 N : ℝ) (M q : ℕ) (Cfr a eta : ℝ)
    (w : (Fin n → Covariate d) → Fin n → ℝ)
    (z : LocalNuisance (HighFrameIndex d F) n) (U : Fin n → Covariate d)
    (y : Fin n → Fin 3) : ℝ :=
  match isField with
  | false => finePairPairAliasAction ad bd T0 N M q Cfr U z.1 z.2.1
      (fun v => highResponseProduct a z.2.2.2 eta z.2.2.1 (w U)
        (fun i => highFrameFeature (U i)) v y)
  | true => finePairEvenFieldAction ad bd T0 N M q Cfr U z.1 z.2.1
      (fun v => highResponseProduct a z.2.2.2 eta z.2.2.1 (w U)
        (fun i => highFrameFeature (U i)) v y)

def finePairNuisanceEnergy {d n F : ℕ} (isField : Bool)
    (ad bd T0 N : ℝ) (M q : ℕ) (Cfr a rho v eta : ℝ)
    (w : (Fin n → Covariate d) → Fin n → ℝ) :
    (Fin n → Covariate d) → ℝ :=
  compactNuisanceEnergy (localNuisanceSet (HighFrameIndex d F) n ad bd Cfr rho v)
    (finePairNuisanceAction isField ad bd T0 N M q Cfr a eta w)

def finePairComponentGeometryEnvelope {d n : ℕ} (isField : Bool)
    (ad bd T0 N : ℝ) (M q : ℕ) (Cfr a rho eta : ℝ) :
    (Fin n → Covariate d) → ℝ :=
  match isField with
  | false => finePairAliasGeometryEnvelope ad bd T0 N M q Cfr a rho eta
  | true => fineFieldGeometryEnvelope ad bd T0 N M q Cfr a rho eta

def finePairComponentSpatialBudget (isField : Bool) (d n M q : ℕ)
    (ad bd Cfr a rho eta T0 : ℝ) : ℝ :=
  match isField with
  | false => finePairAliasActionSpatialBudget d n M q ad bd Cfr a rho eta T0
  | true => finePairEvenActionSpatialBudget d n M q ad bd Cfr a rho eta T0

theorem finePairNuisanceAction_spatial_measurable {d n F : ℕ} [NeZero d]
    (isField : Bool) (ad bd T0 N : ℝ) (M q : ℕ) (Cfr a eta : ℝ)
    (w : (Fin n → Covariate d) → Fin n → ℝ)
    (hw : ∀ i, Measurable (fun U => w U i))
    (z : LocalNuisance (HighFrameIndex d F) n) (y : Fin n → Fin 3) :
    Measurable (fun U => finePairNuisanceAction isField ad bd T0 N M q Cfr a eta w z U y) := by
  cases isField
  · exact finePairPairAliasAction_spatial_measurable ad bd T0 N M q Cfr a z.2.2.2 eta
      (fun _ => z.1) (fun _ => z.2.2.1) w
      (fun _ => measurable_const) (fun _ => measurable_const) hw z.2.1 y
  · exact finePairEvenFieldAction_spatial_measurable ad bd T0 N M q Cfr a z.2.2.2 eta
      (fun _ => z.1) (fun _ => z.2.2.1) w
      (fun _ => measurable_const) (fun _ => measurable_const) hw z.2.1 y

theorem finePairNuisanceAction_continuous_nuisance {d n F : ℕ}
    (isField : Bool) (ad bd T0 N : ℝ) (M q : ℕ) (Cfr a eta : ℝ)
    (w : (Fin n → Covariate d) → Fin n → ℝ)
    (U : Fin n → Covariate d) (y : Fin n → Fin 3) :
    Continuous (fun z : LocalNuisance (HighFrameIndex d F) n =>
      finePairNuisanceAction isField ad bd T0 N M q Cfr a eta w z U y) := by
  cases isField <;> simp only [finePairNuisanceAction]
  · unfold finePairPairAliasAction
    apply continuous_finsetSum
    intro S _
    apply Continuous.mul
    · fun_prop
    · exact responseMatrixAction_continuous_nuisance q Cfr a eta _ U (w U) y
  · unfold finePairEvenFieldAction
    apply continuous_finsetSum
    intro S _
    apply Continuous.mul
    · fun_prop
    · exact responseMatrixAction_continuous_nuisance q Cfr a eta _ U (w U) y

theorem finePairComponentGeometryEnvelope_integrable_and_le {d n : ℕ} [NeZero d]
    (hd : 5 ≤ d) (isField : Bool) (ad bd T0 N : ℝ)
    (hT0 : 0 < T0) (hN : T0 ≤ N) (M q : ℕ) (Cfr a rho eta : ℝ) :
    Integrable (finePairComponentGeometryEnvelope (d := d) (n := n)
      isField ad bd T0 N M q Cfr a rho eta) (fullSpatialPatchDesign d n) ∧
      (∫ U, finePairComponentGeometryEnvelope isField ad bd T0 N M q Cfr a rho eta U
        ∂fullSpatialPatchDesign d n) ≤
        (3 : ℝ)^n*finePairComponentSpatialBudget isField d n M q ad bd Cfr a rho eta T0 := by
  cases isField
  · exact finePairAliasGeometryEnvelope_integrable_and_le (by omega)
      ad bd T0 N hT0 hN M q Cfr a rho eta
  · exact fineFieldGeometryEnvelope_integrable_and_le (by omega)
      ad bd T0 N hT0 M q Cfr a rho eta

theorem finePairNuisanceEnergy_integrable_and_le_geometry {d n F : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (isField : Bool) (ad bd T0 N : ℝ) (had : 0 < ad) (hab : ad < bd)
    (hT0 : 0 < T0) (hN : T0 ≤ N) (M q : ℕ) (hn : 1 ≤ n)
    (Cfr eta : ℝ) (hCfr : 1 ≤ Cfr) (heta : 0 ≤ eta) (hetaRho : eta ≤ Q.ρ/2)
    (w : (Fin n → Covariate d) → Fin n → ℝ)
    (hw : ∀ i, Measurable (fun U => w U i)) (hwb : ∀ U i, |w U i| ≤ 1) :
    Integrable (finePairNuisanceEnergy (F := F) isField ad bd T0 N M q Cfr Q.a Q.ρ Q.v eta w)
      (fullSpatialPatchDesign d n) ∧
      (∫ U, finePairNuisanceEnergy (F := F) isField ad bd T0 N M q Cfr Q.a Q.ρ Q.v eta w U
        ∂fullSpatialPatchDesign d n) ≤
      ∫ U, finePairComponentGeometryEnvelope isField ad bd T0 N M q Cfr Q.a Q.ρ eta U
        ∂fullSpatialPatchDesign d n := by
  let K := localNuisanceSet (HighFrameIndex d F) n ad bd Cfr Q.ρ Q.v
  have hK : IsCompact K := localNuisanceSet_isCompact _ _ _ _ _ _ _
  have hKn : K.Nonempty := localNuisanceSet_nonempty _ _ hab.le
    (zero_le_one.trans hCfr) Q.ρ_pos.le
  have hH := finePairComponentGeometryEnvelope_integrable_and_le (n := n) hd isField
    ad bd T0 N hT0 hN M q Cfr Q.a Q.ρ eta
  have h := compactNuisanceEnergy_integrable_and_bound_ae (fullSpatialPatchDesign d n)
    K hK hKn (finePairNuisanceAction isField ad bd T0 N M q Cfr Q.a eta w)
    (fun z _ y => finePairNuisanceAction_spatial_measurable isField ad bd T0 N M q Cfr Q.a eta w hw z y)
    (fun U y => (finePairNuisanceAction_continuous_nuisance (F := F)
      isField ad bd T0 N M q Cfr Q.a eta w U y).continuousOn)
    (finePairComponentGeometryEnvelope isField ad bd T0 N M q Cfr Q.a Q.ρ eta) hH.1 ?_
  · exact h
  · filter_upwards [fullSpatialPatchDesign_ae_coordinate_bound (d := d) (n := n)] with U hU
    intro z hz
    obtain ⟨hp,hc,hg,hV⟩ := localNuisanceSet_guards _ n ad bd Cfr Q.ρ Q.v z hz
    have hprob (f : ℝ) (hf : |f| ≤ Q.ρ) (y : Fin 3) :
        0 ≤ ternaryMass Q.a f z.2.2.2 y :=
      Q.c_pos.le.trans ((Q.legal f _ hf hV).2.2.1 y)
    cases isField
    · exact finePairPairAliasAction_sum_square_le_geometry ad bd T0 N had hab M q hn
        Cfr Q.a z.2.2.2 eta Q.ρ hCfr Q.a_pos heta Q.ρ_pos.le hetaRho
        U hU z.1 z.2.2.1 (w U) hp z.2.1 hc hg (hwb U) hprob
    · exact finePairEvenFieldAction_sum_square_le_geometry ad bd T0 N had hab M q hn
        Cfr Q.a z.2.2.2 eta Q.ρ hCfr Q.a_pos heta Q.ρ_pos.le hetaRho
        U hU z.1 z.2.2.1 (w U) hp z.2.1 hc hg (hwb U) hprob

theorem finePairNuisanceEnergy_integrable_and_bound {d n F : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (isField : Bool) (ad bd T0 N : ℝ) (had : 0 < ad) (hab : ad < bd)
    (hT0 : 0 < T0) (hN : T0 ≤ N) (M q : ℕ) (hn : 1 ≤ n)
    (Cfr eta : ℝ) (hCfr : 1 ≤ Cfr) (heta : 0 ≤ eta) (hetaRho : eta ≤ Q.ρ/2)
    (w : (Fin n → Covariate d) → Fin n → ℝ)
    (hw : ∀ i, Measurable (fun U => w U i)) (hwb : ∀ U i, |w U i| ≤ 1) :
    Integrable (finePairNuisanceEnergy (F := F) isField ad bd T0 N M q Cfr Q.a Q.ρ Q.v eta w)
      (fullSpatialPatchDesign d n) ∧
      (∫ U, finePairNuisanceEnergy (F := F) isField ad bd T0 N M q Cfr Q.a Q.ρ Q.v eta w U
        ∂fullSpatialPatchDesign d n) ≤
      (3 : ℝ)^n*finePairComponentSpatialBudget isField d n M q ad bd Cfr Q.a Q.ρ eta T0 := by
  have h := finePairNuisanceEnergy_integrable_and_le_geometry (F := F) hd C Q isField
    ad bd T0 N had hab hT0 hN M q hn Cfr eta hCfr heta hetaRho w hw hwb
  exact ⟨h.1,h.2.trans (finePairComponentGeometryEnvelope_integrable_and_le
    hd isField ad bd T0 N hT0 hN M q Cfr Q.a Q.ρ eta).2⟩

theorem finePairAliasNuisanceEnergy_zero_selected_count {d n F : ℕ}
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (ad bd T0 N : ℝ) (had : 0 < ad) (hab : ad < bd) (M q : ℕ)
    (hn : 3 ≤ n) (hM : n ≤ M) (Cfr eta : ℝ) (hCfr : 1 ≤ Cfr)
    (w : (Fin n → Covariate d) → Fin n → ℝ) (U : Fin n → Covariate d) :
    finePairNuisanceEnergy (F := F) false ad bd T0 N M q Cfr Q.a Q.ρ Q.v eta w U = 0 := by
  let K := localNuisanceSet (HighFrameIndex d F) n ad bd Cfr Q.ρ Q.v
  have hK : IsCompact K := localNuisanceSet_isCompact _ _ _ _ _ _ _
  have hKn : K.Nonempty := localNuisanceSet_nonempty _ _ hab.le
    (zero_le_one.trans hCfr) Q.ρ_pos.le
  obtain ⟨z,_,he,_⟩ := compactNuisanceEnergy_attained K hK hKn
    (finePairNuisanceAction false ad bd T0 N M q Cfr Q.a eta w)
    (fun U y => (finePairNuisanceAction_continuous_nuisance (F := F)
      false ad bd T0 N M q Cfr Q.a eta w U y).continuousOn) U
  change compactNuisanceEnergy K _ U = 0
  rw [he]
  apply Finset.sum_eq_zero
  intro y _
  simp only [finePairNuisanceAction,
    finePairPairAliasAction_zero_selected_count ad bd T0 N had hab M q hn hM,
    zero_pow (by norm_num : 2 ≠ 0)]

end NearlyMinimax
