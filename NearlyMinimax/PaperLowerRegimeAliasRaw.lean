module

public import NearlyMinimax.PaperLowerRegimeAliasTail
public import NearlyMinimax.AffineNuisanceNumerator


@[expose] public section

/-! The actual full ordinary-plus-pair alias numerator and the literal
compact nuisance supremum from equation (LB-norm). -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable

def paperRegimeAliasRawAction {d n F : ℕ} (C : ModelConstants d)
    (K Cfr a : ℝ) (M D q : ℕ) (N mu eta : ℝ)
    (w : (Fin n → Covariate d) → Fin n → ℝ)
    (z : LocalNuisance (HighFrameIndex d F) n) (U : Fin n → Covariate d)
    (y : Fin n → Fin 3) : ℝ :=
  let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
  let ell := N*Real.exp (-c0*(D : ℝ))
  let ad := C.densityLower+(M : ℝ)⁻¹
  let bd := C.densityUpper-(M : ℝ)⁻¹
  if M<n then
    ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ell N mu)
      ad bd (spatialInterpolationLambda d) ell (fun r => higherBandTargetScale d r N mu)
      M q Cfr a z.2.2.2 eta U z.1 z.2.2.1 (w U) z.2.1 y +
    finePairPairAliasAction ad bd ell N M q Cfr U z.1 z.2.1
      (fun v => highResponseProduct a z.2.2.2 eta z.2.2.1 (w U)
        (fun i => highFrameFeature (U i)) v y)
  else 0

theorem responseMatrixAction_continuous_nuisance {d n F : ℕ}
    (q : ℕ) (C a eta : ℝ) (A : HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (U : Fin n → Covariate d) (w : Fin n → ℝ) (y : Fin n → Fin 3) :
    Continuous (fun z : LocalNuisance (HighFrameIndex d F) n =>
      responseMatrixAction q C A z.2.1 (fun v =>
        highResponseProduct a z.2.2.2 eta z.2.2.1 w (fun i => highFrameFeature (U i)) v y)) := by
  simp_rw [← highResponseMark_action]
  apply continuous_finsetSum
  intro h _
  apply Continuous.const_mul
  unfold highResponseProduct
  apply continuous_finset_prod
  intro i _
  apply ternaryMass_continuous_both
  · unfold coefficientRegression coefficientReset
    fun_prop
  · fun_prop

theorem paperRegimeAliasRawAction_continuous_nuisance {d n F : ℕ}
    (C : ModelConstants d) (K Cfr a : ℝ) (M D q : ℕ) (N mu eta : ℝ)
    (w : (Fin n → Covariate d) → Fin n → ℝ)
    (U : Fin n → Covariate d) (y : Fin n → Fin 3) :
    Continuous (fun z : LocalNuisance (HighFrameIndex d F) n =>
      paperRegimeAliasRawAction C K Cfr a M D q N mu eta w z U y) := by
  unfold paperRegimeAliasRawAction
  split_ifs
  · apply Continuous.add
    · unfold ordinaryFineAliasFamilyRawAction ordinaryFineAliasRawAction
      apply continuous_finsetSum
      intro r _
      apply Continuous.const_mul
      apply continuous_finsetSum
      intro S _
      exact (continuous_finset_prod S (fun i _ => by fun_prop)).mul
        (responseMatrixAction_continuous_nuisance q Cfr a eta _ U (w U) y)
    · unfold finePairPairAliasAction
      apply continuous_finsetSum
      intro S _
      apply Continuous.mul
      · fun_prop
      · exact responseMatrixAction_continuous_nuisance q Cfr a eta _ U (w U) y
  · exact continuous_const

theorem paperRegimeAliasRawAction_spatial_measurable {d n F : ℕ} [NeZero d]
    (C : ModelConstants d) (K Cfr a : ℝ) (M D q : ℕ) (N mu eta : ℝ)
    (hell : 1 ≤ N*Real.exp (-(densityIntervalExponent C.densityLower C.densityUpper+1)*(D : ℝ)))
    (w : (Fin n → Covariate d) → Fin n → ℝ)
    (hw : ∀ i, Measurable (fun U => w U i))
    (z : LocalNuisance (HighFrameIndex d F) n) (y : Fin n → Fin 3) :
    Measurable (fun U => paperRegimeAliasRawAction C K Cfr a M D q N mu eta w z U y) := by
  unfold paperRegimeAliasRawAction
  split_ifs
  · apply Measurable.add
    · unfold ordinaryFineAliasFamilyRawAction
      apply Finset.measurable_sum
      intro r hr
      have hLT := (Finset.mem_filter.mp hr).2.2.le
      exact ordinaryFineAliasRawAction_spatial_measurable _ _ _ _ _ hell (hell.trans hLT)
        M r q Cfr a z.2.2.2 eta (fun _ => z.1) (fun _ => z.2.2.1) w
        (fun _ => measurable_const) (fun _ => measurable_const) hw
        (fun _ => z.2.1) (fun _ => measurable_const) y
    · exact finePairPairAliasAction_spatial_measurable _ _ _ _ M q Cfr a z.2.2.2 eta
        (fun _ => z.1) (fun _ => z.2.2.1) w
        (fun _ => measurable_const) (fun _ => measurable_const) hw z.2.1 y
  · exact measurable_const

theorem paperRegimeAliasRawAction_sum_square_le_geometry {d n F : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (K Cfr : ℝ)
    (M D q : ℕ) (N mu eta : ℝ)
    (H : PaperRegimeHierarchy d K (densityIntervalExponent C.densityLower C.densityUpper+1) 1 1 M D N mu)
    (hres : highCenterResolutionThreshold C ≤ (M : ℝ))
    (htau : shrunkDensityExponent C.densityLower C.densityUpper M ≤
      densityIntervalExponent C.densityLower C.densityUpper+1)
    (hCfr : 1 ≤ Cfr) (heta : 0 ≤ eta) (hetarho : eta ≤ Q.ρ/2)
    (w : (Fin n → Covariate d) → Fin n → ℝ) (hw : ∀ U i, |w U i| ≤ 1)
    (z : LocalNuisance (HighFrameIndex d F) n)
    (hz : z ∈ localNuisanceSet (HighFrameIndex d F) n
      (C.densityLower+(M : ℝ)⁻¹) (C.densityUpper-(M : ℝ)⁻¹) Cfr Q.ρ Q.v)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2) :
    (∑ y : Fin n → Fin 3, paperRegimeAliasRawAction C K Cfr Q.a M D q N mu eta w z U y^2) ≤
      paperRegimeAliasGeometryEnvelope C K Cfr Q.a Q.ρ M D q n F N mu eta U := by
  by_cases hcount : M<n
  · have hn : 1 ≤ n := by omega
    let c0 := densityIntervalExponent C.densityLower C.densityUpper+1
    let ell := N*Real.exp (-c0*(D : ℝ))
    let I := ordinaryFineAliasTargetSet d D ell N mu
    let Rt := paperRegimeFineTargetBound d K c0
    have hI (r : ℕ) (hr : r ∈ I) : 1 ≤ r ∧ r ≤ Rt := by
      have hh := (Finset.mem_filter.mp hr).2
      exact ⟨by omega,H.target_count r hh.2⟩
    obtain ⟨hpD,hc,hg,hV⟩ := localNuisanceSet_guards (HighFrameIndex d F) n
      (C.densityLower+(M : ℝ)⁻¹) (C.densityUpper-(M : ℝ)⁻¹) Cfr Q.ρ Q.v z hz
    obtain ⟨haD,hinterval⟩ := high_source_interval_numeric C (M : ℝ) hres
    have had : 0 < C.densityLower+(M : ℝ)⁻¹ := by simpa only [one_div] using haD
    have hab : C.densityLower+(M : ℝ)⁻¹ < C.densityUpper-(M : ℝ)⁻¹ := by
      simpa only [one_div] using hinterval
    have hprob (f : ℝ) (hf : |f| ≤ Q.ρ) (y : Fin 3) :
        0 ≤ ternaryMass Q.a f z.2.2.2 y :=
      Q.c_pos.le.trans ((Q.legal f _ hf hV).2.2.1 y)
    have ho := ordinaryFineAliasFamilyResponseSquareEnvelope_dominates (F := F)
      I C.densityLower C.densityUpper c0 ell (fun r => higherBandTargetScale d r N mu)
      C.densityLower_pos hab htau hI q hn Cfr Q.a z.2.2.2 eta Q.ρ hCfr Q.a_pos
      heta Q.ρ_pos.le hetarho U hU (fun _ => z.1) (fun _ => z.2.2.1) (fun _ => w U)
      (fun _ => z.2.1) (fun _ => hpD) (fun _ => hg) (fun _ => hw U) (fun _ => hc) hprob
    have hp := finePairPairAliasAction_sum_square_le_geometry (F := F)
      _ _ ell N had hab M q hn Cfr Q.a z.2.2.2 eta Q.ρ hCfr Q.a_pos heta Q.ρ_pos.le
      hetarho U hU z.1 z.2.2.1 (w U) hpD z.2.1 hc hg (hw U) hprob
    let O := fun y : Fin n → Fin 3 => ordinaryFineAliasFamilyRawAction I
      (C.densityLower+(M : ℝ)⁻¹) (C.densityUpper-(M : ℝ)⁻¹) (spatialInterpolationLambda d)
      ell (fun r => higherBandTargetScale d r N mu) M q Cfr Q.a z.2.2.2 eta U z.1 z.2.2.1 (w U) z.2.1 y
    let P := fun y : Fin n → Fin 3 => finePairPairAliasAction
      (C.densityLower+(M : ℝ)⁻¹) (C.densityUpper-(M : ℝ)⁻¹) ell N M q Cfr U z.1 z.2.1
      (fun v => highResponseProduct Q.a z.2.2.2 eta z.2.2.1 (w U)
        (fun i => highFrameFeature (U i)) v y)
    have hs : (∑ y : Fin n → Fin 3, (O y+P y)^2) ≤
        2*((∑ y : Fin n → Fin 3, (O y)^2)+(∑ y : Fin n → Fin 3, (P y)^2)) := by
      calc
        _ ≤ ∑ y : Fin n → Fin 3, 2*((O y)^2+(P y)^2) :=
          Finset.sum_le_sum (fun y _ => by nlinarith [sq_nonneg (O y-P y)])
        _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib]
    have hb := hs.trans (mul_le_mul_of_nonneg_left (add_le_add ho hp) (by norm_num : (0 : ℝ) ≤ 2))
    simpa only [paperRegimeAliasRawAction,if_pos hcount,paperRegimeAliasGeometryEnvelope,O,P,I,Rt,ell,c0] using hb
  · simp only [paperRegimeAliasRawAction,if_neg hcount,zero_pow (by norm_num : 2 ≠ 0),Finset.sum_const_zero]
    exact paperRegimeAliasGeometryEnvelope_nonneg C K Cfr Q.a Q.ρ M D q n F N mu eta U

theorem compactNuisanceEnergy_integrable_and_bound_ae
    {P X Y : Type*} [TopologicalSpace P] [SecondCountableTopology P]
    [MeasurableSpace X] [Fintype Y] (μ : Measure X)
    (K : Set P) (hK : IsCompact K) (hKn : K.Nonempty)
    (F : P → X → Y → ℝ)
    (hmeas : ∀ p ∈ K, ∀ y, Measurable (fun x => F p x y))
    (hcont : ∀ x y, ContinuousOn (fun p => F p x y) K)
    (H : X → ℝ) (hH : Integrable H μ)
    (hbound : ∀ᵐ x ∂μ, ∀ p ∈ K, (∑ y, (F p x y)^2) ≤ H x) :
    Integrable (compactNuisanceEnergy K F) μ ∧
      (∫ x, compactNuisanceEnergy K F x ∂μ) ≤ ∫ x, H x ∂μ := by
  have hm := compactNuisanceEnergy_measurable K hK hKn F hmeas hcont
  have hb : ∀ᵐ x ∂μ, compactNuisanceEnergy K F x ≤ H x := by
    filter_upwards [hbound] with x hx
    obtain ⟨p,hp,he,_⟩ := compactNuisanceEnergy_attained K hK hKn F hcont x
    rw [he]
    exact hx p hp
  have hi : Integrable (compactNuisanceEnergy K F) μ := by
    apply hH.mono' hm.aestronglyMeasurable
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (compactNuisanceEnergy_nonneg K hK hKn F hcont x)]
    exact hx
  exact ⟨hi,integral_mono_ae hi hH hb⟩

end NearlyMinimax
