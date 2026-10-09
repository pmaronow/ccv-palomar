module

public import NearlyMinimax.HighDefectNuisanceNorm
public import NearlyMinimax.SpatialGeometryFactorialEnergy
public import NearlyMinimax.CompleteGeometryExteriorEnergy
public import NearlyMinimax.HighSourceMatchedPacket


@[expose] public section

/-! The literal defect norm bound under the primitive numerical hypotheses of
`lem:defect`. The nuisance supremum is taken before spatial integration.
No sample-size allocation or `Reg(K)` hypothesis is used. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def genericRadialDefectNormSq {d F : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (ad bd Cfr eta N : ℝ) (D q : ℕ) : ℝ :=
  ∫ U, compactNuisanceEnergy
    (localNuisanceSet (HighFrameIndex d F) 2 ad bd Cfr Q.ρ Q.v)
    (radialActualNuisanceNumerator ad bd 0 N D 2 q C Q Cfr eta) U
      ∂fullSpatialPatchDesign d 2

def genericCardinalDefectNormSq {d F : ℕ}
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (ad bd Cfr eta N mu : ℝ) (D q n : ℕ) : ℝ :=
  ∫ U, compactNuisanceEnergy
    (localNuisanceSet (HighFrameIndex d F) n ad bd Cfr Q.ρ Q.v)
    (cardinalActualNuisanceNumerator ad bd
      (max 1 (higherBandTargetScale d n N mu)) D D q C Q Cfr eta) U
      ∂fullSpatialPatchDesign d n

/-- A fixed defect constant, independent of selector, frame degree, cutoff,
activity and response amplitude. -/
def genericDefectNormConstant {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (bd Cfr Cs : ℝ) (q : ℕ) : ℝ :=
  completeGeometryRadialConstant d bd Q.a Q.ρ Cs +
    cardinalGeometryFactorialConstant d q bd Cfr Q.a Q.ρ Cs

theorem generic_radial_defect_factorial_le {d F : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (hF : 3 ≤ F) (ad bd Cfr eta N mu Cs : ℝ) (D q : ℕ)
    (had : 0 < ad) (hab : ad < bd) (hD : 2 ≤ D) (hq : 2 ≤ q)
    (hCfr : 1 ≤ Cfr) (heta : 0 ≤ eta) (hetaQ : eta ≤ Q.ρ/2)
    (hN : 0 < N) (hmu : 0 ≤ mu) (hCs : 0 ≤ Cs) :
    poissonCountWeight (Cs*mu) 2 * genericRadialDefectNormSq (F := F) C Q ad bd Cfr eta N D q ≤
      completeGeometryRadialConstant d bd Q.a Q.ρ Cs * eta^4*mu^2*N^(-(d : ℝ)) := by
  have hi := (radialActualNuisanceEnergy_integrable_and_bound hF ad bd 0 N had hab
    (by norm_num) hN.le D 2 q hD (by norm_num) hq C Q Cfr eta hCfr heta hetaQ hN).2
  have h := mul_le_mul_of_nonneg_left hi (poissonCountWeight_nonneg (mul_nonneg hCs hmu) 2)
  change poissonCountWeight (Cs*mu) 2 * genericRadialDefectNormSq (F := F) C Q ad bd Cfr eta N D q ≤ _ at h
  apply h.trans_eq
  rw [Real.rpow_neg hN.le, Real.rpow_natCast]
  simp only [poissonCountWeight, finePairCountTwoSpatialBudget, completeGeometryRadialConstant]
  norm_num only [Nat.factorial, Nat.cast_ofNat]
  ring

/-- Primitive defect lemma: all literal count-two through count-`D` defect
norms have total Poisson energy `O(η⁴ μ² N⁻ᵈ)`. In particular cutoffs below
one are handled by the actual empty-scale identity and `max 1 ν`. -/
theorem completeGeometryRadialConstant_mono_upper (d : ℕ) (bd B a rho Cs : ℝ)
    (hbd : 0 ≤ bd) (hB : bd ≤ B) :
    completeGeometryRadialConstant d bd a rho Cs ≤ completeGeometryRadialConstant d B a rho Cs := by
  have hp := pow_le_pow_left₀ hbd hB 4
  let K := 27*Cs^2*((2*rho+a)/a^2)^4*(2 : ℝ)^d*spatialExponentialConstant d
  have hK : 0 ≤ K := by
    have := spatialExponentialConstant_nonneg d
    dsimp [K]
    positivity
  convert mul_le_mul_of_nonneg_left hp hK using 1 <;>
    unfold completeGeometryRadialConstant <;> dsimp [K] <;> ring

theorem generic_defect_norm_factorial_energy {d F : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (ad bd B Cfr eta N mu Cs : ℝ) (D q : ℕ)
    (hF : 3 ≤ F) (hDF : D ≤ F) (had : 0 < ad) (hab : ad < bd)
    (hbdB : bd ≤ B) (hD : 2 ≤ D) (hq : 2 ≤ q) (hCfr : 1 ≤ Cfr)
    (heta : 0 ≤ eta) (hetaQ : eta ≤ Q.ρ/2)
    (hN : 1 ≤ N) (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (hmuH : mu*(1+Real.log N) ≤ 1) (hTaylor : eta^(4*q)*N^d ≤ 1)
    (hCs : 0 ≤ Cs) :
    poissonCountWeight (Cs*mu) 2 * genericRadialDefectNormSq (F := F) C Q ad bd Cfr eta N D q +
      (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
        genericCardinalDefectNormSq (F := F) C Q ad bd Cfr eta N mu D q (3+j)) ≤
      genericDefectNormConstant C Q B Cfr Cs q * eta^4*mu^2*N^(-(d : ℝ)) := by
  have hrad := generic_radial_defect_factorial_le C Q hF ad bd Cfr eta N mu Cs D q
    had hab hD hq hCfr heta hetaQ (zero_lt_one.trans_le hN) hmu.le hCs
  have hradCap : poissonCountWeight (Cs*mu) 2 *
      genericRadialDefectNormSq (F := F) C Q ad bd Cfr eta N D q ≤
      completeGeometryRadialConstant d B Q.a Q.ρ Cs * eta^4*mu^2*N^(-(d : ℝ)) := by
    apply hrad.trans
    have hm := mul_le_mul_of_nonneg_right
      (completeGeometryRadialConstant_mono_upper d bd B Q.a Q.ρ Cs
        (le_of_lt (had.trans hab)) hbdB)
      (show 0 ≤ eta^4*mu^2*N^(-(d : ℝ)) from by positivity)
    convert hm using 1 <;> ring
  have hcard : (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      genericCardinalDefectNormSq (F := F) C Q ad bd Cfr eta N mu D q (3+j)) ≤
      cardinalGeometryFactorialConstant d q B Cfr Q.a Q.ρ Cs * eta^4*N^(-(d : ℝ))*mu^2 := by
    apply (Finset.sum_le_sum (s := Finset.range (D-2)) (g := fun j => poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, cardinalGeometryEnvelope (d := d) (n := 3+j) (F := F) q bd Cfr Q.a Q.ρ eta
        (max 1 (higherBandTargetScale d (3+j) N mu)) U ∂fullSpatialPatchDesign d (3+j)) ?_).trans
    · exact finite_cardinal_geometry_budget_le hd (le_of_lt (had.trans hab)) hbdB q Cfr Q.a Q.ρ eta Cs
        Q.a_pos hCs hN hmu hmu1 hmuH hTaylor
    · intro j hj
      have hjD : 3+j ≤ D := by have := Finset.mem_range.mp hj; omega
      have hi := (cardinalActualNuisanceEnergy_integrable_and_le_geometry ad bd had hab
        (max 1 (higherBandTargetScale d (3+j) N mu)) (le_max_left _ _) D D q
        (by omega) hjD hjD (hjD.trans hDF) C Q Cfr eta hCfr heta hetaQ hd (by omega)).2
      exact mul_le_mul_of_nonneg_left hi (poissonCountWeight_nonneg (mul_nonneg hCs hmu.le) _)
  exact (add_le_add hradCap hcard).trans_eq (by unfold genericDefectNormConstant; ring)

/-- The literal matched-cardinal defect in the paper, including its single
variance correction. Its scale parameter is the unmodified physical `ν`. -/
def paperCardinalDefectNumerator {d n F : ℕ} (q : ℕ) (C a V eta T : ℝ)
    (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) : ℝ :=
  (∏ i, p i) * (responseMatrixAction q C
    (integratedCardinalMatrix (spatialInterpolationLambda d) T U) c
    (fun v => highResponseProduct a V eta g w (fun i => highFrameFeature (U i)) v y) -
      eta^2 * ∑ i, (w i)^2 *
        highResponseVarianceTerm a V eta g w (fun i => highFrameFeature (U i)) c y i)

theorem cardinalDefectPolynomial_max_eq_physical {d n F : ℕ} (hn : 2 ≤ n) (hnF : n ≤ F)
    (q : ℕ) (C a eta T : ℝ) (hC : C ≠ 0) (hT : 0 < T)
    (z : LocalNuisance (HighFrameIndex d F) n) (U : Fin n → Covariate d) (y : Fin n → Fin 3) :
    cardinalDefectPolynomial q C a eta (max 1 T) z U y =
      paperCardinalDefectNumerator q C a z.2.2.2 eta T U z.1 z.2.2.1
        (fun i => highWindowTensor d (U i)) z.2.1 y := by
  have hm : integratedCardinalMatrix (D := F) (spatialInterpolationLambda d) (max 1 T) U =
      integratedCardinalMatrix (spatialInterpolationLambda d) T U := by
    funext b b'
    exact integrated_cardinal_matrix_max_one hn _ hT U b b'
  unfold cardinalDefectPolynomial paperCardinalDefectNumerator
  simp_rw [integrated_cardinal_weight_max_one hn _ _ hT U, hm]
  rw [integrated_cardinal_response_heat_positive hnF q C a z.2.2.2 eta
    (spatialInterpolationLambda d) T hC hT U z.2.2.1
      (fun i => highWindowTensor d (U i)) z.2.1 y]
  have hs : (∑ i, (highWindowTensor d (U i))^2 *
      (integratedCardinalWeight (spatialInterpolationLambda d) T U i - 1) *
        highResponseVarianceTerm a z.2.2.2 eta z.2.2.1
          (fun i => highWindowTensor d (U i)) (fun i => highFrameFeature (U i)) z.2.1 y i) =
      (∑ i, (highWindowTensor d (U i))^2 *
        integratedCardinalWeight (spatialInterpolationLambda d) T U i *
        highResponseVarianceTerm a z.2.2.2 eta z.2.2.1
          (fun i => highWindowTensor d (U i)) (fun i => highFrameFeature (U i)) z.2.1 y i) -
      (∑ i, (highWindowTensor d (U i))^2 *
        highResponseVarianceTerm a z.2.2.2 eta z.2.2.1
          (fun i => highWindowTensor d (U i)) (fun i => highFrameFeature (U i)) z.2.1 y i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

def genericPhysicalCardinalDefectNormSq {d F : ℕ}
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (ad bd Cfr eta N mu : ℝ) (D q n : ℕ) : ℝ :=
  ∫ U, compactNuisanceEnergy
    (localNuisanceSet (HighFrameIndex d F) n ad bd Cfr Q.ρ Q.v)
    (fun z U y => paperCardinalDefectNumerator q Cfr Q.a z.2.2.2 eta
      (higherBandTargetScale d n N mu) U z.1 z.2.2.1
        (fun i => highWindowTensor d (U i)) z.2.1 y) U ∂fullSpatialPatchDesign d n

theorem genericPhysicalCardinalDefectNormSq_eq {d n F : ℕ}
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (ad bd Cfr eta N mu : ℝ) (D q : ℕ) (had : 0 < ad) (hab : ad < bd)
    (hCfr : 1 ≤ Cfr) (hn : 3 ≤ n) (hnD : n ≤ D) (hnF : n ≤ F)
    (hnu : 0 < higherBandTargetScale d n N mu) :
    genericPhysicalCardinalDefectNormSq (F := F) C Q ad bd Cfr eta N mu D q n =
      genericCardinalDefectNormSq (F := F) C Q ad bd Cfr eta N mu D q n := by
  apply integral_congr_ae
  filter_upwards [fullSpatialPatchDesign_ae_hyperplaneCube] with U hU
  apply compactNuisanceEnergy_congrOn
  intro z hz y
  have he := cardinalActualNuisanceNumerator_eq_polynomial ad bd had hab
    (max 1 (higherBandTargetScale d n N mu)) (le_max_left _ _) D D q hn hnD hnD hnF
    C Q Cfr eta hCfr z hz U hU y
  rw [he]
  have hpatch : U ∈ highDefectPatchSet d n := hU
  simp only [cardinalDefectPatchPolynomial, if_pos hpatch]
  exact (cardinalDefectPolynomial_max_eq_physical (by omega) hnF q Cfr Q.a eta _
    (lt_of_lt_of_le zero_lt_one hCfr).ne' hnu z U y).symm

/-- The same primitive bound with the unmodified physical cutoff inside the
literal source defect. Empty scale domains below one are proved harmless. -/
theorem generic_physical_defect_norm_factorial_energy {d F : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (ad bd B Cfr eta N mu Cs : ℝ) (D q : ℕ)
    (hF : 3 ≤ F) (hDF : D ≤ F) (had : 0 < ad) (hab : ad < bd)
    (hbdB : bd ≤ B) (hD : 2 ≤ D) (hq : 2 ≤ q) (hCfr : 1 ≤ Cfr)
    (heta : 0 ≤ eta) (hetaQ : eta ≤ Q.ρ/2)
    (hN : 1 ≤ N) (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (hmuH : mu*(1+Real.log N) ≤ 1) (hTaylor : eta^(4*q)*N^d ≤ 1)
    (hCs : 0 ≤ Cs) :
    poissonCountWeight (Cs*mu) 2 * genericRadialDefectNormSq (F := F) C Q ad bd Cfr eta N D q +
      (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
        genericPhysicalCardinalDefectNormSq (F := F) C Q ad bd Cfr eta N mu D q (3+j)) ≤
      genericDefectNormConstant C Q B Cfr Cs q * eta^4*mu^2*N^(-(d : ℝ)) := by
  have hnu (n : ℕ) : 0 < higherBandTargetScale d n N mu := by
    unfold higherBandTargetScale
    have hH : 0 < 1+Real.log N := by linarith only [Real.log_nonneg hN]
    exact mul_pos (zero_lt_one.trans_le hN) (Real.rpow_pos_of_pos (mul_pos hmu hH) _)
  have he : (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      genericPhysicalCardinalDefectNormSq (F := F) C Q ad bd Cfr eta N mu D q (3+j)) =
      (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      genericCardinalDefectNormSq (F := F) C Q ad bd Cfr eta N mu D q (3+j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hnD : 3+j ≤ D := by have := Finset.mem_range.mp hj; omega
    rw [genericPhysicalCardinalDefectNormSq_eq C Q ad bd Cfr eta N mu D q had hab
      hCfr (by omega) hnD (hnD.trans hDF) (hnu _)]
  rw [he]
  exact generic_defect_norm_factorial_energy hd C Q ad bd B Cfr eta N mu Cs D q
    hF hDF had hab hbdB hD hq hCfr heta hetaQ hN hmu hmu1 hmuH hTaylor hCs

/-- Count-indexed literal defect energy. At count two it is the genuine
three-row radial defect; at higher counts it is the matched heat defect. -/
def paperDefectNormSq {d F : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (ad bd Cfr eta N mu : ℝ) (D q n : ℕ) : ℝ :=
  if n=2 then genericRadialDefectNormSq (F := F) C Q ad bd Cfr eta N D q
  else genericPhysicalCardinalDefectNormSq (F := F) C Q ad bd Cfr eta N mu D q n

/-- Literal `lem:defect`, with its count sum from two through the arbitrary
selector D, under only the lemma's primitive numerical hypotheses. -/
theorem paper_generic_defect_lemma {d F : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (ad bd B Cfr eta N mu Cs : ℝ) (D q : ℕ)
    (hF : 3 ≤ F) (hDF : D ≤ F) (had : 0 < ad) (hab : ad < bd)
    (hbdB : bd ≤ B) (hD : 2 ≤ D) (hq : 2 ≤ q) (hCfr : 1 ≤ Cfr)
    (heta : 0 ≤ eta) (hetaQ : eta ≤ Q.ρ/2)
    (hN : 1 ≤ N) (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (hmuH : mu*(1+Real.log N) ≤ 1) (hTaylor : eta^(4*q)*N^d ≤ 1)
    (hCs : 0 ≤ Cs) :
    (∑ j ∈ Finset.range (D-1), poissonCountWeight (Cs*mu) (2+j) *
      paperDefectNormSq (F := F) C Q ad bd Cfr eta N mu D q (2+j)) ≤
      genericDefectNormConstant C Q B Cfr Cs q * eta^4*mu^2*N^(-(d : ℝ)) := by
  have hsplit : (∑ j ∈ Finset.range (D-1), poissonCountWeight (Cs*mu) (2+j) *
      paperDefectNormSq (F := F) C Q ad bd Cfr eta N mu D q (2+j)) =
      poissonCountWeight (Cs*mu) 2 * genericRadialDefectNormSq (F := F) C Q ad bd Cfr eta N D q +
      (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
        genericPhysicalCardinalDefectNormSq (F := F) C Q ad bd Cfr eta N mu D q (3+j)) := by
    rw [show D-1=(D-2)+1 by omega, Finset.sum_range_succ']
    simp only [Nat.add_zero, paperDefectNormSq, if_pos rfl]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [show 2+(j+1)=3+j by omega, if_neg (show 3+j≠2 by omega)]
  rw [hsplit]
  exact generic_physical_defect_norm_factorial_energy hd C Q ad bd B Cfr eta N mu Cs D q
    hF hDF had hab hbdB hD hq hCfr heta hetaQ hN hmu hmu1 hmuH hTaylor hCs

/-- Fixed positive constants are chosen before every density shrink,
selector and numerical tuple, as in the manuscript's defect lemma. -/
theorem paper_generic_defect_lemma_uniform {d : ℕ} [NeZero d]
    (hd : 5 ≤ d) (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (B Cfr Cs : ℝ) (q : ℕ) (hCfr : 1 ≤ Cfr) (hCs : 0 ≤ Cs) (hq : 2 ≤ q) :
    ∃ C5 eta0 : ℝ, 0 < C5 ∧ 0 < eta0 ∧
      ∀ (F : ℕ) (ad bd eta N mu : ℝ) (D : ℕ),
      3 ≤ F → D ≤ F → 0 < ad → ad < bd → bd ≤ B → 2 ≤ D →
      0 ≤ eta → eta ≤ eta0 → 1 ≤ N → 0 < mu → mu ≤ 1 →
      mu*(1+Real.log N) ≤ 1 → eta^(4*q)*N^d ≤ 1 →
      (∑ j ∈ Finset.range (D-1), poissonCountWeight (Cs*mu) (2+j) *
        paperDefectNormSq (F := F) C Q ad bd Cfr eta N mu D q (2+j)) ≤
        C5 * eta^4*mu^2*N^(-(d : ℝ)) := by
  let K := genericDefectNormConstant C Q B Cfr Cs q
  refine ⟨1+|K|, Q.ρ/2, by positivity, div_pos Q.ρ_pos (by norm_num), ?_⟩
  intro F ad bd eta N mu D hF hDF had hab hbdB hD heta hetaQ hN hmu hmu1 hmuH hTaylor
  have h := paper_generic_defect_lemma hd C Q ad bd B Cfr eta N mu Cs D q
    hF hDF had hab hbdB hD hq hCfr heta hetaQ hN hmu hmu1 hmuH hTaylor hCs
  apply h.trans
  have hk : K ≤ 1+|K| := by linarith only [le_abs_self K]
  have hm := mul_le_mul_of_nonneg_right hk
    (show 0 ≤ eta^4*mu^2*N^(-(d : ℝ)) from by positivity)
  convert hm using 1 <;> dsimp [K] <;> ring

end NearlyMinimax
