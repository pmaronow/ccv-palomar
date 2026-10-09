module

public import NearlyMinimax.HighCardinalSpatialEnergy
public import NearlyMinimax.LowerAliasScale
public import NearlyMinimax.HigherBandActivityConversion


@[expose] public section

/-! Full-product spatial energy for the actual all-count ordinary fine-band
alias expression. All bounds are uniform in the tuple-dependent nuisance
values; the spatial kernel is the constructed cardinal band. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

/-- The exact raw target-r ordinary fine-band expression produced by the
finite density selector and finite response matrix action. -/
def ordinaryFineAliasRawAction {d n F : ℕ} (ad bd lam L T : ℝ) (M r q : ℕ)
    (C a V η : ℝ) (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) : ℝ :=
  densityCountCoefficient ad bd M r n *
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      (∏ i ∈ S, p i) * responseMatrixAction q C
        (globalCardinalBandMatrix lam L T (spatialSubsetConfiguration S U)) c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)

/-- Genuine uniform selector-product bound at every count. -/
theorem ordinary_count_product_abs_bound {n : ℕ} (ad bd : ℝ)
    (ha : 0 < ad) (hab : ad < bd) (M r : ℕ) (hr : 1 ≤ r)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (S : Finset (Fin n)) (hS : S.card = r) :
    |densityCountCoefficient ad bd M r n * (∏ i ∈ S, p i)| ≤
      bd^n * (ordinaryDensityActivityBase ad bd)^r *
        Real.exp ((M : ℝ) * exteriorTau ((ad+bd)/(bd-ad))) := by
  have hbd : 0 < bd := ha.trans hab
  have hcard : r ≤ n := by simpa only [hS, Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ S
  have hm : 0 < |densityMargin ad bd 0| := abs_pos.mpr (densityMargin_zero_ne ad bd ha hab)
  have hτ : 0 ≤ exteriorTau ((ad+bd)/(bd-ad)) := by
    rw [exteriorTau_sqrt_ratio ad bd ha hab]
    exact (densityIntervalExponent_pos ha hab).le
  have hprod : |∏ i ∈ S, p i| ≤ bd^r := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ i ∈ S, bd := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => by
        simpa only [abs_of_pos (ha.trans_le (hp i).1)] using (hp i).2)
      _ = _ := by rw [Finset.prod_const, hS]
  have hcoeff := densityCountCoefficient_abs_bound ad bd ha hab M r n hr
  have hcosh : Real.cosh ((M+r : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) ≤
      Real.exp ((M+r : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) := by
    rw [Real.cosh_eq]
    have he := Real.exp_le_exp.mpr (show -((M+r : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) ≤
      ((M+r : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) by
        have hh := mul_nonneg (Nat.cast_nonneg (M+r)) hτ
        linarith)
    linarith
  have hj : (bd-ad)/4 ≤ bd := by linarith
  have he : Real.exp (exteriorTau ((ad+bd)/(bd-ad))) ≤
      Real.exp (1+exteriorTau ((ad+bd)/(bd-ad))) := Real.exp_le_exp.mpr (by linarith)
  have hb : (bd-ad)/4/|densityMargin ad bd 0| * Real.exp (exteriorTau ((ad+bd)/(bd-ad))) ≤
      ordinaryDensityActivityBase ad bd := by
    unfold ordinaryDensityActivityBase
    rw [abs_div, abs_of_pos hbd]
    exact (mul_le_mul (div_le_div_of_nonneg_right hj hm.le) he
      (Real.exp_pos _).le (div_nonneg hbd.le hm.le)).trans_eq (by ring)
  have h1 := mul_le_mul hcoeff hprod (abs_nonneg _) (by positivity)
  have h2 := mul_le_mul_of_nonneg_left hcosh
    (show 0 ≤ (bd^(n-r)*((bd-ad)/4)^r/|densityMargin ad bd 0|^r)*bd^r by positivity)
  have hid : ((bd^(n-r)*((bd-ad)/4)^r/|densityMargin ad bd 0|^r)*bd^r)*
      Real.exp ((M+r : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) =
      bd^n * (((bd-ad)/4/|densityMargin ad bd 0|)*Real.exp (exteriorTau ((ad+bd)/(bd-ad))))^r *
        Real.exp ((M : ℝ)*exteriorTau ((ad+bd)/(bd-ad))) := by
    have heq : Real.exp ((M+r : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) =
        Real.exp ((M : ℝ)*exteriorTau ((ad+bd)/(bd-ad))) *
          (Real.exp (exteriorTau ((ad+bd)/(bd-ad))))^r := by
      rw [Nat.cast_add, add_mul, Real.exp_add]
      congr 1
      simpa only [mul_comm] using Real.exp_nat_mul (exteriorTau ((ad+bd)/(bd-ad))) r
    rw [heq]
    generalize (bd-ad)/4 = J
    generalize |densityMargin ad bd 0| = H
    generalize Real.exp (exteriorTau ((ad+bd)/(bd-ad))) = X
    generalize Real.exp ((M : ℝ)*exteriorTau ((ad+bd)/(bd-ad))) = Y
    rw [mul_pow, div_pow]
    have hpw : bd^(n-r)*bd^r = bd^n := by rw [← pow_add, Nat.sub_add_cancel hcard]
    calc _ = (bd^(n-r)*bd^r) *
        (J^r/H^r) * X^r * Y := by ring
         _ = _ := by rw [hpw]; ring
  have h3 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb r) (pow_nonneg hbd.le n))
    (Real.exp_pos ((M : ℝ)*exteriorTau ((ad+bd)/(bd-ad)))).le
  calc
    _ ≤ (bd^(n-r)*((bd-ad)/4)^r/|densityMargin ad bd 0|^r)*bd^r *
        Real.cosh ((M+r : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) := by
      simpa only [abs_mul, mul_assoc, mul_left_comm, mul_comm] using h1
    _ ≤ _ := h2
    _ = _ := hid
    _ ≤ _ := h3


/-- Fixed constants bound every actual shrinking interval and every bounded
fine target, before the exterior degree or sample size is chosen. -/
theorem ordinary_count_product_shrunk_abs_bound {n M r R : ℕ}
    (ad bd c0 : ℝ) (ha : 0 < ad)
    (hshrink : ad+(M : ℝ)⁻¹ < bd-(M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0) (hr : 1 ≤ r) (hrR : r ≤ R)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))
    (S : Finset (Fin n)) (hS : S.card = r) :
    |densityCountCoefficient (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) M r n * (∏ i ∈ S, p i)| ≤
      (1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
        Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M) := by
  have ht : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hab : ad < bd := by linarith
  have hap : 0 < ad+(M : ℝ)⁻¹ := by linarith
  have hbp : 0 < bd-(M : ℝ)⁻¹ := hap.trans hshrink
  have he : exteriorTau (((ad+(M : ℝ)⁻¹)+(bd-(M : ℝ)⁻¹))/
      ((bd-(M : ℝ)⁻¹)-(ad+(M : ℝ)⁻¹))) = shrunkDensityExponent ad bd M := by
    rw [exteriorTau_sqrt_ratio _ _ hap hshrink]
    rfl
  have hB : 0 ≤ uniformOrdinaryDensityActivityBase ad bd c0 := by
    unfold uniformOrdinaryDensityActivityBase
    positivity
  have hb := ordinaryDensityActivityBase_shrunk_le ha ht hshrink htau
  have hbn : (bd-(M : ℝ)⁻¹)^n ≤ (1+bd)^n :=
    pow_le_pow_left₀ hbp.le (by linarith) n
  have hBr : (ordinaryDensityActivityBase (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))^r ≤
      (1+uniformOrdinaryDensityActivityBase ad bd c0)^R := by
    have hbase : 0 ≤ ordinaryDensityActivityBase (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) := by
      unfold ordinaryDensityActivityBase
      positivity
    exact (pow_le_pow_left₀ hbase (hb.trans (by linarith)) r).trans
      (pow_le_pow_right₀ (by linarith) hrR)
  have h := ordinary_count_product_abs_bound (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)
    hap hshrink M r hr p hp S hS
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hbn hBr
      (pow_nonneg (by unfold ordinaryDensityActivityBase; positivity) r)
      (pow_nonneg (by linarith) n)) (Real.exp_pos _).le)

def ordinaryAliasResponseConstant (q : ℕ) (C a ρ : ℝ) : ℝ :=
  (2*C^2) * (∑ j : Fin (2*q+2), |responseWeight q j|) * highSeparatedDerivativeBudget a ρ

theorem ordinaryAliasResponseConstant_nonneg (q : ℕ) (C a ρ : ℝ) :
    0 ≤ ordinaryAliasResponseConstant q C a ρ := by
  unfold ordinaryAliasResponseConstant
  exact mul_nonneg (mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _))) (highSeparatedDerivativeBudget_nonneg a ρ)

/-- Uniform pointwise all-count response and selector control. The primitive
nuisance guards hold at this tuple; no norm bound is supplied as a premise. -/
theorem ordinaryFineAliasRawAction_abs_bound_of_chart {d n F M r R : ℕ}
    (ad bd c0 lam L T : ℝ) (haD : 0 < ad)
    (hshrink : ad+(M : ℝ)⁻¹ < bd-(M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0) (hr : 1 ≤ r) (hrR : r ≤ R)
    (q : ℕ) (hn : 1 ≤ n) (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ)
    (hpD : ∀ i, p i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))
    (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) (y : Fin n → Fin 3) :
    |ordinaryFineAliasRawAction (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) lam L T M r q C a V η U p g w c y| ≤
      ((1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
        Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M)) *
      (ordinaryAliasResponseConstant q C a ρ * (n : ℝ)^2 * η^2) *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
          spatialMatrixL1 (globalCardinalBandMatrix (D := F) lam L T (spatialSubsetConfiguration S U)) := by
  unfold ordinaryFineAliasRawAction
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hS : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, S.card = r :=
    fun S hS => (Finset.mem_powersetCard.mp hS).2
  have hterm (S) (hmem : S ∈ (Finset.univ : Finset (Fin n)).powersetCard r) :=
    ordinary_count_product_shrunk_abs_bound ad bd c0 haD hshrink htau hr hrR p hpD S (hS S hmem)
  have hresponse (S : Finset (Fin n)) := high_response_matrix_all_count_bound q hn C a V η ρ
    (lt_of_lt_of_le zero_lt_one hC) ha hη hρ hηρ
    (globalCardinalBandMatrix (D := F) lam L T (spatialSubsetConfiguration S U))
    g w (fun i => highFrameFeature (U i)) c y hc hg hw
    (fun v hv i => highFrameProfile_abs_le_one C hC (U i) (hU i) v hv) hp
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hmem
  have hh := mul_le_mul (hterm S hmem) (hresponse S) (abs_nonneg _)
    (show 0 ≤ (1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
      Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M) by
        have ht : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg M)
        have hbd : 0 < bd := by linarith
        have hab : ad < bd := by linarith
        unfold uniformOrdinaryDensityActivityBase
        positivity)
  simpa only [abs_mul, mul_assoc] using hh.trans_eq (by
    unfold ordinaryAliasResponseConstant highSeparatedDerivativeBudget spatialMatrixL1
    ring)


/-- Jointly varying coefficients and nuisance fields remain genuinely
measurable under the finite product response action. -/
theorem highResponseProduct_spatial_variable_coefficient_measurable {d n F : ℕ}
    (a V η : ℝ) (g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hg : ∀ i, Measurable (fun U => g U i)) (hw : ∀ i, Measurable (fun U => w U i))
    (c : (Fin n → Covariate d) → HighFrameIndex d F → ℝ)
    (hc : ∀ γ, Measurable (fun U => c U γ)) (y : Fin n → Fin 3) :
    Measurable (fun U => highResponseProduct a V η (g U) (w U)
      (fun i => highFrameFeature (U i)) (c U) y) := by
  unfold highResponseProduct
  apply Finset.measurable_prod
  intro i _
  apply ternaryMass_measurable_comp
  unfold coefficientRegression
  exact (hg i).add ((measurable_const.mul (hw i)).mul
    (Finset.measurable_sum _ (fun γ _ => (highFrameFeature_spatial_measurable i γ).mul (hc γ))))

theorem responseMatrixAction_spatial_variable_coefficient_measurable {d n F : ℕ}
    (q : ℕ) (C a V η : ℝ) (g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hg : ∀ i, Measurable (fun U => g U i)) (hw : ∀ i, Measurable (fun U => w U i))
    (A : (Fin n → Covariate d) → HighFrameIndex d F → HighFrameIndex d F → ℝ)
    (hA : ∀ γ δ, Measurable (fun U => A U γ δ))
    (c : (Fin n → Covariate d) → HighFrameIndex d F → ℝ)
    (hc : ∀ γ, Measurable (fun U => c U γ)) (y : Fin n → Fin 3) :
    Measurable (fun U => responseMatrixAction q C (A U) (c U) (fun v =>
      highResponseProduct a V η (g U) (w U) (fun i => highFrameFeature (U i)) v y)) := by
  simp_rw [← highResponseMark_action]
  apply Finset.measurable_sum
  intro h _
  apply Measurable.mul
  · unfold highResponseMarkWeight covarianceWeight
    exact (((hA _ _).const_mul _).mul_const _).mul_const _ |>.const_mul _
  · apply highResponseProduct_spatial_variable_coefficient_measurable a V η g w hg hw
    intro γ
    unfold coefficientReset
    exact (hc γ).const_mul _ |>.add measurable_const

theorem ordinaryFineAliasRawAction_spatial_measurable {d n F : ℕ}
    (ad bd lam L T : ℝ) (hL : 1 ≤ L) (hT : 1 ≤ T) (M r q : ℕ) (C a V η : ℝ)
    (p g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hp : ∀ i, Measurable (fun U => p U i)) (hg : ∀ i, Measurable (fun U => g U i))
    (hw : ∀ i, Measurable (fun U => w U i))
    (c : (Fin n → Covariate d) → HighFrameIndex d F → ℝ)
    (hc : ∀ γ, Measurable (fun U => c U γ)) (y : Fin n → Fin 3) :
    Measurable (fun U => ordinaryFineAliasRawAction ad bd lam L T M r q C a V η U
      (p U) (g U) (w U) (c U) y) := by
  unfold ordinaryFineAliasRawAction
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro S _
  exact (Finset.measurable_prod S (fun i _ => hp i)).mul
    (responseMatrixAction_spatial_variable_coefficient_measurable q C a V η g w hg hw _
      (fun γ δ => ((integrated_cardinal_band_continuous lam hL hT γ δ).measurable).comp
        (spatialSubsetConfiguration_measurable S)) c hc y)

/-- Exact subset lifting of the constructed fine-band matrix envelope. -/
theorem ordinaryFineAliasKernel_sum_square_integrable_and_le {d n F r : ℕ}
    (hd : 5 ≤ d) (hr : 2 ≤ r) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    Integrable (fun U : Fin n → Covariate d =>
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T
          (spatialSubsetConfiguration S U)))^2) (fullSpatialPatchDesign d n) ∧
    (∫ U : Fin n → Covariate d,
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T
          (spatialSubsetConfiguration S U)))^2 ∂fullSpatialPatchDesign d n) ≤
      (n.choose r : ℝ)^2 * (2 : ℝ)^(d*(n-r)) *
        ((r : ℝ)^2*(2 : ℝ)^d*cardinalBandSquareBudget d r L) := by
  let f := fun (S : Finset (Fin n)) (V : Fin S.card → Covariate d) =>
    spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T V)
  have hf (S : Finset (Fin n)) : Measurable (f S) := by
    unfold f spatialMatrixL1
    exact Finset.measurable_sum _ (fun γ _ => Finset.measurable_sum _
      (fun δ _ => (integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT γ δ).measurable.abs))
  have hs (S) (hS : S ∈ (Finset.univ : Finset (Fin n)).powersetCard r) : S.card = r :=
    (Finset.mem_powersetCard.mp hS).2
  have hi (S) (hS : S ∈ (Finset.univ : Finset (Fin n)).powersetCard r) :
      Integrable (fun V => f S V^2) (fullSpatialPatchDesign d S.card) :=
    globalCardinalBandMatrix_square_integrable hd (by rw [hs S hS]; exact hr) hL hT hLT
  constructor
  · have h := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n)
      ((Finset.univ : Finset (Fin n)).powersetCard r)
      (fun S U => f S (spatialSubsetConfiguration S U))
      (fun S _ => (hf S).comp (spatialSubsetConfiguration_measurable S))
      (fun S hS => spatial_subset_square_integrable_enumerated S (f S) (hi S hS))
    simpa only [f, abs_of_nonneg (spatial_matrix_l1_nonnegative _)] using h
  · exact spatial_subset_sum_square_integral_le f _ (fun S _ => hf S) hi
      (fun S hS => by
        have h := globalCardinalBandMatrix_square_integral_le (D := F) hd
          (show 2 ≤ S.card by rw [hs S hS]; exact hr) hL hT hLT
        simpa only [f, hs S hS] using h)


def ordinaryFineAliasSpatialBudget (d n M r R q : ℕ) (ad bd c0 C a ρ η L : ℝ) : ℝ :=
  (((1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
      Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M)) *
    (ordinaryAliasResponseConstant q C a ρ * (n : ℝ)^2 * η^2))^2 *
      ((n.choose r : ℝ)^2 * (2 : ℝ)^(d*(n-r)) *
        ((r : ℝ)^2*(2 : ℝ)^d*cardinalBandSquareBudget d r L))

/-- Actual spatial square-integrability, with all nuisance values allowed to
vary measurably at each spatial tuple. The kernel integral is derived. -/
theorem ordinaryFineAliasRawAction_spatial_square_integrable_and_le {d n F M r R : ℕ}
    (hd : 5 ≤ d) (ad bd c0 L T : ℝ) (haD : 0 < ad)
    (hshrink : ad+(M : ℝ)⁻¹ < bd-(M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0) (hr : 2 ≤ r) (hrR : r ≤ R)
    (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T)
    (q : ℕ) (hn : 1 ≤ n) (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2)
    (p g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hpmeas : ∀ i, Measurable (fun U => p U i))
    (hgmeas : ∀ i, Measurable (fun U => g U i))
    (hwmeas : ∀ i, Measurable (fun U => w U i))
    (c : (Fin n → Covariate d) → HighFrameIndex d F → ℝ)
    (hcmeas : ∀ γ, Measurable (fun U => c U γ))
    (hpD : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i,
      p U i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))
    (hg : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, |g U i| ≤ ρ/2)
    (hw : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, |w U i| ≤ 1)
    (hc : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∑ γ, |c U γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) (y : Fin n → Fin 3) :
    Integrable (fun U => ordinaryFineAliasRawAction (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)
      (spatialInterpolationLambda d) L T M r q C a V η U (p U) (g U) (w U) (c U) y^2)
      (fullSpatialPatchDesign d n) ∧
    (∫ U, ordinaryFineAliasRawAction (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)
      (spatialInterpolationLambda d) L T M r q C a V η U (p U) (g U) (w U) (c U) y^2
      ∂fullSpatialPatchDesign d n) ≤ ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a ρ η L := by
  let lam := spatialInterpolationLambda d
  let A := fun U => ordinaryFineAliasRawAction (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)
    lam L T M r q C a V η U (p U) (g U) (w U) (c U) y
  let H := fun U : Fin n → Covariate d =>
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      spatialMatrixL1 (globalCardinalBandMatrix (D := F) lam L T (spatialSubsetConfiguration S U))
  let K := ((1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
    Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M)) *
      (ordinaryAliasResponseConstant q C a ρ * (n : ℝ)^2 * η^2)
  have hH := ordinaryFineAliasKernel_sum_square_integrable_and_le (F := F) (n := n) hd hr hL hT hLT
  have hm : Measurable A := ordinaryFineAliasRawAction_spatial_measurable _ _ lam L T hL hT
    M r q C a V η p g w hpmeas hgmeas hwmeas c hcmeas y
  have hb : ∀ᵐ U ∂fullSpatialPatchDesign d n, A U^2 ≤ K^2*H U^2 := by
    filter_upwards [fullSpatialPatchDesign_ae_coordinate_bound, hpD, hg, hw, hc] with U hU hpU hgU hwU hcU
    have h := ordinaryFineAliasRawAction_abs_bound_of_chart ad bd c0 lam L T haD hshrink htau
      (by omega) hrR q hn C a V η ρ hC ha hη hρ hηρ U hU (p U) (g U) (w U)
      hpU hgU hwU (c U) hcU hp y
    change |A U| ≤ K*H U at h
    simpa only [sq_abs, mul_pow] using
      (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h)).mpr h
  have hu : Integrable (fun U => K^2*H U^2) (fullSpatialPatchDesign d n) := hH.1.const_mul _
  have hi : Integrable (fun U => A U^2) (fullSpatialPatchDesign d n) :=
    hu.mono' (hm.pow_const 2).aestronglyMeasurable (by
      filter_upwards [hb] with U hU
      simpa only [Real.norm_eq_abs, abs_sq] using hU)
  refine ⟨hi, (integral_mono_ae hi hu hb).trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hH.2 (sq_nonneg K)

/-- The exact binomial, response-polynomial and unused-coordinate factors
are absorbed into one fixed exponential base. -/
theorem ordinary_alias_count_factors_le {d n r : ℕ} {bd : ℝ} (hbd : 0 ≤ bd) :
    ((1+bd)^n)^2 * (n : ℝ)^4 * (n.choose r : ℝ)^2 * (2 : ℝ)^(d*(n-r)) ≤
      (64*(2 : ℝ)^d*(1+bd)^2)^n := by
  have hn : (n : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hc : (n.choose r : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast Nat.choose_le_two_pow n r
  have hn4 : (n : ℝ)^4 ≤ (16 : ℝ)^n := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 4
    convert h using 1 <;> rw [← pow_mul, Nat.mul_comm n 4, pow_mul] <;> norm_num
  have hc2 : (n.choose r : ℝ)^2 ≤ (4 : ℝ)^n := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
    convert h using 1 <;> rw [← pow_mul, Nat.mul_comm n 2, pow_mul] <;> norm_num
  have hv : (2 : ℝ)^(d*(n-r)) ≤ ((2 : ℝ)^d)^n := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left d (Nat.sub_le n r))
  have h := mul_le_mul (mul_le_mul (mul_le_mul (le_refl (((1+bd)^n)^2)) hn4
      (by positivity) (by positivity)) hc2 (by positivity) (by positivity)) hv (by positivity) (by positivity)
  apply h.trans_eq
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_pow, ← mul_pow, ← mul_pow]
  congr 1
  ring


def ordinaryAliasSpatialPrefactor (d q R : ℕ) (ad bd c0 C a ρ : ℝ) : ℝ :=
  ((1+uniformOrdinaryDensityActivityBase ad bd c0)^R)^2 *
    (ordinaryAliasResponseConstant q C a ρ)^2 * lowerAliasSpatialA d R

def ordinaryAliasSpatialCountBase (d : ℕ) (bd : ℝ) : ℝ :=
  64*(2 : ℝ)^d*(1+bd)^2

def ordinaryAliasSpatialResponseBase (d : ℕ) (bd : ℝ) : ℝ :=
  3*ordinaryAliasSpatialCountBase d bd

theorem ordinaryAliasSpatialPrefactor_nonneg (d q R : ℕ) (ad bd c0 C a ρ : ℝ) :
    0 ≤ ordinaryAliasSpatialPrefactor d q R ad bd c0 C a ρ := by
  unfold ordinaryAliasSpatialPrefactor
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (lowerAliasSpatialA_nonneg d R)

/-- Genuine cardinal-band integration and elementary count factors give the
source alias scale, with constants fixed before M,n or nuisance values. -/
theorem ordinaryFineAliasSpatialBudget_source_scale_le {d n M r R : ℕ}
    (hd : 5 ≤ d) (hrR : r ≤ R) {ad bd c0 C a ρ η D K N : ℝ}
    (hbd : 0 ≤ bd) (hD : 0 ≤ D) (hK : 0 ≤ K) (hc0 : 0 ≤ c0)
    (hDK : D ≤ K*M) (hN : 0 < N) (hell : 1 ≤ N*Real.exp (-c0*D))
    (hH : Real.log (1+Real.log N) ≤ M) (q : ℕ) :
    ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a ρ η (N*Real.exp (-c0*D)) ≤
      ordinaryAliasSpatialPrefactor d q R ad bd c0 C a ρ *
        η^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
          Real.exp (lowerAliasSpatialL d R c0 K*M) * (ordinaryAliasSpatialCountBase d bd)^n := by
  have hkernel := cardinalBandSquareBudget_cutoff_le (by omega : 4 ≤ d) hrR
    (Nat.cast_nonneg M) hD hK hc0 hDK hN hell hH
  have hcount := ordinary_alias_count_factors_le (d := d) (n := n) (r := r) hbd
  let P := ((1+uniformOrdinaryDensityActivityBase ad bd c0)^R)^2 *
    (ordinaryAliasResponseConstant q C a ρ)^2 * η^4 * Real.exp (2*shrunkDensityExponent ad bd M*M)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have he : (Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M))^2 =
      Real.exp (2*shrunkDensityExponent ad bd M*M) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hid : ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a ρ η (N*Real.exp (-c0*D)) =
      P * (((1+bd)^n)^2 * (n : ℝ)^4 * (n.choose r : ℝ)^2 * (2 : ℝ)^(d*(n-r))) *
        ((r : ℝ)^2*(2 : ℝ)^d*cardinalBandSquareBudget d r (N*Real.exp (-c0*D))) := by
    unfold ordinaryFineAliasSpatialBudget P
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, he]
    ring
  rw [hid]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hcount hP) hkernel (by
      unfold cardinalBandSquareBudget
      have := cardinalBandDimensionConstant_nonneg d
      have hlog : 0 ≤ 1+Real.log (N*Real.exp (-c0*D)) := by linarith [Real.log_nonneg hell]
      positivity) (by positivity)
  exact hh.trans_eq (by unfold P ordinaryAliasSpatialPrefactor ordinaryAliasSpatialCountBase; ring)

/-- Sum over every actual ternary response, after the full Q^n spatial
integration. The nuisance values and coefficients may vary with the tuple. -/
theorem ordinaryFineAliasRawAction_spatial_response_energy_le {d n F M r R : ℕ}
    (hd : 5 ≤ d) (ad bd c0 D K N T : ℝ) (haD : 0 < ad)
    (hshrink : ad+(M : ℝ)⁻¹ < bd-(M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0) (hr : 2 ≤ r) (hrR : r ≤ R)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hc0 : 0 ≤ c0) (hDK : D ≤ K*M)
    (hN : 0 < N) (hell : 1 ≤ N*Real.exp (-c0*D))
    (hH : Real.log (1+Real.log N) ≤ M) (hLT : N*Real.exp (-c0*D) ≤ T)
    (q : ℕ) (hn : 1 ≤ n) (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2)
    (p g w : (Fin n → Covariate d) → Fin n → ℝ)
    (hpmeas : ∀ i, Measurable (fun U => p U i))
    (hgmeas : ∀ i, Measurable (fun U => g U i))
    (hwmeas : ∀ i, Measurable (fun U => w U i))
    (c : (Fin n → Covariate d) → HighFrameIndex d F → ℝ)
    (hcmeas : ∀ γ, Measurable (fun U => c U γ))
    (hpD : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i,
      p U i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))
    (hg : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, |g U i| ≤ ρ/2)
    (hw : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∀ i, |w U i| ≤ 1)
    (hc : ∀ᵐ U ∂fullSpatialPatchDesign d n, ∑ γ, |c U γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    (∑ y : Fin n → Fin 3, ∫ U,
      ordinaryFineAliasRawAction (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)
        (spatialInterpolationLambda d) (N*Real.exp (-c0*D)) T M r q C a V η U
        (p U) (g U) (w U) (c U) y^2 ∂fullSpatialPatchDesign d n) ≤
      ordinaryAliasSpatialPrefactor d q R ad bd c0 C a ρ *
        η^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
          Real.exp (lowerAliasSpatialL d R c0 K*M) * (ordinaryAliasSpatialResponseBase d bd)^n := by
  have hbd : 0 ≤ bd := by
    have ht : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg M)
    linarith
  have hT : 1 ≤ T := hell.trans hLT
  have hb := ordinaryFineAliasSpatialBudget_source_scale_le (n := n) (M := M) hd hrR hbd hD hK hc0
    hDK hN hell hH q (ad := ad) (C := C) (a := a) (ρ := ρ) (η := η)
  have hterm (y : Fin n → Fin 3) :=
    (ordinaryFineAliasRawAction_spatial_square_integrable_and_le hd ad bd c0 _ T haD hshrink htau
      hr hrR hell hT hLT q hn C a V η ρ hC ha hη hρ hηρ p g w hpmeas hgmeas hwmeas
      c hcmeas hpD hg hw hc hp y).2.trans hb
  have hs := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (Fin n → Fin 3))) => hterm y)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat] at hs
  exact hs.trans_eq (by unfold ordinaryAliasSpatialResponseBase; rw [mul_pow]; ring)

end NearlyMinimax
