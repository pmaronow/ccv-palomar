module

public import NearlyMinimax.FinePairScoreBounds
public import NearlyMinimax.HighFrameLocalBounds
public import NearlyMinimax.CardinalGlobalDefectL2
public import NearlyMinimax.CardinalGlobalBandL2


@[expose] public section

/-! Raw numerator of the genuine ordinary cardinal packet. Its alias and
Taylor pieces are evaluated before a likelihood denominator is introduced. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def highCardinalRawNumerator {d n F : ℕ} (ad bd lam T : ℝ) (m D q : ℕ)
    (C a V η : ℝ) (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) : ℝ :=
  (∫ᵛ e, highPacketObservable ad bd m n D q C c
    (fun ζ z eps => ∏ i, highCardinalDensityReset ad bd lam U p ζ z eps i)
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) e
    ∂<•highPacketSignedMeasure (cardinalSeparatedMeasure d n T) ad bd m n D q C
      (cardinalSeparatedAmplitude lam)) -
    η^2 * (∏ i, p i) * ∑ i, (w i)^2 *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i

theorem highCardinalRawNumerator_eq_alias_defect {d n F : ℕ}
    (ad bd lam : ℝ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (C a V η : ℝ) (hC : C ≠ 0)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y =
      η^2 * (∏ i, p i) * ∑ i, (w i)^2 * (integratedCardinalWeight lam T U i-1) *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i +
      (∏ i, p i) * highResponseDefect q C a V η (integratedCardinalMatrix lam T U)
        g w (fun i => highFrameFeature (U i)) c y := by
  letI := cardinal_separated_measure_finite d n hT
  have hm (z : ℝ) (eps : Fin n → ℝ) (i : Fin n) :
      Measurable (fun ζ => highCardinalDensityReset ad bd lam U p ζ z eps i) := by
    unfold highCardinalDensityReset localDensityReset
    exact (Finset.measurable_fun_sum _ (fun l _ =>
      (cardinal_separated_factor_measurable lam l (U i)).const_mul (eps l))).const_mul _ |>.const_add z
  have hb (ζ : CardinalSeparatedMark d n) (e : HighDensityMarkIndex m n D) (i : Fin n) :
      |highCardinalDensityReset ad bd lam U p ζ (densityPacketAtom ad bd m n D e).1
        (densityPacketAtom ad bd m n D e).2 i| ≤ bd := by
    have he := densityPacketAtom_mem ad bd hab.le m n D e
    have h := localDensityReset_mem_interval ad bd haD hab n hn _ he.1 _ he.2 p
      (fun i l => cardinalSeparatedFactor lam ζ l (U i)) i (hp i)
      (fun l => cardinal_separated_factor_abs_le_one lam ζ l (U i) (hU i))
    change |localDensityReset ad bd n _ _ p _ i| ≤ _
    rw [abs_of_nonneg (haD.le.trans h.1)]
    exact h.2
  unfold highCardinalRawNumerator
  rw [highPacketSignedMeasure_factor_integral _ ad bd m n D q C _
    (cardinal_separated_amplitude_measurable lam) (cardinal_separated_cost_integrable lam hT) c _
    (fun z eps => Finset.measurable_fun_prod _ (fun i _ => hm z eps i))
    (bd^n) (pow_nonneg (haD.trans hab).le n)
    (fun ζ e => finite_density_product_abs_bound _ bd (haD.trans hab).le (hb ζ e))
    _ (finePairResponseAtomBound q C c _) (finePairResponseAtomBound_le q C c _)]
  rw [high_cardinal_packet_action_exact ad bd lam haD hab hlam hT m D q hn hnm hnD C U hU p c,
    integrated_cardinal_response_heat hnF q C a V η lam T hC hT U g w c y]
  simp only [mul_sub, sub_mul, mul_one, Finset.sum_sub_distrib]
  ring

theorem high_cardinal_alias_abs_bound {d n F : ℕ} (lam T a V η bd : ℝ)
    (hlam : 0 ≤ lam) (ha : 0 < a) (hbd : 0 ≤ bd)
    (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (hp : ∀ i, |p i| ≤ bd) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ)
    (hMass : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c i) V u)
    (y : Fin n → Fin 3) :
    |η^2 * (∏ i, p i) * ∑ i, (w i)^2 * (integratedCardinalWeight lam T U i-1) *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i| ≤
      (η^2 * bd^n / a^2) * ∑ i, cardinalWeightDefect i lam T U := by
  have hterm (i : Fin n) :
      |(w i)^2 * (integratedCardinalWeight lam T U i-1) *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i| ≤
      cardinalWeightDefect i lam T U * (1/a^2) := by
    have hd := cardinalWeightDefect_mem_unit i hlam T U
    have hw2 : (w i)^2 ≤ 1 := by simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr (hw i)
    have hv := high_response_variance_term_abs_bound a V η ha g w (fun i => highFrameFeature (U i)) c hMass y i
    rw [abs_mul, abs_mul, abs_sq, abs_sub_comm]
    change (w i)^2 * |cardinalWeightDefect i lam T U| *
      |highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i| ≤ _
    rw [abs_of_nonneg hd.1]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right hw2 hd.1) hv (abs_nonneg _)
      (by simpa only [one_mul] using hd.1)).trans_eq (by ring)
  have hsum : |∑ i, (w i)^2 * (integratedCardinalWeight lam T U i-1) *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i| ≤
      ∑ i, cardinalWeightDefect i lam T U * (1/a^2) :=
    (Finset.abs_sum_le_sum_abs _ Finset.univ).trans (Finset.sum_le_sum (fun i _ => hterm i))
  rw [abs_mul, abs_mul, abs_sq]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left (finite_density_product_abs_bound p bd hbd hp)
    (sq_nonneg η)) hsum (abs_nonneg _) (mul_nonneg (sq_nonneg η) (pow_nonneg hbd n))
  exact hh.trans_eq (by rw [← Finset.sum_mul]; ring)

def cardinalRawAliasCoefficient (n : ℕ) (bd a η : ℝ) : ℝ := η^2 * bd^n / a^2

def cardinalRawTaylorCoefficient (n q : ℕ) (bd C a ρ η : ℝ) : ℝ :=
  bd^n * highResponseRemainderConstant q C a ρ * (n : ℝ)^(2*q+2) * η^(2*q+2)

theorem highCardinalRawNumerator_abs_bound_of_chart {d n F : ℕ}
    (ad bd lam : ℝ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (hq : 1 ≤ q)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) (y : Fin n → Fin 3) :
    |highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y| ≤
      cardinalRawAliasCoefficient n bd a η * (∑ i, cardinalWeightDefect i lam T U) +
        cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U) := by
  have hCpos := lt_of_lt_of_le zero_lt_one hC
  have hpabs (i : Fin n) : |p i| ≤ bd := by
    rw [abs_of_pos (haD.trans_le (hpD i).1)]
    exact (hpD i).2
  have hMass (i : Fin n) (u : Fin 3) :
      0 ≤ ternaryMass a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c i) V u :=
    hp _ (highFrameCoefficientRegression_abs_le C η ρ hC hη hηρ U hU g w hg hw c hc i) u
  have hAlias := high_cardinal_alias_abs_bound lam T a V η bd hlam ha (haD.trans hab).le
    U p g w hpabs hw c hMass y
  have hRem := high_response_defect_abs_bound q hq C a V η ρ hCpos ha hη hρ hηρ
    (integratedCardinalMatrix lam T U) g w (fun i => highFrameFeature (U i)) c y hc hg hw
    (fun v hv i => highFrameProfile_abs_le_one C hC (U i) (hU i) v hv) hp
  have hTaylor : |(∏ i, p i) * highResponseDefect q C a V η (integratedCardinalMatrix lam T U)
      g w (fun i => highFrameFeature (U i)) c y| ≤
      cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U) := by
    rw [abs_mul]
    have hh := mul_le_mul (finite_density_product_abs_bound p bd (haD.trans hab).le hpabs) hRem
      (abs_nonneg _) (pow_nonneg (haD.trans hab).le n)
    exact hh.trans_eq (by unfold cardinalRawTaylorCoefficient spatialMatrixL1; ring)
  rw [highCardinalRawNumerator_eq_alias_defect ad bd lam haD hab hlam hT m D q hn hnm hnD hnF
    C a V η hCpos.ne' U hU p g w hpD c y]
  exact (abs_add_le _ _).trans (add_le_add hAlias hTaylor)

theorem highCardinalRawNumerator_square_bound_of_chart {d n F : ℕ}
    (ad bd lam : ℝ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (hq : 1 ≤ q)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) (y : Fin n → Fin 3) :
    highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y ^ 2 ≤
      2 * cardinalRawAliasCoefficient n bd a η ^ 2 * (∑ i, cardinalWeightDefect i lam T U)^2 +
      2 * cardinalRawTaylorCoefficient n q bd C a ρ η ^ 2 *
        spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U)^2 := by
  have h := highCardinalRawNumerator_abs_bound_of_chart ad bd lam haD hab hlam hT m D q
    hn hnm hnD hnF hq C a V η ρ hC ha hη hρ hηρ U hU p g w hpD hg hw c hc hp y
  have hsum : 0 ≤ ∑ i, cardinalWeightDefect i lam T U :=
    Finset.sum_nonneg (fun i _ => (cardinalWeightDefect_mem_unit i hlam T U).1)
  have hbd : 0 ≤ bd := (haD.trans hab).le
  have hA : 0 ≤ cardinalRawAliasCoefficient n bd a η := by
    unfold cardinalRawAliasCoefficient
    positivity
  have hB : 0 ≤ cardinalRawTaylorCoefficient n q bd C a ρ η := by
    unfold cardinalRawTaylorCoefficient highResponseRemainderConstant
    have hDer : 0 ≤ highResponseDerivativeBudget a ρ :=
      zero_le_one.trans (highResponseDerivativeBudget_guards a ρ).1
    positivity
  have hM : 0 ≤ spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U) := by
    unfold spatialMatrixL1
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hh := (sq_le_sq₀ (abs_nonneg _) (add_nonneg (mul_nonneg hA hsum) (mul_nonneg hB hM))).mpr h
  rw [sq_abs] at hh
  nlinarith only [hh, sq_nonneg (cardinalRawAliasCoefficient n bd a η * (∑ i, cardinalWeightDefect i lam T U) -
    cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U))]

theorem highCardinalRawNumerator_singleton_zero {d F : ℕ}
    (ad bd lam : ℝ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hm : 1 ≤ m) (hD : 1 ≤ D) (hF : 1 ≤ F)
    (hq : 1 ≤ q) (C a V η : ℝ) (hC : C ≠ 0)
    (U : Fin 1 → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin 1 → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (y : Fin 1 → Fin 3) :
    highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y = 0 := by
  rw [highCardinalRawNumerator_eq_alias_defect ad bd lam haD hab hlam hT m D q le_rfl hm hD hF
    C a V η hC U hU p g w hpD c y]
  simp only [integrated_cardinal_weight_singleton lam T hT U, sub_self, mul_zero, zero_mul,
    Finset.sum_const_zero, high_response_defect_zero q hq, add_zero]

end NearlyMinimax
