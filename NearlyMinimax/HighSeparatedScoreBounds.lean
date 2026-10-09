module

public import NearlyMinimax.HighSeparatedScores
public import NearlyMinimax.HighCenteredMark


@[expose] public section

/-! Bounds for the actual signed separated density/response row.  The local
budget is the total variation of its constructed signed packet, rather than
an assumed bound for a score action. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]

def highSeparatedDerivativeBudget (a ρ : ℝ) : ℝ :=
  4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2)

theorem highSeparatedDerivativeBudget_nonneg (a ρ : ℝ) :
    0 ≤ highSeparatedDerivativeBudget a ρ := by
  unfold highSeparatedDerivativeBudget
  positivity

theorem highPacketMarkMass_eq_cost (σ : Measure Z) [IsFiniteMeasure σ]
    (ad bd : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) :
    highPacketMarkMass σ ad bd m r D q C A =
      (∑ h : HighDensityMarkIndex m r D, |densityPacketWeight ad bd m r D h|) *
        (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2) *
          ∫ ζ, separatedMatrixCost A ζ ∂σ := by
  rw [highPacketMarkMass_eq_variation σ ad bd m r D q C A hA hcost,
    highPacketSignedMeasure_totalVariation σ ad bd m r D q C A hA hcost]

theorem highIntegratedResponseAction_abs_bound_variation {n : ℕ}
    (σ : Measure Z) [IsFiniteMeasure σ] (ad bd : ℝ) (m r D q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2) (hpPlus : 0 ≤ pPlus)
    (A : Z → ι → ι → ℝ)
    (reset : Z → ℝ → (Fin r → ℝ) → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hReset : ∀ z ε i, Measurable (fun ζ => reset ζ z ε i))
    (hBound : ∀ ζ (h : HighDensityMarkIndex m r D) i,
      |reset ζ (densityPacketAtom ad bd m r D h).1 (densityPacketAtom ad bd m r D h).2 i| ≤ pPlus)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u)
    (y : Fin n → Fin 3) :
    |highIntegratedResponseAction σ q C a V η
      (fun _ => densityPacketWeight ad bd m r D) (fun ζ _ => A ζ)
      (fun ζ h => reset ζ (densityPacketAtom ad bd m r D h).1
        (densityPacketAtom ad bd m r D h).2) g w φ c y| ≤
      pPlus ^ n * highSeparatedDerivativeBudget a ρ * (n : ℝ) ^ 2 * η ^ 2 *
        highPacketMarkMass σ ad bd m r D q C A := by
  let K : ℝ := pPlus ^ n * highSeparatedDerivativeBudget a ρ * (n : ℝ) ^ 2 * η ^ 2 *
    (∑ h : HighDensityMarkIndex m r D, |densityPacketWeight ad bd m r D h|) *
      (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2)
  have hi := high_separated_density_response_action_integrable σ q C
    (densityPacketWeight ad bd m r D) A
    (fun ζ h => reset ζ (densityPacketAtom ad bd m r D h).1
      (densityPacketAtom ad bd m r D h).2) c
    (fun v => highResponseProduct a V η g w φ v y) hA hcost
    (fun h i => hReset _ _ i) pPlus hpPlus hBound
  have hb (ζ : Z) :
      |highDensityResponseAction q C (densityPacketWeight ad bd m r D)
        (fun _ => A ζ) c
        (fun h => ∏ i, reset ζ (densityPacketAtom ad bd m r D h).1
          (densityPacketAtom ad bd m r D h).2 i)
        (fun v => highResponseProduct a V η g w φ v y)| ≤ K * separatedMatrixCost A ζ := by
    apply (high_density_response_product_abs_bound q hn C a V η ρ pPlus hC ha hη hρ
      hηρ hpPlus (densityPacketWeight ad bd m r D) (fun _ => A ζ)
      (fun h => reset ζ (densityPacketAtom ad bd m r D h).1
        (densityPacketAtom ad bd m r D h).2) g w φ c hc hg hw hφ hp (hBound ζ) y).trans_eq
    dsimp [highResponsePacketCost, highLocalDerivativeConstant, K,
      highSeparatedDerivativeBudget, separatedMatrixCost]
    rw [← Finset.sum_mul]
    ring
  unfold highIntegratedResponseAction
  apply abs_integral_le_integral_abs.trans
  apply (integral_mono hi.abs (hcost.const_mul K) hb).trans_eq
  rw [integral_const_mul, highPacketMarkMass_eq_cost σ ad bd m r D q C A hA hcost]
  dsimp [K]
  ring

theorem high_response_variance_correction_abs_bound {n : ℕ} (hn : 1 ≤ n)
    (a V η pPlus : ℝ) (ha : 0 < a) (hpPlus : 0 ≤ pPlus)
    (p g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hw : ∀ i, |w i| ≤ 1) (hIncoming : ∀ i, |p i| ≤ pPlus)
    (hp : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w φ c i) V u)
    (y : Fin n → Fin 3) :
    |η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i| ≤
      pPlus ^ n * (1 / a ^ 2) * (n : ℝ) ^ 2 * η ^ 2 := by
  have hvar : |∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i| ≤
      (n : ℝ) / a ^ 2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : Fin n, 1 / a ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        have hwsq : (w i) ^ 2 ≤ 1 := by
          simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hw i) 2
        exact (mul_le_mul hwsq
          (high_response_variance_term_abs_bound a V η ha g w φ c hp y i)
          (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
      _ = _ := by simp [div_eq_mul_inv]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn1]
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg η)]
  calc
    _ ≤ η ^ 2 * pPlus ^ n * ((n : ℝ) / a ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        (finite_density_product_abs_bound p pPlus hpPlus hIncoming) (sq_nonneg η))
        hvar (abs_nonneg _) (by positivity)
    _ ≤ η ^ 2 * pPlus ^ n * ((n : ℝ) ^ 2 / a ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnsq (sq_nonneg a)) (by positivity)
    _ = _ := by ring

theorem highSeparatedXiScore_abs_bound_variation {n : ℕ}
    (σ : Measure Z) [IsFiniteMeasure σ] (ad bd : ℝ) (m r D q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus pMinus cMass : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2) (hpPlus : 0 ≤ pPlus)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass)
    (A : Z → ι → ι → ℝ) (p : Fin n → ℝ)
    (reset : Z → ℝ → (Fin r → ℝ) → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hReset : ∀ z ε i, Measurable (fun ζ => reset ζ z ε i))
    (hBound : ∀ ζ (h : HighDensityMarkIndex m r D) i,
      |reset ζ (densityPacketAtom ad bd m r D h).1 (densityPacketAtom ad bd m r D h).2 i| ≤ pPlus)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u)
    (hIncoming : ∀ i, |p i| ≤ pPlus) (hIncomingLower : ∀ i, pMinus ≤ p i)
    (hResponseLower : ∀ i u, cMass ≤ ternaryMass a (coefficientRegression η g w φ c i) V u)
    (y : Fin n → Fin 3) :
    |highSeparatedXiScore σ ad bd m r D q C a V η A p reset g w φ c y| ≤
      (pPlus / (pMinus * cMass)) ^ n *
        (highSeparatedDerivativeBudget a ρ * highPacketMarkMass σ ad bd m r D q C A +
          1 / a ^ 2) * (n : ℝ) ^ 2 * η ^ 2 := by
  rw [highSeparatedXiScore_eq_integrated σ ad bd m r D q C a V η pPlus hpPlus
    A p reset g w φ c hA hcost hReset hBound]
  have hP0 : 0 < ∏ i, p i :=
    Finset.prod_pos (fun i _ => hpMinus.trans_le (hIncomingLower i))
  have hH0 : 0 < highResponseProduct a V η g w φ c y :=
    Finset.prod_pos (fun i _ => hcMass.trans_le (hResponseLower i (y i)))
  have hden0 := mul_pos hP0 hH0
  have hPLower : pMinus ^ n ≤ ∏ i, p i := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod₀ (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hpMinus.le)
        (fun i _ => hIncomingLower i)
  have hHLower : cMass ^ n ≤ highResponseProduct a V η g w φ c y := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, highResponseProduct] using
      Finset.prod_le_prod₀ (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hcMass.le)
        (fun i _ => hResponseLower i (y i))
  have hdenLower : (pMinus * cMass) ^ n ≤
      (∏ i, p i) * highResponseProduct a V η g w φ c y := by
    rw [mul_pow]
    exact mul_le_mul hPLower hHLower (pow_nonneg hcMass.le _) hP0.le
  have hdenLower0 : 0 < (pMinus * cMass) ^ n := pow_pos (mul_pos hpMinus hcMass) _
  have hM0 : 0 ≤ highPacketMarkMass σ ad bd m r D q C A := signedMarkMass_nonneg _ _
  have hK0 := highSeparatedDerivativeBudget_nonneg a ρ
  have haction := highIntegratedResponseAction_abs_bound_variation σ ad bd m r D q hn
    C a V η ρ pPlus hC ha hη hρ hηρ hpPlus A reset g w φ c hA hcost hReset hBound
    hc hg hw hφ hp y
  have hvar := high_response_variance_correction_abs_bound hn a V η pPlus ha hpPlus
    p g w φ c hw hIncoming (fun i u => (hcMass.trans_le (hResponseLower i u)).le) y
  have hnum := (abs_sub _ _).trans (add_le_add haction hvar)
  unfold highIntegratedLocalScore
  rw [abs_div, abs_of_nonneg hden0.le]
  calc
    _ ≤ (pPlus ^ n * highSeparatedDerivativeBudget a ρ * (n : ℝ) ^ 2 * η ^ 2 *
        highPacketMarkMass σ ad bd m r D q C A +
        pPlus ^ n * (1 / a ^ 2) * (n : ℝ) ^ 2 * η ^ 2) /
        ((∏ i, p i) * highResponseProduct a V η g w φ c y) :=
      div_le_div_of_nonneg_right hnum hden0.le
    _ ≤ (pPlus ^ n * highSeparatedDerivativeBudget a ρ * (n : ℝ) ^ 2 * η ^ 2 *
        highPacketMarkMass σ ad bd m r D q C A +
        pPlus ^ n * (1 / a ^ 2) * (n : ℝ) ^ 2 * η ^ 2) /
        ((pMinus * cMass) ^ n) :=
      div_le_div_of_nonneg_left (by positivity) hdenLower0 hdenLower
    _ = _ := by simp only [div_pow]; ring

def highSeparatedScoreExponentialConstant (a ρ pPlus pMinus cMass : ℝ) : ℝ :=
  4 * max 1 (pPlus / (pMinus * cMass)) *
    max 1 (highSeparatedDerivativeBudget a ρ + 1 / a ^ 2)

theorem highSeparatedScoreExponentialConstant_pos (a ρ pPlus pMinus cMass : ℝ) :
    0 < highSeparatedScoreExponentialConstant a ρ pPlus pMinus cMass := by
  unfold highSeparatedScoreExponentialConstant
  exact mul_pos (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))

theorem highSeparated_score_budget_absorb (n : ℕ) (hn : 1 ≤ n)
    (a ρ pPlus pMinus cMass η B : ℝ) (hpPlus : 0 ≤ pPlus)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hB : 0 ≤ B) :
    (pPlus / (pMinus * cMass)) ^ n *
      (highSeparatedDerivativeBudget a ρ * B + 1 / a ^ 2) * (n : ℝ) ^ 2 * η ^ 2 ≤
      (highSeparatedScoreExponentialConstant a ρ pPlus pMinus cMass) ^ n *
        η ^ 2 * (B + 1) := by
  let R : ℝ := max 1 (pPlus / (pMinus * cMass))
  let K : ℝ := max 1 (highSeparatedDerivativeBudget a ρ + 1 / a ^ 2)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hK1 : 1 ≤ K := le_max_left _ _
  have hder := highSeparatedDerivativeBudget_nonneg a ρ
  have hK : highSeparatedDerivativeBudget a ρ * B + 1 / a ^ 2 ≤ K * (B + 1) := by
    have hk : highSeparatedDerivativeBudget a ρ + 1 / a ^ 2 ≤ K := le_max_right _ _
    have hz : 0 ≤ 1 / a ^ 2 := by positivity
    nlinarith only [hk, hB, hder, hz, mul_nonneg hB hz]
  have hnNat := Nat.two_mul_sq_add_one_le_two_pow_two_mul n
  have hnReal : (2 : ℝ) * (n : ℝ) ^ 2 + 1 ≤ 2 ^ (2 * n) := by exact_mod_cast hnNat
  have hnsq : (n : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
    have he : (2 : ℝ) ^ (2 * n) = (4 : ℝ) ^ n := by rw [pow_mul]; norm_num
    rw [he] at hnReal
    nlinarith only [hnReal, sq_nonneg (n : ℝ)]
  have hRpow : (pPlus / (pMinus * cMass)) ^ n ≤ R ^ n :=
    pow_le_pow_left₀ (div_nonneg hpPlus (mul_pos hpMinus hcMass).le) (le_max_right _ _) _
  have hKpow : K ≤ K ^ n := le_self_pow₀ hK1 (by omega)
  calc
    _ ≤ (R ^ n * (K * (B + 1))) * (4 : ℝ) ^ n * η ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul hRpow hK (by positivity) (by positivity)) hnsq
          (sq_nonneg _) (by positivity)) (sq_nonneg η)
    _ ≤ (R ^ n * (K ^ n * (B + 1))) * (4 : ℝ) ^ n * η ^ 2 := by
      gcongr
    _ = _ := by
      dsimp [highSeparatedScoreExponentialConstant, R, K]
      simp only [mul_pow]
      ring

theorem highSeparatedXiScore_exponential_bound {n : ℕ}
    (σ : Measure Z) [IsFiniteMeasure σ] (ad bd : ℝ) (m r D q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus pMinus cMass : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2) (hpPlus : 0 ≤ pPlus)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass)
    (A : Z → ι → ι → ℝ) (p : Fin n → ℝ)
    (reset : Z → ℝ → (Fin r → ℝ) → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hReset : ∀ z ε i, Measurable (fun ζ => reset ζ z ε i))
    (hBound : ∀ ζ (h : HighDensityMarkIndex m r D) i,
      |reset ζ (densityPacketAtom ad bd m r D h).1 (densityPacketAtom ad bd m r D h).2 i| ≤ pPlus)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u)
    (hIncoming : ∀ i, |p i| ≤ pPlus) (hIncomingLower : ∀ i, pMinus ≤ p i)
    (hResponseLower : ∀ i u, cMass ≤ ternaryMass a (coefficientRegression η g w φ c i) V u)
    (y : Fin n → Fin 3) :
    |highSeparatedXiScore σ ad bd m r D q C a V η A p reset g w φ c y| ≤
      (highSeparatedScoreExponentialConstant a ρ pPlus pMinus cMass) ^ n *
        η ^ 2 * (highPacketMarkMass σ ad bd m r D q C A + 1) :=
  (highSeparatedXiScore_abs_bound_variation σ ad bd m r D q hn C a V η ρ pPlus pMinus cMass
    hC ha hη hρ hηρ hpPlus hpMinus hcMass A p reset g w φ c hA hcost hReset hBound
    hc hg hw hφ hp hIncoming hIncomingLower hResponseLower y).trans
      (highSeparated_score_budget_absorb n hn a ρ pPlus pMinus cMass η
        (highPacketMarkMass σ ad bd m r D q C A) hpPlus hpMinus hcMass (signedMarkMass_nonneg _ _))

theorem highSeparatedXiScore_exponential_energy_bound {n : ℕ}
    (σ : Measure Z) [IsFiniteMeasure σ] (ad bd : ℝ) (m r D q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus pMinus cMass : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2) (hpPlus : 0 ≤ pPlus)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass)
    (A : Z → ι → ι → ℝ) (p : Fin n → ℝ)
    (reset : Z → ℝ → (Fin r → ℝ) → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hReset : ∀ z ε i, Measurable (fun ζ => reset ζ z ε i))
    (hBound : ∀ ζ (h : HighDensityMarkIndex m r D) i,
      |reset ζ (densityPacketAtom ad bd m r D h).1 (densityPacketAtom ad bd m r D h).2 i| ≤ pPlus)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u)
    (hIncoming : ∀ i, |p i| ≤ pPlus) (hIncomingLower : ∀ i, pMinus ≤ p i)
    (hResponseLower : ∀ i u, cMass ≤ ternaryMass a (coefficientRegression η g w φ c i) V u) :
    (∑ y : Fin n → Fin 3, highResponseProduct a V η g w φ c y *
      (highSeparatedXiScore σ ad bd m r D q C a V η A p reset g w φ c y) ^ 2) ≤
      (highSeparatedScoreExponentialConstant a ρ pPlus pMinus cMass) ^ (2 * n) *
        η ^ 4 * (highPacketMarkMass σ ad bd m r D q C A + 1) ^ 2 := by
  let B := (highSeparatedScoreExponentialConstant a ρ pPlus pMinus cMass) ^ n *
    η ^ 2 * (highPacketMarkMass σ ad bd m r D q C A + 1)
  have hbound (y : Fin n → Fin 3) :
      |highSeparatedXiScore σ ad bd m r D q C a V η A p reset g w φ c y| ≤ B :=
    highSeparatedXiScore_exponential_bound σ ad bd m r D q hn C a V η ρ pPlus pMinus cMass
      hC ha hη hρ hηρ hpPlus hpMinus hcMass A p reset g w φ c hA hcost hReset hBound
      hc hg hw hφ hp hIncoming hIncomingLower hResponseLower y
  calc
    _ ≤ ∑ y : Fin n → Fin 3, highResponseProduct a V η g w φ c y * B ^ 2 := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _
        (Finset.prod_nonneg (fun i _ => (hcMass.trans_le (hResponseLower i (y i))).le))
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hbound y) 2
    _ = B ^ 2 := by rw [← Finset.sum_mul, high_response_product_normalized a V η ha.ne', one_mul]
    _ = _ := by
      dsimp [B]
      simp only [mul_pow, ← pow_mul]
      rw [Nat.mul_comm n 2]

theorem highSeparatedXiScore_zero_count
    (σ : Measure Z) [IsFiniteMeasure σ] (ad bd : ℝ) (m r D q : ℕ)
    (C a V η : ℝ) (A : Z → ι → ι → ℝ) (p : Fin 0 → ℝ)
    (reset : Z → ℝ → (Fin r → ℝ) → Fin 0 → ℝ)
    (g w : Fin 0 → ℝ) (φ : Fin 0 → ι → ℝ) (c : ι → ℝ)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (y : Fin 0 → Fin 3) :
    highSeparatedXiScore σ ad bd m r D q C a V η A p reset g w φ c y = 0 := by
  have h := highPacketSignedMeasure_conditional_zero_mass σ ad bd m r D q C A hA hcost
    c (fun _ _ _ => 1) (by intro z ε; exact measurable_const) 1 (by norm_num)
    (by intro ζ h; norm_num)
  simpa [highSeparatedXiScore, highResponseProduct] using h

end NearlyMinimax
