module

public import NearlyMinimax.HighSeparatedScoreBounds
public import NearlyMinimax.HighUnionScore


@[expose] public section

/-! The all-count clause of the local-operator lemma for an arbitrary finite
signed measure, rather than only the constructed tensor rows. Conditional
affine annihilation removes the actual first-order Taylor polynomial. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

section Taylor
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coefficient of the affine response Taylor polynomial at the zero
coefficient state. The frame dimension is absent from its remainder bound. -/
def localResponseLinearCoefficient {n : ℕ} (a V η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (y : Fin n → Fin 3) (γ : ι) : ℝ :=
  ∑ i, (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
    ternaryMass a (g j) V (y j)) * (η * w i * φ i γ * ternaryMeanDerivative a (g i) (y i))

omit [DecidableEq ι] in
theorem local_response_affine_remainder {n : ℕ} (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ / 2) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ i, |∑ γ, φ i γ * v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
    (v : ι → ℝ) (hv : ∑ γ, |v γ| ≤ C⁻¹) (y : Fin n → Fin 3) :
    |highResponseProduct a V η g w φ v y - (∏ i, ternaryMass a (g i) V (y i)) -
      ∑ γ, localResponseLinearCoefficient a V η g w φ y γ * v γ| ≤
      highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2 := by
  let δ : Fin n → ℝ := fun i => η * w i * ∑ γ, φ i γ * v γ
  let H : Fin n → ℝ → ℝ := fun i z => ternaryMass a (g i + z * δ i) V (y i)
  let D : Fin n → ℝ → ℝ := fun i z => δ i * ternaryMeanDerivative a (g i + z * δ i) (y i)
  let E : Fin n → ℝ → ℝ := fun i _ => (δ i)^2 * ternaryMeanSecondDerivative a (y i)
  let A := (2 * ρ + a) / a^2
  let S := 2 / a^2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hδ (i : Fin n) : |δ i| ≤ η := by
    dsimp [δ]
    rw [abs_mul, abs_mul, abs_of_nonneg hη]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (hw i) hη) (hφ v hv i)
      (abs_nonneg _) (by simpa using hη)).trans_eq (by ring)
  have hf (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (i : Fin n) : |g i + z * δ i| ≤ ρ := by
    have hzabs : |z| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
    have hterm : |z * δ i| ≤ η := by
      rw [abs_mul]
      exact (mul_le_mul hzabs (hδ i) (abs_nonneg _) (by norm_num)).trans_eq (one_mul η)
    exact (abs_add_le _ _).trans (by linarith [hg i])
  have hH (i : Fin n) (z : ℝ) : HasDerivAt (H i) (D i z) z := by
    have h := (ternary_hasDerivAt_mean a (g i + z * δ i) V (y i)).comp z
      (((hasDerivAt_id z).mul_const (δ i)).const_add (g i))
    exact h.congr_deriv (by dsimp [D]; ring)
  have hD (i : Fin n) (z : ℝ) : HasDerivAt (D i) (E i z) z := by
    have h := ((ternary_hasDerivAt_mean_derivative a (g i + z * δ i) (y i)).comp z
      (((hasDerivAt_id z).mul_const (δ i)).const_add (g i))).const_mul (δ i)
    exact h.congr_deriv (by dsimp [E]; ring)
  have hHbound (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (i : Fin n) : |H i z| ≤ 1 := by
    rw [abs_of_nonneg (hp _ (hf z hz i) (y i))]
    exact ternary_mass_le_one a _ V ha.ne' (hp _ (hf z hz i)) (y i)
  have hDbound (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (i : Fin n) : |D i z| ≤ 2 * η * A := by
    rw [abs_mul]
    exact mul_le_mul ((hδ i).trans (by linarith))
      (ternary_mean_derivative_abs_bound a _ ρ ha hρ (hf z hz i) (y i))
      (abs_nonneg _) (by positivity)
  have hEbound (z : ℝ) (i : Fin n) : |E i z| ≤ 4 * η^2 * S := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hs : (δ i)^2 ≤ (2 * η)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ((hδ i).trans (by linarith)) 2
    have h := mul_le_mul hs (ternary_mean_second_derivative_abs_bound a ha (y i))
      (abs_nonneg _) (by positivity : 0 ≤ (2 * η)^2)
    simpa only [S] using h.trans_eq (by ring)
  have hsecond (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
      |finiteProductSecond Finset.univ H D E z| ≤
        highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2 := by
    have h := finite_product_second_abs_bound Finset.univ H D E z (2 * η * A) (4 * η^2 * S)
      (by positivity) (by positivity) (fun i _ => hHbound z hz i)
      (fun i _ => hDbound z hz i) (fun i _ => hEbound z i)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    apply h.trans
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnn : 0 ≤ (n : ℝ)^2 - n := by nlinarith
    have hmore := mul_nonneg hnn (mul_nonneg (sq_nonneg η) hS)
    dsimp [highSeparatedDerivativeBudget, A, S] at *
    nlinarith
  have hTaylor := affine_line_remainder_abs_bound (fun z => ∏ i, H i z)
    (finiteProductFirst Finset.univ H D) (finiteProductSecond Finset.univ H D E)
    (highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2)
    (mul_nonneg (mul_nonneg (highSeparatedDerivativeBudget_nonneg a ρ) (sq_nonneg _)) (sq_nonneg _))
    (fun z _ => finite_product_hasDerivAt Finset.univ H D z (fun i _ => hH i z))
    (fun z _ => finite_product_first_hasDerivAt Finset.univ H D E z
      (fun i _ => hH i z) (fun i _ => hD i z)) hsecond 1 (by norm_num)
  have hlinear : finiteProductFirst Finset.univ H D 0 =
      ∑ γ, localResponseLinearCoefficient a V η g w φ y γ * v γ := by
    simp only [finiteProductFirst, H, D, zero_mul, δ,
      localResponseLinearCoefficient, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro γ _
    simp only [Finset.sum_const_zero, add_zero]
    ring
  simpa only [H, δ, one_mul, zero_mul, add_zero, highResponseProduct,
    coefficientRegression, hlinear] using hTaylor

end Taylor

section Signed
variable {ι E ED : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace E] [MeasurableSpace ED]

/-- The paper's conditional affine cancellation, stated for actual signed
integrals and every bounded Borel function of the density mark. -/
def SignedDensityAffineCancellation (Ω : SignedMeasure E) (densityMark : E → ED)
    (cReset : E → ι → ℝ) : Prop :=
  ∀ b : ED → ℝ, Measurable b → (∃ B : ℝ, ∀ d, |b d| ≤ B) →
    (∫ᵛ e, b (densityMark e) ∂<•Ω) = 0 ∧
      ∀ γ, (∫ᵛ e, b (densityMark e) * cReset e γ ∂<•Ω) = 0

/-- Universal all-count signed local-update bound. Its inputs are primitive
legal reset bounds and conditional affine cancellation; no score or
numerator estimate is supplied. -/
theorem signed_local_operator_all_count_bound_of_bounded_density {n : ℕ} (hn : 1 ≤ n)
    (Ω : SignedMeasure E) [IsFiniteMeasure Ω.variation]
    (densityMark : E → ED) (hmark : Measurable densityMark)
    (pReset : ED → Fin n → ℝ) (hpm : ∀ i, Measurable (fun d => pReset d i))
    (cReset : E → ι → ℝ) (hcm : ∀ γ, Measurable (fun e => cReset e γ))
    (C a V η ρ pPlus : ℝ) (_hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2) (hpPlus : 0 ≤ pPlus)
    (hReset : ∀ d i, |pReset d i| ≤ pPlus)
    (hcReset : ∀ᵐ e ∂Ω.variation, ∑ γ, |cReset e γ| ≤ C⁻¹)
    (hCancel : SignedDensityAffineCancellation Ω densityMark cReset)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ i, |∑ γ, φ i γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
    (y : Fin n → Fin 3) :
    |∫ᵛ e, (∏ i, pReset (densityMark e) i) *
      highResponseProduct a V η g w φ (cReset e) y ∂<•Ω| ≤
      (pPlus^n * highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2) *
        Ω.variation.real univ := by
  let b : ED → ℝ := fun d => ∏ i, pReset d i
  let P : E → ℝ := fun e => highResponseProduct a V η g w φ (cReset e) y
  let P0 : ℝ := ∏ i, ternaryMass a (g i) V (y i)
  let L : ι → ℝ := localResponseLinearCoefficient a V η g w φ y
  let R : E → ℝ := fun e => P e - P0 - ∑ γ, L γ * cReset e γ
  have hb : Measurable b := Finset.measurable_fun_prod _ (fun i _ => hpm i)
  have hbb (d : ED) : |b d| ≤ pPlus^n :=
    finite_density_product_abs_bound _ pPlus hpPlus (hReset d)
  have hzero := hCancel b hb ⟨pPlus^n, hbb⟩
  have hbInt : Ω.Integrable (fun e => b (densityMark e)) :=
    Integrable.of_bound (hb.comp hmark).aestronglyMeasurable (pPlus^n)
      (Filter.Eventually.of_forall (fun e => by simpa only [Real.norm_eq_abs] using hbb _))
  have hcBound (γ : ι) : ∀ᵐ e ∂Ω.variation, |cReset e γ| ≤ C⁻¹ := by
    filter_upwards [hcReset] with e he
    exact (Finset.single_le_sum (fun i _ => abs_nonneg (cReset e i)) (Finset.mem_univ γ)).trans he
  have hbcInt (γ : ι) : Ω.Integrable (fun e => b (densityMark e) * cReset e γ) :=
    hbInt.mul_bdd (hcm γ).aestronglyMeasurable (by
      simpa only [Real.norm_eq_abs] using hcBound γ)
  have hP : Measurable P := highMarkedResponseProduct_measurable a V η cReset hcm g w φ y
  have hPb : ∀ᵐ e ∂Ω.variation, |P e| ≤ 1 := by
    filter_upwards [hcReset] with e he
    apply highMarkedResponseProduct_abs_le_one a V η ha.ne' g w φ (cReset e) _ y
    intro i u
    apply hp _
    change |g i + η*w i*(∑ γ, φ i γ*cReset e γ)| ≤ ρ
    have hterm : |η*w i*(∑ γ, φ i γ*cReset e γ)| ≤ η := by
      rw [abs_mul, abs_mul, abs_of_nonneg hη]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left (hw i) hη) (hφ _ he i)
        (abs_nonneg _) (by simpa using hη)).trans_eq (by ring)
    exact (abs_add_le _ _).trans (by linarith [hg i])
  have hbPInt : Ω.Integrable (fun e => b (densityMark e) * P e) :=
    hbInt.mul_bdd hP.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hPb)
  have hbP0Int : Ω.Integrable (fun e => b (densityMark e)*P0) := hbInt.mul_const P0
  have hLInt : Ω.Integrable (fun e => ∑ γ, L γ * (b (densityMark e)*cReset e γ)) :=
    integrable_finsetSum _ (fun γ _ => (hbcInt γ).const_mul (L γ))
  have hLzero : (∫ᵛ e, ∑ γ, L γ * (b (densityMark e)*cReset e γ) ∂<•Ω) = 0 := by
    rw [VectorMeasure.integral_finsetSum _ (fun γ _ => (hbcInt γ).const_mul (L γ))]
    apply Finset.sum_eq_zero
    intro γ _
    have hscale := VectorMeasure.integral_fun_smul (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
      (μ := Ω) (L γ) (fun e => b (densityMark e)*cReset e γ)
    simpa only [smul_eq_mul, hzero.2 γ, mul_zero] using hscale
  have he : (∫ᵛ e, b (densityMark e) * R e ∂<•Ω) =
      ∫ᵛ e, b (densityMark e)*P e ∂<•Ω := by
    have hfun : (fun e => b (densityMark e)*R e) =
        (fun e => (b (densityMark e)*P e - b (densityMark e)*P0) -
          ∑ γ, L γ*(b (densityMark e)*cReset e γ)) := by
      funext e
      dsimp [R]
      rw [mul_sub, mul_sub, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl; intro γ _; ring
    rw [hfun]
    have hsub := VectorMeasure.integral_fun_sub (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
      (f := fun e => b (densityMark e)*P e - b (densityMark e)*P0)
      (g := fun e => ∑ γ, L γ*(b (densityMark e)*cReset e γ))
      (hbPInt.sub hbP0Int) hLInt
    rw [hsub, VectorMeasure.integral_fun_sub hbPInt hbP0Int, hLzero]
    have hz : (∫ᵛ e, b (densityMark e)*P0 ∂<•Ω) = 0 := by
      have hscale := VectorMeasure.integral_fun_smul (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
        (μ := Ω) P0 (fun e => b (densityMark e))
      simpa only [smul_eq_mul, hzero.1, mul_zero, mul_comm _ P0] using hscale
    rw [hz, sub_zero, sub_zero]
  rw [← he]
  have hbound : ∀ᵐ e ∂Ω.variation, ‖b (densityMark e)*R e‖ ≤
      pPlus^n * highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2 := by
    filter_upwards [hcReset] with e he
    rw [Real.norm_eq_abs, abs_mul]
    have hr : |R e| ≤ highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2 :=
      local_response_affine_remainder hn C a V η ρ ha hη hρ hηρ g w φ hg hw hφ hp
        (cReset e) he y
    exact (mul_le_mul (hbb _) hr (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hnorm := VectorMeasure.norm_integral_le_of_norm_le_const
      (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip) (μ := Ω) (f := fun e => b (densityMark e)*R e)
      hbound
  have hBnorm : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip‖ ≤ 1 := by
    rw [ContinuousLinearMap.opNorm_flip]
    exact ContinuousLinearMap.opNorm_lsmul_le
  have hnorm' : |∫ᵛ e, b (densityMark e)*R e ∂<•Ω| ≤
      (pPlus^n * highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2) *
        ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip‖ * Ω.variation.real univ := by
    simpa only [Real.norm_eq_abs] using hnorm
  apply hnorm'.trans
  have hK : 0 ≤ pPlus^n * highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2 := by
    have := highSeparatedDerivativeBudget_nonneg a ρ
    positivity
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBnorm hK)
    ENNReal.toReal_nonneg).trans_eq (by simp only [mul_one, Measure.real])

/-- The same universal clause with legal density and coefficient reset
support expressed almost everywhere under the true total variation. A
bounded Borel clipping of the density mark permits the exact conditional
annihilation hypothesis to be used even outside that support. -/
theorem signed_local_operator_all_count_bound {n : ℕ} (hn : 1 ≤ n)
    (Ω : SignedMeasure E) [IsFiniteMeasure Ω.variation]
    (densityMark : E → ED) (hmark : Measurable densityMark)
    (pReset : ED → Fin n → ℝ) (hpm : ∀ i, Measurable (fun d => pReset d i))
    (cReset : E → ι → ℝ) (hcm : ∀ γ, Measurable (fun e => cReset e γ))
    (C a V η ρ pPlus : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2) (hpPlus : 0 ≤ pPlus)
    (hReset : ∀ᵐ e ∂Ω.variation, ∀ i, |pReset (densityMark e) i| ≤ pPlus)
    (hcReset : ∀ᵐ e ∂Ω.variation, ∑ γ, |cReset e γ| ≤ C⁻¹)
    (hCancel : SignedDensityAffineCancellation Ω densityMark cReset)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ i, |∑ γ, φ i γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
    (y : Fin n → Fin 3) :
    |∫ᵛ e, (∏ i, pReset (densityMark e) i) *
      highResponseProduct a V η g w φ (cReset e) y ∂<•Ω| ≤
      (pPlus^n * highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2) *
        Ω.variation.real univ := by
  let pSafe : ED → Fin n → ℝ := fun d i => max (-pPlus) (min pPlus (pReset d i))
  have hpSafe (i : Fin n) : Measurable (fun d => pSafe d i) :=
    measurable_const.max (measurable_const.min (hpm i))
  have hSafeBound (d : ED) (i : Fin n) : |pSafe d i| ≤ pPlus := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hSafeEq : (fun e => (∏ i, pSafe (densityMark e) i) *
      highResponseProduct a V η g w φ (cReset e) y) =ᵐ[Ω.variation]
      (fun e => (∏ i, pReset (densityMark e) i) *
        highResponseProduct a V η g w φ (cReset e) y) := by
    filter_upwards [hReset] with e he
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    dsimp [pSafe]
    rw [min_eq_right (abs_le.mp (he i)).2, max_eq_right (abs_le.mp (he i)).1]
  rw [← VectorMeasure.integral_congr_ae (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip) hSafeEq]
  exact signed_local_operator_all_count_bound_of_bounded_density hn Ω densityMark hmark
    pSafe hpSafe cReset hcm C a V η ρ pPlus hC ha hη hρ hηρ hpPlus hSafeBound
    hcReset hCancel g w φ hg hw hφ hp y

/-- The manuscript's fixed ternary Taylor constant, before the count,
frame, signed measure, or legal reset family is chosen. -/
def localOperatorTernaryConstant (a ρ : ℝ) : ℝ := highSeparatedDerivativeBudget a ρ / 2

theorem localOperatorTernaryConstant_nonneg (a ρ : ℝ) :
    0 ≤ localOperatorTernaryConstant a ρ :=
  div_nonneg (highSeparatedDerivativeBudget_nonneg a ρ) (by norm_num)

/-- The precise `2 C_q k² p₊^k η² ‖Ω‖` ordering in the original statement. -/
theorem signed_local_operator_all_count_paper_bound {n : ℕ} (hn : 1 ≤ n)
    (Ω : SignedMeasure E) [IsFiniteMeasure Ω.variation]
    (densityMark : E → ED) (hmark : Measurable densityMark)
    (pReset : ED → Fin n → ℝ) (hpm : ∀ i, Measurable (fun d => pReset d i))
    (cReset : E → ι → ℝ) (hcm : ∀ γ, Measurable (fun e => cReset e γ))
    (C a V η ρ pPlus : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2) (hpPlus : 0 ≤ pPlus)
    (hReset : ∀ᵐ e ∂Ω.variation, ∀ i, |pReset (densityMark e) i| ≤ pPlus)
    (hcReset : ∀ᵐ e ∂Ω.variation, ∑ γ, |cReset e γ| ≤ C⁻¹)
    (hCancel : SignedDensityAffineCancellation Ω densityMark cReset)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ i, |∑ γ, φ i γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
    (y : Fin n → Fin 3) :
    |∫ᵛ e, (∏ i, pReset (densityMark e) i) *
      highResponseProduct a V η g w φ (cReset e) y ∂<•Ω| ≤
      2 * localOperatorTernaryConstant a ρ * (n : ℝ)^2 * pPlus^n * η^2 *
        Ω.variation.real univ := by
  apply (signed_local_operator_all_count_bound hn Ω densityMark hmark pReset hpm
    cReset hcm C a V η ρ pPlus hC ha hη hρ hηρ hpPlus hReset hcReset hCancel
    g w φ hg hw hφ hp y).trans_eq
  unfold localOperatorTernaryConstant
  ring

end Signed
end NearlyMinimax
