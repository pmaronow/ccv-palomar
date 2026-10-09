module

public import NearlyMinimax.HighMarginalLikelihood
public import NearlyMinimax.HighResponseDecoding
public import NearlyMinimax.WeightedScoreContraction


@[expose] public section

/-! The actual observed-data score: the averaged genuine likelihood derivative
 divided by the averaged genuine likelihood. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

def highMarginalLikelihoodDerivative {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) (π : Measure E) (activation : E → ℝ)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  ∫ ω, highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F ω z ∂ν

def highMarginalIndexScore {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) (π : Measure E) (activation : E → ℝ)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  highMarginalLikelihoodDerivative dependent hsymm ν π activation n a V η p F z /
    highMarginalRawLikelihood ν n a V p F z

def highMarginalRealScore {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) (π : Measure E) (activation : E → ℝ)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (z : Fin n → Observation d) : ℝ :=
  highMarginalIndexScore dependent hsymm ν π activation n a V η p F (decodeDesignResponse a z)

theorem highMarginalIndexScore_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [SFinite ν] (π : Measure E) [SFinite π]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (highMarginalIndexScore dependent hsymm ν π activation n a V η p F) := by
  exact (highHistoryLikelihoodDerivative_measurable dependent hsymm π activation ham n a V η p F hp hF).stronglyMeasurable.integral_prod_left'.measurable.div
    (highMarginalRawLikelihood_measurable ν n a V p F hp hF)

theorem highMarginalRealScore_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [SFinite ν] (π : Measure E) [SFinite π]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (highMarginalRealScore dependent hsymm ν π activation n a V η p F) :=
  (highMarginalIndexScore_measurable dependent hsymm ν π activation ham n a V η p F hp hF).comp
    (decodeDesignResponse_measurable a)

/-- Actual marginal score testing has the genuine averaged derivative
as its density; all Fubini integrability is derived from primitive bounds. -/
theorem highMarginalIndexScore_integral {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η aRaw bRaw B : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw) (hB : 0 ≤ B)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    (∫ z, H (encodeDesignResponse a z) *
      highMarginalIndexScore dependent hsymm ν π activation n a V η p F z
      ∂(highSampleIndexKernel n a V p F hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n)) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
          H (encodeDesignResponse a z.2) *
            highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2
          ∂ν.prod (highSampleReference d n) := by
  let m := fun ω => highRawDensityMass (p ω)
  have hm : Measurable m := highRawDensityMass_joint_measurable p hp
  have hb (ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
      (Eventually.of_forall (hraw ω))
  have hG := massPowerNormalizer_pos ν m hm n aRaw bRaw haRaw hb
  have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  have hL (z) := highMarginalRawLikelihood_pos ν n a V |bRaw| (abs_nonneg _) ha.ne' p F hp hF
    (fun ω x => haRaw.trans_le (hraw ω x).1) hpb hq z
  have hdens : Measurable (fun z => ENNReal.ofReal
      (highMarginalRawLikelihood ν n a V p F z / massPowerNormalizer ν m n)) :=
    ((highMarginalRawLikelihood_measurable ν n a V p F hp hF).div_const _).ennreal_ofReal
  rw [highMassTilt_index_marginal_density ν n a V p F hp hF aRaw bRaw haRaw ha.ne' hraw
    (fun ω x y => (hq ω x y).le),
    integral_withDensity_eq_integral_toReal_smul hdens (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hL _).le hG.le), smul_eq_mul]
  have hi : Integrable (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      H (encodeDesignResponse a z.2) *
        highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2)
      (ν.prod (highSampleReference d n)) := by
    apply Integrable.of_bound
      (((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
        (highHistoryLikelihoodDerivative_measurable dependent hsymm π activation ham n a V η p F hp hF)).aestronglyMeasurable
      (B * ((Fintype.card J : ℝ) * (Ba * |bRaw|^n) + η^2 * (|bRaw|^n * ((n : ℝ)/a^2))))
    exact Eventually.of_forall fun z => by
      change ‖H (encodeDesignResponse a z.2) *
        highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hHb _) (highHistoryLikelihoodDerivative_abs_le π dependent hsymm activation Ba hBa
        habound n a V η |bRaw| (abs_nonneg _) ha p F hpb (fun ω x y => (hq ω x y).le) z.1 z.2)
        (abs_nonneg _) hB
  calc
    _ = (massPowerNormalizer ν m n)⁻¹ *
        ∫ z, H (encodeDesignResponse a z) *
          highMarginalLikelihoodDerivative dependent hsymm ν π activation n a V η p F z
          ∂highSampleReference d n := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only [highMarginalIndexScore]
        field_simp [(hL z).ne', hG.ne'] <;> ring
    _ = _ := by
      congr 1
      rw [MeasureTheory.integral_prod_symm _ hi]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only [highMarginalLikelihoodDerivative]
        rw [integral_const_mul]

theorem highMarginalRealScore_integral {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η aRaw bRaw B : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw) (hB : 0 ≤ B)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    (∫ z, H z * highMarginalRealScore dependent hsymm ν π activation n a V η p F z
      ∂(highRealSampleKernel n a V p F hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n)) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
          H (encodeDesignResponse a z.2) *
            highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2
          ∂ν.prod (highSampleReference d n) := by
  have hm : Measurable (fun z => H z *
      highMarginalRealScore dependent hsymm ν π activation n a V η p F z) :=
    hH.mul (highMarginalRealScore_measurable dependent hsymm ν π activation ham n a V η p F hp hF)
  rw [highRealSampleKernel, ← Measure.map_comp _ _ (encodeDesignResponse_measurable a),
    integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) hm.stronglyMeasurable]
  have he := highMarginalIndexScore_integral dependent hsymm ν π activation ham Ba hBa habound
    n a V η aRaw bRaw B ha haRaw hB p F hp hF hraw hq H hH hHb
  convert he using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only [highMarginalRealScore]
    rw [decodeDesignResponse_encode a ha]

end NearlyMinimax
