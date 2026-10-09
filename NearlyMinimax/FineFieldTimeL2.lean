module

public import NearlyMinimax.FinePairAllCounts
public import NearlyMinimax.HigherFieldMomentL2
public import NearlyMinimax.CardinalWeightedBounds
public import NearlyMinimax.SpatialSubsetEnergy
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Probability.Kernel.MeasurableIntegral


@[expose] public section

/-! Integration of the genuine higher field moments over the fine-row scale. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

/-- The constructed field moment is jointly Borel in its scale and spatial tuple. -/
theorem boundedHyperplaneSpatialMoment_joint_measurable (d j : ℕ) [NeZero d] :
    Measurable (fun z : ℝ × (Fin j → Covariate d) => boundedHyperplaneSpatialMoment d z.1 j z.2) := by
  let κ : Kernel (ℝ × (Fin j → Covariate d)) (FinePairFieldMark d) := (finePairFieldKernel d).comap (Prod.fst : ℝ × (Fin j → Covariate d) → ℝ) measurable_fst
  have hm : Measurable (fun z : (ℝ × (Fin j → Covariate d)) × FinePairFieldMark d =>
      ∏ l, boundedHyperplaneFieldValue z.2 (z.1.2 l)) :=
    Finset.measurable_prod _ (fun l _ => (boundedHyperplaneFieldValue_measurable d).comp
      (measurable_snd.prodMk ((measurable_pi_apply l).comp (measurable_snd.comp measurable_fst))))
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

def fineFieldScaleWeight (d : ℕ) (T : ℝ) : ℝ := T / T ^ d

theorem fineFieldScaleWeight_continuousOn {d : ℕ} {lo hi : ℝ} (hlo : 0 < lo) :
    ContinuousOn (fineFieldScaleWeight d) (Icc lo hi) := by
  apply continuousOn_id.div (continuous_pow d).continuousOn
  intro T hT
  exact (pow_pos (hlo.trans_le hT.1) d).ne'

theorem fineFieldScaleWeight_integrableOn {d : ℕ} {lo hi : ℝ} (hlo : 0 < lo) :
    IntegrableOn (fineFieldScaleWeight d) (Icc lo hi) :=
  (fineFieldScaleWeight_continuousOn hlo).integrableOn_compact isCompact_Icc

theorem fineFieldScaleWeight_eq_rpow {d : ℕ} {T : ℝ} (hT : 0 < T) :
    fineFieldScaleWeight d T = T ^ (1 - (d : ℝ)) := by
  unfold fineFieldScaleWeight
  rw [Real.rpow_sub hT, Real.rpow_one, Real.rpow_natCast]

theorem fineFieldScaleWeight_integral_le {d : ℕ} (hd : 3 ≤ d) {lo hi : ℝ} (hlo : 0 < lo) :
    (∫ T in Icc lo hi, fineFieldScaleWeight d T) ≤ lo ^ (2 - (d : ℝ)) / (d - 2 : ℝ) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdec : (1 : ℝ) - d < -1 := by linarith only [hdR]
  have htail : IntegrableOn (fun T : ℝ => T ^ (1 - (d : ℝ))) (Ici lo) := by
    change Integrable (fun T : ℝ => T ^ (1 - (d : ℝ))) (volume.restrict (Ici lo))
    rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
    exact integrableOn_Ioi_rpow_of_lt hdec hlo
  have he : (∫ T in Icc lo hi, fineFieldScaleWeight d T) =
      ∫ T in Icc lo hi, T ^ (1 - (d : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro T hT
    exact fineFieldScaleWeight_eq_rpow (hlo.trans_le hT.1)
  rw [he]
  apply (integral_mono_measure (Measure.restrict_mono_set volume Icc_subset_Ici_self)
    (by filter_upwards [ae_restrict_mem measurableSet_Ici] with T hT; exact Real.rpow_nonneg (hlo.le.trans hT) _) htail).trans_eq
  rw [integral_Ici_eq_integral_Ioi]
  rw [integral_Ioi_rpow_of_lt hdec hlo]
  have he : (1 - (d : ℝ)) + 1 = 2 - (d : ℝ) := by ring
  rw [he]
  rw [show (2 : ℝ) - d = -(d - 2 : ℝ) by ring]
  simp only [div_neg]
  ring

/-- Weighted Cauchy--Schwarz and genuine Fubini exchange for a bounded
jointly Borel spatial moment, integrated over a finite positive scale band. -/
theorem weighted_scale_square_energy_le {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (d : ℕ) {lo hi K : ℝ}
    (hlo : 0 < lo) (hK : 0 ≤ K) (F : ℝ × X → ℝ) (hF : Measurable F)
    (hFb : ∀ z, |F z| ≤ 1)
    (hE : ∀ T ∈ Icc lo hi, (∫ x, F (T,x) ^ 2 ∂mu) ≤ K ^ 2 / (T ^ d) ^ 2) :
    Integrable (fun x => (∫ T in Icc lo hi, T * F (T,x)) ^ 2) mu ∧
      (∫ x, (∫ T in Icc lo hi, T * F (T,x)) ^ 2 ∂mu) ≤
        K ^ 2 * (∫ T in Icc lo hi, fineFieldScaleWeight d T) ^ 2 := by
  let nu : Measure ℝ := volume.restrict (Icc lo hi)
  let W : ℝ := ∫ T, fineFieldScaleWeight d T ∂nu
  let f : ℝ × X → ℝ := fun z => z.1 * F z
  let g : ℝ × X → ℝ := fun z => z.1 * z.1 ^ d * F z ^ 2
  have hw : Integrable (fineFieldScaleWeight d) nu := fineFieldScaleWeight_integrableOn hlo
  have hW : 0 ≤ W := integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
    exact div_nonneg (hlo.le.trans hT.1) (pow_nonneg (hlo.le.trans hT.1) _))
  have hfm : Measurable f := measurable_fst.mul hF
  have hgm : Measurable g := (measurable_fst.mul (measurable_fst.pow_const d)).mul (hF.pow_const 2)
  have hfi : Integrable f (nu.prod mu) :=
    (((continuous_id.continuousOn.integrableOn_compact isCompact_Icc).comp_fst mu).mul_bdd
      hF.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hFb z))
  have hgi : Integrable g (nu.prod mu) := by
    have ht : Integrable (fun T : ℝ => T * T ^ d) nu :=
      (continuous_id.mul (continuous_pow d)).continuousOn.integrableOn_compact isCompact_Icc
    apply (ht.comp_fst mu).mul_bdd (c := 1) (hF.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_sq]
      nlinarith only [hFb z, sq_abs (F z), abs_nonneg (F z)])
  have hcs : ∀ᵐ x ∂mu, (∫ T, f (T,x) ∂nu) ^ 2 ≤ W * ∫ T, g (T,x) ∂nu := by
    filter_upwards [hfi.prod_left_ae, hgi.prod_left_ae] with x hfx hgx
    apply integral_square_le_weight_mass_mul nu (fun T => f (T,x))
      (fineFieldScaleWeight d) (fun T => g (T,x)) hfx hw hgx
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
      exact div_nonneg (hlo.le.trans hT.1) (pow_nonneg (hlo.le.trans hT.1) _)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
      exact mul_nonneg (mul_nonneg (hlo.le.trans hT.1)
        (pow_nonneg (hlo.le.trans hT.1) _)) (sq_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
      have hp : T ^ d ≠ 0 := (pow_pos (hlo.trans_le hT.1) d).ne'
      dsimp [f, g, fineFieldScaleWeight]
      field_simp
      exact le_refl _
  have hsi : Integrable (fun x => (∫ T, f (T,x) ∂nu) ^ 2) mu := by
    apply (hgi.integral_prod_right.const_mul W).mono'
      (hfm.stronglyMeasurable.integral_prod_left'.measurable.pow_const 2).aestronglyMeasurable
    filter_upwards [hcs] with x hx
    rw [Real.norm_eq_abs, abs_sq]
    exact hx
  have hbound := integral_mono_ae hsi (hgi.integral_prod_right.const_mul W) hcs
  rw [integral_const_mul] at hbound
  have hswap : (∫ x, ∫ T, g (T,x) ∂nu ∂mu) = ∫ T, ∫ x, g (T,x) ∂mu ∂nu :=
    (integral_integral_swap hgi).symm
  rw [hswap] at hbound
  have hi : (∫ T, ∫ x, g (T,x) ∂mu ∂nu) ≤ K ^ 2 * W := by
    have hm : (∫ T, ∫ x, g (T,x) ∂mu ∂nu) ≤ ∫ T, K ^ 2 * fineFieldScaleWeight d T ∂nu := by
      apply integral_mono_ae hgi.integral_prod_left (hw.const_mul (K ^ 2))
      filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
      dsimp [g]
      rw [integral_const_mul]
      have hp : 0 < T := hlo.trans_le hT.1
      have h := mul_le_mul_of_nonneg_left (hE T hT)
        (mul_nonneg hp.le (pow_nonneg hp.le d))
      apply h.trans_eq
      dsimp [fineFieldScaleWeight]
      field_simp
    exact hm.trans_eq (integral_const_mul _ _)
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_left hi hW)
  refine ⟨hsi, ?_⟩
  convert hfinal using 1 <;> dsimp [f, W, nu] <;> ring

theorem finePairTimeSubsetMoment_univ_eq {d j : ℕ} [NeZero d]
    (lo hi : ℝ) (U : Fin j → Covariate d) :
    finePairTimeSubsetMoment lo hi U Finset.univ =
      ∫ T in Icc lo hi, T * boundedHyperplaneSpatialMoment d T j U := by
  rw [finePairTimeSubsetMoment_actual]
  rfl

/-- The actual time-mark integral is genuinely square integrable over Q^j. -/
theorem finePairTimeSubsetMoment_univ_square_integrable {d j : ℕ} [NeZero d]
    (hd : 3 ≤ d) (hj : 4 ≤ j) {lo hi : ℝ} (hlo : 0 < lo) :
    Integrable (fun U : Fin j → Covariate d =>
      finePairTimeSubsetMoment lo hi U Finset.univ ^ 2) (fullSpatialPatchDesign d j) := by
  let K : ℝ := hyperplaneSpatialMomentConstant d ^ j * (j : ℝ) ^ 4
  have hK : 0 ≤ K := by positivity [hyperplaneSpatialMomentConstant_positive d]
  have hh := weighted_scale_square_energy_le (fullSpatialPatchDesign d j) d (lo := lo) (hi := hi) (K := K) hlo hK
    (fun z => boundedHyperplaneSpatialMoment d z.1 j z.2)
    (boundedHyperplaneSpatialMoment_joint_measurable d j)
    (fun z => boundedHyperplaneSpatialMoment_abs_le_one d z.1 j z.2) (fun T hT => by
      have hp : 0 < T := hlo.trans_le hT.1
      have hb := boundedHyperplaneSpatialMoment_L2_le d T hp j hj
      have hn : 0 ≤ ∫ U : Fin j → Covariate d,
          boundedHyperplaneSpatialMoment d T j U ^ 2 ∂fullSpatialPatchDesign d j :=
        integral_nonneg (fun _ => sq_nonneg _)
      have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ K / T ^ d)).mpr hb
      change Real.sqrt (∫ U : Fin j → Covariate d,
        boundedHyperplaneSpatialMoment d T j U ^ 2 ∂fullSpatialPatchDesign d j) ^ 2 ≤
          (K / T ^ d) ^ 2 at hs
      simpa only [Real.sq_sqrt hn, div_pow] using hs)
  simp_rw [finePairTimeSubsetMoment_univ_eq]
  exact hh.1

/-- True spatial decay after scale integration, for the fine row's actual
carrier and field law, rather than an assumed moment or time-energy bound. -/
theorem finePairTimeSubsetMoment_univ_L2_le {d j : ℕ} [NeZero d]
    (hd : 3 ≤ d) (hj : 4 ≤ j) {lo hi : ℝ} (hlo : 0 < lo) :
    Real.sqrt (∫ U : Fin j → Covariate d,
      finePairTimeSubsetMoment lo hi U Finset.univ ^ 2 ∂fullSpatialPatchDesign d j) ≤
      hyperplaneSpatialMomentConstant d ^ j * (j : ℝ) ^ 4 * lo ^ (2 - (d : ℝ)) := by
  let K : ℝ := hyperplaneSpatialMomentConstant d ^ j * (j : ℝ) ^ 4
  have hK : 0 ≤ K := by positivity [hyperplaneSpatialMomentConstant_positive d]
  have hh := weighted_scale_square_energy_le (fullSpatialPatchDesign d j) d (lo := lo) (hi := hi) (K := K) hlo hK
    (fun z => boundedHyperplaneSpatialMoment d z.1 j z.2)
    (boundedHyperplaneSpatialMoment_joint_measurable d j)
    (fun z => boundedHyperplaneSpatialMoment_abs_le_one d z.1 j z.2) (fun T hT => by
      have hp : 0 < T := hlo.trans_le hT.1
      have hb := boundedHyperplaneSpatialMoment_L2_le d T hp j hj
      have hn : 0 ≤ ∫ U : Fin j → Covariate d,
          boundedHyperplaneSpatialMoment d T j U ^ 2 ∂fullSpatialPatchDesign d j :=
        integral_nonneg (fun _ => sq_nonneg _)
      have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ K / T ^ d)).mpr hb
      change Real.sqrt (∫ U : Fin j → Covariate d,
        boundedHyperplaneSpatialMoment d T j U ^ 2 ∂fullSpatialPatchDesign d j) ^ 2 ≤
          (K / T ^ d) ^ 2 at hs
      simpa only [Real.sq_sqrt hn, div_pow] using hs)
  have hW0 : 0 ≤ ∫ T in Icc lo hi, fineFieldScaleWeight d T := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
    exact div_nonneg (hlo.le.trans hT.1) (pow_nonneg (hlo.le.trans hT.1) _)
  have hW := fineFieldScaleWeight_integral_le hd hlo (hi := hi)
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (1 : ℝ) ≤ d - 2 := by linarith only [hdR]
  have hw : (∫ T in Icc lo hi, fineFieldScaleWeight d T) ≤ lo ^ (2 - (d : ℝ)) :=
    hW.trans (div_le_self (Real.rpow_nonneg hlo.le _) hden)
  have hsq := pow_le_pow_left₀ hW0 hw 2
  have ht := mul_le_mul_of_nonneg_left hsq (sq_nonneg K)
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg hK (Real.rpow_nonneg hlo.le _), ?_⟩
  simp_rw [finePairTimeSubsetMoment_univ_eq]
  exact (hh.2.trans ht).trans_eq (mul_pow _ _ 2).symm

end NearlyMinimax
