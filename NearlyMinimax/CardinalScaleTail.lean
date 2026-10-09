module

public import NearlyMinimax.LogScaleChange


@[expose] public section

/-! Actual logarithmic scale-domain complement bound for the integrated
cardinal interpolation matrix. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem log_scale_tail_reindex (e : κ ≃ ι) (b A : ℝ) (s : κ → ℝ) :
    logScaleTail b A ((MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) s) = logScaleTail b A s := by
  have hs := e.sum_comp (fun j : ι => Real.log (1 + ((MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) s) j))
  have hp := e.prod_comp (fun j : ι => (1 + ((MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) s) j) ^ (-b - 1 : ℝ))
  simp only [MeasurableEquiv.piCongrLeft_apply_apply] at hs hp
  unfold logScaleTail
  rw [← hs, ← hp]

theorem log_scale_tail_integral_reindex (e : κ ≃ ι) (b A : ℝ) :
    (∫ t : ι → ℝ in Ici 0, logScaleTail b A t) =
      ∫ s : κ → ℝ in Ici 0, logScaleTail b A s := by
  rw [← exponential_orthant_measure_eq_restrict, ← exponential_orthant_measure_eq_restrict]
  have hp := measurePreserving_piCongrLeft (fun _ : ι => volume.restrict (Ici (0 : ℝ))) e
  unfold exponentialOrthantMeasure
  rw [← hp.integral_comp']
  simp_rw [log_scale_tail_reindex]

theorem log_scale_tail_integrable_of_card {m : ℕ} (hcard : Fintype.card ι = m + 1)
    {b : ℝ} (hb : 0 < b) (A : ℝ) :
    IntegrableOn (logScaleTail b A : (ι → ℝ) → ℝ) (Ici 0) := by
  let e : Fin (m + 1) ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  have hp := measurePreserving_piCongrLeft (fun _ : ι => volume.restrict (Ici (0 : ℝ))) e
  rw [IntegrableOn, ← exponential_orthant_measure_eq_restrict]
  apply (hp.integrable_comp_emb (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e).measurableEmbedding).mp
  have he : (logScaleTail b A) ∘ (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) =
      (logScaleTail b A : (Fin (m + 1) → ℝ) → ℝ) := by
    funext s
    exact log_scale_tail_reindex e b A s
  rw [he]
  have h := finite_log_scale_tail_integrable (m := m) hb A
  rw [IntegrableOn, ← exponential_orthant_measure_eq_restrict] at h
  exact h

theorem log_scale_tail_integral_uniform_of_card {m : ℕ} (hcard : Fintype.card ι = m + 1)
    {b A : ℝ} (hb : (1 / 2 : ℝ) ≤ b) (hA : 0 ≤ A) :
    (∫ t : ι → ℝ in Ici 0, logScaleTail b A t) ≤
      8 ^ (m + 1) * Real.exp (-(b * A)) * (1 + A) ^ m := by
  rw [log_scale_tail_integral_reindex (Fintype.equivFinOfCardEq hcard).symm]
  exact finite_log_scale_tail_integral_uniform hb hA

def strictLogScaleTail (b A : ℝ) (t : ι → ℝ) : ℝ :=
  ({t : ι → ℝ | A < ∑ j, Real.log (1 + t j)}).indicator (logScaleTail b A) t

theorem strict_log_scale_tail_integrable_of_card {m : ℕ} (hcard : Fintype.card ι = m + 1)
    {b : ℝ} (hb : 0 < b) (A : ℝ) :
    IntegrableOn (strictLogScaleTail b A : (ι → ℝ) → ℝ) (Ici 0) := by
  exact (log_scale_tail_integrable_of_card hcard hb A).indicator
    (measurableSet_lt measurable_const (Finset.measurable_sum _ fun j _ =>
      Real.measurable_log.comp (measurable_const.add (measurable_pi_apply j))))

theorem strict_log_scale_tail_integral_le {m : ℕ} (hcard : Fintype.card ι = m + 1)
    {b A : ℝ} (hb : (1 / 2 : ℝ) ≤ b) (hA : 0 ≤ A) :
    (∫ t : ι → ℝ in Ici 0, strictLogScaleTail b A t) ≤
      8 ^ (m + 1) * Real.exp (-(b * A)) * (1 + A) ^ m := by
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hnonneg : ∀ᵐ t : ι → ℝ ∂volume.restrict (Ici 0), 0 ≤ logScaleTail b A t := by
    filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Ici (0 : ι → ℝ)))] with t ht
    unfold logScaleTail
    split_ifs
    · apply Finset.prod_nonneg
      intro j _
      have htj : (0 : ℝ) ≤ t j := ht j
      exact Real.rpow_nonneg (by linarith) _
    · exact le_refl _
  calc
    _ ≤ ∫ t : ι → ℝ in Ici 0, logScaleTail b A t :=
      integral_mono_ae (strict_log_scale_tail_integrable_of_card hcard hbpos A)
        (log_scale_tail_integrable_of_card hcard hbpos A) (by
          filter_upwards [hnonneg] with t ht
          unfold strictLogScaleTail
          by_cases hh : t ∈ {t : ι → ℝ | A < ∑ j, Real.log (1 + t j)}
          · simp only [Set.indicator_of_mem hh, le_refl]
          · simp only [Set.indicator_of_notMem hh]
            exact ht)
    _ ≤ _ := log_scale_tail_integral_uniform_of_card hcard hb hA

theorem spatial_scale_index_card {n : ℕ} (i : Fin n) : Fintype.card (SpatialScaleIndex i) = n - 1 := by
  simpa [SpatialScaleIndex] using Fintype.card_subtype_compl (fun j : Fin n => j = i)

theorem spatial_scale_complement_integral_eq {n : ℕ} (i : Fin n) (b T : ℝ) :
    (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
      ∏ j, (1 + t j) ^ (-b - 1 : ℝ)) =
      ∫ t : SpatialScaleVector i in Ici 0, strictLogScaleTail b (2 * Real.log T) t := by
  change (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
    ∏ j, (1 + t j) ^ (-b - 1 : ℝ)) =
      ∫ t : SpatialScaleVector i in Ici 0,
        ({t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)}).indicator
          (logScaleTail b (2 * Real.log T)) t
  have hlogs : Measurable (fun t : SpatialScaleVector i => ∑ j, Real.log (1 + t j)) :=
    Finset.measurable_sum _ fun j _ => Real.measurable_log.comp
      (measurable_const.add (measurable_pi_apply j))
  have hm : MeasurableSet {t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)} :=
    measurableSet_lt measurable_const hlogs
  rw [integral_indicator hm, Measure.restrict_restrict hm]
  have hs : {t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)} ∩ Ici 0 =
      Ici 0 \ spatialScaleDomain i T := by
    ext t
    constructor
    · rintro ⟨hlog, ht⟩
      change 2 * Real.log T < ∑ j, Real.log (1 + t j) at hlog
      refine ⟨ht, ?_⟩
      intro hD
      have he : spatialScaleLogSum i t = ∑ j, Real.log (1 + t j) := by
        unfold spatialScaleLogSum
        apply Finset.sum_congr rfl
        intro j _
        have htj : (0 : ℝ) ≤ t j := ht j
        rw [max_eq_right htj]
      rw [← he] at hlog
      exact (not_lt_of_ge hD.2) hlog
    · rintro ⟨ht, hD⟩
      refine ⟨?_, ht⟩
      by_contra h
      apply hD
      refine ⟨ht, ?_⟩
      change spatialScaleLogSum i t ≤ 2 * Real.log T
      unfold spatialScaleLogSum
      have hh : ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T := le_of_not_gt h
      convert hh using 1
      apply Finset.sum_congr rfl
      intro j _
      have htj : (0 : ℝ) ≤ t j := ht j
      rw [max_eq_right htj]
  rw [hs]
  apply setIntegral_congr_fun (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet)
  intro t ht
  have hlog : 2 * Real.log T < ∑ j, Real.log (1 + t j) := by
    rw [← hs] at ht
    exact ht.1
  exact (if_pos hlog.le).symm

theorem spatial_scale_complement_power_integrable {n : ℕ} (hn : 2 ≤ n) (i : Fin n)
    {b : ℝ} (hb : 0 < b) (T : ℝ) :
    IntegrableOn (fun t : SpatialScaleVector i => ∏ j, (1 + t j) ^ (-b - 1 : ℝ))
      (Ici 0 \ spatialScaleDomain i T) := by
  have hcard : Fintype.card (SpatialScaleIndex i) = (n - 2) + 1 := by
    rw [spatial_scale_index_card]
    omega
  have h := (strict_log_scale_tail_integrable_of_card hcard hb (2 * Real.log T)).mono_set
    (Set.diff_subset : Ici (0 : SpatialScaleVector i) \ spatialScaleDomain i T ⊆ Ici 0)
  apply h.congr_fun _ (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet)
  intro t ht
  have he : spatialScaleLogSum i t = ∑ j, Real.log (1 + t j) := by
    unfold spatialScaleLogSum
    apply Finset.sum_congr rfl
    intro j _
    have htj : (0 : ℝ) ≤ t j := ht.1 j
    rw [max_eq_right htj]
  have hlog : 2 * Real.log T < ∑ j, Real.log (1 + t j) := by
    by_contra hh
    apply ht.2
    refine ⟨ht.1, ?_⟩
    change spatialScaleLogSum i t ≤ 2 * Real.log T
    rw [he]
    exact le_of_not_gt hh
  unfold strictLogScaleTail logScaleTail
  have hm : t ∈ {t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)} := hlog
  rw [Set.indicator_of_mem hm, ite_eq_left hlog.le]

/-- The scale-domain complement estimate used by the actual cardinal
interpolation defect. The logarithmic power is one less than the number of
scales, exactly as required in the paper's interpolation bound. -/
theorem spatial_scale_complement_power_integral_le {n : ℕ} (hn : 2 ≤ n) (i : Fin n)
    {b T : ℝ} (hb : (1 / 2 : ℝ) ≤ b) (hT : 1 ≤ T) :
    (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
      ∏ j, (1 + t j) ^ (-b - 1 : ℝ)) ≤
      16 ^ (n - 1) * T ^ (-2 * b : ℝ) * (1 + Real.log T) ^ (n - 2) := by
  have hcard : Fintype.card (SpatialScaleIndex i) = (n - 2) + 1 := by
    rw [spatial_scale_index_card]
    omega
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  rw [spatial_scale_complement_integral_eq]
  have h := strict_log_scale_tail_integral_le hcard hb (by linarith : 0 ≤ 2 * Real.log T)
  have he : Real.exp (-(b * (2 * Real.log T))) = T ^ (-2 * b : ℝ) := by
    rw [Real.rpow_def_of_pos hTpos]
    congr 1
    ring
  rw [he] at h
  have hpow : (1 + 2 * Real.log T) ^ (n - 2) ≤
      (2 : ℝ) ^ (n - 2) * (1 + Real.log T) ^ (n - 2) := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 2 * Real.log T)
      (by linarith : 1 + 2 * Real.log T ≤ 2 * (1 + Real.log T)) (n - 2)
    simpa only [mul_pow] using hh
  have hconst : (8 : ℝ) ^ (n - 2 + 1) * 2 ^ (n - 2) ≤ 16 ^ (n - 1) := by
    have hn' : n - 2 + 1 = n - 1 := by omega
    rw [hn']
    calc
      _ ≤ 8 ^ (n - 1) * 2 ^ (n - 1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : n - 2 ≤ n - 1)) (by positivity)
      _ = _ := by rw [← mul_pow]; norm_num
  have hh := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ (8 : ℝ) ^ (n - 2 + 1) * T ^ (-2 * b : ℝ))
  have hc := mul_le_mul_of_nonneg_right hconst
    (by positivity : 0 ≤ T ^ (-2 * b : ℝ) * (1 + Real.log T) ^ (n - 2))
  calc
    _ ≤ _ := h
    _ ≤ _ := by nlinarith [hh, hc]

end NearlyMinimax
