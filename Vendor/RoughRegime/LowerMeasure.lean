module

public import RoughRegime.Lower
public import RoughRegime.GeneralTesting
public import RoughRegime.Model


@[expose] public section

/-! General probability-density ingredients for the one-dimensional lower bound. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace RoughRegime.LowerMeasure

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integrable_sqrt_product {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf₀ : 0 ≤ᵐ[μ] f) (hg₀ : 0 ≤ᵐ[μ] g) :
    Integrable (fun x => Real.sqrt (f x) * Real.sqrt (g x)) μ := by
  apply ((hf.add hg).div_const 2).mono'
  · exact (hf.aemeasurable.sqrt.mul hg.aemeasurable.sqrt).aestronglyMeasurable
  · filter_upwards [hf₀, hg₀] with x hfx hgx
    change 0 ≤ f x at hfx
    change 0 ≤ g x at hgx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    change Real.sqrt (f x) * Real.sqrt (g x) ≤ (f x + g x) / 2
    nlinarith [Real.sq_sqrt hfx, Real.sq_sqrt hgx,
      sq_nonneg (Real.sqrt (f x) - Real.sqrt (g x))]

def densityAffinity (L R : GeneralTesting.DensityLaw μ) : ℝ :=
  ∫ x, Real.sqrt (L.density x) * Real.sqrt (R.density x) ∂μ

theorem densityAffinity_integrable (L R : GeneralTesting.DensityLaw μ) :
    Integrable (fun x => Real.sqrt (L.density x) * Real.sqrt (R.density x)) μ :=
  integrable_sqrt_product L.integrable R.integrable L.nonneg R.nonneg

theorem hellinger_integral_eq (L R : GeneralTesting.DensityLaw μ) :
    GeneralTesting.hellingerSquared L R = 2 - 2 * densityAffinity L R := by
  have hi := densityAffinity_integrable L R
  have he : (fun x => (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2) =ᵐ[μ]
      fun x => L.density x + R.density x -
        2 * (Real.sqrt (L.density x) * Real.sqrt (R.density x)) := by
    filter_upwards [L.nonneg, R.nonneg] with x hx hy
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]
  unfold GeneralTesting.hellingerSquared
  rw [integral_congr_ae he]
  change (∫ x, (L.density + R.density) x -
    (fun x => 2 * (Real.sqrt (L.density x) * Real.sqrt (R.density x))) x ∂μ) = _
  rw [integral_sub (L.integrable.add R.integrable) (hi.const_mul 2)]
  change (∫ x, L.density x + R.density x ∂μ) -
    (∫ x, 2 * (Real.sqrt (L.density x) * Real.sqrt (R.density x)) ∂μ) = _
  rw [integral_add L.integrable R.integrable, integral_const_mul, L.integral_one, R.integral_one]
  unfold densityAffinity
  ring

theorem hellinger_integrable (L R : GeneralTesting.DensityLaw μ) :
    Integrable (fun x => (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2) μ := by
  apply ((L.integrable.add R.integrable).sub ((densityAffinity_integrable L R).const_mul 2)).congr
  filter_upwards [L.nonneg, R.nonneg] with x hx hy
  change 0 ≤ L.density x at hx
  change 0 ≤ R.density x at hy
  change L.density x + R.density x - 2 * (Real.sqrt (L.density x) * Real.sqrt (R.density x)) = _
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

theorem densityAffinity_nonneg (L R : GeneralTesting.DensityLaw μ) :
    0 ≤ densityAffinity L R := integral_nonneg fun _ =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem densityAffinity_le_one (L R : GeneralTesting.DensityLaw μ) :
    densityAffinity L R ≤ 1 := by
  have h : 0 ≤ GeneralTesting.hellingerSquared L R :=
    integral_nonneg fun _ => sq_nonneg _
  rw [hellinger_integral_eq] at h
  linarith

def iidDensityLaw [SigmaFinite μ] (L : GeneralTesting.DensityLaw μ) (n : ℕ) :
    GeneralTesting.DensityLaw (Measure.pi (fun _ : Fin n => μ)) where
  density xs := ∏ i, L.density (xs i)
  measurable := by
    apply Finset.measurable_prod
    intro i _
    exact L.measurable.comp (measurable_pi_apply i)
  integrable := Integrable.fintype_prod fun _ => L.integrable
  nonneg := by
    have h : ∀ᵐ xs : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
        ∀ i, 0 ≤ L.density (xs i) := by
      filter_upwards [ae_le_pi (fun _ : Fin n => L.nonneg)] with xs hx
      exact hx
    filter_upwards [h] with xs hx
    exact Finset.prod_nonneg fun i _ => hx i
  integral_one := by
    rw [integral_fin_nat_prod_eq_prod]
    simp [L.integral_one]

/-- The density-product construction is exactly the iid product of the actual
probability laws, not merely an integral representation. -/
theorem iidDensityLaw_measure [SigmaFinite μ] (L : GeneralTesting.DensityLaw μ) (n : ℕ) :
    (iidDensityLaw L n).measure = Measure.pi (fun _ : Fin n => L.measure) := by
  apply (Measure.pi_eq (μ := fun _ : Fin n => L.measure) ?_).symm
  intro s hs
  have hS : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hrhs : (∏ i : Fin n, L.measure (s i)) ≠ ∞ := by
    rw [← Measure.pi_pi (fun _ : Fin n => L.measure)]
    exact measure_ne_top _ _
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hrhs).mp
  rw [ENNReal.toReal_prod]
  change (iidDensityLaw L n).measure.real (Set.univ.pi s) = ∏ i, L.measure.real (s i)
  rw [(iidDensityLaw L n).measureReal_eq_setIntegral _ hS]
  simp_rw [L.measureReal_eq_setIntegral _ (hs _)]
  rw [Measure.restrict_pi_pi]
  change (∫ xs : Fin n → Ω, ∏ i, L.density (xs i) ∂Measure.pi (fun i => μ.restrict (s i))) = _
  rw [integral_fin_nat_prod_eq_prod (fun _ : Fin n => L.density)]

theorem densityAffinity_iid [SigmaFinite μ] (L R : GeneralTesting.DensityLaw μ) (n : ℕ) :
    densityAffinity (iidDensityLaw L n) (iidDensityLaw R n) = densityAffinity L R ^ n := by
  have hp : ∀ᵐ xs : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i, 0 ≤ L.density (xs i) := by
    filter_upwards [ae_le_pi (fun _ : Fin n => L.nonneg)] with xs hx
    exact hx
  have hq : ∀ᵐ xs : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i, 0 ≤ R.density (xs i) := by
    filter_upwards [ae_le_pi (fun _ : Fin n => R.nonneg)] with xs hx
    exact hx
  have he : (fun xs : Fin n → Ω =>
      Real.sqrt ((iidDensityLaw L n).density xs) * Real.sqrt ((iidDensityLaw R n).density xs)) =ᵐ[
        Measure.pi (fun _ : Fin n => μ)]
      fun xs => ∏ i, Real.sqrt (L.density (xs i)) * Real.sqrt (R.density (xs i)) := by
    filter_upwards [hp, hq] with xs hpx hqx
    change Real.sqrt (∏ i, L.density (xs i)) * Real.sqrt (∏ i, R.density (xs i)) = _
    rw [Lower.sqrt_finite_product _ hpx, Lower.sqrt_finite_product _ hqx,
      Finset.prod_mul_distrib]
  unfold densityAffinity
  rw [integral_congr_ae he]
  rw [integral_fin_nat_prod_eq_prod (fun _ : Fin n =>
    fun x : Ω => Real.sqrt (L.density x) * Real.sqrt (R.density x))]
  simp

theorem hellinger_iid_le [SigmaFinite μ] (L R : GeneralTesting.DensityLaw μ) (n : ℕ) :
    GeneralTesting.hellingerSquared (iidDensityLaw L n) (iidDensityLaw R n) ≤
      n * GeneralTesting.hellingerSquared L R := by
  rw [hellinger_integral_eq, densityAffinity_iid, hellinger_integral_eq]
  have h := one_add_mul_sub_le_pow (by linarith [densityAffinity_nonneg L R] :
    -1 ≤ densityAffinity L R) n
  nlinarith

/-- Quadratic Hellinger bound for an affine density path on an arbitrary
measurable observation space, with all density inequalities almost everywhere. -/
theorem affine_hellinger_bound [IsProbabilityMeasure μ]
    (L R : GeneralTesting.DensityLaw μ) (f₀ f₁ : Ω → ℝ)
    (t s cf Cf : ℝ) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (hL : L.density =ᵐ[μ] fun x => f₀ x + t * f₁ x)
    (hR : R.density =ᵐ[μ] fun x => f₀ x + s * f₁ x)
    (ht : ∀ᵐ x ∂μ, cf ≤ f₀ x + t * f₁ x)
    (hs : ∀ᵐ x ∂μ, cf ≤ f₀ x + s * f₁ x)
    (hf₁ : ∀ᵐ x ∂μ, |f₁ x| ≤ Cf) :
    GeneralTesting.hellingerSquared L R ≤ Cf ^ 2 * (t - s) ^ 2 / (4 * cf) := by
  have hx : ∀ᵐ x ∂μ, (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2 ≤
      Cf ^ 2 * (t - s) ^ 2 / (4 * cf) := by
    filter_upwards [hL, hR, ht, hs, hf₁] with x hxL hxR hxt hxs hxf
    rw [hxL, hxR]
    have h := Lower.square_root_difference_bound hcf hxt hxs
    have hsq : f₁ x ^ 2 ≤ Cf ^ 2 := by
      nlinarith [sq_abs (f₁ x), abs_nonneg (f₁ x), hxf]
    have hid : (f₀ x + t * f₁ x - (f₀ x + s * f₁ x)) ^ 2 =
        f₁ x ^ 2 * (t - s) ^ 2 := by ring
    rw [hid] at h
    exact le_trans h (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)) (by positivity))
  have hi := integral_mono_ae (hellinger_integrable L R)
    (integrable_const (Cf ^ 2 * (t - s) ^ 2 / (4 * cf))) hx
  simpa [GeneralTesting.hellingerSquared] using hi

def densityLawWithSeed {S : Type*} [MeasurableSpace S] (ν : Measure S)
    [SigmaFinite μ] [IsProbabilityMeasure ν] (L : GeneralTesting.DensityLaw μ) :
    GeneralTesting.DensityLaw (μ.prod ν) where
  density x := L.density x.1
  measurable := L.measurable.comp measurable_fst
  integrable := by
    simpa using L.integrable.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : S => (1 : ℝ)) ν)
  nonneg := by
    filter_upwards [quasiMeasurePreserving_fst.tendsto_ae.eventually L.nonneg] with x hx
    exact hx
  integral_one := by
    rw [integral_fun_fst]
    simp [L.integral_one]

theorem densityLawWithSeed_measure {S : Type*} [MeasurableSpace S] (ν : Measure S)
    [SigmaFinite μ] [IsProbabilityMeasure ν] (L : GeneralTesting.DensityLaw μ) :
    (densityLawWithSeed ν L).measure = L.measure.prod ν := by
  unfold densityLawWithSeed GeneralTesting.DensityLaw.measure
  exact (prod_withDensity_left (ENNReal.measurable_ofReal.comp L.measurable)).symm

theorem hellinger_with_seed {S : Type*} [MeasurableSpace S] (ν : Measure S)
    [SigmaFinite μ] [IsProbabilityMeasure ν] (L R : GeneralTesting.DensityLaw μ) :
    GeneralTesting.hellingerSquared (densityLawWithSeed ν L) (densityLawWithSeed ν R) =
      GeneralTesting.hellingerSquared L R := by
  change (∫ x : Ω × S, (Real.sqrt (L.density x.1) - Real.sqrt (R.density x.1)) ^ 2 ∂μ.prod ν) =
    ∫ x, (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2 ∂μ
  rw [integral_fun_fst (fun x => (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2)]
  simp

/-- General-measure affine-path lower bound at a local perturbation scale.
An arbitrary independent probability seed is allowed, and every measurable
estimator is quantified. -/
theorem affine_path_local_testing [IsProbabilityMeasure μ]
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (P : ℝ → GeneralTesting.DensityLaw μ) (f₀ f₁ : Ω → ℝ) (F : ℝ → ℝ)
    (l r t₀ D cf Cf : ℝ) (ht₀ : t₀ ∈ Set.Ioo l r)
    (hF : HasDerivAt F D t₀) (hD : D ≠ 0) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (hdens : ∀ t ∈ Set.Ioo l r, (P t).density =ᵐ[μ] fun x => f₀ x + t * f₁ x)
    (hpos : ∀ t ∈ Set.Ioo l r, ∀ᵐ x ∂μ, cf ≤ f₀ x + t * f₁ x)
    (hscore : ∀ᵐ x ∂μ, |f₁ x| ≤ Cf) :
    ∀ᶠ h in nhdsWithin (0 : ℝ) ({0}ᶜ), ∀ n : ℕ,
      (n : ℝ) * Cf ^ 2 * h ^ 2 / cf ≤ 1 / 4 →
      ∀ (g : (Fin n → Ω) × S → ℝ), Measurable g →
        ∃ t ∈ Set.Ioo l r,
          (1 / 4 ≤ ((Measure.pi (fun _ : Fin n => (P t).measure)).prod ν).real
            {xs | |D| * |h| / 2 ≤ |g xs - F t|}) ∧
          (ENNReal.ofReal (|D| * |h| / 4) ≤ eLpNorm (fun xs => g xs - F t) 2
            ((Measure.pi (fun _ : Fin n => (P t).measure)).prod ν)) := by
  classical
  have hJ : Set.Ioo l r ∈ nhds t₀ := isOpen_Ioo.mem_nhds ht₀
  have hplus : ∀ᶠ h in nhds (0 : ℝ), t₀ + h ∈ Set.Ioo l r := by
    have ht : Filter.Tendsto (fun h : ℝ => t₀ + h) (nhds 0) (nhds t₀) := by
      simpa using tendsto_const_nhds.add (Filter.tendsto_id :
        Filter.Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0))
    exact ht.eventually hJ
  have hminus : ∀ᶠ h in nhds (0 : ℝ), t₀ - h ∈ Set.Ioo l r := by
    have ht : Filter.Tendsto (fun h : ℝ => t₀ - h) (nhds 0) (nhds t₀) := by
      simpa using tendsto_const_nhds.sub (Filter.tendsto_id :
        Filter.Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0))
    exact ht.eventually hJ
  filter_upwards [Lower.derivative_symmetric_separation hF hD,
    hplus.filter_mono nhdsWithin_le_nhds, hminus.filter_mono nhdsWithin_le_nhds] with h hsep hp hm
  intro n hsmall g hg
  let L := densityLawWithSeed ν (iidDensityLaw (P (t₀ + h)) n)
  let R := densityLawWithSeed ν (iidDensityLaw (P (t₀ - h)) n)
  have hb := affine_hellinger_bound (P (t₀ + h)) (P (t₀ - h)) f₀ f₁
    (t₀ + h) (t₀ - h) cf Cf hcf hCf (hdens _ hp) (hdens _ hm)
    (hpos _ hp) (hpos _ hm) hscore
  have hh := hellinger_iid_le (P (t₀ + h)) (P (t₀ - h)) n
  have hi : GeneralTesting.hellingerSquared L R ≤ 1 / 4 := by
    dsimp [L, R]
    rw [hellinger_with_seed]
    have hscale : (n : ℝ) * (Cf ^ 2 * (t₀ + h - (t₀ - h)) ^ 2 / (4 * cf)) =
        (n : ℝ) * Cf ^ 2 * h ^ 2 / cf := by ring
    calc
      _ ≤ (n : ℝ) * GeneralTesting.hellingerSquared (P (t₀ + h)) (P (t₀ - h)) := hh
      _ ≤ (n : ℝ) * (Cf ^ 2 * (t₀ + h - (t₀ - h)) ^ 2 / (4 * cf)) :=
        mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n)
      _ = (n : ℝ) * Cf ^ 2 * h ^ 2 / cf := hscale
      _ ≤ 1 / 4 := hsmall
  have ht := GeneralTesting.two_point_absolute_large_error L R g hg
    (F (t₀ + h)) (F (t₀ - h)) hi
  rw [abs_sub_comm (F (t₀ - h)) (F (t₀ + h))] at ht
  have hL : L.measure = (Measure.pi (fun _ : Fin n => (P (t₀ + h)).measure)).prod ν := by
    dsimp [L]
    rw [densityLawWithSeed_measure, iidDensityLaw_measure]
  have hR : R.measure = (Measure.pi (fun _ : Fin n => (P (t₀ - h)).measure)).prod ν := by
    dsimp [R]
    rw [densityLawWithSeed_measure, iidDensityLaw_measure]
  rw [hL, hR] at ht
  rcases ht with ht | ht
  · have htail : 1 / 4 ≤ ((Measure.pi (fun _ : Fin n => (P (t₀ + h)).measure)).prod ν).real
        {xs | |D| * |h| / 2 ≤ |g xs - F (t₀ + h)|} := by
      refine le_trans ht (measureReal_mono ?_)
      intro xs hx
      change |F (t₀ + h) - F (t₀ - h)| / 2 ≤ |g xs - F (t₀ + h)| at hx
      change |D| * |h| / 2 ≤ |g xs - F (t₀ + h)|
      linarith
    exact ⟨t₀ + h, hp, htail, GeneralTesting.tailReal_to_eLpNorm _ g hg _
      (|D| * |h|) (mul_nonneg (abs_nonneg _) (abs_nonneg _)) htail⟩
  · have htail : 1 / 4 ≤ ((Measure.pi (fun _ : Fin n => (P (t₀ - h)).measure)).prod ν).real
        {xs | |D| * |h| / 2 ≤ |g xs - F (t₀ - h)|} := by
      refine le_trans ht (measureReal_mono ?_)
      intro xs hx
      change |F (t₀ + h) - F (t₀ - h)| / 2 ≤ |g xs - F (t₀ - h)| at hx
      change |D| * |h| / 2 ≤ |g xs - F (t₀ - h)|
      linarith
    exact ⟨t₀ - h, hm, htail, GeneralTesting.tailReal_to_eLpNorm _ g hg _
      (|D| * |h|) (mul_nonneg (abs_nonneg _) (abs_nonneg _)) htail⟩

/-- Root-`n` testing and L² risk for arbitrary observation and seed spaces. -/
theorem affine_path_rootn [IsProbabilityMeasure μ]
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (P : ℝ → GeneralTesting.DensityLaw μ) (f₀ f₁ : Ω → ℝ) (F : ℝ → ℝ)
    (l r t₀ D cf Cf a : ℝ) (ht₀ : t₀ ∈ Set.Ioo l r)
    (hF : HasDerivAt F D t₀) (hD : D ≠ 0) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (ha : 0 < a) (hsmall : Cf ^ 2 * a ^ 2 / cf ≤ 1 / 4)
    (hdens : ∀ t ∈ Set.Ioo l r, (P t).density =ᵐ[μ] fun x => f₀ x + t * f₁ x)
    (hpos : ∀ t ∈ Set.Ioo l r, ∀ᵐ x ∂μ, cf ≤ f₀ x + t * f₁ x)
    (hscore : ∀ᵐ x ∂μ, |f₁ x| ≤ Cf) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (g : (Fin n → Ω) × S → ℝ), Measurable g → ∃ t ∈ Set.Ioo l r,
        (1 / 4 ≤ ((Measure.pi (fun _ : Fin n => (P t).measure)).prod ν).real
          {xs | |D| * (a / Real.sqrt (n : ℝ)) / 2 ≤ |g xs - F t|}) ∧
        (ENNReal.ofReal (|D| * (a / Real.sqrt (n : ℝ)) / 4) ≤
          eLpNorm (fun xs => g xs - F t) 2
            ((Measure.pi (fun _ : Fin n => (P t).measure)).prod ν)) := by
  classical
  let h : ℕ → ℝ := fun n => a / Real.sqrt (n : ℝ)
  have hposn (n : ℕ) (hn : 1 ≤ n) : 0 < h n := by
    dsimp [h]
    exact div_pos ha (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have ht : Filter.Tendsto h Filter.atTop (nhdsWithin (0 : ℝ) ({0}ᶜ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hinv := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop))
      simpa [h, div_eq_mul_inv] using tendsto_const_nhds.mul hinv
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      simpa using ne_of_gt (hposn n hn)
  have hlocal := affine_path_local_testing ν P f₀ f₁ F l r t₀ D cf Cf ht₀
    hF hD hcf hCf hdens hpos hscore
  filter_upwards [ht.eventually hlocal, Filter.eventually_ge_atTop 1] with n hn hn₁
  intro g hg
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn₁)
  have hc : (n : ℝ) * Cf ^ 2 * h n ^ 2 / cf ≤ 1 / 4 := by
    have he : (n : ℝ) * Cf ^ 2 * h n ^ 2 / cf = Cf ^ 2 * a ^ 2 / cf := by
      dsimp [h]
      rw [div_pow, Real.sq_sqrt (le_of_lt hnr)]
      field_simp
    rw [he]
    exact hsmall
  obtain ⟨t, hJ, he, hL₂⟩ := hn n hc g hg
  rw [abs_of_pos (hposn n hn₁)] at he hL₂
  exact ⟨t, hJ, he, hL₂⟩

/-- Lemma 10 for arbitrary measurable observations: an affine positive density
path with nonzero target derivative has a strictly positive root-`n` minimax
RMSE lower bound. The minimax quantities quantify all measurable estimators on
the actual iid experiment with its independent uniform random seed. -/
theorem parametric_path_minimax_bound [IsProbabilityMeasure μ]
    (P : ℝ → GeneralTesting.DensityLaw μ) (f₀ f₁ : Ω → ℝ)
    (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (l r t₀ D cf Cf : ℝ) (ht₀ : t₀ ∈ Set.Ioo l r)
    (hF : HasDerivAt (fun t => T (P t).probabilityMeasure) D t₀)
    (hD : D ≠ 0) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (hdens : ∀ t ∈ Set.Ioo l r, (P t).density =ᵐ[μ] fun x => f₀ x + t * f₁ x)
    (hpos : ∀ t ∈ Set.Ioo l r, ∀ᵐ x ∂μ, cf ≤ f₀ x + t * f₁ x)
    (hscore : ∀ᵐ x ∂μ, |f₁ x| ≤ Cf)
    (hclass : ∀ t ∈ Set.Ioo l r, (P t).probabilityMeasure ∈ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ Model.minimaxRMSE n T C) ∧
      ((1 / 4 : ℝ≥0∞) ≤ Model.minimaxTail n T C (2 * c * (n : ℝ) ^ (-(1 / 2 : ℝ)))) := by
  classical
  obtain ⟨a, ha, hsmall⟩ := Lower.exists_small_parametric_amplitude cf Cf
  let c : ℝ := |D| * a / 4
  have hc : 0 < c := by dsimp [c]; positivity
  let ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hν : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  let _ : IsProbabilityMeasure ν := hν
  have hroot := affine_path_rootn ν P f₀ f₁ (fun t => T (P t).probabilityMeasure)
    l r t₀ D cf Cf a ht₀ hF hD hcf hCf ha hsmall hdens hpos hscore
  refine ⟨c, hc, ?_⟩
  filter_upwards [hroot] with n hn
  have hinv : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
  have he : c * (n : ℝ) ^ (-(1 / 2 : ℝ)) = |D| * (a / Real.sqrt (n : ℝ)) / 4 := by
    rw [hinv]
    dsimp [c]
    ring
  have het : 2 * c * (n : ℝ) ^ (-(1 / 2 : ℝ)) = |D| * (a / Real.sqrt (n : ℝ)) / 2 := by
    rw [hinv]
    dsimp [c]
    ring
  constructor
  · unfold Model.minimaxRMSE
    apply le_iInf
    intro g
    obtain ⟨t, ht, _, hL₂⟩ := hn g.val g.property
    change ENNReal.ofReal (|D| * (a / Real.sqrt (n : ℝ)) / 4) ≤
      eLpNorm (fun xs => g.val xs - T (P t).probabilityMeasure) 2
        (Model.randomizedExperiment n (P t).probabilityMeasure) at hL₂
    rw [he]
    exact le_iSup_of_le (P t).probabilityMeasure (le_iSup_of_le (hclass t ht) hL₂)
  · unfold Model.minimaxTail
    apply le_iInf
    intro g
    obtain ⟨t, ht, htail, _⟩ := hn g.val g.property
    change 1 / 4 ≤ (Model.randomizedExperiment n (P t).probabilityMeasure).real
      {xs | |D| * (a / Real.sqrt (n : ℝ)) / 2 ≤ |g.val xs - T (P t).probabilityMeasure|} at htail
    have hENN := ENNReal.ofReal_le_of_le_toReal htail
    norm_num only [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at hENN
    rw [het]
    exact le_iSup_of_le (P t).probabilityMeasure (le_iSup_of_le (hclass t ht) hENN)

end RoughRegime.LowerMeasure
