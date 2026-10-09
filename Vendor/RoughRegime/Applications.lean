module

public import Mathlib


@[expose] public section

/-!
# Embedding and application reductions

This file proves the finite score embedding, Lemma 18 (hardness to risk),
the probability-event and Chebyshev steps of Lemma 19, and explicit
algebraic constructions used in Appendices B--D. The asymptotic lower
bound and the pilot's concentration theorem are not asserted here.
-/

noncomputable section
open scoped BigOperators ENNReal Topology
open Filter MeasureTheory

namespace RoughRegime.Applications

/-- Expectation on a fixed finite response support. -/
def expectation {ι : Type*} [Fintype ι] (π f : ι → ℝ) : ℝ :=
  ∑ i, π i * f i

/-- The affine response law of equation (49). -/
def affineLaw {ι : Type*} (π su sv : ι → ℝ) (u v : ℝ) : ι → ℝ :=
  fun i => π i * (1 + u * su i + v * sv i)

lemma expectation_affine {ι : Type*} [Fintype ι]
    (π su sv f : ι → ℝ) (u v : ℝ) :
    expectation (affineLaw π su sv u v) f =
      expectation π f + u * expectation π (fun i => f i * su i) +
        v * expectation π (fun i => f i * sv i) := by
  classical
  unfold expectation affineLaw
  calc
    _ = ∑ i, (π i * f i + u * (π i * (f i * su i)) +
      v * (π i * (f i * sv i))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]

lemma affineLaw_normalized {ι : Type*} [Fintype ι]
    (π su sv : ι → ℝ) (u v : ℝ)
    (hπ : expectation π (fun _ => 1) = 1)
    (hu : expectation π su = 0) (hv : expectation π sv = 0) :
    expectation (affineLaw π su sv u v) (fun _ => 1) = 1 := by
  simpa [hπ, hu, hv] using expectation_affine π su sv (fun _ => 1) u v

lemma affineLaw_positive {ι : Type*} (π su sv : ι → ℝ) (u v : ℝ)
    (hπ : ∀ i, 0 ≤ π i)
    (hsmall : ∀ i, |u| * |su i| + |v| * |sv i| ≤ 1 / 2) :
    ∀ i, π i / 2 ≤ affineLaw π su sv u v i := by
  intro i
  have hs : |u * su i + v * sv i| ≤ 1 / 2 :=
    (abs_add_le _ _).trans (by simpa [abs_mul] using hsmall i)
  have hl := (abs_le.mp hs).1
  unfold affineLaw
  nlinarith [mul_nonneg (hπ i) (show 0 ≤ 1 + u * su i + v * sv i - 1 / 2 by linarith)]

lemma expectation_sub_smul {ι : Type*} [Fintype ι]
    (π U D : ι → ℝ) (a : ℝ) :
    expectation π (fun i => U i - a * D i) =
      expectation π U - a * expectation π D := by
  classical
  unfold expectation
  calc
    _ = ∑ i, (π i * U i - a * (π i * D i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The moment formulas implied by the score identities (not assumed as conclusions). -/
theorem score_embedding_moments {ι : Type*} [Fintype ι]
    (π su sv D U V : ι → ℝ) (a0 b0 u v : ℝ)
    (hU : expectation π (fun i => U i - a0 * D i) = 0)
    (hV : expectation π (fun i => V i - b0 * D i) = 0)
    (hUu : expectation π (fun i => (U i - a0 * D i) * su i) = 1)
    (hUv : expectation π (fun i => (U i - a0 * D i) * sv i) = 0)
    (hVu : expectation π (fun i => (V i - b0 * D i) * su i) = 0)
    (hVv : expectation π (fun i => (V i - b0 * D i) * sv i) = 1) :
    let π' := affineLaw π su sv u v
    expectation π' U = a0 * expectation π' D + u ∧
      expectation π' V = b0 * expectation π' D + v := by
  dsimp
  have h1 := expectation_affine π su sv (fun i => U i - a0 * D i) u v
  have h2 := expectation_affine π su sv (fun i => V i - b0 * D i) u v
  rw [hU, hUu, hUv, expectation_sub_smul] at h1
  rw [hV, hVu, hVv, expectation_sub_smul] at h2
  constructor <;> linarith

lemma generic_functional_decomposition (mU mV w a0 b0 : ℝ) (hw : w ≠ 0) :
    mU * mV / w = a0 * mV + b0 * mU - a0 * b0 * w +
      (mU - a0 * w) * (mV - b0 * w) / w := by
  field_simp
  ring

lemma regression_ratio (a0 w ℓ : ℝ) (hw : w ≠ 0) :
    (a0 * w + ℓ) / w = a0 + ℓ / w := by
  field_simp

/-- The local target integrand in the positive-definite score case. -/
def localIntegrand (c0 cu cv lam w0 du dv u v : ℝ) : ℝ :=
  c0 + cu * u + cv * v + lam * u * v / (w0 + du * u + dv * v)

lemma localIntegrand_v_derivative (c0 cu cv lam w0 du dv u : ℝ)
    (hw : w0 + du * u ≠ 0) :
    deriv (fun v => localIntegrand c0 cu cv lam w0 du dv u v) 0 =
      cv + lam * u / (w0 + du * u) := by
  have ha : HasDerivAt (fun v : ℝ => c0 + cu * u + cv * v) cv 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul cv |>.const_add (c0 + cu * u)
  have hn : HasDerivAt (fun v : ℝ => lam * u * v) (lam * u) 0 :=
    by simpa using (hasDerivAt_id (0 : ℝ)).const_mul (lam * u)
  have hd : HasDerivAt (fun v : ℝ => w0 + du * u + dv * v) dv 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul dv |>.const_add (w0 + du * u)
  have h := ha.add (hn.div hd (by simpa using hw))
  have he := h.deriv
  change deriv (fun v => localIntegrand c0 cu cv lam w0 du dv u v) 0 = _ at he
  rw [he]
  simp only [mul_zero, add_zero, zero_mul, sub_zero]
  field_simp

/-- The actual differentiability statement for the affine-score parametric path. -/
theorem localIntegrand_v_hasDerivAt (c0 cu cv lam w0 du dv u : ℝ)
    (hw : w0 + du * u ≠ 0) :
    HasDerivAt (fun v => localIntegrand c0 cu cv lam w0 du dv u v)
      (cv + lam * u / (w0 + du * u)) 0 := by
  have ha : HasDerivAt (fun v : ℝ => c0 + cu * u + cv * v) cv 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul cv |>.const_add (c0 + cu * u)
  have hn : HasDerivAt (fun v : ℝ => lam * u * v) (lam * u) 0 :=
    by simpa using (hasDerivAt_id (0 : ℝ)).const_mul (lam * u)
  have hd : HasDerivAt (fun v : ℝ => w0 + du * u + dv * v) dv 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul dv |>.const_add (w0 + du * u)
  have h := ha.add (hn.div hd (by simpa using hw))
  simp only [mul_zero, add_zero, zero_mul, sub_zero] at h
  have hv : cv + lam * u / (w0 + du * u) = cv + lam * u * (w0 + du * u) / (w0 + du * u) ^ 2 := by
    field_simp
  rw [hv]
  exact h

/-- The nonvanishing slope assertion used for every sufficiently small nonzero
constant perturbation in Proposition 15(b). -/
theorem localIntegrand_nonzero_slope_near (c0 cu cv lam w0 du dv : ℝ)
    (hlam : lam ≠ 0) (hw0 : w0 ≠ 0) :
    ∀ᶠ u in 𝓝 (0 : ℝ), u ≠ 0 →
      deriv (fun v => localIntegrand c0 cu cv lam w0 du dv u v) 0 ≠ 0 := by
  have hd : ContinuousAt (fun u : ℝ => w0 + du * u) 0 := by fun_prop
  have hden : ∀ᶠ u in 𝓝 (0 : ℝ), w0 + du * u ≠ 0 :=
    hd.eventually_ne (by simpa using hw0)
  by_cases hcv : cv = 0
  · filter_upwards [hden] with u hu
    intro hune
    rw [localIntegrand_v_derivative c0 cu cv lam w0 du dv u hu, hcv, zero_add]
    exact div_ne_zero (mul_ne_zero hlam hune) hu
  · have hn : ContinuousAt (fun u : ℝ => lam * u) 0 := by fun_prop
    have hc : ContinuousAt (fun u : ℝ => cv + lam * u / (w0 + du * u)) 0 :=
      continuousAt_const.add (hn.div hd (by simpa using hw0))
    have hne := hc.eventually_ne (by simpa using hcv)
    filter_upwards [hden, hne] with u hu huneq
    intro _
    rw [localIntegrand_v_derivative c0 cu cv lam w0 du dv u hu]
    exact huneq

/-- Nonzero interaction derivative required by the local lower-bound embedding. -/
theorem localIntegrand_mixed_derivative (c0 cu cv lam w0 du dv : ℝ)
    (hw0 : w0 ≠ 0) :
    deriv (fun u => deriv (fun v => localIntegrand c0 cu cv lam w0 du dv u v) 0) 0 = lam / w0 := by
  have hn : HasDerivAt (fun u : ℝ => lam * u) lam 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_mul lam
  have hd : HasDerivAt (fun u : ℝ => w0 + du * u) du 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul du |>.const_add w0
  have h := (hn.div hd (by simpa using hw0)).const_add cv
  have heq : (fun u => deriv (fun v => localIntegrand c0 cu cv lam w0 du dv u v) 0) =ᶠ[𝓝 0]
      (fun u => cv + lam * u / (w0 + du * u)) := by
    have hc : ContinuousAt (fun u : ℝ => w0 + du * u) 0 := by fun_prop
    filter_upwards [hc.eventually_ne (by simpa using hw0)] with u hu
    exact localIntegrand_v_derivative c0 cu cv lam w0 du dv u hu
  have he := (h.congr_of_eventuallyEq heq).deriv
  rw [he]
  simp only [mul_zero, add_zero, zero_mul, sub_zero]
  field_simp

/-- The density margin argument used for the weighted constraints of Lemma 16. -/
theorem local_weighted_membership (p K k0 η δ rminus rplus : ℝ)
    (hk0 : 0 < k0) (hη : 0 ≤ η) (_hηsmall : η ≤ k0)
    (hrminus : 0 ≤ rminus) (hδ : 0 ≤ δ)
    (hpL : rminus + δ ≤ p) (hpU : p ≤ rplus - δ)
    (hK : |K - k0| ≤ η) (hmargin : rplus * η ≤ k0 * δ) :
    rminus * k0 ≤ p * K ∧ p * K ≤ rplus * k0 := by
  have hp : 0 ≤ p := by linarith
  have hr : p ≤ rplus := by linarith
  have hkl : k0 - η ≤ K := by linarith [(abs_le.mp hK).1]
  have hku : K ≤ k0 + η := by linarith [(abs_le.mp hK).2]
  have hl1 : p * (k0 - η) ≤ p * K := mul_le_mul_of_nonneg_left hkl hp
  have hl2 : (rminus + δ) * k0 ≤ p * k0 :=
    mul_le_mul_of_nonneg_right hpL hk0.le
  have hu1 : p * K ≤ p * (k0 + η) := mul_le_mul_of_nonneg_left hku hp
  have hu2 : p * k0 ≤ (rplus - δ) * k0 :=
    mul_le_mul_of_nonneg_right hpU hk0.le
  have he : p * η ≤ rplus * η := mul_le_mul_of_nonneg_right hr hη
  constructor <;> nlinarith

/-- A measurable estimator on an arbitrary experiment, including an experiment
with an auxiliary random seed. -/
abbrev Estimator (Ω : Type*) [MeasurableSpace Ω] := {f : Ω → ℝ // Measurable f}

instance estimator_nonempty (Ω : Type*) [MeasurableSpace Ω] : Nonempty (Estimator Ω) :=
  ⟨⟨fun _ => 0, measurable_const⟩⟩

def minimaxTail {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) (target : Θ → ℝ) (C : Set Θ) (t : ℝ) : ℝ≥0∞ :=
  ⨅ f : Estimator Ω, ⨆ θ ∈ C, laws θ {x | t ≤ |f.val x - target θ|}

def minimaxMSE {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) (target : Θ → ℝ) (C : Set Θ) : ℝ≥0∞ :=
  ⨅ f : Estimator Ω, ⨆ θ ∈ C,
    ∫⁻ x, ENNReal.ofReal ((f.val x - target θ) ^ 2) ∂laws θ

def minimaxRMSE {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) (target : Θ → ℝ) (C : Set Θ) : ℝ≥0∞ :=
  (minimaxMSE laws target C) ^ (1 / 2 : ℝ)

lemma square_tail_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (t : ℝ) (ht : 0 ≤ t) :
    ENNReal.ofReal (t ^ 2) * μ {x | t ≤ |f x|} ≤
      ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
  have hs : MeasurableSet {x | t ≤ |f x|} := measurableSet_le measurable_const hf.abs
  rw [← lintegral_indicator_const hs]
  apply lintegral_mono
  intro x
  by_cases hx : t ≤ |f x|
  · rw [Set.indicator_of_mem (show x ∈ {x | t ≤ |f x|} from hx)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_abs (f x), sq_nonneg (|f x| - t)]
  · rw [Set.indicator_of_notMem (show x ∉ {x | t ≤ |f x|} from hx)]
    exact bot_le

lemma minimaxTail_mono_class {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) (target : Θ → ℝ) {C D : Set Θ} (hCD : C ⊆ D) (t : ℝ) :
    minimaxTail laws target C t ≤ minimaxTail laws target D t := by
  apply iInf_mono
  intro f
  apply iSup_mono
  intro θ
  apply iSup_le
  intro hθ
  exact le_iSup_of_le (hCD hθ) le_rfl

lemma minimaxMSE_lower_of_tail {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) (target : Θ → ℝ) (C : Set Θ) (t : ℝ) (ht : 0 ≤ t) :
    ENNReal.ofReal (t ^ 2) * minimaxTail laws target C t ≤
      minimaxMSE laws target C := by
  rw [minimaxTail, minimaxMSE, ENNReal.mul_iInf]
  · apply iInf_mono
    intro f
    rw [ENNReal.mul_iSup]
    apply iSup_mono
    intro θ
    rw [ENNReal.mul_iSup]
    apply iSup_mono
    intro _
    exact square_tail_lower (laws θ) (fun x => f.val x - target θ)
      (f.property.sub measurable_const) t ht
  · intro h
    exact (ENNReal.ofReal_ne_top h).elim

/-- Square root is an order isomorphism even for infinite nonnegative risks. -/
def halfPowerOrderIso : ℝ≥0∞ ≃o ℝ≥0∞ where
  toFun x := x ^ (1 / 2 : ℝ)
  invFun x := x ^ (2 : ℝ)
  left_inv x := by dsimp; rw [← ENNReal.rpow_mul]; norm_num
  right_inv x := by dsimp; rw [← ENNReal.rpow_mul]; norm_num
  map_rel_iff' := by exact ENNReal.rpow_le_rpow_iff (by norm_num)

lemma eLpNorm_two_eq_squaredIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) :
    eLpNorm f 2 μ = (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  congr 2
  funext x
  rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]

/-- Bridge to the paper's infimum of supremum RMSE, rather than merely a
square root placed outside the minimax operations. -/
theorem minimaxRMSE_eq_eLpNorm {Ω Θ : Type*} [MeasurableSpace Ω]
    (laws : Θ → Measure Ω) (target : Θ → ℝ) (C : Set Θ) :
    minimaxRMSE laws target C =
      ⨅ f : Estimator Ω, ⨆ θ ∈ C, eLpNorm (fun x => f.val x - target θ) 2 (laws θ) := by
  change halfPowerOrderIso (⨅ f : Estimator Ω, ⨆ θ ∈ C,
    ∫⁻ x, ENNReal.ofReal ((f.val x - target θ) ^ 2) ∂laws θ) = _
  rw [halfPowerOrderIso.map_iInf]
  apply iInf_congr
  intro f
  rw [halfPowerOrderIso.map_iSup]
  apply iSup_congr
  intro θ
  rw [halfPowerOrderIso.map_iSup]
  apply iSup_congr
  intro _
  exact (eLpNorm_two_eq_squaredIntegral (laws θ) _ (f.property.sub measurable_const)).symm

/-- Lemma 18, including extended MSE and RMSE. The laws may be any experiment,
so the theorem also applies after adjoining independent estimator randomness. -/
theorem hardness_to_risk {Θ : Type*} {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)]
    (laws : (n : ℕ) → Θ → Measure (Ω n)) (target : Θ → ℝ)
    (Cn : ℕ → Set Θ) (C : Set Θ) (tn : ℕ → ℝ)
    (ht : ∀ n, 0 ≤ tn n)
    (hC : ∀ᶠ n in atTop, Cn n ⊆ C)
    (hhard : (3 / 8 : ℝ≥0∞) ≤
      Filter.liminf (fun n => minimaxTail (laws n) target (Cn n) (tn n)) atTop) :
    ∀ᶠ n in atTop,
      (1 / 4 : ℝ≥0∞) ≤ minimaxTail (laws n) target C (tn n) ∧
      ENNReal.ofReal (tn n / 2) ≤ minimaxRMSE (laws n) target C := by
  have he : ∀ᶠ n in atTop, (1 / 4 : ℝ≥0∞) <
      minimaxTail (laws n) target (Cn n) (tn n) :=
    Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le (by
      have h : ENNReal.ofReal (1 / 4 : ℝ) < ENNReal.ofReal (3 / 8 : ℝ) :=
        ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.2 (by norm_num)
      simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8),
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using h) hhard)
  filter_upwards [he, hC] with n hn hCn
  have hp : (1 / 4 : ℝ≥0∞) ≤ minimaxTail (laws n) target C (tn n) :=
    hn.le.trans (minimaxTail_mono_class (laws n) target hCn (tn n))
  refine ⟨hp, ?_⟩
  have hm : ENNReal.ofReal ((tn n / 2) ^ 2) ≤ minimaxMSE (laws n) target C := by
    calc
      _ = ENNReal.ofReal ((tn n) ^ 2) * (1 / 4 : ℝ≥0∞) := by
        calc
          _ = ENNReal.ofReal ((tn n) ^ 2 * (1 / 4 : ℝ)) := by congr 1; ring
          _ = ENNReal.ofReal ((tn n) ^ 2) * ENNReal.ofReal (1 / 4 : ℝ) :=
            ENNReal.ofReal_mul (sq_nonneg _)
          _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]; norm_num
      _ ≤ ENNReal.ofReal ((tn n) ^ 2) * minimaxTail (laws n) target C (tn n) :=
        by gcongr
      _ ≤ _ := minimaxMSE_lower_of_tail (laws n) target C (tn n) (ht n)
  unfold minimaxRMSE
  have hh := (ENNReal.le_rpow_inv_iff (x := ENNReal.ofReal (tn n / 2))
    (y := minimaxMSE (laws n) target C) (by norm_num : (0 : ℝ) < 2)).2
  have hh' : ENNReal.ofReal (tn n / 2) ^ (2 : ℝ) ≤ minimaxMSE (laws n) target C := by
    rw [ENNReal.rpow_two]
    rw [ENNReal.ofReal_pow (div_nonneg (ht n) (by norm_num)) 2] at hm
    exact hm
  simpa only [one_div] using hh hh' 

/-- The deterministic event implication in Lemma 19(b). -/
theorem reverse_transfer_event (L t e a b c : ℝ)
    (hL : 0 < L) (_ht : 0 < t) (he : e ≤ t / 2)
    (hbound : c ≤ L * (a + b) + e) (hc : t ≤ c) :
    t / (4 * L) ≤ a ∨ t / (4 * L) ≤ b := by
  by_contra h
  push Not at h
  have h1 : a * (4 * L) < t := (lt_div_iff₀ (by positivity)).mp h.1
  have h2 : b * (4 * L) < t := (lt_div_iff₀ (by positivity)).mp h.2
  nlinarith

lemma lipschitz_reverse_error {M : Type*} [PseudoMetricSpace M]
    (Φ : ℝ → M → ℝ) (L e xhat x y : ℝ) (mhat m : M)
    (hLip : ∀ a b q r, |Φ a q - Φ b r| ≤ L * (|a - b| + dist q r))
    (hrelation : |y - Φ x m| ≤ e) :
    |Φ xhat mhat - y| ≤ L * (|xhat - x| + dist mhat m) + e := by
  calc
    _ ≤ |Φ xhat mhat - Φ x m| + |Φ x m - y| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (hLip _ _ _ _) (by simpa [abs_sub_comm] using hrelation)

/-- The actual probability union bound, independent of the particular estimator. -/
theorem reverse_transfer_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (a b c : Ω → ℝ) (L t e : ℝ)
    (hL : 0 < L) (ht : 0 < t) (he : e ≤ t / 2)
    (hbound : ∀ x, c x ≤ L * (a x + b x) + e) :
    μ.real {x | t ≤ c x} ≤
      μ.real {x | t / (4 * L) ≤ a x} + μ.real {x | t / (4 * L) ≤ b x} := by
  apply (measureReal_mono (μ := μ) ?_).trans (measureReal_union_le _ _)
  intro x hx
  exact reverse_transfer_event L t e (a x) (b x) (c x) hL ht he (hbound x) hx

/-- Chebyshev's moment term in equation (59). -/
theorem reverse_transfer_chebyshev {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (b : Ω → ℝ)
    (hb : ∀ x, 0 ≤ b x) (hbint : Integrable (fun x => (b x) ^ 2) μ)
    (L t B n : ℝ) (hL : 0 < L) (ht : 0 < t) (hn : 0 < n)
    (hsecond : (∫ x, (b x) ^ 2 ∂μ) ≤ B ^ 2 / n) :
    μ.real {x | t / (4 * L) ≤ b x} ≤ 16 * L ^ 2 * B ^ 2 / (n * t ^ 2) := by
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (ae_of_all μ (fun x => sq_nonneg (b x))) hbint ((t / (4 * L)) ^ 2)
  have hevents : {x | t / (4 * L) ≤ b x} = {x | (t / (4 * L)) ^ 2 ≤ (b x) ^ 2} := by
    ext x
    change t / (4 * L) ≤ b x ↔ (t / (4 * L)) ^ 2 ≤ (b x) ^ 2
    constructor
    · intro hx
      nlinarith [hb x, show 0 < t / (4 * L) by positivity]
    · intro hx
      nlinarith [hb x, show 0 < t / (4 * L) by positivity]
  rw [← hevents] at hmark
  have hmul : (t / (4 * L)) ^ 2 * μ.real {x | t / (4 * L) ≤ b x} ≤ B ^ 2 / n :=
    hmark.trans hsecond
  let q : ℝ := μ.real {x | t / (4 * L) ≤ b x}
  change (t / (4 * L)) ^ 2 * q ≤ B ^ 2 / n at hmul
  change q ≤ 16 * L ^ 2 * B ^ 2 / (n * t ^ 2)
  apply (le_div_iff₀ (show 0 < n * t ^ 2 by positivity)).2
  have hd := (mul_le_mul_of_nonneg_left hmul (show 0 ≤ n * (4 * L) ^ 2 by positivity))
  field_simp [hL.ne', hn.ne'] at hd
  nlinarith

/-- The empirical average in an actual independent product experiment. -/
def empiricalMean {Ω : Type*} {n : ℕ} (h : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, h (x i)

lemma empiricalMean_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (h : Ω → ℝ) (hh : MemLp h 2 μ) :
    MemLp (empiricalMean (n := n) h) 2 (Measure.pi (fun _ : Fin n => μ)) := by
  unfold empiricalMean
  exact (memLp_finsetSum Finset.univ (fun i _ =>
    hh.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i))).const_mul _

lemma empiricalMean_expectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0) (h : Ω → ℝ) (hh : MemLp h 2 μ) :
    (∫ x, empiricalMean (n := n) h x ∂Measure.pi (fun _ : Fin n => μ)) = ∫ x, h x ∂μ := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hi : ∀ i : Fin n,
      (∫ x, h (x i) ∂Measure.pi (fun _ : Fin n => μ)) = ∫ x, h x ∂μ := by
    intro i
    have hp := measurePreserving_eval (fun _ : Fin n => μ) i
    have he := (integral_map hp.aemeasurable (hp.map_eq ▸ hh.aestronglyMeasurable)).symm
    rw [hp.map_eq] at he
    exact he
  unfold empiricalMean
  rw [integral_const_mul]
  have hint := integral_finsetSum Finset.univ (fun (i : Fin n) _ =>
    (hh.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i)).integrable (by norm_num))
  change (∫ a, ∑ i : Fin n, h (a i) ∂Measure.pi (fun _ : Fin n => μ)) =
    ∑ i : Fin n, ∫ a, h (a i) ∂Measure.pi (fun _ : Fin n => μ) at hint
  rw [hint]
  simp_rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Exact empirical-mean MSE identity used to obtain the pilot bound in Lemma 19. -/
theorem empiricalMean_mse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0) (h : Ω → ℝ) (hh : MemLp h 2 μ) :
    (∫ x, (empiricalMean (n := n) h x - ∫ y, h y ∂μ) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) =
    (∫ y, (h y - ∫ z, h z ∂μ) ^ 2 ∂μ) / n := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hem := empiricalMean_memLp μ h hh (n := n)
  nth_rw 1 [← empiricalMean_expectation μ hn h hh]
  rw [← ProbabilityTheory.variance_eq_integral hem.aemeasurable]
  unfold empiricalMean
  rw [ProbabilityTheory.variance_const_mul]
  have hv := ProbabilityTheory.variance_sum_pi
    (μ := fun _ : Fin n => μ) (X := fun _ : Fin n => h) (fun _ => hh)
  have hsum : (∑ i : Fin n, fun x : Fin n → Ω => h (x i)) =
      (fun x => ∑ i : Fin n, h (x i)) := by ext x; simp
  rw [hsum] at hv
  rw [hv, ProbabilityTheory.variance_eq_integral hh.aemeasurable]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Clipping the empirical mean to a valid compact interval can only decrease MSE. -/
theorem projected_empiricalMean_mse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0) (h : Ω → ℝ) (hh : MemLp h 2 μ)
    (lo hi : ℝ) (hlohi : lo ≤ hi) (hm : (∫ y, h y ∂μ) ∈ Set.Icc lo hi)
    (hmh : Measurable h) :
    (∫ x, ((Set.projIcc lo hi hlohi (empiricalMean (n := n) h x) : ℝ) - ∫ y, h y ∂μ) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) ≤
    (∫ y, (h y - ∫ z, h z ∂μ) ^ 2 ∂μ) / n := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  have he : Integrable (fun x => (empiricalMean (n := n) h x - ∫ y, h y ∂μ) ^ 2) ν :=
    ((empiricalMean_memLp μ h hh).sub (memLp_const _)).integrable_sq
  have hc : ∀ x, ((Set.projIcc lo hi hlohi (empiricalMean (n := n) h x) : ℝ) - ∫ y, h y ∂μ) ^ 2 ≤
      (empiricalMean (n := n) h x - ∫ y, h y ∂μ) ^ 2 := by
    intro x
    have hp := Set.abs_projIcc_sub_projIcc hlohi
      (c := empiricalMean (n := n) h x) (d := ∫ y, h y ∂μ)
    rw [Set.projIcc_of_mem hlohi hm] at hp
    nlinarith [sq_abs ((Set.projIcc lo hi hlohi (empiricalMean (n := n) h x) : ℝ) - ∫ y, h y ∂μ),
      sq_abs (empiricalMean (n := n) h x - ∫ y, h y ∂μ),
      abs_nonneg ((Set.projIcc lo hi hlohi (empiricalMean (n := n) h x) : ℝ) - ∫ y, h y ∂μ)]
  have hmeas : Measurable (empiricalMean (n := n) h) := by unfold empiricalMean; fun_prop
  have hclip : Continuous (fun t : ℝ => (Set.projIcc lo hi hlohi t : ℝ)) :=
    continuous_subtype_val.comp continuous_projIcc
  have hproj : AEStronglyMeasurable (fun x =>
      ((Set.projIcc lo hi hlohi (empiricalMean (n := n) h x) : ℝ) - ∫ y, h y ∂μ) ^ 2) ν :=
    (((hclip.measurable.comp hmeas).sub measurable_const).pow_const 2).aestronglyMeasurable
  have hpint := he.mono' hproj (ae_of_all ν (fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hc x))
  exact (integral_mono hpint he hc).trans_eq (empiricalMean_mse μ hn h hh)

/-- The minimax probability-transfer inequality of Lemma 19(b), with
an explicit measurable moment estimator satisfying the required second-moment bound.
`M` may be the rectangle subtype, with its induced Euclidean metric. -/
theorem reverse_transfer_minimax {Ω Θ M : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    (laws : Θ → Measure Ω) [∀ θ, IsFiniteMeasure (laws θ)]
    (T0 T1 : Θ → ℝ) (C : Set Θ)
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (Φ : Set.Icc lo hi → M → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    (μhat : Ω → M) (hμhat : Measurable μhat) (μtrue : Θ → M)
    (L t e B n : ℝ) (hL : 0 < L) (ht : 0 < t) (hn : 0 < n) (he : e ≤ t / 2)
    (hLip : ∀ a b q r, |Φ a q - Φ b r| ≤ L * (|(a : ℝ) - b| + dist q r))
    (hmem : ∀ θ ∈ C, T0 θ ∈ Set.Icc lo hi)
    (hrelation : ∀ θ ∈ C,
      |T1 θ - Φ (Set.projIcc lo hi hlohi (T0 θ)) (μtrue θ)| ≤ e)
    (hpilotint : ∀ θ ∈ C, Integrable (fun x => (dist (μhat x) (μtrue θ)) ^ 2) (laws θ))
    (hpilot : ∀ θ ∈ C,
      (∫ x, (dist (μhat x) (μtrue θ)) ^ 2 ∂laws θ) ≤ B ^ 2 / n) :
    minimaxTail laws T1 C t ≤ minimaxTail laws T0 C (t / (4 * L)) +
      ENNReal.ofReal (16 * L ^ 2 * B ^ 2 / (n * t ^ 2)) := by
  unfold minimaxTail
  rw [ENNReal.iInf_add]
  apply le_iInf
  intro f
  have hclip : Measurable (Set.projIcc lo hi hlohi) := continuous_projIcc.measurable
  let g : Estimator Ω := ⟨fun x => Φ (Set.projIcc lo hi hlohi (f.val x)) (μhat x),
    hΦ.comp ((hclip.comp f.property).prodMk hμhat)⟩
  apply (iInf_le _ g).trans
  apply iSup_le
  intro θ
  apply iSup_le
  intro hθ
  have hbound : ∀ x, |g.val x - T1 θ| ≤
      L * (|f.val x - T0 θ| + dist (μhat x) (μtrue θ)) + e := by
    intro x
    have hc := Set.abs_projIcc_sub_projIcc hlohi (c := f.val x) (d := T0 θ)
    rw [Set.projIcc_of_mem hlohi (hmem θ hθ)] at hc
    have hl := hLip (Set.projIcc lo hi hlohi (f.val x))
      (Set.projIcc lo hi hlohi (T0 θ)) (μhat x) (μtrue θ)
    have htri := abs_sub_le (g.val x)
      (Φ (Set.projIcc lo hi hlohi (T0 θ)) (μtrue θ)) (T1 θ)
    have hrel := hrelation θ hθ
    rw [abs_sub_comm (T1 θ)] at hrel
    have hmon : L * (|(Set.projIcc lo hi hlohi (f.val x) : ℝ) -
        (Set.projIcc lo hi hlohi (T0 θ) : ℝ)| + dist (μhat x) (μtrue θ)) ≤
        L * (|f.val x - T0 θ| + dist (μhat x) (μtrue θ)) := by
      rw [Set.projIcc_of_mem hlohi (hmem θ hθ)]
      exact mul_le_mul_of_nonneg_left (add_le_add hc le_rfl) hL.le
    exact htri.trans (add_le_add (hl.trans hmon) hrel)
  have hu := reverse_transfer_probability (laws θ)
    (fun x => |f.val x - T0 θ|) (fun x => dist (μhat x) (μtrue θ))
    (fun x => |g.val x - T1 θ|) L t e hL ht he hbound
  have hc := reverse_transfer_chebyshev (laws θ)
    (fun x => dist (μhat x) (μtrue θ)) (fun _ => dist_nonneg)
    (hpilotint θ hθ) L t B n hL ht hn (hpilot θ hθ)
  have hreal : (laws θ).real {x | t ≤ |g.val x - T1 θ|} ≤
      (laws θ).real {x | t / (4 * L) ≤ |f.val x - T0 θ|} +
      16 * L ^ 2 * B ^ 2 / (n * t ^ 2) := by linarith
  have henn := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (by positivity) (by positivity)] at henn
  simp only [measureReal_def] at henn
  rw [ENNReal.ofReal_toReal (measure_ne_top (laws θ) _),
      ENNReal.ofReal_toReal (measure_ne_top (laws θ) _)] at henn
  apply henn.trans
  exact add_le_add (le_iSup_of_le θ (le_iSup_of_le hθ le_rfl)) le_rfl

/-- Smooth-partition pilot: range preservation by convex combinations. -/
theorem pilot_convex_range {ι : Type*} [Fintype ι]
    (φ a : ι → ℝ) (ε : ℝ)
    (hφ : ∀ i, 0 ≤ φ i) (h1 : ∑ i, φ i = 1)
    (ha : ∀ i, ε ≤ a i ∧ a i ≤ 1 - ε) :
    ε ≤ (∑ i, φ i * a i) ∧ (∑ i, φ i * a i) ≤ 1 - ε := by
  constructor
  · calc
      ε = ∑ i, φ i * ε := by rw [← Finset.sum_mul, h1, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (ha i).1 (hφ i))
  · calc
      _ ≤ ∑ i, φ i * (1 - ε) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (ha i).2 (hφ i))
      _ = _ := by rw [← Finset.sum_mul, h1, one_mul]

/-- Smooth-partition pilot: deterministic uniform error bound at each point. -/
theorem pilot_convex_error {ι : Type*} [Fintype ι]
    (φ a : ι → ℝ) (w ζ : ℝ)
    (hφ : ∀ i, 0 ≤ φ i) (h1 : ∑ i, φ i = 1)
    (ha : ∀ i, φ i ≠ 0 → |a i - w| ≤ ζ) :
    |(∑ i, φ i * a i) - w| ≤ ζ := by
  have hi : ∀ i, |φ i * (a i - w)| ≤ φ i * ζ := by
    intro i
    by_cases h : φ i = 0
    · simp [h]
    · rw [abs_mul, abs_of_nonneg (hφ i)]
      exact mul_le_mul_of_nonneg_left (ha i h) (hφ i)
  calc
    _ = |∑ i, φ i * (a i - w)| := by
      congr 1
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
    _ ≤ ∑ i, |φ i * (a i - w)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, φ i * ζ := Finset.sum_le_sum (fun i _ => hi i)
    _ = ζ := by rw [← Finset.sum_mul, h1, one_mul]

/-- Three-point missing-at-random response family from Appendix B. -/
def marBaseline : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]
def marR : Fin 3 → ℝ := ![0, 1, 1]
def marRY : Fin 3 → ℝ := ![0, 0, 1]
def marScoreU : Fin 3 → ℝ := ![1, -1, -1]
def marScoreV : Fin 3 → ℝ := ![0, -4, 4]

 theorem mar_scores :
    expectation marBaseline marScoreU = 0 ∧
    expectation marBaseline marScoreV = 0 ∧
    expectation marBaseline (fun i => (1 - 2 * marR i) * marScoreU i) = 1 ∧
    expectation marBaseline (fun i => (1 - 2 * marR i) * marScoreV i) = 0 ∧
    expectation marBaseline (fun i => (marRY i - marR i / 2) * marScoreU i) = 0 ∧
    expectation marBaseline (fun i => (marRY i - marR i / 2) * marScoreV i) = 1 := by
  norm_num [expectation, Fin.sum_univ_succ, marBaseline, marR, marRY, marScoreU, marScoreV]

 theorem mar_covariance :
    expectation marBaseline (fun i => (1 - 2 * marR i) ^ 2) = 1 ∧
    expectation marBaseline (fun i => (1 - 2 * marR i) * (marRY i - marR i / 2)) = 0 ∧
    expectation marBaseline (fun i => (marRY i - marR i / 2) ^ 2) = 1 / 8 := by
  norm_num [expectation, Fin.sum_univ_succ, marBaseline, marR, marRY]

 theorem mar_affine_law (u v : ℝ) :
    affineLaw marBaseline marScoreU marScoreV u v =
      ![(1 + u) / 2, (1 - u) / 4 - v, (1 - u) / 4 + v] := by
  ext i
  fin_cases i <;> simp [affineLaw, marBaseline, marScoreU, marScoreV] <;> ring

 theorem mar_moments (u v : ℝ) :
    expectation (affineLaw marBaseline marScoreU marScoreV u v) marR = (1 - u) / 2 ∧
    expectation (affineLaw marBaseline marScoreU marScoreV u v) marRY = (1 - u) / 4 + v := by
  rw [mar_affine_law]
  simp [expectation, marR, marRY, Fin.sum_univ_succ]
  ring

 theorem mar_regression (u v : ℝ) (hu : u ≠ 1) :
    ((1 - u) / 4 + v) / ((1 - u) / 2) = 1 / 2 + 2 * v / (1 - u) := by
  have h : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  field_simp
  ring

/-- ATT/ATU exact inverse relations, equation (63). -/
theorem att_atu_relations (ey μ0 μ1 pA : ℝ) (hp : pA ≠ 0) (hp1 : 1 - pA ≠ 0) :
    μ0 = ey - pA * ((ey - μ0) / pA) ∧
    μ1 = ey + (1 - pA) * ((μ1 - ey) / (1 - pA)) := by
  constructor <;> field_simp <;> ring

/-- Four-state response family from the overlap-weighted-effect proof. -/
def overlapS1 : Fin 4 → ℝ := ![1, 1, -1, -1]
def overlapS2 : Fin 4 → ℝ := ![1, -1, 1, -1]
def overlapA : Fin 4 → ℝ := fun i => (1 + overlapS1 i) / 2
def overlapY : Fin 4 → ℝ := fun i => (1 + overlapS2 i) / 2
def overlapLaw (c ℓ1 ℓ2 : ℝ) : Fin 4 → ℝ :=
  fun i => (1 + c * overlapS1 i * overlapS2 i +
    2 * ℓ1 * overlapS1 i + 2 * ℓ2 * overlapS2 i) / 4

theorem overlap_moments (c ℓ1 ℓ2 : ℝ) :
    expectation (overlapLaw c ℓ1 ℓ2) (fun _ => 1) = 1 ∧
    expectation (overlapLaw c ℓ1 ℓ2) overlapA = 1 / 2 + ℓ1 ∧
    expectation (overlapLaw c ℓ1 ℓ2) overlapY = 1 / 2 + ℓ2 ∧
    expectation (overlapLaw c ℓ1 ℓ2) (fun i => overlapA i * overlapY i) =
      (1 + c + 2 * ℓ1 + 2 * ℓ2) / 4 := by
  simp [expectation, overlapLaw, overlapA, overlapY, overlapS1, overlapS2, Fin.sum_univ_succ]
  and_intros <;> ring

theorem overlap_covariance (c ℓ1 ℓ2 : ℝ) :
    expectation (overlapLaw c ℓ1 ℓ2) (fun i => overlapA i * overlapY i) -
      expectation (overlapLaw c ℓ1 ℓ2) overlapA *
        expectation (overlapLaw c ℓ1 ℓ2) overlapY = c / 4 - ℓ1 * ℓ2 := by
  rcases overlap_moments c ℓ1 ℓ2 with ⟨_, ha, hy, hay⟩
  rw [ha, hy, hay]
  ring

theorem overlap_variance (c ℓ1 ℓ2 : ℝ) :
    expectation (overlapLaw c ℓ1 ℓ2) overlapA -
      (expectation (overlapLaw c ℓ1 ℓ2) overlapA) ^ 2 = 1 / 4 - ℓ1 ^ 2 := by
  rw [(overlap_moments c ℓ1 ℓ2).2.1]
  ring

theorem overlap_inverse_denominator (γ : ℝ) (hγ : γ ≠ 0) :
    (1 / 16 : ℝ) / γ = 1 / (16 * γ) := by
  field_simp

/-- At least one of the two excess-loss derivatives is separated from zero. -/
theorem excess_loss_derivative_separation (A B : ℝ) (_hA : 0 < A) :
    A / 4 ≤ |A / 2 - 2 * B| ∨ A / 4 ≤ |A - 2 * B| := by
  by_contra h
  push Not at h
  have h1 := abs_lt.mp h.1
  have h2 := abs_lt.mp h.2
  linarith

end RoughRegime.Applications
