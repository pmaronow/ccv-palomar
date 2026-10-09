module

public import Mathlib


@[expose] public section

/-!
Algebraic and analytic ingredients of Section 4.
The declarations explicitly document which paper claims they cover.
-/

noncomputable section
open scoped BigOperators
open Complex
namespace RoughRegime.Upper

/-- The complete cosine generating series, with its constant term corrected to one. -/
def cosineKernel (q : ℂ) (t : ℝ) : ℂ :=
  2 * (∑' k : ℕ, q ^ k * (Real.cos ((k : ℝ) * t) : ℂ)) - 1

lemma cosine_geometric_term (q : ℂ) (t : ℝ) (k : ℕ) :
    q ^ k * (Real.cos ((k : ℝ) * t) : ℂ) =
      ((q * Complex.exp ((t : ℂ) * I)) ^ k +
       (q * Complex.exp ((-t : ℂ) * I)) ^ k) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, mul_pow, mul_pow,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  push_cast
  rw [show -(↑k * (t : ℂ)) * I = ↑k * ((-t : ℂ) * I) by ring,
    show ↑k * (t : ℂ) * I = ↑k * ((t : ℂ) * I) by ring]
  ring

lemma cosine_geometric_hasSum (q : ℂ) (t : ℝ) (hq : ‖q‖ < 1) :
    HasSum (fun k : ℕ => q ^ k * (Real.cos ((k : ℝ) * t) : ℂ))
      (((1 - q * Complex.exp ((t : ℂ) * I))⁻¹ +
        (1 - q * Complex.exp ((-t : ℂ) * I))⁻¹) / 2) := by
  have ha : ‖q * Complex.exp ((t : ℂ) * I)‖ < 1 := by
    simpa [norm_mul] using hq
  have hb : ‖q * Complex.exp ((-t : ℂ) * I)‖ < 1 := by
    simpa only [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one] using hq
  convert ((hasSum_geometric_of_norm_lt_one ha).add
    (hasSum_geometric_of_norm_lt_one hb)).div_const 2 using 1
  ext k
  exact cosine_geometric_term q t k

/-- Poisson-kernel identity underlying Lemma 4, for complex `q` in the open unit disk. -/
theorem cosineKernel_eq (q : ℂ) (t : ℝ) (hq : ‖q‖ < 1) :
    cosineKernel q t =
      (1 - q ^ 2) / (1 - 2 * q * (Real.cos t : ℂ) + q ^ 2) := by
  let E : ℂ := Complex.exp ((t : ℂ) * I)
  let F : ℂ := Complex.exp ((-t : ℂ) * I)
  have hEF : E * F = 1 := by
    dsimp [E, F]
    rw [← Complex.exp_add]
    have hz : (t : ℂ) * I + (-t : ℂ) * I = 0 := by push_cast; ring
    rw [hz, Complex.exp_zero]
  have hsum : E + F = 2 * (Real.cos t : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos]
    dsimp [E, F]
    ring
  have hE : 1 - q * E ≠ 0 := by
    intro h
    have : q * E = 1 := by linear_combination -h
    have hnorm : ‖q * E‖ < 1 := by simpa [E, norm_mul] using hq
    simpa [this] using hnorm
  have hF : 1 - q * F ≠ 0 := by
    intro h
    have : q * F = 1 := by linear_combination -h
    have hnorm : ‖q * F‖ < 1 := by
      dsimp [F]
      simpa only [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one] using hq
    simpa [this] using hnorm
  have hden : 1 - 2 * q * (Real.cos t : ℂ) + q ^ 2 =
      (1 - q * E) * (1 - q * F) := by
    calc
      _ = 1 - q * (E + F) + q ^ 2 * (E * F) := by rw [hsum, hEF]; ring
      _ = _ := by ring
  rw [cosineKernel, (cosine_geometric_hasSum q t hq).tsum_eq]
  change 2 * (((1 - q * E)⁻¹ + (1 - q * F)⁻¹) / 2) - 1 = _
  rw [hden]
  field_simp
  linear_combination -q ^ 2 * hEF

/-- Interval Chebyshev expansion in angular coordinates (the generating identity in Lemma 4). -/
theorem chebyshev_generating_angular (ρ : ℝ) (z : ℂ) (t : ℝ)
    (h : ‖(-(ρ : ℂ) * z)‖ < 1) :
    cosineKernel (-(ρ : ℂ) * z) t =
      (1 - (ρ : ℂ) ^ 2 * z ^ 2) /
      (1 + 2 * (ρ : ℂ) * z * (Real.cos t : ℂ) + (ρ : ℂ) ^ 2 * z ^ 2) := by
  rw [cosineKernel_eq _ _ h]
  congr 1 <;> ring

/-- The midpoint, half-width, geometric mean, and convergence ratio of the paper. -/
def intervalCenter (lo hi : ℝ) : ℝ := (hi + lo) / 2
def intervalHalfWidth (lo hi : ℝ) : ℝ := (hi - lo) / 2
def intervalGeometricMean (lo hi : ℝ) : ℝ := Real.sqrt (lo * hi)
def intervalRho (lo hi : ℝ) : ℝ :=
  (Real.sqrt hi - Real.sqrt lo) / (Real.sqrt hi + Real.sqrt lo)

lemma intervalRho_pos (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    0 < intervalRho lo hi := by
  unfold intervalRho
  exact div_pos (sub_pos.mpr (Real.sqrt_lt_sqrt hlo.le hlt))
    (add_pos (Real.sqrt_pos.mpr (lt_trans hlo hlt)) (Real.sqrt_pos.mpr hlo))

lemma intervalRho_lt_one (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    intervalRho lo hi < 1 := by
  unfold intervalRho
  have hu := Real.sqrt_pos.mpr hlo
  have hv := Real.sqrt_pos.mpr (lt_trans hlo hlt)
  apply (div_lt_one (add_pos hv hu)).mpr
  linarith

/-- The two normalization identities used at `z = 1` in Lemma 4. -/
lemma interval_normalizations (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    (1 - intervalRho lo hi ^ 2) * intervalCenter lo hi =
      intervalGeometricMean lo hi * (1 + intervalRho lo hi ^ 2) ∧
    (1 - intervalRho lo hi ^ 2) * intervalHalfWidth lo hi =
      2 * intervalRho lo hi * intervalGeometricMean lo hi := by
  have hhi : 0 < hi := lt_trans hlo hlt
  have hu := Real.sqrt_pos.mpr hlo
  have hv := Real.sqrt_pos.mpr hhi
  have hs : Real.sqrt hi + Real.sqrt lo ≠ 0 := ne_of_gt (add_pos hv hu)
  unfold intervalRho intervalCenter intervalHalfWidth intervalGeometricMean
  rw [Real.sqrt_mul hlo.le]
  constructor <;> field_simp <;>
    nlinarith [Real.sq_sqrt hlo.le, Real.sq_sqrt hhi.le]

lemma interval_angular_pos (lo hi t : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    0 < intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos t := by
  have hc := Real.neg_one_le_cos t
  have hd : 0 < intervalHalfWidth lo hi := by unfold intervalHalfWidth; positivity
  have hm := mul_le_mul_of_nonneg_left hc hd.le
  unfold intervalCenter intervalHalfWidth at *
  nlinarith

/-- The normalized reciprocal cosine series in Lemma 4, without any assumed series identity. -/
theorem interval_reciprocal_angular (lo hi t : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    cosineKernel (-(intervalRho lo hi : ℂ)) t =
      (intervalGeometricMean lo hi : ℂ) /
        (intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos t : ℝ) := by
  let ρ := intervalRho lo hi
  have hρ := intervalRho_pos lo hi hlo hlt
  have hρ1 := intervalRho_lt_one lo hi hlo hlt
  have hq : ‖(-(ρ : ℂ))‖ < 1 := by simpa [ρ, norm_neg, Complex.norm_real, abs_of_pos hρ] using hρ1
  have hn := interval_normalizations lo hi hlo hlt
  have hC := hn.1
  have hD := hn.2
  have hpositive := interval_angular_pos lo hi t hlo hlt
  have hnonzero : intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos t ≠ 0 := ne_of_gt hpositive
  have hgpositive : 0 < intervalGeometricMean lo hi := by
    unfold intervalGeometricMean
    exact Real.sqrt_pos.mpr (mul_pos hlo (lt_trans hlo hlt))
  have hgzero : intervalGeometricMean lo hi ≠ 0 := ne_of_gt hgpositive
  have hden :
      (1 - 2 * (-(ρ : ℂ)) * (Real.cos t : ℂ) + (-(ρ : ℂ)) ^ 2) *
      (intervalGeometricMean lo hi : ℂ) =
      (1 - (-(ρ : ℂ)) ^ 2) *
      (intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos t : ℝ) := by
    have hr : (1 - 2 * (-ρ) * Real.cos t + (-ρ) ^ 2) *
        intervalGeometricMean lo hi = (1 - (-ρ) ^ 2) *
        (intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos t) := by
      dsimp [ρ]
      linear_combination -hC - Real.cos t * hD
    exact_mod_cast hr
  rw [cosineKernel_eq _ _ hq]
  have hdnonzero : (1 - 2 * (-(ρ : ℂ)) * (Real.cos t : ℂ) + (-(ρ : ℂ)) ^ 2) ≠ 0 := by
    have hA : (1 - ρ ^ 2 : ℝ) ≠ 0 := by nlinarith
    have hB : (1 - (-(ρ : ℂ)) ^ 2) ≠ 0 := by
      simpa only [neg_sq] using (show (1 - (ρ : ℂ) ^ 2) ≠ 0 by exact_mod_cast hA)
    intro hz
    rw [hz, zero_mul] at hden
    have : ((1 - (-(ρ : ℂ)) ^ 2) *
      (intervalCenter lo hi + intervalHalfWidth lo hi * Real.cos t : ℝ)) ≠ 0 :=
      mul_ne_zero hB (by exact_mod_cast hnonzero)
    exact this hden.symm
  apply (div_eq_div_iff hdnonzero (by exact_mod_cast hnonzero)).mpr
  simpa only [mul_comm] using hden.symm


open MeasureTheory ProbabilityTheory

/-- Ordered, distinct-sample lift of one monomial. The denominator is exactly `(n)_q`. -/
def monomialLift {Ω : Type*} {n q p : ℕ} (σ : Fin q → Fin p)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  (n.descFactorial q : ℝ)⁻¹ *
    ∑ e : Fin q ↪ Fin n, ∏ i : Fin q, X (e i) ω (σ i)

lemma monomial_product_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n q p : ℕ}
    (σ : Fin q → Fin p) (X : Fin n → Ω → Fin p → ℝ)
    (hm : ∀ j, Measurable (X j)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ j ω i, |X j ω i| ≤ M) (e : Fin q ↪ Fin n) :
    Integrable (fun ω => ∏ i : Fin q, X (e i) ω (σ i)) μ := by
  have hcoord : ∀ i : Fin q, Measurable (fun ω => X (e i) ω (σ i)) := by
    intro i
    exact (measurable_pi_apply (σ i)).comp (hm (e i))
  have hmeas : Measurable (fun ω => ∏ i : Fin q, X (e i) ω (σ i)) := by
    exact Finset.measurable_prod _ (fun i _ => hcoord i)
  apply (integrable_const (M ^ q)).mono' hmeas.aestronglyMeasurable
  filter_upwards [] with ω
  simp only [norm_prod, Real.norm_eq_abs]
  calc
    ∏ i : Fin q, |X (e i) ω (σ i)| ≤ ∏ _i : Fin q, M :=
      Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hb (e i) ω (σ i))
    _ = M ^ q := by simp

/-- Exact unbiasedness of the monomial lift, the building block of Lemma 7.
This proof uses independence and equal coordinate means, not an assumed lift identity. -/
theorem monomialLift_unbiased {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n q p : ℕ}
    (σ : Fin q → Fin p) (X : Fin n → Ω → Fin p → ℝ)
    (hq : q ≤ n) (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (m : Fin p → ℝ) (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = m i) :
    ∫ ω, monomialLift σ X ω ∂μ = ∏ i : Fin q, m (σ i) := by
  have hprod (e : Fin q ↪ Fin n) :
      ∫ ω, (∏ i : Fin q, X (e i) ω (σ i)) ∂μ = ∏ i : Fin q, m (σ i) := by
    have hind : iIndepFun (fun i : Fin q => fun ω => X (e i) ω (σ i)) μ := by
      exact (hi.precomp e.injective).comp
        (fun i : Fin q => fun v : Fin p → ℝ => v (σ i))
        (fun i => measurable_pi_apply (σ i))
    rw [hind.integral_fun_prod_eq_prod_integral]
    · simp only [hmean]
    · intro i
      exact ((measurable_pi_apply (σ i)).comp (hm (e i))).aestronglyMeasurable
  have hzero : (n.descFactorial q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hq))
  unfold monomialLift
  rw [integral_const_mul, integral_finsetSum]
  · simp only [hprod, Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro e _
    exact monomial_product_integrable μ σ X hm M hM hb e


/-- The Chebyshev series of Lemma 4; index `k + 1` enumerates the positive integers. -/
def reciprocalSeries (lo hi : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  1 + 2 * ∑' k : ℕ,
    (-(intervalRho lo hi : ℂ) * z) ^ (k + 1) *
      (((Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval
        ((x - intervalCenter lo hi) / intervalHalfWidth lo hi) : ℝ) : ℂ)

lemma reciprocalSeries_eq_cosineKernel (lo hi x : ℝ) (z : ℂ) (t : ℝ)
    (hrep : (x - intervalCenter lo hi) / intervalHalfWidth lo hi = Real.cos t)
    (hq : ‖(-(intervalRho lo hi : ℂ) * z)‖ < 1) :
    reciprocalSeries lo hi z x = cosineKernel (-(intervalRho lo hi : ℂ) * z) t := by
  let q : ℂ := -(intervalRho lo hi : ℂ) * z
  have hs := (cosine_geometric_hasSum q t hq).summable
  have heval (k : ℕ) :
      (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval (Real.cos t) =
        Real.cos (((k + 1 : ℕ) : ℝ) * t) := by
    simpa using Polynomial.Chebyshev.T_real_cos t (k + 1 : ℕ)
  unfold reciprocalSeries cosineKernel
  rw [hrep]
  simp_rw [heval]
  rw [hs.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, zero_mul, Real.cos_zero, Complex.ofReal_one, mul_one]
  change 1 + 2 * ∑' k : ℕ, q ^ (k + 1) * (Real.cos (((k + 1 : ℕ) : ℝ) * t) : ℂ) = _
  ring

lemma interval_argument_mem (lo hi x : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (hx : x ∈ Set.Icc lo hi) :
    (x - intervalCenter lo hi) / intervalHalfWidth lo hi ∈ Set.Icc (-1) 1 := by
  have hd : 0 < intervalHalfWidth lo hi := by unfold intervalHalfWidth; positivity
  constructor
  · apply (le_div_iff₀ hd).mpr
    unfold intervalCenter intervalHalfWidth
    linarith [hx.1]
  · apply (div_le_iff₀ hd).mpr
    unfold intervalCenter intervalHalfWidth
    linarith [hx.2]

lemma interval_series_radius (lo hi : ℝ) (z : ℂ) (hlo : 0 < lo) (hlt : lo < hi)
    (hz : ‖z‖ < (intervalRho lo hi)⁻¹) :
    ‖(-(intervalRho lo hi : ℂ) * z)‖ < 1 := by
  have hp := intervalRho_pos lo hi hlo hlt
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  rw [inv_eq_one_div] at hz
  simpa [mul_comm] using (lt_div_iff₀ hp).mp hz

/-- The full complex generating identity of Lemma 4, for the paper's exact interval parameters. -/
theorem reciprocal_expansion (lo hi x : ℝ) (z : ℂ) (hlo : 0 < lo) (hlt : lo < hi)
    (hx : x ∈ Set.Icc lo hi) (hz : ‖z‖ < (intervalRho lo hi)⁻¹) :
    reciprocalSeries lo hi z x =
      (1 - (intervalRho lo hi : ℂ) ^ 2 * z ^ 2) /
      (1 + 2 * (intervalRho lo hi : ℂ) * z *
        (((x - intervalCenter lo hi) / intervalHalfWidth lo hi : ℝ) : ℂ) +
        (intervalRho lo hi : ℂ) ^ 2 * z ^ 2) := by
  let y := (x - intervalCenter lo hi) / intervalHalfWidth lo hi
  let t := Real.arccos y
  have hy := interval_argument_mem lo hi x hlo hlt hx
  have hcos : Real.cos t = y := Real.cos_arccos hy.1 hy.2
  have hq := interval_series_radius lo hi z hlo hlt hz
  rw [reciprocalSeries_eq_cosineKernel lo hi x z t hcos.symm hq]
  rw [chebyshev_generating_angular _ _ _ hq, hcos]

/-- The `z = 1` reciprocal identity of Lemma 4, for every point in the interval. -/
theorem reciprocal_expansion_at_one (lo hi x : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (hx : x ∈ Set.Icc lo hi) :
    reciprocalSeries lo hi 1 x = (intervalGeometricMean lo hi : ℂ) / (x : ℂ) := by
  let y := (x - intervalCenter lo hi) / intervalHalfWidth lo hi
  let t := Real.arccos y
  have hy := interval_argument_mem lo hi x hlo hlt hx
  have hcos : Real.cos t = y := Real.cos_arccos hy.1 hy.2
  have hp := intervalRho_pos lo hi hlo hlt
  have hlt1 := intervalRho_lt_one lo hi hlo hlt
  have hq : ‖(-(intervalRho lo hi : ℂ) * (1 : ℂ))‖ < 1 := by
    simpa [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp] using hlt1
  rw [reciprocalSeries_eq_cosineKernel lo hi x 1 t hcos.symm hq]
  simp only [mul_one]
  rw [interval_reciprocal_angular lo hi t hlo hlt]
  congr 1
  congr 1
  rw [hcos]
  dsimp [y]
  have hd : intervalHalfWidth lo hi ≠ 0 := by unfold intervalHalfWidth; positivity
  field_simp
  ring


lemma monomialLift_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n q p : ℕ}
    (σ : Fin q → Fin p) (X : Fin n → Ω → Fin p → ℝ)
    (hm : ∀ j, Measurable (X j)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ j ω i, |X j ω i| ≤ M) :
    Integrable (monomialLift σ X) μ := by
  unfold monomialLift
  apply Integrable.const_mul
  exact integrable_finsetSum _ (fun e _ => monomial_product_integrable μ σ X hm M hM hb e)

/-- Slots of an exponent vector: variable `i` occurs `α i` times. -/
def ExponentSlots {p : ℕ} (α : Fin p →₀ ℕ) := Σ i : Fin p, Fin (α i)

instance {p : ℕ} (α : Fin p →₀ ℕ) : Fintype (ExponentSlots α) := by
  unfold ExponentSlots
  infer_instance

/-- A fixed ordering of the factors of a monomial. -/
def exponentCoordinates {p : ℕ} (α : Fin p →₀ ℕ) :
    Fin (Fintype.card (ExponentSlots α)) → Fin p :=
  fun j => ((Fintype.equivFin (ExponentSlots α)).symm j).1

lemma exponentSlots_card {p : ℕ} (α : Fin p →₀ ℕ) :
    Fintype.card (ExponentSlots α) = α.sum (fun _ e => e) := by
  unfold ExponentSlots
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Finsupp.sum_fintype α (fun _ e => e) (fun _ => rfl)).symm

lemma exponentCoordinates_prod {p : ℕ} (α : Fin p →₀ ℕ) (m : Fin p → ℝ) :
    (∏ j, m (exponentCoordinates α j)) = ∏ i : Fin p, m i ^ α i := by
  change (∏ j : Fin (Fintype.card (ExponentSlots α)),
    m (((Fintype.equivFin (ExponentSlots α)).symm j).1)) = _
  rw [Fintype.prod_equiv (Fintype.equivFin (ExponentSlots α)).symm
    (fun j => m (((Fintype.equivFin (ExponentSlots α)).symm j).1))
    (fun s : ExponentSlots α => m s.1) (fun _ => rfl)]
  unfold ExponentSlots
  rw [Fintype.prod_sigma]
  simp

/-- The polynomial lift, explicitly replacing each monomial by its distinct-sample statistic. -/
def polynomialLift {Ω : Type*} {n p : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  ∑ α ∈ F.support, F.coeff α * monomialLift (exponentCoordinates α) X ω

/-- Every bounded-observation polynomial of total degree at most `n` has an exactly
unbiased distinct-sample lift. This proves the expectation assertion of Lemma 7 in
monomial form; equivalence to its derivative notation is a separate combinatorial identity. -/
theorem polynomialLift_unbiased {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ)
    (hdeg : F.totalDegree ≤ n) (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω i, |X j ω i| ≤ M)
    (m : Fin p → ℝ) (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = m i) :
    ∫ ω, polynomialLift F X ω ∂μ = MvPolynomial.eval m F := by
  unfold polynomialLift
  rw [integral_finsetSum]
  · rw [MvPolynomial.eval_eq']
    apply Finset.sum_congr rfl
    intro α hα
    rw [integral_const_mul]
    have hcard : Fintype.card (ExponentSlots α) ≤ n := by
      rw [exponentSlots_card]
      exact (MvPolynomial.le_totalDegree hα).trans hdeg
    rw [monomialLift_unbiased μ (exponentCoordinates α) X hcard hi hm M hM hb m hmean,
      exponentCoordinates_prod]
  · intro α _
    exact (monomialLift_integrable μ (exponentCoordinates α) X hm M hM hb).const_mul _


lemma chebyshev_abs_le_one (y : ℝ) (hy : y ∈ Set.Icc (-1) 1) (k : ℕ) :
    |(Polynomial.Chebyshev.T ℝ (k : ℕ)).eval y| ≤ 1 := by
  have hc : Real.cos (Real.arccos y) = y := Real.cos_arccos hy.1 hy.2
  rw [← hc, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

/-- Absolute convergence of precisely the series appearing in Lemma 4. -/
theorem reciprocal_series_absolute_convergence (lo hi x : ℝ) (z : ℂ)
    (hlo : 0 < lo) (hlt : lo < hi) (hx : x ∈ Set.Icc lo hi)
    (hz : ‖z‖ < (intervalRho lo hi)⁻¹) :
    Summable (fun k : ℕ =>
      ‖(-(intervalRho lo hi : ℂ) * z) ^ (k + 1) *
        (((Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval
          ((x - intervalCenter lo hi) / intervalHalfWidth lo hi) : ℝ) : ℂ)‖) := by
  let q := -(intervalRho lo hi : ℂ) * z
  have hq := interval_series_radius lo hi z hlo hlt hz
  have hy := interval_argument_mem lo hi x hlo hlt hx
  have hs : Summable (fun k : ℕ => ‖q‖ ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hs
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg q) _) (chebyshev_abs_le_one _ hy _)


/-- Scalar real form of the reciprocal series. -/
lemma reciprocal_real_series (lo hi x : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (hx : x ∈ Set.Icc lo hi) :
    1 + 2 * ∑' k : ℕ, (-intervalRho lo hi) ^ (k + 1) *
      (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval
        ((x - intervalCenter lo hi) / intervalHalfWidth lo hi) =
      intervalGeometricMean lo hi / x := by
  have h := reciprocal_expansion_at_one lo hi x hlo hlt hx
  unfold reciprocalSeries at h
  simp only [mul_one, ← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_tsum, ← Complex.ofReal_ofNat, ← Complex.ofReal_div] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_add, Complex.ofReal_one] using h

/-- Scalar reciprocal truncation at total degree `m`. -/
def scalarReciprocalTruncation (lo hi : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  (intervalGeometricMean lo hi)⁻¹ *
    (1 + 2 * ∑ k ∈ Finset.range m, (-intervalRho lo hi) ^ (k + 1) *
      (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval
        ((x - intervalCenter lo hi) / intervalHalfWidth lo hi))

set_option maxHeartbeats 600000 in
/-- A sharp geometric bound for the scalar reciprocal truncation, the `ν' = 0`
scalar case of Lemma 5(a). -/
theorem scalar_reciprocal_truncation_error (lo hi x : ℝ) (m : ℕ)
    (hlo : 0 < lo) (hlt : lo < hi) (hx : x ∈ Set.Icc lo hi) :
    |x⁻¹ - scalarReciprocalTruncation lo hi m x| ≤
      2 / intervalGeometricMean lo hi * intervalRho lo hi ^ (m + 1) /
        (1 - intervalRho lo hi) := by
  let ρ := intervalRho lo hi
  let g := intervalGeometricMean lo hi
  let y := (x - intervalCenter lo hi) / intervalHalfWidth lo hi
  let f : ℕ → ℝ := fun k => (-ρ) ^ (k + 1) *
    (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval y
  have hp : 0 < ρ := intervalRho_pos lo hi hlo hlt
  have h1 : ρ < 1 := intervalRho_lt_one lo hi hlo hlt
  have hg : 0 < g := by
    dsimp [g, intervalGeometricMean]
    exact Real.sqrt_pos.mpr (mul_pos hlo (hlo.trans hlt))
  have hy := interval_argument_mem lo hi x hlo hlt hx
  have hb (k : ℕ) : ‖f k‖ ≤ ρ ^ (k + 1) := by
    dsimp [f]
    rw [abs_mul, abs_pow, abs_neg, abs_of_pos hp]
    exact mul_le_of_le_one_right (pow_nonneg hp.le _) (chebyshev_abs_le_one y hy _)
  have hgeom : Summable (fun k : ℕ => ρ ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hp.le h1)
  have hfnorm : Summable (fun k : ℕ => ‖f k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hgeom
  have hf : Summable f := hgeom.of_norm_bounded hb
  have hsplit := hf.sum_add_tsum_nat_add m
  have hrec : 1 + 2 * ∑' k, f k = g / x := reciprocal_real_series lo hi x hlo hlt hx
  have hidentity : x⁻¹ = g⁻¹ * (1 + 2 * ∑' k, f k) := by
    rw [hrec]
    field_simp [ne_of_gt hg]
  have hgap : x⁻¹ - scalarReciprocalTruncation lo hi m x =
      (2 / g) * ∑' k : ℕ, f (k + m) := by
    rw [hidentity]
    unfold scalarReciprocalTruncation
    change g⁻¹ * (1 + 2 * ∑' k, f k) - g⁻¹ * (1 + 2 * ∑ k ∈ Finset.range m, f k) = _
    rw [← hsplit]
    ring
  have hgeomTail : Summable (fun k : ℕ => ρ ^ (k + m + 1)) := by
    convert (summable_nat_add_iff m).mpr hgeom using 1
  have hnTail : Summable (fun k : ℕ => ‖f (k + m)‖) :=
    (summable_nat_add_iff (f := fun k : ℕ => ‖f k‖) m).mpr hfnorm
  have hNorm : ‖∑' k : ℕ, f (k + m)‖ ≤ ∑' k : ℕ, ‖f (k + m)‖ :=
    norm_tsum_le_tsum_norm hnTail
  have hcomp : (∑' k : ℕ, ‖f (k + m)‖) ≤ ∑' k : ℕ, ρ ^ (k + m + 1) :=
    Summable.tsum_le_tsum (fun k => hb (k + m)) hnTail hgeomTail
  have htail : |∑' k : ℕ, f (k + m)| ≤ ρ ^ (m + 1) / (1 - ρ) := by
    calc
      |∑' k : ℕ, f (k + m)| ≤ ∑' k : ℕ, ‖f (k + m)‖ :=
        hNorm
      _ ≤ ∑' k : ℕ, ρ ^ (k + m + 1) :=
        hcomp
      _ = ρ ^ (m + 1) / (1 - ρ) := by
        simp_rw [show ∀ k : ℕ, k + m + 1 = k + (m + 1) by omega, pow_add]
        rw [tsum_mul_right, tsum_geometric_of_lt_one hp.le h1]
        ring
  rw [hgap, abs_mul, abs_of_pos (div_pos (by norm_num) hg)]
  have hc : 0 ≤ 2 / g := div_nonneg (by norm_num) hg.le
  have hmul := mul_le_mul_of_nonneg_left htail hc
  convert hmul using 1 <;> ring

end RoughRegime.Upper
