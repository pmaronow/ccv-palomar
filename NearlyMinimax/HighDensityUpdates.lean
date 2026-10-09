module

public import NearlyMinimax.AtomicVariation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.Complex.Exponential


@[expose] public section

/-! The genuine finite density-mark operator used by the high-smoothness
lower bound. Tensor derivative marks are proved to extract the square-free
coefficient, and exterior marks produce the count selector. -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Polynomial
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def densityDerivativeWeight (D : ℕ) (j : Fin (derivativeOrder D + 1)) : ℝ :=
  lobattoDerivativeWeight ((D - 1) / 2) j

/-- The exponent selected by one first-derivative mark in every coordinate. -/
def densityUnitExponent (r : ℕ) : Fin r →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun _ => 1) (by simp)

@[simp] theorem densityUnitExponent_apply (r : ℕ) (i : Fin r) :
    densityUnitExponent r i = 1 := by simp [densityUnitExponent]

@[simp] theorem densityUnitExponent_degree (r : ℕ) :
    (densityUnitExponent r).degree = r := by
  simp [Finsupp.degree_eq_sum]

/-- Actual product of the finite Chebyshev derivative marks. -/
def densityDerivativeAction (r D : ℕ) (f : (Fin r → ℝ) → ℝ) : ℝ :=
  ∑ h : Fin r → Fin (derivativeOrder D + 1),
    (∏ l, densityDerivativeWeight D (h l)) *
      f (fun l => lobattoNode (derivativeOrder D) (h l))

theorem derivative_rule_monomial (D : ℕ) (hD : 1 ≤ D) (k : ℕ) (hk : k ≤ D) :
    (∑ j : Fin (derivativeOrder D + 1),
      densityDerivativeWeight D j *
        lobattoNode (derivativeOrder D) j ^ k) = if k = 1 then 1 else 0 := by
  have hp : (X ^ k : ℝ[X]).degree ≤ D := by
    simpa only [degree_X_pow, Nat.cast_withBot] using WithBot.coe_le_coe.mpr hk
  have h := derivative_rule_exact D hD (X ^ k) hp
  simpa [densityDerivativeWeight, ← coeff_zero_eq_eval_zero, coeff_derivative,
    coeff_X_pow, eq_comm] using h

theorem densityDerivativeAction_monomial (r D : ℕ) (hD : 1 ≤ D)
    (d : Fin r →₀ ℕ) (hd : ∀ l, d l ≤ D) :
    densityDerivativeAction r D (fun ε => ∏ l, ε l ^ d l) =
      if d = densityUnitExponent r then 1 else 0 := by
  unfold densityDerivativeAction
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (l : Fin r) (j : Fin (derivativeOrder D + 1)) =>
    densityDerivativeWeight D j * lobattoNode (derivativeOrder D) j ^ d l)]
  simp_rw [derivative_rule_monomial D hD _ (hd _)]
  by_cases he : d = densityUnitExponent r
  · subst d
    simp
  · rw [if_neg he]
    obtain ⟨l, hl⟩ : ∃ l, d l ≠ 1 := by
      by_contra hn
      apply he
      ext l
      simpa using not_exists.mp hn l
    apply Finset.prod_eq_zero (Finset.mem_univ l)
    simp [hl]

/-- Tensor exactness follows from the proved one-variable moments, without
an assumed mixed-derivative or interpolation identity. -/
theorem densityDerivativeAction_polynomial (r D : ℕ) (hD : 1 ≤ D)
    (P : MvPolynomial (Fin r) ℝ)
    (hP : ∀ d ∈ P.support, ∀ l, d l ≤ D) :
    densityDerivativeAction r D (fun ε => MvPolynomial.eval ε P) =
      P.coeff (densityUnitExponent r) := by
  unfold densityDerivativeAction
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  have hm (d : Fin r →₀ ℕ) :
      (∑ h : Fin r → Fin (derivativeOrder D + 1),
        (∏ l, densityDerivativeWeight D (h l)) *
          (P.coeff d * ∏ l, lobattoNode (derivativeOrder D) (h l) ^ d l)) =
        P.coeff d *
          ∑ h : Fin r → Fin (derivativeOrder D + 1),
            (∏ l, densityDerivativeWeight D (h l)) *
              ∏ l, lobattoNode (derivativeOrder D) (h l) ^ d l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    ring
  simp_rw [hm]
  have he (d : Fin r →₀ ℕ) (hd : d ∈ P.support) :
      (∑ h : Fin r → Fin (derivativeOrder D + 1),
        (∏ l, densityDerivativeWeight D (h l)) *
          ∏ l, lobattoNode (derivativeOrder D) (h l) ^ d l) =
        if d = densityUnitExponent r then 1 else 0 :=
    densityDerivativeAction_monomial r D hD d (hP d hd)
  calc
    _ = ∑ d ∈ P.support, P.coeff d * (if d = densityUnitExponent r then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [he d hd]
    _ = _ := by
      simp [Finset.sum_ite_eq', MvPolynomial.mem_support_iff]
      exact fun h => h.symm

/-- Each mark acts on one affine density factor. -/
def densityModulationPolynomial {ι : Type*} (r : ℕ) (B : ι → Fin r → ℝ)
    (i : ι) : MvPolynomial (Fin r) ℝ :=
  ∑ l, MvPolynomial.C (B i l) * MvPolynomial.X l

theorem densityModulationPolynomial_homogeneous {ι : Type*} (r : ℕ)
    (B : ι → Fin r → ℝ) (i : ι) :
    (densityModulationPolynomial r B i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro l _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- The product of the incoming densities after their affine mark reset. -/
def densityResetPolynomial {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (r : ℕ) (z t : ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) : MvPolynomial (Fin r) ℝ :=
  ∏ i ∈ S, (MvPolynomial.C z + MvPolynomial.C (t * p i) *
    densityModulationPolynomial r B i)

theorem densityResetPolynomial_eval {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (r : ℕ) (z t : ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) (ε : Fin r → ℝ) :
    MvPolynomial.eval ε (densityResetPolynomial S r z t p B) =
      ∏ i ∈ S, (z + t * p i * ∑ l, ε l * B i l) := by
  simp only [densityResetPolynomial, map_prod, map_add, map_mul,
    MvPolynomial.eval_C, densityModulationPolynomial, map_sum, MvPolynomial.eval_X]
  simp only [mul_comm (B _ _)]

theorem densityResetPolynomial_totalDegree {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (r : ℕ) (z t : ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    (densityResetPolynomial S r z t p B).totalDegree ≤ S.card := by
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le
      · simp
      · have h := (densityModulationPolynomial_homogeneous r B i).C_mul (t * p i)
        exact h.totalDegree_le
    _ = _ := by simp

/-- Exactly one occurrence of every mark selects only observation subsets
of cardinality r. -/
theorem densityResetPolynomial_coefficient {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (r : ℕ) (z t : ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    (densityResetPolynomial S r z t p B).coeff (densityUnitExponent r) =
      z ^ (S.card - r) * t ^ r *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) := by
  classical
  unfold densityResetPolynomial
  simp_rw [add_comm (MvPolynomial.C z)]
  rw [Finset.prod_add]
  simp only [MvPolynomial.coeff_sum]
  have he (U : Finset ι) (hU : U ∈ S.powerset) :
      ((∏ i ∈ U, MvPolynomial.C (t * p i) * densityModulationPolynomial r B i) *
        ∏ i ∈ S \ U, MvPolynomial.C z).coeff (densityUnitExponent r) =
      z ^ (S \ U).card * t ^ U.card * (∏ i ∈ U, p i) *
        (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) := by
    rw [Finset.prod_mul_distrib, ← map_prod, ← map_prod,
      mul_comm _ (MvPolynomial.C _), mul_assoc, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C_mul]
    simp only [Finset.prod_const, Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl he]
  have hz (U : Finset ι) (hU : U ∈ S.powerset) :
      z ^ (S \ U).card * t ^ U.card * (∏ i ∈ U, p i) *
        (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) =
      if U.card = r then
        z ^ (S.card - r) * t ^ r * ((∏ i ∈ U, p i) *
          (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r))
      else 0 := by
    by_cases hc : U.card = r
    · rw [if_pos hc, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hU), hc]
      ring
    · rw [if_neg hc]
      have hh := MvPolynomial.IsHomogeneous.prod U
        (fun i => densityModulationPolynomial r B i) (fun _ => 1)
        (fun i _ => densityModulationPolynomial_homogeneous r B i)
      have hzero := hh.coeff_eq_zero (d := densityUnitExponent r) (by simpa using Ne.symm hc)
      simp only [hzero, mul_zero]
  rw [Finset.sum_congr rfl hz]
  rw [← Finset.sum_filter, ← Finset.powersetCard_eq_filter, ← Finset.mul_sum]

theorem density_derivative_product_exact {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (r D : ℕ) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (z t : ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityDerivativeAction r D (fun ε => ∏ i ∈ S, (z + t * p i * ∑ l, ε l * B i l)) =
      z ^ (S.card - r) * t ^ r *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) := by
  have hf : (fun ε => ∏ i ∈ S, (z + t * p i * ∑ l, ε l * B i l)) =
      (fun ε => MvPolynomial.eval ε (densityResetPolynomial S r z t p B)) := by
    funext ε
    exact (densityResetPolynomial_eval S r z t p B ε).symm
  rw [hf]
  rw [densityDerivativeAction_polynomial r D hD]
  · exact densityResetPolynomial_coefficient S r z t p B
  · intro d hd l
    exact (MvPolynomial.le_degreeOf_of_mem_support l hd).trans
      ((MvPolynomial.degreeOf_le_totalDegree _ _).trans
        ((densityResetPolynomial_totalDegree S r z t p B).trans hSD))

/-- The quadratic density-interval margin in the manuscript. -/
def densityMargin (a b z : ℝ) : ℝ := (z - a) * (b - z) / (b - a)

theorem densityMargin_bounds (a b : ℝ) (hab : a < b) (z : ℝ) (hz : z ∈ Icc a b) :
    0 ≤ densityMargin a b z ∧ densityMargin a b z ≤ z - a ∧
      densityMargin a b z ≤ b - z ∧ densityMargin a b z ≤ (b - a) / 4 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hn : 0 ≤ z - a := sub_nonneg.mpr hz.1
  have hm : 0 ≤ b - z := sub_nonneg.mpr hz.2
  dsimp [densityMargin]
  refine ⟨div_nonneg (mul_nonneg hn hm) hba.le, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hba).mpr
    nlinarith
  · apply (div_le_iff₀ hba).mpr
    nlinarith
  · apply (div_le_iff₀ hba).mpr
    nlinarith [sq_nonneg (z - (a + b) / 2)]

theorem densityMargin_zero_ne (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    densityMargin a b 0 ≠ 0 := by
  unfold densityMargin
  exact div_ne_zero (mul_ne_zero (by simpa using ha.ne') (by simpa using (ha.trans hab).ne'))
    (sub_pos.mpr hab).ne'

def densityMarginPolynomial (a b : ℝ) : ℝ[X] :=
  (X - C a) * (C b - X) * C ((b - a)⁻¹)

@[simp] theorem densityMarginPolynomial_eval (a b z : ℝ) :
    (densityMarginPolynomial a b).eval z = densityMargin a b z := by
  simp [densityMarginPolynomial, densityMargin, div_eq_mul_inv]

theorem densityMarginPolynomial_natDegree (a b : ℝ) :
    (densityMarginPolynomial a b).natDegree ≤ 2 := by
  apply (natDegree_mul_le).trans
  have h₁ : (X - C a : ℝ[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have h₂ : (C b - X : ℝ[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hm := (natDegree_mul_le (p := X - C a) (q := C b - X)).trans (add_le_add h₁ h₂)
  simpa using hm

def densityCountPolynomial (a b : ℝ) (k r : ℕ) : ℝ[X] :=
  X ^ (k - r) * densityMarginPolynomial a b ^ r

@[simp] theorem densityCountPolynomial_eval (a b z : ℝ) (k r : ℕ) :
    (densityCountPolynomial a b k r).eval z = z ^ (k - r) * densityMargin a b z ^ r := by
  simp [densityCountPolynomial]

theorem densityCountPolynomial_natDegree (a b : ℝ) (k r : ℕ) (hrk : r ≤ k) :
    (densityCountPolynomial a b k r).natDegree ≤ k + r := by
  apply (natDegree_mul_le).trans
  have hp := (natDegree_pow_le (p := densityMarginPolynomial a b) (n := r)).trans
    (Nat.mul_le_mul_left r (densityMarginPolynomial_natDegree a b))
  simp only [natDegree_X_pow]
  omega

/-- The actual exterior count factor, including counts above the cutoff. -/
def densityCountCoefficient (a b : ℝ) (m r k : ℕ) : ℝ :=
  (∑ j : Fin (m + r + 1), exteriorWeight a b (m + r) j *
    (exteriorNode a b (m + r) j ^ (k - r) *
      densityMargin a b (exteriorNode a b (m + r) j) ^ r)) / densityMargin a b 0 ^ r

/-- Exact target-count selection is derived from the concrete exterior
rule: every other count through m is annihilated. -/
theorem densityCountCoefficient_exact (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r k : ℕ) (hr : 1 ≤ r) (hrk : r ≤ k) (hkm : k ≤ m) :
    densityCountCoefficient a b m r k = if k = r then 1 else 0 := by
  have hdeg : (densityCountPolynomial a b k r).degree ≤ m + r :=
    degree_le_natDegree.trans (by
      exact_mod_cast (densityCountPolynomial_natDegree a b k r hrk).trans (Nat.add_le_add_right hkm r))
  have he := exterior_rule_exact a b hab (m + r) (by omega)
    (densityCountPolynomial a b k r) hdeg
  simp only [densityCountPolynomial_eval] at he
  unfold densityCountCoefficient
  rw [he]
  by_cases hkr : k = r
  · subst k
    simp [pow_ne_zero r (densityMargin_zero_ne a b ha hab)]
  · have hpos : k - r ≠ 0 := by omega
    simp [zero_pow hpos, hkr]

/-- Uniform finite-variation control for the count factor beyond the cutoff. -/
theorem densityCountCoefficient_abs_bound (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r k : ℕ) (hr : 1 ≤ r) :
    |densityCountCoefficient a b m r k| ≤
      (b ^ (k - r) * ((b - a) / 4) ^ r / |densityMargin a b 0| ^ r) *
        Real.cosh ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) := by
  have hbn : 0 ≤ b := (ha.trans hab).le
  have hmn : 0 ≤ (b - a) / 4 := by positivity
  have hb : ∀ j : Fin (m + r + 1),
      |exteriorNode a b (m + r) j ^ (k - r) *
        densityMargin a b (exteriorNode a b (m + r) j) ^ r| ≤
      b ^ (k - r) * ((b - a) / 4) ^ r := by
    intro j
    have hz := exteriorNode_mem a b hab.le (m + r) j
    have ht := densityMargin_bounds a b hab _ hz
    rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg (ha.le.trans hz.1), abs_of_nonneg ht.1]
    exact mul_le_mul (pow_le_pow_left₀ (ha.le.trans hz.1) hz.2 _)
      (pow_le_pow_left₀ ht.1 ht.2.2.2 _) (pow_nonneg ht.1 _) (pow_nonneg hbn _)
  have hs : |∑ j : Fin (m + r + 1), exteriorWeight a b (m + r) j *
      (exteriorNode a b (m + r) j ^ (k - r) *
        densityMargin a b (exteriorNode a b (m + r) j) ^ r)| ≤
      Real.cosh ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) *
        (b ^ (k - r) * ((b - a) / 4) ^ r) := by
    calc
      _ ≤ ∑ j : Fin (m + r + 1), |exteriorWeight a b (m + r) j| *
          (b ^ (k - r) * ((b - a) / 4) ^ r) := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, exterior_rule_variation a b ha hab _ (by omega)]
  unfold densityCountCoefficient
  rw [abs_div, abs_pow]
  exact (div_le_div_of_nonneg_right hs (by positivity)).trans_eq (by ring)

/-- The incoming density is reset exactly as in (LB-loc-update). -/
def localDensityReset {ι : Type*} (a b : ℝ) (r : ℕ) (z : ℝ)
    (ε : Fin r → ℝ) (p : ι → ℝ) (B : ι → Fin r → ℝ) (i : ι) : ℝ :=
  z + densityMargin a b z / ((r : ℝ) * b) * p i * ∑ l, ε l * B i l

theorem localDensityReset_slope_bound {ι : Type*} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (r : ℕ) (hr : 1 ≤ r) (z : ℝ) (hz : z ∈ Icc a b)
    (ε : Fin r → ℝ) (hε : ∀ l, |ε l| ≤ 1) (B : ι → Fin r → ℝ) (i : ι)
    (hB : ∀ l, |B i l| ≤ 1) :
    |densityMargin a b z / ((r : ℝ) * b) * ∑ l, ε l * B i l| ≤
      (b - a) / (4 * b) := by
  have hb : 0 < b := ha.trans hab
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hθ := densityMargin_bounds a b hab z hz
  have hsum : |∑ l, ε l * B i l| ≤ (r : ℝ) := by
    calc
      _ ≤ ∑ l, |ε l * B i l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin r, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro l _
        rw [abs_mul]
        exact (mul_le_mul (hε l) (hB l) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
      _ = _ := by simp
  have hcoef : 0 ≤ densityMargin a b z / ((r : ℝ) * b) :=
    div_nonneg hθ.1 (mul_pos hrR hb).le
  rw [abs_mul, abs_of_nonneg hcoef]
  calc
    _ ≤ densityMargin a b z / ((r : ℝ) * b) * r :=
      mul_le_mul_of_nonneg_left hsum hcoef
    _ = densityMargin a b z / b := by field_simp
    _ ≤ ((b - a) / 4) / b := div_le_div_of_nonneg_right hθ.2.2.2 hb.le
    _ = _ := by ring

theorem localDensityReset_slope_lt_quarter (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    (b - a) / (4 * b) < 1 / 4 := by
  apply (div_lt_iff₀ (by nlinarith [ha.trans hab] : 0 < 4 * b)).mpr
  linarith

theorem localDensityReset_mem_interval {ι : Type*} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (r : ℕ) (hr : 1 ≤ r) (z : ℝ) (hz : z ∈ Icc a b)
    (ε : Fin r → ℝ) (hε : ∀ l, |ε l| ≤ 1) (p : ι → ℝ)
    (B : ι → Fin r → ℝ) (i : ι) (hp : p i ∈ Icc a b) (hB : ∀ l, |B i l| ≤ 1) :
    localDensityReset a b r z ε p B i ∈ Icc a b := by
  have hb : 0 < b := ha.trans hab
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hθ := densityMargin_bounds a b hab z hz
  have hp0 : 0 ≤ p i := ha.le.trans hp.1
  have hsum : |∑ l, ε l * B i l| ≤ (r : ℝ) := by
    calc
      _ ≤ ∑ l, |ε l * B i l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin r, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro l _
        rw [abs_mul]
        exact (mul_le_mul (hε l) (hB l) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
      _ = _ := by simp
  have hcoef : 0 ≤ densityMargin a b z / ((r : ℝ) * b) :=
    div_nonneg hθ.1 (mul_pos hrR hb).le
  have hshift : |densityMargin a b z / ((r : ℝ) * b) * p i * ∑ l, ε l * B i l| ≤
      densityMargin a b z := by
    rw [abs_mul, abs_mul, abs_of_nonneg hcoef, abs_of_nonneg hp0]
    calc
      _ ≤ densityMargin a b z / ((r : ℝ) * b) * p i * r :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hcoef hp0)
      _ = densityMargin a b z / b * p i := by field_simp
      _ ≤ densityMargin a b z / b * b :=
        mul_le_mul_of_nonneg_left hp.2 (div_nonneg hθ.1 hb.le)
      _ = _ := div_mul_cancel₀ _ hb.ne'
  obtain ⟨hl, hu⟩ := abs_le.mp hshift
  constructor <;> dsimp [localDensityReset] <;> linarith [hθ.2.1, hθ.2.2.1]

theorem localDensityReset_continuous {ι : Type*} (a b : ℝ) (r : ℕ)
    (B : ι → Fin r → ℝ) (i : ι) :
    Continuous (fun x : ℝ × (Fin r → ℝ) × ℝ =>
      localDensityReset a b r x.1 x.2.1 (fun _ => x.2.2) B i) := by
  unfold localDensityReset densityMargin
  fun_prop

/-- Symmetrization is the square-free coefficient divided by r!: it is
independent of any ordering chosen for the observation subset. -/
def densitySeparatedSym {ι : Type*} [DecidableEq ι] (r : ℕ)
    (B : ι → Fin r → ℝ) (S : Finset ι) : ℝ :=
  (∏ i ∈ S, densityModulationPolynomial r B i).coeff (densityUnitExponent r) /
    (r.factorial : ℝ)

def densityPacketPrefactor (a b : ℝ) (r : ℕ) : ℝ :=
  (r : ℝ) ^ r / (r.factorial : ℝ) * (b / densityMargin a b 0) ^ r

/-- The exact finite action of Gamma_{r,m}. -/
def densityPacketAction (a b : ℝ) (m r D : ℕ) (f : ℝ → (Fin r → ℝ) → ℝ) : ℝ :=
  densityPacketPrefactor a b r * ∑ j : Fin (m + r + 1),
    exteriorWeight a b (m + r) j *
      densityDerivativeAction r D (f (exteriorNode a b (m + r) j))

theorem density_packet_product_exact {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b r z ε p B i) =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) * densitySeparatedSym r B U := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hb : b ≠ 0 := (ha.trans hab).ne'
  have hθ : densityMargin a b 0 ≠ 0 := densityMargin_zero_ne a b ha hab
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  unfold densityPacketAction localDensityReset
  simp_rw [density_derivative_product_exact S r D hD hSD]
  unfold densityCountCoefficient densitySeparatedSym
  have hsum : (∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
      ((∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r) /
        (r.factorial : ℝ))) =
      (∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
        (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r)) /
        (r.factorial : ℝ) := by simp_rw [← mul_div_assoc]; rw [Finset.sum_div]
  rw [hsum]
  unfold densityPacketPrefactor
  simp only [div_pow, mul_pow]
  rw [Finset.mul_sum]
  calc
    _ = ∑ j : Fin (m + r + 1),
      (exteriorWeight a b (m + r) j *
        (exteriorNode a b (m + r) j ^ (S.card - r) *
          densityMargin a b (exteriorNode a b (m + r) j) ^ r) / densityMargin a b 0 ^ r) *
        ((∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) *
          (∏ i ∈ U, densityModulationPolynomial r B i).coeff (densityUnitExponent r)) /
          (r.factorial : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j _
      field_simp
    _ = _ := by simp only [← Finset.sum_mul, Finset.sum_div]

private def densityAssignmentExponent (r : ℕ) (f : Fin r → Fin r) : Fin r →₀ ℕ :=
  ∑ i, Finsupp.single (f i) 1

private theorem densityAssignmentExponent_eq_unit_iff (r : ℕ) (f : Fin r → Fin r) :
    densityAssignmentExponent r f = densityUnitExponent r ↔ Function.Bijective f := by
  classical
  constructor
  · intro he
    have hs : Function.Surjective f := by
      intro l
      by_contra hn
      have hne (i : Fin r) : f i ≠ l := fun h => hn ⟨i, h⟩
      have hv := congrArg (fun d : Fin r →₀ ℕ => d l) he
      simp [densityAssignmentExponent, hne] at hv
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  · intro hf
    let e := Equiv.ofBijective f hf
    change (∑ i, Finsupp.single (e i) 1) = densityUnitExponent r
    rw [e.sum_comp (fun l => Finsupp.single l 1)]
    ext l
    simp

/-- The selected coefficient is the genuine permanent, hence the sum of
all r! assignments of distinct marks to distinct observations. -/
theorem density_linear_product_permanent (r : ℕ) (B : Fin r → Fin r → ℝ) :
    (∏ i, densityModulationPolynomial r B i).coeff (densityUnitExponent r) =
      ∑ σ : Equiv.Perm (Fin r), ∏ i, B i (σ i) := by
  classical
  unfold densityModulationPolynomial
  rw [Fintype.prod_sum]
  simp_rw [MvPolynomial.C_mul_X_eq_monomial]
  have hm (f : Fin r → Fin r) :
      (∏ i, MvPolynomial.monomial (Finsupp.single (f i) 1) (B i (f i))) =
      MvPolynomial.monomial (densityAssignmentExponent r f) (∏ i, B i (f i)) :=
    (MvPolynomial.monomial_sum_prod Finset.univ _ _).symm
  simp_rw [hm]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  simp only [densityAssignmentExponent_eq_unit_iff]
  have hs : (∑ f : Fin r → Fin r, if Function.Bijective f then ∏ i, B i (f i) else 0) =
      ∑ f : {f : Fin r → Fin r // Function.Bijective f}, ∏ i, B i (f.1 i) := by
    apply Finset.sum_congr_set {f : Fin r → Fin r | Function.Bijective f}
    · intro f hf
      change Function.Bijective f at hf
      exact if_pos hf
    · intro f hf
      change ¬Function.Bijective f at hf
      exact if_neg hf
  rw [hs]
  apply Fintype.sum_equiv Equiv.bijectiveEquiv
  intro f
  rfl

/-- Coefficient-based symmetrization agrees with the paper's average over
permutations, for every enumeration of a cardinality-r subset. -/
theorem densitySeparatedSym_eq_permutation_average {ι : Type*} [DecidableEq ι]
    (r : ℕ) (B : ι → Fin r → ℝ) (S : Finset ι) (e : Fin r ≃ S) :
    densitySeparatedSym r B S =
      (∑ σ : Equiv.Perm (Fin r), ∏ i, B (e i) (σ i)) / (r.factorial : ℝ) := by
  unfold densitySeparatedSym
  have he : (∏ i ∈ S, densityModulationPolynomial r B i) =
      ∏ i : Fin r, densityModulationPolynomial r (fun i l => B (e i) l) i := by
    rw [← Finset.prod_coe_sort]
    exact (e.prod_comp (fun i : S => densityModulationPolynomial r B i)).symm
  rw [he, density_linear_product_permanent]

theorem density_packet_product_zero_of_small_count {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (hSr : S.card < r) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b r z ε p B i) = 0 := by
  rw [density_packet_product_exact S a b ha hab m r D hr hD hSD p B,
    Finset.powersetCard_eq_empty.mpr hSr]
  simp

/-- The full count selector identity for all counts through m. -/
theorem density_packet_product_count_selector {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (hSm : S.card ≤ m) (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    densityPacketAction a b m r D (fun z ε => ∏ i ∈ S, localDensityReset a b r z ε p B i) =
      if S.card = r then ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) * densitySeparatedSym r B U else 0 := by
  by_cases hSr : r ≤ S.card
  · rw [density_packet_product_exact S a b ha hab m r D hr hD hSD p B,
      densityCountCoefficient_exact a b ha hab m r S.card hr hSr hSm]
    split_ifs <;> simp
  · rw [density_packet_product_zero_of_small_count S a b ha hab m r D hr hD hSD (by omega) p B,
      if_neg (by omega)]

def densityPacketAtom (a b : ℝ) (m r D : ℕ)
    (j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))) : ℝ × (Fin r → ℝ) :=
  (exteriorNode a b (m + r) j.1, fun l => lobattoNode (derivativeOrder D) (j.2 l))

def densityPacketWeight (a b : ℝ) (m r D : ℕ)
    (j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))) : ℝ :=
  densityPacketPrefactor a b r * exteriorWeight a b (m + r) j.1 *
    ∏ l, densityDerivativeWeight D (j.2 l)

/-- Gamma_{r,m} as an actual finite signed measure on density marks. -/
def densityPacketSignedRule (a b : ℝ) (m r D : ℕ) : SignedMeasure (ℝ × (Fin r → ℝ)) :=
  atomicSignedRule (densityPacketAtom a b m r D) (densityPacketWeight a b m r D)

theorem densityPacketSignedRule_integral (a b : ℝ) (m r D : ℕ)
    (f : ℝ → (Fin r → ℝ) → ℝ) :
    (∫ᵛ e, f e.1 e.2 ∂<•(densityPacketSignedRule a b m r D)) =
      densityPacketAction a b m r D f := by
  rw [densityPacketSignedRule, atomicSignedRule_integral]
  simp only [Fintype.sum_prod_type, densityPacketWeight, densityPacketAtom,
    densityPacketAction, densityDerivativeAction]
  simp only [Finset.mul_sum, mul_assoc]

theorem densityPacketAtom_mem (a b : ℝ) (hab : a ≤ b) (m r D : ℕ)
    (j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1))) :
    (densityPacketAtom a b m r D j).1 ∈ Icc a b ∧
      ∀ l, |(densityPacketAtom a b m r D j).2 l| ≤ 1 := by
  constructor
  · exact exteriorNode_mem a b hab (m + r) j.1
  · intro l
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem densityPacketSignedRule_supported (a b : ℝ) (hab : a ≤ b) (m r D : ℕ) :
    (densityPacketSignedRule a b m r D).variation
      {e : ℝ × (Fin r → ℝ) | e.1 ∈ Icc a b ∧ ∀ l, |e.2 l| ≤ 1}ᶜ = 0 := by
  apply atomicSignedRule_variation_outside
  · apply MeasurableSet.inter
    · exact measurable_fst measurableSet_Icc
    · convert MeasurableSet.iInter (fun l : Fin r =>
        measurableSet_le (show Measurable (fun e : ℝ × (Fin r → ℝ) => |e.2 l|) by fun_prop)
          (show Measurable (fun _ : ℝ × (Fin r → ℝ) => (1 : ℝ)) from measurable_const)) using 1
      ext e
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rfl
  · exact densityPacketAtom_mem a b hab m r D

theorem densityDerivativeWeight_variation (D : ℕ) :
    (∑ j : Fin (derivativeOrder D + 1), |densityDerivativeWeight D j|) = (derivativeOrder D : ℝ) :=
  lobatto_derivative_rule_variation ((D - 1) / 2)

theorem densityDerivativeWeight_tensor_variation (r D : ℕ) :
    (∑ h : Fin r → Fin (derivativeOrder D + 1), ∏ l, |densityDerivativeWeight D (h l)|) =
      (derivativeOrder D : ℝ) ^ r := by
  rw [← Fintype.prod_sum (fun (_l : Fin r) (j : Fin (derivativeOrder D + 1)) =>
    |densityDerivativeWeight D j|)]
  simp only [densityDerivativeWeight_variation, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem densityPacketWeight_variation (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) :
    (∑ j : Fin (m + r + 1) × (Fin r → Fin (derivativeOrder D + 1)),
      |densityPacketWeight a b m r D j|) =
      |densityPacketPrefactor a b r| *
        Real.cosh ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) * (derivativeOrder D : ℝ) ^ r := by
  simp only [densityPacketWeight, abs_mul, Finset.abs_prod, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, densityDerivativeWeight_tensor_variation]
  rw [← Finset.sum_mul, ← Finset.mul_sum, exterior_rule_variation a b ha hab _ (by omega)]

theorem densityPacketSignedRule_totalVariation_bound (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) :
    ((densityPacketSignedRule a b m r D).variation univ).toReal ≤
      |densityPacketPrefactor a b r| *
        Real.cosh ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) * (D : ℝ) ^ r := by
  apply (atomicSignedRule_totalVariation_le _ _).trans
  rw [densityPacketWeight_variation a b ha hab m r D hr]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (derivative_rule_variation D hD).2 r)
    (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)

/-- The factorial normalization has the required exponential cost. -/
theorem densityPacketPrefactor_abs_le (a b : ℝ) (r : ℕ) :
    |densityPacketPrefactor a b r| ≤ Real.exp (r : ℝ) * |b / densityMargin a b 0| ^ r := by
  unfold densityPacketPrefactor
  rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (r : ℝ) ^ r / (r.factorial : ℝ))]
  exact mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) r)
    (by positivity)

/-- The actual packet has cost C^r D^r exp(m tau), with an explicit C
depending only on the fixed density interval. -/
theorem densityPacketSignedRule_exponential_cost (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) :
    ((densityPacketSignedRule a b m r D).variation univ).toReal ≤
      (Real.exp (1 + exteriorTau ((a + b) / (b - a))) * |b / densityMargin a b 0|) ^ r *
        (D : ℝ) ^ r * Real.exp ((m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  have he : Real.cosh ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) ≤
      Real.exp ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) := by
    rw [← exterior_rule_variation a b ha hab (m + r) (by omega)]
    exact exterior_rule_variation_le_exp a b ha hab (m + r) (by omega)
  apply (densityPacketSignedRule_totalVariation_bound a b ha hab m r D hr hD).trans
  calc
    _ ≤ Real.exp (r : ℝ) * |b / densityMargin a b 0| ^ r *
        Real.exp ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) * (D : ℝ) ^ r := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (densityPacketPrefactor_abs_le a b r) he (Real.cosh_pos _).le
        (mul_nonneg (Real.exp_pos _).le (by positivity))
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have heq : Real.exp (r : ℝ) *
          Real.exp ((m + r : ℕ) * exteriorTau ((a + b) / (b - a))) =
          Real.exp ((r : ℝ) * (1 + exteriorTau ((a + b) / (b - a)))) *
            Real.exp ((m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        ring
      calc
        _ = (Real.exp (r : ℝ) * Real.exp ((m + r : ℕ) * exteriorTau ((a + b) / (b - a)))) *
            |b / densityMargin a b 0| ^ r * (D : ℝ) ^ r := by ring
        _ = _ := by rw [heq]; ring

/-- The actual signed-measure endpoint for the local density row. -/
theorem densityPacketSignedRule_product_exact {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hSD : S.card ≤ D)
    (p : ι → ℝ) (B : ι → Fin r → ℝ) :
    (∫ᵛ e, (∏ i ∈ S, localDensityReset a b r e.1 e.2 p B i)
      ∂<•(densityPacketSignedRule a b m r D)) =
      densityCountCoefficient a b m r S.card *
        ∑ U ∈ S.powersetCard r, (∏ i ∈ U, p i) * densitySeparatedSym r B U := by
  rw [densityPacketSignedRule_integral a b m r D
    (fun z ε => ∏ i ∈ S, localDensityReset a b r z ε p B i)]
  exact density_packet_product_exact S a b ha hab m r D hr hD hSD p B

theorem densitySeparatedSym_abs_le_one {ι : Type*} [DecidableEq ι]
    (r : ℕ) (B : ι → Fin r → ℝ) (S : Finset ι) (hS : S.card = r)
    (hB : ∀ i ∈ S, ∀ l, |B i l| ≤ 1) : |densitySeparatedSym r B S| ≤ 1 := by
  classical
  let e : Fin r ≃ S := (Fintype.equivFinOfCardEq (show Fintype.card S = r by simpa)).symm
  rw [densitySeparatedSym_eq_permutation_average r B S e, abs_div,
    abs_of_pos (by exact_mod_cast r.factorial_pos : (0 : ℝ) < r.factorial)]
  apply (div_le_iff₀ (by exact_mod_cast r.factorial_pos : (0 : ℝ) < r.factorial)).mpr
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin r), |∏ i, B (e i) (σ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin r), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [Finset.abs_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hB (e i) (e i).2 (σ i))).trans_eq
        (by simp)
    _ = _ := by simp [Fintype.card_perm]

end NearlyMinimax
