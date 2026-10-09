module

public import Mathlib


@[expose] public section

/-! # The three-point response law

This file formalizes the finite response law in Section 6.1 of the paper.
Index 0 represents `-a`, index 1 represents `0`, and index 2 represents `a`.
Expectations are actual finite sums against the specified masses.
-/

namespace NearlyMinimax

open scoped Topology

noncomputable section

/-- The support of the paper's three-point response law. -/
def ternaryValue (a : ℝ) : Fin 3 → ℝ := ![-a, 0, a]

/-- The three probability masses; positivity is proved separately. -/
def ternaryMass (a f V : ℝ) : Fin 3 → ℝ :=
  ![(V + f ^ 2 - a * f) / (2 * a ^ 2),
    1 - (V + f ^ 2) / a ^ 2,
    (V + f ^ 2 + a * f) / (2 * a ^ 2)]

/-- Integration against the finite response law. -/
def ternaryExpectation (a f V : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑ y : Fin 3, ternaryMass a f V y * g (ternaryValue a y)

/-- A real finite probability vector, including its nonnegativity proof. -/
structure TernaryLaw where
  mass : Fin 3 → ℝ
  nonnegative : ∀ y, 0 ≤ mass y
  normalized : ∑ y, mass y = 1

theorem ternary_normalized (a f V : ℝ) (ha : a ≠ 0) :
    ∑ y : Fin 3, ternaryMass a f V y = 1 := by
  simp [Fin.sum_univ_succ, ternaryMass]
  field_simp [ha]
  ring

theorem ternary_mean (a f V : ℝ) (ha : a ≠ 0) :
    ternaryExpectation a f V id = f := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

theorem ternary_second_moment (a f V : ℝ) (ha : a ≠ 0) :
    ternaryExpectation a f V (fun y => y ^ 2) = V + f ^ 2 := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

theorem ternary_variance (a f V : ℝ) (ha : a ≠ 0) :
    ternaryExpectation a f V (fun y => (y - f) ^ 2) = V := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

/-- The exact centered fourth moment appearing in the paper. -/
theorem ternary_fourth_central_moment (a f V : ℝ) (ha : a ≠ 0) :
    ternaryExpectation a f V (fun y => (y - f) ^ 4) =
      a ^ 2 * V + (6 * V - 3 * a ^ 2) * f ^ 2 + 3 * f ^ 4 := by
  simp [ternaryExpectation, Fin.sum_univ_succ, ternaryMass, ternaryValue]
  field_simp [ha]
  ring

/-- Explicit sufficient conditions for all masses to be strictly positive. -/
theorem ternary_mass_positive (a f V : ℝ) (ha : 0 < a)
    (hupper : V + f ^ 2 < a ^ 2)
    (hlower : a * |f| < V + f ^ 2) :
    ∀ y : Fin 3, 0 < ternaryMass a f V y := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hleft : a * f ≤ a * |f| := mul_le_mul_of_nonneg_left (le_abs_self f) ha.le
  have hright : -(a * f) ≤ a * |f| := by
    have := mul_le_mul_of_nonneg_left (neg_le_abs f) ha.le
    nlinarith
  intro y
  fin_cases y
  · exact div_pos (by linarith) (by positivity)
  · dsimp [ternaryMass]
    exact sub_pos.mpr ((div_lt_one ha2).mpr hupper)
  · exact div_pos (by linarith) (by positivity)

/-- Every nonnegative normalized mass is at most one. -/
theorem ternary_mass_le_one (a f V : ℝ) (ha : a ≠ 0)
    (hnonneg : ∀ y, 0 ≤ ternaryMass a f V y) (y : Fin 3) :
    ternaryMass a f V y ≤ 1 := by
  rw [← ternary_normalized a f V ha]
  exact Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ y)

/-- The response law as a normalized, nonnegative finite probability vector. -/
def mkTernaryLaw (a f V : ℝ) (ha : 0 < a)
    (hupper : V + f ^ 2 < a ^ 2)
    (hlower : a * |f| < V + f ^ 2) : TernaryLaw where
  mass := ternaryMass a f V
  nonnegative := fun y => (ternary_mass_positive a f V ha hupper hlower y).le
  normalized := ternary_normalized a f V (ne_of_gt ha)

/-- All response constraints hold uniformly in a rectangular neighborhood
of an interior zero-regression law, exactly as in Section 6.1. -/
theorem ternary_admissible_neighborhood (a v vMinus vPlus C4 : ℝ)
    (ha : 0 < a) (hv : 0 < v) (hva : v < a ^ 2)
    (hvMinus : vMinus < v) (hvPlus : v < vPlus) (hC4 : a ^ 2 * v < C4) :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧
      ∀ f V : ℝ, |f| ≤ ρ → |V - v| ≤ ρ →
        vMinus < V ∧ V < vPlus ∧
        (∀ y : Fin 3, c ≤ ternaryMass a f V y) ∧
        ternaryExpectation a f V (fun y => (y - f) ^ 4) ≤ C4 := by
  let p : ℝ := v / (2 * a ^ 2)
  let q : ℝ := 1 - v / a ^ 2
  let c : ℝ := min p q / 2
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hp : 0 < p := div_pos hv (by positivity)
  have hq : 0 < q := sub_pos.mpr ((div_lt_one ha2).mpr hva)
  have hc : 0 < c := div_pos (lt_min hp hq) (by norm_num)
  have hcp : c < p := by dsimp [c]; linarith [min_le_left p q]
  have hcq : c < q := by dsimp [c]; linarith [min_le_right p q]
  have hmass0 : ∀ y : Fin 3, c < ternaryMass a 0 v y := by
    intro y
    fin_cases y
    · simpa [ternaryMass, p] using hcp
    · simpa [ternaryMass, q] using hcq
    · simpa [ternaryMass, p] using hcp
  have hmassCont : ∀ y : Fin 3,
      Continuous (fun x : ℝ × ℝ => ternaryMass a x.1 x.2 y) := by
    intro y
    fin_cases y <;> simp [ternaryMass] <;> fun_prop
  have hmassEvent : ∀ᶠ x : ℝ × ℝ in nhds (0, v),
      ∀ y : Fin 3, c < ternaryMass a x.1 x.2 y := by
    exact Filter.eventually_all.mpr (fun y =>
      continuousAt_const.eventually_lt (hmassCont y).continuousAt (hmass0 y))
  have hVMinus : ∀ᶠ x : ℝ × ℝ in nhds (0, v), vMinus < x.2 :=
    continuousAt_const.eventually_lt continuous_snd.continuousAt hvMinus
  have hVPlus : ∀ᶠ x : ℝ × ℝ in nhds (0, v), x.2 < vPlus :=
    continuous_snd.continuousAt.eventually_lt continuousAt_const hvPlus
  have hfourthCont : Continuous (fun x : ℝ × ℝ =>
      a ^ 2 * x.2 + (6 * x.2 - 3 * a ^ 2) * x.1 ^ 2 + 3 * x.1 ^ 4) := by
    fun_prop
  have hfourth : ∀ᶠ x : ℝ × ℝ in nhds (0, v),
      a ^ 2 * x.2 + (6 * x.2 - 3 * a ^ 2) * x.1 ^ 2 + 3 * x.1 ^ 4 < C4 := by
    apply hfourthCont.continuousAt.eventually_lt continuousAt_const
    simpa using hC4
  have hevent : ∀ᶠ x : ℝ × ℝ in nhds (0, v),
      vMinus < x.2 ∧ x.2 < vPlus ∧
      (∀ y : Fin 3, c < ternaryMass a x.1 x.2 y) ∧
      a ^ 2 * x.2 + (6 * x.2 - 3 * a ^ 2) * x.1 ^ 2 + 3 * x.1 ^ 4 < C4 := by
    filter_upwards [hVMinus, hVPlus, hmassEvent, hfourth] with x hm hp hq hf
    exact ⟨hm, hp, hq, hf⟩
  obtain ⟨ε, hε, hbound⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ε / 2, c, by positivity, hc, ?_⟩
  intro f V hf hV
  have hdist : dist (f, V) (0, v) < ε := by
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt (by linarith) (by linarith)
  obtain ⟨hm, hp, hq, hfourth⟩ := hbound hdist
  refine ⟨hm, hp, fun y => (hq y).le, ?_⟩
  rw [ternary_fourth_central_moment a f V (ne_of_gt ha)]
  exact hfourth.le

/-- The mass derivative in the variance direction. -/
def ternaryVarianceDerivative (a : ℝ) : Fin 3 → ℝ :=
  ![1 / (2 * a ^ 2), -1 / a ^ 2, 1 / (2 * a ^ 2)]

/-- The mass derivative in the regression direction. -/
def ternaryMeanDerivative (a f : ℝ) : Fin 3 → ℝ :=
  ![(2 * f - a) / (2 * a ^ 2), -(2 * f) / a ^ 2,
    (2 * f + a) / (2 * a ^ 2)]

/-- The second mass derivative in the regression direction. -/
def ternaryMeanSecondDerivative (a : ℝ) : Fin 3 → ℝ :=
  ![1 / a ^ 2, -2 / a ^ 2, 1 / a ^ 2]

/-- The displayed variance derivative is the actual derivative of every mass. -/
theorem ternary_hasDerivAt_variance (a f V : ℝ) (y : Fin 3) :
    HasDerivAt (fun W => ternaryMass a f W y) (ternaryVarianceDerivative a y) V := by
  fin_cases y
  · change HasDerivAt (fun W => (W + f ^ 2 - a * f) / (2 * a ^ 2))
      (1 / (2 * a ^ 2)) V
    exact ((((hasDerivAt_id V).add_const (f ^ 2)).sub_const (a * f)).div_const
      (2 * a ^ 2)).congr_deriv (by ring)
  · change HasDerivAt (fun W => 1 - (W + f ^ 2) / a ^ 2) (-1 / a ^ 2) V
    exact ((hasDerivAt_const V (1 : ℝ)).sub
      (((hasDerivAt_id V).add_const (f ^ 2)).div_const (a ^ 2))).congr_deriv (by ring)
  · change HasDerivAt (fun W => (W + f ^ 2 + a * f) / (2 * a ^ 2))
      (1 / (2 * a ^ 2)) V
    exact ((((hasDerivAt_id V).add_const (f ^ 2)).add_const (a * f)).div_const
      (2 * a ^ 2)).congr_deriv (by ring)

/-- The displayed regression derivative is the actual derivative. -/
theorem ternary_hasDerivAt_mean (a f V : ℝ) (y : Fin 3) :
    HasDerivAt (fun g => ternaryMass a g V y) (ternaryMeanDerivative a f y) f := by
  fin_cases y
  · change HasDerivAt (fun g => (V + g ^ 2 - a * g) / (2 * a ^ 2))
      ((2 * f - a) / (2 * a ^ 2)) f
    exact ((((hasDerivAt_const f V).add ((hasDerivAt_id f).pow 2)).sub
      ((hasDerivAt_const f a).mul (hasDerivAt_id f))).div_const
      (2 * a ^ 2)).congr_deriv (by simp only [id_eq]; ring)
  · change HasDerivAt (fun g => 1 - (V + g ^ 2) / a ^ 2) (-(2 * f) / a ^ 2) f
    exact ((hasDerivAt_const f (1 : ℝ)).sub
      (((hasDerivAt_const f V).add ((hasDerivAt_id f).pow 2)).div_const
      (a ^ 2))).congr_deriv (by simp only [id_eq]; ring)
  · change HasDerivAt (fun g => (V + g ^ 2 + a * g) / (2 * a ^ 2))
      ((2 * f + a) / (2 * a ^ 2)) f
    exact ((((hasDerivAt_const f V).add ((hasDerivAt_id f).pow 2)).add
      ((hasDerivAt_const f a).mul (hasDerivAt_id f))).div_const
      (2 * a ^ 2)).congr_deriv (by simp only [id_eq]; ring)

/-- The displayed second regression derivative is the actual derivative. -/
theorem ternary_hasDerivAt_mean_derivative (a f : ℝ) (y : Fin 3) :
    HasDerivAt (fun g => ternaryMeanDerivative a g y)
      (ternaryMeanSecondDerivative a y) f := by
  fin_cases y
  · change HasDerivAt (fun g => (2 * g - a) / (2 * a ^ 2)) (1 / a ^ 2) f
    exact ((((hasDerivAt_id f).const_mul 2).sub_const a).div_const
      (2 * a ^ 2)).congr_deriv (by simp [div_eq_mul_inv]; ring)
  · change HasDerivAt (fun g => -(2 * g) / a ^ 2) (-2 / a ^ 2) f
    exact (((hasDerivAt_id f).const_mul 2).neg.div_const
      (a ^ 2)).congr_deriv (by ring)
  · change HasDerivAt (fun g => (2 * g + a) / (2 * a ^ 2)) (1 / a ^ 2) f
    exact ((((hasDerivAt_id f).const_mul 2).add_const a).div_const
      (2 * a ^ 2)).congr_deriv (by simp [div_eq_mul_inv]; ring)

/-- The exact heat identity for the quadratic masses. -/
theorem ternary_heat_identity (a : ℝ) (y : Fin 3) :
    ternaryMeanSecondDerivative a y = 2 * ternaryVarianceDerivative a y := by
  fin_cases y <;> simp [ternaryMeanSecondDerivative, ternaryVarianceDerivative] <;> ring

/-- The heat identity expressed using actual iterated derivatives. -/
theorem ternary_deriv_heat_identity (a f V : ℝ) (y : Fin 3) :
    deriv (fun g => deriv (fun h => ternaryMass a h V y) g) f =
      2 * deriv (fun W => ternaryMass a f W y) V := by
  have hfun : (fun g => deriv (fun h => ternaryMass a h V y) g) =
      (fun g => ternaryMeanDerivative a g y) := by
    funext g
    exact (ternary_hasDerivAt_mean a g V y).deriv
  rw [hfun, (ternary_hasDerivAt_mean_derivative a f y).deriv,
    (ternary_hasDerivAt_variance a f V y).deriv, ternary_heat_identity]

/-- The exact finite-difference identity used in the small-smoothness lower bound. -/
theorem ternary_finite_difference (a g V η w : ℝ) (ha : a ≠ 0) (y : Fin 3) :
    (1 / 2 : ℝ) * ternaryMass a (g + η * w) V y +
      (1 / 2 : ℝ) * ternaryMass a (g - η * w) V y - ternaryMass a g V y =
      η ^ 2 * w ^ 2 * ternaryVarianceDerivative a y := by
  fin_cases y <;> simp [ternaryMass, ternaryVarianceDerivative] <;>
    field_simp [ha] <;> ring

/-- Finite variance-direction score of one response. -/
def ternaryVarianceScore (a f V : ℝ) (y : Fin 3) : ℝ :=
  ternaryVarianceDerivative a y / ternaryMass a f V y

/-- The score is centered under every strictly positive ternary law. -/
theorem ternary_score_mean_zero (a f V : ℝ)
    (hpositive : ∀ y, 0 < ternaryMass a f V y) :
    ∑ y : Fin 3, ternaryMass a f V y * ternaryVarianceScore a f V y = 0 := by
  have hterm : ∀ y, ternaryMass a f V y * ternaryVarianceScore a f V y =
      ternaryVarianceDerivative a y := by
    intro y
    unfold ternaryVarianceScore
    field_simp [ne_of_gt (hpositive y)]
  simp_rw [hterm]
  simp [Fin.sum_univ_succ, ternaryVarianceDerivative]
  ring

/-- Single-observation Fisher information on the zero-regression submodel. -/
theorem ternary_fisher_information (a V : ℝ) (ha : 0 < a) (hV : 0 < V)
    (hVa : V < a ^ 2) :
    (∑ y : Fin 3, ternaryMass a 0 V y * (ternaryVarianceScore a 0 V y) ^ 2) =
      1 / (V * (a ^ 2 - V)) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hV0 : V ≠ 0 := ne_of_gt hV
  have hgap : a ^ 2 - V ≠ 0 := ne_of_gt (sub_pos.mpr hVa)
  have hq0 : 1 - V / a ^ 2 ≠ 0 := by
    have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
    exact ne_of_gt (sub_pos.mpr ((div_lt_one ha2).mpr hVa))
  simp [Fin.sum_univ_succ, ternaryMass, ternaryVarianceScore,
    ternaryVarianceDerivative]
  field_simp [ha0, hV0, hgap, hq0]
  ring

/-- IID joint mass for a sample of `n` responses. -/
def ternarySampleMass (p : Fin 3 → ℝ) (n : ℕ) (x : Fin n → Fin 3) : ℝ :=
  ∏ i : Fin n, p (x i)

/-- Additive single-observation score over a response sample. -/
def ternarySampleScore (s : Fin 3 → ℝ) (n : ℕ) (x : Fin n → Fin 3) : ℝ :=
  ∑ i : Fin n, s (x i)

/-- IID sample normalization, proved by the finite product-of-sums identity. -/
theorem ternary_sample_normalized (p : Fin 3 → ℝ) (hp : ∑ y, p y = 1) (n : ℕ) :
    ∑ x : Fin n → Fin 3, ternarySampleMass p n x = 1 := by
  unfold ternarySampleMass
  rw [← Fintype.prod_sum]
  simp [hp]

private theorem ternary_sample_split (n : ℕ) (F : (Fin (n + 1) → Fin 3) → ℝ) :
    ∑ x, F x = ∑ y : Fin 3, ∑ z : Fin n → Fin 3, F (Fin.cons y z) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 3)).sum_comp F]
  rw [Fintype.sum_prod_type]
  rfl

/-- Independent centered scores add their second moments. The independence
is encoded by the actual finite product mass, rather than assumed as a
moment identity. -/
theorem ternary_sample_score_moments (p s : Fin 3 → ℝ) (I : ℝ)
    (hp : ∑ y, p y = 1) (hs : ∑ y, p y * s y = 0)
    (hI : ∑ y, p y * (s y) ^ 2 = I) (n : ℕ) :
    (∑ x, ternarySampleMass p n x * ternarySampleScore s n x) = 0 ∧
    (∑ x, ternarySampleMass p n x * (ternarySampleScore s n x) ^ 2) = n * I := by
  induction n with
  | zero => simp [ternarySampleScore]
  | succ n ih =>
    have hn := ternary_sample_normalized p hp n
    have hm : ∀ y : Fin 3,
        ∑ z : Fin n → Fin 3, p y * ternarySampleMass p n z *
          (s y + ternarySampleScore s n z) = p y * s y := by
      intro y
      calc
        _ = (p y * s y) * (∑ z, ternarySampleMass p n z) +
            p y * (∑ z, ternarySampleMass p n z * ternarySampleScore s n z) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro z _
          ring
        _ = _ := by rw [hn, ih.1]; ring
    have hv : ∀ y : Fin 3,
        ∑ z : Fin n → Fin 3, p y * ternarySampleMass p n z *
          (s y + ternarySampleScore s n z) ^ 2 = p y * (s y) ^ 2 + p y * (n * I) := by
      intro y
      calc
        _ = (p y * (s y) ^ 2) * (∑ z, ternarySampleMass p n z) +
            (2 * p y * s y) *
              (∑ z, ternarySampleMass p n z * ternarySampleScore s n z) +
            p y * (∑ z, ternarySampleMass p n z * (ternarySampleScore s n z) ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro z _
          ring
        _ = _ := by rw [hn, ih.1, ih.2]; ring
    constructor
    · rw [ternary_sample_split]
      simp only [ternarySampleMass, ternarySampleScore, Fin.prod_univ_succ,
        Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      change (∑ y : Fin 3, ∑ z : Fin n → Fin 3,
        p y * ternarySampleMass p n z * (s y + ternarySampleScore s n z)) = 0
      simp_rw [hm]
      exact hs
    · rw [ternary_sample_split]
      simp only [ternarySampleMass, ternarySampleScore, Fin.prod_univ_succ,
        Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      change (∑ y : Fin 3, ∑ z : Fin n → Fin 3,
        p y * ternarySampleMass p n z * (s y + ternarySampleScore s n z) ^ 2) =
        (n + 1 : ℕ) * I
      simp_rw [hv]
      rw [Finset.sum_add_distrib, hI, ← Finset.sum_mul, hp, Nat.cast_add, Nat.cast_one]
      ring

/-- The `n`-observation parametric score formula from Section 6.3. -/
theorem ternary_parametric_score_second_moment (a V b : ℝ) (n : ℕ)
    (ha : 0 < a) (hV : 0 < V) (hVa : V < a ^ 2) :
    (∑ x : Fin n → Fin 3,
      ternarySampleMass (ternaryMass a 0 V) n x *
        (-b * ternarySampleScore (ternaryVarianceScore a 0 V) n x) ^ 2) =
      n * b ^ 2 / (V * (a ^ 2 - V)) := by
  have hpositive : ∀ y, 0 < ternaryMass a 0 V y :=
    ternary_mass_positive a 0 V ha (by simpa using hVa) (by simpa using hV)
  have hs := (ternary_sample_score_moments (ternaryMass a 0 V)
    (ternaryVarianceScore a 0 V) (1 / (V * (a ^ 2 - V)))
    (ternary_normalized a 0 V (ne_of_gt ha))
    (ternary_score_mean_zero a 0 V hpositive)
    (ternary_fisher_information a V ha hV hVa) n).2
  calc
    _ = b ^ 2 * (∑ x : Fin n → Fin 3,
        ternarySampleMass (ternaryMass a 0 V) n x *
          (ternarySampleScore (ternaryVarianceScore a 0 V) n x) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [hs]; ring

end

end NearlyMinimax
