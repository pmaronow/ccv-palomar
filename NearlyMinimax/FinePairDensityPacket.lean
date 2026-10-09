module

public import NearlyMinimax.ActualSeparatedPacket
public import NearlyMinimax.PacketAbsoluteMoments


@[expose] public section

/-! The genuine fine-pair three-point modulation rule and exterior density
packet from (new-pair-packet). The field mark is retained explicitly. -/
noncomputable section
open Set MeasureTheory Polynomial
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def fineModulationNode (i : Fin 3) : ℝ := if i = 0 then -1 else if i = 1 then 0 else 1
def fineModulationWeight (i : Fin 3) : ℝ := if i = 1 then -1 else 1 / 2

theorem fineModulation_eval (f : ℝ → ℝ) :
    (∑ i : Fin 3, fineModulationWeight i * f (fineModulationNode i)) =
      f (-1) / 2 - f 0 + f 1 / 2 := by
  simp [Fin.sum_univ_succ, fineModulationWeight, fineModulationNode]
  ring

theorem fineModulationNode_bound (i : Fin 3) : |fineModulationNode i| ≤ 1 := by
  fin_cases i <;> norm_num [fineModulationNode]

theorem fineModulationWeight_variation : (∑ i : Fin 3, |fineModulationWeight i|) = 2 := by
  norm_num [Fin.sum_univ_succ, fineModulationWeight]

def fineModulationSignedRule : SignedMeasure ℝ := atomicSignedRule fineModulationNode fineModulationWeight

theorem fineModulationSignedRule_totalVariation :
    (fineModulationSignedRule.variation univ).toReal = 2 := by
  rw [fineModulationSignedRule, atomicSignedRule_totalVariation_eq, fineModulationWeight_variation]
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals simp_all [fineModulationNode]
  all_goals norm_num at hij

theorem fineModulation_moment_zero :
    (∑ i : Fin 3, fineModulationWeight i * fineModulationNode i ^ 0) = 0 := by
  rw [fineModulation_eval (fun z => z ^ 0)]
  norm_num

theorem fineModulation_moment_odd (n : ℕ) (hn : Odd n) :
    (∑ i : Fin 3, fineModulationWeight i * fineModulationNode i ^ n) = 0 := by
  rw [fineModulation_eval (fun z => z ^ n)]
  have hn0 : n ≠ 0 := by intro h; subst n; exact Nat.not_odd_zero hn
  simp [hn.neg_one_pow, zero_pow hn0]
  norm_num

theorem fineModulation_moment_even (n : ℕ) (hn : Even n) (hn0 : n ≠ 0) :
    (∑ i : Fin 3, fineModulationWeight i * fineModulationNode i ^ n) = 1 := by
  rw [fineModulation_eval (fun z => z ^ n)]
  simp [hn.neg_one_pow, zero_pow hn0]
  norm_num

theorem fineModulation_moment (n : ℕ) :
    (∑ i : Fin 3, fineModulationWeight i * fineModulationNode i ^ n) =
      if n = 0 then 0 else if Even n then 1 else 0 := by
  by_cases hn0 : n = 0
  · subst n; simp only [ite_true]; exact fineModulation_moment_zero
  · rw [ite_eq_right hn0]
    rcases Nat.even_or_odd n with hn | hn
    · rw [ite_eq_left hn]; exact fineModulation_moment_even n hn hn0
    · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hn)]; exact fineModulation_moment_odd n hn

abbrev FinePairDensityIndex (M : ℕ) := Fin (M + 3) × Fin 3

def finePairDensityPrefactor (a b : ℝ) : ℝ := b ^ 2 / densityMargin a b 0 ^ 2

def finePairDensityAtom (a b : ℝ) (M : ℕ) (i : FinePairDensityIndex M) : ℝ × ℝ :=
  (exteriorNode a b (M + 2) i.1, fineModulationNode i.2)

def finePairDensityWeight (a b : ℝ) (M : ℕ) (i : FinePairDensityIndex M) : ℝ :=
  finePairDensityPrefactor a b * exteriorWeight a b (M + 2) i.1 * fineModulationWeight i.2

def finePairDensitySignedRule (a b : ℝ) (M : ℕ) : SignedMeasure (ℝ × ℝ) :=
  atomicSignedRule (finePairDensityAtom a b M) (finePairDensityWeight a b M)

theorem finePairDensityWeight_variation (a b : ℝ) (ha : 0 < a) (hab : a < b) (M : ℕ) :
    (∑ i : FinePairDensityIndex M, |finePairDensityWeight a b M i|) =
      2 * |finePairDensityPrefactor a b| *
        Real.cosh ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) := by
  simp only [finePairDensityWeight, abs_mul, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, fineModulationWeight_variation]
  rw [← Finset.sum_mul, ← Finset.mul_sum, exterior_rule_variation a b ha hab (M + 2) (by omega)]
  ring

theorem finePairDensitySignedRule_totalVariation_le (a b : ℝ) (ha : 0 < a) (hab : a < b) (M : ℕ) :
    ((finePairDensitySignedRule a b M).variation univ).toReal ≤
      2 * |finePairDensityPrefactor a b| *
        Real.cosh ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) := by
  apply (atomicSignedRule_totalVariation_le _ _).trans_eq
  exact finePairDensityWeight_variation a b ha hab M

def finePairDensityReset {U : Type*} (a b : ℝ) (z eps : ℝ) (p ψ : U → ℝ) (u : U) : ℝ :=
  z + densityMargin a b z / b * p u * eps * ψ u

theorem finePairDensityReset_mem_interval {U : Type*} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (z eps : ℝ) (hz : z ∈ Icc a b) (heps : |eps| ≤ 1)
    (p ψ : U → ℝ) (u : U) (hp : p u ∈ Icc a b) (hψ : |ψ u| ≤ 1) :
    finePairDensityReset a b z eps p ψ u ∈ Icc a b := by
  have hh := localDensityReset_mem_interval a b ha hab 1 (by omega) z hz (fun _ => eps)
    (fun _ => heps) p (fun u _ => ψ u) u hp (fun _ => hψ)
  simpa [localDensityReset, finePairDensityReset, mul_comm, mul_left_comm, mul_assoc] using hh

theorem finePairDensityReset_slope_bound {U : Type*} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (z eps : ℝ) (hz : z ∈ Icc a b) (heps : |eps| ≤ 1)
    (ψ : U → ℝ) (u : U) (hψ : |ψ u| ≤ 1) :
    |densityMargin a b z / b * eps * ψ u| ≤ (b - a) / (4 * b) := by
  have hh := localDensityReset_slope_bound a b ha hab 1 (by omega) z hz (fun _ => eps)
    (fun _ => heps) (fun u _ => ψ u) u (fun _ => hψ)
  simpa [mul_assoc] using hh

theorem fineModulation_affine_zero (z c : ℝ) :
    (∑ i : Fin 3, fineModulationWeight i * (z + c * fineModulationNode i)) = 0 := by
  rw [fineModulation_eval (fun eps => z + c * eps)]
  ring

theorem fineModulation_quadratic (z c c' : ℝ) :
    (∑ i : Fin 3, fineModulationWeight i *
      ((z + c * fineModulationNode i) * (z + c' * fineModulationNode i))) = c * c' := by
  rw [fineModulation_eval (fun eps => (z + c * eps) * (z + c' * eps))]
  ring

theorem fineModulation_product {ι : Type*} [DecidableEq ι] (S : Finset ι) (z : ℝ) (c : ι → ℝ) :
    (∑ h : Fin 3, fineModulationWeight h * ∏ i ∈ S, (z + c i * fineModulationNode h)) =
      ∑ U ∈ S.powerset, z ^ (S.card - U.card) * (∏ i ∈ U, c i) *
        (if U.card = 0 then 0 else if Even U.card then 1 else 0) := by
  simp_rw [add_comm z, Finset.prod_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hU)]
  have he (h : Fin 3) : fineModulationWeight h *
      ((∏ i ∈ U, c i) * fineModulationNode h ^ U.card * z ^ (S.card - U.card)) =
      z ^ (S.card - U.card) * (∏ i ∈ U, c i) *
        (fineModulationWeight h * fineModulationNode h ^ U.card) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, fineModulation_moment]

def finePairCountCoefficient (a b : ℝ) (M k j : ℕ) : ℝ :=
  finePairDensityPrefactor a b * ∑ h : Fin (M + 3), exteriorWeight a b (M + 2) h *
    (exteriorNode a b (M + 2) h ^ (k - j) * (densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ j)

theorem finePairCountCoefficient_two (a b : ℝ) (ha : 0 < a) (hab : a < b) (M k : ℕ) :
    finePairCountCoefficient a b M k 2 = densityCountCoefficient a b M 2 k := by
  unfold finePairCountCoefficient finePairDensityPrefactor densityCountCoefficient
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _
  field_simp [densityMargin_zero_ne a b ha hab, (ha.trans hab).ne']

theorem finePairCountCoefficient_two_exact (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (M k : ℕ) (hk : 2 ≤ k) (hM : k ≤ M) :
    finePairCountCoefficient a b M k 2 = if k = 2 then 1 else 0 := by
  rw [finePairCountCoefficient_two a b ha hab M k]
  exact densityCountCoefficient_exact a b ha hab M 2 k (by omega) hk hM

theorem finePairCountCoefficient_abs_bound (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (M k j : ℕ) :
    |finePairCountCoefficient a b M k j| ≤
      |finePairDensityPrefactor a b| * (b ^ (k - j) * ((b - a) / (4 * b)) ^ j) *
        Real.cosh ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) := by
  have hb : 0 < b := ha.trans hab
  have hβ : 0 ≤ (b - a) / (4 * b) := by positivity
  have hterm (h : Fin (M + 3)) :
      |exteriorNode a b (M + 2) h ^ (k - j) *
        (densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ j| ≤
      b ^ (k - j) * ((b - a) / (4 * b)) ^ j := by
    have hz := exteriorNode_mem a b hab.le (M + 2) h
    have ht := densityMargin_bounds a b hab _ hz
    have ht0 : 0 ≤ densityMargin a b (exteriorNode a b (M + 2) h) / b := div_nonneg ht.1 hb.le
    have htle : densityMargin a b (exteriorNode a b (M + 2) h) / b ≤ (b - a) / (4 * b) := by
      exact (div_le_div_of_nonneg_right ht.2.2.2 hb.le).trans_eq (by ring)
    rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg (ha.le.trans hz.1), abs_of_nonneg ht0]
    exact mul_le_mul (pow_le_pow_left₀ (ha.le.trans hz.1) hz.2 _)
      (pow_le_pow_left₀ ht0 htle _) (pow_nonneg ht0 _) (pow_nonneg hb.le _)
  unfold finePairCountCoefficient
  rw [abs_mul]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)).trans
  calc
    _ ≤ |finePairDensityPrefactor a b| *
        ∑ h : Fin (M + 3), |exteriorWeight a b (M + 2) h| *
          (b ^ (k - j) * ((b - a) / (4 * b)) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Finset.sum_le_sum
      intro h _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hterm h) (abs_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul, exterior_rule_variation a b ha hab (M + 2) (by omega)]
      ring

theorem finePairDensityWeight_exponential_cost (a b : ℝ) (ha : 0 < a) (hab : a < b) (M : ℕ) :
    (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) ≤
      (2 * |finePairDensityPrefactor a b| * Real.exp (2 * exteriorTau ((a + b) / (b - a)))) *
        Real.exp ((M : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  rw [finePairDensityWeight_variation a b ha hab M]
  have he : Real.cosh ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) ≤
      Real.exp ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) := by
    rw [← exterior_rule_variation a b ha hab (M + 2) (by omega)]
    exact exterior_rule_variation_le_exp a b ha hab (M + 2) (by omega)
  apply (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq
  rw [Nat.cast_add, Nat.cast_ofNat, add_mul, Real.exp_add]
  ring

theorem finePairDensitySignedRule_integral (a b : ℝ) (M : ℕ) (f : ℝ → ℝ → ℝ) :
    (∫ᵛ e, f e.1 e.2 ∂<•finePairDensitySignedRule a b M) =
      finePairDensityPrefactor a b * ∑ j : Fin (M + 3), exteriorWeight a b (M + 2) j *
        ∑ i : Fin 3, fineModulationWeight i * f (exteriorNode a b (M + 2) j) (fineModulationNode i) := by
  rw [finePairDensitySignedRule, atomicSignedRule_integral]
  simp only [finePairDensityAtom, finePairDensityWeight, Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← Finset.mul_sum]

theorem finePairDensitySignedRule_product_expansion {U : Type*} [DecidableEq U]
    (a b : ℝ) (M : ℕ) (S : Finset U) (p ψ : U → ℝ) :
    (∫ᵛ e, ∏ u ∈ S, finePairDensityReset a b e.1 e.2 p ψ u
      ∂<•finePairDensitySignedRule a b M) =
      ∑ W ∈ S.powerset, finePairCountCoefficient a b M S.card W.card * (∏ u ∈ W, p u * ψ u) *
        (if W.card = 0 then 0 else if Even W.card then 1 else 0) := by
  rw [finePairDensitySignedRule_integral a b M (fun z eps => ∏ u ∈ S, finePairDensityReset a b z eps p ψ u)]
  have he (z eps : ℝ) (u : U) : finePairDensityReset a b z eps p ψ u =
      z + (densityMargin a b z / b * (p u * ψ u)) * eps := by
    unfold finePairDensityReset
    ring
  have hprod (z : ℝ) (W : Finset U) :
      (∏ u ∈ W, densityMargin a b z / b * (p u * ψ u)) =
      (densityMargin a b z / b) ^ W.card * (∏ u ∈ W, p u * ψ u) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [he, fineModulation_product, hprod]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro W hW
  unfold finePairCountCoefficient
  have hterm (h : Fin (M + 3)) : finePairDensityPrefactor a b *
      (exteriorWeight a b (M + 2) h *
       (exteriorNode a b (M + 2) h ^ (S.card - W.card) *
        ((densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ W.card * ∏ u ∈ W, p u * ψ u) *
        (if W.card = 0 then 0 else if Even W.card then 1 else 0))) =
      finePairDensityPrefactor a b *
        (exteriorWeight a b (M + 2) h * (exteriorNode a b (M + 2) h ^ (S.card - W.card) *
          (densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ W.card)) *
        ((∏ u ∈ W, p u * ψ u) * (if W.card = 0 then 0 else if Even W.card then 1 else 0)) := by ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem finePairDensitySignedRule_mass_zero (a b : ℝ) (M : ℕ) :
    (∫ᵛ _e, (1 : ℝ) ∂<•finePairDensitySignedRule a b M) = 0 := by
  rw [finePairDensitySignedRule_integral a b M (fun _ _ => 1)]
  have hw : (∑ i : Fin 3, fineModulationWeight i) = 0 := by
    simpa only [pow_zero, mul_one] using fineModulation_moment_zero
  simp [hw]

theorem finePairDensitySignedRule_linear_zero {U : Type*} (a b : ℝ) (M : ℕ)
    (p ψ : U → ℝ) (u : U) :
    (∫ᵛ e, finePairDensityReset a b e.1 e.2 p ψ u
      ∂<•finePairDensitySignedRule a b M) = 0 := by
  rw [finePairDensitySignedRule_integral a b M (fun z eps => finePairDensityReset a b z eps p ψ u)]
  have he (z eps : ℝ) : finePairDensityReset a b z eps p ψ u =
      z + (densityMargin a b z / b * p u * ψ u) * eps := by
    unfold finePairDensityReset
    ring
  simp_rw [he, fineModulation_affine_zero]
  simp

theorem finePairDensitySignedRule_pair_exact {U : Type*} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (M : ℕ) (hM : 2 ≤ M) (p ψ : U → ℝ) (u v : U) :
    (∫ᵛ e, finePairDensityReset a b e.1 e.2 p ψ u * finePairDensityReset a b e.1 e.2 p ψ v
      ∂<•finePairDensitySignedRule a b M) = p u * p v * ψ u * ψ v := by
  rw [finePairDensitySignedRule_integral a b M
    (fun z eps => finePairDensityReset a b z eps p ψ u * finePairDensityReset a b z eps p ψ v)]
  have he (z eps : ℝ) (u : U) : finePairDensityReset a b z eps p ψ u =
      z + (densityMargin a b z / b * p u * ψ u) * eps := by
    unfold finePairDensityReset
    ring
  simp_rw [he, fineModulation_quadratic]
  have hc := densityCountCoefficient_exact a b ha hab M 2 2 (by omega) (by omega) hM
  simp only [densityCountCoefficient, Nat.sub_self, pow_zero, one_mul, ite_true] at hc
  have hθ : densityMargin a b 0 ^ 2 ≠ 0 := pow_ne_zero _ (densityMargin_zero_ne a b ha hab)
  have hs : (∑ j : Fin (M + 3), exteriorWeight a b (M + 2) j *
      densityMargin a b (exteriorNode a b (M + 2) j) ^ 2) = densityMargin a b 0 ^ 2 := by
    exact (div_eq_iff hθ).mp hc |>.trans (one_mul _)
  have hterm (j : Fin (M + 3)) : exteriorWeight a b (M + 2) j *
      ((densityMargin a b (exteriorNode a b (M + 2) j) / b * p u * ψ u) *
       (densityMargin a b (exteriorNode a b (M + 2) j) / b * p v * ψ v)) =
      exteriorWeight a b (M + 2) j * densityMargin a b (exteriorNode a b (M + 2) j) ^ 2 *
      ((p u * p v * ψ u * ψ v) / b ^ 2) := by ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, hs]
  unfold finePairDensityPrefactor
  field_simp [hθ, densityMargin_zero_ne a b ha hab, (ha.trans hab).ne']

section Field
variable {Z : Type*} [MeasurableSpace Z]

def finePairFieldWeight (a b : ℝ) (M : ℕ) (e : Z × FinePairDensityIndex M) : ℝ :=
  finePairDensityWeight a b M e.2

def finePairFieldSignedMeasure (π : Measure Z) (a b : ℝ) (M : ℕ) :
    SignedMeasure (Z × FinePairDensityIndex M) :=
  (π.prod Measure.count).withDensityᵥ (finePairFieldWeight a b M)

theorem finePairFieldWeight_measurable (a b : ℝ) (M : ℕ) :
    Measurable (finePairFieldWeight (Z := Z) a b M) :=
  (measurable_of_countable (finePairDensityWeight a b M)).comp measurable_snd

theorem finePairFieldWeight_integrable (π : Measure Z) [IsFiniteMeasure π] (a b : ℝ) (M : ℕ) :
    Integrable (finePairFieldWeight a b M) (π.prod Measure.count) :=
  joint_finite_integrable π _ (fun h => by
    change Measurable (fun _ : Z => finePairDensityWeight a b M h)
    exact measurable_const)
    (fun h => (integrable_const (finePairDensityWeight a b M h)))

theorem finePairFieldSignedMeasure_totalVariation (π : Measure Z) [IsProbabilityMeasure π]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (M : ℕ) :
    ((finePairFieldSignedMeasure π a b M).variation univ).toReal =
      2 * |finePairDensityPrefactor a b| *
        Real.cosh ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) := by
  rw [finePairFieldSignedMeasure, ← signedMarkMass_eq_variation _ _ (finePairFieldWeight_integrable π a b M)]
  unfold signedMarkMass finePairFieldWeight
  rw [integral_fun_snd (fun h : FinePairDensityIndex M => |finePairDensityWeight a b M h|),
    integral_count, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  exact finePairDensityWeight_variation a b ha hab M

theorem finePairFieldSignedMeasure_integral (π : Measure Z) [IsFiniteMeasure π]
    (a b : ℝ) (M : ℕ) (f : Z × FinePairDensityIndex M → ℝ) (hf : Measurable f)
    (L : ℝ) (hb : ∀ e, ‖f e‖ ≤ L) :
    (∫ᵛ e, f e ∂<•finePairFieldSignedMeasure π a b M) =
      ∫ ζ, ∑ h : FinePairDensityIndex M, finePairDensityWeight a b M h * f (ζ, h) ∂π := by
  rw [finePairFieldSignedMeasure, signedDensity_integral _ _ (finePairFieldWeight_integrable π a b M)
    (finePairFieldWeight_measurable a b M) f hf L hb,
    integral_prod _ ((finePairFieldWeight_integrable π a b M).mul_bdd hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hb))]
  simp only [integral_count, finePairFieldWeight]

def finePairFieldReset {U : Type*} (a b : ℝ) (M : ℕ) (p : U → ℝ) (ψ : Z → U → ℝ)
    (e : Z × FinePairDensityIndex M) (u : U) : ℝ :=
  finePairDensityReset a b (finePairDensityAtom a b M e.2).1
    (finePairDensityAtom a b M e.2).2 p (ψ e.1) u

theorem finePairFieldReset_measurable {U : Type*} (a b : ℝ) (M : ℕ) (p : U → ℝ)
    (ψ : Z → U → ℝ) (hψ : ∀ u, Measurable (fun ζ => ψ ζ u)) (u : U) :
    Measurable (fun e : Z × FinePairDensityIndex M => finePairFieldReset a b M p ψ e u) := by
  apply measurable_from_prod_countable_left
  intro h
  unfold finePairFieldReset finePairDensityReset
  dsimp only
  exact measurable_const.add ((hψ u).const_mul
    (densityMargin a b (finePairDensityAtom a b M h).1 / b * p u * (finePairDensityAtom a b M h).2))

theorem finePairFieldReset_mem_interval {U : Type*} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (M : ℕ) (p : U → ℝ) (hp : ∀ u, p u ∈ Icc a b) (ψ : Z → U → ℝ)
    (hψ : ∀ ζ u, |ψ ζ u| ≤ 1) (e : Z × FinePairDensityIndex M) (u : U) :
    finePairFieldReset a b M p ψ e u ∈ Icc a b :=
  finePairDensityReset_mem_interval a b ha hab _ _
    (exteriorNode_mem a b hab.le (M + 2) e.2.1) (fineModulationNode_bound e.2.2)
    p (ψ e.1) u (hp u) (hψ e.1 u)

theorem finePairFieldReset_abs_le {U : Type*} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (M : ℕ) (p : U → ℝ) (hp : ∀ u, p u ∈ Icc a b) (ψ : Z → U → ℝ)
    (hψ : ∀ ζ u, |ψ ζ u| ≤ 1) (e : Z × FinePairDensityIndex M) (u : U) :
    |finePairFieldReset a b M p ψ e u| ≤ b := by
  have hh := finePairFieldReset_mem_interval a b ha hab M p hp ψ hψ e u
  rw [abs_of_nonneg (ha.le.trans hh.1)]
  exact hh.2

theorem finePairFieldSignedMeasure_mass_zero (π : Measure Z) [IsFiniteMeasure π]
    (a b : ℝ) (M : ℕ) :
    (∫ᵛ _e, (1 : ℝ) ∂<•finePairFieldSignedMeasure π a b M) = 0 := by
  rw [finePairFieldSignedMeasure_integral π a b M _ measurable_const 1 (by intro e; norm_num)]
  have hw : (∑ h : FinePairDensityIndex M, finePairDensityWeight a b M h) = 0 := by
    simpa only [finePairDensitySignedRule, atomicSignedRule_integral, mul_one] using
      finePairDensitySignedRule_mass_zero a b M
  simp [hw]

theorem finePairFieldSignedMeasure_linear_zero {U : Type*} (π : Measure Z) [IsFiniteMeasure π]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (M : ℕ)
    (p : U → ℝ) (hp : ∀ u, p u ∈ Icc a b) (ψ : Z → U → ℝ)
    (hmψ : ∀ u, Measurable (fun ζ => ψ ζ u)) (hψ : ∀ ζ u, |ψ ζ u| ≤ 1) (u : U) :
    (∫ᵛ e, finePairFieldReset a b M p ψ e u ∂<•finePairFieldSignedMeasure π a b M) = 0 := by
  rw [finePairFieldSignedMeasure_integral π a b M _ (finePairFieldReset_measurable a b M p ψ hmψ u) b
    (fun e => by simpa only [Real.norm_eq_abs] using finePairFieldReset_abs_le a b ha hab M p hp ψ hψ e u)]
  have he (ζ : Z) : (∑ h : FinePairDensityIndex M, finePairDensityWeight a b M h *
      finePairFieldReset a b M p ψ (ζ, h) u) = 0 := by
    simpa only [finePairDensitySignedRule, atomicSignedRule_integral, finePairFieldReset] using
      finePairDensitySignedRule_linear_zero a b M p (ψ ζ) u
  simp_rw [he]
  exact integral_zero _ _

theorem finePairFieldSignedMeasure_pair_exact {U : Type*} (π : Measure Z) [IsProbabilityMeasure π]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (M : ℕ) (hM : 2 ≤ M)
    (p : U → ℝ) (hp : ∀ u, p u ∈ Icc a b) (ψ : Z → U → ℝ)
    (hmψ : ∀ u, Measurable (fun ζ => ψ ζ u)) (hψ : ∀ ζ u, |ψ ζ u| ≤ 1) (u v : U) :
    (∫ᵛ e, finePairFieldReset a b M p ψ e u * finePairFieldReset a b M p ψ e v
      ∂<•finePairFieldSignedMeasure π a b M) = p u * p v * (∫ ζ, ψ ζ u * ψ ζ v ∂π) := by
  rw [finePairFieldSignedMeasure_integral π a b M
    (fun e : Z × FinePairDensityIndex M => finePairFieldReset a b M p ψ e u * finePairFieldReset a b M p ψ e v)
    ((finePairFieldReset_measurable a b M p ψ hmψ u).mul (finePairFieldReset_measurable a b M p ψ hmψ v))
    (b ^ 2) (fun e => by
      rw [Real.norm_eq_abs, abs_mul, pow_two]
      exact mul_le_mul (finePairFieldReset_abs_le a b ha hab M p hp ψ hψ e u)
        (finePairFieldReset_abs_le a b ha hab M p hp ψ hψ e v) (abs_nonneg _) (ha.trans hab).le)]
  have he (ζ : Z) : (∑ h : FinePairDensityIndex M, finePairDensityWeight a b M h *
      (finePairFieldReset a b M p ψ (ζ, h) u * finePairFieldReset a b M p ψ (ζ, h) v)) =
      (p u * p v) * (ψ ζ u * ψ ζ v) := by
    simpa only [finePairDensitySignedRule, atomicSignedRule_integral, finePairFieldReset, mul_assoc] using
      finePairDensitySignedRule_pair_exact a b ha hab M hM p (ψ ζ) u v
  simp_rw [he]
  exact integral_const_mul _ _

theorem finePairFieldSignedMeasure_pair_covariance {U : Type*} (π : Measure Z) [IsProbabilityMeasure π]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (M : ℕ) (hM : 2 ≤ M)
    (p : U → ℝ) (hp : ∀ u, p u ∈ Icc a b) (ψ : Z → U → ℝ)
    (hmψ : ∀ u, Measurable (fun ζ => ψ ζ u)) (hψ : ∀ ζ u, |ψ ζ u| ≤ 1)
    (K : U → U → ℝ) (hK : ∀ u v, (∫ ζ, ψ ζ u * ψ ζ v ∂π) = K u v) (u v : U) :
    (∫ᵛ e, finePairFieldReset a b M p ψ e u * finePairFieldReset a b M p ψ e v
      ∂<•finePairFieldSignedMeasure π a b M) = p u * p v * K u v := by
  rw [finePairFieldSignedMeasure_pair_exact π a b ha hab M hM p hp ψ hmψ hψ u v, hK]

theorem finePairFieldSignedMeasure_product_expansion {U : Type*} [DecidableEq U]
    (π : Measure Z) [IsFiniteMeasure π] (a b : ℝ) (ha : 0 < a) (hab : a < b) (M : ℕ)
    (S : Finset U) (p : U → ℝ) (hp : ∀ u, p u ∈ Icc a b) (ψ : Z → U → ℝ)
    (hmψ : ∀ u, Measurable (fun ζ => ψ ζ u)) (hψ : ∀ ζ u, |ψ ζ u| ≤ 1) :
    (∫ᵛ e, ∏ u ∈ S, finePairFieldReset a b M p ψ e u ∂<•finePairFieldSignedMeasure π a b M) =
      ∑ W ∈ S.powerset, finePairCountCoefficient a b M S.card W.card * (∏ u ∈ W, p u) *
        (∫ ζ, ∏ u ∈ W, ψ ζ u ∂π) * (if W.card = 0 then 0 else if Even W.card then 1 else 0) := by
  have hm : Measurable (fun e : Z × FinePairDensityIndex M => ∏ u ∈ S, finePairFieldReset a b M p ψ e u) :=
    Finset.measurable_fun_prod _ (fun u _ => finePairFieldReset_measurable a b M p ψ hmψ u)
  have hb (e : Z × FinePairDensityIndex M) : ‖∏ u ∈ S, finePairFieldReset a b M p ψ e u‖ ≤ b ^ S.card := by
    rw [Real.norm_eq_abs, Finset.abs_prod]
    exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun u _ =>
      finePairFieldReset_abs_le a b ha hab M p hp ψ hψ e u)).trans_eq (Finset.prod_const b)
  rw [finePairFieldSignedMeasure_integral π a b M _ hm (b ^ S.card) hb]
  have he (ζ : Z) : (∑ h : FinePairDensityIndex M, finePairDensityWeight a b M h *
      ∏ u ∈ S, finePairFieldReset a b M p ψ (ζ, h) u) =
      ∑ W ∈ S.powerset, finePairCountCoefficient a b M S.card W.card * (∏ u ∈ W, p u * ψ ζ u) *
        (if W.card = 0 then 0 else if Even W.card then 1 else 0) := by
    simpa only [finePairDensitySignedRule, atomicSignedRule_integral, finePairFieldReset] using
      finePairDensitySignedRule_product_expansion a b M S p (ψ ζ)
  simp_rw [he, Finset.prod_mul_distrib]
  have hi (W : Finset U) : Integrable (fun ζ => ∏ u ∈ W, ψ ζ u) π := by
    apply (integrable_const (1 : ℝ)).mono'
      (Finset.measurable_fun_prod _ (fun u _ => hmψ u)).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ζ
    rw [Real.norm_eq_abs, Finset.abs_prod]
    exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun u _ => hψ ζ u)).trans_eq (by simp)
  have ht (W : Finset U) (ζ : Z) : finePairCountCoefficient a b M S.card W.card *
      ((∏ u ∈ W, p u) * ∏ u ∈ W, ψ ζ u) *
      (if W.card = 0 then 0 else if Even W.card then 1 else 0) =
      (finePairCountCoefficient a b M S.card W.card * (∏ u ∈ W, p u) *
        (if W.card = 0 then 0 else if Even W.card then 1 else 0)) * (∏ u ∈ W, ψ ζ u) := by ring
  simp_rw [ht]
  rw [integral_finsetSum _ (fun W _ => (hi W).const_mul _)]
  simp_rw [integral_const_mul]
  apply Finset.sum_congr rfl
  intro W _
  ring

end Field

end NearlyMinimax
