module

public import Mathlib
public import RoughRegime.LiftTranslation
public import RoughRegime.PolynomialCells
public import RoughRegime.ComplexDerivativeBridge
public import RoughRegime.Centering


@[expose] public section

/-! Cell support and numerical estimates in the variance proof of Lemma 8. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace RoughRegime.LiftVariance

def cellIndicator {Ω : Type*} {K : ℕ} (cell : Ω → Fin K) (c : Fin K) (ω : Ω) : ℝ :=
  if cell ω = c then 1 else 0

lemma measurable_cellIndicator {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (cell : Ω → Fin K) (hcell : Measurable cell) (c : Fin K) :
    Measurable (cellIndicator cell c) := by
  unfold cellIndicator
  exact Measurable.ite (hcell (measurableSet_singleton c)) measurable_const measurable_const

lemma integral_cellIndicator {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K : ℕ} (cell : Ω → Fin K) (hcell : Measurable cell) (c : Fin K) :
    (∫ ω, cellIndicator cell c ω ∂μ) = μ.real {ω | cell ω = c} := by
  have hset : MeasurableSet {ω | cell ω = c} := hcell (measurableSet_singleton c)
  have heq : cellIndicator cell c = Set.indicator {ω | cell ω = c} (fun _ => (1 : ℝ)) := by
    funext ω
    simp [cellIndicator, Set.indicator]
  rw [heq, integral_indicator_const 1 hset]
  simp

lemma integral_product_cellIndicator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K r : ℕ}
    (cell : Fin r → Ω → Fin K) (hi : iIndepFun cell μ)
    (hm : ∀ i, Measurable (cell i)) (c : Fin K) :
    (∫ ω, ∏ i : Fin r, cellIndicator (cell i) c ω ∂μ) =
      ∏ i : Fin r, μ.real {ω | cell i ω = c} := by
  have hind : iIndepFun (fun i => cellIndicator (cell i) c) μ := by
    exact hi.comp (fun _ => fun x : Fin K => if x = c then (1 : ℝ) else 0)
      (fun _ => measurable_of_finite _)
  rw [hind.integral_fun_prod_eq_prod_integral]
  · simp_rw [integral_cellIndicator μ _ (hm _) c]
  · intro i
    exact (measurable_cellIndicator (cell i) (hm i) c).aestronglyMeasurable

/-- A multilinear cell kernel vanishes unless every argument belongs to that cell. -/
lemma cell_kernel_vanishes {K p r : ℕ} (H : Fin K → ContinuousMultilinearMap ℝ
    (fun _ : Fin r => Fin p → ℝ) ℝ) (cell : Fin r → Fin K)
    (Z : Fin r → Fin K → Fin p → ℝ)
    (hz : ∀ i c, cell i ≠ c → Z i c = 0) (c : Fin K)
    (i : Fin r) (hic : cell i ≠ c) : H c (fun j => Z j c) = 0 := by
  exact (H c).map_coord_zero i (hz i c hic)

/-- Cell disjointness removes every cross term in the square of the kernel sum. -/
theorem square_cell_kernel_sum {K p r : ℕ} (hr : 0 < r)
    (H : Fin K → ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (cell : Fin r → Fin K) (Z : Fin r → Fin K → Fin p → ℝ)
    (hz : ∀ i c, cell i ≠ c → Z i c = 0) :
    (∑ c : Fin K, H c (fun i => Z i c)) ^ 2 =
      ∑ c : Fin K, (H c (fun i => Z i c)) ^ 2 := by
  classical
  let c₀ := cell ⟨0, hr⟩
  have hzero (c : Fin K) (hc : c ≠ c₀) : H c (fun i => Z i c) = 0 :=
    cell_kernel_vanishes H cell Z hz c ⟨0, hr⟩ (Ne.symm hc)
  rw [Finset.sum_eq_single c₀]
  · rw [Finset.sum_eq_single c₀]
    · intro c _ hc
      rw [hzero c hc, zero_pow (by omega)]
    · exact (fun h => (h (Finset.mem_univ _)).elim)
  · intro c _ hc
    exact hzero c hc
  · exact (fun h => (h (Finset.mem_univ _)).elim)

lemma kernel_square_bound {p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (A B : ℝ) (hA : ‖H‖ ≤ A) (_hB : 0 ≤ B) (v : Fin r → Fin p → ℝ)
    (hv : ∀ i, ‖v i‖ ≤ B) : H v ^ 2 ≤ A ^ 2 * B ^ (2 * r) := by
  have hA0 : 0 ≤ A := (norm_nonneg H).trans hA
  have hn : ‖H v‖ ≤ A * B ^ r := by
    simpa using H.le_mul_prod_of_opNorm_le_of_le hA hv
  have hsq := pow_le_pow_left₀ (norm_nonneg (H v)) hn 2
  simpa [Real.norm_eq_abs, sq_abs, mul_pow, ← pow_mul, Nat.mul_comm] using hsq

lemma cell_kernel_square_bound {K p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (A B : ℝ) (hA : ‖H‖ ≤ A) (hB : 0 ≤ B)
    (cell : Fin r → Fin K) (c : Fin K) (v : Fin r → Fin p → ℝ)
    (hv : ∀ i, ‖v i‖ ≤ B) (hz : ∀ i, cell i ≠ c → v i = 0) :
    H v ^ 2 ≤ A ^ 2 * B ^ (2 * r) * ∏ i : Fin r, (if cell i = c then (1 : ℝ) else 0) := by
  classical
  by_cases hall : ∀ i, cell i = c
  · simp only [hall, ↓reduceIte, Finset.prod_const_one, mul_one]
    exact kernel_square_bound H A B hA hB v hv
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have hH : H v = 0 := H.map_coord_zero i (hz i hi)
    have hprod : (∏ i : Fin r, (if cell i = c then (1 : ℝ) else 0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [hH, hprod]
    simp

lemma product_cellIndicator_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K r : ℕ}
    (cell : Fin r → Ω → Fin K) (hm : ∀ i, Measurable (cell i)) (c : Fin K) :
    Integrable (fun ω => ∏ i : Fin r, cellIndicator (cell i) c ω) μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (Finset.measurable_prod _ (fun i _ => measurable_cellIndicator (cell i) (hm i) c)).aestronglyMeasurable
  · filter_upwards [] with ω
    rw [norm_prod]
    calc
      (∏ i : Fin r, ‖cellIndicator (cell i) c ω‖) ≤ ∏ _i : Fin r, (1 : ℝ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i _
        simp only [cellIndicator]
        split_ifs <;> norm_num
      _ = 1 := by simp

/-- Exact cell-event second-moment bound, derived from disjoint support and independence. -/
theorem cell_kernel_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (cell : Fin r → Ω → Fin K) (hi : iIndepFun cell μ)
    (hmcell : ∀ i, Measurable (cell i)) (c : Fin K)
    (Z : Fin r → Ω → Fin p → ℝ) (hmZ : ∀ i, Measurable (Z i))
    (A B : ℝ) (hA : ‖H‖ ≤ A) (hB : 0 ≤ B)
    (hb : ∀ i ω, ‖Z i ω‖ ≤ B) (hz : ∀ i ω, cell i ω ≠ c → Z i ω = 0) :
    (∫ ω, H (fun i => Z i ω) ^ 2 ∂μ) ≤
      A ^ 2 * B ^ (2 * r) * ∏ i : Fin r, μ.real {ω | cell i ω = c} := by
  have hmeas : Measurable (fun ω => H (fun i => Z i ω) ^ 2) :=
    (H.cont.measurable.comp (measurable_pi_iff.mpr hmZ)).pow_const 2
  have hint : Integrable (fun ω => H (fun i => Z i ω) ^ 2) μ := by
    apply (integrable_const (A ^ 2 * B ^ (2 * r))).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact kernel_square_bound H A B hA hB _ (fun i => hb i ω)
  calc
    (∫ ω, H (fun i => Z i ω) ^ 2 ∂μ) ≤
        ∫ ω, A ^ 2 * B ^ (2 * r) * ∏ i : Fin r, cellIndicator (cell i) c ω ∂μ := by
      apply integral_mono hint ((product_cellIndicator_integrable μ cell hmcell c).const_mul _)
      intro ω
      exact cell_kernel_square_bound H A B hA hB (fun i => cell i ω) c
        (fun i => Z i ω) (fun i => hb i ω) (fun i h => hz i ω h)
    _ = _ := by rw [integral_const_mul, integral_product_cellIndicator μ cell hi hmcell c]


lemma kernel_square_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (Z : Fin r → Ω → Fin p → ℝ) (hmZ : ∀ i, Measurable (Z i))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ i ω, ‖Z i ω‖ ≤ B) :
    Integrable (fun ω => H (fun i => Z i ω) ^ 2) μ := by
  have hmeas : Measurable (fun ω => H (fun i => Z i ω) ^ 2) :=
    (H.cont.measurable.comp (measurable_pi_iff.mpr hmZ)).pow_const 2
  apply (integrable_const (‖H‖ ^ 2 * B ^ (2 * r))).mono' hmeas.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact kernel_square_bound H ‖H‖ B le_rfl hB _ (fun i => hb i ω)

def aggregateCellKernel {Ω : Type*} {K p r : ℕ}
    (H : Fin K → ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (Z : Fin r → Ω → Fin K → Fin p → ℝ) (ω : Ω) : ℝ :=
  (K : ℝ)⁻¹ * ∑ c : Fin K, H c (fun i => Z i ω c)

/-- Summing over a partition saves exactly a factor `K`; cross-cell terms vanish. -/
theorem aggregate_cell_kernel_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K p r : ℕ} (hK : 0 < K) (hr : 0 < r)
    (H : Fin K → ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (cell : Fin r → Ω → Fin K) (hi : iIndepFun cell μ) (hmcell : ∀ i, Measurable (cell i))
    (Z : Fin r → Ω → Fin K → Fin p → ℝ) (hmZ : ∀ i c, Measurable (fun ω => Z i ω c))
    (A B π : ℝ) (hA : ∀ c, ‖H c‖ ≤ A) (hB : 0 ≤ B) (_hπ : 0 ≤ π)
    (hb : ∀ i ω c, ‖Z i ω c‖ ≤ B) (hz : ∀ i ω c, cell i ω ≠ c → Z i ω c = 0)
    (hprob : ∀ i c, μ.real {ω | cell i ω = c} ≤ π) :
    (∫ ω, aggregateCellKernel H Z ω ^ 2 ∂μ) ≤ A ^ 2 * B ^ (2 * r) * π ^ r / K := by
  classical
  have hint (c : Fin K) := kernel_square_integrable μ (H c) (fun i ω => Z i ω c)
    (fun i => hmZ i c) B hB (fun i ω => hb i ω c)
  have heq (ω : Ω) : aggregateCellKernel H Z ω ^ 2 =
      (K : ℝ)⁻¹ ^ 2 * ∑ c : Fin K, (H c (fun i => Z i ω c)) ^ 2 := by
    rw [aggregateCellKernel, mul_pow,
      square_cell_kernel_sum hr H (fun i => cell i ω) (fun i c => Z i ω c)
        (fun i c h => hz i ω c h)]
  have hbound (c : Fin K) : (∫ ω, H c (fun i => Z i ω c) ^ 2 ∂μ) ≤
      A ^ 2 * B ^ (2 * r) * π ^ r := by
    calc
      _ ≤ A ^ 2 * B ^ (2 * r) * ∏ i : Fin r, μ.real {ω | cell i ω = c} :=
        cell_kernel_second_moment μ (H c) cell hi hmcell c (fun i ω => Z i ω c)
          (fun i => hmZ i c) A B (hA c) hB (fun i ω => hb i ω c) (fun i ω h => hz i ω c h)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (pow_nonneg hB _))
        calc
          _ ≤ ∏ _i : Fin r, π :=
            Finset.prod_le_prod₀ (fun _ _ => measureReal_nonneg) (fun i _ => hprob i c)
          _ = _ := by simp
  simp_rw [heq]
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun c _ => hint c)]
  calc
    _ ≤ (K : ℝ)⁻¹ ^ 2 * ∑ _c : Fin K, A ^ 2 * B ^ (2 * r) * π ^ r :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hbound c)) (sq_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hK)
      field_simp


/-- Squared Euclidean norm, used to express the paper's `ℓ²` hypotheses. -/
def euclideanSquare {p : ℕ} (x : Fin p → ℝ) : ℝ := ∑ i : Fin p, x i ^ 2

lemma norm_le_of_euclideanSquare_le {p : ℕ} (x : Fin p → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hb : euclideanSquare x ≤ B ^ 2) : ‖x‖ ≤ B := by
  rw [pi_norm_le_iff_of_nonneg hB]
  intro i
  have hx : x i ^ 2 ≤ B ^ 2 :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)).trans hb
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) hB).mp
  simpa only [sq_abs] using hx

lemma continuousLinearMap_coordinate_expansion {p : ℕ}
    (L : (Fin p → ℝ) →L[ℝ] ℝ) (x : Fin p → ℝ) :
    L x = ∑ i : Fin p, L (Pi.single i 1) * x i := by
  have hx : x = ∑ i : Fin p, x i • Pi.single i (1 : ℝ) := by
    funext j
    simp [Pi.single_apply]
  rw [hx, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul]
  rw [← hx]
  exact mul_comm _ _

lemma linear_kernel_euclidean_square_bound {p : ℕ}
    (L : (Fin p → ℝ) →L[ℝ] ℝ) (x : Fin p → ℝ) :
    (L x) ^ 2 ≤ euclideanSquare (fun i => L (Pi.single i 1)) * euclideanSquare x := by
  rw [continuousLinearMap_coordinate_expansion]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- First-order cell kernels use the gradient bound and partition support, without
paying a cell probability factor. -/
theorem aggregate_linear_cell_kernel_square_bound {K p : ℕ} (_hK : 0 < K)
    (L : Fin K → (Fin p → ℝ) →L[ℝ] ℝ) (cell : Fin K) (Z : Fin K → Fin p → ℝ)
    (G B : ℝ) (_hG : 0 ≤ G) (_hB : 0 ≤ B)
    (hgrad : ∀ c, euclideanSquare (fun i => L c (Pi.single i 1)) ≤ G ^ 2)
    (hZ : ∀ c, euclideanSquare (Z c) ≤ B ^ 2 * (if cell = c then (1 : ℝ) else 0)) :
    ((K : ℝ)⁻¹ * ∑ c : Fin K, L c (Z c)) ^ 2 ≤ G ^ 2 * B ^ 2 / (K : ℝ) ^ 2 := by
  classical
  have hz (c : Fin K) (hc : c ≠ cell) : Z c = 0 := by
    have hb : euclideanSquare (Z c) ≤ 0 := by simpa [Ne.symm hc] using hZ c
    have hn := norm_le_of_euclideanSquare_le (Z c) 0 le_rfl (by simpa using hb)
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  have hsum : (∑ c : Fin K, L c (Z c)) = L cell (Z cell) := by
    apply Finset.sum_eq_single cell
    · intro c _ hc
      rw [hz c hc, map_zero]
    · exact (fun h => (h (Finset.mem_univ _)).elim)
  rw [hsum, mul_pow]
  calc
    _ ≤ (K : ℝ)⁻¹ ^ 2 * (G ^ 2 * B ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      calc
        _ ≤ euclideanSquare (fun i => L cell (Pi.single i 1)) * euclideanSquare (Z cell) :=
          linear_kernel_euclidean_square_bound _ _
        _ ≤ G ^ 2 * B ^ 2 := by
          apply mul_le_mul (hgrad cell)
          · simpa using hZ cell
          · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
          · exact sq_nonneg _
    _ = _ := by rw [div_eq_mul_inv, inv_pow]; ring


lemma cell_vector_bound_and_support {K p : ℕ} (cell c : Fin K) (Z : Fin p → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hZ : euclideanSquare Z ≤ B ^ 2 * (if cell = c then (1 : ℝ) else 0)) :
    ‖Z‖ ≤ B ∧ (cell ≠ c → Z = 0) := by
  constructor
  · apply norm_le_of_euclideanSquare_le Z B hB
    split_ifs at hZ with h
    · simpa using hZ
    · have hzero : euclideanSquare Z ≤ 0 := by simpa using hZ
      exact hzero.trans (sq_nonneg B)
  · intro h
    have hb : euclideanSquare Z ≤ 0 := by simpa [h] using hZ
    have hn := norm_le_of_euclideanSquare_le Z 0 le_rfl (by simpa using hb)
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

lemma sparse_cell_constant_identity (A C0 K : ℝ) (r : ℕ) (hK : K ≠ 0) (hr : 1 ≤ r) :
    A ^ 2 * (C0 * K) ^ (2 * r) * (C0 / K) ^ r / K =
      A ^ 2 * C0 ^ (3 * r) * K ^ (r - 1) := by
  have hKpow : K ^ r = K ^ (r - 1) * K := by rw [← pow_succ]; congr 1; omega
  rw [show 2 * r = r * 2 by omega, show 3 * r = r * 3 by omega, pow_mul, pow_mul]
  simp only [mul_pow, div_pow]
  rw [hKpow]
  field_simp

lemma cauchy_cell_constant_absorption (C0 : ℝ) (r : ℕ) (hC0 : 1 ≤ C0) (hr : 1 ≤ r) :
    (C0 * (r.factorial : ℝ) * (Real.exp 1 * C0) ^ r) ^ 2 * C0 ^ (3 * r) ≤
      (r.factorial : ℝ) ^ 2 * (Real.exp 1 ^ 2 * C0 ^ 7) ^ r := by
  have hC0pos : 0 ≤ C0 := le_trans zero_le_one hC0
  have hpow : C0 ^ 2 ≤ C0 ^ (2 * r) := pow_le_pow_right₀ hC0 (by omega)
  have hfactor : 0 ≤ (r.factorial : ℝ) ^ 2 * (Real.exp 1 ^ 2 * C0 ^ 5) ^ r := by positivity
  have hC : (C0 ^ r) ^ 2 * C0 ^ (3 * r) = (C0 ^ 5) ^ r := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  have he : (Real.exp 1 ^ r) ^ 2 = (Real.exp 1 ^ 2) ^ r := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  calc
    _ = C0 ^ 2 * (r.factorial : ℝ) ^ 2 *
        ((Real.exp 1 ^ r) ^ 2 * ((C0 ^ r) ^ 2 * C0 ^ (3 * r))) := by
      simp only [mul_pow]
      ring
    _ = C0 ^ 2 * ((r.factorial : ℝ) ^ 2 * (Real.exp 1 ^ 2 * C0 ^ 5) ^ r) := by
      rw [hC, he, mul_pow]
      ring
    _ ≤ C0 ^ (2 * r) * ((r.factorial : ℝ) ^ 2 * (Real.exp 1 ^ 2 * C0 ^ 5) ^ r) :=
      mul_le_mul_of_nonneg_right hpow hfactor
    _ = (r.factorial : ℝ) ^ 2 * ((C0 ^ 2) ^ r * (Real.exp 1 ^ 2 * C0 ^ 5) ^ r) := by
      rw [pow_mul]
      ring
    _ = (r.factorial : ℝ) ^ 2 * (C0 ^ 2 * (Real.exp 1 ^ 2 * C0 ^ 5)) ^ r := by rw [← mul_pow]
    _ = _ := by congr 2; ring

/-- The higher-order kernel moment estimate in the proof of Lemma 8, with the paper's
exact power `e² C₀⁷`, follows from the complex bound on the actual cell polynomials. -/
theorem polynomial_cell_higher_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {K p r : ℕ} (hK : 0 < K) (hr : 0 < r)
    (F : Fin K → MvPolynomial (Fin p) ℝ) (m : Fin K → Fin p → ℝ)
    (cell : Fin r → Ω → Fin K) (hi : iIndepFun cell μ) (hmcell : ∀ i, Measurable (cell i))
    (Z : Fin r → Ω → Fin K → Fin p → ℝ) (hmZ : ∀ i c, Measurable (fun ω => Z i ω c))
    (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hcomplex : ∀ c y, ‖y - (fun j => (m c j : ℂ))‖ < 1 / C0 →
      ‖MvPolynomial.eval y (RoughRegime.ComplexDerivativeBridge.complexify (F c))‖ ≤ C0)
    (hZ : ∀ i ω c, euclideanSquare (Z i ω c) ≤ (C0 * K) ^ 2 * cellIndicator (cell i) c ω)
    (hprob : ∀ i c, μ.real {ω | cell i ω = c} ≤ C0 / K) :
    (∫ ω, aggregateCellKernel (fun c => iteratedFDeriv ℝ r
        (fun x => MvPolynomial.eval x (F c)) (m c)) Z ω ^ 2 ∂μ) ≤
      (r.factorial : ℝ) ^ 2 * (Real.exp 1 ^ 2 * C0 ^ 7) ^ r * (K : ℝ) ^ (r - 1) := by
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast hK
  have hobs (i : Fin r) (ω : Ω) (c : Fin K) :=
    cell_vector_bound_and_support (cell i ω) c (Z i ω c) (C0 * K)
      (mul_nonneg hC0pos.le hKpos.le) (hZ i ω c)
  have hderiv (c : Fin K) : ‖iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x (F c)) (m c)‖ ≤
      C0 * (r.factorial : ℝ) * (Real.exp 1 * C0) ^ r := by
    have h := RoughRegime.ComplexDerivativeBridge.real_polynomial_derivative_norm_bound
      (F c) (m c) (1 / C0) C0 (one_div_pos.mpr hC0pos) hC0pos.le (hcomplex c) hr
    simpa only [one_div, div_inv_eq_mul] using h
  calc
    _ ≤ (C0 * (r.factorial : ℝ) * (Real.exp 1 * C0) ^ r) ^ 2 * (C0 * K) ^ (2 * r) *
        (C0 / K) ^ r / K :=
      aggregate_cell_kernel_second_moment μ hK hr _ cell hi hmcell Z hmZ _ _ _ hderiv
        (mul_nonneg hC0pos.le hKpos.le) (div_nonneg hC0pos.le hKpos.le)
        (fun i ω c => (hobs i ω c).1) (fun i ω c h => (hobs i ω c).2 h) hprob
    _ = _ ^ 2 * C0 ^ (3 * r) * (K : ℝ) ^ (r - 1) :=
      sparse_cell_constant_identity _ C0 K r hKpos.ne' hr
    _ ≤ _ := mul_le_mul_of_nonneg_right (cauchy_cell_constant_absorption C0 r hC0 hr)
      (pow_nonneg hKpos.le _)


lemma full_observable_bound {K p : ℕ} (x : Fin (K * p) → ℝ) (cell : Fin K)
    (B : ℝ) (hB : 0 ≤ B)
    (hZ : ∀ c, euclideanSquare (RoughRegime.PolynomialCells.cellProjection c x) ≤
      B ^ 2 * (if cell = c then (1 : ℝ) else 0)) : ‖x‖ ≤ B := by
  rw [pi_norm_le_iff_of_nonneg hB]
  intro j
  let c := (finProdFinEquiv.symm j).1
  let i := (finProdFinEquiv.symm j).2
  have hcell := (cell_vector_bound_and_support cell c
    (RoughRegime.PolynomialCells.cellProjection c x) B hB (hZ c)).1
  have hj := (norm_le_pi_norm (RoughRegime.PolynomialCells.cellProjection c x) i).trans hcell
  simpa only [RoughRegime.PolynomialCells.cellProjection_apply, c, i,
    Prod.mk.eta, Equiv.apply_symm_apply] using hj

lemma population_vector_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ}
    (X : Ω → Fin p → ℝ) (hm : Measurable X) (M : ℝ) (hb : ∀ ω, ‖X ω‖ ≤ M)
    (m : Fin p → ℝ) (hmean : ∀ i, ∫ ω, X ω i ∂μ = m i) :
    (∫ ω, X ω ∂μ) = m := by
  have hint : Integrable X μ := Integrable.of_bound hm.aestronglyMeasurable M (Filter.Eventually.of_forall hb)
  funext i
  have h := (ContinuousLinearMap.proj i : (Fin p → ℝ) →L[ℝ] ℝ).integral_comp_comm hint
  exact h.symm.trans (hmean i)

/-- The precise first-order uncentered derivative estimate used in Lemma 8. -/
lemma polynomial_cell_first_kernel_bound {K p : ℕ} (hK : 0 < K)
    (F : Fin K → MvPolynomial (Fin p) ℝ) (m x : Fin (K * p) → ℝ) (cell : Fin K)
    (C0 η : ℝ) (hC0 : 0 ≤ C0) (hη : 0 ≤ η)
    (hgrad : ∀ c, euclideanSquare (fun j => fderiv ℝ (fun y => MvPolynomial.eval y (F c))
      (RoughRegime.PolynomialCells.cellProjection c m) (Pi.single j 1)) ≤ (C0 * η) ^ 2)
    (hZ : ∀ c, euclideanSquare (RoughRegime.PolynomialCells.cellProjection c x) ≤
      (C0 * K) ^ 2 * (if cell = c then (1 : ℝ) else 0)) :
    (fderiv ℝ (fun y => MvPolynomial.eval y (RoughRegime.PolynomialCells.cellMomentPolynomial F)) m x) ^ 2 ≤
      C0 ^ 4 * η ^ 2 := by
  have heq : fderiv ℝ (fun y => MvPolynomial.eval y
      (RoughRegime.PolynomialCells.cellMomentPolynomial F)) m x =
      (K : ℝ)⁻¹ * ∑ c : Fin K, fderiv ℝ (fun y => MvPolynomial.eval y (F c))
        (RoughRegime.PolynomialCells.cellProjection c m)
        (RoughRegime.PolynomialCells.cellProjection c x) := by
    simpa only [iteratedFDeriv_one_apply] using
      RoughRegime.PolynomialCells.cellMomentPolynomial_iteratedFDeriv F m (fun _ : Fin 1 => x)
  rw [heq]
  calc
    _ ≤ (C0 * η) ^ 2 * (C0 * K) ^ 2 / (K : ℝ) ^ 2 :=
      aggregate_linear_cell_kernel_square_bound hK _ cell _ (C0 * η) (C0 * K)
        (mul_nonneg hC0 hη) (mul_nonneg hC0 (Nat.cast_nonneg K)) hgrad hZ
    _ = _ := by
      have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hK)
      field_simp

lemma polynomial_cell_raw_higher_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n K p r : ℕ} (hK : 0 < K) (hr : 0 < r)
    (F : Fin K → MvPolynomial (Fin p) ℝ) (m : Fin (K * p) → ℝ)
    (X : Fin n → Ω → Fin (K * p) → ℝ) (hmX : ∀ j, Measurable (X j))
    (cell : Fin n → Ω → Fin K) (hiCell : iIndepFun cell μ) (hmCell : ∀ i, Measurable (cell i))
    (e : Fin r ↪ Fin n) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hcomplex : ∀ c y, ‖y - (fun j => (RoughRegime.PolynomialCells.cellProjection c m j : ℂ))‖ < 1 / C0 →
      ‖MvPolynomial.eval y (RoughRegime.ComplexDerivativeBridge.complexify (F c))‖ ≤ C0)
    (hZ : ∀ i ω c, euclideanSquare (RoughRegime.PolynomialCells.cellProjection c (X i ω)) ≤
      (C0 * K) ^ 2 * cellIndicator (cell i) c ω)
    (hprob : ∀ i c, μ.real {ω | cell i ω = c} ≤ C0 / K) :
    (∫ ω, (iteratedFDeriv ℝ r (fun y => MvPolynomial.eval y
        (RoughRegime.PolynomialCells.cellMomentPolynomial F)) m (fun i => X (e i) ω)) ^ 2 ∂μ) ≤
      (r.factorial : ℝ) ^ 2 * (Real.exp 1 ^ 2 * C0 ^ 7) ^ r * (K : ℝ) ^ (r - 1) := by
  have heq (ω : Ω) : iteratedFDeriv ℝ r (fun y => MvPolynomial.eval y
      (RoughRegime.PolynomialCells.cellMomentPolynomial F)) m (fun i => X (e i) ω) =
      aggregateCellKernel (fun c => iteratedFDeriv ℝ r (fun y => MvPolynomial.eval y (F c))
        (RoughRegime.PolynomialCells.cellProjection c m))
        (fun i ω c => RoughRegime.PolynomialCells.cellProjection c (X (e i) ω)) ω :=
    RoughRegime.PolynomialCells.cellMomentPolynomial_iteratedFDeriv F m _
  simp_rw [heq]
  exact polynomial_cell_higher_moment_bound μ hK hr F
    (fun c => RoughRegime.PolynomialCells.cellProjection c m)
    (fun i ω => cell (e i) ω) (hiCell.precomp e.injective) (fun i => hmCell (e i))
    (fun i ω c => RoughRegime.PolynomialCells.cellProjection c (X (e i) ω))
    (fun i c => (RoughRegime.PolynomialCells.cellProjection c).continuous.measurable.comp (hmX (e i)))
    C0 hC0 hcomplex (fun i ω c => hZ (e i) ω c) (fun i c => hprob (e i) c)


lemma descFactorial_half_lower_bound (n r : ℕ) (hr : 2 * r ≤ n) :
    ((n : ℝ) / 2) ^ r ≤ (n.descFactorial r : ℝ) := by
  have hrn : r ≤ n + 1 := by omega
  have hb : (n : ℝ) / 2 ≤ ((n + 1 - r : ℕ) : ℝ) := by
    rw [Nat.cast_sub hrn, Nat.cast_add, Nat.cast_one]
    have h := (Nat.cast_le (α := ℝ)).mpr hr
    norm_num at h
    linarith
  calc
    ((n : ℝ) / 2) ^ r ≤ (((n + 1 - r : ℕ) : ℝ)) ^ r :=
      pow_le_pow_left₀ (by positivity) hb r
    _ ≤ (n.descFactorial r : ℝ) := by exact_mod_cast Nat.pow_sub_le_descFactorial n r

/-- The factorial series appearing in the source variance bound. -/
def varianceTerm (Cv K n : ℝ) (r : ℕ) : ℝ :=
  Cv ^ r * (r.factorial : ℝ) * (K / n) ^ (r - 1) / n

lemma sparse_variance_term_bound (n r : ℕ) (B K : ℝ) (hr : 1 ≤ r) (hrn : 2 * r ≤ n)
    (hB : 0 ≤ B) (hK : 0 ≤ K) :
    (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ *
      ((r.factorial : ℝ) ^ 2 * B ^ r * K ^ (r - 1))) ≤ varianceTerm (2 * B) K n r := by
  have hn : 0 < (n : ℝ) := by
    have h : 0 < n := by omega
    exact_mod_cast h
  have hfac : 0 < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hhalf : 0 < (n : ℝ) / 2 := by positivity
  have hraw : 0 ≤ (r.factorial : ℝ) ^ 2 * B ^ r * K ^ (r - 1) := by positivity
  have hden : (r.factorial : ℝ) * ((n : ℝ) / 2) ^ r ≤
      (r.factorial : ℝ) * (n.descFactorial r : ℝ) :=
    mul_le_mul_of_nonneg_left (descFactorial_half_lower_bound n r hrn) hfac.le
  have hNpow : (n : ℝ) ^ r = (n : ℝ) ^ (r - 1) * n := by rw [← pow_succ]; congr 1; omega
  calc
    _ = ((r.factorial : ℝ) ^ 2 * B ^ r * K ^ (r - 1)) /
        ((r.factorial : ℝ) * (n.descFactorial r : ℝ)) := by rw [div_eq_mul_inv]; ring
    _ ≤ ((r.factorial : ℝ) ^ 2 * B ^ r * K ^ (r - 1)) /
        ((r.factorial : ℝ) * ((n : ℝ) / 2) ^ r) :=
      div_le_div_of_nonneg_left hraw (mul_pos hfac (pow_pos hhalf r)) hden
    _ = _ := by
      unfold varianceTerm
      simp only [mul_pow, div_pow]
      rw [hNpow]
      have hfac0 := hfac.ne'
      have hn0 := hn.ne'
      field_simp


lemma varianceTerm_nonneg (Cv K n : ℝ) (hCv : 0 ≤ Cv) (hK : 0 ≤ K) (hn : 0 ≤ n) (r : ℕ) :
    0 ≤ varianceTerm Cv K n r := by unfold varianceTerm; positivity

lemma varianceTerm_succ (Cv K n : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    varianceTerm Cv K n (r + 1) = Cv * (r + 1) * (K / n) * varianceTerm Cv K n r := by
  have hpow : (K / n) ^ r = (K / n) ^ (r - 1) * (K / n) := by
    rw [← pow_succ]
    congr 1
    omega
  unfold varianceTerm
  rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ, hpow]
  ring

/-- Under the paper's small-resolution condition, the sum of orders two through `R`
is at most twice its first term, giving its stated constant `4`. -/
theorem variance_tail_small_resolution (Cv K n : ℝ) (R : ℕ)
    (hCv : 0 ≤ Cv) (hK : 0 ≤ K) (hn : 0 < n) (hsmall : Cv * R * K / n ≤ 1 / 2) :
    (∑ j ∈ Finset.range (R - 1), varianceTerm Cv K n (j + 2)) ≤
      4 * Cv ^ 2 * K / n ^ 2 := by
  have hKn : 0 ≤ K / n := div_nonneg hK hn.le
  have hterm0 := varianceTerm_nonneg Cv K n hCv hK hn.le 2
  have hstep (r : ℕ) (hr : 1 ≤ r) (hrR : r + 1 ≤ R) :
      varianceTerm Cv K n (r + 1) ≤ (1 / 2) * varianceTerm Cv K n r := by
    rw [varianceTerm_succ Cv K n r hr]
    apply mul_le_mul_of_nonneg_right _ (varianceTerm_nonneg Cv K n hCv hK hn.le r)
    calc
      Cv * ((r : ℝ) + 1) * (K / n) ≤ Cv * (R : ℝ) * (K / n) := by
        gcongr
        exact_mod_cast hrR
      _ ≤ 1 / 2 := by simpa only [mul_div_assoc] using hsmall
  have hgeom (j : ℕ) (hj : j < R - 1) :
      varianceTerm Cv K n (j + 2) ≤ (1 / 2 : ℝ) ^ j * varianceTerm Cv K n 2 := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hj' : j < R - 1 := by omega
      calc
        varianceTerm Cv K n (j + 1 + 2) ≤ (1 / 2) * varianceTerm Cv K n (j + 2) :=
          hstep (j + 2) (by omega) (by omega)
        _ ≤ (1 / 2) * ((1 / 2 : ℝ) ^ j * varianceTerm Cv K n 2) :=
          mul_le_mul_of_nonneg_left (ih hj') (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  calc
    (∑ j ∈ Finset.range (R - 1), varianceTerm Cv K n (j + 2)) ≤
        ∑ j ∈ Finset.range (R - 1), (1 / 2 : ℝ) ^ j * varianceTerm Cv K n 2 :=
      Finset.sum_le_sum (fun j hj => hgeom j (Finset.mem_range.mp hj))
    _ = (∑ j ∈ Finset.range (R - 1), (1 / 2 : ℝ) ^ j) * varianceTerm Cv K n 2 :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * varianceTerm Cv K n 2 := by
      apply mul_le_mul_of_nonneg_right _ hterm0
      have hs : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) := summable_geometric_of_abs_lt_one (by norm_num)
      calc
        (∑ j ∈ Finset.range (R - 1), (1 / 2 : ℝ) ^ j) ≤ ∑' j : ℕ, (1 / 2 : ℝ) ^ j :=
          hs.sum_le_tsum (Finset.range (R - 1)) (fun j _ => by positivity)
        _ = 2 := by rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)]; norm_num
    _ = _ := by unfold varianceTerm; norm_num; ring

def varianceConstant (C0 : ℝ) : ℝ := 2 * Real.exp 1 ^ 2 * C0 ^ 7

lemma first_order_constant_le_varianceConstant (C0 : ℝ) (hC0 : 1 ≤ C0) :
    C0 ^ 4 ≤ varianceConstant C0 := by
  have hC0n : 0 ≤ C0 := le_trans zero_le_one hC0
  have hpow : C0 ^ 4 ≤ C0 ^ 7 := pow_le_pow_right₀ hC0 (by norm_num)
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have he2 : 1 ≤ Real.exp 1 ^ 2 := one_le_pow₀ he
  unfold varianceConstant
  have hc : 0 ≤ C0 ^ 7 := pow_nonneg hC0n 7
  nlinarith

lemma polynomialLift_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ)
    (hm : ∀ j, Measurable (X j)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ j ω, ‖X j ω‖ ≤ M) : Integrable (RoughRegime.Upper.polynomialLift F X) μ := by
  classical
  unfold RoughRegime.Upper.polynomialLift
  apply integrable_finsetSum
  intro α _
  apply Integrable.const_mul
  exact RoughRegime.Upper.monomialLift_integrable μ _ X hm M hM
    (fun j ω i => by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (X j ω) i).trans (hb j ω))

/-- Lemma 7 specialized to variance and truncated at the actual degree bound `R`. -/
lemma polynomialLift_variance_degree {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p R : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n)
    (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ j ω, ‖X j ω‖ ≤ M)
    (m : Fin p → ℝ) (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = m i) :
    variance (RoughRegime.Upper.polynomialLift F X) μ =
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * (n.descFactorial (r.val + 1) : ℝ))⁻¹ *
        ∫ ω,
          (iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m
            (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hRn) i) ω - m)) ^ 2 ∂μ := by
  rw [← covariance_self (polynomialLift_integrable μ F X hm M hM hb).aestronglyMeasurable.aemeasurable]
  rw [RoughRegime.LiftTranslation.polynomialLift_eq_centeredDerivativeLift F X m hdeg hRn]
  have hcoord (j : Fin n) (ω : Ω) (i : Fin p) : |X j ω i| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (X j ω) i).trans (hb j ω)
  obtain ⟨hYind, hYmeas, hYid, hYbound, hYmean⟩ :=
    RoughRegime.UpperCovariance.centerObservations_properties μ X m hi hm hid M hM hcoord hmean
  simpa only [← pow_two] using
    RoughRegime.UpperCovariance.covariance_centeredDerivativeLift μ F F m
      (fun j ω => X j ω - m) hRn hYind hYmeas hYid (M + ‖m‖)
      (add_nonneg hM (norm_nonneg m)) hYbound hYmean

lemma order_sum_split (R : ℕ) (hR : 0 < R) (a : ℝ) (f : ℕ → ℝ) :
    (∑ r : Fin R, if r.val = 0 then a else f (r.val + 1)) =
      a + ∑ j ∈ Finset.range (R - 1), f (j + 2) := by
  cases R with
  | zero => omega
  | succ R =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.add_one_ne_zero,
      Nat.succ_sub_one]
    simp only [Nat.add_assoc]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j => f (j + 2)) R

/-- Lemma 8 for the paper's actual aggregate cell polynomial and unbiased lift.
`η` denotes `h^s₀`; the Euclidean-square bounds are exactly the squared `ℓ²`
observable and gradient hypotheses. Both displayed variance conclusions are proved. -/
theorem variance_polynomial_cell_lift {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n K p R : ℕ}
    (hK : 0 < K) (hR : 0 < R) (h2R : 2 * R ≤ n)
    (F : Fin K → MvPolynomial (Fin p) ℝ) (hdeg : ∀ c, (F c).totalDegree ≤ R)
    (X : Fin n → Ω → Fin (K * p) → ℝ) (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (m : Fin (K * p) → ℝ) (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = m i)
    (cell : Fin n → Ω → Fin K) (hiCell : iIndepFun cell μ) (hmCell : ∀ j, Measurable (cell j))
    (C0 η : ℝ) (hC0 : 1 ≤ C0) (hη : 0 ≤ η)
    (hcomplex : ∀ c y, ‖y - (fun j => (RoughRegime.PolynomialCells.cellProjection c m j : ℂ))‖ < 1 / C0 →
      ‖MvPolynomial.eval y (RoughRegime.ComplexDerivativeBridge.complexify (F c))‖ ≤ C0)
    (hgrad : ∀ c, euclideanSquare (fun j => fderiv ℝ (fun y => MvPolynomial.eval y (F c))
      (RoughRegime.PolynomialCells.cellProjection c m) (Pi.single j 1)) ≤ (C0 * η) ^ 2)
    (hZ : ∀ i ω c, euclideanSquare (RoughRegime.PolynomialCells.cellProjection c (X i ω)) ≤
      (C0 * K) ^ 2 * cellIndicator (cell i) c ω)
    (hprob : ∀ i c, μ.real {ω | cell i ω = c} ≤ C0 / K) :
    variance (RoughRegime.Upper.polynomialLift (RoughRegime.PolynomialCells.cellMomentPolynomial F) X) μ ≤
        varianceConstant C0 * η ^ 2 / n +
          ∑ j ∈ Finset.range (R - 1), varianceTerm (varianceConstant C0) K n (j + 2) ∧
      (varianceConstant C0 * R * K / n ≤ 1 / 2 →
        variance (RoughRegime.Upper.polynomialLift (RoughRegime.PolynomialCells.cellMomentPolynomial F) X) μ ≤
          varianceConstant C0 * η ^ 2 / n + 4 * varianceConstant C0 ^ 2 * K / (n : ℝ) ^ 2) := by
  classical
  let T := RoughRegime.PolynomialCells.cellMomentPolynomial F
  let B : ℝ := C0 * K
  let V : ℝ := Real.exp 1 ^ 2 * C0 ^ 7
  have hC0n : 0 ≤ C0 := le_trans zero_le_one hC0
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast hK
  have hnpos : 0 < (n : ℝ) := by
    have hn : 0 < n := by omega
    exact_mod_cast hn
  have hB : 0 ≤ B := mul_nonneg hC0n hKpos.le
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hCv : 0 ≤ varianceConstant C0 := by unfold varianceConstant; positivity
  have hRn : R ≤ n := by omega
  have hTdeg : T.totalDegree ≤ R := RoughRegime.PolynomialCells.cellMomentPolynomial_degree F hdeg
  have hX (j : Fin n) (ω : Ω) : ‖X j ω‖ ≤ B :=
    full_observable_bound (X j ω) (cell j ω) B hB (hZ j ω)
  have hvectorMean (j : Fin n) : (∫ ω, X j ω ∂μ) = m :=
    population_vector_mean μ (X j) (hm j) B (hX j) m (hmean j)
  let E (r : Fin R) : Fin (r.val + 1) ↪ Fin n := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hRn)
  let H (r : Fin R) := iteratedFDeriv ℝ (r.val + 1) (fun y => MvPolynomial.eval y T) m
  let a (r : Fin R) : ℝ := (((r.val + 1).factorial : ℝ) * (n.descFactorial (r.val + 1) : ℝ))⁻¹
  let I (r : Fin R) : ℝ := ∫ ω, H r (fun i => X (E r i) ω - m) ^ 2 ∂μ
  let J (r : Fin R) : ℝ := ∫ ω, H r (fun i => X (E r i) ω) ^ 2 ∂μ
  have hvariance : variance (RoughRegime.Upper.polynomialLift T X) μ = ∑ r : Fin R, a r * I r :=
    polynomialLift_variance_degree μ T X hTdeg hRn hi hm hid B hB hX m hmean
  have ha (r : Fin R) : 0 ≤ a r := by dsimp [a]; positivity
  have hint (r : Fin R) : Integrable (fun ω => H r (fun i => X (E r i) ω) ^ 2) μ :=
    kernel_square_integrable μ (H r) (fun i ω => X (E r i) ω) (fun i => hm (E r i)) B hB
      (fun i ω => hX (E r i) ω)
  have hcenter (r : Fin R) : I r ≤ J r :=
    RoughRegime.Centering.independent_centering_square_le μ (H r) (fun i ω => X (E r i) ω)
      (fun i => hm (E r i)) (hi.precomp (E r).injective)
      (fun i j => hid (E r i) (E r j)) B hB (fun i ω => hX (E r i) ω) m
      (fun i => hvectorMean (E r i))
  have hfirst (r : Fin R) (hr0 : r.val = 0) : J r ≤ C0 ^ 4 * η ^ 2 := by
    have hrEq : r = ⟨0, hR⟩ := Fin.ext hr0
    subst r
    have hpoint (ω : Ω) : H ⟨0, hR⟩ (fun i => X (E ⟨0, hR⟩ i) ω) ^ 2 ≤ C0 ^ 4 * η ^ 2 := by
      change (iteratedFDeriv ℝ 1 (fun y => MvPolynomial.eval y T) m
        (fun i => X (E ⟨0, hR⟩ i) ω)) ^ 2 ≤ _
      rw [iteratedFDeriv_one_apply]
      exact polynomial_cell_first_kernel_bound hK F m (X (E ⟨0, hR⟩ 0) ω)
        (cell (E ⟨0, hR⟩ 0) ω) C0 η hC0n hη hgrad (hZ (E ⟨0, hR⟩ 0) ω)
    have hbnd := integral_mono (hint ⟨0, hR⟩) (integrable_const (C0 ^ 4 * η ^ 2)) hpoint
    simpa only [integral_const, probReal_univ, one_smul] using hbnd
  have hhigh (r : Fin R) : J r ≤
      ((r.val + 1).factorial : ℝ) ^ 2 * V ^ (r.val + 1) * (K : ℝ) ^ r.val := by
    exact polynomial_cell_raw_higher_moment_bound μ hK (Nat.succ_pos _) F m X hm cell hiCell hmCell
      (E r) C0 hC0 hcomplex hZ hprob
  have hterm (r : Fin R) : a r * I r ≤ if r.val = 0 then
      varianceConstant C0 * η ^ 2 / n else varianceTerm (varianceConstant C0) K n (r.val + 1) := by
    by_cases hr0 : r.val = 0
    · rw [ite_eq_left hr0]
      calc
        _ ≤ a r * J r := mul_le_mul_of_nonneg_left (hcenter r) (ha r)
        _ ≤ a r * (C0 ^ 4 * η ^ 2) := mul_le_mul_of_nonneg_left (hfirst r hr0) (ha r)
        _ ≤ _ := by
          simp only [a, hr0, Nat.zero_add, Nat.factorial_one, Nat.descFactorial_one,
            Nat.cast_one, one_mul]
          calc
            (n : ℝ)⁻¹ * (C0 ^ 4 * η ^ 2) ≤ (n : ℝ)⁻¹ * (varianceConstant C0 * η ^ 2) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (first_order_constant_le_varianceConstant C0 hC0) (sq_nonneg η))
                (inv_nonneg.mpr hnpos.le)
            _ = _ := by rw [div_eq_mul_inv]; ring
    · rw [ite_eq_right hr0]
      calc
        _ ≤ a r * J r := mul_le_mul_of_nonneg_left (hcenter r) (ha r)
        _ ≤ a r * (((r.val + 1).factorial : ℝ) ^ 2 * V ^ (r.val + 1) * (K : ℝ) ^ r.val) :=
          mul_le_mul_of_nonneg_left (hhigh r) (ha r)
        _ ≤ _ := by
          have h := sparse_variance_term_bound n (r.val + 1) V K (Nat.succ_le_succ (Nat.zero_le _))
            ((Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt r.isLt)).trans h2R) hV hKpos.le
          simpa only [V, a, varianceConstant, mul_assoc, Nat.add_sub_cancel] using h
  have hstrong : variance (RoughRegime.Upper.polynomialLift T X) μ ≤
      varianceConstant C0 * η ^ 2 / n +
        ∑ j ∈ Finset.range (R - 1), varianceTerm (varianceConstant C0) K n (j + 2) := by
    rw [hvariance]
    calc
      _ ≤ ∑ r : Fin R, if r.val = 0 then varianceConstant C0 * η ^ 2 / n
          else varianceTerm (varianceConstant C0) K n (r.val + 1) :=
        Finset.sum_le_sum (fun r _ => hterm r)
      _ = _ := order_sum_split R hR _ _
  refine ⟨hstrong, fun hsmall => ?_⟩
  exact hstrong.trans (add_le_add le_rfl
    (variance_tail_small_resolution (varianceConstant C0) K n R hCv hKpos.le hnpos hsmall))

/-- `euclideanSquare` is the square of the actual Euclidean norm. -/
lemma euclideanSquare_eq_norm_sq {p : ℕ} (x : Fin p → ℝ) :
    euclideanSquare x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin p))‖ ^ 2 := by
  symm
  exact EuclideanSpace.real_norm_sq_eq _

lemma rpow_square (h s : ℝ) (hh : 0 ≤ h) : (h ^ s) ^ 2 = h ^ (2 * s) := by
  rw [mul_comm 2 s, Real.rpow_mul hh]
  exact (Real.rpow_natCast (h ^ s) 2).symm

/-- Lemma 8 in the paper's `ℓ²` and `h^(2s₀)` notation, for the actual lift
of the aggregate polynomial in all cell moments. -/
theorem variance_polynomial_cell_lift_paper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n K p R : ℕ}
    (hK : 0 < K) (hR : 0 < R) (h2R : 2 * R ≤ n)
    (F : Fin K → MvPolynomial (Fin p) ℝ) (hdeg : ∀ c, (F c).totalDegree ≤ R)
    (X : Fin n → Ω → Fin (K * p) → ℝ) (hi : iIndepFun X μ) (hm : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (m : Fin (K * p) → ℝ) (hmean : ∀ j i, ∫ ω, X j ω i ∂μ = m i)
    (cell : Fin n → Ω → Fin K) (hiCell : iIndepFun cell μ) (hmCell : ∀ j, Measurable (cell j))
    (C0 h s0 : ℝ) (hC0 : 1 ≤ C0) (hh : 0 < h) (_hh1 : h ≤ 1) (_hs0 : 0 < s0)
    (hcomplex : ∀ c y, ‖y - (fun j => (RoughRegime.PolynomialCells.cellProjection c m j : ℂ))‖ < 1 / C0 →
      ‖MvPolynomial.eval y (RoughRegime.ComplexDerivativeBridge.complexify (F c))‖ ≤ C0)
    (hgrad : ∀ c, ‖(WithLp.toLp 2 (fun j => fderiv ℝ (fun y => MvPolynomial.eval y (F c))
      (RoughRegime.PolynomialCells.cellProjection c m) (Pi.single j 1)) : EuclideanSpace ℝ (Fin p))‖
        ≤ C0 * h ^ s0)
    (hZ : ∀ i ω c, ‖(WithLp.toLp 2 (RoughRegime.PolynomialCells.cellProjection c (X i ω)) :
      EuclideanSpace ℝ (Fin p))‖ ≤ C0 * K * cellIndicator (cell i) c ω)
    (hprob : ∀ i c, μ.real {ω | cell i ω = c} ≤ C0 / K) :
    variance (RoughRegime.Upper.polynomialLift (RoughRegime.PolynomialCells.cellMomentPolynomial F) X) μ ≤
        varianceConstant C0 * h ^ (2 * s0) / n +
          (1 / (n : ℝ)) * ∑ j ∈ Finset.range (R - 1),
            varianceConstant C0 ^ (j + 2) * ((j + 2).factorial : ℝ) * (K / (n : ℝ)) ^ (j + 1) ∧
      (varianceConstant C0 * R * K / n ≤ 1 / 2 →
        variance (RoughRegime.Upper.polynomialLift (RoughRegime.PolynomialCells.cellMomentPolynomial F) X) μ ≤
          varianceConstant C0 * h ^ (2 * s0) / n + 4 * varianceConstant C0 ^ 2 * K / (n : ℝ) ^ 2) := by
  have hg (c : Fin K) : euclideanSquare (fun j => fderiv ℝ (fun y => MvPolynomial.eval y (F c))
      (RoughRegime.PolynomialCells.cellProjection c m) (Pi.single j 1)) ≤ (C0 * h ^ s0) ^ 2 := by
    rw [euclideanSquare_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hgrad c) 2
  have hz (i : Fin n) (ω : Ω) (c : Fin K) :
      euclideanSquare (RoughRegime.PolynomialCells.cellProjection c (X i ω)) ≤
        (C0 * K) ^ 2 * cellIndicator (cell i) c ω := by
    rw [euclideanSquare_eq_norm_sq]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hZ i ω c) 2
    have hind : cellIndicator (cell i) c ω ^ 2 = cellIndicator (cell i) c ω := by
      unfold cellIndicator
      split_ifs <;> norm_num
    simpa only [mul_pow, hind] using hsq
  have ht := variance_polynomial_cell_lift μ hK hR h2R F hdeg X hi hm hid m hmean
    cell hiCell hmCell C0 (h ^ s0) hC0 (Real.rpow_nonneg hh.le s0) hcomplex hg hz hprob
  rw [rpow_square h s0 hh.le] at ht
  have hsum : (∑ j ∈ Finset.range (R - 1), varianceTerm (varianceConstant C0) K n (j + 2)) =
      (1 / (n : ℝ)) * ∑ j ∈ Finset.range (R - 1),
        varianceConstant C0 ^ (j + 2) * ((j + 2).factorial : ℝ) * (K / (n : ℝ)) ^ (j + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [varianceTerm]
    have hjn : j + 2 - 1 = j + 1 := by omega
    rw [hjn]
    ring
  simpa only [hsum] using ht

end RoughRegime.LiftVariance
