module

public import NearlyMinimax.CellPolynomialProjection
public import NearlyMinimax.TernaryMeasure


@[expose] public section

/-! Concrete nonconstant centered monomials and their Lebesgue Gram matrix. -/

noncomputable section
open MeasureTheory Set Matrix MvPolynomial
open scoped BigOperators ENNReal

namespace NearlyMinimax

/-- Exactly the nonconstant monomials of total degree at most `ℓ`. -/
abbrev AnchoredIndex (d ℓ : ℕ) :=
  {γ : PolynomialBox d ℓ // 0 < ∑ i, (γ i).val ∧ (∑ i, (γ i).val) ≤ ℓ}

def anchoredDegree {d ℓ : ℕ} (γ : AnchoredIndex d ℓ) : ℕ := ∑ i, (γ.val i).val

def anchoredExponent {d ℓ : ℕ} (γ : AnchoredIndex d ℓ) : Fin d →₀ ℕ :=
  polynomialBoxExponent γ.val

@[simp] theorem anchoredExponent_apply {d ℓ : ℕ} (γ : AnchoredIndex d ℓ)
    (i : Fin d) : anchoredExponent γ i = (γ.val i).val :=
  polynomial_box_exponent_apply γ.val i

theorem anchoredExponent_injective {d ℓ : ℕ} :
    Function.Injective (anchoredExponent (d := d) (ℓ := ℓ)) := by
  intro γ δ h
  exact Subtype.ext (polynomial_box_exponent_injective h)

def anchoredMonomial {d ℓ : ℕ} (γ : AnchoredIndex d ℓ) (v : Covariate d) : ℝ :=
  ∏ i, (v i) ^ (γ.val i).val

def anchoredFeature {d ℓ : ℕ} (u w : Covariate d) (γ : AnchoredIndex d ℓ) : ℝ :=
  anchoredMonomial γ (w - u)

/-- The exact scale-`j` feature from the manuscript. -/
def dyadicAnchoredFeature {d ℓ : ℕ} (j : ℕ) (x z : Covariate d)
    (γ : AnchoredIndex d ℓ) : ℝ :=
  anchoredMonomial γ (fun i => (2 : ℝ) ^ j * (z i - x i))

theorem anchoredMonomial_scale {d ℓ : ℕ} (γ : AnchoredIndex d ℓ)
    (a : ℝ) (v : Covariate d) :
    anchoredMonomial γ (fun i => a * v i) = a ^ anchoredDegree γ * anchoredMonomial γ v := by
  unfold anchoredMonomial anchoredDegree
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

@[simp] theorem anchoredMonomial_zero {d ℓ : ℕ} (γ : AnchoredIndex d ℓ) :
    anchoredMonomial γ 0 = 0 := by
  have h := anchoredMonomial_scale γ 0 (fun _ => 1)
  have hd : anchoredDegree γ ≠ 0 := ne_of_gt γ.property.1
  change anchoredMonomial γ (fun _ => 0) = 0
  simpa only [zero_mul, zero_pow hd] using h

@[simp] theorem anchoredFeature_self {d ℓ : ℕ} (x : Covariate d)
    (γ : AnchoredIndex d ℓ) : anchoredFeature x x γ = 0 := by
  simp [anchoredFeature]

theorem dyadicAnchoredFeature_scale {d ℓ : ℕ} (j : ℕ) (x z : Covariate d)
    (γ : AnchoredIndex d ℓ) :
    dyadicAnchoredFeature (j + 1) x z γ =
      (2 : ℝ) ^ anchoredDegree γ * dyadicAnchoredFeature j x z γ := by
  unfold dyadicAnchoredFeature
  rw [show (fun i => (2 : ℝ) ^ (j + 1) * (z i - x i)) =
    (fun i => 2 * ((2 : ℝ) ^ j * (z i - x i))) by funext i; rw [pow_succ]; ring]
  exact anchoredMonomial_scale γ 2 _

/-- The fixed transport is diagonal, with precisely the paper's monomial factors. -/
def anchoredTransport (d ℓ : ℕ) : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  Matrix.diagonal (fun γ => (2 : ℝ) ^ (-(anchoredDegree γ : ℤ)))

theorem dyadicAnchoredFeature_transport {d ℓ : ℕ} (j : ℕ) (x z : Covariate d) :
    anchoredTransport d ℓ *ᵥ dyadicAnchoredFeature (j + 1) x z =
      dyadicAnchoredFeature j x z := by
  classical
  ext γ
  rw [anchoredTransport, mulVec_diagonal, dyadicAnchoredFeature_scale]
  rw [← zpow_natCast (2 : ℝ) (anchoredDegree γ), ← mul_assoc,
    _root_.zpow_neg_mul_zpow_self (anchoredDegree γ : ℤ) (by norm_num)]
  simp

theorem anchoredMonomial_continuous {d ℓ : ℕ} (γ : AnchoredIndex d ℓ) :
    Continuous (anchoredMonomial γ) := by
  unfold anchoredMonomial
  exact continuous_finset_prod Finset.univ (fun i _ => (continuous_apply i).pow _)

theorem anchoredFeature_continuous {d ℓ : ℕ} (γ : AnchoredIndex d ℓ) :
    Continuous (fun z : Covariate d × Covariate d => anchoredFeature z.1 z.2 γ) := by
  exact (anchoredMonomial_continuous γ).comp (continuous_snd.sub continuous_fst)

theorem anchoredMonomial_abs_le_one {d ℓ : ℕ} (γ : AnchoredIndex d ℓ)
    (v : Covariate d) (hv : ∀ i, |v i| ≤ 1) : |anchoredMonomial γ v| ≤ 1 := by
  unfold anchoredMonomial
  rw [Finset.abs_prod]
  simp only [abs_pow]
  exact (Finset.prod_le_prod₀ (fun i _ => pow_nonneg (abs_nonneg _) _)
    (fun i _ => (pow_le_pow_left₀ (abs_nonneg _) (hv i) _))).trans_eq
    (by simp)

theorem anchoredFeature_abs_le_one {d ℓ : ℕ} (u w : Covariate d)
    (hu : u ∈ unitCube d) (hw : w ∈ unitCube d) (γ : AnchoredIndex d ℓ) :
    |anchoredFeature u w γ| ≤ 1 := by
  apply anchoredMonomial_abs_le_one
  intro i
  change |w i - u i| ≤ 1
  rw [abs_le]
  constructor <;> linarith [(hu i).1, (hu i).2, (hw i).1, (hw i).2]

/-- Coefficients in the concrete nonconstant monomial index set. -/
def anchoredPolynomial {d ℓ : ℕ} (c : AnchoredIndex d ℓ → ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ γ, monomial (anchoredExponent γ) (c γ)

theorem anchoredPolynomial_coeff {d ℓ : ℕ} (c : AnchoredIndex d ℓ → ℝ)
    (γ : AnchoredIndex d ℓ) : (anchoredPolynomial c).coeff (anchoredExponent γ) = c γ := by
  classical
  simp only [anchoredPolynomial, coeff_sum, coeff_monomial]
  have heq : ∀ δ : AnchoredIndex d ℓ, anchoredExponent δ = anchoredExponent γ ↔ δ = γ :=
    fun δ => ⟨fun h => anchoredExponent_injective h, fun h => congrArg anchoredExponent h⟩
  simp only [heq]
  simp

theorem anchoredPolynomial_eval {d ℓ : ℕ} (c : AnchoredIndex d ℓ → ℝ)
    (v : Covariate d) :
    eval v (anchoredPolynomial c) = ∑ γ, c γ * anchoredMonomial γ v := by
  unfold anchoredPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [anchoredExponent_apply, anchoredMonomial]

theorem anchoredPolynomial_eq_zero_iff {d ℓ : ℕ} (c : AnchoredIndex d ℓ → ℝ) :
    anchoredPolynomial c = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext γ
    have := congrArg (fun P => P.coeff (anchoredExponent γ)) h
    simpa [anchoredPolynomial_coeff] using this
  · rintro rfl
    simp [anchoredPolynomial]

theorem unitCube_isCompact (d : ℕ) : IsCompact (unitCube d) := by
  rw [unitCube_eq_pi]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

/-- The actual known Lebesgue Gram, with no positivity hypothesis built into its definition. -/
def anchoredGram {d ℓ : ℕ} (u : Covariate d) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  fun γ δ => ∫ w, anchoredFeature u w γ * anchoredFeature u w δ ∂cubeVolume d

theorem anchoredFeature_product_integrable {d ℓ : ℕ} (u : Covariate d)
    (γ δ : AnchoredIndex d ℓ) :
    Integrable (fun w => anchoredFeature u w γ * anchoredFeature u w δ) (cubeVolume d) := by
  apply ContinuousOn.integrableOn_compact (unitCube_isCompact d)
  exact (((anchoredMonomial_continuous γ).comp (continuous_id.sub continuous_const)).mul
    ((anchoredMonomial_continuous δ).comp (continuous_id.sub continuous_const))).continuousOn

theorem anchoredGram_isHermitian {d ℓ : ℕ} (u : Covariate d) :
    (anchoredGram (ℓ := ℓ) u).IsHermitian := by
  ext γ δ
  simp only [conjTranspose_apply, star_trivial, anchoredGram]
  congr 1
  funext w
  exact mul_comm _ _

theorem anchoredGram_quadratic {d ℓ : ℕ} (u : Covariate d)
    (c : AnchoredIndex d ℓ → ℝ) :
    c ⬝ᵥ (anchoredGram u *ᵥ c) =
      ∫ w, (∑ γ, c γ * anchoredFeature u w γ) ^ 2 ∂cubeVolume d := by
  classical
  have heq : (fun w => (∑ γ, c γ * anchoredFeature u w γ) ^ 2) =
      (fun w => ∑ γ, ∑ δ, c γ *
        (anchoredFeature u w γ * anchoredFeature u w δ) * c δ) := by
    funext w
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro δ hδ
    ring
  rw [heq, integral_finset_sum]
  · simp only [dotProduct, mulVec, Finset.mul_sum, anchoredGram]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [integral_finset_sum]
    · simp_rw [integral_mul_const, integral_const_mul]
      apply Finset.sum_congr rfl
      intro δ hδ
      ring
    · intro δ hδ
      exact ((anchoredFeature_product_integrable u γ δ).const_mul (c γ)).mul_const (c δ)
  · intro γ hγ
    exact integrable_finset_sum _ (fun δ hδ =>
      ((anchoredFeature_product_integrable u γ δ).const_mul (c γ)).mul_const (c δ))

/-- A nonzero concrete centered polynomial has strictly positive squared
Lebesgue integral on the cube. Positivity is proved, rather than assumed. -/
theorem anchoredPolynomial_square_integral_pos {d ℓ : ℕ} (u : Covariate d)
    (c : AnchoredIndex d ℓ → ℝ) (hc : c ≠ 0) :
    0 < ∫ w, (∑ γ, c γ * anchoredFeature u w γ) ^ 2 ∂cubeVolume d := by
  classical
  let f : Covariate d → ℝ := fun w => ∑ γ, c γ * anchoredFeature u w γ
  have hf : Continuous f := by
    unfold f
    apply continuous_finset_sum
    intro γ hγ
    exact ((anchoredMonomial_continuous γ).comp
      (continuous_id.sub continuous_const)).const_mul (c γ)
  have hint : Integrable (fun w => f w ^ 2) (cubeVolume d) :=
    ContinuousOn.integrableOn_compact (unitCube_isCompact d) (hf.pow 2).continuousOn
  have hn : 0 ≤ ∫ w, f w ^ 2 ∂cubeVolume d := integral_nonneg (fun w => sq_nonneg (f w))
  change 0 < ∫ w, f w ^ 2 ∂cubeVolume d
  by_contra hnot
  have hz : (∫ w, f w ^ 2 ∂cubeVolume d) = 0 := le_antisymm (le_of_not_gt hnot) hn
  have hae : f =ᵐ[cubeVolume d] 0 :=
    ((integral_eq_zero_iff_of_nonneg (fun w => sq_nonneg (f w)) hint).mp hz).mono
      (fun w hw => (sq_eq_zero_iff.mp hw))
  let U : Set (Covariate d) := univ.pi (fun _ => Ioo (0 : ℝ) 1)
  have hU : IsOpen U := isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)
  have hsub : U ⊆ unitCube d := by
    intro w hw i
    exact ⟨(hw i (mem_univ i)).1.le, (hw i (mem_univ i)).2.le⟩
  have haU : f =ᵐ[volume.restrict U] 0 :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have heq := Measure.eqOn_open_of_ae_eq haU hU hf.continuousOn continuous_const.continuousOn
  have hpoly : anchoredPolynomial c = 0 := by
    apply MvPolynomial.funext_set (fun i : Fin d => Ioo (-u i) (1 - u i))
      (fun i => Ioo_infinite (by linarith))
    intro v hv
    have hvU : (fun i => v i + u i) ∈ U := by
      intro i hi
      have hi' := hv i (mem_univ i)
      constructor <;> linarith [hi'.1, hi'.2]
    have hfv := heq hvU
    have hs : (fun i => v i + u i) - u = v := by
      funext i
      simp only [Pi.sub_apply]
      ring
    simp only [Pi.zero_apply, f, anchoredFeature, hs] at hfv
    rw [anchoredPolynomial_eval]
    exact hfv
  exact hc ((anchoredPolynomial_eq_zero_iff c).mp hpoly)

/-- The known anchored Gram is positive definite for every anchor, including
all boundary anchors, since translation preserves monomial independence. -/
theorem anchoredGram_posDef {d ℓ : ℕ} (u : Covariate d) :
    (anchoredGram (ℓ := ℓ) u).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (anchoredGram_isHermitian u)
  intro c hc
  simp only [star_trivial]
  rw [anchoredGram_quadratic]
  exact anchoredPolynomial_square_integral_pos u c hc

end NearlyMinimax
