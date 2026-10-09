module

public import NearlyMinimax.AnchoredFeatures
public import NearlyMinimax.ModelRegularity


@[expose] public section

/-! Quantitative geometry of the exact nonconstant monomial feature vector. -/

noncomputable section
open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

/-- Each coordinate is bounded by the manuscript's Euclidean norm. -/
theorem abs_coordinate_le_euclideanNorm {d : ℕ} (v : Covariate d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  have hs : (v i) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  simpa only [Real.sqrt_sq_eq_abs, euclideanNorm] using Real.sqrt_le_sqrt hs

/-- Every nonconstant bounded monomial vanishes at least linearly at the origin. -/
theorem anchoredMonomial_abs_le_coordinate {d ℓ : ℕ} (γ : AnchoredIndex d ℓ)
    (v : Covariate d) (hv : ∀ i, |v i| ≤ 1) :
    ∃ i : Fin d, |anchoredMonomial γ v| ≤ |v i| := by
  classical
  obtain ⟨i, hi, hip⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (ne_of_gt γ.property.1 : (∑ i, (γ.val i).val) ≠ 0)
  have hpow : |v i| ^ (γ.val i).val ≤ |v i| := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hip
    rw [hk, pow_succ]
    have hle : |v i| ^ k ≤ 1 := by
      exact (pow_le_pow_left₀ (abs_nonneg _) (hv i) k).trans_eq (one_pow k)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hle (abs_nonneg (v i))
  have hrest : (∏ j ∈ (Finset.univ : Finset (Fin d)).erase i,
      |v j| ^ (γ.val j).val) ≤ 1 := by
    exact (Finset.prod_le_prod₀ (fun j _ => pow_nonneg (abs_nonneg _) _)
      (fun j _ => (pow_le_pow_left₀ (abs_nonneg _) (hv j) _))).trans_eq (by simp)
  refine ⟨i, ?_⟩
  unfold anchoredMonomial
  rw [Finset.abs_prod]
  simp only [abs_pow]
  rw [← Finset.prod_erase_mul _ _ hi]
  exact (mul_le_mul_of_nonneg_right hrest (pow_nonneg (abs_nonneg (v i)) _)).trans
    (by simpa only [one_mul] using hpow)

theorem anchoredMonomial_abs_le_euclideanNorm {d ℓ : ℕ} (γ : AnchoredIndex d ℓ)
    (v : Covariate d) (hv : ∀ i, |v i| ≤ 1) :
    |anchoredMonomial γ v| ≤ euclideanNorm v := by
  obtain ⟨i, hi⟩ := anchoredMonomial_abs_le_coordinate γ v hv
  exact hi.trans (abs_coordinate_le_euclideanNorm v i)

/-- The actual normalized features satisfy the Lipschitz-at-anchor bound. -/
theorem anchoredFeature_abs_le_euclideanNorm {d ℓ : ℕ} (u w : Covariate d)
    (hu : u ∈ unitCube d) (hw : w ∈ unitCube d) (γ : AnchoredIndex d ℓ) :
    |anchoredFeature u w γ| ≤ euclideanNorm (w - u) := by
  apply anchoredMonomial_abs_le_euclideanNorm
  intro i
  change |w i - u i| ≤ 1
  rw [abs_le]
  constructor <;> linarith [(hu i).1, (hu i).2, (hw i).1, (hw i).2]

/-- Euclidean energy of the full feature vector has the fixed finite dimension bound. -/
theorem anchoredFeature_energy_le {d ℓ : ℕ} (u w : Covariate d)
    (hu : u ∈ unitCube d) (hw : w ∈ unitCube d) :
    (∑ γ : AnchoredIndex d ℓ, (anchoredFeature u w γ) ^ 2) ≤
      Fintype.card (AnchoredIndex d ℓ) * (euclideanNorm (w - u)) ^ 2 := by
  calc
    _ ≤ ∑ _γ : AnchoredIndex d ℓ, (euclideanNorm (w - u)) ^ 2 := by
      apply Finset.sum_le_sum
      intro γ hγ
      have h := anchoredFeature_abs_le_euclideanNorm u w hu hw γ
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := by simp

/-- Every monomial transport factor is at most one half. -/
theorem anchoredTransport_entry_bound {d ℓ : ℕ} (γ : AnchoredIndex d ℓ) :
    |(2 : ℝ) ^ (-(anchoredDegree γ : ℤ))| ≤ 1 / 2 := by
  rw [_root_.zpow_neg, zpow_natCast, abs_inv, abs_pow,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpow : (2 : ℝ) ≤ 2 ^ anchoredDegree γ := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 ≤ anchoredDegree γ from γ.property.1)
  simpa only [one_div] using
    (inv_le_inv₀ (by norm_num : (0 : ℝ) < 2 ^ anchoredDegree γ) (by norm_num)).mpr hpow

/-- The exact diagonal transport obeys the manuscript's genuine operator-norm bound. -/
theorem anchoredTransport_norm_le_half (d ℓ : ℕ) :
    ‖anchoredTransport d ℓ‖ ≤ 1 / 2 := by
  classical
  rw [anchoredTransport, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
  intro γ
  exact anchoredTransport_entry_bound γ

end NearlyMinimax
