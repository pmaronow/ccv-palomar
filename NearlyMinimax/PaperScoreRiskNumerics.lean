module

public import NearlyMinimax.HighHistoryMassConcentration
public import NearlyMinimax.Clipping
public import NearlyMinimax.HighPathBudget
public import NearlyMinimax.HighPacketBalancing


@[expose] public section

/-! Exact numerical identifications in the paper's score-risk proposition:
the fixed mass radius, actual MGF parameter, mesh powers, exceptional tail
and replacement of the effective variance width by the original width.
None of these identities assumes Reg(K) or an asymptotic budget. -/
noncomputable section
open MeasureTheory
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def paperScoreMassNeighborhood {d : ℕ} (C : ModelConstants d) : ℝ :=
  1/(2*C.densityUpper)

def paperScoreMassMGFConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  (2 : ℝ)^(2*d)*(C.densityUpper-C.densityLower)^2/8

def paperScoreBadMass {d : ℕ} (C : ModelConstants d) (M : ℕ) (h : ℝ) : ℝ :=
  2*Real.exp (-(paperScoreMassNeighborhood C)^2/
    (8*paperScoreMassMGFConstant C*(M : ℝ)^2*h^d))

theorem paperScoreMassNeighborhood_pos {d : ℕ} (C : ModelConstants d) :
    0 < paperScoreMassNeighborhood C := by
  unfold paperScoreMassNeighborhood
  positivity [zero_lt_one.trans C.one_lt_densityUpper]

theorem paperScoreMassNeighborhood_le_inverse_upper {d : ℕ} (C : ModelConstants d) :
    paperScoreMassNeighborhood C ≤ 1/C.densityUpper := by
  have hb : 0 < C.densityUpper := zero_lt_one.trans C.one_lt_densityUpper
  unfold paperScoreMassNeighborhood
  apply (div_le_div_iff₀ (by positivity : 0 < 2*C.densityUpper) hb).mpr
  linarith

theorem paperScoreMassMGFConstant_pos {d : ℕ} (C : ModelConstants d) :
    0 < paperScoreMassMGFConstant C := by
  have hg : 0 < C.densityUpper-C.densityLower :=
    sub_pos.mpr (C.densityLower_lt_one.trans C.one_lt_densityUpper)
  unfold paperScoreMassMGFConstant
  positivity

theorem highHistoryMassParameter_eq_paper_mgf {d : ℕ} (C : ModelConstants d)
    (k : ℕ) (hk : 0 < k) :
    highHistoryMassParameter d k C.densityLower C.densityUpper =
      paperScoreMassMGFConstant C*(1/(k : ℝ))^d := by
  rw [highHistoryMassParameter_eq d k C.densityLower C.densityUpper hk]
  unfold paperScoreMassMGFConstant
  rw [div_pow]
  simp only [one_pow]
  ring

theorem paper_score_inverse_mesh_rpow (d k : ℕ) (hk : 0 < k) :
    (1/(k : ℝ))^(-(d : ℝ)) = (k : ℝ)^d := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Real.rpow_neg (by positivity : 0 ≤ 1/(k : ℝ)),Real.rpow_natCast,one_div,inv_pow,inv_inv]

theorem paper_score_grid_cardinality (d k : ℕ) (hk : 0 < k) :
    (k : ℝ)^d = (1/(k : ℝ))^(-(d : ℝ)) :=
  (paper_score_inverse_mesh_rpow d k hk).symm

theorem paper_score_mass_guard_iff {d : ℕ} (C : ModelConstants d)
    (k M n : ℕ) (hk : 0 < k) (mu : ℝ)
    (hmu : mu=(n : ℝ)*(1/(k : ℝ))^d) :
    8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n : ℝ) ≤
        paperScoreMassNeighborhood C/(M : ℝ) ↔
      paperScoreMassNeighborhood C/(M : ℝ) ≥ 8*paperScoreMassMGFConstant C*mu := by
  rw [highHistoryMassParameter_eq_paper_mgf C k hk,hmu]
  constructor <;> intro h <;> convert h using 1 <;> ring

theorem paper_score_mass_exponent_eq {d : ℕ} (C : ModelConstants d)
    (k M : ℕ) (hk : 0 < k) (hM : 0 < M) (cm : ℝ) :
    (cm/(M : ℝ))^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper) =
      cm^2/(8*paperScoreMassMGFConstant C*(M : ℝ)^2*(1/(k : ℝ))^d) := by
  have hmR : (0 : ℝ) < M := by exact_mod_cast hM
  rw [highHistoryMassParameter_eq_paper_mgf C k hk]
  rw [div_pow]
  field_simp

theorem paper_score_bad_mass_eq {d : ℕ} (C : ModelConstants d)
    (k M : ℕ) (hk : 0 < k) (hM : 0 < M) :
    2*Real.exp (-(paperScoreMassNeighborhood C/(M : ℝ))^2/
      (8*highHistoryMassParameter d k C.densityLower C.densityUpper)) =
      paperScoreBadMass C M (1/(k : ℝ)) := by
  unfold paperScoreBadMass
  congr 2
  rw [neg_div,paper_score_mass_exponent_eq C k M hk hM]
  ring

theorem paperScoreBadMass_nonneg {d : ℕ} (C : ModelConstants d) (M : ℕ) (h : ℝ) :
    0 ≤ paperScoreBadMass C M h := by unfold paperScoreBadMass; positivity

theorem paper_score_variance_width_square_le {d : ℕ} (C : ModelConstants d) :
    (effectiveVarianceUpper C-C.varianceLower)^2 ≤
      (C.varianceUpper-C.varianceLower)^2 := by
  have hlo : C.varianceLower ≤ effectiveVarianceUpper C :=
    (effective_variance_interval_nondegenerate C).le
  have hhi : effectiveVarianceUpper C ≤ C.varianceUpper := min_le_left _ _
  exact (sq_le_sq₀ (sub_nonneg.mpr hlo) (sub_nonneg.mpr C.variance_interval.le)).mpr
    (sub_le_sub_right hhi C.varianceLower)

theorem paper_score_original_width_loss_le {d : ℕ} (C : ModelConstants d)
    (lead eps : ℝ) (heps : 0 ≤ eps) :
    lead-(C.varianceUpper-C.varianceLower)^2*eps ≤
      lead-(effectiveVarianceUpper C-C.varianceLower)^2*eps :=
  sub_le_sub_left (mul_le_mul_of_nonneg_right (paper_score_variance_width_square_le C) heps) lead

theorem paper_score_original_width_risk_transfer {d : ℕ} (C : ModelConstants d)
    (n : ℕ) (lead eps : ℝ) (heps : 0 ≤ eps)
    (hbound : ENNReal.ofReal (lead-(effectiveVarianceUpper C-C.varianceLower)^2*eps) ≤ minimaxRisk C n) :
    ENNReal.ofReal (lead-(C.varianceUpper-C.varianceLower)^2*eps) ≤ minimaxRisk C n :=
  (ENNReal.ofReal_le_ofReal (paper_score_original_width_loss_le C lead eps heps)).trans hbound

/-- The exact integer threshold M₁' stated before the score-risk proposition. -/
def paperScoreResolutionThreshold {d : ℕ} (C : ModelConstants d) : ℕ :=
  max ⌈4/(C.densityUpper-C.densityLower)⌉₊
    (max ⌈2/(1-C.densityLower)⌉₊ ⌈2/(C.densityUpper-1)⌉₊)

/-- The paper's three ceiling guards imply the real centering threshold;
the formal construction does not require an enlarged resolution cutoff. -/
theorem paper_score_resolution_threshold_sufficient {d : ℕ} (C : ModelConstants d)
    (M : ℕ) (hM : paperScoreResolutionThreshold C ≤ M) :
    highCenterResolutionThreshold C ≤ (M : ℝ) := by
  have ha : 0 < 1-C.densityLower := sub_pos.mpr C.densityLower_lt_one
  have hb : 0 < C.densityUpper-1 := sub_pos.mpr C.one_lt_densityUpper
  have hceilA : ⌈2/(1-C.densityLower)⌉₊ ≤ M :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hceilB : ⌈2/(C.densityUpper-1)⌉₊ ≤ M :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hA : 2/(1-C.densityLower) ≤ (M : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceilA)
  have hB : 2/(C.densityUpper-1) ≤ (M : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceilB)
  have htwo : (2 : ℝ) ≤ M := by
    apply le_trans _ hA
    apply (le_div_iff₀ ha).mpr
    linarith [C.densityLower_pos]
  unfold highCenterResolutionThreshold
  apply max_le htwo
  rcases le_total (1-C.densityLower) (C.densityUpper-1) with hab | hba
  · have heq : (highCenterRadius C)⁻¹ = 2/(1-C.densityLower) := by
      unfold highCenterRadius
      rw [min_eq_left hab]
      field_simp
    simpa only [heq] using hA
  · have heq : (highCenterRadius C)⁻¹ = 2/(C.densityUpper-1) := by
      unfold highCenterRadius
      rw [min_eq_right hba]
      field_simp
    simpa only [heq] using hB

theorem paper_score_resolution_original_guards {d : ℕ} (C : ModelConstants d)
    (M : ℕ) (hM : paperScoreResolutionThreshold C ≤ M) :
    2 ≤ (M : ℝ) ∧ 1/(M : ℝ) ≤ highCenterRadius C :=
  highCenterResolution_guards C (M : ℝ)
    (paper_score_resolution_threshold_sufficient C M hM)

end NearlyMinimax
