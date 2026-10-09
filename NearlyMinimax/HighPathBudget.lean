module

public import NearlyMinimax.ScoreCostAlgebra
public import NearlyMinimax.HistoryReferenceSum


@[expose] public section

/-! The fixed path constant and all positivity/variance budgets in the
local-cost lower-bound proposition. They precede every sample-size choice. -/
noncomputable section
namespace NearlyMinimax

def highPathConstant (Δ : ℕ) (rho eta0 : ℝ) : ℝ :=
  min 1 (min (historyReferenceRho Δ / (2 + 8 * (Δ : ℝ) ^ 2)) (rho / eta0 ^ 2))

theorem highPathConstant_pos (Δ : ℕ) {rho eta0 : ℝ} (hrho : 0 < rho)
    (heta0 : 0 < eta0) : 0 < highPathConstant Δ rho eta0 := by
  unfold highPathConstant
  exact lt_min (by norm_num) (lt_min
    (div_pos (historyReferenceRho_pos Δ) (by positivity)) (div_pos hrho (by positivity)))

theorem highPathConstant_le_one (Δ : ℕ) (rho eta0 : ℝ) :
    highPathConstant Δ rho eta0 ≤ 1 := min_le_left _ _

theorem localScorePathLength_le_constant {c B I : ℝ} (hc : 0 ≤ c)
    (hB : 0 ≤ B) (hI : 0 ≤ I) : localScorePathLength c B I ≤ c := by
  unfold localScorePathLength
  apply (div_le_iff₀ (by linarith only [hB, hI] : 0 < 1 + B + I)).mpr
  have h := mul_le_mul_of_nonneg_left (by linarith only [hB, hI] : 1 ≤ 1 + B + I) hc
  simpa only [mul_one] using h

theorem highPath_update_budget (Δ : ℕ) {rho eta0 B I : ℝ}
    (hrho : 0 < rho) (heta0 : 0 < eta0) (hB : 0 ≤ B) (hI : 0 ≤ I) :
    localScorePathLength (highPathConstant Δ rho eta0) B I * B / historyReferenceRho Δ ≤
      1 / (2 + 8 * (Δ : ℝ) ^ 2) := by
  have hc := highPathConstant_pos Δ hrho heta0
  have hb : localScorePathLength (highPathConstant Δ rho eta0) B I * B ≤
      highPathConstant Δ rho eta0 := by
    have h := localScorePathLength_energy_le hc.le hI hB
    simpa only [localScorePathLength, add_right_comm 1 I B] using h
  have hcb : highPathConstant Δ rho eta0 ≤
      historyReferenceRho Δ / (2 + 8 * (Δ : ℝ) ^ 2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  apply (div_le_iff₀ (historyReferenceRho_pos Δ)).mpr
  have h := hb.trans hcb
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

theorem highPath_variance_budget (Δ : ℕ) {rho eta0 B I eta : ℝ}
    (hrho : 0 < rho) (heta0 : 0 < eta0) (hB : 0 ≤ B) (hI : 0 ≤ I)
    (heta : 0 ≤ eta) (hetaU : eta ≤ eta0) :
    eta ^ 2 * localScorePathLength (highPathConstant Δ rho eta0) B I ≤ rho := by
  have hc := highPathConstant_pos Δ hrho heta0
  have hlen := localScorePathLength_le_constant hc.le hB hI
  have hlen0 := (localScorePathLength_pos hc hB hI).le
  have he2 : eta ^ 2 ≤ eta0 ^ 2 := (sq_le_sq₀ heta heta0.le).mpr hetaU
  have hcb : highPathConstant Δ rho eta0 ≤ rho / eta0 ^ 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hbudget := (le_div_iff₀ (by positivity : 0 < eta0 ^ 2)).mp hcb
  exact (mul_le_mul he2 hlen hlen0 (sq_nonneg _)).trans (by nlinarith only [hbudget])

theorem score_cost_scaled_numeric {c B I eta score K E : ℝ} (hc : 0 < c)
    (hB : 0 ≤ B) (hI : 0 ≤ I) (hscore0 : 0 ≤ score)
    (hscore : score ≤ localScorePathLength c B I * I)
    (hK : 1 ≤ K) (hE : 0 ≤ E) (hIE : I ^ 2 = K * E) :
    c ^ 2 / (3 * K * (2 + c) ^ 2) * eta ^ 4 / (1 + B ^ 2 + E) ≤
      eta ^ 4 * (localScorePathLength c B I) ^ 2 / (2 + score) ^ 2 := by
  have hden : 1 + B ^ 2 + I ^ 2 ≤ K * (1 + B ^ 2 + E) := by
    rw [hIE]
    have hm := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ 1 + B ^ 2)
    nlinarith only [hm]
  have hh := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ c ^ 2 / (3 * (2 + c) ^ 2) * eta ^ 4)
    (by positivity : 0 < 1 + B ^ 2 + I ^ 2) hden
  have hnumeric := score_cost_numeric (η := eta) hc hB hI hscore0 hscore
  apply le_trans _ hnumeric
  convert hh using 1 <;> field_simp <;> ring

end NearlyMinimax
