module

public import NearlyMinimax.HighHistoryMassConcentration
public import NearlyMinimax.LowerSaddle


@[expose] public section

/-! The actual history mass coefficient and the paper's rounded lower saddle.
These are numerical identities and eventual guards; the probability tail is
proved independently for the actual constructed prior. -/
noncomputable section
open Filter
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The actual fixed geometric mass-MGF constant. -/
def highHistoryMassMomentConstant (d : ℕ) (a b : ℝ) : ℝ :=
  (2 : ℝ)^(2*d) * (b-a)^2 / 8

theorem highHistoryMassMomentConstant_pos (d : ℕ) (a b : ℝ) (hab : a < b) :
    0 < highHistoryMassMomentConstant d a b := by
  unfold highHistoryMassMomentConstant
  positivity

theorem highHistoryMassParameter_eq_hpower (d k : ℕ) (a b : ℝ) (hk : 0 < k) :
    highHistoryMassParameter d k a b = highHistoryMassMomentConstant d a b * ((k : ℝ)⁻¹)^d := by
  rw [highHistoryMassParameter_eq d k a b hk]
  unfold highHistoryMassMomentConstant
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

theorem highHistoryMassParameter_lowerSaddle (d : ℕ) (m θ C a b x : ℝ) :
    highHistoryMassParameter d (lowerSaddleGrid d m θ C x) a b =
      highHistoryMassMomentConstant d a b * (lowerSaddleH d m θ C x)^(d : ℝ) := by
  rw [highHistoryMassParameter_eq_hpower d _ a b
    (by exact_mod_cast lowerSaddleGrid_positive (d : ℝ) m θ C x)]
  simp only [lowerSaddleH, Real.rpow_natCast]

/-- Actual rounded saddle parameters satisfy the true mass-tail epsilon guard eventually. -/
theorem eventually_highHistoryMass_saddle_guard {d : ℕ} (hd : 0 < d)
    {m θ cm : ℝ} (hm : 0 < m) (hθ : 0 < θ) (hcm : 0 < cm) (C a b : ℝ) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, 2 ≤ lowerSaddleGrid d m θ C x ∧
      8 * highHistoryMassParameter d (lowerSaddleGrid d m θ C x) a b * x ≤ cm / lowerSaddleM m x := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hCmgf := highHistoryMassMomentConstant_pos d a b hab
  filter_upwards [eventually_lowerSaddle_grid_and_mass hdR hm hθ hcm hCmgf C 2] with x hx
  refine ⟨hx.1, ?_⟩
  rw [highHistoryMassParameter_lowerSaddle]
  unfold lowerSaddleMu at hx
  nlinarith only [hx.2]

/-- The genuine tilted-tail numerical expression equals the source saddle tail envelope. -/
theorem highHistoryMass_saddle_tail_eq (d : ℕ) (m θ C cm a b x : ℝ) :
    2 * Real.exp (-(cm / (lowerSaddleM m x : ℝ))^2 /
      (8 * highHistoryMassParameter d (lowerSaddleGrid d m θ C x) a b)) =
      lowerSaddleExceptionalTail d m θ C (cm^2 / (8 * highHistoryMassMomentConstant d a b)) x := by
  rw [highHistoryMassParameter_lowerSaddle]
  unfold lowerSaddleExceptionalTail
  congr 1
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The source mass-tail envelope with the actual geometric constant is negligible compared with every displayed rate. -/
theorem highHistoryMass_saddle_tail_over_rate_tends_zero {d : ℕ} (hd : 0 < d)
    {m θ cm : ℝ} (hm : 0 < m) (hθ : 0 < θ) (hcm : 0 < cm)
    (C a b lam κ p : ℝ) (hab : a < b) :
    Tendsto (fun x : ℝ => (2 * Real.exp (-(cm / (lowerSaddleM m x : ℝ))^2 /
      (8 * highHistoryMassParameter d (lowerSaddleGrid d m θ C x) a b))) /
      (rateScale lam κ p x)^2) atTop (nhds 0) := by
  simp_rw [highHistoryMass_saddle_tail_eq]
  exact lowerSaddleExceptionalTail_over_rate_tends_zero (by exact_mod_cast hd) hm hθ
    (div_pos (sq_pos_of_pos hcm) (mul_pos (by norm_num) (highHistoryMassMomentConstant_pos d a b hab)))
    C lam κ p

end NearlyMinimax
