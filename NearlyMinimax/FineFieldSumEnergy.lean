module

public import NearlyMinimax.FineFieldSubsetL2


@[expose] public section

/-! Summation of actual time-integrated higher field moments over all
selected subsets, with a geometric count envelope. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

def fineFieldSubsetEnergyBase (d : ℕ) : ℝ :=
  4 * (2 : ℝ) ^ d * hyperplaneSpatialMomentConstant d ^ 2

theorem hyperplaneSpatialMomentConstant_ge_one (d : ℕ) :
    1 ≤ hyperplaneSpatialMomentConstant d := by
  unfold hyperplaneSpatialMomentConstant
  have hp : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hc := spatialExponentialConstant_nonneg d
  nlinarith only [hp, hc]

theorem finePairTimeSubsetMoment_uniform_square_integral_le {d k : ℕ} [NeZero d]
    (hd : 3 ≤ d) {lo hi : ℝ} (hlo : 0 < lo) (S : Finset (Fin k)) (hS : 4 ≤ S.card) :
    (∫ U : Fin k → Covariate d, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d k) ≤
      (2 : ℝ) ^ (d * k) * hyperplaneSpatialMomentConstant d ^ (2 * k) *
        (k : ℝ) ^ 8 * (lo ^ (2 - (d : ℝ))) ^ 2 := by
  have hc : S.card ≤ k := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ S)
  have hv : (2 : ℝ) ^ (d * (k - S.card)) ≤ (2 : ℝ) ^ (d * k) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left d (Nat.sub_le _ _))
  have hconst : hyperplaneSpatialMomentConstant d ^ (2 * S.card) ≤
      hyperplaneSpatialMomentConstant d ^ (2 * k) :=
    pow_le_pow_right₀ (hyperplaneSpatialMomentConstant_ge_one d) (Nat.mul_le_mul_left 2 hc)
  have hj : (S.card : ℝ) ^ 8 ≤ (k : ℝ) ^ 8 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hc) 8
  have h := finePairTimeSubsetMoment_square_integral_le hd (hi := hi) hlo S hS
  apply h.trans
  have hC := (hyperplaneSpatialMomentConstant_positive d).le
  have h2 := mul_le_mul hv hconst (pow_nonneg hC _) (by positivity)
  have h3 := mul_le_mul h2 hj (pow_nonneg (Nat.cast_nonneg S.card) 8)
    (mul_nonneg (by positivity) (pow_nonneg hC _))
  have hh := mul_le_mul_of_nonneg_right h3 (sq_nonneg (lo ^ (2 - (d : ℝ))))
  convert hh using 1 <;> simp only [mul_pow, ← pow_mul] <;> ring

/-- Any family of higher subsets has the same geometric count envelope;
the concrete even-subset field family is a particular case. -/
theorem finePairTimeSubsetMoment_sum_abs_square_integral_le {d k : ℕ} [NeZero d]
    (hd : 3 ≤ d) {lo hi : ℝ} (hlo : 0 < lo) (s : Finset (Finset (Fin k)))
    (hs : ∀ S ∈ s, 4 ≤ S.card) :
    (∫ U : Fin k → Covariate d, (∑ S ∈ s, |finePairTimeSubsetMoment lo hi U S|) ^ 2
      ∂fullSpatialPatchDesign d k) ≤
      fineFieldSubsetEnergyBase d ^ k * (k : ℝ) ^ 8 * (lo ^ (2 - (d : ℝ))) ^ 2 := by
  classical
  let K : ℝ := (2 : ℝ) ^ (d * k) * hyperplaneSpatialMomentConstant d ^ (2 * k) *
    (k : ℝ) ^ 8 * (lo ^ (2 - (d : ℝ))) ^ 2
  have hK : 0 ≤ K := by
    dsimp [K]
    have hC := (hyperplaneSpatialMomentConstant_positive d).le
    positivity
  have h := finite_sum_square_integral_le (fullSpatialPatchDesign d k) s
    (fun S U => |finePairTimeSubsetMoment lo hi U S|) K
    (fun S _ => (finePairTimeSubsetMoment_measurable lo hi S).abs)
    (fun S hS => by simpa only [sq_abs] using finePairTimeSubsetMoment_square_integrable hd hlo S (hs S hS))
    (fun S hS => by simpa only [sq_abs] using finePairTimeSubsetMoment_uniform_square_integral_le hd hlo S (hs S hS))
  have hcNat : s.card ≤ 2 ^ k := by
    have hsub : s ⊆ (Finset.univ : Finset (Fin k)).powerset := by intro S _; simp
    simpa only [Finset.card_powerset, Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsub
  have hc : (s.card : ℝ) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hcNat) 2
  have hh := mul_le_mul_of_nonneg_right hc hK
  apply (h.trans hh).trans_eq
  dsimp [K, fineFieldSubsetEnergyBase]
  simp only [mul_pow, pow_mul]
  have hfour : (4 : ℝ) ^ k = (2 : ℝ) ^ (k * 2) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
  rw [hfour]
  ring

end NearlyMinimax
