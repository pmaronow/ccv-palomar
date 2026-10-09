module

public import RoughRegime.Model


@[expose] public section

/-! Exact Hölder norms of constant functions, using the model's actual coordinate
derivatives. This discharges the smoothness requirement for constant local paths. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace RoughRegime.Model

theorem holderExponent_pos {t : ℝ} (ht : 0 < t) : 0 < holderExponent t := by
  have hc : 0 < Nat.ceil t := Nat.ceil_pos.mpr ht
  have hcast : ((Nat.ceil t - 1 : ℕ) : ℝ) = (Nat.ceil t : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  unfold holderExponent holderOrder
  rw [hcast]
  linarith [Nat.ceil_lt_add_one ht.le]

theorem holderExponent_le_one {t : ℝ} (ht : 0 < t) : holderExponent t ≤ 1 := by
  have hc : 0 < Nat.ceil t := Nat.ceil_pos.mpr ht
  have hcast : ((Nat.ceil t - 1 : ℕ) : ℝ) = (Nat.ceil t : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  unfold holderExponent holderOrder
  rw [hcast]
  linarith [Nat.le_ceil t]

@[simp] theorem coordinateDerivative_const_zero {d : ℕ} (c : ℝ)
    (σ : Fin 0 → Fin d) (x : Covariate d) :
    coordinateDerivative (fun _ : Covariate d ↦ c) 0 σ x = c := rfl

theorem coordinateDerivative_const_pos {d q : ℕ} (c : ℝ) (hq : q ≠ 0)
    (σ : Fin q → Fin d) (x : Covariate d) :
    coordinateDerivative (fun _ : Covariate d ↦ c) q σ x = 0 := by
  simp [coordinateDerivative, iteratedFDerivWithin_const_of_ne hq]

theorem coordinateDerivative_const_independent {d q : ℕ} (c : ℝ)
    (σ : Fin q → Fin d) (x y : Covariate d) :
    coordinateDerivative (fun _ : Covariate d ↦ c) q σ x =
      coordinateDerivative (fun _ : Covariate d ↦ c) q σ y := by
  cases q with
  | zero => rfl
  | succ q => simp [coordinateDerivative_const_pos c (Nat.succ_ne_zero q)]

theorem derivativeSup_const {d : ℕ} (c : ℝ) (k : ℕ) :
    derivativeSup (fun _ : Covariate d ↦ c) k = ENNReal.ofReal |c| := by
  apply le_antisymm
  · apply iSup_le
    intro q
    apply iSup_le
    intro _
    apply iSup_le
    intro σ
    apply iSup_le
    intro x
    apply iSup_le
    intro _
    by_cases hq : q = 0
    · subst q
      simp
    · simp [coordinateDerivative_const_pos c hq]
  · have hx : (0 : Covariate d) ∈ cube d := by
      intro j
      simp
    exact le_iSup_of_le 0 (le_iSup_of_le (Nat.zero_le k)
      (le_iSup_of_le Fin.elim0 (le_iSup_of_le 0 (le_iSup_of_le hx (by simp)))))

theorem holderSeminorm_const {d : ℕ} (c t : ℝ) :
    holderSeminorm (fun _ : Covariate d ↦ c) t = 0 := by
  apply le_antisymm
  · apply iSup_le
    intro σ
    apply iSup_le
    intro x
    apply iSup_le
    intro _
    apply iSup_le
    intro y
    apply iSup_le
    intro _
    apply iSup_le
    intro _
    rw [coordinateDerivative_const_independent c σ x y]
    simp
  · exact bot_le

theorem holderNorm_const {d : ℕ} (c : ℝ) {t : ℝ} (ht : 0 < t) :
    holderNorm (fun _ : Covariate d ↦ c) t = ENNReal.ofReal |c| := by
  simp [holderNorm, ht, contDiffOn_const, derivativeSup_const, holderSeminorm_const]

theorem const_mem_holderBall {d : ℕ} {c t H : ℝ} (ht : 0 < t)
    (hc : |c| ≤ H) : (fun _ : Covariate d ↦ c) ∈ holderBall t H := by
  change holderNorm _ t ≤ ENNReal.ofReal H
  rw [holderNorm_const c ht]
  exact ENNReal.ofReal_le_ofReal hc

theorem const_mem_holderBall_iff {d : ℕ} {c t H : ℝ} (ht : 0 < t) (hH : 0 ≤ H) :
    (fun _ : Covariate d ↦ c) ∈ holderBall t H ↔ |c| ≤ H := by
  change holderNorm _ t ≤ ENNReal.ofReal H ↔ _
  rw [holderNorm_const c ht]
  exact ENNReal.ofReal_le_ofReal_iff hH

end RoughRegime.Model
