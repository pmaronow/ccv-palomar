module

public import NearlyMinimax.LowerSaddle
public import NearlyMinimax.RawCostAlgebra


@[expose] public section

/-! The exact raw-energy expression at the actual lower saddle gives the
squared target risk scale. This module is purely numerical: no minimax or
desired-rate premise occurs in its raw-energy input. -/
noncomputable section
open Filter
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The three actual primitive local-score energy contributions. -/
def lowerSaddleRawEnergyBound (s d m θ C cf C5 C6 C7 ch Bl : ℝ)
    (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  let η := lowerSaddleEta s d m θ C cf x
  let μ := lowerSaddleMu d m θ C x
  let N := lowerSaddleN s d m θ C τM x
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  3*(C5+C7)*η^4*μ^2*N^(-d) +
    3*C6*η^4*(Real.exp (2*τM M*M)*N^(4-d))*(C6*μ)^(M+1)/(M+1).factorial +
    Real.exp ch*η^4*(Bl+1)^2*(ch*μ)^(D+1)/(D+1).factorial

/-- Exact inverse-volume bookkeeping converts the genuine primitive
energy bound to the source's explicit seven-constant cost expression. -/
theorem lowerSaddle_raw_energy_cost {s d m θ C cf CB C5 C6 C7 ch x Bl E : ℝ}
    (τM : ℕ → ℝ) (hx : 0 ≤ x) (hcf : 0 ≤ cf) (hCB : 0 ≤ CB)
    (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6) (hC7 : 0 ≤ C7) (hch : 0 ≤ ch)
    (hB : 1 ≤ lowerSaddleActivity s d m θ C τM x) (hBl : 0 ≤ Bl)
    (hcost : Bl ≤ CB*lowerSaddleActivity s d m θ C τM x)
    (hE : E ≤ lowerSaddleRawEnergyBound s d m θ C cf C5 C6 C7 ch Bl τM x) :
    let CG := rawCostConstant CB C5 C6 C7 cf ch
    1+Bl^2+(lowerSaddleH d m θ C x)^(-d)*E ≤
      CG*((lowerSaddleActivity s d m θ C τM x)^2+
        lowerSaddleEnergyOne s d m θ C τM x+
        lowerSaddleEnergyTwo s d m θ C CG τM x+
        lowerSaddleEnergyThree s d m θ C CG τM x) := by
  let h := lowerSaddleH d m θ C x
  have hh : 0 < h := lowerSaddleH_positive _ _ _ _ _
  have he : (lowerSaddleEta s d m θ C cf x)^4 = cf^4*h^(4*s) := by
    unfold lowerSaddleEta
    rw [mul_pow, ← Real.rpow_mul_natCast hh.le]
    congr 1
    congr 1
    ring
  have hp : h^d*h^(4*s) = h^(d+4*s) := (Real.rpow_add hh _ _).symm
  have hr := raw_energy_cost_bound (n := x) (v := h^d)
    (mu := lowerSaddleMu d m θ C x) (eta4 := (lowerSaddleEta s d m θ C cf x)^4)
    (h4s := h^(4*s)) (B := lowerSaddleActivity s d m θ C τM x) (Bl := Bl) (E := E)
    (Fdef := (lowerSaddleN s d m θ C τM x)^(-d))
    (Fal := Real.exp (2*τM (lowerSaddleM m x)*lowerSaddleM m x)*
      (lowerSaddleN s d m θ C τM x)^(4-d))
    (CB := CB) (C5 := C5) (C6 := C6) (C7 := C7) (cf := cf) (ch := ch)
    (Real.rpow_pos_of_pos hh _)
    (by rfl) hx (Real.rpow_nonneg hh.le _) he hB hBl hCB hC5 hC6 hC7 hcf hch
    (Real.rpow_nonneg (lowerSaddleN_positive _ _ _ _ _ _ _).le _)
    (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (lowerSaddleN_positive _ _ _ _ _ _ _).le _))
    hcost (lowerSaddleM m x) (lowerSaddleD d m x) hE
  dsimp only at hr ⊢
  rw [Real.rpow_neg hh.le] at ⊢
  have he1 : x^2*h^d*h^(4*s)*(lowerSaddleN s d m θ C τM x)^(-d) =
      lowerSaddleEnergyOne s d m θ C τM x := by
    unfold lowerSaddleEnergyOne
    change x^2*h^d*h^(4*s)*(lowerSaddleN s d m θ C τM x)^(-d) =
      x^2*h^(d+4*s)*(lowerSaddleN s d m θ C τM x)^(-d)
    rw [Real.rpow_add hh]
    ring
  rw [he1] at hr
  simpa only [lowerSaddleEnergyTwo, lowerSaddleEnergyThree, ← mul_assoc] using hr

/-- The actual shrunk-endpoint saddle supplies the cost bound eventually;
the only remaining variables are the genuine raw activity and energy. -/
theorem eventually_actual_lowerSaddle_raw_cost {s d a b cf CB C5 C6 C7 ch C : ℝ}
    (hs : 1 < s) (hd : 4*s < d) (ha : 0 < a) (hab : a < b)
    (hcf : 0 ≤ cf) (hCB : 0 ≤ CB) (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6)
    (hC7 : 0 ≤ C7) (hch : 0 ≤ ch)
    (hC : 1+Real.log (rawCostConstant CB C5 C6 C7 cf ch)+
      (d^2-16*s)/(d*(d+4))*lowerSaddleTheta s d (densityIntervalExponent a b)+
      2*d*densityIntervalExponent a b/(d+4) < C) :
    ∀ᶠ x : ℝ in atTop,
      let m := lowerSaddleCoefficient s d (densityIntervalExponent a b)
      let θ := lowerSaddleTheta s d (densityIntervalExponent a b)
      let τM := shrunkDensityExponent a b
      let B := lowerSaddleActivity s d m θ C τM x
      ∀ Bl E : ℝ, 1 ≤ B → 0 ≤ Bl → Bl ≤ CB*B →
        E ≤ lowerSaddleRawEnergyBound s d m θ C cf C5 C6 C7 ch Bl τM x →
      1+Bl^2+(lowerSaddleH d m θ C x)^(-d)*E ≤
        3*rawCostConstant CB C5 C6 C7 cf ch*B^2 := by
  have hCG : 0 < rawCostConstant CB C5 C6 C7 cf ch :=
    lt_of_lt_of_le zero_lt_one (rawCostConstant_ge_one _ _ _ _ _ _)
  filter_upwards [eventually_actual_lowerSaddle_numeric_cost hs hd ha hab hCG hC,
    eventually_ge_atTop (0:ℝ)] with x hx hx0
  dsimp only at hx ⊢
  intro Bl E hB hBl hcost hE
  exact (lowerSaddle_raw_energy_cost _ hx0 hcf hCB hC5 hC6 hC7 hch hB hBl hcost hE).trans hx

/-- A true cost denominator bound yields the square of the actual saddle
risk. This is algebra, without a statistical lower-bound premise. -/
theorem lowerSaddle_cost_risk_reduction {s d m θ C cf x den CG ctr : ℝ}
    (τM : ℕ → ℝ) (hden : 0 < den) (hCG : 0 < CG) (hctr : 0 ≤ ctr)
    (hcost : den ≤ 3*CG*(lowerSaddleActivity s d m θ C τM x)^2) :
    ctr/(3*CG)*(lowerSaddleRisk s d m θ C cf τM x)^2 ≤
      ctr*(lowerSaddleEta s d m θ C cf x)^4/den := by
  have hB := lowerSaddleActivity_positive s d m θ C τM x
  have hh := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ ctr*(lowerSaddleEta s d m θ C cf x)^4) hden hcost
  apply le_trans _ hh
  apply le_of_eq
  unfold lowerSaddleRisk
  field_simp

end NearlyMinimax
