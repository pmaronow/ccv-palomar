module

public import NearlyMinimax.HighObservationReal


@[expose] public section

/-! Borel decoding of the actual three response atoms. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def decodeTernaryResponse (a y : ℝ) : Fin 3 :=
  if y = -a then 0 else if y = 0 then 1 else 2

theorem decodeTernaryResponse_measurable (a : ℝ) : Measurable (decodeTernaryResponse a) := by
  apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const measurable_const

theorem decodeTernaryResponse_value (a : ℝ) (ha : 0 < a) (y : Fin 3) :
    decodeTernaryResponse a (ternaryValue a y) = y := by
  have hna : -a ≠ 0 := neg_ne_zero.mpr ha.ne'
  have han : a ≠ -a := by linarith
  fin_cases y <;> simp [decodeTernaryResponse, ternaryValue, hna, ha.ne', han]

def decodeDesignResponse {d n : ℕ} (a : ℝ) (z : Fin n → Observation d) :
    (Fin n → Covariate d) × (Fin n → Fin 3) :=
  (fun i => (z i).1, fun i => decodeTernaryResponse a (z i).2)

theorem decodeDesignResponse_measurable {d n : ℕ} (a : ℝ) :
    Measurable (decodeDesignResponse (d := d) (n := n) a) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    exact measurable_fst.comp (measurable_pi_apply i)
  · apply measurable_pi_lambda
    intro i
    exact (decodeTernaryResponse_measurable a).comp (measurable_snd.comp (measurable_pi_apply i))

theorem decodeDesignResponse_encode {d n : ℕ} (a : ℝ) (ha : 0 < a)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    decodeDesignResponse a (encodeDesignResponse a z) = z := by
  apply Prod.ext
  · rfl
  · funext i
    exact decodeTernaryResponse_value a ha (z.2 i)

end NearlyMinimax
