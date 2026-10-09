module

public import NearlyMinimax.PairPilotAssumptions
public import NearlyMinimax.TwoScalarPilotVector


@[expose] public section

/-! Construct the primitive common-pair assumptions from genuine scalar
pilot moment estimates; the covariance budget is derived rather than assumed. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000

theorem PairPilotAssumptions.mono_lam {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {θ : RegressionParameter d} {k : ℕ} {hk : 0 < k} {μ : Measure Ω}
    {bar : Covariate d × Covariate d → PairVector}
    {η : Ω → Covariate d × Covariate d → PairVector} {Cp W lam lam' : ℝ}
    (hp : PairPilotAssumptions θ k hk μ bar η Cp W lam) (hl : lam ≤ lam') :
    PairPilotAssumptions θ k hk μ bar η Cp W lam' := by
  refine { hp with lamNonnegative := hp.lamNonnegative.trans hl, linearTest := ?_ }
  intro v hv
  exact (hp.linearTest v hv).trans (mul_le_mul_of_nonneg_right hl
    (integral_nonneg (fun w => sq_nonneg ‖v w‖)))

theorem pairPilotAssumptions_of_two_scalars
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    (bar : Covariate d × Covariate d → PairVector)
    (a b : Ω → Covariate d × Covariate d → ℝ)
    {Cp W point test Λ : ℝ} (hCp : 0 ≤ Cp) (hW : 0 ≤ W)
    (htest : 0 ≤ test) (hΛ : 0 < Λ) (hpoint : 5 * point ≤ Cp)
    (hmbar : Measurable bar)
    (hma : Measurable (fun z : Ω × (Covariate d × Covariate d) => a z.1 z.2))
    (hmb : Measurable (fun z : Ω × (Covariate d × Covariate d) => b z.1 z.2))
    (hbar : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 → ‖bar w‖ ≤ Cp)
    (hsections : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 →
        MemLp (fun x => a x w) 2 μ ∧ MemLp (fun x => b x w) 2 μ)
    (henergy : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
      sameLabelKernel (regularGridCell k hk) w ≠ 0 →
        (∫ x, a x w ^ 2 ∂μ) ≤ point * W ∧ (∫ x, b x w ^ 2 ∂μ) ≤ point * W)
    (hcenter : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      (∫ x, a x w ∂μ) = 0 ∧ (∫ x, b x w ∂μ) = 0)
    (hinta : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) → ∀ x,
        Integrable (fun w => v w * a x w) (regularPairDesignMeasure θ k hk))
    (hintb : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) → ∀ x,
        Integrable (fun w => v w * b x w) (regularPairDesignMeasure θ k hk))
    (hLa : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
        MemLp (fun x => ∫ w, v w * a x w ∂regularPairDesignMeasure θ k hk) 2 μ)
    (hLb : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
        MemLp (fun x => ∫ w, v w * b x w ∂regularPairDesignMeasure θ k hk) 2 μ)
    (hEa : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
        (∫ x, (∫ w, v w * a x w ∂regularPairDesignMeasure θ k hk) ^ 2 ∂μ) ≤
          (test * W / Λ) * ∫ w, v w ^ 2 ∂regularPairDesignMeasure θ k hk)
    (hEb : ∀ v : (Covariate d × Covariate d) → ℝ,
      MemLp v 2 (regularPairDesignMeasure θ k hk) →
        (∫ x, (∫ w, v w * b x w ∂regularPairDesignMeasure θ k hk) ^ 2 ∂μ) ≤
          (test * W / Λ) * ∫ w, v w ^ 2 ∂regularPairDesignMeasure θ k hk) :
    PairPilotAssumptions θ k hk μ bar (fun x w => twoScalarPilotVector (a x w) (b x w))
      Cp W (6 * (test * W / Λ)) := by
  refine ⟨hCp, hW, hmbar, twoScalarPilotVector_measurable hma hmb, hbar, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hsections] with w hw hs
    exact twoScalarPilotVector_memLp (hw hs).1 (hw hs).2
  · filter_upwards [hsections, henergy] with w hw he hs
    exact (twoScalarPilotVector_second_le (hw hs).1 (hw hs).2 (he hs).1 (he hs).2).trans
      (by have hm := mul_le_mul_of_nonneg_right hpoint hW; nlinarith only [hm])
  · have hM := regularPairDesignMeasure_ae_of_supported θ k hk hsections
    filter_upwards [hM, hcenter] with w hw hc
    exact twoScalarPilotVector_mean_zero hw.1 hw.2 hc.1 hc.2
  · positivity
  · intro v hv
    exact twoScalarPilotVector_test_second_le μ (regularPairDesignMeasure θ k hk) a b
      (div_nonneg (mul_nonneg htest hW) hΛ.le) hinta hintb hLa hLb hEa hEb v hv

theorem scalarPilot_covariance_sample_budget {Cp W test Λ n : ℝ}
    (hn : 0 < n) (hW : 0 ≤ W) (htest : 0 ≤ test) (hΛ : n / 12 ≤ Λ)
    (hCp : 72 * test ≤ Cp ^ 2) :
    6 * (test * W / Λ) ≤ Cp ^ 2 * W / n := by
  have hΛ0 : 0 < Λ := (div_pos hn (by norm_num)).trans_le hΛ
  have hm := mul_le_mul_of_nonneg_right hCp hW
  have hden := mul_le_mul_of_nonneg_left hΛ (mul_nonneg (sq_nonneg Cp) hW)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hΛ0 hn).mpr
  have hmn := mul_le_mul_of_nonneg_right hm hn.le
  nlinarith only [hmn, hden]

end NearlyMinimax
