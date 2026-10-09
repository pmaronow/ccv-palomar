module

public import NearlyMinimax.Model


@[expose] public section

/-! A harmless fixed envelope permits both scalar evaluations 0 and 1
when representing the response slope by an exact polynomial difference. -/
noncomputable section
open MeasureTheory
namespace NearlyMinimax

def pilotModelConstants {d : ℕ} (C : ModelConstants d) : ModelConstants d :=
  { C with
    holderBound := max C.holderBound 1
    holderBound_pos := C.holderBound_pos.trans_le (le_max_left _ _) }

theorem admissible_pilotModelConstants {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    Admissible (pilotModelConstants C) θ := by
  obtain ⟨hpd, hpf, hpb, hpone, ⟨F, hFeq, hFdiff, hFnorm⟩, hVlo, hVhi, herr⟩ := hθ
  refine ⟨hpd, hpf, hpb, hpone, ⟨F, hFeq, hFdiff, ?_⟩, hVlo, hVhi, herr⟩
  exact hFnorm.trans (ENNReal.ofReal_mono (le_max_left _ _))

theorem pilotModelConstants_zero_response_bound {d : ℕ} (C : ModelConstants d) :
    |(0 : ℝ)| ≤ (pilotModelConstants C).holderBound := by
  simpa only [abs_zero] using (pilotModelConstants C).holderBound_pos.le

theorem pilotModelConstants_one_response_bound {d : ℕ} (C : ModelConstants d) :
    |(1 : ℝ)| ≤ (pilotModelConstants C).holderBound := by
  simpa [pilotModelConstants] using le_max_right C.holderBound (1 : ℝ)

end NearlyMinimax
