module

public import NearlyMinimax.CompactNuisanceNorm


@[expose] public section

/-! The exact finite nuisance ranges in the lower-bound chart norm. -/
noncomputable section
open Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 500000

abbrev LocalNuisance (ι : Type*) (n : ℕ) :=
  (Fin n → ℝ) × ((ι → ℝ) × ((Fin n → ℝ) × ℝ))

def localCoefficientBall (ι : Type*) [Fintype ι] (C : ℝ) : Set (ι → ℝ) :=
  {c | (∑ γ, |c γ|) ≤ C⁻¹}

def localNuisanceSet (ι : Type*) [Fintype ι] (n : ℕ) (ad bd C ρ v : ℝ) :
    Set (LocalNuisance ι n) :=
  {p | ∀ i, p i ∈ Icc ad bd} ×ˢ
    (localCoefficientBall ι C ×ˢ
      ({g | ∀ i, g i ∈ Icc (-ρ / 2) (ρ / 2)} ×ˢ Icc (v - ρ) v))

theorem localCoefficientBall_isCompact (ι : Type*) [Fintype ι] (C : ℝ) :
    IsCompact (localCoefficientBall ι C) := by
  have hclosed : IsClosed (localCoefficientBall ι C) :=
    isClosed_le (continuous_finsetSum _ (fun γ _ => (continuous_apply γ).abs)) continuous_const
  apply (isCompact_pi_infinite (fun _ : ι => (isCompact_Icc :
    IsCompact (Icc (-C⁻¹) C⁻¹)))).of_isClosed_subset hclosed
  intro c hc γ
  have hb : |c γ| ≤ C⁻¹ :=
    (Finset.single_le_sum (fun δ _ => abs_nonneg (c δ)) (Finset.mem_univ γ)).trans hc
  exact abs_le.mp hb

theorem localNuisanceSet_isCompact (ι : Type*) [Fintype ι] (n : ℕ)
    (ad bd C ρ v : ℝ) : IsCompact (localNuisanceSet ι n ad bd C ρ v) :=
  (isCompact_pi_infinite (fun _ : Fin n => (isCompact_Icc : IsCompact (Icc ad bd)))).prod
    ((localCoefficientBall_isCompact ι C).prod
      ((isCompact_pi_infinite (fun _ : Fin n => (isCompact_Icc :
        IsCompact (Icc (-ρ / 2) (ρ / 2))))).prod isCompact_Icc))

theorem localNuisanceSet_nonempty (ι : Type*) [Fintype ι] (n : ℕ)
    {ad bd C ρ v : ℝ} (hab : ad ≤ bd) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) :
    (localNuisanceSet ι n ad bd C ρ v).Nonempty := by
  refine ⟨((fun _ => ad), ((fun _ => 0), ((fun _ => 0), v))), ?_⟩
  constructor
  · exact fun _ => ⟨le_rfl, hab⟩
  constructor
  · simp only [localCoefficientBall, mem_setOf_eq, abs_zero, Finset.sum_const_zero]
    exact inv_nonneg.mpr hC
  constructor
  · exact fun _ => ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, le_rfl⟩

theorem localNuisanceSet_guards (ι : Type*) [Fintype ι] (n : ℕ)
    (ad bd C ρ v : ℝ) (z : LocalNuisance ι n)
    (hz : z ∈ localNuisanceSet ι n ad bd C ρ v) :
    (∀ i, z.1 i ∈ Icc ad bd) ∧ (∑ γ, |z.2.1 γ|) ≤ C⁻¹ ∧
      (∀ i, |z.2.2.1 i| ≤ ρ/2) ∧ |z.2.2.2 - v| ≤ ρ := by
  refine ⟨hz.1, hz.2.1, ?_, ?_⟩
  · intro i
    exact abs_le.mpr ⟨by simpa only [neg_div] using (hz.2.2.1 i).1, (hz.2.2.1 i).2⟩
  · exact abs_le.mpr ⟨by linarith [hz.2.2.2.1],
      by linarith [hz.2.2.2.1, hz.2.2.2.2]⟩

end NearlyMinimax
