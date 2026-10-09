module

public import NearlyMinimax.DesignCounts
public import NearlyMinimax.HighObservationLaw
public import NearlyMinimax.HighWindowGeometry


@[expose] public section

/-! Actual binomial occupancy under the normalized original design law,
and the exact fixed denominator constant used in the high lower score
energy. Raw normalization and patch volume are derived. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
attribute [local instance] Classical.propDecidable

def highNormalizedDesignLaw {d : ℕ} (p : Covariate d → ℝ) : Measure (Covariate d) :=
  (cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity p x))

theorem high_normalized_design_probability {d : ℕ} (p : Covariate d → ℝ)
    (hp : Measurable p) (a b : ℝ) (ha : 0 < a)
    (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b) : IsProbabilityMeasure (highNormalizedDesignLaw p) :=
  normalizedDensityTernaryParameter_design_probability p hp a b ha hb

theorem high_normalized_design_dominated {d : ℕ} (p : Covariate d → ℝ) (B : ℝ)
    (hB : ∀ᵐ x ∂cubeVolume d, highNormalizedDensity p x ≤ B) :
    highNormalizedDesignLaw p ≤ ENNReal.ofReal B • cubeVolume d := by
  unfold highNormalizedDesignLaw
  rw [← withDensity_const]
  apply withDensity_mono
  exact hB.mono (fun x hx => ENNReal.ofReal_le_ofReal hx)

/-- Original raw interval and mass-good event imply the actual normalized
patch-design domination, rather than assuming a normalized density bound. -/
theorem high_good_mass_design_dominated {d : ℕ} (C : ModelConstants d) (M cm : ℝ)
    (hM : 2 ≤ M) (hcm : 0 ≤ cm) (hcmU : cm ≤ 1 / C.densityUpper)
    (p : Covariate d → ℝ)
    (hb : ∀ᵐ x ∂cubeVolume d, C.densityLower + 1 / M ≤ p x ∧ p x ≤ C.densityUpper - 1 / M)
    (hm : |highRawDensityMass p - 1| ≤ cm / M) :
    highNormalizedDesignLaw p ≤ ENNReal.ofReal C.densityUpper • cubeVolume d :=
  high_normalized_design_dominated p C.densityUpper
    ((highNormalizedDensity_bounds C M cm hM hcm hcmU p hb hm).mono fun x hx => hx.2)

/-- True torus patch occupancy under the actual original normalized design. -/
theorem high_normalized_torus_patch_probability_le {d k : ℕ} [NeZero k] (hk : 2 ≤ k)
    (p : Covariate d → ℝ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ x ∂cubeVolume d, highNormalizedDensity p x ≤ B) (j : HighWindowLabels d k) :
    (highNormalizedDesignLaw p).real (highTorusPatch d k j) ≤ B * (2 / (k : ℝ)) ^ d := by
  have h : (highNormalizedDesignLaw p) (highTorusPatch d k j) ≤
      ENNReal.ofReal B * ENNReal.ofReal (2 / (k : ℝ)) ^ d := by
    calc
      _ ≤ (ENNReal.ofReal B • cubeVolume d) (highTorusPatch d k j) :=
        Measure.le_iff.mp (high_normalized_design_dominated p B hB)
          (highTorusPatch d k j) (highTorusPatch_measurableSet d k j)
      _ = ENNReal.ofReal B * cubeVolume d (highTorusPatch d k j) := by rw [Measure.smul_apply, smul_eq_mul]
      _ ≤ _ := by
        gcongr
        exact highTorusPatch_volume_le d k hk j
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have htop : ENNReal.ofReal B * ENNReal.ofReal (2 / (k : ℝ)) ^ d ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono htop h
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hB0,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 / (k : ℝ))] using hr

/-- Exact actual count law; independence comes from the iid normalized
product measure and the real periodic patch is measurable. -/
theorem high_normalized_torus_count_probability {d k : ℕ} [NeZero k]
    (p : Covariate d → ℝ) (hp : Measurable p) (a b : ℝ) (ha : 0 < a)
    (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b)
    (n r : ℕ) (j : HighWindowLabels d k) :
    (Measure.pi (fun _ : Fin n => highNormalizedDesignLaw p)).real
      {x | designPatchCount n (highTorusPatch d k j) x = r} =
      binomialCountMass n ((highNormalizedDesignLaw p).real (highTorusPatch d k j)) r := by
  letI := high_normalized_design_probability p hp a b ha hb
  exact iid_design_patch_count_probability _ n _ (highTorusPatch_measurableSet d k j) r

/-- The exact source C_sharp, obtained from one raw density floor and one
normalizing mass floor in the selected likelihood. -/
def highFixedScoreDenominator (pMinus cMass : ℝ) : ℝ := (pMinus ^ 2 * cMass)⁻¹

theorem high_fixed_score_denominator_pos {pMinus cMass : ℝ} (hp : 0 < pMinus) (hc : 0 < cMass) :
    0 < highFixedScoreDenominator pMinus cMass := by
  unfold highFixedScoreDenominator
  positivity

theorem high_selected_raw_likelihood_inverse_bound {r : ℕ} (m pMinus cMass : ℝ)
    (hp : 0 < pMinus) (hc : 0 < cMass) (hm : pMinus ≤ m)
    (p q : Fin r → ℝ) (hpd : ∀ i, pMinus ≤ p i) (hqd : ∀ i, cMass ≤ q i) :
    (m ^ r * ∏ i, p i * q i)⁻¹ ≤ (highFixedScoreDenominator pMinus cMass) ^ r := by
  have hfac (i : Fin r) : pMinus ^ 2 * cMass ≤ m * (p i * q i) := by
    have hq0 : 0 ≤ q i := hc.le.trans (hqd i)
    have hp0 : 0 ≤ p i := hp.le.trans (hpd i)
    have hpq := mul_le_mul (hpd i) (hqd i) hc.le hp0
    have hh := mul_le_mul hm hpq (mul_nonneg hp.le hc.le) (hp.le.trans hm)
    nlinarith
  have hprod : (pMinus ^ 2 * cMass) ^ r ≤ m ^ r * ∏ i, p i * q i := by
    calc
      _ = ∏ _i : Fin r, pMinus ^ 2 * cMass := by simp
      _ ≤ ∏ i, m * (p i * q i) := Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hfac i)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hleft : 0 < (pMinus ^ 2 * cMass) ^ r := by positivity
  have hright : 0 < m ^ r * ∏ i, p i * q i := hleft.trans_le hprod
  unfold highFixedScoreDenominator
  rw [inv_pow]
  exact (inv_le_inv₀ hright hleft).mpr hprod

end NearlyMinimax
