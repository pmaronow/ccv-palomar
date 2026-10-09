module

public import NearlyMinimax.HighCenteredMark


@[expose] public section

/-! Intercept bounds and actual absolute-packet slope centering, for source
reference-law mean-one balancing. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

theorem finite_even_odd_sum_zero {I : Type*} [Fintype I]
    (e : Equiv.Perm I) (w f : I → ℝ)
    (hw : ∀ i, w (e i) = w i) (hf : ∀ i, f (e i) = -f i) :
    (∑ i, w i * f i) = 0 := by
  have he : (∑ i, w i * f i) = -(∑ i, w i * f i) := by
    calc
      _ = ∑ i, w (e i) * f (e i) := by
        symm
        apply Fintype.sum_equiv e
        intro i
        rfl
      _ = ∑ i, -(w i * f i) := by simp_rw [hw, hf, mul_neg]
      _ = _ := Finset.sum_neg_distrib _
  linarith

def densityMarkReflection (m r D : ℕ) : Equiv.Perm (HighDensityMarkIndex m r D) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight (fun _ : Fin r => Fin.revPerm))

def packetMarkReflection (ι : Type*) (m r D q : ℕ) : Equiv.Perm (HighPacketMarkIndex ι m r D q) :=
  Equiv.prodCongr (densityMarkReflection m r D) (Equiv.refl _)

theorem densityPacketWeight_abs_reflection (a b : ℝ) (m r D : ℕ)
    (h : HighDensityMarkIndex m r D) :
    |densityPacketWeight a b m r D (densityMarkReflection m r D h)| =
      |densityPacketWeight a b m r D h| := by
  change |densityPacketPrefactor a b r * exteriorWeight a b (m + r) h.1 *
      (∏ l, densityDerivativeWeight D (h.2 l).rev)| = _
  simp only [densityPacketWeight, abs_mul, Finset.abs_prod]
  have hp : (∏ l, |densityDerivativeWeight D (h.2 l).rev|) =
      ∏ l, |densityDerivativeWeight D (h.2 l)| := by
    apply Finset.prod_congr rfl
    intro l hl
    exact lobattoDerivativeWeight_abs_reflection ((D - 1) / 2) (h.2 l)
  rw [hp]

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def highPacketIntercept (a b : ℝ) (m r D q : ℕ)
    (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  (densityPacketAtom a b m r D e.2.1).1

def highPacketSlope (a b : ℝ) (m r D q : ℕ) (B : Z → Fin r → ℝ)
    (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  densityMargin a b (highPacketIntercept a b m r D q e) / ((r : ℝ) * b) *
    ∑ l, (densityPacketAtom a b m r D e.2.1).2 l * B e.1 l

theorem highPacketIntercept_measurable (a b : ℝ) (m r D q : ℕ) :
    Measurable (highPacketIntercept (Z := Z) (ι := ι) a b m r D q) := by
  apply measurable_from_prod_countable_left
  intro h
  change Measurable (fun _ : Z => (densityPacketAtom a b m r D h.1).1)
  exact measurable_const

theorem highPacketSlope_measurable (a b : ℝ) (m r D q : ℕ) (B : Z → Fin r → ℝ)
    (hB : ∀ l, Measurable (fun ζ => B ζ l)) :
    Measurable (highPacketSlope (ι := ι) a b m r D q B) := by
  apply measurable_from_prod_countable_left
  intro h
  unfold highPacketSlope highPacketIntercept
  dsimp only
  apply Measurable.const_mul
  exact Finset.measurable_fun_sum _ (fun l _ => (hB l).const_mul _)

theorem highPacketSlope_bound (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D q : ℕ) (hr : 1 ≤ r) (B : Z → Fin r → ℝ) (hB : ∀ ζ l, |B ζ l| ≤ 1)
    (e : Z × HighPacketMarkIndex ι m r D q) :
    |highPacketSlope a b m r D q B e| ≤ (b - a) / (4 * b) :=
  localDensityReset_slope_bound a b ha hab r hr
    (densityPacketAtom a b m r D e.2.1).1
    (densityPacketAtom_mem a b hab.le m r D e.2.1).1
    (densityPacketAtom a b m r D e.2.1).2
    (densityPacketAtom_mem a b hab.le m r D e.2.1).2
    (fun _ l => B e.1 l) () (hB e.1)

theorem highPacketMarkWeight_abs_reflection (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (ζ : Z) (h : HighPacketMarkIndex ι m r D q) :
    |highPacketMarkWeight a b m r D q C A (ζ, packetMarkReflection ι m r D q h)| =
      |highPacketMarkWeight a b m r D q C A (ζ, h)| := by
  change |densityPacketWeight a b m r D (densityMarkReflection m r D h.1) *
      highResponseMarkWeight C q (A ζ) h.2| = _
  rw [abs_mul, densityPacketWeight_abs_reflection, highPacketMarkWeight, abs_mul]

theorem highPacketSlope_reflection (a b : ℝ) (m r D q : ℕ) (B : Z → Fin r → ℝ)
    (ζ : Z) (h : HighPacketMarkIndex ι m r D q) :
    highPacketSlope a b m r D q B (ζ, packetMarkReflection ι m r D q h) =
      -highPacketSlope a b m r D q B (ζ, h) := by
  change densityMargin a b (exteriorNode a b (m + r) h.1.1) / ((r : ℝ) * b) *
      (∑ l, lobattoNode (derivativeOrder D) (h.1.2 l).rev * B ζ l) = _
  simp_rw [lobattoNode_reflection (derivativeOrder D) (by unfold derivativeOrder; omega)]
  simp only [neg_mul, Finset.sum_neg_distrib, mul_neg]
  rfl

theorem highPacketSlope_absolute_finite_sum_zero (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (B : Z → Fin r → ℝ) (ζ : Z) :
    (∑ h : HighPacketMarkIndex ι m r D q,
      |highPacketMarkWeight a b m r D q C A (ζ, h)| * highPacketSlope a b m r D q B (ζ, h)) = 0 :=
  finite_even_odd_sum_zero (packetMarkReflection ι m r D q) _ _
    (highPacketMarkWeight_abs_reflection a b m r D q C A ζ)
    (highPacketSlope_reflection a b m r D q B ζ)

theorem absoluteMarkLaw_integral {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (w : E → ℝ) (hmw : Measurable w)
    (hpos : 0 < signedMarkMass μ w) (F : E → ℝ) :
    (∫ e, F e ∂absoluteMarkLaw μ w) = (∫ e, |w e| * F e ∂μ) / signedMarkMass μ w := by
  rw [absoluteMarkLaw, integral_withDensity_eq_integral_toReal_smul
    (hmw.abs.div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have he : (fun e => (ENNReal.ofReal (|w e| / signedMarkMass μ w)).toReal • F e) =
      (fun e => (|w e| * F e) / signedMarkMass μ w) := by
    funext e
    rw [ENNReal.toReal_ofReal (div_nonneg (abs_nonneg (w e)) hpos.le), smul_eq_mul]
    exact div_mul_eq_mul_div _ _ _
  rw [he, integral_div]

theorem highPacketIntercept_integrable (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A) :
    Integrable (highPacketIntercept a b m r D q) (highPacketAbsoluteLaw σ a b m r D q C A) := by
  letI := highPacketAbsoluteLaw_probability σ a b m r D q C A hA hcost hpos
  apply (integrable_const b).mono' (highPacketIntercept_measurable a b m r D q).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro e
  have hb := (densityPacketAtom_mem a b hab.le m r D e.2.1).1
  change ‖(densityPacketAtom a b m r D e.2.1).1‖ ≤ b
  rw [Real.norm_eq_abs, abs_of_nonneg (ha.le.trans hb.1)]
  exact hb.2

theorem highPacketAbsoluteLaw_intercept_mem (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A) :
    (∫ e, highPacketIntercept a b m r D q e ∂highPacketAbsoluteLaw σ a b m r D q C A) ∈ Icc a b := by
  letI := highPacketAbsoluteLaw_probability σ a b m r D q C A hA hcost hpos
  have hi := highPacketIntercept_integrable σ a b ha hab m r D q C A hA hcost hpos
  constructor
  · have he := integral_mono (integrable_const a) hi (fun e =>
      (densityPacketAtom_mem a b hab.le m r D e.2.1).1.1)
    simpa using he
  · have he := integral_mono hi (integrable_const b) (fun e =>
      (densityPacketAtom_mem a b hab.le m r D e.2.1).1.2)
    simpa using he

theorem highPacketSlope_integrable (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (B : Z → Fin r → ℝ) (hmB : ∀ l, Measurable (fun ζ => B ζ l))
    (hB : ∀ ζ l, |B ζ l| ≤ 1) :
    Integrable (highPacketSlope a b m r D q B) (highPacketAbsoluteLaw σ a b m r D q C A) := by
  letI := highPacketAbsoluteLaw_probability σ a b m r D q C A hA hcost hpos
  apply (integrable_const ((b - a) / (4 * b))).mono'
    (highPacketSlope_measurable a b m r D q B hmB).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun e => by
    simpa only [Real.norm_eq_abs] using highPacketSlope_bound a b ha hab m r D q hr B hB e)

/-- Absolute derivative-rule reflection kills the actual affine slope under
the genuine normalized absolute packet law. No desired slope mean is supplied. -/
theorem highPacketAbsoluteLaw_slope_integral_zero (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (B : Z → Fin r → ℝ) (hmB : ∀ l, Measurable (fun ζ => B ζ l))
    (hB : ∀ ζ l, |B ζ l| ≤ 1) :
    (∫ e, highPacketSlope a b m r D q B e ∂highPacketAbsoluteLaw σ a b m r D q C A) = 0 := by
  have hi := (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost).abs.mul_bdd
    (highPacketSlope_measurable a b m r D q B hmB).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => by
      simpa only [Real.norm_eq_abs] using highPacketSlope_bound a b ha hab m r D q hr B hB e))
  rw [highPacketAbsoluteLaw, absoluteMarkLaw_integral _ _
    (highPacketMarkWeight_measurable a b m r D q C A hA) hpos,
    integral_prod _ hi]
  simp only [integral_count, highPacketSlope_absolute_finite_sum_zero, integral_zero, zero_div]

theorem highPacketAbsoluteLaw_affine_density_mean (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (B : Z → Fin r → ℝ) (hmB : ∀ l, Measurable (fun ζ => B ζ l))
    (hB : ∀ ζ l, |B ζ l| ≤ 1) (p : ℝ) :
    (∫ e, highPacketIntercept a b m r D q e + highPacketSlope a b m r D q B e * p
      ∂highPacketAbsoluteLaw σ a b m r D q C A) =
      ∫ e, highPacketIntercept a b m r D q e ∂highPacketAbsoluteLaw σ a b m r D q C A := by
  rw [integral_add (highPacketIntercept_integrable σ a b ha hab m r D q C A hA hcost hpos)
    ((highPacketSlope_integrable σ a b ha hab m r D q hr C A hA hcost hpos B hmB hB).mul_const p),
    integral_mul_const, highPacketAbsoluteLaw_slope_integral_zero σ a b ha hab m r D q hr C A
      hA hcost hpos B hmB hB, zero_mul, add_zero]

end Packet
end NearlyMinimax
