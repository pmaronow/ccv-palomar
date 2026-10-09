module

public import NearlyMinimax.FieldLiftCovariance
public import Mathlib.Analysis.Normed.Operator.Extend


@[expose] public section

/-!
Raw observation Hilbert spaces for the measurable-field clause of U6.

The elementary packets below allow a different finite feature space for every
packet. Their finite linear combinations are realized in one finite feature
space only inside the proof. The resulting Hilbert operator is consequently
independent of a common finite-dimensional coefficient representation.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace NearlyMinimax.RawLiftHilbert

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {O : Type*} [MeasurableSpace O] (μ : Measure O) [IsProbabilityMeasure μ]

abbrev SampleLaw (n : ℕ) := Measure.pi (fun _ : Fin n => μ)

def featureVector {p : ℕ} (φ : Fin p → Lp ℝ 2 μ) : O → Fin p → ℝ :=
  fun o a => φ a o

def sampleFeatures {p : ℕ} (φ : Fin p → Lp ℝ 2 μ) (n : ℕ) :
    Fin n → (Fin n → O) → Fin p → ℝ := fun j o => featureVector μ φ (o j)

def featureMean {p : ℕ} (φ : Fin p → Lp ℝ 2 μ) : Fin p → ℝ :=
  fun a => ∫ o, φ a o ∂μ

theorem featureVector_measurable {p : ℕ} (φ : Fin p → Lp ℝ 2 μ) :
    Measurable (featureVector μ φ) :=
  measurable_pi_iff.mpr fun a => (Lp.stronglyMeasurable (φ a)).measurable

theorem sampleFeatures_measurable {p : ℕ} (φ : Fin p → Lp ℝ 2 μ) (n : ℕ) (j : Fin n) :
    Measurable (sampleFeatures μ φ n j) :=
  (featureVector_measurable μ φ).comp (measurable_pi_apply j)

theorem sampleFeatures_independent {p : ℕ} (φ : Fin p → Lp ℝ 2 μ) (n : ℕ) :
    iIndepFun (sampleFeatures μ φ n) (SampleLaw μ n) :=
  iIndepFun_pi (fun _ => (featureVector_measurable μ φ).aemeasurable)

theorem sampleFeatures_memLp {p : ℕ} (φ : Fin p → Lp ℝ 2 μ) (n : ℕ)
    (j : Fin n) (a : Fin p) :
    MemLp (fun o => sampleFeatures μ φ n j o a) 2 (SampleLaw μ n) :=
  (Lp.memLp (φ a)).comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) j)

theorem sampleFeatures_mean {p : ℕ} (φ : Fin p → Lp ℝ 2 μ) (n : ℕ)
    (j : Fin n) (a : Fin p) :
    (∫ o, sampleFeatures μ φ n j o a ∂SampleLaw μ n) = featureMean μ φ a :=
  by
    have h := integral_map (μ := SampleLaw μ n) (φ := Function.eval j)
      (f := fun o => φ a o) (measurable_pi_apply j).aemeasurable
      ((Lp.stronglyMeasurable (φ a)).aestronglyMeasurable
        (μ := Measure.map (Function.eval j) (SampleLaw μ n)))
    rw [(measurePreserving_eval (fun _ : Fin n => μ) j).map_eq] at h
    exact h.symm

theorem sampleFeatures_identDistrib {p : ℕ} (φ : Fin p → Lp ℝ 2 μ)
    (n t : ℕ) (i : Fin n) (j : Fin t) :
    IdentDistrib (sampleFeatures μ φ n i) (sampleFeatures μ φ t j)
      (SampleLaw μ n) (SampleLaw μ t) := by
  have h : IdentDistrib (Function.eval i) (Function.eval j)
      (SampleLaw μ n) (SampleLaw μ t) :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply j).aemeasurable,
      by rw [(measurePreserving_eval (fun _ : Fin n => μ) i).map_eq,
        (measurePreserving_eval (fun _ : Fin t => μ) j).map_eq]⟩
  exact h.comp (featureVector_measurable μ φ)

/-- A genuine symmetric raw polynomial kernel, with its own feature dimension. -/
structure Packet (k : ℕ) where
  featureCount : ℕ
  features : Fin featureCount → Lp ℝ 2 μ
  coefficient : FieldLiftCovariance.KernelMap featureCount k
  symmetric : ∀ (σ : Equiv.Perm (Fin k)) v,
    coefficient (fun i => v (σ i)) = coefficient v

def packetRaw {k : ℕ} (P : Packet μ k) : (Fin k → O) → ℝ :=
  fun o => P.coefficient (fun i => featureVector μ P.features (o i))

theorem packetRaw_memLp {k : ℕ} (P : Packet μ k) :
    MemLp (packetRaw μ P) 2 (SampleLaw μ k) :=
  LiftL2.multilinear_kernel_memLp_two P.coefficient.toMultilinearMap
    (Function.Embedding.refl _) (sampleFeatures μ P.features k)
    (sampleFeatures_independent μ P.features k)
    (sampleFeatures_measurable μ P.features k) (sampleFeatures_memLp μ P.features k)

def packetRawLp {k : ℕ} (P : Packet μ k) : Lp ℝ 2 (SampleLaw μ k) :=
  (packetRaw_memLp μ P).toLp (packetRaw μ P)

def packetStatistic {k : ℕ} (P : Packet μ k) (n : ℕ) : (Fin n → O) → ℝ :=
  LiftL2.kernelStatistic P.coefficient
    (fun j o => sampleFeatures μ P.features n j o - featureMean μ P.features)

theorem packetStatistic_memLp {k : ℕ} (P : Packet μ k) (n : ℕ) :
    MemLp (packetStatistic μ P n) 2 (SampleLaw μ n) := by
  have hc := LiftL2.centerObservations_l2 (sampleFeatures μ P.features n)
    (featureMean μ P.features) (sampleFeatures_independent μ P.features n)
    (sampleFeatures_measurable μ P.features n)
    (sampleFeatures_identDistrib μ P.features n n)
    (sampleFeatures_memLp μ P.features n) (sampleFeatures_mean μ P.features n)
  exact LiftL2.kernelStatistic_memLp_two P.coefficient _ hc.1 hc.2.1 hc.2.2.2.1

def packetStatisticLp {k : ℕ} (P : Packet μ k) (n : ℕ) :
    Lp ℝ 2 (SampleLaw μ n) :=
  (packetStatistic_memLp μ P n).toLp (packetStatistic μ P n)

def rawCombination (k : ℕ) : (Packet μ k →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (SampleLaw μ k) :=
  Finsupp.linearCombination ℝ (packetRawLp μ)

def statisticCombination (k n : ℕ) :
    (Packet μ k →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (SampleLaw μ n) :=
  Finsupp.linearCombination ℝ (fun P => packetStatisticLp μ P n)

/-- Coordinates used only to realize one finite combination. Their size may
depend on the combination and is not constrained for a measurable field. -/
abbrev CombinationCoordinates {k : ℕ} (f : Packet μ k →₀ ℝ) :=
  (P : {P : Packet μ k // P ∈ f.support}) × Fin P.val.featureCount

def combinedFeatures {k : ℕ} (f : Packet μ k →₀ ℝ) :
    Fin (Fintype.card (CombinationCoordinates μ f)) → Lp ℝ 2 μ := by
  classical
  exact fun a => let j := (Fintype.equivFin (CombinationCoordinates μ f)).symm a
    j.1.val.features j.2

def combinationProjection {k : ℕ} (f : Packet μ k →₀ ℝ)
    (P : {P : Packet μ k // P ∈ f.support}) :
    (Fin (Fintype.card (CombinationCoordinates μ f)) → ℝ) →L[ℝ]
      (Fin P.val.featureCount → ℝ) := by
  classical
  exact ContinuousLinearMap.pi (fun a =>
    ContinuousLinearMap.proj ((Fintype.equivFin (CombinationCoordinates μ f)) ⟨P, a⟩))

def combinedCoefficient {k : ℕ} (f : Packet μ k →₀ ℝ) :
    FieldLiftCovariance.KernelMap (Fintype.card (CombinationCoordinates μ f)) k := by
  classical
  exact ∑ P : {P : Packet μ k // P ∈ f.support}, f P.val •
    P.val.coefficient.compContinuousLinearMap (fun _ => combinationProjection μ f P)

theorem combinedCoefficient_symmetric {k : ℕ} (f : Packet μ k →₀ ℝ)
    (σ : Equiv.Perm (Fin k)) v :
    combinedCoefficient μ f (fun i => v (σ i)) = combinedCoefficient μ f v := by
  classical
  simp only [combinedCoefficient, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact Finset.sum_congr rfl fun P _ => congrArg (fun x => f P.val • x)
    (P.val.symmetric σ (fun i => combinationProjection μ f P (v i)))

def combinedPacket {k : ℕ} (f : Packet μ k →₀ ℝ) : Packet μ k where
  featureCount := Fintype.card (CombinationCoordinates μ f)
  features := combinedFeatures μ f
  coefficient := combinedCoefficient μ f
  symmetric := combinedCoefficient_symmetric μ f

theorem combinationProjection_features {k : ℕ} (f : Packet μ k →₀ ℝ)
    (P : {P : Packet μ k // P ∈ f.support}) (o : O) :
    combinationProjection μ f P (featureVector μ (combinedFeatures μ f) o) =
      featureVector μ P.val.features o := by
  classical
  ext a
  change (fun j : CombinationCoordinates μ f => j.1.val.features j.2 o)
    ((Fintype.equivFin (CombinationCoordinates μ f)).symm
      ((Fintype.equivFin (CombinationCoordinates μ f)) ⟨P, a⟩)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem combinationProjection_mean {k : ℕ} (f : Packet μ k →₀ ℝ)
    (P : {P : Packet μ k // P ∈ f.support}) :
    combinationProjection μ f P (featureMean μ (combinedFeatures μ f)) =
      featureMean μ P.val.features := by
  classical
  ext a
  change (fun j : CombinationCoordinates μ f => ∫ o, j.1.val.features j.2 o ∂μ)
    ((Fintype.equivFin (CombinationCoordinates μ f)).symm
      ((Fintype.equivFin (CombinationCoordinates μ f)) ⟨P, a⟩)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem combinedPacket_raw {k : ℕ} (f : Packet μ k →₀ ℝ) (o : Fin k → O) :
    packetRaw μ (combinedPacket μ f) o =
      ∑ P ∈ f.support, f P * packetRaw μ P o := by
  classical
  simp only [packetRaw, combinedPacket, combinedCoefficient,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp_rw [combinationProjection_features]
  simpa only [packetRaw, smul_eq_mul] using
    (Finset.sum_coe_sort f.support (fun P => f P * packetRaw μ P o))

theorem combinedPacket_statistic {k : ℕ} (f : Packet μ k →₀ ℝ)
    (n : ℕ) (o : Fin n → O) :
    packetStatistic μ (combinedPacket μ f) n o =
      ∑ P ∈ f.support, f P * packetStatistic μ P n o := by
  classical
  change (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹) *
    (∑ e : Fin k ↪ Fin n, combinedCoefficient μ f (fun i =>
      sampleFeatures μ (combinedFeatures μ f) n (e i) o -
        featureMean μ (combinedFeatures μ f))) = _
  simp only [combinedCoefficient, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp_rw [map_sub, sampleFeatures, combinationProjection_features, combinationProjection_mean]
  rw [Finset.sum_comm, Finset.mul_sum]
  calc
    _ = ∑ P : {P : Packet μ k // P ∈ f.support},
        f P.val * packetStatistic μ P.val n o := by
      apply Finset.sum_congr rfl
      intro P _
      simp only [packetStatistic, LiftL2.kernelStatistic, LiftL2.kernelSum,
        sampleFeatures, smul_eq_mul]
      change (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹) *
          (∑ e : Fin k ↪ Fin n, f P.val * P.val.coefficient
            (fun i => featureVector μ P.val.features (o (e i)) -
              featureMean μ P.val.features)) =
        f P.val * ((((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹) *
          ∑ e : Fin k ↪ Fin n, P.val.coefficient
            (fun i => featureVector μ P.val.features (o (e i)) -
              featureMean μ P.val.features))
      rw [← Finset.mul_sum]
      ring
    _ = _ := Finset.sum_coe_sort f.support (fun P => f P * packetStatistic μ P n o)

theorem rawCombination_eq_combinedPacket {k : ℕ} (f : Packet μ k →₀ ℝ) :
    rawCombination μ k f = packetRawLp μ (combinedPacket μ f) := by
  classical
  apply Lp.ext
  change (∑ P ∈ f.support, f P • packetRawLp μ P) =ᵐ[SampleLaw μ k]
    packetRawLp μ (combinedPacket μ f)
  have hterms : ∀ᵐ o ∂SampleLaw μ k, ∀ P : Packet μ k,
      P ∈ f.support → packetRawLp μ P o = packetRaw μ P o := by
    have h : ∀ᵐ o ∂SampleLaw μ k, ∀ P : {P : Packet μ k // P ∈ f.support},
        packetRawLp μ P.val o = packetRaw μ P.val o :=
      Filter.eventually_all.mpr fun P => (packetRaw_memLp μ P.val).coeFn_toLp
    filter_upwards [h] with o ho
    intro P hP
    exact ho ⟨P, hP⟩
  filter_upwards [Lp.coeFn_linearCombination f (packetRawLp μ), hterms,
    (packetRaw_memLp μ (combinedPacket μ f)).coeFn_toLp] with o hl ht hr
  change rawCombination μ k f o = packetRawLp μ (combinedPacket μ f) o
  change packetRawLp μ (combinedPacket μ f) o = packetRaw μ (combinedPacket μ f) o at hr
  rw [hr, combinedPacket_raw]
  change (f.linearCombination ℝ (packetRawLp μ)) o = _
  rw [hl]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun P hP => congrArg (fun x => f P * x) (ht P hP)

theorem statisticCombination_eq_combinedPacket {k : ℕ} (f : Packet μ k →₀ ℝ) (n : ℕ) :
    statisticCombination μ k n f = packetStatisticLp μ (combinedPacket μ f) n := by
  classical
  apply Lp.ext
  have hterms : ∀ᵐ o ∂SampleLaw μ n, ∀ P : Packet μ k,
      P ∈ f.support → packetStatisticLp μ P n o = packetStatistic μ P n o := by
    have h : ∀ᵐ o ∂SampleLaw μ n, ∀ P : {P : Packet μ k // P ∈ f.support},
        packetStatisticLp μ P.val n o = packetStatistic μ P.val n o :=
      Filter.eventually_all.mpr fun P => (packetStatistic_memLp μ P.val n).coeFn_toLp
    filter_upwards [h] with o ho
    intro P hP
    exact ho ⟨P, hP⟩
  filter_upwards [Lp.coeFn_linearCombination f (fun P => packetStatisticLp μ P n), hterms,
    (packetStatistic_memLp μ (combinedPacket μ f) n).coeFn_toLp] with o hl ht hr
  change statisticCombination μ k n f o = packetStatisticLp μ (combinedPacket μ f) n o
  change packetStatisticLp μ (combinedPacket μ f) n o =
    packetStatistic μ (combinedPacket μ f) n o at hr
  rw [hr, combinedPacket_statistic]
  change (f.linearCombination ℝ (fun P => packetStatisticLp μ P n)) o = _
  rw [hl]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun P hP => congrArg (fun x => f P * x) (ht P hP)

theorem packetStatistic_mean_zero {k : ℕ} (hk : 0 < k) (P : Packet μ k) (n : ℕ) :
    (∫ o, packetStatistic μ P n o ∂SampleLaw μ n) = 0 := by
  have hc := LiftL2.centerObservations_l2 (sampleFeatures μ P.features n)
    (featureMean μ P.features) (sampleFeatures_independent μ P.features n)
    (sampleFeatures_measurable μ P.features n)
    (sampleFeatures_identDistrib μ P.features n n)
    (sampleFeatures_memLp μ P.features n) (sampleFeatures_mean μ P.features n)
  exact LiftL2.kernelStatistic_integral_eq_zero hk P.coefficient _
    hc.1 hc.2.1 hc.2.2.2.1 hc.2.2.2.2

/-- The actual factorial statistic contracts the raw product-kernel Hilbert
norm, with the sharp factorial constant. No coefficient norm appears. -/
theorem packetStatistic_norm_sq_le {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (P : Packet μ k) :
    ‖packetStatisticLp μ P n‖ ^ 2 ≤
      (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹) * ‖packetRawLp μ P‖ ^ 2 := by
  let X := sampleFeatures μ P.features n
  let Xk := sampleFeatures μ P.features k
  let m := featureMean μ P.features
  have hc := LiftL2.centerObservations_l2 X m
    (sampleFeatures_independent μ P.features n)
    (sampleFeatures_measurable μ P.features n)
    (sampleFeatures_identDistrib μ P.features n n)
    (sampleFeatures_memLp μ P.features n) (sampleFeatures_mean μ P.features n)
  have hv := LiftL2.kernelStatistic_variance hk hkn P.coefficient P.symmetric _
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  change variance (packetStatistic μ P n) (SampleLaw μ n) =
    (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹) *
      (∫ o, P.coefficient (fun i => X (Fin.castLEEmb hkn i) o - m) ^ 2
        ∂SampleLaw μ n) at hv
  have hcopy : IdentDistrib
      (fun o : Fin n → O => fun i : Fin k => X (Fin.castLEEmb hkn i) o - m)
      (fun o : Fin k → O => fun i : Fin k => Xk i o - m)
      (SampleLaw μ n) (SampleLaw μ k) := by
    apply IdentDistrib.pi
      (fun i => (sampleFeatures_identDistrib μ P.features n k
        (Fin.castLEEmb hkn i) i).comp (measurable_id.sub_const m))
    · exact hc.1.precomp (Fin.castLEEmb hkn).injective
    · exact (LiftL2.centerObservations_l2 Xk m
        (sampleFeatures_independent μ P.features k)
        (sampleFeatures_measurable μ P.features k)
        (sampleFeatures_identDistrib μ P.features k k)
        (sampleFeatures_memLp μ P.features k)
        (sampleFeatures_mean μ P.features k)).1
  have he := (hcopy.comp (P.coefficient.cont.pow 2).measurable).integral_eq
  change (∫ o, P.coefficient (fun i => X (Fin.castLEEmb hkn i) o - m) ^ 2
      ∂SampleLaw μ n) =
    (∫ o, P.coefficient (fun i => Xk i o - m) ^ 2 ∂SampleLaw μ k) at he
  have hcontract := LiftL2.independent_centering_square_le_l2 (SampleLaw μ k)
    P.coefficient Xk (sampleFeatures_measurable μ P.features k)
    (sampleFeatures_independent μ P.features k)
    (sampleFeatures_identDistrib μ P.features k k)
    (sampleFeatures_memLp μ P.features k) m (sampleFeatures_mean μ P.features k)
  have hn : ‖packetStatisticLp μ P n‖ ^ 2 =
      variance (packetStatistic μ P n) (SampleLaw μ n) := by
    rw [packetStatisticLp, LocalizationL2.toLp_norm_sq_eq_integral_sq,
      variance_eq_integral (packetStatistic_memLp μ P n).aemeasurable,
      packetStatistic_mean_zero μ hk P n]
    simp only [sub_zero]
  rw [hn, hv, he, packetRawLp, LocalizationL2.toLp_norm_sq_eq_integral_sq]
  exact mul_le_mul_of_nonneg_left hcontract (by positivity)

theorem statisticCombination_norm_sq_le {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (f : Packet μ k →₀ ℝ) :
    ‖statisticCombination μ k n f‖ ^ 2 ≤
      (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹) * ‖rawCombination μ k f‖ ^ 2 := by
  rw [rawCombination_eq_combinedPacket, statisticCombination_eq_combinedPacket]
  exact packetStatistic_norm_sq_le μ hk hkn _

theorem statisticCombination_norm_le {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (f : Packet μ k →₀ ℝ) :
    ‖statisticCombination μ k n f‖ ≤
      Real.sqrt (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹) *
        ‖rawCombination μ k f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact statisticCombination_norm_sq_le μ hk hkn f

/-- The closed raw-kernel space generated by all symmetric finite-feature
polynomials, with no fixed feature count or fixed feature map. -/
def rawKernelSpace (k : ℕ) : Submodule ℝ (Lp ℝ 2 (SampleLaw μ k)) :=
  (LinearMap.range (rawCombination μ k)).topologicalClosure

def rawClosureCombination (k : ℕ) :
    (Packet μ k →₀ ℝ) →ₗ[ℝ] rawKernelSpace μ k :=
  (rawCombination μ k).codRestrict (rawKernelSpace μ k)
    (fun f => (LinearMap.range (rawCombination μ k)).le_topologicalClosure
      (LinearMap.mem_range_self _ f))

theorem rawClosureCombination_dense (k : ℕ) : DenseRange (rawClosureCombination μ k) := by
  let A : Submodule ℝ (Lp ℝ 2 (SampleLaw μ k)) := LinearMap.range (rawCombination μ k)
  have hinc : (A : Set (Lp ℝ 2 (SampleLaw μ k))) ⊆
      (rawKernelSpace μ k : Set (Lp ℝ 2 (SampleLaw μ k))) := A.le_topologicalClosure
  have hd : DenseRange (Set.inclusion hinc) :=
    (denseRange_inclusion_iff hinc).mpr (by
      change closure (LinearMap.range (rawCombination μ k) : Set (Lp ℝ 2 (SampleLaw μ k))) ⊆
        closure (LinearMap.range (rawCombination μ k) : Set (Lp ℝ 2 (SampleLaw μ k)))
      exact Set.Subset.rfl)
  have hs : Function.Surjective (rawCombination μ k).rangeRestrict :=
    LinearMap.surjective_rangeRestrict _
  exact hd.comp hs.denseRange (continuous_inclusion _)

/-- The universal centered factorial lift is defined on the actual raw
Hilbert space by continuous extension of genuine finite polynomial lifts. -/
def centeredLiftOperator (k n : ℕ) :
    rawKernelSpace μ k →L[ℝ] Lp ℝ 2 (SampleLaw μ n) :=
  (statisticCombination μ k n).extendOfNorm (rawClosureCombination μ k)

theorem centeredLiftOperator_combination {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (f : Packet μ k →₀ ℝ) :
    centeredLiftOperator μ k n (rawClosureCombination μ k f) =
      statisticCombination μ k n f := by
  exact LinearMap.extendOfNorm_eq (rawClosureCombination_dense μ k)
    ⟨Real.sqrt (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹),
      fun f => statisticCombination_norm_le μ hk hkn f⟩ f

theorem centeredLiftOperator_norm_le {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (K : rawKernelSpace μ k) :
    ‖centeredLiftOperator μ k n K‖ ≤
      Real.sqrt (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹) * ‖K‖ := by
  exact LinearMap.norm_extendOfNorm_apply_le (rawClosureCombination_dense μ k) _
    (fun f => statisticCombination_norm_le μ hk hkn f) K

theorem centeredLiftOperator_norm_sq_le {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (K : rawKernelSpace μ k) :
    ‖centeredLiftOperator μ k n K‖ ^ 2 ≤
      (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹) * ‖K‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (centeredLiftOperator_norm_le μ hk hkn K) 2
  have hδ : 0 ≤ (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹) := by positivity
  simpa only [mul_pow, Real.sq_sqrt hδ] using h

def packetInRawSpace {k : ℕ} (P : Packet μ k) : rawKernelSpace μ k :=
  ⟨packetRawLp μ P, (LinearMap.range (rawCombination μ k)).le_topologicalClosure
    ⟨Finsupp.single P 1, by simp [rawCombination]⟩⟩

theorem centeredLiftOperator_packet {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (P : Packet μ k) :
    centeredLiftOperator μ k n (packetInRawSpace μ P) = packetStatisticLp μ P n := by
  have h := centeredLiftOperator_combination μ hk hkn (Finsupp.single P 1)
  have he : rawClosureCombination μ k (Finsupp.single P 1) = packetInRawSpace μ P := by
    apply Subtype.ext
    simp [rawClosureCombination, rawCombination, packetInRawSpace]
  rw [he] at h
  simpa [statisticCombination] using h

def pairedFeatures {p q : ℕ} (φ : Fin p → Lp ℝ 2 μ) (ψ : Fin q → Lp ℝ 2 μ) :
    Fin (p + q) → Lp ℝ 2 μ := Fin.addCases φ ψ

def leftProjection (p q : ℕ) : (Fin (p + q) → ℝ) →L[ℝ] (Fin p → ℝ) :=
  ContinuousLinearMap.pi (fun a => ContinuousLinearMap.proj (Fin.castAdd q a))

def rightProjection (p q : ℕ) : (Fin (p + q) → ℝ) →L[ℝ] (Fin q → ℝ) :=
  ContinuousLinearMap.pi (fun a => ContinuousLinearMap.proj (Fin.natAdd p a))

theorem pairedFeatures_left_center {p q n : ℕ}
    (φ : Fin p → Lp ℝ 2 μ) (ψ : Fin q → Lp ℝ 2 μ) (j : Fin n) (o : Fin n → O) :
    leftProjection p q (sampleFeatures μ (pairedFeatures μ φ ψ) n j o -
      featureMean μ (pairedFeatures μ φ ψ)) =
    sampleFeatures μ φ n j o - featureMean μ φ := by
  ext a
  simp [leftProjection, sampleFeatures, featureVector, featureMean, pairedFeatures]

theorem pairedFeatures_right_center {p q n : ℕ}
    (φ : Fin p → Lp ℝ 2 μ) (ψ : Fin q → Lp ℝ 2 μ) (j : Fin n) (o : Fin n → O) :
    rightProjection p q (sampleFeatures μ (pairedFeatures μ φ ψ) n j o -
      featureMean μ (pairedFeatures μ φ ψ)) =
    sampleFeatures μ ψ n j o - featureMean μ ψ := by
  ext a
  simp [rightProjection, sampleFeatures, featureVector, featureMean, pairedFeatures]

/-- Actual scalar packet statistics of different orders are orthogonal,
even when their feature representations differ. -/
theorem packetStatistic_covariance_different_orders {k t n : ℕ}
    (hk : 0 < k) (ht : 0 < t) (hkt : k ≠ t) (P : Packet μ k) (Q : Packet μ t) :
    covariance (packetStatistic μ P n) (packetStatistic μ Q n) (SampleLaw μ n) = 0 := by
  let φ := pairedFeatures μ P.features Q.features
  let m := featureMean μ φ
  let X := sampleFeatures μ φ n
  let H := P.coefficient.compContinuousLinearMap
    (fun _ => leftProjection P.featureCount Q.featureCount)
  let G := Q.coefficient.compContinuousLinearMap
    (fun _ => rightProjection P.featureCount Q.featureCount)
  have hc := LiftL2.centerObservations_l2 X m (sampleFeatures_independent μ φ n)
    (sampleFeatures_measurable μ φ n) (sampleFeatures_identDistrib μ φ n n)
    (sampleFeatures_memLp μ φ n) (sampleFeatures_mean μ φ n)
  have hH : LiftL2.kernelStatistic H (fun j o => X j o - m) = packetStatistic μ P n := by
    funext o
    unfold LiftL2.kernelStatistic LiftL2.kernelSum packetStatistic
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    change P.coefficient (fun i => leftProjection P.featureCount Q.featureCount
        (sampleFeatures μ (pairedFeatures μ P.features Q.features) n (e i) o -
          featureMean μ (pairedFeatures μ P.features Q.features))) = _
    simp_rw [pairedFeatures_left_center]
    rfl
  have hG : LiftL2.kernelStatistic G (fun j o => X j o - m) = packetStatistic μ Q n := by
    funext o
    unfold LiftL2.kernelStatistic LiftL2.kernelSum packetStatistic
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    change Q.coefficient (fun i => rightProjection P.featureCount Q.featureCount
        (sampleFeatures μ (pairedFeatures μ P.features Q.features) n (e i) o -
          featureMean μ (pairedFeatures μ P.features Q.features))) = _
    simp_rw [pairedFeatures_right_center]
    rfl
  rw [← hH, ← hG]
  unfold LiftL2.kernelStatistic
  rw [covariance_const_mul_left, covariance_const_mul_right,
    LiftL2.kernelSum_covariance_different_orders hk ht hkt
      H.toMultilinearMap G.toMultilinearMap _ hc.1 hc.2.1 hc.2.2.2.1 hc.2.2.2.2]
  ring

theorem packetStatistic_inner_different_orders {k t n : ℕ}
    (hk : 0 < k) (ht : 0 < t) (hkt : k ≠ t) (P : Packet μ k) (Q : Packet μ t) :
    inner ℝ (packetStatisticLp μ P n) (packetStatisticLp μ Q n) = 0 := by
  rw [L2.inner_def]
  have he : (∫ o, inner ℝ (packetStatisticLp μ P n o) (packetStatisticLp μ Q n o)
      ∂SampleLaw μ n) =
      ∫ o, packetStatistic μ P n o * packetStatistic μ Q n o ∂SampleLaw μ n := by
    apply integral_congr_ae
    filter_upwards [(packetStatistic_memLp μ P n).coeFn_toLp,
      (packetStatistic_memLp μ Q n).coeFn_toLp] with o hp hq
    change packetStatisticLp μ P n o = packetStatistic μ P n o at hp
    change packetStatisticLp μ Q n o = packetStatistic μ Q n o at hq
    rw [hp, hq]
    simp [RCLike.inner_apply, mul_comm]
  rw [he]
  have hcov := packetStatistic_covariance_different_orders μ hk ht hkt P Q (n := n)
  rw [covariance, packetStatistic_mean_zero μ hk P n,
    packetStatistic_mean_zero μ ht Q n] at hcov
  simpa only [sub_zero] using hcov

theorem statisticCombination_inner_different_orders {k t n : ℕ}
    (hk : 0 < k) (ht : 0 < t) (hkt : k ≠ t)
    (f : Packet μ k →₀ ℝ) (g : Packet μ t →₀ ℝ) :
    inner ℝ (statisticCombination μ k n f) (statisticCombination μ t n g) = 0 := by
  rw [statisticCombination_eq_combinedPacket, statisticCombination_eq_combinedPacket]
  exact packetStatistic_inner_different_orders μ hk ht hkt _ _

/-- Cross-order orthogonality survives passage to the genuine raw-kernel
Hilbert closures. This is proved from actual independent observations. -/
theorem centeredLiftOperator_inner_different_orders {k t n : ℕ}
    (hk : 0 < k) (ht : 0 < t) (hkn : k ≤ n) (htn : t ≤ n) (hkt : k ≠ t)
    (K : rawKernelSpace μ k) (L : rawKernelSpace μ t) :
    inner ℝ (centeredLiftOperator μ k n K) (centeredLiftOperator μ t n L) = 0 := by
  refine (rawClosureCombination_dense μ k).induction_on K
    (isClosed_eq (by fun_prop) continuous_const) ?_
  intro f
  refine (rawClosureCombination_dense μ t).induction_on L
    (isClosed_eq (by fun_prop) continuous_const) ?_
  intro g
  rw [centeredLiftOperator_combination μ hk hkn,
    centeredLiftOperator_combination μ ht htn]
  exact statisticCombination_inner_different_orders μ hk ht hkt f g

def centeredLiftSeries {R : ℕ} (n : ℕ)
    (K : (r : Fin R) → rawKernelSpace μ (r.val + 1)) : Lp ℝ 2 (SampleLaw μ n) :=
  ∑ r : Fin R, centeredLiftOperator μ (r.val + 1) n (K r)

theorem centeredLiftSeries_norm_sq_le {R n : ℕ} (hRn : R ≤ n)
    (K : (r : Fin R) → rawKernelSpace μ (r.val + 1)) :
    ‖centeredLiftSeries μ n K‖ ^ 2 ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) *
        (n.descFactorial (r.val + 1) : ℝ))⁻¹ * ‖K r‖ ^ 2 := by
  have hnorm : ‖centeredLiftSeries μ n K‖ ^ 2 =
      ∑ r : Fin R, ‖centeredLiftOperator μ (r.val + 1) n (K r)‖ ^ 2 := by
    unfold centeredLiftSeries
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    apply Finset.sum_congr rfl
    intro r _
    rw [inner_sum, Finset.sum_eq_single r]
    · exact real_inner_self_eq_norm_sq _
    · intro t _ htr
      exact centeredLiftOperator_inner_different_orders μ (by omega) (by omega)
        ((Nat.succ_le_of_lt r.isLt).trans hRn)
        ((Nat.succ_le_of_lt t.isLt).trans hRn)
        (by intro h; exact htr (Fin.ext (by omega))) _ _
    · exact fun h => (h (Finset.mem_univ r)).elim
  rw [hnorm]
  apply Finset.sum_le_sum
  intro r _
  exact centeredLiftOperator_norm_sq_le μ (by omega)
    ((Nat.succ_le_of_lt r.isLt).trans hRn) _

theorem centeredLiftSeries_norm_sq_le_power {R n : ℕ} (hRn : R ≤ n)
    (K : (r : Fin R) → rawKernelSpace μ (r.val + 1))
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    ‖centeredLiftSeries μ n K‖ ^ 2 ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ * ‖K r‖ ^ 2 := by
  apply (centeredLiftSeries_norm_sq_le μ hRn K).trans
  apply Finset.sum_le_sum
  intro r _
  have hb := LiftL2.descFactorial_lower_bound hRn (Nat.succ_le_of_lt r.isLt) hΛ.le hΛn
  have hfac : 0 < ((r.val + 1).factorial : ℝ) := by positivity
  have hpow : 0 < Λ ^ (r.val + 1) := pow_pos hΛ _
  exact mul_le_mul_of_nonneg_right
    ((inv_le_inv₀ (mul_pos hfac (hpow.trans_le hb)) (mul_pos hfac hpow)).2
      (mul_le_mul_of_nonneg_left hb hfac.le)) (sq_nonneg _)

end NearlyMinimax.RawLiftHilbert
