module

public import NearlyMinimax.RawLiftHilbert


@[expose] public section

/-! Actual coordinatewise-L² features realize the universal raw packets,
with equality under the genuine sample product measures. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace NearlyMinimax.RawLiftHilbert
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {O : Type*} [MeasurableSpace O] (μ : Measure O) [IsProbabilityMeasure μ]

def packetOfFeatures {p k : ℕ} (g : O → Fin p → ℝ)
    (hg : ∀ a, MemLp (fun o => g o a) 2 μ)
    (H : FieldLiftCovariance.KernelMap p k)
    (hsym : ∀ (σ : Equiv.Perm (Fin k)) v, H (fun i => v (σ i)) = H v) : Packet μ k where
  featureCount := p
  features := fun a => (hg a).toLp (fun o => g o a)
  coefficient := H
  symmetric := hsym

def originalFeatureMean {p : ℕ} (g : O → Fin p → ℝ) : Fin p → ℝ :=
  fun a => ∫ o, g o a ∂μ

theorem packetOfFeatures_mean {p k : ℕ} (g : O → Fin p → ℝ)
    (hg : ∀ a, MemLp (fun o => g o a) 2 μ)
    (H : FieldLiftCovariance.KernelMap p k)
    (hsym : ∀ (σ : Equiv.Perm (Fin k)) v, H (fun i => v (σ i)) = H v) :
    featureMean μ (packetOfFeatures μ g hg H hsym).features = originalFeatureMean μ g := by
  ext a
  exact integral_congr_ae (hg a).coeFn_toLp

theorem packetOfFeatures_sample_features_ae {p k n : ℕ} (g : O → Fin p → ℝ)
    (hg : ∀ a, MemLp (fun o => g o a) 2 μ)
    (H : FieldLiftCovariance.KernelMap p k)
    (hsym : ∀ (σ : Equiv.Perm (Fin k)) v, H (fun i => v (σ i)) = H v) :
    ∀ᵐ o ∂SampleLaw μ n, ∀ j : Fin n,
      sampleFeatures μ (packetOfFeatures μ g hg H hsym).features n j o = g (o j) := by
  have h : ∀ j : Fin n, ∀ a : Fin p, ∀ᵐ o ∂SampleLaw μ n,
      (hg a).toLp (fun x => g x a) (o j) = g (o j) a := by
    intro j a
    exact (measurePreserving_eval (fun _ : Fin n => μ) j).quasiMeasurePreserving.ae_eq
      (hg a).coeFn_toLp
  have hall : ∀ᵐ o ∂SampleLaw μ n, ∀ j : Fin n, ∀ a : Fin p,
      (hg a).toLp (fun x => g x a) (o j) = g (o j) a :=
    Filter.eventually_all.mpr (fun j => Filter.eventually_all.mpr (h j))
  filter_upwards [hall] with o ho
  intro j
  ext a
  exact ho j a

theorem packetOfFeatures_raw_ae {p k : ℕ} (g : O → Fin p → ℝ)
    (hg : ∀ a, MemLp (fun o => g o a) 2 μ)
    (H : FieldLiftCovariance.KernelMap p k)
    (hsym : ∀ (σ : Equiv.Perm (Fin k)) v, H (fun i => v (σ i)) = H v) :
    packetRaw μ (packetOfFeatures μ g hg H hsym) =ᵐ[SampleLaw μ k]
      (fun o => H (fun i => g (o i))) := by
  filter_upwards [packetOfFeatures_sample_features_ae μ g hg H hsym (n := k)] with o ho
  exact congrArg H (funext fun i => ho i)

theorem packetOfFeatures_statistic_ae {p k n : ℕ} (g : O → Fin p → ℝ)
    (hg : ∀ a, MemLp (fun o => g o a) 2 μ)
    (H : FieldLiftCovariance.KernelMap p k)
    (hsym : ∀ (σ : Equiv.Perm (Fin k)) v, H (fun i => v (σ i)) = H v) :
    packetStatistic μ (packetOfFeatures μ g hg H hsym) n =ᵐ[SampleLaw μ n]
      LiftL2.kernelStatistic H (fun j o => g (o j) - originalFeatureMean μ g) := by
  filter_upwards [packetOfFeatures_sample_features_ae μ g hg H hsym (n := n)] with o ho
  let φ : Fin p → Lp ℝ 2 μ := fun a => (hg a).toLp (fun o => g o a)
  change LiftL2.kernelStatistic H (fun j o => sampleFeatures μ φ n j o - featureMean μ φ) o = _
  have hm : featureMean μ φ = originalFeatureMean μ g := packetOfFeatures_mean μ g hg H hsym
  have ho' : ∀ j : Fin n, sampleFeatures μ φ n j o = g (o j) := ho
  rw [hm]
  unfold LiftL2.kernelStatistic LiftL2.kernelSum
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  change H (fun i => sampleFeatures μ φ n (e i) o -
      originalFeatureMean μ g) = _
  simp_rw [ho']
  rfl

end NearlyMinimax.RawLiftHilbert
