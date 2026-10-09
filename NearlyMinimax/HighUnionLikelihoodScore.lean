module

public import NearlyMinimax.HighUnionFieldScore
public import NearlyMinimax.HighUnionSourceGeometry
public import NearlyMinimax.HighUnionSourceModel
public import NearlyMinimax.HighHistoryLikelihoodScore
public import NearlyMinimax.HighWindowLikelihoodAlgebra


@[expose] public section

/-! Exact global likelihood-score decomposition for the actual complete
marked source. The squared window partition counts the variance correction once. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

lemma highLocalFieldWithout_update (d k D : ℕ) [NeZero k] (η : ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (j : HighWindowLabels d k) (u : HighFrameIndex d D → ℝ) (x : Covariate d) :
    highLocalFieldWithout d k D η (Function.update c j u) j x =
      highLocalFieldWithout d k D η c j x := by
  unfold highLocalFieldWithout
  apply congrArg (fun v : ℝ => η*v)
  apply Finset.sum_congr rfl
  intro l hl
  rw [Function.update_of_ne (Finset.mem_erase.mp hl).1]

lemma highFrameField_update_coefficientRegression (d k D n : ℕ) [NeZero k] (hk : 4 ≤ k)
    (η : ℝ) (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (j : HighWindowLabels d k) (u : HighFrameIndex d D → ℝ)
    (x : Fin n → Covariate d) :
    coefficientRegression η (fun i => highLocalFieldWithout d k D η c j (x i))
      (fun i => highPeriodicTensor d k j (x i))
      (fun i => highLocalFrameFeature k j (x i)) u =
      fun i => highFrameField d k η (fun l => highFramePolynomial (Function.update c j u l)) (x i) := by
  have h := highFrameField_coefficientRegression d k D n hk η (Function.update c j u) j x
  simpa only [Function.update_self, highLocalFieldWithout_update] using h

section ActualSource
variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (R : HighUnionRowData d k D I E)

lemma highUnionSourceState_append_coefficients (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (e : HighUnionMark E) :
    (highUnionSourceState C R (historyMarkedAppend
      (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e))).2 =
      Function.update (highUnionSourceState C R h).2 j
        (highUnionResponseReset R e ((highUnionSourceState C R h).2 j)) := by
  rw [highUnionSourceState_append R C j h e]
  rfl

lemma highUnionSourceRegression_append (n : ℕ) (hk : 4 ≤ k) (η : ℝ)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (e : HighUnionMark E) (x : Fin n → Covariate d) :
    coefficientRegression η
      (fun i => highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j (x i))
      (fun i => highPeriodicTensor d k j (x i))
      (fun i => highLocalFrameFeature k j (x i))
      (highUnionResponseReset R e ((highUnionSourceState C R h).2 j)) =
      fun i => highUnionSourceRegression C R η
        (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
          (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)) (x i) := by
  unfold highUnionSourceRegression
  rw [highUnionSourceState_append_coefficients C R j h e]
  exact highFrameField_update_coefficientRegression d k D n hk η _ j _ x

/-- The true local score, evaluated on the actual canonical history and
its actual appended reset states. -/
def highUnionSourceLocalScore (n : ℕ) (a V η : ℝ)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Fin n → Covariate d) (j : HighWindowLabels d k) (y : Fin n → Fin 3) : ℝ :=
  highFrameMarkedScore d k D n
    (fun _ => highUnionLaw R (highCenterMix C))
    (fun _ => highUnionActivation R (highCenterMix C)) a V η
    (fun i => highUnionSourceDensity C R h (x i))
    (fun l e i => highUnionSourceDensity C R
      (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) l (h,e)) (x i))
    (fun l e => highUnionResponseReset R e ((highUnionSourceState C R h).2 l))
    (highUnionSourceState C R h).2 x j y

lemma highUnionSourceAppendLikelihoodAction_eq_responseAction (n : ℕ) (hk : 4 ≤ k)
    (a V η : ℝ) (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Fin n → Covariate d) (y : Fin n → Fin 3) :
    highAppendLikelihoodAction (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
      (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
      n a V (highUnionSourceDensity C R) (highUnionSourceRegression C R η) j h (x,y) =
    highMarkedResponseAction (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      (fun e i => highUnionSourceDensity C R
        (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
          (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)) (x i))
      (fun e => highUnionResponseReset R e ((highUnionSourceState C R h).2 j))
      (fun i => highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j (x i))
      (fun i => highPeriodicTensor d k j (x i))
      (fun i => highLocalFrameFeature k j (x i)) y := by
  unfold highAppendLikelihoodAction highMarkedResponseAction
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun e => by
    dsimp only
    unfold highRawSampleLikelihood
    rw [Finset.prod_mul_distrib]
    unfold highResponseProduct
    rw [highUnionSourceRegression_append C R n hk η j h e x]
    exact (mul_assoc _ _ _).symm

/-- The global append/heat likelihood score is exactly the sum of the
true local window scores. This uses the actual reset recursion and exact
squared partition, with no statistical energy premise. -/
theorem highUnionSourceLikelihoodScore_eq_sum (n : ℕ) (hk : 4 ≤ k) (a V η : ℝ)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Fin n → Covariate d) (y : Fin n → Fin 3) :
    highHistoryLikelihoodScore (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
      (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
      n a V η (highUnionSourceDensity C R) (highUnionSourceRegression C R η) h (x,y) =
      ∑ j, highUnionSourceLocalScore C R n a V η h x j y := by
  simp only [highUnionSourceLocalScore, highFrameMarkedScore]
  rw [highMarkedLocalScore_sum_of_partition
    (hreg := fun j => highFrameField_coefficientRegression d k D n hk η
      (highUnionSourceState C R h).2 j x)
    (hpartition := fun i => highPeriodicTensor_sq_partition d k (by omega) (x i))]
  unfold highHistoryLikelihoodScore highHistoryLikelihoodDerivative
  simp_rw [highUnionSourceAppendLikelihoodAction_eq_responseAction C R n hk a V η]
  unfold highRawSampleLikelihood highRawSampleVarianceDerivative highUnionSourceRegression
  rw [Finset.prod_mul_distrib]
  congr 2
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end ActualSource
end NearlyMinimax
