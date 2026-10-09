module

public import NearlyMinimax.HistoryAdjacentExchange
public import NearlyMinimax.HistoryPriorDensity


@[expose] public section

/-!
# Actual heap-density transport through order isomorphisms

The maximal-deletion coefficients and the polynomial density are proved
invariant under a genuine heap order isomorphism with transported marks.
Combined with adjacent-exchange heap isomorphisms, this is the finite algebra
needed before append/delete can be lifted to the reference law.
-/

noncomputable section
namespace NearlyMinimax

variable {A B : Type*} [PartialOrder A] [PartialOrder B] [DecidableEq A] [DecidableEq B]

theorem historyMaximalPieces_orderIso_map (e : A ≃o B) (S : Finset A) :
    historyMaximalPieces (S.map e.toEquiv.toEmbedding) =
      (historyMaximalPieces S).map e.toEquiv.toEmbedding := by
  classical
  have hmem : ∀ (T : Finset A) (b : B), b ∈ T.map e.toEquiv.toEmbedding ↔ e.symm b ∈ T := by
    intro T b
    constructor
    · intro hb
      obtain ⟨a, ha, hab⟩ := Finset.mem_map.1 hb
      have hea : a = e.symm b := by apply e.injective; simpa using hab
      simpa only [← hea] using ha
    · intro hb
      exact Finset.mem_map.2 ⟨e.symm b, hb, e.apply_symm_apply b⟩
  ext b
  rw [mem_historyMaximalPieces, hmem, hmem, mem_historyMaximalPieces]
  constructor
  · rintro ⟨hb, hm⟩
    refine ⟨hb, ?_⟩
    intro a ha hba
    apply e.injective
    simpa only [e.apply_symm_apply] using
      hm (e a) (Finset.mem_map.2 ⟨a, ha, rfl⟩) (by simpa only [e.apply_symm_apply] using e.monotone hba)
  · rintro ⟨hb, hm⟩
    refine ⟨hb, ?_⟩
    intro c hc hbc
    have hh := hm (e.symm c) ((hmem S c).1 hc) (e.symm.monotone hbc)
    simpa only [e.apply_symm_apply] using congrArg e hh

/-- All genuine deletion coefficients are preserved, not just their eventual bounds. -/
theorem historyDeletionCoefficient_orderIso_map (e : A ≃o B) (weight : B → ℝ)
    (k : ℕ) (S : Finset A) :
    historyDeletionCoefficient weight k (S.map e.toEquiv.toEmbedding) =
      historyDeletionCoefficient (weight ∘ e) k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    rw [historyDeletionCoefficient_succ, historyDeletionCoefficient_succ,
      historyMaximalPieces_orderIso_map, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.map_erase, ih]
    rfl

/-- The actual combinatorial order volume is invariant under order transport. -/
theorem historyOrderVolume_orderIso_map (e : A ≃o B) (S : Finset A) :
    historyOrderVolume (S.map e.toEquiv.toEmbedding) = historyOrderVolume S := by
  unfold historyOrderVolume historyOrderCount
  rw [Finset.card_map, historyDeletionCoefficient_orderIso_map]
  rfl

/-- The actual upper-set density inherits invariance from its proved deletion polynomial. -/
theorem historyUpperDensity_orderIso_map (e : A ≃o B) (weight : B → ℝ)
    (S : Finset A) (t : ℝ) :
    historyUpperDensity weight (S.map e.toEquiv.toEmbedding) t =
      historyUpperDensity (weight ∘ e) S t := by
  rw [historyUpperDensity_eq_deletionPolynomial, historyUpperDensity_eq_deletionPolynomial]
  unfold historyDeletionPolynomial
  rw [Finset.card_map]
  apply Finset.sum_congr rfl
  intro k hk
  rw [historyDeletionCoefficient_orderIso_map]

/-- In particular, the actual source density with its rho factors transports exactly. -/
theorem historyScaledUpperDensity_orderIso_map (e : A ≃o B) (weight : B → ℝ)
    (ρ : ℝ) (S : Finset A) (t : ℝ) :
    historyScaledUpperDensity weight ρ (S.map e.toEquiv.toEmbedding) t =
      historyScaledUpperDensity (weight ∘ e) ρ S t := by
  unfold historyScaledUpperDensity
  exact historyUpperDensity_orderIso_map e _ S t

end NearlyMinimax
