module

public import NearlyMinimax.LiftL2
public import NearlyMinimax.LocalizationL2


@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace NearlyMinimax.FieldLiftCovariance

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {M : Measure W}

abbrev KernelMap (p k : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ

/-- The actual raw kernel is a continuous linear function of its
multilinear coefficient map, with values in the observation L² space.
The finite coordinate expansion proves this even for unbounded features. -/
def rawKernelOperator {n p k : ℕ} (e : Fin k ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) : KernelMap p k →L[ℝ] Lp ℝ 2 μ :=
  ∑ σ : Fin k → Fin p,
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin p → ℝ) ℝ
      (fun i => Pi.single (σ i) 1)).smulRight
      ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp
        (fun ω => ∏ i, X (e i) ω (σ i)))

/-- This operator is precisely the real raw kernel, modulo almost-everywhere equality. -/
theorem raw_kernel_operator_eq_toLp {n p k : ℕ} (e : Fin k ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) (H : KernelMap p k) :
    rawKernelOperator e X hind hmeas hL2 H =
      (LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap e X hind hmeas hL2).toLp
        (fun ω => H (fun i => X (e i) ω)) := by
  classical
  have heq : rawKernelOperator e X hind hmeas hL2 H =
      ∑ σ : Fin k → Fin p, H (fun i => Pi.single (σ i) 1) •
        ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp
          (fun ω => ∏ i, X (e i) ω (σ i))) := by
    simp [rawKernelOperator]
  rw [heq]
  apply Lp.ext
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ
    (fun σ : Fin k → Fin p => H (fun i => Pi.single (σ i) 1) •
      ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp
        (fun ω => ∏ i, X (e i) ω (σ i))))
  have hterms : ∀ᵐ ω ∂μ, ∀ σ : Fin k → Fin p,
      (H (fun i => Pi.single (σ i) 1) •
        ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp
          (fun ω => ∏ i, X (e i) ω (σ i)))) ω =
        H (fun i => Pi.single (σ i) 1) * ∏ i, X (e i) ω (σ i) := by
    apply Filter.eventually_all.mpr
    intro σ
    filter_upwards [Lp.coeFn_smul (H (fun i => Pi.single (σ i) 1))
      ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp
        (fun ω => ∏ i, X (e i) ω (σ i))),
      (LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).coeFn_toLp] with ω hs hp
    rw [hs, Pi.smul_apply, hp, smul_eq_mul]
  filter_upwards [hsum, hterms,
    (LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap e X hind hmeas hL2).coeFn_toLp]
    with ω hs ht hH
  change ((LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap e X hind hmeas hL2).toLp
    (fun ω => H (fun i => X (e i) ω))) ω = H (fun i => X (e i) ω) at hH
  rw [hs, hH]
  calc
    _ = ∑ σ : Fin k → Fin p,
        H (fun i => Pi.single (σ i) 1) * ∏ i, X (e i) ω (σ i) :=
      Finset.sum_congr rfl (fun σ _ => ht σ)
    _ = H (fun i => X (e i) ω) :=
      (LiftL2.multilinear_coordinate_expansion H.toMultilinearMap _).symm

/-- The genuine raw-kernel energy equals the operator's squared Hilbert norm. -/
theorem raw_kernel_operator_norm_sq {n p k : ℕ} (e : Fin k ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) (H : KernelMap p k) :
    ‖rawKernelOperator e X hind hmeas hL2 H‖ ^ 2 =
      ∫ ω, H (fun i => X (e i) ω) ^ 2 ∂μ := by
  rw [raw_kernel_operator_eq_toLp]
  exact LocalizationL2.toLp_norm_sq_eq_integral_sq _

/-- Bochner integration commutes with the actual raw-kernel operator. -/
theorem raw_kernel_integral_commute {n p k : ℕ} (e : Fin k ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (ν : W → ℝ) (H : W → KernelMap p k)
    (hH : Integrable (fun w => ν w • H w) M) :
    rawKernelOperator e X hind hmeas hL2 (∫ w, ν w • H w ∂M) =
      ∫ w, ν w • rawKernelOperator e X hind hmeas hL2 (H w) ∂M := by
  rw [← (rawKernelOperator e X hind hmeas hL2).integral_comp_comm hH]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => map_smul _ _ _)

/-- Raw support separation becomes genuine L² orthogonality, before centering. -/
theorem raw_kernel_operator_inner_zero {n p k : ℕ} (e : Fin k ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) (H G : KernelMap p k)
    (hdisjoint : ∀ᵐ ω ∂μ,
      H (fun i => X (e i) ω) * G (fun i => X (e i) ω) = 0) :
    ⟪rawKernelOperator e X hind hmeas hL2 H,
      rawKernelOperator e X hind hmeas hL2 G⟫ = 0 := by
  rw [raw_kernel_operator_eq_toLp, raw_kernel_operator_eq_toLp]
  exact LocalizationL2.toLp_inner_eq_zero_of_disjoint _ _ hdisjoint

/-- A weighted factorial-lift term is integrable in its coefficient field. -/
theorem weighted_kernel_statistic_integrable {n p k : ℕ}
    (X : Fin n → Ω → Fin p → ℝ) (ν : W → ℝ) (H : W → KernelMap p k)
    (hH : Integrable (fun w => ν w • H w) M) (ω : Ω) :
    Integrable (fun w => ν w * LiftL2.kernelStatistic (H w) X ω) M := by
  classical
  let d := (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹)
  have hi (e : Fin k ↪ Fin n) : Integrable (fun w => ν w * H w (fun i => X (e i) ω)) M := by
    simpa only [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul] using
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin p → ℝ) ℝ
        (fun i => X (e i) ω)).integrable_comp hH
  have hsum := integrable_finsetSum Finset.univ (fun e _ => (hi e).const_mul d)
  convert hsum using 1
  funext w
  simp only [LiftL2.kernelStatistic, LiftL2.kernelSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  dsimp [d]
  ring

/-- Actual spatial integration commutes with finite factorial averaging. -/
theorem kernel_statistic_integral_commute {n p k : ℕ}
    (X : Fin n → Ω → Fin p → ℝ) (ν : W → ℝ) (H : W → KernelMap p k)
    (hH : Integrable (fun w => ν w • H w) M) (ω : Ω) :
    (∫ w, ν w * LiftL2.kernelStatistic (H w) X ω ∂M) =
      LiftL2.kernelStatistic (∫ w, ν w • H w ∂M) X ω := by
  classical
  let d := (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹)
  have hi (e : Fin k ↪ Fin n) : Integrable (fun w => ν w * H w (fun i => X (e i) ω)) M := by
    simpa only [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul] using
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin p → ℝ) ℝ
        (fun i => X (e i) ω)).integrable_comp hH
  have heval (v : Fin k → Fin p → ℝ) :
      (∫ w, ν w • H w ∂M) v = ∫ w, ν w * H w v ∂M := by
    rw [ContinuousMultilinearMap.integral_apply hH]
    rfl
  have halg : (fun w => ν w * LiftL2.kernelStatistic (H w) X ω) =
      (fun w => d * ∑ e : Fin k ↪ Fin n, ν w * H w (fun i => X (e i) ω)) := by
    funext w
    simp only [LiftL2.kernelStatistic, LiftL2.kernelSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    dsimp [d]
    ring
  rw [halg, integral_const_mul, integral_finsetSum _ (fun e _ => hi e)]
  change d * ∑ e : Fin k ↪ Fin n, (∫ w, ν w * H w (fun i => X (e i) ω) ∂M) =
    d * ∑ e : Fin k ↪ Fin n, (∫ w, ν w • H w ∂M) (fun i => X (e i) ω)
  simp_rw [heval]

/-- Spatial integration commutes with the entire centered Taylor lift. -/
theorem centered_expansion_integral_commute {n p R : ℕ}
    (X : Fin n → Ω → Fin p → ℝ) (ν : W → ℝ)
    (H : W → (r : Fin R) → KernelMap p (r.val + 1))
    (hH : ∀ r, Integrable (fun w => ν w • H w r) M) (ω : Ω) :
    (∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w) X ω ∂M) =
      LiftL2.centeredKernelExpansion 0 (fun r => ∫ w, ν w • H w r ∂M) X ω := by
  simp only [LiftL2.centeredKernelExpansion, zero_add, Finset.mul_sum]
  rw [integral_finsetSum _ (fun r _ => weighted_kernel_statistic_integrable X ν (fun w => H w r) (hH r) ω)]
  exact Finset.sum_congr rfl (fun r _ => kernel_statistic_integral_commute X ν (fun w => H w r) (hH r) ω)

/-- Symmetry of the genuine multilinear fields is preserved by integration. -/
theorem integrated_kernel_symmetric {p k : ℕ}
    (ν : W → ℝ) (H : W → KernelMap p k)
    (hH : Integrable (fun w => ν w • H w) M)
    (hsym : ∀ w (σ : Equiv.Perm (Fin k)) v,
      H w (fun i => v (σ i)) = H w v)
    (σ : Equiv.Perm (Fin k)) (v : Fin k → Fin p → ℝ) :
    (∫ w, ν w • H w ∂M) (fun i => v (σ i)) = (∫ w, ν w • H w ∂M) v := by
  rw [ContinuousMultilinearMap.integral_apply hH,
    ContinuousMultilinearMap.integral_apply hH]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun w => by
    simp only [smul_apply, hsym w σ v]))

/-- Actual coefficient integration yields a square-integrable centered
random variable; centering and integrability are proved from the input L²
observations, rather than required as covariance hypotheses. -/
theorem integrated_centered_lift_moment_facts {n p R : ℕ}
    (H : W → (r : Fin R) → KernelMap p (r.val + 1))
    (ν : W → ℝ) (hH : ∀ r, Integrable (fun w => ν w • H w r) M)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a) :
    MemLp (fun ω => ∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w)
        (fun j ω => X j ω - m) ω ∂M) 2 μ ∧
      (∫ ω, ∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w)
        (fun j ω => X j ω - m) ω ∂M ∂μ) = 0 := by
  have heq : (fun ω => ∫ w,
      ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) =
      LiftL2.centeredKernelExpansion 0 (fun r => ∫ w, ν w • H w r ∂M)
        (fun j ω => X j ω - m) := by
    funext ω
    exact centered_expansion_integral_commute _ ν H hH ω
  rw [heq]
  obtain ⟨hi, hm, _, hlp, hzero⟩ := LiftL2.centerObservations_l2 X m
    hind hmeas hid hL2 hmean
  exact ⟨LiftL2.centeredKernelExpansion_memLp_two _ _ _ hi hm hlp,
    LiftL2.centeredKernelExpansion_expectation _ _ _ hi hm hlp hzero⟩

/-- The localized variance endpoints are exactly the L² energy asserted in
the manuscript, because the integrated centered field has actual mean zero. -/
theorem integrated_centered_lift_variance_eq_second_moment {n p R : ℕ}
    (H : W → (r : Fin R) → KernelMap p (r.val + 1))
    (ν : W → ℝ) (hH : ∀ r, Integrable (fun w => ν w • H w r) M)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a) :
    variance (fun ω => ∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w)
        (fun j ω => X j ω - m) ω ∂M) μ =
      ∫ ω, (∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w)
        (fun j ω => X j ω - m) ω ∂M) ^ 2 ∂μ := by
  obtain ⟨hlp, hzero⟩ := integrated_centered_lift_moment_facts H ν hH X m
    hind hmeas hid hL2 hmean
  rw [variance_eq_integral hlp.aemeasurable, hzero]
  simp only [sub_zero]

/-- The factorial variance series and the centering contraction apply to an
arbitrary symmetric Taylor coefficient collection, including one obtained by
spatial integration. The right side consists of actual uncentered kernels. -/
theorem centered_expansion_variance_le_raw_power {n p R : ℕ}
    (H : (r : Fin R) → KernelMap p (r.val + 1))
    (hsym : ∀ r (σ : Equiv.Perm (Fin (r.val + 1))) v,
      H r (fun i => v (σ i)) = H r v)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ) (hR : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    variance (LiftL2.centeredKernelExpansion 0 H (fun j ω => X j ω - m)) μ ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
        ∫ ω, H r (fun i => X
          (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ^ 2 ∂μ := by
  obtain ⟨hi, hm, hid', hlp, hzero⟩ := LiftL2.centerObservations_l2 X m
    hind hmeas hid hL2 hmean
  rw [LiftL2.centeredKernelExpansion_variance 0 H hsym _ hR hi hm hid' hlp hzero]
  apply Finset.sum_le_sum
  intro r _
  let e := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR)
  have hc := LiftL2.independent_centering_square_le_l2 μ (H r)
    (fun i => X (e i)) (fun i => hmeas (e i)) (hind.precomp e.injective)
    (fun i j => hid (e i) (e j)) (fun i a => hL2 (e i) a) m
    (fun i a => hmean (e i) a)
  have hb := LiftL2.descFactorial_lower_bound hR (Nat.succ_le_of_lt r.isLt) hΛ.le hΛn
  have hfac : 0 < ((r.val + 1).factorial : ℝ) := by positivity
  have hpow : 0 < Λ ^ (r.val + 1) := pow_pos hΛ _
  have hd := (inv_le_inv₀ (mul_pos hfac (hpow.trans_le hb)) (mul_pos hfac hpow)).2
    (mul_le_mul_of_nonneg_left hb hfac.le)
  exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans
    (mul_le_mul_of_nonneg_right hd (integral_nonneg (fun _ => sq_nonneg _)))

/-- U6's first spatial inequality: the variance of the actual integral of
centered factorial lifts is bounded by the integral-free raw kernel series.
The proof commutes actual integration with the finite lift, proves symmetry
after integration, and then contracts the centered kernel in L². -/
theorem integrated_centered_lift_variance_le_raw {n p R : ℕ}
    (H : W → (r : Fin R) → KernelMap p (r.val + 1))
    (ν : W → ℝ) (hH : ∀ r, Integrable (fun w => ν w • H w r) M)
    (hsym : ∀ w r (σ : Equiv.Perm (Fin (r.val + 1))) v,
      H w r (fun i => v (σ i)) = H w r v)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ) (hR : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    variance (fun ω => ∫ w,
      ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) μ ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
        ∫ ω, (∫ w, ν w • H w r ∂M)
          (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ^ 2 ∂μ := by
  have heq : (fun ω => ∫ w,
      ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) =
      LiftL2.centeredKernelExpansion 0 (fun r => ∫ w, ν w • H w r ∂M)
        (fun j ω => X j ω - m) := by
    funext ω
    exact centered_expansion_integral_commute _ ν H hH ω
  rw [heq]
  exact centered_expansion_variance_le_raw_power _
    (fun r => integrated_kernel_symmetric ν (fun w => H w r) (hH r)
      (fun w => hsym w r)) X m hR hind hmeas hid hL2 hmean Λ hΛ hΛn

/-- U6's second spatial inequality for actual raw kernels. Distinct spatial
blocks are checked before centering; their L² orthogonality is proved from
disjoint raw support. This gains the block mass, without bounding responses. -/
theorem integrated_centered_lift_variance_localized [IsFiniteMeasure M] {n p R q : ℕ}
    (H : W → (r : Fin R) → KernelMap p (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hH : ∀ r, Integrable (fun w => ν w • H w r) M)
    (hHmeas : ∀ r, AEStronglyMeasurable (fun w => H w r) M)
    (hsym : ∀ w r (σ : Equiv.Perm (Fin (r.val + 1))) v,
      H w r (fun i => v (σ i)) = H w r v)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ) (hR : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1)
    (b : W → Fin q) (hb : Measurable b)
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r, ∀ᵐ w ∂M,
      ‖rawKernelOperator (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR))
        X hind hmeas hL2 (H w r)‖ ≤ C r)
    (hdisjoint : ∀ r w v, b w ≠ b v → ∀ᵐ ω ∂μ,
      H w r (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) *
      H v r (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) = 0)
    (L : ℝ) (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    variance (fun ω => ∫ w,
      ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) μ ≤
      L * ∫ w, ν w ^ 2 * ∑ r : Fin R,
        (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
          ∫ ω, H w r (fun i => X
            (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ^ 2 ∂μ ∂M := by
  let e (r : Fin R) := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR)
  let K (r : Fin R) (w : W) := rawKernelOperator (e r) X hind hmeas hL2 (H w r)
  let δ (r : Fin R) := (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹
  have hKmeas (r : Fin R) : AEStronglyMeasurable (K r) M :=
    (rawKernelOperator (e r) X hind hmeas hL2).continuous.comp_aestronglyMeasurable (hHmeas r)
  have horth (r : Fin R) (w v : W) (h : b w ≠ b v) : ⟪K r w, K r v⟫ = 0 :=
    raw_kernel_operator_inner_zero (e r) X hind hmeas hL2 (H w r) (H v r) (hdisjoint r w v h)
  have hl := LocalizationL2.weighted_kernel_series_localization_bound b hb ν hν K hKmeas
    C hC hbound horth δ (fun r => by dsimp [δ]; positivity) L hL
  have hfirst := integrated_centered_lift_variance_le_raw H ν hH hsym X m hR
    hind hmeas hid hL2 hmean Λ hΛ hΛn
  have heq (r : Fin R) :
      (∫ ω, (∫ w, ν w • H w r ∂M) (fun i => X (e r i) ω) ^ 2 ∂μ) =
        ‖∫ w, ν w • K r w ∂M‖ ^ 2 := by
    rw [← raw_kernel_operator_norm_sq (e r) X hind hmeas hL2,
      raw_kernel_integral_commute (e r) X hind hmeas hL2 ν (fun w => H w r) (hH r)]
  have hfirst' : variance (fun ω => ∫ w,
      ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) μ ≤
      ∑ r : Fin R, δ r * ‖∫ w, ν w • K r w ∂M‖ ^ 2 := by
    apply hfirst.trans
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro r _
    exact congrArg (fun t => δ r * t) (heq r)
  apply hfirst'.trans
  convert hl using 1
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => by
    change ν w ^ 2 * ∑ r : Fin R,
      δ r * (∫ ω, H w r (fun i => X (e r i) ω) ^ 2 ∂μ) =
        ν w ^ 2 * ∑ r : Fin R, δ r * ‖K r w‖ ^ 2
    apply congrArg (fun t => ν w ^ 2 * t)
    apply Finset.sum_congr rfl
    intro r _
    exact congrArg (fun t => δ r * t)
      (raw_kernel_operator_norm_sq (e r) X hind hmeas hL2 (H w r)).symm)

end NearlyMinimax.FieldLiftCovariance
