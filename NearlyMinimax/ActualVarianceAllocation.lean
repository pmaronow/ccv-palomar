module

public import NearlyMinimax.AllocationBounds
public import NearlyMinimax.DegreeBounds


@[expose] public section

/-!
# Scalar factorial variance allocation for the actual quadratic profile

The coarse/fine bounds below derive their degree conditions from the profile
and degree floor. No factorial-series inequality is an input hypothesis.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace NearlyMinimax

def profileVarianceArgument (C_D S z : ℝ) : ℝ := Real.exp z / (C_D * S)

def profileVarianceDegree (β S z : ℝ) : ℕ := Nat.floor (β * quadraticProfile S z)

def profileVarianceWeight (C₀ C_D β S z : ℝ) : ℝ :=
  factorialSeries (profileVarianceDegree β S z) (profileVarianceArgument C_D S z) *
    max 1 (C₀ / profileVarianceArgument C_D S z)

theorem profileVariance_coarse_ratio {β C_D S z : ℝ}
    (hβ : 0 ≤ β) (hD1 : 1 ≤ C_D) (hDβ : 4 * β ≤ C_D) (hS : 2 ≤ S) (hz : z ≤ 0) :
    (profileVarianceDegree β S z : ℝ) * profileVarianceArgument C_D S z ≤ 1 / 2 := by
  have hS₀ : 0 < S := by linarith
  have hD₀ : 0 < C_D := by linarith
  have hCS : 0 < C_D * S := mul_pos hD₀ hS₀
  have hQ : 0 ≤ quadraticProfile S z :=
    (by positivity : (0 : ℝ) ≤ S / 4).trans (quadraticProfile_lower hS₀)
  have hf := Nat.floor_le (mul_nonneg hβ hQ)
  have hfe := mul_le_mul_of_nonneg_right hf (Real.exp_pos z).le
  have hc := mul_le_mul_of_nonneg_left (quadraticProfile_coarse_bound hS hz) hβ
  have hDm := mul_le_mul_of_nonneg_right hDβ hS₀.le
  unfold profileVarianceDegree profileVarianceArgument
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hCS).2
  nlinarith [mul_nonneg hβ hS₀.le]

theorem profileVariance_fine_degree_bounds {β C_D S z : ℝ}
    (hβ : 0 ≤ β) (hDβ : 4 * β ≤ C_D) (hS : 0 < S) (hz0 : 0 ≤ z) (hzS : z ≤ S) :
    (profileVarianceDegree β S z : ℝ) ≤ C_D * S ∧
      (profileVarianceDegree β S z : ℝ) * z ≤ β * S ^ 2 / 4 := by
  have hQ : 0 ≤ quadraticProfile S z :=
    (by positivity : (0 : ℝ) ≤ S / 4).trans (quadraticProfile_lower hS)
  have hf := Nat.floor_le (mul_nonneg hβ hQ)
  have hu := mul_le_mul_of_nonneg_left (quadraticProfile_fine_upper hS hz0 hzS) hβ
  have hv := mul_le_mul_of_nonneg_left (quadraticProfile_fine_bound (z := z) hS hzS) hβ
  have hDm := mul_le_mul_of_nonneg_right hDβ hS.le
  unfold profileVarianceDegree
  constructor
  · nlinarith [mul_nonneg hβ hS.le]
  · have hfm := mul_le_mul_of_nonneg_right hf hz0
    nlinarith

theorem profileVarianceWeight_coarse_bound {C₀ C_D β S z : ℝ}
    (hC : 1 ≤ C₀) (hD1 : 1 ≤ C_D) (hDβ : 4 * β ≤ C_D)
    (hβ : 0 ≤ β) (hS : 2 ≤ S) (hz : z ≤ 0) :
    profileVarianceWeight C₀ C_D β S z ≤ 2 * C₀ := by
  have hC₀ : 0 < C₀ := by linarith
  have hS₀ : 0 < S := by linarith
  have hD₀ : 0 < C_D := by linarith
  have hCS : 0 < C_D * S := mul_pos hD₀ hS₀
  have hCS1 : 1 ≤ C_D * S := by nlinarith
  have hx : 0 < profileVarianceArgument C_D S z := div_pos (Real.exp_pos z) hCS
  have hxC : profileVarianceArgument C_D S z ≤ C₀ := by
    have he : Real.exp z ≤ 1 := Real.exp_le_one_iff.2 hz
    have hx1 : profileVarianceArgument C_D S z ≤ 1 := (div_le_one hCS).2 (he.trans hCS1)
    exact hx1.trans hC
  have hm : 1 ≤ C₀ / profileVarianceArgument C_D S z :=
    (le_div_iff₀ hx).2 (by simpa using hxC)
  have hs := factorialSeries_coarse_bound hx.le
    (profileVariance_coarse_ratio hβ hD1 hDβ hS hz)
  unfold profileVarianceWeight
  rw [max_eq_right hm]
  calc
    _ ≤ (2 * profileVarianceArgument C_D S z) * (C₀ / profileVarianceArgument C_D S z) :=
      mul_le_mul_of_nonneg_right hs (div_nonneg hC₀.le hx.le)
    _ = 2 * C₀ := by field_simp

theorem profileVarianceWeight_fine_bound {C₀ C_D β S z : ℝ}
    (hC : 1 ≤ C₀) (hD1 : 1 ≤ C_D) (hDβ : 4 * β ≤ C_D)
    (hβ : 0 ≤ β) (hS : 2 ≤ S) (hz0 : 0 ≤ z) (hzS : z ≤ S) :
    profileVarianceWeight C₀ C_D β S z ≤
      C₀ * C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by
  have hC₀ : 0 < C₀ := by linarith
  have hS₀ : 0 < S := by linarith
  have hD₀ : 0 < C_D := by linarith
  have hCS : 0 < C_D * S := mul_pos hD₀ hS₀
  have hCS1 : 1 ≤ C_D * S := by nlinarith
  have hx : 0 < profileVarianceArgument C_D S z := div_pos (Real.exp_pos z) hCS
  obtain ⟨hdeg, hprod⟩ := profileVariance_fine_degree_bounds hβ hDβ hS₀ hz0 hzS
  have he : (C_D * S) * profileVarianceArgument C_D S z = Real.exp z := by
    unfold profileVarianceArgument
    rw [← mul_div_assoc, mul_comm (C_D * S), mul_div_cancel_right₀ _ hCS.ne']
  have hweight : max 1 (C₀ / profileVarianceArgument C_D S z) ≤ C₀ * C_D * S := by
    apply max_le
    · nlinarith
    · apply (div_le_iff₀ hx).2
      have hm := mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.2 hz0) hC₀.le
      calc
        C₀ ≤ C₀ * Real.exp z := by simpa using hm
        _ = (C₀ * C_D * S) * profileVarianceArgument C_D S z := by rw [← he]; ring
  unfold profileVarianceWeight profileVarianceArgument
  exact factorialSeries_fine_weighted hz0 hC₀.le hCS hdeg hprod
    (by positivity) hweight

/-- Both coarse and fine levels obey the same explicit envelope. -/
theorem profileVarianceWeight_uniform_bound {C₀ C_D β S z : ℝ}
    (hC : 1 ≤ C₀) (hD1 : 1 ≤ C_D) (hDβ : 4 * β ≤ C_D)
    (hβ : 0 ≤ β) (hS : 2 ≤ S) (hz : z ≤ S) :
    profileVarianceWeight C₀ C_D β S z ≤
      2 * C₀ * C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by
  have hS₀ : 0 < S := by linarith
  have hC₀ : 0 < C₀ := by linarith
  have hD₀ : 0 < C_D := by linarith
  have hCS1 : 1 ≤ C_D * S := by nlinarith
  have hsq : 1 ≤ C_D ^ 2 * S ^ 2 := by nlinarith [sq_nonneg (C_D * S - 1)]
  have hexp : 1 ≤ Real.exp (β * S ^ 2 / 4) := Real.one_le_exp_iff.2 (by positivity)
  have hfactor : 1 ≤ C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by nlinarith
  rcases le_or_gt z 0 with hz0 | hz0
  · apply (profileVarianceWeight_coarse_bound hC hD1 hDβ hβ hS hz0).trans
    have hm := mul_le_mul_of_nonneg_left hfactor (by positivity : 0 ≤ 2 * C₀)
    simpa only [mul_one, mul_assoc] using hm
  · apply (profileVarianceWeight_fine_bound hC hD1 hDβ hβ hS hz0.le hz).trans
    have hn : 0 ≤ C₀ * C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by positivity
    nlinarith

/-- In the explicit candidate allocation, the normalized variance argument is exactly `C₀ K_j/n`. -/
theorem actual_profileVarianceArgument_eq_cell_fraction {δ a C C₀ C_D x : ℝ} (j : ℕ)
    (hC : 0 < C₀) (hD : 0 < C_D) (hx : 0 < x) (hS : 0 < allocationWidth a C x) :
    profileVarianceArgument C_D (allocationWidth a C x)
      (allocationLevelPosition δ a C (C₀ * C_D) x j) = C₀ * Real.exp (δ * (j : ℝ)) / x := by
  unfold profileVarianceArgument allocationLevelPosition
  rw [Real.exp_add, Real.exp_sub, Real.exp_log hx,
    Real.exp_log (mul_pos (mul_pos hC hD) hS)]
  field_simp

/-- The sampling weight in the explicit allocation is exactly `max{1,n/K_j}`. -/
theorem actual_profileVarianceWeight_eq_cell_weight {δ a C C₀ C_D β x : ℝ} (j : ℕ)
    (hC : 0 < C₀) (hD : 0 < C_D) (hx : 0 < x) (hS : 0 < allocationWidth a C x) :
    profileVarianceWeight C₀ C_D β (allocationWidth a C x)
      (allocationLevelPosition δ a C (C₀ * C_D) x j) =
        factorialSeries (profileVarianceDegree β (allocationWidth a C x)
          (allocationLevelPosition δ a C (C₀ * C_D) x j))
          (C₀ * Real.exp (δ * (j : ℝ)) / x) * max 1 (x / Real.exp (δ * (j : ℝ))) := by
  unfold profileVarianceWeight
  rw [actual_profileVarianceArgument_eq_cell_fraction j hC hD hx hS]
  congr 2
  field_simp

/-- The paper's maximum weighted factorial variance, over all explicit candidate levels. -/
def actualVarianceMaximum (δ a C C₀ C_D γ β x : ℝ) : ℝ :=
  (Finset.range (terminalAllocationLevel δ a C (C₀ * C_D) γ x + 1)).sup'
    ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (fun j =>
      profileVarianceWeight C₀ C_D β (allocationWidth a C x)
        (allocationLevelPosition δ a C (C₀ * C_D) x j))

theorem actualVarianceMaximum_nonneg {δ a C C₀ C_D γ β x : ℝ}
    (hD : 0 < C_D) (hS : 0 < allocationWidth a C x) :
    0 ≤ actualVarianceMaximum δ a C C₀ C_D γ β x := by
  have hw : 0 ≤ profileVarianceWeight C₀ C_D β (allocationWidth a C x)
      (allocationLevelPosition δ a C (C₀ * C_D) x 0) := by
    unfold profileVarianceWeight
    apply mul_nonneg
    · apply factorialSeries_nonneg
      unfold profileVarianceArgument
      positivity
    · exact zero_le_one.trans (le_max_left _ _)
  apply hw.trans
  unfold actualVarianceMaximum
  exact Finset.le_sup' (s := Finset.range (terminalAllocationLevel δ a C (C₀ * C_D) γ x + 1))
    (b := 0) (fun j : ℕ => profileVarianceWeight C₀ C_D β (allocationWidth a C x)
      (allocationLevelPosition δ a C (C₀ * C_D) x j)) (Finset.mem_range.2 (Nat.succ_pos _))

/-- The actual maximum variance has the proved fine-level envelope eventually. -/
theorem eventually_actualVarianceMaximum_bound {δ a C₀ C_D γ β : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hC : 1 ≤ C₀) (hD1 : 1 ≤ C_D)
    (hDβ : 4 * β ≤ C_D) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      actualVarianceMaximum δ a C C₀ C_D γ β x ≤
        2 * C₀ * C_D ^ 2 * (allocationWidth a C x) ^ 2 *
          Real.exp (β * (allocationWidth a C x) ^ 2 / 4) := by
  have hH : 0 < C₀ * C_D := by positivity
  filter_upwards [(allocationWidth_tendsto_atTop ha C).eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_actual_allocation_level_range hδ ha hH hγ C] with x hx hz
  unfold actualVarianceMaximum
  apply Finset.sup'_le
  intro j hj
  exact profileVarianceWeight_uniform_bound hC hD1 hDβ hβ hx (hz j hj).2

/-- The scalar spatial reserve multiplied by the actual maximum factorial variance. -/
def actualAllocationVarianceRatio (δ a C C₀ C_D γ β η varpi x : ℝ) : ℝ :=
  Real.exp (-2 * varpi * Real.log x + η *
    roundedTerminalDepth δ (Real.log x) (candidateTerminalDepth a C (C₀ * C_D) γ x)) *
      actualVarianceMaximum δ a C C₀ C_D γ β x

set_option maxHeartbeats 600000 in
/-- The actual scalar variance ratio has an explicit exponentially vanishing reserve. -/
theorem eventually_actualAllocationVarianceRatio_bound {δ a C₀ C_D γ β η varpi : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hC : 1 ≤ C₀) (hD1 : 1 ≤ C_D)
    (hDβ : 4 * β ≤ C_D) (hβ : 0 < β) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (C : ℝ) (hshift : C = 1 + 2 * (η + 2) / β) (hcoef : β * a ^ 2 / 4 = 2 * varpi) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ actualAllocationVarianceRatio δ a C C₀ C_D γ β η varpi x ∧
      actualAllocationVarianceRatio δ a C C₀ C_D γ β η varpi x ≤
        2 * C₀ * C_D ^ 2 * (allocationWidth a C x) ^ 2 * Real.exp (-2 * allocationWidth a C x) := by
  have hH : 0 < C₀ * C_D := by positivity
  have hD : 0 < C_D := by linarith
  have hw := allocationWidth_tendsto_atTop ha C
  filter_upwards [hw.eventually (eventually_ge_atTop (2 : ℝ)),
    (hw.const_mul_atTop hH).eventually (eventually_ge_atTop (1 : ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_terminal_cell_log_nonneg ha hH C γ,
    eventually_actualVarianceMaximum_bound hδ ha hC hD1 hDβ hβ.le hγ C]
    with x hS hHS hL hLT hmax
  have hS₀ : 0 < allocationWidth a C x := by linarith
  have hn : 0 ≤ actualVarianceMaximum δ a C C₀ C_D γ β x :=
    actualVarianceMaximum_nonneg (δ := δ) (a := a) (C := C) (C₀ := C₀)
      (C_D := C_D) (γ := γ) (β := β) (x := x) hD hS₀
  have hdef : allocationWidth a C x =
      a * Real.sqrt (Real.log x) - (1 + 2 * (η + 2) / β) := by unfold allocationWidth; rw [hshift]
  have hbudget := quadratic_allocation_budget hβ (by linarith : 0 ≤ η + 2) hS₀.le hdef
  have hbase : β * (a * Real.sqrt (Real.log x)) ^ 2 / 4 = 2 * varpi * Real.log x := by
    rw [mul_pow, Real.sq_sqrt hL]
    calc
      β * (a ^ 2 * Real.log x) / 4 = (β * a ^ 2 / 4) * Real.log x := by ring
      _ = _ := by rw [hcoef]
  rw [hbase] at hbudget
  have ht := (roundedTerminalDepth_bounds hδ hLT).2
  have hcand : candidateTerminalDepth a C (C₀ * C_D) γ x ≤ allocationWidth a C x := by
    unfold candidateTerminalDepth
    have hell : 0 ≤ Real.log ((C₀ * C_D) * allocationWidth a C x) := Real.log_nonneg hHS
    have hlogS : 0 ≤ Real.log (allocationWidth a C x) := Real.log_nonneg (by linarith)
    linarith [mul_nonneg hγ hlogS]
  have hr : Real.exp (-2 * varpi * Real.log x + η *
      roundedTerminalDepth δ (Real.log x) (candidateTerminalDepth a C (C₀ * C_D) γ x)) ≤
      Real.exp (-β * (allocationWidth a C x) ^ 2 / 4 - 2 * allocationWidth a C x) :=
    allocation_budget_reserve (β := β) (S := allocationWidth a C x)
      (η := η) (varpi := varpi) (L := Real.log x)
      (T := roundedTerminalDepth δ (Real.log x) (candidateTerminalDepth a C (C₀ * C_D) γ x))
      hbudget hη (ht.trans hcand)
  constructor
  · unfold actualAllocationVarianceRatio
    exact mul_nonneg (Real.exp_pos _).le hn
  · unfold actualAllocationVarianceRatio
    calc
      _ ≤ Real.exp (-β * (allocationWidth a C x) ^ 2 / 4 - 2 * allocationWidth a C x) *
          (2 * C₀ * C_D ^ 2 * (allocationWidth a C x) ^ 2 *
            Real.exp (β * (allocationWidth a C x) ^ 2 / 4)) :=
        mul_le_mul hr hmax hn (Real.exp_pos _).le
      _ = (2 * C₀ * C_D ^ 2 * (allocationWidth a C x) ^ 2) *
          (Real.exp (-β * (allocationWidth a C x) ^ 2 / 4 - 2 * allocationWidth a C x) *
            Real.exp (β * (allocationWidth a C x) ^ 2 / 4)) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring

/-- Consequently `W≤1` eventually follows for this actual scalar allocation, rather than being assumed. -/
theorem actualAllocationVarianceRatio_tends_zero {δ a C₀ C_D γ β η varpi : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hC : 1 ≤ C₀) (hD1 : 1 ≤ C_D)
    (hDβ : 4 * β ≤ C_D) (hβ : 0 < β) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (C : ℝ) (hshift : C = 1 + 2 * (η + 2) / β) (hcoef : β * a ^ 2 / 4 = 2 * varpi) :
    Tendsto (actualAllocationVarianceRatio δ a C C₀ C_D γ β η varpi) atTop (𝓝 0) := by
  have hb := eventually_actualAllocationVarianceRatio_bound hδ ha hC hD1 hDβ hβ hγ hη C hshift hcoef
  apply squeeze_zero' (hb.mono fun x hx => hx.1) (hb.mono fun x hx => hx.2)
  exact (tendsto_allocation_reserve_bound C₀ C_D).comp (allocationWidth_tendsto_atTop ha C)

end NearlyMinimax
