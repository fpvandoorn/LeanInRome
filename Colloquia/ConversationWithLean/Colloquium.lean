import Mathlib.Analysis.Complex.CauchyIntegral
set_option autoImplicit false
set_option linter.unusedVariables false
open TopologicalSpace Set Metric Filter Complex
open scoped Interval Real NNReal ENNReal Topology BigOperators



/- # Three examples

*** Cauchy integral formula: if `f` is continuous on a closed disc of radius `R` and center `c`, ***
*** is differentiable at all points of the interior of this disc, then the integral ***
*** `∮ z in C(c, R), f z / (z - c) dz` is equal to `2πi ⬝ f(c)`. ***-/
theorem Cauchy_formula {c : ℂ} {R : ℝ} (h0 : 0 < R) -- __the disk of radius `R` around `c`__
    {f : ℂ → ℂ}
    (hf : ContinuousOn f (closedBall c R))
    (hdiff : ∀ z ∈ (ball c R ), DifferentiableAt ℂ f z) : -- *** `:` here means _then_ ***
    (∮ z in C(c, R), (z - c)⁻¹ • f z) = (2 * π * I) • (f c) := by
-- __Here starts the proof__
  let y := f c
  have hy : Tendsto f (𝓝 c) (𝓝 y) := by
    rw [← (@nhdsWithin_eq_nhds _ _ c (closedBall c R)).mpr (closedBall_mem_nhds _ h0)]
    exact ContinuousOn.continuousWithinAt hf <| mem_closedBall_self (le_of_lt h0)
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine' le_of_forall_le_of_dense fun ε ε0 => _
  obtain ⟨α, α0, hα⟩ := (nhds_basis_ball.tendsto_iff (nhds_basis_ball)).1 hy _
    (div_pos ε0 Real.two_pi_pos)
  set δ := α/2
  have δ0 := half_pos α0
  have hδ := fun z hz => hα z ((@closedBall_subset_ball ℂ _ c (α/2) α (by linarith)) hz)
-- *** So far (↑), we have reduced the problem to showing that the difference is arbitrarily small***
  obtain ⟨r, hr0, hrδ, hrR⟩ : ∃ r, 0 < r ∧ r ≤ δ ∧ r ≤ R :=
    ⟨min δ R, lt_min δ0 h0, min_le_left _ _, min_le_right _ _⟩
  have hsub : closedBall c R \ ball c r ⊆ closedBall c R :=  diff_subset (closedBall c R) (ball c r)
  have hsub' : ball c R \ closedBall c r ⊆ ball c R \ {c} :=
    diff_subset_diff_right (singleton_subset_iff.2 <| mem_closedBall_self hr0.le)
  have hzne : ∀ z ∈ sphere c r, z ≠ c := fun z hz =>
    ne_of_mem_of_not_mem hz fun h => hr0.ne' <| dist_self c ▸ Eq.symm h
-- ***  Now (↓) we compute that the integral `∮ z in C(c, r), f z / (z - c)` does not depend on ***
-- ***  `0 < r ≤ R` and tends to `2πIy` as `r → 0`. ***
  calc
    ‖(∮ z in C(c, R), (z - c)⁻¹ • f z) - (2 * ↑π * I) • y‖ =
        ‖(∮ z in C(c, r), (z - c)⁻¹ • f z) - ∮ z in C(c, r), (z - c)⁻¹ • y‖ := by
-- *** First (in)equality (↑), proven below***
      congr 2
      · refine circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable hr0
          hrR countable_empty /- countable_s -/ (hf.mono hsub) fun z hz => hdiff z ?_
        · apply mem_of_subset_of_mem _ hz
          rw [diff_empty]
          -- apply diff_subset_diff_left
          exact diff_subset (ball c R) (closedBall c r)
      · simp only [circleIntegral.integral_smul_const, ne_eq, hr0.ne', not_false_eq_true,
          circleIntegral.integral_sub_center_inv]
    _ = ‖∮ z in C(c, r), (z - c)⁻¹ • (f z - y)‖ := by
-- *** Second (in)equality (↑), proven below ***
      simp only [smul_sub]
      have hc' : ContinuousOn (fun z => (z - c)⁻¹) (sphere c r) :=
        (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => sub_ne_zero.2 <| hzne _ hz
      rw [circleIntegral.integral_sub] <;> refine' (hc'.smul _).circleIntegrable hr0.le
      · exact hf.mono <| (sphere_subset_closedBall).trans (closedBall_subset_closedBall hrR)
      · exact continuousOn_const
    _ ≤ 2 * π * r * (r⁻¹ * (ε / (2 * π))) := by
-- *** Third inequality (↑), proven below***
      refine' circleIntegral.norm_integral_le_of_norm_le_const hr0.le fun z hz => _
      specialize hzne z hz
      rw [mem_sphere, dist_eq_norm] at hz
      rw [norm_smul, norm_inv, hz, ← dist_eq_norm]
      refine' mul_le_mul_of_nonneg_left (le_of_lt <| hδ _ _) (inv_nonneg.2 hr0.le)
      rwa [mem_closedBall_iff_norm, hz]
    _ = ε := by
-- *** Final (in)equality (↑)***
      field_simp [hr0.ne', Real.two_pi_pos.ne']
      ac_rfl

-- #lint
-- ## Something easier but whose proof we can follow


-- *** The sum of two odd integers is even... ***
theorem Odd_Odd_Even (n m : ℕ) (hn : Odd n) (hm : Odd m) : Even (n + m) := by sorry






/-*** ... and the composition `g ∘ f` of two continuous functions `f : X → Y` and `g : Y → Z` ***
  __is continuous.__ -/
