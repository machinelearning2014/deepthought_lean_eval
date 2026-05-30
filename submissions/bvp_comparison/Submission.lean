import Mathlib
import Submission.Helpers

namespace Submission

open Submission.Helpers

  theorem bvp_comparison (J : Set ℝ) (hJ_open : IsOpen J) (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
      (u v : ℝ → ℝ)
      (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
      (hu' : ∀ x ∈ J, HasDerivAt (deriv u) (deriv (deriv u) x) x)
      (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x)
      (hv' : ∀ x ∈ J, HasDerivAt (deriv v) (deriv (deriv v) x) x)
      (hineq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, -deriv (deriv u) x ≤ -deriv (deriv v) x)
      (hu0 : u 0 ≤ v 0) (hu1 : u 1 ≤ v 1) :
      ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ v x := by
    set w := u - v with hw
    have hw0 : w 0 ≤ 0 := by
      dsimp [w]
      linarith
    have hw1 : w 1 ≤ 0 := by
      dsimp [w]
      linarith
    have hw_deriv : ∀ x ∈ J, HasDerivAt w (deriv u x - deriv v x) x := by
      intro x hx
      exact (hu x hx).sub (hv x hx)
    have h_deriv_w_eq : ∀ y ∈ J, deriv w y = (deriv u - deriv v) y := by
      intro y hy
      have hwy := hw_deriv y hy
      dsimp
      rw [hwy.deriv]
    have hw_deriv' : ∀ x ∈ J, HasDerivAt (deriv w) (deriv (deriv u) x - deriv (deriv v) x) x := by
      intro x hx
      have h_deriv_uv_sub : HasDerivAt (deriv u - deriv v) (deriv (deriv u) x - deriv (deriv v) x) x :=
        (hu' x hx).sub (hv' x hx)
      have hJ_mem : J ∈ nhds x := hJ_open.mem_nhds hx
      have h_deriv_w_eventually_eq : deriv w =ᶠ[nhds x] (deriv u - deriv v) := by
        filter_upwards [hJ_mem] with y hy using h_deriv_w_eq y hy
      exact h_deriv_uv_sub.congr_of_eventuallyEq h_deriv_w_eventually_eq
    have hww_nonneg : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ deriv (deriv w) x := by
      intro x hx
      have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hx)
      have hww_at_x := hw_deriv' x hxJ
      have hww_val : deriv (deriv w) x = deriv (deriv u) x - deriv (deriv v) x := hww_at_x.deriv
      rw [hww_val]
      have hineq_at_x : -deriv (deriv u) x ≤ -deriv (deriv v) x := hineq x hx
      linarith
    -- deriv w is monotone non-decreasing on [0,1]
    have h_deriv_w_mono : MonotoneOn (deriv w) (Set.Icc (0 : ℝ) 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
      · -- ContinuousOn (deriv w) (Icc 0 1)
        intro x hx
        have hxJ : x ∈ J := hJ_sub hx
        have hdiff : DifferentiableAt ℝ (deriv w) x := (hw_deriv' x hxJ).differentiableAt
        exact hdiff.continuousAt.continuousWithinAt
      · -- DifferentiableOn ℝ (deriv w) (interior (Icc 0 1))
        rw [interior_Icc]
        intro x hx
        have hxJ : x ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hx)
        have hdiff : DifferentiableAt ℝ (deriv w) x := (hw_deriv' x hxJ).differentiableAt
        exact hdiff.differentiableWithinAt
      · -- ∀ x ∈ interior (Icc 0 1), 0 ≤ deriv (deriv w) x
        rw [interior_Icc]
        exact hww_nonneg
    intro x hx
    rcases hx with ⟨hx0, hx1⟩
    by_contra! hpos
    -- hpos : u x > v x
    have hwpos : w x > 0 := by
      dsimp [w]
      linarith
    -- x cannot be 0 or 1, so x ∈ (0,1)
    have hx0_lt : (0 : ℝ) < x := by
      by_contra! hxle
      have hx_eq0 : x = 0 := le_antisymm hxle hx0
      rw [hx_eq0] at hwpos
      linarith [hw0]
    have hx_lt1 : x < 1 := by
      by_contra! hxle
      have hx_eq1 : x = 1 := le_antisymm hx1 hxle
      rw [hx_eq1] at hwpos
      linarith [hw1]
    have hx_ioo : x ∈ Set.Ioo (0 : ℝ) 1 := Set.mem_Ioo.mpr ⟨hx0_lt, hx_lt1⟩
    -- MVT on [0, x] for w
    have hw_cont_on_0x : ContinuousOn w (Set.Icc (0 : ℝ) x) := by
      intro y hy
      have hyJ : y ∈ J := hJ_sub (Set.Icc_subset_Icc_right (by linarith) hy)
      exact (hw_deriv y hyJ).continuousAt.continuousWithinAt
    have hw_diff_on_0x : DifferentiableOn ℝ w (Set.Ioo (0 : ℝ) x) := by
      intro y hy
      -- hy : y ∈ Ioo 0 x, so hy.1 : 0 < y, hy.2 : y < x
      have hy_ioo_01 : y ∈ Set.Ioo (0 : ℝ) 1 := Set.mem_Ioo.mpr ⟨hy.1, lt_of_lt_of_le hy.2 hx1⟩
      have hyJ : y ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hy_ioo_01)
      exact (hw_deriv y hyJ).differentiableAt.differentiableWithinAt
    rcases exists_deriv_eq_slope w (by linarith) hw_cont_on_0x hw_diff_on_0x with ⟨c₁, hc₁, hc₁_eq⟩
    -- hc₁ : c₁ ∈ Ioo 0 x
    -- hc₁_eq : deriv w c₁ = (w x - w 0) / (x - 0)
    have hc₁_mem : c₁ ∈ Set.Icc (0 : ℝ) 1 := by
      have hc₁_ge_0 : (0 : ℝ) ≤ c₁ := le_of_lt hc₁.1
      have hc₁_le_1 : c₁ ≤ 1 := le_of_lt (lt_of_lt_of_le hc₁.2 hx1)
      exact Set.mem_Icc.mpr ⟨hc₁_ge_0, hc₁_le_1⟩
    have hderiv_c1_pos : deriv w c₁ > 0 := by
      have hnum : w x - w 0 > 0 := by
        linarith
      have hden : x - 0 > 0 := by linarith
      rw [hc₁_eq]
      exact div_pos hnum hden
    -- MVT on [x, 1] for w
    have hw_cont_on_x1 : ContinuousOn w (Set.Icc x 1) := by
      intro y hy
      have hyJ : y ∈ J := hJ_sub (Set.Icc_subset_Icc_left (by linarith) hy)
      exact (hw_deriv y hyJ).continuousAt.continuousWithinAt
    have hw_diff_on_x1 : DifferentiableOn ℝ w (Set.Ioo x 1) := by
      intro y hy
      -- hy : y ∈ Ioo x 1, so hy.1 : x < y, hy.2 : y < 1
      have hy_ioo_01 : y ∈ Set.Ioo (0 : ℝ) 1 := Set.mem_Ioo.mpr ⟨hx0_lt.trans hy.1, hy.2⟩
      have hyJ : y ∈ J := hJ_sub (Set.Ioo_subset_Icc_self hy_ioo_01)
      exact (hw_deriv y hyJ).differentiableAt.differentiableWithinAt
    rcases exists_deriv_eq_slope w (by linarith) hw_cont_on_x1 hw_diff_on_x1 with ⟨c₂, hc₂, hc₂_eq⟩
    -- hc₂ : c₂ ∈ Ioo x 1
    -- hc₂_eq : deriv w c₂ = (w 1 - w x) / (1 - x)
    have hc₂_mem : c₂ ∈ Set.Icc (0 : ℝ) 1 := by
      have hc₂_ge_0 : (0 : ℝ) ≤ c₂ := le_of_lt (hx0_lt.trans hc₂.1)
      have hc₂_le_1 : c₂ ≤ 1 := le_of_lt hc₂.2
      exact Set.mem_Icc.mpr ⟨hc₂_ge_0, hc₂_le_1⟩
    have hderiv_c2_neg : deriv w c₂ < 0 := by
      have hnum : w 1 - w x < 0 := by
        linarith
      have hden : 1 - x > 0 := by linarith
      rw [hc₂_eq]
      exact div_neg_of_neg_of_pos hnum hden
    -- Since deriv w is monotone on [0,1] and c₁ < c₂, we have deriv w c₁ ≤ deriv w c₂
    have h_c1_lt_c2 : c₁ < c₂ := by
      have hc1_x : c₁ < x := hc₁.2
      have hx_c2 : x < c₂ := hc₂.1
      linarith
    have h_deriv_mono : deriv w c₁ ≤ deriv w c₂ :=
      h_deriv_w_mono hc₁_mem hc₂_mem (by linarith)
    -- This gives 0 < deriv w c₁ ≤ deriv w c₂ < 0, a contradiction
    linarith

end Submission
