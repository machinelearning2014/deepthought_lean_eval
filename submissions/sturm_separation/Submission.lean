import Mathlib
import Submission.Helpers

namespace Submission

open Submission.Helpers

  theorem sturm_separation (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
      (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
      (hJ_sub : Set.Icc a b ⊆ J)
      (hp : ContinuousOn p J) (hq : ContinuousOn q J)
      (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
      (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
      (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
      (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
      (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
      (hza : y₁ a = 0) (hzb : y₁ b = 0)
      (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
      ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
    have haJ : a ∈ J := hJ_sub (Set.left_mem_Icc.mpr (by linarith))
    have hbJ : b ∈ J := hJ_sub (Set.right_mem_Icc.mpr (by linarith))
    have hW_nonzero : ∀ x ∈ J, W y₁ y₂ x ≠ 0 := by
      rcases hW with ⟨x₀, hx₀J, hx₀W⟩
      by_contra! h
      rcases h with ⟨x, hxJ, hxW⟩
      have hzero : ∀ x ∈ J, W y₁ y₂ x = 0 :=
        wronskian_zero_of_point p q y₁ y₂ J hJ_open hJ_conn hp hq hy₁ hy₁' hy₂ hy₂' x hxJ hxW
      have : W y₁ y₂ x₀ = 0 := hzero x₀ hx₀J
      exact hx₀W this
    have hWa_nonzero : W y₁ y₂ a ≠ 0 := hW_nonzero a haJ
    have hWb_nonzero : W y₁ y₂ b ≠ 0 := hW_nonzero b hbJ
    have hy₁_cont_ioo : ∀ x ∈ Set.Ioo a b, ContinuousAt y₁ x := by
      intro x hx
      have hxJ : x ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hx)
      exact (hy₁ x hxJ).continuousAt
    rcases constant_sign_nonzero_cont y₁ a b hab hne hy₁_cont_ioo with (hy₁_pos | hy₁_neg)
    · -- y₁(x) > 0 for all x ∈ (a,b)
      have hy₂a_nonzero : y₂ a ≠ 0 := by
        intro h
        have : W y₁ y₂ a = 0 := by
          unfold W; simp [hza, h]
        exact hWa_nonzero this
      have hy₂b_nonzero : y₂ b ≠ 0 := by
        intro h
        have : W y₁ y₂ b = 0 := by
          unfold W; simp [hzb, h]
        exact hWb_nonzero this
      set r := (b - a) / 2 with hr_def
      have hr_pos : r > 0 := by nlinarith
      have h_pos_near_a : ∀ x ∈ Set.Ioo a (a + r), y₁ x > 0 := by
        intro x hx
        rcases hx with ⟨hx1, hx2⟩
        have : x ∈ Set.Ioo a b := ⟨hx1, by dsimp [r] at hx2; nlinarith⟩
        exact hy₁_pos x this
      have h_pos_near_b : ∀ x ∈ Set.Ioo (b - r) b, y₁ x > 0 := by
        intro x hx
        rcases hx with ⟨hx1, hx2⟩
        have : x ∈ Set.Ioo a b := ⟨by dsimp [r] at hx1; nlinarith, hx2⟩
        exact hy₁_pos x this
      have hy₁_deriv_a_nonneg : 0 ≤ deriv y₁ a :=
        deriv_nonneg_of_pos_on_interval y₁ hr_pos h_pos_near_a hza (hy₁ a haJ)
      have hy₁_deriv_a_pos : 0 < deriv y₁ a := by
        by_contra! h
        have : deriv y₁ a = 0 := by linarith
        have : W y₁ y₂ a = 0 := by
          unfold W; rw [hza, this]; simp
        exact hWa_nonzero this
      have hy₁_deriv_b_nonpos : deriv y₁ b ≤ 0 :=
        deriv_nonpos_of_pos_on_interval y₁ hr_pos h_pos_near_b hzb (hy₁ b hbJ)
      have hy₁_deriv_b_neg : deriv y₁ b < 0 := by
        by_contra! h
        have : deriv y₁ b = 0 := by linarith
        have : W y₁ y₂ b = 0 := by
          unfold W; rw [hzb, this]; simp
        exact hWb_nonzero this
      have hW_cont_ioo : ∀ x ∈ Set.Ioo a b, ContinuousAt (W y₁ y₂) x := by
        intro x hx
        have hxJ : x ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hx)
        have hderiv := wronskian_deriv p q y₁ y₂ x (hy₁ x hxJ) (hy₁' x hxJ) (hy₂ x hxJ) (hy₂' x hxJ)
        exact hderiv.continuousAt
      have hW_nonzero_ioo : ∀ x ∈ Set.Ioo a b, W y₁ y₂ x ≠ 0 := by
        intro x hx
        exact hW_nonzero x (hJ_sub (Set.mem_Icc_of_Ioo hx))
      have hW_cont_cc : ContinuousOn (W y₁ y₂) (Set.Icc a b) := by
        intro x hx
        have hxJ : x ∈ J := hJ_sub hx
        have hderiv := wronskian_deriv p q y₁ y₂ x (hy₁ x hxJ) (hy₁' x hxJ) (hy₂ x hxJ) (hy₂' x hxJ)
        exact hderiv.continuousAt.continuousWithinAt
      rcases constant_sign_nonzero_cont (W y₁ y₂) a b hab hW_nonzero_ioo hW_cont_ioo with (hW_pos | hW_neg)
      · -- W > 0 on (a,b). Then y₂(a) < 0 and y₂(b) > 0
        have hWa_pos : W y₁ y₂ a > 0 := pos_at_endpoint (W y₁ y₂) hab hW_pos hW_cont_cc hWa_nonzero
        have hWb_pos : W y₁ y₂ b > 0 := pos_at_endpoint' (W y₁ y₂) hab hW_pos hW_cont_cc hWb_nonzero
        have hy₂a_neg : y₂ a < 0 := by
          have hWa_eq : W y₁ y₂ a = -(y₂ a) * deriv y₁ a := by
            unfold W; rw [hza]; ring
          rw [hWa_eq] at hWa_pos
          nlinarith
        have hy₂b_pos : y₂ b > 0 := by
          have hWb_eq : W y₁ y₂ b = -(y₂ b) * deriv y₁ b := by
            unfold W; rw [hzb]; ring
          rw [hWb_eq] at hWb_pos
          nlinarith
        have h_exists : ∃ c ∈ Set.Ioo a b, y₂ c = 0 := by
          have h_cont_y₂ : ContinuousOn y₂ (Set.Icc a b) := by
            intro x hx
            have hxJ : x ∈ J := hJ_sub hx
            exact (hy₂ x hxJ).continuousAt.continuousWithinAt
          have h0_in : (0 : ℝ) ∈ Set.Ioo (y₂ a) (y₂ b) := ⟨hy₂a_neg, hy₂b_pos⟩
          have h_IVT : (0 : ℝ) ∈ y₂ '' Set.Ioo a b :=
            intermediate_value_Ioo (by nlinarith : a ≤ b) h_cont_y₂ h0_in
          rcases h_IVT with ⟨c, hc, hc_eq⟩
          exact ⟨c, hc, hc_eq⟩
        -- Uniqueness: the quotient y₂/y₁ is strictly monotone on (a,b), hence injective
        have h_unique : ∀ (c₁ c₂ : ℝ), c₁ ∈ Set.Ioo a b → y₂ c₁ = 0 → c₂ ∈ Set.Ioo a b → y₂ c₂ = 0 → c₁ = c₂ := by
          intro u v hu hu_eq hv hv_eq
          by_cases hlt : u < v
          · exfalso
            have h_cont_r : ContinuousOn (fun x => y₂ x / y₁ x) (Set.Icc u v) := by
              intro x hx
              rcases hx with ⟨hx1, hx2⟩
              have hx_ioo : x ∈ Set.Ioo a b := by
                rcases hu with ⟨hua, hub⟩
                rcases hv with ⟨hva, hvb⟩
                refine ⟨by nlinarith, by nlinarith⟩
              have hxJ : x ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hx_ioo)
              have hy₁x_ne_zero : y₁ x ≠ 0 := hne x hx_ioo
              have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ x / (y₁ x)^2) x :=
                HasDerivAt.div (hy₂ x hxJ) (hy₁ x hxJ) hy₁x_ne_zero
              exact h_deriv_quot.continuousAt.continuousWithinAt
            have h_eq : (fun x => y₂ x / y₁ x) u = (fun x => y₂ x / y₁ x) v := by
              simp [hu_eq, hv_eq]
            have h_rolle : ∃ ξ ∈ Set.Ioo u v, deriv (fun x => y₂ x / y₁ x) ξ = 0 :=
              exists_deriv_eq_zero hlt h_cont_r h_eq
            rcases h_rolle with ⟨ξ, hξ, hξ_eq⟩
            have hξ_ioo : ξ ∈ Set.Ioo a b := by
              rcases hξ with ⟨hξ1, hξ2⟩
              rcases hu with ⟨hua, hub⟩
              rcases hv with ⟨hva, hvb⟩
              refine ⟨by nlinarith, by nlinarith⟩
            have hWξ_nonzero : W y₁ y₂ ξ ≠ 0 := hW_nonzero_ioo ξ hξ_ioo
            have hy₁ξ_pos : y₁ ξ > 0 := hy₁_pos ξ hξ_ioo
            have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ ξ / (y₁ ξ)^2) ξ := by
              have hxJ : ξ ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hξ_ioo)
              have hy₁ξ_ne_zero : y₁ ξ ≠ 0 := hne ξ hξ_ioo
              exact HasDerivAt.div (hy₂ ξ hxJ) (hy₁ ξ hxJ) hy₁ξ_ne_zero
            have h_deriv_nonzero : deriv (fun x' => y₂ x' / y₁ x') ξ ≠ 0 := by
              rw [h_deriv_quot.deriv]
              refine div_ne_zero hWξ_nonzero (by positivity)
            exact h_deriv_nonzero hξ_eq
          · by_cases hlt2 : v < u
            · exfalso
              have h_cont_r : ContinuousOn (fun x => y₂ x / y₁ x) (Set.Icc v u) := by
                intro x hx
                rcases hx with ⟨hx1, hx2⟩
                have hx_ioo : x ∈ Set.Ioo a b := by
                  rcases hu with ⟨hua, hub⟩
                  rcases hv with ⟨hva, hvb⟩
                  refine ⟨by nlinarith, by nlinarith⟩
                have hxJ : x ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hx_ioo)
                have hy₁x_ne_zero : y₁ x ≠ 0 := hne x hx_ioo
                have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ x / (y₁ x)^2) x :=
                  HasDerivAt.div (hy₂ x hxJ) (hy₁ x hxJ) hy₁x_ne_zero
                exact h_deriv_quot.continuousAt.continuousWithinAt
              have h_eq : (fun x => y₂ x / y₁ x) v = (fun x => y₂ x / y₁ x) u := by
                simp [hu_eq, hv_eq]
              have h_rolle : ∃ ξ ∈ Set.Ioo v u, deriv (fun x => y₂ x / y₁ x) ξ = 0 :=
                exists_deriv_eq_zero hlt2 h_cont_r h_eq
              rcases h_rolle with ⟨ξ, hξ, hξ_eq⟩
              have hξ_ioo : ξ ∈ Set.Ioo a b := by
                rcases hξ with ⟨hξ1, hξ2⟩
                rcases hu with ⟨hua, hub⟩
                rcases hv with ⟨hva, hvb⟩
                refine ⟨by nlinarith, by nlinarith⟩
              have hWξ_nonzero : W y₁ y₂ ξ ≠ 0 := hW_nonzero_ioo ξ hξ_ioo
              have hy₁ξ_pos : y₁ ξ > 0 := hy₁_pos ξ hξ_ioo
              have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ ξ / (y₁ ξ)^2) ξ := by
                have hxJ : ξ ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hξ_ioo)
                have hy₁ξ_ne_zero : y₁ ξ ≠ 0 := hne ξ hξ_ioo
                exact HasDerivAt.div (hy₂ ξ hxJ) (hy₁ ξ hxJ) hy₁ξ_ne_zero
              have h_deriv_nonzero : deriv (fun x' => y₂ x' / y₁ x') ξ ≠ 0 := by
                rw [h_deriv_quot.deriv]
                refine div_ne_zero hWξ_nonzero (by positivity)
              exact h_deriv_nonzero hξ_eq
            · linarith
        rcases h_exists with ⟨c, hc, hc_eq⟩
        refine ⟨c, hc, hc_eq, ?_⟩
        intro d hd
        rcases hd with ⟨hd_ioo, hd_eq⟩
        exact h_unique c hc hc_eq d hd_ioo hd_eq
      · -- W < 0 on (a,b). Then y₂(a) > 0 and y₂(b) < 0
        have hWa_neg : W y₁ y₂ a < 0 := neg_at_endpoint (W y₁ y₂) hab hW_neg hW_cont_cc hWa_nonzero
        have hWb_neg : W y₁ y₂ b < 0 := neg_at_endpoint' (W y₁ y₂) hab hW_neg hW_cont_cc hWb_nonzero
        have hy₂a_pos : y₂ a > 0 := by
          have hWa_eq : W y₁ y₂ a = -(y₂ a) * deriv y₁ a := by
            unfold W; rw [hza]; ring
          rw [hWa_eq] at hWa_neg
          nlinarith
        have hy₂b_neg : y₂ b < 0 := by
          have hWb_eq : W y₁ y₂ b = -(y₂ b) * deriv y₁ b := by
            unfold W; rw [hzb]; ring
          rw [hWb_eq] at hWb_neg
          nlinarith
        have h_exists : ∃ c ∈ Set.Ioo a b, y₂ c = 0 := by
          have h_cont_y₂ : ContinuousOn y₂ (Set.Icc a b) := by
            intro x hx
            have hxJ : x ∈ J := hJ_sub hx
            exact (hy₂ x hxJ).continuousAt.continuousWithinAt
          have h0_in : (0 : ℝ) ∈ Set.Ioo (y₂ b) (y₂ a) := ⟨hy₂b_neg, hy₂a_pos⟩
          have h_IVT : (0 : ℝ) ∈ y₂ '' Set.Ioo a b :=
            intermediate_value_Ioo' (by nlinarith : a ≤ b) h_cont_y₂ h0_in
          rcases h_IVT with ⟨c, hc, hc_eq⟩
          exact ⟨c, hc, hc_eq⟩
        have h_unique : ∀ (c₁ c₂ : ℝ), c₁ ∈ Set.Ioo a b → y₂ c₁ = 0 → c₂ ∈ Set.Ioo a b → y₂ c₂ = 0 → c₁ = c₂ := by
          intro u v hu hu_eq hv hv_eq
          by_cases hlt : u < v
          · exfalso
            have h_cont_r : ContinuousOn (fun x => y₂ x / y₁ x) (Set.Icc u v) := by
              intro x hx
              rcases hx with ⟨hx1, hx2⟩
              have hx_ioo : x ∈ Set.Ioo a b := by
                rcases hu with ⟨hua, hub⟩
                rcases hv with ⟨hva, hvb⟩
                refine ⟨by nlinarith, by nlinarith⟩
              have hxJ : x ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hx_ioo)
              have hy₁x_ne_zero : y₁ x ≠ 0 := hne x hx_ioo
              have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ x / (y₁ x)^2) x :=
                HasDerivAt.div (hy₂ x hxJ) (hy₁ x hxJ) hy₁x_ne_zero
              exact h_deriv_quot.continuousAt.continuousWithinAt
            have h_eq : (fun x => y₂ x / y₁ x) u = (fun x => y₂ x / y₁ x) v := by
              simp [hu_eq, hv_eq]
            have h_rolle : ∃ ξ ∈ Set.Ioo u v, deriv (fun x => y₂ x / y₁ x) ξ = 0 :=
              exists_deriv_eq_zero hlt h_cont_r h_eq
            rcases h_rolle with ⟨ξ, hξ, hξ_eq⟩
            have hξ_ioo : ξ ∈ Set.Ioo a b := by
              rcases hξ with ⟨hξ1, hξ2⟩
              rcases hu with ⟨hua, hub⟩
              rcases hv with ⟨hva, hvb⟩
              refine ⟨by nlinarith, by nlinarith⟩
            have hWξ_nonzero : W y₁ y₂ ξ ≠ 0 := hW_nonzero_ioo ξ hξ_ioo
            have hy₁ξ_pos : y₁ ξ > 0 := hy₁_pos ξ hξ_ioo
            have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ ξ / (y₁ ξ)^2) ξ := by
              have hxJ : ξ ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hξ_ioo)
              have hy₁ξ_ne_zero : y₁ ξ ≠ 0 := hne ξ hξ_ioo
              exact HasDerivAt.div (hy₂ ξ hxJ) (hy₁ ξ hxJ) hy₁ξ_ne_zero
            have h_deriv_nonzero : deriv (fun x' => y₂ x' / y₁ x') ξ ≠ 0 := by
              rw [h_deriv_quot.deriv]
              refine div_ne_zero hWξ_nonzero (by positivity)
            exact h_deriv_nonzero hξ_eq
          · by_cases hlt2 : v < u
            · exfalso
              have h_cont_r : ContinuousOn (fun x => y₂ x / y₁ x) (Set.Icc v u) := by
                intro x hx
                rcases hx with ⟨hx1, hx2⟩
                have hx_ioo : x ∈ Set.Ioo a b := by
                  rcases hu with ⟨hua, hub⟩
                  rcases hv with ⟨hva, hvb⟩
                  refine ⟨by nlinarith, by nlinarith⟩
                have hxJ : x ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hx_ioo)
                have hy₁x_ne_zero : y₁ x ≠ 0 := hne x hx_ioo
                have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ x / (y₁ x)^2) x :=
                  HasDerivAt.div (hy₂ x hxJ) (hy₁ x hxJ) hy₁x_ne_zero
                exact h_deriv_quot.continuousAt.continuousWithinAt
              have h_eq : (fun x => y₂ x / y₁ x) v = (fun x => y₂ x / y₁ x) u := by
                simp [hu_eq, hv_eq]
              have h_rolle : ∃ ξ ∈ Set.Ioo v u, deriv (fun x => y₂ x / y₁ x) ξ = 0 :=
                exists_deriv_eq_zero hlt2 h_cont_r h_eq
              rcases h_rolle with ⟨ξ, hξ, hξ_eq⟩
              have hξ_ioo : ξ ∈ Set.Ioo a b := by
                rcases hξ with ⟨hξ1, hξ2⟩
                rcases hu with ⟨hua, hub⟩
                rcases hv with ⟨hva, hvb⟩
                refine ⟨by nlinarith, by nlinarith⟩
              have hWξ_nonzero : W y₁ y₂ ξ ≠ 0 := hW_nonzero_ioo ξ hξ_ioo
              have hy₁ξ_pos : y₁ ξ > 0 := hy₁_pos ξ hξ_ioo
              have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ ξ / (y₁ ξ)^2) ξ := by
                have hxJ : ξ ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hξ_ioo)
                have hy₁ξ_ne_zero : y₁ ξ ≠ 0 := hne ξ hξ_ioo
                exact HasDerivAt.div (hy₂ ξ hxJ) (hy₁ ξ hxJ) hy₁ξ_ne_zero
              have h_deriv_nonzero : deriv (fun x' => y₂ x' / y₁ x') ξ ≠ 0 := by
                rw [h_deriv_quot.deriv]
                refine div_ne_zero hWξ_nonzero (by positivity)
              exact h_deriv_nonzero hξ_eq
            · linarith
        rcases h_exists with ⟨c, hc, hc_eq⟩
        refine ⟨c, hc, hc_eq, ?_⟩
        intro d hd
        rcases hd with ⟨hd_ioo, hd_eq⟩
        exact h_unique c hc hc_eq d hd_ioo hd_eq
    · -- y₁(x) < 0 for all x ∈ (a,b). Replace y₁ by -y₁ and apply the y₁ > 0 case.
      have hne' : ∀ x ∈ Set.Ioo a b, (-y₁) x ≠ 0 := by
        intro x hx; simp [hy₁_neg x hx]
      have hza' : (-y₁) a = 0 := by simp [hza]
      have hzb' : (-y₁) b = 0 := by simp [hzb]
      have h_cont_ioo' : ∀ x ∈ Set.Ioo a b, ContinuousAt (-y₁) x := by
        intro x hx; exact (hy₁_cont_ioo x hx).neg
      rcases constant_sign_nonzero_cont (-y₁) a b hab hne' h_cont_ioo' with (hpos' | hneg')
      · -- -y₁ > 0 on (a,b), so apply the y₁ > 0 case to (-y₁, y₂)
        have hW' : ∃ x₀ ∈ J, (-y₁) x₀ * deriv y₂ x₀ - y₂ x₀ * deriv (-y₁) x₀ ≠ 0 := by
          rcases hW with ⟨x₀, hx₀J, hx₀W⟩
          refine ⟨x₀, hx₀J, ?_⟩
          have : deriv (-y₁) x₀ = -deriv y₁ x₀ := deriv_neg _ _
          simp [this, hx₀W]
        have hy₁''_neg : ∀ x ∈ J, HasDerivAt (deriv (-y₁)) (-(p x * deriv (-y₁) x + q x * (-y₁) x)) x := by
          intro x hx
          have h : HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x := hy₁' x hx
          have h_deriv_neg' : HasDerivAt (deriv (-y₁)) (-(p x * (-deriv y₁ x) + q x * (-y₁ x))) x := by
            simpa [deriv_neg] using HasDerivAt.neg h
          have : -(p x * (-deriv y₁ x) + q x * (-y₁ x)) = -(p x * deriv (-y₁) x + q x * (-y₁) x) := by
            simp [deriv_neg]
          rw [this]
          simpa [deriv_neg] using h_deriv_neg'
        exact sturm_separation p q (-y₁) y₂ a b hab J hJ_open hJ_conn hJ_sub hp hq
          (fun x hx => HasDerivAt.neg (hy₁ x hx)) hy₁''_neg hy₂ hy₂' hW' hza' hzb' hne'
      · -- -y₁ < 0 on (a,b), which means y₁ > 0, contradicting hy₁_neg
        exfalso
        have hx : (a+b)/2 ∈ Set.Ioo a b := by nlinarith
        have : (-y₁) ((a+b)/2) > 0 := hpos' ((a+b)/2) hx
        have : (-y₁) ((a+b)/2) < 0 := hneg' ((a+b)/2) hx
        linarith

end Submission
