import Mathlib
open Set
open SimpleGraph

namespace Submission

theorem mulCayley_connected_iff_closure_eq_top {G : Type*} [Group G]
    (S : Set G) :
    (SimpleGraph.mulCayley S).Connected ↔ Subgroup.closure S = ⊤ := by
  constructor
  · intro h_conn
    rw [Subgroup.eq_top_iff']
    intro g
    have h_reach : (SimpleGraph.mulCayley S).Reachable (1 : G) g :=
      h_conn.preconnected 1 g
    rcases h_reach with ⟨w⟩
    have h_mem_closure : ∀ (u : G), (SimpleGraph.mulCayley S).Walk u g →
        u ∈ Subgroup.closure S → g ∈ Subgroup.closure S := by
      intro u w'
      induction w' with
      | nil => exact id
      | cons h_adj w'' ih =>
          intro hu
          rcases (SimpleGraph.mulCayley_adj' S u v).mp h_adj with ⟨h_ne, h_edge⟩
          rcases h_edge with ⟨s, hs, h_cases⟩
          have hv : v ∈ Subgroup.closure S := by
            rcases h_cases with (h_eq | h_eq)
            · -- u * s = v
              rw [← h_eq]
              exact Subgroup.mul_mem _ hu (Subgroup.subset_closure hs)
            · -- u = v * s, so v = u * s⁻¹
              have : v = u * s⁻¹ := by
                calc
                  v = v * 1 := by group
                  _ = v * (s * s⁻¹) := by group
                  _ = (v * s) * s⁻¹ := by group
                  _ = u * s⁻¹ := by rw [h_eq]
              rw [this]
              exact Subgroup.mul_mem _ hu (Subgroup.inv_mem _ (Subgroup.subset_closure hs))
          exact ih hv
    exact h_mem_closure 1 w (Subgroup.one_mem _)
  · intro h_gen
    have h_nonempty : Nonempty G := ⟨1⟩
    -- Left multiplication graph homomorphism
    let leftMulHom (h : G) : SimpleGraph.mulCayley S →g SimpleGraph.mulCayley S :=
      RelHom.mk (λ g => h * g) (by
        intro x y h_adj
        rcases (SimpleGraph.mulCayley_adj' S x y).mp h_adj with ⟨h_ne, h_edge⟩
        rcases h_edge with ⟨s, hs, h_cases⟩
        have h_ne' : h * x ≠ h * y := (mul_ne_mul_right h).mpr h_ne
        refine (SimpleGraph.mulCayley_adj' S (h * x) (h * y)).mpr ⟨h_ne', ?_⟩
        rcases h_cases with (h_eq | h_eq)
        · refine ⟨s, hs, Or.inl ?_⟩
          calc
            (h * x) * s = h * (x * s) := by group
            _ = h * y := by rw [h_eq]
        · refine ⟨s, hs, Or.inr ?_⟩
          calc
            h * x = h * (y * s) := by rw [h_eq]
            _ = (h * y) * s := by group)
    -- Left multiply a walk
    def leftMulWalk (h : G) {u v : G} (w : (SimpleGraph.mulCayley S).Walk u v) :
        (SimpleGraph.mulCayley S).Walk (h * u) (h * v) :=
      Walk.map (leftMulHom h) w
    have h_preconn : (SimpleGraph.mulCayley S).Preconnected := by
      intro a b
      -- Every element is reachable from 1
      have h_reach_one : ∀ (g : G), (SimpleGraph.mulCayley S).Reachable (1 : G) g := by
        intro g
        have hg : g ∈ Subgroup.closure S := by
          rw [h_gen]
          exact Subgroup.mem_top g
        let P (x : G) (hx : x ∈ Subgroup.closure S) : Prop :=
          (SimpleGraph.mulCayley S).Reachable (1 : G) x
        have h_all : ∀ (x : G) (hx : x ∈ Subgroup.closure S), P x hx := by
          intro x hx
          refine Subgroup.closure_induction (k := S) (p := P) ?_ ?_ ?_ ?_ hx
          · intro x' hx'S
            -- x' ∈ S, need Reachable 1 x'
            by_cases hx'1 : x' = 1
            · subst hx'1; exact ⟨Walk.nil⟩
            · have h_adj : (SimpleGraph.mulCayley S).Adj (1 : G) x' := by
                refine (SimpleGraph.mulCayley_adj' S (1 : G) x').mpr ⟨hx'1, ⟨x', hx'S, Or.inl ?_⟩⟩
                simp
              exact ⟨Walk.cons h_adj Walk.nil⟩
          · -- Reachable 1 1
            exact ⟨Walk.nil⟩
          · intro x' y' hx' hy' ihx' ihy'
            -- Need Reachable 1 (x' * y')
            rcases ihx' with ⟨wx⟩
            rcases ihy' with ⟨wy⟩
            -- Left-multiply wy by x' to get walk from x' to x'*y'
            let wx' : (SimpleGraph.mulCayley S).Walk x' (x' * y') :=
              leftMulWalk x' wy
            exact ⟨wx.append wx'⟩
          · intro x' hx' ihx'
            -- Need Reachable 1 x'⁻¹
            rcases ihx' with ⟨wx⟩
            -- Left-multiply wx by x'⁻¹ to get walk from x'⁻¹ to 1
            have : x'⁻¹ * (1 : G) = x'⁻¹ := by simp
            have hx'inv : x'⁻¹ * x' = (1 : G) := by group
            let wx_inv : (SimpleGraph.mulCayley S).Walk (x'⁻¹ * (1 : G)) (x'⁻¹ * x') :=
              leftMulWalk (x'⁻¹) wx
            rw [this, hx'inv] at wx_inv
            exact ⟨wx_inv.reverse⟩
        exact h_all g hg
      -- Reachable a 1: go from a to 1 via a⁻¹
      have h_reach_a_one : (SimpleGraph.mulCayley S).Reachable a 1 := by
        have h_reach_one_a_inv : (SimpleGraph.mulCayley S).Reachable (1 : G) (a⁻¹) := h_reach_one (a⁻¹)
        rcases h_reach_one_a_inv with ⟨w⟩
        have ha1 : a * (1 : G) = a := by simp
        have ha_inv : a * a⁻¹ = (1 : G) := by group
        let w' : (SimpleGraph.mulCayley S).Walk (a * (1 : G)) (a * a⁻¹) := leftMulWalk a w
        rw [ha1, ha_inv] at w'
        exact ⟨w'⟩
      -- Reachable 1 b
      have h_reach_one_b : (SimpleGraph.mulCayley S).Reachable (1 : G) b := h_reach_one b
      -- Combine: a → 1 → b
      exact h_reach_a_one.trans h_reach_one_b
    exact ⟨h_preconn, h_nonempty⟩

end Submission
