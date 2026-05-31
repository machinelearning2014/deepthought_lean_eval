import Mathlib

namespace Submission.Helpers

  open Set

  open SimpleGraph

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

end Submission.Helpers
