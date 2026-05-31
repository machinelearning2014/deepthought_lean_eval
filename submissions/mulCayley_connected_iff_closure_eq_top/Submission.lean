import Mathlib
import Submission.Helpers

namespace Submission
  open Submission.Helpers
  open Set
  open SimpleGraph

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

end Submission
