import Mathlib

namespace Submission.Helpers

  open SimpleGraph

  open Finset

  noncomputable section

  namespace Submission

  lemma comap_subgraph {V : Type*} (k : ℕ) (f : Fin k → V) (hf : Function.Injective f) (G : SimpleGraph V) :
      (SimpleGraph.comap f G) ⊑ G := by
    let hom : (SimpleGraph.comap f G) →g G := by
      refine RelHom.mk f ?_
      intro i j h
      simpa [SimpleGraph.comap_adj] using h
    have hinj : Function.Injective (hom : Fin k → V) := hf
    exact ⟨SimpleGraph.Copy.mk hom hinj⟩

  lemma comap_compl {V : Type*} (k : ℕ) (f : Fin k → V) (hf : Function.Injective f) (G : SimpleGraph V) :
      (SimpleGraph.comap f G)ᶜ = SimpleGraph.comap f (Gᶜ) := by
    ext i j
    simp [SimpleGraph.comap_adj, SimpleGraph.compl_adj, hf.eq_iff]

  lemma map_clique {V : Type*} [DecidableEq V] (k n : ℕ) (f : Fin k → V) (hf : Function.Injective f) (G : SimpleGraph V)
      (T : Finset (Fin k)) (hT : (SimpleGraph.comap f G).IsNClique n T) : G.IsNClique n (Finset.image f T) := by
    rcases hT with ⟨hT_clique, hT_card⟩
    refine {
      isClique := by
        intro x hx y hy hne
        have hx_finset : x ∈ Finset.image f T := by simpa using hx
        have hy_finset : y ∈ Finset.image f T := by simpa using hy
        rcases Finset.mem_image.1 hx_finset with ⟨x', hx'_T, rfl⟩
        rcases Finset.mem_image.1 hy_finset with ⟨y', hy'_T, rfl⟩
        have hne' : x' ≠ y' := by
          intro h_eq
          apply hne
          rw [h_eq]
        have h_adj : (SimpleGraph.comap f G).Adj x' y' :=
          hT_clique (Finset.mem_coe.mpr hx'_T) (Finset.mem_coe.mpr hy'_T) hne'
        simpa [SimpleGraph.comap_adj] using h_adj
      card_eq := by
        have : (Finset.image f T).card = T.card :=
          Finset.card_image_of_injective T hf
        rw [this, hT_card]
    }

  lemma add_vertex_to_clique {V : Type*} (G : SimpleGraph V) (k : ℕ) (v : V) (s : Finset V)
      (hs : G.IsNClique (k-1) s) (h_adj : ∀ u ∈ s, G.Adj v u) (hv_notin : v ∉ s) (hk : 1 ≤ k) :
      G.IsNClique k (Finset.cons v s hv_notin) := by
    rcases hs with ⟨hs_clique, hs_card⟩
    let t : Finset V := Finset.cons v s hv_notin
    have hmem_finset : ∀ x, x ∈ t ↔ (x = v) ∨ (x ∈ s) := by
      intro x; simp [t]
    have hcard : t.card = k := by
      simp [t, hs_card]; omega
    refine {
      isClique := by
        intro x hx y hy hne
        have hxf : x ∈ t := hx
        have hyf : y ∈ t := hy
        rw [hmem_finset] at hxf hyf
        rcases hxf with (rfl | hx')
        · rcases hyf with (rfl | hy')
          · exact (hne rfl).elim
          · apply h_adj y hy'
        · rcases hyf with (rfl | hy')
          · apply G.symm (h_adj x hx')
          · exact hs_clique hx' hy' hne
      card_eq := hcard
    }

  lemma exists_clique_of_not_cf {V : Type*} (G : SimpleGraph V) (k : ℕ) (h : ¬ G.CliqueFree k) :
      ∃ (s : Finset V), G.IsNClique k s := by
    rw [SimpleGraph.CliqueFree] at h
    push_neg at h
    exact h

end Submission.Helpers
