import Mathlib
import Submission.Helpers

namespace Submission

open Submission.Helpers

  theorem finite_graph_ramsey_theorem :
      ∀ r s : ℕ, 2 ≤ r → 2 ≤ s →
      ∃ n : ℕ, ∀ G : SimpleGraph (Fin n),
        ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s := by
    let P (m : ℕ) : Prop := ∀ (r' s' : ℕ), 2 ≤ r' → 2 ≤ s' → r' + s' = m →
      ∃ n : ℕ, ∀ (G : SimpleGraph (Fin n)), ¬ G.CliqueFree r' ∨ ¬ Gᶜ.CliqueFree s'
    have hP_step : ∀ m, (∀ k < m, P k) → P m := by
      intro m IH r' s' hr' hs' hsum
      by_cases h2r : r' = 2
      · subst r'
        refine ⟨s', λ G => ?_⟩
        by_cases h_edge : ∃ (x y : Fin s'), G.Adj x y
        · rcases h_edge with ⟨x, y, h_adj⟩
          left
          intro h
          have hxy : x ≠ y := by
            intro h_eq
            rw [h_eq] at h_adj
            exact G.loopless.irrefl y h_adj
          have h_clique : G.IsNClique 2 ({x, y} : Finset (Fin s')) := {
            isClique := by
              intro a ha b hb hne
              simp at ha hb
              rcases ha with (rfl | rfl)
              · rcases hb with (rfl | rfl)
                · exact (hne rfl).elim
                · exact h_adj
              · rcases hb with (rfl | rfl)
                · simpa using G.symm h_adj
                · exact (hne rfl).elim
            card_eq := by simp [hxy]
          }
          exact h ({x, y}) h_clique
        · have h_no_edge : ∀ x y : Fin s', ¬ G.Adj x y := by
            intro x y; by_contra! h; exact h_edge ⟨x, y, h⟩
          right
          intro h
          have h_clique : Gᶜ.IsNClique s' (Finset.univ : Finset (Fin s')) := {
            isClique := by
              intro x hx y hy hne
              rw [SimpleGraph.compl_adj]
              exact ⟨hne, h_no_edge x y⟩
            card_eq := by simp
          }
          exact h Finset.univ h_clique
      · by_cases h2s : s' = 2
        · subst s'
          refine ⟨r', λ G => ?_⟩
          by_cases hcomplete : ∀ (x y : Fin r'), x ≠ y → G.Adj x y
          · left
            intro h
            have h_clique : G.IsNClique r' (Finset.univ : Finset (Fin r')) := {
              isClique := by
                intro x hx y hy hne
                exact hcomplete x y hne
              card_eq := by simp
            }
            exact h Finset.univ h_clique
          · push_neg at hcomplete
            rcases hcomplete with ⟨x, y, hne, h_not_adj⟩
            right
            intro h
            have h_clique : Gᶜ.IsNClique 2 ({x, y} : Finset (Fin r')) := {
              isClique := by
                intro a ha b hb hne2
                simp at ha hb
                rcases ha with (rfl | rfl)
                · rcases hb with (rfl | rfl)
                  · exact (hne2 rfl).elim
                  · rw [SimpleGraph.compl_adj]
                    exact ⟨hne, h_not_adj⟩
                · rcases hb with (rfl | rfl)
                  · rw [SimpleGraph.compl_adj]
                    exact ⟨hne.symm, fun h_adj => h_not_adj (G.symm h_adj)⟩
                  · exact (hne2 rfl).elim
              card_eq := by simp [hne]
            }
            exact h ({x, y}) h_clique
        · have hrgt2 : 2 < r' := by omega
          have hsgt2 : 2 < s' := by omega
          have hsum1_m : (r' - 1) + s' < m := by omega
          have hsum2_m : r' + (s' - 1) < m := by omega
          have hIH1 : P ((r' - 1) + s') := IH ((r' - 1) + s') hsum1_m
          have hIH2 : P (r' + (s' - 1)) := IH (r' + (s' - 1)) hsum2_m
          rcases hIH1 (r' - 1) s' (by omega) hs' rfl with ⟨n1, hP1⟩
          rcases hIH2 r' (s' - 1) hr' (by omega) rfl with ⟨n2, hP2⟩
          refine ⟨n1 + n2, λ G => ?_⟩
          classical
            by_cases hzero : n1 + n2 = 0
            · have hn1z : n1 = 0 := by omega
              have hn2z : n2 = 0 := by omega
              subst hn1z; subst hn2z
              have hcard0 : ∀ (t : Finset (Fin 0)), t.card = 0 := by
                intro t
                have : t ⊆ Finset.univ := Finset.subset_univ t
                have huniv : (Finset.univ : Finset (Fin 0)).card = 0 := by simp
                have hle : t.card ≤ (Finset.univ : Finset (Fin 0)).card := Finset.card_le_card this
                omega
              have h_cf : G.CliqueFree (r'-1) := by
                intro t ⟨_, hcard⟩
                have : t.card = 0 := hcard0 t
                omega
              have h_ccf : Gᶜ.CliqueFree s' := by
                intro t ⟨_, hcard⟩
                have : t.card = 0 := hcard0 t
                omega
              rcases hP1 G with (hleft | hright)
              · exfalso; exact hleft h_cf
              · exfalso; exact hright h_ccf
            · have hnpos : 0 < n1 + n2 := Nat.pos_of_ne_zero hzero
              let v : Fin (n1 + n2) := ⟨0, hnpos⟩
              let A : Finset (Fin (n1 + n2)) := (Finset.univ.erase v).filter (λ u => G.Adj v u)
              let B : Finset (Fin (n1 + n2)) := (Finset.univ.erase v).filter (λ u => ¬ G.Adj v u)
              have h_total : (Finset.univ.erase v) = A ∪ B := by
                ext u
                have h_cases : G.Adj v u ∨ ¬ G.Adj v u := em _
                constructor
                · intro huv
                  rcases h_cases with (hadj | hnot)
                  · apply Finset.mem_union_left; simp [A, huv, hadj]
                  · apply Finset.mem_union_right; simp [B, huv, hnot]
                · intro h
                  rcases Finset.mem_union.1 h with (hA | hB)
                  · simp [A, Finset.mem_filter] at hA
                    rcases hA with ⟨huv, hadj⟩
                    simp [huv]
                  · simp [B, Finset.mem_filter] at hB
                    rcases hB with ⟨huv, hnot⟩
                    simp [huv]
              have h_disjoint : A ∩ B = ∅ := by
                ext u
                constructor
                · intro h
                  exfalso
                  simp [A, B, Finset.mem_inter, Finset.mem_filter, Finset.mem_erase] at h
                  rcases h with ⟨⟨huv, hadj⟩, ⟨_, hnot⟩⟩
                  exact hnot hadj
                · intro h; exfalso; simp at h
              have h_card_sum : A.card + B.card = n1 + n2 - 1 := by
                calc
                  A.card + B.card = (A ∪ B).card + (A ∩ B).card := by
                    rw [(Finset.card_union_add_card_inter A B).symm]
                  _ = (Finset.univ.erase v).card + 0 := by
                    rw [← h_total, h_disjoint, Finset.card_empty]
                  _ = (Finset.univ.erase v).card := by simp
                  _ = (n1 + n2) - 1 := by simp
              by_cases hA : A.card ≥ n1
              · rcases Finset.exists_subset_card_eq hA with ⟨A', hA'mem, hA'card⟩
                have h_linear : LinearOrder (Fin (n1 + n2)) := by infer_instance
                let f_emb' := Finset.orderEmbOfFin A' hA'card
                have hf_emb_mem : ∀ (i : Fin n1), f_emb' i ∈ A' :=
                  Finset.orderEmbOfFin_mem A' hA'card
                have hf_image : ∀ (i : Fin n1), G.Adj v (f_emb' i) := by
                  intro i
                  have hmemA' : f_emb' i ∈ A' := hf_emb_mem i
                  have hmemA : f_emb' i ∈ A := hA'mem hmemA'
                  simp [A, Finset.mem_filter, Finset.mem_erase] at hmemA
                  exact hmemA.2
                have hf_inj : Function.Injective f_emb' := f_emb'.injective
                let H : SimpleGraph (Fin n1) := SimpleGraph.comap f_emb' G
                rcases hP1 H with (hH_cf | hH_ccf)
                · left
                  intro hG_cf_r'
                  rcases exists_clique_of_not_cf H (r'-1) hH_cf with ⟨T, hT⟩
                  have hG_clique_sub : G.IsNClique (r'-1) (Finset.image f_emb' T) :=
                    map_clique n1 (r'-1) f_emb' hf_inj G T hT
                  have hS_sub_A' : Finset.image f_emb' T ⊆ A' := by
                    intro x hx
                    rcases Finset.mem_image.1 hx with ⟨i, hi, rfl⟩
                    exact hf_emb_mem i
                  have hS_sub_A : Finset.image f_emb' T ⊆ A := Finset.Subset.trans hS_sub_A' hA'mem
                  have hv_notin_S : v ∉ Finset.image f_emb' T := by
                    intro hv
                    have hvA : v ∈ A := hS_sub_A hv
                    simp [A, Finset.mem_filter, Finset.mem_erase] at hvA
                  have h_adj_all : ∀ u ∈ Finset.image f_emb' T, G.Adj v u := by
                    intro u hu
                    rcases Finset.mem_image.1 hu with ⟨i, hi, rfl⟩
                    exact hf_image i
                  have hk_ge1 : 1 ≤ r' := by omega
                  let S := Finset.image f_emb' T
                  have hv_notin_S' : v ∉ S := hv_notin_S
                  have hG_clique_r' : G.IsNClique r' (Finset.cons v S hv_notin_S') :=
                    add_vertex_to_clique G r' v S hG_clique_sub h_adj_all hv_notin_S' hk_ge1
                  exact hG_cf_r' (Finset.cons v S hv_notin_S') hG_clique_r'
                · right
                  intro hGc_cf_s'
                  apply hH_ccf
                  rw [comap_compl n1 f_emb' hf_inj G]
                  exact SimpleGraph.CliqueFree.comap (comap_subgraph n1 f_emb' hf_inj (Gᶜ)) hGc_cf_s'
              · have hB : B.card ≥ n2 := by
                  have hA_lt : A.card < n1 := by omega
                  by_contra! hB_lt
                  have : A.card + B.card ≤ n1 + n2 - 2 := by omega
                  omega
                rcases Finset.exists_subset_card_eq hB with ⟨B', hB'mem, hB'card⟩
                have h_linear : LinearOrder (Fin (n1 + n2)) := by infer_instance
                let g_emb' := Finset.orderEmbOfFin B' hB'card
                have hg_emb_mem : ∀ (i : Fin n2), g_emb' i ∈ B' :=
                  Finset.orderEmbOfFin_mem B' hB'card
                have hg_image : ∀ (i : Fin n2), ¬ G.Adj v (g_emb' i) := by
                  intro i
                  have hmemB' : g_emb' i ∈ B' := hg_emb_mem i
                  have hmemB : g_emb' i ∈ B := hB'mem hmemB'
                  simp [B, Finset.mem_filter, Finset.mem_erase] at hmemB
                  exact hmemB.2
                have hg_inj : Function.Injective g_emb' := g_emb'.injective
                let K : SimpleGraph (Fin n2) := SimpleGraph.comap g_emb' G
                rcases hP2 K with (hK_cf | hK_ccf)
                · left
                  intro hG_cf_r'
                  apply hK_cf
                  exact SimpleGraph.CliqueFree.comap (comap_subgraph n2 g_emb' hg_inj G) hG_cf_r'
                · right
                  intro hGc_cf_s'
                  rcases exists_clique_of_not_cf (Kᶜ) (s'-1) hK_ccf with ⟨T, hT⟩
                  rw [comap_compl n2 g_emb' hg_inj G] at hT
                  have hGc_clique_sub : Gᶜ.IsNClique (s'-1) (Finset.image g_emb' T) :=
                    map_clique n2 (s'-1) g_emb' hg_inj (Gᶜ) T hT
                  have hS_sub_B' : Finset.image g_emb' T ⊆ B' := by
                    intro x hx
                    rcases Finset.mem_image.1 hx with ⟨i, hi, rfl⟩
                    exact hg_emb_mem i
                  have hS_sub_B : Finset.image g_emb' T ⊆ B := Finset.Subset.trans hS_sub_B' hB'mem
                  have hv_notin_S : v ∉ Finset.image g_emb' T := by
                    intro hv
                    have hvB : v ∈ B := hS_sub_B hv
                    simp [B, Finset.mem_filter, Finset.mem_erase] at hvB
                  have h_adj_all : ∀ u ∈ Finset.image g_emb' T, Gᶜ.Adj v u := by
                    intro u hu
                    rcases Finset.mem_image.1 hu with ⟨i, hi, rfl⟩
                    rw [SimpleGraph.compl_adj]
                    refine ⟨?_, hg_image i⟩
                    have h_not_eq : g_emb' i ≠ v := by
                      intro h_eq
                      have hmemB : g_emb' i ∈ B := hS_sub_B (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
                      simp [B, Finset.mem_filter, Finset.mem_erase] at hmemB
                      exact hmemB.1 h_eq
                    exact Ne.symm h_not_eq
                  have hk_ge1 : 1 ≤ s' := by omega
                  let S := Finset.image g_emb' T
                  have hv_notin_S' : v ∉ S := hv_notin_S
                  have hGc_clique_s' : Gᶜ.IsNClique s' (Finset.cons v S hv_notin_S') :=
                    add_vertex_to_clique (Gᶜ) s' v S hGc_clique_sub h_adj_all hv_notin_S' hk_ge1
                  exact hGc_cf_s' (Finset.cons v S hv_notin_S') hGc_clique_s'
    have hP_total : ∀ m, P m := by
      intro m
      refine Nat.strong_induction_on m ?_
      intro m' IH
      exact hP_step m' IH
    intro r s hr hs
    have hsum : r + s = r + s := rfl
    exact hP_total (r + s) r s hr hs hsum

end Submission
