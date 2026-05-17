import Mathlib

open SimpleGraph
open Finset
open Nat

namespace Submission.Helpers

noncomputable def subsetEmbedding (n m : ℕ) (S : Finset (Fin n)) (h : S.card = m) : Fin m ↪ Fin n :=
  (Finset.orderEmbOfFin S (by simpa using h)).toEmbedding

lemma subsetEmbedding_mem (n m : ℕ) (S : Finset (Fin n)) (h : S.card = m) (a : Fin m) : subsetEmbedding n m S h a ∈ S := by
  dsimp [subsetEmbedding]
  have h_mem : (Finset.orderEmbOfFin S (by simpa using h)) a ∈ S :=
    Finset.orderEmbOfFin_mem S (by simpa using h) a
  simpa using h_mem

def pullback {α β : Type} (G : SimpleGraph β) (f : α → β) : SimpleGraph α where
  Adj a b := G.Adj (f a) (f b)
  symm := by intro a b h; exact G.symm h
  loopless := by intro a; exact G.loopless (f a)

lemma not_cliqueFree_of_exists_isNClique {α : Type} (G : SimpleGraph α) (r : ℕ) (t : Finset α) (h : G.IsNClique r t) : ¬ G.CliqueFree r := by
  intro hcf; rw [SimpleGraph.CliqueFree] at hcf; exact hcf t h

lemma not_cliqueFree_iff_exists_isNClique {α : Type} (G : SimpleGraph α) (n : ℕ) : ¬ G.CliqueFree n ↔ ∃ (s : Finset α), G.IsNClique n s := by
  constructor
  · intro h; rw [SimpleGraph.CliqueFree] at h; push_neg at h; exact h
  · rintro ⟨s, hs⟩ hcf; exact (hcf s) hs

lemma isNClique_insert_adjacent' {α : Type} [DecidableEq α] (G : SimpleGraph α) (r : ℕ) (s : Finset α) (v : α)
    (h_clique : G.IsNClique r s) (hv : v ∉ s) (h_adj : ∀ u ∈ s, G.Adj v u) : G.IsNClique (r+1) (insert v s) := by
  refine SimpleGraph.IsNClique.mk ?_ ?_
  · rw [SimpleGraph.IsClique, Finset.coe_insert]
    have h_is_clique : (s : Set α).Pairwise G.Adj := h_clique.isClique
    have h_insert_adj : ∀ b ∈ (s : Set α), v ≠ b → (G.Adj v b ∧ G.Adj b v) := by
      intro b hb hne
      have h_adj : G.Adj v b := h_adj b hb
      exact ⟨h_adj, G.symm h_adj⟩
    exact Set.Pairwise.insert h_is_clique h_insert_adj
  · calc
      card (insert v s) = card s + 1 := Finset.card_insert_of_notMem hv
      _ = r + 1 := by rw [h_clique.card_eq]

lemma image_pullback_isNClique {α β : Type} [DecidableEq α] [DecidableEq β] (G : SimpleGraph β) (f : α → β)
    (hf : Function.Injective f) (r : ℕ) (s : Finset α) (h : (pullback G f).IsNClique r s) : G.IsNClique r (Finset.image f s) := by
  refine SimpleGraph.IsNClique.mk ?_ ?_
  · rw [SimpleGraph.IsClique]
    intro x hx y hy hxy
    rcases Finset.mem_image.1 hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.1 hy with ⟨b, hb, rfl⟩
    have hne : a ≠ b := by intro h_eq; apply hxy; rw [h_eq]
    have h_clique_set : (pullback G f).IsClique (s : Set α) := h.isClique
    rw [SimpleGraph.IsClique] at h_clique_set
    have hadj : (pullback G f).Adj a b := h_clique_set ha hb hne
    dsimp [pullback] at hadj; exact hadj
  · rw [Finset.card_image_of_injective s hf, h.card_eq]

lemma image_pullback_compl_isNClique {α β : Type} [DecidableEq α] [DecidableEq β] (G : SimpleGraph β) (f : α → β)
    (hf : Function.Injective f) (r : ℕ) (s : Finset α) (h : (pullback G f)ᶜ.IsNClique r s) : Gᶜ.IsNClique r (Finset.image f s) := by
  refine SimpleGraph.IsNClique.mk ?_ ?_
  · rw [SimpleGraph.IsClique]
    intro x hx y hy hxy
    rcases Finset.mem_image.1 hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.1 hy with ⟨b, hb, rfl⟩
    have hne : a ≠ b := by intro h_eq; apply hxy; rw [h_eq]
    have h_clique_set : (pullback G f)ᶜ.IsClique (s : Set α) := h.isClique
    rw [SimpleGraph.IsClique] at h_clique_set
    have hadj : (pullback G f)ᶜ.Adj a b := h_clique_set ha hb hne
    rw [SimpleGraph.compl_adj] at hadj
    rcases hadj with ⟨hne_ab, hnot⟩
    rw [SimpleGraph.compl_adj]
    refine ⟨?_, ?_⟩
    · intro h_eq; apply hne_ab; exact hf h_eq
    · intro hadj_G; apply hnot; dsimp [pullback]; exact hadj_G
  · rw [Finset.card_image_of_injective s hf, h.card_eq]

lemma finset_in_fin0_empty (s : Finset (Fin 0)) : s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact x.elim0

lemma cliqueFree_on_fin0 (G : SimpleGraph (Fin 0)) (k : ℕ) (hk : 1 ≤ k) : G.CliqueFree k := by
  intro s hs
  have hcard := hs.card_eq
  have : s = ∅ := finset_in_fin0_empty s
  subst this
  simp at hcard
  omega

end Submission.Helpers
