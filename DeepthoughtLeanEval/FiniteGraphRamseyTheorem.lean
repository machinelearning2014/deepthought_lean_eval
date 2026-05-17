import Mathlib
open SimpleGraph
open Finset
open Nat
open Classical

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

theorem finite_graph_ramsey_theorem (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) :
    ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s := by
  let P (k : ℕ) : Prop := ∀ (r' s' : ℕ), r' + s' = k → 2 ≤ r' → 2 ≤ s' →
    ∃ n, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r' ∨ ¬ Gᶜ.CliqueFree s'
  have hP_induction : ∀ k, (∀ m < k, P m) → P k := by
    intro k IH r' s' hsum hr' hs'
    by_cases h2r : r' = 2
    · subst r'; refine ⟨s', λ G => ?_⟩
      by_cases hG : G.CliqueFree 2
      · right
        have : Gᶜ.IsNClique s' (Finset.univ : Finset (Fin s')) := by
          refine SimpleGraph.IsNClique.mk ?_ ?_
          · rw [SimpleGraph.IsClique]
            intro x hx y hy hxy
            rw [SimpleGraph.compl_adj]
            refine ⟨hxy, ?_⟩
            intro hadj
            have : G.IsNClique 2 {x, y} := by
              refine SimpleGraph.IsNClique.mk ?_ ?_
              · rw [SimpleGraph.IsClique]
                intro a ha b hb hab
                simp at ha hb
                rcases ha with (rfl|rfl) <;> rcases hb with (rfl|rfl) <;> try {exfalso; exact hab rfl}
                · exact hadj
                · exact G.symm hadj
              · simp [hxy]
            have not_cf : ¬ G.CliqueFree 2 := not_cliqueFree_of_exists_isNClique G 2 {x, y} this
            exact not_cf hG
          · simp
        exact not_cliqueFree_of_exists_isNClique Gᶜ s' Finset.univ this
      · left; exact hG
    · by_cases h2s : s' = 2
      · subst s'; refine ⟨r', λ G => ?_⟩
        by_cases hG : Gᶜ.CliqueFree 2
        · left
          have : G.IsNClique r' (Finset.univ : Finset (Fin r')) := by
            refine SimpleGraph.IsNClique.mk ?_ ?_
            · rw [SimpleGraph.IsClique]
              intro x hx y hy hxy
              by_contra! hnot
              have h_adj_compl : Gᶜ.Adj x y := by
                rw [SimpleGraph.compl_adj]; exact ⟨hxy, hnot⟩
              have : Gᶜ.IsNClique 2 {x, y} := by
                refine SimpleGraph.IsNClique.mk ?_ ?_
                · rw [SimpleGraph.IsClique]
                  intro a ha b hb hab
                  simp at ha hb
                  rcases ha with (rfl|rfl) <;> rcases hb with (rfl|rfl) <;> try {exfalso; exact hab rfl}
                  · exact h_adj_compl
                  · exact Gᶜ.symm h_adj_compl
                · simp [hxy]
              have not_cf : ¬ Gᶜ.CliqueFree 2 := not_cliqueFree_of_exists_isNClique Gᶜ 2 {x, y} this
              exact not_cf hG
            · simp
          exact not_cliqueFree_of_exists_isNClique G r' Finset.univ this
        · right; exact hG
      · have h3r : 3 ≤ r' := by omega
        have h3s : 3 ≤ s' := by omega
        have hsum1 : (r'-1) + s' < k := by rw [← hsum]; omega
        have hsum2 : r' + (s'-1) < k := by rw [← hsum]; omega
        rcases IH ((r'-1) + s') hsum1 (r'-1) s' rfl (by omega) hs' with ⟨n1, h1⟩
        rcases IH (r' + (s'-1)) hsum2 r' (s'-1) rfl hr' (by omega) with ⟨n2, h2⟩
        have hn1pos : n1 ≠ 0 := by
          intro hzero
          subst hzero
          have h_cf_r : (⊤ : SimpleGraph (Fin 0)).CliqueFree (r'-1) := by
            have : 1 ≤ r'-1 := by omega
            exact cliqueFree_on_fin0 ⊤ (r'-1) this
          have h_cf_s : (⊤ : SimpleGraph (Fin 0))ᶜ.CliqueFree s' := by
            have : 1 ≤ s' := by omega
            exact cliqueFree_on_fin0 (⊤ : SimpleGraph (Fin 0))ᶜ s' this
          have h1' : ¬ (⊤ : SimpleGraph (Fin 0)).CliqueFree (r'-1) ∨ ¬ (⊤ : SimpleGraph (Fin 0))ᶜ.CliqueFree s' := h1 ⊤
          rcases h1' with (h | h); exact h h_cf_r; exact h h_cf_s
        have hn2pos : n2 ≠ 0 := by
          intro hzero
          subst hzero
          have h_cf_r : (⊤ : SimpleGraph (Fin 0)).CliqueFree r' := by
            have : 1 ≤ r' := by omega
            exact cliqueFree_on_fin0 ⊤ r' this
          have h_cf_s : (⊤ : SimpleGraph (Fin 0))ᶜ.CliqueFree (s'-1) := by
            have : 1 ≤ s'-1 := by omega
            exact cliqueFree_on_fin0 (⊤ : SimpleGraph (Fin 0))ᶜ (s'-1) this
          have h2' : ¬ (⊤ : SimpleGraph (Fin 0)).CliqueFree r' ∨ ¬ (⊤ : SimpleGraph (Fin 0))ᶜ.CliqueFree (s'-1) := h2 ⊤
          rcases h2' with (h | h); exact h h_cf_r; exact h h_cf_s
        let n : ℕ := n1 + n2
        have hnpos : 0 < n := by
          dsimp [n]; omega
        refine ⟨n, λ (G : SimpleGraph (Fin n)) => ?_⟩
        let v : Fin n := ⟨0, hnpos⟩
        classical
          let A : Finset (Fin n) := Finset.filter (G.Adj v) Finset.univ
          let B : Finset (Fin n) := Finset.filter (λ (u : Fin n) => u ≠ v ∧ ¬ G.Adj v u) Finset.univ
          have hAB_disjoint : A ∩ B = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro x hx
            have hxA : x ∈ A := (Finset.mem_inter.mp hx).left
            have hxB : x ∈ B := (Finset.mem_inter.mp hx).right
            rw [Finset.mem_filter] at hxA hxB
            rcases hxA with ⟨_, h_adj⟩
            rcases hxB with ⟨_, ⟨_, h_not_adj⟩⟩
            exact h_not_adj h_adj
          have hAB_union : A ∪ B = Finset.univ.erase v := by
            ext u; constructor
            · intro hu
              rcases Finset.mem_union.mp hu with (huA | huB)
              · rw [Finset.mem_filter] at huA
                rcases huA with ⟨hu_univ, h_adj⟩
                have hu_ne_v : u ≠ v := by
                  intro h_eq
                  apply G.loopless v
                  rw [h_eq] at h_adj; exact h_adj
                exact Finset.mem_erase.mpr ⟨hu_ne_v, hu_univ⟩
              · rw [Finset.mem_filter] at huB
                rcases huB with ⟨hu_univ, ⟨hu_ne_v, _⟩⟩
                exact Finset.mem_erase.mpr ⟨hu_ne_v, hu_univ⟩
            · intro hu
              have hu_univ : u ∈ Finset.univ := (Finset.mem_erase.mp hu).right
              have hu_ne_v : u ≠ v := (Finset.mem_erase.mp hu).left
              by_cases h_adj : G.Adj v u
              · apply Finset.mem_union_left; rw [Finset.mem_filter]; exact ⟨hu_univ, h_adj⟩
              · apply Finset.mem_union_right; rw [Finset.mem_filter]; exact ⟨hu_univ, ⟨hu_ne_v, h_adj⟩⟩
          have h_card_total : A.card + B.card = n1 + n2 - 1 := by
            have h_card_union : (A ∪ B).card = A.card + B.card := by
              have h_card_eq : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
                Finset.card_union_add_card_inter A B
              rw [hAB_disjoint, Finset.card_empty] at h_card_eq
              omega
            rw [← h_card_union, hAB_union]
            simp [n]
          by_cases hA_card_ge : A.card ≥ n1
          · have hA_card_ge' : n1 ≤ A.card := hA_card_ge
            have h_exists : ∃ (t : Finset (Fin n)), t ⊆ A ∧ t.card = n1 :=
              Finset.exists_subset_card_eq hA_card_ge'
            rcases h_exists with ⟨A_sub, hA_sub, hA_card⟩
            let f_emb : Fin n1 ↪ Fin n := subsetEmbedding n n1 A_sub hA_card
            have f_emb_inj : Function.Injective f_emb := f_emb.injective
            have f_emb_mem (a : Fin n1) : f_emb a ∈ A_sub := by
              simpa [f_emb] using subsetEmbedding_mem n n1 A_sub hA_card a
            have h1_case : ¬ (pullback G f_emb).CliqueFree (r'-1) ∨ ¬ ((pullback G f_emb)ᶜ).CliqueFree s' :=
              h1 (pullback G f_emb)
            rcases h1_case with (hclique | hcompl)
            · rcases (not_cliqueFree_iff_exists_isNClique (pullback G f_emb) (r'-1)).mp hclique with ⟨t, ht⟩
              have hG_clique : G.IsNClique (r'-1) (Finset.image f_emb t) :=
                image_pullback_isNClique G f_emb f_emb_inj (r'-1) t ht
              have h_img_sub_A : Finset.image f_emb t ⊆ A := by
                intro x hx
                rcases Finset.mem_image.1 hx with ⟨a, ha, rfl⟩
                apply hA_sub; exact f_emb_mem a
              have hv_not_img : v ∉ Finset.image f_emb t := by
                intro hv_img
                rcases Finset.mem_image.1 hv_img with ⟨a, _, h_eq⟩
                have hA_mem : f_emb a ∈ A := h_img_sub_A (by
                  apply Finset.mem_image.mpr; exact ⟨a, by assumption, rfl⟩)
                rw [Finset.mem_filter] at hA_mem
                have h_adj : G.Adj v (f_emb a) := hA_mem.right
                rw [h_eq] at h_adj; exact G.loopless v h_adj
              have h_adj_all : ∀ u ∈ Finset.image f_emb t, G.Adj v u := by
                intro u hu
                have hA_mem : u ∈ A := h_img_sub_A hu
                rw [Finset.mem_filter] at hA_mem; exact hA_mem.right
              have hG_clique_temp : G.IsNClique ((r'-1)+1) (insert v (Finset.image f_emb t)) :=
                isNClique_insert_adjacent' G (r'-1) (Finset.image f_emb t) v hG_clique hv_not_img h_adj_all
              have h_eq_r' : r' = (r'-1)+1 := by omega
              have hG_clique_r' : G.IsNClique r' (insert v (Finset.image f_emb t)) := by
                rw [h_eq_r']; exact hG_clique_temp
              left; exact not_cliqueFree_of_exists_isNClique G r' (insert v (Finset.image f_emb t)) hG_clique_r'
            · rcases (not_cliqueFree_iff_exists_isNClique ((pullback G f_emb)ᶜ) s').mp hcompl with ⟨t, ht⟩
              have hG_compl_clique : Gᶜ.IsNClique s' (Finset.image f_emb t) :=
                image_pullback_compl_isNClique G f_emb f_emb_inj s' t ht
              right; exact not_cliqueFree_of_exists_isNClique Gᶜ s' (Finset.image f_emb t) hG_compl_clique
          · have hA_card_lt : A.card < n1 := by omega
            have hB_card_ge : B.card ≥ n2 := by
              by_contra! h
              have : A.card + B.card < n1 + n2 - 1 := by omega
              rw [h_card_total] at this
              omega
            have hB_card_ge' : n2 ≤ B.card := hB_card_ge
            have h_exists : ∃ (t : Finset (Fin n)), t ⊆ B ∧ t.card = n2 :=
              Finset.exists_subset_card_eq hB_card_ge'
            rcases h_exists with ⟨B_sub, hB_sub, hB_card⟩
            let g_emb : Fin n2 ↪ Fin n := subsetEmbedding n n2 B_sub hB_card
            have g_emb_inj : Function.Injective g_emb := g_emb.injective
            have g_emb_mem (a : Fin n2) : g_emb a ∈ B_sub := by
              simpa [g_emb] using subsetEmbedding_mem n n2 B_sub hB_card a
            have h2_case : ¬ (pullback G g_emb).CliqueFree r' ∨ ¬ ((pullback G g_emb)ᶜ).CliqueFree (s'-1) :=
              h2 (pullback G g_emb)
            rcases h2_case with (hclique | hcompl)
            · rcases (not_cliqueFree_iff_exists_isNClique (pullback G g_emb) r').mp hclique with ⟨t, ht⟩
              have hG_clique : G.IsNClique r' (Finset.image g_emb t) :=
                image_pullback_isNClique G g_emb g_emb_inj r' t ht
              left; exact not_cliqueFree_of_exists_isNClique G r' (Finset.image g_emb t) hG_clique
            · rcases (not_cliqueFree_iff_exists_isNClique ((pullback G g_emb)ᶜ) (s'-1)).mp hcompl with ⟨t, ht⟩
              have hG_compl_clique : Gᶜ.IsNClique (s'-1) (Finset.image g_emb t) :=
                image_pullback_compl_isNClique G g_emb g_emb_inj (s'-1) t ht
              have h_img_sub_B : Finset.image g_emb t ⊆ B := by
                intro x hx
                rcases Finset.mem_image.1 hx with ⟨a, ha, rfl⟩
                apply hB_sub; exact g_emb_mem a
              have hv_not_img : v ∉ Finset.image g_emb t := by
                intro hv_img
                rcases Finset.mem_image.1 hv_img with ⟨a, _, h_eq⟩
                have hB_mem : g_emb a ∈ B := h_img_sub_B (by
                  apply Finset.mem_image.mpr; exact ⟨a, by assumption, rfl⟩)
                rw [Finset.mem_filter] at hB_mem
                rcases hB_mem with ⟨_, ⟨h_ne_v, _⟩⟩
                exact h_ne_v h_eq
              have h_adj_all_compl : ∀ u ∈ Finset.image g_emb t, Gᶜ.Adj v u := by
                intro u hu
                have hB_mem : u ∈ B := h_img_sub_B hu
                rw [Finset.mem_filter] at hB_mem
                rcases hB_mem with ⟨_, ⟨h_ne_v, h_not_adj⟩⟩
                rw [SimpleGraph.compl_adj]
                refine ⟨Ne.symm h_ne_v, ?_⟩
                intro h_adj
                exact h_not_adj h_adj
              have hG_compl_clique_temp : Gᶜ.IsNClique ((s'-1)+1) (insert v (Finset.image g_emb t)) :=
                isNClique_insert_adjacent' Gᶜ (s'-1) (Finset.image g_emb t) v hG_compl_clique hv_not_img h_adj_all_compl
              have h_eq_s' : s' = (s'-1)+1 := by omega
              have hG_compl_clique_s' : Gᶜ.IsNClique s' (insert v (Finset.image g_emb t)) := by
                rw [h_eq_s']; exact hG_compl_clique_temp
              right; exact not_cliqueFree_of_exists_isNClique Gᶜ s' (insert v (Finset.image g_emb t)) hG_compl_clique_s'
  have hP_total : P (r + s) := Nat.strong_induction_on (r + s) hP_induction
  exact hP_total r s rfl hr hs
