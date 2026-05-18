import Mathlib
open SimpleGraph
open Finset

set_option autoImplicit false

theorem finite_graph_ramsey_theorem :
    ∀ r s : ℕ, 2 ≤ r → 2 ≤ s →
    ∃ n : ℕ, ∀ G : SimpleGraph (Fin n),
      ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s := by
  -- Lemma: G.CliqueFree 2 means G has no edges between distinct vertices
  have h_no_edges {V : Type} [DecidableEq V] {G : SimpleGraph V} (hcf : G.CliqueFree 2) {x y : V} (hne : x ≠ y) :
      ¬ G.Adj x y := by
    intro hadj
    -- Build {x, y} as a Finset and show it's a 2-clique, contradicting hcf
    let s : Finset V := {x, y}
    have h_isNClique : G.IsNClique 2 s := by
      rw [isNClique_iff]
      constructor
      · rw [isClique_iff]
        intro a ha b hb hne'
        simp [s] at ha hb
        rcases ha with (rfl | rfl) <;> rcases hb with (rfl | rfl) <;>
          try { exact (hne' rfl).elim }
        · exact hadj
        · exact G.symm hadj
      · simp [s, hne]
    exact hcf s h_isNClique

  -- Lemma: CliqueFree 2 in complement means the graph is complete (all distinct vertices adjacent)
  have h_complete_from_compl {V : Type} [DecidableEq V] {G : SimpleGraph V} (hcf : Gᶜ.CliqueFree 2) {x y : V} (hne : x ≠ y) :
      G.Adj x y := by
    have h_no_compl_edge : ¬ Gᶜ.Adj x y := h_no_edges hcf hne
    rw [compl_adj] at h_no_compl_edge
    -- h_no_compl_edge: ¬ (x ≠ y ∧ ¬ G.Adj x y)
    -- equivalent to x = y ∨ G.Adj x y
    -- since x ≠ y, we get G.Adj x y
    simpa [hne] using h_no_compl_edge

  -- Lemma: for injective f, H := comap f G, then Hᶜ.Adj i j ↔ Gᶜ.Adj (f i) (f j)
  have h_comap_compl_adj {V W : Type} {G : SimpleGraph W} {f : V → W} (hf : Function.Injective f) (i j : V) :
      (SimpleGraph.comap f G)ᶜ.Adj i j ↔ Gᶜ.Adj (f i) (f j) := by
    rw [compl_adj, compl_adj, SimpleGraph.comap]
    -- LHS: i ≠ j ∧ ¬ G.Adj (f i) (f j)
    -- RHS: f i ≠ f j ∧ ¬ G.Adj (f i) (f j)
    constructor
    · rintro ⟨hne, h⟩
      exact ⟨by intro heq; apply hne; exact hf heq, h⟩
    · rintro ⟨hne, h⟩
      exact ⟨by intro heq; apply hne; rw [heq], h⟩

  -- Lemma: for injective f, an n-clique in comap f G maps to an n-clique in G
  have h_map_nclique {V W : Type} {G : SimpleGraph W} {f : V → W} (hf : Function.Injective f) {n : ℕ} {t : Finset V}
      (ht : (SimpleGraph.comap f G).IsNClique n t) : G.IsNClique n (t.map ⟨f, hf⟩) := by
    rw [isNClique_iff] at ht ⊢
    rcases ht with ⟨hclique, hcard⟩
    constructor
    · -- IsClique condition
      rw [isClique_iff] at hclique ⊢
      intro x hx y hy hne
      rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
      rcases Finset.mem_map.mp hy with ⟨j, hj, rfl⟩
      have hne' : i ≠ j := by
        intro heq; apply hne; rw [heq]
      -- hclique: (t : Set V).Pairwise (comap f G).Adj
      -- which means ∀ ⦃x⦄, x ∈ (t : Set V) → ∀ ⦃y⦄, y ∈ (t : Set V) → x ≠ y → (comap f G).Adj x y
      have h_adj := hclique (by exact hi) (by exact hj) hne'
      -- h_adj: (comap f G).Adj i j = G.Adj (f i) (f j)
      simpa [SimpleGraph.comap] using h_adj
    · -- cardinality preserved by embedding
      simp [hcard]

  -- Lemma: for injective f, an n-clique in Hᶜ maps to an n-clique in Gᶜ
  have h_map_nclique_compl {V W : Type} {G : SimpleGraph W} {f : V → W} (hf : Function.Injective f) {n : ℕ}
      {t : Finset V} (ht : (SimpleGraph.comap f G)ᶜ.IsNClique n t) : Gᶜ.IsNClique n (t.map ⟨f, hf⟩) := by
    rw [isNClique_iff] at ht ⊢
    rcases ht with ⟨hclique, hcard⟩
    constructor
    · rw [isClique_iff] at hclique ⊢
      intro x hx y hy hne
      rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
      rcases Finset.mem_map.mp hy with ⟨j, hj, rfl⟩
      have hne' : i ≠ j := by
        intro heq; apply hne; rw [heq]
      have h_adj := hclique (by exact hi) (by exact hj) hne'
      -- h_adj: Hᶜ.Adj i j, need Gᶜ.Adj (⟨f, hf⟩ i) (⟨f, hf⟩ j) which is Gᶜ.Adj (f i) (f j)
      -- Use simpa [DFunLike.coe] or just simpa since the embedding coerces to f
      simpa using (h_comap_compl_adj hf i j).mp h_adj
    · simp [hcard]

  -- Lemma: Ramsey bound is at least 2
  have h_bound_ge_two {r' s' n' : ℕ} (hr' : 2 ≤ r') (hs' : 2 ≤ s')
      (hn' : ∀ G : SimpleGraph (Fin n'), ¬ G.CliqueFree r' ∨ ¬ Gᶜ.CliqueFree s') : 2 ≤ n' := by
    by_contra! h
    have hn_lt_2 : n' < 2 := by omega
    -- n' is 0 or 1, so Fin n' has at most 1 vertex
    let G : SimpleGraph (Fin n') := ⊥
    rcases hn' G with (h1 | h2)
    · -- ¬ G.CliqueFree r', so there's an r'-clique in the empty graph
      rw [CliqueFree] at h1
      push Not at h1
      rcases h1 with ⟨t, ht⟩
      rw [isNClique_iff] at ht
      rcases ht with ⟨hclique, hcard⟩
      -- t is a Finset of Fin n' with t.card = r' ≥ 2
      have hcard_univ : (Finset.univ : Finset (Fin n')).card = n' := by simp
      have ht_le : t.card ≤ (Finset.univ : Finset (Fin n')).card := Finset.card_le_univ t
      rw [hcard_univ] at ht_le
      omega
    · -- symmetric: ¬ Gᶜ.CliqueFree s'
      rw [CliqueFree] at h2
      push Not at h2
      rcases h2 with ⟨t, ht⟩
      rw [isNClique_iff] at ht
      rcases ht with ⟨hclique, hcard⟩
      have hcard_univ : (Finset.univ : Finset (Fin n')).card = n' := by simp
      have ht_le : t.card ≤ (Finset.univ : Finset (Fin n')).card := Finset.card_le_univ t
      rw [hcard_univ] at ht_le
      omega

  -- Helper lemma: from a Finset of size ≥ M on a linearly ordered type,
  -- we can get an injective function Fin M → α with image in the Finset
  have h_embed_from_finset {α : Type} [DecidableEq α] [LinearOrder α] {M : ℕ} (s : Finset α) (hM : M ≤ s.card) :
      ∃ f : Fin M → α, Function.Injective f ∧ ∀ i, f i ∈ s := by
    -- Sort s and take the first M elements
    let l := s.sort (· ≤ ·)
    have hl_nodup : l.Nodup := Finset.sort_nodup _ (· ≤ ·)
    have hl_len : l.length = s.card := Finset.length_sort (· ≤ ·) (s := s)
    have hM_len : M ≤ l.length := by rw [hl_len]; exact hM
    -- Define f i = i-th element of l using list get
    let f (i : Fin M) : α :=
      l.get (⟨i.val, by
        have hi : (i : ℕ) < M := i.2
        omega⟩ : Fin l.length)
    have hf_inj : Function.Injective f := by
      -- Using nodup_iff_injective_getElem
      have hinj := (List.nodup_iff_injective_getElem.mp hl_nodup)
      intro i j heq
      -- Embed Fin M into Fin l.length
      let i' : Fin l.length := ⟨i.val, by
        have hi : (i : ℕ) < M := i.2; omega⟩
      let j' : Fin l.length := ⟨j.val, by
        have hj : (j : ℕ) < M := j.2; omega⟩
      have hval : i' = j' := hinj (by simpa [f, i', j'] using heq)
      apply Fin.ext
      simpa using congrArg Fin.val hval
    refine ⟨f, hf_inj, λ i => ?_⟩
    -- Show f i ∈ s
    have hmem : f i ∈ s := by
      dsimp [f]
      rw [← Finset.mem_sort (· ≤ ·)]
      apply List.get_mem
    exact hmem

  -- Main proof: strong induction on r + s
  intro r s hr hs
  -- Define the predicate for strong induction
  let P (n : ℕ) : Prop :=
    ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → r + s = n →
    ∃ n' : ℕ, ∀ G : SimpleGraph (Fin n'), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s
  have hP : P (r + s) := by
    refine Nat.strong_induction_on (r + s) (λ t IH => ?_)
    intro r s hr hs hsum
    -- Now r, s are the variables for the current induction step
    -- IH: ∀ m < t, P m  where P(m) = ∀ r s, 2 ≤ r → 2 ≤ s → r+s = m → ∃ n', ...
    -- hsum: r + s = t

    -- Base case r = 2
    by_cases hr2 : r = 2
    · subst hr2
      refine ⟨s, λ G => ?_⟩
      by_cases hcf : G.CliqueFree 2
      · right
        rw [CliqueFree]
        push Not
        refine ⟨Finset.univ, ?_⟩
        rw [isNClique_iff]
        constructor
        · rw [isClique_iff]
          intro x hx y hy hne
          simp at hx hy
          rw [compl_adj]
          exact ⟨hne, h_no_edges hcf hne⟩
        · simp
      · left; exact hcf

    -- Base case s = 2
    by_cases hs2 : s = 2
    · subst hs2
      refine ⟨r, λ G => ?_⟩
      by_cases hcf : Gᶜ.CliqueFree 2
      · left
        rw [CliqueFree]
        push Not
        refine ⟨Finset.univ, ?_⟩
        rw [isNClique_iff]
        constructor
        · rw [isClique_iff]
          intro x hx y hy hne
          simp at hx hy
          exact h_complete_from_compl hcf hne
        · simp
      · right; exact hcf

    -- Inductive step: r > 2 and s > 2
    have h_rpred : 2 ≤ r - 1 := by
      by_cases h : 2 < r
      · omega
      · have : r = 2 := by omega
        exact (hr2 this).elim
    have h_spred : 2 ≤ s - 1 := by
      by_cases h : 2 < s
      · omega
      · have : s = 2 := by omega
        exact (hs2 this).elim

    have h_sum1 : (r - 1) + s < r + s := by omega
    have h_sum2 : r + (s - 1) < r + s := by omega

    have h_lt1 : (r - 1) + s < t := by rw [← hsum]; exact h_sum1
    have h_lt2 : r + (s - 1) < t := by rw [← hsum]; exact h_sum2

    -- IH h_lt1 : P ((r-1)+s) = ∀ r' s', 2≤r' → 2≤s' → r'+s' = (r-1)+s → ...
    -- Apply with r' := r-1, s' := s
    rcases IH ((r - 1) + s) h_lt1 (r - 1) s h_rpred hs rfl with ⟨M, hM⟩
    rcases IH (r + (s - 1)) h_lt2 r (s - 1) hr h_spred rfl with ⟨N, hN⟩

    have hM2 : 2 ≤ M := h_bound_ge_two h_rpred hs hM
    have hN2 : 2 ≤ N := h_bound_ge_two hr h_spred hN

    have hpos : 0 < M + N := by omega

    refine ⟨M + N, λ G => ?_⟩
    classical
    -- Pick vertex 0
    let zero : Fin (M + N) := ⟨0, hpos⟩

    -- Partition the remaining vertices into neighbors (A) and non-neighbors (B) of zero
    let A : Finset (Fin (M + N)) := ((Finset.univ : Finset (Fin (M + N))).erase zero).filter (G.Adj zero)
    let B : Finset (Fin (M + N)) := ((Finset.univ : Finset (Fin (M + N))).erase zero).filter (λ v => ¬ G.Adj zero v)

    -- Cardinality analysis: A and B partition univ \ {zero}
    have h_erase_card : ((Finset.univ : Finset (Fin (M + N))).erase zero).card = M + N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ zero)]
      simp

    have h_card_AB : A.card + B.card = ((Finset.univ : Finset (Fin (M + N))).erase zero).card := by
      dsimp [A, B]
      simpa using Finset.card_filter_add_card_filter_not (λ v => G.Adj zero v)
        (s := (Finset.univ : Finset (Fin (M + N))).erase zero)

    have h_card_total : A.card + B.card = M + N - 1 := by
      rw [h_card_AB, h_erase_card]

    -- Pigeonhole principle: either |A| ≥ M or |B| ≥ N
    have h_cases : M ≤ A.card ∨ N ≤ B.card := by
      by_contra! h
      rcases h with ⟨hA, hB⟩
      -- hA: A.card < M, hB: B.card < N
      -- Then A.card + B.card < M + N
      -- But A.card + B.card = M + N - 1
      have h_sum_lt : A.card + B.card < M + N := by omega
      rw [h_card_total] at h_sum_lt
      omega

    rcases h_cases with (hA | hB)
    · -- Case: |A| ≥ M. Apply IH for (r-1, s) to pullback subgraph on A
      rcases h_embed_from_finset A hA with ⟨f, hf_inj, hf_mem_A⟩

      -- From hf_mem_A, we get: f i ≠ zero and G.Adj zero (f i)
      have hf_ne_zero : ∀ i, f i ≠ zero := by
        intro i
        have hi := hf_mem_A i
        simp [A] at hi
        exact hi.1
      have hf_adj_zero : ∀ i, G.Adj zero (f i) := by
        intro i
        have hi := hf_mem_A i
        simp [A] at hi
        exact hi.2

      let H : SimpleGraph (Fin M) := SimpleGraph.comap f G

      rcases hM H with (hH | hH)
      · -- H has an (r-1)-clique → add vertex zero to get an r-clique in G
        left
        rw [CliqueFree] at hH
        push Not at hH
        rcases hH with ⟨t, ht⟩
        have h_map : G.IsNClique (r - 1) (t.map ⟨f, hf_inj⟩) := h_map_nclique hf_inj ht
        rw [isNClique_iff] at h_map
        rcases h_map with ⟨hclique_map, hcard_map⟩
        -- Insert zero into the mapped set
        let t' : Finset (Fin (M + N)) := insert zero (t.map ⟨f, hf_inj⟩)
        have h_zero_notin_map : zero ∉ t.map ⟨f, hf_inj⟩ := by
          intro h
          rcases Finset.mem_map.mp h with ⟨i, hi, h_eq⟩
          apply hf_ne_zero i
          exact h_eq
        have hcard_t' : t'.card = r := by
          rw [Finset.card_insert_of_notMem h_zero_notin_map, hcard_map]
          omega
        -- Clique condition for t'
        have hclique_t' : G.IsClique (t' : Set (Fin (M + N))) := by
          rw [isClique_iff]
          intro x hx y hy hne
          rw [Finset.mem_coe, Finset.mem_insert] at hx hy
          rcases hx with (rfl | hx)
          · -- x = zero
            rcases hy with (rfl | hy)
            · exact (hne rfl).elim
            · -- y = f j for some j
              rcases Finset.mem_map.mp hy with ⟨j, hj, rfl⟩
              exact hf_adj_zero j
          · -- x = f i for some i
            rcases hy with (rfl | hy)
            · -- y = zero
              rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
              exact G.symm (hf_adj_zero i)
            · -- y = f j for some j
              rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
              rcases Finset.mem_map.mp hy with ⟨j, hj, rfl⟩
              have hne' : i ≠ j := by
                intro heq; apply hne; rw [heq]
              -- Use the clique condition from h_map
              rw [isClique_iff] at hclique_map
              exact hclique_map (by
                apply Finset.mem_coe.mpr
                apply Finset.mem_map.mpr
                exact ⟨i, hi, rfl⟩) (by
                apply Finset.mem_coe.mpr
                apply Finset.mem_map.mpr
                exact ⟨j, hj, rfl⟩) (by intro h; apply hne'; exact hf_inj h)
        -- Now we have G.IsNClique r t'
        rw [CliqueFree]
        push Not
        refine ⟨t', ?_⟩
        rw [isNClique_iff]
        exact ⟨hclique_t', hcard_t'⟩
      · -- Hᶜ has an s-clique → Gᶜ has an s-clique (using injectivity of f)
        right
        rw [CliqueFree] at hH
        push Not at hH
        rcases hH with ⟨t, ht⟩
        have h_map : Gᶜ.IsNClique s (t.map ⟨f, hf_inj⟩) := h_map_nclique_compl hf_inj ht
        rw [CliqueFree]
        push Not
        exact ⟨t.map ⟨f, hf_inj⟩, h_map⟩

    · -- Case: |B| ≥ N. Symmetric argument, apply IH for (r, s-1)
      rcases h_embed_from_finset B hB with ⟨f, hf_inj, hf_mem_B⟩

      -- From hf_mem_B, we get: f i ≠ zero and ¬ G.Adj zero (f i)
      have hf_ne_zero : ∀ i, f i ≠ zero := by
        intro i
        have hi := hf_mem_B i
        simp [B] at hi
        exact hi.1
      have hf_not_adj_zero : ∀ i, ¬ G.Adj zero (f i) := by
        intro i
        have hi := hf_mem_B i
        simp [B] at hi
        exact hi.2

      let H : SimpleGraph (Fin N) := SimpleGraph.comap f G

      rcases hN H with (hH | hH)
      · -- H has an r-clique → G has an r-clique
        left
        rw [CliqueFree] at hH
        push Not at hH
        rcases hH with ⟨t, ht⟩
        have h_map : G.IsNClique r (t.map ⟨f, hf_inj⟩) := h_map_nclique hf_inj ht
        rw [CliqueFree]
        push Not
        exact ⟨t.map ⟨f, hf_inj⟩, h_map⟩
      · -- Hᶜ has an (s-1)-clique → add vertex zero to get an s-clique in Gᶜ
        right
        rw [CliqueFree] at hH
        push Not at hH
        rcases hH with ⟨t, ht⟩
        have h_map : Gᶜ.IsNClique (s - 1) (t.map ⟨f, hf_inj⟩) := h_map_nclique_compl hf_inj ht
        rw [isNClique_iff] at h_map
        rcases h_map with ⟨hclique_map, hcard_map⟩
        -- Insert zero into the mapped set
        let t' : Finset (Fin (M + N)) := insert zero (t.map ⟨f, hf_inj⟩)
        have h_zero_notin_map : zero ∉ t.map ⟨f, hf_inj⟩ := by
          intro h
          rcases Finset.mem_map.mp h with ⟨i, hi, h_eq⟩
          apply hf_ne_zero i
          exact h_eq
        have hcard_t' : t'.card = s := by
          rw [Finset.card_insert_of_notMem h_zero_notin_map, hcard_map]
          omega
        -- Clique condition for t' in Gᶜ
        have hclique_t' : Gᶜ.IsClique (t' : Set (Fin (M + N))) := by
          rw [isClique_iff]
          intro x hx y hy hne
          rw [Finset.mem_coe, Finset.mem_insert] at hx hy
          rcases hx with (rfl | hx)
          · -- x = zero
            rcases hy with (rfl | hy)
            · exact (hne rfl).elim
            · -- y = f j for some j
              rcases Finset.mem_map.mp hy with ⟨j, hj, rfl⟩
              rw [compl_adj]
              exact ⟨(hf_ne_zero j).symm, hf_not_adj_zero j⟩
          · -- x = f i for some i
            rcases hy with (rfl | hy)
            · -- y = zero
              rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
              rw [compl_adj]
              exact ⟨hf_ne_zero i, λ h => hf_not_adj_zero i (G.symm h)⟩
            · -- y = f j for some j
              rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
              rcases Finset.mem_map.mp hy with ⟨j, hj, rfl⟩
              have hne' : i ≠ j := by
                intro heq; apply hne; rw [heq]
              -- Use the clique condition from h_map (which is about Gᶜ)
              rw [isClique_iff] at hclique_map
              exact hclique_map (by
                apply Finset.mem_coe.mpr
                apply Finset.mem_map.mpr
                exact ⟨i, hi, rfl⟩) (by
                apply Finset.mem_coe.mpr
                apply Finset.mem_map.mpr
                exact ⟨j, hj, rfl⟩) (by intro h; apply hne'; exact hf_inj h)
        -- Now we have Gᶜ.IsNClique s t'
        rw [CliqueFree]
        push Not
        refine ⟨t', ?_⟩
        rw [isNClique_iff]
        exact ⟨hclique_t', hcard_t'⟩
  -- Use the proven predicate for the original r, s
  exact hP r s hr hs rfl
