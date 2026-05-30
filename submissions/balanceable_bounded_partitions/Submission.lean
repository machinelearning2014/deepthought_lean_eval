import ChallengeDeps
import Submission.Helpers

namespace Submission

open Submission.Helpers

  theorem minimal_balanceable_of_bounded (k : ℕ) (hk : 0 < k) :
      Minimal (fun n : ℕ => 0 < n ∧ ∀ p : n.Partition, Bounded k p → Balanceable p)
        (2 * (Finset.Icc 1 k).lcm id) := by
    set L := (Finset.Icc 1 k).lcm id with hL
    have hLpos : 0 < L := by
      have h1mem : 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have h1dvd : 1 ∣ L := Finset.dvd_lcm (f := id) h1mem
      exact Nat.pos_of_dvd_of_pos h1dvd (by norm_num)
    have hL_ge_k_mul_k_sub_one : L ≥ k * (k-1) := L_ge_k_mul_k_sub_one k hk
    have hpos_2L : 0 < 2 * L := by omega
    have hL_even : 2 ∣ L := by
      by_cases hk1 : k = 1
      · subst hk1; simp
      · have hk2 : 2 ≤ k := by omega
        have h2mem : 2 ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by norm_num, hk2⟩
        exact Finset.dvd_lcm (f := id) h2mem

    rw [minimal_iff_forall_lt]
    constructor
    · -- Part A: P(2L) holds
      constructor
      · exact hpos_2L
      · intro p hBounded
        -- Need: Balanceable p
        have hparts_sum : p.parts.sum = 2 * L := Nat.Partition.parts_sum (p := p)
        have hBounded_parts : ∀ a ∈ p.parts, a ≤ k := hBounded
        have hparts_pos : ∀ a ∈ p.parts, 0 < a := Nat.Partition.parts_pos (p := p)
        let M := p.parts
        have hM_sum : M.sum = 2 * L := hparts_sum
        have hM_pos : ∀ a ∈ M, 0 < a := hparts_pos
        have hM_bounded : ∀ a ∈ M, a ≤ k := hBounded_parts

        -- Special case k=1
        by_cases hk1 : k = 1
        · subst hk1
          have hL1 : L = 1 := by
            simp [hL, Finset.Icc]
          rw [hL1] at hM_sum
          have hall1 : ∀ a ∈ M, a = 1 := by
            intro a ha
            have ha1 : a ≤ 1 := hM_bounded a ha
            have ha_pos : 0 < a := hM_pos a ha
            omega
          have hcard_M_2 : M.card = 2 := by
            calc
              M.card = ∑ a ∈ M, 1 := by simp
              _ = ∑ a ∈ M, a := by
                refine Finset.sum_congr rfl (λ a ha => ?_)
                simp [hall1 a ha]
              _ = M.sum := by simp
              _ = 2 := hM_sum
          have hM_repl : M = {1, 1} :=
            Multiset.eq_replicate.mpr ⟨hcard_M_2, λ a ha => hall1 a ha⟩
          refine ⟨{1}, ?_, ?_⟩
          · have : ({1} : Multiset ℕ) ≤ M := by
              rw [hM_repl]
              simp
            exact this
          · simp

        -- General case: k ≥ 2
        have hk2 : 2 ≤ k := by omega

        -- Convert M to list for indexing
        let l := M.toList
        have hl_len : l.length = M.card := Multiset.length_toList M
        set n := l.length with hn
        have hn_card : n = M.card := hl_len

        -- Lower bound on n: n*k ≥ 2*L
        have hn_times_k_ge_2L : n * k ≥ 2 * L := by
          calc
            n * k = M.card * k := by simp [hn_card]
            _ = ∑ a ∈ M, k := by simp
            _ ≥ ∑ a ∈ M, a := Finset.sum_le_sum (λ a ha => hM_bounded a ha)
            _ = M.sum := by simp
            _ = 2 * L := hM_sum

        by_cases h_min : n * k = 2 * L
        · -- All elements = k. Take L/k copies of k.
          have hall_k : ∀ a ∈ M, a = k := by
            intro a ha
            have ha_pos : 0 < a := hM_pos a ha
            have ha_le_k : a ≤ k := hM_bounded a ha
            by_contra! ha_lt_k
            have : n * k > 2 * L := by
              calc
                n * k = M.card * k := by simp [hn_card]
                _ = ∑ b ∈ M, k := by simp
                _ > ∑ b ∈ M, b := by
                  apply Finset.sum_lt_sum (λ b hb => hM_bounded b hb)
                  exact ⟨a, ha, ha_lt_k⟩
                _ = M.sum := by simp
                _ = 2 * L := hM_sum
            rw [h_min] at this
            omega

          have hL_dvd_k : k ∣ L := by
            have hkmem : k ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hk, le_refl _⟩
            exact Finset.dvd_lcm (f := id) hkmem
          rcases hL_dvd_k with ⟨t, ht⟩
          have ht_pos : t > 0 := by
            intro hzero
            have : L = 0 := by
              rw [ht, hzero, mul_zero]
            exact ne_of_gt hLpos this

          have hM_eq : M = Multiset.replicate n k :=
            Multiset.eq_replicate.mpr ⟨by
              simp [hn_card, Multiset.card_replicate], hall_k⟩

          have h_2t_eq_n : 2*t = n := by
            calc
              2*t = (2*L)/k := by
                rw [ht]
                have : k * t = 2*L := by
                  calc
                    k * t = t * k := mul_comm _ _
                    _ = L := ht
                    _ = 2*L/2 := by omega
                  -- Hmm, this isn't right.
                  sorry
                sorry
              _ = (n*k)/k := by rw [h_min]
              _ = n := by
                have : 0 < k := hk
                exact Nat.mul_div_right _ this

          refine ⟨Multiset.replicate t k, ?_, ?_⟩
          · calc
              Multiset.replicate t k ≤ Multiset.replicate n k :=
                Multiset.replicate_le_replicate (by omega) (le_refl k)
              _ = M := by symm; exact hM_eq
          · simp [ht, smul_eq_mul]

        · -- n*k > 2*L (strict), so n*k ≥ 2*L + 1
          have hn_gt : n * k > 2 * L := by omega
          have hn_k_ge_2L_plus_1 : n * k ≥ 2 * L + 1 := by omega

          -- Key inequality: 2^n > 2*L
          have h_2n_gt_2L : 2 ^ n > 2 * L := by
            by_cases hn4 : n < 4
            · -- n = 3 only possible for k=2 (since n*k > 2L and k≥2)
              have hn3 : n = 3 := by omega
              subst hn3
              have hk_eq_2 : k = 2 := by
                by_contra! hk_gt_2
                have hk3 : 3 ≤ k := by omega
                have : 2*L ≥ 2*k*(k-1) := by
                  have : L ≥ k*(k-1) := hL_ge_k_mul_k_sub_one
                  omega
                have : 3*k > 2*L := hn_gt
                have : 3*k ≤ 2*k*(k-1) := by
                  have hk3' : 3 ≤ 2*(k-1) := by
                    omega
                  nlinarith
                omega
              subst hk_eq_2
              have hL_eq_2 : L = 2 := by
                have : (Finset.Icc 1 2).lcm id = 2 := by native_decide
                rw [this] at hL
                exact this
              rw [hL_eq_2]
              native_decide
            · -- n ≥ 4
              have hn4' : 4 ≤ n := by omega
              have h_2n_ge_n_sq : 2 ^ n ≥ n ^ 2 := two_pow_ge_sq n hn4'
              have hn_ge_k : n ≥ k := by
                by_contra! hn_lt_k
                have : n * k < k * k := mul_lt_mul_of_pos_right hn_lt_k hk
                have : 2*L + 1 > k*k := by
                  calc
                    2*L + 1 ≥ 2*(k*(k-1)) + 1 := by omega
                    _ = 2*k*k - 2*k + 1 := by ring
                    _ > k*k := by
                      have : 0 < k := hk
                      nlinarith
                omega
              have h_n_sq_ge_2L_plus_1 : n ^ 2 ≥ 2 * L + 1 := by
                calc
                  n ^ 2 ≥ n * k := by nlinarith
                  _ ≥ 2 * L + 1 := hn_k_ge_2L_plus_1
              calc
                2 ^ n ≥ n ^ 2 := h_2n_ge_n_sq
                _ ≥ 2 * L + 1 := h_n_sq_ge_2L_plus_1
                _ > 2 * L := by omega

          -- Pigeonhole: Finset (Fin n) → Fin L
          have hL_ne_zero : L ≠ 0 := by omega
          have hcard_lt : Fintype.card (Fin L) < Fintype.card (Finset (Fin n)) := by
            calc
              Fintype.card (Fin L) = L := Fintype.card_fin _
              _ < 2 * L := by
                have : 0 < 2 * L := hpos_2L
                omega
              _ < 2 ^ n := h_2n_gt_2L
              _ = Fintype.card (Finset (Fin n)) := card_finset_fin n

          -- Define f(S) = sum of elements at indices in S, modulo L
          let f : Finset (Fin n) → Fin L := λ S =>
            ⟨(Finset.sum S (λ i => l.get i)) % L, Nat.mod_lt _ hLpos⟩

          rcases Fintype.exists_ne_map_eq_of_card_lt f hcard_lt with ⟨X, Y, hXYne, hXYeq⟩

          -- We have f(X) = f(Y). Need a third subset Z with f(Z) = f(X) = f(Y).
          -- Since 2^n > 2L, the pigeonhole with Fintype (Fin (2L)) would give 3 subsets.
          -- But we used Fin L, so we only get 2 subsets with same residue.
          -- We need to argue there's a third one.

          -- Actually, with card inequality Fintype.card (Fin L) < Fintype.card (Finset (Fin n)):
          -- the pigeonhole gives at least 2 subsets per residue ON AVERAGE.
          -- But 2^n > 2L doesn't guarantee 3 in a class.

          -- FIX: Use the stronger inequality 2^n > 2L to get 3 subsets.
          -- Since 2^n > 2L, the average is > 2. So some residue has ≥ 3 subsets.

          -- Let's find the residue class with ≥ 3 subsets.
          -- Define g : Finset (Fin n) → Fin (2*L)
          sorry

      sorry

    · -- Part B: Minimality
      intro y hy
      intro h
      rcases h with ⟨hypos, hall⟩

      by_cases h_odd : Odd y
      · -- y is odd: partition into y copies of 1
        have h_not_even : ¬ 2 ∣ y := by
          intro h_even
          have : Even y := h_even
          rcases this with ⟨m, hm⟩
          have h_odd' : ¬ Even y := h_odd
          exact h_odd' ⟨m, hm⟩

        let p : y.Partition :=
          Nat.Partition.mk (Multiset.replicate y 1)
            (by
              intro a ha
              simp at ha
              subst ha
              omega)
            (by simp)

        have hBounded_p : Bounded k p := by
          intro a ha
          simp at ha
          subst ha
          exact hk

        have hNotBal : ¬ Balanceable p := by
          intro hbal
          rcases hbal with ⟨S, hSle, hseq⟩
          have : 2 ∣ y := by
            rw [hseq]
            exact ⟨S.sum, by ring⟩
          exact h_not_even this

        exact ⟨p, hBounded_p, hNotBal⟩

      · -- y is even: y = 2*m
        have hy_even : 2 ∣ y := by
          have hmod : y % 2 = 0 := by
            have hmod' := Nat.mod_two_eq_zero_or_one y
            rcases hmod' with (h | h)
            · exact h
            · exfalso
              apply h_odd
              have : Odd y := ⟨y/2, by
                have : y = 2*(y/2) + y%2 := Nat.div_add_mod y 2
                rw [h, this]
                omega⟩
              exact this
          exact Nat.dvd_of_mod_eq_zero hmod

        rcases hy_even with ⟨m, hm⟩
        have hm_pos : 0 < m := by
          by_contra! hmz
          have : y = 0 := by
            rw [hm, hmz, mul_zero]
          omega
        have hm_lt_L : m < L := by
          by_contra! hm_ge
          have : 2 * m ≥ 2 * L := by omega
          have : y ≥ 2 * L := by
            rw [hm]
            omega
          omega

        rcases exists_i_not_dvd_of_lt_lcm k m hm_lt_L with ⟨i, hi_mem, hi_not_dvd⟩
        have hi_le_k : i ≤ k := (Finset.mem_Icc.mp hi_mem).2
        have hi_pos : 0 < i := (Finset.mem_Icc.mp hi_mem).1

        by_cases hi_dvd_y : i ∣ y
        · -- Case 1: i | y
          let q := y / i
          have hy_eq : q * i = y := by
            symm; exact Nat.mul_div_cancel' hi_dvd_y
          have hq_pos : 0 < q :=
            Nat.pos_of_dvd_of_pos hi_dvd_y hi_pos

          let p : y.Partition :=
            Nat.Partition.mk (Multiset.replicate q i)
              (by
                intro a ha
                simp at ha
                subst ha
                exact hi_pos)
              (by
                simp [Multiset.sum_replicate, smul_eq_mul, hy_eq, mul_comm])

          have hBounded_p : Bounded k p := by
            intro a ha
            simp at ha
            subst ha
            exact hi_le_k

          have hNotBal : ¬ Balanceable p := by
            intro hbal
            rcases hbal with ⟨S, hSle, hseq⟩
            have hSsum_eq_m : S.sum = m := by
              have : 2 * S.sum = y := hseq
              rw [hm] at this
              omega
            have hi_dvd_Ssum : i ∣ S.sum := by
              have hall_i : ∀ a ∈ S, a = i := by
                intro a ha
                have ha_mem : a ∈ p.parts := Multiset.mem_of_le hSle ha
                simp [p] at ha_mem
                exact ha_mem
              have hS_repl : S = Multiset.replicate (S.card) i :=
                Multiset.eq_replicate.mpr ⟨Multiset.card_replicate _ _, hall_i⟩
              have : S.sum = S.card * i := by
                simp [hS_repl, smul_eq_mul]
              rw [this]
              exact ⟨S.card, rfl⟩
            rw [hSsum_eq_m] at hi_dvd_Ssum
            exact hi_not_dvd hi_dvd_Ssum

          exact ⟨p, hBounded_p, hNotBal⟩

        · -- Case 2: i ∤ y
          let q := y / i
          let r := y % i
          have hy_div : y = q * i + r := Nat.div_add_mod y i
          have hr_pos : 0 < r := by
            have hr_ne_zero : r ≠ 0 := Nat.mod_ne_zero_of_not_dvd hi_dvd_y
            omega
          have hr_lt_i : r < i := Nat.mod_lt y hi_pos
          have hr_le_k : r ≤ k := by omega

          let p : y.Partition :=
            Nat.Partition.mk (Multiset.replicate q i + {r})
              (by
                intro a ha
                rw [Multiset.mem_add] at ha
                rcases ha with (ha | ha)
                · simp at ha; subst ha; exact hi_pos
                · simp at ha; subst ha; omega)
              (by
                simp [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, hy_div, mul_comm])

          have hBounded_p : Bounded k p := by
            intro a ha
            rw [Multiset.mem_add] at ha
            rcases ha with (ha | ha)
            · simp at ha; subst ha; exact hi_le_k
            · simp at ha; subst ha; exact hr_le_k

          have hNotBal : ¬ Balanceable p := by
            intro hbal
            rcases hbal with ⟨S, hSle, hseq⟩
            have hSsum_eq_m : S.sum = m := by
              have : 2 * S.sum = y := hseq
              rw [hm] at this
              omega

            let cnt_i := (S.filter (λ a => a = i)).card

            have hSsum_decomp : S.sum = cnt_i * i + (if r ∈ S then r else 0) := by
              have h_filter_eq : (S.filter (λ a => a = i)).sum = cnt_i * i := by
                have h_repl : S.filter (λ a => a = i) = Multiset.replicate cnt_i i :=
                  Multiset.eq_replicate.mpr ⟨by simp [cnt_i], λ a ha => by
                    simp at ha; exact ha⟩
                simp [h_repl, smul_eq_mul]
              have h_filter_neq : (S.filter (λ a => a ≠ i)).sum = (if r ∈ S then r else 0) := by
                by_cases hr_mem : r ∈ S
                · have h_singleton : S.filter (λ a => a ≠ i) = {r} := by
                    apply Multiset.eq_singleton.mpr
                    constructor
                    · intro a ha
                      simp at ha
                      rcases ha with ⟨ha_mem, ha_ne⟩
                      have ha_in_parts : a ∈ p.parts := Multiset.mem_of_le hSle ha_mem
                      rw [Multiset.mem_add] at ha_in_parts
                      rcases ha_in_parts with (ha_i | ha_r)
                      · exfalso; apply ha_ne; simp at ha_i; exact ha_i
                      · simp at ha_r; subst ha_r; rfl
                    · exact hr_mem
                  simp [h_singleton]
                · simp [hr_mem]
              calc
                S.sum = (S.filter (λ a => a = i) + S.filter (λ a => a ≠ i)).sum := by
                  rw [Multiset.filter_add_filter (λ a => a = i) S, Multiset.add_comm]
                _ = (S.filter (λ a => a = i)).sum + (S.filter (λ a => a ≠ i)).sum := Multiset.sum_add _ _
                _ = cnt_i * i + (if r ∈ S then r else 0) := by rw [h_filter_eq, h_filter_neq]

            rw [hSsum_eq_m] at hSsum_decomp

            by_cases hr_mem : r ∈ S
            · rw [if_pos hr_mem] at hSsum_decomp
              -- m = cnt_i * i + r
              have : 2*(cnt_i*i + r) = q*i + r := by
                calc
                  2*(cnt_i*i + r) = 2*m := by rw [hSsum_decomp]
                  _ = y := hm.symm ▸ rfl
                  _ = q*i + r := hy_div
              have h_eq : (q - 2*cnt_i) * i = r := by
                calc
                  (q - 2*cnt_i) * i = q*i - 2*cnt_i*i := by ring
                  _ = (q*i + r) - (2*cnt_i*i + r) := by omega
                  _ = y - 2*(cnt_i*i + r) := by
                    rw [hy_div, hSsum_decomp]
                    ring
                  _ = y - y := by
                    rw [hm]
                    calc
                      2*(cnt_i*i + r) = 2*m := by rw [hSsum_decomp]
                      _ = y := hm.symm
                  _ = 0 := by omega
              have : r = 0 := by
                have : (q - 2*cnt_i) * i = 0 := h_eq
                rcases mul_eq_zero.mp this with (h | h)
                · -- q - 2*cnt_i = 0
                  have : r = 0 := by
                    calc
                      r = (q - 2*cnt_i) * i := by symm; exact h_eq
                      _ = 0 * i := by rw [h]
                      _ = 0 := by simp
                  exact this
                · -- i = 0, contradicts hi_pos
                  exact absurd hi_pos (NeZero.ne i)
              omega
            · rw [if_neg hr_mem] at hSsum_decomp
              have : i ∣ m := ⟨cnt_i, hSsum_decomp⟩
              exact hi_not_dvd this

          exact ⟨p, hBounded_p, hNotBal⟩

  end Submission

end Submission
