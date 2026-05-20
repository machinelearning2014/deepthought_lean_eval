import Mathlib
open Multiset
open Finset
open Nat

lemma foldr_max_singleton (y : ℕ) : Multiset.foldr max 0 ({y} : Multiset ℕ) = y := by
  simp

lemma foldr_max_replicate_start (q k a : ℕ) (hq : q > 0) : Multiset.foldr max a (Multiset.replicate q k) = max k a := by
  induction q generalizing a with
  | zero => omega
  | succ q ih =>
    rw [Multiset.replicate_succ, Multiset.foldr_cons]
    by_cases hq' : q = 0
    · subst q; simp
    · have hqpos : q > 0 := by omega
      rw [ih a hqpos]
      simp

lemma foldr_max_replicate_zero (q k : ℕ) (hq : q > 0) : Multiset.foldr max 0 (Multiset.replicate q k) = k := by
  have h := foldr_max_replicate_start q k 0 hq
  simpa [max_eq_left (by omega : 0 ≤ k)] using h

lemma foldr_max_replicate_add_singleton (q k r : ℕ) (hq : q > 0) :
    Multiset.foldr max 0 (Multiset.replicate q k + {r}) = max k r := by
  rw [Multiset.foldr_add, foldr_max_singleton]
  have h' : Multiset.foldr max r (Multiset.replicate q k) = max k r :=
    foldr_max_replicate_start q k r hq
  simpa using h'

lemma foldr_max_ge_all (s : Multiset ℕ) (M : ℕ) (h : ∀ a ∈ s, a ≤ M) : Multiset.foldr max 0 s ≤ M := by
  induction' s using Multiset.induction_on with a s ih
  · simp
  · rw [Multiset.foldr_cons]
    have ha : a ≤ M := h a (by simp)
    have hs : Multiset.foldr max 0 s ≤ M := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    exact max_le ha hs

lemma lcm_Icc_pos (k : ℕ) (hk : 0 < k) : 0 < Finset.lcm (Finset.Icc 1 k) id := by
  have h1 : (1 : ℕ) ∈ Finset.Icc (1 : ℕ) k := Finset.mem_Icc.mpr ⟨by omega, hk⟩
  have h1_dvd_lcm : (1 : ℕ) ∣ (Finset.Icc 1 k).lcm id := Finset.dvd_lcm (f := id) h1
  have hpos : 0 < (Finset.Icc 1 k).lcm id := by
    by_contra! hzero
    have : (Finset.Icc 1 k).lcm id = 0 := by omega
    rw [Finset.lcm_eq_zero_iff] at this
    rcases this with ⟨x, hx, hx0⟩
    have : id x = 0 := hx0
    have hxpos : 1 ≤ x := (Finset.mem_Icc.mp hx).1
    simp at this
    omega
  exact hpos

lemma lcm_Icc_dvd_lcm_Icc (maxPart k : ℕ) (h : maxPart ≤ k) :
    Finset.lcm (Finset.Icc 1 maxPart) id ∣ Finset.lcm (Finset.Icc 1 k) id := by
  apply Finset.lcm_dvd
  intro a ha
  rcases Finset.mem_Icc.mp ha with ⟨ha1, ha2⟩
  have ha_mem : a ∈ Finset.Icc (1 : ℕ) k := Finset.mem_Icc.mpr ⟨ha1, Nat.le_trans ha2 h⟩
  exact Finset.dvd_lcm (f := id) ha_mem

lemma lcm_Icc_ge (y : ℕ) (hy : 0 < y) : y ≤ (Finset.Icc 1 y).lcm id := by
  have hymem : y ∈ Finset.Icc (1 : ℕ) y := Finset.mem_Icc.mpr ⟨by omega, le_refl y⟩
  have h_dvd : y ∣ (Finset.Icc 1 y).lcm id := Finset.dvd_lcm (f := id) hymem
  have hpos : 0 < (Finset.Icc 1 y).lcm id := by
    have h1 : (1 : ℕ) ∈ Finset.Icc (1 : ℕ) y := Finset.mem_Icc.mpr ⟨by omega, hy⟩
    have h1_dvd : (1 : ℕ) ∣ (Finset.Icc 1 y).lcm id := Finset.dvd_lcm (f := id) h1
    by_contra! hzero
    have : (Finset.Icc 1 y).lcm id = 0 := by omega
    rw [Finset.lcm_eq_zero_iff] at this
    rcases this with ⟨x, hx, hx0⟩
    have : id x = 0 := hx0
    have hxpos : 1 ≤ x := (Finset.mem_Icc.mp hx).1
    simp at this
    omega
  exact Nat.le_of_dvd hpos h_dvd

lemma lcm_Icc_foldr_replicate_one (y : ℕ) (hypos : 0 < y) : (Finset.Icc 1 (Multiset.foldr max 0 (Multiset.replicate y 1))).lcm id = 1 := by
  have h_max : Multiset.foldr max 0 (Multiset.replicate y 1) = 1 := by
    have hcalc := foldr_max_replicate_zero y 1 hypos
    simpa using hcalc
  rw [h_max]
  simp

lemma foldr_max_parts_to_k (parts : Multiset ℕ) (k : ℕ) (h_maxPart_eq : Multiset.foldr max 0 parts = k) :
    (Finset.Icc 1 (Multiset.foldr max 0 parts)).lcm id = (Finset.Icc 1 k).lcm id := by
  rw [h_maxPart_eq]

namespace LeanEval
namespace Combinatorics

def Bounded (k : ℕ) {n : ℕ} (p : n.Partition) : Prop :=
  ∀ a, a ∈ p.parts → a ≤ k

def Balanceable {n : ℕ} (p : n.Partition) : Prop :=
  2 * (Finset.Icc 1 (Multiset.foldr max 0 p.parts)).lcm id ∣ n

end Combinatorics
end LeanEval

open LeanEval.Combinatorics

theorem minimal_balanceable_of_bounded (k : ℕ) (hk : 0 < k) :
    Minimal (fun n => 0 < n ∧ ∀ p : n.Partition, Bounded k p → Balanceable p) (2 * (Finset.Icc 1 k).lcm id) := by
  let L := (Finset.Icc 1 k).lcm id
  have hLpos : 0 < L := lcm_Icc_pos k hk
  have h2Lpos : 0 < 2 * L := by omega
  unfold Minimal
  constructor
  · -- Part 1: Show P(2L) holds
    refine ⟨h2Lpos, ?_⟩
    intro p hbounded
    dsimp [Balanceable]
    let maxPart := Multiset.foldr max 0 p.parts
    have hmaxPart_le_k : maxPart ≤ k := by
      dsimp [maxPart]
      apply foldr_max_ge_all p.parts k
      intro a ha
      exact hbounded a ha
    have h_lcm_dvd : (Finset.Icc 1 maxPart).lcm id ∣ L := by
      dsimp [L]
      exact lcm_Icc_dvd_lcm_Icc maxPart k hmaxPart_le_k
    have h_mul_dvd : 2 * (Finset.Icc 1 maxPart).lcm id ∣ 2 * L :=
      Nat.mul_dvd_mul_left 2 h_lcm_dvd
    exact h_mul_dvd
  · -- Part 2: Show minimality
    intro y hy
    rcases hy with ⟨hypos, hyprop⟩
    intro hyle
    by_contra! hlt
    have h_ndvd_raw : ¬ (2 * (Finset.Icc 1 k).lcm id ∣ y) := by
      intro h_dvd
      have h_le : 2 * (Finset.Icc 1 k).lcm id ≤ y := Nat.le_of_dvd hypos h_dvd
      omega
    by_cases h_even : 2 ∣ y
    · -- y is even
      by_cases h_y_le_k : y ≤ k
      · -- Case 1: y ≤ k. Use [y]
        let parts : Multiset ℕ := {y}
        have h_parts_pos : ∀ {i : ℕ}, i ∈ parts → 0 < i := by
          intro i hi
          have : i = y := by simpa [parts] using hi
          subst this; omega
        have h_parts_sum : parts.sum = y := by simp [parts]
        let p : y.Partition := @Nat.Partition.mk y parts h_parts_pos h_parts_sum
        have h_bounded : Bounded k p := by
          intro i hi
          dsimp [p, parts] at hi
          have : i = y := by simpa using hi
          subst this; exact h_y_le_k
        have h_not_balanceable : ¬ Balanceable p := by
          have hmax_eq : Multiset.foldr max 0 p.parts = y := by
            dsimp [p, parts]; simp
          dsimp [Balanceable]
          rw [hmax_eq]
          have h_lcm_ge_y : y ≤ (Finset.Icc 1 y).lcm id := lcm_Icc_ge y hypos
          have h_gt : y < 2 * (Finset.Icc 1 y).lcm id :=
            lt_of_lt_of_le (by omega : y < 2 * y) (Nat.mul_le_mul_left 2 h_lcm_ge_y)
          intro hdiv
          have h_le : 2 * (Finset.Icc 1 y).lcm id ≤ y := Nat.le_of_dvd hypos hdiv
          omega
        exact h_not_balanceable (hyprop p h_bounded)
      · -- Case 2: y > k
        have hq_pos : y / k > 0 := Nat.div_pos (by omega) hk
        have h_r_lt_k : y % k < k := Nat.mod_lt y (by omega)
        let q := y / k
        let r := y % k
        have hqpos' : q > 0 := hq_pos
        have h_r_lt_k' : r < k := h_r_lt_k
        let parts_raw : Multiset ℕ := (Multiset.replicate q k) + (if r > 0 then {r} else (0 : Multiset ℕ))
        have h_parts_raw_sum : parts_raw.sum = y := by
          dsimp [parts_raw, q, r]
          by_cases hr : y % k > 0
          · simp [hr, mul_comm, Nat.div_add_mod y k]
          · have hr0 : y % k = 0 := by omega
            have h_dvd : k ∣ y := Nat.dvd_of_mod_eq_zero hr0
            simp [hr0, Multiset.sum_replicate, mul_comm, Nat.mul_div_cancel' h_dvd]
        have h_parts_raw_pos : ∀ {i : ℕ}, i ∈ parts_raw → 0 < i := by
          intro i hi
          dsimp [parts_raw] at hi
          rcases Multiset.mem_add.mp hi with (hi' | hi')
          · have : i = k := Multiset.eq_of_mem_replicate hi'; subst this; omega
          · by_cases hr : r > 0
            · have hi_r : i = r := by
                simpa [hr] using hi'
              subst i; omega
            · simp [hr] at hi'
        let p : y.Partition := @Nat.Partition.mk y parts_raw h_parts_raw_pos h_parts_raw_sum
        have h_bounded : Bounded k p := by
          intro i hi
          dsimp [p, parts_raw] at hi
          rcases Multiset.mem_add.mp hi with (hi' | hi')
          · have : i = k := Multiset.eq_of_mem_replicate hi'; subst this; rfl
          · by_cases hr : r > 0
            · have hi_r : i = r := by simpa [hr] using hi'
              subst i; omega
            · simp [hr] at hi'
        have h_maxPart_eq : Multiset.foldr max 0 p.parts = k := by
          dsimp [p, parts_raw]
          by_cases hr' : r > 0
          · calc
              Multiset.foldr max 0 ((Multiset.replicate q k) + (if r > 0 then {r} else (0 : Multiset ℕ)))
                  = Multiset.foldr max 0 ((Multiset.replicate q k) + {r}) :=
                    congrArg (fun s : Multiset ℕ => Multiset.foldr max 0 ((Multiset.replicate q k) + s)) (if_pos hr')
              _ = max k r := foldr_max_replicate_add_singleton q k r hqpos'
              _ = k := by
                apply max_eq_left; omega
          · calc
              Multiset.foldr max 0 ((Multiset.replicate q k) + (if r > 0 then {r} else (0 : Multiset ℕ)))
                  = Multiset.foldr max 0 ((Multiset.replicate q k) + (0 : Multiset ℕ)) :=
                    congrArg (fun s : Multiset ℕ => Multiset.foldr max 0 ((Multiset.replicate q k) + s)) (if_neg hr')
              _ = Multiset.foldr max 0 (Multiset.replicate q k) := by simp
              _ = k := foldr_max_replicate_zero q k hqpos'
        have h_not_balanceable : ¬ Balanceable p := by
          intro hbal
          have h_lcm_eq : (Finset.Icc 1 (Multiset.foldr max 0 p.parts)).lcm id = (Finset.Icc 1 k).lcm id :=
            foldr_max_parts_to_k p.parts k h_maxPart_eq
          have h_div : 2*(Finset.Icc 1 k).lcm id ∣ y := by
            have h_bal' : 2*(Finset.Icc 1 (Multiset.foldr max 0 p.parts)).lcm id ∣ y := hbal
            rw [h_lcm_eq] at h_bal'
            exact h_bal'
          apply h_ndvd_raw
          exact h_div
        exact h_not_balanceable (hyprop p h_bounded)
    · -- y is odd
      let parts : Multiset ℕ := Multiset.replicate y 1
      have h_parts_pos : ∀ {i : ℕ}, i ∈ parts → 0 < i := by
        intro i hi; have hi_eq : i = 1 := Multiset.eq_of_mem_replicate hi
        subst hi_eq; omega
      have h_parts_sum : parts.sum = y := by simp [parts]
      let p : y.Partition := @Nat.Partition.mk y parts h_parts_pos h_parts_sum
      have h_bounded : Bounded k p := by
        intro i hi; dsimp [p, parts] at hi; have hi_eq : i = 1 := Multiset.eq_of_mem_replicate hi
        subst hi_eq; omega
      have h_not_balanceable : ¬ Balanceable p := by
        have h_lcm_eq : (Finset.Icc 1 (Multiset.foldr max 0 p.parts)).lcm id = 1 := by
          dsimp [p, parts]
          exact lcm_Icc_foldr_replicate_one y hypos
        intro hbal
        apply h_even
        have h_bal' : 2 * (Finset.Icc 1 (Multiset.foldr max 0 p.parts)).lcm id ∣ y := hbal
        rw [h_lcm_eq] at h_bal'
        have h_two_dvd_y : 2 ∣ y := by
          simpa [mul_comm] using h_bal'
        exact h_two_dvd_y
      exact h_not_balanceable (hyprop p h_bounded)
