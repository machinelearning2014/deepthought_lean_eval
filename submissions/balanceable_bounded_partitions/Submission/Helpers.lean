import Mathlib

namespace Submission.Helpers

  open LeanEval.Combinatorics

  open Finset

  open Multiset

  open Nat

  -- ============================================================
  -- Helper lemma: Fintype.card (Finset (Fin n)) = 2^n
  -- ============================================================
  lemma card_finset_fin (n : ℕ) : Fintype.card (Finset (Fin n)) = 2 ^ n := by
    calc
      Fintype.card (Finset (Fin n)) = Finset.card (Finset.univ : Finset (Finset (Fin n))) := rfl
      _ = Finset.card ((Finset.univ : Finset (Fin n)).powerset) := by simp
      _ = 2 ^ ((Finset.univ : Finset (Fin n)).card) := Finset.card_powerset _
      _ = 2 ^ n := by simp

  -- ============================================================
  -- Helper lemma: 2^n ≥ n^2 for n ≥ 4
  -- ============================================================

  lemma two_pow_ge_sq (n : ℕ) (hn : 4 ≤ n) : 2 ^ n ≥ n ^ 2 := by
    induction' n from 4 to n using Nat.le_induction with m hm IH
    · native_decide
    · have hm_sq : (m : ℕ) ^ 2 ≥ 2 * m + 1 := by
        have hm3 : 3 ≤ m := by omega
        nlinarith
      calc
        2 ^ (m+1) = 2 * (2 ^ m) := by ring
        _ ≥ 2 * (m ^ 2) := by nlinarith
        _ = m ^ 2 + m ^ 2 := by ring
        _ ≥ m ^ 2 + (2 * m + 1) := by nlinarith
        _ = (m+1) ^ 2 := by ring

  -- ============================================================
  -- Helper lemma: gcd(k, k-1) = 1 for k ≥ 2
  -- ============================================================

  lemma coprime_k_k_sub_one (k : ℕ) (hk : 2 ≤ k) : Nat.gcd k (k-1) = 1 := by
    calc
      Nat.gcd k (k-1) = Nat.gcd (k-1) k := Nat.gcd_comm _ _
      _ = Nat.gcd (k-1) ((k-1) + 1) := by omega
      _ = Nat.gcd (k-1) 1 := by
        simpa using Nat.gcd_add_self_right (k-1) 1
      _ = 1 := by simp

  -- ============================================================
  -- Helper lemma: L = lcm(1,...,k) ≥ k*(k-1)
  -- ============================================================

  lemma L_ge_k_mul_k_sub_one (k : ℕ) (hk : 0 < k) : (Finset.Icc 1 k).lcm id ≥ k * (k-1) := by
    by_cases hk1 : k = 1
    · subst hk1; simp
    · have hk2 : 2 ≤ k := by omega
      have hkmem1 : k ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hk, le_refl _⟩
      have hkmem2 : (k-1) ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hdvd1 : k ∣ (Finset.Icc 1 k).lcm id := Finset.dvd_lcm (f := id) hkmem1
      have hdvd2 : (k-1) ∣ (Finset.Icc 1 k).lcm id := Finset.dvd_lcm (f := id) hkmem2
      have hcp : Nat.Coprime k (k-1) := coprime_k_k_sub_one k hk2
      have hprod : k*(k-1) ∣ (Finset.Icc 1 k).lcm id :=
        hcp.mul_dvd_of_dvd_of_dvd hdvd1 hdvd2
      have hpos : 0 < (Finset.Icc 1 k).lcm id := by
        have h1mem : 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have h1dvd : 1 ∣ (Finset.Icc 1 k).lcm id := Finset.dvd_lcm (f := id) h1mem
        exact Nat.pos_of_dvd_of_pos h1dvd (by norm_num)
      exact Nat.le_of_dvd hpos hprod

  -- ============================================================
  -- Helper lemma: If m < lcm(1,...,k), then ∃ i ∈ {1,...,k} with i ∤ m
  -- ============================================================

  lemma exists_i_not_dvd_of_lt_lcm (k : ℕ) (m : ℕ) (hm : m < (Finset.Icc 1 k).lcm id) :
      ∃ i, i ∈ Finset.Icc 1 k ∧ ¬ (i ∣ m) := by
    by_contra! hall
    have hL_dvd_m : (Finset.Icc 1 k).lcm id ∣ m := by
      apply Finset.dvd_lcm_of_dvd (f := id)
      intro i hi
      exact hall i hi
    have hLpos : 0 < (Finset.Icc 1 k).lcm id := by
      have h1mem : 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have h1dvd : 1 ∣ (Finset.Icc 1 k).lcm id := Finset.dvd_lcm (f := id) h1mem
      exact Nat.pos_of_dvd_of_pos h1dvd (by norm_num)
    have hm_ge_L : (Finset.Icc 1 k).lcm id ≤ m :=
      Nat.le_of_dvd (by omega) hL_dvd_m
    omega

  -- ============================================================
  -- Main theorem
  -- ============================================================

end Submission.Helpers
