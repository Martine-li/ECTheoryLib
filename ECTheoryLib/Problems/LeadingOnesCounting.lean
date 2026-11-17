import ECTheoryLib.Problems.LeadingOnes
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Prefix recursion and counting for LeadingOnes

The all-one prefix length follows the first bit: zero terminates it and one
extends the suffix prefix by one. Mathlib's Fin.consEquiv partitions all strings
by that bit. This gives 2^(n-k) strings with prefix at least k and a total
LeadingOnes score of 2^n-1. These are problem-level counting properties;
no algorithm or probability law is imported.
-/

namespace ECTheoryLib.Problems.LeadingOnes

theorem LeadingOnesConsFalse {n : ℕ} (x : Bits n) : LeadingOnes (Fin.cons false x) = 0 := by
  by_contra Nonzero
  have Positive : 0 < LeadingOnes (Fin.cons false x) := Nat.pos_of_ne_zero Nonzero
  have First := HasLeadingOnesPrefix (Fin.cons false x) 0 Positive
  change false = true at First
  cases First

theorem LeadingOnesConsTrue {n : ℕ} (x : Bits n) :
    LeadingOnes (Fin.cons true x) = 1 + LeadingOnes x := by
  have Lower : LeadingOnes x + 1 ≤ LeadingOnes (Fin.cons true x) := by
    apply PrefixLeLeadingOnes _ (Nat.succ_le_succ (LeadingOnesLeN x))
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro _InPrefix
      rfl
    · intro InPrefix
      rw [Fin.cons_succ]
      apply HasLeadingOnesPrefix x
      change j.val + 1 < LeadingOnes x + 1 at InPrefix
      omega
  have Upper := LeadingOnesLeN (Fin.cons true x)
  have TailPrefix : HasOnePrefix x (LeadingOnes (Fin.cons true x) - 1) := by
    intro i InPrefix
    have Original := HasLeadingOnesPrefix (Fin.cons true x) i.succ (by
      change i.val + 1 < LeadingOnes (Fin.cons true x)
      omega)
    exact Original
  have TailBound := PrefixLeLeadingOnes x (show LeadingOnes (Fin.cons true x) - 1 ≤ n by omega) TailPrefix
  omega

/-- Exactly 2^(n-k) strings have an all-one prefix of length k. -/
theorem PrefixCount (n k : ℕ) (Within : k ≤ n) :
    (∑ x : Bits n, if k ≤ LeadingOnes x then (1 : ℕ) else 0) = 2^(n-k) := by
  induction k generalizing n with
  | zero =>
    simp only [Nat.zero_le, if_true, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      mul_one, Nat.sub_zero, Bits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  | succ k Before =>
    cases n with
    | zero => omega
    | succ n =>
      have Split : (∑ x : Bits (n+1), if k+1 ≤ LeadingOnes x then (1 : ℕ) else 0) =
          ∑ p : Bool × Bits n, if k+1 ≤ LeadingOnes (Fin.cons p.1 p.2) then (1 : ℕ) else 0 := by
        exact (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool)) _ _ (fun _ => rfl)).symm
      rw [Split, Fintype.sum_prod_type, Fintype.sum_bool]
      have TrueComparison (x : Bits n) : k+1 ≤ LeadingOnes (Fin.cons true x) ↔ k ≤ LeadingOnes x := by
        rw [LeadingOnesConsTrue]
        omega
      have FalseComparison : ¬ k+1 ≤ 0 := by omega
      simp only [TrueComparison, LeadingOnesConsFalse, if_neg FalseComparison,
        Finset.sum_const_zero, add_zero]
      rw [Before n (by omega)]
      congr 1
      omega

/-- Sum over every bit string, obtained by splitting its first coordinate. -/
theorem LeadingOnesTotal (n : ℕ) :
    (∑ x : Bits n, (LeadingOnes x : ℝ)) = (2 : ℝ)^n - 1 := by
  induction n with
  | zero =>
    have Empty (x : Bits 0) : LeadingOnes x = 0 := Nat.eq_zero_of_le_zero (LeadingOnesLeN x)
    simp only [Empty, Nat.cast_zero, Finset.sum_const_zero, pow_zero, sub_self]
  | succ n Before =>
    have Split : (∑ x : Bits (n+1), (LeadingOnes x : ℝ)) =
        ∑ p : Bool × Bits n, (LeadingOnes (Fin.cons p.1 p.2) : ℝ) := by
      exact (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool)) _ _ (fun _ => rfl)).symm
    rw [Split, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [LeadingOnesConsTrue, LeadingOnesConsFalse, Nat.cast_add, Nat.cast_one,
      Nat.cast_zero, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have Card : Fintype.card (Bits n) = 2^n := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [Card, Nat.cast_pow, Nat.cast_ofNat, Before, pow_succ]
    ring

end ECTheoryLib.Problems.LeadingOnes
