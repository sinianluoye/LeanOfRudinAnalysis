import Mathlib
import Rudin.Chapter1.Field

namespace Rudin

variable {α: Type u} [Field α]

theorem func_eq_then_range_sum_eq_range_sum {f g:ℕ -> α} {n:Nat} (h: ∀ i < n, f i = g i):
  ∑ x ∈ Finset.range n, f x = ∑ x ∈ Finset.range n, g x := by
  induction' n with n hi
  simp
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_succ]
  rw [hi]
  simp
  simp [h]
  intro i hi
  have : i < n + 1 := by linarith
  have h1 := h i this
  exact h1


theorem powNat_sub_powNat_eq {a b:α} {n:Nat} : a^n - b^n = (a - b) * (∑ x ∈ Finset.range n, a ^ (n-1-x) * b ^ x) := by
  by_cases hb : b = 0
  simp [hb]
  by_cases hn : n = 0
  simp [hn]
  simp [hn]
  have hn1: n > 0 := by exact Nat.zero_lt_of_ne_zero hn
  simp [hn1]
  have : n = n - 1 + 1 := by exact (Nat.sub_eq_iff_eq_add hn1).mp rfl
  rw [this]
  simp
  rw [Rudin.mul_comm]

  induction' n with n hi
  simp
  simp
  by_cases hn: n = 0
  simp [hn]
  have : n = n - 1 + 1 := by exact Eq.symm (Nat.succ_pred_eq_of_ne_zero hn)
  rw [Finset.sum_range_succ]
  rw (occs := .pos [4]) [this]
  have : ∑ x ∈ Finset.range n, a ^ (n - 1 + 1 - x) * b ^ x = ∑ x ∈ Finset.range n, a ^ (n - 1 - x + 1) * b ^ x := by
    apply func_eq_then_range_sum_eq_range_sum
    intro i ih
    by_cases hi : i = 0
    simp [hi]
    repeat rw [Rudin.mul_comm (b:=b^i)]
    rw [Rudin.mul_eq_left_cancel]
    apply exp_eq_then_powNat_eq
    refine Nat.sub_add_comm ?_
    linarith
    rw [powNat_nz_iff_base_nz]
    exact hb
    exact hi
  simp [this]
  have hFactor :
    (∑ x ∈ Finset.range n, a ^ (n - 1 - x) * a * b ^ x)
      = a * ∑ x ∈ Finset.range n, a ^ (n - 1 - x) * b ^ x := by
    rw [Finset.mul_sum]
    refine func_eq_then_range_sum_eq_range_sum ?_
    intro x hx
    ring
  rw [hFactor]
  rw [mul_add]
  rw [← mul_assoc, mul_comm (a:=a-b), mul_assoc]
  rw [← hi]
  ring







end Rudin
