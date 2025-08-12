import Mathlib
import Rudin.Chapter1.FinsetIdentity
import Rudin.Chapter1.OrderedField
import Rudin.Chapter1.Finset


namespace Rudin

open Finset

variable {α: Type u} [OrderedField α]


theorem powNat_sub_powNat_lt_sub_mul_exp_mul_max_powNat_exp_sub_one {a b:α} {n:Nat} (hn: n > 1) (ha: 0 < a) (hab: a < b):
  b ^ n - a ^ n < (b - a) * n • b ^ (n - 1) := by
  rw [powNat_sub_powNat_eq]
  have h1: ∑ x ∈ range n, b ^ (n - 1 - x) * a ^ x < ∑ x ∈ range n, b ^ (n - 1) := by
    refine Finset.sum_lt_sum ?_ ?_
    intro i hi
    have h1: a ^ i ≤ b ^ i := by
      exact gtz_lt_gtz_then_powNat_le ha hab
    have h2: b ^ (n - 1 - i) * a ^ i ≤ b ^ (n - 1 - i) * b ^ i := by
      refine mul_le_mul_of_nonneg_left h1 ?_
      have hb: b > 0 := by linarith
      refine pow_nonneg ?_ (n - 1 - i)
      linarith
    have h3 : b ^ (n - 1 - i) * b ^ i = b ^ (n - 1) := by
      refine pow_sub_mul_pow b ?_
      simp [range] at hi
      exact Nat.le_sub_one_of_lt hi
    linarith
    use n - 1
    constructor
    simp
    linarith
    simp
    refine (pow_lt_pow_iff_left₀ ?_ ?_ ?_).mpr hab
    linarith
    linarith
    exact Nat.sub_ne_zero_iff_lt.mpr hn
  rw [Rudin.gtz_mul_lt_left_cancel]
  have h2: ∑ x ∈ range n, b ^ (n - 1) = n • b ^ (n - 1) := by
    exact Eq.symm (Finset.nsmul_eq_sum_const (b ^ (n - 1)) n)
  linarith
  linarith


theorem sum_sqr_eq_zero_iff_eq_zero {n:Nat} {a:Nat → α} :
    ∑ i ∈ range n, (a i) ^ 2 = 0 ↔
    ∀ i ∈ range n, (a i) = 0 := by
  classical
  have hnonneg : ∀ i ∈ range n, 0 ≤ (a i) ^ 2 := by
    intro i hi; exact sq_nonneg _
  constructor
  · intro hsum i hi
    have hAll := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
    have hi' := hAll i hi
    exact (sq_eq_zero_iff).1 hi'
  · intro hall
    have hAllSquares : ∀ i ∈ range n, (a i) ^ 2 = 0 := by
      intro i hi
      have : a i = 0 := hall i hi
      simp [this]
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mpr hAllSquares



end Rudin
