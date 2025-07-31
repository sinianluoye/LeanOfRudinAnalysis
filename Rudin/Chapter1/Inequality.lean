import Mathlib
import Rudin.Chapter1.FinsetIdentity
import Rudin.Chapter1.OrderedField

namespace Rudin

variable {α: Type u} [OrderedField α]


theorem powNat_sub_powNat_lt_sub_mul_exp_mul_max_powNat_exp_sub_one {a b:α} {n:Nat} (hn: n > 1) (ha: 0 < a) (hab: a < b):
  b ^ n - a ^ n < (b - a) * n • b ^ (n - 1) := by
  rw [powNat_sub_powNat_eq]
  have h1: ∑ x ∈ Finset.range n, b ^ (n - 1 - x) * a ^ x < ∑ x ∈ Finset.range n, b ^ (n - 1) := by
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
      simp [Finset.range] at hi
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
  have h2: ∑ x ∈ Finset.range n, b ^ (n - 1) = n • b ^ (n - 1) := by
    exact Eq.symm (Finset.nsmul_eq_sum_const (b ^ (n - 1)) n)
  linarith
  linarith



end Rudin
