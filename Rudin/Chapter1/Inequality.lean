import Mathlib
import Rudin.Chapter1.FinsetIdentity
import Rudin.Chapter1.OrderedField

namespace Rudin

variable {α: Type u} [OrderedField α]


theorem powNat_sub_powNat_lt_sub_mul_exp_mul_max_powNat_exp_sub_one {a b:α} {n:Nat} (hn: n ≠ 0) (ha: 0 < a) (hab: a < b):
  b ^ n - a ^ n < (b - a) * n * b ^ (n - 1) := by
  rw [powNat_sub_powNat_eq]
  have : ∑ x ∈ Finset.range n, b ^ (n - 1 - x) * a ^ x < ∑ x ∈ Finset.range n, b ^ (n - 1) := by
    refine Finset.sum_lt_sum ?_ ?_
    intro i hi
    apply?


end Rudin
