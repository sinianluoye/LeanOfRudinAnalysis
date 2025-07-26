import Rudin.Command
import Rudin.Basic.Rational
import Rudin.Chapter1.Field
import Rudin.Chapter1.Ordered
import Rudin.Chapter1.OrderedField

namespace Rudin

namespace Rat
variable {a b:ℚ}


-- 证明 ℚ 满足 Ordered
instance : Rudin.Ordered ℚ where
  lt_trans      := by                              -- 传递性
    intro a b c h₁ h₂
    exact lt_trans h₁ h₂
  lt_trichotomy_complete := by
    intro a b
    exact lt_trichotomy_complete (a := a) (b := b)
  le_iff_lt_or_eq := le_iff_lt_or_eq

instance : Rudin.Field ℚ where
  add_comm      := by apply Rat.add_comm
  add_assoc     := by apply Rat.add_assoc
  zero_add      := by apply Rat.zero_add
  add_neg       := by apply Rat.add_neg
  mul_comm      := by apply Rat.mul_comm
  mul_assoc     := by apply Rat.mul_assoc
  one_nz := by apply Rat.one_nz
  one_mul       := by apply Rat.one_mul
  mul_inv_when_nz := by
    intro a ha
    simp [Rat.instInv_mathlib]
    rw [← Rat.div_def]
    rw [Rat.div_eq_mul_inv]
    rw [Rat.mul_inv_when_nz]
    exact rfl
    exact ha

  mul_add       := by apply Rat.mul_add
  sub_eq_add_neg := Rat.sub_eq_add_neg
  div_eq_mul_inv := by
    intro a b
    simp [Rat.instInv_mathlib, Rat.div_def]

  inv_eq_one_div := by
    intro a
    simp only [Rat.instInv_mathlib]
    rw [Rat.div_def]
    simp [One.one]

  pow := (fun a n => a ^ n)
  pow_nat_def    := by apply Rat.pow_nat_def
  natMul_def     := by
    intro a n
    by_cases hn : n = 0
    <;>simp [hn]
    have : (↑(n-1):Rat) = n - 1 := by
      refine Nat.cast_pred ?_
      exact Nat.zero_lt_of_ne_zero hn
    rw [this]
    linarith


/-1.17 ℚ IS OrderedField-/

instance : Rudin.OrderedField ℚ where
  add_lt_left_cancel := by
    intro a b c h
    rw [← Rat.add_lt_left_cancel (a:=a)]
    exact h

  gtz_mul_gtz_then_gtz := by apply Rat.gtz_mul_gtz_then_gtz

theorem smul_eq_mul {n:Nat} {a:Rat} : n • a = n * a := by
  induction n with
  | zero => simp
  | succ n hn => simp


theorem gtz_pow_ge_one_add_exp_mul_base_sub_one {a : Rat} {n:ℕ} (ha: a > 0) :
  a ^ n ≥ 1 + n * (a - 1) := by
  have h := Rudin.gtz_pow_ge_one_add_exp_mul_base_sub_one (n:=n) ha
  rw [smul_eq_mul] at h
  exact h


end Rat




end Rudin
