import Rudin.Basic.Rational
import Rudin.Chapter1.Field
import Rudin.Chapter1.Ordered
import Rudin.Chapter1.OrderedField


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
  mul_inv_when_nz := by apply Rat.mul_inv_when_nz
  mul_add       := by apply Rat.mul_add
  sub_eq_add_neg := Rat.sub_eq_add_neg
  div_eq_mul_inv := by apply Rat.div_eq_mul_inv
  pow := (fun a n => a ^ n)
  pow_nat_def    := by apply Rat.pow_nat_def
  hMul := (fun n a => n * a)
  nat_mul_def       := by apply Rat.nat_mul_def

/-1.17 ℚ IS OrderedField-/

instance : Rudin.OrderedField ℚ where
  add_lt_left_cancel := by
    intro a b c h
    rw [← Rat.add_lt_left_cancel (a:=a)]
    exact h

  gtz_mul_gtz_then_gtz := by apply Rat.gtz_mul_gtz_then_gtz

def Avg2 (a:Rat) (b:Rat) := (a + b) / 2

def lt_then_lt_avg2 (hab: a < b) : a < Avg2 a b := by
  simp [Avg2]
  rw [← add_lt_left_cancel (a:=a)] at hab
  rw [div_eq_mul_inv]
  sorry


end Rat
