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

end Rat

end Rudin

-- refer to one_add_mul_sub_le_pow, just proof for a > 0
theorem Rat.gtz_pow_ge_one_add_exp_mul_base_sub_one {a : ℚ} {n:ℕ} (ha: a > 0) :
  a ^ n ≥ 1 + n * (a - 1) := by
  induction n with
  | zero =>
    rw [pow_zero]
    ring_nf
    linarith
  | succ n h =>
    push_cast
    rw [pow_succ, add_mul, ← add_assoc]
    have h1: a ≥ a - 1 := by simp
    rw [ge_iff_le] at *
    rw [← Rudin.gtz_mul_le_right_cancel (a:=a)] at h
    have h2: a = 1 + (a - 1) := by simp
    rw (occs := .pos [2])[h2] at h
    rw [mul_add, mul_one] at h
    have : 1 + ↑n * (a - 1) + (1 + ↑n * (a - 1)) * (a - 1) ≥ 1 + ↑n * (a - 1) + 1 * (a - 1) := by
      simp
      rw [← Rudin.add_le_left_cancel (a:=-a), Rudin.neg_add, add_comm, Rudin.add_neg_eq_sub]
      rw [add_sub_assoc, ← neg_neg (a:=(1-a)), neg_sub, Rudin.add_neg_eq_sub]
      rw (occs := .pos [3])[← one_mul (a:=(a-1))]
      rw [← Rudin.sub_mul]
      rw [Rudin.add_sub_cancel]
      rw [mul_assoc, ← pow_two]
      apply Rudin.Rat.gez_mul_gez_then_gez
      linarith
      by_cases h3: a ≠ 1
      rw [Rudin.ge_iff_gt_or_eq]
      left
      apply Rudin.pow_two_gtz (a:=a-1)
      intro h4
      apply h3
      linarith
      simp at h3
      rw [h3]
      ring_nf
      linarith
    linarith
    exact ha
