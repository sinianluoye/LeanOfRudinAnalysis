
import Batteries.Tactic.Init

namespace Rudin

universe u

class Field (α : Type u) extends
  Add α, Mul α, Sub α, Neg α, Div α, Zero α, One α, Pow α Nat, HMul Nat α α where
  -- add axioms
  add_comm  : ∀ a b : α, a + b = b + a
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  zero_add  : ∀ a : α, 0 + a = a
  add_neg   : ∀ a : α, a + -a = 0
  -- mul axioms
  mul_comm  : ∀ a b : α, a * b = b * a
  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)
  one_nz : (1 : α) ≠ (0 : α)
  one_mul   : ∀ a : α, 1 * a = a
  mul_inv_when_nz   : ∀ a : α, a ≠ 0 → a * (1 / a) = 1
  -- distributive law
  mul_add   : ∀ a b c : α, a * (b + c) = a * b + a * c

  -- remarks
  sub_eq_add_neg : ∀ a b : α, a - b = a + -b
  div_eq_mul_inv : ∀ a b : α, a / b = a * (1 / b)
  pow_nat_def : ∀ a : α, ∀ n : Nat, a ^ n = if n = 0 then 1 else a ^ (n - 1) * a
  nat_mul_def : ∀ a : α, ∀ n : Nat, n * a = if n = 0 then 0 else (n - 1) * a + a

variable {α: Type u} [Field α]

-- add axioms
theorem add_comm {a b : α} : a + b = b + a := by
  apply Field.add_comm

theorem add_assoc {a b c : α} : (a + b) + c = a + (b + c) := by
  apply Field.add_assoc

@[simp] theorem zero_add {a : α} : 0 + a = a := by
  apply Field.zero_add

@[simp] theorem add_neg {a : α} : a + -a = 0 := by
  apply Field.add_neg

@[simp] theorem neg_add {a : α} : -a + a = 0 := by
  rw [add_comm]
  apply Field.add_neg

-- mul axioms
theorem mul_comm {a b : α} : a * b = b * a := by
  apply Field.mul_comm

theorem mul_assoc {a b c : α} : (a * b) * c = a * (b * c) := by
  apply Field.mul_assoc

@[simp] theorem one_nz : (1 : α) ≠ (0 : α) := by
  apply Field.one_nz

@[simp] theorem one_mul {a : α} : 1 * a = a := by
  apply Field.one_mul

@[simp] theorem mul_inv {a : α} (ha : a ≠ 0) : a * (1 / a) = 1 := by
  apply Field.mul_inv_when_nz
  exact ha

@[simp] theorem inv_mul {a : α} (ha : a ≠ 0) : (1 / a) * a = 1 := by
  rw [mul_comm]
  simp [ha]

-- distributive law
theorem mul_add {a b c : α} : a * (b + c) = a * b + a * c := by
  apply Field.mul_add

theorem add_mul {a b c : α} : (a + b) * c = a * c + b * c := by
  rw [mul_comm]
  rw [mul_add]
  rw [mul_comm (a:=c) (b:=a), mul_comm (a:=c) (b:=b)]


-- remarks
theorem sub_eq_add_neg {a b : α} : a - b = a + -b := by
  apply Field.sub_eq_add_neg

@[simp] theorem add_neg_eq_sub {a b: α} : a + -b = a - b := sub_eq_add_neg.symm

theorem div_eq_mul_inv {a b : α} : a / b = a * (1 / b) := by
  apply Field.div_eq_mul_inv

theorem pow_nat_def {a : α} {n : Nat} : a ^ n = if n = 0 then 1 else a ^ (n - 1) * a := Field.pow_nat_def a n

theorem nat_mul_def {a : α} {n : Nat} : n * a = if n = 0 then 0 else (n - 1) * a + a := Field.nat_mul_def a n

/- other helpful theorems -/
@[simp] theorem sub_eq_zero {a : α} : a - a = 0 := by
  simp [sub_eq_add_neg, add_neg]

@[simp] theorem neg_add_eq_zero {a : α} : -a + a = 0 := by
  rw [add_comm]
  simp

@[simp] theorem add_neg_eq_zero {a : α} : a + -a = 0 := by
  rw [add_comm]
  simp

@[simp] theorem add_sub_cancel {a b : α} : a + b - a = b := by
  rw [sub_eq_add_neg, add_comm, ← add_assoc]
  simp

@[simp] theorem add_sub_cancel_right {a b:α} : a + b - b = a := by
  rw [add_comm]
  simp

theorem add_sub_assoc {a b c : α} : a + b - c = a + (b - c) := by
  rw [sub_eq_add_neg]
  rw [add_assoc]
  rw [sub_eq_add_neg]

@[simp] theorem add_sub_cancel' {a b : α} : a + (b - a) = b := by
  rw [← add_sub_assoc]
  simp


@[simp] theorem add_zero {a : α} : a + 0 = a := by
  rw [add_comm]
  simp

/-1.14-/
@[simp] theorem add_eq_left_cancel {a b c : α} :
    (a + b = a + c) ↔ (b = c) := by
  constructor
  · intro h
    have : (a + b) - a = (a + c) - a := by
      simpa using congrArg (fun x : α => x - a) h
    simpa [add_sub_cancel] using this
  · intro h
    rw [h]

@[simp] theorem add_eq_left_cancel₀ {a b : α} :
    (a + b = a) ↔ (b = 0) := by
  constructor
  · intro h
    have : a + b - a = 0 := by
      simpa using congrArg (fun x : α => x - a) h
    simpa [add_sub_cancel] using this
  · intro h
    rw [h]
    exact add_zero

@[simp] theorem add_eq_left_cancel_neg {a b : α} :
    (a + b = 0) ↔ (b = -a) := by
  constructor
  · intro h
    rw [← add_neg (a:=a)] at h
    rw [add_eq_left_cancel] at h
    exact h
  · intro h
    rw [h]
    simp

@[simp] theorem neg_neg {a : α} : -(-a) = a := by
  have h := add_neg (a := a)
  rw [add_comm] at h
  rw [add_eq_left_cancel_neg] at h
  exact h.symm

@[simp] theorem neg_zero_eq_zero : -(0:α) = 0 := by
  rw [← zero_add (a:=-0)]
  rw [add_neg]

@[simp] theorem zero_sub_eq_neg {a:α} : (0:α) - a = -a := by
  rw [sub_eq_add_neg, zero_add]

@[simp] theorem neg_ez_iff_ez {a:α} : -a = 0 ↔ a = 0 := by
  constructor
  <;>intro h
  <;>rw [← add_neg (a:=a)]
  <;>rw [h]
  rw [add_zero]
  rw [zero_add]

@[simp] theorem neg_nz_iff_nz {a:α} : -a ≠ 0 ↔ a ≠ 0 := by
  constructor
  intro h
  intro h1
  apply h
  rw [h1]
  have : (0:α) + -0 = 0 := by simp
  rw [← zero_add (a:=-0)]
  exact this
  intro h
  intro h1
  apply h
  simp at h1
  exact h1




/-1.15-/

theorem mul_div_assoc {a b c : α} :
  a * (b / c) = a * b / c := by
  rw [div_eq_mul_inv]
  rw [← mul_assoc]
  rw [← div_eq_mul_inv]

@[simp] theorem div_self {a:α} (ha: a ≠ 0) : a / a = 1 := by
  rw [div_eq_mul_inv]
  rw [mul_inv]
  exact ha

@[simp] theorem mul_div_cancel_left' {a b : α} (ha : a ≠ 0) :
    a * (b / a) = b := by
  rw [div_eq_mul_inv,
    ← mul_assoc,
    mul_comm (a:=a) (b:=b),
    mul_assoc,
    mul_inv ha,
    mul_comm,
    one_mul]

@[simp] theorem mul_div_cancel_left {a b : α} (ha : a ≠ 0) : a * b / a = b := by
  rw [← mul_div_assoc]
  rw [mul_div_cancel_left' ha]

@[simp] theorem mul_div_cancel {a b:α} (hb : b ≠ 0) : a * b / b = a := by
  rw [← mul_div_assoc]
  simp [hb]
  rw [mul_comm, one_mul]

@[simp] theorem div_mul_cancel {a b:α} (hb : b ≠ 0) : a / b * b = a := by
  rw [mul_comm]
  simp [hb]

/-1.15 a-/
theorem mul_eq_left_cancel {a b c : α} (ha : a ≠ 0) :
    (a * b = a * c) ↔ (b = c) := by
  constructor
  <;>intro h
  rw [← mul_div_cancel_left (a:=a) (b:=b) ha]
  rw [h]
  rw [mul_div_cancel_left ha]
  rw [h]

@[simp] theorem mul_one {a : α} : a * 1 = a := by
  rw [mul_comm]
  simp

/-1.15 b-/
@[simp] theorem mul_eq_left_cancel₁ {a b : α} (ha : a ≠ 0) :
    (a * b = a) ↔ (b = 1) := by
  constructor
  <;> intro h
  rw (occs := .pos [2]) [← one_mul (a:=a)] at h
  rw [mul_comm (a:=1)] at h
  rw [mul_eq_left_cancel ha] at h
  exact h
  simp [h]

/-1.15 c-/
@[simp] theorem mul_eq_left_cancel_inv {a b : α} (ha : a ≠ 0) :
    (a * b = 1) ↔ (b = 1 / a) := by
  constructor
  <;> intro h
  rw [← mul_inv ha] at h
  rw [mul_eq_left_cancel ha] at h
  exact h
  simp [h, ha]

/-1.16 a-/
@[simp] theorem zero_mul {a : α} : 0 * a = 0 := by
  have : 0 * a + 0 * a = 0 * a := by
    calc
      0 * a + 0 * a = (0 + 0) * a := by rw [← add_mul]
      _ = 0 * a := by simp
  simp at this
  exact this

@[simp] theorem mul_zero {a : α} : a * 0 = 0 := by
  rw [mul_comm]
  simp [zero_mul]

theorem inv_nz {a : α} (ha:a ≠ 0): 1 / a ≠ 0 := by
  intro h
  have := mul_inv ha
  rw [h, mul_comm] at this
  rw []
  simp at this
  exact Field.one_nz this.symm



/-1.15 d-/
@[simp] theorem inv_inv {a : α} (ha : a ≠ 0) : (1 / (1 / a)) = a := by
  have h := mul_inv ha
  rw [mul_comm] at h
  rw [mul_eq_left_cancel_inv (a:=1/a) (b:=a)] at h
  exact h.symm
  exact inv_nz ha


/-1.16 b-/
theorem nz_and_nz_iff_mul_nz {a b:α} : a ≠ 0 ∧ b ≠ 0 ↔ a * b ≠ 0 := by
  constructor
  intro h
  intro ha
  have : (1:α) = (0:α) := by
    calc
      (1:α) = (1/b) * (1/a) * a * b := by
        rw [mul_assoc (b := 1/a) (c := a)]
        simp [h.left, h.right]
      _ = (1/b) * (1/a) * (a * b) := by rw [mul_assoc]
      _ = 0 := by simp [ha]
  simp at this
  intro h
  by_cases ha : a = 0
  have : a * b = 0 := by simp [ha]
  exfalso
  exact h this
  by_cases hb : b = 0
  have : a * b = 0 := by simp [hb]
  exfalso
  exact h this
  exact ⟨ha, hb⟩

/-1.16 c-/
theorem neg_mul {a b : α} :
    -a * b = -(a * b) := by
  have h1 : -a * b + a * b = 0 := by
    rw [← add_mul]
    rw [add_comm]
    simp
  have h2 : - (a * b) + a * b = 0 := by
    simp [add_neg]
  rw [← h1] at h2
  rw [add_comm (a := -(a*b))] at h2
  rw [add_comm (a := -a*b)] at h2
  rw [add_eq_left_cancel] at h2
  exact h2.symm

@[simp] theorem mul_neg {a b : α} :
    a * -b = -(a * b) := by
  rw [mul_comm]
  rw [mul_comm (a:=a)]
  exact neg_mul


/-1.16 d-/
@[simp] theorem neg_mul_neg {a b : α} :
    -a * -b = a * b := by
  calc
    -a * -b = -(a * -b) := by rw [neg_mul]
    _ = - - (a * b) := by rw [mul_neg]
    _ = a * b := by simp [neg_neg]

theorem mul_sub {a b c : α} : a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg]
  rw [mul_add]
  simp

theorem sub_mul {a b c : α} : (a - b) * c = a * c - b * c := by
  rw [mul_comm]
  rw [mul_sub]
  rw [mul_comm (a:=c)]
  rw [mul_comm (b:=c)]
  rw [mul_comm (a:=b)]


@[simp] theorem pow_zero {a : α} : a ^ 0 = 1 := by simp [pow_nat_def]

@[simp] theorem pow_one {a:α} : a ^ 1 = a := by simp [pow_nat_def]

theorem pow_two {a : α} : a ^ 2 = a * a := by simp [pow_nat_def]

theorem div_eq_div_iff_mul_eq_mul {a b c d:α} (hbnz: b ≠ 0) (hdnz: d ≠ 0) : a / b = c / d ↔ a * d = b * c := by
  constructor
  . intro h
    rw [← mul_div_cancel_left (a:=b) (b:=a*d) hbnz]
    rw [← mul_comm, mul_assoc]
    rw [mul_comm]
    rw [← mul_div_assoc]
    rw [h]
    rw [mul_comm (a:=d)]
    rw [mul_assoc]
    rw [mul_div_cancel_left' hdnz]
  . intro h
    rw [← mul_div_cancel_left (a:=d) (b:=a) hdnz, mul_comm]
    rw [h]
    rw [← mul_div_assoc, mul_div_cancel_left (a:=b) (b:=c/d) hbnz]

@[simp] theorem neg_one_mul {a:α} : -1 * a = -a := by
  rw [← one_mul (a:=-a)]
  rw [mul_neg]
  rw [mul_comm, mul_neg, mul_comm (a:=1)]

@[simp] theorem neg_inv {a:α} (ha: a ≠ 0) : 1 / -a = -(1/a) := by
  have : 1 / -a = -1 / a := by
    rw [div_eq_div_iff_mul_eq_mul]
    simp
    exact neg_nz_iff_nz.mpr ha
    exact ha
  rw [div_eq_mul_inv (a:=-1)] at this
  rw [this]
  simp


end Rudin
