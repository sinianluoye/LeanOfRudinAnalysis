import Mathlib
import Batteries.Tactic.Init


namespace Rudin

universe u

class Field (α : Type u)  extends
  Add α, SMul Nat α, Mul α, Sub α, Neg α, Div α, Zero α, One α, Pow α Nat, Inv α where
  -- add axioms
  add_comm  : ∀ a b : α, a + b = b + a
  add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
  zero_add  : ∀ a : α, zero + a = a
  add_neg   : ∀ a : α, a + -a = zero
  -- mul axioms
  mul_comm  : ∀ a b : α, a * b = b * a
  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)
  one_nz : one ≠ zero
  one_mul   : ∀ a : α, one * a = a
  mul_inv_when_nz   : ∀ a : α, a ≠ zero → a * a⁻¹ = one
  -- distributive law
  mul_add   : ∀ a b c : α, a * (b + c) = a * b + a * c
  -- remarks
  sub_eq_add_neg : ∀ a b : α, a - b = a + -b
  div_eq_mul_inv : ∀ a b : α, a / b = a * b⁻¹
  inv_eq_one_div : ∀ a : α, a⁻¹ = one / a
  powNat_def : ∀ a : α, ∀ n : Nat, a ^ n = if n = 0 then 1 else a ^ (n - 1) * a
  natMul_def : ∀ a : α, ∀ n : Nat, n • a = if n = 0 then 0 else (n - 1) • a + a

variable {α: Type u} [Field α]

open Classical
noncomputable instance : DecidableEq α := Classical.decEq _


-- instance : NatCast α where
--   natCast n :=  by
--     induction n with
--     | zero => exact Zero.zero
--     | succ n ih =>
--       exact (n + 1) • One.one

-- instance instRudinFieldOfNat {n:Nat} : OfNat α n where
--   ofNat := NatCast.natCast n

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

theorem one_eq_field_one : (1:α) = One.one := by
  simp [OfNat.ofNat]

theorem zero_eq_field_zero : (0:α) = Zero.zero := by
  simp [OfNat.ofNat]



@[simp] theorem one_nz : (1 : α) ≠ (0 : α) := by
  rw [one_eq_field_one, zero_eq_field_zero]
  apply Field.one_nz

@[simp] theorem one_mul {a : α} : 1 * a = a := by
  simp [one_eq_field_one]
  apply Field.one_mul

@[simp] theorem mul_inv {a : α} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  simp [one_eq_field_one]
  apply Field.mul_inv_when_nz
  exact ha


theorem inv_eq_one_div {a : α} : a⁻¹ = 1 / a := by
  simp [one_eq_field_one]
  apply Field.inv_eq_one_div

@[simp] theorem inv_mul {a : α} (ha : a ≠ 0) : a⁻¹ * a = 1 := by
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

theorem div_eq_mul_inv {a b : α} : a / b = a * b⁻¹ := by
  apply Field.div_eq_mul_inv

theorem powNat_def {a : α} {n : Nat} : a ^ n = if n = 0 then 1 else a ^ (n - 1) * a := by
  have h := Field.powNat_def a n
  simp [one_eq_field_one]
  exact h

theorem natMul_def {a : α} {n : Nat} : n • a = if n = 0 then 0 else (n - 1) • a + a := Field.natMul_def a n

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
@[simp]
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
    (a * b = 1) ↔ (b = a⁻¹) := by
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

theorem inv_nz {a : α} (ha:a ≠ 0): a⁻¹ ≠ 0 := by
  intro h
  have := mul_inv ha
  rw [h, mul_comm] at this
  simp at this
  exact one_nz this.symm



/-1.15 d-/
@[simp] theorem inv_inv {a : α} (ha : a ≠ 0) : (a⁻¹⁻¹) = a := by
  have h := mul_inv ha
  rw [mul_comm] at h
  rw [mul_eq_left_cancel_inv (a:=a⁻¹) (b:=a)] at h
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
    simp
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


@[simp] theorem pow_zero {a : α} : a ^ 0 = 1 := by simp [powNat_def]

@[simp] theorem pow_one {a:α} : a ^ 1 = a := by simp [powNat_def]

theorem pow_two {a : α} : a ^ 2 = a * a := by simp [powNat_def]

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

@[simp]
theorem div_one {a:α} : a / 1 = a := by
  rw [← one_mul (a:=a)]
  rw [mul_div_cancel_left]
  simp
  exact one_nz

theorem div_eq_iff_eq_mul {a b c:α} (hbnz: b ≠ 0) : a / b = c ↔ a = b * c := by
  have := div_eq_div_iff_mul_eq_mul (a:=a) (b:=b) (c:=c) (d:=1) hbnz one_nz
  simp at this
  exact this

@[simp] theorem neg_one_mul {a:α} : -1 * a = -a := by
  rw [← one_mul (a:=-a)]
  rw [mul_neg]
  rw [mul_comm, mul_neg, mul_comm (a:=1)]

@[simp] theorem neg_inv {a:α} (ha: a ≠ 0) : (-a)⁻¹ = -a⁻¹ := by
  rw [inv_eq_one_div]
  have : 1 / -a = -1 / a := by
    rw [div_eq_div_iff_mul_eq_mul]
    simp
    exact neg_nz_iff_nz.mpr ha
    exact ha
  rw [div_eq_mul_inv (a:=-1)] at this
  rw [this]
  simp

@[simp] theorem neg_div {a b:α} : (-a) / b = - (a / b) := by
  rw (occs := .pos [1]) [div_eq_mul_inv]
  rw [inv_eq_one_div]
  rw (occs := .pos [2]) [div_eq_mul_inv]
  rw [neg_mul]
  rw [← inv_eq_one_div]

theorem inv_mul_inv {a b:α} (ha: a ≠ 0) (hb: b ≠ 0): a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
  refine (mul_eq_left_cancel_inv ?_).mp ?_
  refine nz_and_nz_iff_mul_nz.mp ?_
  constructor
  exact ha
  exact hb
  rw [← mul_assoc]
  rw [mul_comm (a:=a)]
  rw [mul_assoc (c:= a⁻¹)]
  rw [mul_inv]
  simp
  rw [mul_inv]
  exact hb
  exact ha

theorem mul_eq_zero_iff_eq_zero_or_eq_zero {a b:α} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  intro h
  by_contra! hab
  rw [← Rudin.mul_eq_left_cancel (a:=a⁻¹)] at h
  rw [Rudin.mul_zero, ← Rudin.mul_assoc, inv_mul, one_mul] at h
  exact hab.right h
  exact hab.left
  apply Rudin.inv_nz
  exact hab.left
  intro h
  rcases h with h|h
  <;>simp [h]

@[simp]
theorem ofNat_one_eq_one : @OfNat.ofNat α 1 One.toOfNat1 = 1 := by
  simp [OfNat.ofNat, OfNat.ofNat]

@[simp]
theorem zero_smul {a:α} : 0 • a = 0 := by simp [natMul_def]

@[simp]
theorem one_smul {a:α} : 1 • a = a := by
  rw [natMul_def]
  have hn: ¬ 1 = 0 := by norm_num
  split_ifs with h
  exact h.elim
  simp

@[simp]
theorem add_one_smul {a:α} {n:Nat} : (n + 1) • a = n • a + a := by
  rw [natMul_def]
  exact rfl

@[simp]
theorem add_smul {a:α} {n m:Nat} : (m + n) • a = m • a + n • a := by
  induction m with
  | zero =>
    simp
  | succ m hm =>
    simp
    rw [Nat.add_comm, ← Nat.add_assoc]
    simp
    rw [Nat.add_comm, hm]
    rw [Rudin.add_assoc, Rudin.add_comm (a:=n • a), ← Rudin.add_assoc]


@[simp]
theorem powNat_add_one {a:α} {n:Nat}: a ^ (n+1) = a ^ n * a := by
  rw [powNat_def]
  rfl

theorem smul_mul_assoc {a b:α} {n:Nat} : n • a * b = n • (a * b) := by
  induction n with
  | zero => simp
  | succ n hi =>
    simp
    rw [add_mul]
    rw [hi]

@[simp]
theorem smul_zero {n:Nat} : n • 0 = 0 := by
  simp

theorem exp_eq_then_powNat_eq {m n:Nat} {a:α} (h: m = n): a ^ m = a ^ n := by simp [h]




@[simp]
theorem sub_zero {a:α} : a - 0 = a := by
  rw [← Rudin.add_neg (a:=a)]
  rw [Rudin.sub_eq_add_neg]
  simp

@[simp]
theorem zero_powNat {n:Nat} : (0:α) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with hn
  rw [hn]
  simp
  rw [powNat_def]
  simp [hn]

theorem powNat_nz_iff_base_nz {a:α} {n:Nat} (hn: n ≠ 0): a ^ n ≠ 0 ↔ a ≠ 0 := by
  constructor
  <;>intro h
  <;>contrapose! h
  rw [h]
  simp
  exact hn
  induction' n with n hi
  simp at h
  by_cases hn1: n = 0
  rw [hn1] at h
  simp at h
  exact h
  rw [powNat_add_one] at h
  rw [Rudin.mul_eq_zero_iff_eq_zero_or_eq_zero] at h
  rcases h with h|h
  exact hi hn1 h
  exact h

theorem powNat_add {a:α} {m n:Nat} : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => simp
  | succ n hi =>
    rw [← Nat.add_assoc]
    simp
    rw [hi]
    rw [mul_assoc]

noncomputable instance : Pow α Int where
  pow a n :=
    if a = 0 then
      if n = 0 then 1
      else 0
    else if n < 0 then 1 / (a ^ ((-n).toNat))
    else a ^ (n.toNat)

theorem powInt_def {a:α} {n:Int} : a ^ n =
   if a = 0 then
      if n = 0 then 1
      else 0
    else if n < 0 then 1 / (a ^ ((-n).toNat))
    else a ^ (n.toNat)
  := by rfl

@[simp]
theorem powInt_zero {a:α} : a ^ (0:Int) = 1 := by
  by_cases ha : a = 0
  <;>simp [powInt_def]

private theorem powInt_add_lemma_1 {a:α} {m n:Int} (ha: a ≠ 0) (hm: m < 0) (hn: n < 0):a ^ (m + n) = a ^ m * a ^ n := by
  simp [powInt_def]
  simp [ha, hm, hn]
  have : m + n < 0 := by linarith
  simp [this]
  repeat rw [Rudin.div_eq_mul_inv]
  simp
  have {t:Int}: Pow.pow a t.toNat = a ^ t.toNat := by rfl
  rw [inv_mul_inv]
  rw [← powNat_add]
  rw [Int.add_comm]
  repeat rw [Rudin.inv_eq_one_div]
  rw [Rudin.div_eq_div_iff_mul_eq_mul]
  simp
  rw [Rudin.exp_eq_then_powNat_eq]
  rw [Int.toNat_add]
  linarith
  linarith
  refine (powNat_nz_iff_base_nz ?_).mpr ha
  simp
  linarith
  refine (powNat_nz_iff_base_nz ?_).mpr ha
  rw [← Int.toNat_add]
  simp
  linarith
  linarith
  linarith
  refine (powNat_nz_iff_base_nz ?_).mpr ha
  simp
  linarith
  refine (powNat_nz_iff_base_nz ?_).mpr ha
  simp
  linarith

private theorem powInt_add_lemma_2 {a:α} {m n:Int} (ha: a ≠ 0) (hm: m < 0) (hn: ¬ n < 0) (hmn: m + n < 0): a ^ (m + n) = a ^ m * a ^ n := by
  simp [powInt_def]
  simp [ha, hm, hn, hmn]
  rw [mul_comm, Rudin.mul_div_assoc, mul_one]
  rw [Rudin.div_eq_div_iff_mul_eq_mul]
  rw [← powNat_add]
  simp
  apply Rudin.exp_eq_then_powNat_eq
  rw [← Int.toNat_add]
  simp
  linarith
  linarith
  refine (powNat_nz_iff_base_nz ?_).mpr ha
  simp
  linarith
  refine (powNat_nz_iff_base_nz ?_).mpr ha
  simp
  linarith

private theorem powInt_add_lemma_3 {a:α} {m n:Int} (ha: a ≠ 0) (hm: m < 0) (hn: ¬ n < 0) (hmn: ¬ m + n < 0): a ^ (m + n) = a ^ m * a ^ n := by
  simp [powInt_def]
  simp [ha, hm, hn, hmn]
  rw [mul_comm, Rudin.mul_div_assoc, mul_one]
  rw [← Rudin.div_one (a:=a ^ (m + n).toNat)]
  rw [Rudin.div_eq_div_iff_mul_eq_mul]
  rw [← powNat_add]
  simp
  apply Rudin.exp_eq_then_powNat_eq
  rw [← Int.toNat_add]
  ring_nf
  linarith
  linarith
  exact one_nz
  refine (powNat_nz_iff_base_nz ?_).mpr ha
  simp
  linarith


private theorem powInt_add_lemma_4 {a:α} {m n:Int} (ha: a ≠ 0) (hm: ¬ m < 0) (hn: ¬ n < 0): a ^ (m + n) = a ^ m * a ^ n := by
  simp [powInt_def]
  simp [ha, hm, hn]
  have hmn : ¬ m + n < 0 := by linarith
  simp [hmn]
  rw [Int.toNat_add]
  rw [powNat_add]
  linarith
  linarith


theorem powInt_add {a:α} {m n:Int} (ha: a ≠ 0) :  a ^ (m + n) = a ^ m * a ^ n := by
  by_cases hm : m < 0
  <;>by_cases hn: n < 0
  exact powInt_add_lemma_1 ha hm hn
  by_cases hmn : m + n < 0
  exact powInt_add_lemma_2 ha hm hn hmn
  exact powInt_add_lemma_3 ha hm hn hmn
  rw [Int.add_comm, Rudin.mul_comm]
  by_cases hmn : n + m < 0
  exact powInt_add_lemma_2 ha hn hm hmn
  exact powInt_add_lemma_3 ha hn hm hmn
  exact powInt_add_lemma_4 ha hm hn

@[simp]
theorem powInt_one {a:α} : a ^ (1:Int) = a := by
  simp [powInt_def]
  by_cases ha : a = 0
  simp [ha]
  simp [ha]


@[simp]
theorem powInt_add_one {a:α} {n:Int} (ha: a ≠ 0) : a ^ (n + 1) = a ^ n * a := by
  rw [powInt_add]
  simp
  exact ha



instance (priority := default - 1) : AddCommMonoid α where
  add_assoc := by exact fun a b c ↦ add_assoc
  zero_add := by exact fun a ↦ zero_add
  add_zero := by exact fun a ↦ add_zero
  nsmul n a := n • a
  add_comm := by exact fun a b ↦ add_comm
  nsmul_zero := by exact fun x ↦ zero_smul
  nsmul_succ := by exact fun n x ↦ add_one_smul

instance (priority := default - 1) : CommMonoid α where
  mul_assoc := by exact fun a b c ↦ Field.mul_assoc a b c
  one_mul := by exact fun a ↦ one_mul
  mul_one := by exact fun a ↦ mul_one
  mul_comm := by exact fun a b ↦ Field.mul_comm a b
  npow n a := a ^ n
  npow_zero := by exact fun x ↦ pow_zero
  npow_succ := by exact fun n x ↦ powNat_add_one

instance (priority := default - 1) : NonUnitalNonAssocSemiring α where
  left_distrib := by exact fun a b c ↦ Field.mul_add a b c
  right_distrib := by exact fun a b c ↦ add_mul
  zero_mul := by exact fun a ↦ zero_mul
  mul_zero := by exact fun a ↦ mul_zero

instance (priority := default - 1) : SemigroupWithZero α where

instance (priority := default - 1) : NonUnitalSemiring α where

instance (priority := default - 1) : MulZeroOneClass α where

instance (priority := default - 1) : AddCommMonoidWithOne α where

instance (priority := default - 1) : NonAssocSemiring α where

instance (priority := default - 1) : Semiring α where


instance (priority := default - 1) : AddMonoid α where
  nsmul n a := n • a
  nsmul_zero := by exact fun x ↦ zero_smul
  nsmul_succ := by exact fun n x ↦ add_one_smul

attribute [-simp] nsmul_eq_mul  Algebra.smul_mul_assoc

instance (priority := default - 1) : SubNegMonoid α where
  sub a b := a - b
  sub_eq_add_neg := by exact fun a b ↦ Field.sub_eq_add_neg a b
  zsmul n a := if n < 0 then -((-n).toNat • a) else n.toNat • a
  zsmul_zero' := by
    split_ifs with h
    simp
    norm_num

  zsmul_succ' := by
    intro n a
    split_ifs with h1 h2 h3
    linarith
    linarith
    linarith
    simp

  zsmul_neg' := by
    intro n a
    split_ifs with h1 h2 h3
    linarith
    simp
    have : (-Int.negSucc n).toNat = n + 1 := by
      exact rfl
    rw [this]
    simp
    linarith
    simp at h1

instance (priority := default - 1) : AddGroup α where
  neg_add_cancel := by exact fun a ↦ neg_add_eq_zero

instance (priority := default - 1) : AddCommGroup α where

instance (priority := default - 1) : Ring α where

instance (priority := default - 1) : CommRing α where

instance (priority := default - 1) : NonUnitalCommRing α where

instance (priority := default - 1) : AddZeroClass α where
  zero_add a := by simp
  add_zero a := by simp

instance (priority := default - 1) : MulOneClass α where
  one_mul a := by simp
  mul_one a := by simp

instance (priority := default - 1) : NonUnitalNonAssocCommRing α where

instance (priority := default - 1) : NonUnitalNonAssocCommSemiring α where


theorem div_assoc {a b c:α} (hb: b ≠ 0) (hc: c ≠ 0): a / b / c = a / (b * c) := by
  rw [Rudin.div_eq_div_iff_mul_eq_mul]
  rw [← Rudin.mul_assoc]
  simp [hb]
  rw [Rudin.mul_comm]
  exact hc
  refine nz_and_nz_iff_mul_nz.mp ?_
  exact Decidable.not_imp_iff_and_not.mp fun a ↦ hc (a hb)

@[simp]
theorem div_inv {a b:α} (hb: b ≠ 0) : a / b⁻¹ = a * b := by
  rw [Rudin.div_eq_mul_inv]
  rw [Rudin.inv_inv]
  exact hb

theorem powNat_mul {a:α} {m n:Nat} : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => simp
  | succ n hi =>
    rw [Nat.mul_add]
    simp
    rw [powNat_add]
    rw [hi]

theorem mul_powNat {a b:α} {n:Nat} : (a*b) ^ n = a^n * b^n := by
  induction' n with n hn
  simp
  simp
  rw [hn]
  ring

theorem powNat_comm {a:α} {m n:Nat} : (a ^ m) ^ n = (a ^ n) ^ m := by
  repeat rw [← powNat_mul]
  rw [Nat.mul_comm]

theorem powNat_eq_zero_iff {a:α} {n:Nat} : a ^ n = 0 ↔ a = 0 ∧ n ≠ 0 := by
  induction' n with n hn
  simp
  simp
  rw [Rudin.mul_eq_zero_iff_eq_zero_or_eq_zero]
  rw [hn]
  simp
  exact fun a a_1 ↦ a

@[simp]
theorem zero_powInt {n:Int}: (0:α) ^ n = if n = 0 then 1 else 0 := by simp [powInt_def]

@[simp]
theorem one_powInt {n:Int} : (1:α) ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n hi => simp [hi]
  | pred n hi => simp [powInt_def]


theorem powInt_eq_zero_iff {a:α} {n:Int} : a ^ n = 0 ↔ a = 0 ∧ n ≠ 0 := by
  induction' n with n hn n hn
  simp
  by_cases ha: a = 0
  simp [powInt_def, ha]
  rw [powInt_add_one]
  rw [Rudin.mul_eq_zero_iff_eq_zero_or_eq_zero]
  simp [ha]
  intro h
  rw [hn] at h
  simp [ha] at h
  exact ha
  simp [powInt_def]
  by_cases ha : a = 0
  <;>simp [ha]
  split_ifs with h1
  rw [← Rudin.inv_eq_one_div]
  refine inv_nz ?_
  intro h
  rw [powNat_eq_zero_iff] at h
  exact ha h.left
  simp

theorem powInt_negOne_eq_inv {a:α} (ha: a ≠ 0): a ^ (-1:Int) = a⁻¹ := by
  rw [powInt_def]
  simp [ha]
  exact Eq.symm inv_eq_one_div

theorem powInt_sub_one {a:α} {n:Int} (ha: a ≠ 0) : a ^ (n - 1) = a ^ n * a⁻¹ := by
  rw [Int.sub_eq_add_neg, powInt_add, powInt_negOne_eq_inv]
  repeat exact ha

@[simp]
theorem powInt_nz_iff_base_nz {a:α} {n:Int} (hn: n ≠ 0): a ^ n ≠ 0 ↔ a ≠ 0 := by
  constructor
  intro h
  intro h1
  apply h
  refine powInt_eq_zero_iff.mpr ?_
  exact Decidable.not_imp_iff_and_not.mp fun a ↦ hn (a h1)
  intro h
  intro h1
  rw [powInt_eq_zero_iff] at h1
  exact h h1.left


theorem powInt_sub {a:α} {m n:Int} {ha: a≠ 0}: a ^ (m - n) = a ^ m / a ^ n := by
  induction' n with u hu v hv
  simp
  by_cases hu0 : u = 0
  simp [hu0]
  rw [powInt_sub_one, Rudin.div_eq_mul_inv]
  exact ha
  rw [Int.sub_eq_add_neg, Int.neg_add, ← Int.add_assoc, ← Int.sub_eq_add_neg, powInt_sub_one]
  rw [← Int.sub_eq_add_neg, hu]
  rw [powInt_add, ← Rudin.div_eq_mul_inv]
  rw [Rudin.div_eq_div_iff_mul_eq_mul]
  rw [← Rudin.mul_assoc, Rudin.div_mul_cancel, powInt_one, Rudin.mul_comm]
  rw [powInt_nz_iff_base_nz]
  exact ha
  exact Int.ofNat_ne_zero.mpr hu0
  exact ha
  simp
  intro h
  rw [Rudin.mul_eq_zero_iff_eq_zero_or_eq_zero] at h
  simp [ha] at h
  rw [powInt_eq_zero_iff] at h
  exact ha h.left
  exact ha
  exact ha
  by_cases hv0 : v = 0
  simp [hv0, ha]
  rw [powInt_negOne_eq_inv, Rudin.div_inv]
  exact ha
  exact ha
  rw [Int.sub_eq_add_neg, Int.neg_sub, Int.sub_eq_add_neg]
  rw [← Int.add_comm, Int.add_assoc, Int.add_comm, powInt_add_one]
  rw [Int.add_comm, ← Int.sub_eq_add_neg, hv]
  rw [powInt_sub_one]
  rw [← div_assoc, Rudin.div_inv]
  exact ha
  refine (powInt_nz_iff_base_nz ?_).mpr ha
  simp [hv0]
  exact inv_nz ha
  exact ha
  exact ha

theorem powInt_neg {a:α} {n:Int} (ha: a ≠ 0) : a ^ (-n) = 1 / a^n := by
  rw (occs := .pos [1]) [← Int.zero_add (a:=n)]
  rw [Int.neg_add, Int.neg_zero, ← Int.sub_eq_add_neg, powInt_sub]
  simp
  exact ha

theorem powInt_mul {a:α} {m n:Int} (ha: a ≠ 0) : a ^ (m * n) = (a ^ m) ^ n := by
  induction' n with n hn n hn
  simp
  rw [Int.mul_add, powInt_add]
  rw [hn]
  rw [powInt_add_one]
  simp
  intro h
  rw [powInt_eq_zero_iff] at h
  exact ha h.left
  exact ha
  by_cases hm : m = 0
  simp [hm]
  rw [powInt_sub_one]
  simp [Int.mul_sub]
  rw [powInt_sub]
  simp at hn
  rw [hn]
  rw [Rudin.div_eq_mul_inv]
  exact ha
  refine (powInt_nz_iff_base_nz ?_).mpr ha
  exact hm

theorem powInt_comm {a:α} {m n:Int} (ha: a ≠ 0) : (a ^ m) ^ n = (a ^ n) ^ m := by
  repeat rw [← powInt_mul]
  rw [Int.mul_comm]
  repeat exact ha

private theorem mul_powInt_lemma_0 {a b:α} {n:Int} (ha: a = 0) :  (a * b) ^ n = a ^ n * b ^ n := by
  simp [ha]
  by_cases hn : n = 0
  simp [hn]
  simp [hn]

theorem mul_powInt {a b:α} {n:Int} : (a * b) ^ n = a ^ n * b ^ n := by
  by_cases ha : a = 0
  exact mul_powInt_lemma_0 (n:=n) ha
  by_cases hb : b = 0
  rw [mul_comm]
  rw [mul_comm (b:=b^n)]
  exact mul_powInt_lemma_0 (n:=n) hb
  have hab : a * b ≠ 0 := by
    refine nz_and_nz_iff_mul_nz.mp ?_
    exact Decidable.not_imp_iff_and_not.mp fun a ↦ hb (a ha)
  induction' n with n hn n hn
  simp
  simp [ha, hb, hab]
  rw [hn]
  ring
  simp [powInt_sub_one, ha, hb, hab]
  rw [hn]
  have : (a*b)⁻¹ = a⁻¹ * b⁻¹ := by exact Eq.symm (inv_mul_inv ha hb)
  rw [this]
  ring

theorem powNat_eq_powInt {a:α} {n:Nat}: a ^ n = a ^ (n:Int) := by
  rw [powInt_def]
  by_cases ha : a = 0
  <;>simp [ha]



end Rudin
