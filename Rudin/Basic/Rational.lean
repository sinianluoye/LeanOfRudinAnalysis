import Mathlib
import Batteries.Data.Rat
import Rudin.Basic.Integer


/-
Although some proofs use the properties of rings in mathlib,
comments are still provided here to show how to prove the statements without using the properties of rings.
-/

namespace Rudin

namespace Rat
variable {a b c:ℚ}

open _root_.Rat

theorem add_comm: a + b = b + a := by
  rw [add_def']
  rw [add_def']
  rw [Nat.mul_comm]
  rw [Int.add_comm]

@[simp] theorem zero_add : 0 + a = a := by
  simp

@[simp] theorem add_zero : a + 0 = a := by
  simp

theorem den_zero_then_zero (h: a.den = 0) : a = 0 := by
  rw [← mkRat_self a]
  rw [h]
  simp

theorem nz_then_den_nz (h: a ≠ 0) : a.den ≠ 0 := by
  intro h1
  exact (h (den_zero_then_zero h1)).elim

theorem nz_then_num_nz (h: a ≠ 0) : a.num ≠ 0 := by
  have h1 := h
  rw [← mkRat_self a] at h
  rw [mkRat_ne_zero] at h
  exact h
  exact nz_then_den_nz h1

theorem add_assoc_lemma_1 (h: a = 0 ∨ b = 0 ∨ c = 0) : a + b + c = a + (b + c) := by
  rcases h with h | h | h
  <;>rw [h]
  <;>simp

theorem add_assoc_lemma_2 (h: a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) : a + b + c = a + (b + c) := by
  have hadnz := nz_then_den_nz h.left
  have hbdnz := nz_then_den_nz h.right.left
  have hcdnz := nz_then_den_nz h.right.right
  have habdnz : a.den * b.den ≠ 0 := Nat.mul_ne_zero_iff.mpr ⟨ hadnz, hbdnz ⟩
  have hbcnz : b.den * c.den ≠ 0 :=  Nat.mul_ne_zero_iff.mpr ⟨ hbdnz, hcdnz ⟩
  rw [← mkRat_self a, ← mkRat_self b, ← mkRat_self c]
  repeat rw [mkRat_add_mkRat]
  repeat simp [Int.add_mul, ← Int.mul_assoc, ← Int.add_assoc, ← Nat.mul_assoc]
  rw [Int.mul_assoc b.num  ↑c.den  ↑a.den, Int.mul_comm (↑c.den) (↑a.den), ← Int.mul_assoc]
  rw [Int.mul_assoc c.num  ↑b.den  ↑a.den, Int.mul_comm (↑b.den) (↑a.den), ← Int.mul_assoc]
  exact hadnz
  exact hbcnz
  exact hbdnz
  exact hcdnz
  exact habdnz
  exact hcdnz
  exact hadnz
  exact hbdnz


theorem add_assoc: a + b + c = a + (b + c) := by
  by_cases h:a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0
  exact add_assoc_lemma_2 h
  have h1 : a = 0 ∨ b = 0 ∨ c = 0 := by
    repeat rw [ne_eq] at h
    simp at h
    by_cases ha: a = 0
    left
    exact ha
    have hbc := h ha
    by_cases hb : b = 0
    right
    left
    exact hb
    right
    right
    exact hbc hb
  exact add_assoc_lemma_1 h1

theorem add_neg : a + -a = 0 := by simp
  -- rw [Rat.add_def']
  -- simp [Rat.neg]
  -- rw [← Int.add_mul]
  -- rw [Int.add_neg_eq_sub]
  -- rw [Int.sub_self]
  -- rw [Int.zero_mul]
  -- exact zero_mkRat (a.den * a.den)

theorem neg_add :  -(a + b) = -a - b := by
  rw [Rat.sub_eq_add_neg]
  rw [← Rat.mkRat_self a, ← Rat.mkRat_self b]
  rw [mkRat_add_mkRat]
  rw [Rat.neg_mkRat, Rat.neg_mkRat, Rat.neg_mkRat]
  rw [mkRat_add_mkRat]
  repeat rw [Int.neg_add]
  repeat rw [Int.neg_mul]
  exact a.den_nz
  exact b.den_nz
  exact a.den_nz
  exact b.den_nz

theorem one_nz : (1:ℚ) ≠ (0:ℚ) := by
  norm_cast



theorem mul_assoc : a * b * c = a * (b * c) := by
  by_cases h: a = 0 ∨ b = 0 ∨ c = 0
  rcases h with h|h|h
  <;>rw [h]
  <;>simp
  simp at h
  rw [← mkRat_self a]
  rw [← mkRat_self b]
  rw [← mkRat_self c]
  repeat rw [mkRat_mul_mkRat]
  simp [← Int.mul_assoc, ← Nat.mul_assoc]

theorem mul_add : a * (b + c) = a * b + a * c := by
  by_cases h: a = 0 ∨ b = 0 ∨ c = 0
  rcases h with h|h|h
  <;>rw [h]
  <;>simp
  simp at h
  have hadnz := nz_then_den_nz h.left
  have hbdnz := nz_then_den_nz h.right.left
  have hcdnz := nz_then_den_nz h.right.right

  rw [← mkRat_self a]
  rw [← mkRat_self b]
  rw [← mkRat_self c]
  rw [mkRat_add_mkRat]
  rw [mkRat_mul_mkRat]
  rw [mkRat_mul_mkRat]
  rw [mkRat_mul_mkRat]
  rw [mkRat_add_mkRat]
  rw [← mkRat_mul_left (a:=a.den)]
  simp [Int.mul_add]
  simp [← Int.mul_assoc]
  rw [Int.mul_assoc ↑a.den   a.num   b.num, Int.mul_assoc ↑a.den   (a.num * b.num)   ↑c.den, Int.mul_comm (a.num * b.num)  ↑c.den]
  rw [← Int.mul_assoc]
  rw [Int.mul_assoc (a.num * b.num) ↑a.den  ↑c.den]
  rw [Int.mul_comm (a.num * b.num)]
  rw [Int.mul_assoc ↑a.den  a.num  c.num, Int.mul_comm  ↑a.den  (a.num * c.num)]
  simp [← Nat.mul_assoc]
  rw [Nat.mul_assoc a.den b.den a.den, Nat.mul_comm b.den a.den]
  simp [← Nat.mul_assoc]

  exact hadnz
  exact Nat.mul_ne_zero_iff.mpr ⟨ hadnz, hbdnz ⟩
  exact Nat.mul_ne_zero_iff.mpr ⟨ hadnz, hcdnz ⟩
  exact hbdnz
  exact hcdnz

theorem divInt_eq_one {a:Int} (ha: a ≠ 0): a /. a = 1 := by
  rw [← divInt_self 1]
  rw [one_num, one_den]
  rw (occs := .pos [2]) [← divInt_mul_left ha  (a:=a)]
  simp

theorem mul_inv_when_nz (hanz:a ≠ 0) : a * (1 / a) = 1 := by
  have hadnz := nz_then_den_nz hanz
  have hannz := nz_then_num_nz hanz
  rw [div_def]
  rw [← mul_assoc]
  rw [Rat.mul_comm a 1, mul_assoc]
  rw [Rat.inv_def]
  rw (occs := .pos [1]) [← divInt_self a]
  rw [divInt_mul_divInt]
  rw [Int.mul_comm ↑a.den]
  rw [divInt_eq_one]
  simp
  apply Int.mul_ne_zero_iff.mpr
  constructor
  exact hannz
  rw [Int.natCast_ne_zero]
  exact hadnz
  rw [Int.natCast_ne_zero]
  exact hadnz
  exact hannz

theorem inv_eq_one_div : a.inv = 1 / a := by
  rw [div_def]
  rw [Rat.one_mul]

theorem div_eq_mul_inv : a / b = a * (1 / b) := by
  rw [div_def]
  rw [div_def]
  rw [Rat.one_mul]

-- instance instPowNat : HPow Rat Nat (outParam Rat) where
--   hPow a n :=  ⟨a.num ^ n, a.den ^ n, by
--     simp [Nat.pow_eq_zero]
--     -- intro h
--     -- exact (a.den_nz h).elim
--   , by
--     rw [Int.natAbs_pow]
--     exact a.reduced.pow _ _
--   ⟩

theorem pow_succ {n:Nat} : a ^ (n + 1) = a ^ n * a := by
  ring
  -- simp [Rat.instPowNat]
  -- rw [mk_eq_mkRat, mk_eq_mkRat]
  -- rw (occs := .pos [5])[← mkRat_self a]
  -- rw [mkRat_mul_mkRat]
  -- rw [Int.pow_succ, Nat.pow_succ]

@[simp] theorem pow_zero : a ^ 0 = 1 := by simp
  -- simp [instPowNat]
  -- norm_cast

@[simp] theorem zero_pow {n:Nat}: (0:ℚ) ^ n = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  <;>simp [hn]
  -- simp [Rat.instPowNat]
  -- cases n with
  -- | zero => exact (hn rfl).elim
  -- | succ k =>
  --   rw [Nat.add_one, Int.pow_succ', Int.zero_mul]
  --   norm_cast

theorem pow_nat_def {n:Nat} : a ^ n = if n = 0 then 1 else a ^ (n - 1) * a:= by
  by_cases hn : n = 0
  <;>simp [hn]
  have h: n > 0 := Nat.pos_iff_ne_zero.mpr hn
  have h1 := Nat.sub_one_add_one_eq_of_pos h
  rw [← h1]
  simp
  rw [pow_succ]



theorem mkRat_pow {n:Int} {d:Nat} {m:Nat} : (mkRat n d) ^ m = mkRat (n^m) (d^m) := by
  by_cases hd : d = 0
  simp [mkRat_def, hd]
  by_cases hm : m = 0
  <;>simp [hm]
  rw [Rat.normalize_eq]
  simp
  -- norm_cast
  induction m with
  | zero =>
    simp
    -- rw [← mkRat_self 1]
    -- rfl
  | succ k hi =>
    rw [pow_succ]
    rw [hi]
    rw [mkRat_mul_mkRat]
    rw [Int.pow_succ, Nat.pow_succ]




theorem mkRat_sub_mkRat {n1 n2:Int} {d1 d2: Nat}
  (hd1: d1 ≠ 0) (hd2: d2 ≠ 0):
  mkRat n1 d1 - mkRat n2 d2 = mkRat (n1 * d2 - n2 * d1) (d1 * d2) := by
  rw [Rat.sub_eq_add_neg, neg_mkRat, mkRat_add_mkRat]
  rw [Int.neg_mul, Int.add_neg_eq_sub]
  exact hd1
  exact hd2

@[simp] theorem mkRat_num_ltz_iff_num_ltz {n:Int} {d:Nat} (hd: d ≠ 0): (mkRat n d).num < 0 ↔ n < 0 := by
  constructor
  <;>intro h
  simp [Rat.mkRat_def, hd, Rat.normalize] at h
  rw [Int.ediv_lt_iff_lt_mul] at h
  simp at h
  exact h
  simp
  left
  intro h1
  simp [h1] at h
  simp [Rat.mkRat_def, hd, Rat.normalize]
  rw [Int.ediv_lt_iff_lt_mul]
  simp
  exact h
  norm_cast
  simp
  left
  intro h1
  simp [h1] at h

@[simp] theorem mkRat_ltz_iff_num_ltz {n:Int} {d:Nat}: mkRat n d < 0 ↔ (mkRat n d).num < 0 := by
  constructor
  <;>intro h
  simp
  exact h
  simp at h
  exact h
  -- intro h
  -- simp [Rat.instLT, Rat.blt] at h
  -- rw [← and_assoc] at h
  -- simp at h
  -- exact h
  -- intro h
  -- simp [Rat.instLT, Rat.blt]
  -- rw [← and_assoc]
  -- simp
  -- exact h

@[simp] theorem mkRat_ez_iff_num_zero {n:Int} {d:Nat} (hd: d ≠ 0): mkRat n d = 0 ↔ n = 0 := by
  constructor
  intro h
  rw [mkRat_eq_zero] at h
  exact h
  exact hd
  intro h
  rw [mkRat_eq_zero]
  exact h
  exact hd

@[simp] theorem mkRat_gtz_iff_num_gtz {n:Int} {d:Nat}: mkRat n d > 0 ↔ (mkRat n d).num > 0 := by
  simp
  -- simp [Rat.instLT, Rat.blt]


@[simp] theorem mkRat_num_gtz_iff_num_gtz {n:Int} {d:Nat} (hd: d ≠ 0): (mkRat n d).num > 0 ↔ n > 0 := by
  constructor
  <;>intro h
  simp [Rat.mkRat_def, hd, Rat.normalize] at h
  rw [Int.lt_ediv_iff_mul_lt] at h
  simp at h
  exact h
  simp
  left
  intro h1
  simp [h1] at h
  rw [← Int.dvd_natAbs]
  exact Int.gcd_dvd_left (↑n.natAbs) d
  simp [Rat.mkRat_def, hd, Rat.normalize]
  rw [Int.lt_ediv_iff_mul_lt]
  simp
  exact h
  norm_cast
  simp
  left
  intro h1
  simp [h1] at h
  rw [← Int.dvd_natAbs]
  exact Int.gcd_dvd_left (↑n.natAbs) d



  -- simp [mkRat, hd] at h
  -- simp [Rat.normalize] at h
  -- rw [Int.lt_ediv_iff_mul_lt] at h
  -- rw [Int.zero_mul] at h
  -- exact h
  -- have hnnz : n ≠ 0 := by
  --   intro h1
  --   rw [h1] at h
  --   simp at h
  -- simp
  -- left
  -- exact hnnz
  -- rw [← Int.dvd_natAbs]
  -- exact Int.gcd_dvd_left (↑n.natAbs) d
  -- simp [mkRat, hd]
  -- simp [normalize]
  -- rw [Int.lt_ediv_iff_mul_lt]
  -- rw [Int.zero_mul]
  -- exact h
  -- simp
  -- left
  -- exact Int.ne_of_gt h
  -- rw [← Int.dvd_natAbs]
  -- exact Int.gcd_dvd_left (↑n.natAbs) d

theorem den_gtz : a.den > 0 := by
  simp
  rw [Nat.lt_iff_le_and_ne]
  simp
  exact a.den_nz.symm

theorem ltz_iff_num_ltz : a < 0 ↔ a.num < 0 := by
  rw [← mkRat_self a]
  exact mkRat_ltz_iff_num_ltz

theorem gtz_iff_num_gtz : a > 0 ↔ a.num > 0 := by
  rw [← mkRat_self a]
  exact mkRat_gtz_iff_num_gtz

theorem ez_iff_num_ez : a = 0 ↔ a.num = 0 := by
  rw (occs := .pos [1]) [← mkRat_self a, mkRat_eq_zero]
  exact a.den_nz



theorem lt_iff_sub_ltz : a < b ↔ a - b < 0 := by simp
  -- have hadnz := a.den_nz
  -- have hbdnz := b.den_nz
  -- have habdnz : a.den * b.den ≠ 0 := by
  --   rw [Nat.mul_ne_zero_iff]
  --   exact ⟨ hadnz, hbdnz⟩
  -- have hadgtz := den_gtz (a:=a)
  -- have hbdgtz := den_gtz (a:=b)

  -- constructor
  -- intro h
  -- simp [Rat.instLT, Rat.blt]
  -- simp [Rat.instLT, Rat.blt] at h

  -- rw [← and_assoc]
  -- simp
  -- rw [← mkRat_self a, ← mkRat_self b]
  -- rw [mkRat_sub_mkRat]

  -- simp [hadnz, hbdnz, habdnz, Int.ne_and_le_iff_lt]
  -- rcases h with h|h
  -- have h2: a.num * ↑b.den < 0 := by
  --   apply  Int.ltz_mul_gtz_then_ltz
  --   exact h.left
  --   norm_cast
  -- have h3: ↑a.den * b.num ≥ 0:= by
  --   rw [Int.mul_comm]
  --   apply Int.gez_mul_gtz_then_gez
  --   exact h.right
  --   norm_cast
  -- rcases Int.lt_trichotomy (a.num * ↑b.den - b.num * ↑a.den) 0 with h1|h1|h1
  -- simp [h1]
  -- simp [h1]
  -- rw [Int.sub_eq_zero] at h1
  -- rw [Int.mul_comm b.num] at h1
  -- simp at h3
  -- rw [Int.le_iff_eq_or_lt] at h3
  -- rcases h3 with h3|h3
  -- rw [h3] at h2
  -- apply Int.ne_of_lt h2
  -- exact h1
  -- apply Int.ne_of_lt (Int.lt_trans h2 h3)
  -- exact h1
  -- exfalso
  -- rw [← Int.not_le] at h1
  -- apply h1
  -- apply Int.sub_le_of_sub_le
  -- simp
  -- have h4: a.num * ↑b.den ≤ 0 := by
  --   apply Int.le_of_lt
  --   exact h2
  -- rw [Int.mul_comm] at h3
  -- exact Int.le_trans h4 h3
  -- by_cases h1:a.num = 0
  -- <;>simp [h1] at h
  -- simp [h1]
  -- apply Int.gtz_mul_gtz_then_gtz
  -- exact h
  -- norm_cast
  -- apply Int.sub_lt_of_sub_lt
  -- simp
  -- exact h.right
  -- exact hadnz
  -- exact hbdnz
  -- intro h
  -- rw [← mkRat_self a, ← mkRat_self b] at h
  -- rw [mkRat_sub_mkRat] at h
  -- simp [habdnz] at h
  -- simp [Rat.instLT, Rat.blt]
  -- by_cases h1:a.num = 0
  -- simp [h1]
  -- simp [h1] at h
  -- rw [← Int.mul_lt_mul_right (a:=a.den)]
  -- simp
  -- exact h
  -- norm_cast
  -- rw [Int.sub_ltz_iff_lt] at h
  -- simp [Int.le_iff_eq_or_lt, h1, h]
  -- rcases Int.lt_trichotomy a.num 0 with h2|h2|h2
  -- simp [h2]
  -- exfalso
  -- exact h1 h2
  -- right
  -- right
  -- have h3:a.num * b.den > 0 := by
  --   apply Int.gtz_mul_gtz_then_gtz
  --   exact h2
  --   norm_cast
  -- rw [Int.lt_iff_gt]
  -- have : b.num * a.den > 0 := by
  --   exact Int.lt_trans h3 h
  -- apply Int.mul_gtz_gtz_then_gtz (b := ↑a.den)
  -- norm_cast
  -- exact this
  -- exact hadnz
  -- exact hbdnz

theorem ltz_add_ltz_ltz (ha: a < 0) (hb: b < 0) : a + b < 0 := by
  linarith

  -- have hadnz := a.den_nz
  -- have hbdnz := b.den_nz
  -- have habdnz : a.den * b.den ≠ 0 := by
  --   rw [Nat.mul_ne_zero_iff]
  --   exact ⟨ hadnz, hbdnz⟩
  -- have hadgtz := den_gtz (a:=a)
  -- have hbdgtz := den_gtz (a:=b)
  -- rw [← mkRat_self a, ← mkRat_self b]
  -- rw [← mkRat_self a] at ha
  -- rw [← mkRat_self b] at hb
  -- rw [mkRat_add_mkRat]
  -- simp [hadnz, hbdnz, habdnz]
  -- simp [hadnz, hbdnz, habdnz] at ha
  -- simp [hadnz, hbdnz, habdnz] at hb
  -- rw [← Int.zero_add 0]
  -- apply Int.add_lt_add
  -- apply Int.ltz_mul_gtz_then_ltz
  -- exact ha
  -- norm_cast
  -- apply Int.ltz_mul_gtz_then_ltz
  -- exact hb
  -- norm_cast
  -- exact hadnz
  -- exact hbdnz


theorem lt_trans (hab: a < b) (hbc: b < c) : a < c := by
  rw [lt_iff_sub_ltz] at *
  have h : (a - b) + (b - c) < 0 := by
    apply ltz_add_ltz_ltz
    exact hab
    exact hbc
  repeat rw [Rat.sub_eq_add_neg] at h
  rw [← Rat.add_assoc, Rat.add_assoc (a:=a)] at h
  rw [Rat.add_comm (a:=-b)] at h
  rw [Rat.add_neg] at h
  rw [Rat.add_zero] at h
  rw [← Rat.sub_eq_add_neg] at h
  exact h

theorem add_lt_add {a b c d:ℚ} (hab: a < b) (hcd: c < d): a + c < b + d := by
  rw [lt_iff_sub_ltz] at *
  have h : (a - b) + (c - d) < 0 := by
    apply ltz_add_ltz_ltz
    exact hab
    exact hcd
  rw [Rat.sub_eq_add_neg, Rat.neg_add, Rat.sub_eq_add_neg, ← Rat.add_assoc]
  rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, ← Rat.add_assoc] at h
  rw [Rat.add_assoc (a:=a), add_comm (a:=c), ← Rat.add_assoc]
  exact h

theorem lt_trichotomy : a < b ∨ a = b ∨ b < a := by
  by_cases h : a < b
  <;>simp [h]
  by_cases h1 : a = b
  <;>simp [h1]
  apply lt_of_not_ge
  rw [le_iff_lt_or_eq]
  intro h2
  rcases h2 with h2 | h2
  exact h h2
  exact h1 h2

  -- have hadnz := a.den_nz
  -- have hbdnz := b.den_nz
  -- have habdnz : a.den * b.den ≠ 0 := by
  --   rw [Nat.mul_ne_zero_iff]
  --   exact ⟨ hadnz, hbdnz⟩
  -- have hbadnz : b.den * a.den ≠ 0 := by
  --   rw [Nat.mul_comm]
  --   exact habdnz
  -- rw [lt_iff_sub_ltz, lt_iff_sub_ltz (a:=b), ← mkRat_self a, ← mkRat_self b]
  -- rw [mkRat_sub_mkRat, mkRat_sub_mkRat]
  -- simp [hadnz, hbdnz, habdnz, hbadnz]
  -- rw [mkRat_eq_iff]
  -- rw [Int.sub_ltz_iff_lt, Int.sub_ltz_iff_lt]
  -- exact Int.lt_trichotomy (a.num * ↑b.den) (b.num * ↑a.den)
  -- exact hadnz
  -- exact hbdnz
  -- exact hbdnz
  -- exact hadnz
  -- exact hadnz
  -- exact hbdnz

theorem ne_of_lt (hab: a < b) : a ≠ b := by
  intro h
  rw [lt_iff_sub_ltz] at hab
  rw [h] at hab
  rw [Rat.sub_eq_add_neg, add_neg] at hab
  exfalso
  norm_cast

theorem ne_of_gt (hab: a > b) : a ≠ b := by
  symm
  simp at hab
  exact ne_of_lt hab

theorem lt_irrefl : ¬ a < a := by
  rw [lt_iff_sub_ltz]
  rw [Rat.sub_eq_add_neg, add_neg]
  norm_cast

theorem lt_asymm (hab: a < b): ¬ b < a := by
  intro h
  have h1 := lt_trans hab h
  exact lt_irrefl h1

theorem lt_trichotomy_complete :
    (a < b ∧ ¬ a = b ∧ ¬ b < a) ∨
    (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
    (¬ a < b ∧ ¬ a = b ∧ b < a) := by
  rcases lt_trichotomy (a:=a) (b:=b) with h|h|h
  <;>simp [h]
  rw [le_iff_lt_or_eq]
  simp [h]
  apply ne_of_lt
  exact h
  simp [le_iff_lt_or_eq]
  constructor
  left
  exact h
  apply ne_of_gt
  exact h
  -- constructor
  -- intro h1
  -- rw [h1] at h
  -- exact lt_irrefl h
  -- exact lt_asymm h
  -- exact lt_irrefl
  -- constructor
  -- exact lt_asymm h
  -- intro h1
  -- rw [h1] at h
  -- exact lt_irrefl h

theorem lt_iff_not_le : a < b ↔ ¬ b ≤ a := by
  simp [Rat.instLT, Rat.instLE]

theorem lt_iff_num_den : a < b ↔ a.num * b.den < b.num * a.den := by
  rw [lt_iff_sub_ltz, Rat.sub_eq_add_neg]
  rw (occs := .pos [1])[← mkRat_self a, ← mkRat_self b, neg_mkRat, mkRat_add_mkRat]
  rw [mkRat_ltz_iff_num_ltz]
  rw [mkRat_num_ltz_iff_num_ltz]
  rw [Int.neg_mul, Int.add_neg_eq_sub, Int.sub_lt_iff, Int.zero_add]

  have habdnz : a.den * b.den ≠ 0 := by
    rw [Nat.mul_ne_zero_iff]
    exact ⟨ a.den_nz, b.den_nz⟩
  exact habdnz
  exact a.den_nz
  exact b.den_nz

theorem eq_iff_num_den : a = b ↔ a.num * b.den = b.num * a.den := by
  rw (occs := .pos [1])[← mkRat_self a, ← mkRat_self b]
  exact mkRat_eq_iff a.den_nz b.den_nz

theorem eq_or_not_eq : a = b ∨ a ≠ b := by
  by_cases h : a = b
  left
  exact h
  right
  exact h

theorem le_iff_lt_or_eq : a ≤ b ↔ a < b ∨ a = b := by
  rw [_root_.le_iff_lt_or_eq]
  -- simp [Rat.instLE, Rat.instLT, Rat.blt]
  -- simp [Int.le_iff_eq_or_lt]
  -- have : 0 = b.num ↔ b.num = 0 := by
  --   constructor
  --   intro h
  --   rw [h]
  --   intro h
  --   rw [h]

  -- simp [this, ← lt_iff_num_den, ← eq_iff_num_den, ← ez_iff_num_ez, ← ez_iff_num_ez, ← ltz_iff_num_ltz, ← gtz_iff_num_gtz]
  -- rcases lt_trichotomy (a:=b) (b:=0) with hb|hb|hb
  -- <;>simp [hb]
  -- <;>rcases lt_trichotomy (a:=a) (b:=0) with ha|ha|ha
  -- simp [ne_of_lt ha, ne_of_lt hb, lt_asymm ha, lt_asymm hb, lt_irrefl, ha, hb, or_comm]
  -- simp [ne_of_lt hb, lt_asymm hb, lt_irrefl, ha, hb, or_comm]
  -- intro h
  -- rw [h] at hb
  -- exact lt_irrefl hb
  -- simp [ne_of_lt hb, lt_asymm hb, lt_irrefl, ha, hb, or_comm]
  -- simp [ne_of_gt ha, ne_of_lt hb, lt_asymm ha, lt_asymm hb]
  -- apply ne_of_gt
  -- simp
  -- exact lt_trans hb ha
  -- simp [ne_of_lt ha,  hb, lt_asymm ha, lt_irrefl]
  -- simp [lt_irrefl, ha, hb]
  -- simp [ne_of_lt ha,  hb, lt_asymm ha, lt_irrefl]
  -- simp [ne_of_lt ha, ne_of_gt hb, lt_asymm ha, lt_asymm hb, lt_trans ha hb]
  -- simp [ha, ne_of_gt hb, lt_asymm hb, lt_irrefl]
  -- simp [ne_of_gt ha, ne_of_gt hb, lt_asymm ha, lt_asymm hb, lt_irrefl, ha, hb]
  -- rw [or_comm]

theorem nat_mul_def {n:Nat}: n * a = if n = 0 then 0 else ↑(n - 1) * a + a:= by
  by_cases h: n = 0
  <;>simp [h]
  -- rw [← Rat.zero_mul (a:=a)]
  -- rfl
  have hn: n > 0 := Nat.pos_iff_ne_zero.mpr h
  have h1 := Nat.sub_one_add_one_eq_of_pos hn
  have h2 : (↑(n-1):Int) = n - 1 := by
    rw [Int.ofNat_sub]
    rfl
    rw [Nat.succ_le]
    exact hn
  have h3 : (↑(n-1):ℚ) = (↑(n-1):Int) := by
    rfl
  have h4 : (↑(n-1):ℚ) = n - 1 := by
    rw [h3, h2]
    simp
    -- rfl
  rw [h4]
  rw (occs := .pos [3])[← Rat.one_mul a]
  rw [Rat.mul_comm (↑n - 1), Rat.mul_comm 1]
  rw [← Rat.mul_add]
  rw [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm (a:=-1), Rat.add_neg, Rat.add_zero, Rat.mul_comm]

theorem add_lt_left_cancel : a + b < a + c ↔ b < c := by
  rw [Rat.lt_iff_sub_ltz]
  rw [Rat.sub_eq_add_neg]
  rw [Rat.neg_add, Rat.sub_eq_add_neg]
  rw [← Rat.add_assoc]
  rw [Rat.add_assoc (a:=a), Rat.add_comm (a:=b)]
  rw [← Rat.add_assoc]
  rw [Rat.add_neg, Rat.zero_add]
  rw [← Rat.sub_eq_add_neg]
  rw [Rat.lt_iff_sub_ltz (a:=b) (b:=c)]

theorem gtz_mul_gtz_then_gtz (ha: a > 0) (hb: b > 0) : a * b > 0 := by
  rw [Rat.gtz_iff_num_gtz] at *
  rw [← mkRat_self a, ← mkRat_self b, mkRat_mul_mkRat]
  rw [mkRat_num_gtz_iff_num_gtz]
  exact Int.gtz_mul_gtz_then_gtz ha hb
  rw [Nat.mul_ne_zero_iff]
  exact ⟨a.den_nz, b.den_nz⟩

theorem gez_mul_gez_then_gez (ha: a ≥ 0) (hb: b ≥ 0) : a * b ≥ 0 := by
  rw [ge_iff_le, le_iff_lt_or_eq] at *
  rcases ha with ha|ha
  rcases hb with hb|hb
  left
  exact gtz_mul_gtz_then_gtz ha hb
  right
  simp
  right
  symm
  assumption
  right
  simp
  left
  symm
  exact ha


theorem mkRat_den_eq_iff {a:Int} {b c:Nat} (ha: a ≠ 0) (hb: b ≠ 0): (mkRat a b).den = c ↔ b = c * (a.natAbs.gcd b) := by
  constructor
  intro h
  simp [mkRat] at h
  simp [hb, Rat.normalize] at h
  rw [← h]
  rw [Nat.div_mul_cancel]
  exact Nat.gcd_dvd_right a.natAbs b
  intro h
  simp [mkRat, hb, Rat.normalize]
  rw [h]
  rw [Nat.mul_div_assoc]
  have : a.natAbs.gcd b / a.natAbs.gcd (c * a.natAbs.gcd b) = 1 := by
    refine Eq.symm (Nat.eq_div_of_mul_eq_right ?_ ?_)
    refine Nat.gcd_ne_zero_left ?_
    exact Int.natAbs_ne_zero.mpr ha
    simp
    exact congrArg a.natAbs.gcd (id (Eq.symm h))
  rw [this]
  simp
  exact dvd_of_eq (congrArg a.natAbs.gcd (id (Eq.symm h)))

theorem den_ne_one_then_add_int_den_ne_one {a:Rat} {b:Int} (ha: a.den ≠ 1) : (a + b).den ≠ 1 := by
  contrapose! ha
  have : a = (a + b) - b := by ring
  rw [this]

  -- Use the characterization that den = 1 iff the number is an integer
  have ab_int : (a + b : ℚ) = ((a + b).num : ℚ) := by
    rw [← Rat.num_div_den (a + b), ha]
    norm_cast
    simp

  rw [ab_int]
  rw [sub_eq_add_neg, ← Int.cast_neg, ← Int.cast_add]
  exact Rat.den_intCast _

theorem add_num_eq {a b:Rat} : (a + b).num = (a.num * b.den + b.num * a.den) / (a.num * b.den + b.num * a.den).natAbs.gcd (a.den * b.den) := by
  rw [Rat.add_def]
  simp [Rat.normalize]

theorem add_den_eq {a b:Rat} : (a + b).den = (a.den * b.den)  / (a.num * b.den + b.num * a.den).natAbs.gcd (a.den * b.den) := by
  rw [Rat.add_def]
  simp [Rat.normalize]

private lemma add_int_lemma_1 {a:Rat} {b:Int} : (a.num + b * ↑a.den).natAbs.gcd a.den = 1 := by
  have h1: a.den = ((a.den):Int).natAbs := by
    exact rfl
  rw [h1]
  rw [← Int.gcd_eq_natAbs_gcd_natAbs]
  rw [← Int.isCoprime_iff_gcd_eq_one]
  simp
  refine IsCoprime.add_mul_right_left_iff.mpr ?_
  rw [Int.isCoprime_iff_nat_coprime]
  rw [← h1]
  exact a.reduced

theorem add_int_den {a:Rat} {b:Int} : (a+b).den = a.den := by
  simp [add_den_eq]
  rw [add_int_lemma_1 (a:=a) (b:=b)]
  simp

theorem add_int_num {a:Rat} {b:Int} : (a+b).num = a.num + b * a.den := by
  simp [add_num_eq]
  rw [add_int_lemma_1 (a:=a) (b:=b)]
  simp

theorem add_den_eq_one_then_den_eq {m n:ℚ} (h: (m + n).den = 1): m.den = n.den := by

  -- first, m = (m+n) - n
  have eq1 : m = (m + n) - n := by ring
  -- since (m+n).den = 1, (m+n) = (m+n).num
  have eq2 : (m + n) = (m + n).num := by
    rw [← Rat.num_div_den (m + n), h]
    simp
  -- combine those
  have eq3 : m = (m + n).num - n := by rw [eq2] at eq1; exact eq1
  -- rewrite subtraction as addition of negation
  have eq4 : m = (m + n).num + -n := by rw [Rat.sub_eq_add_neg] at eq3; exact eq3
  -- take denominators on both sides
  have den_m : m.den = ((m + n).num + -n).den := congrArg Rat.den eq4
  -- use add_int_den (for a = -n, b = (m+n).num) to see that adding an integer preserves the other denom
  have den_eq : ((m + n).num + -n).den = (-n).den := by
    rw [add_comm (a:=(m+n).num) (b:=-n)]
    exact add_int_den (a:= -n) (b:=(m + n).num)
  -- finish by noticing `(-n).den = n.den`
  calc
    m.den = ((m + n).num + -n).den := by exact den_m
      _ = (-n).den                             := by rw [den_eq]
      _ = n.den                                := by simp


theorem add_den_eq_one_then_den_dvd_num_add {m n:ℚ} (h: (m + n).den = 1) : (m.den:Int) ∣ (m.num + n.num) := by
  have h_den_eq := add_den_eq_one_then_den_eq h
  rw [← Rat.mkRat_self (a:=m), ← Rat.mkRat_self (a:=n), Rat.mkRat_add_mkRat (z₁:=m.den_nz) (z₂:=n.den_nz), h_den_eq, ← Int.add_mul] at h
  rw [Rat.mkRat_mul_right (a0:=n.den_nz)] at h
  simp [Rat.mkRat_def, Rat.normalize] at h
  rw [Nat.div_eq_iff_eq_mul_left, Nat.one_mul] at h
  rw [Int.ofNat_dvd_left]
  rw [h_den_eq]
  exact Nat.gcd_eq_right_iff_dvd.mp (id (Eq.symm h))
  refine Nat.gcd_pos_of_pos_right (m.num + n.num).natAbs ?_
  exact den_gtz
  exact Nat.gcd_dvd_right (m.num + n.num).natAbs n.den



theorem add_den_eq_one_then_add_num_eq {m n:ℚ} (h: (m + n).den = 1): (m + n).num = (m.num + n.num) / m.den := by
  have h_den_cast : (↑(m.den * n.den):Int) = m.den * n.den := by norm_num
  have h_den_eq := add_den_eq_one_then_den_eq h
  have h_den_dvd := add_den_eq_one_then_den_dvd_num_add h
  rw [add_den_eq] at h
  rw [add_num_eq]
  rw [Nat.div_eq_iff_eq_mul_left, Nat.one_mul] at h
  rw [← h]
  rw [Int.ediv_eq_iff_eq_mul_left]
  rw [h_den_cast]
  repeat rw [← h_den_eq]
  rw [← Int.mul_assoc, Int.ediv_mul_cancel, Int.add_mul]
  exact h_den_dvd
  rw [h_den_cast]
  refine Int.mul_ne_zero_iff.mpr ?_
  norm_cast
  constructor
  exact m.den_nz
  exact n.den_nz
  exact normalize.dvd_num h
  refine Nat.gcd_pos_of_pos_right (m.num * ↑n.den + n.num * ↑m.den).natAbs ?_
  simp
  exact And.intro (den_gtz (a:=m)) (den_gtz (a:=n))
  exact Nat.gcd_dvd_right (m.num * ↑n.den + n.num * ↑m.den).natAbs (m.den * n.den)





end Rat

end Rudin
