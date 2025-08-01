import Mathlib
import Rudin.Chapter1.Ordered
import Rudin.Chapter1.Field
attribute [-simp] nsmul_eq_mul  Algebra.smul_mul_assoc

namespace Rudin

/-1.17-/
class OrderedField (α : Type u) extends Field α, Ordered α where
  -- axioms
  add_lt_left_cancel {a b c :α} (h: a + b < a + c) : b < c
  gtz_mul_gtz_then_gtz {a b :α} (ha: a > 0) (hb: b > 0) : a * b > 0

variable {α: Type u} [OrderedField α] {a b c : α}

theorem add_lt_left_cancel : a + b < a + c ↔ b < c := by
  constructor
  intro h
  apply OrderedField.add_lt_left_cancel h
  intro h
  rw [← zero_add (a:=b), ← zero_add (a:=c)] at h
  rw [← neg_add (a:=a)] at h
  rw [add_assoc (a:=-a)] at h
  rw [add_assoc (a:=-a)] at h
  exact OrderedField.add_lt_left_cancel h

theorem add_le_left_cancel : a + b ≤ a + c ↔ b ≤ c := by
  repeat rw [le_iff_lt_or_eq]
  rw [add_lt_left_cancel]
  simp

theorem gtz_mul_gtz_then_gtz (ha: a > 0) (hb: b > 0) : a * b > 0 := by
  apply OrderedField.gtz_mul_gtz_then_gtz ha hb


/-1.18 a-/
@[simp] theorem neg_ltz_iff_gtz : -a < 0 ↔ a > 0 := by
  constructor
  <;>intro h
  rw [←  add_neg (a:=a)]
  rw [gt_iff_lt]
  rw (occs := .pos [3]) [← add_zero (a:=a)]
  rw [add_lt_left_cancel]
  exact h
  have : -a + a > -a + 0 := by
    apply add_lt_left_cancel.mpr
    exact h
  rw [add_comm (a := -a), add_comm (a := -a)] at this
  simp at this
  exact this


@[simp] theorem neg_gtz_iff_ltz: -a > 0 ↔ a < 0:= by
  rw [← neg_ltz_iff_gtz (a:=-a)]
  simp

@[simp] theorem sub_ltz_iff_lt : a - b < 0 ↔ a < b := by
  constructor
  intro h
  apply (add_lt_left_cancel (a:=-b)).mp
  simp [add_comm, ← sub_eq_add_neg]
  exact h
  intro h
  apply (add_lt_left_cancel (a:=b)).mp
  rw [sub_eq_add_neg, ← add_assoc, add_comm, ← add_assoc, neg_add_eq_zero]
  simp
  exact h

@[simp] theorem sub_gtz_iff_gt : a - b > 0 ↔ a > b := by
  constructor
  intro h
  apply (add_lt_left_cancel (a:=-b)).mp
  simp [add_comm, ← sub_eq_add_neg]
  exact h
  intro h
  apply (add_lt_left_cancel (a:=b)).mp
  rw [add_sub_cancel']
  simp
  exact h

theorem gtz_mul_ltz_ltz (ha: a > 0) (hb: b < 0) : a * b < 0 := by
  rw [← mul_zero (a:=a)]
  rw [← add_neg (a:=b)]
  rw [mul_add]
  rw (occs := .pos [1]) [← add_zero (a:=a*b)]
  rw [add_lt_left_cancel]
  have hnb : -b > 0 := by
    simp [hb]
  exact gtz_mul_gtz_then_gtz ha hnb


theorem ltz_mul_ltz_gtz (ha: a < 0) (hb: b < 0) : a * b > 0 := by
  have : (-a) * b < 0 := by
    apply gtz_mul_ltz_ltz
    simp [ha]
    exact hb
  rw [neg_mul] at this
  -- rw [← zero_add (a:=-(a * b))] at this
  rw [← add_lt_left_cancel (a:=a * b) (b:=-(a*b)) (c:=0)] at this
  simp at this
  simp [this]


/-1.18 b-/


theorem gtz_mul_lt_gtz_mul (ha: a > 0) (hbc: b < c): a * b < a * c := by
  have : c - b > 0 := by
    apply sub_gtz_iff_gt.mpr
    exact hbc
  have h1: a * (c - b) > 0 := by
    apply gtz_mul_gtz_then_gtz ha
    exact this
  rw [mul_sub] at h1
  simp at h1
  exact h1



/-1.18 c-/
theorem neg_mul_lt_then_gt (ha: a < 0) (hbc: b < c) : a * b > a * c := by
  have : c - b > 0 := by
    apply sub_gtz_iff_gt.mpr
    exact hbc
  have ha' : -a > 0 := by
    simp
    exact ha
  have h1: -a * (c - b) > 0 := by
    apply gtz_mul_gtz_then_gtz ha'
    exact this
  rw [mul_sub] at h1
  rw [neg_mul] at h1
  rw [neg_mul] at h1
  rw [sub_eq_add_neg] at h1
  rw [neg_neg] at h1
  rw [add_comm] at h1
  rw [← sub_eq_add_neg] at h1
  rw [sub_gtz_iff_gt] at h1
  exact h1



@[simp] theorem gtz_mul_lt_left_cancel (ha: a > 0) : a * b < a * c ↔ b < c:= by
  constructor
  <;>intro h
  · rcases lt_trichotomy (a:=b) (b:=c) with hbc|hbc|hbc
    exact hbc
    rw [hbc] at h
    exact (lt_irrefl h).elim
    have : a * c < a * b := gtz_mul_lt_gtz_mul ha hbc
    rw [← gt_iff_lt] at this
    exact (lt_and_gt_then_false h this).elim
  . apply gtz_mul_lt_gtz_mul ha h

@[simp] theorem gtz_mul_lt_right_cancel (ha: a > 0) : b * a < c * a ↔ b < c := by
  rw [Rudin.mul_comm (a:=b) (b:=a)]
  rw [Rudin.mul_comm (a:=c) (b:=a)]
  exact gtz_mul_lt_left_cancel ha


@[simp] theorem gtz_mul_le_left_cancel (ha: a > 0) : a * b ≤ a * c ↔ b ≤ c:= by
  rw [Rudin.le_iff_lt_or_eq (a:=b) (b:=c), Rudin.le_iff_lt_or_eq (a:=a*b) (b:=a*c)]
  have hanz := Rudin.gt_then_ne ha
  constructor
  <;>intro h
  <;>rcases h with h|h
  simp [ha] at h
  left
  exact h
  simp [hanz] at h
  right
  exact h
  simp [ha]
  left
  exact h
  right
  simp [hanz]
  exact h

@[simp] theorem gtz_mul_le_right_cancel (ha: a > 0) : b * a ≤ c * a ↔ b ≤ c:= by
  rw [Rudin.mul_comm (a:=b) (b:=a)]
  rw [Rudin.mul_comm (a:=c) (b:=a)]
  exact gtz_mul_le_left_cancel ha

/-1.18 d-/
@[simp] theorem pow_two_gtz {a:α} (ha: a ≠ 0) : a ^ 2 > 0 := by
  by_cases h : a > 0
  rw [pow_two (a:=a)]
  exact gtz_mul_gtz_then_gtz h h
  have : a < 0 := by
    simp at h
    rw [le_iff_lt_or_eq] at h
    rcases h with h1|h1
    exact h1
    exfalso
    exact ha h1
  rw [pow_two]
  apply ltz_mul_ltz_gtz
  <;> exact this

@[simp] theorem pow_two_gez {a:α} : a ^ 2 ≥ 0 := by
  by_cases ha: a = 0
  rw [ha]
  simp
  apply lt_then_le
  exact pow_two_gtz ha

@[simp] theorem one_gtz : (1:α) > 0 := by
  have h1 : (1:α) ^ 2 > 0 := by
    exact pow_two_gtz one_nz
  rw [pow_two] at h1
  rw [one_mul] at h1
  exact h1

@[simp] theorem neg_one_ltz : -(1:α) < 0 := by
  rw [← add_lt_left_cancel (a:=1)]
  simp


@[simp] theorem neg_lt_neg_iff_gt : -a < -b ↔ a > b := by
  constructor
  <;>intro h
  rw [← add_lt_left_cancel (a:=a+b)] at h
  simp at h
  simp
  exact h
  rw [← neg_one_mul (a:=a), ← neg_one_mul (a:=b)]
  apply neg_mul_lt_then_gt
  exact neg_one_ltz
  simp [h]

@[simp] theorem ltz_mul_lt_left_cancel (ha: a < 0): a * b < a * c ↔ b > c := by
  have hnega : -a > 0 := by simp [ha]
  have h := gtz_mul_lt_left_cancel (a:=-a) (b:=-b) (c:=-c) hnega
  rw [neg_mul_neg] at h
  rw [neg_mul_neg] at h
  simp at h
  exact h

/-1.18 e-/

theorem gtz_then_inv_gtz (ha: a > 0): a⁻¹ > 0 := by
  have : a * a⁻¹ > 0 := by
    rw [mul_inv]
    simp
    simp [ha]
  rcases lt_trichotomy (a:=a⁻¹) (b:=0) with h1|h1|h1
  have hn: a * a⁻¹ < 0 := gtz_mul_ltz_ltz ha h1
  exfalso
  exact lt_and_gt_then_false hn this
  have hn: a * a⁻¹ = 0 := by
    rw [h1]
    exact mul_zero
  exfalso
  exact gt_and_eq_then_false (a:=a * a⁻¹) (b:=0) this hn
  rw [gt_iff_lt]
  exact h1

theorem ltz_then_inv_ltz (ha: a < 0) : a⁻¹ < 0 := by
  have hneg: -a > 0 := by simp [ha]
  have hneg_inv: (-a)⁻¹ > 0 := by
    exact gtz_then_inv_gtz hneg
  have hinv_neg: - a⁻¹ > 0 := by
    rw [← neg_inv (a:=a)]
    exact hneg_inv
    exact lt_then_ne ha
  rw [neg_gtz_iff_ltz (a:=a⁻¹)] at hinv_neg
  exact hinv_neg


/-some another prove-/
def SameSign (a:α) (b:α) := (a > 0 ∧ b > 0) ∨ (a < 0 ∧ b < 0)

def OppSign (a:α) (b:α) := (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)

theorem same_sign_eq_not_opp_sign_when_nz {a b:α} (hanz: a ≠ 0) (hbnz: b ≠ 0): SameSign a b = ¬ OppSign a b := by
  simp [SameSign, OppSign]
  constructor
  intro h
  rcases h with h1|h1
  constructor
  <;>intro h2
  exfalso
  exact lt_and_gt_then_false h1.left h2
  apply lt_then_le
  exact h1.right
  constructor
  intro h2
  apply lt_then_le
  exact h1.right
  intro h2
  exfalso
  exact lt_and_gt_then_false h1.left h2
  intro h
  have h1 := h.left
  have h2 := h.right
  rcases lt_trichotomy (a:=a) (b:=0) with ha|ha|ha
  right
  constructor
  exact ha
  apply le_and_ne_then_lt
  exact h1 ha
  exact hbnz
  exfalso
  exact hanz ha
  left
  constructor
  exact ha
  apply le_and_ne_then_lt
  exact h2 ha
  exact hbnz.symm




theorem mul_gtz_iff_same_sign : a * b > 0 ↔ SameSign a b := by
  simp [SameSign]
  constructor
  intro h
  rcases lt_trichotomy (a:=a) (b:=0) with ha|ha|ha
  right
  rcases lt_trichotomy (a:=b) (b:=0) with hb|hb|hb
  exact ⟨ ha, hb ⟩
  have : 0 = a * b := by
    rw [hb, mul_zero]
  exfalso
  exact lt_and_eq_then_false h this
  have : 0 > a * b := by
    rw [gt_iff_lt, mul_comm]
    exact gtz_mul_ltz_ltz hb ha
  exfalso
  exact lt_and_gt_then_false (a:=0) (b:=a*b) h this
  have : 0 = a * b := by
    rw [ha, zero_mul]
  exfalso
  exact lt_and_eq_then_false h this
  left
  rcases lt_trichotomy (a:=b) (b:=0) with hb|hb|hb
  have : 0 > a * b := by
    rw [gt_iff_lt]
    exact gtz_mul_ltz_ltz ha hb
  exfalso
  exact lt_and_gt_then_false (a:=0) (b:=a*b) h this
  have : 0 = a * b := by
    rw [hb, mul_zero]
  exfalso
  exact lt_and_eq_then_false h this
  exact ⟨ ha, hb ⟩
  intro h
  rcases h with h1|h1
  apply gtz_mul_gtz_then_gtz
  exact h1.left
  exact h1.right
  apply ltz_mul_ltz_gtz
  exact h1.left
  exact h1.right

theorem mul_ltz_iff_opp_sign : a * b < 0 ↔ OppSign a b := by
  constructor
  . intro hab
    have hanz: a ≠ 0 := by
      intro ha
      rw [ha, zero_mul] at hab
      exact lt_irrefl hab
    have hbnz: b ≠ 0 := by
      intro hb
      rw [hb, mul_zero] at hab
      exact lt_irrefl hab
    by_contra h
    rw [← same_sign_eq_not_opp_sign_when_nz hanz hbnz] at h
    rw [← mul_gtz_iff_same_sign] at h
    exact lt_and_gt_then_false hab h
  . intro h
    simp [OppSign] at h
    rcases h with h1|h1
    rw [mul_comm]
    exact gtz_mul_ltz_ltz h1.right h1.left
    exact gtz_mul_ltz_ltz h1.left h1.right


theorem same_sign_then_nz_and_nz (h: SameSign a b) : a ≠ 0 ∧ b ≠ 0 := by
  simp [SameSign] at h
  rcases h with h1|h1
  <;>constructor
  <;>simp [h1]

theorem lt_iff_inv_gt_when_same_sign (h: SameSign a b) : a < b ↔ a⁻¹ > b⁻¹ := by
  have hanz := (same_sign_then_nz_and_nz h).left
  have hbnz := (same_sign_then_nz_and_nz h).right
  have hab := mul_gtz_iff_same_sign.mpr h
  constructor
  intro h
  rw [gt_iff_lt]
  rw [← gtz_mul_lt_left_cancel (a:=a*b)]
  rw [← div_eq_mul_inv, ← div_eq_mul_inv]
  rw (occs := .pos [1]) [mul_comm]
  rw [mul_div_cancel_left, mul_div_cancel_left]
  exact h
  exact hanz
  exact hbnz
  exact hab
  intro h
  rw [gt_iff_lt] at h
  rw [← gtz_mul_lt_left_cancel (a:=a*b)] at h
  rw [← div_eq_mul_inv, ← div_eq_mul_inv] at h
  rw (occs := .pos [1]) [mul_comm] at h
  rw [mul_div_cancel_left, mul_div_cancel_left] at h
  exact h
  exact hanz
  exact hbnz
  exact hab

theorem ex_lt : ∃ t, t < a := by
  use a + -1
  rw (occs := .pos [2]) [← add_zero (a:=a)]
  rw [add_lt_left_cancel]
  simp

theorem ex_gt : ∃ t, t > a := by
  simp
  use a + 1
  rw (occs := .pos [1]) [← add_zero (a:=a)]
  rw [add_lt_left_cancel]
  simp

theorem lt_div_gtz_iff_mul_lt (h: c > 0) : a < b / c ↔ a * c < b := by
  constructor
  <;>intro h1
  rw [← gtz_mul_lt_left_cancel (a:=c)] at h1
  rw [mul_div_cancel_left'] at h1
  rw [mul_comm]
  exact h1
  exact gt_then_ne h
  exact h
  rw [← gtz_mul_lt_left_cancel (a:=c)]
  rw [mul_div_cancel_left']
  rw [mul_comm]
  exact h1
  exact gt_then_ne h
  exact h

theorem lt_div_ltz_iff_mul_gt (h: c < 0) : a < b / c ↔ a * c > b := by
  constructor
  <;>intro h1
  apply gt_iff_lt.mpr at h1
  rw [← ltz_mul_lt_left_cancel (a:=c)] at h1
  rw [mul_div_cancel_left'] at h1
  rw [mul_comm]
  exact h1
  exact lt_then_ne h
  exact h
  rw [← gt_iff_lt]
  rw [← ltz_mul_lt_left_cancel (a:=c)]
  rw [mul_div_cancel_left']
  rw [mul_comm]
  exact h1
  exact lt_then_ne h
  exact h

theorem gt_div_gtz_iff_mul_gt (h: c > 0) : a > b / c ↔ a * c > b := by
  have : c⁻¹ > 0 := gtz_then_inv_gtz h
  have h1 := gtz_mul_lt_left_cancel (a:=c⁻¹) (b:=b) (c:=a*c) this
  rw [Rudin.mul_comm] at h1
  rw [← div_eq_mul_inv] at h1
  rw [mul_comm, ← div_eq_mul_inv, mul_div_cancel] at h1
  exact h1
  apply gt_then_ne
  exact h


theorem gt_div_ltz_iff_mul_lt (h: c < 0) : a > b / c ↔ a * c < b := by
  have h1 := gt_div_gtz_iff_mul_gt (a:=a) (b:=-b) (c:=-c) (neg_gtz_iff_ltz.mpr h)
  rw [Rudin.div_eq_mul_inv] at h1
  rw [Rudin.neg_inv] at h1
  simp [Rudin.mul_neg, Rudin.neg_mul] at h1
  rw [← Rudin.div_eq_mul_inv] at h1
  rw [gt_iff_lt]
  exact h1
  apply lt_then_ne
  exact h

theorem le_div_gtz_iff_mul_le (h: c > 0) : a ≤ b / c ↔ a * c ≤ b := by
  repeat rw [Rudin.le_iff_lt_or_eq]
  simp [lt_div_gtz_iff_mul_lt h]
  have : a = b / c ↔ a * c = b := by
    rw [eq_comm]
    rw [Rudin.div_eq_iff_eq_mul]
    rw [eq_comm]
    rw [Rudin.mul_comm]
    apply Rudin.gt_then_ne h
  rw [this]

theorem ge_div_gtz_iff_mul_ge (h: c > 0) : a ≥ b / c ↔ a * c ≥ b := by
  repeat rw [Rudin.ge_iff_gt_or_eq]
  rw [gt_div_gtz_iff_mul_gt]
  rw [eq_comm, Rudin.div_eq_iff_eq_mul, eq_comm]
  rw [Rudin.mul_comm]
  apply gt_then_ne
  exact h
  exact h

theorem le_div_ltz_iff_mul_ge (h: c < 0) : a ≤ b / c ↔ a * c ≥ b := by
  repeat rw [Rudin.le_iff_lt_or_eq, Rudin.ge_iff_gt_or_eq]
  simp [lt_div_ltz_iff_mul_gt h]
  rw [eq_comm, Rudin.div_eq_iff_eq_mul, eq_comm]
  rw [Rudin.mul_comm]
  apply lt_then_ne
  exact h

theorem ge_div_ltz_iff_mul_le (h: c < 0) : a ≥ b / c ↔ a * c ≤ b := by
  repeat rw [Rudin.ge_iff_gt_or_eq, Rudin.le_iff_lt_or_eq]
  simp [gt_div_ltz_iff_mul_lt h]
  rw [eq_comm, Rudin.div_eq_iff_eq_mul, eq_comm]
  rw [Rudin.mul_comm]
  apply lt_then_ne
  exact h

theorem gtz_add_gtz_then_gtz (ha: a > 0) (hb: b > 0) : a + b > 0 := by
  simp at *
  rw [← add_lt_left_cancel (a:=a)] at hb
  simp at hb
  exact lt_trans ha hb

theorem gez_then_smul_gez {n:Nat} {a:α} (ha : a ≥ 0) : n • a ≥ 0 := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp
    simp at hn
    rw [le_iff_lt_or_eq] at hn
    rcases hn with hn|hn
    apply lt_then_le
    simp at ha
    rw [le_iff_lt_or_eq] at ha
    rcases ha with ha|ha
    exact gtz_add_gtz_then_gtz hn ha
    rw [← ha]
    simp
    rw [← ha] at hn
    simp at hn
    rw [← hn]
    simp
    exact ha




/- support mathlib -/
--  [IsStrictOrderedRing R]
-- IsOrderedCancelAddMonoid R, ZeroLEOneClass R


instance (priority := default-1) : IsOrderedAddMonoid α where
  add_le_add_left := by
    intro a b h c
    exact add_le_left_cancel.mpr h

instance (priority := default-1) : IsOrderedCancelAddMonoid α where
  le_of_add_le_add_left := by
    intro a b c h
    exact add_le_left_cancel.mp h

instance (priority := default-1) : ZeroLEOneClass α where
  zero_le_one := by
    rw [Rudin.le_iff_lt_or_eq]
    left
    simp [OfNat.ofNat]
    rw [← one_eq_field_one, ← zero_eq_field_zero]
    simp


instance (priority := default-1) : IsStrictOrderedRing α where
  mul_lt_mul_of_pos_left := fun a b c a_2 a_3 ↦ gtz_mul_lt_gtz_mul a_3 a_2
  mul_lt_mul_of_pos_right := by
    intro a b c hab hc
    exact (gtz_mul_lt_right_cancel hc).mpr hab
  exists_pair_ne := by
    use 1
    use 0
    simp


-- refer to one_add_mul_sub_le_pow, just proof for a > 0


theorem gtz_lt_then_mul_lt {a b c d:α} (ha: a > 0) (hb: a < b) (hc: c > 0) (hd: c < d):
  a * c < b * d := by
  have h1: a * c < a * d := by exact gtz_mul_lt_gtz_mul ha hd
  have h2: a * d < b * d := by
    refine (gtz_mul_lt_right_cancel ?_).mpr hb
    exact lt_trans hc hd
  exact lt_trans h1 h2

theorem gtz_le_then_mul_le {a b c d:α} (ha: a > 0) (hb: a ≤ b) (hc: c > 0) (hd: c ≤ d):
  a * c ≤ b * d := by
  have h1: a * c ≤ a * d := by exact (gtz_mul_le_left_cancel ha).mpr hd
  have h2: a * d ≤  b * d := by
    refine (gtz_mul_le_right_cancel ?_).mpr hb
    rw [le_iff_lt_or_eq] at hd
    rcases hd with hd|hd
    exact lt_trans hc hd
    rw [← hd]
    exact hc
  exact le_trans h1 h2



theorem gto_mul_gto_then_gto {a b:α} (ha: a > 1) (hb: b > 1) : a * b > 1 := by
  rw [← one_mul (a:=1)]
  apply gtz_lt_then_mul_lt
  simp
  exact ha
  simp
  exact hb

theorem gtz_pow_ge_one_add_exp_mul_base_sub_one {a : α} {n:ℕ} (ha: a > 0) :
  a ^ n ≥ 1 + n • (a - 1) := by
  induction n with
  | zero =>
    rw [Rudin.pow_zero]
    simp
  | succ n h =>
    simp
    simp at h
    rw [← Rudin.gtz_mul_le_right_cancel (a:=a) ha] at h
    simp [add_mul] at h
    rw [← Rudin.add_assoc]
    rw [Rudin.add_comm, ← Rudin.add_assoc]
    rw [Rudin.sub_eq_add_neg]
    rw [Rudin.add_assoc (a:=a)]
    simp
    have : n • (a - 1) ≤  n • (a - 1) * a := by
      rw [← Rudin.add_le_left_cancel (a:=- (n • (a - 1)))]
      simp only [neg_add]
      rw [Rudin.add_comm]
      rw [← Rudin.sub_eq_add_neg]
      rw (occs := .pos [2]) [← mul_one (a:=n • (a - 1))]
      rw [← Rudin.mul_sub (a:=n • (a - 1)) (b:=a) (c:=1)]
      rw [smul_mul_assoc]
      have : (a-1) * (a-1) = (a-1) ^ 2 := by
        simp
      rw [this]
      apply gez_then_smul_gez
      exact Rudin.pow_two_gez
    have h1:a + n • (a - 1) ≤ a + n • (a - 1) * a := by
      rw [add_le_left_cancel]
      exact this
    exact Rudin.le_trans h1 h

theorem gtz_then_powNat_gtz {x:α} {n:Nat} (hx: x > 0) : x ^ n > 0 := by
  induction n with
  | zero => simp
  | succ n hi =>
    simp
    exact OrderedField.gtz_mul_gtz_then_gtz hi hx

theorem gto_then_natPow_geo {x:α} {n:Nat} (hx: x > 1) : x ^ n ≥ 1 := by
  induction n with
  | zero => simp
  | succ n hi =>
    simp
    rw [← one_mul (a:=1)]
    apply gtz_le_then_mul_le
    simp
    exact hi
    simp
    apply lt_then_le
    exact hx


theorem gto_then_natPow_gto_gto {x:α} {n:Nat} (hx: x > 1) (hn: n > 0): x ^ n > 1 := by
  have : n = n - 1 + 1 := by exact (Nat.sub_eq_iff_eq_add hn).mp rfl
  rw [this]
  simp
  have h1 := gto_then_natPow_geo (n:=n-1) hx
  rw [ge_iff_le, le_iff_lt_or_eq] at h1
  rcases h1 with h1|h1
  apply gto_mul_gto_then_gto
  exact h1
  exact hx
  rw [← h1]
  simp
  exact hx

theorem gto_then_natPow_gto_gt_base {x:α} {n:Nat} (hx: x > 1) (hn: n > 1) : x^n > x := by
  have : n = n - 1 + 1 := by
    refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
    exact Nat.one_le_of_lt hn
  rw [this]
  simp
  rw (occs := .pos [1]) [← Rudin.one_mul (a:=x)]
  rw [Rudin.gtz_mul_lt_right_cancel]
  apply gto_then_natPow_gto_gto
  exact hx
  linarith
  have h1: (1:α) > 0 := by simp
  exact lt_trans h1 hx

theorem gtz_lt_gtz_then_powNat_le {x y:α} {n:Nat} (hx: 0<x) (hy: x < y) : x^n ≤ y^n := by
  induction n with
  | zero => simp
  | succ n hi =>
    simp
    apply gtz_le_then_mul_le
    exact gtz_then_powNat_gtz hx
    exact hi
    exact hx
    exact lt_then_le hy

theorem gtz_lt_gtz_then_powNat_gtz_lt {x y : α} {n : Nat} (hx : 0 < x) (hy : x < y)
    (hn : n > 0) : x ^ n < y ^ n := by
  induction n with
  | zero =>
    cases hn
  | succ n hi =>
    by_cases hn1 : n > 0
    simp
    refine gtz_lt_then_mul_lt ?_ ?_ hx hy
    exact gtz_then_powNat_gtz hx
    exact hi hn1
    simp at hn1
    rw [hn1]
    simp
    exact hy


end Rudin
