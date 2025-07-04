
import Rudin.Tactic
import Rudin.Chapter1.Ordered
import Rudin.Chapter1.Field


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

/-1.18 d-/
@[simp] theorem pow_two_gtz {a:α} (ha: a ≠ 0) : a ^ 2 > 0 := by
  by_cases h : a > 0
  rw [pow_two]
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

theorem gtz_then_inv_gtz (ha: a > 0): (1/a) > 0 := by
  have : a * (1/a) > 0 := by
    rw [mul_inv]
    simp
    simp [ha]
  rcases lt_trichotomy (a:=1/a) (b:=0) with h1|h1|h1
  have hn: a * (1/a) < 0 := gtz_mul_ltz_ltz ha h1
  exfalso
  exact lt_and_gt_then_false hn this
  have hn: a * (1/a) = 0 := by
    rw [h1]
    exact mul_zero
  exfalso
  exact gt_and_eq_then_false (a:=a * (1/a)) (b:=0) this hn
  rw [gt_iff_lt]
  exact h1

theorem ltz_then_inv_ltz (ha: a < 0) : (1/a) < 0 := by
  have hneg: -a > 0 := by simp [ha]
  have hneg_inv: 1/(-a) > 0 := by
    exact gtz_then_inv_gtz hneg
  have hinv_neg: - (1 / a) > 0 := by
    rw [← neg_inv (a:=a)]
    exact hneg_inv
    exact lt_then_ne ha
  rw [neg_gtz_iff_ltz (a:=1/a)] at hinv_neg
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

theorem lt_iff_inv_gt_when_same_sign (h: SameSign a b) : a < b ↔ (1/a) > (1/b) := by
  have hanz := (same_sign_then_nz_and_nz h).left
  have hbnz := (same_sign_then_nz_and_nz h).right
  have hab := mul_gtz_iff_same_sign.mpr h
  constructor
  intro h
  rw [gt_iff_lt]
  rw [← gtz_mul_lt_left_cancel (a:=a*b)]
  rw [← div_eq_mul_inv, ← div_eq_mul_inv]
  rw (occs := .pos [1]) [mul_comm]
  rw [mul_div_cancel, mul_div_cancel]
  exact h
  exact hanz
  exact hbnz
  exact hab
  intro h
  rw [gt_iff_lt] at h
  rw [← gtz_mul_lt_left_cancel (a:=a*b)] at h
  rw [← div_eq_mul_inv, ← div_eq_mul_inv] at h
  rw (occs := .pos [1]) [mul_comm] at h
  rw [mul_div_cancel, mul_div_cancel] at h
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
  rw [mul_div_cancel'] at h1
  rw [mul_comm]
  exact h1
  exact gt_then_ne h
  exact h
  rw [← gtz_mul_lt_left_cancel (a:=c)]
  rw [mul_div_cancel']
  rw [mul_comm]
  exact h1
  exact gt_then_ne h
  exact h

theorem lt_div_ltz_iff_mul_gt (h: c < 0) : a < b / c ↔ a * c > b := by
  constructor
  <;>intro h1
  apply gt_iff_lt.mpr at h1
  rw [← ltz_mul_lt_left_cancel (a:=c)] at h1
  rw [mul_div_cancel'] at h1
  rw [mul_comm]
  exact h1
  exact lt_then_ne h
  exact h
  rw [← gt_iff_lt]
  rw [← ltz_mul_lt_left_cancel (a:=c)]
  rw [mul_div_cancel']
  rw [mul_comm]
  exact h1
  exact lt_then_ne h
  exact h


end Rudin
