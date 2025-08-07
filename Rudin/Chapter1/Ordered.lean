import Mathlib

namespace Rudin


class Ordered (α: Type u) extends LT α, LE α where
  lt_trans : ∀ a b c : α, a < b → b < c → a < c
  lt_trichotomy_complete : ∀ a b : α,
    (a < b ∧ ¬ a = b ∧ ¬ b < a) ∨
    (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
    (¬ a < b ∧ ¬ a = b ∧ b < a)
  le_iff_lt_or_eq : ∀ {a b : α}, a ≤ b ↔ (a < b ∨ a = b)

variable {α} [Ordered α] {a b : α}

theorem lt_trichotomy {a b:α} : a < b ∨ a = b ∨ b < a := by
  have h := Ordered.lt_trichotomy_complete a b
  by_cases hab: a < b
  <;> simp [hab] at h
  <;> by_cases haeb: a = b
  <;> simp [haeb] at h
  left
  exact hab
  right
  left
  exact haeb
  right
  right
  exact h


theorem lt_trans {a b c:α} (hab: a < b) (hbc: b < c): a < c := by
  exact Ordered.lt_trans a b c hab hbc

theorem le_iff_lt_or_eq {a b:α} : a ≤ b ↔ (a < b ∨ a = b) := by
  apply Ordered.le_iff_lt_or_eq

theorem ge_iff_gt_or_eq {a b:α} : a ≥ b ↔ (a > b ∨ a = b) := by
  simp [le_iff_lt_or_eq, eq_comm]

@[simp] theorem le_refl { a : α } : a ≤ a := by
  apply le_iff_lt_or_eq.mpr
  right
  rfl

theorem le_trans {a b c : α} (hab: a ≤ b) (hbc: b ≤ c): a ≤ c := by
  apply le_iff_lt_or_eq.mpr
  by_cases hlt : a < b
  <;> simp [le_iff_lt_or_eq, hlt] at hab
  <;> by_cases hlt' : b < c
  <;> simp [le_iff_lt_or_eq, hlt'] at hbc
  left
  exact lt_trans hlt hlt'
  rw [← hbc]
  left
  exact hlt
  rw [hab]
  left
  exact hlt'
  right
  rw [← hbc]
  exact hab


@[simp] theorem lt_irrefl {a : α} : ¬ a < a := by
  have h := Ordered.lt_trichotomy_complete a a
  simp at h
  exact h

@[simp] theorem not_le_iff_lt  {a b:α} : ¬ b ≤ a ↔ a < b := by
  have htri := Ordered.lt_trichotomy_complete a b
  constructor
  <;>intro h
  . rw [le_iff_lt_or_eq] at h
    have htri := lt_trichotomy (a:=a) (b:=b)
    simp at h
    rcases htri with h1| h1| h1
    exact h1
    exfalso
    exact h.right h1.symm
    exfalso
    exact h.left h1

  . intro h1
    simp [h] at htri
    have : ¬ (a = b ∨ b < a) := by simp [htri]
    apply this
    rw [le_iff_lt_or_eq] at h1
    rcases h1 with h1 | h1
    right
    exact h1
    left
    exact h1.symm

@[simp] theorem not_lt_iff_le {a b:α} : ¬ b < a ↔ a ≤ b := by
  constructor
  <;>intro h
  have htri := lt_trichotomy (a:=a) (b:=b)
  simp [h] at htri
  rw [le_iff_lt_or_eq]
  exact htri
  contrapose! h
  simp
  exact h



@[simp] theorem gt_iff_lt {a b : α} : a > b ↔ b < a := by
  rfl

@[simp] theorem ge_iff_le {a b : α} : a ≥ b ↔ b ≤ a := by
  rfl

-- @[simp] theorem gt_iff_lt {a b:α} : a > b ↔ b < a := by
--   simp

-- @[simp] theorem ge_iff_le {a b:α} : a ≥ b ↔ b ≤ a := by
--   simp

theorem eq_then_le {α : Type u} [Ordered α] {a b : α} (h : a = b) : a ≤ b := by
  rw [Ordered.le_iff_lt_or_eq, h]
  right
  rfl

theorem lt_then_le {α : Type u} [Ordered α] {a b : α} (h : a < b) : a ≤ b := by
  rw [Ordered.le_iff_lt_or_eq]
  left
  exact h

@[simp] theorem lt_and_le_then_false (hlt: a < b) (hle: b ≤ a): False := by
  rw [← not_lt_iff_le] at hle
  exact hle hlt

@[simp] theorem lt_and_gt_then_false (hlt: a < b) (hgt: a > b): False := by
  rw [gt_iff_lt] at hgt
  exact lt_and_le_then_false hlt (lt_then_le hgt)

@[simp] theorem lt_and_eq_then_false (hlt: a < b) (heq: a = b): False :=
  lt_and_le_then_false hlt (eq_then_le heq.symm)


@[simp] theorem gt_and_eq_then_false (hgt: a > b) (heq: a = b): False := by
  rw [gt_iff_lt] at hgt
  exact lt_and_le_then_false hgt (eq_then_le heq)

theorem le_and_ne_then_lt (hle: a ≤ b) (hne: a ≠ b) : a < b := by
  rw [le_iff_lt_or_eq] at hle
  rcases hle with h|h
  exact h
  exfalso
  exact hne h


theorem lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  intro a b
  constructor
  intro h
  constructor
  apply Ordered.le_iff_lt_or_eq.mpr
  left
  exact h
  intro h1
  exact lt_and_le_then_false h h1
  intro h
  have h1 := h.left
  have h2 := h.right
  simp [Ordered.le_iff_lt_or_eq] at h2
  rw [Ordered.le_iff_lt_or_eq] at h1
  rcases h1 with h1 | h1
  exact h1
  exfalso
  exact h2.right h1.symm



theorem le_total : ∀ a b : α, a ≤ b ∨ b ≤ a := by
  intro a b
  have h := lt_trichotomy (a:=a) (b:=b)
  rcases h with h1 | h2 | h3
  left
  exact lt_then_le h1
  right
  exact eq_then_le h2.symm
  right
  exact lt_then_le h3

@[simp] theorem lt_then_ne {a b : α} (h : a < b) : a ≠ b := by
  intro heq
  rw [heq] at h
  exact lt_irrefl (a:=b) h

@[simp] theorem gt_then_ne {a b : α} (h : a > b) : a ≠ b := by
  have : b < a := by simp [h]
  have hne : b ≠ a := by simp [h]
  intro h
  rw [h] at hne
  apply hne
  rfl

theorem lt_iff_le_and_ne {a b:α} : a < b ↔ a ≤ b ∧ a ≠ b := by
  constructor
  <;>intro h
  constructor
  rw [le_iff_lt_or_eq]
  left
  exact h
  apply lt_then_ne
  exact h
  rw [le_iff_lt_or_eq] at h
  rcases h with ⟨ h1, h2⟩
  rcases h1 with h1|h1
  exact h1
  exact (h2 h1).elim

theorem lt_then_not_gt {a b:α} (h: a < b) : ¬ a > b := by
  simp
  apply lt_then_le
  exact h

theorem le_antisymm {a b:α} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rcases lt_trichotomy (a:=a) (b:=b) with h|h|h
  exfalso
  rw [← Rudin.not_le_iff_lt] at h
  exact h hba
  exact h
  exfalso
  rw [← Rudin.not_le_iff_lt] at h
  exact h hab

/- ----------------------------support mathlib ----------------------------- -/

instance (priority := default-1) : Preorder α where
  le_refl := by simp
  le_trans := by apply le_trans
  lt a b := a < b
  lt_iff_le_not_ge := by
    intro a b
    have h1:= Rudin.not_le_iff_lt (a:=a) (b:=b)
    rw [Rudin.le_iff_lt_or_eq]
    simp
    intro h
    left
    exact h

instance (priority := default-1) : PartialOrder α where
  le_antisymm := by
    intro a b hab hba
    exact le_antisymm hab hba

noncomputable instance (priority := default-1) : Min α where
  min a b := by
    classical
    exact if h : a ≤ b then a else b

noncomputable instance (priority := default-1) : Max α where
  max a b := by
    classical
    exact if a ≤ b then b else a

noncomputable instance (priority := default-1) : Ord α where
  compare a b := by
    classical
    exact if a < b then Ordering.lt else if a > b then Ordering.gt else Ordering.eq

noncomputable instance (priority := default-1) : LinearOrder α where
  le_total := Rudin.le_total
  toDecidableLE a := by
    classical
    exact fun b ↦ Classical.propDecidable (a ≤ b)
  compare_eq_compareOfLessAndEq := by
    intro a b
    simp [compare]
    simp [compareOfLessAndEq]
    rcases lt_trichotomy (a:=a) (b:=b) with h|h|h
    <;>simp [h]

end Rudin
