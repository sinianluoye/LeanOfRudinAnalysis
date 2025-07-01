import Rudin.Tactic
import Rudin.Basic
import Rudin.Chapter1.Set
import Rudin.Chapter1.Field
import Rudin.Chapter1.Ordered
import Rudin.Chapter1.OrderedField
import Rudin.Chapter1.Ratitional

namespace Rudin

structure Cut where
  carrier : Set ℚ
  ne_nempty : carrier ≠ ∅
  ne_univ : carrier ≠ Set.univ
  lt_then_in {p q:ℚ} (hp: p ∈ carrier) (hq: q < p): q ∈ carrier
  ex_gt {p:ℚ} (hp: p ∈ carrier): ∃ r ∈ carrier, p < r

theorem ext {a b : Cut} (hab : a.carrier = b.carrier) : a = b := by
  cases a
  cases b
  cases hab
  simp

theorem ne_iff_carrier_ne {a b:Cut} : a ≠ b ↔ a.carrier ≠ b.carrier := by
  constructor
  intro h h1
  apply h
  apply ext
  exact h1
  intro h h1
  rw [h1] at h
  apply h
  rfl



instance : Membership ℚ Cut where
  mem α q  := q ∈ α.carrier

namespace Cut

variable {α β γ: Cut}

theorem no_max : ¬ ∃ x ∈ α, ∀ y ∈ α, x > y := by
  rintro ⟨ x, hx⟩
  have h1 := α.ex_gt hx.left
  have h2 := hx.right
  rcases h1 with ⟨ r, hr⟩
  have h3 := hx.right r hr.left
  exact lt_and_gt_then_false hr.right h3

theorem in_lt_not_in {p q:ℚ} (hp: p ∈ α) (hq: q ∉ α) : p < q := by
  rcases lt_trichotomy (a:=p) (b:=q) with hpq|hpq|hpq
  exact hpq
  exfalso
  rw [← hpq] at hq
  exact hq hp
  have h1:= α.lt_then_in hp hpq
  exact (hq h1).elim

end Cut

instance : LT Cut where
  lt a b := a.carrier < b.carrier

instance : LE Cut where
  le a b := a.carrier ≤ b.carrier


theorem le_iff_not_gt {a b:Cut} : a ≤ b ↔ ¬ a > b := by
  simp [instLTCut, instLECut, ← Set.ssub_iff_lt, ← Set.sub_iff_le]
  constructor
  intro h1 h2
  rw [Set.ssub_def] at h2
  rcases h2 with ⟨ h3, h4⟩
  rcases h4 with ⟨ x, ⟨ hx1, hx2⟩ ⟩
  rw [Set.sub_def] at h1
  have h7:= h1 x hx1
  exact hx2 h7
  intro h
  rw [Set.sub_def]
  intro x hx
  simp [Set.ssub_def] at h
  by_cases hy: ∃ y, y ∈ b.carrier
  rcases hy with ⟨ y, hy⟩
  by_cases hy1: y ∈ a.carrier
  sorry





instance : Rudin.Ordered Cut where

  lt_trans : ∀ a b c : Cut, a < b → b < c → a < c := by
    simp [instLTCut]
    intro a b c hab hbc
    exact Set.lt_trans hab hbc


  lt_trichotomy_complete : ∀ a b : Cut,
    (a < b ∧ ¬ a = b ∧ ¬ b < a) ∨
    (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
    (¬ a < b ∧ ¬ a = b ∧ b < a) := by
    intro a b
    by_cases h: a = b
    <;>simp [h, instLTCut, ← Set.ssub_iff_lt]
    by_cases h1: a.carrier ⊂ b.carrier
    <;>simp [h1]







  le_iff_lt_or_eq : ∀ a b : Cut, a ≤ b ↔ (a < b ∨ a = b) := by
    simp [instLTCut, instLECut]
    intro a b
    have h1:= Set.le_iff_lt_or_eq (A:=a.carrier) (B:=b.carrier)
    constructor
    intro h
    have h2 := h1.mp h
    rcases h2 with h2|h2
    left
    exact h2
    right
    apply ext
    exact h2
    intro h
    rcases h with h|h
    exact h1.mpr (Or.inl h)
    have : a.carrier = b.carrier := by
      rw [h]
    exact h1.mpr (Or.inr this)







namespace Cut


end Cut

end Rudin
