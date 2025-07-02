import Rudin.Tactic
import Mathlib.Data.Set.Defs
import Rudin.Chapter1.Ordered

namespace Set

universe u
variable {α: Type u}

@[simp] theorem in_univ : x ∈ Set.univ := by trivial

@[simp] theorem not_in_emptyset {x:α}: x ∉ (∅:Set α) := by
  intro h
  trivial

theorem ne_iff_ex_not_in (A B:Set α) : A ≠ B ↔ (∃ x ∈ A, x ∉ B) ∨ (∃ x ∈ B, x ∉ A):= by
  constructor
  intro h
  by_contra hx
  simp at hx
  simp at h
  apply h
  apply ext
  intro x
  constructor
  intro hxa
  exact hx.left x hxa
  intro hxb
  exact hx.right x hxb
  intro h
  intro hab
  rcases h with h|h
  <;>rw [hab] at h
  <;>rcases h with ⟨_, h⟩
  <;>exact h.right h.left

theorem ne_univ_iff_ex_not_in (S: Set α) : S ≠ Set.univ ↔ ∃ x, x ∉ S := by
  simp [ne_iff_ex_not_in, in_univ]


/-
LE has defined at Mathlib
instance : LE (Set α) where
  le a b := a ⊆ b
-/

/-
define LT first to keep same format (LE->Subset, LT->SSubset)
-/
instance : LT (Set α) where
  lt a b := a ≤ b ∧ a ≠ b

instance : HasSSubset (Set α) where
  SSubset a b := a < b

theorem ssub_iff_sub_and_ne  (A B:Set α) : A ⊂ B ↔ A ⊆ B ∧ A ≠ B := by rfl

theorem sub_def (A B:Set α): A ⊆ B ↔ ∀ a:α, a ∈ A → a ∈ B := by rfl

theorem ssub_def (A B:Set α): A ⊂ B ↔ (∀ a ∈ A, a ∈ B) ∧ (∃ b ∈ B, b ∉ A) := by
  simp [ssub_iff_sub_and_ne, sub_def, ne_iff_ex_not_in]
  rintro h a ha hb
  have h:= h a
  exfalso
  exact hb (h ha)

theorem sub_iff_le (A B:Set α): A ⊆ B ↔ A ≤ B := by rfl

theorem ssub_iff_lt (A B:Set α): A ⊂ B ↔ A < B := by rfl

@[simp] theorem ssub_irrefl (A:Set α): ¬ A ⊂ A := by simp [ssub_def]

@[simp] theorem sub_refl (A:Set α): A ⊆ A := by simp [sub_def]

@[simp] theorem ssub_asymm  (A B:Set α) (hab: A ⊂ B): ¬ B ⊂ A := by
  simp [ssub_def] at *
  intro h x ha
  exact hab.left x ha

@[simp] theorem lt_trans {A B C : Set α} (hab: A < B) (hbc: B < C): A < C := by
    simp [← Set.ssub_iff_lt, ssub_def] at *
    constructor
    intro a
    intro ha
    exact hbc.left a (hab.left a ha)
    rcases hbc with ⟨ hy1, hy2⟩
    rcases hy2 with ⟨ a, ha⟩
    use a
    constructor
    exact ha.left
    intro ha2
    have ha3 := hab.left a ha2
    exact ha.right ha3

theorem le_iff_lt_or_eq {A B : Set α} : A ≤ B ↔ (A < B ∨ A = B) := by
    simp [LT.lt]
    by_cases h: A = B
    <;>simp [h]
    simp [Set.instLE]
    rw [Set.Subset]
    intro x
    intro hx
    exact hx

@[simp] theorem mem_setOf_eq {x : α} {p : α → Prop} : (x ∈ {y | p y}) = p x := rfl

theorem eq_mem_setOf (p : α → Prop) : p = (· ∈ {a | p a}) := rfl

theorem mem_setOf {a : α} {p : α → Prop} : a ∈ { x | p x } ↔ p a := Iff.rfl

@[simp] theorem setOf_mem_eq {s : Set α} : { x | x ∈ s } = s := rfl

theorem not_empty_iff_ex_mem {A : Set α} : A ≠ ∅ ↔ ∃ x, x ∈ A := by
  simp [ne_iff_ex_not_in]

@[simp] theorem univ_subset_iff {s : Set α} : univ ⊆ s ↔ s = univ := by
  simp [Set.sub_def, univ]
  constructor
  intro h
  apply ext
  intro x
  simp
  exact h x
  intro h
  intro x
  simp [h]




theorem eq_univ_iff_forall {s : Set α} : s = univ ↔ ∀ x, x ∈ s :=
  univ_subset_iff.symm.trans <| forall_congr' fun _ => imp_iff_right trivial

end Set
