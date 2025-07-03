import Rudin.Tactic
import Rudin.Basic
import Rudin.Chapter1.Set
import Rudin.Chapter1.Field
import Rudin.Chapter1.Ordered
import Rudin.Chapter1.OrderedField
import Rudin.Chapter1.Ratitional
import Rudin.Chapter1.Bound

namespace Rudin

namespace Real

structure Cut where
  carrier : Set ℚ
  ne_nempty : carrier ≠ ∅
  ne_univ : carrier ≠ Set.univ
  lt_then_in {p q:ℚ} (hp: p ∈ carrier) (hq: q < p): q ∈ carrier
  ex_gt {p:ℚ} (hp: p ∈ carrier): ∃ r ∈ carrier, p < r


instance : Membership ℚ Cut where
  mem α q  := q ∈ α.carrier

namespace Cut

variable {α β γ: Cut}

theorem ext {a b : Cut} (hab : a.carrier = b.carrier) : a = b := by
  cases a
  cases b
  cases hab
  simp


theorem mem_iff_mem_carrier {x:ℚ} {a:Cut} : x ∈ a ↔ x ∈ a.carrier := by
  simp [instMembershipℚCut]

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

instance : LT Cut where
  lt a b := a.carrier < b.carrier

instance : LE Cut where
  le a b := a.carrier ≤ b.carrier



theorem lt_then_ex_not_in_carrier {a b:Cut} (h: a < b): ∃ x ∈ b, x ∉ a := by
  simp [instLT, ← Set.ssub_iff_lt, Set.ssub_def] at h
  rcases h with ⟨h1, x, hx1, hx2⟩
  use x
  simp [instMembershipℚCut]
  constructor
  exact hx1
  exact hx2





theorem le_iff_not_gt {a b:Cut} : a ≤ b ↔ ¬ a > b := by
  simp [Cut.instLT, Cut.instLE, ← Set.ssub_iff_lt, ← Set.sub_iff_le]
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
  intro x hxa
  by_contra hxb
  apply h
  rw [Set.ssub_def]
  constructor
  intro y hyb
  have hxyb := in_lt_not_in hyb hxb
  exact a.lt_then_in hxa hxyb
  use x


instance : Ordered Cut where

  lt_trans : ∀ a b c : Cut, a < b → b < c → a < c := by
    simp [Cut.instLT]
    intro a b c hab hbc
    exact Set.lt_trans hab hbc


  lt_trichotomy_complete : ∀ a b : Cut,
    (a < b ∧ ¬ a = b ∧ ¬ b < a) ∨
    (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
    (¬ a < b ∧ ¬ a = b ∧ b < a) := by
    intro a b
    by_cases h: a = b
    <;>simp [h, Cut.instLT, ← Set.ssub_iff_lt]
    by_cases h1: a.carrier ⊂ b.carrier
    <;>simp [h1]
    simp [Cut.ne_iff_carrier_ne] at h
    rw [Set.ssub_iff_lt] at h1
    simp only [Set.instLT_rudin] at h1
    have h2 : ¬(a ≤ b ∧ a.carrier ≠ b.carrier) := by
      simp only [Cut.instLE]
      exact h1
    rw [Cut.le_iff_not_gt] at h2
    rw [Classical.not_and_iff_not_or_not] at h2
    simp [Cut.instLT] at h2
    rcases h2 with h2|h2
    exact h2
    exact (h h2).elim

  le_iff_lt_or_eq : ∀ a b : Cut, a ≤ b ↔ (a < b ∨ a = b) := by
    simp [Cut.instLT, Cut.instLE]
    intro a b
    have h1:= Set.le_iff_lt_or_eq (A:=a.carrier) (B:=b.carrier)
    constructor
    intro h
    have h2 := h1.mp h
    rcases h2 with h2|h2
    left
    exact h2
    right
    apply Cut.ext
    exact h2
    intro h
    rcases h with h|h
    exact h1.mpr (Or.inl h)
    have : a.carrier = b.carrier := by
      rw [h]
    exact h1.mpr (Or.inr this)

theorem le_def {a b:Cut} : a ≤ b ↔ (∀ x, x ∈ a.carrier → x ∈ b.carrier) := by
  simp [Real.instMembershipℚCut, instLE, ← Set.sub_iff_le, Set.sub_def]


theorem lt_def {a b:Cut} : a < b ↔ (∀ x, x ∈ a.carrier → x ∈ b.carrier) ∧ ∃ x ∈ b.carrier, x ∉ a.carrier:= by
  simp [lt_iff_le_not_le, le_def]



end Cut


end Real

abbrev Real := Real.Cut

abbrev ℝ := Real

namespace Real

instance : LeastUpperBoundProperty ℝ where
  subset_sup_exist : ∀ (E : Set ℝ), E ≠ ∅ ∧ BoundAbove E → ∃ a, Sup E a := by
    intro A hA
    simp only [BoundAbove] at hA
    rcases hA with ⟨ hA1, ⟨ β  ,  hA2 ⟩⟩
    -- p ∈ γ if and only if p ∈ α for some α ∈ A
    let carr: Set ℚ := {p : ℚ | ∃ α : ℝ, α ∈ A ∧ p ∈ α}
    rw [UpperBound] at hA2

    have carr_ne_empty : carr ≠ ∅ := by
      rw [Set.not_empty_iff_ex_mem]
      rw [Set.not_empty_iff_ex_mem] at hA1
      obtain ⟨ α , hα ⟩ := hA1
      simp [carr]
      have :  ∃ x, x ∈ α := Set.not_empty_iff_ex_mem.mp α.ne_nempty
      obtain ⟨ x, hx ⟩ := this
      use x
      use α

    have carr_ne_univ : carr ≠ Set.univ := by
      intro h
      have h1:= β.ne_univ
      have h2: β.carrier = Set.univ := by
        simp [Set.eq_univ_iff_forall]
        intro x
        simp [Set.eq_univ_iff_forall, carr] at h
        have h3:= (h x)
        rcases h3 with ⟨ α, ha⟩
        have h4:= hA2 α ha.left
        simp [Real.Cut.le_def] at h4
        exact h4 x ha.right
      exact h1 h2

    have carr_lt_then_in {p q:ℚ} (hp: p ∈ carr) (hq: q < p): q ∈ carr := by
      simp [carr] at hp
      rcases hp with ⟨ α , ha1, ha2⟩
      simp [carr]
      use α
      constructor
      exact ha1
      exact α.lt_then_in ha2 hq

    have carr_ex_gt {p:ℚ} (hp: p ∈ carr): ∃ r ∈ carr, p < r := by
      simp [carr] at hp
      rcases hp with ⟨ α , ha1, ha2⟩
      have h1 := α.ex_gt ha2
      rcases h1 with ⟨ r, hr1, hr2⟩
      use r
      constructor
      simp [carr]
      use α
      constructor
      exact ha1
      exact hr1
      exact hr2

    let γ:ℝ := ⟨carr, carr_ne_empty, carr_ne_univ,  carr_lt_then_in, carr_ex_gt⟩
    use γ
    by_cases h: ∃ δ, δ < γ ∧ Sup A δ
    rcases h with ⟨ δ, h1, h2 ⟩
    have h3:= Real.Cut.lt_then_ex_not_in_carrier h1
    rcases h3 with ⟨ s, hs1, hs2⟩
    simp [Real.instMembershipℚCut] at hs1
    rw [Set.mem_setOf] at hs1
    simp [Sup, UpperBound] at h2
    rcases h2 with ⟨ h3, h4⟩
    rcases hs1 with ⟨ α , ha1, ha2⟩
    have h5 := h3 α ha1
    have h6 : s ∈ δ := by
      simp [Real.Cut.le_def] at h5
      rw [Real.Cut.mem_iff_mem_carrier] at ha2
      have := h5 s ha2
      rw [← Real.Cut.mem_iff_mem_carrier] at this
      exact this
    exfalso
    exact hs2 h6
    simp [Sup] at *
    constructor
    simp [UpperBound]
    intro α hα
    simp [Real.Cut.le_def]
    intro s hs
    rw [Set.mem_setOf]
    use α
    constructor
    exact hα
    exact hs
    intro δ h1 h2
    simp only [Real.Cut.lt_def] at h1
    rcases h1 with ⟨ h3, h4⟩
    rcases h4 with ⟨ s, hs1, hs2⟩
    rw [Set.mem_setOf] at hs1
    rcases hs1 with ⟨ α , hα1, hα2⟩
    simp [UpperBound] at h2
    have h5:= h2 α hα1
    simp [Real.Cut.le_def] at h5
    have h6 := h5 s hα2
    exact hs2 h6

def AddDef (α:ℝ) (β:ℝ) := {p | ∃ r ∈ α, ∃ s ∈ β, p = r + s}

-- structure Cut where
--   carrier : Set ℚ
--   ne_nempty : carrier ≠ ∅
--   ne_univ : carrier ≠ Set.univ
--   lt_then_in {p q:ℚ} (hp: p ∈ carrier) (hq: q < p): q ∈ carrier
--   ex_gt {p:ℚ} (hp: p ∈ carrier): ∃ r ∈ carrier, p < r

theorem add_def_ne_empty {α β:ℝ} : AddDef α β ≠ ∅ := by
  simp [AddDef, Set.not_empty_iff_ex_mem]
  have h1:= α.ne_nempty
  have h2:= β.ne_nempty
  simp [Set.not_empty_iff_ex_mem] at h1 h2
  rcases h1 with ⟨ r, hr⟩
  rcases h2 with ⟨ s, hs⟩
  use r + s
  use r
  constructor
  exact hr
  use s
  constructor
  exact hs
  rfl

theorem add_def_ne_univ {α β:ℝ} : AddDef α β ≠ Set.univ := by
  simp [AddDef, Set.ne_univ_iff_ex_not_in]
  have h1 := α.ne_univ
  have h2 := β.ne_univ
  simp [Set.ne_univ_iff_ex_not_in] at h1 h2
  rcases h1 with ⟨ r, hr⟩
  rcases h2 with ⟨ s, hs⟩
  use r + s
  intro a ha
  intro b hb
  have hra : r > a := Cut.in_lt_not_in ha hr
  have hsb : s > b := Cut.in_lt_not_in hb hs
  apply Rat.ne_of_gt
  apply Rat.add_lt_add
  exact hra
  exact hsb




instance : Add ℝ where
  add a b := sorry

end Real


end Rudin
