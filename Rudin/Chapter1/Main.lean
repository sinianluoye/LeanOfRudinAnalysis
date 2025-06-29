import Rudin.Basic
import Rudin.Tactic
import Rudin.Chapter1.Ordered
import Rudin.Chapter1.Field
import Rudin.Chapter1.OrderedField
import Rudin.Chapter1.Set




/-1.5-/


/-1.7-/

namespace Rudin

universe u
variable {α : Type u} [Ordered α]

def UpperBound (E: Set α) (b : α) := ∀ x ∈ E, x ≤ b

def BoundAbove (E: Set α) := ∃ b, UpperBound E b

def LowerBound (E: Set α) (b : α) := ∀ x ∈ E, b ≤ x

def BoundBelow (E: Set α) := ∃ b, LowerBound E b

/-1.8-/

def Sup (E: Set α) (a : α) := UpperBound E a ∧ ∀ b, b < a → ¬ UpperBound E b

def Inf (E: Set α) (a : α) := LowerBound E a ∧ ∀ b, b > a → ¬ LowerBound E b

/-1.9-/
-- see Examples.lean

/-1.10-/
/-
An ordered set S is said to have the least-upper-bound property if
the following is true:
 If E ⊂ S, Eis not empty, and E is bounded above, then supE exists in S.
-/
class LeastUpperBoundProperty (α: Type u) extends Ordered α where
  subset_sup_exist : ∀ (E : Set α), BoundAbove E → ∃ a, Sup E a

class GreatestLowerBoundProperty (α: Type u) extends Ordered α where
  subset_inf_exist : ∀ (E : Set α), BoundBelow E → ∃ a, Inf E a

/-1.11-/
/-
Suppose S is an ordered set with the least-upper-bound property, B ⊂ S,
 B is not empty, and B is bounded below. Let L be the set of all lower bounds of B. Then
 α = sup L
 exists in S and α = inf B.
 In particular, inf B exists in S.
-/
theorem sup_only_one
  {α : Type u}[Ordered α]
  {E : Set α}
  {m n: α}
  (hm: Sup E m)
  (hn: Sup E n) : m = n := by
  simp [Sup, UpperBound] at hm hn
  have hm1 := hm.1
  have hn1 := hn.1
  have hm2 := hm.2
  have hn2 := hn.2
  by_contra hmn
  rcases lt_trichotomy (a:=m) (b:=n) with hlt | heq | hgt
  have := hn2 m hlt
  rcases this with ⟨ x, hx1, hx2 ⟩
  exact lt_and_le_then_false hx2 (hm1 x hx1)
  exact hmn heq
  have := hm2 n hgt
  rcases this with ⟨ y, hy1, hy2 ⟩
  exact lt_and_le_then_false hy2 (hn1 y hy1)


theorem rudin_1_11
    {α : Type u} [LeastUpperBoundProperty α] {B : Set α}
    (hB_nonempty : ∃ b, b ∈ B)
    (hB_bound_below : BoundBelow B) :
    ∃ a : α, Sup {x | LowerBound B x} a ∧ Inf B a := by
  rcases hB_nonempty with ⟨ b, hb ⟩
  rcases hB_bound_below with ⟨ l, hl ⟩
  let L := {x | LowerBound B x}
  have : L = {x | LowerBound B x} := by rfl
  rw [← this]
  simp [Sup, LowerBound] at this
  have hB_upper_bound_L : ∀ x ∈ B, UpperBound L x := by
    intro x hx
    simp [Sup, UpperBound]
    intro y
    intro hy
    rw [this] at hy
    exact hy x hx

  have hB_bound_above_L : BoundAbove L := by
    have := hB_upper_bound_L b hb
    simp [Sup] at this
    use b

  have hL_have_sup : ∃ s, Sup L s := by
    apply LeastUpperBoundProperty.subset_sup_exist
    exact hB_bound_above_L

  rcases hL_have_sup with ⟨ s, hs ⟩
  use s
  constructor
  exact hs
  simp [Sup] at hs
  have hs1 := hs.1
  simp [UpperBound] at hs1

  constructor
  have hsinL: s ∈ L := by
    intro x hx
    by_cases hle : s ≤ x
    exact hle
    have hlt : x < s := by
      rw [← not_le_iff_lt]
      exact hle
    have hupper  : UpperBound L x := hB_upper_bound_L x hx
    have hnotUB  : ¬ UpperBound L x := hs.2 x hlt
    exact (hnotUB hupper).elim
  intro y hy

  apply Set.mem_setOf.mp hsinL
  exact hy

  intro y hy
  have hynotinl : y ∉ L := by
    by_contra hyinl
    apply hs1 at hyinl
    simp at hy
    exact lt_and_le_then_false hy hyinl
  intro hlby
  have hyinl : y ∈ L := by
    simp [L]
    exact hlby
  exact hynotinl hyinl

end Rudin

/-
1.12 to 1.18 see `Field.lean`
-/

/-1.13 b-/
