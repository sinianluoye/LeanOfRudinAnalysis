import Mathlib
import Rudin.Command
import Rudin.Basic
import Rudin.Chapter1.Set
import Rudin.Chapter1.Field
import Rudin.Chapter1.Ordered
import Rudin.Chapter1.OrderedField
import Rudin.Chapter1.Rational
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

@[simp] theorem mem_iff_mem_carrier {x:ℚ} {a:Cut} : x ∈ a ↔ x ∈ a.carrier := by
  simp [Rudin.Real.instMembershipRatCut]

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

theorem ex_mem : ∃ x:ℚ, x ∈ α := by
  have h:= α.ne_nempty
  rw [Set.not_empty_iff_ex_mem] at h
  exact h

theorem ex_not_mem : ∃ x:ℚ, x ∉ α := by
  have h:= α.ne_univ
  rw [Set.ne_univ_iff_ex_not_in] at h
  exact h

theorem mem_then_ex_add_mem_and_add_delta_not_mem {r d:ℚ} (hr: r ∈ α) (hd: d > 0) :
  ∃ n:ℕ, r + n * d ∈ α ∧ r + (n+1) * d ∉ α := by
  by_contra h
  simp at h
  have h2: ∀ (n:ℕ), r + n * d ∈ α := by
    intro n
    induction n with
    | zero =>
      simp
      exact hr
    | succ n ih =>
      rw [Nat.cast_succ]
      apply h
      exact ih

  rcases ex_not_mem (α := α) with ⟨ s, hs⟩
  rcases exists_nat_gt ((s-r)/d) with ⟨ n, hn⟩
  have h4 : r + ((s - r) / d) * d < r + ↑n * d := by
    rw [mul_comm]
    rw (occs := .pos [2])[mul_comm]
    rw [add_lt_left_cancel, gtz_mul_lt_left_cancel hd]
    exact hn
  have h3 := h2 n
  have h5 := α.lt_then_in h3 h4
  simp [hd] at h5
  exact hs h5

theorem ex_mem_and_add_not_mem {d:ℚ}(hd: d > 0) : ∃ x, x ∈ α ∧ x + d ∉ α := by
  rcases ex_mem (α := α) with ⟨r, hr⟩
  rcases mem_then_ex_add_mem_and_add_delta_not_mem hr hd with ⟨n, hn⟩
  use r + ↑n * d
  simp [add_mul, ← add_assoc] at hn
  exact hn

instance : LT Cut where
  lt a b := a.carrier < b.carrier

instance : LE Cut where
  le a b := a.carrier ≤ b.carrier

theorem lt_then_ex_not_in_carrier {a b:Cut} (h: a < b): ∃ x ∈ b, x ∉ a := by
  simp [instLT, ← Set.ssub_iff_lt, Set.ssub_def] at h
  rcases h with ⟨h1, x, hx1, hx2⟩
  use x
  simp [Rudin.Real.instMembershipRatCut]
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
    simp at h1
    have h2 : ¬(a ≤ b ∧ a.carrier ≠ b.carrier) := by
      simp [instLE]
      intro h3
      exfalso
      simp [← Set.le_iff_subset, Set.le_iff_lt_or_eq] at h3
      rcases h3 with h3|h3
      <;>contradiction

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
  simp [Rudin.Real.instMembershipRatCut, instLE, ← Set.sub_iff_le, Set.sub_def]

theorem lt_def {a b:Cut} : a < b ↔ (∀ x, x ∈ a.carrier → x ∈ b.carrier) ∧ ∃ x ∈ b.carrier, x ∉ a.carrier:= by
  simp [Rudin.Real.instMembershipRatCut, instLT, ← Set.ssub_iff_lt, Set.ssub_def]

theorem ex_delta_between_lt_diff
  (h: α < β) :
  ∃ d:ℚ, d > 0 ∧ (∀ p, p ∈ β ∧ p ∉ α → ∀ q, q ∈ β ∧ q ∉ α → p - q < d) := by
  rcases Cut.ex_not_mem (α := β) with ⟨ s, hs⟩
  rcases Cut.ex_mem (α := α) with ⟨ r, hr ⟩
  use s - r
  constructor
  simp [lt_def] at h
  have hrb := h.left r (mem_iff_mem_carrier.mp hr)
  have hrs := β.in_lt_not_in hrb hs
  simp [hrs]
  intro p hp
  intro q hq
  have hqr := α.in_lt_not_in hr hq.right
  have hps := β.in_lt_not_in hp.left hs
  have : r + p < q + s := by linarith
  linarith

end Cut

end Real

abbrev Real := Real.Cut

abbrev RR := Real /-use RR instead of ℝ to avoid confilict with mathlib-/

namespace Real

instance : LeastUpperBoundProperty RR where

  subset_sup_exist : ∀ (E : Set RR), E ≠ ∅ ∧ BoundAbove E → ∃ a, Sup E a := by
    intro A hA
    simp only [BoundAbove] at hA
    rcases hA with ⟨ hA1, ⟨ β  ,  hA2 ⟩⟩
    -- p ∈ γ if and only if p ∈ α for some α ∈ A
    let carr: Set ℚ := {p : ℚ | ∃ α : RR, α ∈ A ∧ p ∈ α}
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
      constructor
      <;>assumption

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
      assumption

    let γ:RR := ⟨carr, carr_ne_empty, carr_ne_univ,  carr_lt_then_in, carr_ex_gt⟩
    use γ
    by_cases h: ∃ δ, δ < γ ∧ Sup A δ
    rcases h with ⟨ δ, h1, h2 ⟩
    have h3:= Real.Cut.lt_then_ex_not_in_carrier h1
    rcases h3 with ⟨ s, hs1, hs2⟩
    simp [Real.instMembershipRatCut] at hs1
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

def AddDef (α:RR) (β:RR) := {p | ∃ r ∈ α, ∃ s ∈ β, p = r + s}

theorem add_def_ne_empty {α β:RR} : AddDef α β ≠ ∅ := by
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

theorem add_def_ne_univ {α β:RR} : AddDef α β ≠ Set.univ := by
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

theorem add_def_lt_then_in {α β:RR} {p q:ℚ} (hp: p ∈ AddDef α β) (hq: q < p): q ∈ (AddDef α β) := by
  simp [AddDef] at *
  rcases hp with ⟨ r, hr, s ,hs, hrs⟩
  rw [hrs] at hq
  have hqr: q - r < s := by
    rw [← add_lt_left_cancel (a:=r)]
    simp
    exact hq
  have hqr2 := β.lt_then_in (q:=q-r) hs hqr
  use r
  constructor
  exact hr
  use q - r
  constructor
  exact hqr2
  simp

theorem add_def_ex_gt {α β:RR} {p:ℚ} (hp: p ∈ AddDef α β): ∃ r ∈ AddDef α β, p < r := by
  simp [AddDef] at *
  rcases hp with ⟨ r, hr, s ,hs, hrs⟩
  rcases α.ex_gt hr with ⟨ a, ha1, ha2⟩
  rcases β.ex_gt hs with ⟨ b, hb1, hb2⟩
  use a + b
  constructor
  use a
  constructor
  exact ha1
  use b
  rw [hrs]
  apply Rat.add_lt_add
  exact ha2
  exact hb2

instance : Add RR where
  add a b := ⟨ AddDef a b, add_def_ne_empty, add_def_ne_univ, add_def_lt_then_in, add_def_ex_gt⟩

theorem mem_add_def_iff {α β:RR} {x : ℚ}: x ∈ (α + β) ↔ ∃ r ∈ α, ∃ s ∈ β, x = r + s := by
  simp [Rudin.Real.instMembershipRatCut, HAdd.hAdd, instAddRR, AddDef]

def OfRatDef (n:ℚ) := {x:ℚ | x < n}


-- structure Cut where
--   carrier : Set ℚ
--   ne_nempty : carrier ≠ ∅
--   ne_univ : carrier ≠ Set.univ
--   lt_then_in {p q:ℚ} (hp: p ∈ carrier) (hq: q < p): q ∈ carrier
--   ex_gt {p:ℚ} (hp: p ∈ carrier): ∃ r ∈ carrier, p < r

theorem ofRat_def_ne_empty {n:ℚ} : OfRatDef n ≠ ∅ := by
  simp [OfRatDef, Set.not_empty_iff_ex_mem]
  use n-1
  rw [← sub_ltz_iff_lt]
  rw [sub_eq_add_neg (b:=1)]
  rw [add_sub_cancel]
  simp

theorem ofRat_def_ne_univ {n:ℚ} : OfRatDef n ≠ Set.univ := by
  simp [OfRatDef, Set.ne_univ_iff_ex_not_in]
  use n

theorem OfRat_lt_then_in {n p q:ℚ} (hp: p ∈ OfRatDef n) (hq: q < p): q ∈ OfRatDef n := by
  simp [OfRatDef] at *
  exact lt_trans hq hp

theorem OfRat_def_ex_gt {n p:ℚ} (hp: p ∈ OfRatDef n): ∃ r ∈ OfRatDef n, p < r := by
  simp [OfRatDef] at *
  use (p+n) / 2
  constructor
  rw [← add_lt_left_cancel (a:=-n)]
  rw [add_comm]
  rw [← sub_eq_add_neg]
  rw [neg_add]
  rw [← gtz_mul_lt_left_cancel (a:=2)]
  ring_nf
  simp [hp]
  simp
  rw [← add_lt_left_cancel (a:=-p)]
  rw [add_comm]
  rw [← sub_eq_add_neg]
  rw [sub_self]
  rw [← gtz_mul_lt_left_cancel (a:=2)]
  ring_nf
  simp [hp]
  simp

instance instOfNatRR (n : Nat) : OfNat RR n where
  ofNat := ⟨ OfRatDef n, ofRat_def_ne_empty, ofRat_def_ne_univ, OfRat_lt_then_in, OfRat_def_ex_gt⟩

instance : Zero RR where
  zero := (instOfNatRR 0).ofNat

instance : One RR where
  one := (instOfNatRR 1).ofNat

theorem zero_def : (0 : RR) = ⟨ OfRatDef 0, ofRat_def_ne_empty, ofRat_def_ne_univ, OfRat_lt_then_in, OfRat_def_ex_gt⟩ := rfl

theorem one_def : (1 : RR) = ⟨ OfRatDef 1, ofRat_def_ne_empty, ofRat_def_ne_univ, OfRat_lt_then_in, OfRat_def_ex_gt⟩ := rfl

def NegDef (α : RR) := {p:ℚ | ∃ r:ℚ, r > 0 ∧ - p - r ∉ α }

theorem neg_def_ne_empty {α: RR} : NegDef α ≠ ∅ := by
  simp [Set.not_empty_iff_ex_mem, NegDef]
  have h:= α.ne_univ
  rw [Set.ne_univ_iff_ex_not_in] at h
  rcases h with ⟨ s, hs⟩
  let p := -s -1
  have h1: -p-1 ∉ α.carrier := by
    simp [p]
    exact hs
  use p
  use 1
  simp
  exact h1

theorem neg_def_ne_univ {α: RR} : NegDef α ≠ Set.univ := by
  simp [Set.ne_univ_iff_ex_not_in, NegDef]
  have h:= α.ne_nempty
  rw [Set.not_empty_iff_ex_mem] at h
  rcases h with ⟨r, hr⟩
  use -r
  intro x hx
  simp
  have h: r - x < r := by
    simp
    exact hx
  apply α.lt_then_in hr h

theorem neg_def_lt_then_in {α: RR} {p q:ℚ} (hp: p ∈ NegDef α) (hq: q < p): q ∈ NegDef α := by
  simp [NegDef] at *
  rcases hp with ⟨ r, hr, hpr⟩
  use r
  constructor
  exact hr
  intro hqr
  have h:= α.in_lt_not_in hqr hpr
  simp at h
  linarith

theorem neg_def_ex_gt {α: RR} {p:ℚ} (hp: p ∈ NegDef α): ∃ r ∈ NegDef α, p < r := by
  simp [NegDef] at *
  rcases hp with ⟨ r, hr, hpr⟩
  have h := α.ne_nempty
  rw [Set.not_empty_iff_ex_mem] at h
  rcases h with ⟨ x, hx⟩
  use p + r / 2
  simp
  constructor
  use r / 2
  simp
  constructor
  assumption
  ring_nf
  rw [neg_sub_comm]
  exact hpr
  exact hr

instance : Neg RR where
  neg a := ⟨
    NegDef a,
    neg_def_ne_empty,
    neg_def_ne_univ,
    neg_def_lt_then_in,
    neg_def_ex_gt⟩

theorem neg_def {α:RR} : -α = ⟨
    NegDef α,
    neg_def_ne_empty,
    neg_def_ne_univ,
    neg_def_lt_then_in,
    neg_def_ex_gt⟩ := by rfl

/-
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
-/

theorem add_comm {a b : RR} : a + b = b + a := by
  apply Cut.ext
  simp [HAdd.hAdd, instAddRR, AddDef]
  apply Set.ext
  intro x
  simp
  constructor
  <;>intro h
  <;>rcases h with ⟨ r, hr, s, hs, hrs⟩
  <;>use s
  <;>constructor
  assumption
  use r
  constructor
  assumption
  simp [hrs]
  simpa [HAdd.hAdd] using (Rat.add_comm (a:=r) (b:=s))
  exact hs
  use r
  constructor
  assumption
  simp [hrs]
  simpa [HAdd.hAdd] using (Rat.add_comm (a:=r) (b:=s))

theorem add_assoc {a b c: RR} : (a + b) + c = a + (b + c) := by
  apply Cut.ext
  simp [HAdd.hAdd, instAddRR, AddDef]
  apply Set.ext
  intro x
  simp
  constructor
  <;>intro h
  rcases h with ⟨n, ⟨⟨ r, hr0, ⟨ s, hs0, hs1⟩ ⟩, t, ⟨ ht0, ht1⟩ ⟩ ⟩
  use r
  constructor
  assumption
  use s + t
  constructor
  use s
  constructor
  assumption
  use t
  constructor
  assumption
  rfl
  rw [ht1, hs1]
  simpa [HAdd.hAdd] using (Rat.add_assoc (a:=r) (b:=s))
  rcases h with ⟨r, hr0, h⟩
  rcases h with ⟨n, h, hrn⟩
  rcases h with ⟨s, hs0, h⟩
  rcases h with ⟨t, ht0, hst⟩
  use r + s
  constructor
  use r
  constructor
  assumption
  use s
  constructor
  assumption
  rfl
  use t
  constructor
  assumption
  simp [hrn, hst]
  have h := (Rat.add_assoc (a:=r) (b:=s) (c:=t)).symm
  exact h

theorem zero_add {a:RR} : 0 + a = a := by
  apply Cut.ext
  simp [zero_def, OfRatDef]
  simp [HAdd.hAdd, instAddRR, AddDef]
  apply Set.ext
  intro x
  constructor
  <;>intro h
  -- rw [Set.mem_setOf] at h
  rcases h with ⟨ r, hr, s, hs, hrs⟩
  rw [← Rat.add_lt_left_cancel (a:=s), add_zero] at hr
  have : x = r + s := hrs
  rw [Rat.add_comm] at this
  rw [← this] at hr
  apply a.lt_then_in (p:=s)
  exact hs
  exact hr
  simp
  have h1:= a.ex_gt h
  rcases h1 with ⟨ r, hr1, hr2⟩
  use x - r
  constructor
  simp [hr2]
  use r
  constructor
  exact hr1
  have : Add.add (x - r) r = (x - r) + r := by rfl
  rw [this]
  simp

theorem add_neg {a:RR} : a + -a = 0 := by
  simp [neg_def, zero_def]
  simp [HAdd.hAdd, instAddRR, AddDef, OfRatDef, NegDef]
  apply Set.ext
  intro x
  simp
  constructor
  intro h
  rcases h with ⟨ r, hr, s, h, hrs⟩
  rcases h with ⟨ t, ht, hst⟩
  have := Cut.in_lt_not_in  hr hst
  have h : x = r + s := by
    rw [hrs]
    rfl
  rw [h]
  have h: r + s < -t := by linarith
  have h1: -t < 0 := by linarith
  have h2: r + s < 0 := by linarith
  exact h2
  intro hx
  let y := -x/2
  have hy : y > 0 := by
    simp [y]
    exact hx
  have hynz := ne_of_gt hy
  rcases Cut.ex_mem (α := a) with ⟨ r, hr ⟩
  rcases Cut.mem_then_ex_add_mem_and_add_delta_not_mem hr hy with ⟨n, hn⟩
  use r +  ↑n * y
  constructor
  exact hn.left
  use x - (r +  ↑n * y)
  constructor
  use -x - y
  have : x = -2 * y := by
    simp [y]
  constructor
  simp [y]
  exact hx
  simp [this]
  ring_nf
  ring_nf at hn
  exact hn.right
  have : Add.add (r + ↑n * y) (x - (r + ↑n * y)) = (r + ↑n * y) + (x - (r + ↑n * y)) := by rfl
  simp [this]

theorem le_then_add_le {a b c:RR} (hbc: b ≤ c) : a + b ≤ a + c:= by
  simp only [Cut.le_def, HAdd.hAdd, instAddRR, AddDef, Set.mem_setOf] at hbc
  simp only [Cut.le_def, HAdd.hAdd, instAddRR, AddDef, Set.mem_setOf]
  intro x hx
  rcases hx with ⟨ r, hr, s, hs, hrs⟩
  use r
  constructor
  exact hr
  use s
  constructor
  exact hbc s (Cut.mem_iff_mem_carrier.mp hs)
  exact hrs


theorem lt_then_add_lt {a b c:RR} (hbc: b < c) : a + b < a + c:= by
  rw [lt_iff_le_and_ne] at *
  constructor
  exact le_then_add_le hbc.left
  intro h
  apply hbc.right
  have : a + b + -a = a + c + -a := by
    rw [h]
  rw [add_comm] at this
  rw [← add_assoc] at this
  rw [add_comm, add_comm (a:=-a), add_neg, add_comm, zero_add] at this
  rw [add_comm, ← add_assoc, add_comm (a:=-a), add_neg, zero_add] at this
  exact this







theorem add_lt_left_cancel {a b c:RR}: b < c ↔ a + b < a + c := by
  sorry

end Real


end Rudin
