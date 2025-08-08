import Mathlib
import Rudin.Command
import Rudin.Basic
import Rudin.Chapter1.Set
import Rudin.Chapter1.Field
import Rudin.Chapter1.Ordered
import Rudin.Chapter1.OrderedField
import Rudin.Chapter1.Rational
import Rudin.Chapter1.Bound
import Rudin.Chapter1.Inequality
import Rudin.Chapter1.PowRat

attribute [-simp] nsmul_eq_mul

namespace Rudin

namespace Real

structure Cut where
  carrier : Set ℚ
  ne_nempty : carrier ≠ ∅
  ne_univ : carrier ≠ Set.univ
  lt_then_in {p q:ℚ} (hp: p ∈ carrier) (hq: q < p): q ∈ carrier
  ex_gt {p:ℚ} (hp: p ∈ carrier): ∃ r ∈ carrier, p < r


instance instMemRR : Membership ℚ Cut where
  mem α q  := q ∈ α.carrier


namespace Cut

variable {α β γ: Cut}

theorem ext {a b : Cut} (hab : a.carrier = b.carrier) : a = b := by
  cases a
  cases b
  cases hab
  simp

theorem ext_iff {a b:Cut} : a = b ↔ a.carrier = b.carrier := by
  constructor
  intro h
  rw [h]
  exact ext


instance : DecidableEq (α = β) := fun a b => decEq a b

@[simp] theorem mem_iff_mem_carrier {x:ℚ} {a:Cut} : x ∈ a ↔ x ∈ a.carrier := by
  simp [Rudin.Real.instMemRR]

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
      have hn:= h n
      simp
      apply hn
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

theorem not_mem_then_gt_not_mem {α:Cut} {p q: ℚ} (hp: p ∉ α) (hpq: p < q) : q ∉ α := by
  by_contra hq
  have h1 := α.lt_then_in hq hpq
  exact hp h1

theorem ex_lt {α : Cut} {r:ℚ} (hr : r ∈ α) : ∃ s, s < r ∧ s ∈ α := by
  use r - 1
  have hs : r - 1 < r := by linarith
  constructor
  exact hs
  exact α.lt_then_in hr hs


instance instLTRR : LT Cut where
  lt a b := a.carrier < b.carrier

instance instLERR : LE Cut where
  le a b := a.carrier ≤ b.carrier

noncomputable instance : DecidableLT Cut := fun a b => Classical.dec (a < b)

noncomputable instance : DecidableLE Cut := fun a b => Classical.dec (a ≤ b)

theorem lt_then_ex_not_in_carrier {a b:Cut} (h: a < b): ∃ x ∈ b, x ∉ a := by
  simp [instLTRR, ← Set.ssub_iff_lt, Set.ssub_def] at h
  rcases h with ⟨h1, x, hx1, hx2⟩
  use x
  simp [Rudin.Real.instMemRR]
  constructor
  exact hx1
  exact hx2

theorem le_iff_not_gt {a b:Cut} : a ≤ b ↔ ¬ a > b := by
  simp [Cut.instLTRR, Cut.instLERR, ← Set.ssub_iff_lt, ← Set.sub_iff_le]
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
    simp [Cut.instLTRR]
    intro a b c hab hbc
    exact Set.lt_trans hab hbc

  lt_trichotomy_complete : ∀ a b : Cut,
    (a < b ∧ ¬ a = b ∧ ¬ b < a) ∨
    (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
    (¬ a < b ∧ ¬ a = b ∧ b < a) := by
    intro a b
    by_cases h: a = b
    <;>simp [h, Cut.instLTRR, ← Set.ssub_iff_lt]
    by_cases h1: a.carrier ⊂ b.carrier
    <;>simp [h1]
    simp [Cut.ne_iff_carrier_ne] at h
    rw [Set.ssub_iff_lt] at h1
    simp at h1
    have h2 : ¬(a ≤ b ∧ a.carrier ≠ b.carrier) := by
      simp [instLERR]
      intro h3
      exfalso
      simp [← Set.le_iff_subset, Set.le_iff_lt_or_eq] at h3
      rcases h3 with h3|h3
      <;>contradiction

    rw [Cut.le_iff_not_gt] at h2
    rw [Classical.not_and_iff_not_or_not] at h2
    simp [Cut.instLTRR] at h2
    rcases h2 with h2|h2
    exact h2
    exact (h h2).elim

  le_iff_lt_or_eq : ∀ a b : Cut, a ≤ b ↔ (a < b ∨ a = b) := by
    simp [Cut.instLTRR, Cut.instLERR]
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
  simp only [instLERR, ← Set.sub_iff_le, Set.sub_def]

theorem lt_def {a b:Cut} : a < b ↔ (∀ x, x ∈ a.carrier → x ∈ b.carrier) ∧ ∃ x ∈ b.carrier, x ∉ a.carrier:= by
  simp [instLTRR, ← Set.ssub_iff_lt, Set.ssub_def]

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


instance instLeastUpperBoundPropertyRR : LeastUpperBoundProperty RR where

  subset_sup_exist (E : Set RR) (h_no_empty: E ≠ ∅) (h_bound_above: BoundAbove E): ∃ a, IsSup E a := by
    let A:= E
    let hA := And.intro h_no_empty h_bound_above
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
    by_cases h: ∃ δ, δ < γ ∧ IsSup A δ
    rcases h with ⟨ δ, h1, h2 ⟩
    have h3:= Real.Cut.lt_then_ex_not_in_carrier h1
    rcases h3 with ⟨ s, hs1, hs2⟩
    simp [Real.instMemRR] at hs1
    rw [Set.mem_setOf] at hs1
    simp [IsSup, UpperBound] at h2
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
    simp at *
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

instance instAddRR: Add RR where
  add a b := ⟨ AddDef a b, add_def_ne_empty, add_def_ne_univ, add_def_lt_then_in, add_def_ex_gt⟩

theorem mem_add_def_iff {α β:RR} {x : ℚ}: x ∈ (α + β) ↔ ∃ r ∈ α, ∃ s ∈ β, x = r + s := by
  simp [Rudin.Real.instMemRR, HAdd.hAdd, instAddRR, AddDef]

def OfRatDef (n:ℚ) := {x:ℚ | x < n}

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

def OfRat (q:ℚ) : RR := ⟨
    OfRatDef q,
    ofRat_def_ne_empty,
    ofRat_def_ne_univ,
    OfRat_lt_then_in,
    OfRat_def_ex_gt
  ⟩

instance instCoeRatRR : Coe Rat RR where
  coe q := OfRat q


instance instOfNatRR (n : Nat) : OfNat RR n where
  ofNat := OfRat n

instance : Zero RR where
  zero := (instOfNatRR 0).ofNat

instance : One RR where
  one := (instOfNatRR 1).ofNat

theorem zero_def : (0 : RR) = OfRat 0 := by rfl

theorem one_def : (1 : RR) = OfRat 1 := by rfl

@[simp]
theorem ofRat_eq_rat {a:Rat} : OfRat a = (a:RR) := by rfl


theorem Cut.gt_ofRat_ex_mem_gt {α : RR} {q:ℚ} (h: α > OfRat q) :
  ∃ x ∈ α , x > q := by
  rcases Cut.lt_then_ex_not_in_carrier h with ⟨ r, hr1, hr2⟩
  simp [OfRat, OfRatDef] at hr2
  rcases α.ex_gt hr1 with ⟨ s, hs1, hs2⟩
  use s
  constructor
  assumption
  linarith


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
  simp at h1
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
  simp [zero_def, OfRatDef, OfRat]
  simp [HAdd.hAdd, instAddRR, AddDef]
  apply Set.ext
  intro x
  constructor
  <;>intro h
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
  simp [HAdd.hAdd, instAddRR, AddDef, OfRatDef, OfRat, NegDef]
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
    linarith
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
  linarith
  simp [this]
  ring_nf
  ring_nf at hn
  exact hn.right
  have : Add.add (r + ↑n * y) (x - (r + ↑n * y)) = (r + ↑n * y) + (x - (r + ↑n * y)) := by rfl
  simp [this]

theorem add_left_cancel {a b c:RR} : a + b = a + c ↔ b = c := by
  constructor
  <;>intro h
  rw [← zero_add (a:=b), ← add_neg (a:=a), add_comm (a:=a), add_assoc, h,
      ← add_assoc, add_comm (a:=-a), add_neg, zero_add]
  rw [h]

theorem le_then_add_le {a b c:RR} (hbc: b ≤ c) : a + b ≤ a + c:= by
  simp only [Cut.le_def] at hbc
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
  constructor
  <;>intro h
  exact lt_then_add_lt h
  have h1:= lt_then_add_lt (a:=-a) h
  rw [← add_assoc, add_comm (a:=-a), add_neg, zero_add] at h1
  rw [← add_assoc, add_comm (a:=-a), add_neg, zero_add] at h1
  exact h1

@[simp]
theorem neg_ltz_iff_gtz {a:RR} : -a < 0 ↔ a > 0 := by
  rw [add_lt_left_cancel (a:=a)]
  rw [add_neg, add_comm, zero_add]

@[simp] theorem neg_neg {a:RR} : - - a = a := by
  have h1: a + -a = 0 := add_neg
  have h2: -a + - -a = 0 := add_neg
  rw [← h1] at h2
  rw (occs := .pos [2])[add_comm] at h2
  rw [add_left_cancel] at h2
  exact h2




def GtzMulDef (α:RR) (β:RR)  := { p : ℚ | ∃ r s : ℚ, r ∈ α ∧ s ∈ β ∧ 0 < r ∧ 0 < s ∧ p ≤ r * s }

theorem gtz_then_ex_mem_gtz {α:RR} (h: α > 0) : ∃ x ∈ α, x > 0 := by
  simp [zero_def, OfRatDef, OfRat, Cut.lt_def] at h
  simp
  rcases h with ⟨ h, ⟨ x, hx1, hx2⟩⟩
  rcases α.ex_gt hx1  with ⟨ y, hy⟩
  use y
  constructor
  exact hy.left
  linarith

theorem gtz_mul_def_ne_empty {α β:RR} (h1: α > 0) (h2: β > 0) : GtzMulDef α β  ≠ ∅ := by
  simp [GtzMulDef, Set.not_empty_iff_ex_mem]
  rcases gtz_then_ex_mem_gtz h1 with ⟨ r, hr⟩
  rcases gtz_then_ex_mem_gtz h2 with ⟨ s, hs⟩
  use r * s
  use r
  constructor
  exact hr.left
  use s
  constructor
  exact hs.left
  constructor
  exact hr.right
  constructor
  exact hs.right
  linarith


theorem gtz_mul_def_ne_univ {α β:RR} : GtzMulDef α β  ≠ Set.univ := by
  simp [GtzMulDef, Set.ne_univ_iff_ex_not_in]
  rcases Cut.ex_not_mem (α := α) with ⟨ r,hr ⟩
  rcases Cut.ex_not_mem (α := β) with ⟨ s,hs ⟩
  use r * s
  intro x hx1 y hy1 hx2 hy2
  have hrx := α.in_lt_not_in hx1 hr
  have hsy := β.in_lt_not_in hy1 hs
  refine mul_lt_mul'' hrx hsy ?_ ?_
  linarith
  linarith

theorem gtz_mul_def_lt_then_in {p q:ℚ} {α β:RR}
  (hp: p ∈ GtzMulDef α β ) (hq: q < p): q ∈ GtzMulDef α β := by
  simp [GtzMulDef] at *
  rcases hp with ⟨ x, hx, y, hy, hx1, hy1, hxy⟩
  use x
  constructor
  exact hx
  use y
  constructor
  exact hy
  constructor
  exact hx1
  constructor
  exact hy1
  linarith

theorem gtz_mul_def_ex_gt {p:ℚ} {α β:RR}
  (hp: p ∈  GtzMulDef α β): ∃ r ∈  GtzMulDef α β , p < r := by
  simp [GtzMulDef] at *
  rcases hp with ⟨ r, hr, s, hs, hr1, hs1, hrs⟩
  rcases α.ex_gt hr with ⟨x, hx1, hx2⟩
  rcases β.ex_gt hs with ⟨y, hy1, hy2⟩
  rcases α.ex_gt hx1 with ⟨a, ha1, ha2⟩
  rcases β.ex_gt hy1 with ⟨b, hb1, hb2⟩
  use x * y
  constructor
  use a
  constructor
  exact ha1
  use b
  constructor
  exact hb1
  constructor
  linarith
  constructor
  linarith
  refine mul_le_mul ?_ ?_ ?_ ?_
  <;>linarith
  have : r * s < x * y := by
    apply mul_lt_mul''
    assumption
    assumption
    linarith
    linarith
  linarith



theorem gtz_mul_def_gtz_mul_gtz_then_gtz {α β:RR} (h1: α > 0) (h2: β > 0) : GtzMulDef α β > (0:RR).carrier := by
  simp only [gt_iff_lt, zero_def, OfRatDef, OfRat, GtzMulDef, Set.lt_iff_ssubset, Set.ssub_def]
  simp
  constructor
  intro x hx
  rcases gtz_then_ex_mem_gtz h1 with ⟨ r, hr⟩
  rcases gtz_then_ex_mem_gtz h2 with ⟨ s, hs⟩
  use r
  constructor
  exact hr.left
  use s
  constructor
  exact hs.left
  constructor
  exact hr.right
  constructor
  exact hs.right
  have : r*s > 0 := gtz_mul_gtz_then_gtz hr.right hs.right
  linarith
  rcases gtz_then_ex_mem_gtz h1 with ⟨ r, hr⟩
  rcases gtz_then_ex_mem_gtz h2 with ⟨ s, hs⟩
  rcases α.ex_gt hr.left with ⟨ x, hx⟩
  rcases β.ex_gt hs.left with ⟨ y, hy⟩
  use r * s
  constructor
  use x
  constructor
  exact hx.left
  use y
  constructor
  exact hy.left
  constructor
  apply lt_trans hr.right hx.right
  constructor
  apply lt_trans hs.right hy.right
  apply le_of_lt
  apply mul_lt_mul''
  exact hx.right
  exact hy.right
  exact le_of_lt hr.right
  exact le_of_lt hs.right
  apply le_of_lt
  apply gtz_mul_gtz_then_gtz
  exact hr.right
  exact hs.right


def GtzMul (α:RR) (β:RR) (h1: α > 0) (h2: β > 0) :=
  (⟨
    GtzMulDef α β,
    gtz_mul_def_ne_empty h1 h2,
    gtz_mul_def_ne_univ,
    gtz_mul_def_lt_then_in,
    gtz_mul_def_ex_gt
  ⟩ : RR)


noncomputable instance instMulRR : Mul RR where
  mul α β :=
    have h1 {x:RR} (hx:x<0): -x > 0 := by
      rw [← neg_ltz_iff_gtz]
      simp
      exact hx
    if ha: α > 0 then
      if hb: β > 0 then
        GtzMul α β ha hb
      else if hb: β < 0 then
        - GtzMul α (-β) ha (h1 hb)
      else
        (0:RR)
    else if ha: α < 0 then
      if hb: β > 0 then
        - GtzMul (-α) β (h1 ha) hb
      else if hb: β < 0 then
        GtzMul (-α) (-β) (h1 ha) (h1 hb)
      else
        (0:RR)
    else
      (0:RR)

-- mul_comm  : ∀ a b : α, a * b = b * a
--   mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)
--   one_nz : (1 : α) ≠ (0 : α)
--   one_mul   : ∀ a : α, 1 * a = a
--   mul_inv_when_nz   : ∀ a : α, a ≠ 0 → a * (1 / a) = 1
--   -- distributive law
--   mul_add   : ∀ a b c : α, a * (b + c) = a * b + a * c

theorem gtzMul_comm {a b:RR} (ha: a>0) (hb:b>0) : GtzMul a b ha hb = GtzMul b a hb ha := by
  simp [GtzMul, GtzMulDef]
  apply Set.ext
  intro x
  constructor
  intro hx
  simp at *
  rcases hx with ⟨ r, hr, s, hs, hr1, hs1, hrs⟩
  use s
  constructor
  exact hs
  use r
  constructor
  exact hr
  constructor
  exact hs1
  constructor
  exact hr1
  rw [mul_comm]
  exact hrs
  intro hx
  simp at *
  rcases hx with ⟨ r, hr, s, hs, hr1, hs1, hrs⟩
  use s
  constructor
  exact hs
  use r
  constructor
  exact hr
  constructor
  exact hs1
  constructor
  exact hr1
  rw [mul_comm]
  exact hrs

@[simp]
theorem gtzMul_gtz {α β : RR} (hα : α > 0) (hβ : β > 0) :
    (0 : RR) < GtzMul α β hα hβ := by
  have h := gtz_mul_def_gtz_mul_gtz_then_gtz hα hβ
  simp [GtzMul, Cut.instLTRR]
  exact h

@[simp]
theorem neg_gtzMul_ltz {α β : RR} (hα : α > 0) (hβ : β > 0) :
    -GtzMul α β hα hβ < 0 := by
  simp

/--  `GtzMul` 的结合律（只列出正数情形即可）。 -/
theorem gtzMul_assoc
    {a b c : RR} (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    GtzMul (GtzMul a b ha hb) c (gtzMul_gtz ha hb) hc =
      GtzMul a (GtzMul b c hb hc) ha (gtzMul_gtz hb hc) := by

  simp [GtzMul, GtzMulDef]
  apply Set.ext
  intro x
  constructor
  intro h
  simp at *
  rcases h with ⟨m, hm1, hm2⟩
  rcases hm1 with ⟨ r, hr1, s, hs1, hr2, hs2, hrs⟩
  rcases hm2 with ⟨ t, ht1, hm, ht2, hmt⟩
  use r
  constructor
  assumption
  use s * t
  constructor
  use s
  constructor
  assumption
  use t
  constructor
  assumption
  constructor
  apply gtz_mul_gtz_then_gtz
  repeat assumption
  rw [← mul_assoc]
  have : m * t ≤ r * s * t := by
    rw [Rudin.gtz_mul_le_right_cancel]
    exact hrs
    exact ht2
  linarith
  intro h
  simp at *
  rcases h with ⟨r, hr, hm⟩
  rcases hm with ⟨m, hm, hr1, hm1, hrm⟩
  rcases hm with ⟨s, hs, t, ht, hs1, ht1, hst⟩
  use r * s
  constructor
  use r
  constructor
  assumption
  use s
  use t
  constructor
  assumption
  constructor
  apply gtz_mul_gtz_then_gtz
  repeat assumption
  constructor
  assumption
  have : r * m ≤ r * s * t := by
    rw [mul_assoc]
    rw [Rudin.gtz_mul_le_left_cancel]
    exact hst
    exact hr1
  linarith

theorem one_gtzMul {α : RR} (ha : α > 0) : GtzMul 1 α one_gz ha = α := by
  apply Cut.ext
  simp [GtzMul, GtzMulDef, one_def, OfRatDef, OfRat, Set.ext_iff]
  intro x
  constructor
  intro h
  rcases h with ⟨r, hr1, s, hs, hr2, hs2, hrs⟩
  have hrs2 : r * s < s := by
    rw (occs := .pos [2]) [← one_mul (a:=s)]
    rw [gtz_mul_lt_right_cancel]
    exact hr1
    exact hs2
  have hx2 : x < s := by linarith
  apply α.lt_then_in (p:=s) (q:=x) hs hx2
  intro hx
  rcases Cut.lt_then_ex_not_in_carrier (a:=0) (b:=1) (one_gz) with ⟨ r', hr1', hr2'⟩
  simp [zero_def, one_def, OfRatDef, OfRat] at hr1' hr2'

  -- turn the inequality into a membership proof for the cut `1`
  have hr1_mem : (r' : ℚ) ∈ (1 : RR) := by
    simpa [one_def, OfRat, OfRatDef, Rudin.Real.instMemRR] using hr1'

  rcases (1 : RR).ex_gt hr1_mem with ⟨ r, hr1, hr2⟩
  simp [one_def, OfRatDef, OfRat] at hr1
  rcases lt_trichotomy (a:=x) (b:=0) with hx1|hx1|hx1
  use r
  simp [hr1]
  rcases Cut.lt_then_ex_not_in_carrier ha with ⟨ s', hs1', hs2'⟩
  simp [zero_def, OfRatDef, OfRat] at hs2'
  rcases α.ex_gt hs1' with ⟨s, hs1, hs2⟩
  use s
  simp [hs1]
  constructor
  linarith
  constructor
  linarith
  have : 0 < r * s := by
    apply Rudin.gtz_mul_gtz_then_gtz
    repeat linarith
  linarith
  use r
  simp [hr1]
  rcases Cut.lt_then_ex_not_in_carrier ha with ⟨ s', hs1', hs2'⟩
  simp [zero_def, OfRatDef, OfRat] at hs2'
  rcases α.ex_gt hs1' with ⟨s, hs1, hs2⟩
  use s
  simp [hs1]
  constructor
  linarith
  constructor
  linarith
  have : 0 < r * s := by
    apply Rudin.gtz_mul_gtz_then_gtz
    repeat linarith
  linarith
  rcases α.ex_gt hx with ⟨ y, hy1, hy2⟩
  use x / y
  constructor
  rw [div_lt_iff₀]
  simp
  exact hy2
  linarith
  use y
  constructor
  exact hy1
  constructor
  rw [Rudin.div_eq_mul_inv]
  apply gtz_mul_gtz_then_gtz
  linarith
  apply Rudin.gtz_then_inv_gtz
  linarith
  constructor
  linarith
  rw [Rudin.div_mul_cancel]
  linarith


theorem mul_comm  {a b:RR} : a * b = b * a := by
  have h {x:RR} (hx:x<0): -x > 0 := by
    rw [← neg_ltz_iff_gtz]
    simp
    exact hx
  apply Cut.ext
  simp [HMul.hMul, instMulRR]
  apply Set.ext
  intro x
  constructor
  repeat
    intro hx
    split_ifs with h1 h2 h3 h4 h5 h6
    simp [h1, h2] at hx
    rw [gtzMul_comm]
    exact hx
    simp [h1, h2, h3] at hx
    rw [gtzMul_comm]
    exact hx
    simp [h2, h3] at hx
    exact hx
    simp [h1, h4, h5] at hx
    rw [gtzMul_comm]
    exact hx
    simp [h1, h4, h5, h6] at hx
    rw [gtzMul_comm]
    exact hx
    simp [h5, h6] at hx
    exact hx
    simp [h1, h4] at hx
    exact hx

theorem mul_assoc {a b c:RR} : a * b * c = a * (b * c) := by
  have h (x:RR) : if x < 0 then -x > 0 else if x > 0 then x > 0 else x = 0 := by
    rw [← neg_ltz_iff_gtz]
    simp
    intro h1
    intro h2
    rcases lt_trichotomy (a:=x) (b:=0) with h|h|h
    rw [← Rudin.not_le_iff_lt] at h
    exact (h h1).elim
    exact h
    rw [← Rudin.not_le_iff_lt] at h
    exact (h h2).elim


  apply Cut.ext
  simp [HMul.hMul, instMulRR]
  apply Set.ext
  intro x
  rcases lt_trichotomy (a:=a) (b:=0) with ha|ha|ha
  <;>have ha1 := h a
  <;>simp [ha] at ha1
  <;>simp [ha]
  <;>rcases lt_trichotomy (a:=b) (b:=0) with hb|hb|hb
  <;>have hb1 := h b
  <;>simp [hb] at hb1
  <;>simp [hb]
  <;>rcases lt_trichotomy (a:=c) (b:=0) with hc|hc|hc
  <;>have hc1 := h c
  <;>simp [hc] at hc1
  <;>simp [hc]
  have hna := Rudin.lt_then_not_gt ha
  have hnb := Rudin.lt_then_not_gt hb
  have hnc := Rudin.lt_then_not_gt hc
  simp [hna, hnb ,hnc, gtzMul_assoc]
  have hna := Rudin.lt_then_not_gt ha
  have hnb := Rudin.lt_then_not_gt hb
  have hmul := Rudin.lt_then_not_gt (neg_gtzMul_ltz hb1 hc)
  simp [hna, hnb, hmul, gtzMul_assoc]
  have hna := Rudin.lt_then_not_gt ha
  have hnc := Rudin.lt_then_not_gt hc
  have hmul1 := Rudin.lt_then_not_gt (neg_gtzMul_ltz ha1 hb)
  have hmul2 := Rudin.lt_then_not_gt (neg_gtzMul_ltz hb hc1)
  simp [hna, hnc, hmul1, hmul2, gtzMul_assoc]
  have hna := Rudin.lt_then_not_gt ha
  have hmul1 := Rudin.lt_then_not_gt (neg_gtzMul_ltz ha1 hb)
  simp [hna, hmul1, gtzMul_assoc]
  have hna := Rudin.lt_then_not_gt hb
  have hnc := Rudin.lt_then_not_gt hc
  have hmul1 := Rudin.lt_then_not_gt (neg_gtzMul_ltz ha hb1)
  simp [hna, hnc, hmul1, gtzMul_assoc]
  have hna := Rudin.lt_then_not_gt hb
  have hmul1 := Rudin.lt_then_not_gt (neg_gtzMul_ltz ha hb1)
  have hmul2 := Rudin.lt_then_not_gt (neg_gtzMul_ltz hb1 hc)
  simp [hna, hmul1, hmul2, gtzMul_assoc]
  have hnc := Rudin.lt_then_not_gt hc
  have hmul1 := Rudin.lt_then_not_gt (neg_gtzMul_ltz hb hc1)
  simp [hnc, hmul1, gtzMul_assoc]
  simp [gtzMul_assoc]

@[simp]
theorem one_gz : (1:RR) > 0 := by
  simp [zero_def, one_def, OfRatDef, OfRat, Cut.instLTRR, Set.ssub_def]
  constructor
  intro a ha
  have h1: (0:Rat) < 1 := by linarith
  linarith
  use 0
  simp

theorem one_nz : (1:RR) ≠ (0:RR) := by
  simp [zero_def, one_def, OfRatDef, OfRat, Set.ext_iff]
  use 0
  simp

/-
one_mul   : ∀ a : α, 1 * a = a
  mul_inv_when_nz   : ∀ a : α, a ≠ 0 → a * (1 / a) = 1
  -- distributive law
  mul_add   : ∀ a b c : α, a * (b + c) = a * b + a * c
-/

theorem one_mul {a:RR}: 1 * a = a := by
  simp [HMul.hMul, instMulRR]
  rcases lt_trichotomy (a:=a) (b:=0) with ha|ha|ha
  <;>simp [ha]
  have hna := Rudin.lt_then_not_gt ha
  simp [hna]
  rw [one_gtzMul]
  simp
  simp [one_gtzMul]

def GtzInvDef (α:RR) := {q | ∃ r : ℚ, r ∉ α ∧ 0 < r ∧ q * r < 1}

  -- ne_nempty : carrier ≠ ∅
  -- ne_univ : carrier ≠ Set.univ
  -- lt_then_in {p q:ℚ} (hp: p ∈ carrier) (hq: q < p): q ∈ carrier
  -- ex_gt {p:ℚ} (hp: p ∈ carrier): ∃ r ∈ carrier, p < r

theorem gtzInv_ne_empty {α:RR} (ha: α > 0): GtzInvDef α ≠ ∅ := by
  simp [GtzInvDef, Set.not_empty_iff_ex_mem]
  rcases Cut.gt_ofRat_ex_mem_gt ha with ⟨ r, hr1, hr2⟩
  rcases α.ex_not_mem with ⟨ s, hs⟩
  use 0
  use s
  constructor
  exact hs
  have hrs := α.in_lt_not_in hr1 hs
  constructor
  linarith
  simp

theorem gtzInv_ne_univ {α:RR} (ha: α > 0): GtzInvDef α ≠ Set.univ := by
  simp [GtzInvDef, Set.ne_univ_iff_ex_not_in]
  rcases Cut.gt_ofRat_ex_mem_gt ha with ⟨ r, hr1, hr2⟩
  rcases α.ex_not_mem with ⟨ s, hs⟩
  use 1/r
  intro x hx1 hx2
  rw [Rudin.mul_comm]
  apply Rudin.lt_then_le
  simp
  rw [← div_eq_mul_inv]
  rw [Rudin.lt_div_gtz_iff_mul_lt (a:=1) (b:=x) (c:=r)]
  simp
  have hrx := α.in_lt_not_in hr1 hx1
  exact hrx
  exact hr2

theorem gtzInv_lt_then_in {α:RR} {p q:ℚ}
   (hp: p ∈ GtzInvDef α ) (hq: q < p): q ∈ GtzInvDef α := by
  simp [GtzInvDef] at *
  rcases hp with ⟨ r, hr1, hr2, hpr⟩
  rcases lt_trichotomy (a:=q) (b:=0) with hq1|hq1|hq1
  . use r
    constructor
    assumption
    constructor
    assumption
    have : q * r < 0 := by
      rw [Rudin.mul_ltz_iff_opp_sign]
      simp [OppSign, hq1, hr2]
    linarith
  . use r
    constructor
    assumption
    constructor
    assumption
    have : q * r = 0 := by
      rw [hq1]
      simp
    linarith
  . use p * r / q
    constructor
    have : p * r / q > r:= by
      rw [gt_iff_lt]
      rw [Rudin.lt_div_gtz_iff_mul_lt (a:=r) (b:=p*r) (c:=q)]
      rw [Rudin.mul_comm]
      rw [gtz_mul_lt_right_cancel]
      exact hq
      exact hr2
      exact hq1
    apply Cut.not_mem_then_gt_not_mem hr1 this
    constructor
    rw [Rudin.lt_div_gtz_iff_mul_lt]
    simp
    apply Rudin.gtz_mul_gtz_then_gtz
    linarith
    assumption
    assumption
    rw [Rudin.mul_div_cancel_left']
    exact hpr
    linarith

theorem gtzInv_ex_gt {α:RR} {p:ℚ} (hp: p ∈ GtzInvDef α): ∃ r ∈ GtzInvDef α, p < r := by
  simp [GtzInvDef] at *
  rcases hp with ⟨ r, hr1, hr2, hpr⟩
  have p_lt_inv : p < 1 / r := by
    rw [Rudin.lt_div_gtz_iff_mul_lt]
    exact hpr
    exact hr2
  let q : ℚ := (p + 1 / r) / 2
  have two_gtz : (0 : ℚ) < 2 := by norm_num
  have p_lt_q : p < q := by
    simp only [q]
    rw [Rudin.lt_div_gtz_iff_mul_lt two_gtz]
    rw [Rudin.mul_comm]
    have := Rat.nat_mul_def (a:=p) (n:=2)
    have two_ne_zero: ¬ (2 = 0) := by norm_num
    norm_num at this
    rw [this]
    rw [Rudin.add_lt_left_cancel]
    exact p_lt_inv
  have q_lt_inv : q < 1 / r := by
    simp only [q]
    simp only [Rudin.gt_div_gtz_iff_mul_gt, two_gtz]
    have := Rat.nat_mul_def (a:=1/r) (n:=2)
    have two_ne_zero: ¬ (2 = 0) := by norm_num
    norm_num at this
    simp
    rw [Rudin.mul_comm, this]
    simp
    simp at p_lt_inv
    exact p_lt_inv
  have q_mul_lt_one : q * r < 1 := by
    rw [Rudin.lt_div_gtz_iff_mul_lt] at q_lt_inv
    exact q_lt_inv
    exact hr2
  use q
  constructor
  use r
  exact p_lt_q

-- 正数逆元
def GtzInv (α : RR) (hα : α > 0) : RR :=
  ⟨ GtzInvDef α
  , gtzInv_ne_empty hα
  , gtzInv_ne_univ  hα
  , gtzInv_lt_then_in
  , gtzInv_ex_gt ⟩

-- 先给出 Inv，再用它定义 Div
noncomputable instance instInvRR : Inv RR where
  inv a :=
    have pos_of_neg {x : RR} (h : x < 0) : -x > 0 := by
      rw [← neg_ltz_iff_gtz]; simpa using h
    by
      by_cases h₁ : a > 0
      · exact GtzInv a h₁
      · by_cases h₂ : a < 0
        · exact -GtzInv (-a) (pos_of_neg h₂)
        · exact 0    -- 这里对应 a = 0

noncomputable instance instDivRR : Div RR where
  div a b := a * (b⁻¹)   -- Lean 里 “⁻¹” 来自 Inv


theorem gtzInv_gtz {a:RR} (ha:a > 0) : GtzInv a ha > 0 := by
  simp [GtzInv, zero_def, OfRat, OfRatDef, GtzInvDef, Cut.lt_def]
  rcases Cut.gt_ofRat_ex_mem_gt ha with ⟨ r, hr1, hr2⟩
  rcases a.ex_not_mem with ⟨ s, hs⟩
  have h1:= Cut.in_lt_not_in hr1 hs
  have : s > 0 := by linarith
  constructor
  intro x hx
  use s
  constructor
  exact hs
  simp [this]
  have h2: x * s < 0 := by
    rw [Rudin.mul_comm]
    apply Rudin.gtz_mul_ltz_ltz
    repeat assumption
  have h3 : 0 < 1 := by norm_num
  linarith
  use 0
  constructor
  use s
  constructor
  exact hs
  constructor
  exact this
  simp
  simp


/-
  mul_inv_when_nz   : ∀ a : α, a ≠ 0 → a * (1 / a) = 1
  -- distributive law
  mul_add   : ∀ a b c : α, a * (b + c) = a * b + a * c

  -- remarks
  sub_eq_add_neg : ∀ a b : α, a - b = a + -b
  div_eq_mul_inv : ∀ a b : α, a / b = a * (1 / b)
  pow_nat_def : ∀ a : α, ∀ n : Nat, a ^ n = if n = 0 then 1 else a ^ (n - 1) * a
  nat_mul_def : ∀ a : α, ∀ n : Nat, n * a = if n = 0 then 0 else (n - 1) * a + a
-/
theorem Cut.ex_mem_gtz_and_gto_mul_not_mem {a:RR} {n:ℚ}
  (ha: a > 0)  (hn: n > 1) :
  ∃ p, p ∈ a ∧ p > 0 ∧ n * p ∉ a := by
  by_contra! h
  rcases Cut.gt_ofRat_ex_mem_gt ha with ⟨ r, hr1, hr2⟩
  have pow_in : ∀ m : ℕ, (n ^ m) * r ∈ a.carrier := by
    intro m
    induction m with
    | zero =>
      simp
      exact hr1
    | succ m hi =>
      have h1:= h (n ^ m * r) hi
      have hnmgz : n ^ m * r > 0 := by
        apply Rudin.gtz_mul_gtz_then_gtz
        refine pow_pos ?_ m
        linarith
        assumption
      have h2 := h1 hnmgz
      rw [pow_add, pow_one]
      rw [← Rudin.mul_assoc] at h2
      rw [Rudin.mul_comm (a:=(n^m))]
      exact h2
  have eq_univ : a.carrier = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    have hngz : n > 0 := by linarith
    rcases exists_nat_gt ((q/r-1)/(n - 1)) with ⟨ m, hm⟩
    have h1 := gtz_pow_ge_one_add_exp_mul_base_sub_one (n:=m) hngz
    have h2 := pow_in m
    have hn1 : n - 1 > 0 := by linarith
    have h3 : (1 + m * (n - 1)) * r > q := by
      rw [← gt_iff_lt] at hm
      rw [Rudin.gt_div_gtz_iff_mul_gt] at hm
      rw [gt_iff_lt] at hm
      rw [← Rudin.add_lt_left_cancel (a:=1)] at hm
      rw [← Rudin.add_sub_assoc, Rudin.add_sub_cancel] at hm
      rw [← gt_iff_lt] at hm
      rw [Rudin.gt_div_gtz_iff_mul_gt] at hm
      rw [gt_iff_lt] at hm
      simp
      repeat assumption
    have h4 : n ^ m > q/r := by
      rw [← Rudin.gt_div_gtz_iff_mul_gt] at h3
            -- 先把两条不等式里的 `Nat.cast` 统一，
      -- 并保证方向与 `gtz_pow_ge_one_add_exp_mul_base_sub_one` 相同
      have h1' : (1 : ℚ) + (m : ℚ) * (n - 1) ≤ n ^ m := by
        simpa [nsmul_eq_mul] using h1                     -- ≤ 方向

      have h3' : (1 : ℚ) + (m : ℚ) * (n - 1) > q / r := by
        simpa using h3                     -- 同时统一 `Nat.cast`

      -- `linarith` 现在可以直接使用
      linarith [h1', h3']
      assumption
    have h5 : n ^ m * r > q := by
      rw [← Rudin.gt_div_gtz_iff_mul_gt]
      exact h4
      assumption
    exact a.lt_then_in h2 h5
  exact a.ne_univ eq_univ

theorem Cut.gt_then_ex_mem_gt_and_lt {α:Cut} {r s:ℚ} (ha : α > r) (hpq: r < s):
  ∃ x ∈ α, x > r ∧ x < s := by
  rcases Rudin.lt_trichotomy (a:=α) (b:=s) with h|h|h
  <;>simp [Cut.lt_def, OfRat, OfRatDef, Cut.ext_iff, Set.ext_iff] at h ha
  rcases ha.right with ⟨ x, hx1, hx2⟩
  rcases α.ex_gt hx1 with ⟨ y, hy1, hy2⟩
  use y
  constructor
  assumption
  constructor
  linarith
  apply h.left
  assumption
  rcases ha.right with ⟨ x, hx1, hx2⟩
  rcases α.ex_gt hx1 with ⟨ y, hy1, hy2⟩
  use y
  constructor
  assumption
  constructor
  linarith
  rw [← h]
  assumption
  have : OfRat r < OfRat s := by
    simp [Cut.lt_def, OfRat, OfRatDef]
    constructor
    intro x hx
    linarith
    use r
  rcases Cut.gt_ofRat_ex_mem_gt (α := OfRat s) this with ⟨ x, hx1, hx2⟩
  simp [OfRat, OfRatDef] at hx1
  use x
  constructor
  apply h.left
  exact hx1
  constructor
  repeat linarith


private theorem gtzMul_gtzInv_eq_OfRat_one {a:RR} (ha: a > 0) : GtzMulDef a a⁻¹ = {x | x < 1} := by
  have ha3 : GtzInv a ha > 0 := gtzInv_gtz ha
  simp [instInvRR, ha]
  simp [HMul.hMul, GtzMulDef, GtzInv, GtzInvDef, Set.ext_iff]
  intro x
  constructor
  intro hx
  rcases hx with ⟨ r, hr, s, ⟨ u, hu1, hu2, hsu⟩ , t, hs1, hrs⟩
  have h: r * s < u * s:= by
    have h1:= a.in_lt_not_in hr hu1
    rw [Rudin.mul_comm (a:=r), Rudin.mul_comm (a:=u)]
    apply Rudin.gtz_mul_lt_gtz_mul
    repeat assumption
  have hsu : s * u < 1 := hsu
  have hru : x ≤ r * s  := hrs
  linarith
  intro hx
  have {m n:ℚ} : Mul.mul m n = m * n := by rfl
  simp [this]
  have hsolve: ∀ y, y > 0 ∧ y < 1 →  ∃ r ∈ a.carrier, ∃ x_1, (∃ r ∉ a.carrier, 0 < r ∧ x_1 * r < 1) ∧ 0 < r ∧ 0 < x_1 ∧ y ≤ r * x_1  := by
    intro y hy
    rcases hy with ⟨ hy1, hy2⟩
    have hy3: 1 / y > 1 := by
      rw [gt_iff_lt]
      rw [Rudin.lt_div_gtz_iff_mul_lt]
      simp
      repeat assumption
    rcases Cut.ex_mem_gtz_and_gto_mul_not_mem (a := a) (n := 1/y) ha hy3 with ⟨ u, hu1, hu2, hu3⟩
    ring_nf at hu3
    rw [Rudin.mul_comm, ← div_eq_mul_inv] at hu3
    rcases a.ex_gt hu1 with ⟨ r, hr1, hr2⟩
    use r
    repeat
      constructor
      assumption
    use y / r
    constructor
    use u / y
    constructor
    exact hu3
    constructor
    rw [Rudin.lt_div_gtz_iff_mul_lt]
    simp
    linarith
    linarith
    rw [Rudin.mul_comm, mul_div_assoc, Rudin.div_mul_cancel]
    rw [← gt_iff_lt]
    rw [Rudin.gt_div_gtz_iff_mul_gt]
    simp
    exact hr2
    linarith
    linarith
    constructor
    linarith
    constructor
    rw [Rudin.lt_div_gtz_iff_mul_lt]
    simp
    linarith
    linarith
    rw [Rudin.mul_div_cancel_left']
    linarith
  by_cases hx1: x > 0
  have h := hsolve x (And.intro hx1 hx)
  exact h
  rcases Cut.gt_then_ex_mem_gt_and_lt (α := a) (r:=0) (s:=1) ha (by linarith) with ⟨ d, hd1, hd2, hd3⟩
  have h := hsolve d (And.intro hd2 hd3)
  rcases h with ⟨ r, hr, s, ⟨ t,ht⟩, hs1, hs2, hs3⟩
  use r
  repeat
    constructor
    assumption
  use s
  constructor
  use t
  repeat
    constructor
    assumption
  have : x < d := by linarith
  linarith

theorem inv_eq_one_div {a:RR} : a⁻¹ = 1 / a := by
  simp [HDiv.hDiv, instDivRR]
  rw [one_mul]

theorem mul_inv_when_nz {a:RR} (ha: a ≠ 0) : a * (1 / a) = 1 := by
  simp [HDiv.hDiv, instDivRR, one_mul]
  simp [instInvRR]
  simp [one_def, OfRat,OfRatDef, HMul.hMul, instMulRR, gtzInv_gtz]

  rcases lt_trichotomy (a:=a) (b:=0) with ha1|ha1|ha1
  <;>simp [ha1,  Rudin.lt_then_not_gt, gtzInv_gtz, GtzMul]

  have ha2 : -a > 0 := by
    rw [← neg_ltz_iff_gtz]
    simp
    exact ha1
  have h:= gtzMul_gtzInv_eq_OfRat_one ha2
  simp [instInvRR, ha2] at h
  exact h

  exact (ha ha1).elim
  have h:= gtzMul_gtzInv_eq_OfRat_one ha1
  simp [instInvRR, ha1] at h
  exact h

private theorem gtz_add_gtz_then_gtz {a b:RR} (ha: a > 0) (hb: b > 0) : a + b > 0 := by
  simp [HAdd.hAdd, instAddRR, AddDef, Cut.lt_def, zero_def, OfRat, OfRatDef] at *
  rcases ha with ⟨ ha, x, hx1, hx2⟩
  rcases hb with ⟨ hb, y, hy1, hy2⟩
  constructor
  intro z hz1
  rcases (OfRat 0).ex_gt hz1 with ⟨ r, hr1, hr2⟩
  simp [OfRat, OfRatDef] at hr1
  use r
  constructor
  apply ha
  exact hr1
  use z - r
  constructor
  apply hb
  linarith
  have :  Add.add r (z - r) = r + (z - r) := by rfl
  simp [this]
  use x + y
  constructor
  use x
  constructor
  assumption
  use y
  constructor
  assumption
  rfl
  linarith





private theorem gtzMul_mul_add {a b c : RR} (ha: a > 0) (hb: b > 0) (hc: c > 0) :
  GtzMul a (b + c) (ha) (gtz_add_gtz_then_gtz hb hc) = GtzMul a b ha hb + GtzMul a c ha hc := by
  simp [GtzMul, GtzMulDef, Cut.ext_iff, Set.ext_iff, HAdd.hAdd, AddDef, instAddRR]
  intro x
  constructor
  intro hx
  rcases hx with ⟨ r , hr1, ⟨y, ⟨s, hs, t, ht, hst⟩, hr2, hy, hry ⟩ ⟩
  have hst : y = s + t := by assumption
  rw [hst, mul_add] at hry
  use r * s
  constructor
  . use r
    repeat
      constructor
      assumption
    by_cases hs1: s > 0
    use s
    simp at hs1
    rcases b.gt_ofRat_ex_mem_gt hb with ⟨ u, hu1, hu2⟩
    use u
    repeat
      constructor
      assumption
    rw [Rudin.gtz_mul_le_left_cancel hr2]
    linarith
  use x - r * s
  constructor
  . use r
    repeat
      constructor
      assumption
    by_cases ht1 : t > 0
    use t
    repeat
      constructor
      assumption
    simp at ht1
    simp
    linarith
    rcases c.gt_ofRat_ex_mem_gt hc with ⟨ v, hv1, hv2⟩
    use v
    repeat
      constructor
      assumption
    have hrv : r*t ≤ r*v := by
      rw [Rudin.gtz_mul_le_left_cancel hr2]
      simp at ht1
      linarith
    have : x - r * s ≤ r * t := by
      simp
      linarith
    linarith
  have : Add.add (r * s) (x - r * s) = r * s + (x-r*s) := by rfl
  simp [this]
  intro hx
  rcases hx with ⟨rs, hx⟩
  rcases hx with ⟨ hx1, rt, hx3⟩
  rcases hx1 with ⟨ r, hr, s, hs, hr1, hs1, hrs⟩
  rcases hx3 with ⟨hx3, hx⟩
  rcases hx3 with ⟨ r', hr', t ,ht, hr1', ht1, hrt'⟩
  by_cases hrr' : r > r'
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
  constructor
  linarith
  constructor
  linarith
  rw [hx]
  rw [mul_add]
  have : Add.add rs rt = rs + rt := by rfl
  simp [this]
  have : r'*t < r * t:= by
    rw [Rudin.gtz_mul_lt_right_cancel]
    exact hrr'
    assumption
  calc
    rs + rt ≤ r * s + rt := by linarith
    _ ≤ r * s + r' * t := by linarith
    _ ≤ r * s + r * t := by linarith
  use r'
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
  constructor
  linarith
  constructor
  linarith
  rw [hx]
  rw [mul_add]
  have : Add.add rs rt = rs + rt := by rfl
  simp [this]
  have : r * s ≤ r' * s:= by
    rw [Rudin.gtz_mul_le_right_cancel]
    simp at hrr'
    linarith
    assumption
  calc
    rs + rt ≤ r' * s + rt := by linarith
    _ ≤ r' * s + r' * t := by linarith

@[simp]
theorem neg_zero_eq_zero : (-0:RR) = 0 := by
  simp [zero_def, neg_def, NegDef, OfRat, OfRatDef, Cut.ext_iff, Set.ext_iff]
  intro x
  constructor
  <;>intro hx
  rcases hx with ⟨ r, hr1, hr2⟩
  have : -x > 0 := by linarith
  linarith
  use -x
  constructor
  linarith
  linarith

@[simp]
theorem mul_neg {a b:RR} : a * -b = - (a * b) := by
  simp [HMul.hMul, instMulRR]
  rcases Rudin.lt_trichotomy (a:=a) (b:=0) with ha|ha|ha
  have ha1: -a > 0 := by
    rw [← neg_ltz_iff_gtz]
    simp
    assumption
  have ha2: ¬ a > 0 := by
    simp
    apply lt_then_le
    exact ha
  simp [ha, ha2]
  rcases Rudin.lt_trichotomy (a:=b) (b:=0) with hb|hb|hb
  have hb1: -b > 0 := by
    rw [← neg_ltz_iff_gtz]
    simp
    assumption
  have hb2: ¬ b > 0 := by
    simp
    apply lt_then_le
    exact hb
  simp [hb, hb1, hb2]
  have hb2: ¬ b > 0 := by
    simp
    apply eq_then_le
    exact hb
  simp [hb]
  have : ¬ -b > 0 := by
    rw [← neg_ltz_iff_gtz]
    rw [neg_neg]
    simp
    apply lt_then_le
    exact hb
  simp [this, hb]
  have ha2: ¬ a > 0 := by
    simp
    apply eq_then_le
    exact ha
  simp [ha]
  simp [ha]
  rcases Rudin.lt_trichotomy (a:=b) (b:=0) with hb|hb|hb
  have hb1: -b > 0 := by
    rw [← neg_ltz_iff_gtz]
    simp
    assumption
  have hb2: ¬ b > 0 := by
    simp
    apply lt_then_le
    exact hb
  simp [hb, hb1, hb2]
  have hb2: ¬ b > 0 := by
    simp
    apply eq_then_le
    exact hb
  simp [hb]
  have : ¬ -b > 0 := by
    rw [← neg_ltz_iff_gtz]
    rw [neg_neg]
    simp
    apply lt_then_le
    exact hb
  simp [hb, this]

theorem neg_add_eq {a b:RR} : -(a+b) = -a + -b := by
  rw [← add_left_cancel (a:=a+b)]
  rw [add_neg]
  rw [← add_assoc, add_comm, add_comm (a:=a), add_assoc, add_neg, ← add_assoc, add_comm, zero_add, add_comm, add_neg]

@[simp]
theorem zero_mul {a:RR} : 0 * a = 0 := by simp [HMul.hMul, instMulRR]

private theorem mul_add_lemma_1  {a b c : RR} (ha: a > 0) (hb: b > 0) (hc: c > 0):
   a * (b + c) = a * b + a * c := by
   simp [HMul.hMul, instMulRR, ha, hb, hc, gtz_add_gtz_then_gtz, gtzMul_mul_add]

private theorem mul_add_lemma_2  {a b c : RR} (ha: a < 0) (hb: b > 0) (hc: c > 0):
  a * (b + c) = a * b + a * c := by
  have ha1:-a > 0 := by
    rw [← neg_ltz_iff_gtz]
    simp
    exact ha
  rw (occs := .pos [1]) [← neg_neg (a:=a)]
  rw [mul_comm]
  rw [mul_neg]
  rw [mul_comm]
  rw [mul_add_lemma_1 ha1 hb hc]
  rw [neg_add_eq]
  rw [mul_comm, mul_neg, neg_neg]
  rw [mul_comm (a:=-a), mul_neg, neg_neg, mul_comm, mul_comm (a:=c)]



private theorem mul_add_lemma_3 {a b c: RR} (hb: b > 0) (hc: c > 0) : a * (b + c) = a * b + a * c := by
  rcases lt_trichotomy (a:=a) (b:=0) with ha|ha|ha
  exact mul_add_lemma_2 ha hb hc
  rw [ha]
  simp [zero_mul, zero_add]
  exact mul_add_lemma_1 ha hb hc

private theorem mul_add_lemma_4  {a b c : RR} (hc: b < 0) (hbc: b + c > 0):
    a * (b + c) = a * b + a * c := by
  have hb1 : c = b + c + (-b):= by
    rw [add_comm]
    rw [← add_assoc]
    rw [add_comm (a:=-b)]
    rw [add_neg]
    rw [zero_add]
  have hb2: -b > 0 := by
    rw [← neg_ltz_iff_gtz]
    simp
    assumption
  rw (occs := .pos [2]) [hb1]
  rw [mul_add_lemma_3 hbc hb2]
  simp
  rw [← add_assoc]
  rw [add_comm (a:=a*b)]
  rw [add_assoc, add_neg, add_comm (b:=0), zero_add]

private theorem mul_add_lemma_5 {a b c : RR} (hb: b > 0) (hbc: b + c > 0):
    a * (b + c) = a * b + a * c := by
  rcases lt_trichotomy (a:=c) (b:=0) with hc|hc|hc
  rw [add_comm (b:=c), add_comm (a:=a*b)]
  rw [add_comm (b:=c)] at hbc
  exact mul_add_lemma_4 hc hbc
  simp [hc, add_comm (b:=0), zero_add, mul_comm (b:=0)]
  rw [add_comm (b:=c), add_comm (a:=a*b)]
  rw [add_comm (b:=c)] at hbc
  apply mul_add_lemma_3
  repeat assumption

private theorem mul_add_lemma_6 {a b c : RR} (hbc: b + c > 0): a * (b + c) = a * b + a * c := by
  rcases lt_trichotomy (a:=b) (b:=0) with hb|hb|hb
  apply mul_add_lemma_4
  repeat assumption
  rw [hb, zero_add, mul_comm (b:=0), zero_mul, zero_add]
  apply mul_add_lemma_5
  repeat assumption

private theorem mul_add_lemma_7  {a b c : RR} (hbc: b + c < 0):
  a * (b + c) = a * b + a * c := by
  have hbc1: -(b+c) > 0 := by
    rw [← neg_ltz_iff_gtz]
    simp
    assumption
  have : b + c = -(-b + -c) := by rw [neg_add_eq, neg_neg, neg_neg]
  rw [this]
  rw [mul_neg]
  rw [add_comm]
  rw [neg_add_eq, add_comm] at hbc1
  rw [mul_add_lemma_6]
  simp [neg_add_eq, add_comm]
  assumption

theorem mul_add {a b c : RR}: a * (b + c) = a * b + a * c := by
  rcases lt_trichotomy (a:=b + c) (b:=0) with h|h|h
  apply mul_add_lemma_7
  assumption
  simp [h, mul_comm (b:=0)]
  rw [← add_neg (a:=b)] at h
  rw [add_left_cancel] at h
  rw [h]
  rw [mul_neg]
  rw [add_neg]
  apply mul_add_lemma_6
  assumption

/-
  sub_eq_add_neg : ∀ a b : α, a - b = a + -b
  div_eq_mul_inv : ∀ a b : α, a / b = a * (1 / b)
  pow_nat_def : ∀ a : α, ∀ n : Nat, a ^ n = if n = 0 then 1 else a ^ (n - 1) * a
  nat_mul_def : ∀ a : α, ∀ n : Nat, n * a = if n = 0 then 0 else (n - 1) * a + a
-/

instance instSubRR : Sub RR where
  sub a b := ⟨ AddDef a (-b), add_def_ne_empty, add_def_ne_univ, add_def_lt_then_in, add_def_ex_gt⟩

theorem sub_eq_add_neg {a b:RR} : a - b = a + -b := by rfl

theorem div_eq_mul_inv {a b:RR} : a / b = a * (1 / b) := by
  simp [HDiv.hDiv, instDivRR]
  rw [← mul_assoc, mul_comm (b:=1), one_mul]

private noncomputable def powRRNat (a : RR) (n:ℕ) :=
  if n = 0
  then (1:RR)
  else a * powRRNat a (n-1)

noncomputable instance instPowRRNat : Pow RR Nat where
  pow a n := powRRNat a n

theorem pow_nat_def {a:RR} {n:ℕ} :  a ^ n = if n = 0 then 1 else a ^ (n - 1) * a := by
  simp [HPow.hPow, instPowRRNat]
  by_cases hn : n = 0
  rw [powRRNat]
  simp [hn]
  rw [powRRNat]
  simp [hn]
  rw [mul_comm]

noncomputable instance instSMulRR : SMul Nat RR where
  smul n a := OfRat n * a

-- Rudin chapter1 appendix step8 (a)
theorem ofRat_add_ofRat_eq {a b:Rat}: OfRat a + OfRat b = OfRat (a + b)  := by
  simp [HAdd.hAdd, instAddRR, AddDef, OfRat, OfRatDef, Cut.ext_iff, Set.ext_iff]
  intro x
  constructor
  intro hx
  rcases hx with ⟨ r, hr, s, hs, hrs⟩
  rw [hrs]
  have {u v:Rat}: Add.add u v = u + v := by rfl
  simp [this]
  linarith
  intro h
  have {u v:Rat}: Add.add u v = u + v := by rfl
  simp [this] at h
  simp [this]
  use (x - b + a) / (1 + 1)
  constructor
  rw [← gt_iff_lt, gt_div_gtz_iff_mul_gt]
  rw [Rudin.mul_add]
  simp
  linarith
  linarith
  use (x + b - a) / (1 + 1)
  constructor
  rw [← gt_iff_lt, gt_div_gtz_iff_mul_gt]
  rw [Rudin.mul_add]
  simp
  linarith
  linarith
  ring_nf


theorem nat_mul_def {a:RR} {n:ℕ} : n • a = if n = 0 then 0 else (n - 1) • a + a := by
  simp [HSMul.hSMul, instSMulRR]
  by_cases hn:n = 0
  <;>simp [hn]
  have : OfRat 0 = 0 := by rfl
  simp [this]
  rw (occs := .pos [3]) [← one_mul (a:=a)]
  repeat rw [mul_comm (b:=a)]
  rw [← mul_add]
  have : (↑(n - 1):Rat) = ↑n - 1 := by
    refine Nat.cast_pred ?_
    exact Nat.zero_lt_of_ne_zero hn
  rw [this]
  have : OfRat (↑n - 1) + 1 = OfRat n := by
    rw [one_def]
    rw [ofRat_add_ofRat_eq]
    rw [sub_add_cancel]
  rw [this]


noncomputable instance instRudinFieldRR : Rudin.Field RR where
  -- add axioms
  add_comm  := by apply add_comm
  add_assoc := by apply add_assoc
  zero_add  := by apply zero_add
  add_neg   := by apply add_neg
  -- mul axioms
  mul_comm  := by apply mul_comm
  mul_assoc := by apply mul_assoc
  one_nz := by apply one_nz
  one_mul   := by apply one_mul
  mul_inv_when_nz := by
    intro a ha
    rw [inv_eq_one_div]
    apply mul_inv_when_nz
    exact ha
  -- distributive law
  mul_add   := by apply mul_add

  -- remarks
  sub_eq_add_neg := by apply sub_eq_add_neg
  div_eq_mul_inv := by
    intro a b
    rw [inv_eq_one_div]
    apply div_eq_mul_inv
  inv_eq_one_div := by apply inv_eq_one_div
  powNat_def := by apply pow_nat_def
  natMul_def := by apply nat_mul_def


theorem gtz_mul_gtz_then_gtz {a b :RR} (ha: a > 0) (hb: b > 0) : a * b > 0 := by
  simp [HMul.hMul, instMulRR, ha, hb]


noncomputable instance instRudinOrderedFieldRR :Rudin.OrderedField RR where
  add_lt_left_cancel := add_lt_left_cancel.mpr
  gtz_mul_gtz_then_gtz := gtz_mul_gtz_then_gtz

-- Rudin chapter1 appendix step8 (c)
theorem ofRat_lt_ofRat_iff_lt {a b:Rat} : OfRat a < OfRat b ↔ a < b:= by
  simp [Cut.lt_def]
  simp [OfRat, OfRatDef]
  constructor
  intro h
  rcases h with ⟨ h1, x, hx1, hx2⟩
  linarith
  intro h
  constructor
  intro x hx
  linarith
  use a


theorem neg_ofRat_eq {a:Rat} : -OfRat a = OfRat (-a) := by
  simp [OfRat, neg_def, NegDef, OfRatDef, Set.ext_iff]
  intro x
  constructor
  <;>intro hx
  rcases hx with ⟨ r,hr1, hr2⟩
  linarith
  use -a - x
  constructor
  linarith
  linarith

private theorem ofRat_mul_ofRat_eq_lemma_1 {a b:Rat} (ha: a > 0) (hb: b > 0): OfRat a * OfRat b = OfRat (a * b) := by
  have h_simp: Mul.mul a b = a * b := by rfl
  have ha1: OfRat a > 0 := by
    rw [zero_def, gt_iff_lt]
    rw [ofRat_lt_ofRat_iff_lt]
    linarith
  have hb1: OfRat b > 0 := by
    rw [zero_def, gt_iff_lt]
    rw [ofRat_lt_ofRat_iff_lt]
    linarith
  simp [HMul.hMul, instMulRR, ha1, hb1]
  simp [GtzMul, GtzMulDef, OfRat, OfRatDef, Cut.ext_iff, Set.ext_iff]
  intro x
  constructor
  intro hx
  rcases hx with ⟨ r,hr, s,hs, hr1, hs1, hrs⟩
  simp [h_simp]
  have h: r*s < a * b := by
    exact mul_lt_mul_of_pos' hr hs hs1 ha
  linarith
  intro hx
  simp [h_simp] at hx
  by_cases hx1 : x > 0
  set d := a * b - x
  have hd: d > 0 := by linarith
  let r := a - d / (2 * b)
  have hr1: r < a := by
    simp [r, d]
    rw [lt_div_gtz_iff_mul_lt]
    simp
    linarith
    linarith

  have hr2 : r > 0 := by
    simp [r, d]
    rw [← gt_iff_lt]
    rw [gt_div_gtz_iff_mul_gt]
    linarith
    linarith
  let s := x / r
  have hs1: s < b := by
    simp [s, r]
    rw [← gt_iff_lt]
    rw [gt_div_gtz_iff_mul_gt]
    rw [Rudin.mul_sub]
    have : b * (d / (2 * b)) < d := by
      rw [Rudin.mul_div_assoc]
      rw [← gt_iff_lt]
      rw [gt_div_gtz_iff_mul_gt]
      rw [Rudin.mul_comm]
      simp [hd]
      linarith
      linarith
    linarith
    simp
    rw [← gt_iff_lt]
    rw [gt_div_gtz_iff_mul_gt]
    simp [d]
    linarith
    linarith
  have hs2 : s > 0 := by
    simp [s, r]
    rw [lt_div_gtz_iff_mul_lt]
    simp
    linarith
    simp
    rw [← gt_iff_lt]
    rw [gt_div_gtz_iff_mul_gt]
    linarith
    linarith
  use r
  constructor
  assumption
  use s
  repeat
    constructor
    assumption
  simp [s]
  rw [mul_div_cancel_left']
  linarith
  use a/2
  constructor
  linarith
  use b/2
  repeat
    constructor
    linarith
  linarith

private theorem ofRat_mul_ofRat_eq_lemma_2 {a b:Rat} (ha: a < 0) (hb: b > 0): OfRat a * OfRat b = OfRat (a * b) := by
  have ha2: -a > 0 := by
    simp
    assumption
  rw [← neg_neg (a:=a)]
  rw [neg_ofRat_eq]
  rw [mul_comm, mul_neg]
  rw [ofRat_mul_ofRat_eq_lemma_1 hb ha2]
  rw [neg_ofRat_eq, Rudin.mul_neg, Rudin.neg_neg, Rudin.mul_comm]

private theorem ofRat_mul_ofRat_eq_lemma_3 {a b:Rat} (hb: b > 0): OfRat a * OfRat b = OfRat (a * b) := by
  rcases lt_trichotomy (a:=a) (b:=0) with ha|ha|ha
  exact ofRat_mul_ofRat_eq_lemma_2 ha hb
  rw [ha]
  have : OfRat 0 = 0 := by rfl
  simp [this]
  exact ofRat_mul_ofRat_eq_lemma_1 ha hb

private theorem ofRat_mul_ofRat_eq_lemma_4 {a b:Rat} (hb: b < 0): OfRat a * OfRat b = OfRat (a * b) := by
  have hb2: -b > 0 := by
    simp
    assumption
  rw [← neg_neg (a:=b)]
  rw [neg_ofRat_eq]
  rw [mul_neg]
  rw [ofRat_mul_ofRat_eq_lemma_3 hb2]
  rw [neg_ofRat_eq, Rudin.mul_neg, Rudin.neg_neg, Rudin.mul_comm]


theorem ofRat_mul_ofRat_eq {a b:Rat}: OfRat a * OfRat b = OfRat (a * b) := by
  rcases lt_trichotomy (a:=b) (b:=0) with hb|hb|hb
  exact ofRat_mul_ofRat_eq_lemma_4 hb
  rw [hb]
  have : OfRat 0 = 0 := by rfl
  simp [this]
  exact ofRat_mul_ofRat_eq_lemma_3 hb

theorem ofRat_ext_iff {a b:Rat} : OfRat a = OfRat b ↔ a = b := by
  simp [OfRat,OfRatDef, Set.ext_iff]
  constructor
  intro h
  let t := (a + b) / (1 + 1)
  rcases lt_trichotomy (a := a) (b := b) with hab | hab | hab
  have ht := h t
  have h1 : t < b := by
    simp [t]
    rw [← gt_iff_lt]
    rw [Rudin.gt_div_gtz_iff_mul_gt]
    simp [Rudin.mul_add]
    exact hab
    linarith
  have h2 := ht.mpr h1
  simp [t] at h2
  rw [← gt_iff_lt] at h2
  rw [Rudin.gt_div_gtz_iff_mul_gt] at h2
  simp [Rudin.mul_add] at h2
  linarith
  linarith
  exact hab
  have h1 : t < a := by
    simp [t]
    rw [← gt_iff_lt]
    rw [Rudin.gt_div_gtz_iff_mul_gt]
    simp [Rudin.mul_add]
    exact hab
    linarith
  have ht := h t
  have h2 := ht.mp h1
  simp [t] at h2
  rw [← gt_iff_lt] at h2
  rw [Rudin.gt_div_gtz_iff_mul_gt] at h2
  simp [Rudin.mul_add] at h2
  linarith
  linarith
  intro h
  rw [h]
  intro x
  rfl


theorem exists_rat_btwn {a b:RR} (h: a < b) : ∃ r:Rat, a < r ∧ r < b := by
  -- pick p ∈ b \ a
  rcases Real.Cut.lt_then_ex_not_in_carrier (a:=a) (b:=b) h with ⟨p, hpB, hpNotA⟩
  -- pick t ∈ b with p < t
  rcases b.ex_gt hpB with ⟨t, htB, hpt⟩
  -- take the midpoint r = (p + t)/2
  let r : ℚ := (p + t) / (1+1)
  have two_pos : (0 : ℚ) < 2 := by norm_num

  -- p < r
  have hp_lt_r : p < r := by
    -- p < (p + t)/2  ↔  2 * p < p + t
    have h2 : (1+1) * p < p + t := by
      simp [Rudin.add_mul]
      exact hpt
    have : p < (p + t) / (1+1) := by
      rw [Rudin.lt_div_gtz_iff_mul_lt]
      simp [Rudin.mul_add]
      exact hpt
      linarith
    simpa [r] using this

  -- r < t
  have hr_lt_t : r < t := by
    -- (p + t)/2 < t  ↔  p + t < t * 2
    have h2 : p + t < t + t := by
      have : p + t < t + t := by linarith [hpt]
      simp
      exact hpt

    have : (p + t) / (1+1) < t := by
      rw [← gt_iff_lt]
      rw [Rudin.gt_div_gtz_iff_mul_gt]
      simp [Rudin.mul_add]
      exact hpt
      linarith
    simpa [r] using this

  -- show a < r
  have h_ar : a < (r : RR) := by
    -- a < OfRat r
    simp [Real.Cut.lt_def, OfRat, OfRatDef]  -- expand definitions
    constructor
    · -- ∀ x ∈ a, x < r
      intro x hx
      have hx_lt_p : x < p := a.in_lt_not_in hx hpNotA
      exact lt_trans hx_lt_p hp_lt_r
    · -- witness: p ∈ OfRat r and p ∉ a
      refine ⟨p, ?_, hpNotA⟩
      simpa [OfRat, OfRatDef] using hp_lt_r

  -- show r < b
  have h_rb : (r : RR) < b := by
    -- OfRat r < b
    simp [Real.Cut.lt_def, OfRat, OfRatDef]
    constructor
    · -- ∀ x < r, x ∈ b (since r < t and t ∈ b, b is downward closed)
      intro x hx
      have hx_lt_t : x < t := lt_trans hx hr_lt_t
      exact b.lt_then_in htB hx_lt_t
    · -- witness: t ∈ b and t ∉ OfRat r (since r < t)
      refine ⟨t, ?_, ?_⟩
      · exact htB
      · linarith

  exact ⟨r, h_ar, h_rb⟩

theorem exists_rat_gt {a:RR} : ∃ r:Rat, a < r := by
  let b := a + 1
  rcases exists_rat_btwn (a:=a) (b:=b) (by linarith) with ⟨ r, hr⟩
  use r
  exact hr.left


theorem exists_rat_lt {a:RR} : ∃ r:Rat, a > r := by
  let b := a - 1
  rcases exists_rat_btwn (a:=b) (b:=a) (by linarith) with ⟨ r, hr⟩
  use r
  exact hr.right


end Real


end Rudin
