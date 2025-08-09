import Mathlib
import Rudin.Chapter1.Real

#check EReal

namespace Rudin

namespace EReal

def ExtendedReal := WithBot (WithTop RR)
  deriving Bot, Zero, One, Nontrivial

noncomputable instance : AddMonoid ExtendedReal := inferInstanceAs (AddMonoid (WithBot (WithTop RR)))
noncomputable instance : PartialOrder ExtendedReal := inferInstanceAs (PartialOrder (WithBot (WithTop RR)))
noncomputable instance : AddCommMonoid ExtendedReal := inferInstanceAs (AddCommMonoid (WithBot (WithTop RR)))

instance : ZeroLEOneClass ExtendedReal := inferInstanceAs (ZeroLEOneClass (WithBot (WithTop RR)))

noncomputable instance : LinearOrder ExtendedReal := inferInstanceAs (LinearOrder (WithBot (WithTop RR)))

instance : IsOrderedAddMonoid ExtendedReal := inferInstanceAs (IsOrderedAddMonoid (WithBot (WithTop RR)))

instance : IsOrderedAddMonoid ExtendedReal := inferInstanceAs (IsOrderedAddMonoid (WithBot (WithTop RR)))

noncomputable instance : AddCommMonoidWithOne ExtendedReal := inferInstanceAs (AddCommMonoidWithOne (WithBot (WithTop RR)))

instance : DenselyOrdered ExtendedReal := inferInstanceAs (DenselyOrdered (WithBot (WithTop RR)))

-- todo

end EReal

abbrev EReal := EReal.ExtendedReal
abbrev ERR := EReal.ExtendedReal

@[coe] def Real.toEReal : RR → EReal := WithBot.some ∘ WithTop.some

namespace EReal


noncomputable instance decidableLT : DecidableLT EReal := WithBot.decidableLT

instance : Top EReal := ⟨WithBot.some ⊤⟩

instance : Coe RR EReal := ⟨Real.toEReal⟩

theorem coe_strictMono : StrictMono Real.toEReal := WithBot.coe_strictMono.comp WithTop.coe_strictMono

@[simp, norm_cast]
protected theorem coe_le_coe_iff {x y : RR} : (x : EReal) ≤ (y : EReal) ↔ x ≤ y :=
  coe_strictMono.le_iff_le

@[gcongr] protected alias ⟨_, coe_le_coe⟩ := EReal.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_lt_coe_iff {x y : RR} : (x : EReal) < (y : EReal) ↔ x < y :=
  coe_strictMono.lt_iff_lt

@[gcongr] protected alias ⟨_, coe_lt_coe⟩ := EReal.coe_lt_coe_iff

theorem coe_injective : Function.Injective Real.toEReal := coe_strictMono.injective

@[simp, norm_cast]
protected theorem coe_eq_coe_iff {x y : RR} : (x : EReal) = (y : EReal) ↔ x = y :=
  coe_injective.eq_iff

protected theorem coe_ne_coe_iff {x y : RR} : (x : EReal) ≠ (y : EReal) ↔ x ≠ y :=
  coe_injective.ne_iff

@[simp, norm_cast]
protected theorem coe_natCast {n : ℕ} : ((n : RR) : EReal) = n := rfl

instance : Inhabited EReal := ⟨0⟩

@[simp, norm_cast]
theorem coe_zero : ((0 : RR) : EReal) = 0 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : RR) : EReal) = 1 := rfl

/-- A recursor for `EReal` in terms of the coercion.

When working in term mode, note that pattern matching can be used directly. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def rec {motive : EReal → Sort*}
    (bot : motive ⊥) (coe : ∀ a : RR, motive a) (top : motive ⊤) : ∀ a : EReal, motive a
  | ⊥ => bot
  | (a : RR) => coe a
  | ⊤ => top

protected lemma «forall» {p : EReal → Prop} : (∀ r, p r) ↔ p ⊥ ∧ p ⊤ ∧ ∀ r : RR, p r where
  mp h := ⟨h _, h _, fun _ ↦ h _⟩
  mpr h := EReal.rec h.1 h.2.2 h.2.1

protected lemma «exists» {p : EReal → Prop} : (∃ r, p r) ↔ p ⊥ ∨ p ⊤ ∨ ∃ r : RR, p r where
  mp := by rintro ⟨r, hr⟩; cases r <;> aesop
  mpr := by rintro (h | h | ⟨r, hr⟩) <;> exact ⟨_, ‹_›⟩

/-- The multiplication on `EReal`. Our definition satisfies `0 * x = x * 0 = 0` for any `x`, and
picks the only sensible value elsewhere. -/
protected noncomputable def mul : EReal → EReal → EReal
  | ⊥, ⊥ => ⊤
  | ⊥, ⊤ => ⊥
  | ⊥, (y : RR) => if 0 < y then ⊥ else if y = 0 then 0 else ⊤
  | ⊤, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | ⊤, (y : RR) => if 0 < y then ⊤ else if y = 0 then 0 else ⊥
  | (x : RR), ⊤ => if 0 < x then ⊤ else if x = 0 then 0 else ⊥
  | (x : RR), ⊥ => if 0 < x then ⊥ else if x = 0 then 0 else ⊤
  | (x : RR), (y : RR) => (x * y : RR)

noncomputable instance : Mul EReal := ⟨EReal.mul⟩

@[simp, norm_cast]
theorem coe_mul (x y : RR) : (↑(x * y) : EReal) = x * y :=
  rfl

/-- Induct on two `EReal`s by performing case splits on the sign of one whenever the other is
infinite. -/
@[elab_as_elim]
theorem induction₂ {P : EReal → EReal → Prop} (top_top : P ⊤ ⊤) (top_pos : ∀ x : RR, 0 < x → P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : ∀ x : RR, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (pos_top : ∀ x : RR, 0 < x → P x ⊤) (pos_bot : ∀ x : RR, 0 < x → P x ⊥) (zero_top : P 0 ⊤)
    (coe_coe : ∀ x y : RR, P x y) (zero_bot : P 0 ⊥) (neg_top : ∀ x : RR, x < 0 → P x ⊤)
    (neg_bot : ∀ x : RR, x < 0 → P x ⊥) (bot_top : P ⊥ ⊤) (bot_pos : ∀ x : RR, 0 < x → P ⊥ x)
    (bot_zero : P ⊥ 0) (bot_neg : ∀ x : RR, x < 0 → P ⊥ x) (bot_bot : P ⊥ ⊥) : ∀ x y, P x y
  | ⊥, ⊥ => bot_bot
  | ⊥, (y : RR) => by
    rcases Rudin.lt_trichotomy (a:=y) (b:=0) with (hy | rfl | hy)
    exacts [bot_neg y hy, bot_zero, bot_pos y hy]
  | ⊥, ⊤ => bot_top
  | (x : RR), ⊥ => by
    rcases Rudin.lt_trichotomy (a:=x) (b:=0) with (hx | rfl | hx)
    exacts [neg_bot x hx, zero_bot, pos_bot x hx]
  | (x : RR), (y : RR) => coe_coe _ _
  | (x : RR), ⊤ => by
    rcases Rudin.lt_trichotomy (a:=x) (b:=0) with (hx | rfl | hx)
    exacts [neg_top x hx, zero_top, pos_top x hx]
  | ⊤, ⊥ => top_bot
  | ⊤, (y : RR) => by
    rcases Rudin.lt_trichotomy (a:=y) (b:=0) with (hy | rfl | hy)
    exacts [top_neg y hy, top_zero, top_pos y hy]
  | ⊤, ⊤ => top_top

/-- Induct on two `EReal`s by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that the relation is symmetric. -/
@[elab_as_elim]
theorem induction₂_symm {P : EReal → EReal → Prop} (symm : ∀ {x y}, P x y → P y x)
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : RR, 0 < x → P ⊤ x) (top_zero : P ⊤ 0)
    (top_neg : ∀ x : RR, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥) (pos_bot : ∀ x : RR, 0 < x → P x ⊥)
    (coe_coe : ∀ x y : RR, P x y) (zero_bot : P 0 ⊥) (neg_bot : ∀ x : RR, x < 0 → P x ⊥)
    (bot_bot : P ⊥ ⊥) : ∀ x y, P x y :=
  @induction₂ P top_top top_pos top_zero top_neg top_bot (fun _ h => symm <| top_pos _ h)
    pos_bot (symm top_zero) coe_coe zero_bot (fun _ h => symm <| top_neg _ h) neg_bot (symm top_bot)
    (fun _ h => symm <| pos_bot _ h) (symm zero_bot) (fun _ h => symm <| neg_bot _ h) bot_bot

protected theorem mul_comm (x y : EReal) : x * y = y * x := by
  induction x <;> induction y  <;>
    try { rfl }
  rw [← coe_mul, ← coe_mul, mul_comm]

protected theorem one_mul : ∀ x : EReal, 1 * x = x
  | ⊤ => if_pos one_pos
  | ⊥ => if_pos one_pos
  | (x : RR) => congr_arg Real.toEReal (one_mul (a:=x))

protected theorem zero_mul : ∀ x : EReal, 0 * x = 0
  | ⊤ => (if_neg (lt_irrefl (a:=_))).trans (if_pos rfl)
  | ⊥ => (if_neg (lt_irrefl (a:=_))).trans (if_pos rfl)
  | (x : RR) => congr_arg Real.toEReal (zero_mul (a:=x))

noncomputable instance : MulZeroOneClass EReal where
  one_mul := EReal.one_mul
  mul_one := fun x => by rw [EReal.mul_comm, EReal.one_mul]
  zero_mul := EReal.zero_mul
  mul_zero := fun x => by rw [EReal.mul_comm, EReal.zero_mul]




/-! ### Real coercion -/

instance canLift : CanLift EReal RR (↑) fun r => r ≠ ⊤ ∧ r ≠ ⊥ where
  prf x hx := by
    induction x
    · simp at hx
    · simp
    · simp at hx

/-- The map from extended reals to reals sending infinities to zero. -/
def toReal : EReal → RR
  | ⊥ => 0
  | ⊤ => 0
  | (x : RR) => x

@[simp]
theorem toReal_top : toReal ⊤ = 0 :=
  rfl

@[simp]
theorem toReal_bot : toReal ⊥ = 0 :=
  rfl

@[simp]
theorem toReal_zero : toReal 0 = 0 :=
  rfl

@[simp]
theorem toReal_one : toReal 1 = 1 :=
  rfl

@[simp]
theorem toReal_coe (x : RR) : toReal (x : EReal) = x :=
  rfl

@[simp]
theorem bot_lt_coe (x : RR) : (⊥ : EReal) < x :=
  WithBot.bot_lt_coe _

@[simp]
theorem coe_ne_bot (x : RR) : (x : EReal) ≠ ⊥ :=
  (bot_lt_coe x).ne'

@[simp]
theorem bot_ne_coe (x : RR) : (⊥ : EReal) ≠ x :=
  (bot_lt_coe x).ne

@[simp]
theorem coe_lt_top (x : RR) : (x : EReal) < ⊤ :=
  WithBot.coe_lt_coe.2 <| WithTop.coe_lt_top _

@[simp]
theorem coe_ne_top (x : RR) : (x : EReal) ≠ ⊤ :=
  (coe_lt_top x).ne

@[simp]
theorem top_ne_coe (x : RR) : (⊤ : EReal) ≠ x :=
  (coe_lt_top x).ne'

@[simp]
theorem bot_lt_zero : (⊥ : EReal) < 0 :=
  bot_lt_coe 0

@[simp]
theorem bot_ne_zero : (⊥ : EReal) ≠ 0 :=
  (coe_ne_bot 0).symm

@[simp]
theorem zero_ne_bot : (0 : EReal) ≠ ⊥ :=
  coe_ne_bot 0

@[simp]
theorem zero_lt_top : (0 : EReal) < ⊤ :=
  coe_lt_top 0

@[simp]
theorem zero_ne_top : (0 : EReal) ≠ ⊤ :=
  coe_ne_top 0

@[simp]
theorem top_ne_zero : (⊤ : EReal) ≠ 0 :=
  (coe_ne_top 0).symm

theorem range_coe : Set.range Real.toEReal = {⊥, ⊤}ᶜ := by
  ext x
  induction x <;> simp

theorem range_coe_eq_Ioo : Set.range Real.toEReal = Set.Ioo ⊥ ⊤ := by
  ext x
  induction x <;> simp

@[simp, norm_cast]
theorem coe_add (x y : RR) : (↑(x + y) : EReal) = x + y :=
  rfl

-- `coe_mul` moved up

@[norm_cast]
theorem coe_nsmul (n : ℕ) (x : RR) : (↑(n • x) : EReal) = n • (x : EReal) :=
  map_nsmul (⟨⟨Real.toEReal, coe_zero⟩, coe_add⟩ : RR →+ EReal) _ _

@[simp, norm_cast]
theorem coe_eq_zero {x : RR} : (x : EReal) = 0 ↔ x = 0 :=
  EReal.coe_eq_coe_iff

@[simp, norm_cast]
theorem coe_eq_one {x : RR} : (x : EReal) = 1 ↔ x = 1 :=
  EReal.coe_eq_coe_iff

theorem coe_ne_zero {x : RR} : (x : EReal) ≠ 0 ↔ x ≠ 0 :=
  EReal.coe_ne_coe_iff

theorem coe_ne_one {x : RR} : (x : EReal) ≠ 1 ↔ x ≠ 1 :=
  EReal.coe_ne_coe_iff

@[simp, norm_cast]
protected theorem coe_nonneg {x : RR} : (0 : EReal) ≤ x ↔ 0 ≤ x :=
  EReal.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_nonpos {x : RR} : (x : EReal) ≤ 0 ↔ x ≤ 0 :=
  EReal.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_pos {x : RR} : (0 : EReal) < x ↔ 0 < x :=
  EReal.coe_lt_coe_iff

@[simp, norm_cast]
protected theorem coe_neg' {x : RR} : (x : EReal) < 0 ↔ x < 0 :=
  EReal.coe_lt_coe_iff

lemma toReal_eq_zero_iff {x : EReal} : x.toReal = 0 ↔ x = 0 ∨ x = ⊤ ∨ x = ⊥ := by
  cases x <;> norm_num

lemma toReal_ne_zero_iff {x : EReal} : x.toReal ≠ 0 ↔ x ≠ 0 ∧ x ≠ ⊤ ∧ x ≠ ⊥ := by
  simp only [ne_eq, toReal_eq_zero_iff, not_or]

lemma toReal_eq_toReal {x y : EReal} (hx_top : x ≠ ⊤) (hx_bot : x ≠ ⊥)
    (hy_top : y ≠ ⊤) (hy_bot : y ≠ ⊥) :
    x.toReal = y.toReal ↔ x = y := by
  lift x to RR using ⟨hx_top, hx_bot⟩
  lift y to RR using ⟨hy_top, hy_bot⟩
  simp

lemma toReal_nonneg {x : EReal} (hx : 0 ≤ x) : 0 ≤ x.toReal := by
  cases x
  · norm_num
  · exact toReal_coe _ ▸ EReal.coe_nonneg.mp hx
  · norm_num

lemma toReal_nonpos {x : EReal} (hx : x ≤ 0) : x.toReal ≤ 0 := by
  cases x
  · norm_num
  · exact toReal_coe _ ▸ EReal.coe_nonpos.mp hx
  · norm_num

instance : OrderBot EReal where
  bot_le := by
    intro x
    induction' x with x
    · exact le_rfl
    · exact (bot_lt_coe x).le
    · exact (bot_lt_zero.trans zero_lt_top).le

instance : OrderTop EReal where
  le_top := by
    intro x
    induction' x with x
    · exact (bot_le : (⊥ : EReal) ≤ ⊤)
    · exact le_of_lt (coe_lt_top x)
    · exact le_rfl


@[simp]
theorem bot_lt_top : (⊥:EReal) < ⊤ := by
  let t := (0:EReal)
  have h1: ⊤ > t := by exact zero_lt_top
  exact bot_lt_of_lt h1

@[simp]
theorem bot_ne_top : (⊥:EReal) ≠ ⊤ := by
  intro h
  have h2: (⊥:EReal) < ⊤ := by exact bot_lt_top
  rw [h] at h2
  exact (lt_self_iff_false ⊤).mp h2

@[simp]
theorem top_ne_bot : ⊤ ≠ (⊥:EReal) := bot_ne_top.symm


noncomputable instance : Ordered EReal where
  lt_trans := by exact fun a b c a_1 a_2 ↦ gt_trans a_2 a_1
  le_iff_lt_or_eq := by exact fun {a b} ↦ _root_.le_iff_lt_or_eq
  lt_trichotomy_complete := by
    intro a b
    induction' a with a
    · simp
      induction' b with b
      · right
        simp
      · left
        simp
      · left
        constructor
        exact compareOfLessAndEq_eq_lt.mp rfl
        simp
    · induction' b with b
      simp
      rcases Rudin.lt_trichotomy (a:=a) (b:=b) with (h | h | h)
      <;>simp [h]
      exact le_of_lt h
      exact le_of_lt h
      simp
    · simp
      induction' b with b
      right
      constructor
      simp
      simp
      right
      constructor
      simp
      simp
      left
      constructor
      simp
      simp



theorem toReal_le_toReal {x y : EReal} (h : x ≤ y) (hx : x ≠ ⊥) (hy : y ≠ ⊤) :
    x.toReal ≤ y.toReal := by
  lift x to RR using ⟨ne_top_of_le_ne_top hy h, hx⟩
  lift y to RR using ⟨hy, ne_bot_of_le_ne_bot hx h⟩
  simpa using h

theorem coe_toReal {x : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) : (x.toReal : EReal) = x := by
  lift x to RR using ⟨hx, h'x⟩
  rfl

theorem le_coe_toReal {x : EReal} (h : x ≠ ⊤) : x ≤ x.toReal := by
  by_cases h' : x = ⊥
  · simp only [h', bot_le]
  · simp only [le_refl, coe_toReal h h']

theorem coe_toReal_le {x : EReal} (h : x ≠ ⊥) : ↑x.toReal ≤ x := by
  by_cases h' : x = ⊤
  · simp only [h', le_top]
  · simp only [le_refl, coe_toReal h' h]

theorem eq_top_iff_forall_lt (x : EReal) : x = ⊤ ↔ ∀ y : RR, (y : EReal) < x := by
  constructor
  · rintro rfl
    exact EReal.coe_lt_top
  · contrapose!
    intro h
    exact ⟨x.toReal, le_coe_toReal h⟩

theorem eq_bot_iff_forall_lt (x : EReal) : x = ⊥ ↔ ∀ y : RR, x < (y : EReal) := by
  constructor
  · rintro rfl
    exact bot_lt_coe
  · contrapose!
    intro h
    exact ⟨x.toReal, coe_toReal_le h⟩

/-! ### Intervals and coercion from reals -/

lemma exists_between_coe_real {x z : EReal} (h : x < z) : ∃ y : RR, x < y ∧ y < z := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h
  induction a with
  | bot => exact (not_lt_bot ha₁).elim
  | coe a₀ => exact ⟨a₀, ha₁, ha₂⟩
  | top => exact (not_top_lt ha₂).elim

open Set

@[simp]
lemma image_coe_Icc (x y : RR) : Real.toEReal '' Icc x y = Icc ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Icc, WithBot.image_coe_Icc]
  rfl

@[simp]
lemma image_coe_Ico (x y : RR) : Real.toEReal '' Ico x y = Ico ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ico, WithBot.image_coe_Ico]
  rfl

@[simp]
lemma image_coe_Ici (x : RR) : Real.toEReal '' Ici x = Ico ↑x ⊤ := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ici, WithBot.image_coe_Ico]
  rfl

@[simp]
lemma image_coe_Ioc (x y : RR) : Real.toEReal '' Ioc x y = Ioc ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioc, WithBot.image_coe_Ioc]
  rfl

@[simp]
lemma image_coe_Ioo (x y : RR) : Real.toEReal '' Ioo x y = Ioo ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioo, WithBot.image_coe_Ioo]
  rfl

@[simp]
lemma image_coe_Ioi (x : RR) : Real.toEReal '' Ioi x = Ioo ↑x ⊤ := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioi, WithBot.image_coe_Ioo]
  rfl

@[simp]
lemma image_coe_Iic (x : RR) : Real.toEReal '' Iic x = Ioc ⊥ ↑x := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iic, WithBot.image_coe_Iic]
  rfl

@[simp]
lemma image_coe_Iio (x : RR) : Real.toEReal '' Iio x = Ioo ⊥ ↑x := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iio, WithBot.image_coe_Iio]
  rfl

@[simp]
lemma preimage_coe_Ici (x : RR) : Real.toEReal ⁻¹' Ici x = Ici x := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ici (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ici, WithTop.preimage_coe_Ici]

@[simp]
lemma preimage_coe_Ioi (x : RR) : Real.toEReal ⁻¹' Ioi x = Ioi x := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ioi (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi, WithTop.preimage_coe_Ioi]

@[simp]
lemma preimage_coe_Ioi_bot : Real.toEReal ⁻¹' Ioi ⊥ = univ := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ioi ⊥) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi_bot, preimage_univ]

@[simp]
lemma preimage_coe_Iic (y : RR) : Real.toEReal ⁻¹' Iic y = Iic y := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iic (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iic, WithTop.preimage_coe_Iic]

@[simp]
lemma preimage_coe_Iio (y : RR) : Real.toEReal ⁻¹' Iio y = Iio y := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio]

@[simp]
lemma preimage_coe_Iio_top : Real.toEReal ⁻¹' Iio ⊤ = univ := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some ⊤)) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio_top]

@[simp]
lemma preimage_coe_Icc (x y : RR) : Real.toEReal ⁻¹' Icc x y = Icc x y := by
  simp_rw [← Ici_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ico (x y : RR) : Real.toEReal ⁻¹' Ico x y = Ico x y := by
  simp_rw [← Ici_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioc (x y : RR) : Real.toEReal ⁻¹' Ioc x y = Ioc x y := by
  simp_rw [← Ioi_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ioo (x y : RR) : Real.toEReal ⁻¹' Ioo x y = Ioo x y := by
  simp_rw [← Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ico_top (x : RR) : Real.toEReal ⁻¹' Ico x ⊤ = Ici x := by
  rw [← Ici_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioo_top (x : RR) : Real.toEReal ⁻¹' Ioo x ⊤ = Ioi x := by
  rw [← Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioc_bot (y : RR) : Real.toEReal ⁻¹' Ioc ⊥ y = Iic y := by
  rw [← Ioi_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ioo_bot (y : RR) : Real.toEReal ⁻¹' Ioo ⊥ y = Iio y := by
  rw [← Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioo_bot_top : Real.toEReal ⁻¹' Ioo ⊥ ⊤ = univ := by
  rw [← Ioi_inter_Iio]
  simp

/-! ### nat coercion -/

theorem coe_coe_eq_natCast (n : ℕ) : (n : RR) = (n : EReal) := rfl

theorem natCast_ne_bot (n : ℕ) : (n : EReal) ≠ ⊥ := by
  refine bot_lt_iff_ne_bot.mp ?_
  exact compareOfLessAndEq_eq_lt.mp rfl

theorem natCast_ne_top (n : ℕ) : (n : EReal) ≠ ⊤ := by
  refine lt_top_iff_ne_top.mp ?_
  exact compareOfLessAndEq_eq_lt.mp rfl

@[norm_cast]
theorem natCast_eq_iff {m n : ℕ} : (m : EReal) = (n : EReal) ↔ m = n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, EReal.coe_eq_coe_iff, Nat.cast_inj]

theorem natCast_ne_iff {m n : ℕ} : (m : EReal) ≠ (n : EReal) ↔ m ≠ n :=
  not_iff_not.2 natCast_eq_iff

@[norm_cast]
theorem natCast_le_iff {m n : ℕ} : (m : EReal) ≤ (n : EReal) ↔ m ≤ n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, EReal.coe_le_coe_iff, Nat.cast_le]

@[norm_cast]
theorem natCast_lt_iff {m n : ℕ} : (m : EReal) < (n : EReal) ↔ m < n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, EReal.coe_lt_coe_iff, Nat.cast_lt]

@[simp, norm_cast]
theorem natCast_mul (m n : ℕ) :
    (m * n : ℕ) = (m : EReal) * (n : EReal) := by
  rw [← coe_coe_eq_natCast, ← coe_coe_eq_natCast, ← coe_coe_eq_natCast, Nat.cast_mul, EReal.coe_mul]

/-! ### Miscellaneous lemmas -/

theorem exists_rat_btwn_of_lt :
    ∀ {a b : EReal}, a < b → ∃ x : ℚ, a < (x : RR) ∧ ((x : RR) : EReal) < b
  | ⊤, _, h => (not_top_lt h).elim
  | (a : RR), ⊥, h =>  by
    let ⟨b, hab⟩ := Rudin.Real.exists_rat_gt (a:=a)
    use b
    constructor
    exact EReal.coe_lt_coe hab
    contrapose! h
    apply Rudin.lt_then_le
    exact bot_lt_coe a

  | (a : RR), (b : RR), h => by
    simp [Rudin.Real.exists_rat_btwn (EReal.coe_lt_coe_iff.1 h)]

  | (a : RR), ⊤, _ =>
    let ⟨b, hab⟩ := Rudin.Real.exists_rat_gt (a:=a)
    ⟨b, by simpa using hab, coe_lt_top _⟩
  | ⊥, ⊥, h => by
    use 0
    constructor
    <;>simp
    exact (lt_self_iff_false ⊥).mp h
  | ⊥, (a : RR), _ =>
    let ⟨b, hab⟩ := Rudin.Real.exists_rat_lt (a:=a)
    ⟨b, bot_lt_coe _, by simpa using hab⟩
  | ⊥, ⊤, _ => ⟨0, bot_lt_coe _, coe_lt_top _⟩

theorem lt_iff_exists_rat_btwn {a b : EReal} :
    a < b ↔ ∃ x : ℚ, a < (x : RR) ∧ ((x : RR) : EReal) < b :=
  ⟨fun hab => exists_rat_btwn_of_lt hab, fun ⟨_x, ax, xb⟩ => ax.trans xb⟩

theorem lt_iff_exists_real_btwn {a b : EReal} : a < b ↔ ∃ x : RR, a < x ∧ (x : EReal) < b :=
  ⟨fun hab =>
    let ⟨x, ax, xb⟩ := exists_rat_btwn_of_lt hab
    ⟨(x : RR), ax, xb⟩,
    fun ⟨_x, ax, xb⟩ => ax.trans xb⟩

/-- The set of numbers in `EReal` that are not equal to `±∞` is equivalent to `RR`. -/
def neTopBotEquivReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ RR where
  toFun x := EReal.toReal x
  invFun x := ⟨x, by simp⟩
  left_inv := fun ⟨x, hx⟩ => by
    lift x to RR
    · simpa [not_or, and_comm] using hx
    · simp
  right_inv x := by simp


end EReal

end Rudin
