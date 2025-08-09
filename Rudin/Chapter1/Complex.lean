import Mathlib
import Rudin.Chapter1.Real

#check Complex

namespace Rudin

structure Complex : Type where
  /-- The real part of a complex number. -/
  re : RR
  /-- The imaginary part of a complex number. -/
  im : RR

abbrev CC := Complex

namespace Complex

noncomputable instance : DecidableEq Complex :=
  Classical.decEq _

/-- The equivalence between the complex numbers and `RR × RR`. -/
@[simps apply]
def equivRealProd : CC ≃ RR × RR where
  toFun z := ⟨z.re, z.im⟩
  invFun p := ⟨p.1, p.2⟩

@[simp]
theorem eta : ∀ z : CC, Complex.mk z.re z.im = z
  | ⟨_, _⟩ => rfl

-- We only mark this lemma with `ext` *locally* to avoid it applying whenever terms of `Complex` appear.
theorem ext : ∀ {z w : CC}, z.re = w.re → z.im = w.im → z = w
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

attribute [local ext] Complex.ext

lemma «forall» {p : CC → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ := by aesop
lemma «exists» {p : CC → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ := by aesop

theorem re_surjective : Function.Surjective re := fun x => ⟨⟨x, 0⟩, rfl⟩

theorem im_surjective : Function.Surjective im := fun y => ⟨⟨0, y⟩, rfl⟩

@[simp]
theorem range_re : Set.range re = Set.univ :=
  re_surjective.range_eq

@[simp]
theorem range_im : Set.range im = Set.univ :=
  im_surjective.range_eq

/-- The natural inclusion of the real numbers into the complex numbers. -/
@[coe]
def OfReal (r : RR) : CC :=
  ⟨r, 0⟩


instance : Coe RR CC :=
  ⟨OfReal⟩


@[simp, norm_cast]
theorem ofReal_re (r : RR) : Complex.re (r : CC) = r :=
  rfl

@[simp, norm_cast]
theorem ofReal_im (r : RR) : (r : CC).im = 0 :=
  rfl

theorem ofReal_def (r : RR) : (r : CC) = ⟨r, 0⟩ :=
  rfl

@[simp, norm_cast]
theorem ofReal_inj {z w : RR} : (z : CC) = w ↔ z = w :=
  ⟨congrArg re, by apply congrArg⟩

theorem ofReal_injective : Function.Injective ((↑) : RR → CC) := fun _ _ => congrArg re

instance canLift : CanLift CC RR (↑) fun z => z.im = 0 where
  prf z hz := ⟨z.re, ext rfl hz.symm⟩


instance : Add Complex where add x y := ⟨ x.re + y.re, x.im + y.im⟩

theorem add_def {x y: CC} : x + y = ⟨ x.re + y.re, x.im + y.im⟩ := rfl

theorem add_comm {x y: CC} : x + y = y + x := by
  repeat rw [add_def]
  rw [Rudin.add_comm (a:=y.re), Rudin.add_comm (a:=y.im)]

theorem add_assoc {x y z: CC} : x + y + z = x + (y + z) := by
  repeat rw [add_def]
  repeat rw [Rudin.add_assoc]

instance : Sub Complex where sub x y := ⟨ x.re - y.re, x.im - y.im⟩

theorem sub_def {x y: CC} : x - y = ⟨ x.re - y.re, x.im - y.im⟩ := rfl

instance : Neg Complex where neg x := ⟨ -x.re, -x.im⟩

theorem neg_def {x: CC} : -x = ⟨ -x.re, -x.im⟩ := rfl

instance : Mul Complex where mul x y := ⟨ x.re*y.re - x.im*y.im, x.re*y.im + y.re*x.im⟩

theorem mul_def {x y: CC} : x * y = ⟨ x.re*y.re - x.im*y.im, x.re*y.im + y.re*x.im⟩ := rfl

theorem mul_comm {x y: CC} : x * y = y * x := by
  repeat rw [mul_def]
  ring_nf

theorem mul_assoc {x y z: CC} : x * y * z = x * (y * z) := by
  simp [mul_def]
  ring_nf
  simp

noncomputable instance : NatCast Complex where
  natCast n := (n : RR)

@[simp]
theorem natCast_eq_ofReal {n:Nat} : (n: CC) = OfReal n := rfl

instance : Zero Complex :=
  ⟨(0 :RR)⟩

instance : Inhabited Complex :=
  ⟨0⟩

@[simp]
theorem zero_re : (0 : CC).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : CC).im = 0 :=
  rfl

theorem zero_def : (0: CC) = ⟨ 0, 0 ⟩ := rfl

@[simp]
theorem zero_def' : Zero.zero = (0: CC) := rfl

@[simp, norm_cast]
theorem ofReal_zero : ((0 :RR) : CC) = 0 :=
  rfl

@[simp]
theorem ofReal_eq_zero {z :RR} : (z : CC) = 0 ↔ z = 0 :=
  ofReal_inj

theorem ofReal_ne_zero {z :RR} : (z : CC) ≠ 0 ↔ z ≠ 0 :=
  not_congr ofReal_eq_zero

instance : One Complex :=
  ⟨(1 :RR)⟩

@[simp]
theorem one_re : (1 : CC).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : CC).im = 0 :=
  rfl

@[simp, norm_cast]
theorem ofReal_one : ((1 :RR) : CC) = 1 :=
  rfl

theorem one_def : (1: CC) = ⟨ 1, 0 ⟩ := rfl

@[simp]
theorem one_def' : One.one = (1: CC) := rfl

theorem zero_add {x: CC} : 0 + x = x := by
  simp [add_def]




theorem nz_iff_re_nz_or_im_nz {x: CC} : x ≠ 0 ↔ x.re ≠ 0 ∨ x.im ≠ 0 := by
  constructor
  <;>intro h
  contrapose! h
  exact Complex.ext_iff.mpr h
  intro h1
  rcases h with h|h
  apply h
  exact
    (AddSemiconjBy.eq_zero_iff (re 0)
          (congrFun (congrArg HAdd.hAdd (congrArg re (id (Eq.symm h1)))) (re 0))).mp
      rfl
  apply h
  exact
    (AddSemiconjBy.eq_zero_iff (im 0)
          (congrFun (congrArg HAdd.hAdd (congrArg im (id (Eq.symm h1)))) (im 0))).mp
      rfl


theorem one_nz : (1: CC) ≠ (0: CC) := by
  refine nz_iff_re_nz_or_im_nz.mpr ?_
  left
  simp


theorem add_neg {x: CC} : x + (-x) = 0 := by
  simp [add_def, neg_def, zero_def]

theorem one_mul {x: CC} : One.one * x = x := by
  simp [One.one, mul_def]

theorem mul_add {x y z: CC} : x * (y + z) = x * y + x * z := by
  simp [add_def, mul_def]
  constructor
  ring_nf
  ring_nf

noncomputable instance : Inv Complex where inv x := ⟨x.re/(x.re*x.re + x.im*x.im), -x.im/(x.re*x.re + x.im*x.im)⟩

theorem inv_def {x: CC} : x⁻¹ = ⟨x.re/(x.re*x.re + x.im*x.im), -x.im/(x.re*x.re + x.im*x.im)⟩ := rfl

noncomputable instance : Div Complex where div x y := x * y⁻¹

theorem div_def {x y: CC} : x / y = x * y⁻¹ := by rfl

theorem mul_inv_when_nz {x: CC} (hx: x ≠ 0): x * x⁻¹ = 1 := by
  simp [inv_def, mul_def, one_def]
  simp [Rudin.mul_div_assoc]
  repeat rw [Rudin.div_eq_mul_inv]
  rw [← Rudin.add_mul]
  rw [Rudin.mul_inv]
  ring_nf
  exact ⟨trivial, trivial⟩
  ring_nf
  rcases nz_iff_re_nz_or_im_nz.mp hx with hx1|hx1
  have h1: x.re ^ 2 > 0 := by exact pow_two_pos_of_ne_zero hx1
  have h2: x.im ^ 2 ≥ 0 := by exact sq_nonneg x.im
  linarith
  have h1: x.re ^ 2 ≥  0 := by exact  sq_nonneg x.re
  have h2: x.im ^ 2 > 0 := by exact pow_two_pos_of_ne_zero hx1
  linarith

theorem inv_eq_one_div {x: CC} : x⁻¹ = 1 / x := by
  simp [inv_def, div_def, mul_def]

noncomputable instance instSMulComplexNat : SMul Nat Complex where
  smul n x := ⟨n*x.re, n*x.im⟩

theorem nat_mul_def {n:Nat} {a:CC} : n * a = ⟨ n*a.re, n*a.im⟩ := by
  simp [mul_def]

private noncomputable def PowComplexNat (a : CC) (n:ℕ) :=
  if n = 0
  then (1: CC)
  else a * PowComplexNat a (n-1)

noncomputable instance : Pow Complex Nat where pow x n := PowComplexNat x n

noncomputable instance : Field Complex where
  add_comm := fun a b ↦ add_comm
  add_assoc := fun a b c ↦ add_assoc
  zero_add := fun a ↦ zero_add
  add_neg := fun a ↦ add_neg
  mul_comm := fun a b ↦ mul_comm
  mul_assoc := fun a b c ↦ mul_assoc
  one_nz := one_nz
  one_mul := fun a ↦ one_mul
  mul_inv_when_nz := by
    simp
    exact fun a a_1 ↦ mul_inv_when_nz a_1
  mul_add := fun a b c ↦ mul_add
  sub_eq_add_neg := fun a b ↦ rfl
  div_eq_mul_inv := fun a b ↦ rfl
  inv_eq_one_div := by
    simp
    exact fun a ↦ inv_eq_one_div
  powNat_def := by
    intro a n
    by_cases hn : n = 0
    <;>simp [hn, HPow.hPow, Pow.pow]
    simp [PowComplexNat]
    rw [PowComplexNat]
    simp [hn]
    rw [mul_comm]

  natMul_def := by
    intro a n
    by_cases hn : n = 0
    <;>simp [hn]
    <;>simp [HSMul.hSMul, SMul.smul]
    rfl
    rw [add_def]
    have : (↑(n - 1):Rat) = n - 1 := by
      refine Nat.cast_pred ?_
      exact Nat.zero_lt_of_ne_zero hn
    simp [this]
    constructor
    rw [Rat.sub_eq_add_neg]
    rw [Real.ofRat_add_mul]
    rw (occs := .pos [4]) [← Rudin.one_mul (a:=a.re)]
    rw [← Real.neg_ofRat_eq]
    simp
    rw [Rat.sub_eq_add_neg]
    rw [Real.ofRat_add_mul]
    rw [← Real.neg_ofRat_eq]
    rw (occs := .pos [3]) [← Rudin.one_mul (a:=a.im)]
    simp


-- 1.26
theorem ofReal_add_ofReal_eq {a b:RR} : OfReal a + OfReal b = OfReal (a + b) := by
  simp [OfReal, add_def]

theorem ofReal_mul_ofReal_eq {a b:RR} : OfReal a * OfReal b = OfReal (a * b) := by
  simp [OfReal, mul_def]

-- 1.27
def I : CC := ⟨ 0, 1 ⟩

-- 1.28
theorem sqr_i_eq : I ^ 2 = -1 := by
  simp [I, mul_def, one_def, neg_def]

-- 1.29
theorem complex_add_format {a b:RR} : a + b * I = ⟨ a, b ⟩ := by
  simp [OfReal, add_def, I, mul_def]

-- 1.30
def Conjugate (z:CC) : CC := ⟨ z.re, -z.im ⟩

theorem conj_def {z:CC} : Conjugate z = ⟨ z.re, -z.im ⟩ := rfl

-- 1.31 a
theorem conj_add {z w:CC} : Conjugate (z + w) = Conjugate z + Conjugate w := by
  simp [conj_def, add_def]
  ring

-- 1.31 b
theorem conj_mul {z w:CC} : Conjugate (z * w) = Conjugate z * Conjugate w := by
  simp [conj_def, mul_def]
  ring

-- 1.31 c
theorem add_conj {z:CC} : z + Conjugate z = z.re + z.re := by
  simp [conj_def, add_def]

theorem sub_conj {z:CC} : z - Conjugate z = I * (z.im + z.im) := by
  simp [conj_def, sub_def, I, mul_def, add_def]

-- 1.31 d
theorem mul_conj_im_eq_zero {z:CC} : (z * Conjugate z).im = 0 := by
  simp [conj_def, mul_def]

theorem nz_then_mul_conj_re_gtz {z:CC} (hz: z ≠ 0): (z * Conjugate z).re > 0 := by
  simp [conj_def, mul_def]
  rcases nz_iff_re_nz_or_im_nz.mp hz with hz1|hz1
  have h1: z.re ^ 2 > 0 := by exact pow_two_pos_of_ne_zero hz1
  have h2: z.im ^ 2 ≥ 0 := by exact sq_nonneg z.im
  linarith
  have h1: z.re ^ 2 ≥  0 := by exact  sq_nonneg z.re
  have h2: z.im ^ 2 > 0 := by exact pow_two_pos_of_ne_zero hz1
  linarith

theorem mul_conj_re_gez {z:CC} : (z * Conjugate z).re ≥ 0 := by
  by_cases hz: z = 0
  simp [hz]
  exact lt_then_le (nz_then_mul_conj_re_gtz hz)

@[simp]
theorem ofReal_conj {r:RR} : Conjugate r = r := by
  simp [conj_def, OfReal]

-- 1.32
noncomputable def Abs (a:CC) : RR := Sqrt ((a * Conjugate a).re) (mul_conj_re_gez (z:=a))

theorem abs_def {a:CC} : Abs a = Sqrt ((a * Conjugate a).re) (mul_conj_re_gez) := rfl

theorem abs_def' {a:CC} : Abs a = Sqrt (a.re*a.re + a.im*a.im) (by
  refine Left.add_nonneg ?_ ?_
  exact mul_self_nonneg a.re
  exact mul_self_nonneg a.im
) := by
  simp [mul_def, conj_def, abs_def]

theorem abs_ofReal {r:RR} : Abs r = if r ≥ 0 then r else -r := by
  simp [abs_def, ofReal_mul_ofReal_eq]

-- 1.33 a
theorem nz_then_abs_gtz {z:CC} (hz: z ≠ 0): Abs z > 0 := by
  simp [abs_def, nz_then_mul_conj_re_gtz hz]

@[simp]
theorem abs_zero : Abs 0 = 0 := by simp [abs_def]

theorem abs_gez {z:CC} : Abs z ≥ 0 := by
  by_cases hz : z = 0
  apply Rudin.eq_then_le
  simp [hz]
  apply Rudin.lt_then_le
  exact nz_then_abs_gtz hz

--1.33 b
theorem abs_eq_abs_conj {z:CC} : Abs z = Abs (Conjugate z) := by
  simp [conj_def, abs_def, Rudin.mul_comm]

-- 1.33 c
theorem abs_mul_eq_mul_abs {z w:CC} : Abs (z * w) = Abs z * Abs w := by
  by_cases hz: z = 0
  simp [hz]
  by_cases hw: w = 0
  simp [hw]
  simp [mul_def, abs_def, conj_def]
  rw [← sqrt_mul]
  ring_nf

-- 1.33 d
theorem abs_re_le_abs {z:CC} : Abs z.re ≤ Abs z := by
  simp [abs_def, conj_def, mul_def]
  by_cases h : 0 ≤ z.re
  <;>simp [h]
  <;>have := sqrt_sqr' (a:=z.re)
  simp only [h, if_pos] at this
  rw (occs := .pos [1]) [← this]
  rw [sqrt_le_iff_le]
  simp
  exact mul_self_nonneg z.im
  simp only [ _root_.ge_iff_le, ge_iff_le, h, ↓reduceIte] at this
  rw (occs := .pos [1]) [← this]
  rw [sqrt_le_iff_le]
  simp
  exact mul_self_nonneg z.im



end Complex

end Rudin
