import Mathlib
import Rudin.Chapter1.Real
import Rudin.Chapter1.FinsetIdentity

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

theorem add_re {x y:CC} : (x + y).re = x.re + y.re := by simp [add_def]
theorem add_im {x y:CC} : (x + y).im = x.im + y.im := by simp [add_def]

instance : Sub Complex where sub x y := ⟨ x.re - y.re, x.im - y.im⟩

theorem sub_def {x y: CC} : x - y = ⟨ x.re - y.re, x.im - y.im⟩ := rfl

theorem sub_re {x y:CC} : (x - y).re = x.re - y.re := by simp [sub_def]
theorem sub_im {x y:CC} : (x - y).im = x.im - y.im := by simp [sub_def]

instance : Neg Complex where neg x := ⟨ -x.re, -x.im⟩

theorem neg_def {x: CC} : -x = ⟨ -x.re, -x.im⟩ := rfl

theorem neg_re {x:CC} : (-x).re = - (x.re) := by simp [neg_def]
theorem neg_im {x:CC} : (-x).im = - (x.im) := by simp [neg_def]

instance : Mul Complex where mul x y := ⟨ x.re*y.re - x.im*y.im, x.re*y.im + y.re*x.im⟩

theorem mul_def {x y: CC} : x * y = ⟨ x.re*y.re - x.im*y.im, x.re*y.im + y.re*x.im⟩ := rfl

theorem mul_re {x y:CC} : (x * y).re = x.re*y.re - x.im*y.im := by simp [mul_def]
theorem mul_im {x y:CC} : (x * y).im = x.re*y.im + y.re*x.im := by simp [mul_def]


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

@[simp]
theorem ofReal_mul_ofReal_re {a b:RR} : (OfReal a * OfReal b).re = a * b := by
  simp [mul_re]

@[simp]
theorem ofReal_mul_re {a:RR} {b:CC} : ((OfReal a) * b).re = a * b.re := by
  simp [mul_re]

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

postfix:1024 "ᶜ" => Complex.Conjugate   -- use zᶜ (\^c)

theorem conj_def {z:CC} : zᶜ = ⟨ z.re, -z.im ⟩ := rfl

@[simp]
theorem conj_conj {z:CC}: zᶜᶜ = z := by
  simp [conj_def]

-- 1.31 a
theorem conj_add {z w:CC} : (z + w)ᶜ = zᶜ + wᶜ := by
  simp [conj_def, add_def]
  ring

-- 1.31 b
theorem conj_mul {z w:CC} : (z * w)ᶜ = zᶜ * wᶜ  := by
  simp [conj_def, mul_def]
  ring

-- 1.31 c
theorem add_conj {z:CC} : z + zᶜ = z.re + z.re := by
  simp [conj_def, add_def]

theorem sub_conj {z:CC} : z - zᶜ = I * (z.im + z.im) := by
  simp [conj_def, sub_def, I, mul_def, add_def]

-- 1.31 d
theorem mul_conj {z:CC} : z * zᶜ = z.re * z.re + z.im * z.im := by
  simp [conj_def, mul_def, add_def]

theorem mul_conj_im_eq_zero {z:CC} : (z * zᶜ).im = 0 := by
  simp [conj_def, mul_def]


theorem nz_then_mul_conj_re_gtz {z:CC} (hz: z ≠ 0): (z * zᶜ).re > 0 := by
  simp [conj_def, mul_def]
  rcases nz_iff_re_nz_or_im_nz.mp hz with hz1|hz1
  have h1: z.re ^ 2 > 0 := by exact pow_two_pos_of_ne_zero hz1
  have h2: z.im ^ 2 ≥ 0 := by exact sq_nonneg z.im
  linarith
  have h1: z.re ^ 2 ≥  0 := by exact  sq_nonneg z.re
  have h2: z.im ^ 2 > 0 := by exact pow_two_pos_of_ne_zero hz1
  linarith

theorem mul_conj_re_gez {z:CC} : (z * zᶜ).re ≥ 0 := by
  by_cases hz: z = 0
  simp [hz]
  exact lt_then_le (nz_then_mul_conj_re_gtz hz)

@[simp]
theorem conj_ofReal {r:RR} : rᶜ = r := by
  simp [conj_def, OfReal]

@[simp]
theorem conj_zero : Conjugate 0 = 0 := by
  simp [conj_def, zero_def]

-- 1.32
noncomputable def Abs (a:CC) : RR := Sqrt ((a * aᶜ).re) (mul_conj_re_gez (z:=a))

theorem abs_def {a:CC} : Abs a = Sqrt ((a * aᶜ).re) (mul_conj_re_gez) := rfl

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

@[simp]
theorem abs_gez {z:CC} : Abs z ≥ 0 := by
  by_cases hz : z = 0
  apply Rudin.eq_then_le
  simp [hz]
  apply Rudin.lt_then_le
  exact nz_then_abs_gtz hz


@[simp]
theorem abs_eq_zero_iff_zero {z:CC} : Abs z = 0 ↔ z = 0 := by
  constructor
  <;>intro h
  contrapose! h
  apply nz_then_abs_gtz at h
  linarith
  simp [h]

--1.33 b
@[simp]
theorem abs_conj {z:CC} :   Abs (zᶜ)  = Abs z := by
  simp [conj_def, abs_def, Rudin.mul_comm]

-- 1.33 c
theorem abs_mul {z w:CC} : Abs (z * w) = Abs z * Abs w := by
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

theorem mul_conj_eq_sqr_abs {z:CC} : z * zᶜ = (Abs z) ^ 2 := by
  simp [abs_def, mul_def, conj_def]

theorem conj_mul_eq_sqr_abs {z:CC} : zᶜ * z = (Abs z) ^ 2 := by
  simp [Rudin.mul_comm, mul_conj_eq_sqr_abs]

theorem sqr_abs_eq {z:CC} : (Abs z) ^ 2 = (z * zᶜ).re := by
  simp [abs_def, mul_def, conj_def]

theorem conj_conj_mul_eq {z w:CC} : (zᶜ * w)ᶜ = z * wᶜ := by
  simp [conj_def, mul_def]
  ring_nf

theorem mul_conj_add_conj_mul_eq {z w:CC} : (zᶜ * w + z * wᶜ).re = (zᶜ * w).re + (zᶜ * w).re := by
  simp [conj_def, mul_def, add_def]

theorem ofReal_le_abs_ofReal {r:RR} : r ≤ Abs r := by
  simp [abs_ofReal]
  split_ifs with h
  exact fun ⦃a⦄ a ↦ a
  simp at h
  have h1: -r > 0 := by exact Left.neg_pos_iff.mpr h
  apply lt_then_le
  exact lt_trans h h1

theorem conj_mul_conj_eq {z w:CC} : (z * wᶜ)ᶜ = zᶜ * w := by
  simp [conj_def, mul_def]
  ring


-- 1.33 e
theorem abs_add_le_add_abs {z w:CC}: Abs (z+w) ≤ Abs z + Abs w := by
  have : (Abs (z + w)) ^ 2 ≤ (Abs z + Abs w) ^ 2 := by
    rw [sqr_abs_eq (z:=z+w)]
    simp [conj_add, mul_add, add_mul, add_re, ← sqr_abs_eq]
    rw [← Rudin.add_assoc]
    rw [Rudin.add_assoc (a:=Abs z * Abs z) (b:=(z * wᶜ).re)  (c:=((w * zᶜ).re)), ← add_re (x:=z * wᶜ) (y:=(w * zᶜ))]
    repeat rw [Rudin.mul_add]
    rw [← Rudin.add_assoc]
    repeat rw [Rudin.add_assoc (a:= Abs z * Abs z)]
    simp
    rw [Rudin.mul_comm, mul_conj_add_conj_mul_eq]
    repeat rw [← abs_mul]
    repeat rw [Rudin.mul_comm (b:=z)]
    ring_nf
    simp
    have  h1 : (z * wᶜ).re ≤ Abs ((z * wᶜ).re) := by
      exact ofReal_le_abs_ofReal
    have h2 : Abs ((z * wᶜ).re) ≤ Abs (z *wᶜ) := by exact abs_re_le_abs
    have h3 : Abs (z *wᶜ) = Abs (z * w) := by
      rw [abs_mul, abs_conj]
      rw [abs_mul]
    linarith
  apply gez_powNat_le_gez_powNat_iff_le at this
  exact this
  simp
  simp
  refine Left.add_nonneg ?_ ?_
  simp
  simp
  simp

theorem sqr_abs_eq_abs_mul_abs_conj {z:CC} : (Abs z)^2 = Abs z * Abs (zᶜ) := by
  simp

@[simp]
theorem conj_neg {z:CC} : (-z)ᶜ = - zᶜ := by
  simp [conj_def, neg_def]

-- 1.34 cauchy-schwarz
open Finset in
theorem sum_re_eq_re_sum {n:Nat} {a:Nat → CC} : ∑ i ∈ range n, (a i).re = re (∑ i ∈ range n, a i) := by
  have h1 := sum_distribute (p := fun (x:CC) => x.re) (hp := by
    simp
    intro x y
    simp [add_re]
  ) (n:=n) (a:=a)
  exact h1.symm

open Finset in
theorem sum_ofReal_eq_ofReal_sum {n:Nat} {a:Nat → RR} : ∑ i ∈ range n, ((a i) : Complex) = OfReal (∑ i in range n, (a i)) := by
  have h1 := sum_distribute (p := fun (x:RR) => OfReal x) (hp := by
    simp
    intro x y
    exact Eq.symm ofReal_add_ofReal_eq
  ) (n:=n) (a:=a)
  exact h1.symm

open Finset in
theorem conj_sum_eq_sum_conj {n:Nat} {a:Nat → CC} : (∑ i ∈ range n, (a i))ᶜ = ∑ i ∈ range n, (a i)ᶜ := by
  have h1 := sum_distribute (p := fun (x:CC) => xᶜ) (hp := by
    simp
    intro x y
    exact conj_add
  ) (n:=n) (a:=a)
  exact h1

open Finset in
theorem sqr_abs_sum_mul_conj_le_mul_sum_sqr_abs {n:Nat} {a b:Nat → CC}:
  Abs (∑ i ∈ range n, (a i)* (b i)ᶜ) ^ 2 ≤
  (∑ i ∈ range n, (Abs (a i)) ^ 2) * (∑ i ∈ range n, (Abs (b i)) ^ 2) := by
  let A := (∑ i ∈ range n, (Abs (a i)) ^ 2)
  have ha: A = (∑ i ∈ range n, (Abs (a i)) ^ 2) := rfl
  let B := (∑ i ∈ range n, (Abs (b i)) ^ 2)
  have hb: B = (∑ i ∈ range n, (Abs (b i)) ^ 2) := rfl
  let C := ∑ i ∈ range n, (a i)* (b i)ᶜ
  have hc : C = ∑ i ∈ range n, (a i)* (b i)ᶜ := rfl
  rw [← ha, ← hb, ← hc]
  by_cases hb0: B = 0
  have hb1 := hb0
  rw [hb] at hb0
  rw [sum_sqr_eq_zero_iff_eq_zero] at hb0
  have h1: ∀ i ∈ range n, a i * (b i)ᶜ = 0 := by
    intro i hi
    have h2:= hb0 i hi
    simp at h2
    rw [h2]
    simp [conj_zero]

  have h2:C = 0 := by
    simp [C]
    rw [Finset.sum_eq_zero]
    exact h1
  rw [h2, hb1]
  simp
  let t := ∑ i ∈ range n, (Abs (B * (a i) - C * (b i))) ^ 2
  have ht : t = ∑ i ∈ range n, (Abs (B * (a i) - C * (b i))) ^ 2 := rfl
  have htz : t ≥ 0 := by
    rw [ht]
    refine Finset.sum_nonneg ?_
    intro i hi
    exact sqr_gez
  have hbgez : B ≥ 0 := by
    rw [hb]
    apply Finset.sum_nonneg
    intro i h
    exact sqr_gez
  have hbgz : B > 0 := by exact lt_of_le_of_ne hbgez fun a ↦ hb0 (id (Eq.symm a))
  have : t = B * (A * B - (Abs C)^2) := by
    rw [ht]
    have : ∑ i ∈ range n, Abs (↑B * a i - C * b i) ^ 2 = ∑ i ∈ range n, ((B * a i - C * b i) * (B * a i - C * b i)ᶜ).re := by
      refine func_eq_then_range_sum_eq_range_sum ?_
      exact fun i a_1 ↦ sqr_abs_eq
    rw [this]
    have : ∀ i ∈ range n, (B * a i - C * b i) * (B * a i - C * b i)ᶜ =
      B^2 *(Abs (a i))^2 - B * Cᶜ * (a i) * (b i)ᶜ - B * C * (a i)ᶜ * (b i) + (Abs C) ^ 2 * (Abs (b i))^2 := by
      intro i hi
      simp only [← mul_assoc, Rudin.sub_eq_add_neg, conj_add, mul_add, add_mul, conj_mul]
      have :  B * a i * (B)ᶜ * (a i)ᶜ =  ↑B ^ 2 * ↑(Abs (a i)) ^ 2 := by
        rw [Rudin.mul_comm (b:=Bᶜ), ← Rudin.mul_assoc]
        rw [Rudin.mul_assoc]
        rw [mul_conj (z:=a i)]
        rw [Rudin.mul_comm (a:=Bᶜ) (b:=↑B)]
        rw [mul_conj]
        simp [ofReal_add_ofReal_eq, ofReal_re, ofReal_im, ofReal_zero, abs_def, mul_conj, ofReal_mul_ofReal_eq]
      rw [this]
      repeat rw [Rudin.add_assoc (a:=((B:CC) ^ 2 * Abs (a i) ^ 2 ))]
      rw [Rudin.add_eq_left_cancel]
      have : ↑B * a i * (-(C * b i))ᶜ =  -(↑B * Cᶜ * a i * (b i)ᶜ) := by
        rw [conj_neg, mul_neg, conj_mul]
        ring_nf
      rw [this]
      repeat rw [Rudin.add_assoc (a:=-(↑B * Cᶜ * a i * (b i)ᶜ))]
      rw [Rudin.add_eq_left_cancel]
      have : -(C * b i) * (B)ᶜ * (a i)ᶜ = -(↑B * C * (a i)ᶜ * b i) := by
        simp [conj_ofReal]
        ring_nf
      rw [this]
      rw [Rudin.add_eq_left_cancel]
      rw [conj_neg, conj_mul, neg_mul_neg, ←mul_assoc]
      rw [Rudin.mul_comm (a:=C), Rudin.mul_assoc (c:=Cᶜ)]
      rw [Rudin.mul_comm, ← mul_assoc]
      rw [Rudin.mul_comm (b:=b i)]
      simp only [mul_conj_eq_sqr_abs]
      ring_nf
    have hsum :
        ∑ i ∈ range n, ((B * a i - C * b i) * (B * a i - C * b i)ᶜ).re
          =
        ∑ i ∈ range n,
          (B^2 *(Abs (a i))^2 - B * Cᶜ * (a i) * (b i)ᶜ - B * C * (a i)ᶜ * (b i) + (Abs C) ^ 2 * (Abs (b i))^2).re := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      -- 用 congrArg 取实部后 simpa
      simpa using congrArg Complex.re (this i hi)
    -- 用得到的求和等式改写
    rw [hsum]
    rw [sum_re_eq_re_sum]
    simp only [Rudin.sub_eq_add_neg, ← sum_add_distribute, add_re, ← mul_sum]
    have : ∑ i ∈ range n, ((Abs (a i)):Complex) ^ 2 = (A:Complex) := by
      simp [ha]
      rw [← sum_ofReal_eq_ofReal_sum]
      simp [← ofReal_mul_ofReal_eq]

    rw [this]
    have : ((B:Complex) ^ 2 * (↑A:Complex)).re = B ^ 2 * A := by simp [mul_re]
    rw [this]
    rw [Rudin.mul_add]
    ring_nf
    rw [Rudin.add_comm (b:=B ^ 2 * A)]
    repeat rw [Rudin.add_assoc]
    rw [Rudin.add_eq_left_cancel]
    simp [sum_neg_distrib, neg_re, ← sum_re_eq_re_sum]
    repeat rw [← Rudin.add_assoc]
    simp only [sum_re_eq_re_sum, ← neg_re, ← add_re]
    have : ∑ i ∈ range n, ↑B * Cᶜ * a i * (b i)ᶜ = B * Cᶜ *  ∑ i ∈ range n, a i * (b i)ᶜ := by
      rw [mul_sum]
      ring_nf
    rw [this, ← hc]
    have : (∑ i ∈ range n, ↑B * C * (a i)ᶜ * (b i)) = B * C * (∑ i ∈ range n, (a i)ᶜ * b i) := by
      rw [mul_sum (b:=(B * C))]
      ring_nf
    rw [this]
    have :  ∑ i ∈ range n, (a i)ᶜ * b i = Cᶜ := by simp [hc, conj_sum_eq_sum_conj, conj_mul_conj_eq]
    rw [this]
    have : ∑ x ∈ range n, (Abs (b x):Complex) ^ 2 = B := by
      simp [hb, ← sum_ofReal_eq_ofReal_sum, ofReal_mul_ofReal_eq]

    rw [this]
    simp only [Rudin.mul_assoc, conj_mul_eq_sqr_abs, mul_conj_eq_sqr_abs]
    ring_nf
    simp [neg_re]
    left
    simp [pow_two]
  rw [this] at htz
  have : A * B - Abs C ^ 2 ≥ 0 := by
    exact nonneg_of_mul_nonneg_right htz hbgz
  simp at this
  linarith

end Complex

end Rudin
