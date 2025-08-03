import Mathlib
import Rudin.Chapter1.Ordered
import Rudin.Chapter1.Field
import Rudin.Chapter1.OrderedField
import Rudin.Chapter1.Bound
import Rudin.Chapter1.Inequality

namespace Rudin


variable {α : Type u} [OrderedField α]
variable {a b:α}

-- test
example {x s:α} (hx: 0 < x): s - x < s := by
  linarith


-- 1.20 (a)
theorem gtz_then_ex_nat_mul_gt  [LeastUpperBoundProperty α] {x y: α} (hx: x > 0) : ∃ n:Nat, n • x > y := by
  rcases lt_trichotomy (a:=y) (b:=0) with hy|hy|hy
  use 0
  simp
  exact hy
  rw [hy]
  use 1
  simp
  exact hx
  simp at hx
  let A := {t | ∃ n:ℕ, t = n • x}
  by_contra h
  simp at h
  have h_up_y : UpperBound A y := by
    simp [UpperBound]
    intro r hr
    simp [A] at hr
    rcases  hr with ⟨n, hn⟩
    have := h n
    rw [← hn] at this
    exact this
  have h_exist_sup := LeastUpperBoundProperty.subset_sup_exist A
  have h_a_not_empy : A ≠ ∅ := by
    simp [Set.not_empty_iff_ex_mem]
    use x
    simp [A]
    use 1
    simp
  have h_bound_above_A : BoundAbove A := by
    simp [BoundAbove]
    use y
  have h_exist_sup := h_exist_sup h_a_not_empy h_bound_above_A
  rcases h_exist_sup with ⟨ s, hs⟩
  let t := s - x
  have h_t_not_ub: ¬ UpperBound A t := by
    simp [IsSup] at hs
    have : t < s := by
      simp [t]
      linarith
    exact hs.right t this
  simp [UpperBound, t, A] at h_t_not_ub
  rcases h_t_not_ub with ⟨ m, hm⟩
  have h_t_lt_m_1_x : s < (m + 1) * x := by
    linarith
  have h_m_1_x_in_A : (m + 1) * x ∈ A := by
    simp [A]
    use m + 1
    left
    push_cast
    linarith
  have h_s_ge_m_1_x : s ≥ (m+1) * x := by
    simp [IsSup, UpperBound] at hs
    apply hs.left
    assumption
  rw [← Rudin.not_le_iff_lt] at h_t_lt_m_1_x
  exact h_t_lt_m_1_x h_s_ge_m_1_x


-- 1.21

private theorem gtz_then_ex_gtz_rootNat_lemma_1 {x:α} {n:Nat} {E: Set α}
  (hE: E = {t:α | t ^ n < x})
  (hx: x > 0)
  (hn: n > 1): E ≠ ∅ := by
  simp [Set.not_empty_iff_ex_mem]
  use 0
  simp [hE]
  have hnnz : n ≠ 0 := by linarith
  simp [hnnz]
  linarith

private theorem gtz_then_ex_gtz_rootNat_lemma_2 {x:α} {n:Nat} {E: Set α}
  (hE: E = {t:α | t ^ n < x})
  (hx: x > 0)
  (hn: n > 1): BoundAbove E := by
  simp [BoundAbove, UpperBound]
  simp [hE]
  use x + 1
  intro a ha
  contrapose ha
  simp at ha
  simp
  have hx1 : x + 1 > 1 := by linarith
  have h1 := gto_then_natPow_gto_gt_base (n:=n) hx1
  apply lt_then_le
  by_cases hn1: n > 1
  simp [hn1] at h1
  have ha1 : (x+1) ^ n < a ^ n := by
    apply gtz_lt_gtz_then_powNat_gtz_lt
    linarith
    linarith
    linarith
  have hx1: x < x + 1 := by linarith
  linarith
  simp at hn1
  have hn2: n = 1 := by linarith
  rw [hn2]
  simp
  linarith

private theorem gtz_then_ex_gtz_rootNat_lemma_3 {y x:α} {n:Nat}
  (hy: IsSup {t:α | t ^ n < x} y)
  (hn: n > 1)
  (hx: x > 0):
  y > 0
  := by
  simp [IsSup, UpperBound] at hy
  rcases hy with ⟨ hy1, hy2⟩
  contrapose! hy1
  use x / (x+1)
  constructor
  have : n = n - 1 + 1 := by
    refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
    exact Nat.one_le_of_lt hn
  rw [this]
  simp
  have h1:  (x / (x + 1)) ^ (n - 1) < 1 := by
    refine pow_lt_one₀ ?_ ?_ ?_
    rw [le_div_gtz_iff_mul_le]
    simp
    linarith
    linarith
    rw [← Rudin.gt_iff_lt]
    rw [gt_div_gtz_iff_mul_gt]
    simp
    linarith
    refine Nat.sub_ne_zero_iff_lt.mpr ?_
    exact hn
  have h2: x / (x + 1) < x := by
    rw [← Rudin.gt_iff_lt, Rudin.gt_div_gtz_iff_mul_gt]
    refine (lt_mul_iff_one_lt_right hx).mpr ?_
    linarith
    linarith
  have h3 :  0 < x / (x + 1):= by
    rw [Rudin.lt_div_gtz_iff_mul_lt]
    simp
    repeat linarith

  rw (occs := .pos [5]) [← Rudin.one_mul (a:=x)]
  refine mul_lt_mul_of_nonneg_of_pos' ?_ h2 ?_ ?_
  linarith
  linarith
  linarith
  have h3 :  0 < x / (x + 1):= by
    rw [Rudin.lt_div_gtz_iff_mul_lt]
    simp
    repeat linarith
  linarith


private theorem gtz_then_ex_gtz_rootNat_lemma_4  [LeastUpperBoundProperty α] {y h x:α} {n:Nat}
  (hn: n > 1)
  (hx: x > 0)
  (hy: IsSup {t:α | t ^ n < x} y)
  (h0: 0 < h)
  (h1: h < 1)
  (h2: h < (x - y^n) / (n * (y+1)^(n-1)))
  :
   (y+h) ^ n < x
  := by
  rw [← nsmul_eq_mul] at h2
  have hy0: y > 0 := gtz_then_ex_gtz_rootNat_lemma_3 hy hn hx
  let a := y
  let b := y + h
  have hab : a < b := by exact lt_add_of_pos_right a h0
  have ha0 : 0 < a := by exact hy0
  have h3 := powNat_sub_powNat_lt_sub_mul_exp_mul_max_powNat_exp_sub_one hn ha0 hab
  have h4 : (b - a) * n • b ^ (n - 1) = h * n • (y + h) ^ (n-1) := by
    simp [b, a]
  rw [h4] at h3
  have h5 : h * n • (y + h) ^ (n - 1) < h * n • (y + 1) ^ (n - 1) := by
    repeat rw [nsmul_eq_mul]
    repeat rw [Rudin.gtz_mul_lt_left_cancel]
    refine pow_lt_pow_left₀ ?_ ?_ ?_
    linarith
    linarith
    exact Nat.sub_ne_zero_iff_lt.mpr hn
    simp
    linarith
    linarith
  have h6 : h * n • (y + 1) ^ (n - 1) < x - y^n := by
    rw [Rudin.lt_div_gtz_iff_mul_lt] at h2
    exact h2
    refine nsmul_pos ?_ ?_
    refine pow_pos ?_ (n - 1)
    linarith
    linarith
  linarith

private theorem gtz_then_ex_gtz_rootNat_lemma_5 [LeastUpperBoundProperty α] {x y:α} {n:Nat}
  (hx: x > 0)
  (hn: n > 1)
  (hy: IsSup {t:α | t ^ n < x} y)
  (hxy : y^n < x)
  :
  ∃ y > 0, y ^ n = x
  := by
  have hy0 : y > 0 := gtz_then_ex_gtz_rootNat_lemma_3 hy hn hx
  have hh : ∃ h, 0 < h ∧ h < 1 ∧ h < (x - y^n) / (n * (y+1)^(n-1)) := by
    by_cases h: 1 < (x - y^n) / (n * (y+1)^(n-1))
    have h1 : (1:α) / (1 + 1) < 1 := by
      rw [← Rudin.gt_iff_lt]
      rw [Rudin.gt_div_gtz_iff_mul_gt]
      simp
      simp
    use 1 / (1 + 1)
    constructor
    rw [Rudin.lt_div_gtz_iff_mul_lt]
    linarith
    simp
    constructor
    exact h1
    linarith
    use (x - y^n) / (n * (y+1)^(n-1)) / (1+1)
    have h1: n * (y+1)^(n-1) > 0 := by
      refine gtz_mul_gtz_then_gtz ?_ ?_
      simp
      linarith
      refine pow_pos ?_ (n - 1)
      linarith
    constructor
    rw [Rudin.lt_div_gtz_iff_mul_lt]
    rw [Rudin.lt_div_gtz_iff_mul_lt]
    simp
    linarith
    apply Rudin.gtz_mul_gtz_then_gtz
    simp
    linarith
    refine pow_pos ?_ (n - 1)
    linarith
    linarith
    constructor
    simp at h
    have h2: 1 < 1 + 1 := by simp
    have h3: (x - y ^ n) / (↑n * (y + 1) ^ (n - 1)) < 1 + 1:= by linarith
    rw [← Rudin.gt_iff_lt]
    rw [Rudin.gt_div_gtz_iff_mul_gt]
    simp
    linarith
    simp
    rw [← Rudin.gt_iff_lt]
    rw [Rudin.gt_div_gtz_iff_mul_gt]
    rw (occs := .pos [2])[← Rudin.mul_one (a:=(x - y ^ n) / (↑n * (y + 1) ^ (n - 1)))]
    rw [Rudin.gt_iff_lt]
    rw [Rudin.gtz_mul_lt_left_cancel]
    simp
    simp
    rw [Rudin.lt_div_gtz_iff_mul_lt]
    simp
    exact hxy
    exact h1
    simp
  rcases hh with ⟨ h, hh1, hh2, hh3⟩
  have h1 := gtz_then_ex_gtz_rootNat_lemma_4 hn hx hy hh1 hh2 hh3
  have : y + h ∈ {t:α | t ^ n < x} := by
    exact h1
  simp [IsSup, UpperBound] at hy
  exfalso
  have h' := hy.left (y+h) this
  linarith

private theorem gtz_then_ex_gtz_rootNat_lemma_6 {x y k:α} {n:Nat}
  (hx: x > 0)
  (hn: n > 1)
  (hy: IsSup {t:α | t ^ n < x} y)
  (hxy : x < y^n)
  (hk: k = (y^n - x) / (n * y^(n-1)))
  :
    ∃ y > 0, y ^ n = x
  := by
  have hy0 := gtz_then_ex_gtz_rootNat_lemma_3 hy hn hx
  have h1 : n * y^(n-1) > 0 := by
    refine gtz_mul_gtz_then_gtz ?_ ?_
    simp
    linarith
    refine pow_pos ?_ (n - 1)
    exact hy0
  have hk0 : 0 < k := by
    simp [hk]
    rw [Rudin.lt_div_gtz_iff_mul_lt]
    simp
    exact hxy
    exact h1
  have hky : k < y := by
    simp [hk]
    rw [← Rudin.gt_iff_lt]
    rw [Rudin.gt_div_gtz_iff_mul_gt]
    rw [Rudin.mul_comm, Rudin.mul_assoc, ← Rudin.powNat_add_one]
    have : n - 1 + 1 = n := by
      refine Nat.sub_add_cancel ?_
      exact Nat.one_le_of_lt hn
    rw [this, ← nsmul_eq_mul]
    rw (occs := .pos [1])[← this]
    simp
    rw [add_mul, Rudin.one_mul]
    rw [Rudin.add_comm]
    rw [Rudin.sub_eq_add_neg, Rudin.add_lt_left_cancel]
    have ht1 : -x < 0 := by linarith
    have ht2 : 0 < (n - 1) • y ^ n := by
      refine (nsmul_pos_iff ?_).mpr ?_
      exact Nat.sub_ne_zero_iff_lt.mpr hn
      linarith
    have : (n - 1) • y ^ n = ↑(n - 1) * y ^ n := by
      exact nsmul_eq_mul (n - 1) (y ^ n)
    linarith
    exact h1
  have h_up : UpperBound {t:α | t ^ n < x} (y - k) := by
    simp [UpperBound]
    intro t ht
    contrapose! ht

    have hyt1 : y^n - t^n < y^n - (y-k)^n := by
      repeat rw [Rudin.sub_eq_add_neg]
      rw [Rudin.add_lt_left_cancel]
      simp
      refine pow_lt_pow_left₀ ht ?_ ?_
      linarith
      linarith

    have hyt2 := powNat_sub_powNat_lt_sub_mul_exp_mul_max_powNat_exp_sub_one (a:=y-k) (b:=y) hn (by linarith) (by linarith)
    have hyt3 : (y - (y - k)) * n • y ^ (n - 1) = y^ n - x := by
      simp
      simp [hk]
      rw [Rudin.div_mul_cancel]
      linarith
    have hyt4 : y ^ n - t ^ n < y ^ n - x := by
      linarith
    have ht1 : t ^ n > x := by
      linarith
    linarith
  simp [IsSup] at hy
  have hy2 := hy.right (y-k) (by linarith)
  exfalso
  exact hy2 h_up


theorem gtz_then_ex_gtz_rootNat [LeastUpperBoundProperty α] {x:α} {n:Nat} (hx: x > 0) (hn:n > 0) : ∃ y > 0, y ^ n = x := by
  by_cases hn1 : n = 1
  simp [hn1]
  linarith
  let E := {t:α | t ^ n < x}
  have hn2 : n > 1 := by exact Nat.lt_of_le_of_ne hn fun a ↦ hn1 (id (Eq.symm a))
  have h := LeastUpperBoundProperty.subset_sup_exist E
    (gtz_then_ex_gtz_rootNat_lemma_1 (E:=E) (by rfl) hx hn2)
    (gtz_then_ex_gtz_rootNat_lemma_2 (E:=E) (by rfl) hx hn2)
  rcases h with ⟨ y, hy⟩

  rcases Rudin.lt_trichotomy (a:=y^n) (b:=x) with hxy|hxy|hxy
  exact gtz_then_ex_gtz_rootNat_lemma_5 hx hn2 hy hxy
  use y
  constructor
  exact gtz_then_ex_gtz_rootNat_lemma_3 hy hn2 hx
  exact hxy
  let k:= (y^n - x) / (n * y^(n-1))
  exact gtz_then_ex_gtz_rootNat_lemma_6 hx hn2 hy hxy (by rfl)

theorem gtz_then_rootNat_unique [LeastUpperBoundProperty α] {x y z:α} {n:Nat}
  (hn:n > 0)
  (hy: y > 0) (hz: z > 0)
  (hxy: y ^ n = x) (hxz: z ^ n = x): y = z := by
  rcases Rudin.lt_trichotomy (a:=y) (b:=z) with hyz|hyz|hyz
  exfalso
  have : y ^ n < z ^ n := by exact gtz_lt_gtz_then_powNat_gtz_lt hy hyz hn
  linarith
  exact hyz
  have : z ^ n < y ^ n := by exact gtz_lt_gtz_then_powNat_gtz_lt hz hyz hn
  linarith


-- y ^ n = x
def IsRootNat [LeastUpperBoundProperty α] (x:α) (n:Nat) (y:α) := y ^ n = x

@[simp]
theorem rootNat_powNat_eq_self [LeastUpperBoundProperty α] {x y: α} {n : Nat}
  (hxy: IsRootNat x n y):
  y ^ n = x := by
  simp [IsRootNat] at hxy
  exact hxy

theorem rootNat_powNat [LeastUpperBoundProperty α] {x y z: α} {n m: Nat}
  (hx : x > 0)
  (hn : n > 0)
  (hm : m > 0)
  (hxy: IsRootNat x n y)
  (hxz: IsRootNat (x^m) n z):
  y ^ m = z := by
  simp [IsRootNat] at *
  rw [← hxy] at hxz
  sorry

/-
theorem rootNat_mul [LeastUpperBoundProperty α] {x y:α} {n:Nat} (hx: x > 0) (hy: y > 0) (hn: n > 0) :
  (RootNat x n hx hn) * (RootNat y n hy hn) = RootNat (x * y) n (by exact mul_pos hx hy) hn:= by
  let a := RootNat x n hx hn
  let b := RootNat y n hy hn
  have ha : a > 0 := (Classical.choose_spec (gtz_then_ex_gtz_rootNat hx hn)).1
  have hb : b > 0 := (Classical.choose_spec (gtz_then_ex_gtz_rootNat hy hn)).1
  have hab_pow : (a * b) ^ n = x * y := by
    rw [mul_pow, rootNat_powNat_eq_self hx hn, rootNat_powNat_eq_self hy hn]
  have hRootNat : (RootNat (x * y) n (mul_pos hx hy) hn) ^ n = x * y := rootNat_powNat_eq_self (mul_pos hx hy) hn
  have hRootNat_pos : RootNat (x * y) n (mul_pos hx hy) hn > 0 := (Classical.choose_spec (gtz_then_ex_gtz_rootNat (mul_pos hx hy) hn)).1
  exact (gtz_then_rootNat_unique hn hRootNat_pos (mul_pos ha hb) hRootNat hab_pow).symm
-/


noncomputable def PowRat [LeastUpperBoundProperty α] (a : α) (n : ℚ) (ha : a ≥ 0) :=
  if h_int : n.isInt then
    a ^ n.num
  else
    by
      by_cases h0 : a = 0
      · -- `a` is zero
        exact 0
      · -- `a` is positive (since `a ≥ 0` and `a ≠ 0`)
        have h_pos : (0 : α) < a := lt_of_le_of_ne ha (Ne.symm h0)
        -- existence of a positive `y` with `y ^ n.den = a`
        have h := gtz_then_ex_gtz_rootNat (x:=a) (n:=n.den) h_pos (n.den_pos)
        -- use classical choice to extract the witness from the existential proof
        let y : α := Classical.choose h
        exact y ^ n.num


private theorem powRat_add_lemma_1 [LeastUpperBoundProperty α] {a: α} {m n: ℚ} (ha : a > 0) (hm: m.isInt) (hn: n.isInt):
   PowRat a (m + n) (by linarith) = (PowRat a m (by linarith)) * (PowRat a n (by linarith)) := by
  simp [PowRat]
  simp [hm, hn]
  simp [Rat.isInt] at *
  rw [← Rat.mkRat_self (a:=m), ← Rat.mkRat_self (a:=n)]
  rw [Rat.mkRat_add_mkRat]
  rw [hn, hm]
  simp
  have : ((m.num:Rat) + ↑n.num).den = 1 := by
    rw [← Rat.ofInt_den (n:=↑m.num + ↑n.num)]
    simp [Rat.ofInt]
  simp [this]
  have : ((↑m.num:Rat) + ↑n.num).num = m.num + n.num := by
    rw [← Rat.ofInt_num (n:=↑m.num + ↑n.num)]
    simp [Rat.ofInt]
  simp [this]
  rw [Rudin.powInt_add]
  linarith
  linarith
  linarith

private theorem powRat_add_lemma_2 [LeastUpperBoundProperty α] {a: α} {m n: ℚ} (ha : a > 0) (hm: ¬ m.isInt) (hn: n.isInt):
   PowRat a (m + n) (by linarith) = (PowRat a m (by linarith)) * (PowRat a n (by linarith)) := by
  simp [PowRat]
  simp [hm, hn]
  simp [Rat.isInt] at *
  have hmn : (m + n).den ≠ 1 := by
    have : n = n.num := by exact Eq.symm ((fun r ↦ (Rat.den_eq_one_iff r).mp) n hn)
    rw [this]
    apply Rat.den_ne_one_then_add_int_den_ne_one
    exact hm
  simp [hmn]
  simp [ha]
  sorry




theorem powRat_add [LeastUpperBoundProperty α] {a: α} {m n: ℚ} (ha : a > 0) :
   PowRat a (m + n) (by linarith) = (PowRat a m (by linarith)) * (PowRat a n (by linarith)) := by
  by_cases hn : n.isInt
  <;>by_cases hm : m.isInt
  exact powRat_add_lemma_1 ha hm hn
  sorry
  sorry
  sorry





end Rudin
