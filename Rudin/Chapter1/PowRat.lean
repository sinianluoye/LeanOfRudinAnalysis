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


theorem gtz_then_powInt_gtz {a:α} {n:Int} (ha: a > 0) :  a ^ n > 0 := by
  induction' n with n hn n hn
  simp
  simp [ha]
  exact hn
  simp [powInt_sub_one, ha]
  refine Left.mul_pos hn ?_
  exact gtz_then_inv_gtz ha



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

theorem gtz_then_rootNat_unique {x y z:α} {n:Nat}
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
def IsRootNat [LeastUpperBoundProperty α] (a:α) (n:Nat) (x:α) := x ^ n = a

noncomputable def RootNat [LeastUpperBoundProperty α] (a:α) (n:Nat) (ha : 0 ≤ a) (hn: 0 < n) : α :=
  if h: a = 0 then 0
  else by
    let hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
    have h := gtz_then_ex_gtz_rootNat (x:=a) (n:=n) hpos hn
    let y := Classical.choose h
    exact y

-- theorem gtz_then_rootNat_gtz [LeastUpperBoundProperty α] {a : α} {n : Nat} (ha : 0 < a) (hn : 0 < n) :
--   RootNat a n (lt_then_le ha) hn > 0 := by
--   -- have h := Classical.choose_spec (gtz_then_ex_gtz_rootNat (x := a) (n := n) ha hn)
--   -- exact h.left

--   -- Unfold RootNat; reduce to the chosen witness from existence lemma
--   unfold RootNat
--   rw [if_neg ha_ne]
--   -- The chosen witness comes from gtz_then_ex_gtz_rootNat ha hn
--   let h := gtz_then_ex_gtz_rootNat (x := a) (n := n) ha hn
--   -- RootNat is Classical.choose h; extract its first component (positivity)
--   exact (Classical.choose_spec h).1

theorem gtz_then_rootNat_gtz [LeastUpperBoundProperty α] {a : α} {n : Nat}
  (ha : 0 < a) (hn : 0 < n) :
  RootNat a n (lt_then_le ha) hn > 0 := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  unfold RootNat
  simp [ha_ne]
  let h := gtz_then_ex_gtz_rootNat (x := a) (n := n) ha hn
  exact (Classical.choose_spec h).1

@[simp]
theorem rootNat_isRootNat [LeastUpperBoundProperty α] (a:α) (n:Nat) (ha : 0 ≤ a) (hn: 0 < n) :
  IsRootNat a n (RootNat a n ha hn) := by

  -- use the equality part of the witness returned by `Classical.choose`
  simp [RootNat, IsRootNat]
  rcases le_iff_lt_or_eq.mp ha with ha|ha
  <;>simp [ha]
  exact (Classical.choose_spec (gtz_then_ex_gtz_rootNat (x := a) (n := n) ha hn)).2
  intro h1
  linarith


@[simp]
theorem rootNat_powNat_eq_self [LeastUpperBoundProperty α] {a x: α} {n : Nat}
  (ha: a ≥ 0)
  (hn: n > 0)
  (h: x = RootNat a n ha hn):
  x ^ n = a := by
  -- `RootNat` satisfies the defining equality, rewrite via `h`
  have hroot : (RootNat a n ha hn) ^ n = a := by
    simpa [IsRootNat] using rootNat_isRootNat a n ha hn
  simpa [h] using hroot


theorem rootNat_powNat [LeastUpperBoundProperty α] {x : α} {n m : Nat}
  (hn : n > 0) (hx : x ≥ 0) :
  (RootNat x n hx hn) ^ m = RootNat (x ^ m) n (pow_nonneg hx m) hn := by
  -- Handle the exponent m by cases
  cases m with
  | zero =>
      -- (·)^0 = 1, and x^0 = 1
      simp
      -- Show RootNat 1 n _ hn = 1
      have hpos : (0 : α) < 1 := by simp
      have hroot_pos :=
        gtz_then_rootNat_gtz (a := 1) (n := n) hpos hn
      have hroot_pow :
        (RootNat (1:α) n (by linarith) hn) ^ n = 1 := by
          simpa using
            (rootNat_powNat_eq_self (a := 1) (x := RootNat 1 n (by linarith) hn)
              (n := n) (ha := by linarith) hn rfl)
      -- Uniqueness with the obvious root 1
      have hone_pow : (1 : α) ^ n = 1 := by simp
      exact
        (gtz_then_rootNat_unique (x := (1 : α)) (y := RootNat 1 n (by linarith) hn)
          (z := 1) hn hroot_pos (by simp) hroot_pow hone_pow).symm
  | succ m =>
      -- Exponent is (m+1)
      by_cases hx0 : x = 0
      · -- x = 0
        subst hx0
        -- Left: (RootNat 0 n _ hn) = 0, so 0^(m+1) = 0
        -- Right: x^(m+1) = 0, RootNat 0 n _ hn = 0
        simp [RootNat]
      · -- x > 0
        have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
        set a := RootNat x n hx hn
        have ha_pos : a > 0 := gtz_then_rootNat_gtz (a := x) (n := n) hxpos hn
        have ha_pow : a ^ n = x :=
          rootNat_powNat_eq_self (a := x) (x := a) (n := n) hx hn rfl
        -- Define the two sides
        let y := a ^ Nat.succ m
        let z := RootNat (x ^ Nat.succ m) n (pow_nonneg hx _) hn
        have hy_pos : y > 0 := pow_pos ha_pos _
        have hz_pos : z > 0 :=
          gtz_then_rootNat_gtz (a := x ^ Nat.succ m) (n := n)
            (pow_pos hxpos _) hn
        -- Show y^n = x^(m+1)
        have hy_pow :
          y ^ n = x ^ Nat.succ m := by
          -- (a^(m+1))^n = a^((m+1)*n) = a^(n*(m+1)) = (a^n)^(m+1) = x^(m+1)
          have h1 : (a ^ Nat.succ m) ^ n = a ^ (Nat.succ m * n) := by
            exact Eq.symm (pow_mul a m.succ n)
          have h2 : a ^ (Nat.succ m * n) = a ^ (n * Nat.succ m) := by
            simp [Nat.mul_comm]
          have h3 : a ^ (n * Nat.succ m) = (a ^ n) ^ Nat.succ m :=
            by
              -- (a^n)^(m+1) = a^(n*(m+1))
              have := (pow_mul a n (Nat.succ m))
              -- This gives (a^n)^(m+1) = a^(n*(m+1))
              -- Rewrite in the needed direction
              exact this
          simpa [y, ha_pow]
            using (h1.trans (h2.trans h3))
        -- Show z^n = x^(m+1)
        have hz_pow :
          z ^ n = x ^ Nat.succ m := by
          -- RootNat (x^(m+1))^n = x^(m+1)
          simpa [z] using
            (rootNat_powNat_eq_self (a := x ^ Nat.succ m) (x := z) (n := n)
              (ha := pow_nonneg hx _) hn rfl)
        -- Uniqueness
        exact
          gtz_then_rootNat_unique (x := x ^ Nat.succ m) (y := y) (z := z)
            hn hy_pos hz_pos hy_pow hz_pow

theorem gtz_rootNat_def [LeastUpperBoundProperty α] {x a:α} {n:Nat} (ha : 0 < a) (hn: 0 < n) (hx: x = RootNat a n (by linarith) hn):
   x > 0 ∧ x ^ n = a := by
  constructor
  have h1:= gtz_then_rootNat_gtz ha hn
  rw [hx]
  exact h1
  have h2 := rootNat_powNat_eq_self (a:=a) (by linarith) hn rfl
  rw [← hx] at h2
  exact h2

theorem zero_rootNat_def  [LeastUpperBoundProperty α] {x a:α} {n:Nat} (ha : a = 0) (hn: 0 < n) (hx: x = RootNat a n (by linarith) hn):
  x = 0 := by
  simp [ha, RootNat] at hx
  exact hx


-- x^n = a, y^n = b => (x*y)^n = a*b
theorem gtz_rootNat_mul [LeastUpperBoundProperty α]
  {a b : α} {n : Nat}
  (hn : n > 0) (ha : a > 0) (hb : b > 0):
  RootNat a n (by linarith) hn * RootNat b n (by linarith) hn = RootNat (a * b) n (le_of_lt (mul_pos ha hb)) hn := by
  let x := RootNat a n (by linarith) hn
  let y := RootNat b n (by linarith) hn
  let z := RootNat (a * b) n (lt_then_le (mul_pos ha hb) ) hn
  have : x * y = z := by
    have hx0 : x > 0 := by exact gtz_then_rootNat_gtz ha hn
    have hy0 : y > 0 := by exact gtz_then_rootNat_gtz hb hn
    have hz0 : z > 0 := by exact gtz_then_rootNat_gtz (mul_pos ha hb) hn
    have hx1 : x ^ n = a := by exact rootNat_powNat_eq_self (a:=a) (by linarith) hn rfl
    have hy1 : y ^ n = b := by exact rootNat_powNat_eq_self (a:=b) (by linarith) hn rfl
    have hz1 : z ^ n = a * b := by
      refine rootNat_powNat_eq_self ?_ hn ?_
      exact le_of_lt (Left.mul_pos ha hb)
      rfl
    rw [← hx1, ← hy1] at hz1
    rw [← mul_powNat (a:=x) (b:=y)] at hz1
    have h1 := gtz_then_rootNat_unique hn hz0 (mul_pos hx0 hy0) (by rfl)
    exact (h1 hz1.symm).symm
  exact this


noncomputable def PowRat [LeastUpperBoundProperty α] (a : α) (n : ℚ) (ha : a ≥ 0) :=
  if n.isInt then
    a ^ n.num
  else
    (RootNat a n.den ha n.den_pos) ^ n.num

theorem gez_powRat_def [LeastUpperBoundProperty α] (a : α) (n : ℚ) (ha : a ≥ 0) :
  PowRat a n ha =
  if n.isInt then
    a ^ n.num
  else
    (RootNat a n.den ha n.den_pos) ^ n.num
  := rfl

theorem powInt_eq_powRat [LeastUpperBoundProperty α] {a:α} {n:Int} (ha: a ≥ 0) : a ^ n = PowRat a (n:Rat) ha := by
  simp [PowRat]
  intro h
  simp [Rat.isInt] at h

private lemma gtz_then_powInt_eq_iff_base_eq_lemma_1 {a b:α} {n:Int} (ha: a > 0) (hb: b > 0) (hn: n > 0): a ^ n = b ^ n ↔ a = b := by
  constructor
  intro h
  have hn1 : n.toNat > 0 := Int.pos_iff_toNat_pos.mp hn
  let z := a ^ n.toNat
  have : n = n.toNat := by
    norm_num
    exact Int.le_of_lt hn
  have h_a_toNat : a ^ n = a ^ n.toNat := by
    rw [powNat_eq_powInt]
    rw (occs := .pos [1]) [this]
  have h_b_toNat : b ^ n = b ^ n.toNat := by
    rw [powNat_eq_powInt]
    rw (occs := .pos [1]) [this]
  have hza : a ^ n.toNat = z := by rfl
  rw [h_a_toNat, h_b_toNat] at h
  have hzb : b ^ n.toNat = z := by
    rw [h] at hza
    exact hza
  have h1:= gtz_then_rootNat_unique (x:=z) (y:=b) (n:=n.toNat) hn1 hb ha hzb hza
  exact h1.symm
  intro h
  simp [h]

theorem gtz_then_powInt_eq_iff_base_eq {a b:α} {n:Int} (ha: a > 0) (hb: b > 0) (hn: n ≠ 0): a ^ n = b ^ n ↔ a = b := by
  constructor
  <;>intro h
  rcases Int.lt_trichotomy n 0 with hn1|hn1|hn1
  simp [powInt_def, ha, hb, hn1] at h
  rw [Rudin.div_eq_div_iff_mul_eq_mul] at h
  have hn1 : (-n).toNat > 0 := by
    norm_num
    exact hn1
  apply gtz_then_rootNat_unique (x:=a ^ (-n).toNat) (hn:=hn1)
  repeat linarith
  refine pow_ne_zero (-n).toNat ?_
  exact Ne.symm (ne_of_lt ha)
  refine pow_ne_zero (-n).toNat ?_
  exact Ne.symm (ne_of_lt hb)
  exfalso
  exact hn hn1
  exact (gtz_then_powInt_eq_iff_base_eq_lemma_1 ha hb hn1).mp h
  rw [h]








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
  let x := RootNat a (m + n).den (by linarith) (m + n).den_pos
  let y := RootNat a m.den (by linarith) m.den_pos
  rcases gtz_rootNat_def (x:=x) ha (m + n).den_pos rfl with ⟨hx1, hx2⟩
  rcases gtz_rootNat_def (x:=y) ha m.den_pos rfl with ⟨hy1, hy2⟩
  have : x ^ (m + n).num = y ^ m.num * a ^ n.num := by
    have hn1: n = n.num := by
      exact Eq.symm ((fun r ↦ (Rat.den_eq_one_iff r).mp) n hn)
    rw [hn1]
    rw [Rat.add_int_num]
    rw [powInt_add]
    rw [hn1, Rat.add_int_den] at hx2
    have hxy := gtz_then_rootNat_unique m.den_pos hx1 hy1 hx2 hy2
    rw [← hxy]
    rw [Int.mul_comm, powInt_mul, ← hx2]
    have : ((↑n.num):Rat).num = n.num := by rfl
    rw [this]
    have : (x ^ (↑m.den:Int)) = x ^ m.den := by
      simp [powInt_def, hx1]
    rw [this]
    repeat linarith

  exact this


private theorem powRat_add_lemma_3 [LeastUpperBoundProperty α] {a: α} {m n: ℚ} (ha : a > 0) (hm: ¬ m.isInt) (hn: ¬ n.isInt) (hmn: (m+n).den = 1):
   PowRat a (m + n) (by linarith) = (PowRat a m (by linarith)) * (PowRat a n (by linarith)) := by
  simp [PowRat]
  simp [hm, hn]
  simp [Rat.isInt] at *
  have hanz : a ≠ 0 := by linarith
  simp [hmn]
  let x := RootNat a m.den (by linarith) m.den_pos
  let y := RootNat a n.den (by linarith) n.den_pos
  rcases gtz_rootNat_def (x:=x) ha m.den_pos rfl with ⟨ hx0, hx1⟩
  rcases gtz_rootNat_def (x:=y) ha n.den_pos rfl with ⟨ hy0, hy1⟩
  have h1 := Rat.add_den_eq_one_then_den_eq hmn
  have : (a ^ (m + n).num) ^ ((m.den * n.den):Int) = (x ^ m.num * y ^ n.num) ^ ((m.den * n.den):Int) := by
    rw [mul_powInt]
    rw [powInt_comm (a:=x), powInt_comm (a:=y)]
    rw [powInt_mul (a:=x),←  powNat_eq_powInt (a:=x)]
    rw [hx1]
    rw [powInt_mul (a:=y), powInt_comm (a:=y), ←  powNat_eq_powInt (a:=y)]
    rw [hy1]
    repeat rw [← powInt_mul]
    rw [← powInt_add]
    rw [Rat.add_den_eq_one_then_add_num_eq]
    repeat rw [← h1]
    rw [← Int.mul_assoc, Int.ediv_mul_cancel]
    rw [Int.add_mul]
    repeat rw [Int.mul_comm (b:=m.den)]
    exact Rat.add_den_eq_one_then_den_dvd_num_add hmn
    repeat linarith
  rw [gtz_then_powInt_eq_iff_base_eq] at this
  exact this
  exact gtz_then_powInt_gtz ha
  refine Left.mul_pos ?_ ?_
  exact gtz_then_powInt_gtz hx0
  exact gtz_then_powInt_gtz hy0
  refine Int.mul_ne_zero_iff.mpr ?_
  constructor
  refine Int.ofNat_ne_zero.mpr ?_
  exact m.den_nz
  refine Int.ofNat_ne_zero.mpr ?_
  exact n.den_nz

private theorem powRat_add_lemma_4 [LeastUpperBoundProperty α] {a: α} {m n: ℚ} (ha : a > 0) (hm: ¬ m.isInt) (hn: ¬ n.isInt) (hmn: (m+n).den ≠ 1):
  PowRat a (m + n) (by linarith) = (PowRat a m (by linarith)) * (PowRat a n (by linarith)) := by
  simp [PowRat]
  simp [hm, hn]
  simp [Rat.isInt] at *
  have hanz : a ≠ 0 := by linarith
  simp [hmn]
  let x := RootNat a m.den (by linarith) m.den_pos
  let y := RootNat a n.den (by linarith) n.den_pos
  let z := RootNat a (m + n).den (by linarith) (m+n).den_pos
  rcases gtz_rootNat_def (x:=x) ha m.den_pos rfl with ⟨ hx0, hx1⟩
  rcases gtz_rootNat_def (x:=y) ha n.den_pos rfl with ⟨ hy0, hy1⟩
  rcases gtz_rootNat_def (x:=z) ha (m+n).den_pos rfl with ⟨ hz0, hz1⟩
  let k := ↑((m.num * (n.den:Int) + n.num * (m.den:Int)).natAbs.gcd (m.den * n.den))
  have hk : k =  ↑((m.num * (n.den:Int) + n.num * (m.den:Int)).natAbs.gcd (m.den * n.den)) := rfl
  rw [Rat.add_den_eq, ← hk] at hz1

  have h_target : (z ^ (m + n).num) ^ ((m.den:Int) * (n.den:Int)) = (x ^ m.num * y ^ n.num) ^ ((m.den:Int) * (n.den:Int)) := by
    rw [Rat.add_num_eq]
    rw [← hk]
    rw [← powInt_mul]
    have : (m.num * ↑n.den + n.num * ↑m.den) / ↑k * (↑m.den * ↑n.den) = (m.num * ↑n.den + n.num * ↑m.den) * (↑m.den * ↑n.den) / ↑k  := by
      refine Eq.symm (Int.mul_ediv_assoc' (↑m.den * ↑n.den) ?_)
      simp [k]
      exact Rat.normalize.dvd_num hk
    rw [this]
    have :  (m.num * ↑n.den + n.num * ↑m.den) * (↑m.den * ↑n.den) / ↑k =  ((m.num * ↑n.den + n.num * ↑m.den)) * ((↑m.den * ↑n.den) / ↑k) := by
      refine Int.mul_ediv_assoc (m.num * ↑n.den + n.num * ↑m.den) ?_
      simp [k]
      have : ↑(m.den:Int) * ↑(n.den:Int) = (↑(m.den * n.den):Int) := by exact rfl
      rw [this]
      refine Int.ofNat_dvd.mpr ?_
      exact Nat.gcd_dvd_right (m.num * ↑n.den + n.num * ↑m.den).natAbs (m.den * n.den)
    rw [this]
    rw [Int.mul_comm, powInt_mul]
    have : z ^ ((↑m.den:Int) * ↑n.den / ↑k) = z ^ (m.den * n.den / k) := by
      rw [powNat_eq_powInt]
      simp
    rw [this]
    rw [hz1]
    rw [mul_powInt, ← powInt_mul, ← Int.mul_assoc]
    rw (occs := .pos [2]) [Int.mul_comm (b:=m.den)]
    rw [powInt_mul, powInt_mul, ← powNat_eq_powInt (n:=m.den), hx1]
    rw [powInt_mul]
    repeat rw [powInt_comm (n:=n.den)]
    rw (occs := .pos [2]) [← powNat_eq_powInt (n:=n.den)]
    rw [hy1]
    repeat rw [← powInt_mul]
    rw [powInt_add]
    rw [Int.mul_comm]
    repeat linarith
    refine (powInt_nz_iff_base_nz ?_).mpr ?_
    refine Rat.num_ne_zero.mpr ?_
    exact Ne.symm (ne_of_apply_ne Rat.den fun a ↦ hn (id (Eq.symm a)))
    repeat linarith
    refine (powInt_nz_iff_base_nz ?_).mpr ?_
    refine Rat.num_ne_zero.mpr ?_
    exact Ne.symm (ne_of_apply_ne Rat.den fun a ↦ hn (id (Eq.symm a)))
    repeat linarith
  rw [gtz_then_powInt_eq_iff_base_eq] at h_target
  exact h_target
  exact gtz_then_powInt_gtz hz0
  refine Left.mul_pos ?_ ?_
  exact gtz_then_powInt_gtz hx0
  exact gtz_then_powInt_gtz hy0
  refine Int.mul_ne_zero_iff.mpr ?_
  constructor
  <;>norm_num

theorem powRat_add [LeastUpperBoundProperty α] {a: α} {m n: ℚ} (ha : a > 0) :
   PowRat a (m + n) (by linarith) = (PowRat a m (by linarith)) * (PowRat a n (by linarith)) := by
  by_cases hn : n.isInt
  <;>by_cases hm : m.isInt
  exact powRat_add_lemma_1 ha hm hn
  exact powRat_add_lemma_2 ha hm hn
  rw [Rat.add_comm]
  rw [Rudin.mul_comm (a:=PowRat a m (by linarith))]
  exact powRat_add_lemma_2 ha hn hm
  by_cases hmn : (m+n).den = 1
  exact powRat_add_lemma_3 ha hm hn hmn
  exact powRat_add_lemma_4 ha hm hn hmn


noncomputable def Sqrt [LeastUpperBoundProperty α] (a:α) (ha : a ≥ 0) := RootNat a 2 (by linarith) (by linarith)

theorem sqrt_def [LeastUpperBoundProperty α] (a:α) (ha : a ≥ 0) : Sqrt a ha = RootNat a 2 (by linarith) (by linarith) := rfl

@[simp]
theorem sqr_sqrt [LeastUpperBoundProperty α] {a:α} (ha : a ≥ 0) : (Sqrt a ha) ^ 2 = a := by
  rw [sqrt_def]
  refine rootNat_powNat_eq_self ?_ ?_ ?_
  linarith
  linarith
  rfl

@[simp]
theorem sqr_sqrt'  [LeastUpperBoundProperty α] {a:α} (ha : a ≥ 0) : (Sqrt a ha) * (Sqrt a ha) = a := by
  rw [← pow_one (a:= (Sqrt a ha))]
  rw [← powNat_add]
  have : 1 + 1 = 2 := by norm_num
  rw [this]
  exact sqr_sqrt (a:=a) ha

@[simp]
theorem sqrt_sqr_gtz' [LeastUpperBoundProperty α] {a:α} (ha : a > 0) : Sqrt (a * a) (lt_then_le (Left.mul_pos ha ha)) = a := by
  rw [sqrt_def, ← gtz_rootNat_mul]
  exact sqr_sqrt' (a:=a) (lt_then_le ha)
  repeat exact ha

@[simp]
theorem sqrt_sqr_gtz [LeastUpperBoundProperty α] {a:α} (ha : a > 0) : Sqrt (a ^ 2) (sq_nonneg a) = a := by
  simp
  exact sqrt_sqr_gtz' ha

@[simp]
theorem sqrt_sqr_ltz' [LeastUpperBoundProperty α] {a:α} (ha : a < 0) : Sqrt (a * a) (lt_then_le (mul_pos_of_neg_of_neg ha ha)) = -a := by
  let t := -a
  have ht: a = -t := by simp [t]
  simp [ht]
  apply sqrt_sqr_gtz'
  simp [t]
  exact ha

@[simp]
theorem sqrt_sqr_ltz [LeastUpperBoundProperty α] {a:α} (ha : a < 0) : Sqrt (a ^ 2) (sq_nonneg a) = -a := by
  simp
  exact sqrt_sqr_ltz' ha

@[simp]
theorem sqrt_sqr' [LeastUpperBoundProperty α] {a:α} : Sqrt (a * a) (mul_self_nonneg a) = if a ≥ 0 then a else -a := by
  split_ifs with ha
  rcases le_iff_lt_or_eq.mp ha with ha|ha
  exact sqrt_sqr_gtz' ha
  simp [ha.symm, sqrt_def, RootNat]
  simp at ha
  exact sqrt_sqr_ltz' ha

@[simp]
theorem sqrt_sqr [LeastUpperBoundProperty α] {a:α} : Sqrt (a ^ 2) (sq_nonneg a) = if a ≥ 0 then a else -a := by
  simp

@[simp]
theorem nz_then_sqrt_gtz  [LeastUpperBoundProperty α] {a:α} (ha : a > 0) : Sqrt a (by linarith) > 0 := by
  rw [sqrt_def]
  apply gtz_then_rootNat_gtz ha

@[simp]
theorem sqrt_zero [LeastUpperBoundProperty α] : Sqrt (0:α) (by linarith) = 0 := by
  simp [sqrt_def, RootNat]

theorem sqrt_mul [LeastUpperBoundProperty α] {a b:α} (ha: a ≥ 0) (hb: b ≥ 0) :
  Sqrt (a * b) (Rudin.gez_mul_gez_then_gez ha hb) = Sqrt a ha * Sqrt b hb := by
  by_cases ha0 : a = 0
  simp [ha0]
  by_cases hb0 : b = 0
  simp [hb0]
  simp [sqrt_def]
  rw [gtz_rootNat_mul]
  exact lt_of_le_of_ne ha fun a_1 ↦ ha0 (id (Eq.symm a_1))
  exact lt_of_le_of_ne hb fun a ↦ hb0 (id (Eq.symm a))

theorem rootNat_lt_iff_lt [LeastUpperBoundProperty α] {x y:α} {n:Nat} (hx: x ≥ 0) (hy: y ≥ 0) (hn: n > 0) :
  RootNat x n hx hn < RootNat y n hy hn ↔ x < y := by

  let a := RootNat x n hx hn
  let b := RootNat y n hy hn
  have ha : a = RootNat x n hx hn := rfl
  have hb : b = RootNat y n hy hn := rfl
  rw [← ha, ← hb]
  have han : a ^ n = x := by
    simp [a]
    exact rootNat_powNat_eq_self hx hn ha
  have hbn : b ^ n = y := by
    simp [b]
    exact rootNat_powNat_eq_self hy hn hb
  have ha0 : 0 ≤ a := by
    rcases le_iff_lt_or_eq.mp hx with hx|hx
    rw [le_iff_lt_or_eq]
    left
    exact gtz_then_rootNat_gtz hx hn
    simp [← han] at hx
    rw [le_iff_lt_or_eq]
    right
    exact Eq.symm (pow_eq_zero (id (Eq.symm hx)))
  have hb0 : 0 ≤ b := by
    rcases le_iff_lt_or_eq.mp hy with hy|hy
    rw [le_iff_lt_or_eq]
    left
    exact gtz_then_rootNat_gtz hy hn
    simp [← hbn] at hy
    rw [le_iff_lt_or_eq]
    right
    exact Eq.symm (pow_eq_zero (id (Eq.symm hy)))
  rw [← han, ← hbn]
  constructor
  intro h
  refine pow_lt_pow_left₀ h ha0 (by linarith)
  intro h
  apply gtz_powNat_lt_gtz_powNat_iff_lt (x:=a) (y:=b) (n:=n)
  rcases le_iff_lt_or_eq.mp hb0 with hb0|hb0
  exact hb0
  rw [← hb0] at h
  have hnnz : n ≠ 0 := by linarith
  simp [hnnz] at h
  have : a^n ≥ 0 := by exact pow_nonneg ha0 n
  exfalso
  linarith
  linarith
  exact h

theorem rootNat_eq_iff_eq [LeastUpperBoundProperty α] {x y:α} {n:Nat} (hx: x ≥ 0) (hy: y ≥ 0) (hn: n > 0) :
  RootNat x n hx hn = RootNat y n hy hn ↔ x = y := by

  let a := RootNat x n hx hn
  let b := RootNat y n hy hn
  have ha : a = RootNat x n hx hn := rfl
  have hb : b = RootNat y n hy hn := rfl
  rw [← ha, ← hb]
  have han : a ^ n = x := by
    simp [a]
    exact rootNat_powNat_eq_self hx hn ha
  have hbn : b ^ n = y := by
    simp [b]
    exact rootNat_powNat_eq_self hy hn hb
  rw [← han, ← hbn]
  constructor
  <;>intro h
  exact congrFun (congrArg HPow.hPow h) n
  rcases le_iff_lt_or_eq.mp hx with hx|hx
  rcases le_iff_lt_or_eq.mp hy with hy|hy
  have ha0 : a > 0 := by
    exact gtz_then_rootNat_gtz hx hn
  have hb0 : b > 0 := by
    exact gtz_then_rootNat_gtz hy hn
  have h1:= gtz_then_rootNat_unique (x:=a^n) (y:=a) (z:=b) (n:=n) hn ha0 hb0 rfl h.symm
  exact h1
  exfalso
  rw [← hy] at hbn
  rw [hbn] at h
  rw [han] at h
  linarith
  rw [← hx] at han
  rw [han] at h
  rw [hbn] at h
  have ha0: a = 0 := by exact zero_rootNat_def (id (Eq.symm hx)) hn ha
  have hb0: b = 0 := by exact zero_rootNat_def (id (Eq.symm h)) hn hb
  linarith



theorem rootNat_le_iff_le [LeastUpperBoundProperty α] {x y:α} {n:Nat} (hx: x ≥ 0) (hy: y ≥ 0) (hn: n > 0) :
  RootNat x n hx hn ≤ RootNat y n hy hn ↔ x ≤ y := by
  simp [le_iff_lt_or_eq, rootNat_lt_iff_lt, rootNat_eq_iff_eq]


theorem sqrt_lt_iff_lt [LeastUpperBoundProperty α] {x y:α} (hx: x ≥ 0) (hy: y ≥ 0) :
  Sqrt x hx < Sqrt y hy ↔ x < y := by
  simp [sqrt_def]
  apply rootNat_lt_iff_lt


theorem sqrt_eq_iff_eq [LeastUpperBoundProperty α] {x y:α} (hx: x ≥ 0) (hy: y ≥ 0) :
  Sqrt x hx = Sqrt y hy ↔ x = y := by
  simp [sqrt_def]
  apply rootNat_eq_iff_eq

theorem sqrt_le_iff_le [LeastUpperBoundProperty α] {x y:α} (hx: x ≥ 0) (hy: y ≥ 0) :
  Sqrt x hx ≤ Sqrt y hy ↔ x ≤ y := by
  simp [sqrt_def]
  apply rootNat_le_iff_le

theorem nz_then_sqr_gtz [LeastUpperBoundProperty α] {x:α} (hx: x ≠ 0) : x^2 > 0 := by
  exact pow_two_pos_of_ne_zero hx

theorem sqr_gez [LeastUpperBoundProperty α] {x:α} : x ^ 2 ≥ 0 := by
  exact sq_nonneg x

theorem sqrt_gez [LeastUpperBoundProperty α] {x:α} (hx: x ≥ 0): Sqrt x hx ≥ 0 := by
  have : ∃ y ≥ 0, x = y ^ 2 := by
    by_cases hxz : x = 0
    use 0
    simp
    exact hxz
    have hx1 : x > 0 := by
      exact lt_of_le_of_ne hx fun a ↦ hxz (id (Eq.symm a))
    have h1:= gtz_then_ex_gtz_rootNat (x:=x) (n:=2) hx1 (by norm_num)
    rcases h1 with ⟨ y, hy1, hy2⟩
    use y
    constructor
    linarith
    exact hy2.symm
  rcases this with ⟨ y, hy1, hy2⟩
  rcases le_iff_lt_or_eq.mp hy1 with hy1|hy1
  have h:= sqrt_sqr_gtz hy1
  sorry


end Rudin
