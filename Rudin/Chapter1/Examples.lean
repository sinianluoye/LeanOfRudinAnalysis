import Mathlib
import Rudin.Chapter1.Bound
import Rudin.Chapter1.Rational

theorem prime_of_mul {x y p: ℤ} (hp:Prime p) (hxy: p ∣ x * y): p ∣ x ∨ p ∣ y := by
  apply (Prime.dvd_mul hp).mp
  exact hxy


theorem prime_dvd_pow_iff_prime_dvd {t p:ℤ} {n:ℕ} (hp: Prime p) (hn: n ≥ 1) :  p ∣ t ^ n ↔ p ∣ t := by
  apply hp.dvd_pow_iff_dvd
  linarith


theorem pow_root_of_prime_is_irrational {prime : ℤ} {n : ℕ} (hprime: Prime prime) (hn: n ≥ 2): ¬ ∃ x : ℚ, x ^ n = prime := by
  intro h
  have hng1 : n ≥ 1 := by linarith
  rcases h with ⟨ x, hx ⟩
  rcases x with ⟨ p, qnat, hqnz, hpqnat⟩
  let q:ℤ := qnat
  have hpq: Int.gcd p q = 1 := by
    have h : Nat.gcd p.natAbs qnat = 1 := hpqnat.gcd_eq_one
    simp [q, Int.gcd_eq_natAbs, h]
  simp [Rat.pow_def, Rat.mkRat_def] at hx
  have h1 : p ^ n = prime * q ^ n := by
    apply Rat.eq_iff_mul_eq_mul.mp at hx
    simpa [Rat.mkRat_def] using hx
  by_cases hq_dvd_prime : prime ∣ q
  · have hp_dvd_prime : prime ∣ p := by
      have : prime ∣ p ^ n := by
        rw [h1]
        simp
      apply (prime_dvd_pow_iff_prime_dvd hprime hng1).mp
      exact this
    apply Int.gcd_eq_one_iff.mp at hpq
    have : prime ∣ 1 := hpq prime hp_dvd_prime hq_dvd_prime
    apply Prime.not_dvd_one at this
    exact this
    exact hprime

  · apply hq_dvd_prime
    have hp_dvd_prime : prime ∣ p := by
      have : prime ∣ p ^ n := by
        rw [Int.dvd_def]
        use q^n
      apply (prime_dvd_pow_iff_prime_dvd hprime hng1).mp
      exact this
    have hqn_dvd_prime: prime ∣ q ^ n := by
      have : prime ^ n ∣ p ^ n := by
        apply pow_dvd_pow_of_dvd
        exact hp_dvd_prime
      rw [h1] at this
      rw [dvd_def] at this
      rw [dvd_def]
      rcases this with ⟨ c, hc⟩
      use prime^(n-2) * c
      have h1 : prime * q ^ n = prime * (prime ^ (n - 1) * c) := by
        nth_rw 2 [← pow_one prime]
        rw [← mul_assoc, ← pow_add]
        have : 1 + (n - 1) = n := by
          simpa [add_comm] using Nat.sub_add_cancel hng1
        rw [this]
        exact hc
      have h2 : q^n = prime ^ (n - 1) * c := by
        apply mul_left_cancel₀ hprime.ne_zero
        exact h1
      nth_rw 1 [← pow_one prime]
      rw [← mul_assoc, ← pow_add]
      rw [h2]
      by_cases hczero : c = 0
      rw [hczero, mul_zero, mul_zero]
      have h3: 1 + (n - 2) = n - 1 := by omega
      rw [h3]
    apply (prime_dvd_pow_iff_prime_dvd hprime hng1).mp
    exact hqn_dvd_prime

theorem sqrt2_irrational : ¬∃ x : ℚ, x ^ 2 = 2 := by
  apply pow_root_of_prime_is_irrational
  apply Int.prime_two
  omega

namespace Rudin_1_1

def A := { p:ℚ | p ^ 2 < 2}
def B := { p:ℚ | p ^ 2 > 2}

lemma sqr_x_lt_2_then_2_x_sub_2_div_x_add_2_sqr_le_2 {a:ℚ} (h: a^2 < 2) : ((2*a + 2) / (a + 2))^2 < 2 := by
  rw [div_pow]
  have h_aux : (2 * a + 2) ^ 2 - 2 * (a + 2) ^ 2 = 2 * (a ^ 2 - 2) := by
    ring
  have h_lt_zero : (2 * a + 2) ^ 2 - 2 * (a + 2) ^ 2 < 0 := by
    rw [h_aux]
    linarith
  have hm_add2_nz : a + 2 ≠ 0 := by
    intro ha
    have : a = -2 := by linarith
    simp [this, pow_two] at h

  have hm_add2_sqr_gz : (a + 2) ^ 2 > 0 := by
    apply pow_two_pos_of_ne_zero
    exact hm_add2_nz
  rw [div_lt_iff₀ hm_add2_sqr_gz]
  linarith

lemma sqr_x_gt_2_then_2_x_sub_2_div_x_add_2_sqr_gt_2 {a:ℚ} (h: a^2 > 2) (h1: a > 0) : ((2*a + 2) / (a + 2))^2 > 2 := by
  rw [div_pow]
  have h_aux : (2 * a + 2) ^ 2 - 2 * (a + 2) ^ 2 = 2 * (a ^ 2 - 2) := by
    ring
  have h_lt_zero : (2 * a + 2) ^ 2 - 2 * (a + 2) ^ 2 > 0 := by
    rw [h_aux]
    linarith
  have hm_add2_nz : a + 2 ≠ 0 := by
    intro ha
    have : a = -2 := by linarith
    linarith

  have hm_add2_sqr_gz : (a + 2) ^ 2 > 0 := by
    apply pow_two_pos_of_ne_zero
    exact hm_add2_nz
  rw [gt_iff_lt]
  rw [lt_div_iff₀' hm_add2_sqr_gz]
  linarith


lemma sqr_x_lt_2_then_sub_2_div_x_add_2_sqr_le_2_gt_x {a:ℚ} (h: a^2 < 2) : (2*a + 2) / (a + 2) > a := by
  have hm_add2_gz : a + 2 > 0 := by
    by_contra!
    have : a ≤ -2 := by linarith
    have : a^2 ≥ 4 := by nlinarith [this]
    linarith
  simp [lt_div_iff₀' hm_add2_gz]
  linarith

lemma sqr_x_lg_2_then_sub_2_div_x_add_2_sqr_le_2_lt_x {a:ℚ} (h: a^2 > 2) (h1: a > 0): (2*a + 2) / (a + 2) < a := by
  have hm_add2_gz : a + 2 > 0 := by
    by_contra!
    have : a ≤ -2 := by linarith
    have : a^2 ≥ 4 := by nlinarith [this]
    linarith
  rw [div_lt_iff₀ hm_add2_gz]
  linarith


theorem a_has_no_max : ¬ ∃ m ∈ A, ∀ x ∈ A, x < m := by
  intro h
  rcases h with ⟨ m, hma, hmax⟩
  apply Set.mem_setOf.mp at hma
  let q := m - (m^2 - 2) / (m + 2)
  have hm_add2_nz : m + 2 ≠ 0 := by
    intro h
    have : m = -2 := by linarith
    simp [this, pow_two] at hma

  have hq1: q = (2*m + 2) / (m + 2) := by
    calc
      q = m - (m^2 - 2) / (m + 2) := by rfl
      _ = (2*m + 2) / (m + 2) := by
        rw [sub_div', pow_two, mul_add]
        have : m * m + m * 2 - (m * m - 2) = 2*m + 2 := by linarith
        rw [this]
        exact hm_add2_nz
  have hq := sqr_x_lt_2_then_2_x_sub_2_div_x_add_2_sqr_le_2 hma
  have hqa: q ∈ A := by
    apply Set.mem_setOf.mpr
    simp [hq1]
    exact hq

  have hqm: q > m := by
    rw [hq1]
    exact sqr_x_lt_2_then_sub_2_div_x_add_2_sqr_le_2_gt_x hma

  have hqm_anti : q < m := by
    apply hmax
    exact hqa
  have : q < q := lt_trans hqm_anti hqm
  apply lt_irrefl _ this

-- similar to a_has_no_max, skip
theorem b_has_no_min : ¬ ∃ m ∈ B, ∀ x ∈ B, x > m := by
  sorry

end Rudin_1_1

namespace Rudin

-- 1.9 1)
example : ¬ ∃ s : ℚ, IsSup ({ p : ℚ | p ^ 2 < 2 }) s := by
  intro h
  simp [IsSup, UpperBound] at h
  have h1 := Rudin_1_1.a_has_no_max
  apply h1
  simp [Rudin_1_1.A]
  rcases h with ⟨s, ⟨hs1, hs2⟩⟩

  have htri := lt_trichotomy (a:=s^2) (b:=2)
  rcases htri with hlt | heq | hgt
  -- s ^ 2 < 2
  let s' := (2*s + 2) / (s + 2)
  use s'
  have hs' : s' ^ 2 < 2 := by
    simp [s']
    exact Rudin_1_1.sqr_x_lt_2_then_2_x_sub_2_div_x_add_2_sqr_le_2 hlt
  constructor
  exact hs'
  intro x hx
  have hs'gs : s' > s := Rudin_1_1.sqr_x_lt_2_then_sub_2_div_x_add_2_sqr_le_2_gt_x hlt
  have hxles := hs1 x hx
  calc
    x ≤ s := hxles
    _ < s' := hs'gs
  -- s ^ 2 = 2
  have h2 := sqrt2_irrational ⟨ s, heq ⟩
  exfalso
  exact h2
  -- s ^ 2 > 2
  have hsgz : s > 0 := by
    by_contra! hs
    have h0_lt2 : (0 : ℚ) ^ 2 < 2 := by norm_num
    have h0_le_s : (0 : ℚ) ≤ s := hs1 0 h0_lt2
    have hsz : s = 0 := le_antisymm hs h0_le_s
    have : (2 : ℚ) < (0 : ℚ) := by
      rw [hsz] at hgt
      ring_nf at hgt
      exact hgt
    linarith
  let s' := (2*s + 2) / (s + 2)
  have := hs2 s'
  have hs'lts : s' < s:= Rudin_1_1.sqr_x_lg_2_then_sub_2_div_x_add_2_sqr_le_2_lt_x hgt hsgz
  have hs' : s' ^ 2 > 2 := Rudin_1_1.sqr_x_gt_2_then_2_x_sub_2_div_x_add_2_sqr_gt_2 hgt hsgz
  have hs'2 := hs2 s' hs'lts
  rcases hs'2 with ⟨ x, hx1, hx2 ⟩
  exfalso
  have : s' > 0 := by
    have hnum : 0 < 2 * s + 2 := by linarith [hsgz]
    have hden : 0 < s + 2     := by linarith [hsgz]
    simpa [s'] using div_pos hnum hden
  by_cases hx : x > 0
  have h_lt_sq : s' ^ 2 < x ^ 2 := by
    -- s'^2 < x * s'  (multiply hx2 by s' > 0)
    have h1 : s' * s' < x * s' :=
      mul_lt_mul_of_pos_right hx2 this
    -- x * s' < x^2   (multiply hx2 by x > 0)
    have h2 : x * s' < x * x :=
      mul_lt_mul_of_pos_left hx2 hx
    have : s' * s' < x * x := lt_trans h1 h2
    simpa [pow_two] using this
  linarith
  linarith

-- 1.9 2)
lemma sup_mem_or_not {α : Type*}[Rudin.Ordered α] {E : Set α} {s : α} (h : IsSup E s) : s ∈ E ∨ s ∉ E := by
  classical
  exact (em (s ∈ E))

-- 1.9 3)
namespace Rudin_1_9_3

def E := {x:ℚ | ∃ n : ℕ, x = 1 / (n+1) }

lemma Sup_E_is_one : IsSup E 1 := by
  simp [E, IsSup, UpperBound]
  constructor
  · intro n
    have hden : (0 : ℚ) < (n : ℚ) + 1 := by
      have : (0 : ℕ) < n.succ := Nat.succ_pos _
      exact_mod_cast this
    have hle : (1 : ℚ) ≤ (n : ℚ) + 1 := by
      have : (1 : ℕ) ≤ n.succ := Nat.succ_le_succ (Nat.zero_le n)
      exact_mod_cast this
    simpa [one_div] using (div_le_one hden).2 hle
  · intro b hb
    have h1 : (1 : ℚ) ∈ ({x : ℚ | ∃ n : ℕ, x = 1 / (n + 1)}) := by
      exact ⟨0, by simp⟩
    use 0
    linarith

lemma Inf_E_is_zero : IsInf E 0 := by
  simp [E, IsInf, LowerBound]
  constructor
  norm_cast
  omega
  intro x
  intro hx
  simpa [one_div] using (exists_nat_one_div_lt hx : ∃ n : ℕ, (1 / ((n : ℚ) + 1)) < x)


end Rudin_1_9_3


end Rudin
