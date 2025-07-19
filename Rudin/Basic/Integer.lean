theorem Int.lt_then_not_gt {a b:Int} (hab: a < b): ¬ a > b := by
  rw [Int.not_lt]
  rw [Int.le_iff_eq_or_lt]
  right
  exact hab

theorem Int.ltz_mul_gtz_then_ltz {a b:Int} (ha: a < 0) (hb: b > 0) : a * b < 0 := by
  rw [← Int.zero_mul b]
  rw [Int.mul_lt_mul_right]
  exact ha
  exact hb

theorem Int.lez_mul_gtz_then_lez {a b:Int} (ha: a ≤ 0) (hb: b > 0) : a * b ≤ 0 := by
  rw [← Int.zero_mul b]
  rw [Int.mul_le_mul_right]
  exact ha
  exact hb

theorem Int.gtz_mul_gtz_then_gtz {a b:Int} (ha: a > 0) (hb: b > 0) : a * b > 0 := by
  simp
  rw [← Int.zero_mul b]
  rw [Int.mul_lt_mul_right]
  exact ha
  exact hb

theorem Int.gez_mul_gtz_then_gez {a b:Int} (ha: a ≥ 0) (hb: b > 0) : a * b ≥ 0 := by
  simp
  rw [← Int.zero_mul b]
  rw [Int.mul_le_mul_right]
  exact ha
  exact hb

@[simp] theorem Int.ne_and_le_iff_lt {a b:Int} : a ≠ b ∧ a ≤ b ↔ a < b := by
  simp
  constructor
  intro h
  rw [Int.le_iff_eq_or_lt] at h
  simp [h.left] at h
  exact h
  intro h
  constructor
  apply Int.ne_of_lt
  exact h
  apply Int.le_of_lt
  exact h

theorem Int.sub_ltz_iff_lt {a b:Int}: a - b < 0 ↔ a < b := by
  constructor
  <;>intro h
  apply Int.lt_of_sub_lt_sub_right (c:=b)
  rw [Int.sub_self]
  exact h
  rw [Int.sub_lt_iff]
  simp
  exact h

theorem Int.lt_iff_gt {a b:Int} : a < b ↔ b > a := by
  simp

theorem Int.mul_gtz_gtz_then_gtz {a b:Int} (hb: b > 0): a * b > 0 → a > 0 := by
  intro h
  rcases Int.lt_trichotomy a 0 with ha|ha|ha
  have : a * b < 0 := by
    apply Int.ltz_mul_gtz_then_ltz
    exact ha
    exact hb
  exfalso
  apply lt_then_not_gt (a:=a*b) (b:=0)
  exact this
  exact h
  exfalso
  rw [ha] at h
  simp at h
  exact ha

theorem Int.mul_gtz_ltz_then_ltz {a b:Int} (hb: b > 0): a * b < 0 → a < 0 := by
  intro h
  rcases Int.lt_trichotomy a 0 with ha|ha|ha
  exact ha
  rw [ha] at h
  simp at h
  have : a * b > 0 := gtz_mul_gtz_then_gtz ha hb
  exfalso
  apply lt_then_not_gt (a:=a*b) (b:=0)
  exact h
  exact this
