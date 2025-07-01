import Mathlib.Tactic.Use
import Mathlib.Tactic.ApplyAt
import Batteries.Tactic.Init

example :∃ a, a > 1 := by
  use 2
  simp

example (h : P → Q) (hP : P) : Q := by
  -- 将 `h` 应用于 `hP`
  apply h at hP
  exact hP
