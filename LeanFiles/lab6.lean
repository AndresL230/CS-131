import Mathlib.Logic.Basic
import Mathlib.Data.Real.Basic

theorem problem_1 {p q r : Prop} : (p → r) → ((p ∧ q) → r) := by sorry

theorem problem_2 {x y : ℝ} : (x + (y - x)) = y := by
calc
  x + (y - x) = x + ((0 - x) + y) := by sorry
  _           = (x + (0 - x)) + y := by sorry
  _           = ((0 - x) + x) + y := by sorry
  _           = (x - x) + y := by sorry
  _           = 0 + y := by sorry
  _           = y := by sorry

theorem problem_3 {a b c : Prop} : (a →  c) ∧  (b → c) →  (a ∧ b) →  c := by sorry


theorem problem_4 {p q r s : Prop} : ((p → r) ∧ (q → r)) → ((p ∧ q) ∧ s → r) := by sorry
