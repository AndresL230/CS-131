import Mathlib.Logic.Basic
import Mathlib.Data.Real.Basic


theorem problem_1_sol {p q r : Prop} : (p → r) → ((p ∧ q) → r) := by
  intro h ⟨hp, hq⟩
  apply h
  exact hp


theorem problem_2_sol {x y : ℝ} : (x + (y - x)) = y := by
calc
  x + (y - x) = x + ((0 - x) + y) := by rw [zero_sub_add_eq_sub]
  _           = (x + (0 - x)) + y := by rw [add_assoc]
  _           = ((0 - x) + x) + y := by nth_rw 2 [add_comm]
  _           = (x - x) + y := by rw [zero_sub_add_eq_sub]
  _           = 0 + y := by rw [sub_self]
  _           = y := by rw [zero_add]



theorem problem_3_sol {a b c : Prop} : (a →  c) ∧  (b → c) →  (a ∧ b) →  c := by
  intro ⟨h1,h2⟩ ⟨h3, h4⟩
  apply h1
  exact h3



theorem problem_4_sol {p q r s : Prop} : ((p → r) ∧ (q → r)) → ((p ∧ q) ∧ s → r) := by
  intro h1 ⟨hpq, hs⟩
  apply problem_3_sol h1
  exact hpq
