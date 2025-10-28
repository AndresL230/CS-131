import Mathlib


theorem problem_1_sol : ∀ (a b : Prop), ((b → a) ∧ b) → a := by
intro a b ⟨hba,hb⟩
apply hba
exact hb

#eval 19 + 20
