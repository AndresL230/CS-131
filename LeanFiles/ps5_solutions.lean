import Mathlib.Logic.Basic

-- This file contains problems for Problem Set 5 for CS131
-- There are 3 problems that needs to be completed using Lean.

-- We recommend you to use the live version of Lean available at
-- http://live.lean-lang.org/
-- You can either copy paste the code in the live version window or
-- just upload this file to the live version.

-- As a reminder, to type some of the symbols used in the problems,
-- you can use the following shortcuts:
-- ∧ : \and
-- ∨ : \or
-- ¬ : \not
-- → : \to
-- ⟨ : \<
-- ⟩ : \>

-- The problems focus on propositional logic.
-- You can use the theorems listed below in this part of the homework.
-- imp_iff_not_or {a b: Prop}: (a → b) ↔ (¬ a ∨ b)
-- not_and_or {a b: Prop}: ¬(a ∧ b) ↔ ¬a ∨ ¬b
-- not_or {a b : Prop}: ¬(a ∨ b) ↔ ¬a ∧ ¬b
-- or_and_left {a b c : Prop}: a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c)
-- and_or_left {a b c : Prop}: a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c)
-- or_assoc {a b c : Prop}: a ∨ (b ∨ c) ↔ (a ∨ b) ∨ c
-- or_comm {a b : Prop}: a ∨ b ↔ b ∨ a
-- and_assoc {a b c : Prop}: a ∧ (b ∧ c) ↔ (a ∧ b) ∧ c
-- and_comm {a b : Prop}: a ∧ b ↔ b ∧ a

-- *****************Problem 1**************
--      (This problem is worth 33 points)
-- Use the tactic rw to fill in the justifications for the steps
-- of the proofs of the following theorem in Lean.
-- The use of the tactic grind is not allowed in this problem.


theorem problem_1_sol {a b c : Prop} :  (a → (b ∧  c)) = ((a →  b) ∧ (a → c)) := by
calc
  (a → (b ∧ c)) = (¬ a ∨ (b ∧ c)) := by rw [imp_iff_not_or]
  _              = ((¬ a ∨ b) ∧ (¬ a ∨ c)) := by rw [or_and_left]
  _              = ((a → b) ∧ (¬ a ∨ c)) := by rw [<- imp_iff_not_or]
  _              = ((a → b) ∧ (a → c)) := by rw [<- imp_iff_not_or]


-- *****************Problem 2**************
--      (This problem is worth 33 points)
-- Use the tactic rw to fill in the justifications for the steps
-- of the proofs of the following theorem in Lean.
-- The use of the tactic grind is not allowed in this problem.


theorem problem_2_sol {a b c : Prop} :  (a → (b → c)) =  ((a ∧  b) → c) := by
calc
  (a → (b → c)) = (¬ a ∨ (b → c)) := by rw [imp_iff_not_or]
  _             = (¬ a ∨ (¬ b ∨ c)) := by rw [imp_iff_not_or]
  _             = ((¬ a ∨ ¬ b) ∨ c) := by rw [or_assoc]
  _             = (¬ (a ∧ b) ∨ c) := by rw [<- not_and_or]
  _             = ((a ∧ b) → c) := by rw [<- imp_iff_not_or]


-- *****************Problem 3**************
--      (This problem is worth 33 points)
-- Write a proof for the following theorem.
-- This theorem doesn't state an equality, and cannot be
-- solved just using rw.
-- The proof of this theorem requires you to work with some of the
-- other tactics we saw in class:
-- intro
-- apply
-- The use of the tactic grind is not allowed in this problem.

theorem problem_3 {a b c: Prop} : ( a ∧ (a → b) ∧ (b → c)) → c := by
intro ⟨ha,hab,hbc⟩
apply hbc
apply hab
apply ha

-- End of the problem set.
