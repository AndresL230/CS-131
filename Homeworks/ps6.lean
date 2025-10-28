import Mathlib.Logic.Basic
import Mathlib.Data.Real.Basic

-- This file contains problems for Problem Set 6 for CS131
-- This contains 5 problems that needs to be completed using Lean.

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

-- Also, here a reminder of the tactics we saw in class that you may need to use:
-- rw
-- intro
-- apply
-- exact
-- have
-- calc
-- nth_rw


-- *****************Problem 1**************
--      (This problem is worth 20 points)
-- Write a proof for the following theorem.
-- This theorem doesn't state
-- an equality, and cannot be solved just using rw.
-- The proof of this theorem requires you to work with some of the
-- other tactics we saw in class.


theorem problem_1 {a b c : Prop} :  (a →  (b ∧  c)) →  ((a ∧ a) →  (b ∧ c)) :=
  by

  intro h1
  intro h2
  apply h1
  exact h2.1




-- *****************Problem 2**************
--      (This problem is worth 20 points)
-- Write a proof for the following theorem.
-- Similarly to the previous problem, this theorem doesn't state
-- an equality, and cannot be solved just using rw.
-- The proof of this theorem requires you to work with some of the
-- other tactics we saw in class.



theorem problem_2  {a b c:Prop} :  ((a →  c) ∧  (b → c)) →  ((a ∧ b) →  c) :=
  by

  intro h1
  intro h2
  apply h1.1
  exact h2.1

-- The next set of problems focuses on real numbers.

-- You can use the theorems listed below.
-- sub_self {a :ℝ}: a - a = 0
-- zero_add {a :ℝ}: 0 + a = a
-- add_zero {a :ℝ}: a + 0 = a
-- add_comm {a b :ℝ}: a + b = b + a
-- add_assoc {a b c :ℝ}: (a + b) + c = a + (b + c)
-- mul_self_eq_zero {a :ℝ}: a * a = 0 ↔ a = 0
-- mul_zero {a :ℝ}: a * 0 = 0
-- zero_mul {a :ℝ}: 0 * a = 0
-- zero_sub_add_eq_sub {a b :ℝ}: (0 - a) + b = b - a
-- add_mul {a b c :ℝ}: (a + b) * c = a * c + b * c
-- mul_add {a b c :ℝ}: a * (b + c) = a * b + a * c
-- pow_two {a :ℝ}: a^2 = a * a
-- two_mul {a :ℝ}: 2 * a = a + a
-- mul_self {a :ℝ}: a^2 = a * a


-- *****************Problem 3**************
--      (This problem is worth 20 points)
-- Use the tactic rw to fill in the justifications for the steps
-- of the proofs of the following theorem in Lean. You may
-- also need to use the tactic nth_rw we saw in class.
-- This tactic takes as a parameter a number that is used
-- to rewrite specific occurrences of an expression in a line.
-- This number is the number of nested parentheses surrounding
-- the expression you want to rewrite, counting from the outside.
-- For example, in the expression (a + (b + (c + d))), the innermost
-- expression is c + d, which has 3 nested parentheses.

theorem problem_3 {a d : ℝ} : ((d + a) + (a - d))  = (2 * a)  := by
calc
  ((d + a) + (a - d)) = ((d + a) + ((0 - d) + a)) := by rw[zero_sub_add_eq_sub]
  _                 = ((a + d) + ((0 - d) + a)) := by nth_rw 1 [add_comm d a]
  _                 = (a + (d + ((0 - d) + a))) := by rw[add_assoc]
  _                 = (a + ((d + (0 - d)) + a)) := by rw[add_assoc]
  _                 = (a + (((0 - d) + d) + a)) := by nth_rw 3 [add_comm]
  _                 = (a + ((d - d) + a)) := by rw[zero_sub_add_eq_sub]
  _                 = (a + (0 + a)) := by rw[sub_self]
  _                 = (a + a) := by rw[zero_add]
  _                 = (2 * a) := by rw[two_mul]


-- *****************Problem 4**************
--      (This problem is worth 20 points)
-- Write a proof for the following theorem.
-- For this proof, you may need to use several of the
-- tactics we saw in class as well as some of the results
-- you proved in previous problems.

theorem problem_4 {a b c d : ℝ} : (c = (d + a) + b) →  (b = a - d) → c = 2 * a  :=
  by

  intro h1
  intro h2

  calc
    c = (d + a) + b := h1
    _ = (d+a) + (a-d) := by rw[h2]
    _ = 2 * a := problem_3


-- *****************Problem 5**************
--      (This problem is worth 20 points)
-- Write a proof for the following theorem.
-- The proof of this theorem is similar to a proof we saw in class.
-- However, you may need to prove some additional lemma to complete the proof.
-- Remember how we stated and proved lemmas in class using the tactic have.

theorem problem_5 {a b :ℝ } : (b*b=0) → (a+b)^2 = a^2 := by
  intro h

  have hb : b = 0 := by
    rw [← mul_self_eq_zero]
    exact h

  calc
    (a + b)^2 = (a + b) * (a + b) := by rw [pow_two]
    _ = (a + 0) * (a + 0) := by rw [hb]
    _ = a * a := by rw [add_zero]
    _ = a^2 := by rw [← pow_two]
