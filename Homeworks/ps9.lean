import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic

-- Submission Instructions: please upload your solution based on this template to
-- gradescope as a single lean file named ps9.lean

-- Please do not change the template, just fill in the missing proofs.

-- Consider the sequence defined by the following recurrence relation:
-- Notice that this is a sequence of integers, that is myseq is a function
-- Nat → Int from natural numbers to integers.

def myseq: Nat → Int
| 0 => 0
| 1 => 1
| n+2 => (5 * (myseq (n+1))) - (6 * (myseq n))

-- For this problem set, you will need to prove that
-- myseq n = 3^n - 2^n for all natural numbers n.

-- Here a list of theorems that may be useful in your proof.
-- If you use your mouse to hover over the names of the theorems below,
-- you will see a more general form of the description we give here.
-- pow_zero: (a : ℤ), a ^ 0 = 1
-- pow_one: (a : ℤ), a ^ 1 = a
-- pow_succ: (a : ℤ) (n : ℕ), a ^ (n + 1) = a ^ n * a
-- mul_comm: (a b : ℤ), a * b = b * a
-- mul_assoc: (a b c : ℤ), a * b * c = a * (b * c)
-- sub_mul: (a b c : ℤ), (a - b) * c = a * c - b * c
-- add_comm: (a b : ℤ), a + b = b + a
-- add_sub_assoc: (a b c : ℤ), a + b - c = a + (b - c)
-- sub_sub: (a b c : ℤ), a - b - c = a - (b + c)

-- You may also find useful the following lemmas, which states
-- algebraic identities of powers of 2 and 3.

theorem lemma_1 {k:ℕ }: 6 * (3:ℤ) ^ k = 2 * 3 ^ (k + 1) := by
  rw [pow_succ]
  nth_rw 3 [mul_comm]
  rw [<- mul_assoc]
  rfl

theorem lemma_2 {k:ℕ} : 6 * (2:ℤ) ^ k = 3 * 2 ^ (k + 1) := by
  rw [pow_succ]
  nth_rw 3 [mul_comm]
  rw [<- mul_assoc]
  rfl

  theorem lemma_3 {k:ℕ}  : 5*(2:ℤ)^(k+1) - 3*2^(k+1) = 2^(k+2) := by
   rw [<- sub_mul]
   rw [mul_comm]
   rfl

theorem lemma_4 {k:ℕ}: 5*(3:ℤ)^(k+1) - 2*3^(k+1) = 3^(k+2) := by
    rw [<- sub_mul]
    rw [mul_comm]
    rfl

-- The next lemma combines the previous ones to prove the main step
-- in the induction that you will need to complete the proof of
-- myseq n = 3^n - 2^n for all natural numbers n.
theorem lemma_5 {k:ℕ }:
5 * ((3:ℤ)^ (k + 2) - 2 ^ (k + 2)) - 6 * (3 ^ (k + 1) - 2 ^ (k + 1))
=
3 ^ (k + 3) - 2 ^ (k + 3) := by
  rw [mul_sub]
  rw [mul_sub]
  rw [sub_sub]
  rw [lemma_1, lemma_2]
  rw [<- add_sub_assoc]
  nth_rw 2 [add_comm]
  rw [add_sub_assoc]
  rw [<- sub_sub]
  rw [lemma_4]
  rw [lemma_3]


-- Complete the proof of the main theorem. It may be useful to think
-- about generalizing the statement to have a stronger induction hypothesis.
-- You may want to review the example of lower_bound for the Fibonacci sequence
-- we saw in class.
-- If you setup the induction correctly, you should be able to use
-- lemma_5 in the inductive step to complete the proof without further
-- algebraic manipulations.

-- In the proof you are allowed to use the following tactics:
-- rw, nth_rw, rfl, induction, cases, unfold, rfl, exact, apply,
-- simp, constructor, intros, have, ring, .left, .right


theorem myseq_bound (n : Nat) : myseq (n) = (3^n) - (2^n) := by
  sorry
