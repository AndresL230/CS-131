import Mathlib
open Finset

-- Example of induction proving that the sum of the first n natural numbers is n*(n+1)/2
-- This is similar to the proof we did in class but this is on naturals instead of
-- positive integers.

-- The statement of the theorem uses the notation
-- `∑ x ∈ range (n + 1), x`
-- to denote the sum of the first n natural numbers.
-- The function range (n + 1) generates the set {0, 1, 2, ..., n}.

theorem sum_id (n : ℕ) : ∑ x ∈ range (n + 1), x = (n + 1)* n / 2 := by
-- The following line tell to lean to perform induction on n,
  induction n with
-- The tactic `induction n with` is what we use to specify which variable we want to
-- perform induction on. In our case, we are performing induction on the natural number n.
-- When we use induction on natural numbers in lean we don't have the option to choose
-- the base case. It has to be 0, which is what the following line specifies.
  | zero =>
-- Since we are proving the statement for n = 0, everything becomes concrete and lean can
-- compute both sides of the equation directly. The tactic `simp` tells lean to simplify
-- both sides of the equation and check if they are equal. We can finish the base case with
-- this tactic.
    simp
-- The next line specifies the inductive step. Here we are specifying two names
-- for the assumptions we have. First we can choose a name for the variable corresponding
-- to the inductive hypothesis. Similarly to what we did in class, I chose the name k.
-- The second name will be the name we associate with the induction hypothesis which
-- is the assumption that the statement holds for n = k. In this case, I chose the name IH,
  | succ k IH =>
-- Notice that now we have in our assumptions k which is an arbitrary natural number,
-- and IH, which stated that the statement holds for n = k.
-- Our goal is to prove that the statement holds for n = k + 1.

-- Similarly to what we did in class, we start by rewriting the sum in the left hand side of
-- the equation to separate the last term of the sum. We can do this using the lemma
-- `Finset.sum_range_succ`. In our case we use it for rewriting the sum up to k + 1.
-- That is: ∑ x ∈ range (k + 1 + 1), x = (∑ x ∈ range (k + 1), x) + (k + 1)
-- remember that range (k + 1 + 1) = {0, 1, ..., k, k + 1} and
-- range (k + 1) = {0, 1, ..., k}
    rw [Finset.sum_range_succ]
-- Now we can use the induction hypothesis IH to rewrite the sum up to k.
-- That is, we can replace (∑ x ∈ range (k + 1), x) with (k + 1)* k / 2
    rw [IH]
-- Now we need to manipulate the equation to show that both sides are equal.
-- We start by rewriting the right hand side to generate a common denominator.
    rw [<- Nat.add_mul_div_right]
-- This tactic generates also a second goal which is to prove that the denominator
-- is not zero. In our case the denominator is 2, so we can finish this second goal
-- by showing that 2 is greater than 0. We will do this at the end of the proof.
-- Now we continue manipulating the equation.
-- We rewrite the right hand side using distributivity of multiplication over addition
-- to grup together (k+2).
    rw [<- mul_add]
-- We are almost done. Now we just need to rewrite the multiplication to have the
-- (k + 2) factor first.
    rw [mul_comm]
-- Now both sides of the equation are the same, so we have finished the main goal.
-- We just need to finish the second goal we generated before, which is to show that
-- 2 is greater than 0.
-- We can do this by applying the lemma `zero_lt_two` which states exactly that.
    apply zero_lt_two
