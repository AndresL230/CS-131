import Mathlib
open Nat

-- You can find below three different proofs of the theorem
-- we discussed in class: 2^n ≥ 2*n for all natural numbers n.
-- These proofs have the same structure, first induction and then
-- case analysis. Their main differences are in the way the
-- inductive step is handled.

theorem problem3 (n : ℕ) : 2^n ≥ 2*n := by
-- As we have already seen before, to proceed by induction we
-- can use the `induction` tactic. As a reminder, we need to provide
-- the variable we want to perform induction on (here `n`), and
-- the tactic will generate two subgoals: the base case (n=0)
-- and the inductive step (n = k+1, assuming the property holds
-- for k). To
  induction n with
-- this is the base case, P(0), which corresponds to n = 0
-- and so we need to prove that 2^0 ≥ 2*0.
  | zero =>  simp
-- this is the inductive step, P(k+1). Here we have an
-- additional hypothesis `ih`, which corresponds to the
-- inductive hypothesis, i.e., the assumption that the property
-- holds for k: 2^k ≥ 2*k. Our goal is to prove P(k+1):
-- 2^(k+1) ≥ 2*(k+1).
  | succ k ih =>
-- as we saw in class, to proceed we can perform case analysis
-- on k. So that we can treat the case P(1) separately
-- from the truly inductive case.
-- Case analysis on k can be done with the `cases` tactic,
-- which will generate two subgoals: one for the case
-- k = 0, and one for the case k = m+1 (for some m).
    cases k with
-- this is the case k = 0, but remember that what we need to
-- prove is P(k+1), so in particular what we need to prove is P(1).
    | zero => simp
-- this is the case k > 0, which we can state as k = m+1 for some m,
-- this is why we use a new variable m.
-- Here again we need to prove P(k+1), which we can now think of
-- as P(m+2). Our assumption is the inductive hypothesis ih,
-- which states that P(k) holds, but since k = m+1, we can
-- think of ih as stating that P(m+1) holds.
    | succ m =>
-- the rest of the proof are just few mathematical manipulations,
-- which we can do using rewriting and applying known lemmas.
      rw [Nat.pow_succ]
      rw [Nat.mul_comm, Nat.two_mul]
-- as we did in class, we need to use transitivity of ≤ to split
-- the goal into two parts.
      apply Nat.le_trans
-- Here we use the inductive hypothesis ih to prove the first part
-- of the inequality. Note that ih states that 2^(m+1) ≥ 2*(m+1),
-- which is exactly what we need here.
      · apply Nat.add_le_add_right ih
-- Here we need to prove the second part of the inequality.
-- Notice that here is where we really use that k ≥ 1, which
-- in this case is m+1 ≥ 1.
      · apply Nat.add_le_add_left
        rw [Nat.succ_le_iff]
        apply Nat.one_lt_two_pow'

-- Here another proof of the same theorem, with a slightly different
-- approach in the inductive step. This is similar to the proof
-- we discussed in class. This doesn't use transitivity of ≤ explicitly
-- but this is done implicitly by the use of `calc`, when we use ≥ instead of =.
theorem pow2_ge_twotimes (n : ℕ) : 2^n ≥ 2*n := by
  induction n with
  | zero =>  simp -- base case, P(0): 2^0 = 1 ≥ 0
  | succ k IH =>  -- inductive step, IH = assume P(k) holds: 2^k ≥ 2*k
                  -- we need to prove P(k+1): 2^(k+1) ≥ 2*(k+1)
    cases k with
    | zero => simp -- case k=0, P(1): 2^1 = 2 ≥ 2*1
    | succ m =>    -- case k=m+1, P(k+1): 2^(m+2) ≥ 2*(m+2)
      have h : 2 ≤ 2 * (m+1) := by grind
      calc 2^(m+1+1) = 2*2^(m+1) := by rw [pow_succ,mul_comm]
        _            ≥ 2*(2*(m+1)) := by apply mul_le_mul_left' IH
        _            = 2*(m+1) + 2*(m+1) := by rw [two_mul]
        _            ≥ 2*(m+1) + 2*1 := by apply add_le_add_left h
        _            = 2*(m+1+1) := by rw [<- mul_add]


-- Yet another proof of the same theorem, similar to the previous one,
-- but using rewriting instead of `calc` in the inductive step.
-- This proof is similar to the previous one but without using `calc`.
theorem pow2_ge_twotimes_1 (n : ℕ) : 2^n ≥ 2*n := by
  induction n with
  | zero =>  simp -- base case, P(0): 2^0 = 1 ≥ 0
  | succ k IH =>  -- inductive step, IH = assume P(k) holds: 2^k ≥ 2*k
                  -- we need to prove P(k+1): 2^(k+1) ≥ 2*(k+1)
    cases k with
    | zero => simp -- case k=0, P(1): 2^1 = 2 ≥ 2*1
    | succ m =>    -- case k=m+1, P(k+1): 2^(m+2) ≥ 2*(m+2)
      rw [Nat.pow_succ,Nat.mul_comm]
      apply Nat.mul_le_mul_left
      apply Nat.le_trans
-- The nextline tells Lean to focus on the second goal, rather than the first one.
      pick_goal 2
      apply IH
      rw [Nat.two_mul]
      apply add_le_add_left
      apply Nat.succ_le_succ
      apply Nat.zero_le
