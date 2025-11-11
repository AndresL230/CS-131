import Mathlib

-- The Lean example from lab on Nov 5 may be helpful
-- You can  use the tactics we learned in class, including:
-- rw, induction, exists, apply, have, rfl, unfold.

-- You can use the theorems listed below in this part of the homework.
-- Nat.pow_succ : ∀ (a : ℕ) (n : ℕ), a^(n + 1) = a^n*a
-- Nat.mul_comm : ∀ (a b : ℕ), a * b = b * a
-- Nat.two_mul : ∀ (n : ℕ), 2 * n = n + n
-- Nat.one_le_two_pow : ∀ (n : ℕ), 1 ≤ 2^n
-- Nat.add_le_add_left : ∀ {a b c : ℕ}, a ≤ b → c + a ≤ c + b
-- Nat.add_le_add_right : ∀ {a b c : ℕ}, a ≤ b → a + c ≤ b + c
-- Nat.le_trans : ∀ {a b c : ℕ}, a ≤ b → b ≤ c → a ≤ c
-- Nat.mul_succ : ∀ (a b : ℕ), a * (b + 1) = a * b + a
-- Nat.add_assoc : ∀ (a b c : ℕ), a + b + c = a + (b + c)


-- Problem 1, (20 points)
-- Prove that for all n ∈ ℕ, 2^n ≥ n.

theorem problem1 (n : ℕ) : 2^n ≥ n := by
sorry


-- Problem 2, (15 points)
-- Consider the sequence (a_n)_{n ∈ N} defined by
-- a_0 = 3, a_n+1 = a_n + 9 for all n ∈ N.
-- Define a function problem2seq : ℕ → ℕ such that
-- problem2seq(n) = a_n for all n ∈ ℕ.

def problem2seq : ℕ  → ℕ
| 0 => sorry
| n+1 => sorry

-- Prove that for all n ∈ ℕ, a_n = 3 + 9*n.

theorem problem2 (n : ℕ ) : problem2seq n = 3 + 9 * n := by
sorry
