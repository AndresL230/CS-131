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
  induction n with
  | zero =>  rw [Nat.pow_zero]
             apply Nat.zero_le
  | succ k ih =>
    rw [Nat.pow_succ]
    rw [Nat.mul_comm, Nat.two_mul]
    apply Nat.le_trans
    · apply Nat.add_le_add_right
      apply ih
    · apply Nat.add_le_add_left
      apply Nat.one_le_two_pow

-- Problem 2, (15 points)
-- Consider the sequence (a_n)_{n ∈ N} defined by
-- a_0 = 3, a_n+1 = a_n + 9 for all n ∈ N.
-- Define a function problem2seq : ℕ → ℕ such that
-- problem2seq(n) = a_n for all n ∈ ℕ.

def problem2seq : ℕ  → ℕ
| 0 => 3
| n+1 => problem2seq n + 9

-- Prove that for all n ∈ ℕ, a_n = 3 + 9*n.

theorem problem2 (n : ℕ ) : problem2seq n = 3 + 9 * n := by
 induction n with
| zero => unfold problem2seq
          rfl
| succ n ih =>
          unfold problem2seq
          rw [ih]
          rw [Nat.mul_succ,Nat.add_assoc]
