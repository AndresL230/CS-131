import Mathlib


def problem1seq : ℕ→ℕ := sorry

-- This defines the sequence {0,2,4,6,...}

theorem problem1 (n : ℕ ) : problem1seq n = 2*n := by sorry

theorem helper_lemma {k : ℕ} :
  (k + 1)^3 + 2*(k + 1) = k^3 + 2*k + 3*(k^2 + k + 1) := by sorry

theorem problem2 : ∀ n :ℕ, ∃ m :ℕ, n^3 + 2*n = 3*m := by sorry

theorem problem3 (n : ℕ) : 2^n ≥ 2*n := by sorry
