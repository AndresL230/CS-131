import Mathlib


def problem1seq : ℕ→ℕ
| 0 => 0
| n+1 => (problem1seq n) + 2

-- This defines the sequence {0,2,4,6,...}

theorem problem1 (n : ℕ) : problem1seq n = 2*n := by
induction n with
| zero =>
   unfold problem1seq
   rfl
| succ n ih =>
   unfold problem1seq
   rw [ih]
   rw [mul_add]

theorem helper_lemma {k : ℕ} :
  (k + 1)^3 + 2*(k + 1) = k^3 + 2*k + 3*(k^2 + k + 1) := by
  ring

theorem problem2 : ∀ n :ℕ, ∃ m :ℕ, n^3 + 2*n = 3*m := by
  intro n
  induction n with
  | zero =>
    exists 0
  | succ k ih =>
    cases ih with
    | intro m hm =>
      exists (m + (k^2 + k + 1))
      rw [helper_lemma]
      rw [hm]
      rw [<- mul_add]

theorem problem3 (n : ℕ) : 2^n ≥ 2*n := by
  induction n with
  | zero =>  simp
  | succ k ih =>
    rw [pow_succ]
    rw [mul_comm, two_mul]
    cases k with
    | zero => simp
    | succ m =>
      apply Nat.le_trans
      · apply Nat.add_le_add_right ih
      · apply Nat.add_le_add_left
        rw [Nat.succ_le_iff]
        apply Nat.one_lt_two_pow'
