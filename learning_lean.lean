import Mathlib

-- ============================================================================
-- LEAN 4 PRACTICE FILE - CS 131 Study Guide
-- ============================================================================
-- This file contains examples and practice problems organized by topic.
-- Start from the top and work your way down!
-- ============================================================================

-- ============================================================================
-- SECTION 1: BASIC TACTICS - PROPOSITIONAL LOGIC
-- ============================================================================

-- Example 1: Using rw (rewrite) tactic
-- Shows how to chain logical equivalences
theorem example1 {a b c : Prop} : (¬ (a ∧ b ∧ c)) = (a → (b → ¬ c)) := by
  calc
  (¬ (a ∧ (b ∧ c))) = (¬ a ∨ ¬ (b ∧ c)) := by rw [not_and_or]
  (¬ a ∨ ¬ (b ∧ c)) = (¬ a ∨ (¬ b ∨ ¬ c)) := by rw [not_and_or]
  (¬ a ∨ (¬ b ∨ ¬ c)) = (a → (¬ b ∨ ¬ c)) := by rw [← imp_iff_not_or]
  (a → (¬ b ∨ ¬ c)) = (a → (b → ¬ c)) := by rw [← imp_iff_not_or]

-- Example 2: Shorter version without calc
theorem example1_short {a b c : Prop} : (¬ (a ∧ b ∧ c)) = (a → (b → ¬ c)) := by
  rw [not_and_or, not_and_or, ← imp_iff_not_or, ← imp_iff_not_or]

-- PRACTICE 1: Fill in the rewrites
theorem practice1 {a b c : Prop} : (a → (b ∧ c)) = ((a → b) ∧ (a → c)) := by
  calc
  (a → (b ∧ c)) = (¬ a ∨ (b ∧ c)) := by sorry
  _             = ((¬ a ∨ b) ∧ (¬ a ∨ c)) := by sorry
  _             = ((a → b) ∧ (¬ a ∨ c)) := by sorry
  _             = ((a → b) ∧ (a → c)) := by sorry

-- PRACTICE 2: Complete this proof
theorem practice2 {a b c : Prop} : (a → (b → c)) = ((a ∧ b) → c) := by
  sorry

-- ============================================================================
-- SECTION 2: INTRO, APPLY, EXACT - WORKING WITH IMPLICATIONS
-- ============================================================================

-- Example 3: Using intro to introduce hypotheses
theorem example3 {a b c : Prop} : (a ∧ (a → b) ∧ (b → c)) → c := by
  intro ⟨ha, hab, hbc⟩  -- pattern matching to break apart conjunction
  apply hbc             -- apply implication b → c
  apply hab             -- apply implication a → b
  exact ha              -- we have a!

-- Example 4: Different style using intro without pattern matching
theorem example4 {a b c : Prop} : (a → (b ∧ c)) → ((a ∧ a) → (b ∧ c)) := by
  intro h1              -- introduce the first implication
  intro ⟨h2, h3⟩        -- introduce the conjunction a ∧ a
  apply h1              -- apply h1 : a → (b ∧ c)
  exact h2              -- we need to provide a, which is h2

-- PRACTICE 3: Fill in the tactics
theorem practice3 {a b c : Prop} : ((a → c) ∧ (b → c)) → ((a ∧ b) → c) := by
  intro ⟨h1, h2⟩ ⟨h3, h4⟩
  sorry  -- complete this

-- PRACTICE 4: Prove this yourself
theorem practice4 {a b : Prop} : (a → b) → (a ∧ a) → b := by
  sorry

-- ============================================================================
-- SECTION 3: REAL NUMBER ALGEBRA
-- ============================================================================

-- Example 5: Proving algebraic identity
theorem example5 {a b : ℝ} : a * b = 0 → (a + b)^2 = a^2 + b^2 := by
  intro h
  calc (a + b)^2 = (a + b) * (a + b) := by rw [pow_two]
    _ = a * (a + b) + b * (a + b) := by rw [add_mul]
    _ = (a * a + a * b) + b * (a + b) := by rw [mul_add]
    _ = (a * a + a * b) + (b * a + b * b) := by rw [mul_add]
    _ = (a * a + a * b) + (a * b + b * b) := by rw [mul_comm b a]
    _ = ((a * a + a * b) + a * b) + b * b := by rw [← add_assoc]
    _ = (a * a + (a * b + a * b)) + b * b := by rw [← add_assoc]
    _ = (a * a + a * b * 2) + b * b := by rw [← mul_two]
    _ = (a * a + 0 * 2) + b * b := by rw [h]
    _ = (a * a + 0) + b * b := by rw [zero_mul]
    _ = a * a + b * b := by rw [add_zero]
    _ = a^2 + b * b := by rw [pow_two]
    _ = a^2 + b^2 := by rw [← pow_two]

-- PRACTICE 5: Complete this algebra proof
theorem practice5 {a d : ℝ} : ((d + a) + (a - d)) = (2 * a) := by
  calc
  ((d + a) + (a - d)) = ((d + a) + ((0 - d) + a)) := by rw [zero_sub_add_eq_sub]
  _                   = sorry  -- continue the chain

-- PRACTICE 6: Prove this (harder)
theorem practice6 {a b : ℝ} : b * b = 0 → (a + b)^2 = a^2 := by
  sorry

-- ============================================================================
-- SECTION 4: WORKING WITH CONJUNCTIONS AND CASES
-- ============================================================================

-- Example 6: Using constructor to prove conjunction
theorem example6 {p q : Prop} : (p ∧ q) → (q ∧ p) := by
  intro h
  cases h with
  | intro hp hq =>
    constructor  -- splits goal q ∧ p into two subgoals
    exact hq     -- prove q
    exact hp     -- prove p

-- Example 7: Using .left and .right
theorem example7 {p q : Prop} : (p ∧ q) → (q ∧ p) := by
  intro h
  constructor
  exact h.right  -- access right part of conjunction
  exact h.left   -- access left part of conjunction

-- PRACTICE 7: Prove this using constructor
theorem practice7 {a b c : Prop} : (a ∧ b) → (b ∧ a) := by
  sorry

-- ============================================================================
-- SECTION 5: EXISTENTIAL QUANTIFIERS
-- ============================================================================

-- Example 8: Proving existence
theorem example8 : Even 16 := by
  unfold Even
  exists 8
  -- Lean automatically proves 16 = 8 + 8

-- Example 9: Working with existentials
theorem example9 : ∀ y : ℝ, ∃ x : ℝ, 2 * x + 3 = y := by
  intro y
  exists ((y - 3) / 2)
  rw [mul_div_cancel₀]
  rw [sub_add_cancel]
  exact two_ne_zero

-- PRACTICE 8: Prove this
theorem practice8 : ∃ x : ℕ, x + 5 = 12 := by
  sorry

-- ============================================================================
-- SECTION 6: BASIC INDUCTION
-- ============================================================================

-- Example 10: Simple induction proof
def myseq : ℕ → ℕ
| 0 => 0
| n + 1 => myseq n + 2

theorem example10 (n : ℕ) : myseq n = 2 * n := by
  induction n with
  | zero =>
    unfold myseq
    rfl
  | succ k ih =>
    unfold myseq
    rw [ih]
    rw [mul_add]

-- Example 11: Induction with inequality
theorem example11 (n : ℕ) : 2^n ≥ n := by
  induction n with
  | zero =>
    rw [Nat.pow_zero]
    apply Nat.zero_le
  | succ k ih =>
    rw [Nat.pow_succ]
    rw [Nat.mul_comm, Nat.two_mul]
    apply Nat.le_trans
    · apply Nat.add_le_add_right
      apply ih
    · apply Nat.add_le_add_left
      apply Nat.one_le_two_pow

-- PRACTICE 9: Define sequence and prove formula
def practice9seq : ℕ → ℕ
| 0 => sorry  -- should be 3
| n + 1 => sorry  -- should be practice9seq n + 9

theorem practice9 (n : ℕ) : practice9seq n = 3 + 9 * n := by
  sorry

-- PRACTICE 10: Induction proof
theorem practice10 (n : ℕ) : 2^n ≥ 2 * n := by
  sorry

-- ============================================================================
-- SECTION 7: INDUCTION WITH CASE ANALYSIS
-- ============================================================================

-- Example 12: Induction with cases for edge cases
theorem example12 (n : ℕ) : 2^n ≥ 2 * n := by
  induction n with
  | zero => simp
  | succ k ih =>
    cases k with
    | zero => simp  -- handle k = 0 (so succ k = 1) separately
    | succ m =>     -- true inductive case (k = m+1)
      rw [Nat.pow_succ]
      rw [Nat.mul_comm, Nat.two_mul]
      apply Nat.le_trans
      · apply Nat.add_le_add_right ih
      · apply Nat.add_le_add_left
        rw [Nat.succ_le_iff]
        apply Nat.one_lt_two_pow'

-- PRACTICE 11: Complete this induction with case analysis
theorem practice11 (n : ℕ) : 3^n ≥ 3 * n := by
  induction n with
  | zero => sorry
  | succ k ih =>
    cases k with
    | zero => sorry
    | succ m => sorry

-- ============================================================================
-- SECTION 8: WORKING WITH INEQUALITIES
-- ============================================================================

-- Example 13: Using transitivity
theorem example13 : ∀ (x y : ℝ), (0 ≤ x) ∧ (0 ≤ y) ∧ x ≤ y → x^2 ≤ y^2 := by
  intro x y ⟨h1, h2, h3⟩
  rw [pow_two, pow_two]
  apply le_trans
  apply mul_le_mul_of_nonneg_left
  exact h3
  exact h1
  apply mul_le_mul_of_nonneg_right
  exact h3
  exact h2

-- PRACTICE 12: Use have to create intermediate lemma
theorem practice12 {a b c : ℝ} : a ≤ b → b ≤ c → a ≤ c := by
  intro h1 h2
  -- Use le_trans here
  sorry

-- ============================================================================
-- SECTION 9: SET THEORY
-- ============================================================================

-- Example 14: Set equality proof
theorem example14 {U} {A B : Set U} : (A \ (B ∩ A)) = (A \ B) := by
  rw [Set.ext_iff]
  intro x
  calc x ∈ (A \ (B ∩ A)) ↔ (x ∈ A ∧ x ∉ (B ∩ A)) := by rw [Set.mem_diff]
    _ ↔ (x ∈ A ∧ ¬(x ∈ B ∧ x ∈ A)) := by rw [Set.mem_inter_iff]
    _ ↔ (x ∈ A ∧ ((x ∉ B) ∨ (x ∉ A))) := by rw [not_and_or]
    _ ↔ (x ∈ A ∧ x ∉ B) ∨ (x ∈ A ∧ x ∉ A) := by rw [and_or_left]
    _ ↔ (x ∈ A ∧ x ∉ B) ∨ False := by rw [and_not_self_iff]
    _ ↔ (x ∈ A ∧ x ∉ B) := by rw [or_false]
    _ ↔ (x ∈ (A \ B)) := by rw [Set.mem_diff]

-- PRACTICE 13: Set theory proof
theorem practice13 {U} {A B : Set U} : A ∩ B = B ∩ A := by
  sorry

-- ============================================================================
-- SECTION 10: ADVANCED - STRENGTHENED INDUCTION
-- ============================================================================

-- Example 15: Fibonacci definition
def fib : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n

-- Example 16: Fibonacci is increasing
theorem fib_increasing (n : Nat) : fib n ≤ fib (n + 1) := by
  cases n with
  | zero =>
    unfold fib
    apply Nat.le_succ
  | succ m =>
    cases m with
    | zero =>
      unfold fib
      unfold fib
      apply Nat.le_refl
    | succ l =>
      unfold fib
      have h1 : fib (l + 1 + 1) = fib (l + 1) + fib l := by rfl
      rw [h1]
      apply Nat.le_add_right

-- Example 17: Using strengthened induction hypothesis
-- Proving: fib(n+2) ≥ (1.5)^n requires proving BOTH:
--   fib(n+2) ≥ (1.5)^n AND fib(n+3) ≥ (1.5)^(n+1)
-- This example shows the pattern (simplified version)

-- PRACTICE 14: Complete a strengthened induction
-- Try proving something about Fibonacci or another recursive sequence

-- ============================================================================
-- SECTION 11: EXISTENTIAL PROOFS IN INDUCTION
-- ============================================================================

-- Example 18: Proving divisibility with exists
theorem example18 : ∀ n : ℕ, ∃ m : ℕ, n^3 + 2 * n = 3 * m := by
  intro n
  induction n with
  | zero =>
    exists 0
  | succ k ih =>
    cases ih with
    | intro m hm =>
      exists (m + (k^2 + k + 1))
      -- Would need helper_lemma here in full proof
      sorry

-- PRACTICE 15: Prove divisibility
theorem practice15 : ∀ n : ℕ, ∃ m : ℕ, 2 * n = 2 * m := by
  sorry

-- ============================================================================
-- SUMMARY OF KEY TACTICS
-- ============================================================================

/-
rw [thm]          - Rewrite using theorem
rw [← thm]        - Rewrite backwards
intro h           - Introduce hypothesis
intro ⟨h1, h2⟩    - Introduce and pattern match
apply thm         - Apply theorem to goal
exact h           - Prove goal with exact match
calc              - Chain of equalities/inequalities
constructor       - Split conjunction into subgoals
cases h           - Case analysis on hypothesis
exists val        - Provide witness for existential
have h: P := by   - Introduce local lemma
unfold def        - Expand definition
rfl               - Reflexivity (definitional equality)
simp              - Simplification
induction n with  - Induction on n
nth_rw n [thm]    - Rewrite nth occurrence

Access parts:
h.left, h.right   - For conjunctions
-/

-- ============================================================================
-- QUICK REFERENCE: COMMON THEOREMS
-- ============================================================================

/-
LOGIC:
imp_iff_not_or, not_and_or, not_or
or_and_left, and_or_left
or_assoc, and_assoc, or_comm, and_comm
and_not_self_iff, or_false, and_true, and_false

REAL NUMBERS:
add_zero, zero_add, add_comm, add_assoc
mul_zero, zero_mul, mul_add, add_mul, mul_comm
pow_two, two_mul, sub_self

NATURAL NUMBERS:
Nat.pow_succ, Nat.mul_comm, Nat.two_mul
Nat.add_le_add_left, Nat.add_le_add_right
Nat.le_trans, Nat.le_refl, Nat.le_succ
Nat.zero_le, Nat.one_le_two_pow

SETS:
Set.ext_iff, Set.mem_diff, Set.mem_inter_iff, Set.mem_union
-/

-- ============================================================================
-- NOW GO PRACTICE! Start with practice1 and work through each section.
-- ============================================================================
