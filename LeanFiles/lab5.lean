import Mathlib

theorem problem_1 : ∀ (a b : Prop), ((b → a) ∧ b) → a := by
  sorry

theorem problem_2: ∀ (a b c : Prop), ((b → c → a) ∧ b) → c → a := by
  sorry

theorem problem_3 {a b c d : ℝ} : (a = b) → (c = d) → (a + c) = (b + d) := by
  sorry

-- Example Theorems (Note this is not exhaustive)
-- imp_iff_not_or {a b: Prop}: (a → b) ↔ (¬ a ∨ b)
-- not_and_or {a b: Prop}: ¬(a ∧ b) ↔ ¬a ∨ ¬b
-- not_or {a b : Prop}: ¬(a ∨ b) ↔ ¬a ∧ ¬b
-- or_and_left {a b c : Prop}: a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c)
-- and_or_left {a b c : Prop}: a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c)
-- or_false {p : Prop}: p ∨ False ↔ p
-- or_true {p : Prop}: p ∨ True ↔ True
-- or_assoc {a b c : Prop}: a ∨ (b ∨ c) ↔ (a ∨ b) ∨ c
-- or_comm {a b : Prop}: a ∨ b ↔ b ∨ a
-- and_assoc {a b c : Prop}: a ∧ (b ∧ c) ↔ (a ∧ b) ∧ c
-- and_comm {a b : Prop}: a ∧ b ↔ b ∧ a
-- and_true {p : Prop}: p ∧ True ↔ p
-- and_false {p : Prop}: p ∧ False ↔ False
-- and_not_self_iff {a : Prop}: a ∧ ¬a ↔ False
-- Classical.not_not {a : Prop}: ¬¬a ↔ a

theorem problem_4_fill {a b c d : Prop} :  ((a ∧ (a → (b ∧  c))) ∧ ((b ∧ c) → d))  = (a ∧ (b ∧ (c ∧ d))) := by
calc
  ((a ∧ (a → (b ∧  c))) ∧ ((b ∧ c) → d)) = ((a ∧ (¬ a ∨ (b ∧ c))) ∧ ((b ∧ c) → d)) := by sorry
  _                                   = (((a ∧ ¬ a) ∨ (a ∧ (b ∧ c))) ∧ ((b ∧ c) → d)) := by sorry
  _                                   = ((False ∨ (a ∧ (b ∧ c))) ∧ ((b ∧ c) → d)) := by sorry
  _                                   = ((a ∧ (b ∧ c)) ∧ ((b ∧ c) → d)) := by sorry
  _                                   = ((a ∧ (b ∧ c)) ∧ (¬ (b ∧ c) ∨ d)) := by sorry
  _                                   = (a ∧ ((b ∧ c) ∧ (¬ (b ∧ c) ∨ d))) := by sorry
  _                                   = (a ∧ (((b ∧ c) ∧ (¬ (b ∧ c))) ∨ ((b∧ c) ∧ d))) := by sorry
  _                                   = (a ∧ (False ∨ ((b∧ c) ∧ d))) := by sorry
  _                                   = (a ∧ ((b ∧ c) ∧ d)) := by sorry
  _                                   = (a ∧ (b ∧ (c ∧ d))) := by sorry


 theorem problem_5 {a b c : Prop} :  (a → (b → c)) =  (¬ c → (a→ ¬ b)) := by
 calc
  (a → (b → c)) = (¬ a ∨ (b → c)) := by sorry
  _             = (¬ a ∨ (¬ b ∨ c)) := by sorry
  _             = ((¬ a ∨ ¬ b) ∨ c) := by sorry
  _             = (c ∨ (¬ a ∨ ¬ b)) := by sorry
  _             = ((¬ ¬ c) ∨ (¬ a ∨ ¬ b)) := by sorry
  _             = (¬ c → (¬ a ∨ ¬ b)) := by sorry
  _             = (¬ c → ( a →  ¬ b)) := by sorry

-- Example Theorems (Also not exhaustive)
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

theorem problem_6 {a b : ℝ} : a * b = 0 → (a + b)^2 = (a - b)^2 := by
  sorry
