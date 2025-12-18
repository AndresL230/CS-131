import Mathlib

theorem problem_1_sol : ∀ (a b : Prop), ((b → a) ∧ b) → a := by
intro a b ⟨hba,hb⟩
apply hba
exact hb

theorem problem_2_sol : ∀ (a b c : Prop), ((b → c → a) ∧ b) → (c → a) := by
intro a b c ⟨hbca,hb⟩
apply hbca
exact hb

theorem problem_3_sol {a b c d : ℝ} : (a = b) → (c = d) → (a + c) = (b + d) := by
  intro h1 h2
  calc
    a + c = b + c := by rw [h1]
    _     = b + d := by rw [h2]

theorem problem_3_sol_v2 {a b c d : ℝ} : (a = b) → (c = d) → (a + c) = (b + d) := by
  intro h1 h2
  have h3 : a + c = b + c := by rw [h1]
  have h4 : b + d = b + c := by rw [h2]
  rw [h3]
  rw [h4]

theorem problem_4_sol {a b c d : Prop} :  ((a ∧ (a → (b ∧  c))) ∧ ((b ∧ c) → d))  = (a ∧ (b ∧ (c ∧ d))) := by
 calc
  ((a ∧ (a → (b ∧  c))) ∧ ((b ∧ c) → d)) = ((a ∧ (¬ a ∨ (b ∧ c))) ∧ ((b ∧ c) → d)) := by rw [imp_iff_not_or]
  _                                   = (((a ∧ ¬ a) ∨ (a ∧ (b ∧ c))) ∧ ((b ∧ c) → d)) := by rw [and_or_left]
  _                                   = ((False ∨ (a ∧ (b ∧ c))) ∧ ((b ∧ c) → d)) := by rw [and_not_self_iff]
  _                                   = ((a ∧ (b ∧ c)) ∧ ((b ∧ c) → d)) := by rw [false_or]
  _                                   = ((a ∧ (b ∧ c)) ∧ (¬ (b ∧ c) ∨ d)) := by rw [imp_iff_not_or]
  _                                   = (a ∧ ((b ∧ c) ∧ (¬ (b ∧ c) ∨ d))) := by rw [and_assoc]
  _                                   = (a ∧ (((b ∧ c) ∧ (¬ (b ∧ c))) ∨ ((b∧ c) ∧ d))) := by rw [and_or_left]
  _                                   = (a ∧ (False ∨ ((b∧ c) ∧ d))) := by rw [and_not_self_iff]
  _                                   = (a ∧ ((b ∧ c) ∧ d)) := by rw [false_or]
  _                                   = (a ∧ (b ∧ (c ∧ d))) := by rw [and_assoc]

theorem problem_5_sol {a b c : Prop} :  (a → (b → c)) =  (¬ c → (a→ ¬ b)) := by
 calc
  (a → (b → c)) = (¬ a ∨ (b → c)) := by rw [imp_iff_not_or]
  _             = (¬ a ∨ (¬ b ∨ c)) := by rw [imp_iff_not_or]
  _             = ((¬ a ∨ ¬ b) ∨ c) := by rw [or_assoc]
  _             = (c ∨ (¬ a ∨ ¬ b)) := by rw [or_comm]
  _             = ((¬ ¬ c) ∨ (¬ a ∨ ¬ b)) := by rw [Classical.not_not]
  _             = (¬ c → (¬ a ∨ ¬ b)) := by rw [imp_iff_not_or]
  _             = (¬ c → ( a →  ¬ b)) := by rw [<- imp_iff_not_or]

theorem problem_6_sol {a b : ℝ} : a * b = 0 → (a + b)^2 = (a - b)^2 := by
  intro h
  have h1 : (a + b)^2 = a*a + b*b := by
    calc
      (a + b)^2 = (a + b) * (a + b) := by rw[pow_two]
      _         = (a + b) * a + (a + b) * b := by rw[mul_add]
      _         = (a*a + b*a) + (a + b) * b := by rw[add_mul]
      _         = (a*a + b*a) + (a*b + b*b) := by rw[add_mul]
      _         = (a*a + a*b) + (a*b + b*b) := by nth_rw 2 [mul_comm]
      _         = (a*a + 0) + (0 + b*b) := by rw[h]
      _         = (a*a) + (0+ b*b) := by rw[add_zero]
      _         = (a*a) + (b*b) := by rw[zero_add]
  have h2 : (a - b)^2 = a*a + b*b := by
    calc
      (a - b)^2 = (a - b) * (a - b) := by rw[pow_two]
      _         = (a - b) * a - (a - b) * b := by rw[mul_sub]
      _         = (a*a - b*a) - (a - b) * b := by rw[sub_mul]
      _         = (a*a - b*a) - (a*b - b*b) := by rw[sub_mul]
      _         = (a*a - a*b) - (a*b - b*b) := by nth_rw 2 [mul_comm]
      _         = a*a - a*b - a*b + b*b := by rw[<- sub_add]
      _         = a*a - 0 - 0 + b*b := by rw[h]
      _         = a*a - 0 + b*b := by rw[sub_zero]
      _         = a*a + b*b := by rw[sub_zero]
  rw [h1]
  rw [h2]

-- Version Below with Annotations for Explanations!

-- Place your cursor throughout the proofs to understand what's going on!
-- → separates assumptions and the final clause after a → is always the goal
  -- ie. theorem sample {x : Prop} : h1 → h2 → goal := by sorry
-- Reminder, ⊢ is the symbol for the current goal

-- For All a and b that are propositions
-- Assumptions/hypotheses: ((b → a) ∧ b)
-- Goal: a
theorem problem_1_sol_annot : ∀ (a b : Prop), ((b → a) ∧ b) → a := by
-- Note that For All variables require intro due to Universal Instantiation
intro a b ⟨hba,hb⟩ -- Match onto the LHS and RHS of the conjunction, s.t. hba: b → a, hb: b
apply hba -- Goal transforms from a to b after we apply b → a; idea that if we prove b, then we get a
exact hb -- Our goal is proving b, and hb is exactly b

-- For All a, b, and c that are Propositions
-- Assumptions/hypotheses: ((b → c → a) ∧ b)
-- Goal: (c → a)
theorem problem_2_sol_annot : ∀ (a b c : Prop), ((b → c → a) ∧ b) → (c → a) := by
-- Again, a, b, and c are universally instantiated, so we need to intro them
intro a b c ⟨hbca,hb⟩ -- Match onto LHS and RHS of conjunction again, s.t. hbca: (b → c → a), hb: b
apply hbca -- We can do the same thing as p1, transform the goal (c → a) to b by applying hbca
exact hb -- Our goal becomes proving b, and hb is exactly b

-- For local a, b, c, d that are Real Numbers (Note that we don't need to intro local variables)
-- Assumptions/hypotheses: (a=b), (c=d)
-- Goal: (a + c) = (b + d)
theorem problem_3_sol_annot {a b c d : ℝ} : (a = b) → (c = d) → (a + c) = (b + d) := by
  intro h1 h2 -- Name the hypotheses
  calc -- Enter Calc Mode, allowing us to use two column proofs and write out each manipulation step
    a + c = b + c := by rw [h1] -- Start with LHS, using h1: a = b, replace the b with a
    _     = b + d := by rw [h2] -- Replace c with d using h2: c = d, which results in the RHS


-- For local a, b, c, d that are Real Numbers (Note that we don't need to intro local variables)
-- Assumptions/hypotheses: (a=b), (c=d)
-- Goal: (a + c) = (b + d)
theorem problem_3_sol_v2_annot {a b c d : ℝ} : (a = b) → (c = d) → (a + c) = (b + d) := by
  intro h1 h2 -- Name the hypotheses
  have h3 : a + c = b + c := by rw [h1] -- Create a lemma h3
  have h4 : b + d = b + c := by rw [h2] -- Create a lemma h4
  rw [h3] -- Goal was (a + c) = (b + d), now replace (a + c) with (b + c) due to h3 lemma!
  rw [h4] -- Goal was (b + c) = (b + d), now replace (b + d) with (b + c) due to h4 lemma!

-- Example Theorems (Note this is not exhaustive)
-- Note that Lean cares about order i.e. there is a difference between or_false vs false_or
-- For rw [false_or], it will search through your statement for a (→) to turn into the not-or equivalent
-- You can change what Lean searches for and replaces with using the <-
-- i.e. rw [<- imp_iff_not_or] means Lean will search through your statement for a not-or and turn it into the (→) equivalent

-- If you are unsure about a theorem, hover over it and read the annotation
-- The LHS of the ↔ is what Lean will default look for and the RHS is what Lean will replace it with

-- Examples
-- imp_iff_not_or {a b: Prop}: (a → b) ↔ (¬ a ∨ b)
-- not_and_or {a b: Prop}: ¬(a ∧ b) ↔ ¬a ∨ ¬b
-- not_or {a b : Prop}: ¬(a ∨ b) ↔ ¬a ∧ ¬b
-- or_and_left {a b c : Prop}: a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c)

-- For local a, b, c, and d that are Propositions (Note that we don't need to intro local variables)
-- Assumptions/hypotheses: None
-- Goal: ((a ∧ (a → (b ∧  c))) ∧ ((b ∧ c) → d))  = (a ∧ (b ∧ (c ∧ d)))
theorem problem_4_sol_annot {a b c d : Prop} :  ((a ∧ (a → (b ∧  c))) ∧ ((b ∧ c) → d))  = (a ∧ (b ∧ (c ∧ d))) := by
 calc
  ((a ∧ (a → (b ∧  c))) ∧ ((b ∧ c) → d)) = ((a ∧ (¬ a ∨ (b ∧ c))) ∧ ((b ∧ c) → d)) := by rw [imp_iff_not_or]
  _                                   = (((a ∧ ¬ a) ∨ (a ∧ (b ∧ c))) ∧ ((b ∧ c) → d)) := by rw [and_or_left]
  _                                   = ((False ∨ (a ∧ (b ∧ c))) ∧ ((b ∧ c) → d)) := by rw [and_not_self_iff]
  _                                   = ((a ∧ (b ∧ c)) ∧ ((b ∧ c) → d)) := by rw [false_or]
  _                                   = ((a ∧ (b ∧ c)) ∧ (¬ (b ∧ c) ∨ d)) := by rw [imp_iff_not_or]
  _                                   = (a ∧ ((b ∧ c) ∧ (¬ (b ∧ c) ∨ d))) := by rw [and_assoc]
  _                                   = (a ∧ (((b ∧ c) ∧ (¬ (b ∧ c))) ∨ ((b∧ c) ∧ d))) := by rw [and_or_left]
  _                                   = (a ∧ (False ∨ ((b∧ c) ∧ d))) := by rw [and_not_self_iff]
  _                                   = (a ∧ ((b ∧ c) ∧ d)) := by rw [false_or]
  _                                   = (a ∧ (b ∧ (c ∧ d))) := by rw [and_assoc]

-- For local a, b, and c that are Propositions (Note that we don't need to intro local variables)
-- Assumptions/hypotheses: None
-- Goal: (a → (b → c)) =  (¬ c → (a→ ¬ b))
theorem problem_5_sol_annot {a b c : Prop} :  (a → (b → c)) =  (¬ c → (a→ ¬ b)) := by
 calc
  (a → (b → c)) = (¬ a ∨ (b → c)) := by rw [imp_iff_not_or]
  _             = (¬ a ∨ (¬ b ∨ c)) := by rw [imp_iff_not_or]
  _             = ((¬ a ∨ ¬ b) ∨ c) := by rw [or_assoc]
  _             = (c ∨ (¬ a ∨ ¬ b)) := by rw [or_comm]
  _             = ((¬ ¬ c) ∨ (¬ a ∨ ¬ b)) := by rw [Classical.not_not]
  _             = (¬ c → (¬ a ∨ ¬ b)) := by rw [imp_iff_not_or]
  _             = (¬ c → ( a →  ¬ b)) := by rw [<- imp_iff_not_or]

-- For local a and b that are Real Numbers
-- Assumptions/hypotheses: a * b = 0
-- Goal: (a + b)^2 = (a - b)^2
theorem problem_6_sol_annot {a b : ℝ} : a * b = 0 → (a + b)^2 = (a - b)^2 := by
  intro h -- Name the hypotheses
  have h1 : (a + b)^2 = a*a + b*b := by -- Handle LHS of = by creating a lemma of what (a + b)^2 is equivalent to
    calc
      (a + b)^2 = (a + b) * (a + b) := by rw[pow_two]
      _         = (a + b) * a + (a + b) * b := by rw[mul_add] -- Distribute the (a + b) to the a and b in the RHS of the *
      _         = (a*a + b*a) + (a + b) * b := by rw[add_mul]
      _         = (a*a + b*a) + (a*b + b*b) := by rw[add_mul]
      _         = (a*a + a*b) + (a*b + b*b) := by nth_rw 2 [mul_comm]
      _         = (a*a + 0) + (0 + b*b) := by rw[h]
      _         = (a*a) + (0+ b*b) := by rw[add_zero]
      _         = (a*a) + (b*b) := by rw[zero_add]
  have h2 : (a - b)^2 = a*a + b*b := by -- Handle RHS of = by creating a lemma of what (a - b)^2 is equivalent to
    calc
      (a - b)^2 = (a - b) * (a - b) := by rw[pow_two]
      _         = (a - b) * a - (a - b) * b := by rw[mul_sub]
      _         = (a*a - b*a) - (a - b) * b := by rw[sub_mul]
      _         = (a*a - b*a) - (a*b - b*b) := by rw[sub_mul]
      _         = (a*a - a*b) - (a*b - b*b) := by nth_rw 2 [mul_comm]
      _         = a*a - a*b - a*b + b*b := by rw[<- sub_add]
      _         = a*a - 0 - 0 + b*b := by rw[h]
      _         = a*a - 0 + b*b := by rw[sub_zero]
      _         = a*a + b*b := by rw[sub_zero]
  rw [h1] -- Goal was (a + b)^2 = (a - b)^2, so rewrite (a + b)^2 with h1: (a*a) + (b*b)
  rw [h2] -- Goal was (a*a) + (b*b) = (a - b)^2, so rewrite (a - b)^2 with h2 a*a + b*b
