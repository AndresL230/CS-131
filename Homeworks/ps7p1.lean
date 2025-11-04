import Mathlib

-- The Lean example from class on Oct 21 may be helpful

-- You can use the theorems listed below in this part of the homework.
-- imp_iff_not_or {a b: Prop}: (a → b) ↔ (¬ a ∨ b)
-- not_and_or {a b: Prop}: ¬(a ∧ b) ↔ ¬a ∨ ¬b
-- not_or {a b : Prop}: ¬(a ∨ b) ↔ ¬a ∧ ¬b
-- or_and_left {a b c : Prop}: a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c)
-- and_or_left {a b c : Prop}: a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c)
-- or_assoc {a b c : Prop}: a ∨ (b ∨ c) ↔ (a ∨ b) ∨ c
-- or_comm {a b : Prop}: a ∨ b ↔ b ∨ a
-- and_assoc {a b c : Prop}: a ∧ (b ∧ c) ↔ (a ∧ b) ∧ c
-- and_comm {a b : Prop}: a ∧ b ↔ b ∧ a
-- and_not_self_iff {a b : Prop}: a ∧ ¬a ↔ False
-- or_false {a b : Prop}: a ∨ False ↔ a
-- Set.ext_iff.{u} {α : Type u} {a b : Set α} : a = b ↔ ∀ (x : α), x ∈ a ↔ x ∈ b
-- Set.mem_diff {α : Type u} {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ ¬x ∈ t
-- Set.mem_inter_iff {α : Type u} {s t : Set α} (x : α) : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t

theorem problem_1 {U}  {A B : Set U}: (A \ (B ∩ A)) = (A \ B) :=  by
  rw[Set.ext_iff]
  intro x
  calc
    x ∈ (A \ (B ∩ A)) ↔ x ∈ A ∧ ¬(x ∈ (B ∩ A)) := by rw[Set.mem_diff]
    _     ↔ x ∈ A ∧ ¬(x ∈ B ∧ x ∈ A) := by rw[Set.mem_inter_iff]
    _     ↔ x ∈ A ∧ (¬x ∈ B ∨ ¬x ∈ A) := by rw[not_and_or]
    _     ↔ (x ∈ A ∧ ¬x ∈ B) ∨ (x ∈ A ∧ ¬x ∈ A) := by rw[and_or_left]
    _     ↔ (x ∈ A ∧ ¬x ∈ B) ∨ False := by rw[and_not_self_iff]
    _     ↔ (x ∈ A ∧ ¬x ∈ B) := by rw[or_false]
    _     ↔ x ∈ (A \ B) := by rw[Set.mem_diff]
