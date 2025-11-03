import Mathlib

example {U}  {A: Set U}: A ⊆ A := by
rw[Set.subset_def] -- "we  need to prove that every element in A is also an element of A, by definition of subset"
intro c -- "consider an element c"
intro h_c_is_in_A -- "assume c is an element of A"
exact h_c_is_in_A -- "then c is in A, which is what we needed to prove"

example {U}  {A B C: Set U}: (A ⊆ B ∧ B ⊆ C) → A ⊆ C := by
rw[Set.subset_def] -- "by definition of subset, A is a subset of B iff every element of A is also an element of B"
rw[Set.subset_def] -- "by definition of subset, B is a subset of C iff every element of B is also an element of C"
intro ⟨h_a_subset_b, h_b_subset_c⟩  -- "So suppose every element of A is also an element of B AND every element of B is also an element of C"
rw[Set.subset_def] -- "We need to prove that every element in A is also in C"
intro q -- "Consider an element q of U"
intro q_in_A -- "Suppose q is in A"
apply h_b_subset_c -- "Because every element in C is also in B, it suffices to prove that q is in B"
apply h_a_subset_b -- "Because every element in B is also in A, it suffices to prove that q is in A"
exact q_in_A


example {U} {A B: Set U}: (A ∪ B)ᶜ = (Aᶜ ∩ Bᶜ) := by
rw [Set.ext_iff]
intro r
calc
r ∈ (A∪B)ᶜ  ↔ ¬ (r ∈ (A∪B)) := by rw[Set.mem_compl_iff] 
_           ↔ ¬ (r∈ A ∨ r∈ B) := by rw[Set.mem_union]
_           ↔ (¬ r∈ A ∧ ¬ r∈ B) := by rw[not_or]
_           ↔ (r∈Aᶜ  ∧ r ∈ Bᶜ) := by rw[Set.mem_compl_iff,Set.mem_compl_iff]
_           ↔ (r∈Aᶜ ∩ Bᶜ) := by rw[Set.mem_inter_iff]
