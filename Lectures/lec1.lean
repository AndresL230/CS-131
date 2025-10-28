import Mathlib

-- Our first example is a simple theorem in propositional logic

theorem first_try : (¬ (a ∧ b ∧ c) ) = (a → (b → ¬ c)):= sorry


-- the keyword theorem says that we are stating a theorem, and I am
-- calling it "first_try"
-- what the theorem is stating is what is given after the : symbol,
-- in this case it states that "(¬ (a ∧ b ∧ c) ) = (a → (b → ¬ c))"
-- After the symbol ":=" is where the proof of the theorem is.
-- For the moment we are not interested in proving it, and we
-- use the placeholder "sorry" to tell this to Lean.
-- There is a part of the theorem that I didn't write and that my
-- editors add for me, this is the part "{a b c}", I will come back
-- to this later.


-- If we are not interested in giving a name to our statement,
-- we can just use the keyword "example". This doesn't need to be
-- followed by a name, and the rest of the notation is the same
example : (¬ (a ∧ b ∧ c) ) = (a → (b → ¬ c)) := sorry



-- Let's now prove the theorem. How can we prove it?
-- One way is to use two times de Morgan's law for the negation of
-- a conjunction, and two times the definition of implication,
-- which we called conditional identity. The de Morgan's law
-- we are interested into states that -- ¬ (p ∧ q) = ¬ p ∨ ¬ q,
-- and the definition of implication, which we called conditional identity,
-- states that p → q = ¬ p ∨ q.

-- In lean these two theorems are called "not_and_or" and "imp_iff_not_or"
-- respectively.
-- Here are their statements:
--
-- theorem imp_iff_not_or {a b : Prop} :
-- (a → b) ↔ (¬ a ∨ b)
--
-- theorem not_and_or {a b : Prop} :
-- ¬(a ∧ b) ↔ ¬a ∨ ¬b
--
-- Note that these theorems are stated using "↔" instead of "=",
-- but we can use them as if they were stated using "=" for the moment.
--
-- So we can use these two theorems to prove our statement.


-- How can we translate this in Lean?
-- One way is to use a sequence of equalities, this is done
-- using the "calc" keyword. The idea is to start from one
-- side of the equality and then use a sequence of equalities
-- to reach the other side of the equality. Each step of the
-- equality is justified by a reason, which is given after the
-- ":=" symbol. The reason can be a reference to a theorem,
-- or a sequence of tactics, which are given after the "by"
-- keyword. This gives us the following structure, which we
-- can fill in.

theorem first_theorem_fill : (¬ (a ∧ b ∧ c) ) = (a → (b → ¬ c)) :=
-- the first step we will use in general in a proof is to write
-- the keyword "by" to indicate that we are starting the proof.
  by
  calc
  (¬ (a ∧ (b ∧ c))) = (¬ a ∨ ¬ (b ∧ c)) := by sorry
  (¬ a ∨ ¬ (b ∧ c)) = (¬ a ∨ (¬ b ∨ ¬ c)) := by sorry
  (¬ a ∨ (¬ b ∨ ¬ c)) = (a → (¬ b ∨ ¬ c)) := by sorry
  (a → (¬ b ∨ ¬ c)) = (a → (b → ¬ c)) := by sorry

-- Here we used the tactic rw, which is used to rewrite our
-- goal using a theorem. Specifically, the tactic rw takes as
-- argument in [ ] the name of a theorem, and it rewrites
-- the goal using the theorem. This tactical can be used when
-- the theorem we want to use is an equality or an iff.
-- The tactic rw can be used to rewrite in both directions.
-- If we  have a theorem stating that A = B, then
-- the tactic rw [theorem_name] can be used to rewrite A into B,
-- while the tactic rw [<- theorem_name] can be used to rewrite
-- B into A. Similarly, we can do the same if we have a theorem stating that
-- A ↔ B.

-- Summarizing, we have the following proof.

theorem first_theorem : (¬ (a ∧ b ∧ c) ) = (a → (b → ¬ c)) :=
  by
  calc
  (¬ (a ∧ (b ∧ c))) = (¬ a ∨ ¬ (b ∧ c)) := by rw [not_and_or]
  (¬ a ∨ ¬ (b ∧ c))  = (¬ a ∨ (¬ b ∨ ¬ c)) := by rw[not_and_or]
  (¬ a ∨ (¬ b ∨ ¬ c)) = (a → (¬ b ∨ ¬ c)) := by rw[<- imp_iff_not_or]
  (a → (¬ b ∨ ¬ c)) = (a → (b → ¬ c)) := by rw[<- imp_iff_not_or]

-- There is a shorter way to write this proof, without showing all the steps
-- explicitly. We can remove the calc keyword and just use the
-- tactic "by rw [...]" with a list of theorems to be used
-- to rewrite the goal. This gives us the following proof.
theorem first_theorem_v2 : (¬ (a ∧ b ∧ c)) =  (a → (b → ¬ c)) :=
  by
  rw [not_and_or, not_and_or, <- imp_iff_not_or,<- imp_iff_not_or]

-- Again, notice that we didn't use "calc" here, but just the tactic "by rw [...]".

-- We can check the statement of a theorem using the command #check followed
-- by the name of the theorem. This is useful when we want to check the details of
-- a theorem we want to use.

-- In general, command starting with # are commands for Lean
-- and not part of the language of Lean, so they cannot be used
-- in the statement of a theorem or in a proof.

-- Going back to #check, we can check the statement of the theorem first_theorem_v2 as follows.
#check first_theorem_v2


-- We can now see the meaning of the part "{a b c : Prop}" that
-- was missing in the statement of the theorem first_theorem and that lean completed for us.
-- This part includes the "implicit arguments" of the theorem. Notice that lean also
-- added the keyword "Prop" to indicate that a, b and c are propositions.

-- although implicit arguments can often be inferred by Lean, it is often useful
-- to include them explicitly, especially when we want to refer to the theorem
-- in a different context, and when we are learning. We can include them explicitly as follows.

theorem first_theorem_v3 {a b c:Prop}: (¬ (a ∧ b ∧ c)) =  (a → (b → ¬ c)) :=
  by
  rw [not_and_or, not_and_or, <- imp_iff_not_or,<- imp_iff_not_or]

-- In fact, we could have been even more explicit and write the theorem
-- with the implicit arguments quantified as follows.

theorem first_theorem_v4 : ∀ (a b c: Prop), (¬ (a ∧ b ∧ c)) =  (a → (b → ¬ c)) :=
-- If we choose this option then we need to use the tactic "intro" to introduce
-- the quantified variables in the proof state. This tactic takes as argument
-- the names of the variables we want to introduce, and it introduces them
-- in our proof state. This gives us the following proof.
  by
  intro a b c
  rw [not_and_or, not_and_or, <- imp_iff_not_or,<- imp_iff_not_or]

-- Let's see another even shorter way to write this proof is to use the tactic
-- "by grind", which tries to prove the goal automatically using a collection of
-- known theorems and tactics. This gives us the following proof.
theorem first_theorem_v5 {a b c : Prop}: (¬ (a ∧ b ∧ c)) =  (a → (b → ¬ c)) :=
  by
  grind

-- grind is a powerful tactic that can solve many goals in propositional
-- logic, but it can also be slow and not always successful.
-- Here another example of using grind that will be useful later.
theorem em_iff_true (a : Prop) : (¬ a ∨ a) ↔ True :=
  by
  grind

-- We will avoid using grind as much as possible for the moment, but it is good to know.

-- Great, we have proved our first theorem in lean.

-- Let's see another example. For this example we will use a sequence of equalities
-- using "calc" again. This will give us more practice with the tactic "rw".
-- The statement we want to prove is the following.
theorem second_theorem_fill {a b : Prop} : (¬ (a ∨ b) ∨ (¬ a ∧ b) ) = ¬ a :=
  by
-- and we can use the following theorems/principles
-- em_iff_true : (¬ a ∨ a) ↔ True
-- and_true : p ∧ True ↔ p
-- and_or_left : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c)
-- not_or : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b
--
-- A key aspect of using Lean is understanding the "proof state"
-- at each step of the proof. The proof state consists of
-- the current goal we want to prove, and the list of
-- hypotheses we have available to prove the goal.
-- In this case, the goal is the equality we want to prove,
-- and we don't have any hypotheses.
-- The proof state changes at each step of the proof, and
-- it is important to understand how it changes to be able
-- to prove the goal. To visualize the proof state at each step,
-- we can use the Info View of our editor, which shows
-- the current goal and the list of hypotheses depending on where
-- our cursor is.

-- Let's go back to our theorem, and start the proof by writing the structure of the proof
-- using calc, we can then check the proof state.
  calc
  (¬ (a ∨ b) ∨ (¬ a ∧ b) ) = ((¬ a ∧ ¬ b) ∨ (¬ a ∧ b) ) := by sorry
  _                        = (¬ a ∧ (¬ b ∨ b)) := by sorry
  _                        = (¬ a ∧ True) := by sorry
  _                        = ¬ a := by sorry

--
-- Here we avoid repeating the left hand side of each equality, and
-- we use the underscore _ to indicate that we want to use
-- the right hand side of the previous equality.


---
-- Going back to Filling in the reasons for each step, we get the following proof.
---
theorem second_theorem {a b : Prop} : (¬ (a ∨ b) ∨ (¬ a ∧ b) ) = ¬ a :=
  by
  calc
  (¬ (a ∨ b) ∨ (¬ a ∧ b) ) = ((¬ a ∧ ¬ b) ∨ (¬ a ∧ b) ) := by  rw[not_or]
  _                        = (¬ a ∧ (¬ b ∨ b)) := by rw[and_or_left]
  _                        = (¬ a ∧ True) := by rw[em_iff_true]
  _                        = ¬ a := by rw[and_true]

-- A reminder that sometimes it is useful to check what one of the theorems we want to use states.
-- we can do this using the command #check followed by the name of the theorem.
#check and_true


-- Notice that in this case, the theorem and_true is stated using "=",
-- and this is exactly what we need to use to conclude our proof.
-- Another way to conclude the proof is to use the tactic "apply",
-- which is used to apply a theorem to the current goal.
theorem second_theorem_v2 {a b : Prop} : (¬ (a ∨ b) ∨ (¬ a ∧ b) ) = ¬ a :=
  by
  calc
  (¬ (a ∨ b) ∨ (¬ a ∧ b) ) = ((¬ a ∧ ¬ b) ∨ (¬ a ∧ b) ) := by  rw [not_or]
  _                        = (¬ a ∧ (¬ b ∨ b)) := by rw[and_or_left]
  _                        = (¬ a ∧ True) := by rw[em_iff_true]
  _                        = ¬ a := by apply and_true

-- There is actually another way to conclude the proof, which is to use
-- the tactic "exact", which is used to prove the goal using a theorem
-- or a hypothesis that matches the goal exactly. However, if we try to apply it
-- directly with the theorem and_true, it will fail because of the
-- quantification. We can instantiate it with what we need.
-- This gives us the following proof.
theorem second_theorem_v3 {a b : Prop} : (¬ (a ∨ b) ∨ (¬ a ∧ b))  = ¬ a :=
  by
  calc
  (¬ (a ∨ b) ∨ (¬ a ∧ b) ) = ((¬ a ∧ ¬ b) ∨ (¬ a ∧ b) ) := by  rw [not_or]
  _                        = (¬ a ∧ (¬ b ∨ b)) := by rw[and_or_left]
  _                        = (¬ a ∧ True) := by rw[em_iff_true]
  _                        = ¬ a := by exact (and_true (¬ a))

-- Great, we have proved our second theorem in Lean.

-- Let's do some TopHat now.
