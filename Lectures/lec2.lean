import Mathlib
import Init

-- Last week we saw how to use Lean to prove some basic theorems
-- in propositional logic. We saw how to use some basic tactics

-- Let's summarize the tactics we have seen today.
-- intro: to introduce quantified variables and hypotheses in our proof state.
-- rw: to rewrite our goal using known theorems, or hypotheses.
-- apply: to apply a theorem to our goal, this can generate subgoals.
-- exact: to prove our goal using a theorem or hypothesis that matches the goal exactly.
-- calc: to prove an equality using a sequence of equalities.

-- Let's go back to TopHat


-- Let's now look at some other examples in the context of basic algebra.

-- In the next example we want to show that
-- (a + b)^2 = a^2 + b^2 when a*b=0.
-- This is a basic algebraic fact that can be proved using
-- a sequence of equalities. The statement we want to prove is the following.

theorem third_theorem_fill {a b: Real} : a*b=0 -> (a + b)^2 = a^2 + b^2 :=
  by
-- the first thing to notice is that we have an hypothesis
-- a*b=0, which we can use in our proof. To use this hypothesis
-- we need to introduce it in our proof state. This is done
-- using the tactic "intro" again. This tactic takes as argument
-- the name of the hypothesis we want to introduce, and it
-- introduces the hypothesis in our proof state.
-- In this case we can introduce the hypothesis as follows.
  intro h
-- Notice that now h ii in our list of hypotheses now, that is the list of
-- objects before the turnstile ⊢ in the Info View of our editor.
-- In general the tactic "intro" can be used to introduce all the
-- assumptions we need, as long as we give names for them.


--Let's try to work out the proof together.
  sorry


-- Now we can start the sequence of equalities using calc.
-- Also in this case we can use the tactic "rw" to rewrite
-- our goal using known theorems. In this case we will use
-- theorems about real numbers, which are available in Lean.
-- The theorems we will use are the following.
-- zero_mul : ∀ (a : α), 0 * a = 0
-- add_zero : ∀ (a : α), a + 0 = a
-- pow_two : ∀ (x : α), x ^ 2 = x * x
-- add_assoc : ∀ (a b c : α), a + b + c = a + (b + c)
-- add_mul : ∀ (a b c : α), (a + b)*c = a*c + b*c
-- mul_add : ∀ (a b c : α), a*(b + c) = a*b + a*c
-- mul_comm : ∀ (a b : α), a*b = b*a
-- mul_two : ∀ (a : α), a * 2 = a + a
-- These theorems can be checked using the command #check followed
-- by the name of the theorem.



theorem third_theorem {a b: Real} : a*b=0 -> (a + b)^2 = a^2 + b^2 :=
  by
  intro h
  calc (a + b)^2 = (a+b) * (a+b) := by rw[pow_two]
  _ = a*(a+b) + b*(a+b) := by rw[add_mul]
  _ = (a*a + a*b) + b*(a+b) := by rw[mul_add]
  _ = (a*a + a*b) + (b*a + b*b) := by rw[ mul_add]
  _ = (a*a + a*b) + (a*b + b*b) := by rw[mul_comm b a]
  _ = ((a*a + a*b) + a*b) + b*b := by rw[<- add_assoc]
  _ = (a*a + (a*b + a*b)) + b*b := by rw[<- add_assoc]
  _ = (a*a + a*b*2) + b*b := by rw[<- mul_two]
  _ = (a*a + 0*2) + b*b := by rw[h]
  _ = (a*a + 0) + b*b := by rw[zero_mul]
  _ = a*a + b*b := by rw[add_zero]
  _ = a^2 + b*b := by rw [pow_two]
  _ = a^2 + b^2 := by rw[<- pow_two]

-- Here another proof we worked out in class
/-calc (a + b)^2 = (a+b)*(a+b) := by rw [pow_two]
  _ =  (a*(a+b)) + (b*(a+b)) := by rw[add_mul]
  _ =  ((a*a) + (a*b)) + ((b*a) +(b*b)) := by rw[mul_add,mul_add]
  _ =  ((a*a) + 0 ) + ( (b*a) + (b*b)) := by rw[h]
  _ =  ((a*a) + 0 ) + ( (a*b) + (b*b)) := by nth_rw 2 [mul_comm]
  _ =  ((a*a) + 0 ) + ( 0 + (b*b)) := by rw [h]
  _ =  (a^2 + 0 ) + ( 0 + (b*b)) := by rw [pow_two]
  _ =  (a^2 + 0 ) + ( 0 + b^2) := by rw [<- pow_two]
  _ =  a^2 + ( 0 + b^2) := by rw [add_zero]
  _ =  a^2 + (b^2 + 0) := by nth_rw 2 [add_comm]
  _ =  a^2 + b^2 := by rw [add_zero]
 -/

-- Let's do some more TopHat

-- We want now to look at another example, which is a bit more
-- complex and whose proof is not directly described by a series of
-- rewriting. This is an example that is in the lecture notes.
-- We want to show that for a and b non negative real numbers,
-- if x ≤ y then x^2 ≤ y^2.

-- Here  is the proof in the lecture notes.:
-- Proof.
-- Multiplying both sides of x ≤ y by x (which preserves
-- the inequality because 0 ≤ x) gives us x^2 < x*y.
-- Similarly, multiplying both sides of x < y by y gives
-- us x*y < y^2. By transitivity, x^2 < y^2.

-- One way to formalize this in Lean is the following.
theorem le_impl_pow_two_le : forall (x y:ℝ), (0≤x) ∧ (0≤y) ∧ x ≤ y → x^2 ≤ y^2 :=
  by
-- The first step in this case is to introduce the quantified variables
-- x and y in our assumptions. This is done using the tactic "intro"
-- again. Specifically, we can introduce both variables at the same time
-- as follows.
  intro x y
-- Notice that now x and y are in our list of hypotheses, that is the list of
-- objects before the turnstile ⊢ in the Info View of our editor.
-- We can also introduce the hypothesis (0≤x) ∧ (0≤y) ∧ x ≤ y
-- in our proof state. This is done again using the tactic "intro".
-- We could introduce the hypothesis as follows.
-- intro h
-- but in this case it is more convenient to introduce the three
-- components of the hypothesis separately, so that we can use them
-- directly without need of further separate them. This can be done using
-- the tactic "intro" again, but in this case we can use
-- pattern matching ⟨h1,h2,h3⟩ to introduce the three components
-- of the hypothesis separately. This can be done as follows.
  intro ⟨h1,h2,h3⟩
-- Great, now our list of hypotheses includes everything we need to prove our goal.
-- The goal is to prove that x^2 ≤ y^2, and we want to use the transitivity of the
-- relation ≤ to prove this. Specifically, we want to show that x^2 ≤ x*y and
-- x*y ≤ y^2, and then use the transitivity of ≤ to conclude that x^2 ≤ y^2.
-- Our first step is to make explicit the multiplication in x^2 and y^2. This can be done
-- using the theorem pow_two, which states that x^2 = x*x. We can use the tactic "rw" to rewrite
-- our goal using this theorem. This can be done as follows.
  rw [pow_two, pow_two]
-- Now we can try to use the transitivity of ≤ to prove our goal.
  apply le_trans
-- Notice that now our goal is split into three subgoals. The first subgoal
-- is to prove that x^2 ≤ ?b, the second one is to prove that ?b ≤ y^2,
-- and the third one is to prove that ?b is a real number.
-- The ?b is an "existential metavariable", which is a variable that Lean introduces
-- to represent an unknown value that we need to find to complete the proof.
-- In this case, we need to find a value for ?b that makes the two inequalities
-- true. We know that a good candidate for ?b is x*y, so we can try to use this value.
-- To do that we can use a theorem stating that we can multiply both sides of
-- an inequality by a positive real number and preserve the inequality.
-- That is:
-- mul_le_mul_of_nonneg_left : ∀ {a b c : α}, a ≤ b → 0 ≤ c → c * a ≤ c * b
-- One way to use this theorem is to use the tactic "apply" again.
  apply mul_le_mul_of_nonneg_left
-- Notice that now we have four goals, since we also need to prove that we
-- can satisfy the two hypotheses of the theorem.
-- Notice also that we multiplied both sides of the inequality on the left.
-- This has changed our first goal, which is now to prove that x ≤ ?a.c,
-- where ?a.c is another existential metavariable that Lean introduced
-- to represent an unknown value that we need to find to complete the proof.
-- Notice that this also changed our last goal, which is now to prove that x*?a.c≤ y*y.
-- Let's now go back to our first subgoal, which is to prove that x ≤ ?a.c.
-- We know that a good candidate for ?a.c is y, so that the last goal becomes
-- x*?a.c≤ y*y
-- So we can try to use this value and show x≤y. This is exactly what our hypothesis h3 states.
-- We can use the tactic "exact" to prove this subgoal using our hypothesis h3.
  exact h3
-- The second subgoal is to prove that 0 ≤ x, which is exactly our hypothesis h1.
-- We can use the tactic "exact" to prove this subgoal using our hypothesis h1
  exact h1
-- We now need to prove the second inequality ?b ≤ y*y, where ?b is x*y.
-- We can use a similar theorem as the one we used before, but this time we need to
-- multiply both sides of the inequality on the right. This can be done as follows.
  apply mul_le_mul_of_nonneg_right
  exact h3
  exact h2

-- Let's do some TopHat


-- This theorem is a good playground to practice using Lean and its tactics.
-- There are several other ways to prove this theorem.
-- For example, we could replace the previous proof by the following one.

theorem le_impl_pow_two_le_v2 : forall (x y:ℝ), (0≤x) ∧ (0≤y) ∧ x ≤ y → x^2 ≤ y^2 :=
  by
  intro x y ⟨h1,h2,h3⟩
  rw [pow_two, pow_two]
  exact le_trans (mul_le_mul_of_nonneg_left h3 h1) (mul_le_mul_of_nonneg_right h3 h2)

-- This proof is very similar to the one we wrote before but shorter
-- because we use the fact that theorem can take as arguments
-- other statements that prove the hypotheses of the theorem.
-- However, like in programming, sometimes shorter is not better since
-- shorter proofs can be harder to read and understand.
--

-- Another way to prove this theorem is to use the more general theorem
-- mul_le_mul: ∀ {a b c d : α}, a ≤ b → c ≤ d → 0 ≤ a → 0 ≤ c → a * c ≤ b * d
-- instead of the theorem
-- mul_le_mul_of_nonneg_left: ∀ {a b c : α}, a ≤ b → 0 ≤ c → c * a ≤ c * b
-- we used before. For students with experience in programming, this is like using
-- a more general method/function instead of a more specific one.
-- Remembering that we use theorems to prove
-- x*x ≤ x*y and x*y ≤ y*y
-- we can use the theorem mul_le_mul to prove both inequalities.
-- However, to do this we need to introduce two additional hypotheses
-- a ≤ a and b ≤ b, which are true by reflexivity of the relation ≤.
-- This can be done using the theorem le_refl: ∀ (a : α), a ≤ a

theorem le_impl_pow_two_le_v3 : forall (x y : ℝ), (0≤x) ∧ (0≤y) ∧ x ≤ y → x^2 ≤ y^2 :=
  by
  intro x y ⟨h1,h2,h3⟩
  rw [pow_two, pow_two]
-- To introduce the two additional hypotheses we can use the tactic "have"
-- which is used to introduce a fact in our proof state.
-- You can think about this tactic as allowing us to define a local
-- lemma.
-- This tactic takes as argument the name of the fact,
-- followed by a colon :, followed by the statement of the fact
-- followed by :=, followed by a proof of the fact.
-- In this case we can introduce the two additional hypotheses
-- as follows.
  have h4: x≤x := by apply (le_refl x)
  have h5: y≤y := by apply (le_refl y)
-- now we can proceed with transitivity
  apply le_trans
-- and now we can use the theorem mul_le_mul to prove both inequalities,
-- using the two additional hypotheses we just introduced.
  exact mul_le_mul h4 h3 h1 h1
  exact mul_le_mul h3 h5 h2 h2


-- Great, we have proved several theorems in Lean today
-- and we have seen how to use some basic tactics to prove
-- theorems in basic algebra.
-- We have also seen how to use the Info View of our editor
-- to visualize the proof state at each step of the proof.

-- Today we have seen one new tactic:
-- "have" allows us to define local lemmas that we can use in our proof.
-- We have also revisited the use of the tactic "intro", to introduce
-- hypothesis, and to perform pattern matching. We will look more into this
-- in the next class.

-- An important aspect of Lean we have seen today is that we can give
-- arguments to theorems. These arguments are fact that the theorems
-- expect, that is they are facts that match the hypothesis of the
-- theorem.
