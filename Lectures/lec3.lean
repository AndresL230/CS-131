import Mathlib
import Init
open Classical

-- If you want to follow what we are doing on your laptop,
-- please make sure to include the packages I am using.

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

-- Let's do some TopHat

-- Above we have used pattern matching in intro to introduce multiple
-- hypotheses given as a conjunction. Let's see another example of
-- how conjunctions work in lean. Let's look at how we can prove
-- (one side of) the commutativity of conjunctions from first principles.

example {p q :Prop} : (p ∧ q) → (q ∧ p) := by
-- Notice that this is an implication and we can introduce
-- our hypothesis in the assumptions. As we did before we
-- could do this by intro ⟨hp,hq⟩ but let's see how we can
-- obtain the same result if we actually introduce only one
-- hypothesis
 intro h
-- we need now to extract the two components of the conjunction
-- and we can do this using the tactics "cases'" as follows.
 cases' h with hp hq
-- Now to prove the goal we need to prove the conjunction
-- q ∧ p. To prove a conjunction we can use the tactic "constructor"
-- which creates two subgoals, one for each component of the conjunction.
 constructor
 -- "constructor" uses the constructor of conjunction
-- And.intro, which takes as arguments the two components of the
-- conjunction. After using "constructor" our two subgoals are
-- q and p. To prove these subgoals we can use the hypotheses
-- we introduced earlier.
 exact hq
 exact hp

example {p q :Prop} : (p ∧ q) → (q ∧ p) := by
-- Another option is to use the tactic "cases" as follows.
intro h
cases h with
| intro hp hq =>
 -- This shows us how to write the constructor of the conjunction
 -- in lean. We can then finish the proof using this constructor
 -- to build the conjunction we want:
exact (And.intro hq hp)


-- Let's see now some example involving quantifiers.
-- Let's consider a definition of Even as follows:
-- Even (a) = ∃ r. a = r + r

-- We can easily prove that a number is even. Let's try this for 16

example : Even 16 := by
-- We want to prove that Even 16, that is that 16 is Even
-- To see exactly what we need to prove, we can spell out
-- the definition of Even. We can do this using the tactic
-- "unfold". This tactic takes the name of the definition we
-- want to unfold/spell out. If we apply it to our case we have.
  unfold Even
-- Now we can see that our goal is to show that
-- ⊢ ∃ r, 16 = r + r. This is an existentially quantified
-- statement. To prove it we need to show some evidence of the
-- existence of such r. We can do this using the tactic
-- "exists". This tactic takes as argument a term that we
-- want to use as evidence of the existence of r. In our case
-- we can just write:
  exists 8
-- and this concludes our proof, since Lean try to solve
-- the remaining goal automatically.


-- Let's see another example. Let's consider the following
example : ∀ y:Real, ∃ x:Real, 2 * x + 3 = y := by
-- This is a universally quantified statement. So we can
-- start by introducing the quantified variable
  intro y
-- We now need to prove the existentially quantified
-- statement ∃ x:Real, 2 * x + 3 = y. The evidence we can
-- provide is now ((y-3)/2).
  exists ((y-3)/2)
-- We now need to prove that 2 * ((y-3)/2) + 3 = y
-- To prove this we need to show that we can cancel
-- the multiplication by 2 with the division by 2.
-- We can do this by using the theorem
-- mul_div_cancel₀: ∀ {α : Type u} [field α] {a b : α}, b ≠ 0 → a * (b / a) =
  rw [mul_div_cancel₀]
  -- Notice that this creates a new goal, which is to show that
  -- 2 ≠ 0. First, lets finish our main goal. We can use here
  -- the theorem
  -- sub_add_cancel: ∀ {α : Type u} [add_group α] (a b : α), (a - b) + b = a
  rw [sub_add_cancel]
  -- Now we need to prove that 2 ≠ 0. We can do this using
  -- the theorem two_ne_zero: 2 ≠ 0
  exact two_ne_zero


-- Great, we have proved several theorems in Lean today
-- and we have seen how to use some basic tactics to prove
-- theorems in basic algebra.
-- We have also seen how to use the Info View of our editor
-- to visualize the proof state at each step of the proof.

-- Today we have seen some new tactics:
-- - "have" allows us to define local lemmas that we can use in our proof.
-- - "cases" and "cases'" allow us to perform pattern matching on
--   hypotheses that are conjunctions or existentially quantified statements.
-- - "constructor" allows us to prove conjunctions by creating subgoals
--   for each component of the conjunction.
-- - "unfold" allows us to spell out the definition of a term.
-- - "exists" allows us to provide evidence for existentially quantified statements.
-- We have also revisited the use of the tactic "intro", to introduce
-- hypothesis, and to perform pattern matching.

-- We have also seen an important aspect of Lean: we can give
-- arguments to theorems. These arguments are facts that the theorems
-- expect, that is they are facts that match the hypothesis of the
-- theorem.
