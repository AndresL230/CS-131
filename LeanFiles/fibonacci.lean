import Mathlib

-- Before we look into formalizing bounds on the Fibonacci numbers,
-- let's recall how we can work with conjunctions in Lean.
example {A B : Prop} : A ∧ B -> B ∧ A := by
  intro h
  cases h with
  | intro ha hb =>
  constructor
  exact hb
  exact ha

-- here another version we saw in class
example {A B : Prop} : A ∧ B -> B ∧ A := by
  intro ⟨ha,hb⟩
  constructor
  exact hb
  exact ha

-- here yet another version using `left` and `right`
-- which will be useful later
example {A B : Prop} : A ∧ B -> B ∧ A := by
  intro h
  constructor
  exact h.right
  exact h.left

-- let's also recall how rfl works. We can use rfl to prove
-- equalities that are true by definition. An example is the following:

example (a : Nat):   a + 5 - 1 = a + 4 := by
 rfl

-- unfortunately, telling when an equality is true by definition
-- is not easy, and as a consequence we may encounter situations
-- where rfl seems like the right tactic but it doesn't work
-- directly.

-- you can see this by uncommenting the following line
-- just adding a 0+ on the left makes rfl fail
-- example (a : Nat): 0 + a + 5 - 1 = a + 4 := by
-- rfl

-- In these situations, we can often help Lean by rewriting
-- using some known equalities. For example, in the previous case
-- we can use the fact that 0 + a = a to help Lean see that
-- the equality is true by definition:
example (a : Nat): 0 + a + 5 - 1 = a + 4 := by
 rw [Nat.zero_add]
 rfl


-- Now let's move on to prove the bound properties of
-- the Fibonacci sequence, as we did in class.

-- First, let's define the Fibonacci numbers.

def fib: Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib (n+1) + fib n

-- As a first result we want to prove an upper bound on every
-- Fibonacci number: fib(n) ≤ 2^n

-- we do this by induction on n using the fact that
-- the fibonacci numbers are increasing: fib(n) ≤ fib(n+1).
-- Let's first prove this fact.

theorem fib_increasing (n : Nat) : fib (n) ≤ fib (n+1):= by
  -- Interestingly we don't need to use induction at all
  -- here and we can prove just by cases, considering the
  -- case n=0, n=1, or n≥2.
  cases n with
  | zero =>
  -- the first case is P(0), i.e.,
  -- fib(0) ≤ fib(1)
    -- this follows directly from the definition of fib
  -- which we can unfold using the `unfold` tactic
    unfold fib
  -- after unfolding, the goal becomes 0 ≤ 1
  -- which is true by definition of ≤ on natural numbers
  -- there are a few theorems that we can use to prove this,
  -- one of them is Nat.le_succ which states that
  -- for every natural number k, k ≤ k+1
    apply Nat.le_succ
  | succ m =>
  -- we are now in the case n≥1, which means that n = m + 1
  -- for some m (which is the name I chose). In this case,
  -- we can again use cases to
  -- consider the case n=1 and the case n≥2 separately
    cases m with
    | zero =>
  -- here we are in the case m=0, which means n=1,
  -- we need to show that fib(1) ≤ fib(2)
  -- we can again unfold the definition of fib
      unfold fib
  -- and actually we need to unfold it again to just
  -- get rid of it and work with numbers
      unfold fib
  -- and we see that we need to show that 1 ≤ 1
  -- which is true by reflexivity of ≤, which is
  -- expressed by the theorem Nat.le_refl
      apply Nat.le_refl
    | succ l =>
  -- here we are in the case n ≥ 2, or equivalently,
  -- n1≥1 since n = l + 1, or equivalently l≥0 since
  -- m = l + 1 for some l (which is the name I chose).
  -- In this case, we need to show
  -- that P(l+2) holds, i.e., fib(l+2) ≤ fib(l+3)
  -- we start by unfolding the definition of fib
      unfold fib
  -- and we see that our goal is now
  -- fib(l+1) + fib(l) ≤ fib(l+2) + fib(l+1)
  -- now we can use the definition of fib to prove the
  -- following lemma
      have h1: fib (l + 1+1) = fib (l+1) + fib (l) := by
  -- this follows directly from the definition of fib
  -- which can be used by the tactic rfl
        rfl
  -- we can use this equality to rewrite our goal
      rw [h1]
  -- Now we can apply the lemma Nat.le_add_right to conclude.
  -- This lemma states that for every natural numbers a,b,
  -- a ≤ a + b
  -- which is exactly what we need here since our left hand
  -- hand side is fib(l+1) + fib(l) and our right hand side
  -- is fib(l+1) + fib(l) + fib(l+1)
      apply Nat.le_add_right


-- Now we can use fib_increasing to prove the upper bound
-- on Fibonacci numbers.
theorem fib_upper_bound (n: Nat): fib n ≤ 2^n := by
-- We proceed by induction on n
  induction n with
  | zero =>
-- the base case is n=0, i.e., we need to show that
-- fib(0) ≤ 2^0. We can unfold the definition of fib
-- and see that we need to show that 0 ≤ 1, which
-- follows from Nat.le_succ as we saw before.
    unfold fib
    apply Nat.le_succ
  | succ k ih =>
  -- in the inductive case we need to show that
  -- fib(k+1) ≤ 2^(k+1), assuming the inductive
  -- hypothesis ih: fib(k) ≤ 2^k.
  -- Like we did in class, we start by doing some
  -- case analysis on k to treat the cases n=1
  -- and n≥2 separately.
    cases k with
    | zero =>
  -- here we are in the case k=0, i.e., n=1,
  -- we need to show that fib(1) ≤ 2^1
  -- we can unfold the definition of fib
      unfold fib
  -- and use the fact that 2^1 = 2 to rewrite the goal
      rw [Nat.pow_one]
  -- we can now conclude using Nat.le_succ as before
      apply Nat.le_succ
    | succ h =>
  -- here we are in the case k≥1, i.e., n≥2
  -- or equivalently h≥0 since k = h + 1 for some h
  -- (which is the name I chose). In this case,
  -- we need to show that fib(h+2) ≤ 2^(h+2)
  -- let's start by unfolding the definition of fib
    unfold fib
  -- and we see that our goal is now
  -- fib(h+1) + fib(h) ≤ 2^(h+2)
  -- we want to proceed using a sequence of inequalities.
  -- So, we apply transitivity of ≤ using the `apply Nat.le_trans` tactic
    apply Nat.le_trans
  -- this creates a new goal, which is the "middle"
  -- term in the sequence of inequalities. We want
  -- to choose this to be 2^(h+1) + 2^(h), so we
  -- need to show that fib(h+1) + fib(h) ≤ 2^(h+1) + fib(h+1)
  -- we do this in a few steps. First, we use the fact that
  -- if a1 ≤ b1 and a2 ≤ b2 then a1 + a2 ≤ b1 + b2
  -- which corresponds to using the `apply Nat.add_le_add` tactic
    apply Nat.add_le_add
  -- this creates two new goals, to prove that
  -- fib(h+1) ≤ 2^(h+1) and fib(h) ≤ fib(h+1)
  -- Notice that Lean doesn't know yet what we want to
  -- use on the right hand side of the inequalities,
  -- but we can help it.
  -- For the first goal, we can use the inductive hypothesis ih
  -- since it states exactly that fib(h+1) ≤ 2^(h+1)
    exact ih
  -- for the second goal, we can again use the inductive
  -- hypothesis ih, but we need to rewrite its left hand
  -- side to match what we need, i.e., fib(h+1).
  -- We can do this using the lemma fib_increasing
  -- which states that fib(h) ≤ fib(h+1)
    apply fib_increasing
  -- we have now have to do another sequence of inequalities
  -- to show that 2^(h+1) + fib(h+1) ≤ 2^(h+2)
  -- we again use transitivity of ≤
    apply Nat.le_trans
  -- this creates a new goal, which we want to prove
  -- 2^(h+1) + fib(h+1) ≤ 2^(h+1) + 2^(h+1)
  -- we can prove this using again Nat.add_le_add
  -- which states that if a ≤ b and c ≤ d then
  -- a + c ≤ b + d.
    apply Nat.add_le_add
  -- this creates two new goals, to show that
  -- 2^(h+1) ≤ 2^(h+1) and fib(h+1) ≤ 2^(h+1)
  -- the first one is true by reflexivity of ≤
  -- expressed by Nat.le_refl
    apply Nat.le_refl
  -- the second one follows from the inductive hypothesis ih
    exact ih
  -- finally, we need to show that 2^(h+1) + 2^(h+1) = 2^(h+2)
  -- we can do this by rewriting using the definition of exponentiation
    nth_rw 3 [Nat.pow_succ]
    rw [Nat.mul_two]

-- Here we prove an auxiliary lemma that states that
-- (1.5)^(k+3) ≤ (1.5)^(k+2) + (1.5)^(k+1)
-- we will use this lemma in the proof of the lower bound
-- on Fibonacci numbers, as we did in class
theorem auxiliary_lemma:
(1.5:ℝ)^(k+3) ≤ (1.5)^(k+2) + (1.5)^(k+1) := by
  nth_rw 1 [pow_succ, pow_succ]
  rw [mul_assoc]
  have h2: (1.5:ℝ) * 1.5 ≤ 1.5 + 1 := by
    linarith
  apply le_trans
  apply mul_le_mul_of_nonneg_left h2
  apply pow_nonneg
  linarith
  apply le_trans
  rw [mul_add]
  rw [mul_one]
  rw [<- pow_succ]

-- Now we can prove the lower bound on Fibonacci numbers:
-- fib(n+2) ≥ (1.5)^n
-- this is slightly different from what we did in class,
-- but the idea is the same: we generalize the statement
-- to get a stronger inductive hypothesis, which
-- allows us to complete the inductive step.
theorem fib_lower_bound (n: Nat): (1.5:ℝ)^n ≤ fib (n+2):= by
--here we generalize the statement we want to prove
-- to get a stronger inductive hypothesis.
-- we want to prove that both (1.5)^n ≤ fib(n+2)
-- and (1.5)^(n+1) ≤ fib(n+3)
-- we can express this using a conjunction
-- and then prove this conjunction by induction on n
-- we start by stating this as an auxiliary goal (aux)
  have aux : (1.5:ℝ)^n ≤ fib (n+2) ∧ (1.5:ℝ)^(n+1) ≤ fib (n+3) := by
-- we can now proceed by induction on n
    induction n with
    | zero =>
-- in the base case n=0, we need to show both
-- that (1.5)^0 ≤ fib(2) and (1.5)^1 ≤ fib(3)
-- we can do this by unfolding the definition of fib
-- and since we are using real numbers we will
-- for convenience using some automation   using
-- the tactic simp and linarith.
-- We will not look at how these tactics work
-- in this course, but they are very useful to
-- solve simple arithmetic goals like these.
      simp [fib]; linarith
    | succ k ih =>
-- in the inductive case, we need to show both
-- that (1.5)^(k+1) ≤ fib(k+3) and
-- that (1.5)^(k+2) ≤ fib(k+4)
-- Notice that our inductive hypothesis ih states that
-- both (1.5)^k ≤ fib(k+2) and (1.5)^(k+1) ≤ fib(k+3)
-- we can use these two inequalities to prove the two
-- inequalities we need.
-- We start by proving the two inequalities separately
-- and then combining them using And.intro
-- first, we prove (1.5)^(k+1) ≤ fib(k+3), we call this left_goal
      have left_goal: (1.5:ℝ)^(k+1) ≤ fib (k+3) := by
-- this is the first part of the conjunction we need to prove
-- and this follows from the inductive hypothesis
-- in particular we can use the right part of the inductive hypothesis ih
        exact ih.right
-- now we prove the second part of the conjunction
-- (1.5)^(k+2) ≤ fib(k+4), we call this right_goal
      have right_goal: (1.5:ℝ)^(k+2) ≤ fib (k+4) := by
-- for this we start by doing case analysis on k
        cases k with
        | zero =>
-- here we are in the case k=0, which  we need to show that
-- (1.5)^2 ≤ fib(4)
-- to solve this we use some automation again
-- we use simp [fib] to unfold the definition of fib and
-- simplify the resulting expression, and then linarith
-- to solve the resulting arithmetic goal
          simp [fib]; linarith
        | succ h =>
-- here we are in the case k≥1, or equivalently h≥0
-- since k = h + 1 for some h (which is the name I chose).
-- In this case, we need to show that
-- (1.5)^(h+3) ≤ fib(h+5)
-- we start by unfolding the definition of fib
          unfold fib
-- and we see that our goal is now
-- (1.5)^(h+3) ≤ fib(h+4) + fib(h+3)
-- we want to proceed using a sequence of inequalities.
-- So, we apply transitivity of ≤ using the `apply le_trans` tactic
          apply le_trans
-- this creates a new goal, which is the "middle"
-- term in the sequence of inequalities. We want
-- to choose this to be (1.5)^(h+2) + (1.5)^(h+1), so we
-- need to show that (1.5)^(h+3) ≤ (1.5)^(h+2) + (1.5)^(h+1)
-- we can prove this using the auxiliary_lemma we proved before
          exact auxiliary_lemma
-- now we need to show that
-- (1.5)^(h+2) + (1.5)^(h+1) ≤ fib(h+4) + fib(h+3)
--first we simplify our goal using the simp tactic
-- this step is needed for tecnical reasons due to the
-- fact that we are working with real numbers and
-- natural numbers at the same time
          simp
-- we can again use add_le_add
-- which states that if a1 ≤ b1 and a2 ≤ b2 then a1 + a2 ≤ b1 + b2
          apply add_le_add
-- this creates two new goals, to prove that
-- (1.5)^(h+2) ≤ fib(h+4) and (1.5)^(h+1) ≤ fib(h+3)
-- We have both of these inequalities in our inductive hypothesis ih
-- we can use the left part of ih to prove the first goal
          exact ih.right
-- and the right part of ih to prove the second goal
          exact ih.left
-- now we have both left_goal and right_goal
-- and we can combine them to conclude the proof of our
-- fact aux
      apply And.intro left_goal right_goal
-- now we have proved aux, which states that
-- both (1.5)^n ≤ fib(n+2) and (1.5)^(n+1) ≤ fib(n+3)
-- we can use aux to conclude the proof of our original goal
-- which is to show that (1.5)^n ≤ fib(n+2)
  apply aux.left
