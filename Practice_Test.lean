import Mathlib.Tactic
variable (P Q R S T : Prop)
variable (X : Type)
(A B C : Set X)

-- Question 1 --
example: (P → R) → (S → Q) → (R → T) → (Q → R) → (S → T) := by
-- Introducing Hypotheses --
intro h1 h2 h3 h4 h5
-- Using h2 to prove h5 is Q --
apply h2 at h5
-- Using h4 to prove h5 is R --
apply h4 at h5
-- Using h3 to prove h5 is T --
apply h3 at h5
-- Final Answer is equal to h5 so proof is done --
exact h5
done

-- Question 2 --
example: ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by -- Not p or q if and only if not p and not q --
-- Split LHS → RHS and RHS → LHS
  constructor
  -- Case One Assume LHS True
  -- Introduce Hypothesis --
  · intro h
    -- Split
    constructor
    -- ¬ P equivalent to P → False
    -- Case 1.1 Assume P prove False
    · intro hP
      -- argue back from (P ∨ Q) → False
      apply h
      -- If proving P ∨ Q it suffices to P
      left
      -- Assumption
      exact hP
    -- Case 1.2 Equivalent to Case 1.1 for Q
    · intro hQ
      apply h
      right
      exact hQ
  -- Case 2 Assume RHS True
  · intro h

    · cases' h with hnP hnQ -- Split h into h not p and h not q
        -- (P V Q) → false
        -- Assume (P V Q), Prove false
      · intro h
        cases' h with hP hQ
        · apply hnP
          exact hP
        · apply hnQ
          exact hQ
done

-- Question 3 --
example: ∀ x y : ℝ , |x + y| ≤ |x|+|y| := by
-- Applying theorem from mathlib "The absolute value satisfies the triangle inequality"
exact abs_add_le x y
done

-- Question 4 --
example: B ⊆ A → C ⊆ A → (B ∪ C) ⊆ A := by
-- Introduce Hypotheses --
intro hBA hCA x hBC
-- Uses Cases To Split The Union B U C --
cases' hBC with hB hC

-- Proving hB --
-- Uses hBA to prove x ∈ A --
· apply hBA at hB
-- Goal is hB --
-- x is in A --
  exact hB

-- Proving hC --
-- Uses hCA to prove x belongs to x belongs to A --
· apply hCA at hC
-- Goal is hC --
  exact hC
done

-- Question 5 --
example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  -- Changes = to ↔ --
  ext x
  -- Splits into two case LHS → RHS and RHS → LHS --
  constructor
  -- Case 1 --
  -- Introduce Hypothesis --
  · intro hABC
    -- Split into two cases x ∈ A & x ∈ B ∪ C --
    cases' hABC with hA hBC

    -- Case 1.1 --
      -- Eliminates C from the goal --
    · left
      -- Eliminates B from the goal --
      left
      -- Goal equals hA --
      exact hA

    -- Case 1.2 --
    · cases' hBC with hB hC
      -- Case 1.2.1 --
      -- Eliminates C from the goal --
      · left
      -- Eliminates A from the goal --
        right
      -- Goal equals hB --
        exact hB

      -- Case 1.2.2 --
      -- Eliminates A & B from the goal --
      · right
      -- Goal equals hC --
        exact hC

-- Case 2 --
  · intro hABC
    cases' hABC with hAB hC
    -- Case 2.1 --
    · cases' hAB with hA hB
      -- Case 2.1.1 --
      · left
        exact hA
      -- Case 2.1.2
      · right
        left
        exact hB
    -- Case 2.2
    · right
      right
      exact hC

done
