/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 1 : ∪ ∩ ⊆ and all that

Lean doesn't have "abstract" sets like `{π, ℝ², {1,2,3}}` whose elements can
be totally random; it only has *subsets* of a type. If `X : Type` is a type
then the type of subsets of `X` is called `Set X`. So for example the
subset `{1,2,3}` of `ℕ` is a term of type `Set ℕ`.

A term of type `set X` can be thought of in four ways:

1) A set of elements of `X` (i.e. a set of elements all of which have type `X`);
2) A subset of `X`;
3) An element of the power set of `X`;
4) A function from `X` to `Prop` (sending the elements of `A` to `True` and the other ones to `False`)

So `Set X` could have been called `Subset X` or `Powerset X`; I guess they chose `Set X`
because it was the shortest.

Note that `X` is a type, but if `A` is a subset of `X` then `A` is a *term*; the type of `A` is `Set X`.
This means that `a : A` doesn't make sense. What we say instead is `a : X` and `a ∈ A`.
Of course `a ∈ A` is a true-false statement, so `a ∈ A : Prop`.

All the sets `A`, `B`, `C` etc we consider will be subsets of `X`.
If `x : X` then `x` may or may not be an element of `A`, `B`, `C`,
but it will always be a term of type `X`.

-/

namespace Section4sheet1


-- set up variables
variable (X : Type) -- Everything will be a subset of `X`
  (A B C D : Set X) -- A,B,C,D are subsets of `X`

/-
# subset (`⊆`), union (`∪`) and intersection (`∩`)

Here are some mathematical facts:

`A ⊆ B` is equivalent to `∀ x, x ∈ A → x ∈ B`;
`x ∈ A ∪ B` is equivalent to `x ∈ A ∨ x ∈ B`;
`x ∈ A ∩ B` is equivalent to `x ∈ A ∧ x ∈ B`.

All of these things are true *by definition* in Lean. Let's
check this.

-/
theorem subset_def : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := by
  -- ↔ is reflexive so `rfl` works because LHS is defined to be equal to RHS
  rfl

-- Say `x` is an arbitrary element of `X`.
variable (x : X)

theorem mem_union_iff : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  rfl

theorem mem_inter_iff : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  -- you don't even have to go into tactic mode to prove this stuff
  Iff.rfl
  -- note no `by` -- this is just the term

/-

So now to change one side of these `↔`s to the other, you can
`rw` the appropriate lemma, or you can just use `change`. Or
you can ask yourself whether you need to do this at all.

Let's prove some theorems.

-/

example : A ⊆ A := by
-- Introducing Hypotheses --
intro h1 h2
-- Goal is h2 so finished --
exact h2
------------------------------------------
example : A ⊆ B → B ⊆ C → A ⊆ C := by
-- Introducing Hypotheses --
intro hAB hBC x hA

-- Use hAB to prove x belongs to the set of B --
apply hAB at hA

-- Use hBC to prove x belongs to the set of C --
apply hBC at hA

-- Goal is hA so finished --
exact hA
------------------------------------------
example : A ⊆ A ∪ B := by
-- Introducing Hypotheses --
intro h1 h2
-- Changes So Only Have To Prove It Belongs To A --
left
-- Goal is hA --
exact h2
------------------------------------------
example : A ∩ B ⊆ A := by
-- Introducing Hypotheses --
intro h1 h2
-- Splits h2 into two cases for h1 is in A and h1 is in B --
cases' h2 with hA hB
-- Goal is hA so finished --
exact hA
------------------------------------------
example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := by
-- Introduces hypotheses --
intro hAB hAC x hA
-- Splits into two cases --
constructor
-- Case One --
-- Uses hAB to prove x belongs to the set of B --
· apply hAB at hA
  -- Left goal is exact hA so case finished --
  exact hA
-- Case Two --
-- Uses hAB to prove x belongs to the set of B --
· apply hAC at hA
  -- Right goal is exact hA so case finished --
  exact hA
-------------------------------------------
example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by
-- Introduces hypotheses --
intro hBA hCA x hBC
-- Uses Cases To Split The Union B U C --
cases' hBC with hB hC

-- Proving hB --
-- Uses hBA to prove x belongs to A --
· apply hBA at hB
-- Goal is hB --
  exact hB

-- Proving hC --
-- Uses hCA to prove x belongs to x belongs to A --
· apply hCA at hC
-- Goal equals hC --
  exact hC
--------------------------------------------
example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D := by
-- Introduces hypotheses --
intro hAB hCD x hAC
-- Splits hAC into x ∈ A and x ∈ C --
cases' hAC with hA hC
-- Case 1.1 --
-- Use hAB to prove x belongs to B --
· apply hAB at hA
-- Eliminate D from the goal --
  left
-- Goal equals hA --
  exact hA

-- Case 1.2 --
-- Use hCD to prove x belongs to D --
· apply hCD at hC
-- Eliminates B from the goal --
  right
-- Goal equals hC --
  exact hC
done
--------------------------------------------
example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D := by
-- Introduces hypotheses --
intro hAB hCD x hAC
-- Splits the goal into x ∈ B and x ∈ D
constructor

-- Case 1 --
-- Splits hAC into x ∈ A and x ∈ C --
· cases' hAC with hA hC
-- Case 1.1 --
-- Uses hAB to prove x ∈ B --
  apply hAB at hA
-- Goal equals hA --
  exact hA


-- Case 2 --
-- Splits hAC into x ∈ A and x ∈ C --
· cases' hAC with hA hC
-- Case 2.1 --
-- Uses hCD to prove x ∈ C --
  apply hCD at hC
-- Goal equals hC --
  exact hC

done
------------------------------Moodle Example--------------------------------------
variable (X : Type) -- Everything will be a subset of `X`
  (A B C D : Set X)

example : C ⊆ A ∪ B ∪ C ∪ D := by
-- Introduces hypotheses --
intro h1 h2
-- Eliminates D from the goal --
left
-- Eliminates A and B from the goal --
right
-- Goal is h2 --
exact h2
done
